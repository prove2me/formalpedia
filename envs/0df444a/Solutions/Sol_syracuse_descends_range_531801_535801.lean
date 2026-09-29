-- Prove2me | solution 1 for syracuse_descends_range_531801_535801
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:28.57689+00:00
-- url     : https://prove2.me/submissions/a3bfea30-4c0b-4e2a-a1c9-bb2d5adc2f7b

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


theorem B1015877 : Blo 531801 1015877 := bbase (se 4 (by rfl) ⟨95238, by rfl⟩ : syracuseStep 1015877 = 190477) (by norm_num)
theorem B1802357 : Blo 531801 1802357 := bbase (se 5 (by rfl) ⟨84485, by rfl⟩ : syracuseStep 1802357 = 168971) (by norm_num)
theorem B4063445 : Blo 531801 4063445 := bbase (se 7 (by rfl) ⟨47618, by rfl⟩ : syracuseStep 4063445 = 95237) (by norm_num)
theorem B852277 : Blo 531801 852277 := bbase (se 5 (by rfl) ⟨39950, by rfl⟩ : syracuseStep 852277 = 79901) (by norm_num)
theorem B5144917 : Blo 531801 5144917 := bbase (se 10 (by rfl) ⟨7536, by rfl⟩ : syracuseStep 5144917 = 15073) (by norm_num)
theorem B1016165 : Blo 531801 1016165 := bbase (se 4 (by rfl) ⟨95265, by rfl⟩ : syracuseStep 1016165 = 190531) (by norm_num)
theorem B1016317 : Blo 531801 1016317 := bbase (se 3 (by rfl) ⟨190559, by rfl⟩ : syracuseStep 1016317 = 381119) (by norm_num)
theorem B1802789 : Blo 531801 1802789 := bbase (se 4 (by rfl) ⟨169011, by rfl⟩ : syracuseStep 1802789 = 338023) (by norm_num)
theorem B2556485 : Blo 531801 2556485 := bbase (se 4 (by rfl) ⟨239670, by rfl⟩ : syracuseStep 2556485 = 479341) (by norm_num)
theorem B721477 : Blo 531801 721477 := bbase (se 4 (by rfl) ⟨67638, by rfl⟩ : syracuseStep 721477 = 135277) (by norm_num)
theorem B1278541 : Blo 531801 1278541 := bbase (se 3 (by rfl) ⟨239726, by rfl⟩ : syracuseStep 1278541 = 479453) (by norm_num)
theorem B852725 : Blo 531801 852725 := bbase (se 5 (by rfl) ⟨39971, by rfl⟩ : syracuseStep 852725 = 79943) (by norm_num)
theorem B2196229 : Blo 531801 2196229 := bbase (se 4 (by rfl) ⟨205896, by rfl⟩ : syracuseStep 2196229 = 411793) (by norm_num)
theorem B721693 : Blo 531801 721693 := bbase (se 3 (by rfl) ⟨135317, by rfl⟩ : syracuseStep 721693 = 270635) (by norm_num)
theorem B1016621 : Blo 531801 1016621 := bbase (se 3 (by rfl) ⟨190616, by rfl⟩ : syracuseStep 1016621 = 381233) (by norm_num)
theorem B1278773 : Blo 531801 1278773 := bbase (se 5 (by rfl) ⟨59942, by rfl⟩ : syracuseStep 1278773 = 119885) (by norm_num)
theorem B2163509 : Blo 531801 2163509 := bbase (se 5 (by rfl) ⟨101414, by rfl⟩ : syracuseStep 2163509 = 202829) (by norm_num)
theorem B1213325 : Blo 531801 1213325 := bbase (se 3 (by rfl) ⟨227498, by rfl⟩ : syracuseStep 1213325 = 454997) (by norm_num)
theorem B852925 : Blo 531801 852925 := bbase (se 3 (by rfl) ⟨159923, by rfl⟩ : syracuseStep 852925 = 319847) (by norm_num)
theorem B11535317 : Blo 531801 11535317 := bbase (se 7 (by rfl) ⟨135179, by rfl⟩ : syracuseStep 11535317 = 270359) (by norm_num)
theorem B721877 : Blo 531801 721877 := bbase (se 7 (by rfl) ⟨8459, by rfl⟩ : syracuseStep 721877 = 16919) (by norm_num)
theorem B1803221 : Blo 531801 1803221 := bbase (se 7 (by rfl) ⟨21131, by rfl⟩ : syracuseStep 1803221 = 42263) (by norm_num)
theorem B1279165 : Blo 531801 1279165 := bbase (se 3 (by rfl) ⟨239843, by rfl⟩ : syracuseStep 1279165 = 479687) (by norm_num)
theorem B853181 : Blo 531801 853181 := bbase (se 3 (by rfl) ⟨159971, by rfl⟩ : syracuseStep 853181 = 319943) (by norm_num)
theorem B2557253 : Blo 531801 2557253 := bbase (se 4 (by rfl) ⟨239742, by rfl⟩ : syracuseStep 2557253 = 479485) (by norm_num)
theorem B1803653 : Blo 531801 1803653 := bbase (se 4 (by rfl) ⟨169092, by rfl⟩ : syracuseStep 1803653 = 338185) (by norm_num)
theorem B2033045 : Blo 531801 2033045 := bbase (se 6 (by rfl) ⟨47649, by rfl⟩ : syracuseStep 2033045 = 95299) (by norm_num)
theorem B820709 : Blo 531801 820709 := bbase (se 4 (by rfl) ⟨76941, by rfl⟩ : syracuseStep 820709 = 153883) (by norm_num)
theorem B2033333 : Blo 531801 2033333 := bbase (se 5 (by rfl) ⟨95312, by rfl⟩ : syracuseStep 2033333 = 190625) (by norm_num)
theorem B820925 : Blo 531801 820925 := bbase (se 3 (by rfl) ⟨153923, by rfl⟩ : syracuseStep 820925 = 307847) (by norm_num)
theorem B1804085 : Blo 531801 1804085 := bbase (se 5 (by rfl) ⟨84566, by rfl⟩ : syracuseStep 1804085 = 169133) (by norm_num)
theorem B624721 : Blo 531801 624721 := bbase (se 2 (by rfl) ⟨234270, by rfl⟩ : syracuseStep 624721 = 468541) (by norm_num)
theorem B3049589 : Blo 531801 3049589 := bbase (se 5 (by rfl) ⟨142949, by rfl⟩ : syracuseStep 3049589 = 285899) (by norm_num)
theorem B1804517 : Blo 531801 1804517 := bbase (se 4 (by rfl) ⟨169173, by rfl⟩ : syracuseStep 1804517 = 338347) (by norm_num)
theorem B1280261 : Blo 531801 1280261 := bbase (se 4 (by rfl) ⟨120024, by rfl⟩ : syracuseStep 1280261 = 240049) (by norm_num)
theorem B854309 : Blo 531801 854309 := bbase (se 4 (by rfl) ⟨80091, by rfl⟩ : syracuseStep 854309 = 160183) (by norm_num)
theorem B1083773 : Blo 531801 1083773 := bbase (se 3 (by rfl) ⟨203207, by rfl⟩ : syracuseStep 1083773 = 406415) (by norm_num)
theorem B1280549 : Blo 531801 1280549 := bbase (se 4 (by rfl) ⟨120051, by rfl⟩ : syracuseStep 1280549 = 240103) (by norm_num)
theorem B1804949 : Blo 531801 1804949 := bbase (se 6 (by rfl) ⟨42303, by rfl⟩ : syracuseStep 1804949 = 84607) (by norm_num)
theorem B1215157 : Blo 531801 1215157 := bbase (se 5 (by rfl) ⟨56960, by rfl⟩ : syracuseStep 1215157 = 113921) (by norm_num)
theorem B1346341 : Blo 531801 1346341 := bbase (se 4 (by rfl) ⟨126219, by rfl⟩ : syracuseStep 1346341 = 252439) (by norm_num)
theorem B854821 : Blo 531801 854821 := bbase (se 4 (by rfl) ⟨80139, by rfl⟩ : syracuseStep 854821 = 160279) (by norm_num)
theorem B1346453 : Blo 531801 1346453 := bbase (se 6 (by rfl) ⟨31557, by rfl⟩ : syracuseStep 1346453 = 63115) (by norm_num)
theorem B3476405 : Blo 531801 3476405 := bbase (se 5 (by rfl) ⟨162956, by rfl⟩ : syracuseStep 3476405 = 325913) (by norm_num)
theorem B1805381 : Blo 531801 1805381 := bbase (se 4 (by rfl) ⟨169254, by rfl⟩ : syracuseStep 1805381 = 338509) (by norm_num)
theorem B1346645 : Blo 531801 1346645 := bbase (se 8 (by rfl) ⟨7890, by rfl⟩ : syracuseStep 1346645 = 15781) (by norm_num)
theorem B855365 : Blo 531801 855365 := bbase (se 4 (by rfl) ⟨80190, by rfl⟩ : syracuseStep 855365 = 160381) (by norm_num)
theorem B691573 : Blo 531801 691573 := bbase (se 5 (by rfl) ⟨32417, by rfl⟩ : syracuseStep 691573 = 64835) (by norm_num)
theorem B1346989 : Blo 531801 1346989 := bbase (se 3 (by rfl) ⟨252560, by rfl⟩ : syracuseStep 1346989 = 505121) (by norm_num)
theorem B1805813 : Blo 531801 1805813 := bbase (se 5 (by rfl) ⟨84647, by rfl⟩ : syracuseStep 1805813 = 169295) (by norm_num)
theorem B1609205 : Blo 531801 1609205 := bbase (se 5 (by rfl) ⟨75431, by rfl⟩ : syracuseStep 1609205 = 150863) (by norm_num)
theorem B1347101 : Blo 531801 1347101 := bbase (se 3 (by rfl) ⟨252581, by rfl⟩ : syracuseStep 1347101 = 505163) (by norm_num)
theorem B1085005 : Blo 531801 1085005 := bbase (se 3 (by rfl) ⟨203438, by rfl⟩ : syracuseStep 1085005 = 406877) (by norm_num)
theorem B757397 : Blo 531801 757397 := bbase (se 6 (by rfl) ⟨17751, by rfl⟩ : syracuseStep 757397 = 35503) (by norm_num)
theorem B1347293 : Blo 531801 1347293 := bbase (se 3 (by rfl) ⟨252617, by rfl⟩ : syracuseStep 1347293 = 505235) (by norm_num)
theorem B1707797 : Blo 531801 1707797 := bbase (se 6 (by rfl) ⟨40026, by rfl⟩ : syracuseStep 1707797 = 80053) (by norm_num)
theorem B855917 : Blo 531801 855917 := bbase (se 3 (by rfl) ⟨160484, by rfl⟩ : syracuseStep 855917 = 320969) (by norm_num)
theorem B855949 : Blo 531801 855949 := bbase (se 3 (by rfl) ⟨160490, by rfl⟩ : syracuseStep 855949 = 320981) (by norm_num)
theorem B1806245 : Blo 531801 1806245 := bbase (se 4 (by rfl) ⟨169335, by rfl⟩ : syracuseStep 1806245 = 338671) (by norm_num)
theorem B1347637 : Blo 531801 1347637 := bbase (se 5 (by rfl) ⟨63170, by rfl⟩ : syracuseStep 1347637 = 126341) (by norm_num)
theorem B2199653 : Blo 531801 2199653 := bbase (se 4 (by rfl) ⟨206217, by rfl⟩ : syracuseStep 2199653 = 412435) (by norm_num)
theorem B1347749 : Blo 531801 1347749 := bbase (se 4 (by rfl) ⟨126351, by rfl⟩ : syracuseStep 1347749 = 252703) (by norm_num)
theorem B1806677 : Blo 531801 1806677 := bbase (se 10 (by rfl) ⟨2646, by rfl⟩ : syracuseStep 1806677 = 5293) (by norm_num)
theorem B1347941 : Blo 531801 1347941 := bbase (se 4 (by rfl) ⟨126369, by rfl⟩ : syracuseStep 1347941 = 252739) (by norm_num)
theorem B2429365 : Blo 531801 2429365 := bbase (se 5 (by rfl) ⟨113876, by rfl⟩ : syracuseStep 2429365 = 227753) (by norm_num)
theorem B9277973 : Blo 531801 9277973 := bbase (se 6 (by rfl) ⟨217452, by rfl⟩ : syracuseStep 9277973 = 434905) (by norm_num)
theorem B1282645 : Blo 531801 1282645 := bbase (se 8 (by rfl) ⟨7515, by rfl⟩ : syracuseStep 1282645 = 15031) (by norm_num)
theorem B1151581 : Blo 531801 1151581 := bbase (se 3 (by rfl) ⟨215921, by rfl⟩ : syracuseStep 1151581 = 431843) (by norm_num)
theorem B1348285 : Blo 531801 1348285 := bbase (se 3 (by rfl) ⟨252803, by rfl⟩ : syracuseStep 1348285 = 505607) (by norm_num)
theorem B1807109 : Blo 531801 1807109 := bbase (se 4 (by rfl) ⟨169416, by rfl⟩ : syracuseStep 1807109 = 338833) (by norm_num)
theorem B1348397 : Blo 531801 1348397 := bbase (se 3 (by rfl) ⟨252824, by rfl⟩ : syracuseStep 1348397 = 505649) (by norm_num)
theorem B856877 : Blo 531801 856877 := bbase (se 3 (by rfl) ⟨160664, by rfl⟩ : syracuseStep 856877 = 321329) (by norm_num)
theorem B660433 : Blo 531801 660433 := bbase (se 2 (by rfl) ⟨247662, by rfl⟩ : syracuseStep 660433 = 495325) (by norm_num)
theorem B1348589 : Blo 531801 1348589 := bbase (se 3 (by rfl) ⟨252860, by rfl⟩ : syracuseStep 1348589 = 505721) (by norm_num)
theorem B758821 : Blo 531801 758821 := bbase (se 4 (by rfl) ⟨71139, by rfl⟩ : syracuseStep 758821 = 142279) (by norm_num)
theorem B2430005 : Blo 531801 2430005 := bbase (se 5 (by rfl) ⟨113906, by rfl⟩ : syracuseStep 2430005 = 227813) (by norm_num)
theorem B2692277 : Blo 531801 2692277 := bbase (se 5 (by rfl) ⟨126200, by rfl⟩ : syracuseStep 2692277 = 252401) (by norm_num)
theorem B1807541 : Blo 531801 1807541 := bbase (se 5 (by rfl) ⟨84728, by rfl⟩ : syracuseStep 1807541 = 169457) (by norm_num)
theorem B1283309 : Blo 531801 1283309 := bbase (se 3 (by rfl) ⟨240620, by rfl⟩ : syracuseStep 1283309 = 481241) (by norm_num)
theorem B1348933 : Blo 531801 1348933 := bbase (se 4 (by rfl) ⟨126462, by rfl⟩ : syracuseStep 1348933 = 252925) (by norm_num)
theorem B1349045 : Blo 531801 1349045 := bbase (se 5 (by rfl) ⟨63236, by rfl⟩ : syracuseStep 1349045 = 126473) (by norm_num)
theorem B857557 : Blo 531801 857557 := bbase (se 7 (by rfl) ⟨10049, by rfl⟩ : syracuseStep 857557 = 20099) (by norm_num)
theorem B2168309 : Blo 531801 2168309 := bbase (se 5 (by rfl) ⟨101639, by rfl⟩ : syracuseStep 2168309 = 203279) (by norm_num)
theorem B857621 : Blo 531801 857621 := bbase (se 6 (by rfl) ⟨20100, by rfl⟩ : syracuseStep 857621 = 40201) (by norm_num)
theorem B1807973 : Blo 531801 1807973 := bbase (se 4 (by rfl) ⟨169497, by rfl⟩ : syracuseStep 1807973 = 338995) (by norm_num)
theorem B1349237 : Blo 531801 1349237 := bbase (se 5 (by rfl) ⟨63245, by rfl⟩ : syracuseStep 1349237 = 126491) (by norm_num)
theorem B759413 : Blo 531801 759413 := bbase (se 5 (by rfl) ⟨35597, by rfl⟩ : syracuseStep 759413 = 71195) (by norm_num)
theorem B1218221 : Blo 531801 1218221 := bbase (se 3 (by rfl) ⟨228416, by rfl⟩ : syracuseStep 1218221 = 456833) (by norm_num)
theorem B759493 : Blo 531801 759493 := bbase (se 4 (by rfl) ⟨71202, by rfl⟩ : syracuseStep 759493 = 142405) (by norm_num)
theorem B759613 : Blo 531801 759613 := bbase (se 3 (by rfl) ⟨142427, by rfl⟩ : syracuseStep 759613 = 284855) (by norm_num)
theorem B759709 : Blo 531801 759709 := bbase (se 3 (by rfl) ⟨142445, by rfl⟩ : syracuseStep 759709 = 284891) (by norm_num)
theorem B1349581 : Blo 531801 1349581 := bbase (se 3 (by rfl) ⟨253046, by rfl⟩ : syracuseStep 1349581 = 506093) (by norm_num)
theorem B1349693 : Blo 531801 1349693 := bbase (se 3 (by rfl) ⟨253067, by rfl⟩ : syracuseStep 1349693 = 506135) (by norm_num)
theorem B1349885 : Blo 531801 1349885 := bbase (se 3 (by rfl) ⟨253103, by rfl⟩ : syracuseStep 1349885 = 506207) (by norm_num)
theorem B760205 : Blo 531801 760205 := bbase (se 3 (by rfl) ⟨142538, by rfl⟩ : syracuseStep 760205 = 285077) (by norm_num)
theorem B2693573 : Blo 531801 2693573 := bbase (se 4 (by rfl) ⟨252522, by rfl⟩ : syracuseStep 2693573 = 505045) (by norm_num)
theorem B1710629 : Blo 531801 1710629 := bbase (se 4 (by rfl) ⟨160371, by rfl⟩ : syracuseStep 1710629 = 320743) (by norm_num)
theorem B1350229 : Blo 531801 1350229 := bbase (se 8 (by rfl) ⟨7911, by rfl⟩ : syracuseStep 1350229 = 15823) (by norm_num)
theorem B1350341 : Blo 531801 1350341 := bbase (se 4 (by rfl) ⟨126594, by rfl⟩ : syracuseStep 1350341 = 253189) (by norm_num)
theorem B1350533 : Blo 531801 1350533 := bbase (se 4 (by rfl) ⟨126612, by rfl⟩ : syracuseStep 1350533 = 253225) (by norm_num)
theorem B760757 : Blo 531801 760757 := bbase (se 5 (by rfl) ⟨35660, by rfl⟩ : syracuseStep 760757 = 71321) (by norm_num)
theorem B1285085 : Blo 531801 1285085 := bbase (se 3 (by rfl) ⟨240953, by rfl⟩ : syracuseStep 1285085 = 481907) (by norm_num)
theorem B1219645 : Blo 531801 1219645 := bbase (se 3 (by rfl) ⟨228683, by rfl⟩ : syracuseStep 1219645 = 457367) (by norm_num)
theorem B1350877 : Blo 531801 1350877 := bbase (se 3 (by rfl) ⟨253289, by rfl⟩ : syracuseStep 1350877 = 506579) (by norm_num)
theorem B695569 : Blo 531801 695569 := bbase (se 2 (by rfl) ⟨260838, by rfl⟩ : syracuseStep 695569 = 521677) (by norm_num)
theorem B1350989 : Blo 531801 1350989 := bbase (se 3 (by rfl) ⟨253310, by rfl⟩ : syracuseStep 1350989 = 506621) (by norm_num)
theorem B6069653 : Blo 531801 6069653 := bbase (se 6 (by rfl) ⟨142257, by rfl⟩ : syracuseStep 6069653 = 284515) (by norm_num)
theorem B1711525 : Blo 531801 1711525 := bbase (se 4 (by rfl) ⟨160455, by rfl⟩ : syracuseStep 1711525 = 320911) (by norm_num)
theorem B1351181 : Blo 531801 1351181 := bbase (se 3 (by rfl) ⟨253346, by rfl⟩ : syracuseStep 1351181 = 506693) (by norm_num)
theorem B1515125 : Blo 531801 1515125 := bbase (se 5 (by rfl) ⟨71021, by rfl⟩ : syracuseStep 1515125 = 142043) (by norm_num)
theorem B761509 : Blo 531801 761509 := bbase (se 4 (by rfl) ⟨71391, by rfl⟩ : syracuseStep 761509 = 142783) (by norm_num)
theorem B2694869 : Blo 531801 2694869 := bbase (se 7 (by rfl) ⟨31580, by rfl⟩ : syracuseStep 2694869 = 63161) (by norm_num)
theorem B1351525 : Blo 531801 1351525 := bbase (se 4 (by rfl) ⟨126705, by rfl⟩ : syracuseStep 1351525 = 253411) (by norm_num)
theorem B1220557 : Blo 531801 1220557 := bbase (se 3 (by rfl) ⟨228854, by rfl⟩ : syracuseStep 1220557 = 457709) (by norm_num)
theorem B1351637 : Blo 531801 1351637 := bbase (se 7 (by rfl) ⟨15839, by rfl⟩ : syracuseStep 1351637 = 31679) (by norm_num)
theorem B1351829 : Blo 531801 1351829 := bbase (se 6 (by rfl) ⟨31683, by rfl⟩ : syracuseStep 1351829 = 63367) (by norm_num)
theorem B1515797 : Blo 531801 1515797 := bbase (se 6 (by rfl) ⟨35526, by rfl⟩ : syracuseStep 1515797 = 71053) (by norm_num)
theorem B598297 : Blo 531801 598297 := bbase (se 2 (by rfl) ⟨224361, by rfl⟩ : syracuseStep 598297 = 448723) (by norm_num)
theorem B598333 : Blo 531801 598333 := bbase (se 3 (by rfl) ⟨112187, by rfl⟩ : syracuseStep 598333 = 224375) (by norm_num)
theorem B598369 : Blo 531801 598369 := bbase (se 2 (by rfl) ⟨224388, by rfl⟩ : syracuseStep 598369 = 448777) (by norm_num)
theorem B598405 : Blo 531801 598405 := bbase (se 4 (by rfl) ⟨56100, by rfl⟩ : syracuseStep 598405 = 112201) (by norm_num)
theorem B598441 : Blo 531801 598441 := bbase (se 2 (by rfl) ⟨224415, by rfl⟩ : syracuseStep 598441 = 448831) (by norm_num)
theorem B762301 : Blo 531801 762301 := bbase (se 3 (by rfl) ⟨142931, by rfl⟩ : syracuseStep 762301 = 285863) (by norm_num)
theorem B598477 : Blo 531801 598477 := bbase (se 3 (by rfl) ⟨112214, by rfl⟩ : syracuseStep 598477 = 224429) (by norm_num)
theorem B1352173 : Blo 531801 1352173 := bbase (se 3 (by rfl) ⟨253532, by rfl⟩ : syracuseStep 1352173 = 507065) (by norm_num)
theorem B598513 : Blo 531801 598513 := bbase (se 2 (by rfl) ⟨224442, by rfl⟩ : syracuseStep 598513 = 448885) (by norm_num)
theorem B1155589 : Blo 531801 1155589 := bbase (se 4 (by rfl) ⟨108336, by rfl⟩ : syracuseStep 1155589 = 216673) (by norm_num)
theorem B598549 : Blo 531801 598549 := bbase (se 6 (by rfl) ⟨14028, by rfl⟩ : syracuseStep 598549 = 28057) (by norm_num)
theorem B598585 : Blo 531801 598585 := bbase (se 2 (by rfl) ⟨224469, by rfl⟩ : syracuseStep 598585 = 448939) (by norm_num)
theorem B598621 : Blo 531801 598621 := bbase (se 3 (by rfl) ⟨112241, by rfl⟩ : syracuseStep 598621 = 224483) (by norm_num)
theorem B1352285 : Blo 531801 1352285 := bbase (se 3 (by rfl) ⟨253553, by rfl⟩ : syracuseStep 1352285 = 507107) (by norm_num)
theorem B2433653 : Blo 531801 2433653 := bbase (se 5 (by rfl) ⟨114077, by rfl⟩ : syracuseStep 2433653 = 228155) (by norm_num)
theorem B598657 : Blo 531801 598657 := bbase (se 2 (by rfl) ⟨224496, by rfl⟩ : syracuseStep 598657 = 448993) (by norm_num)
theorem B598693 : Blo 531801 598693 := bbase (se 4 (by rfl) ⟨56127, by rfl⟩ : syracuseStep 598693 = 112255) (by norm_num)
theorem B1516229 : Blo 531801 1516229 := bbase (se 4 (by rfl) ⟨142146, by rfl⟩ : syracuseStep 1516229 = 284293) (by norm_num)
theorem B598729 : Blo 531801 598729 := bbase (se 2 (by rfl) ⟨224523, by rfl⟩ : syracuseStep 598729 = 449047) (by norm_num)
theorem B598765 : Blo 531801 598765 := bbase (se 3 (by rfl) ⟨112268, by rfl⟩ : syracuseStep 598765 = 224537) (by norm_num)
theorem B762637 : Blo 531801 762637 := bbase (se 3 (by rfl) ⟨142994, by rfl⟩ : syracuseStep 762637 = 285989) (by norm_num)
theorem B598801 : Blo 531801 598801 := bbase (se 2 (by rfl) ⟨224550, by rfl⟩ : syracuseStep 598801 = 449101) (by norm_num)
theorem B1352477 : Blo 531801 1352477 := bbase (se 3 (by rfl) ⟨253589, by rfl⟩ : syracuseStep 1352477 = 507179) (by norm_num)
theorem B598837 : Blo 531801 598837 := bbase (se 5 (by rfl) ⟨28070, by rfl⟩ : syracuseStep 598837 = 56141) (by norm_num)
theorem B598873 : Blo 531801 598873 := bbase (se 2 (by rfl) ⟨224577, by rfl⟩ : syracuseStep 598873 = 449155) (by norm_num)
theorem B598909 : Blo 531801 598909 := bbase (se 3 (by rfl) ⟨112295, by rfl⟩ : syracuseStep 598909 = 224591) (by norm_num)
theorem B598945 : Blo 531801 598945 := bbase (se 2 (by rfl) ⟨224604, by rfl⟩ : syracuseStep 598945 = 449209) (by norm_num)
theorem B598981 : Blo 531801 598981 := bbase (se 4 (by rfl) ⟨56154, by rfl⟩ : syracuseStep 598981 = 112309) (by norm_num)
theorem B2696165 : Blo 531801 2696165 := bbase (se 4 (by rfl) ⟨252765, by rfl⟩ : syracuseStep 2696165 = 505531) (by norm_num)
theorem B762853 : Blo 531801 762853 := bbase (se 4 (by rfl) ⟨71517, by rfl⟩ : syracuseStep 762853 = 143035) (by norm_num)
theorem B599017 : Blo 531801 599017 := bbase (se 2 (by rfl) ⟨224631, by rfl⟩ : syracuseStep 599017 = 449263) (by norm_num)
theorem B599053 : Blo 531801 599053 := bbase (se 3 (by rfl) ⟨112322, by rfl⟩ : syracuseStep 599053 = 224645) (by norm_num)
theorem B1287181 : Blo 531801 1287181 := bbase (se 3 (by rfl) ⟨241346, by rfl⟩ : syracuseStep 1287181 = 482693) (by norm_num)
theorem B599089 : Blo 531801 599089 := bbase (se 2 (by rfl) ⟨224658, by rfl⟩ : syracuseStep 599089 = 449317) (by norm_num)
theorem B599125 : Blo 531801 599125 := bbase (se 8 (by rfl) ⟨3510, by rfl⟩ : syracuseStep 599125 = 7021) (by norm_num)
theorem B1352821 : Blo 531801 1352821 := bbase (se 5 (by rfl) ⟨63413, by rfl⟩ : syracuseStep 1352821 = 126827) (by norm_num)
theorem B599161 : Blo 531801 599161 := bbase (se 2 (by rfl) ⟨224685, by rfl⟩ : syracuseStep 599161 = 449371) (by norm_num)
theorem B599197 : Blo 531801 599197 := bbase (se 3 (by rfl) ⟨112349, by rfl⟩ : syracuseStep 599197 = 224699) (by norm_num)
theorem B599233 : Blo 531801 599233 := bbase (se 2 (by rfl) ⟨224712, by rfl⟩ : syracuseStep 599233 = 449425) (by norm_num)
theorem B599269 : Blo 531801 599269 := bbase (se 4 (by rfl) ⟨56181, by rfl⟩ : syracuseStep 599269 = 112363) (by norm_num)
theorem B1352933 : Blo 531801 1352933 := bbase (se 4 (by rfl) ⟨126837, by rfl⟩ : syracuseStep 1352933 = 253675) (by norm_num)
theorem B599305 : Blo 531801 599305 := bbase (se 2 (by rfl) ⟨224739, by rfl⟩ : syracuseStep 599305 = 449479) (by norm_num)
theorem B599341 : Blo 531801 599341 := bbase (se 3 (by rfl) ⟨112376, by rfl⟩ : syracuseStep 599341 = 224753) (by norm_num)
theorem B599377 : Blo 531801 599377 := bbase (se 2 (by rfl) ⟨224766, by rfl⟩ : syracuseStep 599377 = 449533) (by norm_num)
theorem B599413 : Blo 531801 599413 := bbase (se 5 (by rfl) ⟨28097, by rfl⟩ : syracuseStep 599413 = 56195) (by norm_num)
theorem B3417461 : Blo 531801 3417461 := bbase (se 5 (by rfl) ⟨160193, by rfl⟩ : syracuseStep 3417461 = 320387) (by norm_num)
theorem B599449 : Blo 531801 599449 := bbase (se 2 (by rfl) ⟨224793, by rfl⟩ : syracuseStep 599449 = 449587) (by norm_num)
theorem B1353125 : Blo 531801 1353125 := bbase (se 4 (by rfl) ⟨126855, by rfl⟩ : syracuseStep 1353125 = 253711) (by norm_num)
theorem B4040117 : Blo 531801 4040117 := bbase (se 5 (by rfl) ⟨189380, by rfl⟩ : syracuseStep 4040117 = 378761) (by norm_num)
theorem B1516981 : Blo 531801 1516981 := bbase (se 5 (by rfl) ⟨71108, by rfl⟩ : syracuseStep 1516981 = 142217) (by norm_num)
theorem B2565557 : Blo 531801 2565557 := bbase (se 5 (by rfl) ⟨120260, by rfl⟩ : syracuseStep 2565557 = 240521) (by norm_num)
theorem B599485 : Blo 531801 599485 := bbase (se 3 (by rfl) ⟨112403, by rfl⟩ : syracuseStep 599485 = 224807) (by norm_num)
theorem B599521 : Blo 531801 599521 := bbase (se 2 (by rfl) ⟨224820, by rfl⟩ : syracuseStep 599521 = 449641) (by norm_num)
theorem B599557 : Blo 531801 599557 := bbase (se 4 (by rfl) ⟨56208, by rfl⟩ : syracuseStep 599557 = 112417) (by norm_num)
theorem B599593 : Blo 531801 599593 := bbase (se 2 (by rfl) ⟨224847, by rfl⟩ : syracuseStep 599593 = 449695) (by norm_num)
theorem B599629 : Blo 531801 599629 := bbase (se 3 (by rfl) ⟨112430, by rfl⟩ : syracuseStep 599629 = 224861) (by norm_num)
theorem B599665 : Blo 531801 599665 := bbase (se 2 (by rfl) ⟨224874, by rfl⟩ : syracuseStep 599665 = 449749) (by norm_num)
theorem B599701 : Blo 531801 599701 := bbase (se 6 (by rfl) ⟨14055, by rfl⟩ : syracuseStep 599701 = 28111) (by norm_num)
theorem B599737 : Blo 531801 599737 := bbase (se 2 (by rfl) ⟨224901, by rfl⟩ : syracuseStep 599737 = 449803) (by norm_num)
theorem B599773 : Blo 531801 599773 := bbase (se 3 (by rfl) ⟨112457, by rfl⟩ : syracuseStep 599773 = 224915) (by norm_num)
theorem B1353469 : Blo 531801 1353469 := bbase (se 3 (by rfl) ⟨253775, by rfl⟩ : syracuseStep 1353469 = 507551) (by norm_num)
theorem B599809 : Blo 531801 599809 := bbase (se 2 (by rfl) ⟨224928, by rfl⟩ : syracuseStep 599809 = 449857) (by norm_num)
theorem B599845 : Blo 531801 599845 := bbase (se 4 (by rfl) ⟨56235, by rfl⟩ : syracuseStep 599845 = 112471) (by norm_num)
theorem B599881 : Blo 531801 599881 := bbase (se 2 (by rfl) ⟨224955, by rfl⟩ : syracuseStep 599881 = 449911) (by norm_num)
theorem B599917 : Blo 531801 599917 := bbase (se 3 (by rfl) ⟨112484, by rfl⟩ : syracuseStep 599917 = 224969) (by norm_num)
theorem B1353581 : Blo 531801 1353581 := bbase (se 3 (by rfl) ⟨253796, by rfl⟩ : syracuseStep 1353581 = 507593) (by norm_num)
theorem B599953 : Blo 531801 599953 := bbase (se 2 (by rfl) ⟨224982, by rfl⟩ : syracuseStep 599953 = 449965) (by norm_num)
theorem B599989 : Blo 531801 599989 := bbase (se 5 (by rfl) ⟨28124, by rfl⟩ : syracuseStep 599989 = 56249) (by norm_num)
theorem B600025 : Blo 531801 600025 := bbase (se 2 (by rfl) ⟨225009, by rfl⟩ : syracuseStep 600025 = 450019) (by norm_num)
theorem B600061 : Blo 531801 600061 := bbase (se 3 (by rfl) ⟨112511, by rfl⟩ : syracuseStep 600061 = 225023) (by norm_num)
theorem B600097 : Blo 531801 600097 := bbase (se 2 (by rfl) ⟨225036, by rfl⟩ : syracuseStep 600097 = 450073) (by norm_num)
theorem B1353773 : Blo 531801 1353773 := bbase (se 3 (by rfl) ⟨253832, by rfl⟩ : syracuseStep 1353773 = 507665) (by norm_num)
theorem B600133 : Blo 531801 600133 := bbase (se 4 (by rfl) ⟨56262, by rfl⟩ : syracuseStep 600133 = 112525) (by norm_num)
theorem B600169 : Blo 531801 600169 := bbase (se 2 (by rfl) ⟨225063, by rfl⟩ : syracuseStep 600169 = 450127) (by norm_num)
theorem B600205 : Blo 531801 600205 := bbase (se 3 (by rfl) ⟨112538, by rfl⟩ : syracuseStep 600205 = 225077) (by norm_num)
theorem B600241 : Blo 531801 600241 := bbase (se 2 (by rfl) ⟨225090, by rfl⟩ : syracuseStep 600241 = 450181) (by norm_num)
theorem B600277 : Blo 531801 600277 := bbase (se 7 (by rfl) ⟨7034, by rfl⟩ : syracuseStep 600277 = 14069) (by norm_num)
theorem B2697461 : Blo 531801 2697461 := bbase (se 5 (by rfl) ⟨126443, by rfl⟩ : syracuseStep 2697461 = 252887) (by norm_num)
theorem B1714421 : Blo 531801 1714421 := bbase (se 5 (by rfl) ⟨80363, by rfl⟩ : syracuseStep 1714421 = 160727) (by norm_num)
theorem B600313 : Blo 531801 600313 := bbase (se 2 (by rfl) ⟨225117, by rfl⟩ : syracuseStep 600313 = 450235) (by norm_num)
theorem B1124621 : Blo 531801 1124621 := bbase (se 3 (by rfl) ⟨210866, by rfl⟩ : syracuseStep 1124621 = 421733) (by norm_num)
theorem B600349 : Blo 531801 600349 := bbase (se 3 (by rfl) ⟨112565, by rfl⟩ : syracuseStep 600349 = 225131) (by norm_num)
theorem B3909941 : Blo 531801 3909941 := bbase (se 5 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 3909941 = 366557) (by norm_num)
theorem B600385 : Blo 531801 600385 := bbase (se 2 (by rfl) ⟨225144, by rfl⟩ : syracuseStep 600385 = 450289) (by norm_num)
theorem B1845605 : Blo 531801 1845605 := bbase (se 4 (by rfl) ⟨173025, by rfl⟩ : syracuseStep 1845605 = 346051) (by norm_num)
theorem B600421 : Blo 531801 600421 := bbase (se 4 (by rfl) ⟨56289, by rfl⟩ : syracuseStep 600421 = 112579) (by norm_num)
theorem B1354117 : Blo 531801 1354117 := bbase (se 4 (by rfl) ⟨126948, by rfl⟩ : syracuseStep 1354117 = 253897) (by norm_num)
theorem B600457 : Blo 531801 600457 := bbase (se 2 (by rfl) ⟨225171, by rfl⟩ : syracuseStep 600457 = 450343) (by norm_num)
theorem B960925 : Blo 531801 960925 := bbase (se 3 (by rfl) ⟨180173, by rfl⟩ : syracuseStep 960925 = 360347) (by norm_num)
theorem B600493 : Blo 531801 600493 := bbase (se 3 (by rfl) ⟨112592, by rfl⟩ : syracuseStep 600493 = 225185) (by norm_num)
theorem B600529 : Blo 531801 600529 := bbase (se 2 (by rfl) ⟨225198, by rfl⟩ : syracuseStep 600529 = 450397) (by norm_num)
theorem B600565 : Blo 531801 600565 := bbase (se 5 (by rfl) ⟨28151, by rfl⟩ : syracuseStep 600565 = 56303) (by norm_num)
theorem B1354229 : Blo 531801 1354229 := bbase (se 5 (by rfl) ⟨63479, by rfl⟩ : syracuseStep 1354229 = 126959) (by norm_num)
theorem B6826517 : Blo 531801 6826517 := bbase (se 6 (by rfl) ⟨159996, by rfl⟩ : syracuseStep 6826517 = 319993) (by norm_num)
theorem B600601 : Blo 531801 600601 := bbase (se 2 (by rfl) ⟨225225, by rfl⟩ : syracuseStep 600601 = 450451) (by norm_num)
theorem B600637 : Blo 531801 600637 := bbase (se 3 (by rfl) ⟨112619, by rfl⟩ : syracuseStep 600637 = 225239) (by norm_num)
theorem B600673 : Blo 531801 600673 := bbase (se 2 (by rfl) ⟨225252, by rfl⟩ : syracuseStep 600673 = 450505) (by norm_num)
theorem B600709 : Blo 531801 600709 := bbase (se 4 (by rfl) ⟨56316, by rfl⟩ : syracuseStep 600709 = 112633) (by norm_num)
theorem B600745 : Blo 531801 600745 := bbase (se 2 (by rfl) ⟨225279, by rfl⟩ : syracuseStep 600745 = 450559) (by norm_num)
theorem B1354421 : Blo 531801 1354421 := bbase (se 5 (by rfl) ⟨63488, by rfl⟩ : syracuseStep 1354421 = 126977) (by norm_num)
theorem B600781 : Blo 531801 600781 := bbase (se 3 (by rfl) ⟨112646, by rfl⟩ : syracuseStep 600781 = 225293) (by norm_num)
theorem B600817 : Blo 531801 600817 := bbase (se 2 (by rfl) ⟨225306, by rfl⟩ : syracuseStep 600817 = 450613) (by norm_num)
theorem B600853 : Blo 531801 600853 := bbase (se 6 (by rfl) ⟨14082, by rfl⟩ : syracuseStep 600853 = 28165) (by norm_num)
theorem B600889 : Blo 531801 600889 := bbase (se 2 (by rfl) ⟨225333, by rfl⟩ : syracuseStep 600889 = 450667) (by norm_num)
theorem B600925 : Blo 531801 600925 := bbase (se 3 (by rfl) ⟨112673, by rfl⟩ : syracuseStep 600925 = 225347) (by norm_num)
theorem B568193 : Blo 531801 568193 := bbase (se 2 (by rfl) ⟨213072, by rfl⟩ : syracuseStep 568193 = 426145) (by norm_num)
theorem B600961 : Blo 531801 600961 := bbase (se 2 (by rfl) ⟨225360, by rfl⟩ : syracuseStep 600961 = 450721) (by norm_num)
theorem B4565909 : Blo 531801 4565909 := bbase (se 6 (by rfl) ⟨107013, by rfl⟩ : syracuseStep 4565909 = 214027) (by norm_num)
theorem B600997 : Blo 531801 600997 := bbase (se 4 (by rfl) ⟨56343, by rfl⟩ : syracuseStep 600997 = 112687) (by norm_num)
theorem B568253 : Blo 531801 568253 := bbase (se 3 (by rfl) ⟨106547, by rfl⟩ : syracuseStep 568253 = 213095) (by norm_num)
theorem B1158085 : Blo 531801 1158085 := bbase (se 4 (by rfl) ⟨108570, by rfl⟩ : syracuseStep 1158085 = 217141) (by norm_num)
theorem B601033 : Blo 531801 601033 := bbase (se 2 (by rfl) ⟨225387, by rfl⟩ : syracuseStep 601033 = 450775) (by norm_num)
theorem B601069 : Blo 531801 601069 := bbase (se 3 (by rfl) ⟨112700, by rfl⟩ : syracuseStep 601069 = 225401) (by norm_num)
theorem B2567173 : Blo 531801 2567173 := bbase (se 4 (by rfl) ⟨240672, by rfl⟩ : syracuseStep 2567173 = 481345) (by norm_num)
theorem B1354765 : Blo 531801 1354765 := bbase (se 3 (by rfl) ⟨254018, by rfl⟩ : syracuseStep 1354765 = 508037) (by norm_num)
theorem B601105 : Blo 531801 601105 := bbase (se 2 (by rfl) ⟨225414, by rfl⟩ : syracuseStep 601105 = 450829) (by norm_num)
theorem B797717 : Blo 531801 797717 := bbase (se 6 (by rfl) ⟨18696, by rfl⟩ : syracuseStep 797717 = 37393) (by norm_num)
theorem B1027093 : Blo 531801 1027093 := bbase (se 6 (by rfl) ⟨24072, by rfl⟩ : syracuseStep 1027093 = 48145) (by norm_num)
theorem B797741 : Blo 531801 797741 := bbase (se 3 (by rfl) ⟨149576, by rfl⟩ : syracuseStep 797741 = 299153) (by norm_num)
theorem B601141 : Blo 531801 601141 := bbase (se 5 (by rfl) ⟨28178, by rfl⟩ : syracuseStep 601141 = 56357) (by norm_num)
theorem B568381 : Blo 531801 568381 := bbase (se 3 (by rfl) ⟨106571, by rfl⟩ : syracuseStep 568381 = 213143) (by norm_num)
theorem B797765 : Blo 531801 797765 := bbase (se 4 (by rfl) ⟨74790, by rfl⟩ : syracuseStep 797765 = 149581) (by norm_num)
theorem B601177 : Blo 531801 601177 := bbase (se 2 (by rfl) ⟨225441, by rfl⟩ : syracuseStep 601177 = 450883) (by norm_num)
theorem B797789 : Blo 531801 797789 := bbase (se 3 (by rfl) ⟨149585, by rfl⟩ : syracuseStep 797789 = 299171) (by norm_num)
theorem B797813 : Blo 531801 797813 := bbase (se 5 (by rfl) ⟨37397, by rfl⟩ : syracuseStep 797813 = 74795) (by norm_num)
theorem B601213 : Blo 531801 601213 := bbase (se 3 (by rfl) ⟨112727, by rfl⟩ : syracuseStep 601213 = 225455) (by norm_num)
theorem B1354877 : Blo 531801 1354877 := bbase (se 3 (by rfl) ⟨254039, by rfl⟩ : syracuseStep 1354877 = 508079) (by norm_num)
theorem B797837 : Blo 531801 797837 := bbase (se 3 (by rfl) ⟨149594, by rfl⟩ : syracuseStep 797837 = 299189) (by norm_num)
theorem B601249 : Blo 531801 601249 := bbase (se 2 (by rfl) ⟨225468, by rfl⟩ : syracuseStep 601249 = 450937) (by norm_num)
theorem B797861 : Blo 531801 797861 := bbase (se 4 (by rfl) ⟨74799, by rfl⟩ : syracuseStep 797861 = 149599) (by norm_num)
theorem B797885 : Blo 531801 797885 := bbase (se 3 (by rfl) ⟨149603, by rfl⟩ : syracuseStep 797885 = 299207) (by norm_num)
theorem B601285 : Blo 531801 601285 := bbase (se 4 (by rfl) ⟨56370, by rfl⟩ : syracuseStep 601285 = 112741) (by norm_num)
theorem B797909 : Blo 531801 797909 := bbase (se 7 (by rfl) ⟨9350, by rfl⟩ : syracuseStep 797909 = 18701) (by norm_num)
theorem B601321 : Blo 531801 601321 := bbase (se 2 (by rfl) ⟨225495, by rfl⟩ : syracuseStep 601321 = 450991) (by norm_num)
theorem B797933 : Blo 531801 797933 := bbase (se 3 (by rfl) ⟨149612, by rfl⟩ : syracuseStep 797933 = 299225) (by norm_num)
theorem B797957 : Blo 531801 797957 := bbase (se 4 (by rfl) ⟨74808, by rfl⟩ : syracuseStep 797957 = 149617) (by norm_num)
theorem B601357 : Blo 531801 601357 := bbase (se 3 (by rfl) ⟨112754, by rfl⟩ : syracuseStep 601357 = 225509) (by norm_num)
theorem B797981 : Blo 531801 797981 := bbase (se 3 (by rfl) ⟨149621, by rfl⟩ : syracuseStep 797981 = 299243) (by norm_num)
theorem B601393 : Blo 531801 601393 := bbase (se 2 (by rfl) ⟨225522, by rfl⟩ : syracuseStep 601393 = 451045) (by norm_num)
theorem B798005 : Blo 531801 798005 := bbase (se 5 (by rfl) ⟨37406, by rfl⟩ : syracuseStep 798005 = 74813) (by norm_num)
theorem B961853 : Blo 531801 961853 := bbase (se 3 (by rfl) ⟨180347, by rfl⟩ : syracuseStep 961853 = 360695) (by norm_num)
theorem B1355069 : Blo 531801 1355069 := bbase (se 3 (by rfl) ⟨254075, by rfl⟩ : syracuseStep 1355069 = 508151) (by norm_num)
theorem B798029 : Blo 531801 798029 := bbase (se 3 (by rfl) ⟨149630, by rfl⟩ : syracuseStep 798029 = 299261) (by norm_num)
theorem B601429 : Blo 531801 601429 := bbase (se 11 (by rfl) ⟨440, by rfl⟩ : syracuseStep 601429 = 881) (by norm_num)
theorem B798053 : Blo 531801 798053 := bbase (se 4 (by rfl) ⟨74817, by rfl⟩ : syracuseStep 798053 = 149635) (by norm_num)
theorem B601465 : Blo 531801 601465 := bbase (se 2 (by rfl) ⟨225549, by rfl⟩ : syracuseStep 601465 = 451099) (by norm_num)
theorem B798077 : Blo 531801 798077 := bbase (se 3 (by rfl) ⟨149639, by rfl⟩ : syracuseStep 798077 = 299279) (by norm_num)
theorem B798101 : Blo 531801 798101 := bbase (se 6 (by rfl) ⟨18705, by rfl⟩ : syracuseStep 798101 = 37411) (by norm_num)
theorem B601501 : Blo 531801 601501 := bbase (se 3 (by rfl) ⟨112781, by rfl⟩ : syracuseStep 601501 = 225563) (by norm_num)
theorem B798125 : Blo 531801 798125 := bbase (se 3 (by rfl) ⟨149648, by rfl⟩ : syracuseStep 798125 = 299297) (by norm_num)
theorem B601537 : Blo 531801 601537 := bbase (se 2 (by rfl) ⟨225576, by rfl⟩ : syracuseStep 601537 = 451153) (by norm_num)
theorem B798149 : Blo 531801 798149 := bbase (se 4 (by rfl) ⟨74826, by rfl⟩ : syracuseStep 798149 = 149653) (by norm_num)
theorem B798173 : Blo 531801 798173 := bbase (se 3 (by rfl) ⟨149657, by rfl⟩ : syracuseStep 798173 = 299315) (by norm_num)
theorem B601573 : Blo 531801 601573 := bbase (se 4 (by rfl) ⟨56397, by rfl⟩ : syracuseStep 601573 = 112795) (by norm_num)
theorem B798197 : Blo 531801 798197 := bbase (se 5 (by rfl) ⟨37415, by rfl⟩ : syracuseStep 798197 = 74831) (by norm_num)
theorem B568825 : Blo 531801 568825 := bbase (se 2 (by rfl) ⟨213309, by rfl⟩ : syracuseStep 568825 = 426619) (by norm_num)
theorem B2698757 : Blo 531801 2698757 := bbase (se 4 (by rfl) ⟨253008, by rfl⟩ : syracuseStep 2698757 = 506017) (by norm_num)
theorem B601609 : Blo 531801 601609 := bbase (se 2 (by rfl) ⟨225603, by rfl⟩ : syracuseStep 601609 = 451207) (by norm_num)
theorem B798221 : Blo 531801 798221 := bbase (se 3 (by rfl) ⟨149666, by rfl⟩ : syracuseStep 798221 = 299333) (by norm_num)
theorem B798245 : Blo 531801 798245 := bbase (se 4 (by rfl) ⟨74835, by rfl⟩ : syracuseStep 798245 = 149671) (by norm_num)
theorem B601645 : Blo 531801 601645 := bbase (se 3 (by rfl) ⟨112808, by rfl⟩ : syracuseStep 601645 = 225617) (by norm_num)
theorem B798269 : Blo 531801 798269 := bbase (se 3 (by rfl) ⟨149675, by rfl⟩ : syracuseStep 798269 = 299351) (by norm_num)
theorem B601681 : Blo 531801 601681 := bbase (se 2 (by rfl) ⟨225630, by rfl⟩ : syracuseStep 601681 = 451261) (by norm_num)
theorem B831061 : Blo 531801 831061 := bbase (se 8 (by rfl) ⟨4869, by rfl⟩ : syracuseStep 831061 = 9739) (by norm_num)
theorem B10923605 : Blo 531801 10923605 := bbase (se 8 (by rfl) ⟨64005, by rfl⟩ : syracuseStep 10923605 = 128011) (by norm_num)
theorem B798293 : Blo 531801 798293 := bbase (se 8 (by rfl) ⟨4677, by rfl⟩ : syracuseStep 798293 = 9355) (by norm_num)
theorem B798317 : Blo 531801 798317 := bbase (se 3 (by rfl) ⟨149684, by rfl⟩ : syracuseStep 798317 = 299369) (by norm_num)
theorem B568945 : Blo 531801 568945 := bbase (se 2 (by rfl) ⟨213354, by rfl⟩ : syracuseStep 568945 = 426709) (by norm_num)
theorem B601717 : Blo 531801 601717 := bbase (se 5 (by rfl) ⟨28205, by rfl⟩ : syracuseStep 601717 = 56411) (by norm_num)
theorem B798341 : Blo 531801 798341 := bbase (se 4 (by rfl) ⟨74844, by rfl⟩ : syracuseStep 798341 = 149689) (by norm_num)
theorem B1355413 : Blo 531801 1355413 := bbase (se 6 (by rfl) ⟨31767, by rfl⟩ : syracuseStep 1355413 = 63535) (by norm_num)
theorem B601753 : Blo 531801 601753 := bbase (se 2 (by rfl) ⟨225657, by rfl⟩ : syracuseStep 601753 = 451315) (by norm_num)
theorem B798365 : Blo 531801 798365 := bbase (se 3 (by rfl) ⟨149693, by rfl⟩ : syracuseStep 798365 = 299387) (by norm_num)
theorem B798389 : Blo 531801 798389 := bbase (se 5 (by rfl) ⟨37424, by rfl⟩ : syracuseStep 798389 = 74849) (by norm_num)
theorem B601789 : Blo 531801 601789 := bbase (se 3 (by rfl) ⟨112835, by rfl⟩ : syracuseStep 601789 = 225671) (by norm_num)
theorem B798413 : Blo 531801 798413 := bbase (se 3 (by rfl) ⟨149702, by rfl⟩ : syracuseStep 798413 = 299405) (by norm_num)
theorem B601825 : Blo 531801 601825 := bbase (se 2 (by rfl) ⟨225684, by rfl⟩ : syracuseStep 601825 = 451369) (by norm_num)
theorem B798437 : Blo 531801 798437 := bbase (se 4 (by rfl) ⟨74853, by rfl⟩ : syracuseStep 798437 = 149707) (by norm_num)
theorem B798461 : Blo 531801 798461 := bbase (se 3 (by rfl) ⟨149711, by rfl⟩ : syracuseStep 798461 = 299423) (by norm_num)
theorem B601861 : Blo 531801 601861 := bbase (se 4 (by rfl) ⟨56424, by rfl⟩ : syracuseStep 601861 = 112849) (by norm_num)
theorem B1355525 : Blo 531801 1355525 := bbase (se 4 (by rfl) ⟨127080, by rfl⟩ : syracuseStep 1355525 = 254161) (by norm_num)
theorem B798485 : Blo 531801 798485 := bbase (se 6 (by rfl) ⟨18714, by rfl⟩ : syracuseStep 798485 = 37429) (by norm_num)
theorem B601897 : Blo 531801 601897 := bbase (se 2 (by rfl) ⟨225711, by rfl⟩ : syracuseStep 601897 = 451423) (by norm_num)
theorem B798509 : Blo 531801 798509 := bbase (se 3 (by rfl) ⟨149720, by rfl⟩ : syracuseStep 798509 = 299441) (by norm_num)
theorem B1945397 : Blo 531801 1945397 := bbase (se 5 (by rfl) ⟨91190, by rfl⟩ : syracuseStep 1945397 = 182381) (by norm_num)
theorem B798533 : Blo 531801 798533 := bbase (se 4 (by rfl) ⟨74862, by rfl⟩ : syracuseStep 798533 = 149725) (by norm_num)
theorem B601933 : Blo 531801 601933 := bbase (se 3 (by rfl) ⟨112862, by rfl⟩ : syracuseStep 601933 = 225725) (by norm_num)
theorem B798557 : Blo 531801 798557 := bbase (se 3 (by rfl) ⟨149729, by rfl⟩ : syracuseStep 798557 = 299459) (by norm_num)
theorem B569197 : Blo 531801 569197 := bbase (se 3 (by rfl) ⟨106724, by rfl⟩ : syracuseStep 569197 = 213449) (by norm_num)
theorem B569201 : Blo 531801 569201 := bbase (se 2 (by rfl) ⟨213450, by rfl⟩ : syracuseStep 569201 = 426901) (by norm_num)
theorem B601969 : Blo 531801 601969 := bbase (se 2 (by rfl) ⟨225738, by rfl⟩ : syracuseStep 601969 = 451477) (by norm_num)
theorem B798581 : Blo 531801 798581 := bbase (se 5 (by rfl) ⟨37433, by rfl⟩ : syracuseStep 798581 = 74867) (by norm_num)
theorem B798605 : Blo 531801 798605 := bbase (se 3 (by rfl) ⟨149738, by rfl⟩ : syracuseStep 798605 = 299477) (by norm_num)
theorem B602005 : Blo 531801 602005 := bbase (se 6 (by rfl) ⟨14109, by rfl⟩ : syracuseStep 602005 = 28219) (by norm_num)
theorem B798629 : Blo 531801 798629 := bbase (se 4 (by rfl) ⟨74871, by rfl⟩ : syracuseStep 798629 = 149743) (by norm_num)
theorem B602041 : Blo 531801 602041 := bbase (se 2 (by rfl) ⟨225765, by rfl⟩ : syracuseStep 602041 = 451531) (by norm_num)
theorem B798653 : Blo 531801 798653 := bbase (se 3 (by rfl) ⟨149747, by rfl⟩ : syracuseStep 798653 = 299495) (by norm_num)
theorem B1355717 : Blo 531801 1355717 := bbase (se 4 (by rfl) ⟨127098, by rfl⟩ : syracuseStep 1355717 = 254197) (by norm_num)
theorem B798677 : Blo 531801 798677 := bbase (se 7 (by rfl) ⟨9359, by rfl⟩ : syracuseStep 798677 = 18719) (by norm_num)
theorem B602077 : Blo 531801 602077 := bbase (se 3 (by rfl) ⟨112889, by rfl⟩ : syracuseStep 602077 = 225779) (by norm_num)
theorem B798701 : Blo 531801 798701 := bbase (se 3 (by rfl) ⟨149756, by rfl⟩ : syracuseStep 798701 = 299513) (by norm_num)
theorem B602113 : Blo 531801 602113 := bbase (se 2 (by rfl) ⟨225792, by rfl⟩ : syracuseStep 602113 = 451585) (by norm_num)
theorem B2273285 : Blo 531801 2273285 := bbase (se 4 (by rfl) ⟨213120, by rfl⟩ : syracuseStep 2273285 = 426241) (by norm_num)
theorem B798725 : Blo 531801 798725 := bbase (se 4 (by rfl) ⟨74880, by rfl⟩ : syracuseStep 798725 = 149761) (by norm_num)
theorem B798749 : Blo 531801 798749 := bbase (se 3 (by rfl) ⟨149765, by rfl⟩ : syracuseStep 798749 = 299531) (by norm_num)
theorem B962597 : Blo 531801 962597 := bbase (se 4 (by rfl) ⟨90243, by rfl⟩ : syracuseStep 962597 = 180487) (by norm_num)
theorem B602149 : Blo 531801 602149 := bbase (se 4 (by rfl) ⟨56451, by rfl⟩ : syracuseStep 602149 = 112903) (by norm_num)
theorem B798773 : Blo 531801 798773 := bbase (se 5 (by rfl) ⟨37442, by rfl⟩ : syracuseStep 798773 = 74885) (by norm_num)
theorem B602185 : Blo 531801 602185 := bbase (se 2 (by rfl) ⟨225819, by rfl⟩ : syracuseStep 602185 = 451639) (by norm_num)
theorem B798797 : Blo 531801 798797 := bbase (se 3 (by rfl) ⟨149774, by rfl⟩ : syracuseStep 798797 = 299549) (by norm_num)
theorem B798821 : Blo 531801 798821 := bbase (se 4 (by rfl) ⟨74889, by rfl⟩ : syracuseStep 798821 = 149779) (by norm_num)
theorem B602221 : Blo 531801 602221 := bbase (se 3 (by rfl) ⟨112916, by rfl⟩ : syracuseStep 602221 = 225833) (by norm_num)
theorem B798845 : Blo 531801 798845 := bbase (se 3 (by rfl) ⟨149783, by rfl⟩ : syracuseStep 798845 = 299567) (by norm_num)
theorem B602257 : Blo 531801 602257 := bbase (se 2 (by rfl) ⟨225846, by rfl⟩ : syracuseStep 602257 = 451693) (by norm_num)
theorem B798869 : Blo 531801 798869 := bbase (se 6 (by rfl) ⟨18723, by rfl⟩ : syracuseStep 798869 = 37447) (by norm_num)
theorem B798893 : Blo 531801 798893 := bbase (se 3 (by rfl) ⟨149792, by rfl⟩ : syracuseStep 798893 = 299585) (by norm_num)
theorem B602293 : Blo 531801 602293 := bbase (se 5 (by rfl) ⟨28232, by rfl⟩ : syracuseStep 602293 = 56465) (by norm_num)
theorem B798917 : Blo 531801 798917 := bbase (se 4 (by rfl) ⟨74898, by rfl⟩ : syracuseStep 798917 = 149797) (by norm_num)
theorem B1519829 : Blo 531801 1519829 := bbase (se 7 (by rfl) ⟨17810, by rfl⟩ : syracuseStep 1519829 = 35621) (by norm_num)
theorem B602329 : Blo 531801 602329 := bbase (se 2 (by rfl) ⟨225873, by rfl⟩ : syracuseStep 602329 = 451747) (by norm_num)
theorem B798941 : Blo 531801 798941 := bbase (se 3 (by rfl) ⟨149801, by rfl⟩ : syracuseStep 798941 = 299603) (by norm_num)
theorem B1618165 : Blo 531801 1618165 := bbase (se 5 (by rfl) ⟨75851, by rfl⟩ : syracuseStep 1618165 = 151703) (by norm_num)
theorem B798965 : Blo 531801 798965 := bbase (se 5 (by rfl) ⟨37451, by rfl⟩ : syracuseStep 798965 = 74903) (by norm_num)
theorem B602365 : Blo 531801 602365 := bbase (se 3 (by rfl) ⟨112943, by rfl⟩ : syracuseStep 602365 = 225887) (by norm_num)
theorem B798989 : Blo 531801 798989 := bbase (se 3 (by rfl) ⟨149810, by rfl⟩ : syracuseStep 798989 = 299621) (by norm_num)
theorem B1356061 : Blo 531801 1356061 := bbase (se 3 (by rfl) ⟨254261, by rfl⟩ : syracuseStep 1356061 = 508523) (by norm_num)
theorem B602401 : Blo 531801 602401 := bbase (se 2 (by rfl) ⟨225900, by rfl⟩ : syracuseStep 602401 = 451801) (by norm_num)
theorem B799013 : Blo 531801 799013 := bbase (se 4 (by rfl) ⟨74907, by rfl⟩ : syracuseStep 799013 = 149815) (by norm_num)
theorem B799037 : Blo 531801 799037 := bbase (se 3 (by rfl) ⟨149819, by rfl⟩ : syracuseStep 799037 = 299639) (by norm_num)
theorem B602437 : Blo 531801 602437 := bbase (se 4 (by rfl) ⟨56478, by rfl⟩ : syracuseStep 602437 = 112957) (by norm_num)
theorem B799061 : Blo 531801 799061 := bbase (se 10 (by rfl) ⟨1170, by rfl⟩ : syracuseStep 799061 = 2341) (by norm_num)
theorem B602473 : Blo 531801 602473 := bbase (se 2 (by rfl) ⟨225927, by rfl⟩ : syracuseStep 602473 = 451855) (by norm_num)
theorem B799085 : Blo 531801 799085 := bbase (se 3 (by rfl) ⟨149828, by rfl⟩ : syracuseStep 799085 = 299657) (by norm_num)
theorem B799109 : Blo 531801 799109 := bbase (se 4 (by rfl) ⟨74916, by rfl⟩ : syracuseStep 799109 = 149833) (by norm_num)
theorem B602509 : Blo 531801 602509 := bbase (se 3 (by rfl) ⟨112970, by rfl⟩ : syracuseStep 602509 = 225941) (by norm_num)
theorem B1356173 : Blo 531801 1356173 := bbase (se 3 (by rfl) ⟨254282, by rfl⟩ : syracuseStep 1356173 = 508565) (by norm_num)
theorem B799133 : Blo 531801 799133 := bbase (se 3 (by rfl) ⟨149837, by rfl⟩ : syracuseStep 799133 = 299675) (by norm_num)
theorem B569765 : Blo 531801 569765 := bbase (se 4 (by rfl) ⟨53415, by rfl⟩ : syracuseStep 569765 = 106831) (by norm_num)
theorem B602545 : Blo 531801 602545 := bbase (se 2 (by rfl) ⟨225954, by rfl⟩ : syracuseStep 602545 = 451909) (by norm_num)
theorem B799157 : Blo 531801 799157 := bbase (se 5 (by rfl) ⟨37460, by rfl⟩ : syracuseStep 799157 = 74921) (by norm_num)
theorem B799181 : Blo 531801 799181 := bbase (se 3 (by rfl) ⟨149846, by rfl⟩ : syracuseStep 799181 = 299693) (by norm_num)
theorem B897493 : Blo 531801 897493 := bbase (se 7 (by rfl) ⟨10517, by rfl⟩ : syracuseStep 897493 = 21035) (by norm_num)
theorem B602581 : Blo 531801 602581 := bbase (se 7 (by rfl) ⟨7061, by rfl⟩ : syracuseStep 602581 = 14123) (by norm_num)
theorem B799205 : Blo 531801 799205 := bbase (se 4 (by rfl) ⟨74925, by rfl⟩ : syracuseStep 799205 = 149851) (by norm_num)
theorem B602617 : Blo 531801 602617 := bbase (se 2 (by rfl) ⟨225981, by rfl⟩ : syracuseStep 602617 = 451963) (by norm_num)
theorem B799229 : Blo 531801 799229 := bbase (se 3 (by rfl) ⟨149855, by rfl⟩ : syracuseStep 799229 = 299711) (by norm_num)
theorem B799253 : Blo 531801 799253 := bbase (se 6 (by rfl) ⟨18732, by rfl⟩ : syracuseStep 799253 = 37465) (by norm_num)
theorem B3650069 : Blo 531801 3650069 := bbase (se 6 (by rfl) ⟨85548, by rfl⟩ : syracuseStep 3650069 = 171097) (by norm_num)
theorem B602653 : Blo 531801 602653 := bbase (se 3 (by rfl) ⟨112997, by rfl⟩ : syracuseStep 602653 = 225995) (by norm_num)
theorem B897581 : Blo 531801 897581 := bbase (se 3 (by rfl) ⟨168296, by rfl⟩ : syracuseStep 897581 = 336593) (by norm_num)
theorem B799277 : Blo 531801 799277 := bbase (se 3 (by rfl) ⟨149864, by rfl⟩ : syracuseStep 799277 = 299729) (by norm_num)
theorem B602689 : Blo 531801 602689 := bbase (se 2 (by rfl) ⟨226008, by rfl⟩ : syracuseStep 602689 = 452017) (by norm_num)
theorem B799301 : Blo 531801 799301 := bbase (se 4 (by rfl) ⟨74934, by rfl⟩ : syracuseStep 799301 = 149869) (by norm_num)
theorem B799325 : Blo 531801 799325 := bbase (se 3 (by rfl) ⟨149873, by rfl⟩ : syracuseStep 799325 = 299747) (by norm_num)
theorem B569953 : Blo 531801 569953 := bbase (se 2 (by rfl) ⟨213732, by rfl⟩ : syracuseStep 569953 = 427465) (by norm_num)
theorem B602725 : Blo 531801 602725 := bbase (se 4 (by rfl) ⟨56505, by rfl⟩ : syracuseStep 602725 = 113011) (by norm_num)
theorem B799349 : Blo 531801 799349 := bbase (se 5 (by rfl) ⟨37469, by rfl⟩ : syracuseStep 799349 = 74939) (by norm_num)
theorem B602761 : Blo 531801 602761 := bbase (se 2 (by rfl) ⟨226035, by rfl⟩ : syracuseStep 602761 = 452071) (by norm_num)
theorem B799373 : Blo 531801 799373 := bbase (se 3 (by rfl) ⟨149882, by rfl⟩ : syracuseStep 799373 = 299765) (by norm_num)
theorem B799397 : Blo 531801 799397 := bbase (se 4 (by rfl) ⟨74943, by rfl⟩ : syracuseStep 799397 = 149887) (by norm_num)
theorem B897709 : Blo 531801 897709 := bbase (se 3 (by rfl) ⟨168320, by rfl⟩ : syracuseStep 897709 = 336641) (by norm_num)
theorem B799421 : Blo 531801 799421 := bbase (se 3 (by rfl) ⟨149891, by rfl⟩ : syracuseStep 799421 = 299783) (by norm_num)
theorem B799445 : Blo 531801 799445 := bbase (se 7 (by rfl) ⟨9368, by rfl⟩ : syracuseStep 799445 = 18737) (by norm_num)
theorem B799469 : Blo 531801 799469 := bbase (se 3 (by rfl) ⟨149900, by rfl⟩ : syracuseStep 799469 = 299801) (by norm_num)
theorem B897797 : Blo 531801 897797 := bbase (se 4 (by rfl) ⟨84168, by rfl⟩ : syracuseStep 897797 = 168337) (by norm_num)
theorem B799493 : Blo 531801 799493 := bbase (se 4 (by rfl) ⟨74952, by rfl⟩ : syracuseStep 799493 = 149905) (by norm_num)
theorem B2700053 : Blo 531801 2700053 := bbase (se 6 (by rfl) ⟨63282, by rfl⟩ : syracuseStep 2700053 = 126565) (by norm_num)
theorem B799517 : Blo 531801 799517 := bbase (se 3 (by rfl) ⟨149909, by rfl⟩ : syracuseStep 799517 = 299819) (by norm_num)
theorem B799541 : Blo 531801 799541 := bbase (se 5 (by rfl) ⟨37478, by rfl⟩ : syracuseStep 799541 = 74957) (by norm_num)
theorem B799565 : Blo 531801 799565 := bbase (se 3 (by rfl) ⟨149918, by rfl⟩ : syracuseStep 799565 = 299837) (by norm_num)
theorem B799589 : Blo 531801 799589 := bbase (se 4 (by rfl) ⟨74961, by rfl⟩ : syracuseStep 799589 = 149923) (by norm_num)
theorem B799613 : Blo 531801 799613 := bbase (se 3 (by rfl) ⟨149927, by rfl⟩ : syracuseStep 799613 = 299855) (by norm_num)
theorem B897925 : Blo 531801 897925 := bbase (se 4 (by rfl) ⟨84180, by rfl⟩ : syracuseStep 897925 = 168361) (by norm_num)
theorem B799637 : Blo 531801 799637 := bbase (se 6 (by rfl) ⟨18741, by rfl⟩ : syracuseStep 799637 = 37483) (by norm_num)
theorem B799661 : Blo 531801 799661 := bbase (se 3 (by rfl) ⟨149936, by rfl⟩ : syracuseStep 799661 = 299873) (by norm_num)
theorem B799685 : Blo 531801 799685 := bbase (se 4 (by rfl) ⟨74970, by rfl⟩ : syracuseStep 799685 = 149941) (by norm_num)
theorem B898013 : Blo 531801 898013 := bbase (se 3 (by rfl) ⟨168377, by rfl⟩ : syracuseStep 898013 = 336755) (by norm_num)
theorem B799709 : Blo 531801 799709 := bbase (se 3 (by rfl) ⟨149945, by rfl⟩ : syracuseStep 799709 = 299891) (by norm_num)
theorem B799733 : Blo 531801 799733 := bbase (se 5 (by rfl) ⟨37487, by rfl⟩ : syracuseStep 799733 = 74975) (by norm_num)
theorem B799757 : Blo 531801 799757 := bbase (se 3 (by rfl) ⟨149954, by rfl⟩ : syracuseStep 799757 = 299909) (by norm_num)
theorem B963613 : Blo 531801 963613 := bbase (se 3 (by rfl) ⟨180677, by rfl⟩ : syracuseStep 963613 = 361355) (by norm_num)
theorem B799781 : Blo 531801 799781 := bbase (se 4 (by rfl) ⟨74979, by rfl⟩ : syracuseStep 799781 = 149959) (by norm_num)
theorem B799805 : Blo 531801 799805 := bbase (se 3 (by rfl) ⟨149963, by rfl⟩ : syracuseStep 799805 = 299927) (by norm_num)
theorem B799829 : Blo 531801 799829 := bbase (se 8 (by rfl) ⟨4686, by rfl⟩ : syracuseStep 799829 = 9373) (by norm_num)
theorem B898141 : Blo 531801 898141 := bbase (se 3 (by rfl) ⟨168401, by rfl⟩ : syracuseStep 898141 = 336803) (by norm_num)
theorem B799853 : Blo 531801 799853 := bbase (se 3 (by rfl) ⟨149972, by rfl⟩ : syracuseStep 799853 = 299945) (by norm_num)
theorem B799877 : Blo 531801 799877 := bbase (se 4 (by rfl) ⟨74988, by rfl⟩ : syracuseStep 799877 = 149977) (by norm_num)
theorem B1422485 : Blo 531801 1422485 := bbase (se 6 (by rfl) ⟨33339, by rfl⟩ : syracuseStep 1422485 = 66679) (by norm_num)
theorem B799901 : Blo 531801 799901 := bbase (se 3 (by rfl) ⟨149981, by rfl⟩ : syracuseStep 799901 = 299963) (by norm_num)
theorem B898229 : Blo 531801 898229 := bbase (se 5 (by rfl) ⟨42104, by rfl⟩ : syracuseStep 898229 = 84209) (by norm_num)
theorem B799925 : Blo 531801 799925 := bbase (se 5 (by rfl) ⟨37496, by rfl⟩ : syracuseStep 799925 = 74993) (by norm_num)
theorem B799949 : Blo 531801 799949 := bbase (se 3 (by rfl) ⟨149990, by rfl⟩ : syracuseStep 799949 = 299981) (by norm_num)
theorem B799973 : Blo 531801 799973 := bbase (se 4 (by rfl) ⟨74997, by rfl⟩ : syracuseStep 799973 = 149995) (by norm_num)
theorem B963829 : Blo 531801 963829 := bbase (se 5 (by rfl) ⟨45179, by rfl⟩ : syracuseStep 963829 = 90359) (by norm_num)
theorem B799997 : Blo 531801 799997 := bbase (se 3 (by rfl) ⟨149999, by rfl⟩ : syracuseStep 799997 = 299999) (by norm_num)
theorem B800021 : Blo 531801 800021 := bbase (se 6 (by rfl) ⟨18750, by rfl⟩ : syracuseStep 800021 = 37501) (by norm_num)
theorem B800045 : Blo 531801 800045 := bbase (se 3 (by rfl) ⟨150008, by rfl⟩ : syracuseStep 800045 = 300017) (by norm_num)
theorem B898357 : Blo 531801 898357 := bbase (se 5 (by rfl) ⟨42110, by rfl⟩ : syracuseStep 898357 = 84221) (by norm_num)
theorem B800069 : Blo 531801 800069 := bbase (se 4 (by rfl) ⟨75006, by rfl⟩ : syracuseStep 800069 = 150013) (by norm_num)
theorem B800093 : Blo 531801 800093 := bbase (se 3 (by rfl) ⟨150017, by rfl⟩ : syracuseStep 800093 = 300035) (by norm_num)
theorem B800117 : Blo 531801 800117 := bbase (se 5 (by rfl) ⟨37505, by rfl⟩ : syracuseStep 800117 = 75011) (by norm_num)
theorem B1521013 : Blo 531801 1521013 := bbase (se 5 (by rfl) ⟨71297, by rfl⟩ : syracuseStep 1521013 = 142595) (by norm_num)
theorem B898445 : Blo 531801 898445 := bbase (se 3 (by rfl) ⟨168458, by rfl⟩ : syracuseStep 898445 = 336917) (by norm_num)
theorem B800141 : Blo 531801 800141 := bbase (se 3 (by rfl) ⟨150026, by rfl⟩ : syracuseStep 800141 = 300053) (by norm_num)
theorem B570773 : Blo 531801 570773 := bbase (se 6 (by rfl) ⟨13377, by rfl⟩ : syracuseStep 570773 = 26755) (by norm_num)
theorem B800165 : Blo 531801 800165 := bbase (se 4 (by rfl) ⟨75015, by rfl⟩ : syracuseStep 800165 = 150031) (by norm_num)
theorem B800189 : Blo 531801 800189 := bbase (se 3 (by rfl) ⟨150035, by rfl⟩ : syracuseStep 800189 = 300071) (by norm_num)
theorem B800213 : Blo 531801 800213 := bbase (se 7 (by rfl) ⟨9377, by rfl⟩ : syracuseStep 800213 = 18755) (by norm_num)
theorem B800237 : Blo 531801 800237 := bbase (se 3 (by rfl) ⟨150044, by rfl⟩ : syracuseStep 800237 = 300089) (by norm_num)
theorem B800261 : Blo 531801 800261 := bbase (se 4 (by rfl) ⟨75024, by rfl⟩ : syracuseStep 800261 = 150049) (by norm_num)
theorem B898573 : Blo 531801 898573 := bbase (se 3 (by rfl) ⟨168482, by rfl⟩ : syracuseStep 898573 = 336965) (by norm_num)
theorem B1521173 : Blo 531801 1521173 := bbase (se 6 (by rfl) ⟨35652, by rfl⟩ : syracuseStep 1521173 = 71305) (by norm_num)
theorem B800285 : Blo 531801 800285 := bbase (se 3 (by rfl) ⟨150053, by rfl⟩ : syracuseStep 800285 = 300107) (by norm_num)
theorem B800309 : Blo 531801 800309 := bbase (se 5 (by rfl) ⟨37514, by rfl⟩ : syracuseStep 800309 = 75029) (by norm_num)
theorem B800333 : Blo 531801 800333 := bbase (se 3 (by rfl) ⟨150062, by rfl⟩ : syracuseStep 800333 = 300125) (by norm_num)
theorem B898661 : Blo 531801 898661 := bbase (se 4 (by rfl) ⟨84249, by rfl⟩ : syracuseStep 898661 = 168499) (by norm_num)
theorem B800357 : Blo 531801 800357 := bbase (se 4 (by rfl) ⟨75033, by rfl⟩ : syracuseStep 800357 = 150067) (by norm_num)
theorem B1390189 : Blo 531801 1390189 := bbase (se 3 (by rfl) ⟨260660, by rfl⟩ : syracuseStep 1390189 = 521321) (by norm_num)
theorem B800381 : Blo 531801 800381 := bbase (se 3 (by rfl) ⟨150071, by rfl⟩ : syracuseStep 800381 = 300143) (by norm_num)
theorem B800405 : Blo 531801 800405 := bbase (se 6 (by rfl) ⟨18759, by rfl⟩ : syracuseStep 800405 = 37519) (by norm_num)
theorem B800429 : Blo 531801 800429 := bbase (se 3 (by rfl) ⟨150080, by rfl⟩ : syracuseStep 800429 = 300161) (by norm_num)
theorem B800453 : Blo 531801 800453 := bbase (se 4 (by rfl) ⟨75042, by rfl⟩ : syracuseStep 800453 = 150085) (by norm_num)
theorem B800477 : Blo 531801 800477 := bbase (se 3 (by rfl) ⟨150089, by rfl⟩ : syracuseStep 800477 = 300179) (by norm_num)
theorem B898789 : Blo 531801 898789 := bbase (se 4 (by rfl) ⟨84261, by rfl⟩ : syracuseStep 898789 = 168523) (by norm_num)
theorem B800501 : Blo 531801 800501 := bbase (se 5 (by rfl) ⟨37523, by rfl⟩ : syracuseStep 800501 = 75047) (by norm_num)
theorem B1521413 : Blo 531801 1521413 := bbase (se 4 (by rfl) ⟨142632, by rfl⟩ : syracuseStep 1521413 = 285265) (by norm_num)
theorem B800525 : Blo 531801 800525 := bbase (se 3 (by rfl) ⟨150098, by rfl⟩ : syracuseStep 800525 = 300197) (by norm_num)
theorem B800549 : Blo 531801 800549 := bbase (se 4 (by rfl) ⟨75051, by rfl⟩ : syracuseStep 800549 = 150103) (by norm_num)
theorem B4568885 : Blo 531801 4568885 := bbase (se 5 (by rfl) ⟨214166, by rfl⟩ : syracuseStep 4568885 = 428333) (by norm_num)
theorem B898877 : Blo 531801 898877 := bbase (se 3 (by rfl) ⟨168539, by rfl⟩ : syracuseStep 898877 = 337079) (by norm_num)
theorem B800573 : Blo 531801 800573 := bbase (se 3 (by rfl) ⟨150107, by rfl⟩ : syracuseStep 800573 = 300215) (by norm_num)
theorem B571217 : Blo 531801 571217 := bbase (se 2 (by rfl) ⟨214206, by rfl⟩ : syracuseStep 571217 = 428413) (by norm_num)
theorem B800597 : Blo 531801 800597 := bbase (se 9 (by rfl) ⟨2345, by rfl⟩ : syracuseStep 800597 = 4691) (by norm_num)
theorem B800621 : Blo 531801 800621 := bbase (se 3 (by rfl) ⟨150116, by rfl⟩ : syracuseStep 800621 = 300233) (by norm_num)
theorem B800645 : Blo 531801 800645 := bbase (se 4 (by rfl) ⟨75060, by rfl⟩ : syracuseStep 800645 = 150121) (by norm_num)
theorem B800669 : Blo 531801 800669 := bbase (se 3 (by rfl) ⟨150125, by rfl⟩ : syracuseStep 800669 = 300251) (by norm_num)
theorem B800693 : Blo 531801 800693 := bbase (se 5 (by rfl) ⟨37532, by rfl⟩ : syracuseStep 800693 = 75065) (by norm_num)
theorem B899005 : Blo 531801 899005 := bbase (se 3 (by rfl) ⟨168563, by rfl⟩ : syracuseStep 899005 = 337127) (by norm_num)
theorem B1521605 : Blo 531801 1521605 := bbase (se 4 (by rfl) ⟨142650, by rfl⟩ : syracuseStep 1521605 = 285301) (by norm_num)
theorem B800717 : Blo 531801 800717 := bbase (se 3 (by rfl) ⟨150134, by rfl⟩ : syracuseStep 800717 = 300269) (by norm_num)
theorem B800741 : Blo 531801 800741 := bbase (se 4 (by rfl) ⟨75069, by rfl⟩ : syracuseStep 800741 = 150139) (by norm_num)
theorem B800765 : Blo 531801 800765 := bbase (se 3 (by rfl) ⟨150143, by rfl⟩ : syracuseStep 800765 = 300287) (by norm_num)
theorem B964621 : Blo 531801 964621 := bbase (se 3 (by rfl) ⟨180866, by rfl⟩ : syracuseStep 964621 = 361733) (by norm_num)
theorem B899093 : Blo 531801 899093 := bbase (se 6 (by rfl) ⟨21072, by rfl⟩ : syracuseStep 899093 = 42145) (by norm_num)
theorem B800789 : Blo 531801 800789 := bbase (se 6 (by rfl) ⟨18768, by rfl⟩ : syracuseStep 800789 = 37537) (by norm_num)
theorem B2701349 : Blo 531801 2701349 := bbase (se 4 (by rfl) ⟨253251, by rfl⟩ : syracuseStep 2701349 = 506503) (by norm_num)
theorem B800813 : Blo 531801 800813 := bbase (se 3 (by rfl) ⟨150152, by rfl⟩ : syracuseStep 800813 = 300305) (by norm_num)
theorem B800837 : Blo 531801 800837 := bbase (se 4 (by rfl) ⟨75078, by rfl⟩ : syracuseStep 800837 = 150157) (by norm_num)
theorem B571465 : Blo 531801 571465 := bbase (se 2 (by rfl) ⟨214299, by rfl⟩ : syracuseStep 571465 = 428599) (by norm_num)
theorem B800861 : Blo 531801 800861 := bbase (se 3 (by rfl) ⟨150161, by rfl⟩ : syracuseStep 800861 = 300323) (by norm_num)
theorem B800885 : Blo 531801 800885 := bbase (se 5 (by rfl) ⟨37541, by rfl⟩ : syracuseStep 800885 = 75083) (by norm_num)
theorem B1620101 : Blo 531801 1620101 := bbase (se 4 (by rfl) ⟨151884, by rfl⟩ : syracuseStep 1620101 = 303769) (by norm_num)
theorem B800909 : Blo 531801 800909 := bbase (se 3 (by rfl) ⟨150170, by rfl⟩ : syracuseStep 800909 = 300341) (by norm_num)
theorem B899221 : Blo 531801 899221 := bbase (se 6 (by rfl) ⟨21075, by rfl⟩ : syracuseStep 899221 = 42151) (by norm_num)
theorem B800933 : Blo 531801 800933 := bbase (se 4 (by rfl) ⟨75087, by rfl⟩ : syracuseStep 800933 = 150175) (by norm_num)
theorem B800957 : Blo 531801 800957 := bbase (se 3 (by rfl) ⟨150179, by rfl⟩ : syracuseStep 800957 = 300359) (by norm_num)
theorem B800981 : Blo 531801 800981 := bbase (se 7 (by rfl) ⟨9386, by rfl⟩ : syracuseStep 800981 = 18773) (by norm_num)
theorem B899309 : Blo 531801 899309 := bbase (se 3 (by rfl) ⟨168620, by rfl⟩ : syracuseStep 899309 = 337241) (by norm_num)
theorem B801005 : Blo 531801 801005 := bbase (se 3 (by rfl) ⟨150188, by rfl⟩ : syracuseStep 801005 = 300377) (by norm_num)
theorem B3258613 : Blo 531801 3258613 := bbase (se 5 (by rfl) ⟨152747, by rfl⟩ : syracuseStep 3258613 = 305495) (by norm_num)
theorem B801029 : Blo 531801 801029 := bbase (se 4 (by rfl) ⟨75096, by rfl⟩ : syracuseStep 801029 = 150193) (by norm_num)
theorem B801053 : Blo 531801 801053 := bbase (se 3 (by rfl) ⟨150197, by rfl⟩ : syracuseStep 801053 = 300395) (by norm_num)
theorem B801077 : Blo 531801 801077 := bbase (se 5 (by rfl) ⟨37550, by rfl⟩ : syracuseStep 801077 = 75101) (by norm_num)
theorem B866621 : Blo 531801 866621 := bbase (se 3 (by rfl) ⟨162491, by rfl⟩ : syracuseStep 866621 = 324983) (by norm_num)
theorem B801101 : Blo 531801 801101 := bbase (se 3 (by rfl) ⟨150206, by rfl⟩ : syracuseStep 801101 = 300413) (by norm_num)
theorem B801125 : Blo 531801 801125 := bbase (se 4 (by rfl) ⟨75105, by rfl⟩ : syracuseStep 801125 = 150211) (by norm_num)
theorem B899437 : Blo 531801 899437 := bbase (se 3 (by rfl) ⟨168644, by rfl⟩ : syracuseStep 899437 = 337289) (by norm_num)
theorem B801149 : Blo 531801 801149 := bbase (se 3 (by rfl) ⟨150215, by rfl⟩ : syracuseStep 801149 = 300431) (by norm_num)
theorem B801173 : Blo 531801 801173 := bbase (se 6 (by rfl) ⟨18777, by rfl⟩ : syracuseStep 801173 = 37555) (by norm_num)
theorem B768413 : Blo 531801 768413 := bbase (se 3 (by rfl) ⟨144077, by rfl⟩ : syracuseStep 768413 = 288155) (by norm_num)
theorem B801197 : Blo 531801 801197 := bbase (se 3 (by rfl) ⟨150224, by rfl⟩ : syracuseStep 801197 = 300449) (by norm_num)
theorem B899525 : Blo 531801 899525 := bbase (se 4 (by rfl) ⟨84330, by rfl⟩ : syracuseStep 899525 = 168661) (by norm_num)
theorem B801221 : Blo 531801 801221 := bbase (se 4 (by rfl) ⟨75114, by rfl⟩ : syracuseStep 801221 = 150229) (by norm_num)
theorem B801245 : Blo 531801 801245 := bbase (se 3 (by rfl) ⟨150233, by rfl⟩ : syracuseStep 801245 = 300467) (by norm_num)
theorem B801269 : Blo 531801 801269 := bbase (se 5 (by rfl) ⟨37559, by rfl⟩ : syracuseStep 801269 = 75119) (by norm_num)
theorem B539129 : Blo 531801 539129 := bbase (se 2 (by rfl) ⟨202173, by rfl⟩ : syracuseStep 539129 = 404347) (by norm_num)
theorem B571897 : Blo 531801 571897 := bbase (se 2 (by rfl) ⟨214461, by rfl⟩ : syracuseStep 571897 = 428923) (by norm_num)
theorem B801293 : Blo 531801 801293 := bbase (se 3 (by rfl) ⟨150242, by rfl⟩ : syracuseStep 801293 = 300485) (by norm_num)
theorem B539161 : Blo 531801 539161 := bbase (se 2 (by rfl) ⟨202185, by rfl⟩ : syracuseStep 539161 = 404371) (by norm_num)
theorem B801317 : Blo 531801 801317 := bbase (se 4 (by rfl) ⟨75123, by rfl⟩ : syracuseStep 801317 = 150247) (by norm_num)
theorem B801341 : Blo 531801 801341 := bbase (se 3 (by rfl) ⟨150251, by rfl⟩ : syracuseStep 801341 = 300503) (by norm_num)
theorem B571969 : Blo 531801 571969 := bbase (se 2 (by rfl) ⟨214488, by rfl⟩ : syracuseStep 571969 = 428977) (by norm_num)
theorem B899653 : Blo 531801 899653 := bbase (se 4 (by rfl) ⟨84342, by rfl⟩ : syracuseStep 899653 = 168685) (by norm_num)
theorem B801365 : Blo 531801 801365 := bbase (se 8 (by rfl) ⟨4695, by rfl⟩ : syracuseStep 801365 = 9391) (by norm_num)
theorem B801389 : Blo 531801 801389 := bbase (se 3 (by rfl) ⟨150260, by rfl⟩ : syracuseStep 801389 = 300521) (by norm_num)
theorem B1096325 : Blo 531801 1096325 := bbase (se 4 (by rfl) ⟨102780, by rfl⟩ : syracuseStep 1096325 = 205561) (by norm_num)
theorem B801413 : Blo 531801 801413 := bbase (se 4 (by rfl) ⟨75132, by rfl⟩ : syracuseStep 801413 = 150265) (by norm_num)
theorem B899741 : Blo 531801 899741 := bbase (se 3 (by rfl) ⟨168701, by rfl⟩ : syracuseStep 899741 = 337403) (by norm_num)
theorem B801437 : Blo 531801 801437 := bbase (se 3 (by rfl) ⟨150269, by rfl⟩ : syracuseStep 801437 = 300539) (by norm_num)
theorem B965285 : Blo 531801 965285 := bbase (se 4 (by rfl) ⟨90495, by rfl⟩ : syracuseStep 965285 = 180991) (by norm_num)
theorem B801461 : Blo 531801 801461 := bbase (se 5 (by rfl) ⟨37568, by rfl⟩ : syracuseStep 801461 = 75137) (by norm_num)
theorem B801485 : Blo 531801 801485 := bbase (se 3 (by rfl) ⟨150278, by rfl⟩ : syracuseStep 801485 = 300557) (by norm_num)
theorem B801509 : Blo 531801 801509 := bbase (se 4 (by rfl) ⟨75141, by rfl⟩ : syracuseStep 801509 = 150283) (by norm_num)
theorem B801533 : Blo 531801 801533 := bbase (se 3 (by rfl) ⟨150287, by rfl⟩ : syracuseStep 801533 = 300575) (by norm_num)
theorem B801557 : Blo 531801 801557 := bbase (se 6 (by rfl) ⟨18786, by rfl⟩ : syracuseStep 801557 = 37573) (by norm_num)
theorem B899869 : Blo 531801 899869 := bbase (se 3 (by rfl) ⟨168725, by rfl⟩ : syracuseStep 899869 = 337451) (by norm_num)
theorem B801581 : Blo 531801 801581 := bbase (se 3 (by rfl) ⟨150296, by rfl⟩ : syracuseStep 801581 = 300593) (by norm_num)
theorem B965429 : Blo 531801 965429 := bbase (se 5 (by rfl) ⟨45254, by rfl⟩ : syracuseStep 965429 = 90509) (by norm_num)
theorem B801605 : Blo 531801 801605 := bbase (se 4 (by rfl) ⟨75150, by rfl⟩ : syracuseStep 801605 = 150301) (by norm_num)
theorem B801629 : Blo 531801 801629 := bbase (se 3 (by rfl) ⟨150305, by rfl⟩ : syracuseStep 801629 = 300611) (by norm_num)
theorem B899957 : Blo 531801 899957 := bbase (se 5 (by rfl) ⟨42185, by rfl⟩ : syracuseStep 899957 = 84371) (by norm_num)
theorem B801653 : Blo 531801 801653 := bbase (se 5 (by rfl) ⟨37577, by rfl⟩ : syracuseStep 801653 = 75155) (by norm_num)
theorem B801677 : Blo 531801 801677 := bbase (se 3 (by rfl) ⟨150314, by rfl⟩ : syracuseStep 801677 = 300629) (by norm_num)
theorem B801701 : Blo 531801 801701 := bbase (se 4 (by rfl) ⟨75159, by rfl⟩ : syracuseStep 801701 = 150319) (by norm_num)
theorem B1522597 : Blo 531801 1522597 := bbase (se 4 (by rfl) ⟨142743, by rfl⟩ : syracuseStep 1522597 = 285487) (by norm_num)
theorem B801725 : Blo 531801 801725 := bbase (se 3 (by rfl) ⟨150323, by rfl⟩ : syracuseStep 801725 = 300647) (by norm_num)
theorem B801749 : Blo 531801 801749 := bbase (se 7 (by rfl) ⟨9395, by rfl⟩ : syracuseStep 801749 = 18791) (by norm_num)
theorem B801773 : Blo 531801 801773 := bbase (se 3 (by rfl) ⟨150332, by rfl⟩ : syracuseStep 801773 = 300665) (by norm_num)
theorem B900085 : Blo 531801 900085 := bbase (se 5 (by rfl) ⟨42191, by rfl⟩ : syracuseStep 900085 = 84383) (by norm_num)
theorem B801797 : Blo 531801 801797 := bbase (se 4 (by rfl) ⟨75168, by rfl⟩ : syracuseStep 801797 = 150337) (by norm_num)
theorem B801821 : Blo 531801 801821 := bbase (se 3 (by rfl) ⟨150341, by rfl⟩ : syracuseStep 801821 = 300683) (by norm_num)
theorem B801845 : Blo 531801 801845 := bbase (se 5 (by rfl) ⟨37586, by rfl⟩ : syracuseStep 801845 = 75173) (by norm_num)
theorem B900173 : Blo 531801 900173 := bbase (se 3 (by rfl) ⟨168782, by rfl⟩ : syracuseStep 900173 = 337565) (by norm_num)
theorem B801869 : Blo 531801 801869 := bbase (se 3 (by rfl) ⟨150350, by rfl⟩ : syracuseStep 801869 = 300701) (by norm_num)
theorem B15416405 : Blo 531801 15416405 := bbase (se 8 (by rfl) ⟨90330, by rfl⟩ : syracuseStep 15416405 = 180661) (by norm_num)
theorem B801893 : Blo 531801 801893 := bbase (se 4 (by rfl) ⟨75177, by rfl⟩ : syracuseStep 801893 = 150355) (by norm_num)
theorem B801917 : Blo 531801 801917 := bbase (se 3 (by rfl) ⟨150359, by rfl⟩ : syracuseStep 801917 = 300719) (by norm_num)
theorem B801941 : Blo 531801 801941 := bbase (se 6 (by rfl) ⟨18795, by rfl⟩ : syracuseStep 801941 = 37591) (by norm_num)
theorem B801965 : Blo 531801 801965 := bbase (se 3 (by rfl) ⟨150368, by rfl⟩ : syracuseStep 801965 = 300737) (by norm_num)
theorem B801989 : Blo 531801 801989 := bbase (se 4 (by rfl) ⟨75186, by rfl⟩ : syracuseStep 801989 = 150373) (by norm_num)
theorem B900301 : Blo 531801 900301 := bbase (se 3 (by rfl) ⟨168806, by rfl⟩ : syracuseStep 900301 = 337613) (by norm_num)
theorem B802013 : Blo 531801 802013 := bbase (se 3 (by rfl) ⟨150377, by rfl⟩ : syracuseStep 802013 = 300755) (by norm_num)
theorem B802037 : Blo 531801 802037 := bbase (se 5 (by rfl) ⟨37595, by rfl⟩ : syracuseStep 802037 = 75191) (by norm_num)
theorem B802061 : Blo 531801 802061 := bbase (se 3 (by rfl) ⟨150386, by rfl⟩ : syracuseStep 802061 = 300773) (by norm_num)
theorem B900389 : Blo 531801 900389 := bbase (se 4 (by rfl) ⟨84411, by rfl⟩ : syracuseStep 900389 = 168823) (by norm_num)
theorem B802085 : Blo 531801 802085 := bbase (se 4 (by rfl) ⟨75195, by rfl⟩ : syracuseStep 802085 = 150391) (by norm_num)
theorem B2702645 : Blo 531801 2702645 := bbase (se 5 (by rfl) ⟨126686, by rfl⟩ : syracuseStep 2702645 = 253373) (by norm_num)
theorem B802109 : Blo 531801 802109 := bbase (se 3 (by rfl) ⟨150395, by rfl⟩ : syracuseStep 802109 = 300791) (by norm_num)
theorem B802133 : Blo 531801 802133 := bbase (se 11 (by rfl) ⟨587, by rfl⟩ : syracuseStep 802133 = 1175) (by norm_num)
theorem B802157 : Blo 531801 802157 := bbase (se 3 (by rfl) ⟨150404, by rfl⟩ : syracuseStep 802157 = 300809) (by norm_num)
theorem B802181 : Blo 531801 802181 := bbase (se 4 (by rfl) ⟨75204, by rfl⟩ : syracuseStep 802181 = 150409) (by norm_num)
theorem B769429 : Blo 531801 769429 := bbase (se 6 (by rfl) ⟨18033, by rfl⟩ : syracuseStep 769429 = 36067) (by norm_num)
theorem B802205 : Blo 531801 802205 := bbase (se 3 (by rfl) ⟨150413, by rfl⟩ : syracuseStep 802205 = 300827) (by norm_num)
theorem B1392029 : Blo 531801 1392029 := bbase (se 3 (by rfl) ⟨261005, by rfl⟩ : syracuseStep 1392029 = 522011) (by norm_num)
theorem B900517 : Blo 531801 900517 := bbase (se 4 (by rfl) ⟨84423, by rfl⟩ : syracuseStep 900517 = 168847) (by norm_num)
theorem B802229 : Blo 531801 802229 := bbase (se 5 (by rfl) ⟨37604, by rfl⟩ : syracuseStep 802229 = 75209) (by norm_num)
theorem B802253 : Blo 531801 802253 := bbase (se 3 (by rfl) ⟨150422, by rfl⟩ : syracuseStep 802253 = 300845) (by norm_num)
theorem B802277 : Blo 531801 802277 := bbase (se 4 (by rfl) ⟨75213, by rfl⟩ : syracuseStep 802277 = 150427) (by norm_num)
theorem B900605 : Blo 531801 900605 := bbase (se 3 (by rfl) ⟨168863, by rfl⟩ : syracuseStep 900605 = 337727) (by norm_num)
theorem B802301 : Blo 531801 802301 := bbase (se 3 (by rfl) ⟨150431, by rfl⟩ : syracuseStep 802301 = 300863) (by norm_num)
theorem B802325 : Blo 531801 802325 := bbase (se 6 (by rfl) ⟨18804, by rfl⟩ : syracuseStep 802325 = 37609) (by norm_num)
theorem B802349 : Blo 531801 802349 := bbase (se 3 (by rfl) ⟨150440, by rfl⟩ : syracuseStep 802349 = 300881) (by norm_num)
theorem B802373 : Blo 531801 802373 := bbase (se 4 (by rfl) ⟨75222, by rfl⟩ : syracuseStep 802373 = 150445) (by norm_num)
theorem B802397 : Blo 531801 802397 := bbase (se 3 (by rfl) ⟨150449, by rfl⟩ : syracuseStep 802397 = 300899) (by norm_num)
theorem B802421 : Blo 531801 802421 := bbase (se 5 (by rfl) ⟨37613, by rfl⟩ : syracuseStep 802421 = 75227) (by norm_num)
theorem B900733 : Blo 531801 900733 := bbase (se 3 (by rfl) ⟨168887, by rfl⟩ : syracuseStep 900733 = 337775) (by norm_num)
theorem B802445 : Blo 531801 802445 := bbase (se 3 (by rfl) ⟨150458, by rfl⟩ : syracuseStep 802445 = 300917) (by norm_num)
theorem B540313 : Blo 531801 540313 := bbase (se 2 (by rfl) ⟨202617, by rfl⟩ : syracuseStep 540313 = 405235) (by norm_num)
theorem B802469 : Blo 531801 802469 := bbase (se 4 (by rfl) ⟨75231, by rfl⟩ : syracuseStep 802469 = 150463) (by norm_num)
theorem B802493 : Blo 531801 802493 := bbase (se 3 (by rfl) ⟨150467, by rfl⟩ : syracuseStep 802493 = 300935) (by norm_num)
theorem B900821 : Blo 531801 900821 := bbase (se 7 (by rfl) ⟨10556, by rfl⟩ : syracuseStep 900821 = 21113) (by norm_num)
theorem B802517 : Blo 531801 802517 := bbase (se 7 (by rfl) ⟨9404, by rfl⟩ : syracuseStep 802517 = 18809) (by norm_num)
theorem B802541 : Blo 531801 802541 := bbase (se 3 (by rfl) ⟨150476, by rfl⟩ : syracuseStep 802541 = 300953) (by norm_num)
theorem B802565 : Blo 531801 802565 := bbase (se 4 (by rfl) ⟨75240, by rfl⟩ : syracuseStep 802565 = 150481) (by norm_num)
theorem B802589 : Blo 531801 802589 := bbase (se 3 (by rfl) ⟨150485, by rfl⟩ : syracuseStep 802589 = 300971) (by norm_num)
theorem B802613 : Blo 531801 802613 := bbase (se 5 (by rfl) ⟨37622, by rfl⟩ : syracuseStep 802613 = 75245) (by norm_num)
theorem B802637 : Blo 531801 802637 := bbase (se 3 (by rfl) ⟨150494, by rfl⟩ : syracuseStep 802637 = 300989) (by norm_num)
theorem B900949 : Blo 531801 900949 := bbase (se 9 (by rfl) ⟨2639, by rfl⟩ : syracuseStep 900949 = 5279) (by norm_num)
theorem B802661 : Blo 531801 802661 := bbase (se 4 (by rfl) ⟨75249, by rfl⟩ : syracuseStep 802661 = 150499) (by norm_num)
theorem B802685 : Blo 531801 802685 := bbase (se 3 (by rfl) ⟨150503, by rfl⟩ : syracuseStep 802685 = 301007) (by norm_num)
theorem B802709 : Blo 531801 802709 := bbase (se 6 (by rfl) ⟨18813, by rfl⟩ : syracuseStep 802709 = 37627) (by norm_num)
theorem B540589 : Blo 531801 540589 := bbase (se 3 (by rfl) ⟨101360, by rfl⟩ : syracuseStep 540589 = 202721) (by norm_num)
theorem B901037 : Blo 531801 901037 := bbase (se 3 (by rfl) ⟨168944, by rfl⟩ : syracuseStep 901037 = 337889) (by norm_num)
theorem B802733 : Blo 531801 802733 := bbase (se 3 (by rfl) ⟨150512, by rfl⟩ : syracuseStep 802733 = 301025) (by norm_num)
theorem B802757 : Blo 531801 802757 := bbase (se 4 (by rfl) ⟨75258, by rfl⟩ : syracuseStep 802757 = 150517) (by norm_num)
theorem B638929 : Blo 531801 638929 := bbase (se 2 (by rfl) ⟨239598, by rfl⟩ : syracuseStep 638929 = 479197) (by norm_num)
theorem B540629 : Blo 531801 540629 := bbase (se 7 (by rfl) ⟨6335, by rfl⟩ : syracuseStep 540629 = 12671) (by norm_num)
theorem B802781 : Blo 531801 802781 := bbase (se 3 (by rfl) ⟨150521, by rfl⟩ : syracuseStep 802781 = 301043) (by norm_num)
theorem B770029 : Blo 531801 770029 := bbase (se 3 (by rfl) ⟨144380, by rfl⟩ : syracuseStep 770029 = 288761) (by norm_num)
theorem B1523701 : Blo 531801 1523701 := bbase (se 5 (by rfl) ⟨71423, by rfl⟩ : syracuseStep 1523701 = 142847) (by norm_num)
theorem B802805 : Blo 531801 802805 := bbase (se 5 (by rfl) ⟨37631, by rfl⟩ : syracuseStep 802805 = 75263) (by norm_num)
theorem B802829 : Blo 531801 802829 := bbase (se 3 (by rfl) ⟨150530, by rfl⟩ : syracuseStep 802829 = 301061) (by norm_num)
theorem B802853 : Blo 531801 802853 := bbase (se 4 (by rfl) ⟨75267, by rfl⟩ : syracuseStep 802853 = 150535) (by norm_num)
theorem B901165 : Blo 531801 901165 := bbase (se 3 (by rfl) ⟨168968, by rfl⟩ : syracuseStep 901165 = 337937) (by norm_num)
theorem B802877 : Blo 531801 802877 := bbase (se 3 (by rfl) ⟨150539, by rfl⟩ : syracuseStep 802877 = 301079) (by norm_num)
theorem B802901 : Blo 531801 802901 := bbase (se 8 (by rfl) ⟨4704, by rfl⟩ : syracuseStep 802901 = 9409) (by norm_num)
theorem B802925 : Blo 531801 802925 := bbase (se 3 (by rfl) ⟨150548, by rfl⟩ : syracuseStep 802925 = 301097) (by norm_num)
theorem B901253 : Blo 531801 901253 := bbase (se 4 (by rfl) ⟨84492, by rfl⟩ : syracuseStep 901253 = 168985) (by norm_num)
theorem B802949 : Blo 531801 802949 := bbase (se 4 (by rfl) ⟨75276, by rfl⟩ : syracuseStep 802949 = 150553) (by norm_num)
theorem B802973 : Blo 531801 802973 := bbase (se 3 (by rfl) ⟨150557, by rfl⟩ : syracuseStep 802973 = 301115) (by norm_num)
theorem B2277557 : Blo 531801 2277557 := bbase (se 5 (by rfl) ⟨106760, by rfl⟩ : syracuseStep 2277557 = 213521) (by norm_num)
theorem B802997 : Blo 531801 802997 := bbase (se 5 (by rfl) ⟨37640, by rfl⟩ : syracuseStep 802997 = 75281) (by norm_num)
theorem B803021 : Blo 531801 803021 := bbase (se 3 (by rfl) ⟨150566, by rfl⟩ : syracuseStep 803021 = 301133) (by norm_num)
theorem B803045 : Blo 531801 803045 := bbase (se 4 (by rfl) ⟨75285, by rfl⟩ : syracuseStep 803045 = 150571) (by norm_num)
theorem B540913 : Blo 531801 540913 := bbase (se 2 (by rfl) ⟨202842, by rfl⟩ : syracuseStep 540913 = 405685) (by norm_num)
theorem B803069 : Blo 531801 803069 := bbase (se 3 (by rfl) ⟨150575, by rfl⟩ : syracuseStep 803069 = 301151) (by norm_num)
theorem B901381 : Blo 531801 901381 := bbase (se 4 (by rfl) ⟨84504, by rfl⟩ : syracuseStep 901381 = 169009) (by norm_num)
theorem B803093 : Blo 531801 803093 := bbase (se 6 (by rfl) ⟨18822, by rfl⟩ : syracuseStep 803093 = 37645) (by norm_num)
theorem B803117 : Blo 531801 803117 := bbase (se 3 (by rfl) ⟨150584, by rfl⟩ : syracuseStep 803117 = 301169) (by norm_num)
theorem B803141 : Blo 531801 803141 := bbase (se 4 (by rfl) ⟨75294, by rfl⟩ : syracuseStep 803141 = 150589) (by norm_num)
theorem B901469 : Blo 531801 901469 := bbase (se 3 (by rfl) ⟨169025, by rfl⟩ : syracuseStep 901469 = 338051) (by norm_num)
theorem B803165 : Blo 531801 803165 := bbase (se 3 (by rfl) ⟨150593, by rfl⟩ : syracuseStep 803165 = 301187) (by norm_num)
theorem B803189 : Blo 531801 803189 := bbase (se 5 (by rfl) ⟨37649, by rfl⟩ : syracuseStep 803189 = 75299) (by norm_num)
theorem B803213 : Blo 531801 803213 := bbase (se 3 (by rfl) ⟨150602, by rfl⟩ : syracuseStep 803213 = 301205) (by norm_num)
theorem B803237 : Blo 531801 803237 := bbase (se 4 (by rfl) ⟨75303, by rfl⟩ : syracuseStep 803237 = 150607) (by norm_num)
theorem B803261 : Blo 531801 803261 := bbase (se 3 (by rfl) ⟨150611, by rfl⟩ : syracuseStep 803261 = 301223) (by norm_num)
theorem B10961365 : Blo 531801 10961365 := bbase (se 7 (by rfl) ⟨128453, by rfl⟩ : syracuseStep 10961365 = 256907) (by norm_num)
theorem B803285 : Blo 531801 803285 := bbase (se 7 (by rfl) ⟨9413, by rfl⟩ : syracuseStep 803285 = 18827) (by norm_num)
theorem B606685 : Blo 531801 606685 := bbase (se 3 (by rfl) ⟨113753, by rfl⟩ : syracuseStep 606685 = 227507) (by norm_num)
theorem B901597 : Blo 531801 901597 := bbase (se 3 (by rfl) ⟨169049, by rfl⟩ : syracuseStep 901597 = 338099) (by norm_num)
theorem B803309 : Blo 531801 803309 := bbase (se 3 (by rfl) ⟨150620, by rfl⟩ : syracuseStep 803309 = 301241) (by norm_num)
theorem B803333 : Blo 531801 803333 := bbase (se 4 (by rfl) ⟨75312, by rfl⟩ : syracuseStep 803333 = 150625) (by norm_num)
theorem B803357 : Blo 531801 803357 := bbase (se 3 (by rfl) ⟨150629, by rfl⟩ : syracuseStep 803357 = 301259) (by norm_num)
theorem B901685 : Blo 531801 901685 := bbase (se 5 (by rfl) ⟨42266, by rfl⟩ : syracuseStep 901685 = 84533) (by norm_num)
theorem B803381 : Blo 531801 803381 := bbase (se 5 (by rfl) ⟨37658, by rfl⟩ : syracuseStep 803381 = 75317) (by norm_num)
theorem B770629 : Blo 531801 770629 := bbase (se 4 (by rfl) ⟨72246, by rfl⟩ : syracuseStep 770629 = 144493) (by norm_num)
theorem B2703941 : Blo 531801 2703941 := bbase (se 4 (by rfl) ⟨253494, by rfl⟩ : syracuseStep 2703941 = 506989) (by norm_num)
theorem B2114117 : Blo 531801 2114117 := bbase (se 4 (by rfl) ⟨198198, by rfl⟩ : syracuseStep 2114117 = 396397) (by norm_num)
theorem B1196621 : Blo 531801 1196621 := bbase (se 3 (by rfl) ⟨224366, by rfl⟩ : syracuseStep 1196621 = 448733) (by norm_num)
theorem B803405 : Blo 531801 803405 := bbase (se 3 (by rfl) ⟨150638, by rfl⟩ : syracuseStep 803405 = 301277) (by norm_num)
theorem B803429 : Blo 531801 803429 := bbase (se 4 (by rfl) ⟨75321, by rfl⟩ : syracuseStep 803429 = 150643) (by norm_num)
theorem B803453 : Blo 531801 803453 := bbase (se 3 (by rfl) ⟨150647, by rfl⟩ : syracuseStep 803453 = 301295) (by norm_num)
theorem B1196693 : Blo 531801 1196693 := bbase (se 6 (by rfl) ⟨28047, by rfl⟩ : syracuseStep 1196693 = 56095) (by norm_num)
theorem B803477 : Blo 531801 803477 := bbase (se 6 (by rfl) ⟨18831, by rfl⟩ : syracuseStep 803477 = 37663) (by norm_num)
theorem B803501 : Blo 531801 803501 := bbase (se 3 (by rfl) ⟨150656, by rfl⟩ : syracuseStep 803501 = 301313) (by norm_num)
theorem B901813 : Blo 531801 901813 := bbase (se 5 (by rfl) ⟨42272, by rfl⟩ : syracuseStep 901813 = 84545) (by norm_num)
theorem B803525 : Blo 531801 803525 := bbase (se 4 (by rfl) ⟨75330, by rfl⟩ : syracuseStep 803525 = 150661) (by norm_num)
theorem B1196765 : Blo 531801 1196765 := bbase (se 3 (by rfl) ⟨224393, by rfl⟩ : syracuseStep 1196765 = 448787) (by norm_num)
theorem B803549 : Blo 531801 803549 := bbase (se 3 (by rfl) ⟨150665, by rfl⟩ : syracuseStep 803549 = 301331) (by norm_num)
theorem B803573 : Blo 531801 803573 := bbase (se 5 (by rfl) ⟨37667, by rfl⟩ : syracuseStep 803573 = 75335) (by norm_num)
theorem B901901 : Blo 531801 901901 := bbase (se 3 (by rfl) ⟨169106, by rfl⟩ : syracuseStep 901901 = 338213) (by norm_num)
theorem B803597 : Blo 531801 803597 := bbase (se 3 (by rfl) ⟨150674, by rfl⟩ : syracuseStep 803597 = 301349) (by norm_num)
theorem B1196837 : Blo 531801 1196837 := bbase (se 4 (by rfl) ⟨112203, by rfl⟩ : syracuseStep 1196837 = 224407) (by norm_num)
theorem B803621 : Blo 531801 803621 := bbase (se 4 (by rfl) ⟨75339, by rfl⟩ : syracuseStep 803621 = 150679) (by norm_num)
theorem B639785 : Blo 531801 639785 := bbase (se 2 (by rfl) ⟨239919, by rfl⟩ : syracuseStep 639785 = 479839) (by norm_num)
theorem B803645 : Blo 531801 803645 := bbase (se 3 (by rfl) ⟨150683, by rfl⟩ : syracuseStep 803645 = 301367) (by norm_num)
theorem B803669 : Blo 531801 803669 := bbase (se 9 (by rfl) ⟨2354, by rfl⟩ : syracuseStep 803669 = 4709) (by norm_num)
theorem B1196909 : Blo 531801 1196909 := bbase (se 3 (by rfl) ⟨224420, by rfl⟩ : syracuseStep 1196909 = 448841) (by norm_num)
theorem B803693 : Blo 531801 803693 := bbase (se 3 (by rfl) ⟨150692, by rfl⟩ : syracuseStep 803693 = 301385) (by norm_num)
theorem B902029 : Blo 531801 902029 := bbase (se 3 (by rfl) ⟨169130, by rfl⟩ : syracuseStep 902029 = 338261) (by norm_num)
theorem B1196981 : Blo 531801 1196981 := bbase (se 5 (by rfl) ⟨56108, by rfl⟩ : syracuseStep 1196981 = 112217) (by norm_num)
theorem B902117 : Blo 531801 902117 := bbase (se 4 (by rfl) ⟨84573, by rfl⟩ : syracuseStep 902117 = 169147) (by norm_num)
theorem B1197053 : Blo 531801 1197053 := bbase (se 3 (by rfl) ⟨224447, by rfl⟩ : syracuseStep 1197053 = 448895) (by norm_num)
theorem B1295365 : Blo 531801 1295365 := bbase (se 4 (by rfl) ⟨121440, by rfl⟩ : syracuseStep 1295365 = 242881) (by norm_num)
theorem B4047893 : Blo 531801 4047893 := bbase (se 6 (by rfl) ⟨94872, by rfl⟩ : syracuseStep 4047893 = 189745) (by norm_num)
theorem B1197125 : Blo 531801 1197125 := bbase (se 4 (by rfl) ⟨112230, by rfl⟩ : syracuseStep 1197125 = 224461) (by norm_num)
theorem B607333 : Blo 531801 607333 := bbase (se 4 (by rfl) ⟨56937, by rfl⟩ : syracuseStep 607333 = 113875) (by norm_num)
theorem B902245 : Blo 531801 902245 := bbase (se 4 (by rfl) ⟨84585, by rfl⟩ : syracuseStep 902245 = 169171) (by norm_num)
theorem B1197197 : Blo 531801 1197197 := bbase (se 3 (by rfl) ⟨224474, by rfl⟩ : syracuseStep 1197197 = 448949) (by norm_num)
theorem B2573477 : Blo 531801 2573477 := bbase (se 4 (by rfl) ⟨241263, by rfl⟩ : syracuseStep 2573477 = 482527) (by norm_num)
theorem B902333 : Blo 531801 902333 := bbase (se 3 (by rfl) ⟨169187, by rfl⟩ : syracuseStep 902333 = 338375) (by norm_num)
theorem B771277 : Blo 531801 771277 := bbase (se 3 (by rfl) ⟨144614, by rfl⟩ : syracuseStep 771277 = 289229) (by norm_num)
theorem B1197269 : Blo 531801 1197269 := bbase (se 7 (by rfl) ⟨14030, by rfl⟩ : syracuseStep 1197269 = 28061) (by norm_num)
theorem B2442469 : Blo 531801 2442469 := bbase (se 4 (by rfl) ⟨228981, by rfl⟩ : syracuseStep 2442469 = 457963) (by norm_num)
theorem B1197341 : Blo 531801 1197341 := bbase (se 3 (by rfl) ⟨224501, by rfl⟩ : syracuseStep 1197341 = 449003) (by norm_num)
theorem B2770229 : Blo 531801 2770229 := bbase (se 5 (by rfl) ⟨129854, by rfl⟩ : syracuseStep 2770229 = 259709) (by norm_num)
theorem B902461 : Blo 531801 902461 := bbase (se 3 (by rfl) ⟨169211, by rfl⟩ : syracuseStep 902461 = 338423) (by norm_num)
theorem B673105 : Blo 531801 673105 := bbase (se 2 (by rfl) ⟨252414, by rfl⟩ : syracuseStep 673105 = 504829) (by norm_num)
theorem B1197413 : Blo 531801 1197413 := bbase (se 4 (by rfl) ⟨112257, by rfl⟩ : syracuseStep 1197413 = 224515) (by norm_num)
theorem B542057 : Blo 531801 542057 := bbase (se 2 (by rfl) ⟨203271, by rfl⟩ : syracuseStep 542057 = 406543) (by norm_num)
theorem B902549 : Blo 531801 902549 := bbase (se 6 (by rfl) ⟨21153, by rfl⟩ : syracuseStep 902549 = 42307) (by norm_num)
theorem B1197485 : Blo 531801 1197485 := bbase (se 3 (by rfl) ⟨224528, by rfl⟩ : syracuseStep 1197485 = 449057) (by norm_num)
theorem B673201 : Blo 531801 673201 := bbase (se 2 (by rfl) ⟨252450, by rfl⟩ : syracuseStep 673201 = 504901) (by norm_num)
theorem B1525205 : Blo 531801 1525205 := bbase (se 7 (by rfl) ⟨17873, by rfl⟩ : syracuseStep 1525205 = 35747) (by norm_num)
theorem B1197557 : Blo 531801 1197557 := bbase (se 5 (by rfl) ⟨56135, by rfl⟩ : syracuseStep 1197557 = 112271) (by norm_num)
theorem B640505 : Blo 531801 640505 := bbase (se 2 (by rfl) ⟨240189, by rfl⟩ : syracuseStep 640505 = 480379) (by norm_num)
theorem B902677 : Blo 531801 902677 := bbase (se 6 (by rfl) ⟨21156, by rfl⟩ : syracuseStep 902677 = 42313) (by norm_num)
theorem B1197629 : Blo 531801 1197629 := bbase (se 3 (by rfl) ⟨224555, by rfl⟩ : syracuseStep 1197629 = 449111) (by norm_num)
theorem B26297941 : Blo 531801 26297941 := bbase (se 8 (by rfl) ⟨154089, by rfl⟩ : syracuseStep 26297941 = 308179) (by norm_num)
theorem B2475605 : Blo 531801 2475605 := bbase (se 8 (by rfl) ⟨14505, by rfl⟩ : syracuseStep 2475605 = 29011) (by norm_num)
theorem B673373 : Blo 531801 673373 := bbase (se 3 (by rfl) ⟨126257, by rfl⟩ : syracuseStep 673373 = 252515) (by norm_num)
theorem B902765 : Blo 531801 902765 := bbase (se 3 (by rfl) ⟨169268, by rfl⟩ : syracuseStep 902765 = 338537) (by norm_num)
theorem B1197701 : Blo 531801 1197701 := bbase (se 4 (by rfl) ⟨112284, by rfl⟩ : syracuseStep 1197701 = 224569) (by norm_num)
theorem B673429 : Blo 531801 673429 := bbase (se 6 (by rfl) ⟨15783, by rfl⟩ : syracuseStep 673429 = 31567) (by norm_num)
theorem B1197773 : Blo 531801 1197773 := bbase (se 3 (by rfl) ⟨224582, by rfl⟩ : syracuseStep 1197773 = 449165) (by norm_num)
theorem B902893 : Blo 531801 902893 := bbase (se 3 (by rfl) ⟨169292, by rfl⟩ : syracuseStep 902893 = 338585) (by norm_num)
theorem B673525 : Blo 531801 673525 := bbase (se 5 (by rfl) ⟨31571, by rfl⟩ : syracuseStep 673525 = 63143) (by norm_num)
theorem B2443013 : Blo 531801 2443013 := bbase (se 4 (by rfl) ⟨229032, by rfl⟩ : syracuseStep 2443013 = 458065) (by norm_num)
theorem B1197845 : Blo 531801 1197845 := bbase (se 6 (by rfl) ⟨28074, by rfl⟩ : syracuseStep 1197845 = 56149) (by norm_num)
theorem B640813 : Blo 531801 640813 := bbase (se 3 (by rfl) ⟨120152, by rfl⟩ : syracuseStep 640813 = 240305) (by norm_num)
theorem B902981 : Blo 531801 902981 := bbase (se 4 (by rfl) ⟨84654, by rfl⟩ : syracuseStep 902981 = 169309) (by norm_num)
theorem B2705237 : Blo 531801 2705237 := bbase (se 9 (by rfl) ⟨7925, by rfl⟩ : syracuseStep 2705237 = 15851) (by norm_num)
theorem B1197917 : Blo 531801 1197917 := bbase (se 3 (by rfl) ⟨224609, by rfl⟩ : syracuseStep 1197917 = 449219) (by norm_num)
theorem B640909 : Blo 531801 640909 := bbase (se 3 (by rfl) ⟨120170, by rfl⟩ : syracuseStep 640909 = 240341) (by norm_num)
theorem B673697 : Blo 531801 673697 := bbase (se 2 (by rfl) ⟨252636, by rfl⟩ : syracuseStep 673697 = 505273) (by norm_num)
theorem B1197989 : Blo 531801 1197989 := bbase (se 4 (by rfl) ⟨112311, by rfl⟩ : syracuseStep 1197989 = 224623) (by norm_num)
theorem B2279333 : Blo 531801 2279333 := bbase (se 4 (by rfl) ⟨213687, by rfl⟩ : syracuseStep 2279333 = 427375) (by norm_num)
theorem B903109 : Blo 531801 903109 := bbase (se 4 (by rfl) ⟨84666, by rfl⟩ : syracuseStep 903109 = 169333) (by norm_num)
theorem B673753 : Blo 531801 673753 := bbase (se 2 (by rfl) ⟨252657, by rfl⟩ : syracuseStep 673753 = 505315) (by norm_num)
theorem B1198061 : Blo 531801 1198061 := bbase (se 3 (by rfl) ⟨224636, by rfl⟩ : syracuseStep 1198061 = 449273) (by norm_num)
theorem B542705 : Blo 531801 542705 := bbase (se 2 (by rfl) ⟨203514, by rfl⟩ : syracuseStep 542705 = 407029) (by norm_num)
theorem B641053 : Blo 531801 641053 := bbase (se 3 (by rfl) ⟨120197, by rfl⟩ : syracuseStep 641053 = 240395) (by norm_num)
theorem B903197 : Blo 531801 903197 := bbase (se 3 (by rfl) ⟨169349, by rfl⟩ : syracuseStep 903197 = 338699) (by norm_num)
theorem B1198133 : Blo 531801 1198133 := bbase (se 5 (by rfl) ⟨56162, by rfl⟩ : syracuseStep 1198133 = 112325) (by norm_num)
theorem B3655733 : Blo 531801 3655733 := bbase (se 5 (by rfl) ⟨171362, by rfl⟩ : syracuseStep 3655733 = 342725) (by norm_num)
theorem B673849 : Blo 531801 673849 := bbase (se 2 (by rfl) ⟨252693, by rfl⟩ : syracuseStep 673849 = 505387) (by norm_num)
theorem B1198205 : Blo 531801 1198205 := bbase (se 3 (by rfl) ⟨224663, by rfl⟩ : syracuseStep 1198205 = 449327) (by norm_num)
theorem B1099909 : Blo 531801 1099909 := bbase (se 4 (by rfl) ⟨103116, by rfl⟩ : syracuseStep 1099909 = 206233) (by norm_num)
theorem B2279573 : Blo 531801 2279573 := bbase (se 6 (by rfl) ⟨53427, by rfl⟩ : syracuseStep 2279573 = 106855) (by norm_num)
theorem B903325 : Blo 531801 903325 := bbase (se 3 (by rfl) ⟨169373, by rfl⟩ : syracuseStep 903325 = 338747) (by norm_num)
theorem B1198277 : Blo 531801 1198277 := bbase (se 4 (by rfl) ⟨112338, by rfl⟩ : syracuseStep 1198277 = 224677) (by norm_num)
theorem B674021 : Blo 531801 674021 := bbase (se 4 (by rfl) ⟨63189, by rfl⟩ : syracuseStep 674021 = 126379) (by norm_num)
theorem B542953 : Blo 531801 542953 := bbase (se 2 (by rfl) ⟨203607, by rfl⟩ : syracuseStep 542953 = 407215) (by norm_num)
theorem B903413 : Blo 531801 903413 := bbase (se 5 (by rfl) ⟨42347, by rfl⟩ : syracuseStep 903413 = 84695) (by norm_num)
theorem B1198349 : Blo 531801 1198349 := bbase (se 3 (by rfl) ⟨224690, by rfl⟩ : syracuseStep 1198349 = 449381) (by norm_num)
theorem B674077 : Blo 531801 674077 := bbase (se 3 (by rfl) ⟨126389, by rfl⟩ : syracuseStep 674077 = 252779) (by norm_num)
theorem B1198421 : Blo 531801 1198421 := bbase (se 10 (by rfl) ⟨1755, by rfl⟩ : syracuseStep 1198421 = 3511) (by norm_num)
theorem B903541 : Blo 531801 903541 := bbase (se 5 (by rfl) ⟨42353, by rfl⟩ : syracuseStep 903541 = 84707) (by norm_num)
theorem B674173 : Blo 531801 674173 := bbase (se 3 (by rfl) ⟨126407, by rfl⟩ : syracuseStep 674173 = 252815) (by norm_num)
theorem B1198493 : Blo 531801 1198493 := bbase (se 3 (by rfl) ⟨224717, by rfl⟩ : syracuseStep 1198493 = 449435) (by norm_num)
theorem B903629 : Blo 531801 903629 := bbase (se 3 (by rfl) ⟨169430, by rfl⟩ : syracuseStep 903629 = 338861) (by norm_num)
theorem B1198565 : Blo 531801 1198565 := bbase (se 4 (by rfl) ⟨112365, by rfl⟩ : syracuseStep 1198565 = 224731) (by norm_num)
theorem B674345 : Blo 531801 674345 := bbase (se 2 (by rfl) ⟨252879, by rfl⟩ : syracuseStep 674345 = 505759) (by norm_num)
theorem B1198637 : Blo 531801 1198637 := bbase (se 3 (by rfl) ⟨224744, by rfl⟩ : syracuseStep 1198637 = 449489) (by norm_num)
theorem B903757 : Blo 531801 903757 := bbase (se 3 (by rfl) ⟨169454, by rfl⟩ : syracuseStep 903757 = 338909) (by norm_num)
theorem B674401 : Blo 531801 674401 := bbase (se 2 (by rfl) ⟨252900, by rfl⟩ : syracuseStep 674401 = 505801) (by norm_num)
theorem B1198709 : Blo 531801 1198709 := bbase (se 5 (by rfl) ⟨56189, by rfl⟩ : syracuseStep 1198709 = 112379) (by norm_num)
theorem B903845 : Blo 531801 903845 := bbase (se 4 (by rfl) ⟨84735, by rfl⟩ : syracuseStep 903845 = 169471) (by norm_num)
theorem B1198781 : Blo 531801 1198781 := bbase (se 3 (by rfl) ⟨224771, by rfl⟩ : syracuseStep 1198781 = 449543) (by norm_num)
theorem B674497 : Blo 531801 674497 := bbase (se 2 (by rfl) ⟨252936, by rfl⟩ : syracuseStep 674497 = 505873) (by norm_num)
theorem B1854181 : Blo 531801 1854181 := bbase (se 4 (by rfl) ⟨173829, by rfl⟩ : syracuseStep 1854181 = 347659) (by norm_num)
theorem B1198853 : Blo 531801 1198853 := bbase (se 4 (by rfl) ⟨112392, by rfl⟩ : syracuseStep 1198853 = 224785) (by norm_num)
theorem B903973 : Blo 531801 903973 := bbase (se 4 (by rfl) ⟨84747, by rfl⟩ : syracuseStep 903973 = 169495) (by norm_num)
theorem B5327669 : Blo 531801 5327669 := bbase (se 5 (by rfl) ⟨249734, by rfl⟩ : syracuseStep 5327669 = 499469) (by norm_num)
theorem B1198925 : Blo 531801 1198925 := bbase (se 3 (by rfl) ⟨224798, by rfl⟩ : syracuseStep 1198925 = 449597) (by norm_num)
theorem B674669 : Blo 531801 674669 := bbase (se 3 (by rfl) ⟨126500, by rfl⟩ : syracuseStep 674669 = 253001) (by norm_num)
theorem B904061 : Blo 531801 904061 := bbase (se 3 (by rfl) ⟨169511, by rfl⟩ : syracuseStep 904061 = 339023) (by norm_num)
theorem B1198997 : Blo 531801 1198997 := bbase (se 6 (by rfl) ⟨28101, by rfl⟩ : syracuseStep 1198997 = 56203) (by norm_num)
theorem B674725 : Blo 531801 674725 := bbase (se 4 (by rfl) ⟨63255, by rfl⟩ : syracuseStep 674725 = 126511) (by norm_num)
theorem B1199069 : Blo 531801 1199069 := bbase (se 3 (by rfl) ⟨224825, by rfl⟩ : syracuseStep 1199069 = 449651) (by norm_num)
theorem B674821 : Blo 531801 674821 := bbase (se 4 (by rfl) ⟨63264, by rfl⟩ : syracuseStep 674821 = 126529) (by norm_num)
theorem B642053 : Blo 531801 642053 := bbase (se 4 (by rfl) ⟨60192, by rfl⟩ : syracuseStep 642053 = 120385) (by norm_num)
theorem B1199141 : Blo 531801 1199141 := bbase (se 4 (by rfl) ⟨112419, by rfl⟩ : syracuseStep 1199141 = 224839) (by norm_num)
theorem B2706533 : Blo 531801 2706533 := bbase (se 4 (by rfl) ⟨253737, by rfl⟩ : syracuseStep 2706533 = 507475) (by norm_num)
theorem B1199213 : Blo 531801 1199213 := bbase (se 3 (by rfl) ⟨224852, by rfl⟩ : syracuseStep 1199213 = 449705) (by norm_num)
theorem B674993 : Blo 531801 674993 := bbase (se 2 (by rfl) ⟨253122, by rfl⟩ : syracuseStep 674993 = 506245) (by norm_num)
theorem B1199285 : Blo 531801 1199285 := bbase (se 5 (by rfl) ⟨56216, by rfl⟩ : syracuseStep 1199285 = 112433) (by norm_num)
theorem B2608357 : Blo 531801 2608357 := bbase (se 4 (by rfl) ⟨244533, by rfl⟩ : syracuseStep 2608357 = 489067) (by norm_num)
theorem B675049 : Blo 531801 675049 := bbase (se 2 (by rfl) ⟨253143, by rfl⟩ : syracuseStep 675049 = 506287) (by norm_num)
theorem B1199357 : Blo 531801 1199357 := bbase (se 3 (by rfl) ⟨224879, by rfl⟩ : syracuseStep 1199357 = 449759) (by norm_num)
theorem B1920277 : Blo 531801 1920277 := bbase (se 6 (by rfl) ⟨45006, by rfl⟩ : syracuseStep 1920277 = 90013) (by norm_num)
theorem B1199429 : Blo 531801 1199429 := bbase (se 4 (by rfl) ⟨112446, by rfl⟩ : syracuseStep 1199429 = 224893) (by norm_num)
theorem B675145 : Blo 531801 675145 := bbase (se 2 (by rfl) ⟨253179, by rfl⟩ : syracuseStep 675145 = 506359) (by norm_num)
theorem B1199501 : Blo 531801 1199501 := bbase (se 3 (by rfl) ⟨224906, by rfl⟩ : syracuseStep 1199501 = 449813) (by norm_num)
theorem B1199573 : Blo 531801 1199573 := bbase (se 7 (by rfl) ⟨14057, by rfl⟩ : syracuseStep 1199573 = 28115) (by norm_num)
theorem B675317 : Blo 531801 675317 := bbase (se 5 (by rfl) ⟨31655, by rfl⟩ : syracuseStep 675317 = 63311) (by norm_num)
theorem B1199645 : Blo 531801 1199645 := bbase (se 3 (by rfl) ⟨224933, by rfl⟩ : syracuseStep 1199645 = 449867) (by norm_num)
theorem B675373 : Blo 531801 675373 := bbase (se 3 (by rfl) ⟨126632, by rfl⟩ : syracuseStep 675373 = 253265) (by norm_num)
theorem B1920581 : Blo 531801 1920581 := bbase (se 4 (by rfl) ⟨180054, by rfl⟩ : syracuseStep 1920581 = 360109) (by norm_num)
theorem B1199717 : Blo 531801 1199717 := bbase (se 4 (by rfl) ⟨112473, by rfl⟩ : syracuseStep 1199717 = 224947) (by norm_num)
theorem B1298045 : Blo 531801 1298045 := bbase (se 3 (by rfl) ⟨243383, by rfl⟩ : syracuseStep 1298045 = 486767) (by norm_num)
theorem B675469 : Blo 531801 675469 := bbase (se 3 (by rfl) ⟨126650, by rfl⟩ : syracuseStep 675469 = 253301) (by norm_num)
theorem B1068701 : Blo 531801 1068701 := bbase (se 3 (by rfl) ⟨200381, by rfl⟩ : syracuseStep 1068701 = 400763) (by norm_num)
theorem B2608805 : Blo 531801 2608805 := bbase (se 4 (by rfl) ⟨244575, by rfl⟩ : syracuseStep 2608805 = 489151) (by norm_num)
theorem B1199789 : Blo 531801 1199789 := bbase (se 3 (by rfl) ⟨224960, by rfl⟩ : syracuseStep 1199789 = 449921) (by norm_num)
theorem B3428021 : Blo 531801 3428021 := bbase (se 5 (by rfl) ⟨160688, by rfl⟩ : syracuseStep 3428021 = 321377) (by norm_num)
theorem B642745 : Blo 531801 642745 := bbase (se 2 (by rfl) ⟨241029, by rfl⟩ : syracuseStep 642745 = 482059) (by norm_num)
theorem B1199861 : Blo 531801 1199861 := bbase (se 5 (by rfl) ⟨56243, by rfl⟩ : syracuseStep 1199861 = 112487) (by norm_num)
theorem B675641 : Blo 531801 675641 := bbase (se 2 (by rfl) ⟨253365, by rfl⟩ : syracuseStep 675641 = 506731) (by norm_num)
theorem B1199933 : Blo 531801 1199933 := bbase (se 3 (by rfl) ⟨224987, by rfl⟩ : syracuseStep 1199933 = 449975) (by norm_num)
theorem B675697 : Blo 531801 675697 := bbase (se 2 (by rfl) ⟨253386, by rfl⟩ : syracuseStep 675697 = 506773) (by norm_num)
theorem B1200005 : Blo 531801 1200005 := bbase (se 4 (by rfl) ⟨112500, by rfl⟩ : syracuseStep 1200005 = 225001) (by norm_num)
theorem B642961 : Blo 531801 642961 := bbase (se 2 (by rfl) ⟨241110, by rfl⟩ : syracuseStep 642961 = 482221) (by norm_num)
theorem B2019269 : Blo 531801 2019269 := bbase (se 4 (by rfl) ⟨189306, by rfl⟩ : syracuseStep 2019269 = 378613) (by norm_num)
theorem B1200077 : Blo 531801 1200077 := bbase (se 3 (by rfl) ⟨225014, by rfl⟩ : syracuseStep 1200077 = 450029) (by norm_num)
theorem B675793 : Blo 531801 675793 := bbase (se 2 (by rfl) ⟨253422, by rfl⟩ : syracuseStep 675793 = 506845) (by norm_num)
theorem B2740229 : Blo 531801 2740229 := bbase (se 4 (by rfl) ⟨256896, by rfl⟩ : syracuseStep 2740229 = 513793) (by norm_num)
theorem B1200149 : Blo 531801 1200149 := bbase (se 6 (by rfl) ⟨28128, by rfl⟩ : syracuseStep 1200149 = 56257) (by norm_num)
theorem B1200221 : Blo 531801 1200221 := bbase (se 3 (by rfl) ⟨225041, by rfl⟩ : syracuseStep 1200221 = 450083) (by norm_num)
theorem B610421 : Blo 531801 610421 := bbase (se 5 (by rfl) ⟨28613, by rfl⟩ : syracuseStep 610421 = 57227) (by norm_num)
theorem B675965 : Blo 531801 675965 := bbase (se 3 (by rfl) ⟨126743, by rfl⟩ : syracuseStep 675965 = 253487) (by norm_num)
theorem B1200293 : Blo 531801 1200293 := bbase (se 4 (by rfl) ⟨112527, by rfl⟩ : syracuseStep 1200293 = 225055) (by norm_num)
theorem B676021 : Blo 531801 676021 := bbase (se 5 (by rfl) ⟨31688, by rfl⟩ : syracuseStep 676021 = 63377) (by norm_num)
theorem B1200365 : Blo 531801 1200365 := bbase (se 3 (by rfl) ⟨225068, by rfl⟩ : syracuseStep 1200365 = 450137) (by norm_num)
theorem B676117 : Blo 531801 676117 := bbase (se 6 (by rfl) ⟨15846, by rfl⟩ : syracuseStep 676117 = 31693) (by norm_num)
theorem B1200437 : Blo 531801 1200437 := bbase (se 5 (by rfl) ⟨56270, by rfl⟩ : syracuseStep 1200437 = 112541) (by norm_num)
theorem B2707829 : Blo 531801 2707829 := bbase (se 5 (by rfl) ⟨126929, by rfl⟩ : syracuseStep 2707829 = 253859) (by norm_num)
theorem B1200509 : Blo 531801 1200509 := bbase (se 3 (by rfl) ⟨225095, by rfl⟩ : syracuseStep 1200509 = 450191) (by norm_num)
theorem B2281861 : Blo 531801 2281861 := bbase (se 4 (by rfl) ⟨213924, by rfl⟩ : syracuseStep 2281861 = 427849) (by norm_num)
theorem B676289 : Blo 531801 676289 := bbase (se 2 (by rfl) ⟨253608, by rfl⟩ : syracuseStep 676289 = 507217) (by norm_num)
theorem B1200581 : Blo 531801 1200581 := bbase (se 4 (by rfl) ⟨112554, by rfl⟩ : syracuseStep 1200581 = 225109) (by norm_num)
theorem B676345 : Blo 531801 676345 := bbase (se 2 (by rfl) ⟨253629, by rfl⟩ : syracuseStep 676345 = 507259) (by norm_num)
theorem B1200653 : Blo 531801 1200653 := bbase (se 3 (by rfl) ⟨225122, by rfl⟩ : syracuseStep 1200653 = 450245) (by norm_num)
theorem B1200725 : Blo 531801 1200725 := bbase (se 8 (by rfl) ⟨7035, by rfl⟩ : syracuseStep 1200725 = 14071) (by norm_num)
theorem B676441 : Blo 531801 676441 := bbase (se 2 (by rfl) ⟨253665, by rfl⟩ : syracuseStep 676441 = 507331) (by norm_num)
theorem B1200797 : Blo 531801 1200797 := bbase (se 3 (by rfl) ⟨225149, by rfl⟩ : syracuseStep 1200797 = 450299) (by norm_num)
theorem B1200869 : Blo 531801 1200869 := bbase (se 4 (by rfl) ⟨112581, by rfl⟩ : syracuseStep 1200869 = 225163) (by norm_num)
theorem B676613 : Blo 531801 676613 := bbase (se 4 (by rfl) ⟨63432, by rfl⟩ : syracuseStep 676613 = 126865) (by norm_num)
theorem B1200941 : Blo 531801 1200941 := bbase (se 3 (by rfl) ⟨225176, by rfl⟩ : syracuseStep 1200941 = 450353) (by norm_num)
theorem B676669 : Blo 531801 676669 := bbase (se 3 (by rfl) ⟨126875, by rfl⟩ : syracuseStep 676669 = 253751) (by norm_num)
theorem B1201013 : Blo 531801 1201013 := bbase (se 5 (by rfl) ⟨56297, by rfl⟩ : syracuseStep 1201013 = 112595) (by norm_num)
theorem B676765 : Blo 531801 676765 := bbase (se 3 (by rfl) ⟨126893, by rfl⟩ : syracuseStep 676765 = 253787) (by norm_num)
theorem B1201085 : Blo 531801 1201085 := bbase (se 3 (by rfl) ⟨225203, by rfl⟩ : syracuseStep 1201085 = 450407) (by norm_num)
theorem B3036149 : Blo 531801 3036149 := bbase (se 5 (by rfl) ⟨142319, by rfl⟩ : syracuseStep 3036149 = 284639) (by norm_num)
theorem B1201157 : Blo 531801 1201157 := bbase (se 4 (by rfl) ⟨112608, by rfl⟩ : syracuseStep 1201157 = 225217) (by norm_num)
theorem B676937 : Blo 531801 676937 := bbase (se 2 (by rfl) ⟨253851, by rfl⟩ : syracuseStep 676937 = 507703) (by norm_num)
theorem B1201229 : Blo 531801 1201229 := bbase (se 3 (by rfl) ⟨225230, by rfl⟩ : syracuseStep 1201229 = 450461) (by norm_num)
theorem B676993 : Blo 531801 676993 := bbase (se 2 (by rfl) ⟨253872, by rfl⟩ : syracuseStep 676993 = 507745) (by norm_num)
theorem B1201301 : Blo 531801 1201301 := bbase (se 6 (by rfl) ⟨28155, by rfl⟩ : syracuseStep 1201301 = 56311) (by norm_num)
theorem B1201373 : Blo 531801 1201373 := bbase (se 3 (by rfl) ⟨225257, by rfl⟩ : syracuseStep 1201373 = 450515) (by norm_num)
theorem B677089 : Blo 531801 677089 := bbase (se 2 (by rfl) ⟨253908, by rfl⟩ : syracuseStep 677089 = 507817) (by norm_num)
theorem B1365245 : Blo 531801 1365245 := bbase (se 3 (by rfl) ⟨255983, by rfl⟩ : syracuseStep 1365245 = 511967) (by norm_num)
theorem B1201445 : Blo 531801 1201445 := bbase (se 4 (by rfl) ⟨112635, by rfl⟩ : syracuseStep 1201445 = 225271) (by norm_num)
theorem B1201517 : Blo 531801 1201517 := bbase (se 3 (by rfl) ⟨225284, by rfl⟩ : syracuseStep 1201517 = 450569) (by norm_num)
theorem B677261 : Blo 531801 677261 := bbase (se 3 (by rfl) ⟨126986, by rfl⟩ : syracuseStep 677261 = 253973) (by norm_num)
theorem B1136045 : Blo 531801 1136045 := bbase (se 3 (by rfl) ⟨213008, by rfl⟩ : syracuseStep 1136045 = 426017) (by norm_num)
theorem B1201589 : Blo 531801 1201589 := bbase (se 5 (by rfl) ⟨56324, by rfl⟩ : syracuseStep 1201589 = 112649) (by norm_num)
theorem B677317 : Blo 531801 677317 := bbase (se 4 (by rfl) ⟨63498, by rfl⟩ : syracuseStep 677317 = 126997) (by norm_num)
theorem B1201661 : Blo 531801 1201661 := bbase (se 3 (by rfl) ⟨225311, by rfl⟩ : syracuseStep 1201661 = 450623) (by norm_num)
theorem B677413 : Blo 531801 677413 := bbase (se 4 (by rfl) ⟨63507, by rfl⟩ : syracuseStep 677413 = 127015) (by norm_num)
theorem B1201733 : Blo 531801 1201733 := bbase (se 4 (by rfl) ⟨112662, by rfl⟩ : syracuseStep 1201733 = 225325) (by norm_num)
theorem B2709125 : Blo 531801 2709125 := bbase (se 4 (by rfl) ⟨253980, by rfl⟩ : syracuseStep 2709125 = 507961) (by norm_num)
theorem B1201805 : Blo 531801 1201805 := bbase (se 3 (by rfl) ⟨225338, by rfl⟩ : syracuseStep 1201805 = 450677) (by norm_num)
theorem B677585 : Blo 531801 677585 := bbase (se 2 (by rfl) ⟨254094, by rfl⟩ : syracuseStep 677585 = 508189) (by norm_num)
theorem B1201877 : Blo 531801 1201877 := bbase (se 7 (by rfl) ⟨14084, by rfl⟩ : syracuseStep 1201877 = 28169) (by norm_num)
theorem B677641 : Blo 531801 677641 := bbase (se 2 (by rfl) ⟨254115, by rfl⟩ : syracuseStep 677641 = 508231) (by norm_num)
theorem B1201949 : Blo 531801 1201949 := bbase (se 3 (by rfl) ⟨225365, by rfl⟩ : syracuseStep 1201949 = 450731) (by norm_num)
theorem B13850453 : Blo 531801 13850453 := bbase (se 9 (by rfl) ⟨40577, by rfl⟩ : syracuseStep 13850453 = 81155) (by norm_num)
theorem B2283349 : Blo 531801 2283349 := bbase (se 9 (by rfl) ⟨6689, by rfl⟩ : syracuseStep 2283349 = 13379) (by norm_num)
theorem B1202021 : Blo 531801 1202021 := bbase (se 4 (by rfl) ⟨112689, by rfl⟩ : syracuseStep 1202021 = 225379) (by norm_num)
theorem B2283365 : Blo 531801 2283365 := bbase (se 4 (by rfl) ⟨214065, by rfl⟩ : syracuseStep 2283365 = 428131) (by norm_num)
theorem B677737 : Blo 531801 677737 := bbase (se 2 (by rfl) ⟨254151, by rfl⟩ : syracuseStep 677737 = 508303) (by norm_num)
theorem B1202093 : Blo 531801 1202093 := bbase (se 3 (by rfl) ⟨225392, by rfl⟩ : syracuseStep 1202093 = 450785) (by norm_num)
theorem B7722965 : Blo 531801 7722965 := bbase (se 7 (by rfl) ⟨90503, by rfl⟩ : syracuseStep 7722965 = 181007) (by norm_num)
theorem B1202165 : Blo 531801 1202165 := bbase (se 5 (by rfl) ⟨56351, by rfl⟩ : syracuseStep 1202165 = 112703) (by norm_num)
theorem B2021381 : Blo 531801 2021381 := bbase (se 4 (by rfl) ⟨189504, by rfl⟩ : syracuseStep 2021381 = 379009) (by norm_num)
theorem B677909 : Blo 531801 677909 := bbase (se 6 (by rfl) ⟨15888, by rfl⟩ : syracuseStep 677909 = 31777) (by norm_num)
theorem B1202237 : Blo 531801 1202237 := bbase (se 3 (by rfl) ⟨225419, by rfl⟩ : syracuseStep 1202237 = 450839) (by norm_num)
theorem B677965 : Blo 531801 677965 := bbase (se 3 (by rfl) ⟨127118, by rfl⟩ : syracuseStep 677965 = 254237) (by norm_num)
theorem B1202309 : Blo 531801 1202309 := bbase (se 4 (by rfl) ⟨112716, by rfl⟩ : syracuseStep 1202309 = 225433) (by norm_num)
theorem B678061 : Blo 531801 678061 := bbase (se 3 (by rfl) ⟨127136, by rfl⟩ : syracuseStep 678061 = 254273) (by norm_num)
theorem B1202381 : Blo 531801 1202381 := bbase (se 3 (by rfl) ⟨225446, by rfl⟩ : syracuseStep 1202381 = 450893) (by norm_num)
theorem B579817 : Blo 531801 579817 := bbase (se 2 (by rfl) ⟨217431, by rfl⟩ : syracuseStep 579817 = 434863) (by norm_num)
theorem B1202453 : Blo 531801 1202453 := bbase (se 6 (by rfl) ⟨28182, by rfl⟩ : syracuseStep 1202453 = 56365) (by norm_num)
theorem B1136933 : Blo 531801 1136933 := bbase (se 4 (by rfl) ⟨106587, by rfl⟩ : syracuseStep 1136933 = 213175) (by norm_num)
theorem B2021669 : Blo 531801 2021669 := bbase (se 4 (by rfl) ⟨189531, by rfl⟩ : syracuseStep 2021669 = 379063) (by norm_num)
theorem B1038653 : Blo 531801 1038653 := bbase (se 3 (by rfl) ⟨194747, by rfl⟩ : syracuseStep 1038653 = 389495) (by norm_num)
theorem B6838613 : Blo 531801 6838613 := bbase (se 10 (by rfl) ⟨10017, by rfl⟩ : syracuseStep 6838613 = 20035) (by norm_num)
theorem B1202525 : Blo 531801 1202525 := bbase (se 3 (by rfl) ⟨225473, by rfl⟩ : syracuseStep 1202525 = 450947) (by norm_num)
theorem B1366397 : Blo 531801 1366397 := bbase (se 3 (by rfl) ⟨256199, by rfl⟩ : syracuseStep 1366397 = 512399) (by norm_num)
theorem B1137053 : Blo 531801 1137053 := bbase (se 3 (by rfl) ⟨213197, by rfl⟩ : syracuseStep 1137053 = 426395) (by norm_num)
theorem B1202597 : Blo 531801 1202597 := bbase (se 4 (by rfl) ⟨112743, by rfl⟩ : syracuseStep 1202597 = 225487) (by norm_num)
theorem B1202669 : Blo 531801 1202669 := bbase (se 3 (by rfl) ⟨225500, by rfl⟩ : syracuseStep 1202669 = 451001) (by norm_num)
theorem B1202741 : Blo 531801 1202741 := bbase (se 5 (by rfl) ⟨56378, by rfl⟩ : syracuseStep 1202741 = 112757) (by norm_num)
theorem B1202813 : Blo 531801 1202813 := bbase (se 3 (by rfl) ⟨225527, by rfl⟩ : syracuseStep 1202813 = 451055) (by norm_num)
theorem B1202885 : Blo 531801 1202885 := bbase (se 4 (by rfl) ⟨112770, by rfl⟩ : syracuseStep 1202885 = 225541) (by norm_num)
theorem B1202957 : Blo 531801 1202957 := bbase (se 3 (by rfl) ⟨225554, by rfl⟩ : syracuseStep 1202957 = 451109) (by norm_num)
theorem B809813 : Blo 531801 809813 := bbase (se 9 (by rfl) ⟨2372, by rfl⟩ : syracuseStep 809813 = 4745) (by norm_num)
theorem B1203029 : Blo 531801 1203029 := bbase (se 9 (by rfl) ⟨3524, by rfl⟩ : syracuseStep 1203029 = 7049) (by norm_num)
theorem B2710421 : Blo 531801 2710421 := bbase (se 6 (by rfl) ⟨63525, by rfl⟩ : syracuseStep 2710421 = 127051) (by norm_num)
theorem B1203101 : Blo 531801 1203101 := bbase (se 3 (by rfl) ⟨225581, by rfl⟩ : syracuseStep 1203101 = 451163) (by norm_num)
theorem B1203173 : Blo 531801 1203173 := bbase (se 4 (by rfl) ⟨112797, by rfl⟩ : syracuseStep 1203173 = 225595) (by norm_num)
theorem B1137685 : Blo 531801 1137685 := bbase (se 6 (by rfl) ⟨26664, by rfl⟩ : syracuseStep 1137685 = 53329) (by norm_num)
theorem B1203245 : Blo 531801 1203245 := bbase (se 3 (by rfl) ⟨225608, by rfl⟩ : syracuseStep 1203245 = 451217) (by norm_num)
theorem B1203317 : Blo 531801 1203317 := bbase (se 5 (by rfl) ⟨56405, by rfl⟩ : syracuseStep 1203317 = 112811) (by norm_num)
theorem B1203389 : Blo 531801 1203389 := bbase (se 3 (by rfl) ⟨225635, by rfl⟩ : syracuseStep 1203389 = 451271) (by norm_num)
theorem B1203461 : Blo 531801 1203461 := bbase (se 4 (by rfl) ⟨112824, by rfl⟩ : syracuseStep 1203461 = 225649) (by norm_num)
theorem B1203533 : Blo 531801 1203533 := bbase (se 3 (by rfl) ⟨225662, by rfl⟩ : syracuseStep 1203533 = 451325) (by norm_num)
theorem B1203605 : Blo 531801 1203605 := bbase (se 6 (by rfl) ⟨28209, by rfl⟩ : syracuseStep 1203605 = 56419) (by norm_num)
theorem B2022853 : Blo 531801 2022853 := bbase (se 4 (by rfl) ⟨189642, by rfl⟩ : syracuseStep 2022853 = 379285) (by norm_num)
theorem B1203677 : Blo 531801 1203677 := bbase (se 3 (by rfl) ⟨225689, by rfl⟩ : syracuseStep 1203677 = 451379) (by norm_num)
theorem B1203749 : Blo 531801 1203749 := bbase (se 4 (by rfl) ⟨112851, by rfl⟩ : syracuseStep 1203749 = 225703) (by norm_num)
theorem B1203821 : Blo 531801 1203821 := bbase (se 3 (by rfl) ⟨225716, by rfl⟩ : syracuseStep 1203821 = 451433) (by norm_num)
theorem B1203893 : Blo 531801 1203893 := bbase (se 5 (by rfl) ⟨56432, by rfl⟩ : syracuseStep 1203893 = 112865) (by norm_num)
theorem B2023157 : Blo 531801 2023157 := bbase (se 5 (by rfl) ⟨94835, by rfl⟩ : syracuseStep 2023157 = 189671) (by norm_num)
theorem B1203965 : Blo 531801 1203965 := bbase (se 3 (by rfl) ⟨225743, by rfl⟩ : syracuseStep 1203965 = 451487) (by norm_num)
theorem B1204037 : Blo 531801 1204037 := bbase (se 4 (by rfl) ⟨112878, by rfl⟩ : syracuseStep 1204037 = 225757) (by norm_num)
theorem B548737 : Blo 531801 548737 := bbase (se 2 (by rfl) ⟨205776, by rfl⟩ : syracuseStep 548737 = 411553) (by norm_num)
theorem B1138573 : Blo 531801 1138573 := bbase (se 3 (by rfl) ⟨213482, by rfl⟩ : syracuseStep 1138573 = 426965) (by norm_num)
theorem B1204109 : Blo 531801 1204109 := bbase (se 3 (by rfl) ⟨225770, by rfl⟩ : syracuseStep 1204109 = 451541) (by norm_num)
theorem B1204181 : Blo 531801 1204181 := bbase (se 7 (by rfl) ⟨14111, by rfl⟩ : syracuseStep 1204181 = 28223) (by norm_num)
theorem B1138693 : Blo 531801 1138693 := bbase (se 4 (by rfl) ⟨106752, by rfl⟩ : syracuseStep 1138693 = 213505) (by norm_num)
theorem B1204253 : Blo 531801 1204253 := bbase (se 3 (by rfl) ⟨225797, by rfl⟩ : syracuseStep 1204253 = 451595) (by norm_num)
theorem B2285621 : Blo 531801 2285621 := bbase (se 5 (by rfl) ⟨107138, by rfl⟩ : syracuseStep 2285621 = 214277) (by norm_num)
theorem B1204325 : Blo 531801 1204325 := bbase (se 4 (by rfl) ⟨112905, by rfl⟩ : syracuseStep 1204325 = 225811) (by norm_num)
theorem B2711717 : Blo 531801 2711717 := bbase (se 4 (by rfl) ⟨254223, by rfl⟩ : syracuseStep 2711717 = 508447) (by norm_num)
theorem B1204397 : Blo 531801 1204397 := bbase (se 3 (by rfl) ⟨225824, by rfl⟩ : syracuseStep 1204397 = 451649) (by norm_num)
theorem B1204469 : Blo 531801 1204469 := bbase (se 5 (by rfl) ⟨56459, by rfl⟩ : syracuseStep 1204469 = 112919) (by norm_num)
theorem B1138949 : Blo 531801 1138949 := bbase (se 4 (by rfl) ⟨106776, by rfl⟩ : syracuseStep 1138949 = 213553) (by norm_num)
theorem B1204541 : Blo 531801 1204541 := bbase (se 3 (by rfl) ⟨225851, by rfl⟩ : syracuseStep 1204541 = 451703) (by norm_num)
theorem B1204613 : Blo 531801 1204613 := bbase (se 4 (by rfl) ⟨112932, by rfl⟩ : syracuseStep 1204613 = 225865) (by norm_num)
theorem B1204685 : Blo 531801 1204685 := bbase (se 3 (by rfl) ⟨225878, by rfl⟩ : syracuseStep 1204685 = 451757) (by norm_num)
theorem B1204757 : Blo 531801 1204757 := bbase (se 6 (by rfl) ⟨28236, by rfl⟩ : syracuseStep 1204757 = 56473) (by norm_num)
theorem B1204829 : Blo 531801 1204829 := bbase (se 3 (by rfl) ⟨225905, by rfl⟩ : syracuseStep 1204829 = 451811) (by norm_num)
theorem B4055669 : Blo 531801 4055669 := bbase (se 5 (by rfl) ⟨190109, by rfl⟩ : syracuseStep 4055669 = 380219) (by norm_num)
theorem B1204901 : Blo 531801 1204901 := bbase (se 4 (by rfl) ⟨112959, by rfl⟩ : syracuseStep 1204901 = 225919) (by norm_num)
theorem B1204973 : Blo 531801 1204973 := bbase (se 3 (by rfl) ⟨225932, by rfl⟩ : syracuseStep 1204973 = 451865) (by norm_num)
theorem B1205045 : Blo 531801 1205045 := bbase (se 5 (by rfl) ⟨56486, by rfl⟩ : syracuseStep 1205045 = 112973) (by norm_num)
theorem B1925957 : Blo 531801 1925957 := bbase (se 4 (by rfl) ⟨180558, by rfl⟩ : syracuseStep 1925957 = 361117) (by norm_num)
theorem B1205117 : Blo 531801 1205117 := bbase (se 3 (by rfl) ⟨225959, by rfl⟩ : syracuseStep 1205117 = 451919) (by norm_num)
theorem B3072917 : Blo 531801 3072917 := bbase (se 6 (by rfl) ⟨72021, by rfl⟩ : syracuseStep 3072917 = 144043) (by norm_num)
theorem B1795013 : Blo 531801 1795013 := bbase (se 4 (by rfl) ⟨168282, by rfl⟩ : syracuseStep 1795013 = 336565) (by norm_num)
theorem B1205189 : Blo 531801 1205189 := bbase (se 4 (by rfl) ⟨112986, by rfl⟩ : syracuseStep 1205189 = 225973) (by norm_num)
theorem B9102293 : Blo 531801 9102293 := bbase (se 7 (by rfl) ⟨106667, by rfl⟩ : syracuseStep 9102293 = 213335) (by norm_num)
theorem B1369045 : Blo 531801 1369045 := bbase (se 7 (by rfl) ⟨16043, by rfl⟩ : syracuseStep 1369045 = 32087) (by norm_num)
theorem B1205261 : Blo 531801 1205261 := bbase (se 3 (by rfl) ⟨225986, by rfl⟩ : syracuseStep 1205261 = 451973) (by norm_num)
theorem B615481 : Blo 531801 615481 := bbase (se 2 (by rfl) ⟨230805, by rfl⟩ : syracuseStep 615481 = 461611) (by norm_num)
theorem B1205333 : Blo 531801 1205333 := bbase (se 8 (by rfl) ⟨7062, by rfl⟩ : syracuseStep 1205333 = 14125) (by norm_num)
theorem B1139837 : Blo 531801 1139837 := bbase (se 3 (by rfl) ⟨213719, by rfl⟩ : syracuseStep 1139837 = 427439) (by norm_num)
theorem B1205405 : Blo 531801 1205405 := bbase (se 3 (by rfl) ⟨226013, by rfl⟩ : syracuseStep 1205405 = 452027) (by norm_num)
theorem B1205477 : Blo 531801 1205477 := bbase (se 4 (by rfl) ⟨113013, by rfl⟩ : syracuseStep 1205477 = 226027) (by norm_num)
theorem B1205549 : Blo 531801 1205549 := bbase (se 3 (by rfl) ⟨226040, by rfl⟩ : syracuseStep 1205549 = 452081) (by norm_num)
theorem B1140077 : Blo 531801 1140077 := bbase (se 3 (by rfl) ⟨213764, by rfl⟩ : syracuseStep 1140077 = 427529) (by norm_num)
theorem B1795445 : Blo 531801 1795445 := bbase (se 5 (by rfl) ⟨84161, by rfl⟩ : syracuseStep 1795445 = 168323) (by norm_num)
theorem B1336733 : Blo 531801 1336733 := bbase (se 3 (by rfl) ⟨250637, by rfl⟩ : syracuseStep 1336733 = 501275) (by norm_num)
theorem B976573 : Blo 531801 976573 := bbase (se 3 (by rfl) ⟨183107, by rfl⟩ : syracuseStep 976573 = 366215) (by norm_num)
theorem B976613 : Blo 531801 976613 := bbase (se 4 (by rfl) ⟨91557, by rfl⟩ : syracuseStep 976613 = 183115) (by norm_num)
theorem B1795877 : Blo 531801 1795877 := bbase (se 4 (by rfl) ⟨168363, by rfl⟩ : syracuseStep 1795877 = 336727) (by norm_num)
theorem B1828645 : Blo 531801 1828645 := bbase (se 4 (by rfl) ⟨171435, by rfl⟩ : syracuseStep 1828645 = 342871) (by norm_num)
theorem B2025269 : Blo 531801 2025269 := bbase (se 5 (by rfl) ⟨94934, by rfl⟩ : syracuseStep 2025269 = 189869) (by norm_num)
theorem B1140581 : Blo 531801 1140581 := bbase (se 4 (by rfl) ⟨106929, by rfl⟩ : syracuseStep 1140581 = 213859) (by norm_num)
theorem B1140589 : Blo 531801 1140589 := bbase (se 3 (by rfl) ⟨213860, by rfl⟩ : syracuseStep 1140589 = 427721) (by norm_num)
theorem B1009597 : Blo 531801 1009597 := bbase (se 3 (by rfl) ⟨189299, by rfl⟩ : syracuseStep 1009597 = 378599) (by norm_num)
theorem B5498837 : Blo 531801 5498837 := bbase (se 7 (by rfl) ⟨64439, by rfl⟩ : syracuseStep 5498837 = 128879) (by norm_num)
theorem B1009741 : Blo 531801 1009741 := bbase (se 3 (by rfl) ⟨189326, by rfl⟩ : syracuseStep 1009741 = 378653) (by norm_num)
theorem B2025557 : Blo 531801 2025557 := bbase (se 8 (by rfl) ⟨11868, by rfl⟩ : syracuseStep 2025557 = 23737) (by norm_num)
theorem B649361 : Blo 531801 649361 := bbase (se 2 (by rfl) ⟨243510, by rfl⟩ : syracuseStep 649361 = 487021) (by norm_num)
theorem B911533 : Blo 531801 911533 := bbase (se 3 (by rfl) ⟨170912, by rfl⟩ : syracuseStep 911533 = 341825) (by norm_num)
theorem B1796309 : Blo 531801 1796309 := bbase (se 7 (by rfl) ⟨21050, by rfl⟩ : syracuseStep 1796309 = 42101) (by norm_num)
theorem B1927397 : Blo 531801 1927397 := bbase (se 4 (by rfl) ⟨180693, by rfl⟩ : syracuseStep 1927397 = 361387) (by norm_num)
theorem B1009901 : Blo 531801 1009901 := bbase (se 3 (by rfl) ⟨189356, by rfl⟩ : syracuseStep 1009901 = 378713) (by norm_num)
theorem B813413 : Blo 531801 813413 := bbase (se 4 (by rfl) ⟨76257, by rfl⟩ : syracuseStep 813413 = 152515) (by norm_num)
theorem B1010045 : Blo 531801 1010045 := bbase (se 3 (by rfl) ⟨189383, by rfl⟩ : syracuseStep 1010045 = 378767) (by norm_num)
theorem B6482389 : Blo 531801 6482389 := bbase (se 7 (by rfl) ⟨75965, by rfl⟩ : syracuseStep 6482389 = 151931) (by norm_num)
theorem B1796741 : Blo 531801 1796741 := bbase (se 4 (by rfl) ⟨168444, by rfl⟩ : syracuseStep 1796741 = 336889) (by norm_num)
theorem B1010333 : Blo 531801 1010333 := bbase (se 3 (by rfl) ⟨189437, by rfl⟩ : syracuseStep 1010333 = 378875) (by norm_num)
theorem B1370789 : Blo 531801 1370789 := bbase (se 4 (by rfl) ⟨128511, by rfl⟩ : syracuseStep 1370789 = 257023) (by norm_num)
theorem B1010485 : Blo 531801 1010485 := bbase (se 5 (by rfl) ⟨47366, by rfl⟩ : syracuseStep 1010485 = 94733) (by norm_num)
theorem B682921 : Blo 531801 682921 := bbase (se 2 (by rfl) ⟨256095, by rfl⟩ : syracuseStep 682921 = 512191) (by norm_num)
theorem B813997 : Blo 531801 813997 := bbase (se 3 (by rfl) ⟨152624, by rfl⟩ : syracuseStep 813997 = 305249) (by norm_num)
theorem B1141717 : Blo 531801 1141717 := bbase (se 7 (by rfl) ⟨13379, by rfl⟩ : syracuseStep 1141717 = 26759) (by norm_num)
theorem B3894293 : Blo 531801 3894293 := bbase (se 6 (by rfl) ⟨91272, by rfl⟩ : syracuseStep 3894293 = 182545) (by norm_num)
theorem B1797173 : Blo 531801 1797173 := bbase (se 5 (by rfl) ⟨84242, by rfl⟩ : syracuseStep 1797173 = 168485) (by norm_num)
theorem B1010789 : Blo 531801 1010789 := bbase (se 4 (by rfl) ⟨94761, by rfl⟩ : syracuseStep 1010789 = 189523) (by norm_num)
theorem B683177 : Blo 531801 683177 := bbase (se 2 (by rfl) ⟨256191, by rfl⟩ : syracuseStep 683177 = 512383) (by norm_num)
theorem B3075317 : Blo 531801 3075317 := bbase (se 5 (by rfl) ⟨144155, by rfl⟩ : syracuseStep 3075317 = 288311) (by norm_num)
theorem B2026741 : Blo 531801 2026741 := bbase (se 5 (by rfl) ⟨95003, by rfl⟩ : syracuseStep 2026741 = 190007) (by norm_num)
theorem B3665173 : Blo 531801 3665173 := bbase (se 6 (by rfl) ⟨85902, by rfl⟩ : syracuseStep 3665173 = 171805) (by norm_num)
theorem B1142093 : Blo 531801 1142093 := bbase (se 3 (by rfl) ⟨214142, by rfl⟩ : syracuseStep 1142093 = 428285) (by norm_num)
theorem B1797605 : Blo 531801 1797605 := bbase (se 4 (by rfl) ⟨168525, by rfl⟩ : syracuseStep 1797605 = 337051) (by norm_num)
theorem B2027045 : Blo 531801 2027045 := bbase (se 4 (by rfl) ⟨190035, by rfl⟩ : syracuseStep 2027045 = 380071) (by norm_num)
theorem B1371773 : Blo 531801 1371773 := bbase (se 3 (by rfl) ⟨257207, by rfl⟩ : syracuseStep 1371773 = 514415) (by norm_num)
theorem B913189 : Blo 531801 913189 := bbase (se 4 (by rfl) ⟨85611, by rfl⟩ : syracuseStep 913189 = 171223) (by norm_num)
theorem B1011541 : Blo 531801 1011541 := bbase (se 9 (by rfl) ⟨2963, by rfl⟩ : syracuseStep 1011541 = 5927) (by norm_num)
theorem B1798037 : Blo 531801 1798037 := bbase (se 6 (by rfl) ⟨42141, by rfl⟩ : syracuseStep 1798037 = 84283) (by norm_num)
theorem B1011685 : Blo 531801 1011685 := bbase (se 4 (by rfl) ⟨94845, by rfl⟩ : syracuseStep 1011685 = 189691) (by norm_num)
theorem B2060309 : Blo 531801 2060309 := bbase (se 6 (by rfl) ⟨48288, by rfl⟩ : syracuseStep 2060309 = 96577) (by norm_num)
theorem B684137 : Blo 531801 684137 := bbase (se 2 (by rfl) ⟨256551, by rfl⟩ : syracuseStep 684137 = 513103) (by norm_num)
theorem B1011845 : Blo 531801 1011845 := bbase (se 4 (by rfl) ⟨94860, by rfl⟩ : syracuseStep 1011845 = 189721) (by norm_num)
theorem B1011989 : Blo 531801 1011989 := bbase (se 6 (by rfl) ⟨23718, by rfl⟩ : syracuseStep 1011989 = 47437) (by norm_num)
theorem B1798469 : Blo 531801 1798469 := bbase (se 4 (by rfl) ⟨168606, by rfl⟩ : syracuseStep 1798469 = 337213) (by norm_num)
theorem B782669 : Blo 531801 782669 := bbase (se 3 (by rfl) ⟨146750, by rfl⟩ : syracuseStep 782669 = 293501) (by norm_num)
theorem B913885 : Blo 531801 913885 := bbase (se 3 (by rfl) ⟨171353, by rfl⟩ : syracuseStep 913885 = 342707) (by norm_num)
theorem B619049 : Blo 531801 619049 := bbase (se 2 (by rfl) ⟨232143, by rfl⟩ : syracuseStep 619049 = 464287) (by norm_num)
theorem B1372717 : Blo 531801 1372717 := bbase (se 3 (by rfl) ⟨257384, by rfl⟩ : syracuseStep 1372717 = 514769) (by norm_num)
theorem B1012277 : Blo 531801 1012277 := bbase (se 5 (by rfl) ⟨47450, by rfl⟩ : syracuseStep 1012277 = 94901) (by norm_num)
theorem B1012429 : Blo 531801 1012429 := bbase (se 3 (by rfl) ⟨189830, by rfl⟩ : syracuseStep 1012429 = 379661) (by norm_num)
theorem B1798901 : Blo 531801 1798901 := bbase (se 5 (by rfl) ⟨84323, by rfl⟩ : syracuseStep 1798901 = 168647) (by norm_num)
theorem B3044213 : Blo 531801 3044213 := bbase (se 5 (by rfl) ⟨142697, by rfl⟩ : syracuseStep 3044213 = 285395) (by norm_num)
theorem B2749301 : Blo 531801 2749301 := bbase (se 5 (by rfl) ⟨128873, by rfl⟩ : syracuseStep 2749301 = 257747) (by norm_num)
theorem B1143733 : Blo 531801 1143733 := bbase (se 5 (by rfl) ⟨53612, by rfl⟩ : syracuseStep 1143733 = 107225) (by norm_num)
theorem B1012733 : Blo 531801 1012733 := bbase (se 3 (by rfl) ⟨189887, by rfl⟩ : syracuseStep 1012733 = 379775) (by norm_num)
theorem B1799333 : Blo 531801 1799333 := bbase (se 4 (by rfl) ⟨168687, by rfl⟩ : syracuseStep 1799333 = 337375) (by norm_num)
theorem B1733813 : Blo 531801 1733813 := bbase (se 5 (by rfl) ⟨81272, by rfl⟩ : syracuseStep 1733813 = 162545) (by norm_num)
theorem B685621 : Blo 531801 685621 := bbase (se 5 (by rfl) ⟨32138, by rfl⟩ : syracuseStep 685621 = 64277) (by norm_num)
theorem B1799765 : Blo 531801 1799765 := bbase (se 8 (by rfl) ⟨10545, by rfl⟩ : syracuseStep 1799765 = 21091) (by norm_num)
theorem B2029157 : Blo 531801 2029157 := bbase (se 4 (by rfl) ⟨190233, by rfl⟩ : syracuseStep 2029157 = 380467) (by norm_num)
theorem B1013485 : Blo 531801 1013485 := bbase (se 3 (by rfl) ⟨190028, by rfl⟩ : syracuseStep 1013485 = 380057) (by norm_num)
theorem B685837 : Blo 531801 685837 := bbase (se 3 (by rfl) ⟨128594, by rfl⟩ : syracuseStep 685837 = 257189) (by norm_num)
theorem B1013629 : Blo 531801 1013629 := bbase (se 3 (by rfl) ⟨190055, by rfl⟩ : syracuseStep 1013629 = 380111) (by norm_num)
theorem B2029445 : Blo 531801 2029445 := bbase (se 4 (by rfl) ⟨190260, by rfl⟩ : syracuseStep 2029445 = 380521) (by norm_num)
theorem B1800197 : Blo 531801 1800197 := bbase (se 4 (by rfl) ⟨168768, by rfl⟩ : syracuseStep 1800197 = 337537) (by norm_num)
theorem B3045397 : Blo 531801 3045397 := bbase (se 6 (by rfl) ⟨71376, by rfl⟩ : syracuseStep 3045397 = 142753) (by norm_num)
theorem B1013789 : Blo 531801 1013789 := bbase (se 3 (by rfl) ⟨190085, by rfl⟩ : syracuseStep 1013789 = 380171) (by norm_num)
theorem B1013933 : Blo 531801 1013933 := bbase (se 3 (by rfl) ⟨190112, by rfl⟩ : syracuseStep 1013933 = 380225) (by norm_num)
theorem B2193685 : Blo 531801 2193685 := bbase (se 6 (by rfl) ⟨51414, by rfl⟩ : syracuseStep 2193685 = 102829) (by norm_num)
theorem B1800629 : Blo 531801 1800629 := bbase (se 5 (by rfl) ⟨84404, by rfl⟩ : syracuseStep 1800629 = 168809) (by norm_num)
theorem B719293 : Blo 531801 719293 := bbase (se 3 (by rfl) ⟨134867, by rfl⟩ : syracuseStep 719293 = 269735) (by norm_num)
theorem B1014221 : Blo 531801 1014221 := bbase (se 3 (by rfl) ⟨190166, by rfl⟩ : syracuseStep 1014221 = 380333) (by norm_num)
theorem B1014373 : Blo 531801 1014373 := bbase (se 4 (by rfl) ⟨95097, by rfl⟩ : syracuseStep 1014373 = 190195) (by norm_num)
theorem B1801061 : Blo 531801 1801061 := bbase (se 4 (by rfl) ⟨168849, by rfl⟩ : syracuseStep 1801061 = 337699) (by norm_num)
theorem B1440661 : Blo 531801 1440661 := bbase (se 6 (by rfl) ⟨33765, by rfl⟩ : syracuseStep 1440661 = 67531) (by norm_num)
theorem B1014677 : Blo 531801 1014677 := bbase (se 6 (by rfl) ⟨23781, by rfl⟩ : syracuseStep 1014677 = 47563) (by norm_num)
theorem B2030629 : Blo 531801 2030629 := bbase (se 4 (by rfl) ⟨190371, by rfl⟩ : syracuseStep 2030629 = 380743) (by norm_num)
theorem B1801493 : Blo 531801 1801493 := bbase (se 6 (by rfl) ⟨42222, by rfl⟩ : syracuseStep 1801493 = 84445) (by norm_num)
theorem B2030933 : Blo 531801 2030933 := bbase (se 11 (by rfl) ⟨1487, by rfl⟩ : syracuseStep 2030933 = 2975) (by norm_num)
theorem B1015429 : Blo 531801 1015429 := bbase (se 4 (by rfl) ⟨95196, by rfl⟩ : syracuseStep 1015429 = 190393) (by norm_num)
theorem B1801925 : Blo 531801 1801925 := bbase (se 4 (by rfl) ⟨168930, by rfl⟩ : syracuseStep 1801925 = 337861) (by norm_num)
theorem B2162389 : Blo 531801 2162389 := bbase (se 7 (by rfl) ⟨25340, by rfl⟩ : syracuseStep 2162389 = 50681) (by norm_num)
theorem B1015573 : Blo 531801 1015573 := bbase (se 6 (by rfl) ⟨23802, by rfl⟩ : syracuseStep 1015573 = 47605) (by norm_num)
theorem B6225749 : Blo 531801 6225749 := bbase (se 9 (by rfl) ⟨18239, by rfl⟩ : syracuseStep 6225749 = 36479) (by norm_num)
theorem B1015733 : Blo 531801 1015733 := bbase (se 5 (by rfl) ⟨47612, by rfl⟩ : syracuseStep 1015733 = 95225) (by norm_num)
theorem B3047381 : Blo 531801 3047381 := bbase (se 7 (by rfl) ⟨35711, by rfl⟩ : syracuseStep 3047381 = 71423) (by norm_num)
theorem B721217 : Blo 531801 721217 := bstep (se 2 (by rfl) ⟨270456, by rfl⟩ : syracuseStep 721217 = 540913) B540913
theorem B1802573 : Blo 531801 1802573 := bstep (se 3 (by rfl) ⟨337982, by rfl⟩ : syracuseStep 1802573 = 675965) B675965
theorem B1704323 : Blo 531801 1704323 := bstep (se 1 (by rfl) ⟨1278242, by rfl⟩ : syracuseStep 1704323 = 2556485) B2556485
theorem B1802627 : Blo 531801 1802627 := bstep (se 1 (by rfl) ⟨1351970, by rfl⟩ : syracuseStep 1802627 = 2703941) B2703941
theorem B1409411 : Blo 531801 1409411 := bstep (se 1 (by rfl) ⟨1057058, by rfl⟩ : syracuseStep 1409411 = 2114117) B2114117
theorem B3047813 : Blo 531801 3047813 := bstep (se 4 (by rfl) ⟨285732, by rfl⟩ : syracuseStep 3047813 = 571465) B571465
theorem B11502101 : Blo 531801 11502101 := bstep (se 6 (by rfl) ⟨269580, by rfl⟩ : syracuseStep 11502101 = 539161) B539161
theorem B852515 : Blo 531801 852515 := bstep (se 1 (by rfl) ⟨639386, by rfl⟩ : syracuseStep 852515 = 1278773) B1278773
theorem B1442339 : Blo 531801 1442339 := bstep (se 1 (by rfl) ⟨1081754, by rfl⟩ : syracuseStep 1442339 = 2163509) B2163509
theorem B1016401 : Blo 531801 1016401 := bstep (se 2 (by rfl) ⟨381150, by rfl⟩ : syracuseStep 1016401 = 762301) B762301
theorem B14615153 : Blo 531801 14615153 := bstep (se 2 (by rfl) ⟨5480682, by rfl⟩ : syracuseStep 14615153 = 10961365) B10961365
theorem B1802897 : Blo 531801 1802897 := bstep (se 2 (by rfl) ⟨676086, by rfl⟩ : syracuseStep 1802897 = 1352173) B1352173
theorem B1704721 : Blo 531801 1704721 := bstep (se 2 (by rfl) ⟨639270, by rfl⟩ : syracuseStep 1704721 = 1278541) B1278541
theorem B1704835 : Blo 531801 1704835 := bstep (se 1 (by rfl) ⟨1278626, by rfl⟩ : syracuseStep 1704835 = 2557253) B2557253
theorem B1016803 : Blo 531801 1016803 := bstep (se 1 (by rfl) ⟨762602, by rfl⟩ : syracuseStep 1016803 = 1525205) B1525205
theorem B1016849 : Blo 531801 1016849 := bstep (se 2 (by rfl) ⟨381318, by rfl⟩ : syracuseStep 1016849 = 762637) B762637
theorem B1803437 : Blo 531801 1803437 := bstep (se 3 (by rfl) ⟨338144, by rfl⟩ : syracuseStep 1803437 = 676289) B676289
theorem B1803491 : Blo 531801 1803491 := bstep (se 1 (by rfl) ⟨1352618, by rfl⟩ : syracuseStep 1803491 = 2705237) B2705237
theorem B1017137 : Blo 531801 1017137 := bstep (se 2 (by rfl) ⟨381426, by rfl⟩ : syracuseStep 1017137 = 762853) B762853
theorem B9733517 : Blo 531801 9733517 := bstep (se 3 (by rfl) ⟨1825034, by rfl⟩ : syracuseStep 9733517 = 3650069) B3650069
theorem B2033059 : Blo 531801 2033059 := bstep (se 1 (by rfl) ⟨1524794, by rfl⟩ : syracuseStep 2033059 = 3049589) B3049589
theorem B11699653 : Blo 531801 11699653 := bstep (se 4 (by rfl) ⟨1096842, by rfl⟩ : syracuseStep 11699653 = 2193685) B2193685
theorem B1803761 : Blo 531801 1803761 := bstep (se 2 (by rfl) ⟨676410, by rfl⟩ : syracuseStep 1803761 = 1352821) B1352821
theorem B853507 : Blo 531801 853507 := bstep (se 1 (by rfl) ⟨640130, by rfl⟩ : syracuseStep 853507 = 1280261) B1280261
theorem B1705553 : Blo 531801 1705553 := bstep (se 2 (by rfl) ⟨639582, by rfl⟩ : syracuseStep 1705553 = 1279165) B1279165
theorem B722515 : Blo 531801 722515 := bstep (se 1 (by rfl) ⟨541886, by rfl⟩ : syracuseStep 722515 = 1083773) B1083773
theorem B1804301 : Blo 531801 1804301 := bstep (se 3 (by rfl) ⟨338306, by rfl⟩ : syracuseStep 1804301 = 676613) B676613
theorem B1804355 : Blo 531801 1804355 := bstep (se 1 (by rfl) ⟨1353266, by rfl⟩ : syracuseStep 1804355 = 2706533) B2706533
theorem B1706093 : Blo 531801 1706093 := bstep (se 3 (by rfl) ⟨319892, by rfl⟩ : syracuseStep 1706093 = 639785) B639785
theorem B35063921 : Blo 531801 35063921 := bstep (se 2 (by rfl) ⟨13148970, by rfl⟩ : syracuseStep 35063921 = 26297941) B26297941
theorem B1804625 : Blo 531801 1804625 := bstep (se 2 (by rfl) ⟨676734, by rfl⟩ : syracuseStep 1804625 = 1353469) B1353469
theorem B1280387 : Blo 531801 1280387 := bstep (se 1 (by rfl) ⟨960290, by rfl⟩ : syracuseStep 1280387 = 1920581) B1920581
theorem B854417 : Blo 531801 854417 := bstep (se 2 (by rfl) ⟨320406, by rfl⟩ : syracuseStep 854417 = 640813) B640813
theorem B854545 : Blo 531801 854545 := bstep (se 2 (by rfl) ⟨320454, by rfl⟩ : syracuseStep 854545 = 640909) B640909
theorem B1346129 : Blo 531801 1346129 := bstep (se 2 (by rfl) ⟨504798, by rfl⟩ : syracuseStep 1346129 = 1009597) B1009597
theorem B1346179 : Blo 531801 1346179 := bstep (se 1 (by rfl) ⟨1009634, by rfl⟩ : syracuseStep 1346179 = 2019269) B2019269
theorem B6163141 : Blo 531801 6163141 := bstep (se 4 (by rfl) ⟨577794, by rfl⟩ : syracuseStep 6163141 = 1155589) B1155589
theorem B1346321 : Blo 531801 1346321 := bstep (se 2 (by rfl) ⟨504870, by rfl⟩ : syracuseStep 1346321 = 1009741) B1009741
theorem B1805165 : Blo 531801 1805165 := bstep (se 3 (by rfl) ⟨338468, by rfl⟩ : syracuseStep 1805165 = 676937) B676937
theorem B1215377 : Blo 531801 1215377 := bstep (se 2 (by rfl) ⟨455766, by rfl⟩ : syracuseStep 1215377 = 911533) B911533
theorem B1805219 : Blo 531801 1805219 := bstep (se 1 (by rfl) ⟨1353914, by rfl⟩ : syracuseStep 1805219 = 2707829) B2707829
theorem B1805489 : Blo 531801 1805489 := bstep (se 2 (by rfl) ⟨677058, by rfl⟩ : syracuseStep 1805489 = 1354117) B1354117
theorem B1281233 : Blo 531801 1281233 := bstep (se 2 (by rfl) ⟨480462, by rfl⟩ : syracuseStep 1281233 = 960925) B960925
theorem B855539 : Blo 531801 855539 := bstep (se 1 (by rfl) ⟨641654, by rfl⟩ : syracuseStep 855539 = 1283309) B1283309
theorem B1445485 : Blo 531801 1445485 := bstep (se 3 (by rfl) ⟨271028, by rfl⟩ : syracuseStep 1445485 = 542057) B542057
theorem B757363 : Blo 531801 757363 := bstep (se 1 (by rfl) ⟨568022, by rfl⟩ : syracuseStep 757363 = 1136045) B1136045
theorem B1445539 : Blo 531801 1445539 := bstep (se 1 (by rfl) ⟨1084154, by rfl⟩ : syracuseStep 1445539 = 2168309) B2168309
theorem B1806029 : Blo 531801 1806029 := bstep (se 3 (by rfl) ⟨338630, by rfl⟩ : syracuseStep 1806029 = 677261) B677261
theorem B1347313 : Blo 531801 1347313 := bstep (se 2 (by rfl) ⟨505242, by rfl⟩ : syracuseStep 1347313 = 1010485) B1010485
theorem B1806083 : Blo 531801 1806083 := bstep (se 1 (by rfl) ⟨1354562, by rfl⟩ : syracuseStep 1806083 = 2709125) B2709125
theorem B1085329 : Blo 531801 1085329 := bstep (se 2 (by rfl) ⟨406998, by rfl⟩ : syracuseStep 1085329 = 813997) B813997
theorem B1544113 : Blo 531801 1544113 := bstep (se 2 (by rfl) ⟨579042, by rfl⟩ : syracuseStep 1544113 = 1158085) B1158085
theorem B5148643 : Blo 531801 5148643 := bstep (se 1 (by rfl) ⟨3861482, by rfl⟩ : syracuseStep 5148643 = 7722965) B7722965
theorem B1708013 : Blo 531801 1708013 := bstep (se 3 (by rfl) ⟨320252, by rfl⟩ : syracuseStep 1708013 = 640505) B640505
theorem B1347587 : Blo 531801 1347587 := bstep (se 1 (by rfl) ⟨1010690, by rfl⟩ : syracuseStep 1347587 = 2021381) B2021381
theorem B1806353 : Blo 531801 1806353 := bstep (se 2 (by rfl) ⟨677382, by rfl⟩ : syracuseStep 1806353 = 1354765) B1354765
theorem B757841 : Blo 531801 757841 := bstep (se 2 (by rfl) ⟨284190, by rfl⟩ : syracuseStep 757841 = 568381) B568381
theorem B757955 : Blo 531801 757955 := bstep (se 1 (by rfl) ⟨568466, by rfl⟩ : syracuseStep 757955 = 1136933) B1136933
theorem B1347779 : Blo 531801 1347779 := bstep (se 1 (by rfl) ⟨1010834, by rfl⟩ : syracuseStep 1347779 = 2021669) B2021669
theorem B692435 : Blo 531801 692435 := bstep (se 1 (by rfl) ⟨519326, by rfl⟩ : syracuseStep 692435 = 1038653) B1038653
theorem B4559075 : Blo 531801 4559075 := bstep (se 1 (by rfl) ⟨3419306, by rfl⟩ : syracuseStep 4559075 = 6838613) B6838613
theorem B758035 : Blo 531801 758035 := bstep (se 1 (by rfl) ⟨568526, by rfl⟩ : syracuseStep 758035 = 1137053) B1137053
theorem B3477809 : Blo 531801 3477809 := bstep (se 2 (by rfl) ⟨1304178, by rfl⟩ : syracuseStep 3477809 = 2608357) B2608357
theorem B2560369 : Blo 531801 2560369 := bstep (se 2 (by rfl) ⟨960138, by rfl⟩ : syracuseStep 2560369 = 1920277) B1920277
theorem B4886897 : Blo 531801 4886897 := bstep (se 2 (by rfl) ⟨1832586, by rfl⟩ : syracuseStep 4886897 = 3665173) B3665173
theorem B922097 : Blo 531801 922097 := bstep (se 2 (by rfl) ⟨345786, by rfl⟩ : syracuseStep 922097 = 691573) B691573
theorem B1806893 : Blo 531801 1806893 := bstep (se 3 (by rfl) ⟨338792, by rfl⟩ : syracuseStep 1806893 = 677585) B677585
theorem B1806947 : Blo 531801 1806947 := bstep (se 1 (by rfl) ⟨1355210, by rfl⟩ : syracuseStep 1806947 = 2710421) B2710421
theorem B1446673 : Blo 531801 1446673 := bstep (se 2 (by rfl) ⟨542502, by rfl⟩ : syracuseStep 1446673 = 1085005) B1085005
theorem B758593 : Blo 531801 758593 := bstep (se 2 (by rfl) ⟨284472, by rfl⟩ : syracuseStep 758593 = 568945) B568945
theorem B1807217 : Blo 531801 1807217 := bstep (se 2 (by rfl) ⟨677706, by rfl⟩ : syracuseStep 1807217 = 1355413) B1355413
theorem B856993 : Blo 531801 856993 := bstep (se 2 (by rfl) ⟨321372, by rfl⟩ : syracuseStep 856993 = 642745) B642745
theorem B1217585 : Blo 531801 1217585 := bstep (se 2 (by rfl) ⟨456594, by rfl⟩ : syracuseStep 1217585 = 913189) B913189
theorem B1348721 : Blo 531801 1348721 := bstep (se 2 (by rfl) ⟨505770, by rfl⟩ : syracuseStep 1348721 = 1011541) B1011541
theorem B1348771 : Blo 531801 1348771 := bstep (se 1 (by rfl) ⟨1011578, by rfl⟩ : syracuseStep 1348771 = 2023157) B2023157
theorem B1348913 : Blo 531801 1348913 := bstep (se 2 (by rfl) ⟨505842, by rfl⟩ : syracuseStep 1348913 = 1011685) B1011685
theorem B1807757 : Blo 531801 1807757 := bstep (se 3 (by rfl) ⟨338954, by rfl⟩ : syracuseStep 1807757 = 677909) B677909
theorem B1807811 : Blo 531801 1807811 := bstep (se 1 (by rfl) ⟨1355858, by rfl⟩ : syracuseStep 1807811 = 2711717) B2711717
theorem B759299 : Blo 531801 759299 := bstep (se 1 (by rfl) ⟨569474, by rfl⟩ : syracuseStep 759299 = 1138949) B1138949
theorem B3282565 : Blo 531801 3282565 := bstep (se 4 (by rfl) ⟨307740, by rfl⟩ : syracuseStep 3282565 = 615481) B615481
theorem B1808081 : Blo 531801 1808081 := bstep (se 2 (by rfl) ⟨678030, by rfl⟩ : syracuseStep 1808081 = 1356061) B1356061
theorem B1283971 : Blo 531801 1283971 := bstep (se 1 (by rfl) ⟨962978, by rfl⟩ : syracuseStep 1283971 = 1925957) B1925957
theorem B6068195 : Blo 531801 6068195 := bstep (se 1 (by rfl) ⟨4551146, by rfl⟩ : syracuseStep 6068195 = 9102293) B9102293
theorem B1710193 : Blo 531801 1710193 := bstep (se 2 (by rfl) ⟨641322, by rfl⟩ : syracuseStep 1710193 = 1282645) B1282645
theorem B759937 : Blo 531801 759937 := bstep (se 2 (by rfl) ⟨284976, by rfl⟩ : syracuseStep 759937 = 569953) B569953
theorem B760051 : Blo 531801 760051 := bstep (se 1 (by rfl) ⟨570038, by rfl⟩ : syracuseStep 760051 = 1140077) B1140077
theorem B4921613 : Blo 531801 4921613 := bstep (se 3 (by rfl) ⟨922802, by rfl⟩ : syracuseStep 4921613 = 1845605) B1845605
theorem B1349905 : Blo 531801 1349905 := bstep (se 2 (by rfl) ⟨506214, by rfl⟩ : syracuseStep 1349905 = 1012429) B1012429
theorem B891155 : Blo 531801 891155 := bstep (se 1 (by rfl) ⟨668366, by rfl⟩ : syracuseStep 891155 = 1336733) B1336733
theorem B2693411 : Blo 531801 2693411 := bstep (se 1 (by rfl) ⟨2020058, by rfl⟩ : syracuseStep 2693411 = 4040117) B4040117
theorem B1710371 : Blo 531801 1710371 := bstep (se 1 (by rfl) ⟨1282778, by rfl⟩ : syracuseStep 1710371 = 2565557) B2565557
theorem B1350179 : Blo 531801 1350179 := bstep (se 1 (by rfl) ⟨1012634, by rfl⟩ : syracuseStep 1350179 = 2025269) B2025269
theorem B1284817 : Blo 531801 1284817 := bstep (se 2 (by rfl) ⟨481806, by rfl⟩ : syracuseStep 1284817 = 963613) B963613
theorem B1350371 : Blo 531801 1350371 := bstep (se 1 (by rfl) ⟨1012778, by rfl⟩ : syracuseStep 1350371 = 2025557) B2025557
theorem B3414797 : Blo 531801 3414797 := bstep (se 3 (by rfl) ⟨640274, by rfl⟩ : syracuseStep 3414797 = 1280549) B1280549
theorem B1284931 : Blo 531801 1284931 := bstep (se 1 (by rfl) ⟨963698, by rfl⟩ : syracuseStep 1284931 = 1927397) B1927397
theorem B2694221 : Blo 531801 2694221 := bstep (se 3 (by rfl) ⟨505166, by rfl⟩ : syracuseStep 2694221 = 1010333) B1010333
theorem B531811 : Blo 531801 531811 := bstep (se 1 (by rfl) ⟨398858, by rfl⟩ : syracuseStep 531811 = 797717) B797717
theorem B2596195 : Blo 531801 2596195 := bstep (se 1 (by rfl) ⟨1947146, by rfl⟩ : syracuseStep 2596195 = 3894293) B3894293
theorem B531827 : Blo 531801 531827 := bstep (se 1 (by rfl) ⟨398870, by rfl⟩ : syracuseStep 531827 = 797741) B797741
theorem B531843 : Blo 531801 531843 := bstep (se 1 (by rfl) ⟨398882, by rfl⟩ : syracuseStep 531843 = 797765) B797765
theorem B531859 : Blo 531801 531859 := bstep (se 1 (by rfl) ⟨398894, by rfl⟩ : syracuseStep 531859 = 797789) B797789
theorem B531875 : Blo 531801 531875 := bstep (se 1 (by rfl) ⟨398906, by rfl⟩ : syracuseStep 531875 = 797813) B797813
theorem B531891 : Blo 531801 531891 := bstep (se 1 (by rfl) ⟨398918, by rfl⟩ : syracuseStep 531891 = 797837) B797837
theorem B531907 : Blo 531801 531907 := bstep (se 1 (by rfl) ⟨398930, by rfl⟩ : syracuseStep 531907 = 797861) B797861
theorem B531923 : Blo 531801 531923 := bstep (se 1 (by rfl) ⟨398942, by rfl⟩ : syracuseStep 531923 = 797885) B797885
theorem B531939 : Blo 531801 531939 := bstep (se 1 (by rfl) ⟨398954, by rfl⟩ : syracuseStep 531939 = 797909) B797909
theorem B531955 : Blo 531801 531955 := bstep (se 1 (by rfl) ⟨398966, by rfl⟩ : syracuseStep 531955 = 797933) B797933
theorem B531971 : Blo 531801 531971 := bstep (se 1 (by rfl) ⟨398978, by rfl⟩ : syracuseStep 531971 = 797957) B797957
theorem B531987 : Blo 531801 531987 := bstep (se 1 (by rfl) ⟨398990, by rfl⟩ : syracuseStep 531987 = 797981) B797981
theorem B532003 : Blo 531801 532003 := bstep (se 1 (by rfl) ⟨399002, by rfl⟩ : syracuseStep 532003 = 798005) B798005
theorem B532019 : Blo 531801 532019 := bstep (se 1 (by rfl) ⟨399014, by rfl⟩ : syracuseStep 532019 = 798029) B798029
theorem B761395 : Blo 531801 761395 := bstep (se 1 (by rfl) ⟨571046, by rfl⟩ : syracuseStep 761395 = 1142093) B1142093
theorem B532035 : Blo 531801 532035 := bstep (se 1 (by rfl) ⟨399026, by rfl⟩ : syracuseStep 532035 = 798053) B798053
theorem B532051 : Blo 531801 532051 := bstep (se 1 (by rfl) ⟨399038, by rfl⟩ : syracuseStep 532051 = 798077) B798077
theorem B532067 : Blo 531801 532067 := bstep (se 1 (by rfl) ⟨399050, by rfl⟩ : syracuseStep 532067 = 798101) B798101
theorem B532083 : Blo 531801 532083 := bstep (se 1 (by rfl) ⟨399062, by rfl⟩ : syracuseStep 532083 = 798125) B798125
theorem B532099 : Blo 531801 532099 := bstep (se 1 (by rfl) ⟨399074, by rfl⟩ : syracuseStep 532099 = 798149) B798149
theorem B1351313 : Blo 531801 1351313 := bstep (se 2 (by rfl) ⟨506742, by rfl⟩ : syracuseStep 1351313 = 1013485) B1013485
theorem B532115 : Blo 531801 532115 := bstep (se 1 (by rfl) ⟨399086, by rfl⟩ : syracuseStep 532115 = 798173) B798173
theorem B532131 : Blo 531801 532131 := bstep (se 1 (by rfl) ⟨399098, by rfl⟩ : syracuseStep 532131 = 798197) B798197
theorem B1515181 : Blo 531801 1515181 := bstep (se 3 (by rfl) ⟨284096, by rfl⟩ : syracuseStep 1515181 = 568193) B568193
theorem B532147 : Blo 531801 532147 := bstep (se 1 (by rfl) ⟨399110, by rfl⟩ : syracuseStep 532147 = 798221) B798221
theorem B532163 : Blo 531801 532163 := bstep (se 1 (by rfl) ⟨399122, by rfl⟩ : syracuseStep 532163 = 798245) B798245
theorem B1351363 : Blo 531801 1351363 := bstep (se 1 (by rfl) ⟨1013522, by rfl⟩ : syracuseStep 1351363 = 2027045) B2027045
theorem B532179 : Blo 531801 532179 := bstep (se 1 (by rfl) ⟨399134, by rfl⟩ : syracuseStep 532179 = 798269) B798269
theorem B7282403 : Blo 531801 7282403 := bstep (se 1 (by rfl) ⟨5461802, by rfl⟩ : syracuseStep 7282403 = 10923605) B10923605
theorem B532195 : Blo 531801 532195 := bstep (se 1 (by rfl) ⟨399146, by rfl⟩ : syracuseStep 532195 = 798293) B798293
theorem B532211 : Blo 531801 532211 := bstep (se 1 (by rfl) ⟨399158, by rfl⟩ : syracuseStep 532211 = 798317) B798317
theorem B532227 : Blo 531801 532227 := bstep (se 1 (by rfl) ⟨399170, by rfl⟩ : syracuseStep 532227 = 798341) B798341
theorem B532243 : Blo 531801 532243 := bstep (se 1 (by rfl) ⟨399182, by rfl⟩ : syracuseStep 532243 = 798365) B798365
theorem B532259 : Blo 531801 532259 := bstep (se 1 (by rfl) ⟨399194, by rfl⟩ : syracuseStep 532259 = 798389) B798389
theorem B532275 : Blo 531801 532275 := bstep (se 1 (by rfl) ⟨399206, by rfl⟩ : syracuseStep 532275 = 798413) B798413
theorem B532291 : Blo 531801 532291 := bstep (se 1 (by rfl) ⟨399218, by rfl⟩ : syracuseStep 532291 = 798437) B798437
theorem B1515341 : Blo 531801 1515341 := bstep (se 3 (by rfl) ⟨284126, by rfl⟩ : syracuseStep 1515341 = 568253) B568253
theorem B1351505 : Blo 531801 1351505 := bstep (se 2 (by rfl) ⟨506814, by rfl⟩ : syracuseStep 1351505 = 1013629) B1013629
theorem B532307 : Blo 531801 532307 := bstep (se 1 (by rfl) ⟨399230, by rfl⟩ : syracuseStep 532307 = 798461) B798461
theorem B532323 : Blo 531801 532323 := bstep (se 1 (by rfl) ⟨399242, by rfl⟩ : syracuseStep 532323 = 798485) B798485
theorem B532339 : Blo 531801 532339 := bstep (se 1 (by rfl) ⟨399254, by rfl⟩ : syracuseStep 532339 = 798509) B798509
theorem B532355 : Blo 531801 532355 := bstep (se 1 (by rfl) ⟨399266, by rfl⟩ : syracuseStep 532355 = 798533) B798533
theorem B532371 : Blo 531801 532371 := bstep (se 1 (by rfl) ⟨399278, by rfl⟩ : syracuseStep 532371 = 798557) B798557
theorem B532387 : Blo 531801 532387 := bstep (se 1 (by rfl) ⟨399290, by rfl⟩ : syracuseStep 532387 = 798581) B798581
theorem B532403 : Blo 531801 532403 := bstep (se 1 (by rfl) ⟨399302, by rfl⟩ : syracuseStep 532403 = 798605) B798605
theorem B532419 : Blo 531801 532419 := bstep (se 1 (by rfl) ⟨399314, by rfl⟩ : syracuseStep 532419 = 798629) B798629
theorem B532435 : Blo 531801 532435 := bstep (se 1 (by rfl) ⟨399326, by rfl⟩ : syracuseStep 532435 = 798653) B798653
theorem B532451 : Blo 531801 532451 := bstep (se 1 (by rfl) ⟨399338, by rfl⟩ : syracuseStep 532451 = 798677) B798677
theorem B532467 : Blo 531801 532467 := bstep (se 1 (by rfl) ⟨399350, by rfl⟩ : syracuseStep 532467 = 798701) B798701
theorem B1515523 : Blo 531801 1515523 := bstep (se 1 (by rfl) ⟨1136642, by rfl⟩ : syracuseStep 1515523 = 2273285) B2273285
theorem B532483 : Blo 531801 532483 := bstep (se 1 (by rfl) ⟨399362, by rfl⟩ : syracuseStep 532483 = 798725) B798725
theorem B1712141 : Blo 531801 1712141 := bstep (se 3 (by rfl) ⟨321026, by rfl⟩ : syracuseStep 1712141 = 642053) B642053
theorem B1286161 : Blo 531801 1286161 := bstep (se 2 (by rfl) ⟨482310, by rfl⟩ : syracuseStep 1286161 = 964621) B964621
theorem B532499 : Blo 531801 532499 := bstep (se 1 (by rfl) ⟨399374, by rfl⟩ : syracuseStep 532499 = 798749) B798749
theorem B11706389 : Blo 531801 11706389 := bstep (se 6 (by rfl) ⟨274368, by rfl⟩ : syracuseStep 11706389 = 548737) B548737
theorem B532515 : Blo 531801 532515 := bstep (se 1 (by rfl) ⟨399386, by rfl⟩ : syracuseStep 532515 = 798773) B798773
theorem B532531 : Blo 531801 532531 := bstep (se 1 (by rfl) ⟨399398, by rfl⟩ : syracuseStep 532531 = 798797) B798797
theorem B532547 : Blo 531801 532547 := bstep (se 1 (by rfl) ⟨399410, by rfl⟩ : syracuseStep 532547 = 798821) B798821
theorem B532563 : Blo 531801 532563 := bstep (se 1 (by rfl) ⟨399422, by rfl⟩ : syracuseStep 532563 = 798845) B798845
theorem B532579 : Blo 531801 532579 := bstep (se 1 (by rfl) ⟨399434, by rfl⟩ : syracuseStep 532579 = 798869) B798869
theorem B532595 : Blo 531801 532595 := bstep (se 1 (by rfl) ⟨399446, by rfl⟩ : syracuseStep 532595 = 798893) B798893
theorem B532611 : Blo 531801 532611 := bstep (se 1 (by rfl) ⟨399458, by rfl⟩ : syracuseStep 532611 = 798917) B798917
theorem B532627 : Blo 531801 532627 := bstep (se 1 (by rfl) ⟨399470, by rfl⟩ : syracuseStep 532627 = 798941) B798941
theorem B532643 : Blo 531801 532643 := bstep (se 1 (by rfl) ⟨399482, by rfl⟩ : syracuseStep 532643 = 798965) B798965
theorem B532659 : Blo 531801 532659 := bstep (se 1 (by rfl) ⟨399494, by rfl⟩ : syracuseStep 532659 = 798989) B798989
theorem B532675 : Blo 531801 532675 := bstep (se 1 (by rfl) ⟨399506, by rfl⟩ : syracuseStep 532675 = 799013) B799013
theorem B532691 : Blo 531801 532691 := bstep (se 1 (by rfl) ⟨399518, by rfl⟩ : syracuseStep 532691 = 799037) B799037
theorem B532707 : Blo 531801 532707 := bstep (se 1 (by rfl) ⟨399530, by rfl⟩ : syracuseStep 532707 = 799061) B799061
theorem B532723 : Blo 531801 532723 := bstep (se 1 (by rfl) ⟨399542, by rfl⟩ : syracuseStep 532723 = 799085) B799085
theorem B532739 : Blo 531801 532739 := bstep (se 1 (by rfl) ⟨399554, by rfl⟩ : syracuseStep 532739 = 799109) B799109
theorem B532755 : Blo 531801 532755 := bstep (se 1 (by rfl) ⟨399566, by rfl⟩ : syracuseStep 532755 = 799133) B799133
theorem B532771 : Blo 531801 532771 := bstep (se 1 (by rfl) ⟨399578, by rfl⟩ : syracuseStep 532771 = 799157) B799157
theorem B532787 : Blo 531801 532787 := bstep (se 1 (by rfl) ⟨399590, by rfl⟩ : syracuseStep 532787 = 799181) B799181
theorem B532803 : Blo 531801 532803 := bstep (se 1 (by rfl) ⟨399602, by rfl⟩ : syracuseStep 532803 = 799205) B799205
theorem B532819 : Blo 531801 532819 := bstep (se 1 (by rfl) ⟨399614, by rfl⟩ : syracuseStep 532819 = 799229) B799229
theorem B532835 : Blo 531801 532835 := bstep (se 1 (by rfl) ⟨399626, by rfl⟩ : syracuseStep 532835 = 799253) B799253
theorem B598387 : Blo 531801 598387 := bstep (se 1 (by rfl) ⟨448790, by rfl⟩ : syracuseStep 598387 = 897581) B897581
theorem B532851 : Blo 531801 532851 := bstep (se 1 (by rfl) ⟨399638, by rfl⟩ : syracuseStep 532851 = 799277) B799277
theorem B532867 : Blo 531801 532867 := bstep (se 1 (by rfl) ⟨399650, by rfl⟩ : syracuseStep 532867 = 799301) B799301
theorem B532883 : Blo 531801 532883 := bstep (se 1 (by rfl) ⟨399662, by rfl⟩ : syracuseStep 532883 = 799325) B799325
theorem B532899 : Blo 531801 532899 := bstep (se 1 (by rfl) ⟨399674, by rfl⟩ : syracuseStep 532899 = 799349) B799349
theorem B532915 : Blo 531801 532915 := bstep (se 1 (by rfl) ⟨399686, by rfl⟩ : syracuseStep 532915 = 799373) B799373
theorem B532931 : Blo 531801 532931 := bstep (se 1 (by rfl) ⟨399698, by rfl⟩ : syracuseStep 532931 = 799397) B799397
theorem B532947 : Blo 531801 532947 := bstep (se 1 (by rfl) ⟨399710, by rfl⟩ : syracuseStep 532947 = 799421) B799421
theorem B532963 : Blo 531801 532963 := bstep (se 1 (by rfl) ⟨399722, by rfl⟩ : syracuseStep 532963 = 799445) B799445
theorem B532979 : Blo 531801 532979 := bstep (se 1 (by rfl) ⟨399734, by rfl⟩ : syracuseStep 532979 = 799469) B799469
theorem B598531 : Blo 531801 598531 := bstep (se 1 (by rfl) ⟨448898, by rfl⟩ : syracuseStep 598531 = 897797) B897797
theorem B532995 : Blo 531801 532995 := bstep (se 1 (by rfl) ⟨399746, by rfl⟩ : syracuseStep 532995 = 799493) B799493
theorem B533011 : Blo 531801 533011 := bstep (se 1 (by rfl) ⟨399758, by rfl⟩ : syracuseStep 533011 = 799517) B799517
theorem B533027 : Blo 531801 533027 := bstep (se 1 (by rfl) ⟨399770, by rfl⟩ : syracuseStep 533027 = 799541) B799541
theorem B533043 : Blo 531801 533043 := bstep (se 1 (by rfl) ⟨399782, by rfl⟩ : syracuseStep 533043 = 799565) B799565
theorem B533059 : Blo 531801 533059 := bstep (se 1 (by rfl) ⟨399794, by rfl⟩ : syracuseStep 533059 = 799589) B799589
theorem B959057 : Blo 531801 959057 := bstep (se 2 (by rfl) ⟨359646, by rfl⟩ : syracuseStep 959057 = 719293) B719293
theorem B533075 : Blo 531801 533075 := bstep (se 1 (by rfl) ⟨399806, by rfl⟩ : syracuseStep 533075 = 799613) B799613
theorem B533091 : Blo 531801 533091 := bstep (se 1 (by rfl) ⟨399818, by rfl⟩ : syracuseStep 533091 = 799637) B799637
theorem B533107 : Blo 531801 533107 := bstep (se 1 (by rfl) ⟨399830, by rfl⟩ : syracuseStep 533107 = 799661) B799661
theorem B533123 : Blo 531801 533123 := bstep (se 1 (by rfl) ⟨399842, by rfl⟩ : syracuseStep 533123 = 799685) B799685
theorem B598675 : Blo 531801 598675 := bstep (se 1 (by rfl) ⟨449006, by rfl⟩ : syracuseStep 598675 = 898013) B898013
theorem B533139 : Blo 531801 533139 := bstep (se 1 (by rfl) ⟨399854, by rfl⟩ : syracuseStep 533139 = 799709) B799709
theorem B762529 : Blo 531801 762529 := bstep (se 2 (by rfl) ⟨285948, by rfl⟩ : syracuseStep 762529 = 571897) B571897
theorem B533155 : Blo 531801 533155 := bstep (se 1 (by rfl) ⟨399866, by rfl⟩ : syracuseStep 533155 = 799733) B799733
theorem B533171 : Blo 531801 533171 := bstep (se 1 (by rfl) ⟨399878, by rfl⟩ : syracuseStep 533171 = 799757) B799757
theorem B533187 : Blo 531801 533187 := bstep (se 1 (by rfl) ⟨399890, by rfl⟩ : syracuseStep 533187 = 799781) B799781
theorem B533203 : Blo 531801 533203 := bstep (se 1 (by rfl) ⟨399902, by rfl⟩ : syracuseStep 533203 = 799805) B799805
theorem B533219 : Blo 531801 533219 := bstep (se 1 (by rfl) ⟨399914, by rfl⟩ : syracuseStep 533219 = 799829) B799829
theorem B533235 : Blo 531801 533235 := bstep (se 1 (by rfl) ⟨399926, by rfl⟩ : syracuseStep 533235 = 799853) B799853
theorem B762625 : Blo 531801 762625 := bstep (se 2 (by rfl) ⟨285984, by rfl⟩ : syracuseStep 762625 = 571969) B571969
theorem B533251 : Blo 531801 533251 := bstep (se 1 (by rfl) ⟨399938, by rfl⟩ : syracuseStep 533251 = 799877) B799877
theorem B533267 : Blo 531801 533267 := bstep (se 1 (by rfl) ⟨399950, by rfl⟩ : syracuseStep 533267 = 799901) B799901
theorem B598819 : Blo 531801 598819 := bstep (se 1 (by rfl) ⟨449114, by rfl⟩ : syracuseStep 598819 = 898229) B898229
theorem B533283 : Blo 531801 533283 := bstep (se 1 (by rfl) ⟨399962, by rfl⟩ : syracuseStep 533283 = 799925) B799925
theorem B1155875 : Blo 531801 1155875 := bstep (se 1 (by rfl) ⟨866906, by rfl⟩ : syracuseStep 1155875 = 1733813) B1733813
theorem B1352497 : Blo 531801 1352497 := bstep (se 2 (by rfl) ⟨507186, by rfl⟩ : syracuseStep 1352497 = 1014373) B1014373
theorem B533299 : Blo 531801 533299 := bstep (se 1 (by rfl) ⟨399974, by rfl⟩ : syracuseStep 533299 = 799949) B799949
theorem B533315 : Blo 531801 533315 := bstep (se 1 (by rfl) ⟨399986, by rfl⟩ : syracuseStep 533315 = 799973) B799973
theorem B2564941 : Blo 531801 2564941 := bstep (se 3 (by rfl) ⟨480926, by rfl⟩ : syracuseStep 2564941 = 961853) B961853
theorem B533331 : Blo 531801 533331 := bstep (se 1 (by rfl) ⟨399998, by rfl⟩ : syracuseStep 533331 = 799997) B799997
theorem B533347 : Blo 531801 533347 := bstep (se 1 (by rfl) ⟨400010, by rfl⟩ : syracuseStep 533347 = 800021) B800021
theorem B533363 : Blo 531801 533363 := bstep (se 1 (by rfl) ⟨400022, by rfl⟩ : syracuseStep 533363 = 800045) B800045
theorem B533379 : Blo 531801 533379 := bstep (se 1 (by rfl) ⟨400034, by rfl⟩ : syracuseStep 533379 = 800069) B800069
theorem B533395 : Blo 531801 533395 := bstep (se 1 (by rfl) ⟨400046, by rfl⟩ : syracuseStep 533395 = 800093) B800093
theorem B533411 : Blo 531801 533411 := bstep (se 1 (by rfl) ⟨400058, by rfl⟩ : syracuseStep 533411 = 800117) B800117
theorem B598963 : Blo 531801 598963 := bstep (se 1 (by rfl) ⟨449222, by rfl⟩ : syracuseStep 598963 = 898445) B898445
theorem B533427 : Blo 531801 533427 := bstep (se 1 (by rfl) ⟨400070, by rfl⟩ : syracuseStep 533427 = 800141) B800141
theorem B533443 : Blo 531801 533443 := bstep (se 1 (by rfl) ⟨400082, by rfl⟩ : syracuseStep 533443 = 800165) B800165
theorem B533459 : Blo 531801 533459 := bstep (se 1 (by rfl) ⟨400094, by rfl⟩ : syracuseStep 533459 = 800189) B800189
theorem B533475 : Blo 531801 533475 := bstep (se 1 (by rfl) ⟨400106, by rfl⟩ : syracuseStep 533475 = 800213) B800213
theorem B533491 : Blo 531801 533491 := bstep (se 1 (by rfl) ⟨400118, by rfl⟩ : syracuseStep 533491 = 800237) B800237
theorem B533507 : Blo 531801 533507 := bstep (se 1 (by rfl) ⟨400130, by rfl⟩ : syracuseStep 533507 = 800261) B800261
theorem B533523 : Blo 531801 533523 := bstep (se 1 (by rfl) ⟨400142, by rfl⟩ : syracuseStep 533523 = 800285) B800285
theorem B533539 : Blo 531801 533539 := bstep (se 1 (by rfl) ⟨400154, by rfl⟩ : syracuseStep 533539 = 800309) B800309
theorem B533555 : Blo 531801 533555 := bstep (se 1 (by rfl) ⟨400166, by rfl⟩ : syracuseStep 533555 = 800333) B800333
theorem B599107 : Blo 531801 599107 := bstep (se 1 (by rfl) ⟨449330, by rfl⟩ : syracuseStep 599107 = 898661) B898661
theorem B533571 : Blo 531801 533571 := bstep (se 1 (by rfl) ⟨400178, by rfl⟩ : syracuseStep 533571 = 800357) B800357
theorem B1352771 : Blo 531801 1352771 := bstep (se 1 (by rfl) ⟨1014578, by rfl⟩ : syracuseStep 1352771 = 2029157) B2029157
theorem B533587 : Blo 531801 533587 := bstep (se 1 (by rfl) ⟨400190, by rfl⟩ : syracuseStep 533587 = 800381) B800381
theorem B533603 : Blo 531801 533603 := bstep (se 1 (by rfl) ⟨400202, by rfl⟩ : syracuseStep 533603 = 800405) B800405
theorem B533619 : Blo 531801 533619 := bstep (se 1 (by rfl) ⟨400214, by rfl⟩ : syracuseStep 533619 = 800429) B800429
theorem B533635 : Blo 531801 533635 := bstep (se 1 (by rfl) ⟨400226, by rfl⟩ : syracuseStep 533635 = 800453) B800453
theorem B533651 : Blo 531801 533651 := bstep (se 1 (by rfl) ⟨400238, by rfl⟩ : syracuseStep 533651 = 800477) B800477
theorem B533667 : Blo 531801 533667 := bstep (se 1 (by rfl) ⟨400250, by rfl⟩ : syracuseStep 533667 = 800501) B800501
theorem B533683 : Blo 531801 533683 := bstep (se 1 (by rfl) ⟨400262, by rfl⟩ : syracuseStep 533683 = 800525) B800525
theorem B533699 : Blo 531801 533699 := bstep (se 1 (by rfl) ⟨400274, by rfl⟩ : syracuseStep 533699 = 800549) B800549
theorem B599251 : Blo 531801 599251 := bstep (se 1 (by rfl) ⟨449438, by rfl⟩ : syracuseStep 599251 = 898877) B898877
theorem B533715 : Blo 531801 533715 := bstep (se 1 (by rfl) ⟨400286, by rfl⟩ : syracuseStep 533715 = 800573) B800573
theorem B533731 : Blo 531801 533731 := bstep (se 1 (by rfl) ⟨400298, by rfl⟩ : syracuseStep 533731 = 800597) B800597
theorem B533747 : Blo 531801 533747 := bstep (se 1 (by rfl) ⟨400310, by rfl⟩ : syracuseStep 533747 = 800621) B800621
theorem B533763 : Blo 531801 533763 := bstep (se 1 (by rfl) ⟨400322, by rfl⟩ : syracuseStep 533763 = 800645) B800645
theorem B1352963 : Blo 531801 1352963 := bstep (se 1 (by rfl) ⟨1014722, by rfl⟩ : syracuseStep 1352963 = 2029445) B2029445
theorem B533779 : Blo 531801 533779 := bstep (se 1 (by rfl) ⟨400334, by rfl⟩ : syracuseStep 533779 = 800669) B800669
theorem B533795 : Blo 531801 533795 := bstep (se 1 (by rfl) ⟨400346, by rfl⟩ : syracuseStep 533795 = 800693) B800693
theorem B533811 : Blo 531801 533811 := bstep (se 1 (by rfl) ⟨400358, by rfl⟩ : syracuseStep 533811 = 800717) B800717
theorem B533827 : Blo 531801 533827 := bstep (se 1 (by rfl) ⟨400370, by rfl⟩ : syracuseStep 533827 = 800741) B800741
theorem B533843 : Blo 531801 533843 := bstep (se 1 (by rfl) ⟨400382, by rfl⟩ : syracuseStep 533843 = 800765) B800765
theorem B599395 : Blo 531801 599395 := bstep (se 1 (by rfl) ⟨449546, by rfl⟩ : syracuseStep 599395 = 899093) B899093
theorem B533859 : Blo 531801 533859 := bstep (se 1 (by rfl) ⟨400394, by rfl⟩ : syracuseStep 533859 = 800789) B800789
theorem B1516913 : Blo 531801 1516913 := bstep (se 2 (by rfl) ⟨568842, by rfl⟩ : syracuseStep 1516913 = 1137685) B1137685
theorem B533875 : Blo 531801 533875 := bstep (se 1 (by rfl) ⟨400406, by rfl⟩ : syracuseStep 533875 = 800813) B800813
theorem B533891 : Blo 531801 533891 := bstep (se 1 (by rfl) ⟨400418, by rfl⟩ : syracuseStep 533891 = 800837) B800837
theorem B533907 : Blo 531801 533907 := bstep (se 1 (by rfl) ⟨400430, by rfl⟩ : syracuseStep 533907 = 800861) B800861
theorem B533923 : Blo 531801 533923 := bstep (se 1 (by rfl) ⟨400442, by rfl⟩ : syracuseStep 533923 = 800885) B800885
theorem B533939 : Blo 531801 533939 := bstep (se 1 (by rfl) ⟨400454, by rfl⟩ : syracuseStep 533939 = 800909) B800909
theorem B533955 : Blo 531801 533955 := bstep (se 1 (by rfl) ⟨400466, by rfl⟩ : syracuseStep 533955 = 800933) B800933
theorem B533971 : Blo 531801 533971 := bstep (se 1 (by rfl) ⟨400478, by rfl⟩ : syracuseStep 533971 = 800957) B800957
theorem B533987 : Blo 531801 533987 := bstep (se 1 (by rfl) ⟨400490, by rfl⟩ : syracuseStep 533987 = 800981) B800981
theorem B599539 : Blo 531801 599539 := bstep (se 1 (by rfl) ⟨449654, by rfl⟩ : syracuseStep 599539 = 899309) B899309
theorem B534003 : Blo 531801 534003 := bstep (se 1 (by rfl) ⟨400502, by rfl⟩ : syracuseStep 534003 = 801005) B801005
theorem B534019 : Blo 531801 534019 := bstep (se 1 (by rfl) ⟨400514, by rfl⟩ : syracuseStep 534019 = 801029) B801029
theorem B534035 : Blo 531801 534035 := bstep (se 1 (by rfl) ⟨400526, by rfl⟩ : syracuseStep 534035 = 801053) B801053
theorem B534051 : Blo 531801 534051 := bstep (se 1 (by rfl) ⟨400538, by rfl⟩ : syracuseStep 534051 = 801077) B801077
theorem B534067 : Blo 531801 534067 := bstep (se 1 (by rfl) ⟨400550, by rfl⟩ : syracuseStep 534067 = 801101) B801101
theorem B534083 : Blo 531801 534083 := bstep (se 1 (by rfl) ⟨400562, by rfl⟩ : syracuseStep 534083 = 801125) B801125
theorem B534099 : Blo 531801 534099 := bstep (se 1 (by rfl) ⟨400574, by rfl⟩ : syracuseStep 534099 = 801149) B801149
theorem B534115 : Blo 531801 534115 := bstep (se 1 (by rfl) ⟨400586, by rfl⟩ : syracuseStep 534115 = 801173) B801173
theorem B534131 : Blo 531801 534131 := bstep (se 1 (by rfl) ⟨400598, by rfl⟩ : syracuseStep 534131 = 801197) B801197
theorem B599683 : Blo 531801 599683 := bstep (se 1 (by rfl) ⟨449762, by rfl⟩ : syracuseStep 599683 = 899525) B899525
theorem B534147 : Blo 531801 534147 := bstep (se 1 (by rfl) ⟨400610, by rfl⟩ : syracuseStep 534147 = 801221) B801221
theorem B534163 : Blo 531801 534163 := bstep (se 1 (by rfl) ⟨400622, by rfl⟩ : syracuseStep 534163 = 801245) B801245
theorem B534179 : Blo 531801 534179 := bstep (se 1 (by rfl) ⟨400634, by rfl⟩ : syracuseStep 534179 = 801269) B801269
theorem B534195 : Blo 531801 534195 := bstep (se 1 (by rfl) ⟨400646, by rfl⟩ : syracuseStep 534195 = 801293) B801293
theorem B927425 : Blo 531801 927425 := bstep (se 2 (by rfl) ⟨347784, by rfl⟩ : syracuseStep 927425 = 695569) B695569
theorem B534211 : Blo 531801 534211 := bstep (se 1 (by rfl) ⟨400658, by rfl⟩ : syracuseStep 534211 = 801317) B801317
theorem B534227 : Blo 531801 534227 := bstep (se 1 (by rfl) ⟨400670, by rfl⟩ : syracuseStep 534227 = 801341) B801341
theorem B534243 : Blo 531801 534243 := bstep (se 1 (by rfl) ⟨400682, by rfl⟩ : syracuseStep 534243 = 801365) B801365
theorem B534259 : Blo 531801 534259 := bstep (se 1 (by rfl) ⟨400694, by rfl⟩ : syracuseStep 534259 = 801389) B801389
theorem B730883 : Blo 531801 730883 := bstep (se 1 (by rfl) ⟨548162, by rfl⟩ : syracuseStep 730883 = 1096325) B1096325
theorem B534275 : Blo 531801 534275 := bstep (se 1 (by rfl) ⟨400706, by rfl⟩ : syracuseStep 534275 = 801413) B801413
theorem B6956813 : Blo 531801 6956813 := bstep (se 3 (by rfl) ⟨1304402, by rfl⟩ : syracuseStep 6956813 = 2608805) B2608805
theorem B599827 : Blo 531801 599827 := bstep (se 1 (by rfl) ⟨449870, by rfl⟩ : syracuseStep 599827 = 899741) B899741
theorem B534291 : Blo 531801 534291 := bstep (se 1 (by rfl) ⟨400718, by rfl⟩ : syracuseStep 534291 = 801437) B801437
theorem B534307 : Blo 531801 534307 := bstep (se 1 (by rfl) ⟨400730, by rfl⟩ : syracuseStep 534307 = 801461) B801461
theorem B534323 : Blo 531801 534323 := bstep (se 1 (by rfl) ⟨400742, by rfl⟩ : syracuseStep 534323 = 801485) B801485
theorem B534339 : Blo 531801 534339 := bstep (se 1 (by rfl) ⟨400754, by rfl⟩ : syracuseStep 534339 = 801509) B801509
theorem B534355 : Blo 531801 534355 := bstep (se 1 (by rfl) ⟨400766, by rfl⟩ : syracuseStep 534355 = 801533) B801533
theorem B534371 : Blo 531801 534371 := bstep (se 1 (by rfl) ⟨400778, by rfl⟩ : syracuseStep 534371 = 801557) B801557
theorem B1025905 : Blo 531801 1025905 := bstep (se 2 (by rfl) ⟨384714, by rfl⟩ : syracuseStep 1025905 = 769429) B769429
theorem B534387 : Blo 531801 534387 := bstep (se 1 (by rfl) ⟨400790, by rfl⟩ : syracuseStep 534387 = 801581) B801581
theorem B534403 : Blo 531801 534403 := bstep (se 1 (by rfl) ⟨400802, by rfl⟩ : syracuseStep 534403 = 801605) B801605
theorem B534419 : Blo 531801 534419 := bstep (se 1 (by rfl) ⟨400814, by rfl⟩ : syracuseStep 534419 = 801629) B801629
theorem B599971 : Blo 531801 599971 := bstep (se 1 (by rfl) ⟨449978, by rfl⟩ : syracuseStep 599971 = 899957) B899957
theorem B534435 : Blo 531801 534435 := bstep (se 1 (by rfl) ⟨400826, by rfl⟩ : syracuseStep 534435 = 801653) B801653
theorem B2697137 : Blo 531801 2697137 := bstep (se 2 (by rfl) ⟨1011426, by rfl⟩ : syracuseStep 2697137 = 2022853) B2022853
theorem B534451 : Blo 531801 534451 := bstep (se 1 (by rfl) ⟨400838, by rfl⟩ : syracuseStep 534451 = 801677) B801677
theorem B534467 : Blo 531801 534467 := bstep (se 1 (by rfl) ⟨400850, by rfl⟩ : syracuseStep 534467 = 801701) B801701
theorem B534483 : Blo 531801 534483 := bstep (se 1 (by rfl) ⟨400862, by rfl⟩ : syracuseStep 534483 = 801725) B801725
theorem B534499 : Blo 531801 534499 := bstep (se 1 (by rfl) ⟨400874, by rfl⟩ : syracuseStep 534499 = 801749) B801749
theorem B534515 : Blo 531801 534515 := bstep (se 1 (by rfl) ⟨400886, by rfl⟩ : syracuseStep 534515 = 801773) B801773
theorem B534531 : Blo 531801 534531 := bstep (se 1 (by rfl) ⟨400898, by rfl⟩ : syracuseStep 534531 = 801797) B801797
theorem B534547 : Blo 531801 534547 := bstep (se 1 (by rfl) ⟨400910, by rfl⟩ : syracuseStep 534547 = 801821) B801821
theorem B534563 : Blo 531801 534563 := bstep (se 1 (by rfl) ⟨400922, by rfl⟩ : syracuseStep 534563 = 801845) B801845
theorem B600115 : Blo 531801 600115 := bstep (se 1 (by rfl) ⟨450086, by rfl⟩ : syracuseStep 600115 = 900173) B900173
theorem B534579 : Blo 531801 534579 := bstep (se 1 (by rfl) ⟨400934, by rfl⟩ : syracuseStep 534579 = 801869) B801869
theorem B534595 : Blo 531801 534595 := bstep (se 1 (by rfl) ⟨400946, by rfl⟩ : syracuseStep 534595 = 801893) B801893
theorem B534611 : Blo 531801 534611 := bstep (se 1 (by rfl) ⟨400958, by rfl⟩ : syracuseStep 534611 = 801917) B801917
theorem B534627 : Blo 531801 534627 := bstep (se 1 (by rfl) ⟨400970, by rfl⟩ : syracuseStep 534627 = 801941) B801941
theorem B534643 : Blo 531801 534643 := bstep (se 1 (by rfl) ⟨400982, by rfl⟩ : syracuseStep 534643 = 801965) B801965
theorem B534659 : Blo 531801 534659 := bstep (se 1 (by rfl) ⟨400994, by rfl⟩ : syracuseStep 534659 = 801989) B801989
theorem B5187725 : Blo 531801 5187725 := bstep (se 3 (by rfl) ⟨972698, by rfl⟩ : syracuseStep 5187725 = 1945397) B1945397
theorem B534675 : Blo 531801 534675 := bstep (se 1 (by rfl) ⟨401006, by rfl⟩ : syracuseStep 534675 = 802013) B802013
theorem B534691 : Blo 531801 534691 := bstep (se 1 (by rfl) ⟨401018, by rfl⟩ : syracuseStep 534691 = 802037) B802037
theorem B1353905 : Blo 531801 1353905 := bstep (se 2 (by rfl) ⟨507714, by rfl⟩ : syracuseStep 1353905 = 1015429) B1015429
theorem B534707 : Blo 531801 534707 := bstep (se 1 (by rfl) ⟨401030, by rfl⟩ : syracuseStep 534707 = 802061) B802061
theorem B600259 : Blo 531801 600259 := bstep (se 1 (by rfl) ⟨450194, by rfl⟩ : syracuseStep 600259 = 900389) B900389
theorem B534723 : Blo 531801 534723 := bstep (se 1 (by rfl) ⟨401042, by rfl⟩ : syracuseStep 534723 = 802085) B802085
theorem B534739 : Blo 531801 534739 := bstep (se 1 (by rfl) ⟨401054, by rfl⟩ : syracuseStep 534739 = 802109) B802109
theorem B534755 : Blo 531801 534755 := bstep (se 1 (by rfl) ⟨401066, by rfl⟩ : syracuseStep 534755 = 802133) B802133
theorem B1353955 : Blo 531801 1353955 := bstep (se 1 (by rfl) ⟨1015466, by rfl⟩ : syracuseStep 1353955 = 2030933) B2030933
theorem B534771 : Blo 531801 534771 := bstep (se 1 (by rfl) ⟨401078, by rfl⟩ : syracuseStep 534771 = 802157) B802157
theorem B534787 : Blo 531801 534787 := bstep (se 1 (by rfl) ⟨401090, by rfl⟩ : syracuseStep 534787 = 802181) B802181
theorem B534803 : Blo 531801 534803 := bstep (se 1 (by rfl) ⟨401102, by rfl⟩ : syracuseStep 534803 = 802205) B802205
theorem B928019 : Blo 531801 928019 := bstep (se 1 (by rfl) ⟨696014, by rfl⟩ : syracuseStep 928019 = 1392029) B1392029
theorem B534819 : Blo 531801 534819 := bstep (se 1 (by rfl) ⟨401114, by rfl⟩ : syracuseStep 534819 = 802229) B802229
theorem B1517869 : Blo 531801 1517869 := bstep (se 3 (by rfl) ⟨284600, by rfl⟩ : syracuseStep 1517869 = 569201) B569201
theorem B534835 : Blo 531801 534835 := bstep (se 1 (by rfl) ⟨401126, by rfl⟩ : syracuseStep 534835 = 802253) B802253
theorem B534851 : Blo 531801 534851 := bstep (se 1 (by rfl) ⟨401138, by rfl⟩ : syracuseStep 534851 = 802277) B802277
theorem B600403 : Blo 531801 600403 := bstep (se 1 (by rfl) ⟨450302, by rfl⟩ : syracuseStep 600403 = 900605) B900605
theorem B534867 : Blo 531801 534867 := bstep (se 1 (by rfl) ⟨401150, by rfl⟩ : syracuseStep 534867 = 802301) B802301
theorem B534883 : Blo 531801 534883 := bstep (se 1 (by rfl) ⟨401162, by rfl⟩ : syracuseStep 534883 = 802325) B802325
theorem B1354097 : Blo 531801 1354097 := bstep (se 2 (by rfl) ⟨507786, by rfl⟩ : syracuseStep 1354097 = 1015573) B1015573
theorem B534899 : Blo 531801 534899 := bstep (se 1 (by rfl) ⟨401174, by rfl⟩ : syracuseStep 534899 = 802349) B802349
theorem B534915 : Blo 531801 534915 := bstep (se 1 (by rfl) ⟨401186, by rfl⟩ : syracuseStep 534915 = 802373) B802373
theorem B534931 : Blo 531801 534931 := bstep (se 1 (by rfl) ⟨401198, by rfl⟩ : syracuseStep 534931 = 802397) B802397
theorem B534947 : Blo 531801 534947 := bstep (se 1 (by rfl) ⟨401210, by rfl⟩ : syracuseStep 534947 = 802421) B802421
theorem B534963 : Blo 531801 534963 := bstep (se 1 (by rfl) ⟨401222, by rfl⟩ : syracuseStep 534963 = 802445) B802445
theorem B534979 : Blo 531801 534979 := bstep (se 1 (by rfl) ⟨401234, by rfl⟩ : syracuseStep 534979 = 802469) B802469
theorem B534995 : Blo 531801 534995 := bstep (se 1 (by rfl) ⟨401246, by rfl⟩ : syracuseStep 534995 = 802493) B802493
theorem B600547 : Blo 531801 600547 := bstep (se 1 (by rfl) ⟨450410, by rfl⟩ : syracuseStep 600547 = 900821) B900821
theorem B535011 : Blo 531801 535011 := bstep (se 1 (by rfl) ⟨401258, by rfl⟩ : syracuseStep 535011 = 802517) B802517
theorem B535027 : Blo 531801 535027 := bstep (se 1 (by rfl) ⟨401270, by rfl⟩ : syracuseStep 535027 = 802541) B802541
theorem B535043 : Blo 531801 535043 := bstep (se 1 (by rfl) ⟨401282, by rfl⟩ : syracuseStep 535043 = 802565) B802565
theorem B1518097 : Blo 531801 1518097 := bstep (se 2 (by rfl) ⟨569286, by rfl⟩ : syracuseStep 1518097 = 1138573) B1138573
theorem B535059 : Blo 531801 535059 := bstep (se 1 (by rfl) ⟨401294, by rfl⟩ : syracuseStep 535059 = 802589) B802589
theorem B535075 : Blo 531801 535075 := bstep (se 1 (by rfl) ⟨401306, by rfl⟩ : syracuseStep 535075 = 802613) B802613
theorem B535091 : Blo 531801 535091 := bstep (se 1 (by rfl) ⟨401318, by rfl⟩ : syracuseStep 535091 = 802637) B802637
theorem B535107 : Blo 531801 535107 := bstep (se 1 (by rfl) ⟨401330, by rfl⟩ : syracuseStep 535107 = 802661) B802661
theorem B4106821 : Blo 531801 4106821 := bstep (se 4 (by rfl) ⟨385014, by rfl⟩ : syracuseStep 4106821 = 770029) B770029
theorem B535123 : Blo 531801 535123 := bstep (se 1 (by rfl) ⟨401342, by rfl⟩ : syracuseStep 535123 = 802685) B802685
theorem B535139 : Blo 531801 535139 := bstep (se 1 (by rfl) ⟨401354, by rfl⟩ : syracuseStep 535139 = 802709) B802709
theorem B600691 : Blo 531801 600691 := bstep (se 1 (by rfl) ⟨450518, by rfl⟩ : syracuseStep 600691 = 901037) B901037
theorem B535155 : Blo 531801 535155 := bstep (se 1 (by rfl) ⟨401366, by rfl⟩ : syracuseStep 535155 = 802733) B802733
theorem B535171 : Blo 531801 535171 := bstep (se 1 (by rfl) ⟨401378, by rfl⟩ : syracuseStep 535171 = 802757) B802757
theorem B535187 : Blo 531801 535187 := bstep (se 1 (by rfl) ⟨401390, by rfl⟩ : syracuseStep 535187 = 802781) B802781
theorem B535203 : Blo 531801 535203 := bstep (se 1 (by rfl) ⟨401402, by rfl⟩ : syracuseStep 535203 = 802805) B802805
theorem B1518257 : Blo 531801 1518257 := bstep (se 2 (by rfl) ⟨569346, by rfl⟩ : syracuseStep 1518257 = 1138693) B1138693
theorem B535219 : Blo 531801 535219 := bstep (se 1 (by rfl) ⟨401414, by rfl⟩ : syracuseStep 535219 = 802829) B802829
theorem B535235 : Blo 531801 535235 := bstep (se 1 (by rfl) ⟨401426, by rfl⟩ : syracuseStep 535235 = 802853) B802853
theorem B535251 : Blo 531801 535251 := bstep (se 1 (by rfl) ⟨401438, by rfl⟩ : syracuseStep 535251 = 802877) B802877
theorem B535267 : Blo 531801 535267 := bstep (se 1 (by rfl) ⟨401450, by rfl⟩ : syracuseStep 535267 = 802901) B802901
theorem B535283 : Blo 531801 535283 := bstep (se 1 (by rfl) ⟨401462, by rfl⟩ : syracuseStep 535283 = 802925) B802925
theorem B600835 : Blo 531801 600835 := bstep (se 1 (by rfl) ⟨450626, by rfl⟩ : syracuseStep 600835 = 901253) B901253
theorem B535299 : Blo 531801 535299 := bstep (se 1 (by rfl) ⟨401474, by rfl⟩ : syracuseStep 535299 = 802949) B802949
theorem B535315 : Blo 531801 535315 := bstep (se 1 (by rfl) ⟨401486, by rfl⟩ : syracuseStep 535315 = 802973) B802973
theorem B1518371 : Blo 531801 1518371 := bstep (se 1 (by rfl) ⟨1138778, by rfl⟩ : syracuseStep 1518371 = 2277557) B2277557
theorem B535331 : Blo 531801 535331 := bstep (se 1 (by rfl) ⟨401498, by rfl⟩ : syracuseStep 535331 = 802997) B802997
theorem B535347 : Blo 531801 535347 := bstep (se 1 (by rfl) ⟨401510, by rfl⟩ : syracuseStep 535347 = 803021) B803021
theorem B535363 : Blo 531801 535363 := bstep (se 1 (by rfl) ⟨401522, by rfl⟩ : syracuseStep 535363 = 803045) B803045
theorem B3418949 : Blo 531801 3418949 := bstep (se 4 (by rfl) ⟨320526, by rfl⟩ : syracuseStep 3418949 = 641053) B641053
theorem B535379 : Blo 531801 535379 := bstep (se 1 (by rfl) ⟨401534, by rfl⟩ : syracuseStep 535379 = 803069) B803069
theorem B535395 : Blo 531801 535395 := bstep (se 1 (by rfl) ⟨401546, by rfl⟩ : syracuseStep 535395 = 803093) B803093
theorem B535411 : Blo 531801 535411 := bstep (se 1 (by rfl) ⟨401558, by rfl⟩ : syracuseStep 535411 = 803117) B803117
theorem B535427 : Blo 531801 535427 := bstep (se 1 (by rfl) ⟨401570, by rfl⟩ : syracuseStep 535427 = 803141) B803141
theorem B600979 : Blo 531801 600979 := bstep (se 1 (by rfl) ⟨450734, by rfl⟩ : syracuseStep 600979 = 901469) B901469
theorem B535443 : Blo 531801 535443 := bstep (se 1 (by rfl) ⟨401582, by rfl⟩ : syracuseStep 535443 = 803165) B803165
theorem B535459 : Blo 531801 535459 := bstep (se 1 (by rfl) ⟨401594, by rfl⟩ : syracuseStep 535459 = 803189) B803189
theorem B535475 : Blo 531801 535475 := bstep (se 1 (by rfl) ⟨401606, by rfl⟩ : syracuseStep 535475 = 803213) B803213
theorem B535491 : Blo 531801 535491 := bstep (se 1 (by rfl) ⟨401618, by rfl⟩ : syracuseStep 535491 = 803237) B803237
theorem B535507 : Blo 531801 535507 := bstep (se 1 (by rfl) ⟨401630, by rfl⟩ : syracuseStep 535507 = 803261) B803261
theorem B535523 : Blo 531801 535523 := bstep (se 1 (by rfl) ⟨401642, by rfl⟩ : syracuseStep 535523 = 803285) B803285
theorem B535539 : Blo 531801 535539 := bstep (se 1 (by rfl) ⟨401654, by rfl⟩ : syracuseStep 535539 = 803309) B803309
theorem B535555 : Blo 531801 535555 := bstep (se 1 (by rfl) ⟨401666, by rfl⟩ : syracuseStep 535555 = 803333) B803333
theorem B535571 : Blo 531801 535571 := bstep (se 1 (by rfl) ⟨401678, by rfl⟩ : syracuseStep 535571 = 803357) B803357
theorem B797729 : Blo 531801 797729 := bstep (se 2 (by rfl) ⟨299148, by rfl⟩ : syracuseStep 797729 = 598297) B598297
theorem B601123 : Blo 531801 601123 := bstep (se 1 (by rfl) ⟨450842, by rfl⟩ : syracuseStep 601123 = 901685) B901685
theorem B535587 : Blo 531801 535587 := bstep (se 1 (by rfl) ⟨401690, by rfl⟩ : syracuseStep 535587 = 803381) B803381
theorem B797747 : Blo 531801 797747 := bstep (se 1 (by rfl) ⟨598310, by rfl⟩ : syracuseStep 797747 = 1196621) B1196621
theorem B535603 : Blo 531801 535603 := bstep (se 1 (by rfl) ⟨401702, by rfl⟩ : syracuseStep 535603 = 803405) B803405
theorem B535619 : Blo 531801 535619 := bstep (se 1 (by rfl) ⟨401714, by rfl⟩ : syracuseStep 535619 = 803429) B803429
theorem B797777 : Blo 531801 797777 := bstep (se 2 (by rfl) ⟨299166, by rfl⟩ : syracuseStep 797777 = 598333) B598333
theorem B535635 : Blo 531801 535635 := bstep (se 1 (by rfl) ⟨401726, by rfl⟩ : syracuseStep 535635 = 803453) B803453
theorem B797795 : Blo 531801 797795 := bstep (se 1 (by rfl) ⟨598346, by rfl⟩ : syracuseStep 797795 = 1196693) B1196693
theorem B535651 : Blo 531801 535651 := bstep (se 1 (by rfl) ⟨401738, by rfl⟩ : syracuseStep 535651 = 803477) B803477
theorem B6859889 : Blo 531801 6859889 := bstep (se 2 (by rfl) ⟨2572458, by rfl⟩ : syracuseStep 6859889 = 5144917) B5144917
theorem B535667 : Blo 531801 535667 := bstep (se 1 (by rfl) ⟨401750, by rfl⟩ : syracuseStep 535667 = 803501) B803501
theorem B797825 : Blo 531801 797825 := bstep (se 2 (by rfl) ⟨299184, by rfl⟩ : syracuseStep 797825 = 598369) B598369
theorem B535683 : Blo 531801 535683 := bstep (se 1 (by rfl) ⟨401762, by rfl⟩ : syracuseStep 535683 = 803525) B803525
theorem B797843 : Blo 531801 797843 := bstep (se 1 (by rfl) ⟨598382, by rfl⟩ : syracuseStep 797843 = 1196765) B1196765
theorem B535699 : Blo 531801 535699 := bstep (se 1 (by rfl) ⟨401774, by rfl⟩ : syracuseStep 535699 = 803549) B803549
theorem B535715 : Blo 531801 535715 := bstep (se 1 (by rfl) ⟨401786, by rfl⟩ : syracuseStep 535715 = 803573) B803573
theorem B797873 : Blo 531801 797873 := bstep (se 2 (by rfl) ⟨299202, by rfl⟩ : syracuseStep 797873 = 598405) B598405
theorem B601267 : Blo 531801 601267 := bstep (se 1 (by rfl) ⟨450950, by rfl⟩ : syracuseStep 601267 = 901901) B901901
theorem B535731 : Blo 531801 535731 := bstep (se 1 (by rfl) ⟨401798, by rfl⟩ : syracuseStep 535731 = 803597) B803597
theorem B797891 : Blo 531801 797891 := bstep (se 1 (by rfl) ⟨598418, by rfl⟩ : syracuseStep 797891 = 1196837) B1196837
theorem B535747 : Blo 531801 535747 := bstep (se 1 (by rfl) ⟨401810, by rfl⟩ : syracuseStep 535747 = 803621) B803621
theorem B535763 : Blo 531801 535763 := bstep (se 1 (by rfl) ⟨401822, by rfl⟩ : syracuseStep 535763 = 803645) B803645
theorem B797921 : Blo 531801 797921 := bstep (se 2 (by rfl) ⟨299220, by rfl⟩ : syracuseStep 797921 = 598441) B598441
theorem B535779 : Blo 531801 535779 := bstep (se 1 (by rfl) ⟨401834, by rfl⟩ : syracuseStep 535779 = 803669) B803669
theorem B797939 : Blo 531801 797939 := bstep (se 1 (by rfl) ⟨598454, by rfl⟩ : syracuseStep 797939 = 1196909) B1196909
theorem B535795 : Blo 531801 535795 := bstep (se 1 (by rfl) ⟨401846, by rfl⟩ : syracuseStep 535795 = 803693) B803693
theorem B797969 : Blo 531801 797969 := bstep (se 2 (by rfl) ⟨299238, by rfl⟩ : syracuseStep 797969 = 598477) B598477
theorem B797987 : Blo 531801 797987 := bstep (se 1 (by rfl) ⟨598490, by rfl⟩ : syracuseStep 797987 = 1196981) B1196981
theorem B798017 : Blo 531801 798017 := bstep (se 2 (by rfl) ⟨299256, by rfl⟩ : syracuseStep 798017 = 598513) B598513
theorem B601411 : Blo 531801 601411 := bstep (se 1 (by rfl) ⟨451058, by rfl⟩ : syracuseStep 601411 = 902117) B902117
theorem B1355089 : Blo 531801 1355089 := bstep (se 2 (by rfl) ⟨508158, by rfl⟩ : syracuseStep 1355089 = 1016317) B1016317
theorem B798035 : Blo 531801 798035 := bstep (se 1 (by rfl) ⟨598526, by rfl⟩ : syracuseStep 798035 = 1197053) B1197053
theorem B2698595 : Blo 531801 2698595 := bstep (se 1 (by rfl) ⟨2023946, by rfl⟩ : syracuseStep 2698595 = 4047893) B4047893
theorem B798065 : Blo 531801 798065 := bstep (se 2 (by rfl) ⟨299274, by rfl⟩ : syracuseStep 798065 = 598549) B598549
theorem B798083 : Blo 531801 798083 := bstep (se 1 (by rfl) ⟨598562, by rfl⟩ : syracuseStep 798083 = 1197125) B1197125
theorem B798113 : Blo 531801 798113 := bstep (se 2 (by rfl) ⟨299292, by rfl⟩ : syracuseStep 798113 = 598585) B598585
theorem B961969 : Blo 531801 961969 := bstep (se 2 (by rfl) ⟨360738, by rfl⟩ : syracuseStep 961969 = 721477) B721477
theorem B1027505 : Blo 531801 1027505 := bstep (se 2 (by rfl) ⟨385314, by rfl⟩ : syracuseStep 1027505 = 770629) B770629
theorem B798131 : Blo 531801 798131 := bstep (se 1 (by rfl) ⟨598598, by rfl⟩ : syracuseStep 798131 = 1197197) B1197197
theorem B1715651 : Blo 531801 1715651 := bstep (se 1 (by rfl) ⟨1286738, by rfl⟩ : syracuseStep 1715651 = 2573477) B2573477
theorem B798161 : Blo 531801 798161 := bstep (se 2 (by rfl) ⟨299310, by rfl⟩ : syracuseStep 798161 = 598621) B598621
theorem B568787 : Blo 531801 568787 := bstep (se 1 (by rfl) ⟨426590, by rfl⟩ : syracuseStep 568787 = 853181) B853181
theorem B601555 : Blo 531801 601555 := bstep (se 1 (by rfl) ⟨451166, by rfl⟩ : syracuseStep 601555 = 902333) B902333
theorem B798179 : Blo 531801 798179 := bstep (se 1 (by rfl) ⟨598634, by rfl⟩ : syracuseStep 798179 = 1197269) B1197269
theorem B798209 : Blo 531801 798209 := bstep (se 2 (by rfl) ⟨299328, by rfl⟩ : syracuseStep 798209 = 598657) B598657
theorem B798227 : Blo 531801 798227 := bstep (se 1 (by rfl) ⟨598670, by rfl⟩ : syracuseStep 798227 = 1197341) B1197341
theorem B1846819 : Blo 531801 1846819 := bstep (se 1 (by rfl) ⟨1385114, by rfl⟩ : syracuseStep 1846819 = 2770229) B2770229
theorem B798257 : Blo 531801 798257 := bstep (se 2 (by rfl) ⟨299346, by rfl⟩ : syracuseStep 798257 = 598693) B598693
theorem B798275 : Blo 531801 798275 := bstep (se 1 (by rfl) ⟨598706, by rfl⟩ : syracuseStep 798275 = 1197413) B1197413
theorem B798305 : Blo 531801 798305 := bstep (se 2 (by rfl) ⟨299364, by rfl⟩ : syracuseStep 798305 = 598729) B598729
theorem B601699 : Blo 531801 601699 := bstep (se 1 (by rfl) ⟨451274, by rfl⟩ : syracuseStep 601699 = 902549) B902549
theorem B1355363 : Blo 531801 1355363 := bstep (se 1 (by rfl) ⟨1016522, by rfl⟩ : syracuseStep 1355363 = 2033045) B2033045
theorem B798323 : Blo 531801 798323 := bstep (se 1 (by rfl) ⟨598742, by rfl⟩ : syracuseStep 798323 = 1197485) B1197485
theorem B798353 : Blo 531801 798353 := bstep (se 2 (by rfl) ⟨299382, by rfl⟩ : syracuseStep 798353 = 598765) B598765
theorem B798371 : Blo 531801 798371 := bstep (se 1 (by rfl) ⟨598778, by rfl⟩ : syracuseStep 798371 = 1197557) B1197557
theorem B2928305 : Blo 531801 2928305 := bstep (se 2 (by rfl) ⟨1098114, by rfl⟩ : syracuseStep 2928305 = 2196229) B2196229
theorem B798401 : Blo 531801 798401 := bstep (se 2 (by rfl) ⟨299400, by rfl⟩ : syracuseStep 798401 = 598801) B598801
theorem B798419 : Blo 531801 798419 := bstep (se 1 (by rfl) ⟨598814, by rfl⟩ : syracuseStep 798419 = 1197629) B1197629
theorem B1650403 : Blo 531801 1650403 := bstep (se 1 (by rfl) ⟨1237802, by rfl⟩ : syracuseStep 1650403 = 2475605) B2475605
theorem B798449 : Blo 531801 798449 := bstep (se 2 (by rfl) ⟨299418, by rfl⟩ : syracuseStep 798449 = 598837) B598837
theorem B601843 : Blo 531801 601843 := bstep (se 1 (by rfl) ⟨451382, by rfl⟩ : syracuseStep 601843 = 902765) B902765
theorem B798467 : Blo 531801 798467 := bstep (se 1 (by rfl) ⟨598850, by rfl⟩ : syracuseStep 798467 = 1197701) B1197701
theorem B1519373 : Blo 531801 1519373 := bstep (se 3 (by rfl) ⟨284882, by rfl⟩ : syracuseStep 1519373 = 569765) B569765
theorem B798497 : Blo 531801 798497 := bstep (se 2 (by rfl) ⟨299436, by rfl⟩ : syracuseStep 798497 = 598873) B598873
theorem B1355555 : Blo 531801 1355555 := bstep (se 1 (by rfl) ⟨1016666, by rfl⟩ : syracuseStep 1355555 = 2033333) B2033333
theorem B798515 : Blo 531801 798515 := bstep (se 1 (by rfl) ⟨598886, by rfl⟩ : syracuseStep 798515 = 1197773) B1197773
theorem B798545 : Blo 531801 798545 := bstep (se 2 (by rfl) ⟨299454, by rfl⟩ : syracuseStep 798545 = 598909) B598909
theorem B798563 : Blo 531801 798563 := bstep (se 1 (by rfl) ⟨598922, by rfl⟩ : syracuseStep 798563 = 1197845) B1197845
theorem B798593 : Blo 531801 798593 := bstep (se 2 (by rfl) ⟨299472, by rfl⟩ : syracuseStep 798593 = 598945) B598945
theorem B601987 : Blo 531801 601987 := bstep (se 1 (by rfl) ⟨451490, by rfl⟩ : syracuseStep 601987 = 902981) B902981
theorem B2895749 : Blo 531801 2895749 := bstep (se 4 (by rfl) ⟨271476, by rfl⟩ : syracuseStep 2895749 = 542953) B542953
theorem B3092357 : Blo 531801 3092357 := bstep (se 4 (by rfl) ⟨289908, by rfl⟩ : syracuseStep 3092357 = 579817) B579817
theorem B798611 : Blo 531801 798611 := bstep (se 1 (by rfl) ⟨598958, by rfl⟩ : syracuseStep 798611 = 1197917) B1197917
theorem B798641 : Blo 531801 798641 := bstep (se 2 (by rfl) ⟨299490, by rfl⟩ : syracuseStep 798641 = 598981) B598981
theorem B798659 : Blo 531801 798659 := bstep (se 1 (by rfl) ⟨598994, by rfl⟩ : syracuseStep 798659 = 1197989) B1197989
theorem B1519555 : Blo 531801 1519555 := bstep (se 1 (by rfl) ⟨1139666, by rfl⟩ : syracuseStep 1519555 = 2279333) B2279333
theorem B17379269 : Blo 531801 17379269 := bstep (se 4 (by rfl) ⟨1629306, by rfl⟩ : syracuseStep 17379269 = 3258613) B3258613
theorem B798689 : Blo 531801 798689 := bstep (se 2 (by rfl) ⟨299508, by rfl⟩ : syracuseStep 798689 = 599017) B599017
theorem B798707 : Blo 531801 798707 := bstep (se 1 (by rfl) ⟨599030, by rfl⟩ : syracuseStep 798707 = 1198061) B1198061
theorem B798737 : Blo 531801 798737 := bstep (se 2 (by rfl) ⟨299526, by rfl⟩ : syracuseStep 798737 = 599053) B599053
theorem B1716241 : Blo 531801 1716241 := bstep (se 2 (by rfl) ⟨643590, by rfl⟩ : syracuseStep 1716241 = 1287181) B1287181
theorem B602131 : Blo 531801 602131 := bstep (se 1 (by rfl) ⟨451598, by rfl⟩ : syracuseStep 602131 = 903197) B903197
theorem B798755 : Blo 531801 798755 := bstep (se 1 (by rfl) ⟨599066, by rfl⟩ : syracuseStep 798755 = 1198133) B1198133
theorem B798785 : Blo 531801 798785 := bstep (se 2 (by rfl) ⟨299544, by rfl⟩ : syracuseStep 798785 = 599089) B599089
theorem B798803 : Blo 531801 798803 := bstep (se 1 (by rfl) ⟨599102, by rfl⟩ : syracuseStep 798803 = 1198205) B1198205
theorem B1519715 : Blo 531801 1519715 := bstep (se 1 (by rfl) ⟨1139786, by rfl⟩ : syracuseStep 1519715 = 2279573) B2279573
theorem B1650797 : Blo 531801 1650797 := bstep (se 3 (by rfl) ⟨309524, by rfl⟩ : syracuseStep 1650797 = 619049) B619049
theorem B798833 : Blo 531801 798833 := bstep (se 2 (by rfl) ⟨299562, by rfl⟩ : syracuseStep 798833 = 599125) B599125
theorem B798851 : Blo 531801 798851 := bstep (se 1 (by rfl) ⟨599138, by rfl⟩ : syracuseStep 798851 = 1198277) B1198277
theorem B2699405 : Blo 531801 2699405 := bstep (se 3 (by rfl) ⟨506138, by rfl⟩ : syracuseStep 2699405 = 1012277) B1012277
theorem B798881 : Blo 531801 798881 := bstep (se 2 (by rfl) ⟨299580, by rfl⟩ : syracuseStep 798881 = 599161) B599161
theorem B602275 : Blo 531801 602275 := bstep (se 1 (by rfl) ⟨451706, by rfl⟩ : syracuseStep 602275 = 903413) B903413
theorem B798899 : Blo 531801 798899 := bstep (se 1 (by rfl) ⟨599174, by rfl⟩ : syracuseStep 798899 = 1198349) B1198349
theorem B569539 : Blo 531801 569539 := bstep (se 1 (by rfl) ⟨427154, by rfl⟩ : syracuseStep 569539 = 854309) B854309
theorem B798929 : Blo 531801 798929 := bstep (se 2 (by rfl) ⟨299598, by rfl⟩ : syracuseStep 798929 = 599197) B599197
theorem B798947 : Blo 531801 798947 := bstep (se 1 (by rfl) ⟨599210, by rfl⟩ : syracuseStep 798947 = 1198421) B1198421
theorem B798977 : Blo 531801 798977 := bstep (se 2 (by rfl) ⟨299616, by rfl⟩ : syracuseStep 798977 = 599233) B599233
theorem B1028369 : Blo 531801 1028369 := bstep (se 2 (by rfl) ⟨385638, by rfl⟩ : syracuseStep 1028369 = 771277) B771277
theorem B798995 : Blo 531801 798995 := bstep (se 1 (by rfl) ⟨599246, by rfl⟩ : syracuseStep 798995 = 1198493) B1198493
theorem B799025 : Blo 531801 799025 := bstep (se 2 (by rfl) ⟨299634, by rfl⟩ : syracuseStep 799025 = 599269) B599269
theorem B3256625 : Blo 531801 3256625 := bstep (se 2 (by rfl) ⟨1221234, by rfl⟩ : syracuseStep 3256625 = 2442469) B2442469
theorem B602419 : Blo 531801 602419 := bstep (se 1 (by rfl) ⟨451814, by rfl⟩ : syracuseStep 602419 = 903629) B903629
theorem B799043 : Blo 531801 799043 := bstep (se 1 (by rfl) ⟨599282, by rfl⟩ : syracuseStep 799043 = 1198565) B1198565
theorem B799073 : Blo 531801 799073 := bstep (se 2 (by rfl) ⟨299652, by rfl⟩ : syracuseStep 799073 = 599305) B599305
theorem B799091 : Blo 531801 799091 := bstep (se 1 (by rfl) ⟨599318, by rfl⟩ : syracuseStep 799091 = 1198637) B1198637
theorem B799121 : Blo 531801 799121 := bstep (se 2 (by rfl) ⟨299670, by rfl⟩ : syracuseStep 799121 = 599341) B599341
theorem B799139 : Blo 531801 799139 := bstep (se 1 (by rfl) ⟨599354, by rfl⟩ : syracuseStep 799139 = 1198709) B1198709
theorem B7287221 : Blo 531801 7287221 := bstep (se 5 (by rfl) ⟨341588, by rfl⟩ : syracuseStep 7287221 = 683177) B683177
theorem B897473 : Blo 531801 897473 := bstep (se 2 (by rfl) ⟨336552, by rfl⟩ : syracuseStep 897473 = 673105) B673105
theorem B799169 : Blo 531801 799169 := bstep (se 2 (by rfl) ⟨299688, by rfl⟩ : syracuseStep 799169 = 599377) B599377
theorem B602563 : Blo 531801 602563 := bstep (se 1 (by rfl) ⟨451922, by rfl⟩ : syracuseStep 602563 = 903845) B903845
theorem B799187 : Blo 531801 799187 := bstep (se 1 (by rfl) ⟨599390, by rfl⟩ : syracuseStep 799187 = 1198781) B1198781
theorem B799217 : Blo 531801 799217 := bstep (se 2 (by rfl) ⟨299706, by rfl⟩ : syracuseStep 799217 = 599413) B599413
theorem B799235 : Blo 531801 799235 := bstep (se 1 (by rfl) ⟨599426, by rfl⟩ : syracuseStep 799235 = 1198853) B1198853
theorem B799265 : Blo 531801 799265 := bstep (se 2 (by rfl) ⟨299724, by rfl⟩ : syracuseStep 799265 = 599449) B599449
theorem B3551779 : Blo 531801 3551779 := bstep (se 1 (by rfl) ⟨2663834, by rfl⟩ : syracuseStep 3551779 = 5327669) B5327669
theorem B799283 : Blo 531801 799283 := bstep (se 1 (by rfl) ⟨599462, by rfl⟩ : syracuseStep 799283 = 1198925) B1198925
theorem B897601 : Blo 531801 897601 := bstep (se 2 (by rfl) ⟨336600, by rfl⟩ : syracuseStep 897601 = 673201) B673201
theorem B799313 : Blo 531801 799313 := bstep (se 2 (by rfl) ⟨299742, by rfl⟩ : syracuseStep 799313 = 599485) B599485
theorem B602707 : Blo 531801 602707 := bstep (se 1 (by rfl) ⟨452030, by rfl⟩ : syracuseStep 602707 = 904061) B904061
theorem B897635 : Blo 531801 897635 := bstep (se 1 (by rfl) ⟨673226, by rfl⟩ : syracuseStep 897635 = 1346453) B1346453
theorem B799331 : Blo 531801 799331 := bstep (se 1 (by rfl) ⟨599498, by rfl⟩ : syracuseStep 799331 = 1198997) B1198997
theorem B799361 : Blo 531801 799361 := bstep (se 2 (by rfl) ⟨299760, by rfl⟩ : syracuseStep 799361 = 599521) B599521
theorem B2273933 : Blo 531801 2273933 := bstep (se 3 (by rfl) ⟨426362, by rfl⟩ : syracuseStep 2273933 = 852725) B852725
theorem B799379 : Blo 531801 799379 := bstep (se 1 (by rfl) ⟨599534, by rfl⟩ : syracuseStep 799379 = 1199069) B1199069
theorem B799409 : Blo 531801 799409 := bstep (se 2 (by rfl) ⟨299778, by rfl⟩ : syracuseStep 799409 = 599557) B599557
theorem B799427 : Blo 531801 799427 := bstep (se 1 (by rfl) ⟨599570, by rfl⟩ : syracuseStep 799427 = 1199141) B1199141
theorem B799457 : Blo 531801 799457 := bstep (se 2 (by rfl) ⟨299796, by rfl⟩ : syracuseStep 799457 = 599593) B599593
theorem B897763 : Blo 531801 897763 := bstep (se 1 (by rfl) ⟨673322, by rfl⟩ : syracuseStep 897763 = 1346645) B1346645
theorem B799475 : Blo 531801 799475 := bstep (se 1 (by rfl) ⟨599606, by rfl⟩ : syracuseStep 799475 = 1199213) B1199213
theorem B799505 : Blo 531801 799505 := bstep (se 2 (by rfl) ⟨299814, by rfl⟩ : syracuseStep 799505 = 599629) B599629
theorem B799523 : Blo 531801 799523 := bstep (se 1 (by rfl) ⟨599642, by rfl⟩ : syracuseStep 799523 = 1199285) B1199285
theorem B799553 : Blo 531801 799553 := bstep (se 2 (by rfl) ⟨299832, by rfl⟩ : syracuseStep 799553 = 599665) B599665
theorem B799571 : Blo 531801 799571 := bstep (se 1 (by rfl) ⟨599678, by rfl⟩ : syracuseStep 799571 = 1199357) B1199357
theorem B897905 : Blo 531801 897905 := bstep (se 2 (by rfl) ⟨336714, by rfl⟩ : syracuseStep 897905 = 673429) B673429
theorem B799601 : Blo 531801 799601 := bstep (se 2 (by rfl) ⟨299850, by rfl⟩ : syracuseStep 799601 = 599701) B599701
theorem B799619 : Blo 531801 799619 := bstep (se 1 (by rfl) ⟨599714, by rfl⟩ : syracuseStep 799619 = 1199429) B1199429
theorem B799649 : Blo 531801 799649 := bstep (se 2 (by rfl) ⟨299868, by rfl⟩ : syracuseStep 799649 = 599737) B599737
theorem B799667 : Blo 531801 799667 := bstep (se 1 (by rfl) ⟨599750, by rfl⟩ : syracuseStep 799667 = 1199501) B1199501
theorem B799697 : Blo 531801 799697 := bstep (se 2 (by rfl) ⟨299886, by rfl⟩ : syracuseStep 799697 = 599773) B599773
theorem B799715 : Blo 531801 799715 := bstep (se 1 (by rfl) ⟨599786, by rfl⟩ : syracuseStep 799715 = 1199573) B1199573
theorem B898033 : Blo 531801 898033 := bstep (se 2 (by rfl) ⟨336762, by rfl⟩ : syracuseStep 898033 = 673525) B673525
theorem B799745 : Blo 531801 799745 := bstep (se 2 (by rfl) ⟨299904, by rfl⟩ : syracuseStep 799745 = 599809) B599809
theorem B898067 : Blo 531801 898067 := bstep (se 1 (by rfl) ⟨673550, by rfl⟩ : syracuseStep 898067 = 1347101) B1347101
theorem B799763 : Blo 531801 799763 := bstep (se 1 (by rfl) ⟨599822, by rfl⟩ : syracuseStep 799763 = 1199645) B1199645
theorem B799793 : Blo 531801 799793 := bstep (se 2 (by rfl) ⟨299922, by rfl⟩ : syracuseStep 799793 = 599845) B599845
theorem B799811 : Blo 531801 799811 := bstep (se 1 (by rfl) ⟨599858, by rfl⟩ : syracuseStep 799811 = 1199717) B1199717
theorem B799841 : Blo 531801 799841 := bstep (se 2 (by rfl) ⟨299940, by rfl⟩ : syracuseStep 799841 = 599881) B599881
theorem B799859 : Blo 531801 799859 := bstep (se 1 (by rfl) ⟨599894, by rfl⟩ : syracuseStep 799859 = 1199789) B1199789
theorem B799889 : Blo 531801 799889 := bstep (se 2 (by rfl) ⟨299958, by rfl⟩ : syracuseStep 799889 = 599917) B599917
theorem B1520785 : Blo 531801 1520785 := bstep (se 2 (by rfl) ⟨570294, by rfl⟩ : syracuseStep 1520785 = 1140589) B1140589
theorem B898195 : Blo 531801 898195 := bstep (se 1 (by rfl) ⟨673646, by rfl⟩ : syracuseStep 898195 = 1347293) B1347293
theorem B799907 : Blo 531801 799907 := bstep (se 1 (by rfl) ⟨599930, by rfl⟩ : syracuseStep 799907 = 1199861) B1199861
theorem B799937 : Blo 531801 799937 := bstep (se 2 (by rfl) ⟨299976, by rfl⟩ : syracuseStep 799937 = 599953) B599953
theorem B799955 : Blo 531801 799955 := bstep (se 1 (by rfl) ⟨599966, by rfl⟩ : syracuseStep 799955 = 1199933) B1199933
theorem B799985 : Blo 531801 799985 := bstep (se 2 (by rfl) ⟨299994, by rfl⟩ : syracuseStep 799985 = 599989) B599989
theorem B570611 : Blo 531801 570611 := bstep (se 1 (by rfl) ⟨427958, by rfl⟩ : syracuseStep 570611 = 855917) B855917
theorem B800003 : Blo 531801 800003 := bstep (se 1 (by rfl) ⟨600002, by rfl⟩ : syracuseStep 800003 = 1200005) B1200005
theorem B898337 : Blo 531801 898337 := bstep (se 2 (by rfl) ⟨336876, by rfl⟩ : syracuseStep 898337 = 673753) B673753
theorem B800033 : Blo 531801 800033 := bstep (se 2 (by rfl) ⟨300012, by rfl⟩ : syracuseStep 800033 = 600025) B600025
theorem B800051 : Blo 531801 800051 := bstep (se 1 (by rfl) ⟨600038, by rfl⟩ : syracuseStep 800051 = 1200077) B1200077
theorem B800081 : Blo 531801 800081 := bstep (se 2 (by rfl) ⟨300030, by rfl⟩ : syracuseStep 800081 = 600061) B600061
theorem B800099 : Blo 531801 800099 := bstep (se 1 (by rfl) ⟨600074, by rfl⟩ : syracuseStep 800099 = 1200149) B1200149
theorem B800129 : Blo 531801 800129 := bstep (se 2 (by rfl) ⟨300048, by rfl⟩ : syracuseStep 800129 = 600097) B600097
theorem B800147 : Blo 531801 800147 := bstep (se 1 (by rfl) ⟨600110, by rfl⟩ : syracuseStep 800147 = 1200221) B1200221
theorem B898465 : Blo 531801 898465 := bstep (se 2 (by rfl) ⟨336924, by rfl⟩ : syracuseStep 898465 = 673849) B673849
theorem B800177 : Blo 531801 800177 := bstep (se 2 (by rfl) ⟨300066, by rfl⟩ : syracuseStep 800177 = 600133) B600133
theorem B832961 : Blo 531801 832961 := bstep (se 2 (by rfl) ⟨312360, by rfl⟩ : syracuseStep 832961 = 624721) B624721
theorem B898499 : Blo 531801 898499 := bstep (se 1 (by rfl) ⟨673874, by rfl⟩ : syracuseStep 898499 = 1347749) B1347749
theorem B800195 : Blo 531801 800195 := bstep (se 1 (by rfl) ⟨600146, by rfl⟩ : syracuseStep 800195 = 1200293) B1200293
theorem B800225 : Blo 531801 800225 := bstep (se 2 (by rfl) ⟨300084, by rfl⟩ : syracuseStep 800225 = 600169) B600169
theorem B800243 : Blo 531801 800243 := bstep (se 1 (by rfl) ⟨600182, by rfl⟩ : syracuseStep 800243 = 1200365) B1200365
theorem B800273 : Blo 531801 800273 := bstep (se 2 (by rfl) ⟨300102, by rfl⟩ : syracuseStep 800273 = 600205) B600205
theorem B800291 : Blo 531801 800291 := bstep (se 1 (by rfl) ⟨600218, by rfl⟩ : syracuseStep 800291 = 1200437) B1200437
theorem B800321 : Blo 531801 800321 := bstep (se 2 (by rfl) ⟨300120, by rfl⟩ : syracuseStep 800321 = 600241) B600241
theorem B898627 : Blo 531801 898627 := bstep (se 1 (by rfl) ⟨673970, by rfl⟩ : syracuseStep 898627 = 1347941) B1347941
theorem B800339 : Blo 531801 800339 := bstep (se 1 (by rfl) ⟨600254, by rfl⟩ : syracuseStep 800339 = 1200509) B1200509
theorem B800369 : Blo 531801 800369 := bstep (se 2 (by rfl) ⟨300138, by rfl⟩ : syracuseStep 800369 = 600277) B600277
theorem B800387 : Blo 531801 800387 := bstep (se 1 (by rfl) ⟨600290, by rfl⟩ : syracuseStep 800387 = 1200581) B1200581
theorem B800417 : Blo 531801 800417 := bstep (se 2 (by rfl) ⟨300156, by rfl⟩ : syracuseStep 800417 = 600313) B600313
theorem B800435 : Blo 531801 800435 := bstep (se 1 (by rfl) ⟨600326, by rfl⟩ : syracuseStep 800435 = 1200653) B1200653
theorem B898769 : Blo 531801 898769 := bstep (se 2 (by rfl) ⟨337038, by rfl⟩ : syracuseStep 898769 = 674077) B674077
theorem B800465 : Blo 531801 800465 := bstep (se 2 (by rfl) ⟨300174, by rfl⟩ : syracuseStep 800465 = 600349) B600349
theorem B800483 : Blo 531801 800483 := bstep (se 1 (by rfl) ⟨600362, by rfl⟩ : syracuseStep 800483 = 1200725) B1200725
theorem B800513 : Blo 531801 800513 := bstep (se 2 (by rfl) ⟨300192, by rfl⟩ : syracuseStep 800513 = 600385) B600385
theorem B800531 : Blo 531801 800531 := bstep (se 1 (by rfl) ⟨600398, by rfl⟩ : syracuseStep 800531 = 1200797) B1200797
theorem B800561 : Blo 531801 800561 := bstep (se 2 (by rfl) ⟨300210, by rfl⟩ : syracuseStep 800561 = 600421) B600421
theorem B800579 : Blo 531801 800579 := bstep (se 1 (by rfl) ⟨600434, by rfl⟩ : syracuseStep 800579 = 1200869) B1200869
theorem B898897 : Blo 531801 898897 := bstep (se 2 (by rfl) ⟨337086, by rfl⟩ : syracuseStep 898897 = 674173) B674173
theorem B800609 : Blo 531801 800609 := bstep (se 2 (by rfl) ⟨300228, by rfl⟩ : syracuseStep 800609 = 600457) B600457
theorem B898931 : Blo 531801 898931 := bstep (se 1 (by rfl) ⟨674198, by rfl⟩ : syracuseStep 898931 = 1348397) B1348397
theorem B800627 : Blo 531801 800627 := bstep (se 1 (by rfl) ⟨600470, by rfl⟩ : syracuseStep 800627 = 1200941) B1200941
theorem B800657 : Blo 531801 800657 := bstep (se 2 (by rfl) ⟨300246, by rfl⟩ : syracuseStep 800657 = 600493) B600493
theorem B800675 : Blo 531801 800675 := bstep (se 1 (by rfl) ⟨600506, by rfl⟩ : syracuseStep 800675 = 1201013) B1201013
theorem B800705 : Blo 531801 800705 := bstep (se 2 (by rfl) ⟨300264, by rfl⟩ : syracuseStep 800705 = 600529) B600529
theorem B800723 : Blo 531801 800723 := bstep (se 1 (by rfl) ⟨600542, by rfl⟩ : syracuseStep 800723 = 1201085) B1201085
theorem B800753 : Blo 531801 800753 := bstep (se 2 (by rfl) ⟨300282, by rfl⟩ : syracuseStep 800753 = 600565) B600565
theorem B899059 : Blo 531801 899059 := bstep (se 1 (by rfl) ⟨674294, by rfl⟩ : syracuseStep 899059 = 1348589) B1348589
theorem B800771 : Blo 531801 800771 := bstep (se 1 (by rfl) ⟨600578, by rfl⟩ : syracuseStep 800771 = 1201157) B1201157
theorem B800801 : Blo 531801 800801 := bstep (se 2 (by rfl) ⟨300300, by rfl⟩ : syracuseStep 800801 = 600601) B600601
theorem B800819 : Blo 531801 800819 := bstep (se 1 (by rfl) ⟨600614, by rfl⟩ : syracuseStep 800819 = 1201229) B1201229
theorem B800849 : Blo 531801 800849 := bstep (se 2 (by rfl) ⟨300318, by rfl⟩ : syracuseStep 800849 = 600637) B600637
theorem B800867 : Blo 531801 800867 := bstep (se 1 (by rfl) ⟨600650, by rfl⟩ : syracuseStep 800867 = 1201301) B1201301
theorem B899201 : Blo 531801 899201 := bstep (se 2 (by rfl) ⟨337200, by rfl⟩ : syracuseStep 899201 = 674401) B674401
theorem B800897 : Blo 531801 800897 := bstep (se 2 (by rfl) ⟨300336, by rfl⟩ : syracuseStep 800897 = 600673) B600673
theorem B800915 : Blo 531801 800915 := bstep (se 1 (by rfl) ⟨600686, by rfl⟩ : syracuseStep 800915 = 1201373) B1201373
theorem B800945 : Blo 531801 800945 := bstep (se 2 (by rfl) ⟨300354, by rfl⟩ : syracuseStep 800945 = 600709) B600709
theorem B800963 : Blo 531801 800963 := bstep (se 1 (by rfl) ⟨600722, by rfl⟩ : syracuseStep 800963 = 1201445) B1201445
theorem B800993 : Blo 531801 800993 := bstep (se 2 (by rfl) ⟨300372, by rfl⟩ : syracuseStep 800993 = 600745) B600745
theorem B1620209 : Blo 531801 1620209 := bstep (se 2 (by rfl) ⟨607578, by rfl⟩ : syracuseStep 1620209 = 1215157) B1215157
theorem B801011 : Blo 531801 801011 := bstep (se 1 (by rfl) ⟨600758, by rfl⟩ : syracuseStep 801011 = 1201517) B1201517
theorem B899329 : Blo 531801 899329 := bstep (se 2 (by rfl) ⟨337248, by rfl⟩ : syracuseStep 899329 = 674497) B674497
theorem B801041 : Blo 531801 801041 := bstep (se 2 (by rfl) ⟨300390, by rfl⟩ : syracuseStep 801041 = 600781) B600781
theorem B899363 : Blo 531801 899363 := bstep (se 1 (by rfl) ⟨674522, by rfl⟩ : syracuseStep 899363 = 1349045) B1349045
theorem B801059 : Blo 531801 801059 := bstep (se 1 (by rfl) ⟨600794, by rfl⟩ : syracuseStep 801059 = 1201589) B1201589
theorem B2472241 : Blo 531801 2472241 := bstep (se 2 (by rfl) ⟨927090, by rfl⟩ : syracuseStep 2472241 = 1854181) B1854181
theorem B801089 : Blo 531801 801089 := bstep (se 2 (by rfl) ⟨300408, by rfl⟩ : syracuseStep 801089 = 600817) B600817
theorem B801107 : Blo 531801 801107 := bstep (se 1 (by rfl) ⟨600830, by rfl⟩ : syracuseStep 801107 = 1201661) B1201661
theorem B571747 : Blo 531801 571747 := bstep (se 1 (by rfl) ⟨428810, by rfl⟩ : syracuseStep 571747 = 857621) B857621
theorem B801137 : Blo 531801 801137 := bstep (se 2 (by rfl) ⟨300426, by rfl⟩ : syracuseStep 801137 = 600853) B600853
theorem B801155 : Blo 531801 801155 := bstep (se 1 (by rfl) ⟨600866, by rfl⟩ : syracuseStep 801155 = 1201733) B1201733
theorem B1522061 : Blo 531801 1522061 := bstep (se 3 (by rfl) ⟨285386, by rfl⟩ : syracuseStep 1522061 = 570773) B570773
theorem B801185 : Blo 531801 801185 := bstep (se 2 (by rfl) ⟨300444, by rfl⟩ : syracuseStep 801185 = 600889) B600889
theorem B899491 : Blo 531801 899491 := bstep (se 1 (by rfl) ⟨674618, by rfl⟩ : syracuseStep 899491 = 1349237) B1349237
theorem B801203 : Blo 531801 801203 := bstep (se 1 (by rfl) ⟨600902, by rfl⟩ : syracuseStep 801203 = 1201805) B1201805
theorem B801233 : Blo 531801 801233 := bstep (se 2 (by rfl) ⟨300462, by rfl⟩ : syracuseStep 801233 = 600925) B600925
theorem B801251 : Blo 531801 801251 := bstep (se 1 (by rfl) ⟨600938, by rfl⟩ : syracuseStep 801251 = 1201877) B1201877
theorem B801281 : Blo 531801 801281 := bstep (se 2 (by rfl) ⟨300480, by rfl⟩ : syracuseStep 801281 = 600961) B600961
theorem B801299 : Blo 531801 801299 := bstep (se 1 (by rfl) ⟨600974, by rfl⟩ : syracuseStep 801299 = 1201949) B1201949
theorem B899633 : Blo 531801 899633 := bstep (se 2 (by rfl) ⟨337362, by rfl⟩ : syracuseStep 899633 = 674725) B674725
theorem B801329 : Blo 531801 801329 := bstep (se 2 (by rfl) ⟨300498, by rfl⟩ : syracuseStep 801329 = 600997) B600997
theorem B801347 : Blo 531801 801347 := bstep (se 1 (by rfl) ⟨601010, by rfl⟩ : syracuseStep 801347 = 1202021) B1202021
theorem B1522243 : Blo 531801 1522243 := bstep (se 1 (by rfl) ⟨1141682, by rfl⟩ : syracuseStep 1522243 = 2283365) B2283365
theorem B801377 : Blo 531801 801377 := bstep (se 2 (by rfl) ⟨300516, by rfl⟩ : syracuseStep 801377 = 601033) B601033
theorem B1522289 : Blo 531801 1522289 := bstep (se 2 (by rfl) ⟨570858, by rfl⟩ : syracuseStep 1522289 = 1141717) B1141717
theorem B801395 : Blo 531801 801395 := bstep (se 1 (by rfl) ⟨601046, by rfl⟩ : syracuseStep 801395 = 1202093) B1202093
theorem B801425 : Blo 531801 801425 := bstep (se 2 (by rfl) ⟨300534, by rfl⟩ : syracuseStep 801425 = 601069) B601069
theorem B801443 : Blo 531801 801443 := bstep (se 1 (by rfl) ⟨601082, by rfl⟩ : syracuseStep 801443 = 1202165) B1202165
theorem B899761 : Blo 531801 899761 := bstep (se 2 (by rfl) ⟨337410, by rfl⟩ : syracuseStep 899761 = 674821) B674821
theorem B3422897 : Blo 531801 3422897 := bstep (se 2 (by rfl) ⟨1283586, by rfl⟩ : syracuseStep 3422897 = 2567173) B2567173
theorem B801473 : Blo 531801 801473 := bstep (se 2 (by rfl) ⟨300552, by rfl⟩ : syracuseStep 801473 = 601105) B601105
theorem B899795 : Blo 531801 899795 := bstep (se 1 (by rfl) ⟨674846, by rfl⟩ : syracuseStep 899795 = 1349693) B1349693
theorem B801491 : Blo 531801 801491 := bstep (se 1 (by rfl) ⟨601118, by rfl⟩ : syracuseStep 801491 = 1202237) B1202237
theorem B801521 : Blo 531801 801521 := bstep (se 2 (by rfl) ⟨300570, by rfl⟩ : syracuseStep 801521 = 601141) B601141
theorem B801539 : Blo 531801 801539 := bstep (se 1 (by rfl) ⟨601154, by rfl⟩ : syracuseStep 801539 = 1202309) B1202309
theorem B801569 : Blo 531801 801569 := bstep (se 2 (by rfl) ⟨300588, by rfl⟩ : syracuseStep 801569 = 601177) B601177
theorem B801587 : Blo 531801 801587 := bstep (se 1 (by rfl) ⟨601190, by rfl⟩ : syracuseStep 801587 = 1202381) B1202381
theorem B3849029 : Blo 531801 3849029 := bstep (se 4 (by rfl) ⟨360846, by rfl⟩ : syracuseStep 3849029 = 721693) B721693
theorem B801617 : Blo 531801 801617 := bstep (se 2 (by rfl) ⟨300606, by rfl⟩ : syracuseStep 801617 = 601213) B601213
theorem B899923 : Blo 531801 899923 := bstep (se 1 (by rfl) ⟨674942, by rfl⟩ : syracuseStep 899923 = 1349885) B1349885
theorem B801635 : Blo 531801 801635 := bstep (se 1 (by rfl) ⟨601226, by rfl⟩ : syracuseStep 801635 = 1202453) B1202453
theorem B801665 : Blo 531801 801665 := bstep (se 2 (by rfl) ⟨300624, by rfl⟩ : syracuseStep 801665 = 601249) B601249
theorem B801683 : Blo 531801 801683 := bstep (se 1 (by rfl) ⟨601262, by rfl⟩ : syracuseStep 801683 = 1202525) B1202525
theorem B801713 : Blo 531801 801713 := bstep (se 2 (by rfl) ⟨300642, by rfl⟩ : syracuseStep 801713 = 601285) B601285
theorem B801731 : Blo 531801 801731 := bstep (se 1 (by rfl) ⟨601298, by rfl⟩ : syracuseStep 801731 = 1202597) B1202597
theorem B900065 : Blo 531801 900065 := bstep (se 2 (by rfl) ⟨337524, by rfl⟩ : syracuseStep 900065 = 675049) B675049
theorem B801761 : Blo 531801 801761 := bstep (se 2 (by rfl) ⟨300660, by rfl⟩ : syracuseStep 801761 = 601321) B601321
theorem B2702321 : Blo 531801 2702321 := bstep (se 2 (by rfl) ⟨1013370, by rfl⟩ : syracuseStep 2702321 = 2026741) B2026741
theorem B801779 : Blo 531801 801779 := bstep (se 1 (by rfl) ⟨601334, by rfl⟩ : syracuseStep 801779 = 1202669) B1202669
theorem B801809 : Blo 531801 801809 := bstep (se 2 (by rfl) ⟨300678, by rfl⟩ : syracuseStep 801809 = 601357) B601357
theorem B801827 : Blo 531801 801827 := bstep (se 1 (by rfl) ⟨601370, by rfl⟩ : syracuseStep 801827 = 1202741) B1202741
theorem B801857 : Blo 531801 801857 := bstep (se 2 (by rfl) ⟨300696, by rfl⟩ : syracuseStep 801857 = 601393) B601393
theorem B801875 : Blo 531801 801875 := bstep (se 1 (by rfl) ⟨601406, by rfl⟩ : syracuseStep 801875 = 1202813) B1202813
theorem B900193 : Blo 531801 900193 := bstep (se 2 (by rfl) ⟨337572, by rfl⟩ : syracuseStep 900193 = 675145) B675145
theorem B801905 : Blo 531801 801905 := bstep (se 2 (by rfl) ⟨300714, by rfl⟩ : syracuseStep 801905 = 601429) B601429
theorem B900227 : Blo 531801 900227 := bstep (se 1 (by rfl) ⟨675170, by rfl⟩ : syracuseStep 900227 = 1350341) B1350341
theorem B801923 : Blo 531801 801923 := bstep (se 1 (by rfl) ⟨601442, by rfl⟩ : syracuseStep 801923 = 1202885) B1202885
theorem B801953 : Blo 531801 801953 := bstep (se 2 (by rfl) ⟨300732, by rfl⟩ : syracuseStep 801953 = 601465) B601465
theorem B801971 : Blo 531801 801971 := bstep (se 1 (by rfl) ⟨601478, by rfl⟩ : syracuseStep 801971 = 1202957) B1202957
theorem B802001 : Blo 531801 802001 := bstep (se 2 (by rfl) ⟨300750, by rfl⟩ : syracuseStep 802001 = 601501) B601501
theorem B539875 : Blo 531801 539875 := bstep (se 1 (by rfl) ⟨404906, by rfl⟩ : syracuseStep 539875 = 809813) B809813
theorem B802019 : Blo 531801 802019 := bstep (se 1 (by rfl) ⟨601514, by rfl⟩ : syracuseStep 802019 = 1203029) B1203029
theorem B802049 : Blo 531801 802049 := bstep (se 2 (by rfl) ⟨300768, by rfl⟩ : syracuseStep 802049 = 601537) B601537
theorem B900355 : Blo 531801 900355 := bstep (se 1 (by rfl) ⟨675266, by rfl⟩ : syracuseStep 900355 = 1350533) B1350533
theorem B802067 : Blo 531801 802067 := bstep (se 1 (by rfl) ⟨601550, by rfl⟩ : syracuseStep 802067 = 1203101) B1203101
theorem B802097 : Blo 531801 802097 := bstep (se 2 (by rfl) ⟨300786, by rfl⟩ : syracuseStep 802097 = 601573) B601573
theorem B802115 : Blo 531801 802115 := bstep (se 1 (by rfl) ⟨601586, by rfl⟩ : syracuseStep 802115 = 1203173) B1203173
theorem B802145 : Blo 531801 802145 := bstep (se 2 (by rfl) ⟨300804, by rfl⟩ : syracuseStep 802145 = 601609) B601609
theorem B802163 : Blo 531801 802163 := bstep (se 1 (by rfl) ⟨601622, by rfl⟩ : syracuseStep 802163 = 1203245) B1203245
theorem B900497 : Blo 531801 900497 := bstep (se 2 (by rfl) ⟨337686, by rfl⟩ : syracuseStep 900497 = 675373) B675373
theorem B802193 : Blo 531801 802193 := bstep (se 2 (by rfl) ⟨300822, by rfl⟩ : syracuseStep 802193 = 601645) B601645
theorem B802211 : Blo 531801 802211 := bstep (se 1 (by rfl) ⟨601658, by rfl⟩ : syracuseStep 802211 = 1203317) B1203317
theorem B802241 : Blo 531801 802241 := bstep (se 2 (by rfl) ⟨300840, by rfl⟩ : syracuseStep 802241 = 601681) B601681
theorem B802259 : Blo 531801 802259 := bstep (se 1 (by rfl) ⟨601694, by rfl⟩ : syracuseStep 802259 = 1203389) B1203389
theorem B802289 : Blo 531801 802289 := bstep (se 2 (by rfl) ⟨300858, by rfl⟩ : syracuseStep 802289 = 601717) B601717
theorem B802307 : Blo 531801 802307 := bstep (se 1 (by rfl) ⟨601730, by rfl⟩ : syracuseStep 802307 = 1203461) B1203461
theorem B900625 : Blo 531801 900625 := bstep (se 2 (by rfl) ⟨337734, by rfl⟩ : syracuseStep 900625 = 675469) B675469
theorem B802337 : Blo 531801 802337 := bstep (se 2 (by rfl) ⟨300876, by rfl⟩ : syracuseStep 802337 = 601753) B601753
theorem B802355 : Blo 531801 802355 := bstep (se 1 (by rfl) ⟨601766, by rfl⟩ : syracuseStep 802355 = 1203533) B1203533
theorem B900659 : Blo 531801 900659 := bstep (se 1 (by rfl) ⟨675494, by rfl⟩ : syracuseStep 900659 = 1350989) B1350989
theorem B802385 : Blo 531801 802385 := bstep (se 2 (by rfl) ⟨300894, by rfl⟩ : syracuseStep 802385 = 601789) B601789
theorem B4046435 : Blo 531801 4046435 := bstep (se 1 (by rfl) ⟨3034826, by rfl⟩ : syracuseStep 4046435 = 6069653) B6069653
theorem B802403 : Blo 531801 802403 := bstep (se 1 (by rfl) ⟨601802, by rfl⟩ : syracuseStep 802403 = 1203605) B1203605
theorem B802433 : Blo 531801 802433 := bstep (se 2 (by rfl) ⟨300912, by rfl⟩ : syracuseStep 802433 = 601825) B601825
theorem B802451 : Blo 531801 802451 := bstep (se 1 (by rfl) ⟨601838, by rfl⟩ : syracuseStep 802451 = 1203677) B1203677
theorem B802481 : Blo 531801 802481 := bstep (se 2 (by rfl) ⟨300930, by rfl⟩ : syracuseStep 802481 = 601861) B601861
theorem B900787 : Blo 531801 900787 := bstep (se 1 (by rfl) ⟨675590, by rfl⟩ : syracuseStep 900787 = 1351181) B1351181
theorem B802499 : Blo 531801 802499 := bstep (se 1 (by rfl) ⟨601874, by rfl⟩ : syracuseStep 802499 = 1203749) B1203749
theorem B802529 : Blo 531801 802529 := bstep (se 2 (by rfl) ⟨300948, by rfl⟩ : syracuseStep 802529 = 601897) B601897
theorem B802547 : Blo 531801 802547 := bstep (se 1 (by rfl) ⟨601910, by rfl⟩ : syracuseStep 802547 = 1203821) B1203821
theorem B802577 : Blo 531801 802577 := bstep (se 2 (by rfl) ⟨300966, by rfl⟩ : syracuseStep 802577 = 601933) B601933
theorem B802595 : Blo 531801 802595 := bstep (se 1 (by rfl) ⟨601946, by rfl⟩ : syracuseStep 802595 = 1203893) B1203893
theorem B900929 : Blo 531801 900929 := bstep (se 2 (by rfl) ⟨337848, by rfl⟩ : syracuseStep 900929 = 675697) B675697
theorem B802625 : Blo 531801 802625 := bstep (se 2 (by rfl) ⟨300984, by rfl⟩ : syracuseStep 802625 = 601969) B601969
theorem B802643 : Blo 531801 802643 := bstep (se 1 (by rfl) ⟨601982, by rfl⟩ : syracuseStep 802643 = 1203965) B1203965
theorem B802673 : Blo 531801 802673 := bstep (se 2 (by rfl) ⟨301002, by rfl⟩ : syracuseStep 802673 = 602005) B602005
theorem B802691 : Blo 531801 802691 := bstep (se 1 (by rfl) ⟨602018, by rfl⟩ : syracuseStep 802691 = 1204037) B1204037
theorem B802721 : Blo 531801 802721 := bstep (se 2 (by rfl) ⟨301020, by rfl⟩ : syracuseStep 802721 = 602041) B602041
theorem B802739 : Blo 531801 802739 := bstep (se 1 (by rfl) ⟨602054, by rfl⟩ : syracuseStep 802739 = 1204109) B1204109
theorem B901057 : Blo 531801 901057 := bstep (se 2 (by rfl) ⟨337896, by rfl⟩ : syracuseStep 901057 = 675793) B675793
theorem B802769 : Blo 531801 802769 := bstep (se 2 (by rfl) ⟨301038, by rfl⟩ : syracuseStep 802769 = 602077) B602077
theorem B901091 : Blo 531801 901091 := bstep (se 1 (by rfl) ⟨675818, by rfl⟩ : syracuseStep 901091 = 1351637) B1351637
theorem B802787 : Blo 531801 802787 := bstep (se 1 (by rfl) ⟨602090, by rfl⟩ : syracuseStep 802787 = 1204181) B1204181
theorem B802817 : Blo 531801 802817 := bstep (se 2 (by rfl) ⟨301056, by rfl⟩ : syracuseStep 802817 = 602113) B602113
theorem B802835 : Blo 531801 802835 := bstep (se 1 (by rfl) ⟨602126, by rfl⟩ : syracuseStep 802835 = 1204253) B1204253
theorem B1523747 : Blo 531801 1523747 := bstep (se 1 (by rfl) ⟨1142810, by rfl⟩ : syracuseStep 1523747 = 2285621) B2285621
theorem B802865 : Blo 531801 802865 := bstep (se 2 (by rfl) ⟨301074, by rfl⟩ : syracuseStep 802865 = 602149) B602149
theorem B802883 : Blo 531801 802883 := bstep (se 1 (by rfl) ⟨602162, by rfl⟩ : syracuseStep 802883 = 1204325) B1204325
theorem B802913 : Blo 531801 802913 := bstep (se 2 (by rfl) ⟨301092, by rfl⟩ : syracuseStep 802913 = 602185) B602185
theorem B901219 : Blo 531801 901219 := bstep (se 1 (by rfl) ⟨675914, by rfl⟩ : syracuseStep 901219 = 1351829) B1351829
theorem B802931 : Blo 531801 802931 := bstep (se 1 (by rfl) ⟨602198, by rfl⟩ : syracuseStep 802931 = 1204397) B1204397
theorem B9748621 : Blo 531801 9748621 := bstep (se 3 (by rfl) ⟨1827866, by rfl⟩ : syracuseStep 9748621 = 3655733) B3655733
theorem B802961 : Blo 531801 802961 := bstep (se 2 (by rfl) ⟨301110, by rfl⟩ : syracuseStep 802961 = 602221) B602221
theorem B802979 : Blo 531801 802979 := bstep (se 1 (by rfl) ⟨602234, by rfl⟩ : syracuseStep 802979 = 1204469) B1204469
theorem B803009 : Blo 531801 803009 := bstep (se 2 (by rfl) ⟨301128, by rfl⟩ : syracuseStep 803009 = 602257) B602257
theorem B803027 : Blo 531801 803027 := bstep (se 1 (by rfl) ⟨602270, by rfl⟩ : syracuseStep 803027 = 1204541) B1204541
theorem B901361 : Blo 531801 901361 := bstep (se 2 (by rfl) ⟨338010, by rfl⟩ : syracuseStep 901361 = 676021) B676021
theorem B803057 : Blo 531801 803057 := bstep (se 2 (by rfl) ⟨301146, by rfl⟩ : syracuseStep 803057 = 602293) B602293
theorem B803075 : Blo 531801 803075 := bstep (se 1 (by rfl) ⟨602306, by rfl⟩ : syracuseStep 803075 = 1204613) B1204613
theorem B803105 : Blo 531801 803105 := bstep (se 2 (by rfl) ⟨301164, by rfl⟩ : syracuseStep 803105 = 602329) B602329
theorem B803123 : Blo 531801 803123 := bstep (se 1 (by rfl) ⟨602342, by rfl⟩ : syracuseStep 803123 = 1204685) B1204685
theorem B803153 : Blo 531801 803153 := bstep (se 2 (by rfl) ⟨301182, by rfl⟩ : syracuseStep 803153 = 602365) B602365
theorem B803171 : Blo 531801 803171 := bstep (se 1 (by rfl) ⟨602378, by rfl⟩ : syracuseStep 803171 = 1204757) B1204757
theorem B901489 : Blo 531801 901489 := bstep (se 2 (by rfl) ⟨338058, by rfl⟩ : syracuseStep 901489 = 676117) B676117
theorem B803201 : Blo 531801 803201 := bstep (se 2 (by rfl) ⟨301200, by rfl⟩ : syracuseStep 803201 = 602401) B602401
theorem B901523 : Blo 531801 901523 := bstep (se 1 (by rfl) ⟨676142, by rfl⟩ : syracuseStep 901523 = 1352285) B1352285
theorem B803219 : Blo 531801 803219 := bstep (se 1 (by rfl) ⟨602414, by rfl⟩ : syracuseStep 803219 = 1204829) B1204829
theorem B1622435 : Blo 531801 1622435 := bstep (se 1 (by rfl) ⟨1216826, by rfl⟩ : syracuseStep 1622435 = 2433653) B2433653
theorem B2703779 : Blo 531801 2703779 := bstep (se 1 (by rfl) ⟨2027834, by rfl⟩ : syracuseStep 2703779 = 4055669) B4055669
theorem B803249 : Blo 531801 803249 := bstep (se 2 (by rfl) ⟨301218, by rfl⟩ : syracuseStep 803249 = 602437) B602437
theorem B803267 : Blo 531801 803267 := bstep (se 1 (by rfl) ⟨602450, by rfl⟩ : syracuseStep 803267 = 1204901) B1204901
theorem B803297 : Blo 531801 803297 := bstep (se 2 (by rfl) ⟨301236, by rfl⟩ : syracuseStep 803297 = 602473) B602473
theorem B803315 : Blo 531801 803315 := bstep (se 1 (by rfl) ⟨602486, by rfl⟩ : syracuseStep 803315 = 1204973) B1204973
theorem B803345 : Blo 531801 803345 := bstep (se 2 (by rfl) ⟨301254, by rfl⟩ : syracuseStep 803345 = 602509) B602509
theorem B901651 : Blo 531801 901651 := bstep (se 1 (by rfl) ⟨676238, by rfl⟩ : syracuseStep 901651 = 1352477) B1352477
theorem B803363 : Blo 531801 803363 := bstep (se 1 (by rfl) ⟨602522, by rfl⟩ : syracuseStep 803363 = 1205045) B1205045
theorem B803393 : Blo 531801 803393 := bstep (se 2 (by rfl) ⟨301272, by rfl⟩ : syracuseStep 803393 = 602545) B602545
theorem B803411 : Blo 531801 803411 := bstep (se 1 (by rfl) ⟨602558, by rfl⟩ : syracuseStep 803411 = 1205117) B1205117
theorem B2048611 : Blo 531801 2048611 := bstep (se 1 (by rfl) ⟨1536458, by rfl⟩ : syracuseStep 2048611 = 3072917) B3072917
theorem B1196657 : Blo 531801 1196657 := bstep (se 2 (by rfl) ⟨448746, by rfl⟩ : syracuseStep 1196657 = 897493) B897493
theorem B803441 : Blo 531801 803441 := bstep (se 2 (by rfl) ⟨301290, by rfl⟩ : syracuseStep 803441 = 602581) B602581
theorem B1196675 : Blo 531801 1196675 := bstep (se 1 (by rfl) ⟨897506, by rfl⟩ : syracuseStep 1196675 = 1795013) B1795013
theorem B803459 : Blo 531801 803459 := bstep (se 1 (by rfl) ⟨602594, by rfl⟩ : syracuseStep 803459 = 1205189) B1205189
theorem B901793 : Blo 531801 901793 := bstep (se 2 (by rfl) ⟨338172, by rfl⟩ : syracuseStep 901793 = 676345) B676345
theorem B803489 : Blo 531801 803489 := bstep (se 2 (by rfl) ⟨301308, by rfl⟩ : syracuseStep 803489 = 602617) B602617
theorem B803507 : Blo 531801 803507 := bstep (se 1 (by rfl) ⟨602630, by rfl⟩ : syracuseStep 803507 = 1205261) B1205261
theorem B803537 : Blo 531801 803537 := bstep (se 2 (by rfl) ⟨301326, by rfl⟩ : syracuseStep 803537 = 602653) B602653
theorem B803555 : Blo 531801 803555 := bstep (se 1 (by rfl) ⟨602666, by rfl⟩ : syracuseStep 803555 = 1205333) B1205333
theorem B803585 : Blo 531801 803585 := bstep (se 2 (by rfl) ⟨301344, by rfl⟩ : syracuseStep 803585 = 602689) B602689
theorem B803603 : Blo 531801 803603 := bstep (se 1 (by rfl) ⟨602702, by rfl⟩ : syracuseStep 803603 = 1205405) B1205405
theorem B901921 : Blo 531801 901921 := bstep (se 2 (by rfl) ⟨338220, by rfl⟩ : syracuseStep 901921 = 676441) B676441
theorem B803633 : Blo 531801 803633 := bstep (se 2 (by rfl) ⟨301362, by rfl⟩ : syracuseStep 803633 = 602725) B602725
theorem B901955 : Blo 531801 901955 := bstep (se 1 (by rfl) ⟨676466, by rfl⟩ : syracuseStep 901955 = 1352933) B1352933
theorem B803651 : Blo 531801 803651 := bstep (se 1 (by rfl) ⟨602738, by rfl⟩ : syracuseStep 803651 = 1205477) B1205477
theorem B803681 : Blo 531801 803681 := bstep (se 2 (by rfl) ⟨301380, by rfl⟩ : syracuseStep 803681 = 602761) B602761
theorem B803699 : Blo 531801 803699 := bstep (se 1 (by rfl) ⟨602774, by rfl⟩ : syracuseStep 803699 = 1205549) B1205549
theorem B1196945 : Blo 531801 1196945 := bstep (se 2 (by rfl) ⟨448854, by rfl⟩ : syracuseStep 1196945 = 897709) B897709
theorem B1196963 : Blo 531801 1196963 := bstep (se 1 (by rfl) ⟨897722, by rfl⟩ : syracuseStep 1196963 = 1795445) B1795445
theorem B2278307 : Blo 531801 2278307 := bstep (se 1 (by rfl) ⟨1708730, by rfl⟩ : syracuseStep 2278307 = 3417461) B3417461
theorem B902083 : Blo 531801 902083 := bstep (se 1 (by rfl) ⟨676562, by rfl⟩ : syracuseStep 902083 = 1353125) B1353125
theorem B2049101 : Blo 531801 2049101 := bstep (se 3 (by rfl) ⟨384206, by rfl⟩ : syracuseStep 2049101 = 768413) B768413
theorem B902225 : Blo 531801 902225 := bstep (se 2 (by rfl) ⟨338334, by rfl⟩ : syracuseStep 902225 = 676669) B676669
theorem B1197233 : Blo 531801 1197233 := bstep (se 2 (by rfl) ⟨448962, by rfl⟩ : syracuseStep 1197233 = 897925) B897925
theorem B1197251 : Blo 531801 1197251 := bstep (se 1 (by rfl) ⟨897938, by rfl⟩ : syracuseStep 1197251 = 1795877) B1795877
theorem B2704589 : Blo 531801 2704589 := bstep (se 3 (by rfl) ⟨507110, by rfl⟩ : syracuseStep 2704589 = 1014221) B1014221
theorem B902353 : Blo 531801 902353 := bstep (se 2 (by rfl) ⟨338382, by rfl⟩ : syracuseStep 902353 = 676765) B676765
theorem B1524977 : Blo 531801 1524977 := bstep (se 2 (by rfl) ⟨571866, by rfl⟩ : syracuseStep 1524977 = 1143733) B1143733
theorem B902387 : Blo 531801 902387 := bstep (se 1 (by rfl) ⟨676790, by rfl⟩ : syracuseStep 902387 = 1353581) B1353581
theorem B902515 : Blo 531801 902515 := bstep (se 1 (by rfl) ⟨676886, by rfl⟩ : syracuseStep 902515 = 1353773) B1353773
theorem B1197521 : Blo 531801 1197521 := bstep (se 2 (by rfl) ⟨449070, by rfl⟩ : syracuseStep 1197521 = 898141) B898141
theorem B1197539 : Blo 531801 1197539 := bstep (se 1 (by rfl) ⟨898154, by rfl⟩ : syracuseStep 1197539 = 1796309) B1796309
theorem B673267 : Blo 531801 673267 := bstep (se 1 (by rfl) ⟨504950, by rfl⟩ : syracuseStep 673267 = 1009901) B1009901
theorem B902657 : Blo 531801 902657 := bstep (se 2 (by rfl) ⟨338496, by rfl⟩ : syracuseStep 902657 = 676993) B676993
theorem B2606627 : Blo 531801 2606627 := bstep (se 1 (by rfl) ⟨1954970, by rfl⟩ : syracuseStep 2606627 = 3909941) B3909941
theorem B542275 : Blo 531801 542275 := bstep (se 1 (by rfl) ⟨406706, by rfl⟩ : syracuseStep 542275 = 813413) B813413
theorem B673363 : Blo 531801 673363 := bstep (se 1 (by rfl) ⟨505022, by rfl⟩ : syracuseStep 673363 = 1010045) B1010045
theorem B902785 : Blo 531801 902785 := bstep (se 2 (by rfl) ⟨338544, by rfl⟩ : syracuseStep 902785 = 677089) B677089
theorem B902819 : Blo 531801 902819 := bstep (se 1 (by rfl) ⟨677114, by rfl⟩ : syracuseStep 902819 = 1354229) B1354229
theorem B1197809 : Blo 531801 1197809 := bstep (se 2 (by rfl) ⟨449178, by rfl⟩ : syracuseStep 1197809 = 898357) B898357
theorem B1197827 : Blo 531801 1197827 := bstep (se 1 (by rfl) ⟨898370, by rfl⟩ : syracuseStep 1197827 = 1796741) B1796741
theorem B902947 : Blo 531801 902947 := bstep (se 1 (by rfl) ⟨677210, by rfl⟩ : syracuseStep 902947 = 1354421) B1354421
theorem B12994357 : Blo 531801 12994357 := bstep (se 5 (by rfl) ⟨609110, by rfl⟩ : syracuseStep 12994357 = 1218221) B1218221
theorem B903089 : Blo 531801 903089 := bstep (se 2 (by rfl) ⟨338658, by rfl⟩ : syracuseStep 903089 = 677317) B677317
theorem B1198097 : Blo 531801 1198097 := bstep (se 2 (by rfl) ⟨449286, by rfl⟩ : syracuseStep 1198097 = 898573) B898573
theorem B1198115 : Blo 531801 1198115 := bstep (se 1 (by rfl) ⟨898586, by rfl⟩ : syracuseStep 1198115 = 1797173) B1797173
theorem B903217 : Blo 531801 903217 := bstep (se 2 (by rfl) ⟨338706, by rfl⟩ : syracuseStep 903217 = 677413) B677413
theorem B673859 : Blo 531801 673859 := bstep (se 1 (by rfl) ⟨505394, by rfl⟩ : syracuseStep 673859 = 1010789) B1010789
theorem B903251 : Blo 531801 903251 := bstep (se 1 (by rfl) ⟨677438, by rfl⟩ : syracuseStep 903251 = 1354877) B1354877
theorem B1853585 : Blo 531801 1853585 := bstep (se 2 (by rfl) ⟨695094, by rfl⟩ : syracuseStep 1853585 = 1390189) B1390189
theorem B2050211 : Blo 531801 2050211 := bstep (se 1 (by rfl) ⟨1537658, by rfl⟩ : syracuseStep 2050211 = 3075317) B3075317
theorem B903379 : Blo 531801 903379 := bstep (se 1 (by rfl) ⟨677534, by rfl⟩ : syracuseStep 903379 = 1355069) B1355069
theorem B1198385 : Blo 531801 1198385 := bstep (se 2 (by rfl) ⟨449394, by rfl⟩ : syracuseStep 1198385 = 898789) B898789
theorem B1198403 : Blo 531801 1198403 := bstep (se 1 (by rfl) ⟨898802, by rfl⟩ : syracuseStep 1198403 = 1797605) B1797605
theorem B903521 : Blo 531801 903521 := bstep (se 2 (by rfl) ⟨338820, by rfl⟩ : syracuseStep 903521 = 677641) B677641
theorem B903649 : Blo 531801 903649 := bstep (se 2 (by rfl) ⟨338868, by rfl⟩ : syracuseStep 903649 = 677737) B677737
theorem B903683 : Blo 531801 903683 := bstep (se 1 (by rfl) ⟨677762, by rfl⟩ : syracuseStep 903683 = 1355525) B1355525
theorem B3426893 : Blo 531801 3426893 := bstep (se 3 (by rfl) ⟨642542, by rfl⟩ : syracuseStep 3426893 = 1285085) B1285085
theorem B1198673 : Blo 531801 1198673 := bstep (se 2 (by rfl) ⟨449502, by rfl⟩ : syracuseStep 1198673 = 899005) B899005
theorem B1198691 : Blo 531801 1198691 := bstep (se 1 (by rfl) ⟨899018, by rfl⟩ : syracuseStep 1198691 = 1798037) B1798037
theorem B903811 : Blo 531801 903811 := bstep (se 1 (by rfl) ⟨677858, by rfl⟩ : syracuseStep 903811 = 1355717) B1355717
theorem B3033733 : Blo 531801 3033733 := bstep (se 4 (by rfl) ⟨284412, by rfl⟩ : syracuseStep 3033733 = 568825) B568825
theorem B641731 : Blo 531801 641731 := bstep (se 1 (by rfl) ⟨481298, by rfl⟩ : syracuseStep 641731 = 962597) B962597
theorem B674563 : Blo 531801 674563 := bstep (se 1 (by rfl) ⟨505922, by rfl⟩ : syracuseStep 674563 = 1011845) B1011845
theorem B903953 : Blo 531801 903953 := bstep (se 2 (by rfl) ⟨338982, by rfl⟩ : syracuseStep 903953 = 677965) B677965
theorem B674659 : Blo 531801 674659 := bstep (se 1 (by rfl) ⟨505994, by rfl⟩ : syracuseStep 674659 = 1011989) B1011989
theorem B1198961 : Blo 531801 1198961 := bstep (se 2 (by rfl) ⟨449610, by rfl⟩ : syracuseStep 1198961 = 899221) B899221
theorem B1198979 : Blo 531801 1198979 := bstep (se 1 (by rfl) ⟨899234, by rfl⟩ : syracuseStep 1198979 = 1798469) B1798469
theorem B904081 : Blo 531801 904081 := bstep (se 2 (by rfl) ⟨339030, by rfl⟩ : syracuseStep 904081 = 678061) B678061
theorem B904115 : Blo 531801 904115 := bstep (se 1 (by rfl) ⟨678086, by rfl⟩ : syracuseStep 904115 = 1356173) B1356173
theorem B1199249 : Blo 531801 1199249 := bstep (se 2 (by rfl) ⟨449718, by rfl⟩ : syracuseStep 1199249 = 899437) B899437
theorem B1199267 : Blo 531801 1199267 := bstep (se 1 (by rfl) ⟨899450, by rfl⟩ : syracuseStep 1199267 = 1798901) B1798901
theorem B675155 : Blo 531801 675155 := bstep (se 1 (by rfl) ⟨506366, by rfl⟩ : syracuseStep 675155 = 1012733) B1012733
theorem B1199537 : Blo 531801 1199537 := bstep (se 2 (by rfl) ⟨449826, by rfl⟩ : syracuseStep 1199537 = 899653) B899653
theorem B1199555 : Blo 531801 1199555 := bstep (se 1 (by rfl) ⟨899666, by rfl⟩ : syracuseStep 1199555 = 1799333) B1799333
theorem B2280973 : Blo 531801 2280973 := bstep (se 3 (by rfl) ⟨427682, by rfl⟩ : syracuseStep 2280973 = 855365) B855365
theorem B1199825 : Blo 531801 1199825 := bstep (se 2 (by rfl) ⟨449934, by rfl⟩ : syracuseStep 1199825 = 899869) B899869
theorem B1199843 : Blo 531801 1199843 := bstep (se 1 (by rfl) ⟨899882, by rfl⟩ : syracuseStep 1199843 = 1799765) B1799765
theorem B1920881 : Blo 531801 1920881 := bstep (se 2 (by rfl) ⟨720330, by rfl⟩ : syracuseStep 1920881 = 1440661) B1440661
theorem B1200113 : Blo 531801 1200113 := bstep (se 2 (by rfl) ⟨450042, by rfl⟩ : syracuseStep 1200113 = 900085) B900085
theorem B1200131 : Blo 531801 1200131 := bstep (se 1 (by rfl) ⟨900098, by rfl⟩ : syracuseStep 1200131 = 1800197) B1800197
theorem B675859 : Blo 531801 675859 := bstep (se 1 (by rfl) ⟨506894, by rfl⟩ : syracuseStep 675859 = 1013789) B1013789
theorem B2707505 : Blo 531801 2707505 := bstep (se 2 (by rfl) ⟨1015314, by rfl⟩ : syracuseStep 2707505 = 2030629) B2030629
theorem B1626193 : Blo 531801 1626193 := bstep (se 2 (by rfl) ⟨609822, by rfl⟩ : syracuseStep 1626193 = 1219645) B1219645
theorem B675955 : Blo 531801 675955 := bstep (se 1 (by rfl) ⟨506966, by rfl⟩ : syracuseStep 675955 = 1013933) B1013933
theorem B9752773 : Blo 531801 9752773 := bstep (se 4 (by rfl) ⟨914322, by rfl⟩ : syracuseStep 9752773 = 1828645) B1828645
theorem B577747 : Blo 531801 577747 := bstep (se 1 (by rfl) ⟨433310, by rfl⟩ : syracuseStep 577747 = 866621) B866621
theorem B1200401 : Blo 531801 1200401 := bstep (se 2 (by rfl) ⟨450150, by rfl⟩ : syracuseStep 1200401 = 900301) B900301
theorem B1200419 : Blo 531801 1200419 := bstep (se 1 (by rfl) ⟨900314, by rfl⟩ : syracuseStep 1200419 = 1800629) B1800629
theorem B3461453 : Blo 531801 3461453 := bstep (se 3 (by rfl) ⟨649022, by rfl⟩ : syracuseStep 3461453 = 1298045) B1298045
theorem B3658061 : Blo 531801 3658061 := bstep (se 3 (by rfl) ⟨685886, by rfl⟩ : syracuseStep 3658061 = 1371773) B1371773
theorem B2019725 : Blo 531801 2019725 := bstep (se 3 (by rfl) ⟨378698, by rfl⟩ : syracuseStep 2019725 = 757397) B757397
theorem B643523 : Blo 531801 643523 := bstep (se 1 (by rfl) ⟨482642, by rfl⟩ : syracuseStep 643523 = 965285) B965285
theorem B643619 : Blo 531801 643619 := bstep (se 1 (by rfl) ⟨482714, by rfl⟩ : syracuseStep 643619 = 965429) B965429
theorem B1200689 : Blo 531801 1200689 := bstep (se 2 (by rfl) ⟨450258, by rfl⟩ : syracuseStep 1200689 = 900517) B900517
theorem B2282033 : Blo 531801 2282033 := bstep (se 2 (by rfl) ⟨855762, by rfl⟩ : syracuseStep 2282033 = 1711525) B1711525
theorem B1200707 : Blo 531801 1200707 := bstep (se 1 (by rfl) ⟨900530, by rfl⟩ : syracuseStep 1200707 = 1801061) B1801061
theorem B3035717 : Blo 531801 3035717 := bstep (se 4 (by rfl) ⟨284598, by rfl⟩ : syracuseStep 3035717 = 569197) B569197
theorem B676451 : Blo 531801 676451 := bstep (se 1 (by rfl) ⟨507338, by rfl⟩ : syracuseStep 676451 = 1014677) B1014677
theorem B10277603 : Blo 531801 10277603 := bstep (se 1 (by rfl) ⟨7708202, by rfl⟩ : syracuseStep 10277603 = 15416405) B15416405
theorem B3429125 : Blo 531801 3429125 := bstep (se 4 (by rfl) ⟨321480, by rfl⟩ : syracuseStep 3429125 = 642961) B642961
theorem B4051781 : Blo 531801 4051781 := bstep (se 4 (by rfl) ⟨379854, by rfl⟩ : syracuseStep 4051781 = 759709) B759709
theorem B1200977 : Blo 531801 1200977 := bstep (se 2 (by rfl) ⟨450366, by rfl⟩ : syracuseStep 1200977 = 900733) B900733
theorem B1200995 : Blo 531801 1200995 := bstep (se 1 (by rfl) ⟨900746, by rfl⟩ : syracuseStep 1200995 = 1801493) B1801493
theorem B1201265 : Blo 531801 1201265 := bstep (se 2 (by rfl) ⟨450474, by rfl⟩ : syracuseStep 1201265 = 900949) B900949
theorem B1201283 : Blo 531801 1201283 := bstep (se 1 (by rfl) ⟨900962, by rfl⟩ : syracuseStep 1201283 = 1801925) B1801925
theorem B5788853 : Blo 531801 5788853 := bstep (se 5 (by rfl) ⟨271352, by rfl⟩ : syracuseStep 5788853 = 542705) B542705
theorem B4150499 : Blo 531801 4150499 := bstep (se 1 (by rfl) ⟨3112874, by rfl⟩ : syracuseStep 4150499 = 6225749) B6225749
theorem B1627409 : Blo 531801 1627409 := bstep (se 2 (by rfl) ⟨610278, by rfl⟩ : syracuseStep 1627409 = 1220557) B1220557
theorem B677155 : Blo 531801 677155 := bstep (se 1 (by rfl) ⟨507866, by rfl⟩ : syracuseStep 677155 = 1015733) B1015733
theorem B677251 : Blo 531801 677251 := bstep (se 1 (by rfl) ⟨507938, by rfl⟩ : syracuseStep 677251 = 1015877) B1015877
theorem B1201553 : Blo 531801 1201553 := bstep (se 2 (by rfl) ⟨450582, by rfl⟩ : syracuseStep 1201553 = 901165) B901165
theorem B1201571 : Blo 531801 1201571 := bstep (se 1 (by rfl) ⟨901178, by rfl⟩ : syracuseStep 1201571 = 1802357) B1802357
theorem B2708963 : Blo 531801 2708963 := bstep (se 1 (by rfl) ⟨2031722, by rfl⟩ : syracuseStep 2708963 = 4063445) B4063445
theorem B1824365 : Blo 531801 1824365 := bstep (se 3 (by rfl) ⟨342068, by rfl⟩ : syracuseStep 1824365 = 684137) B684137
theorem B1627789 : Blo 531801 1627789 := bstep (se 3 (by rfl) ⟨305210, by rfl⟩ : syracuseStep 1627789 = 610421) B610421
theorem B1201841 : Blo 531801 1201841 := bstep (se 2 (by rfl) ⟨450690, by rfl⟩ : syracuseStep 1201841 = 901381) B901381
theorem B1201859 : Blo 531801 1201859 := bstep (se 1 (by rfl) ⟨901394, by rfl⟩ : syracuseStep 1201859 = 1802789) B1802789
theorem B1136369 : Blo 531801 1136369 := bstep (se 2 (by rfl) ⟨426138, by rfl⟩ : syracuseStep 1136369 = 852277) B852277
theorem B677747 : Blo 531801 677747 := bstep (se 1 (by rfl) ⟨508310, by rfl⟩ : syracuseStep 677747 = 1016621) B1016621
theorem B808883 : Blo 531801 808883 := bstep (se 1 (by rfl) ⟨606662, by rfl⟩ : syracuseStep 808883 = 1213325) B1213325
theorem B808913 : Blo 531801 808913 := bstep (se 2 (by rfl) ⟨303342, by rfl⟩ : syracuseStep 808913 = 606685) B606685
theorem B1202129 : Blo 531801 1202129 := bstep (se 2 (by rfl) ⟨450798, by rfl⟩ : syracuseStep 1202129 = 901597) B901597
theorem B7690211 : Blo 531801 7690211 := bstep (se 1 (by rfl) ⟨5767658, by rfl⟩ : syracuseStep 7690211 = 11535317) B11535317
theorem B1202147 : Blo 531801 1202147 := bstep (se 1 (by rfl) ⟨901610, by rfl⟩ : syracuseStep 1202147 = 1803221) B1803221
theorem B2087117 : Blo 531801 2087117 := bstep (se 3 (by rfl) ⟨391334, by rfl⟩ : syracuseStep 2087117 = 782669) B782669
theorem B1202417 : Blo 531801 1202417 := bstep (se 2 (by rfl) ⟨450906, by rfl⟩ : syracuseStep 1202417 = 901813) B901813
theorem B1202435 : Blo 531801 1202435 := bstep (se 1 (by rfl) ⟨901826, by rfl⟩ : syracuseStep 1202435 = 1803653) B1803653
theorem B2709773 : Blo 531801 2709773 := bstep (se 3 (by rfl) ⟨508082, by rfl⟩ : syracuseStep 2709773 = 1016165) B1016165
theorem B547139 : Blo 531801 547139 := bstep (se 1 (by rfl) ⟨410354, by rfl⟩ : syracuseStep 547139 = 820709) B820709
theorem B547283 : Blo 531801 547283 := bstep (se 1 (by rfl) ⟨410462, by rfl⟩ : syracuseStep 547283 = 820925) B820925
theorem B1628675 : Blo 531801 1628675 := bstep (se 1 (by rfl) ⟨1221506, by rfl⟩ : syracuseStep 1628675 = 2443013) B2443013
theorem B1202705 : Blo 531801 1202705 := bstep (se 2 (by rfl) ⟨451014, by rfl⟩ : syracuseStep 1202705 = 902029) B902029
theorem B1202723 : Blo 531801 1202723 := bstep (se 1 (by rfl) ⟨902042, by rfl⟩ : syracuseStep 1202723 = 1804085) B1804085
theorem B1137233 : Blo 531801 1137233 := bstep (se 2 (by rfl) ⟨426462, by rfl⟩ : syracuseStep 1137233 = 852925) B852925
theorem B1727153 : Blo 531801 1727153 := bstep (se 2 (by rfl) ⟨647682, by rfl⟩ : syracuseStep 1727153 = 1295365) B1295365
theorem B809777 : Blo 531801 809777 := bstep (se 2 (by rfl) ⟨303666, by rfl⟩ : syracuseStep 809777 = 607333) B607333
theorem B1202993 : Blo 531801 1202993 := bstep (se 2 (by rfl) ⟨451122, by rfl⟩ : syracuseStep 1202993 = 902245) B902245
theorem B1203011 : Blo 531801 1203011 := bstep (se 1 (by rfl) ⟨902258, by rfl⟩ : syracuseStep 1203011 = 1804517) B1804517
theorem B1203281 : Blo 531801 1203281 := bstep (se 2 (by rfl) ⟨451230, by rfl⟩ : syracuseStep 1203281 = 902461) B902461
theorem B1203299 : Blo 531801 1203299 := bstep (se 1 (by rfl) ⟨902474, by rfl⟩ : syracuseStep 1203299 = 1804949) B1804949
theorem B2022641 : Blo 531801 2022641 := bstep (se 2 (by rfl) ⟨758490, by rfl⟩ : syracuseStep 2022641 = 1516981) B1516981
theorem B1203569 : Blo 531801 1203569 := bstep (se 2 (by rfl) ⟨451338, by rfl⟩ : syracuseStep 1203569 = 902677) B902677
theorem B1203587 : Blo 531801 1203587 := bstep (se 1 (by rfl) ⟨902690, by rfl⟩ : syracuseStep 1203587 = 1805381) B1805381
theorem B2285005 : Blo 531801 2285005 := bstep (se 3 (by rfl) ⟨428438, by rfl⟩ : syracuseStep 2285005 = 856877) B856877
theorem B1302097 : Blo 531801 1302097 := bstep (se 2 (by rfl) ⟨488286, by rfl⟩ : syracuseStep 1302097 = 976573) B976573
theorem B1203857 : Blo 531801 1203857 := bstep (se 2 (by rfl) ⟨451446, by rfl⟩ : syracuseStep 1203857 = 902893) B902893
theorem B1203875 : Blo 531801 1203875 := bstep (se 1 (by rfl) ⟨902906, by rfl⟩ : syracuseStep 1203875 = 1805813) B1805813
theorem B2285347 : Blo 531801 2285347 := bstep (se 1 (by rfl) ⟨1714010, by rfl⟩ : syracuseStep 2285347 = 3428021) B3428021
theorem B4874053 : Blo 531801 4874053 := bstep (se 4 (by rfl) ⟨456942, by rfl⟩ : syracuseStep 4874053 = 913885) B913885
theorem B1138531 : Blo 531801 1138531 := bstep (se 1 (by rfl) ⟨853898, by rfl⟩ : syracuseStep 1138531 = 1707797) B1707797
theorem B1925005 : Blo 531801 1925005 := bstep (se 3 (by rfl) ⟨360938, by rfl⟩ : syracuseStep 1925005 = 721877) B721877
theorem B1204145 : Blo 531801 1204145 := bstep (se 2 (by rfl) ⟨451554, by rfl⟩ : syracuseStep 1204145 = 903109) B903109
theorem B1204163 : Blo 531801 1204163 := bstep (se 1 (by rfl) ⟨903122, by rfl⟩ : syracuseStep 1204163 = 1806245) B1806245
theorem B1826819 : Blo 531801 1826819 := bstep (se 1 (by rfl) ⟨1370114, by rfl⟩ : syracuseStep 1826819 = 2740229) B2740229
theorem B1466435 : Blo 531801 1466435 := bstep (se 1 (by rfl) ⟨1099826, by rfl⟩ : syracuseStep 1466435 = 2199653) B2199653
theorem B6480013 : Blo 531801 6480013 := bstep (se 3 (by rfl) ⟨1215002, by rfl⟩ : syracuseStep 6480013 = 2430005) B2430005
theorem B1466545 : Blo 531801 1466545 := bstep (se 2 (by rfl) ⟨549954, by rfl⟩ : syracuseStep 1466545 = 1099909) B1099909
theorem B1204433 : Blo 531801 1204433 := bstep (se 2 (by rfl) ⟨451662, by rfl⟩ : syracuseStep 1204433 = 903325) B903325
theorem B1204451 : Blo 531801 1204451 := bstep (se 1 (by rfl) ⟨903338, by rfl⟩ : syracuseStep 1204451 = 1806677) B1806677
theorem B3039565 : Blo 531801 3039565 := bstep (se 3 (by rfl) ⟨569918, by rfl⟩ : syracuseStep 3039565 = 1139837) B1139837
theorem B6185315 : Blo 531801 6185315 := bstep (se 1 (by rfl) ⟨4638986, by rfl⟩ : syracuseStep 6185315 = 9277973) B9277973
theorem B1204721 : Blo 531801 1204721 := bstep (se 2 (by rfl) ⟨451770, by rfl⟩ : syracuseStep 1204721 = 903541) B903541
theorem B1204739 : Blo 531801 1204739 := bstep (se 1 (by rfl) ⟨903554, by rfl⟩ : syracuseStep 1204739 = 1807109) B1807109
theorem B8643185 : Blo 531801 8643185 := bstep (se 2 (by rfl) ⟨3241194, by rfl⟩ : syracuseStep 8643185 = 6482389) B6482389
theorem B2024099 : Blo 531801 2024099 := bstep (se 1 (by rfl) ⟨1518074, by rfl⟩ : syracuseStep 2024099 = 3036149) B3036149
theorem B1205009 : Blo 531801 1205009 := bstep (se 2 (by rfl) ⟨451878, by rfl⟩ : syracuseStep 1205009 = 903757) B903757
theorem B1794851 : Blo 531801 1794851 := bstep (se 1 (by rfl) ⟨1346138, by rfl⟩ : syracuseStep 1794851 = 2692277) B2692277
theorem B1205027 : Blo 531801 1205027 := bstep (se 1 (by rfl) ⟨903770, by rfl⟩ : syracuseStep 1205027 = 1807541) B1807541
theorem B910163 : Blo 531801 910163 := bstep (se 1 (by rfl) ⟨682622, by rfl⟩ : syracuseStep 910163 = 1365245) B1365245
theorem B1795121 : Blo 531801 1795121 := bstep (se 2 (by rfl) ⟨673170, by rfl⟩ : syracuseStep 1795121 = 1346341) B1346341
theorem B1139761 : Blo 531801 1139761 := bstep (se 2 (by rfl) ⟨427410, by rfl⟩ : syracuseStep 1139761 = 854821) B854821
theorem B1205297 : Blo 531801 1205297 := bstep (se 2 (by rfl) ⟨451986, by rfl⟩ : syracuseStep 1205297 = 903973) B903973
theorem B1205315 : Blo 531801 1205315 := bstep (se 1 (by rfl) ⟨903986, by rfl⟩ : syracuseStep 1205315 = 1807973) B1807973
theorem B910561 : Blo 531801 910561 := bstep (se 2 (by rfl) ⟨341460, by rfl⟩ : syracuseStep 910561 = 682921) B682921
theorem B9233635 : Blo 531801 9233635 := bstep (se 1 (by rfl) ⟨6925226, by rfl⟩ : syracuseStep 9233635 = 13850453) B13850453
theorem B1369457 : Blo 531801 1369457 := bstep (se 2 (by rfl) ⟨513546, by rfl⟩ : syracuseStep 1369457 = 1027093) B1027093
theorem B1795661 : Blo 531801 1795661 := bstep (se 3 (by rfl) ⟨336686, by rfl⟩ : syracuseStep 1795661 = 673373) B673373
theorem B910931 : Blo 531801 910931 := bstep (se 1 (by rfl) ⟨683198, by rfl⟩ : syracuseStep 910931 = 1366397) B1366397
theorem B1795715 : Blo 531801 1795715 := bstep (se 1 (by rfl) ⟨1346786, by rfl⟩ : syracuseStep 1795715 = 2693573) B2693573
theorem B2025101 : Blo 531801 2025101 := bstep (se 3 (by rfl) ⟨379706, by rfl⟩ : syracuseStep 2025101 = 759413) B759413
theorem B1140419 : Blo 531801 1140419 := bstep (se 1 (by rfl) ⟨855314, by rfl⟩ : syracuseStep 1140419 = 1710629) B1710629
theorem B1795985 : Blo 531801 1795985 := bstep (se 2 (by rfl) ⟨673494, by rfl⟩ : syracuseStep 1795985 = 1346989) B1346989
theorem B1108081 : Blo 531801 1108081 := bstep (se 2 (by rfl) ⟨415530, by rfl⟩ : syracuseStep 1108081 = 831061) B831061
theorem B3041549 : Blo 531801 3041549 := bstep (se 3 (by rfl) ⟨570290, by rfl⟩ : syracuseStep 3041549 = 1140581) B1140581
theorem B1010083 : Blo 531801 1010083 := bstep (se 1 (by rfl) ⟨757562, by rfl⟩ : syracuseStep 1010083 = 1515125) B1515125
theorem B1796525 : Blo 531801 1796525 := bstep (se 3 (by rfl) ⟨336848, by rfl⟩ : syracuseStep 1796525 = 673697) B673697
theorem B7301573 : Blo 531801 7301573 := bstep (se 4 (by rfl) ⟨684522, by rfl⟩ : syracuseStep 7301573 = 1369045) B1369045
theorem B1796579 : Blo 531801 1796579 := bstep (se 1 (by rfl) ⟨1347434, by rfl⟩ : syracuseStep 1796579 = 2694869) B2694869
theorem B4057613 : Blo 531801 4057613 := bstep (se 3 (by rfl) ⟨760802, by rfl⟩ : syracuseStep 4057613 = 1521605) B1521605
theorem B1141265 : Blo 531801 1141265 := bstep (se 2 (by rfl) ⟨427974, by rfl⟩ : syracuseStep 1141265 = 855949) B855949
theorem B1796849 : Blo 531801 1796849 := bstep (se 2 (by rfl) ⟨673818, by rfl⟩ : syracuseStep 1796849 = 1347637) B1347637
theorem B1010531 : Blo 531801 1010531 := bstep (se 1 (by rfl) ⟨757898, by rfl⟩ : syracuseStep 1010531 = 1515797) B1515797
theorem B2157553 : Blo 531801 2157553 := bstep (se 2 (by rfl) ⟨809082, by rfl⟩ : syracuseStep 2157553 = 1618165) B1618165
theorem B1731629 : Blo 531801 1731629 := bstep (se 3 (by rfl) ⟨324680, by rfl⟩ : syracuseStep 1731629 = 649361) B649361
theorem B1010819 : Blo 531801 1010819 := bstep (se 1 (by rfl) ⟨758114, by rfl⟩ : syracuseStep 1010819 = 1516229) B1516229
theorem B3042481 : Blo 531801 3042481 := bstep (se 2 (by rfl) ⟨1140930, by rfl⟩ : syracuseStep 3042481 = 2281861) B2281861
theorem B3239153 : Blo 531801 3239153 := bstep (se 2 (by rfl) ⟨1214682, by rfl⟩ : syracuseStep 3239153 = 2429365) B2429365
theorem B1797389 : Blo 531801 1797389 := bstep (se 3 (by rfl) ⟨337010, by rfl⟩ : syracuseStep 1797389 = 674021) B674021
theorem B1797443 : Blo 531801 1797443 := bstep (se 1 (by rfl) ⟨1348082, by rfl⟩ : syracuseStep 1797443 = 2696165) B2696165
theorem B1830289 : Blo 531801 1830289 := bstep (se 2 (by rfl) ⟨686358, by rfl⟩ : syracuseStep 1830289 = 1372717) B1372717
theorem B1535441 : Blo 531801 1535441 := bstep (se 2 (by rfl) ⟨575790, by rfl⟩ : syracuseStep 1535441 = 1151581) B1151581
theorem B1797713 : Blo 531801 1797713 := bstep (se 2 (by rfl) ⟨674142, by rfl⟩ : syracuseStep 1797713 = 1348285) B1348285
theorem B2027213 : Blo 531801 2027213 := bstep (se 3 (by rfl) ⟨380102, by rfl⟩ : syracuseStep 2027213 = 760205) B760205
theorem B880577 : Blo 531801 880577 := bstep (se 2 (by rfl) ⟨330216, by rfl⟩ : syracuseStep 880577 = 660433) B660433
theorem B5140421 : Blo 531801 5140421 := bstep (se 4 (by rfl) ⟨481914, by rfl⟩ : syracuseStep 5140421 = 963829) B963829
theorem B3665891 : Blo 531801 3665891 := bstep (se 1 (by rfl) ⟨2749418, by rfl⟩ : syracuseStep 3665891 = 5498837) B5498837
theorem B1437677 : Blo 531801 1437677 := bstep (se 3 (by rfl) ⟨269564, by rfl⟩ : syracuseStep 1437677 = 539129) B539129
theorem B1011761 : Blo 531801 1011761 := bstep (se 2 (by rfl) ⟨379410, by rfl⟩ : syracuseStep 1011761 = 758821) B758821
theorem B1798253 : Blo 531801 1798253 := bstep (se 3 (by rfl) ⟨337172, by rfl⟩ : syracuseStep 1798253 = 674345) B674345
theorem B1798307 : Blo 531801 1798307 := bstep (se 1 (by rfl) ⟨1348730, by rfl⟩ : syracuseStep 1798307 = 2697461) B2697461
theorem B1142947 : Blo 531801 1142947 := bstep (se 1 (by rfl) ⟨857210, by rfl⟩ : syracuseStep 1142947 = 1714421) B1714421
theorem B749747 : Blo 531801 749747 := bstep (se 1 (by rfl) ⟨562310, by rfl⟩ : syracuseStep 749747 = 1124621) B1124621
theorem B4551011 : Blo 531801 4551011 := bstep (se 1 (by rfl) ⟨3413258, by rfl⟩ : syracuseStep 4551011 = 6826517) B6826517
theorem B1798577 : Blo 531801 1798577 := bstep (se 2 (by rfl) ⟨674466, by rfl⟩ : syracuseStep 1798577 = 1348933) B1348933
theorem B913859 : Blo 531801 913859 := bstep (se 1 (by rfl) ⟨685394, by rfl⟩ : syracuseStep 913859 = 1370789) B1370789
theorem B2028017 : Blo 531801 2028017 := bstep (se 2 (by rfl) ⟨760506, by rfl⟩ : syracuseStep 2028017 = 1521013) B1521013
theorem B3043939 : Blo 531801 3043939 := bstep (se 1 (by rfl) ⟨2282954, by rfl⟩ : syracuseStep 3043939 = 4565909) B4565909
theorem B1143409 : Blo 531801 1143409 := bstep (se 2 (by rfl) ⟨428778, by rfl⟩ : syracuseStep 1143409 = 857557) B857557
theorem B914161 : Blo 531801 914161 := bstep (se 2 (by rfl) ⟨342810, by rfl⟩ : syracuseStep 914161 = 685621) B685621
theorem B1012657 : Blo 531801 1012657 := bstep (se 2 (by rfl) ⟨379746, by rfl⟩ : syracuseStep 1012657 = 759493) B759493
theorem B1799117 : Blo 531801 1799117 := bstep (se 3 (by rfl) ⟨337334, by rfl⟩ : syracuseStep 1799117 = 674669) B674669
theorem B1799171 : Blo 531801 1799171 := bstep (se 1 (by rfl) ⟨1349378, by rfl⟩ : syracuseStep 1799171 = 2698757) B2698757
theorem B914449 : Blo 531801 914449 := bstep (se 2 (by rfl) ⟨342918, by rfl⟩ : syracuseStep 914449 = 685837) B685837
theorem B10417205 : Blo 531801 10417205 := bstep (se 5 (by rfl) ⟨488306, by rfl⟩ : syracuseStep 10417205 = 976613) B976613
theorem B1012817 : Blo 531801 1012817 := bstep (se 2 (by rfl) ⟨379806, by rfl⟩ : syracuseStep 1012817 = 759613) B759613
theorem B3044465 : Blo 531801 3044465 := bstep (se 2 (by rfl) ⟨1141674, by rfl⟩ : syracuseStep 3044465 = 2283349) B2283349
theorem B2028685 : Blo 531801 2028685 := bstep (se 3 (by rfl) ⟨380378, by rfl⟩ : syracuseStep 2028685 = 760757) B760757
theorem B9270413 : Blo 531801 9270413 := bstep (se 3 (by rfl) ⟨1738202, by rfl⟩ : syracuseStep 9270413 = 3476405) B3476405
theorem B1799441 : Blo 531801 1799441 := bstep (se 2 (by rfl) ⟨674790, by rfl⟩ : syracuseStep 1799441 = 1349581) B1349581
theorem B1373539 : Blo 531801 1373539 := bstep (se 1 (by rfl) ⟨1030154, by rfl⟩ : syracuseStep 1373539 = 2060309) B2060309
theorem B4060529 : Blo 531801 4060529 := bstep (se 2 (by rfl) ⟨1522698, by rfl⟩ : syracuseStep 4060529 = 3045397) B3045397
theorem B1013219 : Blo 531801 1013219 := bstep (se 1 (by rfl) ⟨759914, by rfl⟩ : syracuseStep 1013219 = 1519829) B1519829
theorem B1799981 : Blo 531801 1799981 := bstep (se 3 (by rfl) ⟨337496, by rfl⟩ : syracuseStep 1799981 = 674993) B674993
theorem B1800035 : Blo 531801 1800035 := bstep (se 1 (by rfl) ⟨1350026, by rfl⟩ : syracuseStep 1800035 = 2700053) B2700053
theorem B2029475 : Blo 531801 2029475 := bstep (se 1 (by rfl) ⟨1522106, by rfl⟩ : syracuseStep 2029475 = 3044213) B3044213
theorem B1832867 : Blo 531801 1832867 := bstep (se 1 (by rfl) ⟨1374650, by rfl⟩ : syracuseStep 1832867 = 2749301) B2749301
theorem B948323 : Blo 531801 948323 := bstep (se 1 (by rfl) ⟨711242, by rfl⟩ : syracuseStep 948323 = 1422485) B1422485
theorem B1800305 : Blo 531801 1800305 := bstep (se 2 (by rfl) ⟨675114, by rfl⟩ : syracuseStep 1800305 = 1350229) B1350229
theorem B2881669 : Blo 531801 2881669 := bstep (se 4 (by rfl) ⟨270156, by rfl⟩ : syracuseStep 2881669 = 540313) B540313
theorem B6092981 : Blo 531801 6092981 := bstep (se 5 (by rfl) ⟨285608, by rfl⟩ : syracuseStep 6092981 = 571217) B571217
theorem B1014115 : Blo 531801 1014115 := bstep (se 1 (by rfl) ⟨760586, by rfl⟩ : syracuseStep 1014115 = 1521173) B1521173
theorem B1014275 : Blo 531801 1014275 := bstep (se 1 (by rfl) ⟨760706, by rfl⟩ : syracuseStep 1014275 = 1521413) B1521413
theorem B3045923 : Blo 531801 3045923 := bstep (se 1 (by rfl) ⟨2284442, by rfl⟩ : syracuseStep 3045923 = 4568885) B4568885
theorem B2030129 : Blo 531801 2030129 := bstep (se 2 (by rfl) ⟨761298, by rfl⟩ : syracuseStep 2030129 = 1522597) B1522597
theorem B1800845 : Blo 531801 1800845 := bstep (se 3 (by rfl) ⟨337658, by rfl⟩ : syracuseStep 1800845 = 675317) B675317
theorem B4291213 : Blo 531801 4291213 := bstep (se 3 (by rfl) ⟨804602, by rfl⟩ : syracuseStep 4291213 = 1609205) B1609205
theorem B1800899 : Blo 531801 1800899 := bstep (se 1 (by rfl) ⟨1350674, by rfl⟩ : syracuseStep 1800899 = 2701349) B2701349
theorem B1080067 : Blo 531801 1080067 := bstep (se 1 (by rfl) ⟨810050, by rfl⟩ : syracuseStep 1080067 = 1620101) B1620101
theorem B1801169 : Blo 531801 1801169 := bstep (se 2 (by rfl) ⟨675438, by rfl⟩ : syracuseStep 1801169 = 1350877) B1350877
theorem B2849869 : Blo 531801 2849869 := bstep (se 3 (by rfl) ⟨534350, by rfl⟩ : syracuseStep 2849869 = 1068701) B1068701
theorem B1801709 : Blo 531801 1801709 := bstep (se 3 (by rfl) ⟨337820, by rfl⟩ : syracuseStep 1801709 = 675641) B675641
theorem B1801763 : Blo 531801 1801763 := bstep (se 1 (by rfl) ⟨1351322, by rfl⟩ : syracuseStep 1801763 = 2702645) B2702645
theorem B1015345 : Blo 531801 1015345 := bstep (se 2 (by rfl) ⟨380754, by rfl⟩ : syracuseStep 1015345 = 761509) B761509
theorem B5766709 : Blo 531801 5766709 := bstep (se 5 (by rfl) ⟨270314, by rfl⟩ : syracuseStep 5766709 = 540629) B540629
theorem B2883185 : Blo 531801 2883185 := bstep (se 2 (by rfl) ⟨1081194, by rfl⟩ : syracuseStep 2883185 = 2162389) B2162389
theorem B1802033 : Blo 531801 1802033 := bstep (se 2 (by rfl) ⟨675762, by rfl⟩ : syracuseStep 1802033 = 1351525) B1351525
theorem B720785 : Blo 531801 720785 := bstep (se 2 (by rfl) ⟨270294, by rfl⟩ : syracuseStep 720785 = 540589) B540589
theorem B851905 : Blo 531801 851905 := bstep (se 2 (by rfl) ⟨319464, by rfl⟩ : syracuseStep 851905 = 638929) B638929
theorem B2031587 : Blo 531801 2031587 := bstep (se 1 (by rfl) ⟨1523690, by rfl⟩ : syracuseStep 2031587 = 3047381) B3047381
theorem B2031601 : Blo 531801 2031601 := bstep (se 2 (by rfl) ⟨761850, by rfl⟩ : syracuseStep 2031601 = 1523701) B1523701
theorem B1015831 : Blo 531801 1015831 := bstep (se 1 (by rfl) ⟨761873, by rfl⟩ : syracuseStep 1015831 = 1523747) B1523747
theorem B2031875 : Blo 531801 2031875 := bstep (se 1 (by rfl) ⟨1523906, by rfl⟩ : syracuseStep 2031875 = 3047813) B3047813
theorem B1802519 : Blo 531801 1802519 := bstep (se 1 (by rfl) ⟨1351889, by rfl⟩ : syracuseStep 1802519 = 2703779) B2703779
theorem B7668067 : Blo 531801 7668067 := bstep (se 1 (by rfl) ⟨5751050, by rfl⟩ : syracuseStep 7668067 = 11502101) B11502101
theorem B1999325 : Blo 531801 1999325 := bstep (se 3 (by rfl) ⟨374873, by rfl⟩ : syracuseStep 1999325 = 749747) B749747
theorem B1803059 : Blo 531801 1803059 := bstep (se 1 (by rfl) ⟨1352294, by rfl⟩ : syracuseStep 1803059 = 2704589) B2704589
theorem B1016651 : Blo 531801 1016651 := bstep (se 1 (by rfl) ⟨762488, by rfl⟩ : syracuseStep 1016651 = 1524977) B1524977
theorem B1016705 : Blo 531801 1016705 := bstep (se 2 (by rfl) ⟨381264, by rfl⟩ : syracuseStep 1016705 = 762529) B762529
theorem B6489011 : Blo 531801 6489011 := bstep (se 1 (by rfl) ⟨4866758, by rfl⟩ : syracuseStep 6489011 = 9733517) B9733517
theorem B1803329 : Blo 531801 1803329 := bstep (se 2 (by rfl) ⟨676248, by rfl⟩ : syracuseStep 1803329 = 1352497) B1352497
theorem B2458925 : Blo 531801 2458925 := bstep (se 3 (by rfl) ⟨461048, by rfl⟩ : syracuseStep 2458925 = 922097) B922097
theorem B853591 : Blo 531801 853591 := bstep (se 1 (by rfl) ⟨640193, by rfl⟩ : syracuseStep 853591 = 1280387) B1280387
theorem B1803869 : Blo 531801 1803869 := bstep (se 3 (by rfl) ⟨338225, by rfl⟩ : syracuseStep 1803869 = 676451) B676451
theorem B1214081 : Blo 531801 1214081 := bstep (se 2 (by rfl) ⟨455280, by rfl⟩ : syracuseStep 1214081 = 910561) B910561
theorem B6063821 : Blo 531801 6063821 := bstep (se 3 (by rfl) ⟨1136966, by rfl⟩ : syracuseStep 6063821 = 2273933) B2273933
theorem B15599537 : Blo 531801 15599537 := bstep (se 2 (by rfl) ⟨5849826, by rfl⟩ : syracuseStep 15599537 = 11699653) B11699653
theorem B3082333 : Blo 531801 3082333 := bstep (se 3 (by rfl) ⟨577937, by rfl⟩ : syracuseStep 3082333 = 1155875) B1155875
theorem B854155 : Blo 531801 854155 := bstep (se 1 (by rfl) ⟨640616, by rfl⟩ : syracuseStep 854155 = 1281233) B1281233
theorem B2427101 : Blo 531801 2427101 := bstep (se 3 (by rfl) ⟨455081, by rfl⟩ : syracuseStep 2427101 = 910163) B910163
theorem B1805003 : Blo 531801 1805003 := bstep (se 1 (by rfl) ⟨1353752, by rfl⟩ : syracuseStep 1805003 = 2707505) B2707505
theorem B1477441 : Blo 531801 1477441 := bstep (se 2 (by rfl) ⟨554040, by rfl⟩ : syracuseStep 1477441 = 1108081) B1108081
theorem B1346483 : Blo 531801 1346483 := bstep (se 1 (by rfl) ⟨1009862, by rfl⟩ : syracuseStep 1346483 = 2019725) B2019725
theorem B1805273 : Blo 531801 1805273 := bstep (se 2 (by rfl) ⟨676977, by rfl⟩ : syracuseStep 1805273 = 1353955) B1353955
theorem B6851735 : Blo 531801 6851735 := bstep (se 1 (by rfl) ⟨5138801, by rfl⟩ : syracuseStep 6851735 = 10277603) B10277603
theorem B1346777 : Blo 531801 1346777 := bstep (se 2 (by rfl) ⟨505041, by rfl⟩ : syracuseStep 1346777 = 1010083) B1010083
theorem B5475761 : Blo 531801 5475761 := bstep (se 2 (by rfl) ⟨2053410, by rfl⟩ : syracuseStep 5475761 = 4106821) B4106821
theorem B855641 : Blo 531801 855641 := bstep (se 2 (by rfl) ⟨320865, by rfl⟩ : syracuseStep 855641 = 641731) B641731
theorem B1805975 : Blo 531801 1805975 := bstep (se 1 (by rfl) ⟨1354481, by rfl⟩ : syracuseStep 1805975 = 2708963) B2708963
theorem B1216243 : Blo 531801 1216243 := bstep (se 1 (by rfl) ⟨912182, by rfl⟩ : syracuseStep 1216243 = 1824365) B1824365
theorem B4067333 : Blo 531801 4067333 := bstep (se 4 (by rfl) ⟨381312, by rfl⟩ : syracuseStep 4067333 = 762625) B762625
theorem B6951005 : Blo 531801 6951005 := bstep (se 3 (by rfl) ⟨1303313, by rfl⟩ : syracuseStep 6951005 = 2606627) B2606627
theorem B3281075 : Blo 531801 3281075 := bstep (se 1 (by rfl) ⟨2460806, by rfl⟩ : syracuseStep 3281075 = 4921613) B4921613
theorem B1806515 : Blo 531801 1806515 := bstep (se 1 (by rfl) ⟨1354886, by rfl⟩ : syracuseStep 1806515 = 2709773) B2709773
theorem B594103 : Blo 531801 594103 := bstep (se 1 (by rfl) ⟨445577, by rfl⟩ : syracuseStep 594103 = 891155) B891155
theorem B2429149 : Blo 531801 2429149 := bstep (se 3 (by rfl) ⟨455465, by rfl⟩ : syracuseStep 2429149 = 910931) B910931
theorem B1085783 : Blo 531801 1085783 := bstep (se 1 (by rfl) ⟨814337, by rfl⟩ : syracuseStep 1085783 = 1628675) B1628675
theorem B17305973 : Blo 531801 17305973 := bstep (se 5 (by rfl) ⟨811217, by rfl⟩ : syracuseStep 17305973 = 1622435) B1622435
theorem B758155 : Blo 531801 758155 := bstep (se 1 (by rfl) ⟨568616, by rfl⟩ : syracuseStep 758155 = 1137233) B1137233
theorem B1806785 : Blo 531801 1806785 := bstep (se 2 (by rfl) ⟨677544, by rfl⟩ : syracuseStep 1806785 = 1355089) B1355089
theorem B1151435 : Blo 531801 1151435 := bstep (se 1 (by rfl) ⟨863576, by rfl⟩ : syracuseStep 1151435 = 1727153) B1727153
theorem B1282625 : Blo 531801 1282625 := bstep (se 2 (by rfl) ⟨480984, by rfl⟩ : syracuseStep 1282625 = 961969) B961969
theorem B18551501 : Blo 531801 18551501 := bstep (se 3 (by rfl) ⟨3478406, by rfl⟩ : syracuseStep 18551501 = 6956813) B6956813
theorem B1348427 : Blo 531801 1348427 := bstep (se 1 (by rfl) ⟨1011320, by rfl⟩ : syracuseStep 1348427 = 2022641) B2022641
theorem B2200537 : Blo 531801 2200537 := bstep (se 2 (by rfl) ⟨825201, by rfl⟩ : syracuseStep 2200537 = 1650403) B1650403
theorem B1807325 : Blo 531801 1807325 := bstep (se 3 (by rfl) ⟨338873, by rfl⟩ : syracuseStep 1807325 = 677747) B677747
theorem B4854935 : Blo 531801 4854935 := bstep (se 1 (by rfl) ⟨3641201, by rfl⟩ : syracuseStep 4854935 = 7282403) B7282403
theorem B1217879 : Blo 531801 1217879 := bstep (se 1 (by rfl) ⟨913409, by rfl⟩ : syracuseStep 1217879 = 1826819) B1826819
theorem B7804259 : Blo 531801 7804259 := bstep (se 1 (by rfl) ⟨5853194, by rfl⟩ : syracuseStep 7804259 = 11706389) B11706389
theorem B2168257 : Blo 531801 2168257 := bstep (se 2 (by rfl) ⟨813096, by rfl⟩ : syracuseStep 2168257 = 1626193) B1626193
theorem B759385 : Blo 531801 759385 := bstep (se 2 (by rfl) ⟨284769, by rfl⟩ : syracuseStep 759385 = 569539) B569539
theorem B1349399 : Blo 531801 1349399 := bstep (se 1 (by rfl) ⟨1012049, by rfl⟩ : syracuseStep 1349399 = 2024099) B2024099
theorem B3413825 : Blo 531801 3413825 := bstep (se 2 (by rfl) ⟨1280184, by rfl⟩ : syracuseStep 3413825 = 2560369) B2560369
theorem B1218881 : Blo 531801 1218881 := bstep (se 2 (by rfl) ⟨457080, by rfl⟩ : syracuseStep 1218881 = 914161) B914161
theorem B1350067 : Blo 531801 1350067 := bstep (se 1 (by rfl) ⟨1012550, by rfl⟩ : syracuseStep 1350067 = 2025101) B2025101
theorem B760279 : Blo 531801 760279 := bstep (se 1 (by rfl) ⟨570209, by rfl⟩ : syracuseStep 760279 = 1140419) B1140419
theorem B1350209 : Blo 531801 1350209 := bstep (se 2 (by rfl) ⟨506328, by rfl⟩ : syracuseStep 1350209 = 1012657) B1012657
theorem B1219265 : Blo 531801 1219265 := bstep (se 2 (by rfl) ⟨457224, by rfl⟩ : syracuseStep 1219265 = 914449) B914449
theorem B760843 : Blo 531801 760843 := bstep (se 1 (by rfl) ⟨570632, by rfl⟩ : syracuseStep 760843 = 1141265) B1141265
theorem B531819 : Blo 531801 531819 := bstep (se 1 (by rfl) ⟨398864, by rfl⟩ : syracuseStep 531819 = 797729) B797729
theorem B1154419 : Blo 531801 1154419 := bstep (se 1 (by rfl) ⟨865814, by rfl⟩ : syracuseStep 1154419 = 1731629) B1731629
theorem B531831 : Blo 531801 531831 := bstep (se 1 (by rfl) ⟨398873, by rfl⟩ : syracuseStep 531831 = 797747) B797747
theorem B531851 : Blo 531801 531851 := bstep (se 1 (by rfl) ⟨398888, by rfl⟩ : syracuseStep 531851 = 797777) B797777
theorem B531863 : Blo 531801 531863 := bstep (se 1 (by rfl) ⟨398897, by rfl⟩ : syracuseStep 531863 = 797795) B797795
theorem B531883 : Blo 531801 531883 := bstep (se 1 (by rfl) ⟨398912, by rfl⟩ : syracuseStep 531883 = 797825) B797825
theorem B531895 : Blo 531801 531895 := bstep (se 1 (by rfl) ⟨398921, by rfl⟩ : syracuseStep 531895 = 797843) B797843
theorem B531915 : Blo 531801 531915 := bstep (se 1 (by rfl) ⟨398936, by rfl⟩ : syracuseStep 531915 = 797873) B797873
theorem B531927 : Blo 531801 531927 := bstep (se 1 (by rfl) ⟨398945, by rfl⟩ : syracuseStep 531927 = 797891) B797891
theorem B531947 : Blo 531801 531947 := bstep (se 1 (by rfl) ⟨398960, by rfl⟩ : syracuseStep 531947 = 797921) B797921
theorem B531959 : Blo 531801 531959 := bstep (se 1 (by rfl) ⟨398969, by rfl⟩ : syracuseStep 531959 = 797939) B797939
theorem B531979 : Blo 531801 531979 := bstep (se 1 (by rfl) ⟨398984, by rfl⟩ : syracuseStep 531979 = 797969) B797969
theorem B2170385 : Blo 531801 2170385 := bstep (se 2 (by rfl) ⟨813894, by rfl⟩ : syracuseStep 2170385 = 1627789) B1627789
theorem B531991 : Blo 531801 531991 := bstep (se 1 (by rfl) ⟨398993, by rfl⟩ : syracuseStep 531991 = 797987) B797987
theorem B532011 : Blo 531801 532011 := bstep (se 1 (by rfl) ⟨399008, by rfl⟩ : syracuseStep 532011 = 798017) B798017
theorem B532023 : Blo 531801 532023 := bstep (se 1 (by rfl) ⟨399017, by rfl⟩ : syracuseStep 532023 = 798035) B798035
theorem B532043 : Blo 531801 532043 := bstep (se 1 (by rfl) ⟨399032, by rfl⟩ : syracuseStep 532043 = 798065) B798065
theorem B532055 : Blo 531801 532055 := bstep (se 1 (by rfl) ⟨399041, by rfl⟩ : syracuseStep 532055 = 798083) B798083
theorem B532075 : Blo 531801 532075 := bstep (se 1 (by rfl) ⟨399056, by rfl⟩ : syracuseStep 532075 = 798113) B798113
theorem B532087 : Blo 531801 532087 := bstep (se 1 (by rfl) ⟨399065, by rfl⟩ : syracuseStep 532087 = 798131) B798131
theorem B532107 : Blo 531801 532107 := bstep (se 1 (by rfl) ⟨399080, by rfl⟩ : syracuseStep 532107 = 798161) B798161
theorem B532119 : Blo 531801 532119 := bstep (se 1 (by rfl) ⟨399089, by rfl⟩ : syracuseStep 532119 = 798179) B798179
theorem B532139 : Blo 531801 532139 := bstep (se 1 (by rfl) ⟨399104, by rfl⟩ : syracuseStep 532139 = 798209) B798209
theorem B532151 : Blo 531801 532151 := bstep (se 1 (by rfl) ⟨399113, by rfl⟩ : syracuseStep 532151 = 798227) B798227
theorem B532171 : Blo 531801 532171 := bstep (se 1 (by rfl) ⟨399128, by rfl⟩ : syracuseStep 532171 = 798257) B798257
theorem B532183 : Blo 531801 532183 := bstep (se 1 (by rfl) ⟨399137, by rfl⟩ : syracuseStep 532183 = 798275) B798275
theorem B532203 : Blo 531801 532203 := bstep (se 1 (by rfl) ⟨399152, by rfl⟩ : syracuseStep 532203 = 798305) B798305
theorem B532215 : Blo 531801 532215 := bstep (se 1 (by rfl) ⟨399161, by rfl⟩ : syracuseStep 532215 = 798323) B798323
theorem B532235 : Blo 531801 532235 := bstep (se 1 (by rfl) ⟨399176, by rfl⟩ : syracuseStep 532235 = 798353) B798353
theorem B532247 : Blo 531801 532247 := bstep (se 1 (by rfl) ⟨399185, by rfl⟩ : syracuseStep 532247 = 798371) B798371
theorem B532267 : Blo 531801 532267 := bstep (se 1 (by rfl) ⟨399200, by rfl⟩ : syracuseStep 532267 = 798401) B798401
theorem B1351475 : Blo 531801 1351475 := bstep (se 1 (by rfl) ⟨1013606, by rfl⟩ : syracuseStep 1351475 = 2027213) B2027213
theorem B532279 : Blo 531801 532279 := bstep (se 1 (by rfl) ⟨399209, by rfl⟩ : syracuseStep 532279 = 798419) B798419
theorem B532299 : Blo 531801 532299 := bstep (se 1 (by rfl) ⟨399224, by rfl⟩ : syracuseStep 532299 = 798449) B798449
theorem B532311 : Blo 531801 532311 := bstep (se 1 (by rfl) ⟨399233, by rfl⟩ : syracuseStep 532311 = 798467) B798467
theorem B1711961 : Blo 531801 1711961 := bstep (se 2 (by rfl) ⟨641985, by rfl⟩ : syracuseStep 1711961 = 1283971) B1283971
theorem B532331 : Blo 531801 532331 := bstep (se 1 (by rfl) ⟨399248, by rfl⟩ : syracuseStep 532331 = 798497) B798497
theorem B532343 : Blo 531801 532343 := bstep (se 1 (by rfl) ⟨399257, by rfl⟩ : syracuseStep 532343 = 798515) B798515
theorem B532363 : Blo 531801 532363 := bstep (se 1 (by rfl) ⟨399272, by rfl⟩ : syracuseStep 532363 = 798545) B798545
theorem B532375 : Blo 531801 532375 := bstep (se 1 (by rfl) ⟨399281, by rfl⟩ : syracuseStep 532375 = 798563) B798563
theorem B532395 : Blo 531801 532395 := bstep (se 1 (by rfl) ⟨399296, by rfl⟩ : syracuseStep 532395 = 798593) B798593
theorem B532407 : Blo 531801 532407 := bstep (se 1 (by rfl) ⟨399305, by rfl⟩ : syracuseStep 532407 = 798611) B798611
theorem B532427 : Blo 531801 532427 := bstep (se 1 (by rfl) ⟨399320, by rfl⟩ : syracuseStep 532427 = 798641) B798641
theorem B532439 : Blo 531801 532439 := bstep (se 1 (by rfl) ⟨399329, by rfl⟩ : syracuseStep 532439 = 798659) B798659
theorem B532459 : Blo 531801 532459 := bstep (se 1 (by rfl) ⟨399344, by rfl⟩ : syracuseStep 532459 = 798689) B798689
theorem B958451 : Blo 531801 958451 := bstep (se 1 (by rfl) ⟨718838, by rfl⟩ : syracuseStep 958451 = 1437677) B1437677
theorem B532471 : Blo 531801 532471 := bstep (se 1 (by rfl) ⟨399353, by rfl⟩ : syracuseStep 532471 = 798707) B798707
theorem B532491 : Blo 531801 532491 := bstep (se 1 (by rfl) ⟨399368, by rfl⟩ : syracuseStep 532491 = 798737) B798737
theorem B532503 : Blo 531801 532503 := bstep (se 1 (by rfl) ⟨399377, by rfl⟩ : syracuseStep 532503 = 798755) B798755
theorem B532523 : Blo 531801 532523 := bstep (se 1 (by rfl) ⟨399392, by rfl⟩ : syracuseStep 532523 = 798785) B798785
theorem B532535 : Blo 531801 532535 := bstep (se 1 (by rfl) ⟨399401, by rfl⟩ : syracuseStep 532535 = 798803) B798803
theorem B532555 : Blo 531801 532555 := bstep (se 1 (by rfl) ⟨399416, by rfl⟩ : syracuseStep 532555 = 798833) B798833
theorem B532567 : Blo 531801 532567 := bstep (se 1 (by rfl) ⟨399425, by rfl⟩ : syracuseStep 532567 = 798851) B798851
theorem B532587 : Blo 531801 532587 := bstep (se 1 (by rfl) ⟨399440, by rfl⟩ : syracuseStep 532587 = 798881) B798881
theorem B532599 : Blo 531801 532599 := bstep (se 1 (by rfl) ⟨399449, by rfl⟩ : syracuseStep 532599 = 798899) B798899
theorem B532619 : Blo 531801 532619 := bstep (se 1 (by rfl) ⟨399464, by rfl⟩ : syracuseStep 532619 = 798929) B798929
theorem B532631 : Blo 531801 532631 := bstep (se 1 (by rfl) ⟨399473, by rfl⟩ : syracuseStep 532631 = 798947) B798947
theorem B532651 : Blo 531801 532651 := bstep (se 1 (by rfl) ⟨399488, by rfl⟩ : syracuseStep 532651 = 798977) B798977
theorem B3842225 : Blo 531801 3842225 := bstep (se 2 (by rfl) ⟨1440834, by rfl⟩ : syracuseStep 3842225 = 2881669) B2881669
theorem B532663 : Blo 531801 532663 := bstep (se 1 (by rfl) ⟨399497, by rfl⟩ : syracuseStep 532663 = 798995) B798995
theorem B532683 : Blo 531801 532683 := bstep (se 1 (by rfl) ⟨399512, by rfl⟩ : syracuseStep 532683 = 799025) B799025
theorem B2171083 : Blo 531801 2171083 := bstep (se 1 (by rfl) ⟨1628312, by rfl⟩ : syracuseStep 2171083 = 3256625) B3256625
theorem B532695 : Blo 531801 532695 := bstep (se 1 (by rfl) ⟨399521, by rfl⟩ : syracuseStep 532695 = 799043) B799043
theorem B532715 : Blo 531801 532715 := bstep (se 1 (by rfl) ⟨399536, by rfl⟩ : syracuseStep 532715 = 799073) B799073
theorem B532727 : Blo 531801 532727 := bstep (se 1 (by rfl) ⟨399545, by rfl⟩ : syracuseStep 532727 = 799091) B799091
theorem B532747 : Blo 531801 532747 := bstep (se 1 (by rfl) ⟨399560, by rfl⟩ : syracuseStep 532747 = 799121) B799121
theorem B532759 : Blo 531801 532759 := bstep (se 1 (by rfl) ⟨399569, by rfl⟩ : syracuseStep 532759 = 799139) B799139
theorem B4858147 : Blo 531801 4858147 := bstep (se 1 (by rfl) ⟨3643610, by rfl⟩ : syracuseStep 4858147 = 7287221) B7287221
theorem B598315 : Blo 531801 598315 := bstep (se 1 (by rfl) ⟨448736, by rfl⟩ : syracuseStep 598315 = 897473) B897473
theorem B532779 : Blo 531801 532779 := bstep (se 1 (by rfl) ⟨399584, by rfl⟩ : syracuseStep 532779 = 799169) B799169
theorem B532791 : Blo 531801 532791 := bstep (se 1 (by rfl) ⟨399593, by rfl⟩ : syracuseStep 532791 = 799187) B799187
theorem B532811 : Blo 531801 532811 := bstep (se 1 (by rfl) ⟨399608, by rfl⟩ : syracuseStep 532811 = 799217) B799217
theorem B1352011 : Blo 531801 1352011 := bstep (se 1 (by rfl) ⟨1014008, by rfl⟩ : syracuseStep 1352011 = 2028017) B2028017
theorem B532823 : Blo 531801 532823 := bstep (se 1 (by rfl) ⟨399617, by rfl⟩ : syracuseStep 532823 = 799235) B799235
theorem B2695517 : Blo 531801 2695517 := bstep (se 3 (by rfl) ⟨505409, by rfl⟩ : syracuseStep 2695517 = 1010819) B1010819
theorem B2892133 : Blo 531801 2892133 := bstep (se 4 (by rfl) ⟨271137, by rfl⟩ : syracuseStep 2892133 = 542275) B542275
theorem B532843 : Blo 531801 532843 := bstep (se 1 (by rfl) ⟨399632, by rfl⟩ : syracuseStep 532843 = 799265) B799265
theorem B532855 : Blo 531801 532855 := bstep (se 1 (by rfl) ⟨399641, by rfl⟩ : syracuseStep 532855 = 799283) B799283
theorem B532875 : Blo 531801 532875 := bstep (se 1 (by rfl) ⟨399656, by rfl⟩ : syracuseStep 532875 = 799313) B799313
theorem B598423 : Blo 531801 598423 := bstep (se 1 (by rfl) ⟨448817, by rfl⟩ : syracuseStep 598423 = 897635) B897635
theorem B532887 : Blo 531801 532887 := bstep (se 1 (by rfl) ⟨399665, by rfl⟩ : syracuseStep 532887 = 799331) B799331
theorem B532907 : Blo 531801 532907 := bstep (se 1 (by rfl) ⟨399680, by rfl⟩ : syracuseStep 532907 = 799361) B799361
theorem B532919 : Blo 531801 532919 := bstep (se 1 (by rfl) ⟨399689, by rfl⟩ : syracuseStep 532919 = 799379) B799379
theorem B532939 : Blo 531801 532939 := bstep (se 1 (by rfl) ⟨399704, by rfl⟩ : syracuseStep 532939 = 799409) B799409
theorem B532951 : Blo 531801 532951 := bstep (se 1 (by rfl) ⟨399713, by rfl⟩ : syracuseStep 532951 = 799427) B799427
theorem B1352153 : Blo 531801 1352153 := bstep (se 2 (by rfl) ⟨507057, by rfl⟩ : syracuseStep 1352153 = 1014115) B1014115
theorem B762329 : Blo 531801 762329 := bstep (se 2 (by rfl) ⟨285873, by rfl⟩ : syracuseStep 762329 = 571747) B571747
theorem B532971 : Blo 531801 532971 := bstep (se 1 (by rfl) ⟨399728, by rfl⟩ : syracuseStep 532971 = 799457) B799457
theorem B532983 : Blo 531801 532983 := bstep (se 1 (by rfl) ⟨399737, by rfl⟩ : syracuseStep 532983 = 799475) B799475
theorem B533003 : Blo 531801 533003 := bstep (se 1 (by rfl) ⟨399752, by rfl⟩ : syracuseStep 533003 = 799505) B799505
theorem B533015 : Blo 531801 533015 := bstep (se 1 (by rfl) ⟨399761, by rfl⟩ : syracuseStep 533015 = 799523) B799523
theorem B533035 : Blo 531801 533035 := bstep (se 1 (by rfl) ⟨399776, by rfl⟩ : syracuseStep 533035 = 799553) B799553
theorem B533047 : Blo 531801 533047 := bstep (se 1 (by rfl) ⟨399785, by rfl⟩ : syracuseStep 533047 = 799571) B799571
theorem B598603 : Blo 531801 598603 := bstep (se 1 (by rfl) ⟨448952, by rfl⟩ : syracuseStep 598603 = 897905) B897905
theorem B533067 : Blo 531801 533067 := bstep (se 1 (by rfl) ⟨399800, by rfl⟩ : syracuseStep 533067 = 799601) B799601
theorem B533079 : Blo 531801 533079 := bstep (se 1 (by rfl) ⟨399809, by rfl⟩ : syracuseStep 533079 = 799619) B799619
theorem B533099 : Blo 531801 533099 := bstep (se 1 (by rfl) ⟨399824, by rfl⟩ : syracuseStep 533099 = 799649) B799649
theorem B533111 : Blo 531801 533111 := bstep (se 1 (by rfl) ⟨399833, by rfl⟩ : syracuseStep 533111 = 799667) B799667
theorem B533131 : Blo 531801 533131 := bstep (se 1 (by rfl) ⟨399848, by rfl⟩ : syracuseStep 533131 = 799697) B799697
theorem B533143 : Blo 531801 533143 := bstep (se 1 (by rfl) ⟨399857, by rfl⟩ : syracuseStep 533143 = 799715) B799715
theorem B533163 : Blo 531801 533163 := bstep (se 1 (by rfl) ⟨399872, by rfl⟩ : syracuseStep 533163 = 799745) B799745
theorem B598711 : Blo 531801 598711 := bstep (se 1 (by rfl) ⟨449033, by rfl⟩ : syracuseStep 598711 = 898067) B898067
theorem B533175 : Blo 531801 533175 := bstep (se 1 (by rfl) ⟨399881, by rfl⟩ : syracuseStep 533175 = 799763) B799763
theorem B533195 : Blo 531801 533195 := bstep (se 1 (by rfl) ⟨399896, by rfl⟩ : syracuseStep 533195 = 799793) B799793
theorem B533207 : Blo 531801 533207 := bstep (se 1 (by rfl) ⟨399905, by rfl⟩ : syracuseStep 533207 = 799811) B799811
theorem B533227 : Blo 531801 533227 := bstep (se 1 (by rfl) ⟨399920, by rfl⟩ : syracuseStep 533227 = 799841) B799841
theorem B533239 : Blo 531801 533239 := bstep (se 1 (by rfl) ⟨399929, by rfl⟩ : syracuseStep 533239 = 799859) B799859
theorem B533259 : Blo 531801 533259 := bstep (se 1 (by rfl) ⟨399944, by rfl⟩ : syracuseStep 533259 = 799889) B799889
theorem B533271 : Blo 531801 533271 := bstep (se 1 (by rfl) ⟨399953, by rfl⟩ : syracuseStep 533271 = 799907) B799907
theorem B533291 : Blo 531801 533291 := bstep (se 1 (by rfl) ⟨399968, by rfl⟩ : syracuseStep 533291 = 799937) B799937
theorem B533303 : Blo 531801 533303 := bstep (se 1 (by rfl) ⟨399977, by rfl⟩ : syracuseStep 533303 = 799955) B799955
theorem B533323 : Blo 531801 533323 := bstep (se 1 (by rfl) ⟨399992, by rfl⟩ : syracuseStep 533323 = 799985) B799985
theorem B533335 : Blo 531801 533335 := bstep (se 1 (by rfl) ⟨400001, by rfl⟩ : syracuseStep 533335 = 800003) B800003
theorem B598891 : Blo 531801 598891 := bstep (se 1 (by rfl) ⟨449168, by rfl⟩ : syracuseStep 598891 = 898337) B898337
theorem B533355 : Blo 531801 533355 := bstep (se 1 (by rfl) ⟨400016, by rfl⟩ : syracuseStep 533355 = 800033) B800033
theorem B533367 : Blo 531801 533367 := bstep (se 1 (by rfl) ⟨400025, by rfl⟩ : syracuseStep 533367 = 800051) B800051
theorem B533387 : Blo 531801 533387 := bstep (se 1 (by rfl) ⟨400040, by rfl⟩ : syracuseStep 533387 = 800081) B800081
theorem B533399 : Blo 531801 533399 := bstep (se 1 (by rfl) ⟨400049, by rfl⟩ : syracuseStep 533399 = 800099) B800099
theorem B533419 : Blo 531801 533419 := bstep (se 1 (by rfl) ⟨400064, by rfl⟩ : syracuseStep 533419 = 800129) B800129
theorem B533431 : Blo 531801 533431 := bstep (se 1 (by rfl) ⟨400073, by rfl⟩ : syracuseStep 533431 = 800147) B800147
theorem B1713089 : Blo 531801 1713089 := bstep (se 2 (by rfl) ⟨642408, by rfl⟩ : syracuseStep 1713089 = 1284817) B1284817
theorem B533451 : Blo 531801 533451 := bstep (se 1 (by rfl) ⟨400088, by rfl⟩ : syracuseStep 533451 = 800177) B800177
theorem B598999 : Blo 531801 598999 := bstep (se 1 (by rfl) ⟨449249, by rfl⟩ : syracuseStep 598999 = 898499) B898499
theorem B533463 : Blo 531801 533463 := bstep (se 1 (by rfl) ⟨400097, by rfl⟩ : syracuseStep 533463 = 800195) B800195
theorem B533483 : Blo 531801 533483 := bstep (se 1 (by rfl) ⟨400112, by rfl⟩ : syracuseStep 533483 = 800225) B800225
theorem B533495 : Blo 531801 533495 := bstep (se 1 (by rfl) ⟨400121, by rfl⟩ : syracuseStep 533495 = 800243) B800243
theorem B533515 : Blo 531801 533515 := bstep (se 1 (by rfl) ⟨400136, by rfl⟩ : syracuseStep 533515 = 800273) B800273
theorem B533527 : Blo 531801 533527 := bstep (se 1 (by rfl) ⟨400145, by rfl⟩ : syracuseStep 533527 = 800291) B800291
theorem B533547 : Blo 531801 533547 := bstep (se 1 (by rfl) ⟨400160, by rfl⟩ : syracuseStep 533547 = 800321) B800321
theorem B533559 : Blo 531801 533559 := bstep (se 1 (by rfl) ⟨400169, by rfl⟩ : syracuseStep 533559 = 800339) B800339
theorem B533579 : Blo 531801 533579 := bstep (se 1 (by rfl) ⟨400184, by rfl⟩ : syracuseStep 533579 = 800369) B800369
theorem B533591 : Blo 531801 533591 := bstep (se 1 (by rfl) ⟨400193, by rfl⟩ : syracuseStep 533591 = 800387) B800387
theorem B1713241 : Blo 531801 1713241 := bstep (se 2 (by rfl) ⟨642465, by rfl⟩ : syracuseStep 1713241 = 1284931) B1284931
theorem B533611 : Blo 531801 533611 := bstep (se 1 (by rfl) ⟨400208, by rfl⟩ : syracuseStep 533611 = 800417) B800417
theorem B533623 : Blo 531801 533623 := bstep (se 1 (by rfl) ⟨400217, by rfl⟩ : syracuseStep 533623 = 800435) B800435
theorem B599179 : Blo 531801 599179 := bstep (se 1 (by rfl) ⟨449384, by rfl⟩ : syracuseStep 599179 = 898769) B898769
theorem B533643 : Blo 531801 533643 := bstep (se 1 (by rfl) ⟨400232, by rfl⟩ : syracuseStep 533643 = 800465) B800465
theorem B533655 : Blo 531801 533655 := bstep (se 1 (by rfl) ⟨400241, by rfl⟩ : syracuseStep 533655 = 800483) B800483
theorem B533675 : Blo 531801 533675 := bstep (se 1 (by rfl) ⟨400256, by rfl⟩ : syracuseStep 533675 = 800513) B800513
theorem B533687 : Blo 531801 533687 := bstep (se 1 (by rfl) ⟨400265, by rfl⟩ : syracuseStep 533687 = 800531) B800531
theorem B533707 : Blo 531801 533707 := bstep (se 1 (by rfl) ⟨400280, by rfl⟩ : syracuseStep 533707 = 800561) B800561
theorem B533719 : Blo 531801 533719 := bstep (se 1 (by rfl) ⟨400289, by rfl⟩ : syracuseStep 533719 = 800579) B800579
theorem B1516765 : Blo 531801 1516765 := bstep (se 3 (by rfl) ⟨284393, by rfl⟩ : syracuseStep 1516765 = 568787) B568787
theorem B533739 : Blo 531801 533739 := bstep (se 1 (by rfl) ⟨400304, by rfl⟩ : syracuseStep 533739 = 800609) B800609
theorem B599287 : Blo 531801 599287 := bstep (se 1 (by rfl) ⟨449465, by rfl⟩ : syracuseStep 599287 = 898931) B898931
theorem B533751 : Blo 531801 533751 := bstep (se 1 (by rfl) ⟨400313, by rfl⟩ : syracuseStep 533751 = 800627) B800627
theorem B533771 : Blo 531801 533771 := bstep (se 1 (by rfl) ⟨400328, by rfl⟩ : syracuseStep 533771 = 800657) B800657
theorem B533783 : Blo 531801 533783 := bstep (se 1 (by rfl) ⟨400337, by rfl⟩ : syracuseStep 533783 = 800675) B800675
theorem B1352983 : Blo 531801 1352983 := bstep (se 1 (by rfl) ⟨1014737, by rfl⟩ : syracuseStep 1352983 = 2029475) B2029475
theorem B1221911 : Blo 531801 1221911 := bstep (se 1 (by rfl) ⟨916433, by rfl⟩ : syracuseStep 1221911 = 1832867) B1832867
theorem B533803 : Blo 531801 533803 := bstep (se 1 (by rfl) ⟨400352, by rfl⟩ : syracuseStep 533803 = 800705) B800705
theorem B533815 : Blo 531801 533815 := bstep (se 1 (by rfl) ⟨400361, by rfl⟩ : syracuseStep 533815 = 800723) B800723
theorem B533835 : Blo 531801 533835 := bstep (se 1 (by rfl) ⟨400376, by rfl⟩ : syracuseStep 533835 = 800753) B800753
theorem B533847 : Blo 531801 533847 := bstep (se 1 (by rfl) ⟨400385, by rfl⟩ : syracuseStep 533847 = 800771) B800771
theorem B533867 : Blo 531801 533867 := bstep (se 1 (by rfl) ⟨400400, by rfl⟩ : syracuseStep 533867 = 800801) B800801
theorem B533879 : Blo 531801 533879 := bstep (se 1 (by rfl) ⟨400409, by rfl⟩ : syracuseStep 533879 = 800819) B800819
theorem B533899 : Blo 531801 533899 := bstep (se 1 (by rfl) ⟨400424, by rfl⟩ : syracuseStep 533899 = 800849) B800849
theorem B632215 : Blo 531801 632215 := bstep (se 1 (by rfl) ⟨474161, by rfl⟩ : syracuseStep 632215 = 948323) B948323
theorem B533911 : Blo 531801 533911 := bstep (se 1 (by rfl) ⟨400433, by rfl⟩ : syracuseStep 533911 = 800867) B800867
theorem B599467 : Blo 531801 599467 := bstep (se 1 (by rfl) ⟨449600, by rfl⟩ : syracuseStep 599467 = 899201) B899201
theorem B533931 : Blo 531801 533931 := bstep (se 1 (by rfl) ⟨400448, by rfl⟩ : syracuseStep 533931 = 800897) B800897
theorem B533943 : Blo 531801 533943 := bstep (se 1 (by rfl) ⟨400457, by rfl⟩ : syracuseStep 533943 = 800915) B800915
theorem B533963 : Blo 531801 533963 := bstep (se 1 (by rfl) ⟨400472, by rfl⟩ : syracuseStep 533963 = 800945) B800945
theorem B533975 : Blo 531801 533975 := bstep (se 1 (by rfl) ⟨400481, by rfl⟩ : syracuseStep 533975 = 800963) B800963
theorem B533995 : Blo 531801 533995 := bstep (se 1 (by rfl) ⟨400496, by rfl⟩ : syracuseStep 533995 = 800993) B800993
theorem B534007 : Blo 531801 534007 := bstep (se 1 (by rfl) ⟨400505, by rfl⟩ : syracuseStep 534007 = 801011) B801011
theorem B534027 : Blo 531801 534027 := bstep (se 1 (by rfl) ⟨400520, by rfl⟩ : syracuseStep 534027 = 801041) B801041
theorem B599575 : Blo 531801 599575 := bstep (se 1 (by rfl) ⟨449681, by rfl⟩ : syracuseStep 599575 = 899363) B899363
theorem B534039 : Blo 531801 534039 := bstep (se 1 (by rfl) ⟨400529, by rfl⟩ : syracuseStep 534039 = 801059) B801059
theorem B534059 : Blo 531801 534059 := bstep (se 1 (by rfl) ⟨400544, by rfl⟩ : syracuseStep 534059 = 801089) B801089
theorem B534071 : Blo 531801 534071 := bstep (se 1 (by rfl) ⟨400553, by rfl⟩ : syracuseStep 534071 = 801107) B801107
theorem B534091 : Blo 531801 534091 := bstep (se 1 (by rfl) ⟨400568, by rfl⟩ : syracuseStep 534091 = 801137) B801137
theorem B534103 : Blo 531801 534103 := bstep (se 1 (by rfl) ⟨400577, by rfl⟩ : syracuseStep 534103 = 801155) B801155
theorem B534123 : Blo 531801 534123 := bstep (se 1 (by rfl) ⟨400592, by rfl⟩ : syracuseStep 534123 = 801185) B801185
theorem B534135 : Blo 531801 534135 := bstep (se 1 (by rfl) ⟨400601, by rfl⟩ : syracuseStep 534135 = 801203) B801203
theorem B534155 : Blo 531801 534155 := bstep (se 1 (by rfl) ⟨400616, by rfl⟩ : syracuseStep 534155 = 801233) B801233
theorem B534167 : Blo 531801 534167 := bstep (se 1 (by rfl) ⟨400625, by rfl⟩ : syracuseStep 534167 = 801251) B801251
theorem B534187 : Blo 531801 534187 := bstep (se 1 (by rfl) ⟨400640, by rfl⟩ : syracuseStep 534187 = 801281) B801281
theorem B534199 : Blo 531801 534199 := bstep (se 1 (by rfl) ⟨400649, by rfl⟩ : syracuseStep 534199 = 801299) B801299
theorem B599755 : Blo 531801 599755 := bstep (se 1 (by rfl) ⟨449816, by rfl⟩ : syracuseStep 599755 = 899633) B899633
theorem B534219 : Blo 531801 534219 := bstep (se 1 (by rfl) ⟨400664, by rfl⟩ : syracuseStep 534219 = 801329) B801329
theorem B1353419 : Blo 531801 1353419 := bstep (se 1 (by rfl) ⟨1015064, by rfl⟩ : syracuseStep 1353419 = 2030129) B2030129
theorem B534231 : Blo 531801 534231 := bstep (se 1 (by rfl) ⟨400673, by rfl⟩ : syracuseStep 534231 = 801347) B801347
theorem B534251 : Blo 531801 534251 := bstep (se 1 (by rfl) ⟨400688, by rfl⟩ : syracuseStep 534251 = 801377) B801377
theorem B534263 : Blo 531801 534263 := bstep (se 1 (by rfl) ⟨400697, by rfl⟩ : syracuseStep 534263 = 801395) B801395
theorem B534283 : Blo 531801 534283 := bstep (se 1 (by rfl) ⟨400712, by rfl⟩ : syracuseStep 534283 = 801425) B801425
theorem B534295 : Blo 531801 534295 := bstep (se 1 (by rfl) ⟨400721, by rfl⟩ : syracuseStep 534295 = 801443) B801443
theorem B534315 : Blo 531801 534315 := bstep (se 1 (by rfl) ⟨400736, by rfl⟩ : syracuseStep 534315 = 801473) B801473
theorem B7808813 : Blo 531801 7808813 := bstep (se 3 (by rfl) ⟨1464152, by rfl⟩ : syracuseStep 7808813 = 2928305) B2928305
theorem B599863 : Blo 531801 599863 := bstep (se 1 (by rfl) ⟨449897, by rfl⟩ : syracuseStep 599863 = 899795) B899795
theorem B534327 : Blo 531801 534327 := bstep (se 1 (by rfl) ⟨400745, by rfl⟩ : syracuseStep 534327 = 801491) B801491
theorem B534347 : Blo 531801 534347 := bstep (se 1 (by rfl) ⟨400760, by rfl⟩ : syracuseStep 534347 = 801521) B801521
theorem B534359 : Blo 531801 534359 := bstep (se 1 (by rfl) ⟨400769, by rfl⟩ : syracuseStep 534359 = 801539) B801539
theorem B534379 : Blo 531801 534379 := bstep (se 1 (by rfl) ⟨400784, by rfl⟩ : syracuseStep 534379 = 801569) B801569
theorem B534391 : Blo 531801 534391 := bstep (se 1 (by rfl) ⟨400793, by rfl⟩ : syracuseStep 534391 = 801587) B801587
theorem B2566019 : Blo 531801 2566019 := bstep (se 1 (by rfl) ⟨1924514, by rfl⟩ : syracuseStep 2566019 = 3849029) B3849029
theorem B534411 : Blo 531801 534411 := bstep (se 1 (by rfl) ⟨400808, by rfl⟩ : syracuseStep 534411 = 801617) B801617
theorem B534423 : Blo 531801 534423 := bstep (se 1 (by rfl) ⟨400817, by rfl⟩ : syracuseStep 534423 = 801635) B801635
theorem B534443 : Blo 531801 534443 := bstep (se 1 (by rfl) ⟨400832, by rfl⟩ : syracuseStep 534443 = 801665) B801665
theorem B534455 : Blo 531801 534455 := bstep (se 1 (by rfl) ⟨400841, by rfl⟩ : syracuseStep 534455 = 801683) B801683
theorem B534475 : Blo 531801 534475 := bstep (se 1 (by rfl) ⟨400856, by rfl⟩ : syracuseStep 534475 = 801713) B801713
theorem B534487 : Blo 531801 534487 := bstep (se 1 (by rfl) ⟨400865, by rfl⟩ : syracuseStep 534487 = 801731) B801731
theorem B600043 : Blo 531801 600043 := bstep (se 1 (by rfl) ⟨450032, by rfl⟩ : syracuseStep 600043 = 900065) B900065
theorem B534507 : Blo 531801 534507 := bstep (se 1 (by rfl) ⟨400880, by rfl⟩ : syracuseStep 534507 = 801761) B801761
theorem B534519 : Blo 531801 534519 := bstep (se 1 (by rfl) ⟨400889, by rfl⟩ : syracuseStep 534519 = 801779) B801779
theorem B534539 : Blo 531801 534539 := bstep (se 1 (by rfl) ⟨400904, by rfl⟩ : syracuseStep 534539 = 801809) B801809
theorem B534551 : Blo 531801 534551 := bstep (se 1 (by rfl) ⟨400913, by rfl⟩ : syracuseStep 534551 = 801827) B801827
theorem B534571 : Blo 531801 534571 := bstep (se 1 (by rfl) ⟨400928, by rfl⟩ : syracuseStep 534571 = 801857) B801857
theorem B534583 : Blo 531801 534583 := bstep (se 1 (by rfl) ⟨400937, by rfl⟩ : syracuseStep 534583 = 801875) B801875
theorem B1353793 : Blo 531801 1353793 := bstep (se 2 (by rfl) ⟨507672, by rfl⟩ : syracuseStep 1353793 = 1015345) B1015345
theorem B534603 : Blo 531801 534603 := bstep (se 1 (by rfl) ⟨400952, by rfl⟩ : syracuseStep 534603 = 801905) B801905
theorem B600151 : Blo 531801 600151 := bstep (se 1 (by rfl) ⟨450113, by rfl⟩ : syracuseStep 600151 = 900227) B900227
theorem B534615 : Blo 531801 534615 := bstep (se 1 (by rfl) ⟨400961, by rfl⟩ : syracuseStep 534615 = 801923) B801923
theorem B534635 : Blo 531801 534635 := bstep (se 1 (by rfl) ⟨400976, by rfl⟩ : syracuseStep 534635 = 801953) B801953
theorem B534647 : Blo 531801 534647 := bstep (se 1 (by rfl) ⟨400985, by rfl⟩ : syracuseStep 534647 = 801971) B801971
theorem B534667 : Blo 531801 534667 := bstep (se 1 (by rfl) ⟨401000, by rfl⟩ : syracuseStep 534667 = 802001) B802001
theorem B534679 : Blo 531801 534679 := bstep (se 1 (by rfl) ⟨401009, by rfl⟩ : syracuseStep 534679 = 802019) B802019
theorem B534699 : Blo 531801 534699 := bstep (se 1 (by rfl) ⟨401024, by rfl⟩ : syracuseStep 534699 = 802049) B802049
theorem B534711 : Blo 531801 534711 := bstep (se 1 (by rfl) ⟨401033, by rfl⟩ : syracuseStep 534711 = 802067) B802067
theorem B534731 : Blo 531801 534731 := bstep (se 1 (by rfl) ⟨401048, by rfl⟩ : syracuseStep 534731 = 802097) B802097
theorem B534743 : Blo 531801 534743 := bstep (se 1 (by rfl) ⟨401057, by rfl⟩ : syracuseStep 534743 = 802115) B802115
theorem B534763 : Blo 531801 534763 := bstep (se 1 (by rfl) ⟨401072, by rfl⟩ : syracuseStep 534763 = 802145) B802145
theorem B534775 : Blo 531801 534775 := bstep (se 1 (by rfl) ⟨401081, by rfl⟩ : syracuseStep 534775 = 802163) B802163
theorem B600331 : Blo 531801 600331 := bstep (se 1 (by rfl) ⟨450248, by rfl⟩ : syracuseStep 600331 = 900497) B900497
theorem B534795 : Blo 531801 534795 := bstep (se 1 (by rfl) ⟨401096, by rfl⟩ : syracuseStep 534795 = 802193) B802193
theorem B534807 : Blo 531801 534807 := bstep (se 1 (by rfl) ⟨401105, by rfl⟩ : syracuseStep 534807 = 802211) B802211
theorem B534827 : Blo 531801 534827 := bstep (se 1 (by rfl) ⟨401120, by rfl⟩ : syracuseStep 534827 = 802241) B802241
theorem B5122349 : Blo 531801 5122349 := bstep (se 3 (by rfl) ⟨960440, by rfl⟩ : syracuseStep 5122349 = 1920881) B1920881
theorem B534839 : Blo 531801 534839 := bstep (se 1 (by rfl) ⟨401129, by rfl⟩ : syracuseStep 534839 = 802259) B802259
theorem B534859 : Blo 531801 534859 := bstep (se 1 (by rfl) ⟨401144, by rfl⟩ : syracuseStep 534859 = 802289) B802289
theorem B534871 : Blo 531801 534871 := bstep (se 1 (by rfl) ⟨401153, by rfl⟩ : syracuseStep 534871 = 802307) B802307
theorem B534891 : Blo 531801 534891 := bstep (se 1 (by rfl) ⟨401168, by rfl⟩ : syracuseStep 534891 = 802337) B802337
theorem B600439 : Blo 531801 600439 := bstep (se 1 (by rfl) ⟨450329, by rfl⟩ : syracuseStep 600439 = 900659) B900659
theorem B534903 : Blo 531801 534903 := bstep (se 1 (by rfl) ⟨401177, by rfl⟩ : syracuseStep 534903 = 802355) B802355
theorem B534923 : Blo 531801 534923 := bstep (se 1 (by rfl) ⟨401192, by rfl⟩ : syracuseStep 534923 = 802385) B802385
theorem B2697623 : Blo 531801 2697623 := bstep (se 1 (by rfl) ⟨2023217, by rfl⟩ : syracuseStep 2697623 = 4046435) B4046435
theorem B534935 : Blo 531801 534935 := bstep (se 1 (by rfl) ⟨401201, by rfl⟩ : syracuseStep 534935 = 802403) B802403
theorem B534955 : Blo 531801 534955 := bstep (se 1 (by rfl) ⟨401216, by rfl⟩ : syracuseStep 534955 = 802433) B802433
theorem B6498737 : Blo 531801 6498737 := bstep (se 2 (by rfl) ⟨2437026, by rfl⟩ : syracuseStep 6498737 = 4874053) B4874053
theorem B534967 : Blo 531801 534967 := bstep (se 1 (by rfl) ⟨401225, by rfl⟩ : syracuseStep 534967 = 802451) B802451
theorem B534987 : Blo 531801 534987 := bstep (se 1 (by rfl) ⟨401240, by rfl⟩ : syracuseStep 534987 = 802481) B802481
theorem B534999 : Blo 531801 534999 := bstep (se 1 (by rfl) ⟨401249, by rfl⟩ : syracuseStep 534999 = 802499) B802499
theorem B1518041 : Blo 531801 1518041 := bstep (se 2 (by rfl) ⟨569265, by rfl⟩ : syracuseStep 1518041 = 1138531) B1138531
theorem B535019 : Blo 531801 535019 := bstep (se 1 (by rfl) ⟨401264, by rfl⟩ : syracuseStep 535019 = 802529) B802529
theorem B535031 : Blo 531801 535031 := bstep (se 1 (by rfl) ⟨401273, by rfl⟩ : syracuseStep 535031 = 802547) B802547
theorem B535051 : Blo 531801 535051 := bstep (se 1 (by rfl) ⟨401288, by rfl⟩ : syracuseStep 535051 = 802577) B802577
theorem B2566673 : Blo 531801 2566673 := bstep (se 2 (by rfl) ⟨962502, by rfl⟩ : syracuseStep 2566673 = 1925005) B1925005
theorem B535063 : Blo 531801 535063 := bstep (se 1 (by rfl) ⟨401297, by rfl⟩ : syracuseStep 535063 = 802595) B802595
theorem B600619 : Blo 531801 600619 := bstep (se 1 (by rfl) ⟨450464, by rfl⟩ : syracuseStep 600619 = 900929) B900929
theorem B535083 : Blo 531801 535083 := bstep (se 1 (by rfl) ⟨401312, by rfl⟩ : syracuseStep 535083 = 802625) B802625
theorem B535095 : Blo 531801 535095 := bstep (se 1 (by rfl) ⟨401321, by rfl⟩ : syracuseStep 535095 = 802643) B802643
theorem B535115 : Blo 531801 535115 := bstep (se 1 (by rfl) ⟨401336, by rfl⟩ : syracuseStep 535115 = 802673) B802673
theorem B535127 : Blo 531801 535127 := bstep (se 1 (by rfl) ⟨401345, by rfl⟩ : syracuseStep 535127 = 802691) B802691
theorem B535147 : Blo 531801 535147 := bstep (se 1 (by rfl) ⟨401360, by rfl⟩ : syracuseStep 535147 = 802721) B802721
theorem B535159 : Blo 531801 535159 := bstep (se 1 (by rfl) ⟨401369, by rfl⟩ : syracuseStep 535159 = 802739) B802739
theorem B535179 : Blo 531801 535179 := bstep (se 1 (by rfl) ⟨401384, by rfl⟩ : syracuseStep 535179 = 802769) B802769
theorem B600727 : Blo 531801 600727 := bstep (se 1 (by rfl) ⟨450545, by rfl⟩ : syracuseStep 600727 = 901091) B901091
theorem B1354391 : Blo 531801 1354391 := bstep (se 1 (by rfl) ⟨1015793, by rfl⟩ : syracuseStep 1354391 = 2031587) B2031587
theorem B535191 : Blo 531801 535191 := bstep (se 1 (by rfl) ⟨401393, by rfl⟩ : syracuseStep 535191 = 802787) B802787
theorem B535211 : Blo 531801 535211 := bstep (se 1 (by rfl) ⟨401408, by rfl⟩ : syracuseStep 535211 = 802817) B802817
theorem B535223 : Blo 531801 535223 := bstep (se 1 (by rfl) ⟨401417, by rfl⟩ : syracuseStep 535223 = 802835) B802835
theorem B535243 : Blo 531801 535243 := bstep (se 1 (by rfl) ⟨401432, by rfl⟩ : syracuseStep 535243 = 802865) B802865
theorem B535255 : Blo 531801 535255 := bstep (se 1 (by rfl) ⟨401441, by rfl⟩ : syracuseStep 535255 = 802883) B802883
theorem B535275 : Blo 531801 535275 := bstep (se 1 (by rfl) ⟨401456, by rfl⟩ : syracuseStep 535275 = 802913) B802913
theorem B535287 : Blo 531801 535287 := bstep (se 1 (by rfl) ⟨401465, by rfl⟩ : syracuseStep 535287 = 802931) B802931
theorem B6859525 : Blo 531801 6859525 := bstep (se 4 (by rfl) ⟨643080, by rfl⟩ : syracuseStep 6859525 = 1286161) B1286161
theorem B535307 : Blo 531801 535307 := bstep (se 1 (by rfl) ⟨401480, by rfl⟩ : syracuseStep 535307 = 802961) B802961
theorem B535319 : Blo 531801 535319 := bstep (se 1 (by rfl) ⟨401489, by rfl⟩ : syracuseStep 535319 = 802979) B802979
theorem B535339 : Blo 531801 535339 := bstep (se 1 (by rfl) ⟨401504, by rfl⟩ : syracuseStep 535339 = 803009) B803009
theorem B535351 : Blo 531801 535351 := bstep (se 1 (by rfl) ⟨401513, by rfl⟩ : syracuseStep 535351 = 803027) B803027
theorem B600907 : Blo 531801 600907 := bstep (se 1 (by rfl) ⟨450680, by rfl⟩ : syracuseStep 600907 = 901361) B901361
theorem B535371 : Blo 531801 535371 := bstep (se 1 (by rfl) ⟨401528, by rfl⟩ : syracuseStep 535371 = 803057) B803057
theorem B535383 : Blo 531801 535383 := bstep (se 1 (by rfl) ⟨401537, by rfl⟩ : syracuseStep 535383 = 803075) B803075
theorem B3910493 : Blo 531801 3910493 := bstep (se 3 (by rfl) ⟨733217, by rfl⟩ : syracuseStep 3910493 = 1466435) B1466435
theorem B535403 : Blo 531801 535403 := bstep (se 1 (by rfl) ⟨401552, by rfl⟩ : syracuseStep 535403 = 803105) B803105
theorem B535415 : Blo 531801 535415 := bstep (se 1 (by rfl) ⟨401561, by rfl⟩ : syracuseStep 535415 = 803123) B803123
theorem B535435 : Blo 531801 535435 := bstep (se 1 (by rfl) ⟨401576, by rfl⟩ : syracuseStep 535435 = 803153) B803153
theorem B535447 : Blo 531801 535447 := bstep (se 1 (by rfl) ⟨401585, by rfl⟩ : syracuseStep 535447 = 803171) B803171
theorem B535467 : Blo 531801 535467 := bstep (se 1 (by rfl) ⟨401600, by rfl⟩ : syracuseStep 535467 = 803201) B803201
theorem B601015 : Blo 531801 601015 := bstep (se 1 (by rfl) ⟨450761, by rfl⟩ : syracuseStep 601015 = 901523) B901523
theorem B535479 : Blo 531801 535479 := bstep (se 1 (by rfl) ⟨401609, by rfl⟩ : syracuseStep 535479 = 803219) B803219
theorem B535499 : Blo 531801 535499 := bstep (se 1 (by rfl) ⟨401624, by rfl⟩ : syracuseStep 535499 = 803249) B803249
theorem B535511 : Blo 531801 535511 := bstep (se 1 (by rfl) ⟨401633, by rfl⟩ : syracuseStep 535511 = 803267) B803267
theorem B535531 : Blo 531801 535531 := bstep (se 1 (by rfl) ⟨401648, by rfl⟩ : syracuseStep 535531 = 803297) B803297
theorem B535543 : Blo 531801 535543 := bstep (se 1 (by rfl) ⟨401657, by rfl⟩ : syracuseStep 535543 = 803315) B803315
theorem B535563 : Blo 531801 535563 := bstep (se 1 (by rfl) ⟨401672, by rfl⟩ : syracuseStep 535563 = 803345) B803345
theorem B568343 : Blo 531801 568343 := bstep (se 1 (by rfl) ⟨426257, by rfl⟩ : syracuseStep 568343 = 852515) B852515
theorem B961559 : Blo 531801 961559 := bstep (se 1 (by rfl) ⟨721169, by rfl⟩ : syracuseStep 961559 = 1442339) B1442339
theorem B535575 : Blo 531801 535575 := bstep (se 1 (by rfl) ⟨401681, by rfl⟩ : syracuseStep 535575 = 803363) B803363
theorem B535595 : Blo 531801 535595 := bstep (se 1 (by rfl) ⟨401696, by rfl⟩ : syracuseStep 535595 = 803393) B803393
theorem B535607 : Blo 531801 535607 := bstep (se 1 (by rfl) ⟨401705, by rfl⟩ : syracuseStep 535607 = 803411) B803411
theorem B797771 : Blo 531801 797771 := bstep (se 1 (by rfl) ⟨598328, by rfl⟩ : syracuseStep 797771 = 1196657) B1196657
theorem B9743435 : Blo 531801 9743435 := bstep (se 1 (by rfl) ⟨7307576, by rfl⟩ : syracuseStep 9743435 = 14615153) B14615153
theorem B535627 : Blo 531801 535627 := bstep (se 1 (by rfl) ⟨401720, by rfl⟩ : syracuseStep 535627 = 803441) B803441
theorem B797783 : Blo 531801 797783 := bstep (se 1 (by rfl) ⟨598337, by rfl⟩ : syracuseStep 797783 = 1196675) B1196675
theorem B535639 : Blo 531801 535639 := bstep (se 1 (by rfl) ⟨401729, by rfl⟩ : syracuseStep 535639 = 803459) B803459
theorem B601195 : Blo 531801 601195 := bstep (se 1 (by rfl) ⟨450896, by rfl⟩ : syracuseStep 601195 = 901793) B901793
theorem B535659 : Blo 531801 535659 := bstep (se 1 (by rfl) ⟨401744, by rfl⟩ : syracuseStep 535659 = 803489) B803489
theorem B535671 : Blo 531801 535671 := bstep (se 1 (by rfl) ⟨401753, by rfl⟩ : syracuseStep 535671 = 803507) B803507
theorem B535691 : Blo 531801 535691 := bstep (se 1 (by rfl) ⟨401768, by rfl⟩ : syracuseStep 535691 = 803537) B803537
theorem B535703 : Blo 531801 535703 := bstep (se 1 (by rfl) ⟨401777, by rfl⟩ : syracuseStep 535703 = 803555) B803555
theorem B797849 : Blo 531801 797849 := bstep (se 2 (by rfl) ⟨299193, by rfl⟩ : syracuseStep 797849 = 598387) B598387
theorem B535723 : Blo 531801 535723 := bstep (se 1 (by rfl) ⟨401792, by rfl⟩ : syracuseStep 535723 = 803585) B803585
theorem B535735 : Blo 531801 535735 := bstep (se 1 (by rfl) ⟨401801, by rfl⟩ : syracuseStep 535735 = 803603) B803603
theorem B535755 : Blo 531801 535755 := bstep (se 1 (by rfl) ⟨401816, by rfl⟩ : syracuseStep 535755 = 803633) B803633
theorem B601303 : Blo 531801 601303 := bstep (se 1 (by rfl) ⟨450977, by rfl⟩ : syracuseStep 601303 = 901955) B901955
theorem B535767 : Blo 531801 535767 := bstep (se 1 (by rfl) ⟨401825, by rfl⟩ : syracuseStep 535767 = 803651) B803651
theorem B1846493 : Blo 531801 1846493 := bstep (se 3 (by rfl) ⟨346217, by rfl⟩ : syracuseStep 1846493 = 692435) B692435
theorem B535787 : Blo 531801 535787 := bstep (se 1 (by rfl) ⟨401840, by rfl⟩ : syracuseStep 535787 = 803681) B803681
theorem B535799 : Blo 531801 535799 := bstep (se 1 (by rfl) ⟨401849, by rfl⟩ : syracuseStep 535799 = 803699) B803699
theorem B797963 : Blo 531801 797963 := bstep (se 1 (by rfl) ⟨598472, by rfl⟩ : syracuseStep 797963 = 1196945) B1196945
theorem B797975 : Blo 531801 797975 := bstep (se 1 (by rfl) ⟨598481, by rfl⟩ : syracuseStep 797975 = 1196963) B1196963
theorem B798041 : Blo 531801 798041 := bstep (se 2 (by rfl) ⟨299265, by rfl⟩ : syracuseStep 798041 = 598531) B598531
theorem B601483 : Blo 531801 601483 := bstep (se 1 (by rfl) ⟨451112, by rfl⟩ : syracuseStep 601483 = 902225) B902225
theorem B1355201 : Blo 531801 1355201 := bstep (se 2 (by rfl) ⟨508200, by rfl⟩ : syracuseStep 1355201 = 1016401) B1016401
theorem B798155 : Blo 531801 798155 := bstep (se 1 (by rfl) ⟨598616, by rfl⟩ : syracuseStep 798155 = 1197233) B1197233
theorem B798167 : Blo 531801 798167 := bstep (se 1 (by rfl) ⟨598625, by rfl⟩ : syracuseStep 798167 = 1197251) B1197251
theorem B2731481 : Blo 531801 2731481 := bstep (se 2 (by rfl) ⟨1024305, by rfl⟩ : syracuseStep 2731481 = 2048611) B2048611
theorem B601591 : Blo 531801 601591 := bstep (se 1 (by rfl) ⟨451193, by rfl⟩ : syracuseStep 601591 = 902387) B902387
theorem B798233 : Blo 531801 798233 := bstep (se 2 (by rfl) ⟨299337, by rfl⟩ : syracuseStep 798233 = 598675) B598675
theorem B798347 : Blo 531801 798347 := bstep (se 1 (by rfl) ⟨598760, by rfl⟩ : syracuseStep 798347 = 1197521) B1197521
theorem B798359 : Blo 531801 798359 := bstep (se 1 (by rfl) ⟨598769, by rfl⟩ : syracuseStep 798359 = 1197539) B1197539
theorem B601771 : Blo 531801 601771 := bstep (se 1 (by rfl) ⟨451328, by rfl⟩ : syracuseStep 601771 = 902657) B902657
theorem B2272961 : Blo 531801 2272961 := bstep (se 2 (by rfl) ⟨852360, by rfl⟩ : syracuseStep 2272961 = 1704721) B1704721
theorem B798425 : Blo 531801 798425 := bstep (se 2 (by rfl) ⟨299409, by rfl⟩ : syracuseStep 798425 = 598819) B598819
theorem B3419921 : Blo 531801 3419921 := bstep (se 2 (by rfl) ⟨1282470, by rfl⟩ : syracuseStep 3419921 = 2564941) B2564941
theorem B601879 : Blo 531801 601879 := bstep (se 1 (by rfl) ⟨451409, by rfl⟩ : syracuseStep 601879 = 902819) B902819
theorem B798539 : Blo 531801 798539 := bstep (se 1 (by rfl) ⟨598904, by rfl⟩ : syracuseStep 798539 = 1197809) B1197809
theorem B798551 : Blo 531801 798551 := bstep (se 1 (by rfl) ⟨598913, by rfl⟩ : syracuseStep 798551 = 1197827) B1197827
theorem B2273113 : Blo 531801 2273113 := bstep (se 2 (by rfl) ⟨852417, by rfl⟩ : syracuseStep 2273113 = 1704835) B1704835
theorem B1716061 : Blo 531801 1716061 := bstep (se 3 (by rfl) ⟨321761, by rfl⟩ : syracuseStep 1716061 = 643523) B643523
theorem B798617 : Blo 531801 798617 := bstep (se 2 (by rfl) ⟨299481, by rfl⟩ : syracuseStep 798617 = 598963) B598963
theorem B602059 : Blo 531801 602059 := bstep (se 1 (by rfl) ⟨451544, by rfl⟩ : syracuseStep 602059 = 903089) B903089
theorem B1355737 : Blo 531801 1355737 := bstep (se 2 (by rfl) ⟨508401, by rfl⟩ : syracuseStep 1355737 = 1016803) B1016803
theorem B798731 : Blo 531801 798731 := bstep (se 1 (by rfl) ⟨599048, by rfl⟩ : syracuseStep 798731 = 1198097) B1198097
theorem B798743 : Blo 531801 798743 := bstep (se 1 (by rfl) ⟨599057, by rfl⟩ : syracuseStep 798743 = 1198115) B1198115
theorem B602167 : Blo 531801 602167 := bstep (se 1 (by rfl) ⟨451625, by rfl⟩ : syracuseStep 602167 = 903251) B903251
theorem B1519681 : Blo 531801 1519681 := bstep (se 2 (by rfl) ⟨569880, by rfl⟩ : syracuseStep 1519681 = 1139761) B1139761
theorem B23375947 : Blo 531801 23375947 := bstep (se 1 (by rfl) ⟨17531960, by rfl⟩ : syracuseStep 23375947 = 35063921) B35063921
theorem B798809 : Blo 531801 798809 := bstep (se 2 (by rfl) ⟨299553, by rfl⟩ : syracuseStep 798809 = 599107) B599107
theorem B1716317 : Blo 531801 1716317 := bstep (se 3 (by rfl) ⟨321809, by rfl⟩ : syracuseStep 1716317 = 643619) B643619
theorem B798923 : Blo 531801 798923 := bstep (se 1 (by rfl) ⟨599192, by rfl⟩ : syracuseStep 798923 = 1198385) B1198385
theorem B798935 : Blo 531801 798935 := bstep (se 1 (by rfl) ⟨599201, by rfl⟩ : syracuseStep 798935 = 1198403) B1198403
theorem B602347 : Blo 531801 602347 := bstep (se 1 (by rfl) ⟨451760, by rfl⟩ : syracuseStep 602347 = 903521) B903521
theorem B569611 : Blo 531801 569611 := bstep (se 1 (by rfl) ⟨427208, by rfl⟩ : syracuseStep 569611 = 854417) B854417
theorem B799001 : Blo 531801 799001 := bstep (se 2 (by rfl) ⟨299625, by rfl⟩ : syracuseStep 799001 = 599251) B599251
theorem B602455 : Blo 531801 602455 := bstep (se 1 (by rfl) ⟨451841, by rfl⟩ : syracuseStep 602455 = 903683) B903683
theorem B897419 : Blo 531801 897419 := bstep (se 1 (by rfl) ⟨673064, by rfl⟩ : syracuseStep 897419 = 1346129) B1346129
theorem B799115 : Blo 531801 799115 := bstep (se 1 (by rfl) ⟨599336, by rfl⟩ : syracuseStep 799115 = 1198673) B1198673
theorem B799127 : Blo 531801 799127 := bstep (se 1 (by rfl) ⟨599345, by rfl⟩ : syracuseStep 799127 = 1198691) B1198691
theorem B799193 : Blo 531801 799193 := bstep (se 2 (by rfl) ⟨299697, by rfl⟩ : syracuseStep 799193 = 599395) B599395
theorem B897547 : Blo 531801 897547 := bstep (se 1 (by rfl) ⟨673160, by rfl⟩ : syracuseStep 897547 = 1346321) B1346321
theorem B602635 : Blo 531801 602635 := bstep (se 1 (by rfl) ⟨451976, by rfl⟩ : syracuseStep 602635 = 903953) B903953
theorem B799307 : Blo 531801 799307 := bstep (se 1 (by rfl) ⟨599480, by rfl⟩ : syracuseStep 799307 = 1198961) B1198961
theorem B799319 : Blo 531801 799319 := bstep (se 1 (by rfl) ⟨599489, by rfl⟩ : syracuseStep 799319 = 1198979) B1198979
theorem B602743 : Blo 531801 602743 := bstep (se 1 (by rfl) ⟨452057, by rfl⟩ : syracuseStep 602743 = 904115) B904115
theorem B897689 : Blo 531801 897689 := bstep (se 2 (by rfl) ⟨336633, by rfl⟩ : syracuseStep 897689 = 673267) B673267
theorem B799385 : Blo 531801 799385 := bstep (se 2 (by rfl) ⟨299769, by rfl⟩ : syracuseStep 799385 = 599539) B599539
theorem B799499 : Blo 531801 799499 := bstep (se 1 (by rfl) ⟨599624, by rfl⟩ : syracuseStep 799499 = 1199249) B1199249
theorem B799511 : Blo 531801 799511 := bstep (se 1 (by rfl) ⟨599633, by rfl⟩ : syracuseStep 799511 = 1199267) B1199267
theorem B897817 : Blo 531801 897817 := bstep (se 2 (by rfl) ⟨336681, by rfl⟩ : syracuseStep 897817 = 673363) B673363
theorem B963353 : Blo 531801 963353 := bstep (se 2 (by rfl) ⟨361257, by rfl⟩ : syracuseStep 963353 = 722515) B722515
theorem B799577 : Blo 531801 799577 := bstep (se 2 (by rfl) ⟨299841, by rfl⟩ : syracuseStep 799577 = 599683) B599683
theorem B799691 : Blo 531801 799691 := bstep (se 1 (by rfl) ⟨599768, by rfl⟩ : syracuseStep 799691 = 1199537) B1199537
theorem B799703 : Blo 531801 799703 := bstep (se 1 (by rfl) ⟨599777, by rfl⟩ : syracuseStep 799703 = 1199555) B1199555
theorem B570359 : Blo 531801 570359 := bstep (se 1 (by rfl) ⟨427769, by rfl⟩ : syracuseStep 570359 = 855539) B855539
theorem B799769 : Blo 531801 799769 := bstep (se 2 (by rfl) ⟨299913, by rfl⟩ : syracuseStep 799769 = 599827) B599827
theorem B6075485 : Blo 531801 6075485 := bstep (se 3 (by rfl) ⟨1139153, by rfl⟩ : syracuseStep 6075485 = 2278307) B2278307
theorem B799883 : Blo 531801 799883 := bstep (se 1 (by rfl) ⟨599912, by rfl⟩ : syracuseStep 799883 = 1199825) B1199825
theorem B799895 : Blo 531801 799895 := bstep (se 1 (by rfl) ⟨599921, by rfl⟩ : syracuseStep 799895 = 1199843) B1199843
theorem B799961 : Blo 531801 799961 := bstep (se 2 (by rfl) ⟨299985, by rfl⟩ : syracuseStep 799961 = 599971) B599971
theorem B800075 : Blo 531801 800075 := bstep (se 1 (by rfl) ⟨600056, by rfl⟩ : syracuseStep 800075 = 1200113) B1200113
theorem B898391 : Blo 531801 898391 := bstep (se 1 (by rfl) ⟨673793, by rfl⟩ : syracuseStep 898391 = 1347587) B1347587
theorem B800087 : Blo 531801 800087 := bstep (se 1 (by rfl) ⟨600065, by rfl⟩ : syracuseStep 800087 = 1200131) B1200131
theorem B800153 : Blo 531801 800153 := bstep (se 2 (by rfl) ⟨300057, by rfl⟩ : syracuseStep 800153 = 600115) B600115
theorem B898519 : Blo 531801 898519 := bstep (se 1 (by rfl) ⟨673889, by rfl⟩ : syracuseStep 898519 = 1347779) B1347779
theorem B800267 : Blo 531801 800267 := bstep (se 1 (by rfl) ⟨600200, by rfl⟩ : syracuseStep 800267 = 1200401) B1200401
theorem B800279 : Blo 531801 800279 := bstep (se 1 (by rfl) ⟨600209, by rfl⟩ : syracuseStep 800279 = 1200419) B1200419
theorem B2307635 : Blo 531801 2307635 := bstep (se 1 (by rfl) ⟨1730726, by rfl⟩ : syracuseStep 2307635 = 3461453) B3461453
theorem B2438707 : Blo 531801 2438707 := bstep (se 1 (by rfl) ⟨1829030, by rfl⟩ : syracuseStep 2438707 = 3658061) B3658061
theorem B800345 : Blo 531801 800345 := bstep (se 2 (by rfl) ⟨300129, by rfl⟩ : syracuseStep 800345 = 600259) B600259
theorem B800459 : Blo 531801 800459 := bstep (se 1 (by rfl) ⟨600344, by rfl⟩ : syracuseStep 800459 = 1200689) B1200689
theorem B1521355 : Blo 531801 1521355 := bstep (se 1 (by rfl) ⟨1141016, by rfl⟩ : syracuseStep 1521355 = 2282033) B2282033
theorem B800471 : Blo 531801 800471 := bstep (se 1 (by rfl) ⟨600353, by rfl⟩ : syracuseStep 800471 = 1200707) B1200707
theorem B800537 : Blo 531801 800537 := bstep (se 2 (by rfl) ⟨300201, by rfl⟩ : syracuseStep 800537 = 600403) B600403
theorem B2701187 : Blo 531801 2701187 := bstep (se 1 (by rfl) ⟨2025890, by rfl⟩ : syracuseStep 2701187 = 4051781) B4051781
theorem B800651 : Blo 531801 800651 := bstep (se 1 (by rfl) ⟨600488, by rfl⟩ : syracuseStep 800651 = 1200977) B1200977
theorem B800663 : Blo 531801 800663 := bstep (se 1 (by rfl) ⟨600497, by rfl⟩ : syracuseStep 800663 = 1200995) B1200995
theorem B800729 : Blo 531801 800729 := bstep (se 2 (by rfl) ⟨300273, by rfl⟩ : syracuseStep 800729 = 600547) B600547
theorem B1521629 : Blo 531801 1521629 := bstep (se 3 (by rfl) ⟨285305, by rfl⟩ : syracuseStep 1521629 = 570611) B570611
theorem B4339757 : Blo 531801 4339757 := bstep (se 3 (by rfl) ⟨813704, by rfl⟩ : syracuseStep 4339757 = 1627409) B1627409
theorem B899147 : Blo 531801 899147 := bstep (se 1 (by rfl) ⟨674360, by rfl⟩ : syracuseStep 899147 = 1348721) B1348721
theorem B800843 : Blo 531801 800843 := bstep (se 1 (by rfl) ⟨600632, by rfl⟩ : syracuseStep 800843 = 1201265) B1201265
theorem B800855 : Blo 531801 800855 := bstep (se 1 (by rfl) ⟨600641, by rfl⟩ : syracuseStep 800855 = 1201283) B1201283
theorem B800921 : Blo 531801 800921 := bstep (se 2 (by rfl) ⟨300345, by rfl⟩ : syracuseStep 800921 = 600691) B600691
theorem B4044977 : Blo 531801 4044977 := bstep (se 2 (by rfl) ⟨1516866, by rfl⟩ : syracuseStep 4044977 = 3033733) B3033733
theorem B899275 : Blo 531801 899275 := bstep (se 1 (by rfl) ⟨674456, by rfl⟩ : syracuseStep 899275 = 1348913) B1348913
theorem B801035 : Blo 531801 801035 := bstep (se 1 (by rfl) ⟨600776, by rfl⟩ : syracuseStep 801035 = 1201553) B1201553
theorem B801047 : Blo 531801 801047 := bstep (se 1 (by rfl) ⟨600785, by rfl⟩ : syracuseStep 801047 = 1201571) B1201571
theorem B899417 : Blo 531801 899417 := bstep (se 2 (by rfl) ⟨337281, by rfl⟩ : syracuseStep 899417 = 674563) B674563
theorem B801113 : Blo 531801 801113 := bstep (se 2 (by rfl) ⟨300417, by rfl⟩ : syracuseStep 801113 = 600835) B600835
theorem B801227 : Blo 531801 801227 := bstep (se 1 (by rfl) ⟨600920, by rfl⟩ : syracuseStep 801227 = 1201841) B1201841
theorem B801239 : Blo 531801 801239 := bstep (se 1 (by rfl) ⟨600929, by rfl⟩ : syracuseStep 801239 = 1201859) B1201859
theorem B899545 : Blo 531801 899545 := bstep (se 2 (by rfl) ⟨337329, by rfl⟩ : syracuseStep 899545 = 674659) B674659
theorem B801305 : Blo 531801 801305 := bstep (se 2 (by rfl) ⟨300489, by rfl⟩ : syracuseStep 801305 = 600979) B600979
theorem B539255 : Blo 531801 539255 := bstep (se 1 (by rfl) ⟨404441, by rfl⟩ : syracuseStep 539255 = 808883) B808883
theorem B801419 : Blo 531801 801419 := bstep (se 1 (by rfl) ⟨601064, by rfl⟩ : syracuseStep 801419 = 1202129) B1202129
theorem B4045463 : Blo 531801 4045463 := bstep (se 1 (by rfl) ⟨3034097, by rfl⟩ : syracuseStep 4045463 = 6068195) B6068195
theorem B5126807 : Blo 531801 5126807 := bstep (se 1 (by rfl) ⟨3845105, by rfl⟩ : syracuseStep 5126807 = 7690211) B7690211
theorem B801431 : Blo 531801 801431 := bstep (se 1 (by rfl) ⟨601073, by rfl⟩ : syracuseStep 801431 = 1202147) B1202147
theorem B801497 : Blo 531801 801497 := bstep (se 2 (by rfl) ⟨300561, by rfl⟩ : syracuseStep 801497 = 601123) B601123
theorem B1391411 : Blo 531801 1391411 := bstep (se 1 (by rfl) ⟨1043558, by rfl⟩ : syracuseStep 1391411 = 2087117) B2087117
theorem B801611 : Blo 531801 801611 := bstep (se 1 (by rfl) ⟨601208, by rfl⟩ : syracuseStep 801611 = 1202417) B1202417
theorem B801623 : Blo 531801 801623 := bstep (se 1 (by rfl) ⟨601217, by rfl⟩ : syracuseStep 801623 = 1202435) B1202435
theorem B801689 : Blo 531801 801689 := bstep (se 2 (by rfl) ⟨300633, by rfl⟩ : syracuseStep 801689 = 601267) B601267
theorem B801803 : Blo 531801 801803 := bstep (se 1 (by rfl) ⟨601352, by rfl⟩ : syracuseStep 801803 = 1202705) B1202705
theorem B900119 : Blo 531801 900119 := bstep (se 1 (by rfl) ⟨675089, by rfl⟩ : syracuseStep 900119 = 1350179) B1350179
theorem B801815 : Blo 531801 801815 := bstep (se 1 (by rfl) ⟨601361, by rfl⟩ : syracuseStep 801815 = 1202723) B1202723
theorem B801881 : Blo 531801 801881 := bstep (se 2 (by rfl) ⟨300705, by rfl⟩ : syracuseStep 801881 = 601411) B601411
theorem B900247 : Blo 531801 900247 := bstep (se 1 (by rfl) ⟨675185, by rfl⟩ : syracuseStep 900247 = 1350371) B1350371
theorem B2276531 : Blo 531801 2276531 := bstep (se 1 (by rfl) ⟨1707398, by rfl⟩ : syracuseStep 2276531 = 3414797) B3414797
theorem B2440385 : Blo 531801 2440385 := bstep (se 2 (by rfl) ⟨915144, by rfl⟩ : syracuseStep 2440385 = 1830289) B1830289
theorem B801995 : Blo 531801 801995 := bstep (se 1 (by rfl) ⟨601496, by rfl⟩ : syracuseStep 801995 = 1202993) B1202993
theorem B802007 : Blo 531801 802007 := bstep (se 1 (by rfl) ⟨601505, by rfl⟩ : syracuseStep 802007 = 1203011) B1203011
theorem B802073 : Blo 531801 802073 := bstep (se 2 (by rfl) ⟨300777, by rfl⟩ : syracuseStep 802073 = 601555) B601555
theorem B3030317 : Blo 531801 3030317 := bstep (se 3 (by rfl) ⟨568184, by rfl⟩ : syracuseStep 3030317 = 1136369) B1136369
theorem B1949021 : Blo 531801 1949021 := bstep (se 3 (by rfl) ⟨365441, by rfl⟩ : syracuseStep 1949021 = 730883) B730883
theorem B802187 : Blo 531801 802187 := bstep (se 1 (by rfl) ⟨601640, by rfl⟩ : syracuseStep 802187 = 1203281) B1203281
theorem B802199 : Blo 531801 802199 := bstep (se 1 (by rfl) ⟨601649, by rfl⟩ : syracuseStep 802199 = 1203299) B1203299
theorem B802265 : Blo 531801 802265 := bstep (se 2 (by rfl) ⟨300849, by rfl⟩ : syracuseStep 802265 = 601699) B601699
theorem B802379 : Blo 531801 802379 := bstep (se 1 (by rfl) ⟨601784, by rfl⟩ : syracuseStep 802379 = 1203569) B1203569
theorem B802391 : Blo 531801 802391 := bstep (se 1 (by rfl) ⟨601793, by rfl⟩ : syracuseStep 802391 = 1203587) B1203587
theorem B802457 : Blo 531801 802457 := bstep (se 2 (by rfl) ⟨300921, by rfl⟩ : syracuseStep 802457 = 601843) B601843
theorem B900875 : Blo 531801 900875 := bstep (se 1 (by rfl) ⟨675656, by rfl⟩ : syracuseStep 900875 = 1351313) B1351313
theorem B802571 : Blo 531801 802571 := bstep (se 1 (by rfl) ⟨601928, by rfl⟩ : syracuseStep 802571 = 1203857) B1203857
theorem B802583 : Blo 531801 802583 := bstep (se 1 (by rfl) ⟨601937, by rfl⟩ : syracuseStep 802583 = 1203875) B1203875
theorem B802649 : Blo 531801 802649 := bstep (se 2 (by rfl) ⟨300993, by rfl⟩ : syracuseStep 802649 = 601987) B601987
theorem B901003 : Blo 531801 901003 := bstep (se 1 (by rfl) ⟨675752, by rfl⟩ : syracuseStep 901003 = 1351505) B1351505
theorem B802763 : Blo 531801 802763 := bstep (se 1 (by rfl) ⟨602072, by rfl⟩ : syracuseStep 802763 = 1204145) B1204145
theorem B802775 : Blo 531801 802775 := bstep (se 1 (by rfl) ⟨602081, by rfl⟩ : syracuseStep 802775 = 1204163) B1204163
theorem B6864857 : Blo 531801 6864857 := bstep (se 2 (by rfl) ⟨2574321, by rfl⟩ : syracuseStep 6864857 = 5148643) B5148643
theorem B901145 : Blo 531801 901145 := bstep (se 2 (by rfl) ⟨337929, by rfl⟩ : syracuseStep 901145 = 675859) B675859
theorem B802841 : Blo 531801 802841 := bstep (se 2 (by rfl) ⟨301065, by rfl⟩ : syracuseStep 802841 = 602131) B602131
theorem B802955 : Blo 531801 802955 := bstep (se 1 (by rfl) ⟨602216, by rfl⟩ : syracuseStep 802955 = 1204433) B1204433
theorem B802967 : Blo 531801 802967 := bstep (se 1 (by rfl) ⟨602225, by rfl⟩ : syracuseStep 802967 = 1204451) B1204451
theorem B901273 : Blo 531801 901273 := bstep (se 2 (by rfl) ⟨337977, by rfl⟩ : syracuseStep 901273 = 675955) B675955
theorem B1523929 : Blo 531801 1523929 := bstep (se 2 (by rfl) ⟨571473, by rfl⟩ : syracuseStep 1523929 = 1142947) B1142947
theorem B803033 : Blo 531801 803033 := bstep (se 2 (by rfl) ⟨301137, by rfl⟩ : syracuseStep 803033 = 602275) B602275
theorem B770329 : Blo 531801 770329 := bstep (se 2 (by rfl) ⟨288873, by rfl⟩ : syracuseStep 770329 = 577747) B577747
theorem B803147 : Blo 531801 803147 := bstep (se 1 (by rfl) ⟨602360, by rfl⟩ : syracuseStep 803147 = 1204721) B1204721
theorem B803159 : Blo 531801 803159 := bstep (se 1 (by rfl) ⟨602369, by rfl⟩ : syracuseStep 803159 = 1204739) B1204739
theorem B639371 : Blo 531801 639371 := bstep (se 1 (by rfl) ⟨479528, by rfl⟩ : syracuseStep 639371 = 959057) B959057
theorem B803225 : Blo 531801 803225 := bstep (se 2 (by rfl) ⟨301209, by rfl⟩ : syracuseStep 803225 = 602419) B602419
theorem B803339 : Blo 531801 803339 := bstep (se 1 (by rfl) ⟨602504, by rfl⟩ : syracuseStep 803339 = 1205009) B1205009
theorem B1196567 : Blo 531801 1196567 := bstep (se 1 (by rfl) ⟨897425, by rfl⟩ : syracuseStep 1196567 = 1794851) B1794851
theorem B803351 : Blo 531801 803351 := bstep (se 1 (by rfl) ⟨602513, by rfl⟩ : syracuseStep 803351 = 1205027) B1205027
theorem B803417 : Blo 531801 803417 := bstep (se 2 (by rfl) ⟨301281, by rfl⟩ : syracuseStep 803417 = 602563) B602563
theorem B1196747 : Blo 531801 1196747 := bstep (se 1 (by rfl) ⟨897560, by rfl⟩ : syracuseStep 1196747 = 1795121) B1795121
theorem B803531 : Blo 531801 803531 := bstep (se 1 (by rfl) ⟨602648, by rfl⟩ : syracuseStep 803531 = 1205297) B1205297
theorem B79086293 : Blo 531801 79086293 := bstep (se 7 (by rfl) ⟨926792, by rfl⟩ : syracuseStep 79086293 = 1853585) B1853585
theorem B901847 : Blo 531801 901847 := bstep (se 1 (by rfl) ⟨676385, by rfl⟩ : syracuseStep 901847 = 1352771) B1352771
theorem B803543 : Blo 531801 803543 := bstep (se 1 (by rfl) ⟨602657, by rfl⟩ : syracuseStep 803543 = 1205315) B1205315
theorem B4735705 : Blo 531801 4735705 := bstep (se 2 (by rfl) ⟨1775889, by rfl⟩ : syracuseStep 4735705 = 3551779) B3551779
theorem B1196801 : Blo 531801 1196801 := bstep (se 2 (by rfl) ⟨448800, by rfl⟩ : syracuseStep 1196801 = 897601) B897601
theorem B803609 : Blo 531801 803609 := bstep (se 2 (by rfl) ⟨301353, by rfl⟩ : syracuseStep 803609 = 602707) B602707
theorem B1524545 : Blo 531801 1524545 := bstep (se 2 (by rfl) ⟨571704, by rfl⟩ : syracuseStep 1524545 = 1143409) B1143409
theorem B901975 : Blo 531801 901975 := bstep (se 1 (by rfl) ⟨676481, by rfl⟩ : syracuseStep 901975 = 1352963) B1352963
theorem B1459037 : Blo 531801 1459037 := bstep (se 3 (by rfl) ⟨273569, by rfl⟩ : syracuseStep 1459037 = 547139) B547139
theorem B1197017 : Blo 531801 1197017 := bstep (se 2 (by rfl) ⟨448881, by rfl⟩ : syracuseStep 1197017 = 897763) B897763
theorem B1197107 : Blo 531801 1197107 := bstep (se 1 (by rfl) ⟨897830, by rfl⟩ : syracuseStep 1197107 = 1795661) B1795661
theorem B1197143 : Blo 531801 1197143 := bstep (se 1 (by rfl) ⟨897857, by rfl⟩ : syracuseStep 1197143 = 1795715) B1795715
theorem B1459421 : Blo 531801 1459421 := bstep (se 3 (by rfl) ⟨273641, by rfl⟩ : syracuseStep 1459421 = 547283) B547283
theorem B1197323 : Blo 531801 1197323 := bstep (se 1 (by rfl) ⟨897992, by rfl⟩ : syracuseStep 1197323 = 1795985) B1795985
theorem B1197377 : Blo 531801 1197377 := bstep (se 2 (by rfl) ⟨449016, by rfl⟩ : syracuseStep 1197377 = 898033) B898033
theorem B3458483 : Blo 531801 3458483 := bstep (se 1 (by rfl) ⟨2593862, by rfl⟩ : syracuseStep 3458483 = 5187725) B5187725
theorem B902603 : Blo 531801 902603 := bstep (se 1 (by rfl) ⟨676952, by rfl⟩ : syracuseStep 902603 = 1353905) B1353905
theorem B2704913 : Blo 531801 2704913 := bstep (se 2 (by rfl) ⟨1014342, by rfl⟩ : syracuseStep 2704913 = 2028685) B2028685
theorem B1197593 : Blo 531801 1197593 := bstep (se 2 (by rfl) ⟨449097, by rfl⟩ : syracuseStep 1197593 = 898195) B898195
theorem B902731 : Blo 531801 902731 := bstep (se 1 (by rfl) ⟨677048, by rfl⟩ : syracuseStep 902731 = 1354097) B1354097
theorem B1197683 : Blo 531801 1197683 := bstep (se 1 (by rfl) ⟨898262, by rfl⟩ : syracuseStep 1197683 = 1796525) B1796525
theorem B4867715 : Blo 531801 4867715 := bstep (se 1 (by rfl) ⟨3650786, by rfl⟩ : syracuseStep 4867715 = 7301573) B7301573
theorem B1197719 : Blo 531801 1197719 := bstep (se 1 (by rfl) ⟨898289, by rfl⟩ : syracuseStep 1197719 = 1796579) B1796579
theorem B2705075 : Blo 531801 2705075 := bstep (se 1 (by rfl) ⟨2028806, by rfl⟩ : syracuseStep 2705075 = 4057613) B4057613
theorem B902873 : Blo 531801 902873 := bstep (se 2 (by rfl) ⟨338577, by rfl⟩ : syracuseStep 902873 = 677155) B677155
theorem B1197899 : Blo 531801 1197899 := bstep (se 1 (by rfl) ⟨898424, by rfl⟩ : syracuseStep 1197899 = 1796849) B1796849
theorem B903001 : Blo 531801 903001 := bstep (se 2 (by rfl) ⟨338625, by rfl⟩ : syracuseStep 903001 = 677251) B677251
theorem B13846373 : Blo 531801 13846373 := bstep (se 4 (by rfl) ⟨1298097, by rfl⟩ : syracuseStep 13846373 = 2596195) B2596195
theorem B1197953 : Blo 531801 1197953 := bstep (se 2 (by rfl) ⟨449232, by rfl⟩ : syracuseStep 1197953 = 898465) B898465
theorem B2279299 : Blo 531801 2279299 := bstep (se 1 (by rfl) ⟨1709474, by rfl⟩ : syracuseStep 2279299 = 3418949) B3418949
theorem B673687 : Blo 531801 673687 := bstep (se 1 (by rfl) ⟨505265, by rfl⟩ : syracuseStep 673687 = 1010531) B1010531
theorem B4573259 : Blo 531801 4573259 := bstep (se 1 (by rfl) ⟨3429944, by rfl⟩ : syracuseStep 4573259 = 6859889) B6859889
theorem B1198169 : Blo 531801 1198169 := bstep (se 2 (by rfl) ⟨449313, by rfl⟩ : syracuseStep 1198169 = 898627) B898627
theorem B4376753 : Blo 531801 4376753 := bstep (se 2 (by rfl) ⟨1641282, by rfl⟩ : syracuseStep 4376753 = 3282565) B3282565
theorem B1198259 : Blo 531801 1198259 := bstep (se 1 (by rfl) ⟨898694, by rfl⟩ : syracuseStep 1198259 = 1797389) B1797389
theorem B1198295 : Blo 531801 1198295 := bstep (se 1 (by rfl) ⟨898721, by rfl⟩ : syracuseStep 1198295 = 1797443) B1797443
theorem B1198475 : Blo 531801 1198475 := bstep (se 1 (by rfl) ⟨898856, by rfl⟩ : syracuseStep 1198475 = 1797713) B1797713
theorem B903575 : Blo 531801 903575 := bstep (se 1 (by rfl) ⟨677681, by rfl⟩ : syracuseStep 903575 = 1355363) B1355363
theorem B1198529 : Blo 531801 1198529 := bstep (se 2 (by rfl) ⟨449448, by rfl⟩ : syracuseStep 1198529 = 898897) B898897
theorem B903703 : Blo 531801 903703 := bstep (se 1 (by rfl) ⟨677777, by rfl⟩ : syracuseStep 903703 = 1355555) B1355555
theorem B3426947 : Blo 531801 3426947 := bstep (se 1 (by rfl) ⟨2570210, by rfl⟩ : syracuseStep 3426947 = 5140421) B5140421
theorem B11586179 : Blo 531801 11586179 := bstep (se 1 (by rfl) ⟨8689634, by rfl⟩ : syracuseStep 11586179 = 17379269) B17379269
theorem B2443927 : Blo 531801 2443927 := bstep (se 1 (by rfl) ⟨1832945, by rfl⟩ : syracuseStep 2443927 = 3665891) B3665891
theorem B1198745 : Blo 531801 1198745 := bstep (se 2 (by rfl) ⟨449529, by rfl⟩ : syracuseStep 1198745 = 899059) B899059
theorem B674507 : Blo 531801 674507 := bstep (se 1 (by rfl) ⟨505880, by rfl⟩ : syracuseStep 674507 = 1011761) B1011761
theorem B1198835 : Blo 531801 1198835 := bstep (se 1 (by rfl) ⟨899126, by rfl⟩ : syracuseStep 1198835 = 1798253) B1798253
theorem B1100531 : Blo 531801 1100531 := bstep (se 1 (by rfl) ⟨825398, by rfl⟩ : syracuseStep 1100531 = 1650797) B1650797
theorem B1198871 : Blo 531801 1198871 := bstep (se 1 (by rfl) ⟨899153, by rfl⟩ : syracuseStep 1198871 = 1798307) B1798307
theorem B2280257 : Blo 531801 2280257 := bstep (se 2 (by rfl) ⟨855096, by rfl⟩ : syracuseStep 2280257 = 1710193) B1710193
theorem B9849701 : Blo 531801 9849701 := bstep (se 4 (by rfl) ⟨923409, by rfl⟩ : syracuseStep 9849701 = 1846819) B1846819
theorem B3034007 : Blo 531801 3034007 := bstep (se 1 (by rfl) ⟨2275505, by rfl⟩ : syracuseStep 3034007 = 4551011) B4551011
theorem B1199051 : Blo 531801 1199051 := bstep (se 1 (by rfl) ⟨899288, by rfl⟩ : syracuseStep 1199051 = 1798577) B1798577
theorem B609239 : Blo 531801 609239 := bstep (se 1 (by rfl) ⟨456929, by rfl⟩ : syracuseStep 609239 = 913859) B913859
theorem B1199105 : Blo 531801 1199105 := bstep (se 2 (by rfl) ⟨449664, by rfl⟩ : syracuseStep 1199105 = 899329) B899329
theorem B3296321 : Blo 531801 3296321 := bstep (se 2 (by rfl) ⟨1236120, by rfl⟩ : syracuseStep 3296321 = 2472241) B2472241
theorem B1199321 : Blo 531801 1199321 := bstep (se 2 (by rfl) ⟨449745, by rfl⟩ : syracuseStep 1199321 = 899491) B899491
theorem B1199411 : Blo 531801 1199411 := bstep (se 1 (by rfl) ⟨899558, by rfl⟩ : syracuseStep 1199411 = 1799117) B1799117
theorem B1199447 : Blo 531801 1199447 := bstep (se 1 (by rfl) ⟨899585, by rfl⟩ : syracuseStep 1199447 = 1799171) B1799171
theorem B675211 : Blo 531801 675211 := bstep (se 1 (by rfl) ⟨506408, by rfl⟩ : syracuseStep 675211 = 1012817) B1012817
theorem B6180275 : Blo 531801 6180275 := bstep (se 1 (by rfl) ⟨4635206, by rfl⟩ : syracuseStep 6180275 = 9270413) B9270413
theorem B1199627 : Blo 531801 1199627 := bstep (se 1 (by rfl) ⟨899720, by rfl⟩ : syracuseStep 1199627 = 1799441) B1799441
theorem B5721617 : Blo 531801 5721617 := bstep (se 2 (by rfl) ⟨2145606, by rfl⟩ : syracuseStep 5721617 = 4291213) B4291213
theorem B1199681 : Blo 531801 1199681 := bstep (se 2 (by rfl) ⟨449880, by rfl⟩ : syracuseStep 1199681 = 899761) B899761
theorem B2707019 : Blo 531801 2707019 := bstep (se 1 (by rfl) ⟨2030264, by rfl⟩ : syracuseStep 2707019 = 4060529) B4060529
theorem B675479 : Blo 531801 675479 := bstep (se 1 (by rfl) ⟨506609, by rfl⟩ : syracuseStep 675479 = 1013219) B1013219
theorem B1199897 : Blo 531801 1199897 := bstep (se 2 (by rfl) ⟨449961, by rfl⟩ : syracuseStep 1199897 = 899923) B899923
theorem B1199987 : Blo 531801 1199987 := bstep (se 1 (by rfl) ⟨899990, by rfl⟩ : syracuseStep 1199987 = 1799981) B1799981
theorem B1200023 : Blo 531801 1200023 := bstep (se 1 (by rfl) ⟨900017, by rfl⟩ : syracuseStep 1200023 = 1800035) B1800035
theorem B1200203 : Blo 531801 1200203 := bstep (se 1 (by rfl) ⟨900152, by rfl⟩ : syracuseStep 1200203 = 1800305) B1800305
theorem B1200257 : Blo 531801 1200257 := bstep (se 2 (by rfl) ⟨450096, by rfl⟩ : syracuseStep 1200257 = 900193) B900193
theorem B676183 : Blo 531801 676183 := bstep (se 1 (by rfl) ⟨507137, by rfl⟩ : syracuseStep 676183 = 1014275) B1014275
theorem B1200473 : Blo 531801 1200473 := bstep (se 2 (by rfl) ⟨450177, by rfl⟩ : syracuseStep 1200473 = 900355) B900355
theorem B1200563 : Blo 531801 1200563 := bstep (se 1 (by rfl) ⟨900422, by rfl⟩ : syracuseStep 1200563 = 1800845) B1800845
theorem B2281931 : Blo 531801 2281931 := bstep (se 1 (by rfl) ⟨1711448, by rfl⟩ : syracuseStep 2281931 = 3422897) B3422897
theorem B1200599 : Blo 531801 1200599 := bstep (se 1 (by rfl) ⟨900449, by rfl⟩ : syracuseStep 1200599 = 1800899) B1800899
theorem B1200779 : Blo 531801 1200779 := bstep (se 1 (by rfl) ⟨900584, by rfl⟩ : syracuseStep 1200779 = 1801169) B1801169
theorem B1200833 : Blo 531801 1200833 := bstep (se 2 (by rfl) ⟨450312, by rfl⟩ : syracuseStep 1200833 = 900625) B900625
theorem B7688945 : Blo 531801 7688945 := bstep (se 2 (by rfl) ⟨2883354, by rfl⟩ : syracuseStep 7688945 = 5766709) B5766709
theorem B5788421 : Blo 531801 5788421 := bstep (se 4 (by rfl) ⟨542664, by rfl⟩ : syracuseStep 5788421 = 1085329) B1085329
theorem B2020241 : Blo 531801 2020241 := bstep (se 2 (by rfl) ⟨757590, by rfl⟩ : syracuseStep 2020241 = 1515181) B1515181
theorem B1201049 : Blo 531801 1201049 := bstep (se 2 (by rfl) ⟨450393, by rfl⟩ : syracuseStep 1201049 = 900787) B900787
theorem B1201139 : Blo 531801 1201139 := bstep (se 1 (by rfl) ⟨900854, by rfl⟩ : syracuseStep 1201139 = 1801709) B1801709
theorem B1201175 : Blo 531801 1201175 := bstep (se 1 (by rfl) ⟨900881, by rfl⟩ : syracuseStep 1201175 = 1801763) B1801763
theorem B1922093 : Blo 531801 1922093 := bstep (se 3 (by rfl) ⟨360392, by rfl⟩ : syracuseStep 1922093 = 720785) B720785
theorem B1922123 : Blo 531801 1922123 := bstep (se 1 (by rfl) ⟨1441592, by rfl⟩ : syracuseStep 1922123 = 2883185) B2883185
theorem B1201355 : Blo 531801 1201355 := bstep (se 1 (by rfl) ⟨901016, by rfl⟩ : syracuseStep 1201355 = 1802033) B1802033
theorem B1135873 : Blo 531801 1135873 := bstep (se 2 (by rfl) ⟨425952, by rfl⟩ : syracuseStep 1135873 = 851905) B851905
theorem B1201409 : Blo 531801 1201409 := bstep (se 2 (by rfl) ⟨450528, by rfl⟩ : syracuseStep 1201409 = 901057) B901057
theorem B2708801 : Blo 531801 2708801 := bstep (se 2 (by rfl) ⟨1015800, by rfl⟩ : syracuseStep 2708801 = 2031601) B2031601
theorem B2020697 : Blo 531801 2020697 := bstep (se 2 (by rfl) ⟨757761, by rfl⟩ : syracuseStep 2020697 = 1515523) B1515523
theorem B1201625 : Blo 531801 1201625 := bstep (se 2 (by rfl) ⟨450609, by rfl⟩ : syracuseStep 1201625 = 901219) B901219
theorem B8640017 : Blo 531801 8640017 := bstep (se 2 (by rfl) ⟨3240006, by rfl⟩ : syracuseStep 8640017 = 6480013) B6480013
theorem B12998161 : Blo 531801 12998161 := bstep (se 2 (by rfl) ⟨4874310, by rfl⟩ : syracuseStep 12998161 = 9748621) B9748621
theorem B2020909 : Blo 531801 2020909 := bstep (se 3 (by rfl) ⟨378920, by rfl⟩ : syracuseStep 2020909 = 757841) B757841
theorem B1201715 : Blo 531801 1201715 := bstep (se 1 (by rfl) ⟨901286, by rfl⟩ : syracuseStep 1201715 = 1802573) B1802573
theorem B1955393 : Blo 531801 1955393 := bstep (se 2 (by rfl) ⟨733272, by rfl⟩ : syracuseStep 1955393 = 1466545) B1466545
theorem B1136215 : Blo 531801 1136215 := bstep (se 1 (by rfl) ⟨852161, by rfl⟩ : syracuseStep 1136215 = 1704323) B1704323
theorem B1201751 : Blo 531801 1201751 := bstep (se 1 (by rfl) ⟨901313, by rfl⟩ : syracuseStep 1201751 = 1802627) B1802627
theorem B939607 : Blo 531801 939607 := bstep (se 1 (by rfl) ⟨704705, by rfl⟩ : syracuseStep 939607 = 1409411) B1409411
theorem B1201931 : Blo 531801 1201931 := bstep (se 1 (by rfl) ⟨901448, by rfl⟩ : syracuseStep 1201931 = 1802897) B1802897
theorem B4052753 : Blo 531801 4052753 := bstep (se 2 (by rfl) ⟨1519782, by rfl⟩ : syracuseStep 4052753 = 3039565) B3039565
theorem B1201985 : Blo 531801 1201985 := bstep (se 2 (by rfl) ⟨450744, by rfl⟩ : syracuseStep 1201985 = 901489) B901489
theorem B2021213 : Blo 531801 2021213 := bstep (se 3 (by rfl) ⟨378977, by rfl⟩ : syracuseStep 2021213 = 757955) B757955
theorem B677899 : Blo 531801 677899 := bstep (se 1 (by rfl) ⟨508424, by rfl⟩ : syracuseStep 677899 = 1016849) B1016849
theorem B1202201 : Blo 531801 1202201 := bstep (se 2 (by rfl) ⟨450825, by rfl⟩ : syracuseStep 1202201 = 901651) B901651
theorem B1366067 : Blo 531801 1366067 := bstep (se 1 (by rfl) ⟨1024550, by rfl⟩ : syracuseStep 1366067 = 2049101) B2049101
theorem B1202291 : Blo 531801 1202291 := bstep (se 1 (by rfl) ⟨901718, by rfl⟩ : syracuseStep 1202291 = 1803437) B1803437
theorem B1202327 : Blo 531801 1202327 := bstep (se 1 (by rfl) ⟨901745, by rfl⟩ : syracuseStep 1202327 = 1803491) B1803491
theorem B1923245 : Blo 531801 1923245 := bstep (se 3 (by rfl) ⟨360608, by rfl⟩ : syracuseStep 1923245 = 721217) B721217
theorem B13031725 : Blo 531801 13031725 := bstep (se 3 (by rfl) ⟨2443448, by rfl⟩ : syracuseStep 13031725 = 4886897) B4886897
theorem B1202507 : Blo 531801 1202507 := bstep (se 1 (by rfl) ⟨901880, by rfl⟩ : syracuseStep 1202507 = 1803761) B1803761
theorem B1202561 : Blo 531801 1202561 := bstep (se 2 (by rfl) ⟨450960, by rfl⟩ : syracuseStep 1202561 = 901921) B901921
theorem B1137035 : Blo 531801 1137035 := bstep (se 1 (by rfl) ⟨852776, by rfl⟩ : syracuseStep 1137035 = 1705553) B1705553
theorem B1202777 : Blo 531801 1202777 := bstep (se 2 (by rfl) ⟨451041, by rfl⟩ : syracuseStep 1202777 = 902083) B902083
theorem B1202867 : Blo 531801 1202867 := bstep (se 1 (by rfl) ⟨902150, by rfl⟩ : syracuseStep 1202867 = 1804301) B1804301
theorem B1202903 : Blo 531801 1202903 := bstep (se 1 (by rfl) ⟨902177, by rfl⟩ : syracuseStep 1202903 = 1804355) B1804355
theorem B1137395 : Blo 531801 1137395 := bstep (se 1 (by rfl) ⟨853046, by rfl⟩ : syracuseStep 1137395 = 1706093) B1706093
theorem B1366807 : Blo 531801 1366807 := bstep (se 1 (by rfl) ⟨1025105, by rfl⟩ : syracuseStep 1366807 = 2050211) B2050211
theorem B1203083 : Blo 531801 1203083 := bstep (se 1 (by rfl) ⟨902312, by rfl⟩ : syracuseStep 1203083 = 1804625) B1804625
theorem B1203137 : Blo 531801 1203137 := bstep (se 2 (by rfl) ⟨451176, by rfl⟩ : syracuseStep 1203137 = 902353) B902353
theorem B12311513 : Blo 531801 12311513 := bstep (se 2 (by rfl) ⟨4616817, by rfl⟩ : syracuseStep 12311513 = 9233635) B9233635
theorem B2284595 : Blo 531801 2284595 := bstep (se 1 (by rfl) ⟨1713446, by rfl⟩ : syracuseStep 2284595 = 3426893) B3426893
theorem B1203353 : Blo 531801 1203353 := bstep (se 2 (by rfl) ⟨451257, by rfl⟩ : syracuseStep 1203353 = 902515) B902515
theorem B2710745 : Blo 531801 2710745 := bstep (se 2 (by rfl) ⟨1016529, by rfl⟩ : syracuseStep 2710745 = 2033059) B2033059
theorem B1203443 : Blo 531801 1203443 := bstep (se 1 (by rfl) ⟨902582, by rfl⟩ : syracuseStep 1203443 = 1805165) B1805165
theorem B810251 : Blo 531801 810251 := bstep (se 1 (by rfl) ⟨607688, by rfl⟩ : syracuseStep 810251 = 1215377) B1215377
theorem B1203479 : Blo 531801 1203479 := bstep (se 1 (by rfl) ⟨902609, by rfl⟩ : syracuseStep 1203479 = 1805219) B1805219
theorem B1203659 : Blo 531801 1203659 := bstep (se 1 (by rfl) ⟨902744, by rfl⟩ : syracuseStep 1203659 = 1805489) B1805489
theorem B1203713 : Blo 531801 1203713 := bstep (se 2 (by rfl) ⟨451392, by rfl⟩ : syracuseStep 1203713 = 902785) B902785
theorem B1203929 : Blo 531801 1203929 := bstep (se 2 (by rfl) ⟨451473, by rfl⟩ : syracuseStep 1203929 = 902947) B902947
theorem B17325809 : Blo 531801 17325809 := bstep (se 2 (by rfl) ⟨6497178, by rfl⟩ : syracuseStep 17325809 = 12994357) B12994357
theorem B1204019 : Blo 531801 1204019 := bstep (se 1 (by rfl) ⟨903014, by rfl⟩ : syracuseStep 1204019 = 1806029) B1806029
theorem B1367873 : Blo 531801 1367873 := bstep (se 2 (by rfl) ⟨512952, by rfl⟩ : syracuseStep 1367873 = 1025905) B1025905
theorem B1204055 : Blo 531801 1204055 := bstep (se 1 (by rfl) ⟨903041, by rfl⟩ : syracuseStep 1204055 = 1806083) B1806083
theorem B1204235 : Blo 531801 1204235 := bstep (se 1 (by rfl) ⟨903176, by rfl⟩ : syracuseStep 1204235 = 1806353) B1806353
theorem B1204289 : Blo 531801 1204289 := bstep (se 2 (by rfl) ⟨451608, by rfl⟩ : syracuseStep 1204289 = 903217) B903217
theorem B27779213 : Blo 531801 27779213 := bstep (se 3 (by rfl) ⟨5208602, by rfl⟩ : syracuseStep 27779213 = 10417205) B10417205
theorem B3039383 : Blo 531801 3039383 := bstep (se 1 (by rfl) ⟨2279537, by rfl⟩ : syracuseStep 3039383 = 4559075) B4559075
theorem B2318539 : Blo 531801 2318539 := bstep (se 1 (by rfl) ⟨1738904, by rfl⟩ : syracuseStep 2318539 = 3477809) B3477809
theorem B1204505 : Blo 531801 1204505 := bstep (se 2 (by rfl) ⟨451689, by rfl⟩ : syracuseStep 1204505 = 903379) B903379
theorem B1204595 : Blo 531801 1204595 := bstep (se 1 (by rfl) ⟨903446, by rfl⟩ : syracuseStep 1204595 = 1806893) B1806893
theorem B2023811 : Blo 531801 2023811 := bstep (se 1 (by rfl) ⟨1517858, by rfl⟩ : syracuseStep 2023811 = 3035717) B3035717
theorem B2023825 : Blo 531801 2023825 := bstep (se 2 (by rfl) ⟨758934, by rfl⟩ : syracuseStep 2023825 = 1517869) B1517869
theorem B1204631 : Blo 531801 1204631 := bstep (se 1 (by rfl) ⟨903473, by rfl⟩ : syracuseStep 1204631 = 1806947) B1806947
theorem B2286083 : Blo 531801 2286083 := bstep (se 1 (by rfl) ⟨1714562, by rfl⟩ : syracuseStep 2286083 = 3429125) B3429125
theorem B1204811 : Blo 531801 1204811 := bstep (se 1 (by rfl) ⟨903608, by rfl⟩ : syracuseStep 1204811 = 1807217) B1807217
theorem B11067997 : Blo 531801 11067997 := bstep (se 3 (by rfl) ⟨2075249, by rfl⟩ : syracuseStep 11067997 = 4150499) B4150499
theorem B1204865 : Blo 531801 1204865 := bstep (se 2 (by rfl) ⟨451824, by rfl⟩ : syracuseStep 1204865 = 903649) B903649
theorem B2024129 : Blo 531801 2024129 := bstep (se 2 (by rfl) ⟨759048, by rfl⟩ : syracuseStep 2024129 = 1518097) B1518097
theorem B1139393 : Blo 531801 1139393 := bstep (se 2 (by rfl) ⟨427272, by rfl⟩ : syracuseStep 1139393 = 854545) B854545
theorem B811723 : Blo 531801 811723 := bstep (se 1 (by rfl) ⟨608792, by rfl⟩ : syracuseStep 811723 = 1217585) B1217585
theorem B3859235 : Blo 531801 3859235 := bstep (se 1 (by rfl) ⟨2894426, by rfl⟩ : syracuseStep 3859235 = 5788853) B5788853
theorem B2712365 : Blo 531801 2712365 := bstep (se 3 (by rfl) ⟨508568, by rfl⟩ : syracuseStep 2712365 = 1017137) B1017137
theorem B1794905 : Blo 531801 1794905 := bstep (se 2 (by rfl) ⟨673089, by rfl⟩ : syracuseStep 1794905 = 1346179) B1346179
theorem B1205081 : Blo 531801 1205081 := bstep (se 2 (by rfl) ⟨451905, by rfl⟩ : syracuseStep 1205081 = 903811) B903811
theorem B8217521 : Blo 531801 8217521 := bstep (se 2 (by rfl) ⟨3081570, by rfl⟩ : syracuseStep 8217521 = 6163141) B6163141
theorem B1205171 : Blo 531801 1205171 := bstep (se 1 (by rfl) ⟨903878, by rfl⟩ : syracuseStep 1205171 = 1807757) B1807757
theorem B1205207 : Blo 531801 1205207 := bstep (se 1 (by rfl) ⟨903905, by rfl⟩ : syracuseStep 1205207 = 1807811) B1807811
theorem B1205387 : Blo 531801 1205387 := bstep (se 1 (by rfl) ⟨904040, by rfl⟩ : syracuseStep 1205387 = 1808081) B1808081
theorem B2221229 : Blo 531801 2221229 := bstep (se 3 (by rfl) ⟨416480, by rfl⟩ : syracuseStep 2221229 = 832961) B832961
theorem B1205441 : Blo 531801 1205441 := bstep (se 2 (by rfl) ⟨452040, by rfl⟩ : syracuseStep 1205441 = 904081) B904081
theorem B2876737 : Blo 531801 2876737 := bstep (se 2 (by rfl) ⟨1078776, by rfl⟩ : syracuseStep 2876737 = 2157553) B2157553
theorem B2024797 : Blo 531801 2024797 := bstep (se 3 (by rfl) ⟨379649, by rfl⟩ : syracuseStep 2024797 = 759299) B759299
theorem B1795607 : Blo 531801 1795607 := bstep (se 1 (by rfl) ⟨1346705, by rfl⟩ : syracuseStep 1795607 = 2693411) B2693411
theorem B1140247 : Blo 531801 1140247 := bstep (se 1 (by rfl) ⟨855185, by rfl⟩ : syracuseStep 1140247 = 1710371) B1710371
theorem B4056641 : Blo 531801 4056641 := bstep (se 2 (by rfl) ⟨1521240, by rfl⟩ : syracuseStep 4056641 = 3042481) B3042481
theorem B3041297 : Blo 531801 3041297 := bstep (se 2 (by rfl) ⟨1140486, by rfl⟩ : syracuseStep 3041297 = 2280973) B2280973
theorem B1796147 : Blo 531801 1796147 := bstep (se 1 (by rfl) ⟨1347110, by rfl⟩ : syracuseStep 1796147 = 2694221) B2694221
theorem B1927313 : Blo 531801 1927313 := bstep (se 2 (by rfl) ⟨722742, by rfl⟩ : syracuseStep 1927313 = 1445485) B1445485
theorem B1009817 : Blo 531801 1009817 := bstep (se 2 (by rfl) ⟨378681, by rfl⟩ : syracuseStep 1009817 = 757363) B757363
theorem B1927385 : Blo 531801 1927385 := bstep (se 2 (by rfl) ⟨722769, by rfl⟩ : syracuseStep 1927385 = 1445539) B1445539
theorem B1796417 : Blo 531801 1796417 := bstep (se 2 (by rfl) ⟨673656, by rfl⟩ : syracuseStep 1796417 = 1347313) B1347313
theorem B2157101 : Blo 531801 2157101 := bstep (se 3 (by rfl) ⟨404456, by rfl⟩ : syracuseStep 2157101 = 808913) B808913
theorem B1010227 : Blo 531801 1010227 := bstep (se 1 (by rfl) ⟨757670, by rfl⟩ : syracuseStep 1010227 = 1515341) B1515341
theorem B2058817 : Blo 531801 2058817 := bstep (se 2 (by rfl) ⟨772056, by rfl⟩ : syracuseStep 2058817 = 1544113) B1544113
theorem B2026073 : Blo 531801 2026073 := bstep (se 2 (by rfl) ⟨759777, by rfl⟩ : syracuseStep 2026073 = 1519555) B1519555
theorem B1141427 : Blo 531801 1141427 := bstep (se 1 (by rfl) ⟨856070, by rfl⟩ : syracuseStep 1141427 = 1712141) B1712141
theorem B2288321 : Blo 531801 2288321 := bstep (se 2 (by rfl) ⟨858120, by rfl⟩ : syracuseStep 2288321 = 1716241) B1716241
theorem B1796957 : Blo 531801 1796957 := bstep (se 3 (by rfl) ⟨336929, by rfl⟩ : syracuseStep 1796957 = 673859) B673859
theorem B4123543 : Blo 531801 4123543 := bstep (se 1 (by rfl) ⟨3092657, by rfl⟩ : syracuseStep 4123543 = 6185315) B6185315
theorem B13003697 : Blo 531801 13003697 := bstep (se 2 (by rfl) ⟨4876386, by rfl⟩ : syracuseStep 13003697 = 9752773) B9752773
theorem B1010713 : Blo 531801 1010713 := bstep (se 2 (by rfl) ⟨379017, by rfl⟩ : syracuseStep 1010713 = 758035) B758035
theorem B15199301 : Blo 531801 15199301 := bstep (se 4 (by rfl) ⟨1424934, by rfl⟩ : syracuseStep 15199301 = 2849869) B2849869
theorem B5762123 : Blo 531801 5762123 := bstep (se 1 (by rfl) ⟨4321592, by rfl⟩ : syracuseStep 5762123 = 8643185) B8643185
theorem B4058585 : Blo 531801 4058585 := bstep (se 2 (by rfl) ⟨1521969, by rfl⟩ : syracuseStep 4058585 = 3043939) B3043939
theorem B1011275 : Blo 531801 1011275 := bstep (se 1 (by rfl) ⟨758456, by rfl⟩ : syracuseStep 1011275 = 1516913) B1516913
theorem B912971 : Blo 531801 912971 := bstep (se 1 (by rfl) ⟨684728, by rfl⟩ : syracuseStep 912971 = 1369457) B1369457
theorem B1928897 : Blo 531801 1928897 := bstep (se 2 (by rfl) ⟨723336, by rfl⟩ : syracuseStep 1928897 = 1446673) B1446673
theorem B1011457 : Blo 531801 1011457 := bstep (se 2 (by rfl) ⟨379296, by rfl⟩ : syracuseStep 1011457 = 758593) B758593
theorem B618283 : Blo 531801 618283 := bstep (se 1 (by rfl) ⟨463712, by rfl⟩ : syracuseStep 618283 = 927425) B927425
theorem B2879333 : Blo 531801 2879333 := bstep (se 4 (by rfl) ⟨269937, by rfl⟩ : syracuseStep 2879333 = 539875) B539875
theorem B1142657 : Blo 531801 1142657 := bstep (se 2 (by rfl) ⟨428496, by rfl⟩ : syracuseStep 1142657 = 856993) B856993
theorem B1798091 : Blo 531801 1798091 := bstep (se 1 (by rfl) ⟨1348568, by rfl⟩ : syracuseStep 1798091 = 2697137) B2697137
theorem B2027699 : Blo 531801 2027699 := bstep (se 1 (by rfl) ⟨1520774, by rfl⟩ : syracuseStep 2027699 = 3041549) B3041549
theorem B618679 : Blo 531801 618679 := bstep (se 1 (by rfl) ⟨464009, by rfl⟩ : syracuseStep 618679 = 928019) B928019
theorem B2027713 : Blo 531801 2027713 := bstep (se 2 (by rfl) ⟨760392, by rfl⟩ : syracuseStep 2027713 = 1520785) B1520785
theorem B1798361 : Blo 531801 1798361 := bstep (se 2 (by rfl) ⟨674385, by rfl⟩ : syracuseStep 1798361 = 1348771) B1348771
theorem B1012171 : Blo 531801 1012171 := bstep (se 1 (by rfl) ⟨759128, by rfl⟩ : syracuseStep 1012171 = 1518257) B1518257
theorem B1831385 : Blo 531801 1831385 := bstep (se 2 (by rfl) ⟨686769, by rfl⟩ : syracuseStep 1831385 = 1373539) B1373539
theorem B1012247 : Blo 531801 1012247 := bstep (se 1 (by rfl) ⟨759185, by rfl⟩ : syracuseStep 1012247 = 1518371) B1518371
theorem B2159405 : Blo 531801 2159405 := bstep (se 3 (by rfl) ⟨404888, by rfl⟩ : syracuseStep 2159405 = 809777) B809777
theorem B2159435 : Blo 531801 2159435 := bstep (se 1 (by rfl) ⟨1619576, by rfl⟩ : syracuseStep 2159435 = 3239153) B3239153
theorem B1799063 : Blo 531801 1799063 := bstep (se 1 (by rfl) ⟨1349297, by rfl⟩ : syracuseStep 1799063 = 2698595) B2698595
theorem B685003 : Blo 531801 685003 := bstep (se 1 (by rfl) ⟨513752, by rfl⟩ : syracuseStep 685003 = 1027505) B1027505
theorem B1143767 : Blo 531801 1143767 := bstep (se 1 (by rfl) ⟨857825, by rfl⟩ : syracuseStep 1143767 = 1715651) B1715651
theorem B1012915 : Blo 531801 1012915 := bstep (se 1 (by rfl) ⟨759686, by rfl⟩ : syracuseStep 1012915 = 1519373) B1519373
theorem B1930499 : Blo 531801 1930499 := bstep (se 1 (by rfl) ⟨1447874, by rfl⟩ : syracuseStep 1930499 = 2895749) B2895749
theorem B2061571 : Blo 531801 2061571 := bstep (se 1 (by rfl) ⟨1546178, by rfl⟩ : syracuseStep 2061571 = 3092357) B3092357
theorem B587051 : Blo 531801 587051 := bstep (se 1 (by rfl) ⟨440288, by rfl⟩ : syracuseStep 587051 = 880577) B880577
theorem B4552037 : Blo 531801 4552037 := bstep (se 4 (by rfl) ⟨426753, by rfl⟩ : syracuseStep 4552037 = 853507) B853507
theorem B1013143 : Blo 531801 1013143 := bstep (se 1 (by rfl) ⟨759857, by rfl⟩ : syracuseStep 1013143 = 1519715) B1519715
theorem B1799603 : Blo 531801 1799603 := bstep (se 1 (by rfl) ⟨1349702, by rfl⟩ : syracuseStep 1799603 = 2699405) B2699405
theorem B1013249 : Blo 531801 1013249 := bstep (se 2 (by rfl) ⟨379968, by rfl⟩ : syracuseStep 1013249 = 759937) B759937
theorem B685579 : Blo 531801 685579 := bstep (se 1 (by rfl) ⟨514184, by rfl⟩ : syracuseStep 685579 = 1028369) B1028369
theorem B1013401 : Blo 531801 1013401 := bstep (se 2 (by rfl) ⟨380025, by rfl⟩ : syracuseStep 1013401 = 760051) B760051
theorem B1799873 : Blo 531801 1799873 := bstep (se 2 (by rfl) ⟨674952, by rfl⟩ : syracuseStep 1799873 = 1349905) B1349905
theorem B2029643 : Blo 531801 2029643 := bstep (se 1 (by rfl) ⟨1522232, by rfl⟩ : syracuseStep 2029643 = 3044465) B3044465
theorem B2029657 : Blo 531801 2029657 := bstep (se 2 (by rfl) ⟨761121, by rfl⟩ : syracuseStep 2029657 = 1522243) B1522243
theorem B1800413 : Blo 531801 1800413 := bstep (se 3 (by rfl) ⟨337577, by rfl⟩ : syracuseStep 1800413 = 675155) B675155
theorem B1440089 : Blo 531801 1440089 := bstep (se 2 (by rfl) ⟨540033, by rfl⟩ : syracuseStep 1440089 = 1080067) B1080067
theorem B4094509 : Blo 531801 4094509 := bstep (se 3 (by rfl) ⟨767720, by rfl⟩ : syracuseStep 4094509 = 1535441) B1535441
theorem B4061987 : Blo 531801 4061987 := bstep (se 1 (by rfl) ⟨3046490, by rfl⟩ : syracuseStep 4061987 = 6092981) B6092981
theorem B1080139 : Blo 531801 1080139 := bstep (se 1 (by rfl) ⟨810104, by rfl⟩ : syracuseStep 1080139 = 1620209) B1620209
theorem B1014707 : Blo 531801 1014707 := bstep (se 1 (by rfl) ⟨761030, by rfl⟩ : syracuseStep 1014707 = 1522061) B1522061
theorem B2030615 : Blo 531801 2030615 := bstep (se 1 (by rfl) ⟨1522961, by rfl⟩ : syracuseStep 2030615 = 3045923) B3045923
theorem B1014859 : Blo 531801 1014859 := bstep (se 1 (by rfl) ⟨761144, by rfl⟩ : syracuseStep 1014859 = 1522289) B1522289
theorem B3046673 : Blo 531801 3046673 := bstep (se 2 (by rfl) ⟨1142502, by rfl⟩ : syracuseStep 3046673 = 2285005) B2285005
theorem B1801547 : Blo 531801 1801547 := bstep (se 1 (by rfl) ⟨1351160, by rfl⟩ : syracuseStep 1801547 = 2702321) B2702321
theorem B1015193 : Blo 531801 1015193 := bstep (se 2 (by rfl) ⟨380697, by rfl⟩ : syracuseStep 1015193 = 761395) B761395
theorem B1736129 : Blo 531801 1736129 := bstep (se 2 (by rfl) ⟨651048, by rfl⟩ : syracuseStep 1736129 = 1302097) B1302097
theorem B1801817 : Blo 531801 1801817 := bstep (se 2 (by rfl) ⟨675681, by rfl⟩ : syracuseStep 1801817 = 1351363) B1351363
theorem B3047129 : Blo 531801 3047129 := bstep (se 2 (by rfl) ⟨1142673, by rfl⟩ : syracuseStep 3047129 = 2285347) B2285347
theorem B4554701 : Blo 531801 4554701 := bstep (se 3 (by rfl) ⟨854006, by rfl⟩ : syracuseStep 4554701 = 1708013) B1708013
theorem B2031905 : Blo 531801 2031905 := bstep (se 2 (by rfl) ⟨761964, by rfl⟩ : syracuseStep 2031905 = 1523929) B1523929
theorem B1802681 : Blo 531801 1802681 := bstep (se 2 (by rfl) ⟨676005, by rfl⟩ : syracuseStep 1802681 = 1352011) B1352011
theorem B10224089 : Blo 531801 10224089 := bstep (se 2 (by rfl) ⟨3834033, by rfl⟩ : syracuseStep 10224089 = 7668067) B7668067
theorem B52724195 : Blo 531801 52724195 := bstep (se 1 (by rfl) ⟨39543146, by rfl⟩ : syracuseStep 52724195 = 79086293) B79086293
theorem B1016363 : Blo 531801 1016363 := bstep (se 1 (by rfl) ⟨762272, by rfl⟩ : syracuseStep 1016363 = 1524545) B1524545
theorem B4326007 : Blo 531801 4326007 := bstep (se 1 (by rfl) ⟨3244505, by rfl⟩ : syracuseStep 4326007 = 6489011) B6489011
theorem B1639283 : Blo 531801 1639283 := bstep (se 1 (by rfl) ⟨1229462, by rfl⟩ : syracuseStep 1639283 = 2458925) B2458925
theorem B1082297 : Blo 531801 1082297 := bstep (se 2 (by rfl) ⟨405861, by rfl⟩ : syracuseStep 1082297 = 811723) B811723
theorem B1803275 : Blo 531801 1803275 := bstep (se 1 (by rfl) ⟨1352456, by rfl⟩ : syracuseStep 1803275 = 2704913) B2704913
theorem B1704989 : Blo 531801 1704989 := bstep (se 3 (by rfl) ⟨319685, by rfl⟩ : syracuseStep 1704989 = 639371) B639371
theorem B3245143 : Blo 531801 3245143 := bstep (se 1 (by rfl) ⟨2433857, by rfl⟩ : syracuseStep 3245143 = 4867715) B4867715
theorem B1803383 : Blo 531801 1803383 := bstep (se 1 (by rfl) ⟨1352537, by rfl⟩ : syracuseStep 1803383 = 2705075) B2705075
theorem B2032877 : Blo 531801 2032877 := bstep (se 3 (by rfl) ⟨381164, by rfl⟩ : syracuseStep 2032877 = 762329) B762329
theorem B3048839 : Blo 531801 3048839 := bstep (se 1 (by rfl) ⟨2286629, by rfl⟩ : syracuseStep 3048839 = 4573259) B4573259
theorem B2917835 : Blo 531801 2917835 := bstep (se 1 (by rfl) ⟨2188376, by rfl⟩ : syracuseStep 2917835 = 4376753) B4376753
theorem B1803977 : Blo 531801 1803977 := bstep (se 2 (by rfl) ⟨676491, by rfl⟩ : syracuseStep 1803977 = 1352983) B1352983
theorem B3835649 : Blo 531801 3835649 := bstep (se 2 (by rfl) ⟨1438368, by rfl⟩ : syracuseStep 3835649 = 2876737) B2876737
theorem B2197547 : Blo 531801 2197547 := bstep (se 1 (by rfl) ⟨1648160, by rfl⟩ : syracuseStep 2197547 = 3296321) B3296321
theorem B1804679 : Blo 531801 1804679 := bstep (se 1 (by rfl) ⟨1353509, by rfl⟩ : syracuseStep 1804679 = 2707019) B2707019
theorem B3050045 : Blo 531801 3050045 := bstep (se 3 (by rfl) ⟨571883, by rfl⟩ : syracuseStep 3050045 = 1143767) B1143767
theorem B1805057 : Blo 531801 1805057 := bstep (se 2 (by rfl) ⟨676896, by rfl⟩ : syracuseStep 1805057 = 1353793) B1353793
theorem B11537315 : Blo 531801 11537315 := bstep (se 1 (by rfl) ⟨8652986, by rfl⟩ : syracuseStep 11537315 = 17305973) B17305973
theorem B855083 : Blo 531801 855083 := bstep (se 1 (by rfl) ⟨641312, by rfl⟩ : syracuseStep 855083 = 1282625) B1282625
theorem B12946493 : Blo 531801 12946493 := bstep (se 3 (by rfl) ⟨2427467, by rfl⟩ : syracuseStep 12946493 = 4854935) B4854935
theorem B6261877 : Blo 531801 6261877 := bstep (se 5 (by rfl) ⟨293525, by rfl⟩ : syracuseStep 6261877 = 587051) B587051
theorem B1346827 : Blo 531801 1346827 := bstep (se 1 (by rfl) ⟨1010120, by rfl⟩ : syracuseStep 1346827 = 2020241) B2020241
theorem B1281395 : Blo 531801 1281395 := bstep (se 1 (by rfl) ⟨961046, by rfl⟩ : syracuseStep 1281395 = 1922093) B1922093
theorem B1281415 : Blo 531801 1281415 := bstep (se 1 (by rfl) ⟨961061, by rfl⟩ : syracuseStep 1281415 = 1922123) B1922123
theorem B1346969 : Blo 531801 1346969 := bstep (se 2 (by rfl) ⟨505113, by rfl⟩ : syracuseStep 1346969 = 1010227) B1010227
theorem B1805867 : Blo 531801 1805867 := bstep (se 1 (by rfl) ⟨1354400, by rfl⟩ : syracuseStep 1805867 = 2708801) B2708801
theorem B1347131 : Blo 531801 1347131 := bstep (se 1 (by rfl) ⟨1010348, by rfl⟩ : syracuseStep 1347131 = 2020697) B2020697
theorem B9146033 : Blo 531801 9146033 := bstep (se 2 (by rfl) ⟨3429762, by rfl⟩ : syracuseStep 9146033 = 6859525) B6859525
theorem B1969921 : Blo 531801 1969921 := bstep (se 2 (by rfl) ⟨738720, by rfl⟩ : syracuseStep 1969921 = 1477441) B1477441
theorem B1347475 : Blo 531801 1347475 := bstep (se 1 (by rfl) ⟨1010606, by rfl⟩ : syracuseStep 1347475 = 2021213) B2021213
theorem B1347617 : Blo 531801 1347617 := bstep (se 2 (by rfl) ⟨505356, by rfl⟩ : syracuseStep 1347617 = 1010713) B1010713
theorem B1282163 : Blo 531801 1282163 := bstep (se 1 (by rfl) ⟨961622, by rfl⟩ : syracuseStep 1282163 = 1923245) B1923245
theorem B758263 : Blo 531801 758263 := bstep (se 1 (by rfl) ⟨568697, by rfl⟩ : syracuseStep 758263 = 1137395) B1137395
theorem B1807163 : Blo 531801 1807163 := bstep (se 1 (by rfl) ⟨1355372, by rfl⟩ : syracuseStep 1807163 = 2710745) B2710745
theorem B1348609 : Blo 531801 1348609 := bstep (se 2 (by rfl) ⟨505728, by rfl⟩ : syracuseStep 1348609 = 1011457) B1011457
theorem B1446923 : Blo 531801 1446923 := bstep (se 1 (by rfl) ⟨1085192, by rfl⟩ : syracuseStep 1446923 = 2170385) B2170385
theorem B1807649 : Blo 531801 1807649 := bstep (se 2 (by rfl) ⟨677868, by rfl⟩ : syracuseStep 1807649 = 1355737) B1355737
theorem B18519475 : Blo 531801 18519475 := bstep (se 1 (by rfl) ⟨13889606, by rfl⟩ : syracuseStep 18519475 = 27779213) B27779213
theorem B31167929 : Blo 531801 31167929 := bstep (se 2 (by rfl) ⟨11687973, by rfl⟩ : syracuseStep 31167929 = 23375947) B23375947
theorem B2561483 : Blo 531801 2561483 := bstep (se 1 (by rfl) ⟨1921112, by rfl⟩ : syracuseStep 2561483 = 3842225) B3842225
theorem B792137 : Blo 531801 792137 := bstep (se 2 (by rfl) ⟨297051, by rfl⟩ : syracuseStep 792137 = 594103) B594103
theorem B1349207 : Blo 531801 1349207 := bstep (se 1 (by rfl) ⟨1011905, by rfl⟩ : syracuseStep 1349207 = 2023811) B2023811
theorem B1349419 : Blo 531801 1349419 := bstep (se 1 (by rfl) ⟨1012064, by rfl⟩ : syracuseStep 1349419 = 2024129) B2024129
theorem B1808243 : Blo 531801 1808243 := bstep (se 1 (by rfl) ⟨1356182, by rfl⟩ : syracuseStep 1808243 = 2712365) B2712365
theorem B1349561 : Blo 531801 1349561 := bstep (se 2 (by rfl) ⟨506085, by rfl⟩ : syracuseStep 1349561 = 1012171) B1012171
theorem B5478347 : Blo 531801 5478347 := bstep (se 1 (by rfl) ⟨4108760, by rfl⟩ : syracuseStep 5478347 = 8217521) B8217521
theorem B1710679 : Blo 531801 1710679 := bstep (se 1 (by rfl) ⟨1283009, by rfl⟩ : syracuseStep 1710679 = 2566019) B2566019
theorem B1284875 : Blo 531801 1284875 := bstep (se 1 (by rfl) ⟨963656, by rfl⟩ : syracuseStep 1284875 = 1927313) B1927313
theorem B1284923 : Blo 531801 1284923 := bstep (se 1 (by rfl) ⟨963692, by rfl⟩ : syracuseStep 1284923 = 1927385) B1927385
theorem B3414899 : Blo 531801 3414899 := bstep (se 1 (by rfl) ⟨2561174, by rfl⟩ : syracuseStep 3414899 = 5122349) B5122349
theorem B1350553 : Blo 531801 1350553 := bstep (se 2 (by rfl) ⟨506457, by rfl⟩ : syracuseStep 1350553 = 1012915) B1012915
theorem B4332491 : Blo 531801 4332491 := bstep (se 1 (by rfl) ⟨3249368, by rfl⟩ : syracuseStep 4332491 = 6498737) B6498737
theorem B1711115 : Blo 531801 1711115 := bstep (se 1 (by rfl) ⟨1283336, by rfl⟩ : syracuseStep 1711115 = 2566673) B2566673
theorem B1350715 : Blo 531801 1350715 := bstep (se 1 (by rfl) ⟨1013036, by rfl⟩ : syracuseStep 1350715 = 2026073) B2026073
theorem B760951 : Blo 531801 760951 := bstep (se 1 (by rfl) ⟨570713, by rfl⟩ : syracuseStep 760951 = 1141427) B1141427
theorem B1350857 : Blo 531801 1350857 := bstep (se 2 (by rfl) ⟨506571, by rfl⟩ : syracuseStep 1350857 = 1013143) B1013143
theorem B2891009 : Blo 531801 2891009 := bstep (se 2 (by rfl) ⟨1084128, by rfl⟩ : syracuseStep 2891009 = 2168257) B2168257
theorem B10132867 : Blo 531801 10132867 := bstep (se 1 (by rfl) ⟨7599650, by rfl⟩ : syracuseStep 10132867 = 15199301) B15199301
theorem B531847 : Blo 531801 531847 := bstep (se 1 (by rfl) ⟨398885, by rfl⟩ : syracuseStep 531847 = 797771) B797771
theorem B3841415 : Blo 531801 3841415 := bstep (se 1 (by rfl) ⟨2881061, by rfl⟩ : syracuseStep 3841415 = 5762123) B5762123
theorem B6495623 : Blo 531801 6495623 := bstep (se 1 (by rfl) ⟨4871717, by rfl⟩ : syracuseStep 6495623 = 9743435) B9743435
theorem B531855 : Blo 531801 531855 := bstep (se 1 (by rfl) ⟨398891, by rfl⟩ : syracuseStep 531855 = 797783) B797783
theorem B2694545 : Blo 531801 2694545 := bstep (se 2 (by rfl) ⟨1010454, by rfl⟩ : syracuseStep 2694545 = 2020909) B2020909
theorem B3251609 : Blo 531801 3251609 := bstep (se 2 (by rfl) ⟨1219353, by rfl⟩ : syracuseStep 3251609 = 2438707) B2438707
theorem B531899 : Blo 531801 531899 := bstep (se 1 (by rfl) ⟨398924, by rfl⟩ : syracuseStep 531899 = 797849) B797849
theorem B1514953 : Blo 531801 1514953 := bstep (se 2 (by rfl) ⟨568107, by rfl⟩ : syracuseStep 1514953 = 1136215) B1136215
theorem B531975 : Blo 531801 531975 := bstep (se 1 (by rfl) ⟨398981, by rfl⟩ : syracuseStep 531975 = 797963) B797963
theorem B531983 : Blo 531801 531983 := bstep (se 1 (by rfl) ⟨398987, by rfl⟩ : syracuseStep 531983 = 797975) B797975
theorem B1351201 : Blo 531801 1351201 := bstep (se 2 (by rfl) ⟨506700, by rfl⟩ : syracuseStep 1351201 = 1013401) B1013401
theorem B532027 : Blo 531801 532027 := bstep (se 1 (by rfl) ⟨399020, by rfl⟩ : syracuseStep 532027 = 798041) B798041
theorem B532103 : Blo 531801 532103 := bstep (se 1 (by rfl) ⟨399077, by rfl⟩ : syracuseStep 532103 = 798155) B798155
theorem B532111 : Blo 531801 532111 := bstep (se 1 (by rfl) ⟨399083, by rfl⟩ : syracuseStep 532111 = 798167) B798167
theorem B532155 : Blo 531801 532155 := bstep (se 1 (by rfl) ⟨399116, by rfl⟩ : syracuseStep 532155 = 798233) B798233
theorem B532231 : Blo 531801 532231 := bstep (se 1 (by rfl) ⟨399173, by rfl⟩ : syracuseStep 532231 = 798347) B798347
theorem B532239 : Blo 531801 532239 := bstep (se 1 (by rfl) ⟨399179, by rfl⟩ : syracuseStep 532239 = 798359) B798359
theorem B1515307 : Blo 531801 1515307 := bstep (se 1 (by rfl) ⟨1136480, by rfl⟩ : syracuseStep 1515307 = 2272961) B2272961
theorem B34676525 : Blo 531801 34676525 := bstep (se 3 (by rfl) ⟨6501848, by rfl⟩ : syracuseStep 34676525 = 13003697) B13003697
theorem B1285931 : Blo 531801 1285931 := bstep (se 1 (by rfl) ⟨964448, by rfl⟩ : syracuseStep 1285931 = 1928897) B1928897
theorem B532283 : Blo 531801 532283 := bstep (se 1 (by rfl) ⟨399212, by rfl⟩ : syracuseStep 532283 = 798425) B798425
theorem B532359 : Blo 531801 532359 := bstep (se 1 (by rfl) ⟨399269, by rfl⟩ : syracuseStep 532359 = 798539) B798539
theorem B532367 : Blo 531801 532367 := bstep (se 1 (by rfl) ⟨399275, by rfl⟩ : syracuseStep 532367 = 798551) B798551
theorem B761771 : Blo 531801 761771 := bstep (se 1 (by rfl) ⟨571328, by rfl⟩ : syracuseStep 761771 = 1142657) B1142657
theorem B532411 : Blo 531801 532411 := bstep (se 1 (by rfl) ⟨399308, by rfl⟩ : syracuseStep 532411 = 798617) B798617
theorem B532487 : Blo 531801 532487 := bstep (se 1 (by rfl) ⟨399365, by rfl⟩ : syracuseStep 532487 = 798731) B798731
theorem B532495 : Blo 531801 532495 := bstep (se 1 (by rfl) ⟨399371, by rfl⟩ : syracuseStep 532495 = 798743) B798743
theorem B532539 : Blo 531801 532539 := bstep (se 1 (by rfl) ⟨399404, by rfl⟩ : syracuseStep 532539 = 798809) B798809
theorem B1515581 : Blo 531801 1515581 := bstep (se 3 (by rfl) ⟨284171, by rfl⟩ : syracuseStep 1515581 = 568343) B568343
theorem B1351799 : Blo 531801 1351799 := bstep (se 1 (by rfl) ⟨1013849, by rfl⟩ : syracuseStep 1351799 = 2027699) B2027699
theorem B532615 : Blo 531801 532615 := bstep (se 1 (by rfl) ⟨399461, by rfl⟩ : syracuseStep 532615 = 798923) B798923
theorem B532623 : Blo 531801 532623 := bstep (se 1 (by rfl) ⟨399467, by rfl⟩ : syracuseStep 532623 = 798935) B798935
theorem B532667 : Blo 531801 532667 := bstep (se 1 (by rfl) ⟨399500, by rfl⟩ : syracuseStep 532667 = 799001) B799001
theorem B598279 : Blo 531801 598279 := bstep (se 1 (by rfl) ⟨448709, by rfl⟩ : syracuseStep 598279 = 897419) B897419
theorem B532743 : Blo 531801 532743 := bstep (se 1 (by rfl) ⟨399557, by rfl⟩ : syracuseStep 532743 = 799115) B799115
theorem B532751 : Blo 531801 532751 := bstep (se 1 (by rfl) ⟨399563, by rfl⟩ : syracuseStep 532751 = 799127) B799127
theorem B532795 : Blo 531801 532795 := bstep (se 1 (by rfl) ⟨399596, by rfl⟩ : syracuseStep 532795 = 799193) B799193
theorem B1220923 : Blo 531801 1220923 := bstep (se 1 (by rfl) ⟨915692, by rfl⟩ : syracuseStep 1220923 = 1831385) B1831385
theorem B532871 : Blo 531801 532871 := bstep (se 1 (by rfl) ⟨399653, by rfl⟩ : syracuseStep 532871 = 799307) B799307
theorem B532879 : Blo 531801 532879 := bstep (se 1 (by rfl) ⟨399659, by rfl⟩ : syracuseStep 532879 = 799319) B799319
theorem B17375633 : Blo 531801 17375633 := bstep (se 2 (by rfl) ⟨6515862, by rfl⟩ : syracuseStep 17375633 = 13031725) B13031725
theorem B598459 : Blo 531801 598459 := bstep (se 1 (by rfl) ⟨448844, by rfl⟩ : syracuseStep 598459 = 897689) B897689
theorem B532923 : Blo 531801 532923 := bstep (se 1 (by rfl) ⟨399692, by rfl⟩ : syracuseStep 532923 = 799385) B799385
theorem B532999 : Blo 531801 532999 := bstep (se 1 (by rfl) ⟨399749, by rfl⟩ : syracuseStep 532999 = 799499) B799499
theorem B533007 : Blo 531801 533007 := bstep (se 1 (by rfl) ⟨399755, by rfl⟩ : syracuseStep 533007 = 799511) B799511
theorem B533051 : Blo 531801 533051 := bstep (se 1 (by rfl) ⟨399788, by rfl⟩ : syracuseStep 533051 = 799577) B799577
theorem B533127 : Blo 531801 533127 := bstep (se 1 (by rfl) ⟨399845, by rfl⟩ : syracuseStep 533127 = 799691) B799691
theorem B533135 : Blo 531801 533135 := bstep (se 1 (by rfl) ⟨399851, by rfl⟩ : syracuseStep 533135 = 799703) B799703
theorem B533179 : Blo 531801 533179 := bstep (se 1 (by rfl) ⟨399884, by rfl⟩ : syracuseStep 533179 = 799769) B799769
theorem B533255 : Blo 531801 533255 := bstep (se 1 (by rfl) ⟨399941, by rfl⟩ : syracuseStep 533255 = 799883) B799883
theorem B533263 : Blo 531801 533263 := bstep (se 1 (by rfl) ⟨399947, by rfl⟩ : syracuseStep 533263 = 799895) B799895
theorem B533307 : Blo 531801 533307 := bstep (se 1 (by rfl) ⟨399980, by rfl⟩ : syracuseStep 533307 = 799961) B799961
theorem B1286999 : Blo 531801 1286999 := bstep (se 1 (by rfl) ⟨965249, by rfl⟩ : syracuseStep 1286999 = 1930499) B1930499
theorem B533383 : Blo 531801 533383 := bstep (se 1 (by rfl) ⟨400037, by rfl⟩ : syracuseStep 533383 = 800075) B800075
theorem B598927 : Blo 531801 598927 := bstep (se 1 (by rfl) ⟨449195, by rfl⟩ : syracuseStep 598927 = 898391) B898391
theorem B533391 : Blo 531801 533391 := bstep (se 1 (by rfl) ⟨400043, by rfl⟩ : syracuseStep 533391 = 800087) B800087
theorem B533435 : Blo 531801 533435 := bstep (se 1 (by rfl) ⟨400076, by rfl⟩ : syracuseStep 533435 = 800153) B800153
theorem B533511 : Blo 531801 533511 := bstep (se 1 (by rfl) ⟨400133, by rfl⟩ : syracuseStep 533511 = 800267) B800267
theorem B533519 : Blo 531801 533519 := bstep (se 1 (by rfl) ⟨400139, by rfl⟩ : syracuseStep 533519 = 800279) B800279
theorem B533563 : Blo 531801 533563 := bstep (se 1 (by rfl) ⟨400172, by rfl⟩ : syracuseStep 533563 = 800345) B800345
theorem B533639 : Blo 531801 533639 := bstep (se 1 (by rfl) ⟨400229, by rfl⟩ : syracuseStep 533639 = 800459) B800459
theorem B533647 : Blo 531801 533647 := bstep (se 1 (by rfl) ⟨400235, by rfl⟩ : syracuseStep 533647 = 800471) B800471
theorem B533691 : Blo 531801 533691 := bstep (se 1 (by rfl) ⟨400268, by rfl⟩ : syracuseStep 533691 = 800537) B800537
theorem B533767 : Blo 531801 533767 := bstep (se 1 (by rfl) ⟨400325, by rfl⟩ : syracuseStep 533767 = 800651) B800651
theorem B533775 : Blo 531801 533775 := bstep (se 1 (by rfl) ⟨400331, by rfl⟩ : syracuseStep 533775 = 800663) B800663
theorem B533819 : Blo 531801 533819 := bstep (se 1 (by rfl) ⟨400364, by rfl⟩ : syracuseStep 533819 = 800729) B800729
theorem B2893171 : Blo 531801 2893171 := bstep (se 1 (by rfl) ⟨2169878, by rfl⟩ : syracuseStep 2893171 = 4339757) B4339757
theorem B599431 : Blo 531801 599431 := bstep (se 1 (by rfl) ⟨449573, by rfl⟩ : syracuseStep 599431 = 899147) B899147
theorem B533895 : Blo 531801 533895 := bstep (se 1 (by rfl) ⟨400421, by rfl⟩ : syracuseStep 533895 = 800843) B800843
theorem B1353095 : Blo 531801 1353095 := bstep (se 1 (by rfl) ⟨1014821, by rfl⟩ : syracuseStep 1353095 = 2029643) B2029643
theorem B533903 : Blo 531801 533903 := bstep (se 1 (by rfl) ⟨400427, by rfl⟩ : syracuseStep 533903 = 800855) B800855
theorem B1353145 : Blo 531801 1353145 := bstep (se 2 (by rfl) ⟨507429, by rfl⟩ : syracuseStep 1353145 = 1014859) B1014859
theorem B533947 : Blo 531801 533947 := bstep (se 1 (by rfl) ⟨400460, by rfl⟩ : syracuseStep 533947 = 800921) B800921
theorem B2696651 : Blo 531801 2696651 := bstep (se 1 (by rfl) ⟨2022488, by rfl⟩ : syracuseStep 2696651 = 4044977) B4044977
theorem B534023 : Blo 531801 534023 := bstep (se 1 (by rfl) ⟨400517, by rfl⟩ : syracuseStep 534023 = 801035) B801035
theorem B534031 : Blo 531801 534031 := bstep (se 1 (by rfl) ⟨400523, by rfl⟩ : syracuseStep 534031 = 801047) B801047
theorem B960059 : Blo 531801 960059 := bstep (se 1 (by rfl) ⟨720044, by rfl⟩ : syracuseStep 960059 = 1440089) B1440089
theorem B599611 : Blo 531801 599611 := bstep (se 1 (by rfl) ⟨449708, by rfl⟩ : syracuseStep 599611 = 899417) B899417
theorem B534075 : Blo 531801 534075 := bstep (se 1 (by rfl) ⟨400556, by rfl⟩ : syracuseStep 534075 = 801113) B801113
theorem B534151 : Blo 531801 534151 := bstep (se 1 (by rfl) ⟨400613, by rfl⟩ : syracuseStep 534151 = 801227) B801227
theorem B534159 : Blo 531801 534159 := bstep (se 1 (by rfl) ⟨400619, by rfl⟩ : syracuseStep 534159 = 801239) B801239
theorem B534203 : Blo 531801 534203 := bstep (se 1 (by rfl) ⟨400652, by rfl⟩ : syracuseStep 534203 = 801305) B801305
theorem B534279 : Blo 531801 534279 := bstep (se 1 (by rfl) ⟨400709, by rfl⟩ : syracuseStep 534279 = 801419) B801419
theorem B2696975 : Blo 531801 2696975 := bstep (se 1 (by rfl) ⟨2022731, by rfl⟩ : syracuseStep 2696975 = 4045463) B4045463
theorem B3417871 : Blo 531801 3417871 := bstep (se 1 (by rfl) ⟨2563403, by rfl⟩ : syracuseStep 3417871 = 5126807) B5126807
theorem B534287 : Blo 531801 534287 := bstep (se 1 (by rfl) ⟨400715, by rfl⟩ : syracuseStep 534287 = 801431) B801431
theorem B534331 : Blo 531801 534331 := bstep (se 1 (by rfl) ⟨400748, by rfl⟩ : syracuseStep 534331 = 801497) B801497
theorem B927607 : Blo 531801 927607 := bstep (se 1 (by rfl) ⟨695705, by rfl⟩ : syracuseStep 927607 = 1391411) B1391411
theorem B534407 : Blo 531801 534407 := bstep (se 1 (by rfl) ⟨400805, by rfl⟩ : syracuseStep 534407 = 801611) B801611
theorem B534415 : Blo 531801 534415 := bstep (se 1 (by rfl) ⟨400811, by rfl⟩ : syracuseStep 534415 = 801623) B801623
theorem B534459 : Blo 531801 534459 := bstep (se 1 (by rfl) ⟨400844, by rfl⟩ : syracuseStep 534459 = 801689) B801689
theorem B534535 : Blo 531801 534535 := bstep (se 1 (by rfl) ⟨400901, by rfl⟩ : syracuseStep 534535 = 801803) B801803
theorem B600079 : Blo 531801 600079 := bstep (se 1 (by rfl) ⟨450059, by rfl⟩ : syracuseStep 600079 = 900119) B900119
theorem B534543 : Blo 531801 534543 := bstep (se 1 (by rfl) ⟨400907, by rfl⟩ : syracuseStep 534543 = 801815) B801815
theorem B1353743 : Blo 531801 1353743 := bstep (se 1 (by rfl) ⟨1015307, by rfl⟩ : syracuseStep 1353743 = 2030615) B2030615
theorem B9119789 : Blo 531801 9119789 := bstep (se 3 (by rfl) ⟨1709960, by rfl⟩ : syracuseStep 9119789 = 3419921) B3419921
theorem B534587 : Blo 531801 534587 := bstep (se 1 (by rfl) ⟨400940, by rfl⟩ : syracuseStep 534587 = 801881) B801881
theorem B1517687 : Blo 531801 1517687 := bstep (se 1 (by rfl) ⟨1138265, by rfl⟩ : syracuseStep 1517687 = 2276531) B2276531
theorem B534663 : Blo 531801 534663 := bstep (se 1 (by rfl) ⟨400997, by rfl⟩ : syracuseStep 534663 = 801995) B801995
theorem B534671 : Blo 531801 534671 := bstep (se 1 (by rfl) ⟨401003, by rfl⟩ : syracuseStep 534671 = 802007) B802007
theorem B534715 : Blo 531801 534715 := bstep (se 1 (by rfl) ⟨401036, by rfl⟩ : syracuseStep 534715 = 802073) B802073
theorem B534791 : Blo 531801 534791 := bstep (se 1 (by rfl) ⟨401093, by rfl⟩ : syracuseStep 534791 = 802187) B802187
theorem B534799 : Blo 531801 534799 := bstep (se 1 (by rfl) ⟨401099, by rfl⟩ : syracuseStep 534799 = 802199) B802199
theorem B1157419 : Blo 531801 1157419 := bstep (se 1 (by rfl) ⟨868064, by rfl⟩ : syracuseStep 1157419 = 1736129) B1736129
theorem B534843 : Blo 531801 534843 := bstep (se 1 (by rfl) ⟨401132, by rfl⟩ : syracuseStep 534843 = 802265) B802265
theorem B534919 : Blo 531801 534919 := bstep (se 1 (by rfl) ⟨401189, by rfl⟩ : syracuseStep 534919 = 802379) B802379
theorem B534927 : Blo 531801 534927 := bstep (se 1 (by rfl) ⟨401195, by rfl⟩ : syracuseStep 534927 = 802391) B802391
theorem B534971 : Blo 531801 534971 := bstep (se 1 (by rfl) ⟨401228, by rfl⟩ : syracuseStep 534971 = 802457) B802457
theorem B600583 : Blo 531801 600583 := bstep (se 1 (by rfl) ⟨450437, by rfl⟩ : syracuseStep 600583 = 900875) B900875
theorem B535047 : Blo 531801 535047 := bstep (se 1 (by rfl) ⟨401285, by rfl⟩ : syracuseStep 535047 = 802571) B802571
theorem B535055 : Blo 531801 535055 := bstep (se 1 (by rfl) ⟨401291, by rfl⟩ : syracuseStep 535055 = 802583) B802583
theorem B535099 : Blo 531801 535099 := bstep (se 1 (by rfl) ⟨401324, by rfl⟩ : syracuseStep 535099 = 802649) B802649
theorem B535175 : Blo 531801 535175 := bstep (se 1 (by rfl) ⟨401381, by rfl⟩ : syracuseStep 535175 = 802763) B802763
theorem B535183 : Blo 531801 535183 := bstep (se 1 (by rfl) ⟨401387, by rfl⟩ : syracuseStep 535183 = 802775) B802775
theorem B600763 : Blo 531801 600763 := bstep (se 1 (by rfl) ⟨450572, by rfl⟩ : syracuseStep 600763 = 901145) B901145
theorem B535227 : Blo 531801 535227 := bstep (se 1 (by rfl) ⟨401420, by rfl⟩ : syracuseStep 535227 = 802841) B802841
theorem B1354441 : Blo 531801 1354441 := bstep (se 2 (by rfl) ⟨507915, by rfl⟩ : syracuseStep 1354441 = 1015831) B1015831
theorem B535303 : Blo 531801 535303 := bstep (se 1 (by rfl) ⟨401477, by rfl⟩ : syracuseStep 535303 = 802955) B802955
theorem B535311 : Blo 531801 535311 := bstep (se 1 (by rfl) ⟨401483, by rfl⟩ : syracuseStep 535311 = 802967) B802967
theorem B535355 : Blo 531801 535355 := bstep (se 1 (by rfl) ⟨401516, by rfl⟩ : syracuseStep 535355 = 803033) B803033
theorem B1354583 : Blo 531801 1354583 := bstep (se 1 (by rfl) ⟨1015937, by rfl⟩ : syracuseStep 1354583 = 2031875) B2031875
theorem B535431 : Blo 531801 535431 := bstep (se 1 (by rfl) ⟨401573, by rfl⟩ : syracuseStep 535431 = 803147) B803147
theorem B535439 : Blo 531801 535439 := bstep (se 1 (by rfl) ⟨401579, by rfl⟩ : syracuseStep 535439 = 803159) B803159
theorem B2894777 : Blo 531801 2894777 := bstep (se 2 (by rfl) ⟨1085541, by rfl⟩ : syracuseStep 2894777 = 2171083) B2171083
theorem B3091385 : Blo 531801 3091385 := bstep (se 2 (by rfl) ⟨1159269, by rfl⟩ : syracuseStep 3091385 = 2318539) B2318539
theorem B535483 : Blo 531801 535483 := bstep (se 1 (by rfl) ⟨401612, by rfl⟩ : syracuseStep 535483 = 803225) B803225
theorem B535559 : Blo 531801 535559 := bstep (se 1 (by rfl) ⟨401669, by rfl⟩ : syracuseStep 535559 = 803339) B803339
theorem B797711 : Blo 531801 797711 := bstep (se 1 (by rfl) ⟨598283, by rfl⟩ : syracuseStep 797711 = 1196567) B1196567
theorem B535567 : Blo 531801 535567 := bstep (se 1 (by rfl) ⟨401675, by rfl⟩ : syracuseStep 535567 = 803351) B803351
theorem B797753 : Blo 531801 797753 := bstep (se 2 (by rfl) ⟨299157, by rfl⟩ : syracuseStep 797753 = 598315) B598315
theorem B535611 : Blo 531801 535611 := bstep (se 1 (by rfl) ⟨401708, by rfl⟩ : syracuseStep 535611 = 803417) B803417
theorem B797831 : Blo 531801 797831 := bstep (se 1 (by rfl) ⟨598373, by rfl⟩ : syracuseStep 797831 = 1196747) B1196747
theorem B535687 : Blo 531801 535687 := bstep (se 1 (by rfl) ⟨401765, by rfl⟩ : syracuseStep 535687 = 803531) B803531
theorem B601231 : Blo 531801 601231 := bstep (se 1 (by rfl) ⟨450923, by rfl⟩ : syracuseStep 601231 = 901847) B901847
theorem B535695 : Blo 531801 535695 := bstep (se 1 (by rfl) ⟨401771, by rfl⟩ : syracuseStep 535695 = 803543) B803543
theorem B797867 : Blo 531801 797867 := bstep (se 1 (by rfl) ⟨598400, by rfl⟩ : syracuseStep 797867 = 1196801) B1196801
theorem B535739 : Blo 531801 535739 := bstep (se 1 (by rfl) ⟨401804, by rfl⟩ : syracuseStep 535739 = 803609) B803609
theorem B2698433 : Blo 531801 2698433 := bstep (se 2 (by rfl) ⟨1011912, by rfl⟩ : syracuseStep 2698433 = 2023825) B2023825
theorem B797897 : Blo 531801 797897 := bstep (se 2 (by rfl) ⟨299211, by rfl⟩ : syracuseStep 797897 = 598423) B598423
theorem B798011 : Blo 531801 798011 := bstep (se 1 (by rfl) ⟨598508, by rfl⟩ : syracuseStep 798011 = 1197017) B1197017
theorem B798071 : Blo 531801 798071 := bstep (se 1 (by rfl) ⟨598553, by rfl⟩ : syracuseStep 798071 = 1197107) B1197107
theorem B798095 : Blo 531801 798095 := bstep (se 1 (by rfl) ⟨598571, by rfl⟩ : syracuseStep 798095 = 1197143) B1197143
theorem B798137 : Blo 531801 798137 := bstep (se 2 (by rfl) ⟨299301, by rfl⟩ : syracuseStep 798137 = 598603) B598603
theorem B14757329 : Blo 531801 14757329 := bstep (se 2 (by rfl) ⟨5533998, by rfl⟩ : syracuseStep 14757329 = 11067997) B11067997
theorem B798215 : Blo 531801 798215 := bstep (se 1 (by rfl) ⟨598661, by rfl⟩ : syracuseStep 798215 = 1197323) B1197323
theorem B798251 : Blo 531801 798251 := bstep (se 1 (by rfl) ⟨598688, by rfl⟩ : syracuseStep 798251 = 1197377) B1197377
theorem B2895421 : Blo 531801 2895421 := bstep (se 3 (by rfl) ⟨542891, by rfl⟩ : syracuseStep 2895421 = 1085783) B1085783
theorem B798281 : Blo 531801 798281 := bstep (se 2 (by rfl) ⟨299355, by rfl⟩ : syracuseStep 798281 = 598711) B598711
theorem B2305655 : Blo 531801 2305655 := bstep (se 1 (by rfl) ⟨1729241, by rfl⟩ : syracuseStep 2305655 = 3458483) B3458483
theorem B601735 : Blo 531801 601735 := bstep (se 1 (by rfl) ⟨451301, by rfl⟩ : syracuseStep 601735 = 902603) B902603
theorem B798395 : Blo 531801 798395 := bstep (se 1 (by rfl) ⟨598796, by rfl⟩ : syracuseStep 798395 = 1197593) B1197593
theorem B798455 : Blo 531801 798455 := bstep (se 1 (by rfl) ⟨598841, by rfl⟩ : syracuseStep 798455 = 1197683) B1197683
theorem B798479 : Blo 531801 798479 := bstep (se 1 (by rfl) ⟨598859, by rfl⟩ : syracuseStep 798479 = 1197719) B1197719
theorem B4042547 : Blo 531801 4042547 := bstep (se 1 (by rfl) ⟨3031910, by rfl⟩ : syracuseStep 4042547 = 6063821) B6063821
theorem B798521 : Blo 531801 798521 := bstep (se 2 (by rfl) ⟨299445, by rfl⟩ : syracuseStep 798521 = 598891) B598891
theorem B601915 : Blo 531801 601915 := bstep (se 1 (by rfl) ⟨451436, by rfl⟩ : syracuseStep 601915 = 902873) B902873
theorem B798599 : Blo 531801 798599 := bstep (se 1 (by rfl) ⟨598949, by rfl⟩ : syracuseStep 798599 = 1197899) B1197899
theorem B798635 : Blo 531801 798635 := bstep (se 1 (by rfl) ⟨598976, by rfl⟩ : syracuseStep 798635 = 1197953) B1197953
theorem B798665 : Blo 531801 798665 := bstep (se 2 (by rfl) ⟨299499, by rfl⟩ : syracuseStep 798665 = 598999) B598999
theorem B10399691 : Blo 531801 10399691 := bstep (se 1 (by rfl) ⟨7799768, by rfl⟩ : syracuseStep 10399691 = 15599537) B15599537
theorem B798779 : Blo 531801 798779 := bstep (se 1 (by rfl) ⟨599084, by rfl⟩ : syracuseStep 798779 = 1198169) B1198169
theorem B798839 : Blo 531801 798839 := bstep (se 1 (by rfl) ⟨599129, by rfl⟩ : syracuseStep 798839 = 1198259) B1198259
theorem B4108421 : Blo 531801 4108421 := bstep (se 4 (by rfl) ⟨385164, by rfl⟩ : syracuseStep 4108421 = 770329) B770329
theorem B798863 : Blo 531801 798863 := bstep (se 1 (by rfl) ⟨599147, by rfl⟩ : syracuseStep 798863 = 1198295) B1198295
theorem B1618067 : Blo 531801 1618067 := bstep (se 1 (by rfl) ⟨1213550, by rfl⟩ : syracuseStep 1618067 = 2427101) B2427101
theorem B798905 : Blo 531801 798905 := bstep (se 2 (by rfl) ⟨299589, by rfl⟩ : syracuseStep 798905 = 599179) B599179
theorem B798983 : Blo 531801 798983 := bstep (se 1 (by rfl) ⟨599237, by rfl⟩ : syracuseStep 798983 = 1198475) B1198475
theorem B602383 : Blo 531801 602383 := bstep (se 1 (by rfl) ⟨451787, by rfl⟩ : syracuseStep 602383 = 903575) B903575
theorem B799019 : Blo 531801 799019 := bstep (se 1 (by rfl) ⟨599264, by rfl⟩ : syracuseStep 799019 = 1198529) B1198529
theorem B799049 : Blo 531801 799049 := bstep (se 2 (by rfl) ⟨299643, by rfl⟩ : syracuseStep 799049 = 599287) B599287
theorem B799163 : Blo 531801 799163 := bstep (se 1 (by rfl) ⟨599372, by rfl⟩ : syracuseStep 799163 = 1198745) B1198745
theorem B2699729 : Blo 531801 2699729 := bstep (se 2 (by rfl) ⟨1012398, by rfl⟩ : syracuseStep 2699729 = 2024797) B2024797
theorem B799223 : Blo 531801 799223 := bstep (se 1 (by rfl) ⟨599417, by rfl⟩ : syracuseStep 799223 = 1198835) B1198835
theorem B799247 : Blo 531801 799247 := bstep (se 1 (by rfl) ⟨599435, by rfl⟩ : syracuseStep 799247 = 1198871) B1198871
theorem B1520171 : Blo 531801 1520171 := bstep (se 1 (by rfl) ⟨1140128, by rfl⟩ : syracuseStep 1520171 = 2280257) B2280257
theorem B799289 : Blo 531801 799289 := bstep (se 2 (by rfl) ⟨299733, by rfl⟩ : syracuseStep 799289 = 599467) B599467
theorem B6566467 : Blo 531801 6566467 := bstep (se 1 (by rfl) ⟨4924850, by rfl⟩ : syracuseStep 6566467 = 9849701) B9849701
theorem B897655 : Blo 531801 897655 := bstep (se 1 (by rfl) ⟨673241, by rfl⟩ : syracuseStep 897655 = 1346483) B1346483
theorem B799367 : Blo 531801 799367 := bstep (se 1 (by rfl) ⟨599525, by rfl⟩ : syracuseStep 799367 = 1199051) B1199051
theorem B799403 : Blo 531801 799403 := bstep (se 1 (by rfl) ⟨599552, by rfl⟩ : syracuseStep 799403 = 1199105) B1199105
theorem B799433 : Blo 531801 799433 := bstep (se 2 (by rfl) ⟨299787, by rfl⟩ : syracuseStep 799433 = 599575) B599575
theorem B2568941 : Blo 531801 2568941 := bstep (se 3 (by rfl) ⟨481676, by rfl⟩ : syracuseStep 2568941 = 963353) B963353
theorem B4567823 : Blo 531801 4567823 := bstep (se 1 (by rfl) ⟨3425867, by rfl⟩ : syracuseStep 4567823 = 6851735) B6851735
theorem B897851 : Blo 531801 897851 := bstep (se 1 (by rfl) ⟨673388, by rfl⟩ : syracuseStep 897851 = 1346777) B1346777
theorem B799547 : Blo 531801 799547 := bstep (se 1 (by rfl) ⟨599660, by rfl⟩ : syracuseStep 799547 = 1199321) B1199321
theorem B799607 : Blo 531801 799607 := bstep (se 1 (by rfl) ⟨599705, by rfl⟩ : syracuseStep 799607 = 1199411) B1199411
theorem B799631 : Blo 531801 799631 := bstep (se 1 (by rfl) ⟨599723, by rfl⟩ : syracuseStep 799631 = 1199447) B1199447
theorem B799673 : Blo 531801 799673 := bstep (se 2 (by rfl) ⟨299877, by rfl⟩ : syracuseStep 799673 = 599755) B599755
theorem B3650507 : Blo 531801 3650507 := bstep (se 1 (by rfl) ⟨2737880, by rfl⟩ : syracuseStep 3650507 = 5475761) B5475761
theorem B799751 : Blo 531801 799751 := bstep (se 1 (by rfl) ⟨599813, by rfl⟩ : syracuseStep 799751 = 1199627) B1199627
theorem B3814411 : Blo 531801 3814411 := bstep (se 1 (by rfl) ⟨2860808, by rfl⟩ : syracuseStep 3814411 = 5721617) B5721617
theorem B799787 : Blo 531801 799787 := bstep (se 1 (by rfl) ⟨599840, by rfl⟩ : syracuseStep 799787 = 1199681) B1199681
theorem B799817 : Blo 531801 799817 := bstep (se 2 (by rfl) ⟨299931, by rfl⟩ : syracuseStep 799817 = 599863) B599863
theorem B799931 : Blo 531801 799931 := bstep (se 1 (by rfl) ⟨599948, by rfl⟩ : syracuseStep 799931 = 1199897) B1199897
theorem B898249 : Blo 531801 898249 := bstep (se 2 (by rfl) ⟨336843, by rfl⟩ : syracuseStep 898249 = 673687) B673687
theorem B799991 : Blo 531801 799991 := bstep (se 1 (by rfl) ⟨599993, by rfl⟩ : syracuseStep 799991 = 1199987) B1199987
theorem B800015 : Blo 531801 800015 := bstep (se 1 (by rfl) ⟨600011, by rfl⟩ : syracuseStep 800015 = 1200023) B1200023
theorem B800057 : Blo 531801 800057 := bstep (se 2 (by rfl) ⟨300021, by rfl⟩ : syracuseStep 800057 = 600043) B600043
theorem B1520957 : Blo 531801 1520957 := bstep (se 3 (by rfl) ⟨285179, by rfl⟩ : syracuseStep 1520957 = 570359) B570359
theorem B800135 : Blo 531801 800135 := bstep (se 1 (by rfl) ⟨600101, by rfl⟩ : syracuseStep 800135 = 1200203) B1200203
theorem B4634003 : Blo 531801 4634003 := bstep (se 1 (by rfl) ⟨3475502, by rfl⟩ : syracuseStep 4634003 = 6951005) B6951005
theorem B800171 : Blo 531801 800171 := bstep (se 1 (by rfl) ⟨600128, by rfl⟩ : syracuseStep 800171 = 1200257) B1200257
theorem B800201 : Blo 531801 800201 := bstep (se 2 (by rfl) ⟨300075, by rfl⟩ : syracuseStep 800201 = 600151) B600151
theorem B4109777 : Blo 531801 4109777 := bstep (se 2 (by rfl) ⟨1541166, by rfl⟩ : syracuseStep 4109777 = 3082333) B3082333
theorem B800315 : Blo 531801 800315 := bstep (se 1 (by rfl) ⟨600236, by rfl⟩ : syracuseStep 800315 = 1200473) B1200473
theorem B800375 : Blo 531801 800375 := bstep (se 1 (by rfl) ⟨600281, by rfl⟩ : syracuseStep 800375 = 1200563) B1200563
theorem B1521287 : Blo 531801 1521287 := bstep (se 1 (by rfl) ⟨1140965, by rfl⟩ : syracuseStep 1521287 = 2281931) B2281931
theorem B800399 : Blo 531801 800399 := bstep (se 1 (by rfl) ⟨600299, by rfl⟩ : syracuseStep 800399 = 1200599) B1200599
theorem B800441 : Blo 531801 800441 := bstep (se 2 (by rfl) ⟨300165, by rfl⟩ : syracuseStep 800441 = 600331) B600331
theorem B800519 : Blo 531801 800519 := bstep (se 1 (by rfl) ⟨600389, by rfl⟩ : syracuseStep 800519 = 1200779) B1200779
theorem B800555 : Blo 531801 800555 := bstep (se 1 (by rfl) ⟨600416, by rfl⟩ : syracuseStep 800555 = 1200833) B1200833
theorem B12367667 : Blo 531801 12367667 := bstep (se 1 (by rfl) ⟨9275750, by rfl⟩ : syracuseStep 12367667 = 18551501) B18551501
theorem B800585 : Blo 531801 800585 := bstep (se 2 (by rfl) ⟨300219, by rfl⟩ : syracuseStep 800585 = 600439) B600439
theorem B5125963 : Blo 531801 5125963 := bstep (se 1 (by rfl) ⟨3844472, by rfl⟩ : syracuseStep 5125963 = 7688945) B7688945
theorem B898951 : Blo 531801 898951 := bstep (se 1 (by rfl) ⟨674213, by rfl⟩ : syracuseStep 898951 = 1348427) B1348427
theorem B800699 : Blo 531801 800699 := bstep (se 1 (by rfl) ⟨600524, by rfl⟩ : syracuseStep 800699 = 1201049) B1201049
theorem B800759 : Blo 531801 800759 := bstep (se 1 (by rfl) ⟨600569, by rfl⟩ : syracuseStep 800759 = 1201139) B1201139
theorem B800783 : Blo 531801 800783 := bstep (se 1 (by rfl) ⟨600587, by rfl⟩ : syracuseStep 800783 = 1201175) B1201175
theorem B800825 : Blo 531801 800825 := bstep (se 2 (by rfl) ⟨300309, by rfl⟩ : syracuseStep 800825 = 600619) B600619
theorem B800903 : Blo 531801 800903 := bstep (se 1 (by rfl) ⟨600677, by rfl⟩ : syracuseStep 800903 = 1201355) B1201355
theorem B800939 : Blo 531801 800939 := bstep (se 1 (by rfl) ⟨600704, by rfl⟩ : syracuseStep 800939 = 1201409) B1201409
theorem B800969 : Blo 531801 800969 := bstep (se 2 (by rfl) ⟨300363, by rfl⟩ : syracuseStep 800969 = 600727) B600727
theorem B3258569 : Blo 531801 3258569 := bstep (se 2 (by rfl) ⟨1221963, by rfl⟩ : syracuseStep 3258569 = 2443927) B2443927
theorem B801083 : Blo 531801 801083 := bstep (se 1 (by rfl) ⟨600812, by rfl⟩ : syracuseStep 801083 = 1201625) B1201625
theorem B801143 : Blo 531801 801143 := bstep (se 1 (by rfl) ⟨600857, by rfl⟩ : syracuseStep 801143 = 1201715) B1201715
theorem B801167 : Blo 531801 801167 := bstep (se 1 (by rfl) ⟨600875, by rfl⟩ : syracuseStep 801167 = 1201751) B1201751
theorem B801209 : Blo 531801 801209 := bstep (se 2 (by rfl) ⟨300453, by rfl⟩ : syracuseStep 801209 = 600907) B600907
theorem B801287 : Blo 531801 801287 := bstep (se 1 (by rfl) ⟨600965, by rfl⟩ : syracuseStep 801287 = 1201931) B1201931
theorem B2701835 : Blo 531801 2701835 := bstep (se 1 (by rfl) ⟨2026376, by rfl⟩ : syracuseStep 2701835 = 4052753) B4052753
theorem B899599 : Blo 531801 899599 := bstep (se 1 (by rfl) ⟨674699, by rfl⟩ : syracuseStep 899599 = 1349399) B1349399
theorem B2275883 : Blo 531801 2275883 := bstep (se 1 (by rfl) ⟨1706912, by rfl⟩ : syracuseStep 2275883 = 3413825) B3413825
theorem B801323 : Blo 531801 801323 := bstep (se 1 (by rfl) ⟨600992, by rfl⟩ : syracuseStep 801323 = 1201985) B1201985
theorem B801353 : Blo 531801 801353 := bstep (se 2 (by rfl) ⟨300507, by rfl⟩ : syracuseStep 801353 = 601015) B601015
theorem B2701997 : Blo 531801 2701997 := bstep (se 3 (by rfl) ⟨506624, by rfl⟩ : syracuseStep 2701997 = 1013249) B1013249
theorem B801467 : Blo 531801 801467 := bstep (se 1 (by rfl) ⟨601100, by rfl⟩ : syracuseStep 801467 = 1202201) B1202201
theorem B801527 : Blo 531801 801527 := bstep (se 1 (by rfl) ⟨601145, by rfl⟩ : syracuseStep 801527 = 1202291) B1202291
theorem B801551 : Blo 531801 801551 := bstep (se 1 (by rfl) ⟨601163, by rfl⟩ : syracuseStep 801551 = 1202327) B1202327
theorem B801593 : Blo 531801 801593 := bstep (se 2 (by rfl) ⟨300597, by rfl⟩ : syracuseStep 801593 = 601195) B601195
theorem B801671 : Blo 531801 801671 := bstep (se 1 (by rfl) ⟨601253, by rfl⟩ : syracuseStep 801671 = 1202507) B1202507
theorem B801707 : Blo 531801 801707 := bstep (se 1 (by rfl) ⟨601280, by rfl⟩ : syracuseStep 801707 = 1202561) B1202561
theorem B801737 : Blo 531801 801737 := bstep (se 2 (by rfl) ⟨300651, by rfl⟩ : syracuseStep 801737 = 601303) B601303
theorem B900139 : Blo 531801 900139 := bstep (se 1 (by rfl) ⟨675104, by rfl⟩ : syracuseStep 900139 = 1350209) B1350209
theorem B801851 : Blo 531801 801851 := bstep (se 1 (by rfl) ⟨601388, by rfl⟩ : syracuseStep 801851 = 1202777) B1202777
theorem B801911 : Blo 531801 801911 := bstep (se 1 (by rfl) ⟨601433, by rfl⟩ : syracuseStep 801911 = 1202867) B1202867
theorem B801935 : Blo 531801 801935 := bstep (se 1 (by rfl) ⟨601451, by rfl⟩ : syracuseStep 801935 = 1202903) B1202903
theorem B900281 : Blo 531801 900281 := bstep (se 2 (by rfl) ⟨337605, by rfl⟩ : syracuseStep 900281 = 675211) B675211
theorem B801977 : Blo 531801 801977 := bstep (se 2 (by rfl) ⟨300741, by rfl⟩ : syracuseStep 801977 = 601483) B601483
theorem B802055 : Blo 531801 802055 := bstep (se 1 (by rfl) ⟨601541, by rfl⟩ : syracuseStep 802055 = 1203083) B1203083
theorem B802091 : Blo 531801 802091 := bstep (se 1 (by rfl) ⟨601568, by rfl⟩ : syracuseStep 802091 = 1203137) B1203137
theorem B8207675 : Blo 531801 8207675 := bstep (se 1 (by rfl) ⟨6155756, by rfl⟩ : syracuseStep 8207675 = 12311513) B12311513
theorem B802121 : Blo 531801 802121 := bstep (se 2 (by rfl) ⟨300795, by rfl⟩ : syracuseStep 802121 = 601591) B601591
theorem B1523063 : Blo 531801 1523063 := bstep (se 1 (by rfl) ⟨1142297, by rfl⟩ : syracuseStep 1523063 = 2284595) B2284595
theorem B802235 : Blo 531801 802235 := bstep (se 1 (by rfl) ⟨601676, by rfl⟩ : syracuseStep 802235 = 1203353) B1203353
theorem B802295 : Blo 531801 802295 := bstep (se 1 (by rfl) ⟨601721, by rfl⟩ : syracuseStep 802295 = 1203443) B1203443
theorem B540167 : Blo 531801 540167 := bstep (se 1 (by rfl) ⟨405125, by rfl⟩ : syracuseStep 540167 = 810251) B810251
theorem B802319 : Blo 531801 802319 := bstep (se 1 (by rfl) ⟨601739, by rfl⟩ : syracuseStep 802319 = 1203479) B1203479
theorem B802361 : Blo 531801 802361 := bstep (se 2 (by rfl) ⟨300885, by rfl⟩ : syracuseStep 802361 = 601771) B601771
theorem B802439 : Blo 531801 802439 := bstep (se 1 (by rfl) ⟨601829, by rfl⟩ : syracuseStep 802439 = 1203659) B1203659
theorem B1621657 : Blo 531801 1621657 := bstep (se 2 (by rfl) ⟨608121, by rfl⟩ : syracuseStep 1621657 = 1216243) B1216243
theorem B802475 : Blo 531801 802475 := bstep (se 1 (by rfl) ⟨601856, by rfl⟩ : syracuseStep 802475 = 1203713) B1203713
theorem B802505 : Blo 531801 802505 := bstep (se 2 (by rfl) ⟨300939, by rfl⟩ : syracuseStep 802505 = 601879) B601879
theorem B3030817 : Blo 531801 3030817 := bstep (se 2 (by rfl) ⟨1136556, by rfl⟩ : syracuseStep 3030817 = 2273113) B2273113
theorem B802619 : Blo 531801 802619 := bstep (se 1 (by rfl) ⟨601964, by rfl⟩ : syracuseStep 802619 = 1203929) B1203929
theorem B11550539 : Blo 531801 11550539 := bstep (se 1 (by rfl) ⟨8662904, by rfl⟩ : syracuseStep 11550539 = 17325809) B17325809
theorem B900983 : Blo 531801 900983 := bstep (se 1 (by rfl) ⟨675737, by rfl⟩ : syracuseStep 900983 = 1351475) B1351475
theorem B802679 : Blo 531801 802679 := bstep (se 1 (by rfl) ⟨602009, by rfl⟩ : syracuseStep 802679 = 1204019) B1204019
theorem B802703 : Blo 531801 802703 := bstep (se 1 (by rfl) ⟨602027, by rfl⟩ : syracuseStep 802703 = 1204055) B1204055
theorem B802745 : Blo 531801 802745 := bstep (se 2 (by rfl) ⟨301029, by rfl⟩ : syracuseStep 802745 = 602059) B602059
theorem B802823 : Blo 531801 802823 := bstep (se 1 (by rfl) ⟨602117, by rfl⟩ : syracuseStep 802823 = 1204235) B1204235
theorem B802859 : Blo 531801 802859 := bstep (se 1 (by rfl) ⟨602144, by rfl⟩ : syracuseStep 802859 = 1204289) B1204289
theorem B802889 : Blo 531801 802889 := bstep (se 2 (by rfl) ⟨301083, by rfl⟩ : syracuseStep 802889 = 602167) B602167
theorem B803003 : Blo 531801 803003 := bstep (se 1 (by rfl) ⟨602252, by rfl⟩ : syracuseStep 803003 = 1204505) B1204505
theorem B803063 : Blo 531801 803063 := bstep (se 1 (by rfl) ⟨602297, by rfl⟩ : syracuseStep 803063 = 1204595) B1204595
theorem B2703617 : Blo 531801 2703617 := bstep (se 2 (by rfl) ⟨1013856, by rfl⟩ : syracuseStep 2703617 = 2027713) B2027713
theorem B803087 : Blo 531801 803087 := bstep (se 1 (by rfl) ⟨602315, by rfl⟩ : syracuseStep 803087 = 1204631) B1204631
theorem B803129 : Blo 531801 803129 := bstep (se 2 (by rfl) ⟨301173, by rfl⟩ : syracuseStep 803129 = 602347) B602347
theorem B901435 : Blo 531801 901435 := bstep (se 1 (by rfl) ⟨676076, by rfl⟩ : syracuseStep 901435 = 1352153) B1352153
theorem B1524055 : Blo 531801 1524055 := bstep (se 1 (by rfl) ⟨1143041, by rfl⟩ : syracuseStep 1524055 = 2286083) B2286083
theorem B803207 : Blo 531801 803207 := bstep (se 1 (by rfl) ⟨602405, by rfl⟩ : syracuseStep 803207 = 1204811) B1204811
theorem B803243 : Blo 531801 803243 := bstep (se 1 (by rfl) ⟨602432, by rfl⟩ : syracuseStep 803243 = 1204865) B1204865
theorem B901577 : Blo 531801 901577 := bstep (se 2 (by rfl) ⟨338091, by rfl⟩ : syracuseStep 901577 = 676183) B676183
theorem B803273 : Blo 531801 803273 := bstep (se 2 (by rfl) ⟨301227, by rfl⟩ : syracuseStep 803273 = 602455) B602455
theorem B2572823 : Blo 531801 2572823 := bstep (se 1 (by rfl) ⟨1929617, by rfl⟩ : syracuseStep 2572823 = 3859235) B3859235
theorem B1196603 : Blo 531801 1196603 := bstep (se 1 (by rfl) ⟨897452, by rfl⟩ : syracuseStep 1196603 = 1794905) B1794905
theorem B803387 : Blo 531801 803387 := bstep (se 1 (by rfl) ⟨602540, by rfl⟩ : syracuseStep 803387 = 1205081) B1205081
theorem B803447 : Blo 531801 803447 := bstep (se 1 (by rfl) ⟨602585, by rfl⟩ : syracuseStep 803447 = 1205171) B1205171
theorem B803471 : Blo 531801 803471 := bstep (se 1 (by rfl) ⟨602603, by rfl⟩ : syracuseStep 803471 = 1205207) B1205207
theorem B1196729 : Blo 531801 1196729 := bstep (se 2 (by rfl) ⟨448773, by rfl⟩ : syracuseStep 1196729 = 897547) B897547
theorem B803513 : Blo 531801 803513 := bstep (se 2 (by rfl) ⟨301317, by rfl⟩ : syracuseStep 803513 = 602635) B602635
theorem B803591 : Blo 531801 803591 := bstep (se 1 (by rfl) ⟨602693, by rfl⟩ : syracuseStep 803591 = 1205387) B1205387
theorem B803627 : Blo 531801 803627 := bstep (se 1 (by rfl) ⟨602720, by rfl⟩ : syracuseStep 803627 = 1205441) B1205441
theorem B803657 : Blo 531801 803657 := bstep (se 2 (by rfl) ⟨301371, by rfl⟩ : syracuseStep 803657 = 602743) B602743
theorem B1197071 : Blo 531801 1197071 := bstep (se 1 (by rfl) ⟨897803, by rfl⟩ : syracuseStep 1197071 = 1795607) B1795607
theorem B3032093 : Blo 531801 3032093 := bstep (se 3 (by rfl) ⟨568517, by rfl⟩ : syracuseStep 3032093 = 1137035) B1137035
theorem B1197089 : Blo 531801 1197089 := bstep (se 2 (by rfl) ⟨448908, by rfl⟩ : syracuseStep 1197089 = 897817) B897817
theorem B2704427 : Blo 531801 2704427 := bstep (se 1 (by rfl) ⟨2028320, by rfl⟩ : syracuseStep 2704427 = 4056641) B4056641
theorem B902279 : Blo 531801 902279 := bstep (se 1 (by rfl) ⟨676709, by rfl⟩ : syracuseStep 902279 = 1353419) B1353419
theorem B2934049 : Blo 531801 2934049 := bstep (se 2 (by rfl) ⟨1100268, by rfl⟩ : syracuseStep 2934049 = 2200537) B2200537
theorem B1197431 : Blo 531801 1197431 := bstep (se 1 (by rfl) ⟨898073, by rfl⟩ : syracuseStep 1197431 = 1796147) B1796147
theorem B673211 : Blo 531801 673211 := bstep (se 1 (by rfl) ⟨504908, by rfl⟩ : syracuseStep 673211 = 1009817) B1009817
theorem B1197611 : Blo 531801 1197611 := bstep (se 1 (by rfl) ⟨898208, by rfl⟩ : syracuseStep 1197611 = 1796417) B1796417
theorem B902927 : Blo 531801 902927 := bstep (se 1 (by rfl) ⟨677195, by rfl⟩ : syracuseStep 902927 = 1354391) B1354391
theorem B1525547 : Blo 531801 1525547 := bstep (se 1 (by rfl) ⟨1144160, by rfl⟩ : syracuseStep 1525547 = 2288321) B2288321
theorem B1197971 : Blo 531801 1197971 := bstep (se 1 (by rfl) ⟨898478, by rfl⟩ : syracuseStep 1197971 = 1796957) B1796957
theorem B2606995 : Blo 531801 2606995 := bstep (se 1 (by rfl) ⟨1955246, by rfl⟩ : syracuseStep 2606995 = 3910493) B3910493
theorem B1198025 : Blo 531801 1198025 := bstep (se 2 (by rfl) ⟨449259, by rfl⟩ : syracuseStep 1198025 = 898519) B898519
theorem B2934749 : Blo 531801 2934749 := bstep (se 3 (by rfl) ⟨550265, by rfl⟩ : syracuseStep 2934749 = 1100531) B1100531
theorem B641039 : Blo 531801 641039 := bstep (se 1 (by rfl) ⟨480779, by rfl⟩ : syracuseStep 641039 = 961559) B961559
theorem B1230995 : Blo 531801 1230995 := bstep (se 1 (by rfl) ⟨923246, by rfl⟩ : syracuseStep 1230995 = 1846493) B1846493
theorem B903467 : Blo 531801 903467 := bstep (se 1 (by rfl) ⟨677600, by rfl⟩ : syracuseStep 903467 = 1355201) B1355201
theorem B1820987 : Blo 531801 1820987 := bstep (se 1 (by rfl) ⟨1365740, by rfl⟩ : syracuseStep 1820987 = 2731481) B2731481
theorem B2705723 : Blo 531801 2705723 := bstep (se 1 (by rfl) ⟨2029292, by rfl⟩ : syracuseStep 2705723 = 4058585) B4058585
theorem B674183 : Blo 531801 674183 := bstep (se 1 (by rfl) ⟨505637, by rfl⟩ : syracuseStep 674183 = 1011275) B1011275
theorem B608647 : Blo 531801 608647 := bstep (se 1 (by rfl) ⟨456485, by rfl⟩ : syracuseStep 608647 = 912971) B912971
theorem B2705885 : Blo 531801 2705885 := bstep (se 3 (by rfl) ⟨507353, by rfl⟩ : syracuseStep 2705885 = 1014707) B1014707
theorem B1624637 : Blo 531801 1624637 := bstep (se 3 (by rfl) ⟨304619, by rfl⟩ : syracuseStep 1624637 = 609239) B609239
theorem B1919555 : Blo 531801 1919555 := bstep (se 1 (by rfl) ⟨1439666, by rfl⟩ : syracuseStep 1919555 = 2879333) B2879333
theorem B1198727 : Blo 531801 1198727 := bstep (se 1 (by rfl) ⟨899045, by rfl⟩ : syracuseStep 1198727 = 1798091) B1798091
theorem B903865 : Blo 531801 903865 := bstep (se 2 (by rfl) ⟨338949, by rfl⟩ : syracuseStep 903865 = 677899) B677899
theorem B2706209 : Blo 531801 2706209 := bstep (se 2 (by rfl) ⟨1014828, by rfl⟩ : syracuseStep 2706209 = 2029657) B2029657
theorem B6081317 : Blo 531801 6081317 := bstep (se 4 (by rfl) ⟨570123, by rfl⟩ : syracuseStep 6081317 = 1140247) B1140247
theorem B1198907 : Blo 531801 1198907 := bstep (se 1 (by rfl) ⟨899180, by rfl⟩ : syracuseStep 1198907 = 1798361) B1798361
theorem B1199033 : Blo 531801 1199033 := bstep (se 2 (by rfl) ⟨449637, by rfl⟩ : syracuseStep 1199033 = 899275) B899275
theorem B674831 : Blo 531801 674831 := bstep (se 1 (by rfl) ⟨506123, by rfl⟩ : syracuseStep 674831 = 1012247) B1012247
theorem B1199375 : Blo 531801 1199375 := bstep (se 1 (by rfl) ⟨899531, by rfl⟩ : syracuseStep 1199375 = 1799063) B1799063
theorem B1199393 : Blo 531801 1199393 := bstep (se 2 (by rfl) ⟨449772, by rfl⟩ : syracuseStep 1199393 = 899545) B899545
theorem B5459345 : Blo 531801 5459345 := bstep (se 2 (by rfl) ⟨2047254, by rfl⟩ : syracuseStep 5459345 = 4094509) B4094509
theorem B4050323 : Blo 531801 4050323 := bstep (se 1 (by rfl) ⟨3037742, by rfl⟩ : syracuseStep 4050323 = 6075485) B6075485
theorem B3034691 : Blo 531801 3034691 := bstep (se 1 (by rfl) ⟨2276018, by rfl⟩ : syracuseStep 3034691 = 4552037) B4552037
theorem B1199735 : Blo 531801 1199735 := bstep (se 1 (by rfl) ⟨899801, by rfl⟩ : syracuseStep 1199735 = 1799603) B1799603
theorem B1822409 : Blo 531801 1822409 := bstep (se 2 (by rfl) ⟨683403, by rfl⟩ : syracuseStep 1822409 = 1366807) B1366807
theorem B2707181 : Blo 531801 2707181 := bstep (se 3 (by rfl) ⟨507596, by rfl⟩ : syracuseStep 2707181 = 1015193) B1015193
theorem B1199915 : Blo 531801 1199915 := bstep (se 1 (by rfl) ⟨899936, by rfl⟩ : syracuseStep 1199915 = 1799873) B1799873
theorem B1200275 : Blo 531801 1200275 := bstep (se 1 (by rfl) ⟨900206, by rfl⟩ : syracuseStep 1200275 = 1800413) B1800413
theorem B1200329 : Blo 531801 1200329 := bstep (se 2 (by rfl) ⟨450123, by rfl⟩ : syracuseStep 1200329 = 900247) B900247
theorem B3297509 : Blo 531801 3297509 := bstep (se 4 (by rfl) ⟨309141, by rfl⟩ : syracuseStep 3297509 = 618283) B618283
theorem B2281709 : Blo 531801 2281709 := bstep (se 3 (by rfl) ⟨427820, by rfl⟩ : syracuseStep 2281709 = 855641) B855641
theorem B2707991 : Blo 531801 2707991 := bstep (se 1 (by rfl) ⟨2030993, by rfl⟩ : syracuseStep 2707991 = 4061987) B4061987
theorem B1626923 : Blo 531801 1626923 := bstep (se 1 (by rfl) ⟨1220192, by rfl⟩ : syracuseStep 1626923 = 2440385) B2440385
theorem B2020211 : Blo 531801 2020211 := bstep (se 1 (by rfl) ⟨1515158, by rfl⟩ : syracuseStep 2020211 = 3030317) B3030317
theorem B1201031 : Blo 531801 1201031 := bstep (se 1 (by rfl) ⟨900773, by rfl⟩ : syracuseStep 1201031 = 1801547) B1801547
theorem B1299347 : Blo 531801 1299347 := bstep (se 1 (by rfl) ⟨974510, by rfl⟩ : syracuseStep 1299347 = 1949021) B1949021
theorem B1201211 : Blo 531801 1201211 := bstep (se 1 (by rfl) ⟨900908, by rfl⟩ : syracuseStep 1201211 = 1801817) B1801817
theorem B1201337 : Blo 531801 1201337 := bstep (se 2 (by rfl) ⟨450501, by rfl⟩ : syracuseStep 1201337 = 901003) B901003
theorem B3036467 : Blo 531801 3036467 := bstep (se 1 (by rfl) ⟨2277350, by rfl⟩ : syracuseStep 3036467 = 4554701) B4554701
theorem B4576571 : Blo 531801 4576571 := bstep (se 1 (by rfl) ⟨3432428, by rfl⟩ : syracuseStep 4576571 = 6864857) B6864857
theorem B1201679 : Blo 531801 1201679 := bstep (se 1 (by rfl) ⟨901259, by rfl⟩ : syracuseStep 1201679 = 1802519) B1802519
theorem B1201697 : Blo 531801 1201697 := bstep (se 2 (by rfl) ⟨450636, by rfl⟩ : syracuseStep 1201697 = 901273) B901273
theorem B1332883 : Blo 531801 1332883 := bstep (se 1 (by rfl) ⟨999662, by rfl⟩ : syracuseStep 1332883 = 1999325) B1999325
theorem B6477529 : Blo 531801 6477529 := bstep (se 2 (by rfl) ⟨2429073, by rfl⟩ : syracuseStep 6477529 = 4858147) B4858147
theorem B3856177 : Blo 531801 3856177 := bstep (se 2 (by rfl) ⟨1446066, by rfl⟩ : syracuseStep 3856177 = 2892133) B2892133
theorem B1202039 : Blo 531801 1202039 := bstep (se 1 (by rfl) ⟨901529, by rfl⟩ : syracuseStep 1202039 = 1803059) B1803059
theorem B972691 : Blo 531801 972691 := bstep (se 1 (by rfl) ⟨729518, by rfl⟩ : syracuseStep 972691 = 1459037) B1459037
theorem B677803 : Blo 531801 677803 := bstep (se 1 (by rfl) ⟨508352, by rfl⟩ : syracuseStep 677803 = 1016705) B1016705
theorem B1202219 : Blo 531801 1202219 := bstep (se 1 (by rfl) ⟨901664, by rfl⟩ : syracuseStep 1202219 = 1803329) B1803329
theorem B972947 : Blo 531801 972947 := bstep (se 1 (by rfl) ⟨729710, by rfl⟩ : syracuseStep 972947 = 1459421) B1459421
theorem B6314273 : Blo 531801 6314273 := bstep (se 2 (by rfl) ⟨2367852, by rfl⟩ : syracuseStep 6314273 = 4735705) B4735705
theorem B3299621 : Blo 531801 3299621 := bstep (se 4 (by rfl) ⟨309339, by rfl⟩ : syracuseStep 3299621 = 618679) B618679
theorem B1202579 : Blo 531801 1202579 := bstep (se 1 (by rfl) ⟨901934, by rfl⟩ : syracuseStep 1202579 = 1803869) B1803869
theorem B809387 : Blo 531801 809387 := bstep (se 1 (by rfl) ⟨607040, by rfl⟩ : syracuseStep 809387 = 1214081) B1214081
theorem B1202633 : Blo 531801 1202633 := bstep (se 2 (by rfl) ⟨450987, by rfl⟩ : syracuseStep 1202633 = 901975) B901975
theorem B3070493 : Blo 531801 3070493 := bstep (se 3 (by rfl) ⟨575717, by rfl⟩ : syracuseStep 3070493 = 1151435) B1151435
theorem B9230915 : Blo 531801 9230915 := bstep (se 1 (by rfl) ⟨6923186, by rfl⟩ : syracuseStep 9230915 = 13846373) B13846373
theorem B3037925 : Blo 531801 3037925 := bstep (se 4 (by rfl) ⟨284805, by rfl⟩ : syracuseStep 3037925 = 569611) B569611
theorem B2022353 : Blo 531801 2022353 := bstep (se 2 (by rfl) ⟨758382, by rfl⟩ : syracuseStep 2022353 = 1516765) B1516765
theorem B2284631 : Blo 531801 2284631 := bstep (se 1 (by rfl) ⟨1713473, by rfl⟩ : syracuseStep 2284631 = 3426947) B3426947
theorem B7724119 : Blo 531801 7724119 := bstep (se 1 (by rfl) ⟨5793089, by rfl⟩ : syracuseStep 7724119 = 11586179) B11586179
theorem B1203335 : Blo 531801 1203335 := bstep (se 1 (by rfl) ⟨902501, by rfl⟩ : syracuseStep 1203335 = 1805003) B1805003
theorem B3038381 : Blo 531801 3038381 := bstep (se 3 (by rfl) ⟨569696, by rfl⟩ : syracuseStep 3038381 = 1139393) B1139393
theorem B2022671 : Blo 531801 2022671 := bstep (se 1 (by rfl) ⟨1517003, by rfl⟩ : syracuseStep 2022671 = 3034007) B3034007
theorem B1203515 : Blo 531801 1203515 := bstep (se 1 (by rfl) ⟨902636, by rfl⟩ : syracuseStep 1203515 = 1805273) B1805273
theorem B1203641 : Blo 531801 1203641 := bstep (se 2 (by rfl) ⟨451365, by rfl⟩ : syracuseStep 1203641 = 902731) B902731
theorem B1138121 : Blo 531801 1138121 := bstep (se 2 (by rfl) ⟨426795, by rfl⟩ : syracuseStep 1138121 = 853591) B853591
theorem B2711069 : Blo 531801 2711069 := bstep (se 3 (by rfl) ⟨508325, by rfl⟩ : syracuseStep 2711069 = 1016651) B1016651
theorem B4120183 : Blo 531801 4120183 := bstep (se 1 (by rfl) ⟨3090137, by rfl⟩ : syracuseStep 4120183 = 6180275) B6180275
theorem B1203983 : Blo 531801 1203983 := bstep (se 1 (by rfl) ⟨902987, by rfl⟩ : syracuseStep 1203983 = 1805975) B1805975
theorem B1204001 : Blo 531801 1204001 := bstep (se 2 (by rfl) ⟨451500, by rfl⟩ : syracuseStep 1204001 = 903001) B903001
theorem B3039065 : Blo 531801 3039065 := bstep (se 2 (by rfl) ⟨1139649, by rfl⟩ : syracuseStep 3039065 = 2279299) B2279299
theorem B2711555 : Blo 531801 2711555 := bstep (se 1 (by rfl) ⟨2033666, by rfl⟩ : syracuseStep 2711555 = 4067333) B4067333
theorem B2187383 : Blo 531801 2187383 := bstep (se 1 (by rfl) ⟨1640537, by rfl⟩ : syracuseStep 2187383 = 3281075) B3281075
theorem B1204343 : Blo 531801 1204343 := bstep (se 1 (by rfl) ⟨903257, by rfl⟩ : syracuseStep 1204343 = 1806515) B1806515
theorem B1138873 : Blo 531801 1138873 := bstep (se 2 (by rfl) ⟨427077, by rfl⟩ : syracuseStep 1138873 = 854155) B854155
theorem B1204523 : Blo 531801 1204523 := bstep (se 1 (by rfl) ⟨903392, by rfl⟩ : syracuseStep 1204523 = 1806785) B1806785
theorem B5923277 : Blo 531801 5923277 := bstep (se 3 (by rfl) ⟨1110614, by rfl⟩ : syracuseStep 5923277 = 2221229) B2221229
theorem B3858947 : Blo 531801 3858947 := bstep (se 1 (by rfl) ⟨2894210, by rfl⟩ : syracuseStep 3858947 = 5788421) B5788421
theorem B1204883 : Blo 531801 1204883 := bstep (se 1 (by rfl) ⟨903662, by rfl⟩ : syracuseStep 1204883 = 1807325) B1807325
theorem B1204937 : Blo 531801 1204937 := bstep (se 2 (by rfl) ⟨451851, by rfl⟩ : syracuseStep 1204937 = 903703) B903703
theorem B2745089 : Blo 531801 2745089 := bstep (se 2 (by rfl) ⟨1029408, by rfl⟩ : syracuseStep 2745089 = 2058817) B2058817
theorem B811919 : Blo 531801 811919 := bstep (se 1 (by rfl) ⟨608939, by rfl⟩ : syracuseStep 811919 = 1217879) B1217879
theorem B5202839 : Blo 531801 5202839 := bstep (se 1 (by rfl) ⟨3902129, by rfl⟩ : syracuseStep 5202839 = 7804259) B7804259
theorem B5760011 : Blo 531801 5760011 := bstep (se 1 (by rfl) ⟨4320008, by rfl⟩ : syracuseStep 5760011 = 8640017) B8640017
theorem B1303595 : Blo 531801 1303595 := bstep (se 1 (by rfl) ⟨977696, by rfl⟩ : syracuseStep 1303595 = 1955393) B1955393
theorem B5498057 : Blo 531801 5498057 := bstep (se 2 (by rfl) ⟨2061771, by rfl⟩ : syracuseStep 5498057 = 4123543) B4123543
theorem B910711 : Blo 531801 910711 := bstep (se 1 (by rfl) ⟨683033, by rfl⟩ : syracuseStep 910711 = 1366067) B1366067
theorem B812587 : Blo 531801 812587 := bstep (se 1 (by rfl) ⟨609440, by rfl⟩ : syracuseStep 812587 = 1218881) B1218881
theorem B812843 : Blo 531801 812843 := bstep (se 1 (by rfl) ⟨609632, by rfl⟩ : syracuseStep 812843 = 1219265) B1219265
theorem B2288081 : Blo 531801 2288081 := bstep (se 2 (by rfl) ⟨858030, by rfl⟩ : syracuseStep 2288081 = 1716061) B1716061
theorem B911915 : Blo 531801 911915 := bstep (se 1 (by rfl) ⟨683936, by rfl⟩ : syracuseStep 911915 = 1367873) B1367873
theorem B1141307 : Blo 531801 1141307 := bstep (se 1 (by rfl) ⟨855980, by rfl⟩ : syracuseStep 1141307 = 1711961) B1711961
theorem B2026241 : Blo 531801 2026241 := bstep (se 2 (by rfl) ⟨759840, by rfl⟩ : syracuseStep 2026241 = 1519681) B1519681
theorem B2026255 : Blo 531801 2026255 := bstep (se 1 (by rfl) ⟨1519691, by rfl⟩ : syracuseStep 2026255 = 3039383) B3039383
theorem B1797011 : Blo 531801 1797011 := bstep (se 1 (by rfl) ⟨1347758, by rfl⟩ : syracuseStep 1797011 = 2695517) B2695517
theorem B3238865 : Blo 531801 3238865 := bstep (se 2 (by rfl) ⟨1214574, by rfl⟩ : syracuseStep 3238865 = 2429149) B2429149
theorem B9137285 : Blo 531801 9137285 := bstep (se 4 (by rfl) ⟨856620, by rfl⟩ : syracuseStep 9137285 = 1713241) B1713241
theorem B1010873 : Blo 531801 1010873 := bstep (se 2 (by rfl) ⟨379077, by rfl⟩ : syracuseStep 1010873 = 758155) B758155
theorem B1142059 : Blo 531801 1142059 := bstep (se 1 (by rfl) ⟨856544, by rfl⟩ : syracuseStep 1142059 = 1713089) B1713089
theorem B814607 : Blo 531801 814607 := bstep (se 1 (by rfl) ⟨610955, by rfl⟩ : syracuseStep 814607 = 1221911) B1221911
theorem B58453589 : Blo 531801 58453589 := bstep (se 8 (by rfl) ⟨342501, by rfl⟩ : syracuseStep 58453589 = 685003) B685003
theorem B5205875 : Blo 531801 5205875 := bstep (se 1 (by rfl) ⟨3904406, by rfl⟩ : syracuseStep 5205875 = 7808813) B7808813
theorem B6057989 : Blo 531801 6057989 := bstep (se 4 (by rfl) ⟨567936, by rfl⟩ : syracuseStep 6057989 = 1135873) B1135873
theorem B2027531 : Blo 531801 2027531 := bstep (se 1 (by rfl) ⟨1520648, by rfl⟩ : syracuseStep 2027531 = 3041297) B3041297
theorem B1798415 : Blo 531801 1798415 := bstep (se 1 (by rfl) ⟨1348811, by rfl⟩ : syracuseStep 1798415 = 2697623) B2697623
theorem B1012027 : Blo 531801 1012027 := bstep (se 1 (by rfl) ⟨759020, by rfl⟩ : syracuseStep 1012027 = 1518041) B1518041
theorem B1438013 : Blo 531801 1438013 := bstep (se 3 (by rfl) ⟨269627, by rfl⟩ : syracuseStep 1438013 = 539255) B539255
theorem B2748761 : Blo 531801 2748761 := bstep (se 2 (by rfl) ⟨1030785, by rfl⟩ : syracuseStep 2748761 = 2061571) B2061571
theorem B1438067 : Blo 531801 1438067 := bstep (se 1 (by rfl) ⟨1078550, by rfl⟩ : syracuseStep 1438067 = 2157101) B2157101
theorem B1798685 : Blo 531801 1798685 := bstep (se 3 (by rfl) ⟨337253, by rfl⟩ : syracuseStep 1798685 = 674507) B674507
theorem B6156901 : Blo 531801 6156901 := bstep (se 4 (by rfl) ⟨577209, by rfl⟩ : syracuseStep 6156901 = 1154419) B1154419
theorem B914105 : Blo 531801 914105 := bstep (se 2 (by rfl) ⟨342789, by rfl⟩ : syracuseStep 914105 = 685579) B685579
theorem B17330881 : Blo 531801 17330881 := bstep (se 2 (by rfl) ⟨6499080, by rfl⟩ : syracuseStep 17330881 = 12998161) B12998161
theorem B1012513 : Blo 531801 1012513 := bstep (se 2 (by rfl) ⟨379692, by rfl⟩ : syracuseStep 1012513 = 759385) B759385
theorem B3371813 : Blo 531801 3371813 := bstep (se 4 (by rfl) ⟨316107, by rfl⟩ : syracuseStep 3371813 = 632215) B632215
theorem B2028473 : Blo 531801 2028473 := bstep (se 2 (by rfl) ⟨760677, by rfl⟩ : syracuseStep 2028473 = 1521355) B1521355
theorem B1144211 : Blo 531801 1144211 := bstep (se 1 (by rfl) ⟨858158, by rfl⟩ : syracuseStep 1144211 = 1716317) B1716317
theorem B5011237 : Blo 531801 5011237 := bstep (se 4 (by rfl) ⟨469803, by rfl⟩ : syracuseStep 5011237 = 939607) B939607
theorem B1439603 : Blo 531801 1439603 := bstep (se 1 (by rfl) ⟨1079702, by rfl⟩ : syracuseStep 1439603 = 2159405) B2159405
theorem B1439623 : Blo 531801 1439623 := bstep (se 1 (by rfl) ⟨1079717, by rfl⟩ : syracuseStep 1439623 = 2159435) B2159435
theorem B1800089 : Blo 531801 1800089 := bstep (se 2 (by rfl) ⟨675033, by rfl⟩ : syracuseStep 1800089 = 1350067) B1350067
theorem B1013705 : Blo 531801 1013705 := bstep (se 2 (by rfl) ⟨380139, by rfl⟩ : syracuseStep 1013705 = 760279) B760279
theorem B1538423 : Blo 531801 1538423 := bstep (se 1 (by rfl) ⟨1153817, by rfl⟩ : syracuseStep 1538423 = 2307635) B2307635
theorem B1440185 : Blo 531801 1440185 := bstep (se 2 (by rfl) ⟨540069, by rfl⟩ : syracuseStep 1440185 = 1080139) B1080139
theorem B1800791 : Blo 531801 1800791 := bstep (se 1 (by rfl) ⟨1350593, by rfl⟩ : syracuseStep 1800791 = 2701187) B2701187
theorem B1014419 : Blo 531801 1014419 := bstep (se 1 (by rfl) ⟨760814, by rfl⟩ : syracuseStep 1014419 = 1521629) B1521629
theorem B1014457 : Blo 531801 1014457 := bstep (se 2 (by rfl) ⟨380421, by rfl⟩ : syracuseStep 1014457 = 760843) B760843
theorem B1801277 : Blo 531801 1801277 := bstep (se 3 (by rfl) ⟨337739, by rfl⟩ : syracuseStep 1801277 = 675479) B675479
theorem B2031115 : Blo 531801 2031115 := bstep (se 1 (by rfl) ⟨1523336, by rfl⟩ : syracuseStep 2031115 = 3046673) B3046673
theorem B2031419 : Blo 531801 2031419 := bstep (se 1 (by rfl) ⟨1523564, by rfl⟩ : syracuseStep 2031419 = 3047129) B3047129
theorem B2555869 : Blo 531801 2555869 := bstep (se 3 (by rfl) ⟨479225, by rfl⟩ : syracuseStep 2555869 = 958451) B958451
theorem B1802411 : Blo 531801 1802411 := bstep (se 1 (by rfl) ⟨1351808, by rfl⟩ : syracuseStep 1802411 = 2703617) B2703617
theorem B6816059 : Blo 531801 6816059 := bstep (se 1 (by rfl) ⟨5112044, by rfl⟩ : syracuseStep 6816059 = 10224089) B10224089
theorem B5833021 : Blo 531801 5833021 := bstep (se 3 (by rfl) ⟨1093691, by rfl⟩ : syracuseStep 5833021 = 2187383) B2187383
theorem B2032073 : Blo 531801 2032073 := bstep (se 2 (by rfl) ⟨762027, by rfl⟩ : syracuseStep 2032073 = 1524055) B1524055
theorem B721531 : Blo 531801 721531 := bstep (se 1 (by rfl) ⟨541148, by rfl⟩ : syracuseStep 721531 = 1082297) B1082297
theorem B1802951 : Blo 531801 1802951 := bstep (se 1 (by rfl) ⟨1352213, by rfl⟩ : syracuseStep 1802951 = 2704427) B2704427
theorem B5768009 : Blo 531801 5768009 := bstep (se 2 (by rfl) ⟨2163003, by rfl⟩ : syracuseStep 5768009 = 4326007) B4326007
theorem B3834701 : Blo 531801 3834701 := bstep (se 3 (by rfl) ⟨719006, by rfl⟩ : syracuseStep 3834701 = 1438013) B1438013
theorem B2032559 : Blo 531801 2032559 := bstep (se 1 (by rfl) ⟨1524419, by rfl⟩ : syracuseStep 2032559 = 3048839) B3048839
theorem B2557099 : Blo 531801 2557099 := bstep (se 1 (by rfl) ⟨1917824, by rfl⟩ : syracuseStep 2557099 = 3835649) B3835649
theorem B1017031 : Blo 531801 1017031 := bstep (se 1 (by rfl) ⟨762773, by rfl⟩ : syracuseStep 1017031 = 1525547) B1525547
theorem B4326857 : Blo 531801 4326857 := bstep (se 2 (by rfl) ⟨1622571, by rfl⟩ : syracuseStep 4326857 = 3245143) B3245143
theorem B1213991 : Blo 531801 1213991 := bstep (se 1 (by rfl) ⟨910493, by rfl⟩ : syracuseStep 1213991 = 1820987) B1820987
theorem B1803815 : Blo 531801 1803815 := bstep (se 1 (by rfl) ⟨1352861, by rfl⟩ : syracuseStep 1803815 = 2705723) B2705723
theorem B1803923 : Blo 531801 1803923 := bstep (se 1 (by rfl) ⟨1352942, by rfl⟩ : syracuseStep 1803923 = 2705885) B2705885
theorem B2033363 : Blo 531801 2033363 := bstep (se 1 (by rfl) ⟨1525022, by rfl⟩ : syracuseStep 2033363 = 3050045) B3050045
theorem B1279703 : Blo 531801 1279703 := bstep (se 1 (by rfl) ⟨959777, by rfl⟩ : syracuseStep 1279703 = 1919555) B1919555
theorem B1214281 : Blo 531801 1214281 := bstep (se 2 (by rfl) ⟨455355, by rfl⟩ : syracuseStep 1214281 = 910711) B910711
theorem B1804139 : Blo 531801 1804139 := bstep (se 1 (by rfl) ⟨1353104, by rfl⟩ : syracuseStep 1804139 = 2706209) B2706209
theorem B1804193 : Blo 531801 1804193 := bstep (se 2 (by rfl) ⟨676572, by rfl⟩ : syracuseStep 1804193 = 1353145) B1353145
theorem B1083449 : Blo 531801 1083449 := bstep (se 2 (by rfl) ⟨406293, by rfl⟩ : syracuseStep 1083449 = 812587) B812587
theorem B854263 : Blo 531801 854263 := bstep (se 1 (by rfl) ⟨640697, by rfl⟩ : syracuseStep 854263 = 1281395) B1281395
theorem B3639563 : Blo 531801 3639563 := bstep (se 1 (by rfl) ⟨2729672, by rfl⟩ : syracuseStep 3639563 = 5459345) B5459345
theorem B4557161 : Blo 531801 4557161 := bstep (se 2 (by rfl) ⟨1708935, by rfl⟩ : syracuseStep 4557161 = 3417871) B3417871
theorem B6097355 : Blo 531801 6097355 := bstep (se 1 (by rfl) ⟨4573016, by rfl⟩ : syracuseStep 6097355 = 9146033) B9146033
theorem B1214939 : Blo 531801 1214939 := bstep (se 1 (by rfl) ⟨911204, by rfl⟩ : syracuseStep 1214939 = 1822409) B1822409
theorem B1804787 : Blo 531801 1804787 := bstep (se 1 (by rfl) ⟨1353590, by rfl⟩ : syracuseStep 1804787 = 2707181) B2707181
theorem B3475993 : Blo 531801 3475993 := bstep (se 2 (by rfl) ⟨1303497, by rfl⟩ : syracuseStep 3475993 = 2606995) B2606995
theorem B2198339 : Blo 531801 2198339 := bstep (se 1 (by rfl) ⟨1648754, by rfl⟩ : syracuseStep 2198339 = 3297509) B3297509
theorem B1805327 : Blo 531801 1805327 := bstep (se 1 (by rfl) ⟨1353995, by rfl⟩ : syracuseStep 1805327 = 2707991) B2707991
theorem B1543225 : Blo 531801 1543225 := bstep (se 2 (by rfl) ⟨578709, by rfl⟩ : syracuseStep 1543225 = 1157419) B1157419
theorem B1346807 : Blo 531801 1346807 := bstep (se 1 (by rfl) ⟨1010105, by rfl⟩ : syracuseStep 1346807 = 2020211) B2020211
theorem B3051047 : Blo 531801 3051047 := bstep (se 1 (by rfl) ⟨2288285, by rfl⟩ : syracuseStep 3051047 = 4576571) B4576571
theorem B1805921 : Blo 531801 1805921 := bstep (se 2 (by rfl) ⟨677220, by rfl⟩ : syracuseStep 1805921 = 1354441) B1354441
theorem B20778619 : Blo 531801 20778619 := bstep (se 1 (by rfl) ⟨15583964, by rfl⟩ : syracuseStep 20778619 = 31167929) B31167929
theorem B1707655 : Blo 531801 1707655 := bstep (se 1 (by rfl) ⟨1280741, by rfl⟩ : syracuseStep 1707655 = 2561483) B2561483
theorem B3051229 : Blo 531801 3051229 := bstep (se 3 (by rfl) ⟨572105, by rfl⟩ : syracuseStep 3051229 = 1144211) B1144211
theorem B2560157 : Blo 531801 2560157 := bstep (se 3 (by rfl) ⟨480029, by rfl⟩ : syracuseStep 2560157 = 960059) B960059
theorem B856583 : Blo 531801 856583 := bstep (se 1 (by rfl) ⟨642437, by rfl⟩ : syracuseStep 856583 = 1284875) B1284875
theorem B1708553 : Blo 531801 1708553 := bstep (se 2 (by rfl) ⟨640707, by rfl⟩ : syracuseStep 1708553 = 1281415) B1281415
theorem B2888327 : Blo 531801 2888327 := bstep (se 1 (by rfl) ⟨2166245, by rfl⟩ : syracuseStep 2888327 = 4332491) B4332491
theorem B1348235 : Blo 531801 1348235 := bstep (se 1 (by rfl) ⟨1011176, by rfl⟩ : syracuseStep 1348235 = 2022353) B2022353
theorem B1348447 : Blo 531801 1348447 := bstep (se 1 (by rfl) ⟨1011335, by rfl⟩ : syracuseStep 1348447 = 2022671) B2022671
theorem B2560943 : Blo 531801 2560943 := bstep (se 1 (by rfl) ⟨1920707, by rfl⟩ : syracuseStep 2560943 = 3841415) B3841415
theorem B4330415 : Blo 531801 4330415 := bstep (se 1 (by rfl) ⟨3247811, by rfl⟩ : syracuseStep 4330415 = 6495623) B6495623
theorem B2167739 : Blo 531801 2167739 := bstep (se 1 (by rfl) ⟨1625804, by rfl⟩ : syracuseStep 2167739 = 3251609) B3251609
theorem B758747 : Blo 531801 758747 := bstep (se 1 (by rfl) ⟨569060, by rfl⟩ : syracuseStep 758747 = 1138121) B1138121
theorem B2626561 : Blo 531801 2626561 := bstep (se 2 (by rfl) ⟨984960, by rfl⟩ : syracuseStep 2626561 = 1969921) B1969921
theorem B1807379 : Blo 531801 1807379 := bstep (se 1 (by rfl) ⟨1355534, by rfl⟩ : syracuseStep 1807379 = 2711069) B2711069
theorem B857287 : Blo 531801 857287 := bstep (se 1 (by rfl) ⟨642965, by rfl⟩ : syracuseStep 857287 = 1285931) B1285931
theorem B1807703 : Blo 531801 1807703 := bstep (se 1 (by rfl) ⟨1355777, by rfl⟩ : syracuseStep 1807703 = 2711555) B2711555
theorem B1709437 : Blo 531801 1709437 := bstep (se 3 (by rfl) ⟨320519, by rfl⟩ : syracuseStep 1709437 = 641039) B641039
theorem B3282653 : Blo 531801 3282653 := bstep (se 3 (by rfl) ⟨615497, by rfl⟩ : syracuseStep 3282653 = 1230995) B1230995
theorem B1349369 : Blo 531801 1349369 := bstep (se 2 (by rfl) ⟨506013, by rfl⟩ : syracuseStep 1349369 = 1012027) B1012027
theorem B857999 : Blo 531801 857999 := bstep (se 1 (by rfl) ⟨643499, by rfl⟩ : syracuseStep 857999 = 1286999) B1286999
theorem B3840007 : Blo 531801 3840007 := bstep (se 1 (by rfl) ⟨2880005, by rfl⟩ : syracuseStep 3840007 = 5760011) B5760011
theorem B8755289 : Blo 531801 8755289 := bstep (se 2 (by rfl) ⟨3283233, by rfl⟩ : syracuseStep 8755289 = 6566467) B6566467
theorem B23107841 : Blo 531801 23107841 := bstep (se 2 (by rfl) ⟨8665440, by rfl⟩ : syracuseStep 23107841 = 17330881) B17330881
theorem B1350017 : Blo 531801 1350017 := bstep (se 2 (by rfl) ⟨506256, by rfl⟩ : syracuseStep 1350017 = 1012513) B1012513
theorem B3840493 : Blo 531801 3840493 := bstep (se 3 (by rfl) ⟨720092, by rfl⟩ : syracuseStep 3840493 = 1440185) B1440185
theorem B5085881 : Blo 531801 5085881 := bstep (se 2 (by rfl) ⟨1907205, by rfl⟩ : syracuseStep 5085881 = 3814411) B3814411
theorem B4332365 : Blo 531801 4332365 := bstep (se 3 (by rfl) ⟨812318, by rfl⟩ : syracuseStep 4332365 = 1624637) B1624637
theorem B760871 : Blo 531801 760871 := bstep (se 1 (by rfl) ⟨570653, by rfl⟩ : syracuseStep 760871 = 1141307) B1141307
theorem B1350827 : Blo 531801 1350827 := bstep (se 1 (by rfl) ⟨1013120, by rfl⟩ : syracuseStep 1350827 = 2026241) B2026241
theorem B531807 : Blo 531801 531807 := bstep (se 1 (by rfl) ⟨398855, by rfl⟩ : syracuseStep 531807 = 797711) B797711
theorem B531835 : Blo 531801 531835 := bstep (se 1 (by rfl) ⟨398876, by rfl⟩ : syracuseStep 531835 = 797753) B797753
theorem B531887 : Blo 531801 531887 := bstep (se 1 (by rfl) ⟨398915, by rfl⟩ : syracuseStep 531887 = 797831) B797831
theorem B531911 : Blo 531801 531911 := bstep (se 1 (by rfl) ⟨398933, by rfl⟩ : syracuseStep 531911 = 797867) B797867
theorem B531931 : Blo 531801 531931 := bstep (se 1 (by rfl) ⟨398948, by rfl⟩ : syracuseStep 531931 = 797897) B797897
theorem B1777177 : Blo 531801 1777177 := bstep (se 2 (by rfl) ⟨666441, by rfl⟩ : syracuseStep 1777177 = 1332883) B1332883
theorem B532007 : Blo 531801 532007 := bstep (se 1 (by rfl) ⟨399005, by rfl⟩ : syracuseStep 532007 = 798011) B798011
theorem B532047 : Blo 531801 532047 := bstep (se 1 (by rfl) ⟨399035, by rfl⟩ : syracuseStep 532047 = 798071) B798071
theorem B532063 : Blo 531801 532063 := bstep (se 1 (by rfl) ⟨399047, by rfl⟩ : syracuseStep 532063 = 798095) B798095
theorem B532091 : Blo 531801 532091 := bstep (se 1 (by rfl) ⟨399068, by rfl⟩ : syracuseStep 532091 = 798137) B798137
theorem B9838219 : Blo 531801 9838219 := bstep (se 1 (by rfl) ⟨7378664, by rfl⟩ : syracuseStep 9838219 = 14757329) B14757329
theorem B532143 : Blo 531801 532143 := bstep (se 1 (by rfl) ⟨399107, by rfl⟩ : syracuseStep 532143 = 798215) B798215
theorem B532167 : Blo 531801 532167 := bstep (se 1 (by rfl) ⟨399125, by rfl⟩ : syracuseStep 532167 = 798251) B798251
theorem B532187 : Blo 531801 532187 := bstep (se 1 (by rfl) ⟨399140, by rfl⟩ : syracuseStep 532187 = 798281) B798281
theorem B38969059 : Blo 531801 38969059 := bstep (se 1 (by rfl) ⟨29226794, by rfl⟩ : syracuseStep 38969059 = 58453589) B58453589
theorem B532263 : Blo 531801 532263 := bstep (se 1 (by rfl) ⟨399197, by rfl⟩ : syracuseStep 532263 = 798395) B798395
theorem B532303 : Blo 531801 532303 := bstep (se 1 (by rfl) ⟨399227, by rfl⟩ : syracuseStep 532303 = 798455) B798455
theorem B532319 : Blo 531801 532319 := bstep (se 1 (by rfl) ⟨399239, by rfl⟩ : syracuseStep 532319 = 798479) B798479
theorem B2695031 : Blo 531801 2695031 := bstep (se 1 (by rfl) ⟨2021273, by rfl⟩ : syracuseStep 2695031 = 4042547) B4042547
theorem B532347 : Blo 531801 532347 := bstep (se 1 (by rfl) ⟨399260, by rfl⟩ : syracuseStep 532347 = 798521) B798521
theorem B532399 : Blo 531801 532399 := bstep (se 1 (by rfl) ⟨399299, by rfl⟩ : syracuseStep 532399 = 798599) B798599
theorem B532423 : Blo 531801 532423 := bstep (se 1 (by rfl) ⟨399317, by rfl⟩ : syracuseStep 532423 = 798635) B798635
theorem B532443 : Blo 531801 532443 := bstep (se 1 (by rfl) ⟨399332, by rfl⟩ : syracuseStep 532443 = 798665) B798665
theorem B4038659 : Blo 531801 4038659 := bstep (se 1 (by rfl) ⟨3028994, by rfl⟩ : syracuseStep 4038659 = 6057989) B6057989
theorem B1351687 : Blo 531801 1351687 := bstep (se 1 (by rfl) ⟨1013765, by rfl⟩ : syracuseStep 1351687 = 2027531) B2027531
theorem B532519 : Blo 531801 532519 := bstep (se 1 (by rfl) ⟨399389, by rfl⟩ : syracuseStep 532519 = 798779) B798779
theorem B532559 : Blo 531801 532559 := bstep (se 1 (by rfl) ⟨399419, by rfl⟩ : syracuseStep 532559 = 798839) B798839
theorem B532575 : Blo 531801 532575 := bstep (se 1 (by rfl) ⟨399431, by rfl⟩ : syracuseStep 532575 = 798863) B798863
theorem B532603 : Blo 531801 532603 := bstep (se 1 (by rfl) ⟨399452, by rfl⟩ : syracuseStep 532603 = 798905) B798905
theorem B532655 : Blo 531801 532655 := bstep (se 1 (by rfl) ⟨399491, by rfl⟩ : syracuseStep 532655 = 798983) B798983
theorem B532679 : Blo 531801 532679 := bstep (se 1 (by rfl) ⟨399509, by rfl⟩ : syracuseStep 532679 = 799019) B799019
theorem B532699 : Blo 531801 532699 := bstep (se 1 (by rfl) ⟨399524, by rfl⟩ : syracuseStep 532699 = 799049) B799049
theorem B958711 : Blo 531801 958711 := bstep (se 1 (by rfl) ⟨719033, by rfl⟩ : syracuseStep 958711 = 1438067) B1438067
theorem B532775 : Blo 531801 532775 := bstep (se 1 (by rfl) ⟨399581, by rfl⟩ : syracuseStep 532775 = 799163) B799163
theorem B532815 : Blo 531801 532815 := bstep (se 1 (by rfl) ⟨399611, by rfl⟩ : syracuseStep 532815 = 799223) B799223
theorem B532831 : Blo 531801 532831 := bstep (se 1 (by rfl) ⟨399623, by rfl⟩ : syracuseStep 532831 = 799247) B799247
theorem B532859 : Blo 531801 532859 := bstep (se 1 (by rfl) ⟨399644, by rfl⟩ : syracuseStep 532859 = 799289) B799289
theorem B532911 : Blo 531801 532911 := bstep (se 1 (by rfl) ⟨399683, by rfl⟩ : syracuseStep 532911 = 799367) B799367
theorem B532935 : Blo 531801 532935 := bstep (se 1 (by rfl) ⟨399701, by rfl⟩ : syracuseStep 532935 = 799403) B799403
theorem B532955 : Blo 531801 532955 := bstep (se 1 (by rfl) ⟨399716, by rfl⟩ : syracuseStep 532955 = 799433) B799433
theorem B1712627 : Blo 531801 1712627 := bstep (se 1 (by rfl) ⟨1284470, by rfl⟩ : syracuseStep 1712627 = 2568941) B2568941
theorem B598567 : Blo 531801 598567 := bstep (se 1 (by rfl) ⟨448925, by rfl⟩ : syracuseStep 598567 = 897851) B897851
theorem B533031 : Blo 531801 533031 := bstep (se 1 (by rfl) ⟨399773, by rfl⟩ : syracuseStep 533031 = 799547) B799547
theorem B533071 : Blo 531801 533071 := bstep (se 1 (by rfl) ⟨399803, by rfl⟩ : syracuseStep 533071 = 799607) B799607
theorem B533087 : Blo 531801 533087 := bstep (se 1 (by rfl) ⟨399815, by rfl⟩ : syracuseStep 533087 = 799631) B799631
theorem B533115 : Blo 531801 533115 := bstep (se 1 (by rfl) ⟨399836, by rfl⟩ : syracuseStep 533115 = 799673) B799673
theorem B1352315 : Blo 531801 1352315 := bstep (se 1 (by rfl) ⟨1014236, by rfl⟩ : syracuseStep 1352315 = 2028473) B2028473
theorem B2433671 : Blo 531801 2433671 := bstep (se 1 (by rfl) ⟨1825253, by rfl⟩ : syracuseStep 2433671 = 3650507) B3650507
theorem B7709357 : Blo 531801 7709357 := bstep (se 3 (by rfl) ⟨1445504, by rfl⟩ : syracuseStep 7709357 = 2891009) B2891009
theorem B533167 : Blo 531801 533167 := bstep (se 1 (by rfl) ⟨399875, by rfl⟩ : syracuseStep 533167 = 799751) B799751
theorem B533191 : Blo 531801 533191 := bstep (se 1 (by rfl) ⟨399893, by rfl⟩ : syracuseStep 533191 = 799787) B799787
theorem B533211 : Blo 531801 533211 := bstep (se 1 (by rfl) ⟨399908, by rfl⟩ : syracuseStep 533211 = 799817) B799817
theorem B533287 : Blo 531801 533287 := bstep (se 1 (by rfl) ⟨399965, by rfl⟩ : syracuseStep 533287 = 799931) B799931
theorem B533327 : Blo 531801 533327 := bstep (se 1 (by rfl) ⟨399995, by rfl⟩ : syracuseStep 533327 = 799991) B799991
theorem B533343 : Blo 531801 533343 := bstep (se 1 (by rfl) ⟨400007, by rfl⟩ : syracuseStep 533343 = 800015) B800015
theorem B533371 : Blo 531801 533371 := bstep (se 1 (by rfl) ⟨400028, by rfl⟩ : syracuseStep 533371 = 800057) B800057
theorem B1352609 : Blo 531801 1352609 := bstep (se 2 (by rfl) ⟨507228, by rfl⟩ : syracuseStep 1352609 = 1014457) B1014457
theorem B533423 : Blo 531801 533423 := bstep (se 1 (by rfl) ⟨400067, by rfl⟩ : syracuseStep 533423 = 800135) B800135
theorem B3089335 : Blo 531801 3089335 := bstep (se 1 (by rfl) ⟨2317001, by rfl⟩ : syracuseStep 3089335 = 4634003) B4634003
theorem B533447 : Blo 531801 533447 := bstep (se 1 (by rfl) ⟨400085, by rfl⟩ : syracuseStep 533447 = 800171) B800171
theorem B533467 : Blo 531801 533467 := bstep (se 1 (by rfl) ⟨400100, by rfl⟩ : syracuseStep 533467 = 800201) B800201
theorem B533543 : Blo 531801 533543 := bstep (se 1 (by rfl) ⟨400157, by rfl⟩ : syracuseStep 533543 = 800315) B800315
theorem B533583 : Blo 531801 533583 := bstep (se 1 (by rfl) ⟨400187, by rfl⟩ : syracuseStep 533583 = 800375) B800375
theorem B533599 : Blo 531801 533599 := bstep (se 1 (by rfl) ⟨400199, by rfl⟩ : syracuseStep 533599 = 800399) B800399
theorem B533627 : Blo 531801 533627 := bstep (se 1 (by rfl) ⟨400220, by rfl⟩ : syracuseStep 533627 = 800441) B800441
theorem B533679 : Blo 531801 533679 := bstep (se 1 (by rfl) ⟨400259, by rfl⟩ : syracuseStep 533679 = 800519) B800519
theorem B533703 : Blo 531801 533703 := bstep (se 1 (by rfl) ⟨400277, by rfl⟩ : syracuseStep 533703 = 800555) B800555
theorem B533723 : Blo 531801 533723 := bstep (se 1 (by rfl) ⟨400292, by rfl⟩ : syracuseStep 533723 = 800585) B800585
theorem B959735 : Blo 531801 959735 := bstep (se 1 (by rfl) ⟨719801, by rfl⟩ : syracuseStep 959735 = 1439603) B1439603
theorem B533799 : Blo 531801 533799 := bstep (se 1 (by rfl) ⟨400349, by rfl⟩ : syracuseStep 533799 = 800699) B800699
theorem B533839 : Blo 531801 533839 := bstep (se 1 (by rfl) ⟨400379, by rfl⟩ : syracuseStep 533839 = 800759) B800759
theorem B533855 : Blo 531801 533855 := bstep (se 1 (by rfl) ⟨400391, by rfl⟩ : syracuseStep 533855 = 800783) B800783
theorem B533883 : Blo 531801 533883 := bstep (se 1 (by rfl) ⟨400412, by rfl⟩ : syracuseStep 533883 = 800825) B800825
theorem B533935 : Blo 531801 533935 := bstep (se 1 (by rfl) ⟨400451, by rfl⟩ : syracuseStep 533935 = 800903) B800903
theorem B533959 : Blo 531801 533959 := bstep (se 1 (by rfl) ⟨400469, by rfl⟩ : syracuseStep 533959 = 800939) B800939
theorem B10298825 : Blo 531801 10298825 := bstep (se 2 (by rfl) ⟨3862059, by rfl⟩ : syracuseStep 10298825 = 7724119) B7724119
theorem B533979 : Blo 531801 533979 := bstep (se 1 (by rfl) ⟨400484, by rfl⟩ : syracuseStep 533979 = 800969) B800969
theorem B2172379 : Blo 531801 2172379 := bstep (se 1 (by rfl) ⟨1629284, by rfl⟩ : syracuseStep 2172379 = 3258569) B3258569
theorem B534055 : Blo 531801 534055 := bstep (se 1 (by rfl) ⟨400541, by rfl⟩ : syracuseStep 534055 = 801083) B801083
theorem B1025615 : Blo 531801 1025615 := bstep (se 1 (by rfl) ⟨769211, by rfl⟩ : syracuseStep 1025615 = 1538423) B1538423
theorem B534095 : Blo 531801 534095 := bstep (se 1 (by rfl) ⟨400571, by rfl⟩ : syracuseStep 534095 = 801143) B801143
theorem B534111 : Blo 531801 534111 := bstep (se 1 (by rfl) ⟨400583, by rfl⟩ : syracuseStep 534111 = 801167) B801167
theorem B534139 : Blo 531801 534139 := bstep (se 1 (by rfl) ⟨400604, by rfl⟩ : syracuseStep 534139 = 801209) B801209
theorem B534191 : Blo 531801 534191 := bstep (se 1 (by rfl) ⟨400643, by rfl⟩ : syracuseStep 534191 = 801287) B801287
theorem B1517255 : Blo 531801 1517255 := bstep (se 1 (by rfl) ⟨1137941, by rfl⟩ : syracuseStep 1517255 = 2275883) B2275883
theorem B534215 : Blo 531801 534215 := bstep (se 1 (by rfl) ⟨400661, by rfl⟩ : syracuseStep 534215 = 801323) B801323
theorem B534235 : Blo 531801 534235 := bstep (se 1 (by rfl) ⟨400676, by rfl⟩ : syracuseStep 534235 = 801353) B801353
theorem B534311 : Blo 531801 534311 := bstep (se 1 (by rfl) ⟨400733, by rfl⟩ : syracuseStep 534311 = 801467) B801467
theorem B534351 : Blo 531801 534351 := bstep (se 1 (by rfl) ⟨400763, by rfl⟩ : syracuseStep 534351 = 801527) B801527
theorem B13510489 : Blo 531801 13510489 := bstep (se 2 (by rfl) ⟨5066433, by rfl⟩ : syracuseStep 13510489 = 10132867) B10132867
theorem B534367 : Blo 531801 534367 := bstep (se 1 (by rfl) ⟨400775, by rfl⟩ : syracuseStep 534367 = 801551) B801551
theorem B534395 : Blo 531801 534395 := bstep (se 1 (by rfl) ⟨400796, by rfl⟩ : syracuseStep 534395 = 801593) B801593
theorem B534447 : Blo 531801 534447 := bstep (se 1 (by rfl) ⟨400835, by rfl⟩ : syracuseStep 534447 = 801671) B801671
theorem B534471 : Blo 531801 534471 := bstep (se 1 (by rfl) ⟨400853, by rfl⟩ : syracuseStep 534471 = 801707) B801707
theorem B534491 : Blo 531801 534491 := bstep (se 1 (by rfl) ⟨400868, by rfl⟩ : syracuseStep 534491 = 801737) B801737
theorem B7677989 : Blo 531801 7677989 := bstep (se 4 (by rfl) ⟨719811, by rfl⟩ : syracuseStep 7677989 = 1439623) B1439623
theorem B534567 : Blo 531801 534567 := bstep (se 1 (by rfl) ⟨400925, by rfl⟩ : syracuseStep 534567 = 801851) B801851
theorem B534607 : Blo 531801 534607 := bstep (se 1 (by rfl) ⟨400955, by rfl⟩ : syracuseStep 534607 = 801911) B801911
theorem B534623 : Blo 531801 534623 := bstep (se 1 (by rfl) ⟨400967, by rfl⟩ : syracuseStep 534623 = 801935) B801935
theorem B5187685 : Blo 531801 5187685 := bstep (se 4 (by rfl) ⟨486345, by rfl⟩ : syracuseStep 5187685 = 972691) B972691
theorem B600187 : Blo 531801 600187 := bstep (se 1 (by rfl) ⟨450140, by rfl⟩ : syracuseStep 600187 = 900281) B900281
theorem B534651 : Blo 531801 534651 := bstep (se 1 (by rfl) ⟨400988, by rfl⟩ : syracuseStep 534651 = 801977) B801977
theorem B534703 : Blo 531801 534703 := bstep (se 1 (by rfl) ⟨401027, by rfl⟩ : syracuseStep 534703 = 802055) B802055
theorem B534727 : Blo 531801 534727 := bstep (se 1 (by rfl) ⟨401045, by rfl⟩ : syracuseStep 534727 = 802091) B802091
theorem B534747 : Blo 531801 534747 := bstep (se 1 (by rfl) ⟨401060, by rfl⟩ : syracuseStep 534747 = 802121) B802121
theorem B534823 : Blo 531801 534823 := bstep (se 1 (by rfl) ⟨401117, by rfl⟩ : syracuseStep 534823 = 802235) B802235
theorem B534863 : Blo 531801 534863 := bstep (se 1 (by rfl) ⟨401147, by rfl⟩ : syracuseStep 534863 = 802295) B802295
theorem B534879 : Blo 531801 534879 := bstep (se 1 (by rfl) ⟨401159, by rfl⟩ : syracuseStep 534879 = 802319) B802319
theorem B534907 : Blo 531801 534907 := bstep (se 1 (by rfl) ⟨401180, by rfl⟩ : syracuseStep 534907 = 802361) B802361
theorem B4041089 : Blo 531801 4041089 := bstep (se 2 (by rfl) ⟨1515408, by rfl⟩ : syracuseStep 4041089 = 3030817) B3030817
theorem B534959 : Blo 531801 534959 := bstep (se 1 (by rfl) ⟨401219, by rfl⟩ : syracuseStep 534959 = 802439) B802439
theorem B534983 : Blo 531801 534983 := bstep (se 1 (by rfl) ⟨401237, by rfl⟩ : syracuseStep 534983 = 802475) B802475
theorem B535003 : Blo 531801 535003 := bstep (se 1 (by rfl) ⟨401252, by rfl⟩ : syracuseStep 535003 = 802505) B802505
theorem B1354279 : Blo 531801 1354279 := bstep (se 1 (by rfl) ⟨1015709, by rfl⟩ : syracuseStep 1354279 = 2031419) B2031419
theorem B535079 : Blo 531801 535079 := bstep (se 1 (by rfl) ⟨401309, by rfl⟩ : syracuseStep 535079 = 802619) B802619
theorem B600655 : Blo 531801 600655 := bstep (se 1 (by rfl) ⟨450491, by rfl⟩ : syracuseStep 600655 = 900983) B900983
theorem B535119 : Blo 531801 535119 := bstep (se 1 (by rfl) ⟨401339, by rfl⟩ : syracuseStep 535119 = 802679) B802679
theorem B535135 : Blo 531801 535135 := bstep (se 1 (by rfl) ⟨401351, by rfl⟩ : syracuseStep 535135 = 802703) B802703
theorem B535163 : Blo 531801 535163 := bstep (se 1 (by rfl) ⟨401372, by rfl⟩ : syracuseStep 535163 = 802745) B802745
theorem B535215 : Blo 531801 535215 := bstep (se 1 (by rfl) ⟨401411, by rfl⟩ : syracuseStep 535215 = 802823) B802823
theorem B535239 : Blo 531801 535239 := bstep (se 1 (by rfl) ⟨401429, by rfl⟩ : syracuseStep 535239 = 802859) B802859
theorem B535259 : Blo 531801 535259 := bstep (se 1 (by rfl) ⟨401444, by rfl⟩ : syracuseStep 535259 = 802889) B802889
theorem B535335 : Blo 531801 535335 := bstep (se 1 (by rfl) ⟨401501, by rfl⟩ : syracuseStep 535335 = 803003) B803003
theorem B535375 : Blo 531801 535375 := bstep (se 1 (by rfl) ⟨401531, by rfl⟩ : syracuseStep 535375 = 803063) B803063
theorem B535391 : Blo 531801 535391 := bstep (se 1 (by rfl) ⟨401543, by rfl⟩ : syracuseStep 535391 = 803087) B803087
theorem B1354603 : Blo 531801 1354603 := bstep (se 1 (by rfl) ⟨1015952, by rfl⟩ : syracuseStep 1354603 = 2031905) B2031905
theorem B535419 : Blo 531801 535419 := bstep (se 1 (by rfl) ⟨401564, by rfl⟩ : syracuseStep 535419 = 803129) B803129
theorem B1518497 : Blo 531801 1518497 := bstep (se 2 (by rfl) ⟨569436, by rfl⟩ : syracuseStep 1518497 = 1138873) B1138873
theorem B535471 : Blo 531801 535471 := bstep (se 1 (by rfl) ⟨401603, by rfl⟩ : syracuseStep 535471 = 803207) B803207
theorem B535495 : Blo 531801 535495 := bstep (se 1 (by rfl) ⟨401621, by rfl⟩ : syracuseStep 535495 = 803243) B803243
theorem B601051 : Blo 531801 601051 := bstep (se 1 (by rfl) ⟨450788, by rfl⟩ : syracuseStep 601051 = 901577) B901577
theorem B3419101 : Blo 531801 3419101 := bstep (se 3 (by rfl) ⟨641081, by rfl⟩ : syracuseStep 3419101 = 1282163) B1282163
theorem B535515 : Blo 531801 535515 := bstep (se 1 (by rfl) ⟨401636, by rfl⟩ : syracuseStep 535515 = 803273) B803273
theorem B797705 : Blo 531801 797705 := bstep (se 2 (by rfl) ⟨299139, by rfl⟩ : syracuseStep 797705 = 598279) B598279
theorem B797735 : Blo 531801 797735 := bstep (se 1 (by rfl) ⟨598301, by rfl⟩ : syracuseStep 797735 = 1196603) B1196603
theorem B535591 : Blo 531801 535591 := bstep (se 1 (by rfl) ⟨401693, by rfl⟩ : syracuseStep 535591 = 803387) B803387
theorem B535631 : Blo 531801 535631 := bstep (se 1 (by rfl) ⟨401723, by rfl⟩ : syracuseStep 535631 = 803447) B803447
theorem B535647 : Blo 531801 535647 := bstep (se 1 (by rfl) ⟨401735, by rfl⟩ : syracuseStep 535647 = 803471) B803471
theorem B797819 : Blo 531801 797819 := bstep (se 1 (by rfl) ⟨598364, by rfl⟩ : syracuseStep 797819 = 1196729) B1196729
theorem B535675 : Blo 531801 535675 := bstep (se 1 (by rfl) ⟨401756, by rfl⟩ : syracuseStep 535675 = 803513) B803513
theorem B535727 : Blo 531801 535727 := bstep (se 1 (by rfl) ⟨401795, by rfl⟩ : syracuseStep 535727 = 803591) B803591
theorem B535751 : Blo 531801 535751 := bstep (se 1 (by rfl) ⟨401813, by rfl⟩ : syracuseStep 535751 = 803627) B803627
theorem B535771 : Blo 531801 535771 := bstep (se 1 (by rfl) ⟨401828, by rfl⟩ : syracuseStep 535771 = 803657) B803657
theorem B797945 : Blo 531801 797945 := bstep (se 2 (by rfl) ⟨299229, by rfl⟩ : syracuseStep 797945 = 598459) B598459
theorem B798047 : Blo 531801 798047 := bstep (se 1 (by rfl) ⟨598535, by rfl⟩ : syracuseStep 798047 = 1197071) B1197071
theorem B798059 : Blo 531801 798059 := bstep (se 1 (by rfl) ⟨598544, by rfl⟩ : syracuseStep 798059 = 1197089) B1197089
theorem B601519 : Blo 531801 601519 := bstep (se 1 (by rfl) ⟨451139, by rfl⟩ : syracuseStep 601519 = 902279) B902279
theorem B1355251 : Blo 531801 1355251 := bstep (se 1 (by rfl) ⟨1016438, by rfl⟩ : syracuseStep 1355251 = 2032877) B2032877
theorem B798287 : Blo 531801 798287 := bstep (se 1 (by rfl) ⟨598715, by rfl⟩ : syracuseStep 798287 = 1197431) B1197431
theorem B1945223 : Blo 531801 1945223 := bstep (se 1 (by rfl) ⟨1458917, by rfl⟩ : syracuseStep 1945223 = 2917835) B2917835
theorem B798407 : Blo 531801 798407 := bstep (se 1 (by rfl) ⟨598805, by rfl⟩ : syracuseStep 798407 = 1197611) B1197611
theorem B601951 : Blo 531801 601951 := bstep (se 1 (by rfl) ⟨451463, by rfl⟩ : syracuseStep 601951 = 902927) B902927
theorem B798569 : Blo 531801 798569 := bstep (se 2 (by rfl) ⟨299463, by rfl⟩ : syracuseStep 798569 = 598927) B598927
theorem B798647 : Blo 531801 798647 := bstep (se 1 (by rfl) ⟨598985, by rfl⟩ : syracuseStep 798647 = 1197971) B1197971
theorem B798683 : Blo 531801 798683 := bstep (se 1 (by rfl) ⟨599012, by rfl⟩ : syracuseStep 798683 = 1198025) B1198025
theorem B6860861 : Blo 531801 6860861 := bstep (se 3 (by rfl) ⟨1286411, by rfl⟩ : syracuseStep 6860861 = 2572823) B2572823
theorem B602311 : Blo 531801 602311 := bstep (se 1 (by rfl) ⟨451733, by rfl⟩ : syracuseStep 602311 = 903467) B903467
theorem B3912065 : Blo 531801 3912065 := bstep (se 2 (by rfl) ⟨1467024, by rfl⟩ : syracuseStep 3912065 = 2934049) B2934049
theorem B799151 : Blo 531801 799151 := bstep (se 1 (by rfl) ⟨599363, by rfl⟩ : syracuseStep 799151 = 1198727) B1198727
theorem B2437613 : Blo 531801 2437613 := bstep (se 3 (by rfl) ⟨457052, by rfl⟩ : syracuseStep 2437613 = 914105) B914105
theorem B799241 : Blo 531801 799241 := bstep (se 2 (by rfl) ⟨299715, by rfl⟩ : syracuseStep 799241 = 599431) B599431
theorem B799271 : Blo 531801 799271 := bstep (se 1 (by rfl) ⟨599453, by rfl⟩ : syracuseStep 799271 = 1198907) B1198907
theorem B799355 : Blo 531801 799355 := bstep (se 1 (by rfl) ⟨599516, by rfl⟩ : syracuseStep 799355 = 1199033) B1199033
theorem B8630995 : Blo 531801 8630995 := bstep (se 1 (by rfl) ⟨6473246, by rfl⟩ : syracuseStep 8630995 = 12946493) B12946493
theorem B799481 : Blo 531801 799481 := bstep (se 2 (by rfl) ⟨299805, by rfl⟩ : syracuseStep 799481 = 599611) B599611
theorem B4338461 : Blo 531801 4338461 := bstep (se 3 (by rfl) ⟨813461, by rfl⟩ : syracuseStep 4338461 = 1626923) B1626923
theorem B799583 : Blo 531801 799583 := bstep (se 1 (by rfl) ⟨599687, by rfl⟩ : syracuseStep 799583 = 1199375) B1199375
theorem B799595 : Blo 531801 799595 := bstep (se 1 (by rfl) ⟨599696, by rfl⟩ : syracuseStep 799595 = 1199393) B1199393
theorem B2700215 : Blo 531801 2700215 := bstep (se 1 (by rfl) ⟨2025161, by rfl⟩ : syracuseStep 2700215 = 4050323) B4050323
theorem B897979 : Blo 531801 897979 := bstep (se 1 (by rfl) ⟨673484, by rfl⟩ : syracuseStep 897979 = 1346969) B1346969
theorem B4371421 : Blo 531801 4371421 := bstep (se 3 (by rfl) ⟨819641, by rfl⟩ : syracuseStep 4371421 = 1639283) B1639283
theorem B898087 : Blo 531801 898087 := bstep (se 1 (by rfl) ⟨673565, by rfl⟩ : syracuseStep 898087 = 1347131) B1347131
theorem B13874237 : Blo 531801 13874237 := bstep (se 3 (by rfl) ⟨2601419, by rfl⟩ : syracuseStep 13874237 = 5202839) B5202839
theorem B799823 : Blo 531801 799823 := bstep (se 1 (by rfl) ⟨599867, by rfl⟩ : syracuseStep 799823 = 1199735) B1199735
theorem B799943 : Blo 531801 799943 := bstep (se 1 (by rfl) ⟨599957, by rfl⟩ : syracuseStep 799943 = 1199915) B1199915
theorem B800105 : Blo 531801 800105 := bstep (se 2 (by rfl) ⟨300039, by rfl⟩ : syracuseStep 800105 = 600079) B600079
theorem B898411 : Blo 531801 898411 := bstep (se 1 (by rfl) ⟨673808, by rfl⟩ : syracuseStep 898411 = 1347617) B1347617
theorem B800183 : Blo 531801 800183 := bstep (se 1 (by rfl) ⟨600137, by rfl⟩ : syracuseStep 800183 = 1200275) B1200275
theorem B800219 : Blo 531801 800219 := bstep (se 1 (by rfl) ⟨600164, by rfl⟩ : syracuseStep 800219 = 1200329) B1200329
theorem B1521139 : Blo 531801 1521139 := bstep (se 1 (by rfl) ⟨1140854, by rfl⟩ : syracuseStep 1521139 = 2281709) B2281709
theorem B800687 : Blo 531801 800687 := bstep (se 1 (by rfl) ⟨600515, by rfl⟩ : syracuseStep 800687 = 1201031) B1201031
theorem B866231 : Blo 531801 866231 := bstep (se 1 (by rfl) ⟨649673, by rfl⟩ : syracuseStep 866231 = 1299347) B1299347
theorem B800777 : Blo 531801 800777 := bstep (se 2 (by rfl) ⟨300291, by rfl⟩ : syracuseStep 800777 = 600583) B600583
theorem B800807 : Blo 531801 800807 := bstep (se 1 (by rfl) ⟨600605, by rfl⟩ : syracuseStep 800807 = 1201211) B1201211
theorem B800891 : Blo 531801 800891 := bstep (se 1 (by rfl) ⟨600668, by rfl⟩ : syracuseStep 800891 = 1201337) B1201337
theorem B801017 : Blo 531801 801017 := bstep (se 2 (by rfl) ⟨300381, by rfl⟩ : syracuseStep 801017 = 600763) B600763
theorem B801119 : Blo 531801 801119 := bstep (se 1 (by rfl) ⟨600839, by rfl⟩ : syracuseStep 801119 = 1201679) B1201679
theorem B2701673 : Blo 531801 2701673 := bstep (se 2 (by rfl) ⟨1013127, by rfl⟩ : syracuseStep 2701673 = 2026255) B2026255
theorem B801131 : Blo 531801 801131 := bstep (se 1 (by rfl) ⟨600848, by rfl⟩ : syracuseStep 801131 = 1201697) B1201697
theorem B899471 : Blo 531801 899471 := bstep (se 1 (by rfl) ⟨674603, by rfl⟩ : syracuseStep 899471 = 1349207) B1349207
theorem B801359 : Blo 531801 801359 := bstep (se 1 (by rfl) ⟨601019, by rfl⟩ : syracuseStep 801359 = 1202039) B1202039
theorem B899707 : Blo 531801 899707 := bstep (se 1 (by rfl) ⟨674780, by rfl⟩ : syracuseStep 899707 = 1349561) B1349561
theorem B3652231 : Blo 531801 3652231 := bstep (se 1 (by rfl) ⟨2739173, by rfl⟩ : syracuseStep 3652231 = 5478347) B5478347
theorem B801479 : Blo 531801 801479 := bstep (se 1 (by rfl) ⟨601109, by rfl⟩ : syracuseStep 801479 = 1202219) B1202219
theorem B801641 : Blo 531801 801641 := bstep (se 2 (by rfl) ⟨300615, by rfl⟩ : syracuseStep 801641 = 601231) B601231
theorem B4209515 : Blo 531801 4209515 := bstep (se 1 (by rfl) ⟨3157136, by rfl⟩ : syracuseStep 4209515 = 6314273) B6314273
theorem B2112365 : Blo 531801 2112365 := bstep (se 3 (by rfl) ⟨396068, by rfl⟩ : syracuseStep 2112365 = 792137) B792137
theorem B801719 : Blo 531801 801719 := bstep (se 1 (by rfl) ⟨601289, by rfl⟩ : syracuseStep 801719 = 1202579) B1202579
theorem B539591 : Blo 531801 539591 := bstep (se 1 (by rfl) ⟨404693, by rfl⟩ : syracuseStep 539591 = 809387) B809387
theorem B801755 : Blo 531801 801755 := bstep (se 1 (by rfl) ⟨601316, by rfl⟩ : syracuseStep 801755 = 1202633) B1202633
theorem B2046995 : Blo 531801 2046995 := bstep (se 1 (by rfl) ⟨1535246, by rfl⟩ : syracuseStep 2046995 = 3070493) B3070493
theorem B1522745 : Blo 531801 1522745 := bstep (se 2 (by rfl) ⟨571029, by rfl⟩ : syracuseStep 1522745 = 1142059) B1142059
theorem B2276599 : Blo 531801 2276599 := bstep (se 1 (by rfl) ⟨1707449, by rfl⟩ : syracuseStep 2276599 = 3414899) B3414899
theorem B1523087 : Blo 531801 1523087 := bstep (se 1 (by rfl) ⟨1142315, by rfl⟩ : syracuseStep 1523087 = 2284631) B2284631
theorem B802223 : Blo 531801 802223 := bstep (se 1 (by rfl) ⟨601667, by rfl⟩ : syracuseStep 802223 = 1203335) B1203335
theorem B900571 : Blo 531801 900571 := bstep (se 1 (by rfl) ⟨675428, by rfl⟩ : syracuseStep 900571 = 1350857) B1350857
theorem B802313 : Blo 531801 802313 := bstep (se 2 (by rfl) ⟨300867, by rfl⟩ : syracuseStep 802313 = 601735) B601735
theorem B802343 : Blo 531801 802343 := bstep (se 1 (by rfl) ⟨601757, by rfl⟩ : syracuseStep 802343 = 1203515) B1203515
theorem B802427 : Blo 531801 802427 := bstep (se 1 (by rfl) ⟨601820, by rfl⟩ : syracuseStep 802427 = 1203641) B1203641
theorem B802553 : Blo 531801 802553 := bstep (se 2 (by rfl) ⟨300957, by rfl⟩ : syracuseStep 802553 = 601915) B601915
theorem B802655 : Blo 531801 802655 := bstep (se 1 (by rfl) ⟨601991, by rfl⟩ : syracuseStep 802655 = 1203983) B1203983
theorem B802667 : Blo 531801 802667 := bstep (se 1 (by rfl) ⟨602000, by rfl⟩ : syracuseStep 802667 = 1204001) B1204001
theorem B23117683 : Blo 531801 23117683 := bstep (se 1 (by rfl) ⟨17338262, by rfl⟩ : syracuseStep 23117683 = 34676525) B34676525
theorem B901199 : Blo 531801 901199 := bstep (se 1 (by rfl) ⟨675899, by rfl⟩ : syracuseStep 901199 = 1351799) B1351799
theorem B802895 : Blo 531801 802895 := bstep (se 1 (by rfl) ⟨602171, by rfl⟩ : syracuseStep 802895 = 1204343) B1204343
theorem B803015 : Blo 531801 803015 := bstep (se 1 (by rfl) ⟨602261, by rfl⟩ : syracuseStep 803015 = 1204523) B1204523
theorem B11583755 : Blo 531801 11583755 := bstep (se 1 (by rfl) ⟨8687816, by rfl⟩ : syracuseStep 11583755 = 17375633) B17375633
theorem B3948851 : Blo 531801 3948851 := bstep (se 1 (by rfl) ⟨2961638, by rfl⟩ : syracuseStep 3948851 = 5923277) B5923277
theorem B2572631 : Blo 531801 2572631 := bstep (se 1 (by rfl) ⟨1929473, by rfl⟩ : syracuseStep 2572631 = 3858947) B3858947
theorem B803177 : Blo 531801 803177 := bstep (se 2 (by rfl) ⟨301191, by rfl⟩ : syracuseStep 803177 = 602383) B602383
theorem B803255 : Blo 531801 803255 := bstep (se 1 (by rfl) ⟨602441, by rfl⟩ : syracuseStep 803255 = 1204883) B1204883
theorem B803291 : Blo 531801 803291 := bstep (se 1 (by rfl) ⟨602468, by rfl⟩ : syracuseStep 803291 = 1204937) B1204937
theorem B541279 : Blo 531801 541279 := bstep (se 1 (by rfl) ⟨405959, by rfl⟩ : syracuseStep 541279 = 811919) B811919
theorem B869063 : Blo 531801 869063 := bstep (se 1 (by rfl) ⟨651797, by rfl⟩ : syracuseStep 869063 = 1303595) B1303595
theorem B8798989 : Blo 531801 8798989 := bstep (se 3 (by rfl) ⟨1649810, by rfl⟩ : syracuseStep 8798989 = 3299621) B3299621
theorem B8209201 : Blo 531801 8209201 := bstep (se 2 (by rfl) ⟨3078450, by rfl⟩ : syracuseStep 8209201 = 6156901) B6156901
theorem B1196873 : Blo 531801 1196873 := bstep (se 2 (by rfl) ⟨448827, by rfl⟩ : syracuseStep 1196873 = 897655) B897655
theorem B902063 : Blo 531801 902063 := bstep (se 1 (by rfl) ⟨676547, by rfl⟩ : syracuseStep 902063 = 1353095) B1353095
theorem B541895 : Blo 531801 541895 := bstep (se 1 (by rfl) ⟨406421, by rfl⟩ : syracuseStep 541895 = 812843) B812843
theorem B902495 : Blo 531801 902495 := bstep (se 1 (by rfl) ⟨676871, by rfl⟩ : syracuseStep 902495 = 1353743) B1353743
theorem B6079859 : Blo 531801 6079859 := bstep (se 1 (by rfl) ⟨4559894, by rfl⟩ : syracuseStep 6079859 = 9119789) B9119789
theorem B1197665 : Blo 531801 1197665 := bstep (se 2 (by rfl) ⟨449124, by rfl⟩ : syracuseStep 1197665 = 898249) B898249
theorem B1525387 : Blo 531801 1525387 := bstep (se 1 (by rfl) ⟨1144040, by rfl⟩ : syracuseStep 1525387 = 2288081) B2288081
theorem B607943 : Blo 531801 607943 := bstep (se 1 (by rfl) ⟨455957, by rfl⟩ : syracuseStep 607943 = 911915) B911915
theorem B903055 : Blo 531801 903055 := bstep (se 1 (by rfl) ⟨677291, by rfl⟩ : syracuseStep 903055 = 1354583) B1354583
theorem B24692633 : Blo 531801 24692633 := bstep (se 2 (by rfl) ⟨9259737, by rfl⟩ : syracuseStep 24692633 = 18519475) B18519475
theorem B1198007 : Blo 531801 1198007 := bstep (se 1 (by rfl) ⟨898505, by rfl⟩ : syracuseStep 1198007 = 1797011) B1797011
theorem B673915 : Blo 531801 673915 := bstep (se 1 (by rfl) ⟨505436, by rfl⟩ : syracuseStep 673915 = 1010873) B1010873
theorem B3426461 : Blo 531801 3426461 := bstep (se 3 (by rfl) ⟨642461, by rfl⟩ : syracuseStep 3426461 = 1284923) B1284923
theorem B8636705 : Blo 531801 8636705 := bstep (se 2 (by rfl) ⟨3238764, by rfl⟩ : syracuseStep 8636705 = 6477529) B6477529
theorem B543071 : Blo 531801 543071 := bstep (se 1 (by rfl) ⟨407303, by rfl⟩ : syracuseStep 543071 = 814607) B814607
theorem B6834617 : Blo 531801 6834617 := bstep (se 2 (by rfl) ⟨2562981, by rfl⟩ : syracuseStep 6834617 = 5125963) B5125963
theorem B8243693 : Blo 531801 8243693 := bstep (se 3 (by rfl) ⟨1545692, by rfl⟩ : syracuseStep 8243693 = 3091385) B3091385
theorem B1198601 : Blo 531801 1198601 := bstep (se 2 (by rfl) ⟨449475, by rfl⟩ : syracuseStep 1198601 = 898951) B898951
theorem B903737 : Blo 531801 903737 := bstep (se 2 (by rfl) ⟨338901, by rfl⟩ : syracuseStep 903737 = 677803) B677803
theorem B6933127 : Blo 531801 6933127 := bstep (se 1 (by rfl) ⟨5199845, by rfl⟩ : syracuseStep 6933127 = 10399691) B10399691
theorem B2738947 : Blo 531801 2738947 := bstep (se 1 (by rfl) ⟨2054210, by rfl⟩ : syracuseStep 2738947 = 4108421) B4108421
theorem B2280221 : Blo 531801 2280221 := bstep (se 3 (by rfl) ⟨427541, by rfl⟩ : syracuseStep 2280221 = 855083) B855083
theorem B1198943 : Blo 531801 1198943 := bstep (se 1 (by rfl) ⟨899207, by rfl⟩ : syracuseStep 1198943 = 1798415) B1798415
theorem B1199123 : Blo 531801 1199123 := bstep (se 1 (by rfl) ⟨899342, by rfl⟩ : syracuseStep 1199123 = 1798685) B1798685
theorem B2247875 : Blo 531801 2247875 := bstep (se 1 (by rfl) ⟨1685906, by rfl⟩ : syracuseStep 2247875 = 3371813) B3371813
theorem B1199465 : Blo 531801 1199465 := bstep (se 2 (by rfl) ⟨449799, by rfl⟩ : syracuseStep 1199465 = 899599) B899599
theorem B2280905 : Blo 531801 2280905 := bstep (se 2 (by rfl) ⟨855339, by rfl⟩ : syracuseStep 2280905 = 1710679) B1710679
theorem B2739851 : Blo 531801 2739851 := bstep (se 1 (by rfl) ⟨2054888, by rfl⟩ : syracuseStep 2739851 = 4109777) B4109777
theorem B55529333 : Blo 531801 55529333 := bstep (se 5 (by rfl) ⟨2602937, by rfl⟩ : syracuseStep 55529333 = 5205875) B5205875
theorem B8245111 : Blo 531801 8245111 := bstep (se 1 (by rfl) ⟨6183833, by rfl⟩ : syracuseStep 8245111 = 12367667) B12367667
theorem B1200059 : Blo 531801 1200059 := bstep (se 1 (by rfl) ⟨900044, by rfl⟩ : syracuseStep 1200059 = 1800089) B1800089
theorem B675803 : Blo 531801 675803 := bstep (se 1 (by rfl) ⟨506852, by rfl⟩ : syracuseStep 675803 = 1013705) B1013705
theorem B1200185 : Blo 531801 1200185 := bstep (se 2 (by rfl) ⟨450069, by rfl⟩ : syracuseStep 1200185 = 900139) B900139
theorem B26726597 : Blo 531801 26726597 := bstep (se 4 (by rfl) ⟨2505618, by rfl⟩ : syracuseStep 26726597 = 5011237) B5011237
theorem B1200527 : Blo 531801 1200527 := bstep (se 1 (by rfl) ⟨900395, by rfl⟩ : syracuseStep 1200527 = 1800791) B1800791
theorem B676279 : Blo 531801 676279 := bstep (se 1 (by rfl) ⟨507209, by rfl⟩ : syracuseStep 676279 = 1014419) B1014419
theorem B2019937 : Blo 531801 2019937 := bstep (se 2 (by rfl) ⟨757476, by rfl⟩ : syracuseStep 2019937 = 1514953) B1514953
theorem B2708153 : Blo 531801 2708153 := bstep (se 2 (by rfl) ⟨1015557, by rfl⟩ : syracuseStep 2708153 = 2031115) B2031115
theorem B1200851 : Blo 531801 1200851 := bstep (se 1 (by rfl) ⟨900638, by rfl⟩ : syracuseStep 1200851 = 1801277) B1801277
theorem B5493577 : Blo 531801 5493577 := bstep (se 2 (by rfl) ⟨2060091, by rfl⟩ : syracuseStep 5493577 = 4120183) B4120183
theorem B2020409 : Blo 531801 2020409 := bstep (se 2 (by rfl) ⟨757653, by rfl⟩ : syracuseStep 2020409 = 1515307) B1515307
theorem B1201787 : Blo 531801 1201787 := bstep (se 1 (by rfl) ⟨901340, by rfl⟩ : syracuseStep 1201787 = 1802681) B1802681
theorem B35149463 : Blo 531801 35149463 := bstep (se 1 (by rfl) ⟨26362097, by rfl⟩ : syracuseStep 35149463 = 52724195) B52724195
theorem B677575 : Blo 531801 677575 := bstep (se 1 (by rfl) ⟨508181, by rfl⟩ : syracuseStep 677575 = 1016363) B1016363
theorem B4314845 : Blo 531801 4314845 := bstep (se 3 (by rfl) ⟨809033, by rfl⟩ : syracuseStep 4314845 = 1618067) B1618067
theorem B1201913 : Blo 531801 1201913 := bstep (se 2 (by rfl) ⟨450717, by rfl⟩ : syracuseStep 1201913 = 901435) B901435
theorem B1202183 : Blo 531801 1202183 := bstep (se 1 (by rfl) ⟨901637, by rfl⟩ : syracuseStep 1202183 = 1803275) B1803275
theorem B2021395 : Blo 531801 2021395 := bstep (se 1 (by rfl) ⟨1516046, by rfl⟩ : syracuseStep 2021395 = 3032093) B3032093
theorem B1202255 : Blo 531801 1202255 := bstep (se 1 (by rfl) ⟨901691, by rfl⟩ : syracuseStep 1202255 = 1803383) B1803383
theorem B1202651 : Blo 531801 1202651 := bstep (se 1 (by rfl) ⟨901988, by rfl⟩ : syracuseStep 1202651 = 1803977) B1803977
theorem B1465031 : Blo 531801 1465031 := bstep (se 1 (by rfl) ⟨1098773, by rfl⟩ : syracuseStep 1465031 = 2197547) B2197547
theorem B1203119 : Blo 531801 1203119 := bstep (se 1 (by rfl) ⟨902339, by rfl⟩ : syracuseStep 1203119 = 1804679) B1804679
theorem B6511589 : Blo 531801 6511589 := bstep (se 4 (by rfl) ⟨610461, by rfl⟩ : syracuseStep 6511589 = 1220923) B1220923
theorem B3857561 : Blo 531801 3857561 := bstep (se 2 (by rfl) ⟨1446585, by rfl⟩ : syracuseStep 3857561 = 2893171) B2893171
theorem B1203371 : Blo 531801 1203371 := bstep (se 1 (by rfl) ⟨902528, by rfl⟩ : syracuseStep 1203371 = 1805057) B1805057
theorem B4054211 : Blo 531801 4054211 := bstep (se 1 (by rfl) ⟨3040658, by rfl⟩ : syracuseStep 4054211 = 6081317) B6081317
theorem B7691543 : Blo 531801 7691543 := bstep (se 1 (by rfl) ⟨5768657, by rfl⟩ : syracuseStep 7691543 = 11537315) B11537315
theorem B1203911 : Blo 531801 1203911 := bstep (se 1 (by rfl) ⟨902933, by rfl⟩ : syracuseStep 1203911 = 1805867) B1805867
theorem B2023127 : Blo 531801 2023127 := bstep (se 1 (by rfl) ⟨1517345, by rfl⟩ : syracuseStep 2023127 = 3034691) B3034691
theorem B1236809 : Blo 531801 1236809 := bstep (se 2 (by rfl) ⟨463803, by rfl⟩ : syracuseStep 1236809 = 927607) B927607
theorem B3858461 : Blo 531801 3858461 := bstep (se 3 (by rfl) ⟨723461, by rfl⟩ : syracuseStep 3858461 = 1446923) B1446923
theorem B4546637 : Blo 531801 4546637 := bstep (se 3 (by rfl) ⟨852494, by rfl⟩ : syracuseStep 4546637 = 1704989) B1704989
theorem B811529 : Blo 531801 811529 := bstep (se 2 (by rfl) ⟨304323, by rfl⟩ : syracuseStep 811529 = 608647) B608647
theorem B1204775 : Blo 531801 1204775 := bstep (se 1 (by rfl) ⟨903581, by rfl⟩ : syracuseStep 1204775 = 1807163) B1807163
theorem B1205099 : Blo 531801 1205099 := bstep (se 1 (by rfl) ⟨903824, by rfl⟩ : syracuseStep 1205099 = 1807649) B1807649
theorem B2024311 : Blo 531801 2024311 := bstep (se 1 (by rfl) ⟨1518233, by rfl⟩ : syracuseStep 2024311 = 3036467) B3036467
theorem B1205153 : Blo 531801 1205153 := bstep (se 2 (by rfl) ⟨451932, by rfl⟩ : syracuseStep 1205153 = 903865) B903865
theorem B1795229 : Blo 531801 1795229 := bstep (se 3 (by rfl) ⟨336605, by rfl⟩ : syracuseStep 1795229 = 673211) B673211
theorem B1205495 : Blo 531801 1205495 := bstep (se 1 (by rfl) ⟨904121, by rfl⟩ : syracuseStep 1205495 = 1808243) B1808243
theorem B648631 : Blo 531801 648631 := bstep (se 1 (by rfl) ⟨486473, by rfl⟩ : syracuseStep 648631 = 972947) B972947
theorem B8349169 : Blo 531801 8349169 := bstep (se 2 (by rfl) ⟨3130938, by rfl⟩ : syracuseStep 8349169 = 6261877) B6261877
theorem B1795769 : Blo 531801 1795769 := bstep (se 2 (by rfl) ⟨673413, by rfl⟩ : syracuseStep 1795769 = 1346827) B1346827
theorem B6153943 : Blo 531801 6153943 := bstep (se 1 (by rfl) ⟨4615457, by rfl⟩ : syracuseStep 6153943 = 9230915) B9230915
theorem B2025283 : Blo 531801 2025283 := bstep (se 1 (by rfl) ⟨1518962, by rfl⟩ : syracuseStep 2025283 = 3037925) B3037925
theorem B1140743 : Blo 531801 1140743 := bstep (se 1 (by rfl) ⟨855557, by rfl⟩ : syracuseStep 1140743 = 1711115) B1711115
theorem B3860561 : Blo 531801 3860561 := bstep (se 2 (by rfl) ⟨1447710, by rfl⟩ : syracuseStep 3860561 = 2895421) B2895421
theorem B2025587 : Blo 531801 2025587 := bstep (se 1 (by rfl) ⟨1519190, by rfl⟩ : syracuseStep 2025587 = 3038381) B3038381
theorem B1796363 : Blo 531801 1796363 := bstep (se 1 (by rfl) ⟨1347272, by rfl⟩ : syracuseStep 1796363 = 2694545) B2694545
theorem B1796633 : Blo 531801 1796633 := bstep (se 2 (by rfl) ⟨673737, by rfl⟩ : syracuseStep 1796633 = 1347475) B1347475
theorem B2026043 : Blo 531801 2026043 := bstep (se 1 (by rfl) ⟨1519532, by rfl⟩ : syracuseStep 2026043 = 3039065) B3039065
theorem B7825997 : Blo 531801 7825997 := bstep (se 3 (by rfl) ⟨1467374, by rfl⟩ : syracuseStep 7825997 = 2934749) B2934749
theorem B1010387 : Blo 531801 1010387 := bstep (se 1 (by rfl) ⟨757790, by rfl⟩ : syracuseStep 1010387 = 1515581) B1515581
theorem B1830059 : Blo 531801 1830059 := bstep (se 1 (by rfl) ⟨1372544, by rfl⟩ : syracuseStep 1830059 = 2745089) B2745089
theorem B1011017 : Blo 531801 1011017 := bstep (se 2 (by rfl) ⟨379131, by rfl⟩ : syracuseStep 1011017 = 758263) B758263
theorem B3665371 : Blo 531801 3665371 := bstep (se 1 (by rfl) ⟨2749028, by rfl⟩ : syracuseStep 3665371 = 5498057) B5498057
theorem B1797767 : Blo 531801 1797767 := bstep (se 1 (by rfl) ⟨1348325, by rfl⟩ : syracuseStep 1797767 = 2696651) B2696651
theorem B1797821 : Blo 531801 1797821 := bstep (se 3 (by rfl) ⟨337091, by rfl⟩ : syracuseStep 1797821 = 674183) B674183
theorem B1797983 : Blo 531801 1797983 := bstep (se 1 (by rfl) ⟨1348487, by rfl⟩ : syracuseStep 1797983 = 2696975) B2696975
theorem B1798145 : Blo 531801 1798145 := bstep (se 2 (by rfl) ⟨674304, by rfl⟩ : syracuseStep 1798145 = 1348609) B1348609
theorem B1011791 : Blo 531801 1011791 := bstep (se 1 (by rfl) ⟨758843, by rfl⟩ : syracuseStep 1011791 = 1517687) B1517687
theorem B1929851 : Blo 531801 1929851 := bstep (se 1 (by rfl) ⟨1447388, by rfl⟩ : syracuseStep 1929851 = 2894777) B2894777
theorem B2159243 : Blo 531801 2159243 := bstep (se 1 (by rfl) ⟨1619432, by rfl⟩ : syracuseStep 2159243 = 3238865) B3238865
theorem B6091523 : Blo 531801 6091523 := bstep (se 1 (by rfl) ⟨4568642, by rfl⟩ : syracuseStep 6091523 = 9137285) B9137285
theorem B1798955 : Blo 531801 1798955 := bstep (se 1 (by rfl) ⟨1349216, by rfl⟩ : syracuseStep 1798955 = 2698433) B2698433
theorem B1799225 : Blo 531801 1799225 := bstep (se 2 (by rfl) ⟨674709, by rfl⟩ : syracuseStep 1799225 = 1349419) B1349419
theorem B5141569 : Blo 531801 5141569 := bstep (se 2 (by rfl) ⟨1928088, by rfl⟩ : syracuseStep 5141569 = 3856177) B3856177
theorem B1537103 : Blo 531801 1537103 := bstep (se 1 (by rfl) ⟨1152827, by rfl⟩ : syracuseStep 1537103 = 2305655) B2305655
theorem B1799549 : Blo 531801 1799549 := bstep (se 3 (by rfl) ⟨337415, by rfl⟩ : syracuseStep 1799549 = 674831) B674831
theorem B1832507 : Blo 531801 1832507 := bstep (se 1 (by rfl) ⟨1374380, by rfl⟩ : syracuseStep 1832507 = 2748761) B2748761
theorem B1799819 : Blo 531801 1799819 := bstep (se 1 (by rfl) ⟨1349864, by rfl⟩ : syracuseStep 1799819 = 2699729) B2699729
theorem B1013447 : Blo 531801 1013447 := bstep (se 1 (by rfl) ⟨760085, by rfl⟩ : syracuseStep 1013447 = 1520171) B1520171
theorem B3045215 : Blo 531801 3045215 := bstep (se 1 (by rfl) ⟨2283911, by rfl⟩ : syracuseStep 3045215 = 4567823) B4567823
theorem B1013971 : Blo 531801 1013971 := bstep (se 1 (by rfl) ⟨760478, by rfl⟩ : syracuseStep 1013971 = 1520957) B1520957
theorem B4061501 : Blo 531801 4061501 := bstep (se 3 (by rfl) ⟨761531, by rfl⟩ : syracuseStep 4061501 = 1523063) B1523063
theorem B1014191 : Blo 531801 1014191 := bstep (se 1 (by rfl) ⟨760643, by rfl⟩ : syracuseStep 1014191 = 1521287) B1521287
theorem B1800737 : Blo 531801 1800737 := bstep (se 2 (by rfl) ⟨675276, by rfl⟩ : syracuseStep 1800737 = 1350553) B1350553
theorem B1440445 : Blo 531801 1440445 := bstep (se 3 (by rfl) ⟨270083, by rfl⟩ : syracuseStep 1440445 = 540167) B540167
theorem B1800953 : Blo 531801 1800953 := bstep (se 2 (by rfl) ⟨675357, by rfl⟩ : syracuseStep 1800953 = 1350715) B1350715
theorem B1014601 : Blo 531801 1014601 := bstep (se 2 (by rfl) ⟨380475, by rfl⟩ : syracuseStep 1014601 = 760951) B760951
theorem B1801223 : Blo 531801 1801223 := bstep (se 1 (by rfl) ⟨1350917, by rfl⟩ : syracuseStep 1801223 = 2701835) B2701835
theorem B1801331 : Blo 531801 1801331 := bstep (se 1 (by rfl) ⟨1350998, by rfl⟩ : syracuseStep 1801331 = 2701997) B2701997
theorem B1801601 : Blo 531801 1801601 := bstep (se 2 (by rfl) ⟨675600, by rfl⟩ : syracuseStep 1801601 = 1351201) B1351201
theorem B2162209 : Blo 531801 2162209 := bstep (se 2 (by rfl) ⟨810828, by rfl⟩ : syracuseStep 2162209 = 1621657) B1621657
theorem B5471783 : Blo 531801 5471783 := bstep (se 1 (by rfl) ⟨4103837, by rfl⟩ : syracuseStep 5471783 = 8207675) B8207675
theorem B2031389 : Blo 531801 2031389 := bstep (se 3 (by rfl) ⟨380885, by rfl⟩ : syracuseStep 2031389 = 761771) B761771
theorem B7700359 : Blo 531801 7700359 := bstep (se 1 (by rfl) ⟨5775269, by rfl⟩ : syracuseStep 7700359 = 11550539) B11550539
theorem B3407825 : Blo 531801 3407825 := bstep (se 2 (by rfl) ⟨1277934, by rfl⟩ : syracuseStep 3407825 = 2555869) B2555869
theorem B1802249 : Blo 531801 1802249 := bstep (se 2 (by rfl) ⟨675843, by rfl⟩ : syracuseStep 1802249 = 1351687) B1351687
theorem B1278281 : Blo 531801 1278281 := bstep (se 2 (by rfl) ⟨479355, by rfl⟩ : syracuseStep 1278281 = 958711) B958711
theorem B2556467 : Blo 531801 2556467 := bstep (se 1 (by rfl) ⟨1917350, by rfl⟩ : syracuseStep 2556467 = 3834701) B3834701
theorem B721705 : Blo 531801 721705 := bstep (se 2 (by rfl) ⟨270639, by rfl⟩ : syracuseStep 721705 = 541279) B541279
theorem B2884571 : Blo 531801 2884571 := bstep (se 1 (by rfl) ⟨2163428, by rfl⟩ : syracuseStep 2884571 = 4326857) B4326857
theorem B11731985 : Blo 531801 11731985 := bstep (se 2 (by rfl) ⟨4399494, by rfl⟩ : syracuseStep 11731985 = 8798989) B8798989
theorem B10945601 : Blo 531801 10945601 := bstep (se 2 (by rfl) ⟨4104600, by rfl⟩ : syracuseStep 10945601 = 8209201) B8209201
theorem B853135 : Blo 531801 853135 := bstep (se 1 (by rfl) ⟨639851, by rfl⟩ : syracuseStep 853135 = 1279703) B1279703
theorem B722299 : Blo 531801 722299 := bstep (se 1 (by rfl) ⟨541724, by rfl⟩ : syracuseStep 722299 = 1083449) B1083449
theorem B2426375 : Blo 531801 2426375 := bstep (se 1 (by rfl) ⟨1819781, by rfl⟩ : syracuseStep 2426375 = 3639563) B3639563
theorem B3409465 : Blo 531801 3409465 := bstep (se 2 (by rfl) ⟨1278549, by rfl⟩ : syracuseStep 3409465 = 2557099) B2557099
theorem B4556411 : Blo 531801 4556411 := bstep (se 1 (by rfl) ⟨3417308, by rfl⟩ : syracuseStep 4556411 = 6834617) B6834617
theorem B4064903 : Blo 531801 4064903 := bstep (se 1 (by rfl) ⟨3048677, by rfl⟩ : syracuseStep 4064903 = 6097355) B6097355
theorem B11569229 : Blo 531801 11569229 := bstep (se 3 (by rfl) ⟨2169230, by rfl⟩ : syracuseStep 11569229 = 4338461) B4338461
theorem B2033849 : Blo 531801 2033849 := bstep (se 2 (by rfl) ⟨762693, by rfl⟩ : syracuseStep 2033849 = 1525387) B1525387
theorem B2034031 : Blo 531801 2034031 := bstep (se 1 (by rfl) ⟨1525523, by rfl⟩ : syracuseStep 2034031 = 3051047) B3051047
theorem B1706771 : Blo 531801 1706771 := bstep (se 1 (by rfl) ⟨1280078, by rfl⟩ : syracuseStep 1706771 = 2560157) B2560157
theorem B6916913 : Blo 531801 6916913 := bstep (se 2 (by rfl) ⟨2593842, by rfl⟩ : syracuseStep 6916913 = 5187685) B5187685
theorem B1805435 : Blo 531801 1805435 := bstep (se 1 (by rfl) ⟨1354076, by rfl⟩ : syracuseStep 1805435 = 2708153) B2708153
theorem B1445053 : Blo 531801 1445053 := bstep (se 3 (by rfl) ⟨270947, by rfl⟩ : syracuseStep 1445053 = 541895) B541895
theorem B2886943 : Blo 531801 2886943 := bstep (se 1 (by rfl) ⟨2165207, by rfl⟩ : syracuseStep 2886943 = 4330415) B4330415
theorem B1445159 : Blo 531801 1445159 := bstep (se 1 (by rfl) ⟨1083869, by rfl⟩ : syracuseStep 1445159 = 2167739) B2167739
theorem B1346939 : Blo 531801 1346939 := bstep (se 1 (by rfl) ⟨1010204, by rfl⟩ : syracuseStep 1346939 = 2020409) B2020409
theorem B1805705 : Blo 531801 1805705 := bstep (se 2 (by rfl) ⟨677139, by rfl⟩ : syracuseStep 1805705 = 1354279) B1354279
theorem B9244169 : Blo 531801 9244169 := bstep (se 2 (by rfl) ⟨3466563, by rfl⟩ : syracuseStep 9244169 = 6933127) B6933127
theorem B23432975 : Blo 531801 23432975 := bstep (se 1 (by rfl) ⟨17574731, by rfl⟩ : syracuseStep 23432975 = 35149463) B35149463
theorem B1806137 : Blo 531801 1806137 := bstep (se 2 (by rfl) ⟨677301, by rfl⟩ : syracuseStep 1806137 = 1354603) B1354603
theorem B4558801 : Blo 531801 4558801 := bstep (se 2 (by rfl) ⟨1709550, by rfl⟩ : syracuseStep 4558801 = 3419101) B3419101
theorem B5836859 : Blo 531801 5836859 := bstep (se 1 (by rfl) ⟨4377644, by rfl⟩ : syracuseStep 5836859 = 8755289) B8755289
theorem B15405227 : Blo 531801 15405227 := bstep (se 1 (by rfl) ⟨11553920, by rfl⟩ : syracuseStep 15405227 = 23107841) B23107841
theorem B2888243 : Blo 531801 2888243 := bstep (se 1 (by rfl) ⟨2166182, by rfl⟩ : syracuseStep 2888243 = 4332365) B4332365
theorem B4887161 : Blo 531801 4887161 := bstep (se 2 (by rfl) ⟨1832685, by rfl⟩ : syracuseStep 4887161 = 3665371) B3665371
theorem B1807001 : Blo 531801 1807001 := bstep (se 2 (by rfl) ⟨677625, by rfl⟩ : syracuseStep 1807001 = 1355251) B1355251
theorem B4068305 : Blo 531801 4068305 := bstep (se 2 (by rfl) ⟨1525614, by rfl⟩ : syracuseStep 4068305 = 3051229) B3051229
theorem B1348751 : Blo 531801 1348751 := bstep (se 1 (by rfl) ⟨1011563, by rfl⟩ : syracuseStep 1348751 = 2023127) B2023127
theorem B2692439 : Blo 531801 2692439 := bstep (se 1 (by rfl) ⟨2019329, by rfl⟩ : syracuseStep 2692439 = 4038659) B4038659
theorem B2693249 : Blo 531801 2693249 := bstep (se 2 (by rfl) ⟨1009968, by rfl⟩ : syracuseStep 2693249 = 2019937) B2019937
theorem B1448189 : Blo 531801 1448189 := bstep (se 3 (by rfl) ⟨271535, by rfl⟩ : syracuseStep 1448189 = 543071) B543071
theorem B11507993 : Blo 531801 11507993 := bstep (se 2 (by rfl) ⟨4315497, by rfl⟩ : syracuseStep 11507993 = 8630995) B8630995
theorem B5118659 : Blo 531801 5118659 := bstep (se 1 (by rfl) ⟨3838994, by rfl⟩ : syracuseStep 5118659 = 7677989) B7677989
theorem B1350391 : Blo 531801 1350391 := bstep (se 1 (by rfl) ⟨1012793, by rfl⟩ : syracuseStep 1350391 = 2025587) B2025587
theorem B6855425 : Blo 531801 6855425 := bstep (se 2 (by rfl) ⟨2570784, by rfl⟩ : syracuseStep 6855425 = 5141569) B5141569
theorem B2694059 : Blo 531801 2694059 := bstep (se 1 (by rfl) ⟨2020544, by rfl⟩ : syracuseStep 2694059 = 4041089) B4041089
theorem B1350695 : Blo 531801 1350695 := bstep (se 1 (by rfl) ⟨1013021, by rfl⟩ : syracuseStep 1350695 = 2026043) B2026043
theorem B5217331 : Blo 531801 5217331 := bstep (se 1 (by rfl) ⟨3912998, by rfl⟩ : syracuseStep 5217331 = 7825997) B7825997
theorem B3906749 : Blo 531801 3906749 := bstep (se 3 (by rfl) ⟨732515, by rfl⟩ : syracuseStep 3906749 = 1465031) B1465031
theorem B531803 : Blo 531801 531803 := bstep (se 1 (by rfl) ⟨398852, by rfl⟩ : syracuseStep 531803 = 797705) B797705
theorem B531823 : Blo 531801 531823 := bstep (se 1 (by rfl) ⟨398867, by rfl⟩ : syracuseStep 531823 = 797735) B797735
theorem B531879 : Blo 531801 531879 := bstep (se 1 (by rfl) ⟨398909, by rfl⟩ : syracuseStep 531879 = 797819) B797819
theorem B1220039 : Blo 531801 1220039 := bstep (se 1 (by rfl) ⟨915029, by rfl⟩ : syracuseStep 1220039 = 1830059) B1830059
theorem B531963 : Blo 531801 531963 := bstep (se 1 (by rfl) ⟨398972, by rfl⟩ : syracuseStep 531963 = 797945) B797945
theorem B532031 : Blo 531801 532031 := bstep (se 1 (by rfl) ⟨399023, by rfl⟩ : syracuseStep 532031 = 798047) B798047
theorem B532039 : Blo 531801 532039 := bstep (se 1 (by rfl) ⟨399029, by rfl⟩ : syracuseStep 532039 = 798059) B798059
theorem B532191 : Blo 531801 532191 := bstep (se 1 (by rfl) ⟨399143, by rfl⟩ : syracuseStep 532191 = 798287) B798287
theorem B532271 : Blo 531801 532271 := bstep (se 1 (by rfl) ⟨399203, by rfl⟩ : syracuseStep 532271 = 798407) B798407
theorem B532379 : Blo 531801 532379 := bstep (se 1 (by rfl) ⟨399284, by rfl⟩ : syracuseStep 532379 = 798569) B798569
theorem B532431 : Blo 531801 532431 := bstep (se 1 (by rfl) ⟨399323, by rfl⟩ : syracuseStep 532431 = 798647) B798647
theorem B532455 : Blo 531801 532455 := bstep (se 1 (by rfl) ⟨399341, by rfl⟩ : syracuseStep 532455 = 798683) B798683
theorem B5120009 : Blo 531801 5120009 := bstep (se 2 (by rfl) ⟨1920003, by rfl⟩ : syracuseStep 5120009 = 3840007) B3840007
theorem B2695193 : Blo 531801 2695193 := bstep (se 2 (by rfl) ⟨1010697, by rfl⟩ : syracuseStep 2695193 = 2021395) B2021395
theorem B1351961 : Blo 531801 1351961 := bstep (se 2 (by rfl) ⟨506985, by rfl⟩ : syracuseStep 1351961 = 1013971) B1013971
theorem B532767 : Blo 531801 532767 := bstep (se 1 (by rfl) ⟨399575, by rfl⟩ : syracuseStep 532767 = 799151) B799151
theorem B532827 : Blo 531801 532827 := bstep (se 1 (by rfl) ⟨399620, by rfl⟩ : syracuseStep 532827 = 799241) B799241
theorem B532847 : Blo 531801 532847 := bstep (se 1 (by rfl) ⟨399635, by rfl⟩ : syracuseStep 532847 = 799271) B799271
theorem B532903 : Blo 531801 532903 := bstep (se 1 (by rfl) ⟨399677, by rfl⟩ : syracuseStep 532903 = 799355) B799355
theorem B1286567 : Blo 531801 1286567 := bstep (se 1 (by rfl) ⟨964925, by rfl⟩ : syracuseStep 1286567 = 1929851) B1929851
theorem B532987 : Blo 531801 532987 := bstep (se 1 (by rfl) ⟨399740, by rfl⟩ : syracuseStep 532987 = 799481) B799481
theorem B533055 : Blo 531801 533055 := bstep (se 1 (by rfl) ⟨399791, by rfl⟩ : syracuseStep 533055 = 799583) B799583
theorem B533063 : Blo 531801 533063 := bstep (se 1 (by rfl) ⟨399797, by rfl⟩ : syracuseStep 533063 = 799595) B799595
theorem B5120657 : Blo 531801 5120657 := bstep (se 2 (by rfl) ⟨1920246, by rfl⟩ : syracuseStep 5120657 = 3840493) B3840493
theorem B9249491 : Blo 531801 9249491 := bstep (se 1 (by rfl) ⟨6937118, by rfl⟩ : syracuseStep 9249491 = 13874237) B13874237
theorem B1024735 : Blo 531801 1024735 := bstep (se 1 (by rfl) ⟨768551, by rfl⟩ : syracuseStep 1024735 = 1537103) B1537103
theorem B533215 : Blo 531801 533215 := bstep (se 1 (by rfl) ⟨399911, by rfl⟩ : syracuseStep 533215 = 799823) B799823
theorem B533295 : Blo 531801 533295 := bstep (se 1 (by rfl) ⟨399971, by rfl⟩ : syracuseStep 533295 = 799943) B799943
theorem B533403 : Blo 531801 533403 := bstep (se 1 (by rfl) ⟨400052, by rfl⟩ : syracuseStep 533403 = 800105) B800105
theorem B533455 : Blo 531801 533455 := bstep (se 1 (by rfl) ⟨400091, by rfl⟩ : syracuseStep 533455 = 800183) B800183
theorem B533479 : Blo 531801 533479 := bstep (se 1 (by rfl) ⟨400109, by rfl⟩ : syracuseStep 533479 = 800219) B800219
theorem B1221671 : Blo 531801 1221671 := bstep (se 1 (by rfl) ⟨916253, by rfl⟩ : syracuseStep 1221671 = 1832507) B1832507
theorem B1352801 : Blo 531801 1352801 := bstep (se 2 (by rfl) ⟨507300, by rfl⟩ : syracuseStep 1352801 = 1014601) B1014601
theorem B533791 : Blo 531801 533791 := bstep (se 1 (by rfl) ⟨400343, by rfl⟩ : syracuseStep 533791 = 800687) B800687
theorem B533851 : Blo 531801 533851 := bstep (se 1 (by rfl) ⟨400388, by rfl⟩ : syracuseStep 533851 = 800777) B800777
theorem B533871 : Blo 531801 533871 := bstep (se 1 (by rfl) ⟨400403, by rfl⟩ : syracuseStep 533871 = 800807) B800807
theorem B533927 : Blo 531801 533927 := bstep (se 1 (by rfl) ⟨400445, by rfl⟩ : syracuseStep 533927 = 800891) B800891
theorem B534011 : Blo 531801 534011 := bstep (se 1 (by rfl) ⟨400508, by rfl⟩ : syracuseStep 534011 = 801017) B801017
theorem B534079 : Blo 531801 534079 := bstep (se 1 (by rfl) ⟨400559, by rfl⟩ : syracuseStep 534079 = 801119) B801119
theorem B534087 : Blo 531801 534087 := bstep (se 1 (by rfl) ⟨400565, by rfl⟩ : syracuseStep 534087 = 801131) B801131
theorem B599647 : Blo 531801 599647 := bstep (se 1 (by rfl) ⟨449735, by rfl⟩ : syracuseStep 599647 = 899471) B899471
theorem B534239 : Blo 531801 534239 := bstep (se 1 (by rfl) ⟨400679, by rfl⟩ : syracuseStep 534239 = 801359) B801359
theorem B534319 : Blo 531801 534319 := bstep (se 1 (by rfl) ⟨400739, by rfl⟩ : syracuseStep 534319 = 801479) B801479
theorem B534427 : Blo 531801 534427 := bstep (se 1 (by rfl) ⟨400820, by rfl⟩ : syracuseStep 534427 = 801641) B801641
theorem B534479 : Blo 531801 534479 := bstep (se 1 (by rfl) ⟨400859, by rfl⟩ : syracuseStep 534479 = 801719) B801719
theorem B534503 : Blo 531801 534503 := bstep (se 1 (by rfl) ⟨400877, by rfl⟩ : syracuseStep 534503 = 801755) B801755
theorem B2369569 : Blo 531801 2369569 := bstep (se 2 (by rfl) ⟨888588, by rfl⟩ : syracuseStep 2369569 = 1777177) B1777177
theorem B13117625 : Blo 531801 13117625 := bstep (se 2 (by rfl) ⟨4919109, by rfl⟩ : syracuseStep 13117625 = 9838219) B9838219
theorem B534815 : Blo 531801 534815 := bstep (se 1 (by rfl) ⟨401111, by rfl⟩ : syracuseStep 534815 = 802223) B802223
theorem B534875 : Blo 531801 534875 := bstep (se 1 (by rfl) ⟨401156, by rfl⟩ : syracuseStep 534875 = 802313) B802313
theorem B3647855 : Blo 531801 3647855 := bstep (se 1 (by rfl) ⟨2735891, by rfl⟩ : syracuseStep 3647855 = 5471783) B5471783
theorem B534895 : Blo 531801 534895 := bstep (se 1 (by rfl) ⟨401171, by rfl⟩ : syracuseStep 534895 = 802343) B802343
theorem B534951 : Blo 531801 534951 := bstep (se 1 (by rfl) ⟨401213, by rfl⟩ : syracuseStep 534951 = 802427) B802427
theorem B535035 : Blo 531801 535035 := bstep (se 1 (by rfl) ⟨401276, by rfl⟩ : syracuseStep 535035 = 802553) B802553
theorem B10267145 : Blo 531801 10267145 := bstep (se 2 (by rfl) ⟨3850179, by rfl⟩ : syracuseStep 10267145 = 7700359) B7700359
theorem B1354259 : Blo 531801 1354259 := bstep (se 1 (by rfl) ⟨1015694, by rfl⟩ : syracuseStep 1354259 = 2031389) B2031389
theorem B535103 : Blo 531801 535103 := bstep (se 1 (by rfl) ⟨401327, by rfl⟩ : syracuseStep 535103 = 802655) B802655
theorem B535111 : Blo 531801 535111 := bstep (se 1 (by rfl) ⟨401333, by rfl⟩ : syracuseStep 535111 = 802667) B802667
theorem B2271883 : Blo 531801 2271883 := bstep (se 1 (by rfl) ⟨1703912, by rfl⟩ : syracuseStep 2271883 = 3407825) B3407825
theorem B600799 : Blo 531801 600799 := bstep (se 1 (by rfl) ⟨450599, by rfl⟩ : syracuseStep 600799 = 901199) B901199
theorem B535263 : Blo 531801 535263 := bstep (se 1 (by rfl) ⟨401447, by rfl⟩ : syracuseStep 535263 = 802895) B802895
theorem B535343 : Blo 531801 535343 := bstep (se 1 (by rfl) ⟨401507, by rfl⟩ : syracuseStep 535343 = 803015) B803015
theorem B2698109 : Blo 531801 2698109 := bstep (se 3 (by rfl) ⟨505895, by rfl⟩ : syracuseStep 2698109 = 1011791) B1011791
theorem B1715087 : Blo 531801 1715087 := bstep (se 1 (by rfl) ⟨1286315, by rfl⟩ : syracuseStep 1715087 = 2572631) B2572631
theorem B535451 : Blo 531801 535451 := bstep (se 1 (by rfl) ⟨401588, by rfl⟩ : syracuseStep 535451 = 803177) B803177
theorem B535503 : Blo 531801 535503 := bstep (se 1 (by rfl) ⟨401627, by rfl⟩ : syracuseStep 535503 = 803255) B803255
theorem B1354715 : Blo 531801 1354715 := bstep (se 1 (by rfl) ⟨1016036, by rfl⟩ : syracuseStep 1354715 = 2032073) B2032073
theorem B535527 : Blo 531801 535527 := bstep (se 1 (by rfl) ⟨401645, by rfl⟩ : syracuseStep 535527 = 803291) B803291
theorem B7777361 : Blo 531801 7777361 := bstep (se 2 (by rfl) ⟨2916510, by rfl⟩ : syracuseStep 7777361 = 5833021) B5833021
theorem B797915 : Blo 531801 797915 := bstep (se 1 (by rfl) ⟨598436, by rfl⟩ : syracuseStep 797915 = 1196873) B1196873
theorem B3845339 : Blo 531801 3845339 := bstep (se 1 (by rfl) ⟨2884004, by rfl⟩ : syracuseStep 3845339 = 5768009) B5768009
theorem B601375 : Blo 531801 601375 := bstep (se 1 (by rfl) ⟨451031, by rfl⟩ : syracuseStep 601375 = 902063) B902063
theorem B1355039 : Blo 531801 1355039 := bstep (se 1 (by rfl) ⟨1016279, by rfl⟩ : syracuseStep 1355039 = 2032559) B2032559
theorem B798089 : Blo 531801 798089 := bstep (se 2 (by rfl) ⟨299283, by rfl⟩ : syracuseStep 798089 = 598567) B598567
theorem B10530269 : Blo 531801 10530269 := bstep (se 3 (by rfl) ⟨1974425, by rfl⟩ : syracuseStep 10530269 = 3948851) B3948851
theorem B962041 : Blo 531801 962041 := bstep (se 2 (by rfl) ⟨360765, by rfl⟩ : syracuseStep 962041 = 721531) B721531
theorem B601663 : Blo 531801 601663 := bstep (se 1 (by rfl) ⟨451247, by rfl⟩ : syracuseStep 601663 = 902495) B902495
theorem B798443 : Blo 531801 798443 := bstep (se 1 (by rfl) ⟨598832, by rfl⟩ : syracuseStep 798443 = 1197665) B1197665
theorem B1355575 : Blo 531801 1355575 := bstep (se 1 (by rfl) ⟨1016681, by rfl⟩ : syracuseStep 1355575 = 2033363) B2033363
theorem B2699081 : Blo 531801 2699081 := bstep (se 2 (by rfl) ⟨1012155, by rfl⟩ : syracuseStep 2699081 = 2024311) B2024311
theorem B16461755 : Blo 531801 16461755 := bstep (se 1 (by rfl) ⟨12346316, by rfl⟩ : syracuseStep 16461755 = 24692633) B24692633
theorem B798671 : Blo 531801 798671 := bstep (se 1 (by rfl) ⟨599003, by rfl⟩ : syracuseStep 798671 = 1198007) B1198007
theorem B1356041 : Blo 531801 1356041 := bstep (se 2 (by rfl) ⟨508515, by rfl⟩ : syracuseStep 1356041 = 1017031) B1017031
theorem B799067 : Blo 531801 799067 := bstep (se 1 (by rfl) ⟨599300, by rfl⟩ : syracuseStep 799067 = 1198601) B1198601
theorem B602491 : Blo 531801 602491 := bstep (se 1 (by rfl) ⟨451868, by rfl⟩ : syracuseStep 602491 = 903737) B903737
theorem B1520147 : Blo 531801 1520147 := bstep (se 1 (by rfl) ⟨1140110, by rfl⟩ : syracuseStep 1520147 = 2280221) B2280221
theorem B799295 : Blo 531801 799295 := bstep (se 1 (by rfl) ⟨599471, by rfl⟩ : syracuseStep 799295 = 1198943) B1198943
theorem B864841 : Blo 531801 864841 := bstep (se 2 (by rfl) ⟨324315, by rfl⟩ : syracuseStep 864841 = 648631) B648631
theorem B2896505 : Blo 531801 2896505 := bstep (se 2 (by rfl) ⟨1086189, by rfl⟩ : syracuseStep 2896505 = 2172379) B2172379
theorem B799415 : Blo 531801 799415 := bstep (se 1 (by rfl) ⟨599561, by rfl⟩ : syracuseStep 799415 = 1199123) B1199123
theorem B897871 : Blo 531801 897871 := bstep (se 1 (by rfl) ⟨673403, by rfl⟩ : syracuseStep 897871 = 1346807) B1346807
theorem B799643 : Blo 531801 799643 := bstep (se 1 (by rfl) ⟨599732, by rfl⟩ : syracuseStep 799643 = 1199465) B1199465
theorem B8205257 : Blo 531801 8205257 := bstep (se 2 (by rfl) ⟨3076971, by rfl⟩ : syracuseStep 8205257 = 6153943) B6153943
theorem B1520603 : Blo 531801 1520603 := bstep (se 1 (by rfl) ⟨1140452, by rfl⟩ : syracuseStep 1520603 = 2280905) B2280905
theorem B2700377 : Blo 531801 2700377 := bstep (se 2 (by rfl) ⟨1012641, by rfl⟩ : syracuseStep 2700377 = 2025283) B2025283
theorem B1619041 : Blo 531801 1619041 := bstep (se 2 (by rfl) ⟨607140, by rfl⟩ : syracuseStep 1619041 = 1214281) B1214281
theorem B6829181 : Blo 531801 6829181 := bstep (se 3 (by rfl) ⟨1280471, by rfl⟩ : syracuseStep 6829181 = 2560943) B2560943
theorem B800039 : Blo 531801 800039 := bstep (se 1 (by rfl) ⟨600029, by rfl⟩ : syracuseStep 800039 = 1200059) B1200059
theorem B800123 : Blo 531801 800123 := bstep (se 1 (by rfl) ⟨600092, by rfl⟩ : syracuseStep 800123 = 1200185) B1200185
theorem B898553 : Blo 531801 898553 := bstep (se 2 (by rfl) ⟨336957, by rfl⟩ : syracuseStep 898553 = 673915) B673915
theorem B800249 : Blo 531801 800249 := bstep (se 2 (by rfl) ⟨300093, by rfl⟩ : syracuseStep 800249 = 600187) B600187
theorem B800351 : Blo 531801 800351 := bstep (se 1 (by rfl) ⟨600263, by rfl⟩ : syracuseStep 800351 = 1200527) B1200527
theorem B571055 : Blo 531801 571055 := bstep (se 1 (by rfl) ⟨428291, by rfl⟩ : syracuseStep 571055 = 856583) B856583
theorem B898823 : Blo 531801 898823 := bstep (se 1 (by rfl) ⟨674117, by rfl⟩ : syracuseStep 898823 = 1348235) B1348235
theorem B800567 : Blo 531801 800567 := bstep (se 1 (by rfl) ⟨600425, by rfl⟩ : syracuseStep 800567 = 1200851) B1200851
theorem B4634657 : Blo 531801 4634657 := bstep (se 2 (by rfl) ⟨1737996, by rfl⟩ : syracuseStep 4634657 = 3475993) B3475993
theorem B800873 : Blo 531801 800873 := bstep (se 2 (by rfl) ⟨300327, by rfl⟩ : syracuseStep 800873 = 600655) B600655
theorem B3651929 : Blo 531801 3651929 := bstep (se 2 (by rfl) ⟨1369473, by rfl⟩ : syracuseStep 3651929 = 2738947) B2738947
theorem B801191 : Blo 531801 801191 := bstep (se 1 (by rfl) ⟨600893, by rfl⟩ : syracuseStep 801191 = 1201787) B1201787
theorem B899579 : Blo 531801 899579 := bstep (se 1 (by rfl) ⟨674684, by rfl⟩ : syracuseStep 899579 = 1349369) B1349369
theorem B801275 : Blo 531801 801275 := bstep (se 1 (by rfl) ⟨600956, by rfl⟩ : syracuseStep 801275 = 1201913) B1201913
theorem B801401 : Blo 531801 801401 := bstep (se 2 (by rfl) ⟨300525, by rfl⟩ : syracuseStep 801401 = 601051) B601051
theorem B801455 : Blo 531801 801455 := bstep (se 1 (by rfl) ⟨601091, by rfl⟩ : syracuseStep 801455 = 1202183) B1202183
theorem B801503 : Blo 531801 801503 := bstep (se 1 (by rfl) ⟨601127, by rfl⟩ : syracuseStep 801503 = 1202255) B1202255
theorem B900011 : Blo 531801 900011 := bstep (se 1 (by rfl) ⟨675008, by rfl⟩ : syracuseStep 900011 = 1350017) B1350017
theorem B801767 : Blo 531801 801767 := bstep (se 1 (by rfl) ⟨601325, by rfl⟩ : syracuseStep 801767 = 1202651) B1202651
theorem B3390587 : Blo 531801 3390587 := bstep (se 1 (by rfl) ⟨2542940, by rfl⟩ : syracuseStep 3390587 = 5085881) B5085881
theorem B1621181 : Blo 531801 1621181 := bstep (se 3 (by rfl) ⟨303971, by rfl⟩ : syracuseStep 1621181 = 607943) B607943
theorem B802025 : Blo 531801 802025 := bstep (se 2 (by rfl) ⟨300759, by rfl⟩ : syracuseStep 802025 = 601519) B601519
theorem B802079 : Blo 531801 802079 := bstep (se 1 (by rfl) ⟨601559, by rfl⟩ : syracuseStep 802079 = 1203119) B1203119
theorem B4341059 : Blo 531801 4341059 := bstep (se 1 (by rfl) ⟨3255794, by rfl⟩ : syracuseStep 4341059 = 6511589) B6511589
theorem B2571707 : Blo 531801 2571707 := bstep (se 1 (by rfl) ⟨1928780, by rfl⟩ : syracuseStep 2571707 = 3857561) B3857561
theorem B900551 : Blo 531801 900551 := bstep (se 1 (by rfl) ⟨675413, by rfl⟩ : syracuseStep 900551 = 1350827) B1350827
theorem B802247 : Blo 531801 802247 := bstep (se 1 (by rfl) ⟨601685, by rfl⟩ : syracuseStep 802247 = 1203371) B1203371
theorem B2702807 : Blo 531801 2702807 := bstep (se 1 (by rfl) ⟨2027105, by rfl⟩ : syracuseStep 2702807 = 4054211) B4054211
theorem B27704825 : Blo 531801 27704825 := bstep (se 2 (by rfl) ⟨10389309, by rfl⟩ : syracuseStep 27704825 = 20778619) B20778619
theorem B2276873 : Blo 531801 2276873 := bstep (se 2 (by rfl) ⟨853827, by rfl⟩ : syracuseStep 2276873 = 1707655) B1707655
theorem B5127695 : Blo 531801 5127695 := bstep (se 1 (by rfl) ⟨3845771, by rfl⟩ : syracuseStep 5127695 = 7691543) B7691543
theorem B802601 : Blo 531801 802601 := bstep (se 2 (by rfl) ⟨300975, by rfl⟩ : syracuseStep 802601 = 601951) B601951
theorem B802607 : Blo 531801 802607 := bstep (se 1 (by rfl) ⟨601955, by rfl⟩ : syracuseStep 802607 = 1203911) B1203911
theorem B10993481 : Blo 531801 10993481 := bstep (se 2 (by rfl) ⟨4122555, by rfl⟩ : syracuseStep 10993481 = 8245111) B8245111
theorem B2572307 : Blo 531801 2572307 := bstep (se 1 (by rfl) ⟨1929230, by rfl⟩ : syracuseStep 2572307 = 3858461) B3858461
theorem B3031091 : Blo 531801 3031091 := bstep (se 1 (by rfl) ⟨2273318, by rfl⟩ : syracuseStep 3031091 = 4546637) B4546637
theorem B803081 : Blo 531801 803081 := bstep (se 2 (by rfl) ⟨301155, by rfl⟩ : syracuseStep 803081 = 602311) B602311
theorem B541019 : Blo 531801 541019 := bstep (se 1 (by rfl) ⟨405764, by rfl⟩ : syracuseStep 541019 = 811529) B811529
theorem B803183 : Blo 531801 803183 := bstep (se 1 (by rfl) ⟨602387, by rfl⟩ : syracuseStep 803183 = 1204775) B1204775
theorem B901543 : Blo 531801 901543 := bstep (se 1 (by rfl) ⟨676157, by rfl⟩ : syracuseStep 901543 = 1352315) B1352315
theorem B1622447 : Blo 531801 1622447 := bstep (se 1 (by rfl) ⟨1216835, by rfl⟩ : syracuseStep 1622447 = 2433671) B2433671
theorem B803399 : Blo 531801 803399 := bstep (se 1 (by rfl) ⟨602549, by rfl⟩ : syracuseStep 803399 = 1205099) B1205099
theorem B901705 : Blo 531801 901705 := bstep (se 2 (by rfl) ⟨338139, by rfl⟩ : syracuseStep 901705 = 676279) B676279
theorem B901739 : Blo 531801 901739 := bstep (se 1 (by rfl) ⟨676304, by rfl⟩ : syracuseStep 901739 = 1352609) B1352609
theorem B803435 : Blo 531801 803435 := bstep (se 1 (by rfl) ⟨602576, by rfl⟩ : syracuseStep 803435 = 1205153) B1205153
theorem B1196819 : Blo 531801 1196819 := bstep (se 1 (by rfl) ⟨897614, by rfl⟩ : syracuseStep 1196819 = 1795229) B1795229
theorem B639823 : Blo 531801 639823 := bstep (se 1 (by rfl) ⟨479867, by rfl⟩ : syracuseStep 639823 = 959735) B959735
theorem B803663 : Blo 531801 803663 := bstep (se 1 (by rfl) ⟨602747, by rfl⟩ : syracuseStep 803663 = 1205495) B1205495
theorem B6865883 : Blo 531801 6865883 := bstep (se 1 (by rfl) ⟨5149412, by rfl⟩ : syracuseStep 6865883 = 10298825) B10298825
theorem B4572197 : Blo 531801 4572197 := bstep (se 4 (by rfl) ⟨428643, by rfl⟩ : syracuseStep 4572197 = 857287) B857287
theorem B7324769 : Blo 531801 7324769 := bstep (se 2 (by rfl) ⟨2746788, by rfl⟩ : syracuseStep 7324769 = 5493577) B5493577
theorem B1197179 : Blo 531801 1197179 := bstep (se 1 (by rfl) ⟨897884, by rfl⟩ : syracuseStep 1197179 = 1795769) B1795769
theorem B1197305 : Blo 531801 1197305 := bstep (se 2 (by rfl) ⟨448989, by rfl⟩ : syracuseStep 1197305 = 897979) B897979
theorem B1197449 : Blo 531801 1197449 := bstep (se 2 (by rfl) ⟨449043, by rfl⟩ : syracuseStep 1197449 = 898087) B898087
theorem B2573707 : Blo 531801 2573707 := bstep (se 1 (by rfl) ⟨1930280, by rfl⟩ : syracuseStep 2573707 = 3860561) B3860561
theorem B1197575 : Blo 531801 1197575 := bstep (se 1 (by rfl) ⟨898181, by rfl⟩ : syracuseStep 1197575 = 1796363) B1796363
theorem B1197755 : Blo 531801 1197755 := bstep (se 1 (by rfl) ⟨898316, by rfl⟩ : syracuseStep 1197755 = 1796633) B1796633
theorem B673591 : Blo 531801 673591 := bstep (se 1 (by rfl) ⟨505193, by rfl⟩ : syracuseStep 673591 = 1010387) B1010387
theorem B1197881 : Blo 531801 1197881 := bstep (se 2 (by rfl) ⟨449205, by rfl⟩ : syracuseStep 1197881 = 898411) B898411
theorem B2279249 : Blo 531801 2279249 := bstep (se 2 (by rfl) ⟨854718, by rfl⟩ : syracuseStep 2279249 = 1709437) B1709437
theorem B674011 : Blo 531801 674011 := bstep (se 1 (by rfl) ⟨505508, by rfl⟩ : syracuseStep 674011 = 1011017) B1011017
theorem B903433 : Blo 531801 903433 := bstep (se 2 (by rfl) ⟨338787, by rfl⟩ : syracuseStep 903433 = 677575) B677575
theorem B1296815 : Blo 531801 1296815 := bstep (se 1 (by rfl) ⟨972611, by rfl⟩ : syracuseStep 1296815 = 1945223) B1945223
theorem B1198511 : Blo 531801 1198511 := bstep (se 1 (by rfl) ⟨898883, by rfl⟩ : syracuseStep 1198511 = 1797767) B1797767
theorem B1198547 : Blo 531801 1198547 := bstep (se 1 (by rfl) ⟨898910, by rfl⟩ : syracuseStep 1198547 = 1797821) B1797821
theorem B1198655 : Blo 531801 1198655 := bstep (se 1 (by rfl) ⟨898991, by rfl⟩ : syracuseStep 1198655 = 1797983) B1797983
theorem B1198763 : Blo 531801 1198763 := bstep (se 1 (by rfl) ⟨899072, by rfl⟩ : syracuseStep 1198763 = 1798145) B1798145
theorem B4573907 : Blo 531801 4573907 := bstep (se 1 (by rfl) ⟨3430430, by rfl⟩ : syracuseStep 4573907 = 6860861) B6860861
theorem B2608043 : Blo 531801 2608043 := bstep (se 1 (by rfl) ⟨1956032, by rfl⟩ : syracuseStep 2608043 = 3912065) B3912065
theorem B1625075 : Blo 531801 1625075 := bstep (se 1 (by rfl) ⟨1218806, by rfl⟩ : syracuseStep 1625075 = 2437613) B2437613
theorem B1199303 : Blo 531801 1199303 := bstep (se 1 (by rfl) ⟨899477, by rfl⟩ : syracuseStep 1199303 = 1798955) B1798955
theorem B1199483 : Blo 531801 1199483 := bstep (se 1 (by rfl) ⟨899612, by rfl⟩ : syracuseStep 1199483 = 1799225) B1799225
theorem B1199609 : Blo 531801 1199609 := bstep (se 2 (by rfl) ⟨449853, by rfl⟩ : syracuseStep 1199609 = 899707) B899707
theorem B4869641 : Blo 531801 4869641 := bstep (se 2 (by rfl) ⟨1826115, by rfl⟩ : syracuseStep 4869641 = 3652231) B3652231
theorem B1920593 : Blo 531801 1920593 := bstep (se 2 (by rfl) ⟨720222, by rfl⟩ : syracuseStep 1920593 = 1440445) B1440445
theorem B1199699 : Blo 531801 1199699 := bstep (se 1 (by rfl) ⟨899774, by rfl⟩ : syracuseStep 1199699 = 1799549) B1799549
theorem B1199879 : Blo 531801 1199879 := bstep (se 1 (by rfl) ⟨899909, by rfl⟩ : syracuseStep 1199879 = 1799819) B1799819
theorem B675631 : Blo 531801 675631 := bstep (se 1 (by rfl) ⟨506723, by rfl⟩ : syracuseStep 675631 = 1013447) B1013447
theorem B577487 : Blo 531801 577487 := bstep (se 1 (by rfl) ⟨433115, by rfl⟩ : syracuseStep 577487 = 866231) B866231
theorem B2707667 : Blo 531801 2707667 := bstep (se 1 (by rfl) ⟨2030750, by rfl⟩ : syracuseStep 2707667 = 4061501) B4061501
theorem B676127 : Blo 531801 676127 := bstep (se 1 (by rfl) ⟨507095, by rfl⟩ : syracuseStep 676127 = 1014191) B1014191
theorem B3035465 : Blo 531801 3035465 := bstep (se 2 (by rfl) ⟨1138299, by rfl⟩ : syracuseStep 3035465 = 2276599) B2276599
theorem B1200491 : Blo 531801 1200491 := bstep (se 1 (by rfl) ⟨900368, by rfl⟩ : syracuseStep 1200491 = 1800737) B1800737
theorem B1200635 : Blo 531801 1200635 := bstep (se 1 (by rfl) ⟨900476, by rfl⟩ : syracuseStep 1200635 = 1800953) B1800953
theorem B2806343 : Blo 531801 2806343 := bstep (se 1 (by rfl) ⟨2104757, by rfl⟩ : syracuseStep 2806343 = 4209515) B4209515
theorem B1200761 : Blo 531801 1200761 := bstep (se 2 (by rfl) ⟨450285, by rfl⟩ : syracuseStep 1200761 = 900571) B900571
theorem B1200815 : Blo 531801 1200815 := bstep (se 1 (by rfl) ⟨900611, by rfl⟩ : syracuseStep 1200815 = 1801223) B1801223
theorem B1364663 : Blo 531801 1364663 := bstep (se 1 (by rfl) ⟨1023497, by rfl⟩ : syracuseStep 1364663 = 2046995) B2046995
theorem B5755637 : Blo 531801 5755637 := bstep (se 5 (by rfl) ⟨269795, by rfl⟩ : syracuseStep 5755637 = 539591) B539591
theorem B1200887 : Blo 531801 1200887 := bstep (se 1 (by rfl) ⟨900665, by rfl⟩ : syracuseStep 1200887 = 1801331) B1801331
theorem B3298157 : Blo 531801 3298157 := bstep (se 3 (by rfl) ⟨618404, by rfl⟩ : syracuseStep 3298157 = 1236809) B1236809
theorem B1201067 : Blo 531801 1201067 := bstep (se 1 (by rfl) ⟨900800, by rfl⟩ : syracuseStep 1201067 = 1801601) B1801601
theorem B51958745 : Blo 531801 51958745 := bstep (se 2 (by rfl) ⟨19484529, by rfl⟩ : syracuseStep 51958745 = 38969059) B38969059
theorem B30823577 : Blo 531801 30823577 := bstep (se 2 (by rfl) ⟨11558841, by rfl⟩ : syracuseStep 30823577 = 23117683) B23117683
theorem B1201607 : Blo 531801 1201607 := bstep (se 1 (by rfl) ⟨901205, by rfl⟩ : syracuseStep 1201607 = 1802411) B1802411
theorem B7722503 : Blo 531801 7722503 := bstep (se 1 (by rfl) ⟨5791877, by rfl⟩ : syracuseStep 7722503 = 11583755) B11583755
theorem B4544039 : Blo 531801 4544039 := bstep (se 1 (by rfl) ⟨3408029, by rfl⟩ : syracuseStep 4544039 = 6816059) B6816059
theorem B1201967 : Blo 531801 1201967 := bstep (se 1 (by rfl) ⟨901475, by rfl⟩ : syracuseStep 1201967 = 1802951) B1802951
theorem B4053239 : Blo 531801 4053239 := bstep (se 1 (by rfl) ⟨3039929, by rfl⟩ : syracuseStep 4053239 = 6079859) B6079859
theorem B809327 : Blo 531801 809327 := bstep (se 1 (by rfl) ⟨606995, by rfl⟩ : syracuseStep 809327 = 1213991) B1213991
theorem B1202543 : Blo 531801 1202543 := bstep (se 1 (by rfl) ⟨901907, by rfl⟩ : syracuseStep 1202543 = 1803815) B1803815
theorem B1202615 : Blo 531801 1202615 := bstep (se 1 (by rfl) ⟨901961, by rfl⟩ : syracuseStep 1202615 = 1803923) B1803923
theorem B1202759 : Blo 531801 1202759 := bstep (se 1 (by rfl) ⟨902069, by rfl⟩ : syracuseStep 1202759 = 1804139) B1804139
theorem B4119113 : Blo 531801 4119113 := bstep (se 2 (by rfl) ⟨1544667, by rfl⟩ : syracuseStep 4119113 = 3089335) B3089335
theorem B1202795 : Blo 531801 1202795 := bstep (se 1 (by rfl) ⟨902096, by rfl⟩ : syracuseStep 1202795 = 1804193) B1804193
theorem B2284307 : Blo 531801 2284307 := bstep (se 1 (by rfl) ⟨1713230, by rfl⟩ : syracuseStep 2284307 = 3426461) B3426461
theorem B5757803 : Blo 531801 5757803 := bstep (se 1 (by rfl) ⟨4318352, by rfl⟩ : syracuseStep 5757803 = 8636705) B8636705
theorem B3038107 : Blo 531801 3038107 := bstep (se 1 (by rfl) ⟨2278580, by rfl⟩ : syracuseStep 3038107 = 4557161) B4557161
theorem B5495795 : Blo 531801 5495795 := bstep (se 1 (by rfl) ⟨4121846, by rfl⟩ : syracuseStep 5495795 = 8243693) B8243693
theorem B1203191 : Blo 531801 1203191 := bstep (se 1 (by rfl) ⟨902393, by rfl⟩ : syracuseStep 1203191 = 1804787) B1804787
theorem B2317501 : Blo 531801 2317501 := bstep (se 3 (by rfl) ⟨434531, by rfl⟩ : syracuseStep 2317501 = 869063) B869063
theorem B1465559 : Blo 531801 1465559 := bstep (se 1 (by rfl) ⟨1099169, by rfl⟩ : syracuseStep 1465559 = 2198339) B2198339
theorem B11132225 : Blo 531801 11132225 := bstep (se 2 (by rfl) ⟨4174584, by rfl⟩ : syracuseStep 11132225 = 8349169) B8349169
theorem B1203551 : Blo 531801 1203551 := bstep (se 1 (by rfl) ⟨902663, by rfl⟩ : syracuseStep 1203551 = 1805327) B1805327
theorem B1498583 : Blo 531801 1498583 := bstep (se 1 (by rfl) ⟨1123937, by rfl⟩ : syracuseStep 1498583 = 2247875) B2247875
theorem B1203947 : Blo 531801 1203947 := bstep (se 1 (by rfl) ⟨902960, by rfl⟩ : syracuseStep 1203947 = 1805921) B1805921
theorem B1826567 : Blo 531801 1826567 := bstep (se 1 (by rfl) ⟨1369925, by rfl⟩ : syracuseStep 1826567 = 2739851) B2739851
theorem B18013985 : Blo 531801 18013985 := bstep (se 2 (by rfl) ⟨6755244, by rfl⟩ : syracuseStep 18013985 = 13510489) B13510489
theorem B1204073 : Blo 531801 1204073 := bstep (se 2 (by rfl) ⟨451527, by rfl⟩ : syracuseStep 1204073 = 903055) B903055
theorem B2023325 : Blo 531801 2023325 := bstep (se 3 (by rfl) ⟨379373, by rfl⟩ : syracuseStep 2023325 = 758747) B758747
theorem B37019555 : Blo 531801 37019555 := bstep (se 1 (by rfl) ⟨27764666, by rfl⟩ : syracuseStep 37019555 = 55529333) B55529333
theorem B17817731 : Blo 531801 17817731 := bstep (se 1 (by rfl) ⟨13363298, by rfl⟩ : syracuseStep 17817731 = 26726597) B26726597
theorem B1139017 : Blo 531801 1139017 := bstep (se 2 (by rfl) ⟨427131, by rfl⟩ : syracuseStep 1139017 = 854263) B854263
theorem B1139035 : Blo 531801 1139035 := bstep (se 1 (by rfl) ⟨854276, by rfl⟩ : syracuseStep 1139035 = 1708553) B1708553
theorem B1925551 : Blo 531801 1925551 := bstep (se 1 (by rfl) ⟨1444163, by rfl⟩ : syracuseStep 1925551 = 2888327) B2888327
theorem B1204919 : Blo 531801 1204919 := bstep (se 1 (by rfl) ⟨903689, by rfl⟩ : syracuseStep 1204919 = 1807379) B1807379
theorem B1205135 : Blo 531801 1205135 := bstep (se 1 (by rfl) ⟨903851, by rfl⟩ : syracuseStep 1205135 = 1807703) B1807703
theorem B2876563 : Blo 531801 2876563 := bstep (se 1 (by rfl) ⟨2157422, by rfl⟩ : syracuseStep 2876563 = 4314845) B4314845
theorem B2188435 : Blo 531801 2188435 := bstep (se 1 (by rfl) ⟨1641326, by rfl⟩ : syracuseStep 2188435 = 3282653) B3282653
theorem B2057633 : Blo 531801 2057633 := bstep (se 2 (by rfl) ⟨771612, by rfl⟩ : syracuseStep 2057633 = 1543225) B1543225
theorem B2287997 : Blo 531801 2287997 := bstep (se 3 (by rfl) ⟨428999, by rfl⟩ : syracuseStep 2287997 = 857999) B857999
theorem B1796687 : Blo 531801 1796687 := bstep (se 1 (by rfl) ⟨1347515, by rfl⟩ : syracuseStep 1796687 = 2695031) B2695031
theorem B3041981 : Blo 531801 3041981 := bstep (se 3 (by rfl) ⟨570371, by rfl⟩ : syracuseStep 3041981 = 1140743) B1140743
theorem B1141751 : Blo 531801 1141751 := bstep (se 1 (by rfl) ⟨856313, by rfl⟩ : syracuseStep 1141751 = 1712627) B1712627
theorem B5139571 : Blo 531801 5139571 := bstep (se 1 (by rfl) ⟨3854678, by rfl⟩ : syracuseStep 5139571 = 7709357) B7709357
theorem B683743 : Blo 531801 683743 := bstep (se 1 (by rfl) ⟨512807, by rfl⟩ : syracuseStep 683743 = 1025615) B1025615
theorem B1797929 : Blo 531801 1797929 := bstep (se 2 (by rfl) ⟨674223, by rfl⟩ : syracuseStep 1797929 = 1348447) B1348447
theorem B1011503 : Blo 531801 1011503 := bstep (se 1 (by rfl) ⟨758627, by rfl⟩ : syracuseStep 1011503 = 1517255) B1517255
theorem B3239837 : Blo 531801 3239837 := bstep (se 3 (by rfl) ⟨607469, by rfl⟩ : syracuseStep 3239837 = 1214939) B1214939
theorem B5828561 : Blo 531801 5828561 := bstep (se 2 (by rfl) ⟨2185710, by rfl⟩ : syracuseStep 5828561 = 4371421) B4371421
theorem B3502081 : Blo 531801 3502081 := bstep (se 2 (by rfl) ⟨1313280, by rfl⟩ : syracuseStep 3502081 = 2626561) B2626561
theorem B1012331 : Blo 531801 1012331 := bstep (se 1 (by rfl) ⟨759248, by rfl⟩ : syracuseStep 1012331 = 1518497) B1518497
theorem B2028185 : Blo 531801 2028185 := bstep (se 2 (by rfl) ⟨760569, by rfl⟩ : syracuseStep 2028185 = 1521139) B1521139
theorem B5632973 : Blo 531801 5632973 := bstep (se 3 (by rfl) ⟨1056182, by rfl⟩ : syracuseStep 5632973 = 2112365) B2112365
theorem B2028989 : Blo 531801 2028989 := bstep (se 3 (by rfl) ⟨380435, by rfl⟩ : syracuseStep 2028989 = 760871) B760871
theorem B1439495 : Blo 531801 1439495 := bstep (se 1 (by rfl) ⟨1079621, by rfl⟩ : syracuseStep 1439495 = 2159243) B2159243
theorem B4061015 : Blo 531801 4061015 := bstep (se 1 (by rfl) ⟨3045761, by rfl⟩ : syracuseStep 4061015 = 6091523) B6091523
theorem B1800143 : Blo 531801 1800143 := bstep (se 1 (by rfl) ⟨1350107, by rfl⟩ : syracuseStep 1800143 = 2700215) B2700215
theorem B2030143 : Blo 531801 2030143 := bstep (se 1 (by rfl) ⟨1522607, by rfl⟩ : syracuseStep 2030143 = 3045215) B3045215
theorem B1801115 : Blo 531801 1801115 := bstep (se 1 (by rfl) ⟨1350836, by rfl⟩ : syracuseStep 1801115 = 2701673) B2701673
theorem B1015163 : Blo 531801 1015163 := bstep (se 1 (by rfl) ⟨761372, by rfl⟩ : syracuseStep 1015163 = 1522745) B1522745
theorem B2882945 : Blo 531801 2882945 := bstep (se 2 (by rfl) ⟨1081104, by rfl⟩ : syracuseStep 2882945 = 2162209) B2162209
theorem B1015391 : Blo 531801 1015391 := bstep (se 1 (by rfl) ⟨761543, by rfl⟩ : syracuseStep 1015391 = 1523087) B1523087
theorem B1802141 : Blo 531801 1802141 := bstep (se 3 (by rfl) ⟨337901, by rfl⟩ : syracuseStep 1802141 = 675803) B675803
theorem B18677765 : Blo 531801 18677765 := bstep (se 4 (by rfl) ⟨1751040, by rfl⟩ : syracuseStep 18677765 = 3502081) B3502081
theorem B1081631 : Blo 531801 1081631 := bstep (se 1 (by rfl) ⟨811223, by rfl⟩ : syracuseStep 1081631 = 1622447) B1622447
theorem B1704311 : Blo 531801 1704311 := bstep (se 1 (by rfl) ⟨1278233, by rfl⟩ : syracuseStep 1704311 = 2556467) B2556467
theorem B3048131 : Blo 531801 3048131 := bstep (se 1 (by rfl) ⟨2286098, by rfl⟩ : syracuseStep 3048131 = 4572197) B4572197
theorem B4883179 : Blo 531801 4883179 := bstep (se 1 (by rfl) ⟨3662384, by rfl⟩ : syracuseStep 4883179 = 7324769) B7324769
theorem B1803005 : Blo 531801 1803005 := bstep (se 3 (by rfl) ⟨338063, by rfl⟩ : syracuseStep 1803005 = 676127) B676127
theorem B3408749 : Blo 531801 3408749 := bstep (se 3 (by rfl) ⟨639140, by rfl⟩ : syracuseStep 3408749 = 1278281) B1278281
theorem B1442717 : Blo 531801 1442717 := bstep (se 3 (by rfl) ⟨270509, by rfl⟩ : syracuseStep 1442717 = 541019) B541019
theorem B853097 : Blo 531801 853097 := bstep (se 2 (by rfl) ⟨319911, by rfl⟩ : syracuseStep 853097 = 639823) B639823
theorem B2917913 : Blo 531801 2917913 := bstep (se 2 (by rfl) ⟨1094217, by rfl⟩ : syracuseStep 2917913 = 2188435) B2188435
theorem B3049271 : Blo 531801 3049271 := bstep (se 1 (by rfl) ⟨2286953, by rfl⟩ : syracuseStep 3049271 = 4573907) B4573907
theorem B1083383 : Blo 531801 1083383 := bstep (se 1 (by rfl) ⟨812537, by rfl⟩ : syracuseStep 1083383 = 1625075) B1625075
theorem B6162779 : Blo 531801 6162779 := bstep (se 1 (by rfl) ⟨4622084, by rfl⟩ : syracuseStep 6162779 = 9244169) B9244169
theorem B3246427 : Blo 531801 3246427 := bstep (se 1 (by rfl) ⟨2434820, by rfl⟩ : syracuseStep 3246427 = 4869641) B4869641
theorem B1280395 : Blo 531801 1280395 := bstep (se 1 (by rfl) ⟨960296, by rfl⟩ : syracuseStep 1280395 = 1920593) B1920593
theorem B1805111 : Blo 531801 1805111 := bstep (se 1 (by rfl) ⟨1353833, by rfl⟩ : syracuseStep 1805111 = 2707667) B2707667
theorem B1870895 : Blo 531801 1870895 := bstep (se 1 (by rfl) ⟨1403171, by rfl⟩ : syracuseStep 1870895 = 2806343) B2806343
theorem B2198771 : Blo 531801 2198771 := bstep (se 1 (by rfl) ⟨1649078, by rfl⟩ : syracuseStep 2198771 = 3298157) B3298157
theorem B34639163 : Blo 531801 34639163 := bstep (se 1 (by rfl) ⟨25979372, by rfl⟩ : syracuseStep 34639163 = 51958745) B51958745
theorem B20549051 : Blo 531801 20549051 := bstep (se 1 (by rfl) ⟨15411788, by rfl⟩ : syracuseStep 20549051 = 30823577) B30823577
theorem B5148335 : Blo 531801 5148335 := bstep (se 1 (by rfl) ⟨3861251, by rfl⟩ : syracuseStep 5148335 = 7722503) B7722503
theorem B6852761 : Blo 531801 6852761 := bstep (se 2 (by rfl) ⟨2569785, by rfl⟩ : syracuseStep 6852761 = 5139571) B5139571
theorem B7671995 : Blo 531801 7671995 := bstep (se 1 (by rfl) ⟨5753996, by rfl⟩ : syracuseStep 7671995 = 11507993) B11507993
theorem B3412439 : Blo 531801 3412439 := bstep (se 1 (by rfl) ⟨2559329, by rfl⟩ : syracuseStep 3412439 = 5118659) B5118659
theorem B13832693 : Blo 531801 13832693 := bstep (se 5 (by rfl) ⟨648407, by rfl⟩ : syracuseStep 13832693 = 1296815) B1296815
theorem B3838535 : Blo 531801 3838535 := bstep (se 1 (by rfl) ⟨2878901, by rfl⟩ : syracuseStep 3838535 = 5757803) B5757803
theorem B1282721 : Blo 531801 1282721 := bstep (se 2 (by rfl) ⟨481020, by rfl⟩ : syracuseStep 1282721 = 962041) B962041
theorem B1807433 : Blo 531801 1807433 := bstep (se 2 (by rfl) ⟨677787, by rfl⟩ : syracuseStep 1807433 = 1355575) B1355575
theorem B1217711 : Blo 531801 1217711 := bstep (se 1 (by rfl) ⟨913283, by rfl⟩ : syracuseStep 1217711 = 1826567) B1826567
theorem B1348883 : Blo 531801 1348883 := bstep (se 1 (by rfl) ⟨1011662, by rfl⟩ : syracuseStep 1348883 = 2023325) B2023325
theorem B24679703 : Blo 531801 24679703 := bstep (se 1 (by rfl) ⟨18509777, by rfl⟩ : syracuseStep 24679703 = 37019555) B37019555
theorem B3413339 : Blo 531801 3413339 := bstep (se 1 (by rfl) ⟨2560004, by rfl⟩ : syracuseStep 3413339 = 5120009) B5120009
theorem B857711 : Blo 531801 857711 := bstep (se 1 (by rfl) ⟨643283, by rfl⟩ : syracuseStep 857711 = 1286567) B1286567
theorem B3413771 : Blo 531801 3413771 := bstep (se 1 (by rfl) ⟨2560328, by rfl⟩ : syracuseStep 3413771 = 5120657) B5120657
theorem B6166327 : Blo 531801 6166327 := bstep (se 1 (by rfl) ⟨4624745, by rfl⟩ : syracuseStep 6166327 = 9249491) B9249491
theorem B1153121 : Blo 531801 1153121 := bstep (se 2 (by rfl) ⟨432420, by rfl⟩ : syracuseStep 1153121 = 864841) B864841
theorem B15341669 : Blo 531801 15341669 := bstep (se 4 (by rfl) ⟨1438281, by rfl⟩ : syracuseStep 15341669 = 2876563) B2876563
theorem B2431903 : Blo 531801 2431903 := bstep (se 1 (by rfl) ⟨1823927, by rfl⟩ : syracuseStep 2431903 = 3647855) B3647855
theorem B761167 : Blo 531801 761167 := bstep (se 1 (by rfl) ⟨570875, by rfl⟩ : syracuseStep 761167 = 1141751) B1141751
theorem B531943 : Blo 531801 531943 := bstep (se 1 (by rfl) ⟨398957, by rfl⟩ : syracuseStep 531943 = 797915) B797915
theorem B2563559 : Blo 531801 2563559 := bstep (se 1 (by rfl) ⟨1922669, by rfl⟩ : syracuseStep 2563559 = 3845339) B3845339
theorem B532059 : Blo 531801 532059 := bstep (se 1 (by rfl) ⟨399044, by rfl⟩ : syracuseStep 532059 = 798089) B798089
theorem B7020179 : Blo 531801 7020179 := bstep (se 1 (by rfl) ⟨5265134, by rfl⟩ : syracuseStep 7020179 = 10530269) B10530269
theorem B6954781 : Blo 531801 6954781 := bstep (se 3 (by rfl) ⟨1304021, by rfl⟩ : syracuseStep 6954781 = 2608043) B2608043
theorem B532295 : Blo 531801 532295 := bstep (se 1 (by rfl) ⟨399221, by rfl⟩ : syracuseStep 532295 = 798443) B798443
theorem B532447 : Blo 531801 532447 := bstep (se 1 (by rfl) ⟨399335, by rfl⟩ : syracuseStep 532447 = 798671) B798671
theorem B532711 : Blo 531801 532711 := bstep (se 1 (by rfl) ⟨399533, by rfl⟩ : syracuseStep 532711 = 799067) B799067
theorem B532863 : Blo 531801 532863 := bstep (se 1 (by rfl) ⟨399647, by rfl⟩ : syracuseStep 532863 = 799295) B799295
theorem B1352123 : Blo 531801 1352123 := bstep (se 1 (by rfl) ⟨1014092, by rfl⟩ : syracuseStep 1352123 = 2028185) B2028185
theorem B532943 : Blo 531801 532943 := bstep (se 1 (by rfl) ⟨399707, by rfl⟩ : syracuseStep 532943 = 799415) B799415
theorem B533095 : Blo 531801 533095 := bstep (se 1 (by rfl) ⟨399821, by rfl⟩ : syracuseStep 533095 = 799643) B799643
theorem B533359 : Blo 531801 533359 := bstep (se 1 (by rfl) ⟨400019, by rfl⟩ : syracuseStep 533359 = 800039) B800039
theorem B533415 : Blo 531801 533415 := bstep (se 1 (by rfl) ⟨400061, by rfl⟩ : syracuseStep 533415 = 800123) B800123
theorem B1352659 : Blo 531801 1352659 := bstep (se 1 (by rfl) ⟨1014494, by rfl⟩ : syracuseStep 1352659 = 2028989) B2028989
theorem B599035 : Blo 531801 599035 := bstep (se 1 (by rfl) ⟨449276, by rfl⟩ : syracuseStep 599035 = 898553) B898553
theorem B533499 : Blo 531801 533499 := bstep (se 1 (by rfl) ⟨400124, by rfl⟩ : syracuseStep 533499 = 800249) B800249
theorem B533567 : Blo 531801 533567 := bstep (se 1 (by rfl) ⟨400175, by rfl⟩ : syracuseStep 533567 = 800351) B800351
theorem B6857885 : Blo 531801 6857885 := bstep (se 3 (by rfl) ⟨1285853, by rfl⟩ : syracuseStep 6857885 = 2571707) B2571707
theorem B959663 : Blo 531801 959663 := bstep (se 1 (by rfl) ⟨719747, by rfl⟩ : syracuseStep 959663 = 1439495) B1439495
theorem B599215 : Blo 531801 599215 := bstep (se 1 (by rfl) ⟨449411, by rfl⟩ : syracuseStep 599215 = 898823) B898823
theorem B533711 : Blo 531801 533711 := bstep (se 1 (by rfl) ⟨400283, by rfl⟩ : syracuseStep 533711 = 800567) B800567
theorem B3089771 : Blo 531801 3089771 := bstep (se 1 (by rfl) ⟨2317328, by rfl⟩ : syracuseStep 3089771 = 4634657) B4634657
theorem B6956441 : Blo 531801 6956441 := bstep (se 2 (by rfl) ⟨2608665, by rfl⟩ : syracuseStep 6956441 = 5217331) B5217331
theorem B533915 : Blo 531801 533915 := bstep (se 1 (by rfl) ⟨400436, by rfl⟩ : syracuseStep 533915 = 800873) B800873
theorem B2434619 : Blo 531801 2434619 := bstep (se 1 (by rfl) ⟨1825964, by rfl⟩ : syracuseStep 2434619 = 3651929) B3651929
theorem B3090001 : Blo 531801 3090001 := bstep (se 2 (by rfl) ⟨1158750, by rfl⟩ : syracuseStep 3090001 = 2317501) B2317501
theorem B534127 : Blo 531801 534127 := bstep (se 1 (by rfl) ⟨400595, by rfl⟩ : syracuseStep 534127 = 801191) B801191
theorem B599719 : Blo 531801 599719 := bstep (se 1 (by rfl) ⟨449789, by rfl⟩ : syracuseStep 599719 = 899579) B899579
theorem B534183 : Blo 531801 534183 := bstep (se 1 (by rfl) ⟨400637, by rfl⟩ : syracuseStep 534183 = 801275) B801275
theorem B534267 : Blo 531801 534267 := bstep (se 1 (by rfl) ⟨400700, by rfl⟩ : syracuseStep 534267 = 801401) B801401
theorem B534303 : Blo 531801 534303 := bstep (se 1 (by rfl) ⟨400727, by rfl⟩ : syracuseStep 534303 = 801455) B801455
theorem B534335 : Blo 531801 534335 := bstep (se 1 (by rfl) ⟨400751, by rfl⟩ : syracuseStep 534335 = 801503) B801503
theorem B600007 : Blo 531801 600007 := bstep (se 1 (by rfl) ⟨450005, by rfl⟩ : syracuseStep 600007 = 900011) B900011
theorem B534511 : Blo 531801 534511 := bstep (se 1 (by rfl) ⟨400883, by rfl⟩ : syracuseStep 534511 = 801767) B801767
theorem B534683 : Blo 531801 534683 := bstep (se 1 (by rfl) ⟨401012, by rfl⟩ : syracuseStep 534683 = 802025) B802025
theorem B534719 : Blo 531801 534719 := bstep (se 1 (by rfl) ⟨401039, by rfl⟩ : syracuseStep 534719 = 802079) B802079
theorem B2894039 : Blo 531801 2894039 := bstep (se 1 (by rfl) ⟨2170529, by rfl⟩ : syracuseStep 2894039 = 4341059) B4341059
theorem B600367 : Blo 531801 600367 := bstep (se 1 (by rfl) ⟨450275, by rfl⟩ : syracuseStep 600367 = 900551) B900551
theorem B534831 : Blo 531801 534831 := bstep (se 1 (by rfl) ⟨401123, by rfl⟩ : syracuseStep 534831 = 802247) B802247
theorem B1517915 : Blo 531801 1517915 := bstep (se 1 (by rfl) ⟨1138436, by rfl⟩ : syracuseStep 1517915 = 2276873) B2276873
theorem B3418463 : Blo 531801 3418463 := bstep (se 1 (by rfl) ⟨2563847, by rfl⟩ : syracuseStep 3418463 = 5127695) B5127695
theorem B535067 : Blo 531801 535067 := bstep (se 1 (by rfl) ⟨401300, by rfl⟩ : syracuseStep 535067 = 802601) B802601
theorem B535071 : Blo 531801 535071 := bstep (se 1 (by rfl) ⟨401303, by rfl⟩ : syracuseStep 535071 = 802607) B802607
theorem B1714871 : Blo 531801 1714871 := bstep (se 1 (by rfl) ⟨1286153, by rfl⟩ : syracuseStep 1714871 = 2572307) B2572307
theorem B535387 : Blo 531801 535387 := bstep (se 1 (by rfl) ⟨401540, by rfl⟩ : syracuseStep 535387 = 803081) B803081
theorem B535455 : Blo 531801 535455 := bstep (se 1 (by rfl) ⟨401591, by rfl⟩ : syracuseStep 535455 = 803183) B803183
theorem B535599 : Blo 531801 535599 := bstep (se 1 (by rfl) ⟨401699, by rfl⟩ : syracuseStep 535599 = 803399) B803399
theorem B601159 : Blo 531801 601159 := bstep (se 1 (by rfl) ⟨450869, by rfl⟩ : syracuseStep 601159 = 901739) B901739
theorem B535623 : Blo 531801 535623 := bstep (se 1 (by rfl) ⟨401717, by rfl⟩ : syracuseStep 535623 = 803435) B803435
theorem B1518689 : Blo 531801 1518689 := bstep (se 2 (by rfl) ⟨569508, by rfl⟩ : syracuseStep 1518689 = 1139017) B1139017
theorem B1518713 : Blo 531801 1518713 := bstep (se 2 (by rfl) ⟨569517, by rfl⟩ : syracuseStep 1518713 = 1139035) B1139035
theorem B797879 : Blo 531801 797879 := bstep (se 1 (by rfl) ⟨598409, by rfl⟩ : syracuseStep 797879 = 1196819) B1196819
theorem B535775 : Blo 531801 535775 := bstep (se 1 (by rfl) ⟨401831, by rfl⟩ : syracuseStep 535775 = 803663) B803663
theorem B798119 : Blo 531801 798119 := bstep (se 1 (by rfl) ⟨598589, by rfl⟩ : syracuseStep 798119 = 1197179) B1197179
theorem B798203 : Blo 531801 798203 := bstep (se 1 (by rfl) ⟨598652, by rfl⟩ : syracuseStep 798203 = 1197305) B1197305
theorem B798299 : Blo 531801 798299 := bstep (se 1 (by rfl) ⟨598724, by rfl⟩ : syracuseStep 798299 = 1197449) B1197449
theorem B1617583 : Blo 531801 1617583 := bstep (se 1 (by rfl) ⟨1213187, by rfl⟩ : syracuseStep 1617583 = 2426375) B2426375
theorem B798383 : Blo 531801 798383 := bstep (se 1 (by rfl) ⟨598787, by rfl⟩ : syracuseStep 798383 = 1197575) B1197575
theorem B962273 : Blo 531801 962273 := bstep (se 2 (by rfl) ⟨360852, by rfl⟩ : syracuseStep 962273 = 721705) B721705
theorem B798503 : Blo 531801 798503 := bstep (se 1 (by rfl) ⟨598877, by rfl⟩ : syracuseStep 798503 = 1197755) B1197755
theorem B798587 : Blo 531801 798587 := bstep (se 1 (by rfl) ⟨598940, by rfl⟩ : syracuseStep 798587 = 1197881) B1197881
theorem B1519499 : Blo 531801 1519499 := bstep (se 1 (by rfl) ⟨1139624, by rfl⟩ : syracuseStep 1519499 = 2279249) B2279249
theorem B7712819 : Blo 531801 7712819 := bstep (se 1 (by rfl) ⟨5784614, by rfl⟩ : syracuseStep 7712819 = 11569229) B11569229
theorem B1355899 : Blo 531801 1355899 := bstep (se 1 (by rfl) ⟨1016924, by rfl⟩ : syracuseStep 1355899 = 2033849) B2033849
theorem B799007 : Blo 531801 799007 := bstep (se 1 (by rfl) ⟨599255, by rfl⟩ : syracuseStep 799007 = 1198511) B1198511
theorem B799031 : Blo 531801 799031 := bstep (se 1 (by rfl) ⟨599273, by rfl⟩ : syracuseStep 799031 = 1198547) B1198547
theorem B799103 : Blo 531801 799103 := bstep (se 1 (by rfl) ⟨599327, by rfl⟩ : syracuseStep 799103 = 1198655) B1198655
theorem B799175 : Blo 531801 799175 := bstep (se 1 (by rfl) ⟨599381, by rfl⟩ : syracuseStep 799175 = 1198763) B1198763
theorem B963065 : Blo 531801 963065 := bstep (se 2 (by rfl) ⟨361149, by rfl⟩ : syracuseStep 963065 = 722299) B722299
theorem B15348365 : Blo 531801 15348365 := bstep (se 3 (by rfl) ⟨2877818, by rfl⟩ : syracuseStep 15348365 = 5755637) B5755637
theorem B799529 : Blo 531801 799529 := bstep (se 2 (by rfl) ⟨299823, by rfl⟩ : syracuseStep 799529 = 599647) B599647
theorem B799535 : Blo 531801 799535 := bstep (se 1 (by rfl) ⟨599651, by rfl⟩ : syracuseStep 799535 = 1199303) B1199303
theorem B10269605 : Blo 531801 10269605 := bstep (se 4 (by rfl) ⟨962775, by rfl⟩ : syracuseStep 10269605 = 1925551) B1925551
theorem B897959 : Blo 531801 897959 := bstep (se 1 (by rfl) ⟨673469, by rfl⟩ : syracuseStep 897959 = 1346939) B1346939
theorem B799655 : Blo 531801 799655 := bstep (se 1 (by rfl) ⟨599741, by rfl⟩ : syracuseStep 799655 = 1199483) B1199483
theorem B799739 : Blo 531801 799739 := bstep (se 1 (by rfl) ⟨599804, by rfl⟩ : syracuseStep 799739 = 1199609) B1199609
theorem B799799 : Blo 531801 799799 := bstep (se 1 (by rfl) ⟨599849, by rfl⟩ : syracuseStep 799799 = 1199699) B1199699
theorem B898121 : Blo 531801 898121 := bstep (se 2 (by rfl) ⟨336795, by rfl⟩ : syracuseStep 898121 = 673591) B673591
theorem B799919 : Blo 531801 799919 := bstep (se 1 (by rfl) ⟨599939, by rfl⟩ : syracuseStep 799919 = 1199879) B1199879
theorem B3159425 : Blo 531801 3159425 := bstep (se 2 (by rfl) ⟨1184784, by rfl⟩ : syracuseStep 3159425 = 2369569) B2369569
theorem B10270151 : Blo 531801 10270151 := bstep (se 1 (by rfl) ⟨7702613, by rfl⟩ : syracuseStep 10270151 = 15405227) B15405227
theorem B800327 : Blo 531801 800327 := bstep (se 1 (by rfl) ⟨600245, by rfl⟩ : syracuseStep 800327 = 1200491) B1200491
theorem B898681 : Blo 531801 898681 := bstep (se 2 (by rfl) ⟨337005, by rfl⟩ : syracuseStep 898681 = 674011) B674011
theorem B800423 : Blo 531801 800423 := bstep (se 1 (by rfl) ⟨600317, by rfl⟩ : syracuseStep 800423 = 1200635) B1200635
theorem B800507 : Blo 531801 800507 := bstep (se 1 (by rfl) ⟨600380, by rfl⟩ : syracuseStep 800507 = 1200761) B1200761
theorem B3258107 : Blo 531801 3258107 := bstep (se 1 (by rfl) ⟨2443580, by rfl⟩ : syracuseStep 3258107 = 4887161) B4887161
theorem B800543 : Blo 531801 800543 := bstep (se 1 (by rfl) ⟨600407, by rfl⟩ : syracuseStep 800543 = 1200815) B1200815
theorem B800591 : Blo 531801 800591 := bstep (se 1 (by rfl) ⟨600443, by rfl⟩ : syracuseStep 800591 = 1200887) B1200887
theorem B800711 : Blo 531801 800711 := bstep (se 1 (by rfl) ⟨600533, by rfl⟩ : syracuseStep 800711 = 1201067) B1201067
theorem B899167 : Blo 531801 899167 := bstep (se 1 (by rfl) ⟨674375, by rfl⟩ : syracuseStep 899167 = 1348751) B1348751
theorem B3029177 : Blo 531801 3029177 := bstep (se 2 (by rfl) ⟨1135941, by rfl⟩ : syracuseStep 3029177 = 2271883) B2271883
theorem B801065 : Blo 531801 801065 := bstep (se 2 (by rfl) ⟨300399, by rfl⟩ : syracuseStep 801065 = 600799) B600799
theorem B801071 : Blo 531801 801071 := bstep (se 1 (by rfl) ⟨600803, by rfl⟩ : syracuseStep 801071 = 1201607) B1201607
theorem B3029359 : Blo 531801 3029359 := bstep (se 1 (by rfl) ⟨2272019, by rfl⟩ : syracuseStep 3029359 = 4544039) B4544039
theorem B801311 : Blo 531801 801311 := bstep (se 1 (by rfl) ⟨600983, by rfl⟩ : syracuseStep 801311 = 1201967) B1201967
theorem B2702159 : Blo 531801 2702159 := bstep (se 1 (by rfl) ⟨2026619, by rfl⟩ : syracuseStep 2702159 = 4053239) B4053239
theorem B965459 : Blo 531801 965459 := bstep (se 1 (by rfl) ⟨724094, by rfl⟩ : syracuseStep 965459 = 1448189) B1448189
theorem B539551 : Blo 531801 539551 := bstep (se 1 (by rfl) ⟨404663, by rfl⟩ : syracuseStep 539551 = 809327) B809327
theorem B801695 : Blo 531801 801695 := bstep (se 1 (by rfl) ⟨601271, by rfl⟩ : syracuseStep 801695 = 1202543) B1202543
theorem B801743 : Blo 531801 801743 := bstep (se 1 (by rfl) ⟨601307, by rfl⟩ : syracuseStep 801743 = 1202615) B1202615
theorem B3849257 : Blo 531801 3849257 := bstep (se 2 (by rfl) ⟨1443471, by rfl⟩ : syracuseStep 3849257 = 2886943) B2886943
theorem B801833 : Blo 531801 801833 := bstep (se 2 (by rfl) ⟨300687, by rfl⟩ : syracuseStep 801833 = 601375) B601375
theorem B801839 : Blo 531801 801839 := bstep (se 1 (by rfl) ⟨601379, by rfl⟩ : syracuseStep 801839 = 1202759) B1202759
theorem B801863 : Blo 531801 801863 := bstep (se 1 (by rfl) ⟨601397, by rfl⟩ : syracuseStep 801863 = 1202795) B1202795
theorem B1522813 : Blo 531801 1522813 := bstep (se 3 (by rfl) ⟨285527, by rfl⟩ : syracuseStep 1522813 = 571055) B571055
theorem B4570283 : Blo 531801 4570283 := bstep (se 1 (by rfl) ⟨3427712, by rfl⟩ : syracuseStep 4570283 = 6855425) B6855425
theorem B1522871 : Blo 531801 1522871 := bstep (se 1 (by rfl) ⟨1142153, by rfl⟩ : syracuseStep 1522871 = 2284307) B2284307
theorem B802127 : Blo 531801 802127 := bstep (se 1 (by rfl) ⟨601595, by rfl⟩ : syracuseStep 802127 = 1203191) B1203191
theorem B900463 : Blo 531801 900463 := bstep (se 1 (by rfl) ⟨675347, by rfl⟩ : syracuseStep 900463 = 1350695) B1350695
theorem B802217 : Blo 531801 802217 := bstep (se 2 (by rfl) ⟨300831, by rfl⟩ : syracuseStep 802217 = 601663) B601663
theorem B7421483 : Blo 531801 7421483 := bstep (se 1 (by rfl) ⟨5566112, by rfl⟩ : syracuseStep 7421483 = 11132225) B11132225
theorem B802367 : Blo 531801 802367 := bstep (se 1 (by rfl) ⟨601775, by rfl⟩ : syracuseStep 802367 = 1203551) B1203551
theorem B999055 : Blo 531801 999055 := bstep (se 1 (by rfl) ⟨749291, by rfl⟩ : syracuseStep 999055 = 1498583) B1498583
theorem B900841 : Blo 531801 900841 := bstep (se 2 (by rfl) ⟨337815, by rfl⟩ : syracuseStep 900841 = 675631) B675631
theorem B802631 : Blo 531801 802631 := bstep (se 1 (by rfl) ⟨601973, by rfl⟩ : syracuseStep 802631 = 1203947) B1203947
theorem B12009323 : Blo 531801 12009323 := bstep (se 1 (by rfl) ⟨9006992, by rfl⟩ : syracuseStep 12009323 = 18013985) B18013985
theorem B802715 : Blo 531801 802715 := bstep (se 1 (by rfl) ⟨602036, by rfl⟩ : syracuseStep 802715 = 1204073) B1204073
theorem B6078401 : Blo 531801 6078401 := bstep (se 2 (by rfl) ⟨2279400, by rfl⟩ : syracuseStep 6078401 = 4558801) B4558801
theorem B11878487 : Blo 531801 11878487 := bstep (se 1 (by rfl) ⟨8908865, by rfl⟩ : syracuseStep 11878487 = 17817731) B17817731
theorem B901307 : Blo 531801 901307 := bstep (se 1 (by rfl) ⟨675980, by rfl⟩ : syracuseStep 901307 = 1351961) B1351961
theorem B803279 : Blo 531801 803279 := bstep (se 1 (by rfl) ⟨602459, by rfl⟩ : syracuseStep 803279 = 1204919) B1204919
theorem B803321 : Blo 531801 803321 := bstep (se 2 (by rfl) ⟨301245, by rfl⟩ : syracuseStep 803321 = 602491) B602491
theorem B803423 : Blo 531801 803423 := bstep (se 1 (by rfl) ⟨602567, by rfl⟩ : syracuseStep 803423 = 1205135) B1205135
theorem B901867 : Blo 531801 901867 := bstep (se 1 (by rfl) ⟨676400, by rfl⟩ : syracuseStep 901867 = 1352801) B1352801
theorem B1197161 : Blo 531801 1197161 := bstep (se 2 (by rfl) ⟨448935, by rfl⟩ : syracuseStep 1197161 = 897871) B897871
theorem B1525331 : Blo 531801 1525331 := bstep (se 1 (by rfl) ⟨1143998, by rfl⟩ : syracuseStep 1525331 = 2287997) B2287997
theorem B902839 : Blo 531801 902839 := bstep (se 1 (by rfl) ⟨677129, by rfl⟩ : syracuseStep 902839 = 1354259) B1354259
theorem B1197791 : Blo 531801 1197791 := bstep (se 1 (by rfl) ⟨898343, by rfl⟩ : syracuseStep 1197791 = 1796687) B1796687
theorem B903143 : Blo 531801 903143 := bstep (se 1 (by rfl) ⟨677357, by rfl⟩ : syracuseStep 903143 = 1354715) B1354715
theorem B903359 : Blo 531801 903359 := bstep (se 1 (by rfl) ⟨677519, by rfl⟩ : syracuseStep 903359 = 1355039) B1355039
theorem B1198619 : Blo 531801 1198619 := bstep (se 1 (by rfl) ⟨898964, by rfl⟩ : syracuseStep 1198619 = 1797929) B1797929
theorem B674335 : Blo 531801 674335 := bstep (se 1 (by rfl) ⟨505751, by rfl⟩ : syracuseStep 674335 = 1011503) B1011503
theorem B3885707 : Blo 531801 3885707 := bstep (se 1 (by rfl) ⟨2914280, by rfl⟩ : syracuseStep 3885707 = 5828561) B5828561
theorem B904027 : Blo 531801 904027 := bstep (se 1 (by rfl) ⟨678020, by rfl⟩ : syracuseStep 904027 = 1356041) B1356041
theorem B674887 : Blo 531801 674887 := bstep (se 1 (by rfl) ⟨506165, by rfl⟩ : syracuseStep 674887 = 1012331) B1012331
theorem B3755315 : Blo 531801 3755315 := bstep (se 1 (by rfl) ⟨2816486, by rfl⟩ : syracuseStep 3755315 = 5632973) B5632973
theorem B2706857 : Blo 531801 2706857 := bstep (se 2 (by rfl) ⟨1015071, by rfl⟩ : syracuseStep 2706857 = 2030143) B2030143
theorem B3853757 : Blo 531801 3853757 := bstep (se 3 (by rfl) ⟨722579, by rfl⟩ : syracuseStep 3853757 = 1445159) B1445159
theorem B4050809 : Blo 531801 4050809 := bstep (se 2 (by rfl) ⟨1519053, by rfl⟩ : syracuseStep 4050809 = 3038107) B3038107
theorem B2707343 : Blo 531801 2707343 := bstep (se 1 (by rfl) ⟨2030507, by rfl⟩ : syracuseStep 2707343 = 4061015) B4061015
theorem B1200095 : Blo 531801 1200095 := bstep (se 1 (by rfl) ⟨900071, by rfl⟩ : syracuseStep 1200095 = 1800143) B1800143
theorem B1200743 : Blo 531801 1200743 := bstep (se 1 (by rfl) ⟨900557, by rfl⟩ : syracuseStep 1200743 = 1801115) B1801115
theorem B676775 : Blo 531801 676775 := bstep (se 1 (by rfl) ⟨507581, by rfl⟩ : syracuseStep 676775 = 1015163) B1015163
theorem B1921963 : Blo 531801 1921963 := bstep (se 1 (by rfl) ⟨1441472, by rfl⟩ : syracuseStep 1921963 = 2882945) B2882945
theorem B18469883 : Blo 531801 18469883 := bstep (se 1 (by rfl) ⟨13852412, by rfl⟩ : syracuseStep 18469883 = 27704825) B27704825
theorem B676927 : Blo 531801 676927 := bstep (se 1 (by rfl) ⟨507695, by rfl⟩ : syracuseStep 676927 = 1015391) B1015391
theorem B7328987 : Blo 531801 7328987 := bstep (se 1 (by rfl) ⟨5496740, by rfl⟩ : syracuseStep 7328987 = 10993481) B10993481
theorem B1201427 : Blo 531801 1201427 := bstep (se 1 (by rfl) ⟨901070, by rfl⟩ : syracuseStep 1201427 = 1802141) B1802141
theorem B1201499 : Blo 531801 1201499 := bstep (se 1 (by rfl) ⟨901124, by rfl⟩ : syracuseStep 1201499 = 1802249) B1802249
theorem B2020727 : Blo 531801 2020727 := bstep (se 1 (by rfl) ⟨1515545, by rfl⟩ : syracuseStep 2020727 = 3031091) B3031091
theorem B1202057 : Blo 531801 1202057 := bstep (se 2 (by rfl) ⟨450771, by rfl⟩ : syracuseStep 1202057 = 901543) B901543
theorem B1923047 : Blo 531801 1923047 := bstep (se 1 (by rfl) ⟨1442285, by rfl⟩ : syracuseStep 1923047 = 2884571) B2884571
theorem B4577255 : Blo 531801 4577255 := bstep (se 1 (by rfl) ⟨3432941, by rfl⟩ : syracuseStep 4577255 = 6865883) B6865883
theorem B7821323 : Blo 531801 7821323 := bstep (se 1 (by rfl) ⟨5865992, by rfl⟩ : syracuseStep 7821323 = 11731985) B11731985
theorem B7297067 : Blo 531801 7297067 := bstep (se 1 (by rfl) ⟨5472800, by rfl⟩ : syracuseStep 7297067 = 10945601) B10945601
theorem B1202273 : Blo 531801 1202273 := bstep (se 2 (by rfl) ⟨450852, by rfl⟩ : syracuseStep 1202273 = 901705) B901705
theorem B1366313 : Blo 531801 1366313 := bstep (se 2 (by rfl) ⟨512367, by rfl⟩ : syracuseStep 1366313 = 1024735) B1024735
theorem B3037607 : Blo 531801 3037607 := bstep (se 1 (by rfl) ⟨2278205, by rfl⟩ : syracuseStep 3037607 = 4556411) B4556411
theorem B2709935 : Blo 531801 2709935 := bstep (se 1 (by rfl) ⟨2032451, by rfl⟩ : syracuseStep 2709935 = 4064903) B4064903
theorem B4053725 : Blo 531801 4053725 := bstep (se 3 (by rfl) ⟨760073, by rfl⟩ : syracuseStep 4053725 = 1520147) B1520147
theorem B3431609 : Blo 531801 3431609 := bstep (se 2 (by rfl) ⟨1286853, by rfl⟩ : syracuseStep 3431609 = 2573707) B2573707
theorem B4611275 : Blo 531801 4611275 := bstep (se 1 (by rfl) ⟨3458456, by rfl⟩ : syracuseStep 4611275 = 6916913) B6916913
theorem B4545953 : Blo 531801 4545953 := bstep (se 2 (by rfl) ⟨1704732, by rfl⟩ : syracuseStep 4545953 = 3409465) B3409465
theorem B1203623 : Blo 531801 1203623 := bstep (se 1 (by rfl) ⟨902717, by rfl⟩ : syracuseStep 1203623 = 1805435) B1805435
theorem B1203803 : Blo 531801 1203803 := bstep (se 1 (by rfl) ⟨902852, by rfl⟩ : syracuseStep 1203803 = 1805705) B1805705
theorem B15621983 : Blo 531801 15621983 := bstep (se 1 (by rfl) ⟨11716487, by rfl⟩ : syracuseStep 15621983 = 23432975) B23432975
theorem B21880685 : Blo 531801 21880685 := bstep (se 3 (by rfl) ⟨4102628, by rfl⟩ : syracuseStep 21880685 = 8205257) B8205257
theorem B1204091 : Blo 531801 1204091 := bstep (se 1 (by rfl) ⟨903068, by rfl⟩ : syracuseStep 1204091 = 1806137) B1806137
theorem B3891239 : Blo 531801 3891239 := bstep (se 1 (by rfl) ⟨2918429, by rfl⟩ : syracuseStep 3891239 = 5836859) B5836859
theorem B2023643 : Blo 531801 2023643 := bstep (se 1 (by rfl) ⟨1517732, by rfl⟩ : syracuseStep 2023643 = 3035465) B3035465
theorem B1204577 : Blo 531801 1204577 := bstep (se 2 (by rfl) ⟨451716, by rfl⟩ : syracuseStep 1204577 = 903433) B903433
theorem B1925495 : Blo 531801 1925495 := bstep (se 1 (by rfl) ⟨1444121, by rfl⟩ : syracuseStep 1925495 = 2888243) B2888243
theorem B1204667 : Blo 531801 1204667 := bstep (se 1 (by rfl) ⟨903500, by rfl⟩ : syracuseStep 1204667 = 1807001) B1807001
theorem B909775 : Blo 531801 909775 := bstep (se 1 (by rfl) ⟨682331, by rfl⟩ : syracuseStep 909775 = 1364663) B1364663
theorem B2712041 : Blo 531801 2712041 := bstep (se 2 (by rfl) ⟨1017015, by rfl⟩ : syracuseStep 2712041 = 2034031) B2034031
theorem B2712203 : Blo 531801 2712203 := bstep (se 1 (by rfl) ⟨2034152, by rfl⟩ : syracuseStep 2712203 = 4068305) B4068305
theorem B1794959 : Blo 531801 1794959 := bstep (se 1 (by rfl) ⟨1346219, by rfl⟩ : syracuseStep 1794959 = 2692439) B2692439
theorem B1795499 : Blo 531801 1795499 := bstep (se 1 (by rfl) ⟨1346624, by rfl⟩ : syracuseStep 1795499 = 2693249) B2693249
theorem B1926737 : Blo 531801 1926737 := bstep (se 2 (by rfl) ⟨722526, by rfl⟩ : syracuseStep 1926737 = 1445053) B1445053
theorem B2746075 : Blo 531801 2746075 := bstep (se 1 (by rfl) ⟨2059556, by rfl⟩ : syracuseStep 2746075 = 4119113) B4119113
theorem B1796039 : Blo 531801 1796039 := bstep (se 1 (by rfl) ⟨1347029, by rfl⟩ : syracuseStep 1796039 = 2694059) B2694059
theorem B3663863 : Blo 531801 3663863 := bstep (se 1 (by rfl) ⟨2747897, by rfl⟩ : syracuseStep 3663863 = 5495795) B5495795
theorem B977039 : Blo 531801 977039 := bstep (se 1 (by rfl) ⟨732779, by rfl⟩ : syracuseStep 977039 = 1465559) B1465559
theorem B911657 : Blo 531801 911657 := bstep (se 2 (by rfl) ⟨341871, by rfl⟩ : syracuseStep 911657 = 683743) B683743
theorem B813359 : Blo 531801 813359 := bstep (se 1 (by rfl) ⟨610019, by rfl⟩ : syracuseStep 813359 = 1220039) B1220039
theorem B1796795 : Blo 531801 1796795 := bstep (se 1 (by rfl) ⟨1347596, by rfl⟩ : syracuseStep 1796795 = 2695193) B2695193
theorem B814447 : Blo 531801 814447 := bstep (se 1 (by rfl) ⟨610835, by rfl⟩ : syracuseStep 814447 = 1221671) B1221671
theorem B4550053 : Blo 531801 4550053 := bstep (se 4 (by rfl) ⟨426567, by rfl⟩ : syracuseStep 4550053 = 853135) B853135
theorem B1371755 : Blo 531801 1371755 := bstep (se 1 (by rfl) ⟨1028816, by rfl⟩ : syracuseStep 1371755 = 2057633) B2057633
theorem B8745083 : Blo 531801 8745083 := bstep (se 1 (by rfl) ⟨6558812, by rfl⟩ : syracuseStep 8745083 = 13117625) B13117625
theorem B2158721 : Blo 531801 2158721 := bstep (se 2 (by rfl) ⟨809520, by rfl⟩ : syracuseStep 2158721 = 1619041) B1619041
theorem B6844763 : Blo 531801 6844763 := bstep (se 1 (by rfl) ⟨5133572, by rfl⟩ : syracuseStep 6844763 = 10267145) B10267145
theorem B2027987 : Blo 531801 2027987 := bstep (se 1 (by rfl) ⟨1520990, by rfl⟩ : syracuseStep 2027987 = 3041981) B3041981
theorem B1798739 : Blo 531801 1798739 := bstep (se 1 (by rfl) ⟨1349054, by rfl⟩ : syracuseStep 1798739 = 2698109) B2698109
theorem B1143391 : Blo 531801 1143391 := bstep (se 1 (by rfl) ⟨857543, by rfl⟩ : syracuseStep 1143391 = 1715087) B1715087
theorem B4551389 : Blo 531801 4551389 := bstep (se 3 (by rfl) ⟨853385, by rfl⟩ : syracuseStep 4551389 = 1706771) B1706771
theorem B1799387 : Blo 531801 1799387 := bstep (se 1 (by rfl) ⟨1349540, by rfl⟩ : syracuseStep 1799387 = 2699081) B2699081
theorem B2159891 : Blo 531801 2159891 := bstep (se 1 (by rfl) ⟨1619918, by rfl⟩ : syracuseStep 2159891 = 3239837) B3239837
theorem B10974503 : Blo 531801 10974503 := bstep (se 1 (by rfl) ⟨8230877, by rfl⟩ : syracuseStep 10974503 = 16461755) B16461755
theorem B20739629 : Blo 531801 20739629 := bstep (se 3 (by rfl) ⟨3888680, by rfl⟩ : syracuseStep 20739629 = 7777361) B7777361
theorem B1931003 : Blo 531801 1931003 := bstep (se 1 (by rfl) ⟨1448252, by rfl⟩ : syracuseStep 1931003 = 2896505) B2896505
theorem B4323149 : Blo 531801 4323149 := bstep (se 3 (by rfl) ⟨810590, by rfl⟩ : syracuseStep 4323149 = 1621181) B1621181
theorem B10417997 : Blo 531801 10417997 := bstep (se 3 (by rfl) ⟨1953374, by rfl⟩ : syracuseStep 10417997 = 3906749) B3906749
theorem B1013735 : Blo 531801 1013735 := bstep (se 1 (by rfl) ⟨760301, by rfl⟩ : syracuseStep 1013735 = 1520603) B1520603
theorem B1800251 : Blo 531801 1800251 := bstep (se 1 (by rfl) ⟨1350188, by rfl⟩ : syracuseStep 1800251 = 2700377) B2700377
theorem B4552787 : Blo 531801 4552787 := bstep (se 1 (by rfl) ⟨3414590, by rfl⟩ : syracuseStep 4552787 = 6829181) B6829181
theorem B1800521 : Blo 531801 1800521 := bstep (se 2 (by rfl) ⟨675195, by rfl⟩ : syracuseStep 1800521 = 1350391) B1350391
theorem B2260391 : Blo 531801 2260391 := bstep (se 1 (by rfl) ⟨1695293, by rfl⟩ : syracuseStep 2260391 = 3390587) B3390587
theorem B1801871 : Blo 531801 1801871 := bstep (se 1 (by rfl) ⟨1351403, by rfl⟩ : syracuseStep 1801871 = 2702807) B2702807
theorem B1539965 : Blo 531801 1539965 := bstep (se 3 (by rfl) ⟨288743, by rfl⟩ : syracuseStep 1539965 = 577487) B577487
theorem B12451843 : Blo 531801 12451843 := bstep (se 1 (by rfl) ⟨9338882, by rfl⟩ : syracuseStep 12451843 = 18677765) B18677765
theorem B2032087 : Blo 531801 2032087 := bstep (se 1 (by rfl) ⟨1524065, by rfl⟩ : syracuseStep 2032087 = 3048131) B3048131
theorem B2884349 : Blo 531801 2884349 := bstep (se 3 (by rfl) ⟨540815, by rfl⟩ : syracuseStep 2884349 = 1081631) B1081631
theorem B1016887 : Blo 531801 1016887 := bstep (se 1 (by rfl) ⟨762665, by rfl⟩ : syracuseStep 1016887 = 1525331) B1525331
theorem B2032847 : Blo 531801 2032847 := bstep (se 1 (by rfl) ⟨1524635, by rfl⟩ : syracuseStep 2032847 = 3049271) B3049271
theorem B1803545 : Blo 531801 1803545 := bstep (se 2 (by rfl) ⟨676329, by rfl⟩ : syracuseStep 1803545 = 1352659) B1352659
theorem B722255 : Blo 531801 722255 := bstep (se 1 (by rfl) ⟨541691, by rfl⟩ : syracuseStep 722255 = 1083383) B1083383
theorem B2590471 : Blo 531801 2590471 := bstep (se 1 (by rfl) ⟨1942853, by rfl⟩ : syracuseStep 2590471 = 3885707) B3885707
theorem B1804571 : Blo 531801 1804571 := bstep (se 1 (by rfl) ⟨1353428, by rfl⟩ : syracuseStep 1804571 = 2706857) B2706857
theorem B13699367 : Blo 531801 13699367 := bstep (se 1 (by rfl) ⟨10274525, by rfl⟩ : syracuseStep 13699367 = 20549051) B20549051
theorem B4852133 : Blo 531801 4852133 := bstep (se 4 (by rfl) ⟨454887, by rfl⟩ : syracuseStep 4852133 = 909775) B909775
theorem B1804733 : Blo 531801 1804733 := bstep (se 3 (by rfl) ⟨338387, by rfl⟩ : syracuseStep 1804733 = 676775) B676775
theorem B1804895 : Blo 531801 1804895 := bstep (se 1 (by rfl) ⟨1353671, by rfl⟩ : syracuseStep 1804895 = 2707343) B2707343
theorem B5114663 : Blo 531801 5114663 := bstep (se 1 (by rfl) ⟨3835997, by rfl⟩ : syracuseStep 5114663 = 7671995) B7671995
theorem B2559023 : Blo 531801 2559023 := bstep (se 1 (by rfl) ⟨1919267, by rfl⟩ : syracuseStep 2559023 = 3838535) B3838535
theorem B4328569 : Blo 531801 4328569 := bstep (se 2 (by rfl) ⟨1623213, by rfl⟩ : syracuseStep 4328569 = 3246427) B3246427
theorem B3247229 : Blo 531801 3247229 := bstep (se 3 (by rfl) ⟨608855, by rfl⟩ : syracuseStep 3247229 = 1217711) B1217711
theorem B1707193 : Blo 531801 1707193 := bstep (se 2 (by rfl) ⟨640197, by rfl⟩ : syracuseStep 1707193 = 1280395) B1280395
theorem B4885991 : Blo 531801 4885991 := bstep (se 1 (by rfl) ⟨3664493, by rfl⟩ : syracuseStep 4885991 = 7328987) B7328987
theorem B16453135 : Blo 531801 16453135 := bstep (se 1 (by rfl) ⟨12339851, by rfl⟩ : syracuseStep 16453135 = 24679703) B24679703
theorem B1347151 : Blo 531801 1347151 := bstep (se 1 (by rfl) ⟨1010363, by rfl⟩ : syracuseStep 1347151 = 2020727) B2020727
theorem B1282031 : Blo 531801 1282031 := bstep (se 1 (by rfl) ⟨961523, by rfl⟩ : syracuseStep 1282031 = 1923047) B1923047
theorem B3051503 : Blo 531801 3051503 := bstep (se 1 (by rfl) ⟨2288627, by rfl⟩ : syracuseStep 3051503 = 4577255) B4577255
theorem B5214215 : Blo 531801 5214215 := bstep (se 1 (by rfl) ⟨3910661, by rfl⟩ : syracuseStep 5214215 = 7821323) B7821323
theorem B10227779 : Blo 531801 10227779 := bstep (se 1 (by rfl) ⟨7670834, by rfl⟩ : syracuseStep 10227779 = 15341669) B15341669
theorem B1806623 : Blo 531801 1806623 := bstep (se 1 (by rfl) ⟨1354967, by rfl⟩ : syracuseStep 1806623 = 2709935) B2709935
theorem B1085929 : Blo 531801 1085929 := bstep (se 2 (by rfl) ⟨407223, by rfl⟩ : syracuseStep 1085929 = 814447) B814447
theorem B6066737 : Blo 531801 6066737 := bstep (se 2 (by rfl) ⟨2275026, by rfl⟩ : syracuseStep 6066737 = 4550053) B4550053
theorem B1709039 : Blo 531801 1709039 := bstep (se 1 (by rfl) ⟨1281779, by rfl⟩ : syracuseStep 1709039 = 2563559) B2563559
theorem B14587123 : Blo 531801 14587123 := bstep (se 1 (by rfl) ⟨10940342, by rfl⟩ : syracuseStep 14587123 = 21880685) B21880685
theorem B2594159 : Blo 531801 2594159 := bstep (se 1 (by rfl) ⟨1945619, by rfl⟩ : syracuseStep 2594159 = 3891239) B3891239
theorem B1349095 : Blo 531801 1349095 := bstep (se 1 (by rfl) ⟨1011821, by rfl⟩ : syracuseStep 1349095 = 2023643) B2023643
theorem B1807865 : Blo 531801 1807865 := bstep (se 2 (by rfl) ⟨677949, by rfl⟩ : syracuseStep 1807865 = 1355899) B1355899
theorem B1283663 : Blo 531801 1283663 := bstep (se 1 (by rfl) ⟨962747, by rfl⟩ : syracuseStep 1283663 = 1925495) B1925495
theorem B1808027 : Blo 531801 1808027 := bstep (se 1 (by rfl) ⟨1356020, by rfl⟩ : syracuseStep 1808027 = 2712041) B2712041
theorem B1808135 : Blo 531801 1808135 := bstep (se 1 (by rfl) ⟨1356101, by rfl⟩ : syracuseStep 1808135 = 2712203) B2712203
theorem B3643501 : Blo 531801 3643501 := bstep (se 3 (by rfl) ⟨683156, by rfl⟩ : syracuseStep 3643501 = 1366313) B1366313
theorem B2168957 : Blo 531801 2168957 := bstep (se 3 (by rfl) ⟨406679, by rfl⟩ : syracuseStep 2168957 = 813359) B813359
theorem B1284491 : Blo 531801 1284491 := bstep (se 1 (by rfl) ⟨963368, by rfl⟩ : syracuseStep 1284491 = 1926737) B1926737
theorem B2562617 : Blo 531801 2562617 := bstep (se 2 (by rfl) ⟨960981, by rfl⟩ : syracuseStep 2562617 = 1921963) B1921963
theorem B531919 : Blo 531801 531919 := bstep (se 1 (by rfl) ⟨398939, by rfl⟩ : syracuseStep 531919 = 797879) B797879
theorem B532079 : Blo 531801 532079 := bstep (se 1 (by rfl) ⟨399059, by rfl⟩ : syracuseStep 532079 = 798119) B798119
theorem B532135 : Blo 531801 532135 := bstep (se 1 (by rfl) ⟨399101, by rfl⟩ : syracuseStep 532135 = 798203) B798203
theorem B532199 : Blo 531801 532199 := bstep (se 1 (by rfl) ⟨399149, by rfl⟩ : syracuseStep 532199 = 798299) B798299
theorem B532255 : Blo 531801 532255 := bstep (se 1 (by rfl) ⟨399191, by rfl⟩ : syracuseStep 532255 = 798383) B798383
theorem B532335 : Blo 531801 532335 := bstep (se 1 (by rfl) ⟨399251, by rfl⟩ : syracuseStep 532335 = 798503) B798503
theorem B532391 : Blo 531801 532391 := bstep (se 1 (by rfl) ⟨399293, by rfl⟩ : syracuseStep 532391 = 798587) B798587
theorem B4989053 : Blo 531801 4989053 := bstep (se 3 (by rfl) ⟨935447, by rfl⟩ : syracuseStep 4989053 = 1870895) B1870895
theorem B532671 : Blo 531801 532671 := bstep (se 1 (by rfl) ⟨399503, by rfl⟩ : syracuseStep 532671 = 799007) B799007
theorem B532687 : Blo 531801 532687 := bstep (se 1 (by rfl) ⟨399515, by rfl⟩ : syracuseStep 532687 = 799031) B799031
theorem B4563175 : Blo 531801 4563175 := bstep (se 1 (by rfl) ⟨3422381, by rfl⟩ : syracuseStep 4563175 = 6844763) B6844763
theorem B532735 : Blo 531801 532735 := bstep (se 1 (by rfl) ⟨399551, by rfl⟩ : syracuseStep 532735 = 799103) B799103
theorem B532783 : Blo 531801 532783 := bstep (se 1 (by rfl) ⟨399587, by rfl⟩ : syracuseStep 532783 = 799175) B799175
theorem B1351991 : Blo 531801 1351991 := bstep (se 1 (by rfl) ⟨1013993, by rfl⟩ : syracuseStep 1351991 = 2027987) B2027987
theorem B10232243 : Blo 531801 10232243 := bstep (se 1 (by rfl) ⟨7674182, by rfl⟩ : syracuseStep 10232243 = 15348365) B15348365
theorem B4039145 : Blo 531801 4039145 := bstep (se 2 (by rfl) ⟨1514679, by rfl⟩ : syracuseStep 4039145 = 3029359) B3029359
theorem B533019 : Blo 531801 533019 := bstep (se 1 (by rfl) ⟨399764, by rfl⟩ : syracuseStep 533019 = 799529) B799529
theorem B533023 : Blo 531801 533023 := bstep (se 1 (by rfl) ⟨399767, by rfl⟩ : syracuseStep 533023 = 799535) B799535
theorem B598639 : Blo 531801 598639 := bstep (se 1 (by rfl) ⟨448979, by rfl⟩ : syracuseStep 598639 = 897959) B897959
theorem B533103 : Blo 531801 533103 := bstep (se 1 (by rfl) ⟨399827, by rfl⟩ : syracuseStep 533103 = 799655) B799655
theorem B533159 : Blo 531801 533159 := bstep (se 1 (by rfl) ⟨399869, by rfl⟩ : syracuseStep 533159 = 799739) B799739
theorem B533199 : Blo 531801 533199 := bstep (se 1 (by rfl) ⟨399899, by rfl⟩ : syracuseStep 533199 = 799799) B799799
theorem B598747 : Blo 531801 598747 := bstep (se 1 (by rfl) ⟨449060, by rfl⟩ : syracuseStep 598747 = 898121) B898121
theorem B533279 : Blo 531801 533279 := bstep (se 1 (by rfl) ⟨399959, by rfl⟩ : syracuseStep 533279 = 799919) B799919
theorem B7316335 : Blo 531801 7316335 := bstep (se 1 (by rfl) ⟨5487251, by rfl⟩ : syracuseStep 7316335 = 10974503) B10974503
theorem B2106283 : Blo 531801 2106283 := bstep (se 1 (by rfl) ⟨1579712, by rfl⟩ : syracuseStep 2106283 = 3159425) B3159425
theorem B533551 : Blo 531801 533551 := bstep (se 1 (by rfl) ⟨400163, by rfl⟩ : syracuseStep 533551 = 800327) B800327
theorem B533615 : Blo 531801 533615 := bstep (se 1 (by rfl) ⟨400211, by rfl⟩ : syracuseStep 533615 = 800423) B800423
theorem B533671 : Blo 531801 533671 := bstep (se 1 (by rfl) ⟨400253, by rfl⟩ : syracuseStep 533671 = 800507) B800507
theorem B2172071 : Blo 531801 2172071 := bstep (se 1 (by rfl) ⟨1629053, by rfl⟩ : syracuseStep 2172071 = 3258107) B3258107
theorem B1287335 : Blo 531801 1287335 := bstep (se 1 (by rfl) ⟨965501, by rfl⟩ : syracuseStep 1287335 = 1931003) B1931003
theorem B533695 : Blo 531801 533695 := bstep (se 1 (by rfl) ⟨400271, by rfl⟩ : syracuseStep 533695 = 800543) B800543
theorem B533727 : Blo 531801 533727 := bstep (se 1 (by rfl) ⟨400295, by rfl⟩ : syracuseStep 533727 = 800591) B800591
theorem B533807 : Blo 531801 533807 := bstep (se 1 (by rfl) ⟨400355, by rfl⟩ : syracuseStep 533807 = 800711) B800711
theorem B534043 : Blo 531801 534043 := bstep (se 1 (by rfl) ⟨400532, by rfl⟩ : syracuseStep 534043 = 801065) B801065
theorem B534047 : Blo 531801 534047 := bstep (se 1 (by rfl) ⟨400535, by rfl⟩ : syracuseStep 534047 = 801071) B801071
theorem B534207 : Blo 531801 534207 := bstep (se 1 (by rfl) ⟨400655, by rfl⟩ : syracuseStep 534207 = 801311) B801311
theorem B534463 : Blo 531801 534463 := bstep (se 1 (by rfl) ⟨400847, by rfl⟩ : syracuseStep 534463 = 801695) B801695
theorem B534495 : Blo 531801 534495 := bstep (se 1 (by rfl) ⟨400871, by rfl⟩ : syracuseStep 534495 = 801743) B801743
theorem B2566171 : Blo 531801 2566171 := bstep (se 1 (by rfl) ⟨1924628, by rfl⟩ : syracuseStep 2566171 = 3849257) B3849257
theorem B534555 : Blo 531801 534555 := bstep (se 1 (by rfl) ⟨400916, by rfl⟩ : syracuseStep 534555 = 801833) B801833
theorem B534559 : Blo 531801 534559 := bstep (se 1 (by rfl) ⟨400919, by rfl⟩ : syracuseStep 534559 = 801839) B801839
theorem B534575 : Blo 531801 534575 := bstep (se 1 (by rfl) ⟨400931, by rfl⟩ : syracuseStep 534575 = 801863) B801863
theorem B534751 : Blo 531801 534751 := bstep (se 1 (by rfl) ⟨401063, by rfl⟩ : syracuseStep 534751 = 802127) B802127
theorem B534811 : Blo 531801 534811 := bstep (se 1 (by rfl) ⟨401108, by rfl⟩ : syracuseStep 534811 = 802217) B802217
theorem B534911 : Blo 531801 534911 := bstep (se 1 (by rfl) ⟨401183, by rfl⟩ : syracuseStep 534911 = 802367) B802367
theorem B535087 : Blo 531801 535087 := bstep (se 1 (by rfl) ⟨401315, by rfl⟩ : syracuseStep 535087 = 802631) B802631
theorem B8006215 : Blo 531801 8006215 := bstep (se 1 (by rfl) ⟨6004661, by rfl⟩ : syracuseStep 8006215 = 12009323) B12009323
theorem B1026643 : Blo 531801 1026643 := bstep (se 1 (by rfl) ⟨769982, by rfl⟩ : syracuseStep 1026643 = 1539965) B1539965
theorem B535143 : Blo 531801 535143 := bstep (se 1 (by rfl) ⟨401357, by rfl⟩ : syracuseStep 535143 = 802715) B802715
theorem B600871 : Blo 531801 600871 := bstep (se 1 (by rfl) ⟨450653, by rfl⟩ : syracuseStep 600871 = 901307) B901307
theorem B535519 : Blo 531801 535519 := bstep (se 1 (by rfl) ⟨401639, by rfl⟩ : syracuseStep 535519 = 803279) B803279
theorem B535547 : Blo 531801 535547 := bstep (se 1 (by rfl) ⟨401660, by rfl⟩ : syracuseStep 535547 = 803321) B803321
theorem B535615 : Blo 531801 535615 := bstep (se 1 (by rfl) ⟨401711, by rfl⟩ : syracuseStep 535615 = 803423) B803423
theorem B2272499 : Blo 531801 2272499 := bstep (se 1 (by rfl) ⟨1704374, by rfl⟩ : syracuseStep 2272499 = 3408749) B3408749
theorem B961811 : Blo 531801 961811 := bstep (se 1 (by rfl) ⟨721358, by rfl⟩ : syracuseStep 961811 = 1442717) B1442717
theorem B798107 : Blo 531801 798107 := bstep (se 1 (by rfl) ⟨598580, by rfl⟩ : syracuseStep 798107 = 1197161) B1197161
theorem B798527 : Blo 531801 798527 := bstep (se 1 (by rfl) ⟨598895, by rfl⟩ : syracuseStep 798527 = 1197791) B1197791
theorem B602095 : Blo 531801 602095 := bstep (se 1 (by rfl) ⟨451571, by rfl⟩ : syracuseStep 602095 = 903143) B903143
theorem B798713 : Blo 531801 798713 := bstep (se 2 (by rfl) ⟨299517, by rfl⟩ : syracuseStep 798713 = 599035) B599035
theorem B602239 : Blo 531801 602239 := bstep (se 1 (by rfl) ⟨451679, by rfl⟩ : syracuseStep 602239 = 903359) B903359
theorem B4108519 : Blo 531801 4108519 := bstep (se 1 (by rfl) ⟨3081389, by rfl⟩ : syracuseStep 4108519 = 6162779) B6162779
theorem B798953 : Blo 531801 798953 := bstep (se 2 (by rfl) ⟨299607, by rfl⟩ : syracuseStep 798953 = 599215) B599215
theorem B799079 : Blo 531801 799079 := bstep (se 1 (by rfl) ⟨599309, by rfl⟩ : syracuseStep 799079 = 1198619) B1198619
theorem B3420589 : Blo 531801 3420589 := bstep (se 3 (by rfl) ⟨641360, by rfl⟩ : syracuseStep 3420589 = 1282721) B1282721
theorem B2503543 : Blo 531801 2503543 := bstep (se 1 (by rfl) ⟨1877657, by rfl⟩ : syracuseStep 2503543 = 3755315) B3755315
theorem B799625 : Blo 531801 799625 := bstep (se 2 (by rfl) ⟨299859, by rfl⟩ : syracuseStep 799625 = 599719) B599719
theorem B2569171 : Blo 531801 2569171 := bstep (se 1 (by rfl) ⟨1926878, by rfl⟩ : syracuseStep 2569171 = 3853757) B3853757
theorem B2700539 : Blo 531801 2700539 := bstep (se 1 (by rfl) ⟨2025404, by rfl⟩ : syracuseStep 2700539 = 4050809) B4050809
theorem B800009 : Blo 531801 800009 := bstep (se 2 (by rfl) ⟨300003, by rfl⟩ : syracuseStep 800009 = 600007) B600007
theorem B800063 : Blo 531801 800063 := bstep (se 1 (by rfl) ⟨600047, by rfl⟩ : syracuseStep 800063 = 1200095) B1200095
theorem B4568507 : Blo 531801 4568507 := bstep (se 1 (by rfl) ⟨3426380, by rfl⟩ : syracuseStep 4568507 = 6852761) B6852761
theorem B2274925 : Blo 531801 2274925 := bstep (se 3 (by rfl) ⟨426548, by rfl⟩ : syracuseStep 2274925 = 853097) B853097
theorem B2274959 : Blo 531801 2274959 := bstep (se 1 (by rfl) ⟨1706219, by rfl⟩ : syracuseStep 2274959 = 3412439) B3412439
theorem B9221795 : Blo 531801 9221795 := bstep (se 1 (by rfl) ⟨6916346, by rfl⟩ : syracuseStep 9221795 = 13832693) B13832693
theorem B800489 : Blo 531801 800489 := bstep (se 2 (by rfl) ⟨300183, by rfl⟩ : syracuseStep 800489 = 600367) B600367
theorem B800495 : Blo 531801 800495 := bstep (se 1 (by rfl) ⟨600371, by rfl⟩ : syracuseStep 800495 = 1200743) B1200743
theorem B899113 : Blo 531801 899113 := bstep (se 2 (by rfl) ⟨337167, by rfl⟩ : syracuseStep 899113 = 674335) B674335
theorem B899255 : Blo 531801 899255 := bstep (se 1 (by rfl) ⟨674441, by rfl⟩ : syracuseStep 899255 = 1348883) B1348883
theorem B800951 : Blo 531801 800951 := bstep (se 1 (by rfl) ⟨600713, by rfl⟩ : syracuseStep 800951 = 1201427) B1201427
theorem B2275559 : Blo 531801 2275559 := bstep (se 1 (by rfl) ⟨1706669, by rfl⟩ : syracuseStep 2275559 = 3413339) B3413339
theorem B800999 : Blo 531801 800999 := bstep (se 1 (by rfl) ⟨600749, by rfl⟩ : syracuseStep 800999 = 1201499) B1201499
theorem B571807 : Blo 531801 571807 := bstep (se 1 (by rfl) ⟨428855, by rfl⟩ : syracuseStep 571807 = 857711) B857711
theorem B2275847 : Blo 531801 2275847 := bstep (se 1 (by rfl) ⟨1706885, by rfl⟩ : syracuseStep 2275847 = 3413771) B3413771
theorem B801371 : Blo 531801 801371 := bstep (se 1 (by rfl) ⟨601028, by rfl⟩ : syracuseStep 801371 = 1202057) B1202057
theorem B4864711 : Blo 531801 4864711 := bstep (se 1 (by rfl) ⟨3648533, by rfl⟩ : syracuseStep 4864711 = 7297067) B7297067
theorem B801515 : Blo 531801 801515 := bstep (se 1 (by rfl) ⟨601136, by rfl⟩ : syracuseStep 801515 = 1202273) B1202273
theorem B899849 : Blo 531801 899849 := bstep (se 2 (by rfl) ⟨337443, by rfl⟩ : syracuseStep 899849 = 674887) B674887
theorem B801545 : Blo 531801 801545 := bstep (se 2 (by rfl) ⟨300579, by rfl⟩ : syracuseStep 801545 = 601159) B601159
theorem B2702483 : Blo 531801 2702483 := bstep (se 1 (by rfl) ⟨2026862, by rfl⟩ : syracuseStep 2702483 = 4053725) B4053725
theorem B3030635 : Blo 531801 3030635 := bstep (se 1 (by rfl) ⟨2272976, by rfl⟩ : syracuseStep 3030635 = 4545953) B4545953
theorem B802415 : Blo 531801 802415 := bstep (se 1 (by rfl) ⟨601811, by rfl⟩ : syracuseStep 802415 = 1203623) B1203623
theorem B802535 : Blo 531801 802535 := bstep (se 1 (by rfl) ⟨601901, by rfl⟩ : syracuseStep 802535 = 1203803) B1203803
theorem B802727 : Blo 531801 802727 := bstep (se 1 (by rfl) ⟨602045, by rfl⟩ : syracuseStep 802727 = 1204091) B1204091
theorem B2703293 : Blo 531801 2703293 := bstep (se 3 (by rfl) ⟨506867, by rfl⟩ : syracuseStep 2703293 = 1013735) B1013735
theorem B803051 : Blo 531801 803051 := bstep (se 1 (by rfl) ⟨602288, by rfl⟩ : syracuseStep 803051 = 1204577) B1204577
theorem B901415 : Blo 531801 901415 := bstep (se 1 (by rfl) ⟨676061, by rfl⟩ : syracuseStep 901415 = 1352123) B1352123
theorem B803111 : Blo 531801 803111 := bstep (se 1 (by rfl) ⟨602333, by rfl⟩ : syracuseStep 803111 = 1204667) B1204667
theorem B1196639 : Blo 531801 1196639 := bstep (se 1 (by rfl) ⟨897479, by rfl⟩ : syracuseStep 1196639 = 1794959) B1794959
theorem B4571923 : Blo 531801 4571923 := bstep (se 1 (by rfl) ⟨3428942, by rfl⟩ : syracuseStep 4571923 = 6857885) B6857885
theorem B639775 : Blo 531801 639775 := bstep (se 1 (by rfl) ⟨479831, by rfl⟩ : syracuseStep 639775 = 959663) B959663
theorem B1524521 : Blo 531801 1524521 := bstep (se 2 (by rfl) ⟨571695, by rfl⟩ : syracuseStep 1524521 = 1143391) B1143391
theorem B4637627 : Blo 531801 4637627 := bstep (se 1 (by rfl) ⟨3478220, by rfl⟩ : syracuseStep 4637627 = 6956441) B6956441
theorem B1196999 : Blo 531801 1196999 := bstep (se 1 (by rfl) ⟨897749, by rfl⟩ : syracuseStep 1196999 = 1795499) B1795499
theorem B1623079 : Blo 531801 1623079 := bstep (se 1 (by rfl) ⟨1217309, by rfl⟩ : syracuseStep 1623079 = 2434619) B2434619
theorem B1197359 : Blo 531801 1197359 := bstep (se 1 (by rfl) ⟨898019, by rfl⟩ : syracuseStep 1197359 = 1796039) B1796039
theorem B2442575 : Blo 531801 2442575 := bstep (se 1 (by rfl) ⟨1831931, by rfl⟩ : syracuseStep 2442575 = 3663863) B3663863
theorem B902569 : Blo 531801 902569 := bstep (se 2 (by rfl) ⟨338463, by rfl⟩ : syracuseStep 902569 = 676927) B676927
theorem B607771 : Blo 531801 607771 := bstep (se 1 (by rfl) ⟨455828, by rfl⟩ : syracuseStep 607771 = 911657) B911657
theorem B2278975 : Blo 531801 2278975 := bstep (se 1 (by rfl) ⟨1709231, by rfl⟩ : syracuseStep 2278975 = 3418463) B3418463
theorem B1197863 : Blo 531801 1197863 := bstep (se 1 (by rfl) ⟨898397, by rfl⟩ : syracuseStep 1197863 = 1796795) B1796795
theorem B1198241 : Blo 531801 1198241 := bstep (se 2 (by rfl) ⟨449340, by rfl⟩ : syracuseStep 1198241 = 898681) B898681
theorem B641515 : Blo 531801 641515 := bstep (se 1 (by rfl) ⟨481136, by rfl⟩ : syracuseStep 641515 = 962273) B962273
theorem B1198889 : Blo 531801 1198889 := bstep (se 2 (by rfl) ⟨449583, by rfl⟩ : syracuseStep 1198889 = 899167) B899167
theorem B4049837 : Blo 531801 4049837 := bstep (se 3 (by rfl) ⟨759344, by rfl⟩ : syracuseStep 4049837 = 1518689) B1518689
theorem B642043 : Blo 531801 642043 := bstep (se 1 (by rfl) ⟨481532, by rfl⟩ : syracuseStep 642043 = 963065) B963065
theorem B1199159 : Blo 531801 1199159 := bstep (se 1 (by rfl) ⟨899369, by rfl⟩ : syracuseStep 1199159 = 1798739) B1798739
theorem B3034259 : Blo 531801 3034259 := bstep (se 1 (by rfl) ⟨2275694, by rfl⟩ : syracuseStep 3034259 = 4551389) B4551389
theorem B5328293 : Blo 531801 5328293 := bstep (se 4 (by rfl) ⟨499527, by rfl⟩ : syracuseStep 5328293 = 999055) B999055
theorem B1199591 : Blo 531801 1199591 := bstep (se 1 (by rfl) ⟨899693, by rfl⟩ : syracuseStep 1199591 = 1799387) B1799387
theorem B1200167 : Blo 531801 1200167 := bstep (se 1 (by rfl) ⟨900125, by rfl⟩ : syracuseStep 1200167 = 1800251) B1800251
theorem B3035191 : Blo 531801 3035191 := bstep (se 1 (by rfl) ⟨2276393, by rfl⟩ : syracuseStep 3035191 = 4552787) B4552787
theorem B2019451 : Blo 531801 2019451 := bstep (se 1 (by rfl) ⟨1514588, by rfl⟩ : syracuseStep 2019451 = 3029177) B3029177
theorem B1200347 : Blo 531801 1200347 := bstep (se 1 (by rfl) ⟨900260, by rfl⟩ : syracuseStep 1200347 = 1800521) B1800521
theorem B1200617 : Blo 531801 1200617 := bstep (se 2 (by rfl) ⟨450231, by rfl⟩ : syracuseStep 1200617 = 900463) B900463
theorem B643639 : Blo 531801 643639 := bstep (se 1 (by rfl) ⟨482729, by rfl⟩ : syracuseStep 643639 = 965459) B965459
theorem B1201121 : Blo 531801 1201121 := bstep (se 2 (by rfl) ⟨450420, by rfl⟩ : syracuseStep 1201121 = 900841) B900841
theorem B1201247 : Blo 531801 1201247 := bstep (se 1 (by rfl) ⟨900935, by rfl⟩ : syracuseStep 1201247 = 1801871) B1801871
theorem B4052267 : Blo 531801 4052267 := bstep (se 1 (by rfl) ⟨3039200, by rfl⟩ : syracuseStep 4052267 = 6078401) B6078401
theorem B7918991 : Blo 531801 7918991 := bstep (se 1 (by rfl) ⟨5939243, by rfl⟩ : syracuseStep 7918991 = 11878487) B11878487
theorem B1136207 : Blo 531801 1136207 := bstep (se 1 (by rfl) ⟨852155, by rfl⟩ : syracuseStep 1136207 = 1704311) B1704311
theorem B1202003 : Blo 531801 1202003 := bstep (se 1 (by rfl) ⟨901502, by rfl⟩ : syracuseStep 1202003 = 1803005) B1803005
theorem B1202489 : Blo 531801 1202489 := bstep (se 2 (by rfl) ⟨450933, by rfl⟩ : syracuseStep 1202489 = 901867) B901867
theorem B6510905 : Blo 531801 6510905 := bstep (se 2 (by rfl) ⟨2441589, by rfl⟩ : syracuseStep 6510905 = 4883179) B4883179
theorem B1203407 : Blo 531801 1203407 := bstep (se 1 (by rfl) ⟨902555, by rfl⟩ : syracuseStep 1203407 = 1805111) B1805111
theorem B4120001 : Blo 531801 4120001 := bstep (se 2 (by rfl) ⟨1545000, by rfl⟩ : syracuseStep 4120001 = 3090001) B3090001
theorem B1465847 : Blo 531801 1465847 := bstep (se 1 (by rfl) ⟨1099385, by rfl⟩ : syracuseStep 1465847 = 2198771) B2198771
theorem B23092775 : Blo 531801 23092775 := bstep (se 1 (by rfl) ⟨17319581, by rfl⟩ : syracuseStep 23092775 = 34639163) B34639163
theorem B1203785 : Blo 531801 1203785 := bstep (se 2 (by rfl) ⟨451419, by rfl⟩ : syracuseStep 1203785 = 902839) B902839
theorem B3661433 : Blo 531801 3661433 := bstep (se 2 (by rfl) ⟨1373037, by rfl⟩ : syracuseStep 3661433 = 2746075) B2746075
theorem B3432223 : Blo 531801 3432223 := bstep (se 1 (by rfl) ⟨2574167, by rfl⟩ : syracuseStep 3432223 = 5148335) B5148335
theorem B12313255 : Blo 531801 12313255 := bstep (se 1 (by rfl) ⟨9234941, by rfl⟩ : syracuseStep 12313255 = 18469883) B18469883
theorem B1204955 : Blo 531801 1204955 := bstep (se 1 (by rfl) ⟨903716, by rfl⟩ : syracuseStep 1204955 = 1807433) B1807433
theorem B1205369 : Blo 531801 1205369 := bstep (se 2 (by rfl) ⟨452013, by rfl⟩ : syracuseStep 1205369 = 904027) B904027
theorem B2025071 : Blo 531801 2025071 := bstep (se 1 (by rfl) ⟨1518803, by rfl⟩ : syracuseStep 2025071 = 3037607) B3037607
theorem B2287739 : Blo 531801 2287739 := bstep (se 1 (by rfl) ⟨1715804, by rfl⟩ : syracuseStep 2287739 = 3431609) B3431609
theorem B3074183 : Blo 531801 3074183 := bstep (se 1 (by rfl) ⟨2305637, by rfl⟩ : syracuseStep 3074183 = 4611275) B4611275
theorem B2877605 : Blo 531801 2877605 := bstep (se 4 (by rfl) ⟨269775, by rfl⟩ : syracuseStep 2877605 = 539551) B539551
theorem B27781325 : Blo 531801 27781325 := bstep (se 3 (by rfl) ⟨5208998, by rfl⟩ : syracuseStep 27781325 = 10417997) B10417997
theorem B2156777 : Blo 531801 2156777 := bstep (se 2 (by rfl) ⟨808791, by rfl⟩ : syracuseStep 2156777 = 1617583) B1617583
theorem B4680119 : Blo 531801 4680119 := bstep (se 1 (by rfl) ⟨3510089, by rfl⟩ : syracuseStep 4680119 = 7020179) B7020179
theorem B10414655 : Blo 531801 10414655 := bstep (se 1 (by rfl) ⟨7810991, by rfl⟩ : syracuseStep 10414655 = 15621983) B15621983
theorem B3074989 : Blo 531801 3074989 := bstep (se 3 (by rfl) ⟨576560, by rfl⟩ : syracuseStep 3074989 = 1153121) B1153121
theorem B31124405 : Blo 531801 31124405 := bstep (se 5 (by rfl) ⟨1458956, by rfl⟩ : syracuseStep 31124405 = 2917913) B2917913
theorem B2059847 : Blo 531801 2059847 := bstep (se 1 (by rfl) ⟨1544885, by rfl⟩ : syracuseStep 2059847 = 3089771) B3089771
theorem B651359 : Blo 531801 651359 := bstep (se 1 (by rfl) ⟨488519, by rfl⟩ : syracuseStep 651359 = 977039) B977039
theorem B1929359 : Blo 531801 1929359 := bstep (se 1 (by rfl) ⟨1447019, by rfl⟩ : syracuseStep 1929359 = 2894039) B2894039
theorem B1011943 : Blo 531801 1011943 := bstep (se 1 (by rfl) ⟨758957, by rfl⟩ : syracuseStep 1011943 = 1517915) B1517915
theorem B4059557 : Blo 531801 4059557 := bstep (se 4 (by rfl) ⟨380583, by rfl⟩ : syracuseStep 4059557 = 761167) B761167
theorem B1143247 : Blo 531801 1143247 := bstep (se 1 (by rfl) ⟨857435, by rfl⟩ : syracuseStep 1143247 = 1714871) B1714871
theorem B1012475 : Blo 531801 1012475 := bstep (se 1 (by rfl) ⟨759356, by rfl⟩ : syracuseStep 1012475 = 1518713) B1518713
theorem B914503 : Blo 531801 914503 := bstep (se 1 (by rfl) ⟨685877, by rfl⟩ : syracuseStep 914503 = 1371755) B1371755
theorem B8221769 : Blo 531801 8221769 := bstep (se 2 (by rfl) ⟨3083163, by rfl⟩ : syracuseStep 8221769 = 6166327) B6166327
theorem B1012999 : Blo 531801 1012999 := bstep (se 1 (by rfl) ⟨759749, by rfl⟩ : syracuseStep 1012999 = 1519499) B1519499
theorem B5141879 : Blo 531801 5141879 := bstep (se 1 (by rfl) ⟨3856409, by rfl⟩ : syracuseStep 5141879 = 7712819) B7712819
theorem B5830055 : Blo 531801 5830055 := bstep (se 1 (by rfl) ⟨4372541, by rfl⟩ : syracuseStep 5830055 = 8745083) B8745083
theorem B1439147 : Blo 531801 1439147 := bstep (se 1 (by rfl) ⟨1079360, by rfl⟩ : syracuseStep 1439147 = 2158721) B2158721
theorem B6846403 : Blo 531801 6846403 := bstep (se 1 (by rfl) ⟨5134802, by rfl⟩ : syracuseStep 6846403 = 10269605) B10269605
theorem B1439927 : Blo 531801 1439927 := bstep (se 1 (by rfl) ⟨1079945, by rfl⟩ : syracuseStep 1439927 = 2159891) B2159891
theorem B6846767 : Blo 531801 6846767 := bstep (se 1 (by rfl) ⟨5135075, by rfl⟩ : syracuseStep 6846767 = 10270151) B10270151
theorem B13826419 : Blo 531801 13826419 := bstep (se 1 (by rfl) ⟨10369814, by rfl⟩ : syracuseStep 13826419 = 20739629) B20739629
theorem B6027709 : Blo 531801 6027709 := bstep (se 3 (by rfl) ⟨1130195, by rfl⟩ : syracuseStep 6027709 = 2260391) B2260391
theorem B3242537 : Blo 531801 3242537 := bstep (se 2 (by rfl) ⟨1215951, by rfl⟩ : syracuseStep 3242537 = 2431903) B2431903
theorem B2882099 : Blo 531801 2882099 := bstep (se 1 (by rfl) ⟨2161574, by rfl⟩ : syracuseStep 2882099 = 4323149) B4323149
theorem B2030417 : Blo 531801 2030417 := bstep (se 2 (by rfl) ⟨761406, by rfl⟩ : syracuseStep 2030417 = 1522813) B1522813
theorem B1801439 : Blo 531801 1801439 := bstep (se 1 (by rfl) ⟨1351079, by rfl⟩ : syracuseStep 1801439 = 2702159) B2702159
theorem B3046855 : Blo 531801 3046855 := bstep (se 1 (by rfl) ⟨2285141, by rfl⟩ : syracuseStep 3046855 = 4570283) B4570283
theorem B1015247 : Blo 531801 1015247 := bstep (se 1 (by rfl) ⟨761435, by rfl⟩ : syracuseStep 1015247 = 1522871) B1522871
theorem B4947655 : Blo 531801 4947655 := bstep (se 1 (by rfl) ⟨3710741, by rfl⟩ : syracuseStep 4947655 = 7421483) B7421483
theorem B9273041 : Blo 531801 9273041 := bstep (se 2 (by rfl) ⟨3477390, by rfl⟩ : syracuseStep 9273041 = 6954781) B6954781
theorem B1736957 : Blo 531801 1736957 := bstep (se 3 (by rfl) ⟨325679, by rfl⟩ : syracuseStep 1736957 = 651359) B651359
theorem B16417673 : Blo 531801 16417673 := bstep (se 2 (by rfl) ⟨6156627, by rfl⟩ : syracuseStep 16417673 = 12313255) B12313255
theorem B6095897 : Blo 531801 6095897 := bstep (se 2 (by rfl) ⟨2285961, by rfl⟩ : syracuseStep 6095897 = 4571923) B4571923
theorem B853033 : Blo 531801 853033 := bstep (se 2 (by rfl) ⟨319887, by rfl⟩ : syracuseStep 853033 = 639775) B639775
theorem B2164105 : Blo 531801 2164105 := bstep (se 2 (by rfl) ⟨811539, by rfl⟩ : syracuseStep 2164105 = 1623079) B1623079
theorem B3409775 : Blo 531801 3409775 := bstep (se 1 (by rfl) ⟨2557331, by rfl⟩ : syracuseStep 3409775 = 5114663) B5114663
theorem B1706015 : Blo 531801 1706015 := bstep (se 1 (by rfl) ⟨1279511, by rfl⟩ : syracuseStep 1706015 = 2559023) B2559023
theorem B2164819 : Blo 531801 2164819 := bstep (se 1 (by rfl) ⟨1623614, by rfl⟩ : syracuseStep 2164819 = 3247229) B3247229
theorem B4065389 : Blo 531801 4065389 := bstep (se 3 (by rfl) ⟨762260, by rfl⟩ : syracuseStep 4065389 = 1524521) B1524521
theorem B854687 : Blo 531801 854687 := bstep (se 1 (by rfl) ⟨641015, by rfl⟩ : syracuseStep 854687 = 1282031) B1282031
theorem B2034335 : Blo 531801 2034335 := bstep (se 1 (by rfl) ⟨1525751, by rfl⟩ : syracuseStep 2034335 = 3051503) B3051503
theorem B3476143 : Blo 531801 3476143 := bstep (se 1 (by rfl) ⟨2607107, by rfl⟩ : syracuseStep 3476143 = 5214215) B5214215
theorem B6818519 : Blo 531801 6818519 := bstep (se 1 (by rfl) ⟨5113889, by rfl⟩ : syracuseStep 6818519 = 10227779) B10227779
theorem B855353 : Blo 531801 855353 := bstep (se 2 (by rfl) ⟨320757, by rfl⟩ : syracuseStep 855353 = 641515) B641515
theorem B5279327 : Blo 531801 5279327 := bstep (se 1 (by rfl) ⟨3959495, by rfl⟩ : syracuseStep 5279327 = 7918991) B7918991
theorem B855775 : Blo 531801 855775 := bstep (se 1 (by rfl) ⟨641831, by rfl⟩ : syracuseStep 855775 = 1283663) B1283663
theorem B3837725 : Blo 531801 3837725 := bstep (se 3 (by rfl) ⟨719573, by rfl⟩ : syracuseStep 3837725 = 1439147) B1439147
theorem B4099985 : Blo 531801 4099985 := bstep (se 2 (by rfl) ⟨1537494, by rfl⟩ : syracuseStep 4099985 = 3074989) B3074989
theorem B856057 : Blo 531801 856057 := bstep (se 2 (by rfl) ⟨321021, by rfl⟩ : syracuseStep 856057 = 642043) B642043
theorem B5771425 : Blo 531801 5771425 := bstep (se 2 (by rfl) ⟨2164284, by rfl⟩ : syracuseStep 5771425 = 4328569) B4328569
theorem B856327 : Blo 531801 856327 := bstep (se 1 (by rfl) ⟨642245, by rfl⟩ : syracuseStep 856327 = 1284491) B1284491
theorem B2692601 : Blo 531801 2692601 := bstep (se 2 (by rfl) ⟨1009725, by rfl⟩ : syracuseStep 2692601 = 2019451) B2019451
theorem B6821495 : Blo 531801 6821495 := bstep (se 1 (by rfl) ⟨5116121, by rfl⟩ : syracuseStep 6821495 = 10232243) B10232243
theorem B1349257 : Blo 531801 1349257 := bstep (se 2 (by rfl) ⟨505971, by rfl⟩ : syracuseStep 1349257 = 1011943) B1011943
theorem B5478025 : Blo 531801 5478025 := bstep (se 2 (by rfl) ⟨2054259, by rfl⟩ : syracuseStep 5478025 = 4108519) B4108519
theorem B2692763 : Blo 531801 2692763 := bstep (se 1 (by rfl) ⟨2019572, by rfl⟩ : syracuseStep 2692763 = 4039145) B4039145
theorem B4560785 : Blo 531801 4560785 := bstep (se 2 (by rfl) ⟨1710294, by rfl⟩ : syracuseStep 4560785 = 3420589) B3420589
theorem B858185 : Blo 531801 858185 := bstep (se 2 (by rfl) ⟨321819, by rfl⟩ : syracuseStep 858185 = 643639) B643639
theorem B1448047 : Blo 531801 1448047 := bstep (se 1 (by rfl) ⟨1086035, by rfl⟩ : syracuseStep 1448047 = 2172071) B2172071
theorem B858223 : Blo 531801 858223 := bstep (se 1 (by rfl) ⟨643667, by rfl⟩ : syracuseStep 858223 = 1287335) B1287335
theorem B1350047 : Blo 531801 1350047 := bstep (se 1 (by rfl) ⟨1012535, by rfl⟩ : syracuseStep 1350047 = 2025071) B2025071
theorem B1219337 : Blo 531801 1219337 := bstep (se 2 (by rfl) ⟨457251, by rfl⟩ : syracuseStep 1219337 = 914503) B914503
theorem B18520883 : Blo 531801 18520883 := bstep (se 1 (by rfl) ⟨13890662, by rfl⟩ : syracuseStep 18520883 = 27781325) B27781325
theorem B3120079 : Blo 531801 3120079 := bstep (se 1 (by rfl) ⟨2340059, by rfl⟩ : syracuseStep 3120079 = 4680119) B4680119
theorem B1350665 : Blo 531801 1350665 := bstep (se 2 (by rfl) ⟨506499, by rfl⟩ : syracuseStep 1350665 = 1012999) B1012999
theorem B20749603 : Blo 531801 20749603 := bstep (se 1 (by rfl) ⟨15562202, by rfl⟩ : syracuseStep 20749603 = 31124405) B31124405
theorem B1514999 : Blo 531801 1514999 := bstep (se 1 (by rfl) ⟨1136249, by rfl⟩ : syracuseStep 1514999 = 2272499) B2272499
theorem B532071 : Blo 531801 532071 := bstep (se 1 (by rfl) ⟨399053, by rfl⟩ : syracuseStep 532071 = 798107) B798107
theorem B532351 : Blo 531801 532351 := bstep (se 1 (by rfl) ⟨399263, by rfl⟩ : syracuseStep 532351 = 798527) B798527
theorem B532475 : Blo 531801 532475 := bstep (se 1 (by rfl) ⟨399356, by rfl⟩ : syracuseStep 532475 = 798713) B798713
theorem B1286239 : Blo 531801 1286239 := bstep (se 1 (by rfl) ⟨964679, by rfl⟩ : syracuseStep 1286239 = 1929359) B1929359
theorem B4858001 : Blo 531801 4858001 := bstep (se 2 (by rfl) ⟨1821750, by rfl⟩ : syracuseStep 4858001 = 3643501) B3643501
theorem B532635 : Blo 531801 532635 := bstep (se 1 (by rfl) ⟨399476, by rfl⟩ : syracuseStep 532635 = 798953) B798953
theorem B532719 : Blo 531801 532719 := bstep (se 1 (by rfl) ⟨399539, by rfl⟩ : syracuseStep 532719 = 799079) B799079
theorem B762409 : Blo 531801 762409 := bstep (se 2 (by rfl) ⟨285903, by rfl⟩ : syracuseStep 762409 = 571807) B571807
theorem B8036945 : Blo 531801 8036945 := bstep (se 2 (by rfl) ⟨3013854, by rfl⟩ : syracuseStep 8036945 = 6027709) B6027709
theorem B533083 : Blo 531801 533083 := bstep (se 1 (by rfl) ⟨399812, by rfl⟩ : syracuseStep 533083 = 799625) B799625
theorem B5481179 : Blo 531801 5481179 := bstep (se 1 (by rfl) ⟨4110884, by rfl⟩ : syracuseStep 5481179 = 8221769) B8221769
theorem B533339 : Blo 531801 533339 := bstep (se 1 (by rfl) ⟨400004, by rfl⟩ : syracuseStep 533339 = 800009) B800009
theorem B533375 : Blo 531801 533375 := bstep (se 1 (by rfl) ⟨400031, by rfl⟩ : syracuseStep 533375 = 800063) B800063
theorem B1516639 : Blo 531801 1516639 := bstep (se 1 (by rfl) ⟨1137479, by rfl⟩ : syracuseStep 1516639 = 2274959) B2274959
theorem B533659 : Blo 531801 533659 := bstep (se 1 (by rfl) ⟨400244, by rfl⟩ : syracuseStep 533659 = 800489) B800489
theorem B533663 : Blo 531801 533663 := bstep (se 1 (by rfl) ⟨400247, by rfl⟩ : syracuseStep 533663 = 800495) B800495
theorem B959951 : Blo 531801 959951 := bstep (se 1 (by rfl) ⟨719963, by rfl⟩ : syracuseStep 959951 = 1439927) B1439927
theorem B599503 : Blo 531801 599503 := bstep (se 1 (by rfl) ⟨449627, by rfl⟩ : syracuseStep 599503 = 899255) B899255
theorem B533967 : Blo 531801 533967 := bstep (se 1 (by rfl) ⟨400475, by rfl⟩ : syracuseStep 533967 = 800951) B800951
theorem B1517039 : Blo 531801 1517039 := bstep (se 1 (by rfl) ⟨1137779, by rfl⟩ : syracuseStep 1517039 = 2275559) B2275559
theorem B533999 : Blo 531801 533999 := bstep (se 1 (by rfl) ⟨400499, by rfl⟩ : syracuseStep 533999 = 800999) B800999
theorem B4564511 : Blo 531801 4564511 := bstep (se 1 (by rfl) ⟨3423383, by rfl⟩ : syracuseStep 4564511 = 6846767) B6846767
theorem B1517231 : Blo 531801 1517231 := bstep (se 1 (by rfl) ⟨1137923, by rfl⟩ : syracuseStep 1517231 = 2275847) B2275847
theorem B534247 : Blo 531801 534247 := bstep (se 1 (by rfl) ⟨400685, by rfl⟩ : syracuseStep 534247 = 801371) B801371
theorem B534343 : Blo 531801 534343 := bstep (se 1 (by rfl) ⟨400757, by rfl⟩ : syracuseStep 534343 = 801515) B801515
theorem B599899 : Blo 531801 599899 := bstep (se 1 (by rfl) ⟨449924, by rfl⟩ : syracuseStep 599899 = 899849) B899849
theorem B534363 : Blo 531801 534363 := bstep (se 1 (by rfl) ⟨400772, by rfl⟩ : syracuseStep 534363 = 801545) B801545
theorem B1353611 : Blo 531801 1353611 := bstep (se 1 (by rfl) ⟨1015208, by rfl⟩ : syracuseStep 1353611 = 2030417) B2030417
theorem B6596873 : Blo 531801 6596873 := bstep (se 2 (by rfl) ⟨2473827, by rfl⟩ : syracuseStep 6596873 = 4947655) B4947655
theorem B534943 : Blo 531801 534943 := bstep (se 1 (by rfl) ⟨401207, by rfl⟩ : syracuseStep 534943 = 802415) B802415
theorem B535023 : Blo 531801 535023 := bstep (se 1 (by rfl) ⟨401267, by rfl⟩ : syracuseStep 535023 = 802535) B802535
theorem B535151 : Blo 531801 535151 := bstep (se 1 (by rfl) ⟨401363, by rfl⟩ : syracuseStep 535151 = 802727) B802727
theorem B535367 : Blo 531801 535367 := bstep (se 1 (by rfl) ⟨401525, by rfl⟩ : syracuseStep 535367 = 803051) B803051
theorem B600943 : Blo 531801 600943 := bstep (se 1 (by rfl) ⟨450707, by rfl⟩ : syracuseStep 600943 = 901415) B901415
theorem B535407 : Blo 531801 535407 := bstep (se 1 (by rfl) ⟨401555, by rfl⟩ : syracuseStep 535407 = 803111) B803111
theorem B797759 : Blo 531801 797759 := bstep (se 1 (by rfl) ⟨598319, by rfl⟩ : syracuseStep 797759 = 1196639) B1196639
theorem B3091751 : Blo 531801 3091751 := bstep (se 1 (by rfl) ⟨2318813, by rfl⟩ : syracuseStep 3091751 = 4637627) B4637627
theorem B797999 : Blo 531801 797999 := bstep (se 1 (by rfl) ⟨598499, by rfl⟩ : syracuseStep 797999 = 1196999) B1196999
theorem B1355231 : Blo 531801 1355231 := bstep (se 1 (by rfl) ⟨1016423, by rfl⟩ : syracuseStep 1355231 = 2032847) B2032847
theorem B798185 : Blo 531801 798185 := bstep (se 2 (by rfl) ⟨299319, by rfl⟩ : syracuseStep 798185 = 598639) B598639
theorem B798239 : Blo 531801 798239 := bstep (se 1 (by rfl) ⟨598679, by rfl⟩ : syracuseStep 798239 = 1197359) B1197359
theorem B798329 : Blo 531801 798329 := bstep (se 2 (by rfl) ⟨299373, by rfl⟩ : syracuseStep 798329 = 598747) B598747
theorem B798575 : Blo 531801 798575 := bstep (se 1 (by rfl) ⟨598931, by rfl⟩ : syracuseStep 798575 = 1197863) B1197863
theorem B1355849 : Blo 531801 1355849 := bstep (se 2 (by rfl) ⟨508443, by rfl⟩ : syracuseStep 1355849 = 1016887) B1016887
theorem B798827 : Blo 531801 798827 := bstep (se 1 (by rfl) ⟨599120, by rfl⟩ : syracuseStep 798827 = 1198241) B1198241
theorem B799259 : Blo 531801 799259 := bstep (se 1 (by rfl) ⟨599444, by rfl⟩ : syracuseStep 799259 = 1198889) B1198889
theorem B73740901 : Blo 531801 73740901 := bstep (se 4 (by rfl) ⟨6913209, by rfl⟩ : syracuseStep 73740901 = 13826419) B13826419
theorem B2699891 : Blo 531801 2699891 := bstep (se 1 (by rfl) ⟨2024918, by rfl⟩ : syracuseStep 2699891 = 4049837) B4049837
theorem B799439 : Blo 531801 799439 := bstep (se 1 (by rfl) ⟨599579, by rfl⟩ : syracuseStep 799439 = 1199159) B1199159
theorem B799727 : Blo 531801 799727 := bstep (se 1 (by rfl) ⟨599795, by rfl⟩ : syracuseStep 799727 = 1199591) B1199591
theorem B3257327 : Blo 531801 3257327 := bstep (se 1 (by rfl) ⟨2442995, by rfl⟩ : syracuseStep 3257327 = 4885991) B4885991
theorem B3453961 : Blo 531801 3453961 := bstep (se 2 (by rfl) ⟨1295235, by rfl⟩ : syracuseStep 3453961 = 2590471) B2590471
theorem B800111 : Blo 531801 800111 := bstep (se 1 (by rfl) ⟨600083, by rfl⟩ : syracuseStep 800111 = 1200167) B1200167
theorem B800231 : Blo 531801 800231 := bstep (se 1 (by rfl) ⟨600173, by rfl⟩ : syracuseStep 800231 = 1200347) B1200347
theorem B800411 : Blo 531801 800411 := bstep (se 1 (by rfl) ⟨600308, by rfl⟩ : syracuseStep 800411 = 1200617) B1200617
theorem B4044491 : Blo 531801 4044491 := bstep (se 1 (by rfl) ⟨3033368, by rfl⟩ : syracuseStep 4044491 = 6066737) B6066737
theorem B800747 : Blo 531801 800747 := bstep (se 1 (by rfl) ⟨600560, by rfl⟩ : syracuseStep 800747 = 1201121) B1201121
theorem B800831 : Blo 531801 800831 := bstep (se 1 (by rfl) ⟨600623, by rfl⟩ : syracuseStep 800831 = 1201247) B1201247
theorem B2701511 : Blo 531801 2701511 := bstep (se 1 (by rfl) ⟨2026133, by rfl⟩ : syracuseStep 2701511 = 4052267) B4052267
theorem B801161 : Blo 531801 801161 := bstep (se 2 (by rfl) ⟨300435, by rfl⟩ : syracuseStep 801161 = 600871) B600871
theorem B801335 : Blo 531801 801335 := bstep (se 1 (by rfl) ⟨601001, by rfl⟩ : syracuseStep 801335 = 1202003) B1202003
theorem B801659 : Blo 531801 801659 := bstep (se 1 (by rfl) ⟨601244, by rfl⟩ : syracuseStep 801659 = 1202489) B1202489
theorem B4340603 : Blo 531801 4340603 := bstep (se 1 (by rfl) ⟨3255452, by rfl⟩ : syracuseStep 4340603 = 6510905) B6510905
theorem B3029885 : Blo 531801 3029885 := bstep (se 3 (by rfl) ⟨568103, by rfl⟩ : syracuseStep 3029885 = 1136207) B1136207
theorem B2276257 : Blo 531801 2276257 := bstep (se 2 (by rfl) ⟨853596, by rfl⟩ : syracuseStep 2276257 = 1707193) B1707193
theorem B56835125 : Blo 531801 56835125 := bstep (se 5 (by rfl) ⟨2664146, by rfl⟩ : syracuseStep 56835125 = 5328293) B5328293
theorem B21937513 : Blo 531801 21937513 := bstep (se 2 (by rfl) ⟨8226567, by rfl⟩ : syracuseStep 21937513 = 16453135) B16453135
theorem B802271 : Blo 531801 802271 := bstep (se 1 (by rfl) ⟨601703, by rfl⟩ : syracuseStep 802271 = 1203407) B1203407
theorem B802523 : Blo 531801 802523 := bstep (se 1 (by rfl) ⟨601892, by rfl⟩ : syracuseStep 802523 = 1203785) B1203785
theorem B2440955 : Blo 531801 2440955 := bstep (se 1 (by rfl) ⟨1830716, by rfl⟩ : syracuseStep 2440955 = 3661433) B3661433
theorem B802793 : Blo 531801 802793 := bstep (se 2 (by rfl) ⟨301047, by rfl⟩ : syracuseStep 802793 = 602095) B602095
theorem B4046921 : Blo 531801 4046921 := bstep (se 2 (by rfl) ⟨1517595, by rfl⟩ : syracuseStep 4046921 = 3035191) B3035191
theorem B3326035 : Blo 531801 3326035 := bstep (se 1 (by rfl) ⟨2494526, by rfl⟩ : syracuseStep 3326035 = 4989053) B4989053
theorem B802985 : Blo 531801 802985 := bstep (se 2 (by rfl) ⟨301119, by rfl⟩ : syracuseStep 802985 = 602239) B602239
theorem B901327 : Blo 531801 901327 := bstep (se 1 (by rfl) ⟨675995, by rfl⟩ : syracuseStep 901327 = 1351991) B1351991
theorem B5783885 : Blo 531801 5783885 := bstep (se 3 (by rfl) ⟨1084478, by rfl⟩ : syracuseStep 5783885 = 2168957) B2168957
theorem B803303 : Blo 531801 803303 := bstep (se 1 (by rfl) ⟨602477, by rfl⟩ : syracuseStep 803303 = 1204955) B1204955
theorem B1524329 : Blo 531801 1524329 := bstep (se 2 (by rfl) ⟨571623, by rfl⟩ : syracuseStep 1524329 = 1143247) B1143247
theorem B803579 : Blo 531801 803579 := bstep (se 1 (by rfl) ⟨602684, by rfl⟩ : syracuseStep 803579 = 1205369) B1205369
theorem B3425561 : Blo 531801 3425561 := bstep (se 2 (by rfl) ⟨1284585, by rfl⟩ : syracuseStep 3425561 = 2569171) B2569171
theorem B1525159 : Blo 531801 1525159 := bstep (se 1 (by rfl) ⟨1143869, by rfl⟩ : syracuseStep 1525159 = 2287739) B2287739
theorem B2049455 : Blo 531801 2049455 := bstep (se 1 (by rfl) ⟨1537091, by rfl⟩ : syracuseStep 2049455 = 3074183) B3074183
theorem B1918403 : Blo 531801 1918403 := bstep (se 1 (by rfl) ⟨1438802, by rfl⟩ : syracuseStep 1918403 = 2877605) B2877605
theorem B7685597 : Blo 531801 7685597 := bstep (se 3 (by rfl) ⟨1441049, by rfl⟩ : syracuseStep 7685597 = 2882099) B2882099
theorem B6833645 : Blo 531801 6833645 := bstep (se 3 (by rfl) ⟨1281308, by rfl⟩ : syracuseStep 6833645 = 2562617) B2562617
theorem B19449497 : Blo 531801 19449497 := bstep (se 2 (by rfl) ⟨7293561, by rfl⟩ : syracuseStep 19449497 = 14587123) B14587123
theorem B3033233 : Blo 531801 3033233 := bstep (se 2 (by rfl) ⟨1137462, by rfl⟩ : syracuseStep 3033233 = 2274925) B2274925
theorem B641207 : Blo 531801 641207 := bstep (se 1 (by rfl) ⟨480905, by rfl⟩ : syracuseStep 641207 = 961811) B961811
theorem B9128537 : Blo 531801 9128537 := bstep (se 2 (by rfl) ⟨3423201, by rfl⟩ : syracuseStep 9128537 = 6846403) B6846403
theorem B1198817 : Blo 531801 1198817 := bstep (se 2 (by rfl) ⟨449556, by rfl⟩ : syracuseStep 1198817 = 899113) B899113
theorem B2706371 : Blo 531801 2706371 := bstep (se 1 (by rfl) ⟨2029778, by rfl⟩ : syracuseStep 2706371 = 4059557) B4059557
theorem B674983 : Blo 531801 674983 := bstep (se 1 (by rfl) ⟨506237, by rfl⟩ : syracuseStep 674983 = 1012475) B1012475
theorem B3427919 : Blo 531801 3427919 := bstep (se 1 (by rfl) ⟨2570939, by rfl⟩ : syracuseStep 3427919 = 5141879) B5141879
theorem B3886703 : Blo 531801 3886703 := bstep (se 1 (by rfl) ⟨2915027, by rfl⟩ : syracuseStep 3886703 = 5830055) B5830055
theorem B6147863 : Blo 531801 6147863 := bstep (se 1 (by rfl) ⟨4610897, by rfl⟩ : syracuseStep 6147863 = 9221795) B9221795
theorem B1200959 : Blo 531801 1200959 := bstep (se 1 (by rfl) ⟨900719, by rfl⟩ : syracuseStep 1200959 = 1801439) B1801439
theorem B676831 : Blo 531801 676831 := bstep (se 1 (by rfl) ⟨507623, by rfl⟩ : syracuseStep 676831 = 1015247) B1015247
theorem B4576297 : Blo 531801 4576297 := bstep (se 2 (by rfl) ⟨1716111, by rfl⟩ : syracuseStep 4576297 = 3432223) B3432223
theorem B2020423 : Blo 531801 2020423 := bstep (se 1 (by rfl) ⟨1515317, by rfl⟩ : syracuseStep 2020423 = 3030635) B3030635
theorem B6182027 : Blo 531801 6182027 := bstep (se 1 (by rfl) ⟨4636520, by rfl⟩ : syracuseStep 6182027 = 9273041) B9273041
theorem B16602457 : Blo 531801 16602457 := bstep (se 2 (by rfl) ⟨6225921, by rfl⟩ : syracuseStep 16602457 = 12451843) B12451843
theorem B13686245 : Blo 531801 13686245 := bstep (se 4 (by rfl) ⟨1283085, by rfl⟩ : syracuseStep 13686245 = 2566171) B2566171
theorem B6084233 : Blo 531801 6084233 := bstep (se 2 (by rfl) ⟨2281587, by rfl⟩ : syracuseStep 6084233 = 4563175) B4563175
theorem B2709449 : Blo 531801 2709449 := bstep (se 2 (by rfl) ⟨1016043, by rfl⟩ : syracuseStep 2709449 = 2032087) B2032087
theorem B1202363 : Blo 531801 1202363 := bstep (se 1 (by rfl) ⟨901772, by rfl⟩ : syracuseStep 1202363 = 1803545) B1803545
theorem B1628383 : Blo 531801 1628383 := bstep (se 1 (by rfl) ⟨1221287, by rfl⟩ : syracuseStep 1628383 = 2442575) B2442575
theorem B9755113 : Blo 531801 9755113 := bstep (se 2 (by rfl) ⟨3658167, by rfl⟩ : syracuseStep 9755113 = 7316335) B7316335
theorem B2808377 : Blo 531801 2808377 := bstep (se 2 (by rfl) ⟨1053141, by rfl⟩ : syracuseStep 2808377 = 2106283) B2106283
theorem B1203047 : Blo 531801 1203047 := bstep (se 1 (by rfl) ⟨902285, by rfl⟩ : syracuseStep 1203047 = 1804571) B1804571
theorem B9132911 : Blo 531801 9132911 := bstep (se 1 (by rfl) ⟨6849683, by rfl⟩ : syracuseStep 9132911 = 13699367) B13699367
theorem B3234755 : Blo 531801 3234755 := bstep (se 1 (by rfl) ⟨2426066, by rfl⟩ : syracuseStep 3234755 = 4852133) B4852133
theorem B1203155 : Blo 531801 1203155 := bstep (se 1 (by rfl) ⟨902366, by rfl⟩ : syracuseStep 1203155 = 1804733) B1804733
theorem B1203263 : Blo 531801 1203263 := bstep (se 1 (by rfl) ⟨902447, by rfl⟩ : syracuseStep 1203263 = 1804895) B1804895
theorem B1203425 : Blo 531801 1203425 := bstep (se 2 (by rfl) ⟨451284, by rfl⟩ : syracuseStep 1203425 = 902569) B902569
theorem B7691597 : Blo 531801 7691597 := bstep (se 3 (by rfl) ⟨1442174, by rfl⟩ : syracuseStep 7691597 = 2884349) B2884349
theorem B810361 : Blo 531801 810361 := bstep (se 2 (by rfl) ⟨303885, by rfl⟩ : syracuseStep 810361 = 607771) B607771
theorem B3038633 : Blo 531801 3038633 := bstep (se 2 (by rfl) ⟨1139487, by rfl⟩ : syracuseStep 3038633 = 2278975) B2278975
theorem B2022839 : Blo 531801 2022839 := bstep (se 1 (by rfl) ⟨1517129, by rfl⟩ : syracuseStep 2022839 = 3034259) B3034259
theorem B5791621 : Blo 531801 5791621 := bstep (se 4 (by rfl) ⟨542964, by rfl⟩ : syracuseStep 5791621 = 1085929) B1085929
theorem B1204415 : Blo 531801 1204415 := bstep (se 1 (by rfl) ⟨903311, by rfl⟩ : syracuseStep 1204415 = 1806623) B1806623
theorem B1139359 : Blo 531801 1139359 := bstep (se 1 (by rfl) ⟨854519, by rfl⟩ : syracuseStep 1139359 = 1709039) B1709039
theorem B10674953 : Blo 531801 10674953 := bstep (se 2 (by rfl) ⟨4003107, by rfl⟩ : syracuseStep 10674953 = 8006215) B8006215
theorem B1368857 : Blo 531801 1368857 := bstep (se 2 (by rfl) ⟨513321, by rfl⟩ : syracuseStep 1368857 = 1026643) B1026643
theorem B1926013 : Blo 531801 1926013 := bstep (se 3 (by rfl) ⟨361127, by rfl⟩ : syracuseStep 1926013 = 722255) B722255
theorem B1729439 : Blo 531801 1729439 := bstep (se 1 (by rfl) ⟨1297079, by rfl⟩ : syracuseStep 1729439 = 2594159) B2594159
theorem B1205243 : Blo 531801 1205243 := bstep (se 1 (by rfl) ⟨903932, by rfl⟩ : syracuseStep 1205243 = 1807865) B1807865
theorem B1205351 : Blo 531801 1205351 := bstep (se 1 (by rfl) ⟨904013, by rfl⟩ : syracuseStep 1205351 = 1808027) B1808027
theorem B1205423 : Blo 531801 1205423 := bstep (se 1 (by rfl) ⟨904067, by rfl⟩ : syracuseStep 1205423 = 1808135) B1808135
theorem B1796201 : Blo 531801 1796201 := bstep (se 2 (by rfl) ⟨673575, by rfl⟩ : syracuseStep 1796201 = 1347151) B1347151
theorem B2746667 : Blo 531801 2746667 := bstep (se 1 (by rfl) ⟨2060000, by rfl⟩ : syracuseStep 2746667 = 4120001) B4120001
theorem B977231 : Blo 531801 977231 := bstep (se 1 (by rfl) ⟨732923, by rfl⟩ : syracuseStep 977231 = 1465847) B1465847
theorem B15395183 : Blo 531801 15395183 := bstep (se 1 (by rfl) ⟨11546387, by rfl⟩ : syracuseStep 15395183 = 23092775) B23092775
theorem B3338057 : Blo 531801 3338057 := bstep (se 2 (by rfl) ⟨1251771, by rfl⟩ : syracuseStep 3338057 = 2503543) B2503543
theorem B1437851 : Blo 531801 1437851 := bstep (se 1 (by rfl) ⟨1078388, by rfl⟩ : syracuseStep 1437851 = 2156777) B2156777
theorem B6943103 : Blo 531801 6943103 := bstep (se 1 (by rfl) ⟨5207327, by rfl⟩ : syracuseStep 6943103 = 10414655) B10414655
theorem B1798793 : Blo 531801 1798793 := bstep (se 2 (by rfl) ⟨674547, by rfl⟩ : syracuseStep 1798793 = 1349095) B1349095
theorem B1373231 : Blo 531801 1373231 := bstep (se 1 (by rfl) ⟨1029923, by rfl⟩ : syracuseStep 1373231 = 2059847) B2059847
theorem B1800359 : Blo 531801 1800359 := bstep (se 1 (by rfl) ⟨1350269, by rfl⟩ : syracuseStep 1800359 = 2700539) B2700539
theorem B6486281 : Blo 531801 6486281 := bstep (se 2 (by rfl) ⟨2432355, by rfl⟩ : syracuseStep 6486281 = 4864711) B4864711
theorem B3045671 : Blo 531801 3045671 := bstep (se 1 (by rfl) ⟨2284253, by rfl⟩ : syracuseStep 3045671 = 4568507) B4568507
theorem B2161691 : Blo 531801 2161691 := bstep (se 1 (by rfl) ⟨1621268, by rfl⟩ : syracuseStep 2161691 = 3242537) B3242537
theorem B4062473 : Blo 531801 4062473 := bstep (se 2 (by rfl) ⟨1523427, by rfl⟩ : syracuseStep 4062473 = 3046855) B3046855
theorem B1801655 : Blo 531801 1801655 := bstep (se 1 (by rfl) ⟨1351241, by rfl⟩ : syracuseStep 1801655 = 2702483) B2702483
theorem B1802195 : Blo 531801 1802195 := bstep (se 1 (by rfl) ⟨1351646, by rfl⟩ : syracuseStep 1802195 = 2703293) B2703293
theorem B1016219 : Blo 531801 1016219 := bstep (se 1 (by rfl) ⟨762164, by rfl⟩ : syracuseStep 1016219 = 1524329) B1524329
theorem B10945115 : Blo 531801 10945115 := bstep (se 1 (by rfl) ⟨8208836, by rfl⟩ : syracuseStep 10945115 = 16417673) B16417673
theorem B4063931 : Blo 531801 4063931 := bstep (se 1 (by rfl) ⟨3047948, by rfl⟩ : syracuseStep 4063931 = 6095897) B6095897
theorem B1016545 : Blo 531801 1016545 := bstep (se 2 (by rfl) ⟨381204, by rfl⟩ : syracuseStep 1016545 = 762409) B762409
theorem B1278935 : Blo 531801 1278935 := bstep (se 1 (by rfl) ⟨959201, by rfl⟩ : syracuseStep 1278935 = 1918403) B1918403
theorem B4555763 : Blo 531801 4555763 := bstep (se 1 (by rfl) ⟨3416822, by rfl⟩ : syracuseStep 4555763 = 6833645) B6833645
theorem B2885473 : Blo 531801 2885473 := bstep (se 2 (by rfl) ⟨1082052, by rfl⟩ : syracuseStep 2885473 = 2164105) B2164105
theorem B2033545 : Blo 531801 2033545 := bstep (se 2 (by rfl) ⟨762579, by rfl⟩ : syracuseStep 2033545 = 1525159) B1525159
theorem B1804247 : Blo 531801 1804247 := bstep (se 1 (by rfl) ⟨1353185, by rfl⟩ : syracuseStep 1804247 = 2706371) B2706371
theorem B2591135 : Blo 531801 2591135 := bstep (se 1 (by rfl) ⟨1943351, by rfl⟩ : syracuseStep 2591135 = 3886703) B3886703
theorem B4098575 : Blo 531801 4098575 := bstep (se 1 (by rfl) ⟨3073931, by rfl⟩ : syracuseStep 4098575 = 6147863) B6147863
theorem B2558483 : Blo 531801 2558483 := bstep (se 1 (by rfl) ⟨1918862, by rfl⟩ : syracuseStep 2558483 = 3837725) B3837725
theorem B2886425 : Blo 531801 2886425 := bstep (se 2 (by rfl) ⟨1082409, by rfl⟩ : syracuseStep 2886425 = 2164819) B2164819
theorem B2559869 : Blo 531801 2559869 := bstep (se 3 (by rfl) ⟨479975, by rfl⟩ : syracuseStep 2559869 = 959951) B959951
theorem B1806299 : Blo 531801 1806299 := bstep (se 1 (by rfl) ⟨1354724, by rfl⟩ : syracuseStep 1806299 = 2709449) B2709449
theorem B1872251 : Blo 531801 1872251 := bstep (se 1 (by rfl) ⟨1404188, by rfl⟩ : syracuseStep 1872251 = 2808377) B2808377
theorem B1348559 : Blo 531801 1348559 := bstep (se 1 (by rfl) ⟨1011419, by rfl⟩ : syracuseStep 1348559 = 2022839) B2022839
theorem B1709885 : Blo 531801 1709885 := bstep (se 3 (by rfl) ⟨320603, by rfl⟩ : syracuseStep 1709885 = 641207) B641207
theorem B7116635 : Blo 531801 7116635 := bstep (se 1 (by rfl) ⟨5337476, by rfl⟩ : syracuseStep 7116635 = 10674953) B10674953
theorem B1152959 : Blo 531801 1152959 := bstep (se 1 (by rfl) ⟨864719, by rfl⟩ : syracuseStep 1152959 = 1729439) B1729439
theorem B6101729 : Blo 531801 6101729 := bstep (se 2 (by rfl) ⟨2288148, by rfl⟩ : syracuseStep 6101729 = 4576297) B4576297
theorem B2693897 : Blo 531801 2693897 := bstep (se 2 (by rfl) ⟨1010211, by rfl⟩ : syracuseStep 2693897 = 2020423) B2020423
theorem B4397915 : Blo 531801 4397915 := bstep (se 1 (by rfl) ⟨3298436, by rfl⟩ : syracuseStep 4397915 = 6596873) B6596873
theorem B10263455 : Blo 531801 10263455 := bstep (se 1 (by rfl) ⟨7697591, by rfl⟩ : syracuseStep 10263455 = 15395183) B15395183
theorem B531839 : Blo 531801 531839 := bstep (se 1 (by rfl) ⟨398879, by rfl⟩ : syracuseStep 531839 = 797759) B797759
theorem B531999 : Blo 531801 531999 := bstep (se 1 (by rfl) ⟨398999, by rfl⟩ : syracuseStep 531999 = 797999) B797999
theorem B532123 : Blo 531801 532123 := bstep (se 1 (by rfl) ⟨399092, by rfl⟩ : syracuseStep 532123 = 798185) B798185
theorem B532159 : Blo 531801 532159 := bstep (se 1 (by rfl) ⟨399119, by rfl⟩ : syracuseStep 532159 = 798239) B798239
theorem B532219 : Blo 531801 532219 := bstep (se 1 (by rfl) ⟨399164, by rfl⟩ : syracuseStep 532219 = 798329) B798329
theorem B532383 : Blo 531801 532383 := bstep (se 1 (by rfl) ⟨399287, by rfl⟩ : syracuseStep 532383 = 798575) B798575
theorem B532551 : Blo 531801 532551 := bstep (se 1 (by rfl) ⟨399413, by rfl⟩ : syracuseStep 532551 = 798827) B798827
theorem B958567 : Blo 531801 958567 := bstep (se 1 (by rfl) ⟨718925, by rfl⟩ : syracuseStep 958567 = 1437851) B1437851
theorem B4628735 : Blo 531801 4628735 := bstep (se 1 (by rfl) ⟨3471551, by rfl⟩ : syracuseStep 4628735 = 6943103) B6943103
theorem B2171177 : Blo 531801 2171177 := bstep (se 2 (by rfl) ⟨814191, by rfl⟩ : syracuseStep 2171177 = 1628383) B1628383
theorem B532839 : Blo 531801 532839 := bstep (se 1 (by rfl) ⟨399629, by rfl⟩ : syracuseStep 532839 = 799259) B799259
theorem B532959 : Blo 531801 532959 := bstep (se 1 (by rfl) ⟨399719, by rfl⟩ : syracuseStep 532959 = 799439) B799439
theorem B533151 : Blo 531801 533151 := bstep (se 1 (by rfl) ⟨399863, by rfl⟩ : syracuseStep 533151 = 799727) B799727
theorem B2171551 : Blo 531801 2171551 := bstep (se 1 (by rfl) ⟨1628663, by rfl⟩ : syracuseStep 2171551 = 3257327) B3257327
theorem B533407 : Blo 531801 533407 := bstep (se 1 (by rfl) ⟨400055, by rfl⟩ : syracuseStep 533407 = 800111) B800111
theorem B533487 : Blo 531801 533487 := bstep (se 1 (by rfl) ⟨400115, by rfl⟩ : syracuseStep 533487 = 800231) B800231
theorem B533607 : Blo 531801 533607 := bstep (se 1 (by rfl) ⟨400205, by rfl⟩ : syracuseStep 533607 = 800411) B800411
theorem B2696327 : Blo 531801 2696327 := bstep (se 1 (by rfl) ⟨2022245, by rfl⟩ : syracuseStep 2696327 = 4044491) B4044491
theorem B4564133 : Blo 531801 4564133 := bstep (se 4 (by rfl) ⟨427887, by rfl⟩ : syracuseStep 4564133 = 855775) B855775
theorem B533831 : Blo 531801 533831 := bstep (se 1 (by rfl) ⟨400373, by rfl⟩ : syracuseStep 533831 = 800747) B800747
theorem B533887 : Blo 531801 533887 := bstep (se 1 (by rfl) ⟨400415, by rfl⟩ : syracuseStep 533887 = 800831) B800831
theorem B534107 : Blo 531801 534107 := bstep (se 1 (by rfl) ⟨400580, by rfl⟩ : syracuseStep 534107 = 801161) B801161
theorem B534223 : Blo 531801 534223 := bstep (se 1 (by rfl) ⟨400667, by rfl⟩ : syracuseStep 534223 = 801335) B801335
theorem B27666137 : Blo 531801 27666137 := bstep (se 2 (by rfl) ⟨10374801, by rfl⟩ : syracuseStep 27666137 = 20749603) B20749603
theorem B534439 : Blo 531801 534439 := bstep (se 1 (by rfl) ⟨400829, by rfl⟩ : syracuseStep 534439 = 801659) B801659
theorem B2893735 : Blo 531801 2893735 := bstep (se 1 (by rfl) ⟨2170301, by rfl⟩ : syracuseStep 2893735 = 4340603) B4340603
theorem B37890083 : Blo 531801 37890083 := bstep (se 1 (by rfl) ⟨28417562, by rfl⟩ : syracuseStep 37890083 = 56835125) B56835125
theorem B534847 : Blo 531801 534847 := bstep (se 1 (by rfl) ⟨401135, by rfl⟩ : syracuseStep 534847 = 802271) B802271
theorem B535015 : Blo 531801 535015 := bstep (se 1 (by rfl) ⟨401261, by rfl⟩ : syracuseStep 535015 = 802523) B802523
theorem B535195 : Blo 531801 535195 := bstep (se 1 (by rfl) ⟨401396, by rfl⟩ : syracuseStep 535195 = 802793) B802793
theorem B2697947 : Blo 531801 2697947 := bstep (se 1 (by rfl) ⟨2023460, by rfl⟩ : syracuseStep 2697947 = 4046921) B4046921
theorem B4434713 : Blo 531801 4434713 := bstep (se 2 (by rfl) ⟨1663017, by rfl⟩ : syracuseStep 4434713 = 3326035) B3326035
theorem B535323 : Blo 531801 535323 := bstep (se 1 (by rfl) ⟨401492, by rfl⟩ : syracuseStep 535323 = 802985) B802985
theorem B1714985 : Blo 531801 1714985 := bstep (se 2 (by rfl) ⟨643119, by rfl⟩ : syracuseStep 1714985 = 1286239) B1286239
theorem B1157971 : Blo 531801 1157971 := bstep (se 1 (by rfl) ⟨868478, by rfl⟩ : syracuseStep 1157971 = 1736957) B1736957
theorem B535535 : Blo 531801 535535 := bstep (se 1 (by rfl) ⟨401651, by rfl⟩ : syracuseStep 535535 = 803303) B803303
theorem B535719 : Blo 531801 535719 := bstep (se 1 (by rfl) ⟨401789, by rfl⟩ : syracuseStep 535719 = 803579) B803579
theorem B1519145 : Blo 531801 1519145 := bstep (se 2 (by rfl) ⟨569679, by rfl⟩ : syracuseStep 1519145 = 1139359) B1139359
theorem B5123731 : Blo 531801 5123731 := bstep (se 1 (by rfl) ⟨3842798, by rfl⟩ : syracuseStep 5123731 = 7685597) B7685597
theorem B2568017 : Blo 531801 2568017 := bstep (se 2 (by rfl) ⟨963006, by rfl⟩ : syracuseStep 2568017 = 1926013) B1926013
theorem B2273183 : Blo 531801 2273183 := bstep (se 1 (by rfl) ⟨1704887, by rfl⟩ : syracuseStep 2273183 = 3409775) B3409775
theorem B569791 : Blo 531801 569791 := bstep (se 1 (by rfl) ⟨427343, by rfl⟩ : syracuseStep 569791 = 854687) B854687
theorem B1356223 : Blo 531801 1356223 := bstep (se 1 (by rfl) ⟨1017167, by rfl⟩ : syracuseStep 1356223 = 2034335) B2034335
theorem B799211 : Blo 531801 799211 := bstep (se 1 (by rfl) ⟨599408, by rfl⟩ : syracuseStep 799211 = 1198817) B1198817
theorem B799337 : Blo 531801 799337 := bstep (se 2 (by rfl) ⟨299751, by rfl⟩ : syracuseStep 799337 = 599503) B599503
theorem B3650285 : Blo 531801 3650285 := bstep (se 3 (by rfl) ⟨684428, by rfl⟩ : syracuseStep 3650285 = 1368857) B1368857
theorem B570235 : Blo 531801 570235 := bstep (se 1 (by rfl) ⟨427676, by rfl⟩ : syracuseStep 570235 = 855353) B855353
theorem B3519551 : Blo 531801 3519551 := bstep (se 1 (by rfl) ⟨2639663, by rfl⟩ : syracuseStep 3519551 = 5279327) B5279327
theorem B799865 : Blo 531801 799865 := bstep (se 2 (by rfl) ⟨299949, by rfl⟩ : syracuseStep 799865 = 599899) B599899
theorem B2733323 : Blo 531801 2733323 := bstep (se 1 (by rfl) ⟨2049992, by rfl⟩ : syracuseStep 2733323 = 4099985) B4099985
theorem B800639 : Blo 531801 800639 := bstep (se 1 (by rfl) ⟨600479, by rfl⟩ : syracuseStep 800639 = 1200959) B1200959
theorem B4634857 : Blo 531801 4634857 := bstep (se 2 (by rfl) ⟨1738071, by rfl⟩ : syracuseStep 4634857 = 3476143) B3476143
theorem B9124163 : Blo 531801 9124163 := bstep (se 1 (by rfl) ⟨6843122, by rfl⟩ : syracuseStep 9124163 = 13686245) B13686245
theorem B801257 : Blo 531801 801257 := bstep (se 2 (by rfl) ⟨300471, by rfl⟩ : syracuseStep 801257 = 600943) B600943
theorem B572123 : Blo 531801 572123 := bstep (se 1 (by rfl) ⟨429092, by rfl⟩ : syracuseStep 572123 = 858185) B858185
theorem B801575 : Blo 531801 801575 := bstep (se 1 (by rfl) ⟨601181, by rfl⟩ : syracuseStep 801575 = 1202363) B1202363
theorem B899977 : Blo 531801 899977 := bstep (se 2 (by rfl) ⟨337491, by rfl⟩ : syracuseStep 899977 = 674983) B674983
theorem B900031 : Blo 531801 900031 := bstep (se 1 (by rfl) ⟨675023, by rfl⟩ : syracuseStep 900031 = 1350047) B1350047
theorem B4045949 : Blo 531801 4045949 := bstep (se 3 (by rfl) ⟨758615, by rfl⟩ : syracuseStep 4045949 = 1517231) B1517231
theorem B802031 : Blo 531801 802031 := bstep (se 1 (by rfl) ⟨601523, by rfl⟩ : syracuseStep 802031 = 1203047) B1203047
theorem B802103 : Blo 531801 802103 := bstep (se 1 (by rfl) ⟨601577, by rfl⟩ : syracuseStep 802103 = 1203155) B1203155
theorem B900443 : Blo 531801 900443 := bstep (se 1 (by rfl) ⟨675332, by rfl⟩ : syracuseStep 900443 = 1350665) B1350665
theorem B802175 : Blo 531801 802175 := bstep (se 1 (by rfl) ⟨601631, by rfl⟩ : syracuseStep 802175 = 1203263) B1203263
theorem B802283 : Blo 531801 802283 := bstep (se 1 (by rfl) ⟨601712, by rfl⟩ : syracuseStep 802283 = 1203425) B1203425
theorem B5127731 : Blo 531801 5127731 := bstep (se 1 (by rfl) ⟨3845798, by rfl⟩ : syracuseStep 5127731 = 7691597) B7691597
theorem B802943 : Blo 531801 802943 := bstep (se 1 (by rfl) ⟨602207, by rfl⟩ : syracuseStep 802943 = 1204415) B1204415
theorem B5357963 : Blo 531801 5357963 := bstep (se 1 (by rfl) ⟨4018472, by rfl⟩ : syracuseStep 5357963 = 8036945) B8036945
theorem B3654119 : Blo 531801 3654119 := bstep (se 1 (by rfl) ⟨2740589, by rfl⟩ : syracuseStep 3654119 = 5481179) B5481179
theorem B803495 : Blo 531801 803495 := bstep (se 1 (by rfl) ⟨602621, by rfl⟩ : syracuseStep 803495 = 1205243) B1205243
theorem B803567 : Blo 531801 803567 := bstep (se 1 (by rfl) ⟨602675, by rfl⟩ : syracuseStep 803567 = 1205351) B1205351
theorem B7324445 : Blo 531801 7324445 := bstep (se 3 (by rfl) ⟨1373333, by rfl⟩ : syracuseStep 7324445 = 2746667) B2746667
theorem B803615 : Blo 531801 803615 := bstep (se 1 (by rfl) ⟨602711, by rfl⟩ : syracuseStep 803615 = 1205423) B1205423
theorem B98321201 : Blo 531801 98321201 := bstep (se 2 (by rfl) ⟨36870450, by rfl⟩ : syracuseStep 98321201 = 73740901) B73740901
theorem B902407 : Blo 531801 902407 := bstep (se 1 (by rfl) ⟨676805, by rfl⟩ : syracuseStep 902407 = 1353611) B1353611
theorem B902441 : Blo 531801 902441 := bstep (se 2 (by rfl) ⟨338415, by rfl⟩ : syracuseStep 902441 = 676831) B676831
theorem B4605281 : Blo 531801 4605281 := bstep (se 2 (by rfl) ⟨1726980, by rfl⟩ : syracuseStep 4605281 = 3453961) B3453961
theorem B1197467 : Blo 531801 1197467 := bstep (se 1 (by rfl) ⟨898100, by rfl⟩ : syracuseStep 1197467 = 1796201) B1796201
theorem B22136609 : Blo 531801 22136609 := bstep (se 2 (by rfl) ⟨8301228, by rfl⟩ : syracuseStep 22136609 = 16602457) B16602457
theorem B903487 : Blo 531801 903487 := bstep (se 1 (by rfl) ⟨677615, by rfl⟩ : syracuseStep 903487 = 1355231) B1355231
theorem B903899 : Blo 531801 903899 := bstep (se 1 (by rfl) ⟨677924, by rfl⟩ : syracuseStep 903899 = 1355849) B1355849
theorem B1199195 : Blo 531801 1199195 := bstep (se 1 (by rfl) ⟨899396, by rfl⟩ : syracuseStep 1199195 = 1798793) B1798793
theorem B3035009 : Blo 531801 3035009 := bstep (se 2 (by rfl) ⟨1138128, by rfl⟩ : syracuseStep 3035009 = 2276257) B2276257
theorem B1200239 : Blo 531801 1200239 := bstep (se 1 (by rfl) ⟨900179, by rfl⟩ : syracuseStep 1200239 = 1800359) B1800359
theorem B29250017 : Blo 531801 29250017 := bstep (se 2 (by rfl) ⟨10968756, by rfl⟩ : syracuseStep 29250017 = 21937513) B21937513
theorem B2019923 : Blo 531801 2019923 := bstep (se 1 (by rfl) ⟨1514942, by rfl⟩ : syracuseStep 2019923 = 3029885) B3029885
theorem B2708315 : Blo 531801 2708315 := bstep (se 1 (by rfl) ⟨2031236, by rfl⟩ : syracuseStep 2708315 = 4062473) B4062473
theorem B8901485 : Blo 531801 8901485 := bstep (se 3 (by rfl) ⟨1669028, by rfl⟩ : syracuseStep 8901485 = 3338057) B3338057
theorem B1201103 : Blo 531801 1201103 := bstep (se 1 (by rfl) ⟨900827, by rfl⟩ : syracuseStep 1201103 = 1801655) B1801655
theorem B1627303 : Blo 531801 1627303 := bstep (se 1 (by rfl) ⟨1220477, by rfl⟩ : syracuseStep 1627303 = 2440955) B2440955
theorem B7722161 : Blo 531801 7722161 := bstep (se 2 (by rfl) ⟨2895810, by rfl⟩ : syracuseStep 7722161 = 5791621) B5791621
theorem B1201463 : Blo 531801 1201463 := bstep (se 1 (by rfl) ⟨901097, by rfl⟩ : syracuseStep 1201463 = 1802195) B1802195
theorem B3855923 : Blo 531801 3855923 := bstep (se 1 (by rfl) ⟨2891942, by rfl⟩ : syracuseStep 3855923 = 5783885) B5783885
theorem B1201769 : Blo 531801 1201769 := bstep (se 2 (by rfl) ⟨450663, by rfl⟩ : syracuseStep 1201769 = 901327) B901327
theorem B2283707 : Blo 531801 2283707 := bstep (se 1 (by rfl) ⟨1712780, by rfl⟩ : syracuseStep 2283707 = 3425561) B3425561
theorem B1366303 : Blo 531801 1366303 := bstep (se 1 (by rfl) ⟨1024727, by rfl⟩ : syracuseStep 1366303 = 2049455) B2049455
theorem B12966331 : Blo 531801 12966331 := bstep (se 1 (by rfl) ⟨9724748, by rfl⟩ : syracuseStep 12966331 = 19449497) B19449497
theorem B1137343 : Blo 531801 1137343 := bstep (se 1 (by rfl) ⟨853007, by rfl⟩ : syracuseStep 1137343 = 1706015) B1706015
theorem B1137377 : Blo 531801 1137377 := bstep (se 2 (by rfl) ⟨426516, by rfl⟩ : syracuseStep 1137377 = 853033) B853033
theorem B2710259 : Blo 531801 2710259 := bstep (se 1 (by rfl) ⟨2032694, by rfl⟩ : syracuseStep 2710259 = 4065389) B4065389
theorem B2022155 : Blo 531801 2022155 := bstep (se 1 (by rfl) ⟨1516616, by rfl⟩ : syracuseStep 2022155 = 3033233) B3033233
theorem B2022185 : Blo 531801 2022185 := bstep (se 2 (by rfl) ⟨758319, by rfl⟩ : syracuseStep 2022185 = 1516639) B1516639
theorem B6085691 : Blo 531801 6085691 := bstep (se 1 (by rfl) ⟨4564268, by rfl⟩ : syracuseStep 6085691 = 9128537) B9128537
theorem B4545679 : Blo 531801 4545679 := bstep (se 1 (by rfl) ⟨3409259, by rfl⟩ : syracuseStep 4545679 = 6818519) B6818519
theorem B2285279 : Blo 531801 2285279 := bstep (se 1 (by rfl) ⟨1713959, by rfl⟩ : syracuseStep 2285279 = 3427919) B3427919
theorem B3661949 : Blo 531801 3661949 := bstep (se 3 (by rfl) ⟨686615, by rfl⟩ : syracuseStep 3661949 = 1373231) B1373231
theorem B4121351 : Blo 531801 4121351 := bstep (se 1 (by rfl) ⟨3091013, by rfl⟩ : syracuseStep 4121351 = 6182027) B6182027
theorem B1795067 : Blo 531801 1795067 := bstep (se 1 (by rfl) ⟨1346300, by rfl⟩ : syracuseStep 1795067 = 2692601) B2692601
theorem B4547663 : Blo 531801 4547663 := bstep (se 1 (by rfl) ⟨3410747, by rfl⟩ : syracuseStep 4547663 = 6821495) B6821495
theorem B4056155 : Blo 531801 4056155 := bstep (se 1 (by rfl) ⟨3042116, by rfl⟩ : syracuseStep 4056155 = 6084233) B6084233
theorem B1795175 : Blo 531801 1795175 := bstep (se 1 (by rfl) ⟨1346381, by rfl⟩ : syracuseStep 1795175 = 2692763) B2692763
theorem B3040523 : Blo 531801 3040523 := bstep (se 1 (by rfl) ⟨2280392, by rfl⟩ : syracuseStep 3040523 = 4560785) B4560785
theorem B812891 : Blo 531801 812891 := bstep (se 1 (by rfl) ⟨609668, by rfl⟩ : syracuseStep 812891 = 1219337) B1219337
theorem B12347255 : Blo 531801 12347255 := bstep (se 1 (by rfl) ⟨9260441, by rfl⟩ : syracuseStep 12347255 = 18520883) B18520883
theorem B6088607 : Blo 531801 6088607 := bstep (se 1 (by rfl) ⟨4566455, by rfl⟩ : syracuseStep 6088607 = 9132911) B9132911
theorem B2156503 : Blo 531801 2156503 := bstep (se 1 (by rfl) ⟨1617377, by rfl⟩ : syracuseStep 2156503 = 3234755) B3234755
theorem B2025755 : Blo 531801 2025755 := bstep (se 1 (by rfl) ⟨1519316, by rfl⟩ : syracuseStep 2025755 = 3038633) B3038633
theorem B1009999 : Blo 531801 1009999 := bstep (se 1 (by rfl) ⟨757499, by rfl⟩ : syracuseStep 1009999 = 1514999) B1514999
theorem B1141409 : Blo 531801 1141409 := bstep (se 2 (by rfl) ⟨428028, by rfl⟩ : syracuseStep 1141409 = 856057) B856057
theorem B3238667 : Blo 531801 3238667 := bstep (se 1 (by rfl) ⟨2429000, by rfl⟩ : syracuseStep 3238667 = 4858001) B4858001
theorem B7695233 : Blo 531801 7695233 := bstep (se 2 (by rfl) ⟨2885712, by rfl⟩ : syracuseStep 7695233 = 5771425) B5771425
theorem B1141769 : Blo 531801 1141769 := bstep (se 2 (by rfl) ⟨428163, by rfl⟩ : syracuseStep 1141769 = 856327) B856327
theorem B1011359 : Blo 531801 1011359 := bstep (se 1 (by rfl) ⟨758519, by rfl⟩ : syracuseStep 1011359 = 1517039) B1517039
theorem B3043007 : Blo 531801 3043007 := bstep (se 1 (by rfl) ⟨2282255, by rfl⟩ : syracuseStep 3043007 = 4564511) B4564511
theorem B651487 : Blo 531801 651487 := bstep (se 1 (by rfl) ⟨488615, by rfl⟩ : syracuseStep 651487 = 977231) B977231
theorem B1799009 : Blo 531801 1799009 := bstep (se 2 (by rfl) ⟨674628, by rfl⟩ : syracuseStep 1799009 = 1349257) B1349257
theorem B7304033 : Blo 531801 7304033 := bstep (se 2 (by rfl) ⟨2739012, by rfl⟩ : syracuseStep 7304033 = 5478025) B5478025
theorem B2061167 : Blo 531801 2061167 := bstep (se 1 (by rfl) ⟨1545875, by rfl⟩ : syracuseStep 2061167 = 3091751) B3091751
theorem B1930729 : Blo 531801 1930729 := bstep (se 2 (by rfl) ⟨724023, by rfl⟩ : syracuseStep 1930729 = 1448047) B1448047
theorem B1144297 : Blo 531801 1144297 := bstep (se 2 (by rfl) ⟨429111, by rfl⟩ : syracuseStep 1144297 = 858223) B858223
theorem B1799927 : Blo 531801 1799927 := bstep (se 1 (by rfl) ⟨1349945, by rfl⟩ : syracuseStep 1799927 = 2699891) B2699891
theorem B13006817 : Blo 531801 13006817 := bstep (se 2 (by rfl) ⟨4877556, by rfl⟩ : syracuseStep 13006817 = 9755113) B9755113
theorem B4160105 : Blo 531801 4160105 := bstep (se 2 (by rfl) ⟨1560039, by rfl⟩ : syracuseStep 4160105 = 3120079) B3120079
theorem B1801007 : Blo 531801 1801007 := bstep (se 1 (by rfl) ⟨1350755, by rfl⟩ : syracuseStep 1801007 = 2701511) B2701511
theorem B4324187 : Blo 531801 4324187 := bstep (se 1 (by rfl) ⟨3243140, by rfl⟩ : syracuseStep 4324187 = 6486281) B6486281
theorem B2030447 : Blo 531801 2030447 := bstep (se 1 (by rfl) ⟨1522835, by rfl⟩ : syracuseStep 2030447 = 3045671) B3045671
theorem B1080481 : Blo 531801 1080481 := bstep (se 2 (by rfl) ⟨405180, by rfl⟩ : syracuseStep 1080481 = 810361) B810361
theorem B1441127 : Blo 531801 1441127 := bstep (se 1 (by rfl) ⟨1080845, by rfl⟩ : syracuseStep 1441127 = 2161691) B2161691
theorem B1278089 : Blo 531801 1278089 := bstep (se 2 (by rfl) ⟨479283, by rfl⟩ : syracuseStep 1278089 = 958567) B958567
theorem B3571975 : Blo 531801 3571975 := bstep (se 1 (by rfl) ⟨2678981, by rfl⟩ : syracuseStep 3571975 = 5357963) B5357963
theorem B9765197 : Blo 531801 9765197 := bstep (se 3 (by rfl) ⟨1830974, by rfl⟩ : syracuseStep 9765197 = 3661949) B3661949
theorem B4882963 : Blo 531801 4882963 := bstep (se 1 (by rfl) ⟨3662222, by rfl⟩ : syracuseStep 4882963 = 7324445) B7324445
theorem B852623 : Blo 531801 852623 := bstep (se 1 (by rfl) ⟨639467, by rfl⟩ : syracuseStep 852623 = 1278935) B1278935
theorem B1705655 : Blo 531801 1705655 := bstep (se 1 (by rfl) ⟨1279241, by rfl⟩ : syracuseStep 1705655 = 2558483) B2558483
theorem B9734093 : Blo 531801 9734093 := bstep (se 3 (by rfl) ⟨1825142, by rfl⟩ : syracuseStep 9734093 = 3650285) B3650285
theorem B1706579 : Blo 531801 1706579 := bstep (se 1 (by rfl) ⟨1279934, by rfl⟩ : syracuseStep 1706579 = 2559869) B2559869
theorem B1248167 : Blo 531801 1248167 := bstep (se 1 (by rfl) ⟨936125, by rfl⟩ : syracuseStep 1248167 = 1872251) B1872251
theorem B19500011 : Blo 531801 19500011 := bstep (se 1 (by rfl) ⟨14625008, by rfl⟩ : syracuseStep 19500011 = 29250017) B29250017
theorem B1346615 : Blo 531801 1346615 := bstep (se 1 (by rfl) ⟨1009961, by rfl⟩ : syracuseStep 1346615 = 2019923) B2019923
theorem B1346665 : Blo 531801 1346665 := bstep (se 2 (by rfl) ⟨504999, by rfl⟩ : syracuseStep 1346665 = 1009999) B1009999
theorem B1805543 : Blo 531801 1805543 := bstep (se 1 (by rfl) ⟨1354157, by rfl⟩ : syracuseStep 1805543 = 2708315) B2708315
theorem B5934323 : Blo 531801 5934323 := bstep (se 1 (by rfl) ⟨4450742, by rfl⟩ : syracuseStep 5934323 = 8901485) B8901485
theorem B5148107 : Blo 531801 5148107 := bstep (se 1 (by rfl) ⟨3861080, by rfl⟩ : syracuseStep 5148107 = 7722161) B7722161
theorem B1543961 : Blo 531801 1543961 := bstep (se 2 (by rfl) ⟨578985, by rfl⟩ : syracuseStep 1543961 = 1157971) B1157971
theorem B758251 : Blo 531801 758251 := bstep (se 1 (by rfl) ⟨568688, by rfl⟩ : syracuseStep 758251 = 1137377) B1137377
theorem B4067819 : Blo 531801 4067819 := bstep (se 1 (by rfl) ⟨3050864, by rfl⟩ : syracuseStep 4067819 = 6101729) B6101729
theorem B1806839 : Blo 531801 1806839 := bstep (se 1 (by rfl) ⟨1355129, by rfl⟩ : syracuseStep 1806839 = 2710259) B2710259
theorem B1348103 : Blo 531801 1348103 := bstep (se 1 (by rfl) ⟨1011077, by rfl⟩ : syracuseStep 1348103 = 2022155) B2022155
theorem B1348123 : Blo 531801 1348123 := bstep (se 1 (by rfl) ⟨1011092, by rfl⟩ : syracuseStep 1348123 = 2022185) B2022185
theorem B3085823 : Blo 531801 3085823 := bstep (se 1 (by rfl) ⟨2314367, by rfl⟩ : syracuseStep 3085823 = 4628735) B4628735
theorem B1447451 : Blo 531801 1447451 := bstep (se 1 (by rfl) ⟨1085588, by rfl⟩ : syracuseStep 1447451 = 2171177) B2171177
theorem B759721 : Blo 531801 759721 := bstep (se 2 (by rfl) ⟨284895, by rfl⟩ : syracuseStep 759721 = 569791) B569791
theorem B1808297 : Blo 531801 1808297 := bstep (se 2 (by rfl) ⟨678111, by rfl⟩ : syracuseStep 1808297 = 1356223) B1356223
theorem B760313 : Blo 531801 760313 := bstep (se 2 (by rfl) ⟨285117, by rfl⟩ : syracuseStep 760313 = 570235) B570235
theorem B8231503 : Blo 531801 8231503 := bstep (se 1 (by rfl) ⟨6173627, by rfl⟩ : syracuseStep 8231503 = 12347255) B12347255
theorem B1350503 : Blo 531801 1350503 := bstep (se 1 (by rfl) ⟨1012877, by rfl⟩ : syracuseStep 1350503 = 2025755) B2025755
theorem B2169737 : Blo 531801 2169737 := bstep (se 2 (by rfl) ⟨813651, by rfl⟩ : syracuseStep 2169737 = 1627303) B1627303
theorem B2956475 : Blo 531801 2956475 := bstep (se 1 (by rfl) ⟨2217356, by rfl⟩ : syracuseStep 2956475 = 4434713) B4434713
theorem B761179 : Blo 531801 761179 := bstep (se 1 (by rfl) ⟨570884, by rfl⟩ : syracuseStep 761179 = 1141769) B1141769
theorem B1712011 : Blo 531801 1712011 := bstep (se 1 (by rfl) ⟨1284008, by rfl⟩ : syracuseStep 1712011 = 2568017) B2568017
theorem B1515455 : Blo 531801 1515455 := bstep (se 1 (by rfl) ⟨1136591, by rfl⟩ : syracuseStep 1515455 = 2273183) B2273183
theorem B532807 : Blo 531801 532807 := bstep (se 1 (by rfl) ⟨399605, by rfl⟩ : syracuseStep 532807 = 799211) B799211
theorem B532891 : Blo 531801 532891 := bstep (se 1 (by rfl) ⟨399668, by rfl⟩ : syracuseStep 532891 = 799337) B799337
theorem B533243 : Blo 531801 533243 := bstep (se 1 (by rfl) ⟨399932, by rfl⟩ : syracuseStep 533243 = 799865) B799865
theorem B1516457 : Blo 531801 1516457 := bstep (se 2 (by rfl) ⟨568671, by rfl⟩ : syracuseStep 1516457 = 1137343) B1137343
theorem B533759 : Blo 531801 533759 := bstep (se 1 (by rfl) ⟨400319, by rfl⟩ : syracuseStep 533759 = 800639) B800639
theorem B534171 : Blo 531801 534171 := bstep (se 1 (by rfl) ⟨400628, by rfl⟩ : syracuseStep 534171 = 801257) B801257
theorem B534383 : Blo 531801 534383 := bstep (se 1 (by rfl) ⟨400787, by rfl⟩ : syracuseStep 534383 = 801575) B801575
theorem B1353631 : Blo 531801 1353631 := bstep (se 1 (by rfl) ⟨1015223, by rfl⟩ : syracuseStep 1353631 = 2030447) B2030447
theorem B2697299 : Blo 531801 2697299 := bstep (se 1 (by rfl) ⟨2022974, by rfl⟩ : syracuseStep 2697299 = 4045949) B4045949
theorem B534687 : Blo 531801 534687 := bstep (se 1 (by rfl) ⟨401015, by rfl⟩ : syracuseStep 534687 = 802031) B802031
theorem B534735 : Blo 531801 534735 := bstep (se 1 (by rfl) ⟨401051, by rfl⟩ : syracuseStep 534735 = 802103) B802103
theorem B600295 : Blo 531801 600295 := bstep (se 1 (by rfl) ⟨450221, by rfl⟩ : syracuseStep 600295 = 900443) B900443
theorem B960751 : Blo 531801 960751 := bstep (se 1 (by rfl) ⟨720563, by rfl⟩ : syracuseStep 960751 = 1441127) B1441127
theorem B534783 : Blo 531801 534783 := bstep (se 1 (by rfl) ⟨401087, by rfl⟩ : syracuseStep 534783 = 802175) B802175
theorem B534855 : Blo 531801 534855 := bstep (se 1 (by rfl) ⟨401141, by rfl⟩ : syracuseStep 534855 = 802283) B802283
theorem B3418487 : Blo 531801 3418487 := bstep (se 1 (by rfl) ⟨2563865, by rfl⟩ : syracuseStep 3418487 = 5127731) B5127731
theorem B535295 : Blo 531801 535295 := bstep (se 1 (by rfl) ⟨401471, by rfl⟩ : syracuseStep 535295 = 802943) B802943
theorem B2436079 : Blo 531801 2436079 := bstep (se 1 (by rfl) ⟨1827059, by rfl⟩ : syracuseStep 2436079 = 3654119) B3654119
theorem B535663 : Blo 531801 535663 := bstep (se 1 (by rfl) ⟨401747, by rfl⟩ : syracuseStep 535663 = 803495) B803495
theorem B535711 : Blo 531801 535711 := bstep (se 1 (by rfl) ⟨401783, by rfl⟩ : syracuseStep 535711 = 803567) B803567
theorem B535743 : Blo 531801 535743 := bstep (se 1 (by rfl) ⟨401807, by rfl⟩ : syracuseStep 535743 = 803615) B803615
theorem B65547467 : Blo 531801 65547467 := bstep (se 1 (by rfl) ⟨49160600, by rfl⟩ : syracuseStep 65547467 = 98321201) B98321201
theorem B601627 : Blo 531801 601627 := bstep (se 1 (by rfl) ⟨451220, by rfl⟩ : syracuseStep 601627 = 902441) B902441
theorem B2895401 : Blo 531801 2895401 := bstep (se 2 (by rfl) ⟨1085775, by rfl⟩ : syracuseStep 2895401 = 2171551) B2171551
theorem B798311 : Blo 531801 798311 := bstep (se 1 (by rfl) ⟨598733, by rfl⟩ : syracuseStep 798311 = 1197467) B1197467
theorem B1355393 : Blo 531801 1355393 := bstep (se 2 (by rfl) ⟨508272, by rfl⟩ : syracuseStep 1355393 = 1016545) B1016545
theorem B2732383 : Blo 531801 2732383 := bstep (se 1 (by rfl) ⟨2049287, by rfl⟩ : syracuseStep 2732383 = 4098575) B4098575
theorem B602599 : Blo 531801 602599 := bstep (se 1 (by rfl) ⟨451949, by rfl⟩ : syracuseStep 602599 = 903899) B903899
theorem B799463 : Blo 531801 799463 := bstep (se 1 (by rfl) ⟨599597, by rfl⟩ : syracuseStep 799463 = 1199195) B1199195
theorem B800159 : Blo 531801 800159 := bstep (se 1 (by rfl) ⟨600119, by rfl⟩ : syracuseStep 800159 = 1200239) B1200239
theorem B899039 : Blo 531801 899039 := bstep (se 1 (by rfl) ⟨674279, by rfl⟩ : syracuseStep 899039 = 1348559) B1348559
theorem B800735 : Blo 531801 800735 := bstep (se 1 (by rfl) ⟨600551, by rfl⟩ : syracuseStep 800735 = 1201103) B1201103
theorem B7288861 : Blo 531801 7288861 := bstep (se 3 (by rfl) ⟨1366661, by rfl⟩ : syracuseStep 7288861 = 2733323) B2733323
theorem B800975 : Blo 531801 800975 := bstep (se 1 (by rfl) ⟨600731, by rfl⟩ : syracuseStep 800975 = 1201463) B1201463
theorem B2570615 : Blo 531801 2570615 := bstep (se 1 (by rfl) ⟨1927961, by rfl⟩ : syracuseStep 2570615 = 3855923) B3855923
theorem B801179 : Blo 531801 801179 := bstep (se 1 (by rfl) ⟨600884, by rfl⟩ : syracuseStep 801179 = 1201769) B1201769
theorem B1522471 : Blo 531801 1522471 := bstep (se 1 (by rfl) ⟨1141853, by rfl⟩ : syracuseStep 1522471 = 2283707) B2283707
theorem B73776365 : Blo 531801 73776365 := bstep (se 3 (by rfl) ⟨13833068, by rfl⟩ : syracuseStep 73776365 = 27666137) B27666137
theorem B59030957 : Blo 531801 59030957 := bstep (se 3 (by rfl) ⟨11068304, by rfl⟩ : syracuseStep 59030957 = 22136609) B22136609
theorem B6831641 : Blo 531801 6831641 := bstep (se 2 (by rfl) ⟨2561865, by rfl⟩ : syracuseStep 6831641 = 5123731) B5123731
theorem B1523519 : Blo 531801 1523519 := bstep (se 1 (by rfl) ⟨1142639, by rfl⟩ : syracuseStep 1523519 = 2285279) B2285279
theorem B868649 : Blo 531801 868649 := bstep (se 2 (by rfl) ⟨325743, by rfl⟩ : syracuseStep 868649 = 651487) B651487
theorem B1196711 : Blo 531801 1196711 := bstep (se 1 (by rfl) ⟨897533, by rfl⟩ : syracuseStep 1196711 = 1795067) B1795067
theorem B3031775 : Blo 531801 3031775 := bstep (se 1 (by rfl) ⟨2273831, by rfl⟩ : syracuseStep 3031775 = 4547663) B4547663
theorem B2704103 : Blo 531801 2704103 := bstep (se 1 (by rfl) ⟨2028077, by rfl⟩ : syracuseStep 2704103 = 4056155) B4056155
theorem B1196783 : Blo 531801 1196783 := bstep (se 1 (by rfl) ⟨897587, by rfl⟩ : syracuseStep 1196783 = 1795175) B1795175
theorem B541927 : Blo 531801 541927 := bstep (se 1 (by rfl) ⟨406445, by rfl⟩ : syracuseStep 541927 = 812891) B812891
theorem B1525661 : Blo 531801 1525661 := bstep (se 3 (by rfl) ⟨286061, by rfl⟩ : syracuseStep 1525661 = 572123) B572123
theorem B5130155 : Blo 531801 5130155 := bstep (se 1 (by rfl) ⟨3847616, by rfl⟩ : syracuseStep 5130155 = 7695233) B7695233
theorem B2574305 : Blo 531801 2574305 := bstep (se 2 (by rfl) ⟨965364, by rfl⟩ : syracuseStep 2574305 = 1930729) B1930729
theorem B1525729 : Blo 531801 1525729 := bstep (se 2 (by rfl) ⟨572148, by rfl⟩ : syracuseStep 1525729 = 1144297) B1144297
theorem B674239 : Blo 531801 674239 := bstep (se 1 (by rfl) ⟨505679, by rfl⟩ : syracuseStep 674239 = 1011359) B1011359
theorem B6179809 : Blo 531801 6179809 := bstep (se 2 (by rfl) ⟨2317428, by rfl⟩ : syracuseStep 6179809 = 4634857) B4634857
theorem B1821737 : Blo 531801 1821737 := bstep (se 2 (by rfl) ⟨683151, by rfl⟩ : syracuseStep 1821737 = 1366303) B1366303
theorem B1199339 : Blo 531801 1199339 := bstep (se 1 (by rfl) ⟨899504, by rfl⟩ : syracuseStep 1199339 = 1799009) B1799009
theorem B4869355 : Blo 531801 4869355 := bstep (se 1 (by rfl) ⟨3652016, by rfl⟩ : syracuseStep 4869355 = 7304033) B7304033
theorem B17288441 : Blo 531801 17288441 := bstep (se 2 (by rfl) ⟨6483165, by rfl⟩ : syracuseStep 17288441 = 12966331) B12966331
theorem B2346367 : Blo 531801 2346367 := bstep (se 1 (by rfl) ⟨1759775, by rfl⟩ : syracuseStep 2346367 = 3519551) B3519551
theorem B1199951 : Blo 531801 1199951 := bstep (se 1 (by rfl) ⟨899963, by rfl⟩ : syracuseStep 1199951 = 1799927) B1799927
theorem B1199969 : Blo 531801 1199969 := bstep (se 2 (by rfl) ⟨449988, by rfl⟩ : syracuseStep 1199969 = 899977) B899977
theorem B1200041 : Blo 531801 1200041 := bstep (se 2 (by rfl) ⟨450015, by rfl⟩ : syracuseStep 1200041 = 900031) B900031
theorem B8671211 : Blo 531801 8671211 := bstep (se 1 (by rfl) ⟨6503408, by rfl⟩ : syracuseStep 8671211 = 13006817) B13006817
theorem B6082775 : Blo 531801 6082775 := bstep (se 1 (by rfl) ⟨4562081, by rfl⟩ : syracuseStep 6082775 = 9124163) B9124163
theorem B2773403 : Blo 531801 2773403 := bstep (se 1 (by rfl) ⟨2080052, by rfl⟩ : syracuseStep 2773403 = 4160105) B4160105
theorem B15389189 : Blo 531801 15389189 := bstep (se 4 (by rfl) ⟨1442736, by rfl⟩ : syracuseStep 15389189 = 2885473) B2885473
theorem B1200671 : Blo 531801 1200671 := bstep (se 1 (by rfl) ⟨900503, by rfl⟩ : syracuseStep 1200671 = 1801007) B1801007
theorem B677479 : Blo 531801 677479 := bstep (se 1 (by rfl) ⟨508109, by rfl⟩ : syracuseStep 677479 = 1016219) B1016219
theorem B7296743 : Blo 531801 7296743 := bstep (se 1 (by rfl) ⟨5472557, by rfl⟩ : syracuseStep 7296743 = 10945115) B10945115
theorem B2709287 : Blo 531801 2709287 := bstep (se 1 (by rfl) ⟨2031965, by rfl⟩ : syracuseStep 2709287 = 4063931) B4063931
theorem B3037175 : Blo 531801 3037175 := bstep (se 1 (by rfl) ⟨2277881, by rfl⟩ : syracuseStep 3037175 = 4555763) B4555763
theorem B3070187 : Blo 531801 3070187 := bstep (se 1 (by rfl) ⟨2302640, by rfl⟩ : syracuseStep 3070187 = 4605281) B4605281
theorem B1202831 : Blo 531801 1202831 := bstep (se 1 (by rfl) ⟨902123, by rfl⟩ : syracuseStep 1202831 = 1804247) B1804247
theorem B1727423 : Blo 531801 1727423 := bstep (se 1 (by rfl) ⟨1295567, by rfl⟩ : syracuseStep 1727423 = 2591135) B2591135
theorem B1203209 : Blo 531801 1203209 := bstep (se 2 (by rfl) ⟨451203, by rfl⟩ : syracuseStep 1203209 = 902407) B902407
theorem B1924283 : Blo 531801 1924283 := bstep (se 1 (by rfl) ⟨1443212, by rfl⟩ : syracuseStep 1924283 = 2886425) B2886425
theorem B5496445 : Blo 531801 5496445 := bstep (se 3 (by rfl) ⟨1030583, by rfl⟩ : syracuseStep 5496445 = 2061167) B2061167
theorem B2711393 : Blo 531801 2711393 := bstep (se 2 (by rfl) ⟨1016772, by rfl⟩ : syracuseStep 2711393 = 2033545) B2033545
theorem B3858313 : Blo 531801 3858313 := bstep (se 2 (by rfl) ⟨1446867, by rfl⟩ : syracuseStep 3858313 = 2893735) B2893735
theorem B2023339 : Blo 531801 2023339 := bstep (se 1 (by rfl) ⟨1517504, by rfl⟩ : syracuseStep 2023339 = 3035009) B3035009
theorem B2875337 : Blo 531801 2875337 := bstep (se 2 (by rfl) ⟨1078251, by rfl⟩ : syracuseStep 2875337 = 2156503) B2156503
theorem B1204199 : Blo 531801 1204199 := bstep (se 1 (by rfl) ⟨903149, by rfl⟩ : syracuseStep 1204199 = 1806299) B1806299
theorem B1204649 : Blo 531801 1204649 := bstep (se 2 (by rfl) ⟨451743, by rfl⟩ : syracuseStep 1204649 = 903487) B903487
theorem B1139923 : Blo 531801 1139923 := bstep (se 1 (by rfl) ⟨854942, by rfl⟩ : syracuseStep 1139923 = 1709885) B1709885
theorem B4744423 : Blo 531801 4744423 := bstep (se 1 (by rfl) ⟨3558317, by rfl⟩ : syracuseStep 4744423 = 7116635) B7116635
theorem B1795931 : Blo 531801 1795931 := bstep (se 1 (by rfl) ⟨1346948, by rfl⟩ : syracuseStep 1795931 = 2693897) B2693897
theorem B6842303 : Blo 531801 6842303 := bstep (se 1 (by rfl) ⟨5131727, by rfl⟩ : syracuseStep 6842303 = 10263455) B10263455
theorem B4057127 : Blo 531801 4057127 := bstep (se 1 (by rfl) ⟨3042845, by rfl⟩ : syracuseStep 4057127 = 6085691) B6085691
theorem B3074557 : Blo 531801 3074557 := bstep (se 3 (by rfl) ⟨576479, by rfl⟩ : syracuseStep 3074557 = 1152959) B1152959
theorem B2747567 : Blo 531801 2747567 := bstep (se 1 (by rfl) ⟨2060675, by rfl⟩ : syracuseStep 2747567 = 4121351) B4121351
theorem B1797551 : Blo 531801 1797551 := bstep (se 1 (by rfl) ⟨1348163, by rfl⟩ : syracuseStep 1797551 = 2696327) B2696327
theorem B3042755 : Blo 531801 3042755 := bstep (se 1 (by rfl) ⟨2282066, by rfl⟩ : syracuseStep 3042755 = 4564133) B4564133
theorem B2027015 : Blo 531801 2027015 := bstep (se 1 (by rfl) ⟨1520261, by rfl⟩ : syracuseStep 2027015 = 3040523) B3040523
theorem B4059071 : Blo 531801 4059071 := bstep (se 1 (by rfl) ⟨3044303, by rfl⟩ : syracuseStep 4059071 = 6088607) B6088607
theorem B25260055 : Blo 531801 25260055 := bstep (se 1 (by rfl) ⟨18945041, by rfl⟩ : syracuseStep 25260055 = 37890083) B37890083
theorem B3043757 : Blo 531801 3043757 := bstep (se 3 (by rfl) ⟨570704, by rfl⟩ : syracuseStep 3043757 = 1141409) B1141409
theorem B1798631 : Blo 531801 1798631 := bstep (se 1 (by rfl) ⟨1348973, by rfl⟩ : syracuseStep 1798631 = 2697947) B2697947
theorem B2159111 : Blo 531801 2159111 := bstep (se 1 (by rfl) ⟨1619333, by rfl⟩ : syracuseStep 2159111 = 3238667) B3238667
theorem B1143323 : Blo 531801 1143323 := bstep (se 1 (by rfl) ⟨857492, by rfl⟩ : syracuseStep 1143323 = 1714985) B1714985
theorem B11727773 : Blo 531801 11727773 := bstep (se 3 (by rfl) ⟨2198957, by rfl⟩ : syracuseStep 11727773 = 4397915) B4397915
theorem B1012763 : Blo 531801 1012763 := bstep (se 1 (by rfl) ⟨759572, by rfl⟩ : syracuseStep 1012763 = 1519145) B1519145
theorem B2028671 : Blo 531801 2028671 := bstep (se 1 (by rfl) ⟨1521503, by rfl⟩ : syracuseStep 2028671 = 3043007) B3043007
theorem B6060905 : Blo 531801 6060905 := bstep (se 2 (by rfl) ⟨2272839, by rfl⟩ : syracuseStep 6060905 = 4545679) B4545679
theorem B1440641 : Blo 531801 1440641 := bstep (se 2 (by rfl) ⟨540240, by rfl⟩ : syracuseStep 1440641 = 1080481) B1080481
theorem B2882791 : Blo 531801 2882791 := bstep (se 1 (by rfl) ⟨2162093, by rfl⟩ : syracuseStep 2882791 = 4324187) B4324187
theorem B852059 : Blo 531801 852059 := bstep (se 1 (by rfl) ⟨639044, by rfl⟩ : syracuseStep 852059 = 1278089) B1278089
theorem B1802735 : Blo 531801 1802735 := bstep (se 1 (by rfl) ⟨1352051, by rfl⟩ : syracuseStep 1802735 = 2704103) B2704103
theorem B1017107 : Blo 531801 1017107 := bstep (se 1 (by rfl) ⟨762830, by rfl⟩ : syracuseStep 1017107 = 1525661) B1525661
theorem B6489395 : Blo 531801 6489395 := bstep (se 1 (by rfl) ⟨4867046, by rfl⟩ : syracuseStep 6489395 = 9734093) B9734093
theorem B6325897 : Blo 531801 6325897 := bstep (se 2 (by rfl) ⟨2372211, by rfl⟩ : syracuseStep 6325897 = 4744423) B4744423
theorem B722569 : Blo 531801 722569 := bstep (se 2 (by rfl) ⟨270963, by rfl⟩ : syracuseStep 722569 = 541927) B541927
theorem B1804841 : Blo 531801 1804841 := bstep (se 2 (by rfl) ⟨676815, by rfl⟩ : syracuseStep 1804841 = 1353631) B1353631
theorem B2034305 : Blo 531801 2034305 := bstep (se 2 (by rfl) ⟨762864, by rfl⟩ : syracuseStep 2034305 = 1525729) B1525729
theorem B10259459 : Blo 531801 10259459 := bstep (se 1 (by rfl) ⟨7694594, by rfl⟩ : syracuseStep 10259459 = 15389189) B15389189
theorem B4099409 : Blo 531801 4099409 := bstep (se 2 (by rfl) ⟨1537278, by rfl⟩ : syracuseStep 4099409 = 3074557) B3074557
theorem B1806191 : Blo 531801 1806191 := bstep (se 1 (by rfl) ⟨1354643, by rfl⟩ : syracuseStep 1806191 = 2709287) B2709287
theorem B3248105 : Blo 531801 3248105 := bstep (se 2 (by rfl) ⟨1218039, by rfl⟩ : syracuseStep 3248105 = 2436079) B2436079
theorem B8228861 : Blo 531801 8228861 := bstep (se 3 (by rfl) ⟨1542911, by rfl⟩ : syracuseStep 8228861 = 3085823) B3085823
theorem B6492473 : Blo 531801 6492473 := bstep (se 2 (by rfl) ⟨2434677, by rfl⟩ : syracuseStep 6492473 = 4869355) B4869355
theorem B1446491 : Blo 531801 1446491 := bstep (se 1 (by rfl) ⟨1084868, by rfl⟩ : syracuseStep 1446491 = 2169737) B2169737
theorem B1151615 : Blo 531801 1151615 := bstep (se 1 (by rfl) ⟨863711, by rfl⟩ : syracuseStep 1151615 = 1727423) B1727423
theorem B1970983 : Blo 531801 1970983 := bstep (se 1 (by rfl) ⟨1478237, by rfl⟩ : syracuseStep 1970983 = 2956475) B2956475
theorem B1807595 : Blo 531801 1807595 := bstep (se 1 (by rfl) ⟨1355696, by rfl⟩ : syracuseStep 1807595 = 2711393) B2711393
theorem B3643177 : Blo 531801 3643177 := bstep (se 2 (by rfl) ⟨1366191, by rfl⟩ : syracuseStep 3643177 = 2732383) B2732383
theorem B4561535 : Blo 531801 4561535 := bstep (se 1 (by rfl) ⟨3421151, by rfl⟩ : syracuseStep 4561535 = 6842303) B6842303
theorem B1351343 : Blo 531801 1351343 := bstep (se 1 (by rfl) ⟨1013507, by rfl⟩ : syracuseStep 1351343 = 2027015) B2027015
theorem B532207 : Blo 531801 532207 := bstep (se 1 (by rfl) ⟨399155, by rfl⟩ : syracuseStep 532207 = 798311) B798311
theorem B4857965 : Blo 531801 4857965 := bstep (se 3 (by rfl) ⟨910868, by rfl⟩ : syracuseStep 4857965 = 1821737) B1821737
theorem B762215 : Blo 531801 762215 := bstep (se 1 (by rfl) ⟨571661, by rfl⟩ : syracuseStep 762215 = 1143323) B1143323
theorem B532975 : Blo 531801 532975 := bstep (se 1 (by rfl) ⟨399731, by rfl⟩ : syracuseStep 532975 = 799463) B799463
theorem B1352447 : Blo 531801 1352447 := bstep (se 1 (by rfl) ⟨1014335, by rfl⟩ : syracuseStep 1352447 = 2028671) B2028671
theorem B533439 : Blo 531801 533439 := bstep (se 1 (by rfl) ⟨400079, by rfl⟩ : syracuseStep 533439 = 800159) B800159
theorem B599359 : Blo 531801 599359 := bstep (se 1 (by rfl) ⟨449519, by rfl⟩ : syracuseStep 599359 = 899039) B899039
theorem B533823 : Blo 531801 533823 := bstep (se 1 (by rfl) ⟨400367, by rfl⟩ : syracuseStep 533823 = 800735) B800735
theorem B533983 : Blo 531801 533983 := bstep (se 1 (by rfl) ⟨400487, by rfl⟩ : syracuseStep 533983 = 800975) B800975
theorem B1713743 : Blo 531801 1713743 := bstep (se 1 (by rfl) ⟨1285307, by rfl⟩ : syracuseStep 1713743 = 2570615) B2570615
theorem B534119 : Blo 531801 534119 := bstep (se 1 (by rfl) ⟨400589, by rfl⟩ : syracuseStep 534119 = 801179) B801179
theorem B3843721 : Blo 531801 3843721 := bstep (se 2 (by rfl) ⟨1441395, by rfl⟩ : syracuseStep 3843721 = 2882791) B2882791
theorem B4040603 : Blo 531801 4040603 := bstep (se 1 (by rfl) ⟨3030452, by rfl⟩ : syracuseStep 4040603 = 6060905) B6060905
theorem B960427 : Blo 531801 960427 := bstep (se 1 (by rfl) ⟨720320, by rfl⟩ : syracuseStep 960427 = 1440641) B1440641
theorem B2697785 : Blo 531801 2697785 := bstep (se 2 (by rfl) ⟨1011669, by rfl⟩ : syracuseStep 2697785 = 2023339) B2023339
theorem B134720293 : Blo 531801 134720293 := bstep (se 4 (by rfl) ⟨12630027, by rfl⟩ : syracuseStep 134720293 = 25260055) B25260055
theorem B4762633 : Blo 531801 4762633 := bstep (se 2 (by rfl) ⟨1785987, by rfl⟩ : syracuseStep 4762633 = 3571975) B3571975
theorem B568415 : Blo 531801 568415 := bstep (se 1 (by rfl) ⟨426311, by rfl⟩ : syracuseStep 568415 = 852623) B852623
theorem B797807 : Blo 531801 797807 := bstep (se 1 (by rfl) ⟨598355, by rfl⟩ : syracuseStep 797807 = 1196711) B1196711
theorem B797855 : Blo 531801 797855 := bstep (se 1 (by rfl) ⟨598391, by rfl⟩ : syracuseStep 797855 = 1196783) B1196783
theorem B5124005 : Blo 531801 5124005 := bstep (se 4 (by rfl) ⟨480375, by rfl⟩ : syracuseStep 5124005 = 960751) B960751
theorem B3420103 : Blo 531801 3420103 := bstep (se 1 (by rfl) ⟨2565077, by rfl⟩ : syracuseStep 3420103 = 5130155) B5130155
theorem B1716203 : Blo 531801 1716203 := bstep (se 1 (by rfl) ⟨1287152, by rfl⟩ : syracuseStep 1716203 = 2574305) B2574305
theorem B1519897 : Blo 531801 1519897 := bstep (se 2 (by rfl) ⟨569961, by rfl⟩ : syracuseStep 1519897 = 1139923) B1139923
theorem B832111 : Blo 531801 832111 := bstep (se 1 (by rfl) ⟨624083, by rfl⟩ : syracuseStep 832111 = 1248167) B1248167
theorem B897743 : Blo 531801 897743 := bstep (se 1 (by rfl) ⟨673307, by rfl⟩ : syracuseStep 897743 = 1346615) B1346615
theorem B799559 : Blo 531801 799559 := bstep (se 1 (by rfl) ⟨599669, by rfl⟩ : syracuseStep 799559 = 1199339) B1199339
theorem B799967 : Blo 531801 799967 := bstep (se 1 (by rfl) ⟨599975, by rfl⟩ : syracuseStep 799967 = 1199951) B1199951
theorem B4044005 : Blo 531801 4044005 := bstep (se 4 (by rfl) ⟨379125, by rfl⟩ : syracuseStep 4044005 = 758251) B758251
theorem B799979 : Blo 531801 799979 := bstep (se 1 (by rfl) ⟨599984, by rfl⟩ : syracuseStep 799979 = 1199969) B1199969
theorem B800027 : Blo 531801 800027 := bstep (se 1 (by rfl) ⟨600020, by rfl⟩ : syracuseStep 800027 = 1200041) B1200041
theorem B5780807 : Blo 531801 5780807 := bstep (se 1 (by rfl) ⟨4335605, by rfl⟩ : syracuseStep 5780807 = 8671211) B8671211
theorem B2700701 : Blo 531801 2700701 := bstep (se 3 (by rfl) ⟨506381, by rfl⟩ : syracuseStep 2700701 = 1012763) B1012763
theorem B1848935 : Blo 531801 1848935 := bstep (se 1 (by rfl) ⟨1386701, by rfl⟩ : syracuseStep 1848935 = 2773403) B2773403
theorem B800393 : Blo 531801 800393 := bstep (se 2 (by rfl) ⟨300147, by rfl⟩ : syracuseStep 800393 = 600295) B600295
theorem B898735 : Blo 531801 898735 := bstep (se 1 (by rfl) ⟨674051, by rfl⟩ : syracuseStep 898735 = 1348103) B1348103
theorem B800447 : Blo 531801 800447 := bstep (se 1 (by rfl) ⟨600335, by rfl⟩ : syracuseStep 800447 = 1200671) B1200671
theorem B898985 : Blo 531801 898985 := bstep (se 2 (by rfl) ⟨337119, by rfl⟩ : syracuseStep 898985 = 674239) B674239
theorem B964967 : Blo 531801 964967 := bstep (se 1 (by rfl) ⟨723725, by rfl⟩ : syracuseStep 964967 = 1447451) B1447451
theorem B8239745 : Blo 531801 8239745 := bstep (se 2 (by rfl) ⟨3089904, by rfl⟩ : syracuseStep 8239745 = 6179809) B6179809
theorem B2046791 : Blo 531801 2046791 := bstep (se 1 (by rfl) ⟨1535093, by rfl⟩ : syracuseStep 2046791 = 3070187) B3070187
theorem B801887 : Blo 531801 801887 := bstep (se 1 (by rfl) ⟨601415, by rfl⟩ : syracuseStep 801887 = 1202831) B1202831
theorem B3128489 : Blo 531801 3128489 := bstep (se 2 (by rfl) ⟨1173183, by rfl⟩ : syracuseStep 3128489 = 2346367) B2346367
theorem B900335 : Blo 531801 900335 := bstep (se 1 (by rfl) ⟨675251, by rfl⟩ : syracuseStep 900335 = 1350503) B1350503
theorem B802139 : Blo 531801 802139 := bstep (se 1 (by rfl) ⟨601604, by rfl⟩ : syracuseStep 802139 = 1203209) B1203209
theorem B802169 : Blo 531801 802169 := bstep (se 2 (by rfl) ⟨300813, by rfl⟩ : syracuseStep 802169 = 601627) B601627
theorem B1916891 : Blo 531801 1916891 := bstep (se 1 (by rfl) ⟨1437668, by rfl⟩ : syracuseStep 1916891 = 2875337) B2875337
theorem B802799 : Blo 531801 802799 := bstep (se 1 (by rfl) ⟨602099, by rfl⟩ : syracuseStep 802799 = 1204199) B1204199
theorem B803099 : Blo 531801 803099 := bstep (se 1 (by rfl) ⟨602324, by rfl⟩ : syracuseStep 803099 = 1204649) B1204649
theorem B803465 : Blo 531801 803465 := bstep (se 2 (by rfl) ⟨301299, by rfl⟩ : syracuseStep 803465 = 602599) B602599
theorem B1197287 : Blo 531801 1197287 := bstep (se 1 (by rfl) ⟨897965, by rfl⟩ : syracuseStep 1197287 = 1795931) B1795931
theorem B2704751 : Blo 531801 2704751 := bstep (se 1 (by rfl) ⟨2028563, by rfl⟩ : syracuseStep 2704751 = 4057127) B4057127
theorem B2278991 : Blo 531801 2278991 := bstep (se 1 (by rfl) ⟨1709243, by rfl⟩ : syracuseStep 2278991 = 3418487) B3418487
theorem B43698311 : Blo 531801 43698311 := bstep (se 1 (by rfl) ⟨32773733, by rfl⟩ : syracuseStep 43698311 = 65547467) B65547467
theorem B903305 : Blo 531801 903305 := bstep (se 2 (by rfl) ⟨338739, by rfl⟩ : syracuseStep 903305 = 677479) B677479
theorem B1198367 : Blo 531801 1198367 := bstep (se 1 (by rfl) ⟨898775, by rfl⟩ : syracuseStep 1198367 = 1797551) B1797551
theorem B903595 : Blo 531801 903595 := bstep (se 1 (by rfl) ⟨677696, by rfl⟩ : syracuseStep 903595 = 1355393) B1355393
theorem B2706047 : Blo 531801 2706047 := bstep (se 1 (by rfl) ⟨2029535, by rfl⟩ : syracuseStep 2706047 = 4059071) B4059071
theorem B9718481 : Blo 531801 9718481 := bstep (se 2 (by rfl) ⟨3644430, by rfl⟩ : syracuseStep 9718481 = 7288861) B7288861
theorem B1199087 : Blo 531801 1199087 := bstep (se 1 (by rfl) ⟨899315, by rfl⟩ : syracuseStep 1199087 = 1798631) B1798631
theorem B7326845 : Blo 531801 7326845 := bstep (se 3 (by rfl) ⟨1373783, by rfl⟩ : syracuseStep 7326845 = 2747567) B2747567
theorem B5131421 : Blo 531801 5131421 := bstep (se 3 (by rfl) ⟨962141, by rfl⟩ : syracuseStep 5131421 = 1924283) B1924283
theorem B7818515 : Blo 531801 7818515 := bstep (se 1 (by rfl) ⟨5863886, by rfl⟩ : syracuseStep 7818515 = 11727773) B11727773
theorem B4117229 : Blo 531801 4117229 := bstep (se 3 (by rfl) ⟨771980, by rfl⟩ : syracuseStep 4117229 = 1543961) B1543961
theorem B7328593 : Blo 531801 7328593 := bstep (se 2 (by rfl) ⟨2748222, by rfl⟩ : syracuseStep 7328593 = 5496445) B5496445
theorem B2282681 : Blo 531801 2282681 := bstep (se 2 (by rfl) ⟨856005, by rfl⟩ : syracuseStep 2282681 = 1712011) B1712011
theorem B6510131 : Blo 531801 6510131 := bstep (se 1 (by rfl) ⟨4882598, by rfl⟩ : syracuseStep 6510131 = 9765197) B9765197
theorem B2021183 : Blo 531801 2021183 := bstep (se 1 (by rfl) ⟨1515887, by rfl⟩ : syracuseStep 2021183 = 3031775) B3031775
theorem B6510617 : Blo 531801 6510617 := bstep (se 2 (by rfl) ⟨2441481, by rfl⟩ : syracuseStep 6510617 = 4882963) B4882963
theorem B1137719 : Blo 531801 1137719 := bstep (se 1 (by rfl) ⟨853289, by rfl⟩ : syracuseStep 1137719 = 1706579) B1706579
theorem B13000007 : Blo 531801 13000007 := bstep (se 1 (by rfl) ⟨9750005, by rfl⟩ : syracuseStep 13000007 = 19500011) B19500011
theorem B1203695 : Blo 531801 1203695 := bstep (se 1 (by rfl) ⟨902771, by rfl⟩ : syracuseStep 1203695 = 1805543) B1805543
theorem B3956215 : Blo 531801 3956215 := bstep (se 1 (by rfl) ⟨2967161, by rfl⟩ : syracuseStep 3956215 = 5934323) B5934323
theorem B11525627 : Blo 531801 11525627 := bstep (se 1 (by rfl) ⟨8644220, by rfl⟩ : syracuseStep 11525627 = 17288441) B17288441
theorem B3432071 : Blo 531801 3432071 := bstep (se 1 (by rfl) ⟨2574053, by rfl⟩ : syracuseStep 3432071 = 5148107) B5148107
theorem B4055183 : Blo 531801 4055183 := bstep (se 1 (by rfl) ⟨3041387, by rfl⟩ : syracuseStep 4055183 = 6082775) B6082775
theorem B2711879 : Blo 531801 2711879 := bstep (se 1 (by rfl) ⟨2033909, by rfl⟩ : syracuseStep 2711879 = 4067819) B4067819
theorem B1204559 : Blo 531801 1204559 := bstep (se 1 (by rfl) ⟨903419, by rfl⟩ : syracuseStep 1204559 = 1806839) B1806839
theorem B9265589 : Blo 531801 9265589 := bstep (se 5 (by rfl) ⟨434324, by rfl⟩ : syracuseStep 9265589 = 868649) B868649
theorem B1205531 : Blo 531801 1205531 := bstep (se 1 (by rfl) ⟨904148, by rfl⟩ : syracuseStep 1205531 = 1808297) B1808297
theorem B2024783 : Blo 531801 2024783 := bstep (se 1 (by rfl) ⟨1518587, by rfl⟩ : syracuseStep 2024783 = 3037175) B3037175
theorem B1795553 : Blo 531801 1795553 := bstep (se 2 (by rfl) ⟨673332, by rfl⟩ : syracuseStep 1795553 = 1346665) B1346665
theorem B4548413 : Blo 531801 4548413 := bstep (se 3 (by rfl) ⟨852827, by rfl⟩ : syracuseStep 4548413 = 1705655) B1705655
theorem B19457981 : Blo 531801 19457981 := bstep (se 3 (by rfl) ⟨3648371, by rfl⟩ : syracuseStep 19457981 = 7296743) B7296743
theorem B1010303 : Blo 531801 1010303 := bstep (se 1 (by rfl) ⟨757727, by rfl⟩ : syracuseStep 1010303 = 1515455) B1515455
theorem B1010971 : Blo 531801 1010971 := bstep (se 1 (by rfl) ⟨758228, by rfl⟩ : syracuseStep 1010971 = 1516457) B1516457
theorem B1797497 : Blo 531801 1797497 := bstep (se 2 (by rfl) ⟨674061, by rfl⟩ : syracuseStep 1797497 = 1348123) B1348123
theorem B2027501 : Blo 531801 2027501 := bstep (se 3 (by rfl) ⟨380156, by rfl⟩ : syracuseStep 2027501 = 760313) B760313
theorem B1798199 : Blo 531801 1798199 := bstep (se 1 (by rfl) ⟨1348649, by rfl⟩ : syracuseStep 1798199 = 2697299) B2697299
theorem B2028503 : Blo 531801 2028503 := bstep (se 1 (by rfl) ⟨1521377, by rfl⟩ : syracuseStep 2028503 = 3042755) B3042755
theorem B1930267 : Blo 531801 1930267 := bstep (se 1 (by rfl) ⟨1447700, by rfl⟩ : syracuseStep 1930267 = 2895401) B2895401
theorem B1012961 : Blo 531801 1012961 := bstep (se 2 (by rfl) ⟨379860, by rfl⟩ : syracuseStep 1012961 = 759721) B759721
theorem B2029171 : Blo 531801 2029171 := bstep (se 1 (by rfl) ⟨1521878, by rfl⟩ : syracuseStep 2029171 = 3043757) B3043757
theorem B1439407 : Blo 531801 1439407 := bstep (se 1 (by rfl) ⟨1079555, by rfl⟩ : syracuseStep 1439407 = 2159111) B2159111
theorem B10975337 : Blo 531801 10975337 := bstep (se 2 (by rfl) ⟨4115751, by rfl⟩ : syracuseStep 10975337 = 8231503) B8231503
theorem B2029961 : Blo 531801 2029961 := bstep (se 2 (by rfl) ⟨761235, by rfl⟩ : syracuseStep 2029961 = 1522471) B1522471
theorem B1014905 : Blo 531801 1014905 := bstep (se 2 (by rfl) ⟨380589, by rfl⟩ : syracuseStep 1014905 = 761179) B761179
theorem B49184243 : Blo 531801 49184243 := bstep (se 1 (by rfl) ⟨36888182, by rfl⟩ : syracuseStep 49184243 = 73776365) B73776365
theorem B39353971 : Blo 531801 39353971 := bstep (se 1 (by rfl) ⟨29515478, by rfl⟩ : syracuseStep 39353971 = 59030957) B59030957
theorem B4554427 : Blo 531801 4554427 := bstep (se 1 (by rfl) ⟨3415820, by rfl⟩ : syracuseStep 4554427 = 6831641) B6831641
theorem B5144417 : Blo 531801 5144417 := bstep (se 2 (by rfl) ⟨1929156, by rfl⟩ : syracuseStep 5144417 = 3858313) B3858313
theorem B1015679 : Blo 531801 1015679 := bstep (se 1 (by rfl) ⟨761759, by rfl⟩ : syracuseStep 1015679 = 1523519) B1523519
theorem B4326263 : Blo 531801 4326263 := bstep (se 1 (by rfl) ⟨3244697, by rfl⟩ : syracuseStep 4326263 = 6489395) B6489395
theorem B1803167 : Blo 531801 1803167 := bstep (se 1 (by rfl) ⟨1352375, by rfl⟩ : syracuseStep 1803167 = 2704751) B2704751
theorem B2032573 : Blo 531801 2032573 := bstep (se 3 (by rfl) ⟨381107, by rfl⟩ : syracuseStep 2032573 = 762215) B762215
theorem B29132207 : Blo 531801 29132207 := bstep (se 1 (by rfl) ⟨21849155, by rfl⟩ : syracuseStep 29132207 = 43698311) B43698311
theorem B1804031 : Blo 531801 1804031 := bstep (se 1 (by rfl) ⟨1353023, by rfl⟩ : syracuseStep 1804031 = 2706047) B2706047
theorem B4884563 : Blo 531801 4884563 := bstep (se 1 (by rfl) ⟨3663422, by rfl⟩ : syracuseStep 4884563 = 7326845) B7326845
theorem B5212343 : Blo 531801 5212343 := bstep (se 1 (by rfl) ⟨3909257, by rfl⟩ : syracuseStep 5212343 = 7818515) B7818515
theorem B1280569 : Blo 531801 1280569 := bstep (se 2 (by rfl) ⟨480213, by rfl⟩ : syracuseStep 1280569 = 960427) B960427
theorem B4328315 : Blo 531801 4328315 := bstep (se 1 (by rfl) ⟨3246236, by rfl⟩ : syracuseStep 4328315 = 6492473) B6492473
theorem B1347455 : Blo 531801 1347455 := bstep (se 1 (by rfl) ⟨1010591, by rfl⟩ : syracuseStep 1347455 = 2021183) B2021183
theorem B1347961 : Blo 531801 1347961 := bstep (se 2 (by rfl) ⟨505485, by rfl⟩ : syracuseStep 1347961 = 1010971) B1010971
theorem B758479 : Blo 531801 758479 := bstep (se 1 (by rfl) ⟨568859, by rfl⟩ : syracuseStep 758479 = 1137719) B1137719
theorem B4560137 : Blo 531801 4560137 := bstep (se 2 (by rfl) ⟨1710051, by rfl⟩ : syracuseStep 4560137 = 3420103) B3420103
theorem B1807919 : Blo 531801 1807919 := bstep (se 1 (by rfl) ⟨1355939, by rfl⟩ : syracuseStep 1807919 = 2711879) B2711879
theorem B1349855 : Blo 531801 1349855 := bstep (se 1 (by rfl) ⟨1012391, by rfl⟩ : syracuseStep 1349855 = 2024783) B2024783
theorem B2627977 : Blo 531801 2627977 := bstep (se 2 (by rfl) ⟨985491, by rfl⟩ : syracuseStep 2627977 = 1970983) B1970983
theorem B9771457 : Blo 531801 9771457 := bstep (se 2 (by rfl) ⟨3664296, by rfl⟩ : syracuseStep 9771457 = 7328593) B7328593
theorem B2693735 : Blo 531801 2693735 := bstep (se 1 (by rfl) ⟨2020301, by rfl⟩ : syracuseStep 2693735 = 4040603) B4040603
theorem B531871 : Blo 531801 531871 := bstep (se 1 (by rfl) ⟨398903, by rfl⟩ : syracuseStep 531871 = 797807) B797807
theorem B531903 : Blo 531801 531903 := bstep (se 1 (by rfl) ⟨398927, by rfl⟩ : syracuseStep 531903 = 797855) B797855
theorem B4857569 : Blo 531801 4857569 := bstep (se 2 (by rfl) ⟨1821588, by rfl⟩ : syracuseStep 4857569 = 3643177) B3643177
theorem B3416003 : Blo 531801 3416003 := bstep (se 1 (by rfl) ⟨2562002, by rfl⟩ : syracuseStep 3416003 = 5124005) B5124005
theorem B1351667 : Blo 531801 1351667 := bstep (se 1 (by rfl) ⟨1013750, by rfl⟩ : syracuseStep 1351667 = 2027501) B2027501
theorem B1515773 : Blo 531801 1515773 := bstep (se 3 (by rfl) ⟨284207, by rfl⟩ : syracuseStep 1515773 = 568415) B568415
theorem B598495 : Blo 531801 598495 := bstep (se 1 (by rfl) ⟨448871, by rfl⟩ : syracuseStep 598495 = 897743) B897743
theorem B533039 : Blo 531801 533039 := bstep (se 1 (by rfl) ⟨399779, by rfl⟩ : syracuseStep 533039 = 799559) B799559
theorem B1352335 : Blo 531801 1352335 := bstep (se 1 (by rfl) ⟨1014251, by rfl⟩ : syracuseStep 1352335 = 2028503) B2028503
theorem B533311 : Blo 531801 533311 := bstep (se 1 (by rfl) ⟨399983, by rfl⟩ : syracuseStep 533311 = 799967) B799967
theorem B2696003 : Blo 531801 2696003 := bstep (se 1 (by rfl) ⟨2022002, by rfl⟩ : syracuseStep 2696003 = 4044005) B4044005
theorem B533319 : Blo 531801 533319 := bstep (se 1 (by rfl) ⟨399989, by rfl⟩ : syracuseStep 533319 = 799979) B799979
theorem B533351 : Blo 531801 533351 := bstep (se 1 (by rfl) ⟨400013, by rfl⟩ : syracuseStep 533351 = 800027) B800027
theorem B533595 : Blo 531801 533595 := bstep (se 1 (by rfl) ⟨400196, by rfl⟩ : syracuseStep 533595 = 800393) B800393
theorem B533631 : Blo 531801 533631 := bstep (se 1 (by rfl) ⟨400223, by rfl⟩ : syracuseStep 533631 = 800447) B800447
theorem B599323 : Blo 531801 599323 := bstep (se 1 (by rfl) ⟨449492, by rfl⟩ : syracuseStep 599323 = 898985) B898985
theorem B7316891 : Blo 531801 7316891 := bstep (se 1 (by rfl) ⟨5487668, by rfl⟩ : syracuseStep 7316891 = 10975337) B10975337
theorem B1353307 : Blo 531801 1353307 := bstep (se 1 (by rfl) ⟨1014980, by rfl⟩ : syracuseStep 1353307 = 2029961) B2029961
theorem B534591 : Blo 531801 534591 := bstep (se 1 (by rfl) ⟨400943, by rfl⟩ : syracuseStep 534591 = 801887) B801887
theorem B52471961 : Blo 531801 52471961 := bstep (se 2 (by rfl) ⟨19676985, by rfl⟩ : syracuseStep 52471961 = 39353971) B39353971
theorem B600223 : Blo 531801 600223 := bstep (se 1 (by rfl) ⟨450167, by rfl⟩ : syracuseStep 600223 = 900335) B900335
theorem B534759 : Blo 531801 534759 := bstep (se 1 (by rfl) ⟨401069, by rfl⟩ : syracuseStep 534759 = 802139) B802139
theorem B6072569 : Blo 531801 6072569 := bstep (se 2 (by rfl) ⟨2277213, by rfl⟩ : syracuseStep 6072569 = 4554427) B4554427
theorem B534779 : Blo 531801 534779 := bstep (se 1 (by rfl) ⟨401084, by rfl⟩ : syracuseStep 534779 = 802169) B802169
theorem B8661613 : Blo 531801 8661613 := bstep (se 3 (by rfl) ⟨1624052, by rfl⟩ : syracuseStep 8661613 = 3248105) B3248105
theorem B535199 : Blo 531801 535199 := bstep (se 1 (by rfl) ⟨401399, by rfl⟩ : syracuseStep 535199 = 802799) B802799
theorem B535399 : Blo 531801 535399 := bstep (se 1 (by rfl) ⟨401549, by rfl⟩ : syracuseStep 535399 = 803099) B803099
theorem B2272157 : Blo 531801 2272157 := bstep (se 3 (by rfl) ⟨426029, by rfl⟩ : syracuseStep 2272157 = 852059) B852059
theorem B535643 : Blo 531801 535643 := bstep (se 1 (by rfl) ⟨401732, by rfl⟩ : syracuseStep 535643 = 803465) B803465
theorem B798191 : Blo 531801 798191 := bstep (se 1 (by rfl) ⟨598643, by rfl⟩ : syracuseStep 798191 = 1197287) B1197287
theorem B1519327 : Blo 531801 1519327 := bstep (se 1 (by rfl) ⟨1139495, by rfl⟩ : syracuseStep 1519327 = 2278991) B2278991
theorem B602203 : Blo 531801 602203 := bstep (se 1 (by rfl) ⟨451652, by rfl⟩ : syracuseStep 602203 = 903305) B903305
theorem B798911 : Blo 531801 798911 := bstep (se 1 (by rfl) ⟨599183, by rfl⟩ : syracuseStep 798911 = 1198367) B1198367
theorem B799145 : Blo 531801 799145 := bstep (se 2 (by rfl) ⟨299679, by rfl⟩ : syracuseStep 799145 = 599359) B599359
theorem B1356203 : Blo 531801 1356203 := bstep (se 1 (by rfl) ⟨1017152, by rfl⟩ : syracuseStep 1356203 = 2034305) B2034305
theorem B799391 : Blo 531801 799391 := bstep (se 1 (by rfl) ⟨599543, by rfl⟩ : syracuseStep 799391 = 1199087) B1199087
theorem B3420947 : Blo 531801 3420947 := bstep (se 1 (by rfl) ⟨2565710, by rfl⟩ : syracuseStep 3420947 = 5131421) B5131421
theorem B8434529 : Blo 531801 8434529 := bstep (se 2 (by rfl) ⟨3162948, by rfl⟩ : syracuseStep 8434529 = 6325897) B6325897
theorem B5124961 : Blo 531801 5124961 := bstep (se 2 (by rfl) ⟨1921860, by rfl⟩ : syracuseStep 5124961 = 3843721) B3843721
theorem B963425 : Blo 531801 963425 := bstep (se 2 (by rfl) ⟨361284, by rfl⟩ : syracuseStep 963425 = 722569) B722569
theorem B2732939 : Blo 531801 2732939 := bstep (se 1 (by rfl) ⟨2049704, by rfl⟩ : syracuseStep 2732939 = 4099409) B4099409
theorem B5485907 : Blo 531801 5485907 := bstep (se 1 (by rfl) ⟨4114430, by rfl⟩ : syracuseStep 5485907 = 8228861) B8228861
theorem B964327 : Blo 531801 964327 := bstep (se 1 (by rfl) ⟨723245, by rfl⟩ : syracuseStep 964327 = 1446491) B1446491
theorem B4437925 : Blo 531801 4437925 := bstep (se 4 (by rfl) ⟨416055, by rfl⟩ : syracuseStep 4437925 = 832111) B832111
theorem B4340087 : Blo 531801 4340087 := bstep (se 1 (by rfl) ⟨3255065, by rfl⟩ : syracuseStep 4340087 = 6510131) B6510131
theorem B4340411 : Blo 531801 4340411 := bstep (se 1 (by rfl) ⟨3255308, by rfl⟩ : syracuseStep 4340411 = 6510617) B6510617
theorem B8666671 : Blo 531801 8666671 := bstep (se 1 (by rfl) ⟨6500003, by rfl⟩ : syracuseStep 8666671 = 13000007) B13000007
theorem B802463 : Blo 531801 802463 := bstep (se 1 (by rfl) ⟨601847, by rfl⟩ : syracuseStep 802463 = 1203695) B1203695
theorem B7683751 : Blo 531801 7683751 := bstep (se 1 (by rfl) ⟨5762813, by rfl⟩ : syracuseStep 7683751 = 11525627) B11525627
theorem B900895 : Blo 531801 900895 := bstep (se 1 (by rfl) ⟨675671, by rfl⟩ : syracuseStep 900895 = 1351343) B1351343
theorem B2703455 : Blo 531801 2703455 := bstep (se 1 (by rfl) ⟨2027591, by rfl⟩ : syracuseStep 2703455 = 4055183) B4055183
theorem B803039 : Blo 531801 803039 := bstep (se 1 (by rfl) ⟨602279, by rfl⟩ : syracuseStep 803039 = 1204559) B1204559
theorem B6177059 : Blo 531801 6177059 := bstep (se 1 (by rfl) ⟨4632794, by rfl⟩ : syracuseStep 6177059 = 9265589) B9265589
theorem B901631 : Blo 531801 901631 := bstep (se 1 (by rfl) ⟨676223, by rfl⟩ : syracuseStep 901631 = 1352447) B1352447
theorem B803687 : Blo 531801 803687 := bstep (se 1 (by rfl) ⟨602765, by rfl⟩ : syracuseStep 803687 = 1205531) B1205531
theorem B2573245 : Blo 531801 2573245 := bstep (se 3 (by rfl) ⟨482483, by rfl⟩ : syracuseStep 2573245 = 964967) B964967
theorem B1197035 : Blo 531801 1197035 := bstep (se 1 (by rfl) ⟨897776, by rfl⟩ : syracuseStep 1197035 = 1795553) B1795553
theorem B3032275 : Blo 531801 3032275 := bstep (se 1 (by rfl) ⟨2274206, by rfl⟩ : syracuseStep 3032275 = 4548413) B4548413
theorem B2573689 : Blo 531801 2573689 := bstep (se 2 (by rfl) ⟨965133, by rfl⟩ : syracuseStep 2573689 = 1930267) B1930267
theorem B21972653 : Blo 531801 21972653 := bstep (se 3 (by rfl) ⟨4119872, by rfl⟩ : syracuseStep 21972653 = 8239745) B8239745
theorem B673535 : Blo 531801 673535 := bstep (se 1 (by rfl) ⟨505151, by rfl⟩ : syracuseStep 673535 = 1010303) B1010303
theorem B2705561 : Blo 531801 2705561 := bstep (se 2 (by rfl) ⟨1014585, by rfl⟩ : syracuseStep 2705561 = 2029171) B2029171
theorem B1919209 : Blo 531801 1919209 := bstep (se 2 (by rfl) ⟨719703, by rfl⟩ : syracuseStep 1919209 = 1439407) B1439407
theorem B1198313 : Blo 531801 1198313 := bstep (se 2 (by rfl) ⟨449367, by rfl⟩ : syracuseStep 1198313 = 898735) B898735
theorem B1198331 : Blo 531801 1198331 := bstep (se 1 (by rfl) ⟨898748, by rfl⟩ : syracuseStep 1198331 = 1797497) B1797497
theorem B1198799 : Blo 531801 1198799 := bstep (se 1 (by rfl) ⟨899099, by rfl⟩ : syracuseStep 1198799 = 1798199) B1798199
theorem B675307 : Blo 531801 675307 := bstep (se 1 (by rfl) ⟨506480, by rfl⟩ : syracuseStep 675307 = 1012961) B1012961
theorem B3853871 : Blo 531801 3853871 := bstep (se 1 (by rfl) ⟨2890403, by rfl⟩ : syracuseStep 3853871 = 5780807) B5780807
theorem B1232623 : Blo 531801 1232623 := bstep (se 1 (by rfl) ⟨924467, by rfl⟩ : syracuseStep 1232623 = 1848935) B1848935
theorem B1364527 : Blo 531801 1364527 := bstep (se 1 (by rfl) ⟨1023395, by rfl⟩ : syracuseStep 1364527 = 2046791) B2046791
theorem B676603 : Blo 531801 676603 := bstep (se 1 (by rfl) ⟨507452, by rfl⟩ : syracuseStep 676603 = 1014905) B1014905
theorem B2085659 : Blo 531801 2085659 := bstep (se 1 (by rfl) ⟨1564244, by rfl⟩ : syracuseStep 2085659 = 3128489) B3128489
theorem B32789495 : Blo 531801 32789495 := bstep (se 1 (by rfl) ⟨24592121, by rfl⟩ : syracuseStep 32789495 = 49184243) B49184243
theorem B2708477 : Blo 531801 2708477 := bstep (se 3 (by rfl) ⟨507839, by rfl⟩ : syracuseStep 2708477 = 1015679) B1015679
theorem B3429611 : Blo 531801 3429611 := bstep (se 1 (by rfl) ⟨2572208, by rfl⟩ : syracuseStep 3429611 = 5144417) B5144417
theorem B1201823 : Blo 531801 1201823 := bstep (se 1 (by rfl) ⟨901367, by rfl⟩ : syracuseStep 1201823 = 1802735) B1802735
theorem B678071 : Blo 531801 678071 := bstep (se 1 (by rfl) ⟨508553, by rfl⟩ : syracuseStep 678071 = 1017107) B1017107
theorem B3070973 : Blo 531801 3070973 := bstep (se 3 (by rfl) ⟨575807, by rfl⟩ : syracuseStep 3070973 = 1151615) B1151615
theorem B1203227 : Blo 531801 1203227 := bstep (se 1 (by rfl) ⟨902420, by rfl⟩ : syracuseStep 1203227 = 1804841) B1804841
theorem B6839639 : Blo 531801 6839639 := bstep (se 1 (by rfl) ⟨5129729, by rfl⟩ : syracuseStep 6839639 = 10259459) B10259459
theorem B1204127 : Blo 531801 1204127 := bstep (se 1 (by rfl) ⟨903095, by rfl⟩ : syracuseStep 1204127 = 1806191) B1806191
theorem B6087149 : Blo 531801 6087149 := bstep (se 3 (by rfl) ⟨1141340, by rfl⟩ : syracuseStep 6087149 = 2282681) B2282681
theorem B2744819 : Blo 531801 2744819 := bstep (se 1 (by rfl) ⟨2058614, by rfl⟩ : syracuseStep 2744819 = 4117229) B4117229
theorem B1204793 : Blo 531801 1204793 := bstep (se 2 (by rfl) ⟨451797, by rfl⟩ : syracuseStep 1204793 = 903595) B903595
theorem B1205063 : Blo 531801 1205063 := bstep (se 1 (by rfl) ⟨903797, by rfl⟩ : syracuseStep 1205063 = 1807595) B1807595
theorem B179627057 : Blo 531801 179627057 := bstep (se 2 (by rfl) ⟨67360146, by rfl⟩ : syracuseStep 179627057 = 134720293) B134720293
theorem B6350177 : Blo 531801 6350177 := bstep (se 2 (by rfl) ⟨2381316, by rfl⟩ : syracuseStep 6350177 = 4762633) B4762633
theorem B3041023 : Blo 531801 3041023 := bstep (se 1 (by rfl) ⟨2280767, by rfl⟩ : syracuseStep 3041023 = 4561535) B4561535
theorem B2288047 : Blo 531801 2288047 := bstep (se 1 (by rfl) ⟨1716035, by rfl⟩ : syracuseStep 2288047 = 3432071) B3432071
theorem B3238643 : Blo 531801 3238643 := bstep (se 1 (by rfl) ⟨2428982, by rfl⟩ : syracuseStep 3238643 = 4857965) B4857965
theorem B2026529 : Blo 531801 2026529 := bstep (se 2 (by rfl) ⟨759948, by rfl⟩ : syracuseStep 2026529 = 1519897) B1519897
theorem B1142495 : Blo 531801 1142495 := bstep (se 1 (by rfl) ⟨856871, by rfl⟩ : syracuseStep 1142495 = 1713743) B1713743
theorem B12971987 : Blo 531801 12971987 := bstep (se 1 (by rfl) ⟨9728990, by rfl⟩ : syracuseStep 12971987 = 19457981) B19457981
theorem B1798523 : Blo 531801 1798523 := bstep (se 1 (by rfl) ⟨1348892, by rfl⟩ : syracuseStep 1798523 = 2697785) B2697785
theorem B25915949 : Blo 531801 25915949 := bstep (se 3 (by rfl) ⟨4859240, by rfl⟩ : syracuseStep 25915949 = 9718481) B9718481
theorem B1144135 : Blo 531801 1144135 := bstep (se 1 (by rfl) ⟨858101, by rfl⟩ : syracuseStep 1144135 = 1716203) B1716203
theorem B1800467 : Blo 531801 1800467 := bstep (se 1 (by rfl) ⟨1350350, by rfl⟩ : syracuseStep 1800467 = 2700701) B2700701
theorem B5274953 : Blo 531801 5274953 := bstep (se 2 (by rfl) ⟨1978107, by rfl⟩ : syracuseStep 5274953 = 3956215) B3956215
theorem B1277927 : Blo 531801 1277927 := bstep (se 1 (by rfl) ⟨958445, by rfl⟩ : syracuseStep 1277927 = 1916891) B1916891
theorem B1802303 : Blo 531801 1802303 := bstep (se 1 (by rfl) ⟨1351727, by rfl⟩ : syracuseStep 1802303 = 2703455) B2703455
theorem B2884175 : Blo 531801 2884175 := bstep (se 1 (by rfl) ⟨2163131, by rfl⟩ : syracuseStep 2884175 = 4326263) B4326263
theorem B1803113 : Blo 531801 1803113 := bstep (se 2 (by rfl) ⟨676167, by rfl⟩ : syracuseStep 1803113 = 1352335) B1352335
theorem B14648435 : Blo 531801 14648435 := bstep (se 1 (by rfl) ⟨10986326, by rfl⟩ : syracuseStep 14648435 = 21972653) B21972653
theorem B1803707 : Blo 531801 1803707 := bstep (se 1 (by rfl) ⟨1352780, by rfl⟩ : syracuseStep 1803707 = 2705561) B2705561
theorem B3474895 : Blo 531801 3474895 := bstep (se 1 (by rfl) ⟨2606171, by rfl⟩ : syracuseStep 3474895 = 5212343) B5212343
theorem B2885543 : Blo 531801 2885543 := bstep (se 1 (by rfl) ⟨2164157, by rfl⟩ : syracuseStep 2885543 = 4328315) B4328315
theorem B1804409 : Blo 531801 1804409 := bstep (se 2 (by rfl) ⟨676653, by rfl⟩ : syracuseStep 1804409 = 1353307) B1353307
theorem B2558945 : Blo 531801 2558945 := bstep (se 2 (by rfl) ⟨959604, by rfl⟩ : syracuseStep 2558945 = 1919209) B1919209
theorem B3050729 : Blo 531801 3050729 := bstep (se 2 (by rfl) ⟨1144023, by rfl⟩ : syracuseStep 3050729 = 2288047) B2288047
theorem B1805651 : Blo 531801 1805651 := bstep (se 1 (by rfl) ⟨1354238, by rfl⟩ : syracuseStep 1805651 = 2708477) B2708477
theorem B1707425 : Blo 531801 1707425 := bstep (se 2 (by rfl) ⟨640284, by rfl⟩ : syracuseStep 1707425 = 1280569) B1280569
theorem B4559759 : Blo 531801 4559759 := bstep (se 1 (by rfl) ⟨3419819, by rfl⟩ : syracuseStep 4559759 = 6839639) B6839639
theorem B1643497 : Blo 531801 1643497 := bstep (se 2 (by rfl) ⟨616311, by rfl⟩ : syracuseStep 1643497 = 1232623) B1232623
theorem B1808189 : Blo 531801 1808189 := bstep (se 3 (by rfl) ⟨339035, by rfl⟩ : syracuseStep 1808189 = 678071) B678071
theorem B1514771 : Blo 531801 1514771 := bstep (se 1 (by rfl) ⟨1136078, by rfl⟩ : syracuseStep 1514771 = 2272157) B2272157
theorem B1351019 : Blo 531801 1351019 := bstep (se 1 (by rfl) ⟨1013264, by rfl⟩ : syracuseStep 1351019 = 2026529) B2026529
theorem B1285769 : Blo 531801 1285769 := bstep (se 2 (by rfl) ⟨482163, by rfl⟩ : syracuseStep 1285769 = 964327) B964327
theorem B532127 : Blo 531801 532127 := bstep (se 1 (by rfl) ⟨399095, by rfl⟩ : syracuseStep 532127 = 798191) B798191
theorem B761663 : Blo 531801 761663 := bstep (se 1 (by rfl) ⟨571247, by rfl⟩ : syracuseStep 761663 = 1142495) B1142495
theorem B532607 : Blo 531801 532607 := bstep (se 1 (by rfl) ⟨399455, by rfl⟩ : syracuseStep 532607 = 798911) B798911
theorem B532763 : Blo 531801 532763 := bstep (se 1 (by rfl) ⟨399572, by rfl⟩ : syracuseStep 532763 = 799145) B799145
theorem B17277299 : Blo 531801 17277299 := bstep (se 1 (by rfl) ⟨12957974, by rfl⟩ : syracuseStep 17277299 = 25915949) B25915949
theorem B532927 : Blo 531801 532927 := bstep (se 1 (by rfl) ⟨399695, by rfl⟩ : syracuseStep 532927 = 799391) B799391
theorem B2893391 : Blo 531801 2893391 := bstep (se 1 (by rfl) ⟨2170043, by rfl⟩ : syracuseStep 2893391 = 4340087) B4340087
theorem B2893607 : Blo 531801 2893607 := bstep (se 1 (by rfl) ⟨2170205, by rfl⟩ : syracuseStep 2893607 = 4340411) B4340411
theorem B23668933 : Blo 531801 23668933 := bstep (se 4 (by rfl) ⟨2218962, by rfl⟩ : syracuseStep 23668933 = 4437925) B4437925
theorem B3516635 : Blo 531801 3516635 := bstep (se 1 (by rfl) ⟨2637476, by rfl⟩ : syracuseStep 3516635 = 5274953) B5274953
theorem B534975 : Blo 531801 534975 := bstep (se 1 (by rfl) ⟨401231, by rfl⟩ : syracuseStep 534975 = 802463) B802463
theorem B535359 : Blo 531801 535359 := bstep (se 1 (by rfl) ⟨401519, by rfl⟩ : syracuseStep 535359 = 803039) B803039
theorem B601087 : Blo 531801 601087 := bstep (se 1 (by rfl) ⟨450815, by rfl⟩ : syracuseStep 601087 = 901631) B901631
theorem B535791 : Blo 531801 535791 := bstep (se 1 (by rfl) ⟨401843, by rfl⟩ : syracuseStep 535791 = 803687) B803687
theorem B797993 : Blo 531801 797993 := bstep (se 2 (by rfl) ⟨299247, by rfl⟩ : syracuseStep 797993 = 598495) B598495
theorem B798023 : Blo 531801 798023 := bstep (se 1 (by rfl) ⟨598517, by rfl⟩ : syracuseStep 798023 = 1197035) B1197035
theorem B4042061 : Blo 531801 4042061 := bstep (se 3 (by rfl) ⟨757886, by rfl⟩ : syracuseStep 4042061 = 1515773) B1515773
theorem B3256375 : Blo 531801 3256375 := bstep (se 1 (by rfl) ⟨2442281, by rfl⟩ : syracuseStep 3256375 = 4884563) B4884563
theorem B798875 : Blo 531801 798875 := bstep (se 1 (by rfl) ⟨599156, by rfl⟩ : syracuseStep 798875 = 1198313) B1198313
theorem B798887 : Blo 531801 798887 := bstep (se 1 (by rfl) ⟨599165, by rfl⟩ : syracuseStep 798887 = 1198331) B1198331
theorem B4043033 : Blo 531801 4043033 := bstep (se 2 (by rfl) ⟨1516137, by rfl⟩ : syracuseStep 4043033 = 3032275) B3032275
theorem B799097 : Blo 531801 799097 := bstep (se 2 (by rfl) ⟨299661, by rfl⟩ : syracuseStep 799097 = 599323) B599323
theorem B799199 : Blo 531801 799199 := bstep (se 1 (by rfl) ⟨599399, by rfl⟩ : syracuseStep 799199 = 1198799) B1198799
theorem B2569133 : Blo 531801 2569133 := bstep (se 3 (by rfl) ⟨481712, by rfl⟩ : syracuseStep 2569133 = 963425) B963425
theorem B2569247 : Blo 531801 2569247 := bstep (se 1 (by rfl) ⟨1926935, by rfl⟩ : syracuseStep 2569247 = 3853871) B3853871
theorem B898303 : Blo 531801 898303 := bstep (se 1 (by rfl) ⟨673727, by rfl⟩ : syracuseStep 898303 = 1347455) B1347455
theorem B87438653 : Blo 531801 87438653 := bstep (se 3 (by rfl) ⟨16394747, by rfl⟩ : syracuseStep 87438653 = 32789495) B32789495
theorem B800297 : Blo 531801 800297 := bstep (se 2 (by rfl) ⟨300111, by rfl⟩ : syracuseStep 800297 = 600223) B600223
theorem B1390439 : Blo 531801 1390439 := bstep (se 1 (by rfl) ⟨1042829, by rfl⟩ : syracuseStep 1390439 = 2085659) B2085659
theorem B11548817 : Blo 531801 11548817 := bstep (se 2 (by rfl) ⟨4330806, by rfl⟩ : syracuseStep 11548817 = 8661613) B8661613
theorem B14629085 : Blo 531801 14629085 := bstep (se 3 (by rfl) ⟨2742953, by rfl⟩ : syracuseStep 14629085 = 5485907) B5485907
theorem B801215 : Blo 531801 801215 := bstep (se 1 (by rfl) ⟨600911, by rfl⟩ : syracuseStep 801215 = 1201823) B1201823
theorem B899903 : Blo 531801 899903 := bstep (se 1 (by rfl) ⟨674927, by rfl⟩ : syracuseStep 899903 = 1349855) B1349855
theorem B900409 : Blo 531801 900409 := bstep (se 2 (by rfl) ⟨337653, by rfl⟩ : syracuseStep 900409 = 675307) B675307
theorem B2047315 : Blo 531801 2047315 := bstep (se 1 (by rfl) ⟨1535486, by rfl⟩ : syracuseStep 2047315 = 3070973) B3070973
theorem B802151 : Blo 531801 802151 := bstep (se 1 (by rfl) ⟨601613, by rfl⟩ : syracuseStep 802151 = 1203227) B1203227
theorem B802751 : Blo 531801 802751 := bstep (se 1 (by rfl) ⟨602063, by rfl⟩ : syracuseStep 802751 = 1204127) B1204127
theorem B2277335 : Blo 531801 2277335 := bstep (se 1 (by rfl) ⟨1708001, by rfl⟩ : syracuseStep 2277335 = 3416003) B3416003
theorem B901111 : Blo 531801 901111 := bstep (se 1 (by rfl) ⟨675833, by rfl⟩ : syracuseStep 901111 = 1351667) B1351667
theorem B802937 : Blo 531801 802937 := bstep (se 2 (by rfl) ⟨301101, by rfl⟩ : syracuseStep 802937 = 602203) B602203
theorem B803195 : Blo 531801 803195 := bstep (se 1 (by rfl) ⟨602396, by rfl⟩ : syracuseStep 803195 = 1204793) B1204793
theorem B803375 : Blo 531801 803375 := bstep (se 1 (by rfl) ⟨602531, by rfl⟩ : syracuseStep 803375 = 1205063) B1205063
theorem B119751371 : Blo 531801 119751371 := bstep (se 1 (by rfl) ⟨89813528, by rfl⟩ : syracuseStep 119751371 = 179627057) B179627057
theorem B1819369 : Blo 531801 1819369 := bstep (se 2 (by rfl) ⟨682263, by rfl⟩ : syracuseStep 1819369 = 1364527) B1364527
theorem B902137 : Blo 531801 902137 := bstep (se 2 (by rfl) ⟨338301, by rfl⟩ : syracuseStep 902137 = 676603) B676603
theorem B6833281 : Blo 531801 6833281 := bstep (se 2 (by rfl) ⟨2562480, by rfl⟩ : syracuseStep 6833281 = 5124961) B5124961
theorem B34981307 : Blo 531801 34981307 := bstep (se 1 (by rfl) ⟨26235980, by rfl⟩ : syracuseStep 34981307 = 52471961) B52471961
theorem B4048379 : Blo 531801 4048379 := bstep (se 1 (by rfl) ⟨3036284, by rfl⟩ : syracuseStep 4048379 = 6072569) B6072569
theorem B1525513 : Blo 531801 1525513 := bstep (se 2 (by rfl) ⟨572067, by rfl⟩ : syracuseStep 1525513 = 1144135) B1144135
theorem B8636381 : Blo 531801 8636381 := bstep (se 3 (by rfl) ⟨1619321, by rfl⟩ : syracuseStep 8636381 = 3238643) B3238643
theorem B1199015 : Blo 531801 1199015 := bstep (se 1 (by rfl) ⟨899261, by rfl⟩ : syracuseStep 1199015 = 1798523) B1798523
theorem B904135 : Blo 531801 904135 := bstep (se 1 (by rfl) ⟨678101, by rfl⟩ : syracuseStep 904135 = 1356203) B1356203
theorem B2280631 : Blo 531801 2280631 := bstep (se 1 (by rfl) ⟨1710473, by rfl⟩ : syracuseStep 2280631 = 3420947) B3420947
theorem B5623019 : Blo 531801 5623019 := bstep (se 1 (by rfl) ⟨4217264, by rfl⟩ : syracuseStep 5623019 = 8434529) B8434529
theorem B13028609 : Blo 531801 13028609 := bstep (se 2 (by rfl) ⟨4885728, by rfl⟩ : syracuseStep 13028609 = 9771457) B9771457
theorem B1821959 : Blo 531801 1821959 := bstep (se 1 (by rfl) ⟨1366469, by rfl⟩ : syracuseStep 1821959 = 2732939) B2732939
theorem B1200311 : Blo 531801 1200311 := bstep (se 1 (by rfl) ⟨900233, by rfl⟩ : syracuseStep 1200311 = 1800467) B1800467
theorem B11555561 : Blo 531801 11555561 := bstep (se 2 (by rfl) ⟨4333335, by rfl⟩ : syracuseStep 11555561 = 8666671) B8666671
theorem B10245001 : Blo 531801 10245001 := bstep (se 2 (by rfl) ⟨3841875, by rfl⟩ : syracuseStep 10245001 = 7683751) B7683751
theorem B1201193 : Blo 531801 1201193 := bstep (se 2 (by rfl) ⟨450447, by rfl⟩ : syracuseStep 1201193 = 900895) B900895
theorem B4118039 : Blo 531801 4118039 := bstep (se 1 (by rfl) ⟨3088529, by rfl⟩ : syracuseStep 4118039 = 6177059) B6177059
theorem B1202111 : Blo 531801 1202111 := bstep (se 1 (by rfl) ⟨901583, by rfl⟩ : syracuseStep 1202111 = 1803167) B1803167
theorem B19421471 : Blo 531801 19421471 := bstep (se 1 (by rfl) ⟨14566103, by rfl⟩ : syracuseStep 19421471 = 29132207) B29132207
theorem B1202687 : Blo 531801 1202687 := bstep (se 1 (by rfl) ⟨902015, by rfl⟩ : syracuseStep 1202687 = 1804031) B1804031
theorem B2710097 : Blo 531801 2710097 := bstep (se 2 (by rfl) ⟨1016286, by rfl⟩ : syracuseStep 2710097 = 2032573) B2032573
theorem B3430993 : Blo 531801 3430993 := bstep (se 2 (by rfl) ⟨1286622, by rfl⟩ : syracuseStep 3430993 = 2573245) B2573245
theorem B3431585 : Blo 531801 3431585 := bstep (se 2 (by rfl) ⟨1286844, by rfl⟩ : syracuseStep 3431585 = 2573689) B2573689
theorem B4054697 : Blo 531801 4054697 := bstep (se 2 (by rfl) ⟨1520511, by rfl⟩ : syracuseStep 4054697 = 3041023) B3041023
theorem B2286407 : Blo 531801 2286407 := bstep (se 1 (by rfl) ⟨1714805, by rfl⟩ : syracuseStep 2286407 = 3429611) B3429611
theorem B3040091 : Blo 531801 3040091 := bstep (se 1 (by rfl) ⟨2280068, by rfl⟩ : syracuseStep 3040091 = 4560137) B4560137
theorem B16933805 : Blo 531801 16933805 := bstep (se 3 (by rfl) ⟨3175088, by rfl⟩ : syracuseStep 16933805 = 6350177) B6350177
theorem B1205279 : Blo 531801 1205279 := bstep (se 1 (by rfl) ⟨903959, by rfl⟩ : syracuseStep 1205279 = 1807919) B1807919
theorem B1795823 : Blo 531801 1795823 := bstep (se 1 (by rfl) ⟨1346867, by rfl⟩ : syracuseStep 1795823 = 2693735) B2693735
theorem B1796093 : Blo 531801 1796093 := bstep (se 3 (by rfl) ⟨336767, by rfl⟩ : syracuseStep 1796093 = 673535) B673535
theorem B2025769 : Blo 531801 2025769 := bstep (se 2 (by rfl) ⟨759663, by rfl⟩ : syracuseStep 2025769 = 1519327) B1519327
theorem B3238379 : Blo 531801 3238379 := bstep (se 1 (by rfl) ⟨2428784, by rfl⟩ : syracuseStep 3238379 = 4857569) B4857569
theorem B4058099 : Blo 531801 4058099 := bstep (se 1 (by rfl) ⟨3043574, by rfl⟩ : syracuseStep 4058099 = 6087149) B6087149
theorem B1829879 : Blo 531801 1829879 := bstep (se 1 (by rfl) ⟨1372409, by rfl⟩ : syracuseStep 1829879 = 2744819) B2744819
theorem B1797281 : Blo 531801 1797281 := bstep (se 2 (by rfl) ⟨673980, by rfl⟩ : syracuseStep 1797281 = 1347961) B1347961
theorem B1797335 : Blo 531801 1797335 := bstep (se 1 (by rfl) ⟨1348001, by rfl⟩ : syracuseStep 1797335 = 2696003) B2696003
theorem B4877927 : Blo 531801 4877927 := bstep (se 1 (by rfl) ⟨3658445, by rfl⟩ : syracuseStep 4877927 = 7316891) B7316891
theorem B1011305 : Blo 531801 1011305 := bstep (se 2 (by rfl) ⟨379239, by rfl⟩ : syracuseStep 1011305 = 758479) B758479
theorem B8647991 : Blo 531801 8647991 := bstep (se 1 (by rfl) ⟨6485993, by rfl⟩ : syracuseStep 8647991 = 12971987) B12971987
theorem B3503969 : Blo 531801 3503969 := bstep (se 2 (by rfl) ⟨1313988, by rfl⟩ : syracuseStep 3503969 = 2627977) B2627977
theorem B851951 : Blo 531801 851951 := bstep (se 1 (by rfl) ⟨638963, by rfl⟩ : syracuseStep 851951 = 1277927) B1277927
theorem B9765623 : Blo 531801 9765623 := bstep (se 1 (by rfl) ⟨7324217, by rfl⟩ : syracuseStep 9765623 = 14648435) B14648435
theorem B2425825 : Blo 531801 2425825 := bstep (se 2 (by rfl) ⟨909684, by rfl⟩ : syracuseStep 2425825 = 1819369) B1819369
theorem B9111041 : Blo 531801 9111041 := bstep (se 2 (by rfl) ⟨3416640, by rfl⟩ : syracuseStep 9111041 = 6833281) B6833281
theorem B1705963 : Blo 531801 1705963 := bstep (se 1 (by rfl) ⟨1279472, by rfl⟩ : syracuseStep 1705963 = 2558945) B2558945
theorem B2033819 : Blo 531801 2033819 := bstep (se 1 (by rfl) ⟨1525364, by rfl⟩ : syracuseStep 2033819 = 3050729) B3050729
theorem B8685739 : Blo 531801 8685739 := bstep (se 1 (by rfl) ⟨6514304, by rfl⟩ : syracuseStep 8685739 = 13028609) B13028609
theorem B1214639 : Blo 531801 1214639 := bstep (se 1 (by rfl) ⟨910979, by rfl⟩ : syracuseStep 1214639 = 1821959) B1821959
theorem B2034017 : Blo 531801 2034017 := bstep (se 2 (by rfl) ⟨762756, by rfl⟩ : syracuseStep 2034017 = 1525513) B1525513
theorem B31558577 : Blo 531801 31558577 := bstep (se 2 (by rfl) ⟨11834466, by rfl⟩ : syracuseStep 31558577 = 23668933) B23668933
theorem B7703707 : Blo 531801 7703707 := bstep (se 1 (by rfl) ⟨5777780, by rfl⟩ : syracuseStep 7703707 = 11555561) B11555561
theorem B1806731 : Blo 531801 1806731 := bstep (se 1 (by rfl) ⟨1355048, by rfl⟩ : syracuseStep 1806731 = 2710097) B2710097
theorem B857179 : Blo 531801 857179 := bstep (se 1 (by rfl) ⟨642884, by rfl⟩ : syracuseStep 857179 = 1285769) B1285769
theorem B1219919 : Blo 531801 1219919 := bstep (se 1 (by rfl) ⟨914939, by rfl⟩ : syracuseStep 1219919 = 1829879) B1829879
theorem B531995 : Blo 531801 531995 := bstep (se 1 (by rfl) ⟨398996, by rfl⟩ : syracuseStep 531995 = 797993) B797993
theorem B532015 : Blo 531801 532015 := bstep (se 1 (by rfl) ⟨399011, by rfl⟩ : syracuseStep 532015 = 798023) B798023
theorem B2694707 : Blo 531801 2694707 := bstep (se 1 (by rfl) ⟨2021030, by rfl⟩ : syracuseStep 2694707 = 4042061) B4042061
theorem B3251951 : Blo 531801 3251951 := bstep (se 1 (by rfl) ⟨2438963, by rfl⟩ : syracuseStep 3251951 = 4877927) B4877927
theorem B532583 : Blo 531801 532583 := bstep (se 1 (by rfl) ⟨399437, by rfl⟩ : syracuseStep 532583 = 798875) B798875
theorem B532591 : Blo 531801 532591 := bstep (se 1 (by rfl) ⟨399443, by rfl⟩ : syracuseStep 532591 = 798887) B798887
theorem B2695355 : Blo 531801 2695355 := bstep (se 1 (by rfl) ⟨2021516, by rfl⟩ : syracuseStep 2695355 = 4043033) B4043033
theorem B532731 : Blo 531801 532731 := bstep (se 1 (by rfl) ⟨399548, by rfl⟩ : syracuseStep 532731 = 799097) B799097
theorem B532799 : Blo 531801 532799 := bstep (se 1 (by rfl) ⟨399599, by rfl⟩ : syracuseStep 532799 = 799199) B799199
theorem B1712755 : Blo 531801 1712755 := bstep (se 1 (by rfl) ⟨1284566, by rfl⟩ : syracuseStep 1712755 = 2569133) B2569133
theorem B1712831 : Blo 531801 1712831 := bstep (se 1 (by rfl) ⟨1284623, by rfl⟩ : syracuseStep 1712831 = 2569247) B2569247
theorem B533531 : Blo 531801 533531 := bstep (se 1 (by rfl) ⟨400148, by rfl⟩ : syracuseStep 533531 = 800297) B800297
theorem B2335979 : Blo 531801 2335979 := bstep (se 1 (by rfl) ⟨1751984, by rfl⟩ : syracuseStep 2335979 = 3503969) B3503969
theorem B926959 : Blo 531801 926959 := bstep (se 1 (by rfl) ⟨695219, by rfl⟩ : syracuseStep 926959 = 1390439) B1390439
theorem B2696813 : Blo 531801 2696813 := bstep (se 3 (by rfl) ⟨505652, by rfl⟩ : syracuseStep 2696813 = 1011305) B1011305
theorem B534143 : Blo 531801 534143 := bstep (se 1 (by rfl) ⟨400607, by rfl⟩ : syracuseStep 534143 = 801215) B801215
theorem B2729753 : Blo 531801 2729753 := bstep (se 2 (by rfl) ⟨1023657, by rfl⟩ : syracuseStep 2729753 = 2047315) B2047315
theorem B599935 : Blo 531801 599935 := bstep (se 1 (by rfl) ⟨449951, by rfl⟩ : syracuseStep 599935 = 899903) B899903
theorem B534767 : Blo 531801 534767 := bstep (se 1 (by rfl) ⟨401075, by rfl⟩ : syracuseStep 534767 = 802151) B802151
theorem B535167 : Blo 531801 535167 := bstep (se 1 (by rfl) ⟨401375, by rfl⟩ : syracuseStep 535167 = 802751) B802751
theorem B1518223 : Blo 531801 1518223 := bstep (se 1 (by rfl) ⟨1138667, by rfl⟩ : syracuseStep 1518223 = 2277335) B2277335
theorem B567967 : Blo 531801 567967 := bstep (se 1 (by rfl) ⟨425975, by rfl⟩ : syracuseStep 567967 = 851951) B851951
theorem B535291 : Blo 531801 535291 := bstep (se 1 (by rfl) ⟨401468, by rfl⟩ : syracuseStep 535291 = 802937) B802937
theorem B535463 : Blo 531801 535463 := bstep (se 1 (by rfl) ⟨401597, by rfl⟩ : syracuseStep 535463 = 803195) B803195
theorem B535583 : Blo 531801 535583 := bstep (se 1 (by rfl) ⟨401687, by rfl⟩ : syracuseStep 535583 = 803375) B803375
theorem B79834247 : Blo 531801 79834247 := bstep (se 1 (by rfl) ⟨59875685, by rfl⟩ : syracuseStep 79834247 = 119751371) B119751371
theorem B2698919 : Blo 531801 2698919 := bstep (se 1 (by rfl) ⟨2024189, by rfl⟩ : syracuseStep 2698919 = 4048379) B4048379
theorem B4633193 : Blo 531801 4633193 := bstep (se 2 (by rfl) ⟨1737447, by rfl⟩ : syracuseStep 4633193 = 3474895) B3474895
theorem B799343 : Blo 531801 799343 := bstep (se 1 (by rfl) ⟨599507, by rfl⟩ : syracuseStep 799343 = 1199015) B1199015
theorem B3748679 : Blo 531801 3748679 := bstep (se 1 (by rfl) ⟨2811509, by rfl⟩ : syracuseStep 3748679 = 5623019) B5623019
theorem B800207 : Blo 531801 800207 := bstep (se 1 (by rfl) ⟨600155, by rfl⟩ : syracuseStep 800207 = 1200311) B1200311
theorem B2701025 : Blo 531801 2701025 := bstep (se 2 (by rfl) ⟨1012884, by rfl⟩ : syracuseStep 2701025 = 2025769) B2025769
theorem B800795 : Blo 531801 800795 := bstep (se 1 (by rfl) ⟨600596, by rfl⟩ : syracuseStep 800795 = 1201193) B1201193
theorem B801407 : Blo 531801 801407 := bstep (se 1 (by rfl) ⟨601055, by rfl⟩ : syracuseStep 801407 = 1202111) B1202111
theorem B801449 : Blo 531801 801449 := bstep (se 2 (by rfl) ⟨300543, by rfl⟩ : syracuseStep 801449 = 601087) B601087
theorem B801791 : Blo 531801 801791 := bstep (se 1 (by rfl) ⟨601343, by rfl⟩ : syracuseStep 801791 = 1202687) B1202687
theorem B900679 : Blo 531801 900679 := bstep (se 1 (by rfl) ⟨675509, by rfl⟩ : syracuseStep 900679 = 1351019) B1351019
theorem B2703131 : Blo 531801 2703131 := bstep (se 1 (by rfl) ⟨2027348, by rfl⟩ : syracuseStep 2703131 = 4054697) B4054697
theorem B8765317 : Blo 531801 8765317 := bstep (se 4 (by rfl) ⟨821748, by rfl⟩ : syracuseStep 8765317 = 1643497) B1643497
theorem B4341833 : Blo 531801 4341833 := bstep (se 2 (by rfl) ⟨1628187, by rfl⟩ : syracuseStep 4341833 = 3256375) B3256375
theorem B11518199 : Blo 531801 11518199 := bstep (se 1 (by rfl) ⟨8638649, by rfl⟩ : syracuseStep 11518199 = 17277299) B17277299
theorem B1524271 : Blo 531801 1524271 := bstep (se 1 (by rfl) ⟨1143203, by rfl⟩ : syracuseStep 1524271 = 2286407) B2286407
theorem B11289203 : Blo 531801 11289203 := bstep (se 1 (by rfl) ⟨8466902, by rfl⟩ : syracuseStep 11289203 = 16933805) B16933805
theorem B803519 : Blo 531801 803519 := bstep (se 1 (by rfl) ⟨602639, by rfl⟩ : syracuseStep 803519 = 1205279) B1205279
theorem B51790589 : Blo 531801 51790589 := bstep (se 3 (by rfl) ⟨9710735, by rfl⟩ : syracuseStep 51790589 = 19421471) B19421471
theorem B1197215 : Blo 531801 1197215 := bstep (se 1 (by rfl) ⟨897911, by rfl⟩ : syracuseStep 1197215 = 1795823) B1795823
theorem B1197395 : Blo 531801 1197395 := bstep (se 1 (by rfl) ⟨898046, by rfl⟩ : syracuseStep 1197395 = 1796093) B1796093
theorem B2344423 : Blo 531801 2344423 := bstep (se 1 (by rfl) ⟨1758317, by rfl⟩ : syracuseStep 2344423 = 3516635) B3516635
theorem B1197737 : Blo 531801 1197737 := bstep (se 2 (by rfl) ⟨449151, by rfl⟩ : syracuseStep 1197737 = 898303) B898303
theorem B2705399 : Blo 531801 2705399 := bstep (se 1 (by rfl) ⟨2029049, by rfl⟩ : syracuseStep 2705399 = 4058099) B4058099
theorem B1198187 : Blo 531801 1198187 := bstep (se 1 (by rfl) ⟨898640, by rfl⟩ : syracuseStep 1198187 = 1797281) B1797281
theorem B1198223 : Blo 531801 1198223 := bstep (se 1 (by rfl) ⟨898667, by rfl⟩ : syracuseStep 1198223 = 1797335) B1797335
theorem B4574657 : Blo 531801 4574657 := bstep (se 2 (by rfl) ⟨1715496, by rfl⟩ : syracuseStep 4574657 = 3430993) B3430993
theorem B9752723 : Blo 531801 9752723 := bstep (se 1 (by rfl) ⟨7314542, by rfl⟩ : syracuseStep 9752723 = 14629085) B14629085
theorem B1200545 : Blo 531801 1200545 := bstep (se 2 (by rfl) ⟨450204, by rfl⟩ : syracuseStep 1200545 = 900409) B900409
theorem B1201481 : Blo 531801 1201481 := bstep (se 2 (by rfl) ⟨450555, by rfl⟩ : syracuseStep 1201481 = 901111) B901111
theorem B1201535 : Blo 531801 1201535 := bstep (se 1 (by rfl) ⟨901151, by rfl⟩ : syracuseStep 1201535 = 1802303) B1802303
theorem B1922783 : Blo 531801 1922783 := bstep (se 1 (by rfl) ⟨1442087, by rfl⟩ : syracuseStep 1922783 = 2884175) B2884175
theorem B1202075 : Blo 531801 1202075 := bstep (se 1 (by rfl) ⟨901556, by rfl⟩ : syracuseStep 1202075 = 1803113) B1803113
theorem B23320871 : Blo 531801 23320871 := bstep (se 1 (by rfl) ⟨17490653, by rfl⟩ : syracuseStep 23320871 = 34981307) B34981307
theorem B1202471 : Blo 531801 1202471 := bstep (se 1 (by rfl) ⟨901853, by rfl⟩ : syracuseStep 1202471 = 1803707) B1803707
theorem B1923695 : Blo 531801 1923695 := bstep (se 1 (by rfl) ⟨1442771, by rfl⟩ : syracuseStep 1923695 = 2885543) B2885543
theorem B5757587 : Blo 531801 5757587 := bstep (se 1 (by rfl) ⟨4318190, by rfl⟩ : syracuseStep 5757587 = 8636381) B8636381
theorem B1202849 : Blo 531801 1202849 := bstep (se 2 (by rfl) ⟨451068, by rfl⟩ : syracuseStep 1202849 = 902137) B902137
theorem B1202939 : Blo 531801 1202939 := bstep (se 1 (by rfl) ⟨902204, by rfl⟩ : syracuseStep 1202939 = 1804409) B1804409
theorem B1203767 : Blo 531801 1203767 := bstep (se 1 (by rfl) ⟨902825, by rfl⟩ : syracuseStep 1203767 = 1805651) B1805651
theorem B1138283 : Blo 531801 1138283 := bstep (se 1 (by rfl) ⟨853712, by rfl⟩ : syracuseStep 1138283 = 1707425) B1707425
theorem B3039839 : Blo 531801 3039839 := bstep (se 1 (by rfl) ⟨2279879, by rfl⟩ : syracuseStep 3039839 = 4559759) B4559759
theorem B2745359 : Blo 531801 2745359 := bstep (se 1 (by rfl) ⟨2059019, by rfl⟩ : syracuseStep 2745359 = 4118039) B4118039
theorem B1205459 : Blo 531801 1205459 := bstep (se 1 (by rfl) ⟨904094, by rfl⟩ : syracuseStep 1205459 = 1808189) B1808189
theorem B1205513 : Blo 531801 1205513 := bstep (se 2 (by rfl) ⟨452067, by rfl⟩ : syracuseStep 1205513 = 904135) B904135
theorem B3040841 : Blo 531801 3040841 := bstep (se 2 (by rfl) ⟨1140315, by rfl⟩ : syracuseStep 3040841 = 2280631) B2280631
theorem B2287723 : Blo 531801 2287723 := bstep (se 1 (by rfl) ⟨1715792, by rfl⟩ : syracuseStep 2287723 = 3431585) B3431585
theorem B1009847 : Blo 531801 1009847 := bstep (se 1 (by rfl) ⟨757385, by rfl⟩ : syracuseStep 1009847 = 1514771) B1514771
theorem B2026727 : Blo 531801 2026727 := bstep (se 1 (by rfl) ⟨1520045, by rfl⟩ : syracuseStep 2026727 = 3040091) B3040091
theorem B1928927 : Blo 531801 1928927 := bstep (se 1 (by rfl) ⟨1446695, by rfl⟩ : syracuseStep 1928927 = 2893391) B2893391
theorem B13660001 : Blo 531801 13660001 := bstep (se 2 (by rfl) ⟨5122500, by rfl⟩ : syracuseStep 13660001 = 10245001) B10245001
theorem B1929071 : Blo 531801 1929071 := bstep (se 1 (by rfl) ⟨1446803, by rfl⟩ : syracuseStep 1929071 = 2893607) B2893607
theorem B2158919 : Blo 531801 2158919 := bstep (se 1 (by rfl) ⟨1619189, by rfl⟩ : syracuseStep 2158919 = 3238379) B3238379
theorem B5765327 : Blo 531801 5765327 := bstep (se 1 (by rfl) ⟨4323995, by rfl⟩ : syracuseStep 5765327 = 8647991) B8647991
theorem B58292435 : Blo 531801 58292435 := bstep (se 1 (by rfl) ⟨43719326, by rfl⟩ : syracuseStep 58292435 = 87438653) B87438653
theorem B7699211 : Blo 531801 7699211 := bstep (se 1 (by rfl) ⟨5774408, by rfl⟩ : syracuseStep 7699211 = 11548817) B11548817
theorem B2031101 : Blo 531801 2031101 := bstep (se 3 (by rfl) ⟨380831, by rfl⟩ : syracuseStep 2031101 = 761663) B761663
theorem B2032361 : Blo 531801 2032361 := bstep (se 2 (by rfl) ⟨762135, by rfl⟩ : syracuseStep 2032361 = 1524271) B1524271
theorem B1803599 : Blo 531801 1803599 := bstep (se 1 (by rfl) ⟨1352699, by rfl⟩ : syracuseStep 1803599 = 2705399) B2705399
theorem B3049771 : Blo 531801 3049771 := bstep (se 1 (by rfl) ⟨2287328, by rfl⟩ : syracuseStep 3049771 = 4574657) B4574657
theorem B3050297 : Blo 531801 3050297 := bstep (se 2 (by rfl) ⟨1143861, by rfl⟩ : syracuseStep 3050297 = 2287723) B2287723
theorem B757289 : Blo 531801 757289 := bstep (se 2 (by rfl) ⟨283983, by rfl⟩ : syracuseStep 757289 = 567967) B567967
theorem B1282463 : Blo 531801 1282463 := bstep (se 1 (by rfl) ⟨961847, by rfl⟩ : syracuseStep 1282463 = 1923695) B1923695
theorem B3838391 : Blo 531801 3838391 := bstep (se 1 (by rfl) ⟨2878793, by rfl⟩ : syracuseStep 3838391 = 5757587) B5757587
theorem B758855 : Blo 531801 758855 := bstep (se 1 (by rfl) ⟨569141, by rfl⟩ : syracuseStep 758855 = 1138283) B1138283
theorem B2167967 : Blo 531801 2167967 := bstep (se 1 (by rfl) ⟨1625975, by rfl⟩ : syracuseStep 2167967 = 3251951) B3251951
theorem B2692925 : Blo 531801 2692925 := bstep (se 3 (by rfl) ⟨504923, by rfl⟩ : syracuseStep 2692925 = 1009847) B1009847
theorem B53222831 : Blo 531801 53222831 := bstep (se 1 (by rfl) ⟨39917123, by rfl⟩ : syracuseStep 53222831 = 79834247) B79834247
theorem B1351151 : Blo 531801 1351151 := bstep (se 1 (by rfl) ⟨1013363, by rfl⟩ : syracuseStep 1351151 = 2026727) B2026727
theorem B84156205 : Blo 531801 84156205 := bstep (se 3 (by rfl) ⟨15779288, by rfl⟩ : syracuseStep 84156205 = 31558577) B31558577
theorem B1285951 : Blo 531801 1285951 := bstep (se 1 (by rfl) ⟨964463, by rfl⟩ : syracuseStep 1285951 = 1928927) B1928927
theorem B1286047 : Blo 531801 1286047 := bstep (se 1 (by rfl) ⟨964535, by rfl⟩ : syracuseStep 1286047 = 1929071) B1929071
theorem B3088795 : Blo 531801 3088795 := bstep (se 1 (by rfl) ⟨2316596, by rfl⟩ : syracuseStep 3088795 = 4633193) B4633193
theorem B532895 : Blo 531801 532895 := bstep (se 1 (by rfl) ⟨399671, by rfl⟩ : syracuseStep 532895 = 799343) B799343
theorem B2499119 : Blo 531801 2499119 := bstep (se 1 (by rfl) ⟨1874339, by rfl⟩ : syracuseStep 2499119 = 3748679) B3748679
theorem B3253117 : Blo 531801 3253117 := bstep (se 3 (by rfl) ⟨609959, by rfl⟩ : syracuseStep 3253117 = 1219919) B1219919
theorem B533471 : Blo 531801 533471 := bstep (se 1 (by rfl) ⟨400103, by rfl⟩ : syracuseStep 533471 = 800207) B800207
theorem B533863 : Blo 531801 533863 := bstep (se 1 (by rfl) ⟨400397, by rfl⟩ : syracuseStep 533863 = 800795) B800795
theorem B3843551 : Blo 531801 3843551 := bstep (se 1 (by rfl) ⟨2882663, by rfl⟩ : syracuseStep 3843551 = 5765327) B5765327
theorem B534271 : Blo 531801 534271 := bstep (se 1 (by rfl) ⟨400703, by rfl⟩ : syracuseStep 534271 = 801407) B801407
theorem B534299 : Blo 531801 534299 := bstep (se 1 (by rfl) ⟨400724, by rfl⟩ : syracuseStep 534299 = 801449) B801449
theorem B534527 : Blo 531801 534527 := bstep (se 1 (by rfl) ⟨400895, by rfl⟩ : syracuseStep 534527 = 801791) B801791
theorem B1354067 : Blo 531801 1354067 := bstep (se 1 (by rfl) ⟨1015550, by rfl⟩ : syracuseStep 1354067 = 2031101) B2031101
theorem B2894555 : Blo 531801 2894555 := bstep (se 1 (by rfl) ⟨2170916, by rfl⟩ : syracuseStep 2894555 = 4341833) B4341833
theorem B7678799 : Blo 531801 7678799 := bstep (se 1 (by rfl) ⟨5759099, by rfl⟩ : syracuseStep 7678799 = 11518199) B11518199
theorem B535679 : Blo 531801 535679 := bstep (se 1 (by rfl) ⟨401759, by rfl⟩ : syracuseStep 535679 = 803519) B803519
theorem B798143 : Blo 531801 798143 := bstep (se 1 (by rfl) ⟨598607, by rfl⟩ : syracuseStep 798143 = 1197215) B1197215
theorem B798263 : Blo 531801 798263 := bstep (se 1 (by rfl) ⟨598697, by rfl⟩ : syracuseStep 798263 = 1197395) B1197395
theorem B6074027 : Blo 531801 6074027 := bstep (se 1 (by rfl) ⟨4555520, by rfl⟩ : syracuseStep 6074027 = 9111041) B9111041
theorem B798491 : Blo 531801 798491 := bstep (se 1 (by rfl) ⟨598868, by rfl⟩ : syracuseStep 798491 = 1197737) B1197737
theorem B798791 : Blo 531801 798791 := bstep (se 1 (by rfl) ⟨599093, by rfl⟩ : syracuseStep 798791 = 1198187) B1198187
theorem B798815 : Blo 531801 798815 := bstep (se 1 (by rfl) ⟨599111, by rfl⟩ : syracuseStep 798815 = 1198223) B1198223
theorem B1355879 : Blo 531801 1355879 := bstep (se 1 (by rfl) ⟨1016909, by rfl⟩ : syracuseStep 1355879 = 2033819) B2033819
theorem B1356011 : Blo 531801 1356011 := bstep (se 1 (by rfl) ⟨1017008, by rfl⟩ : syracuseStep 1356011 = 2034017) B2034017
theorem B4567549 : Blo 531801 4567549 := bstep (se 3 (by rfl) ⟨856415, by rfl⟩ : syracuseStep 4567549 = 1712831) B1712831
theorem B3125897 : Blo 531801 3125897 := bstep (se 2 (by rfl) ⟨1172211, by rfl⟩ : syracuseStep 3125897 = 2344423) B2344423
theorem B799913 : Blo 531801 799913 := bstep (se 2 (by rfl) ⟨299967, by rfl⟩ : syracuseStep 799913 = 599935) B599935
theorem B2274617 : Blo 531801 2274617 := bstep (se 2 (by rfl) ⟨852981, by rfl⟩ : syracuseStep 2274617 = 1705963) B1705963
theorem B6501815 : Blo 531801 6501815 := bstep (se 1 (by rfl) ⟨4876361, by rfl⟩ : syracuseStep 6501815 = 9752723) B9752723
theorem B11580985 : Blo 531801 11580985 := bstep (se 2 (by rfl) ⟨4342869, by rfl⟩ : syracuseStep 11580985 = 8685739) B8685739
theorem B800363 : Blo 531801 800363 := bstep (se 1 (by rfl) ⟨600272, by rfl⟩ : syracuseStep 800363 = 1200545) B1200545
theorem B800987 : Blo 531801 800987 := bstep (se 1 (by rfl) ⟨600740, by rfl⟩ : syracuseStep 800987 = 1201481) B1201481
theorem B801023 : Blo 531801 801023 := bstep (se 1 (by rfl) ⟨600767, by rfl⟩ : syracuseStep 801023 = 1201535) B1201535
theorem B801383 : Blo 531801 801383 := bstep (se 1 (by rfl) ⟨601037, by rfl⟩ : syracuseStep 801383 = 1202075) B1202075
theorem B15547247 : Blo 531801 15547247 := bstep (se 1 (by rfl) ⟨11660435, by rfl⟩ : syracuseStep 15547247 = 23320871) B23320871
theorem B801647 : Blo 531801 801647 := bstep (se 1 (by rfl) ⟨601235, by rfl⟩ : syracuseStep 801647 = 1202471) B1202471
theorem B10271609 : Blo 531801 10271609 := bstep (se 2 (by rfl) ⟨3851853, by rfl⟩ : syracuseStep 10271609 = 7703707) B7703707
theorem B801899 : Blo 531801 801899 := bstep (se 1 (by rfl) ⟨601424, by rfl⟩ : syracuseStep 801899 = 1202849) B1202849
theorem B801959 : Blo 531801 801959 := bstep (se 1 (by rfl) ⟨601469, by rfl⟩ : syracuseStep 801959 = 1202939) B1202939
theorem B802511 : Blo 531801 802511 := bstep (se 1 (by rfl) ⟨601883, by rfl⟩ : syracuseStep 802511 = 1203767) B1203767
theorem B803639 : Blo 531801 803639 := bstep (se 1 (by rfl) ⟨602729, by rfl⟩ : syracuseStep 803639 = 1205459) B1205459
theorem B1557319 : Blo 531801 1557319 := bstep (se 1 (by rfl) ⟨1167989, by rfl⟩ : syracuseStep 1557319 = 2335979) B2335979
theorem B803675 : Blo 531801 803675 := bstep (se 1 (by rfl) ⟨602756, by rfl⟩ : syracuseStep 803675 = 1205513) B1205513
theorem B1819835 : Blo 531801 1819835 := bstep (se 1 (by rfl) ⟨1364876, by rfl⟩ : syracuseStep 1819835 = 2729753) B2729753
theorem B5132807 : Blo 531801 5132807 := bstep (se 1 (by rfl) ⟨3849605, by rfl⟩ : syracuseStep 5132807 = 7699211) B7699211
theorem B1200905 : Blo 531801 1200905 := bstep (se 2 (by rfl) ⟨450339, by rfl⟩ : syracuseStep 1200905 = 900679) B900679
theorem B11687089 : Blo 531801 11687089 := bstep (se 2 (by rfl) ⟨4382658, by rfl⟩ : syracuseStep 11687089 = 8765317) B8765317
theorem B7526135 : Blo 531801 7526135 := bstep (se 1 (by rfl) ⟨5644601, by rfl⟩ : syracuseStep 7526135 = 11289203) B11289203
theorem B6510415 : Blo 531801 6510415 := bstep (se 1 (by rfl) ⟨4882811, by rfl⟩ : syracuseStep 6510415 = 9765623) B9765623
theorem B34527059 : Blo 531801 34527059 := bstep (se 1 (by rfl) ⟨25895294, by rfl⟩ : syracuseStep 34527059 = 51790589) B51790589
theorem B2283673 : Blo 531801 2283673 := bstep (se 2 (by rfl) ⟨856377, by rfl⟩ : syracuseStep 2283673 = 1712755) B1712755
theorem B3234433 : Blo 531801 3234433 := bstep (se 2 (by rfl) ⟨1212912, by rfl⟩ : syracuseStep 3234433 = 2425825) B2425825
theorem B809759 : Blo 531801 809759 := bstep (se 1 (by rfl) ⟨607319, by rfl⟩ : syracuseStep 809759 = 1214639) B1214639
theorem B1235945 : Blo 531801 1235945 := bstep (se 2 (by rfl) ⟨463479, by rfl⟩ : syracuseStep 1235945 = 926959) B926959
theorem B1204487 : Blo 531801 1204487 := bstep (se 1 (by rfl) ⟨903365, by rfl⟩ : syracuseStep 1204487 = 1806731) B1806731
theorem B2024297 : Blo 531801 2024297 := bstep (se 2 (by rfl) ⟨759111, by rfl⟩ : syracuseStep 2024297 = 1518223) B1518223
theorem B1796471 : Blo 531801 1796471 := bstep (se 1 (by rfl) ⟨1347353, by rfl⟩ : syracuseStep 1796471 = 2694707) B2694707
theorem B1796903 : Blo 531801 1796903 := bstep (se 1 (by rfl) ⟨1347677, by rfl⟩ : syracuseStep 1796903 = 2695355) B2695355
theorem B2026559 : Blo 531801 2026559 := bstep (se 1 (by rfl) ⟨1519919, by rfl⟩ : syracuseStep 2026559 = 3039839) B3039839
theorem B1830239 : Blo 531801 1830239 := bstep (se 1 (by rfl) ⟨1372679, by rfl⟩ : syracuseStep 1830239 = 2745359) B2745359
theorem B2027227 : Blo 531801 2027227 := bstep (se 1 (by rfl) ⟨1520420, by rfl⟩ : syracuseStep 2027227 = 3040841) B3040841
theorem B1797875 : Blo 531801 1797875 := bstep (se 1 (by rfl) ⟨1348406, by rfl⟩ : syracuseStep 1797875 = 2696813) B2696813
theorem B1142905 : Blo 531801 1142905 := bstep (se 2 (by rfl) ⟨428589, by rfl⟩ : syracuseStep 1142905 = 857179) B857179
theorem B20509685 : Blo 531801 20509685 := bstep (se 5 (by rfl) ⟨961391, by rfl⟩ : syracuseStep 20509685 = 1922783) B1922783
theorem B1799279 : Blo 531801 1799279 := bstep (se 1 (by rfl) ⟨1349459, by rfl⟩ : syracuseStep 1799279 = 2698919) B2698919
theorem B9106667 : Blo 531801 9106667 := bstep (se 1 (by rfl) ⟨6830000, by rfl⟩ : syracuseStep 9106667 = 13660001) B13660001
theorem B1439279 : Blo 531801 1439279 := bstep (se 1 (by rfl) ⟨1079459, by rfl⟩ : syracuseStep 1439279 = 2158919) B2158919
theorem B1800683 : Blo 531801 1800683 := bstep (se 1 (by rfl) ⟨1350512, by rfl⟩ : syracuseStep 1800683 = 2701025) B2701025
theorem B38861623 : Blo 531801 38861623 := bstep (se 1 (by rfl) ⟨29146217, by rfl⟩ : syracuseStep 38861623 = 58292435) B58292435
theorem B1802087 : Blo 531801 1802087 := bstep (se 1 (by rfl) ⟨1351565, by rfl⟩ : syracuseStep 1802087 = 2703131) B2703131
theorem B1213223 : Blo 531801 1213223 := bstep (se 1 (by rfl) ⟨909917, by rfl⟩ : syracuseStep 1213223 = 1819835) B1819835
theorem B2033531 : Blo 531801 2033531 := bstep (se 1 (by rfl) ⟨1525148, by rfl⟩ : syracuseStep 2033531 = 3050297) B3050297
theorem B854975 : Blo 531801 854975 := bstep (se 1 (by rfl) ⟨641231, by rfl⟩ : syracuseStep 854975 = 1282463) B1282463
theorem B2558927 : Blo 531801 2558927 := bstep (se 1 (by rfl) ⟨1919195, by rfl⟩ : syracuseStep 2558927 = 3838391) B3838391
theorem B4066361 : Blo 531801 4066361 := bstep (se 2 (by rfl) ⟨1524885, by rfl⟩ : syracuseStep 4066361 = 3049771) B3049771
theorem B1445311 : Blo 531801 1445311 := bstep (se 1 (by rfl) ⟨1083983, by rfl⟩ : syracuseStep 1445311 = 2167967) B2167967
theorem B5017423 : Blo 531801 5017423 := bstep (se 1 (by rfl) ⟨3763067, by rfl⟩ : syracuseStep 5017423 = 7526135) B7526135
theorem B823963 : Blo 531801 823963 := bstep (se 1 (by rfl) ⟨617972, by rfl⟩ : syracuseStep 823963 = 1235945) B1235945
theorem B1349531 : Blo 531801 1349531 := bstep (se 1 (by rfl) ⟨1012148, by rfl⟩ : syracuseStep 1349531 = 2024297) B2024297
theorem B2562367 : Blo 531801 2562367 := bstep (se 1 (by rfl) ⟨1921775, by rfl⟩ : syracuseStep 2562367 = 3843551) B3843551
theorem B5119199 : Blo 531801 5119199 := bstep (se 1 (by rfl) ⟨3839399, by rfl⟩ : syracuseStep 5119199 = 7678799) B7678799
theorem B1351039 : Blo 531801 1351039 := bstep (se 1 (by rfl) ⟨1013279, by rfl⟩ : syracuseStep 1351039 = 2026559) B2026559
theorem B15441313 : Blo 531801 15441313 := bstep (se 2 (by rfl) ⟨5790492, by rfl⟩ : syracuseStep 15441313 = 11580985) B11580985
theorem B1220159 : Blo 531801 1220159 := bstep (se 1 (by rfl) ⟨915119, by rfl⟩ : syracuseStep 1220159 = 1830239) B1830239
theorem B532095 : Blo 531801 532095 := bstep (se 1 (by rfl) ⟨399071, by rfl⟩ : syracuseStep 532095 = 798143) B798143
theorem B532175 : Blo 531801 532175 := bstep (se 1 (by rfl) ⟨399131, by rfl⟩ : syracuseStep 532175 = 798263) B798263
theorem B532327 : Blo 531801 532327 := bstep (se 1 (by rfl) ⟨399245, by rfl⟩ : syracuseStep 532327 = 798491) B798491
theorem B532527 : Blo 531801 532527 := bstep (se 1 (by rfl) ⟨399395, by rfl⟩ : syracuseStep 532527 = 798791) B798791
theorem B532543 : Blo 531801 532543 := bstep (se 1 (by rfl) ⟨399407, by rfl⟩ : syracuseStep 532543 = 798815) B798815
theorem B13673123 : Blo 531801 13673123 := bstep (se 1 (by rfl) ⟨10254842, by rfl⟩ : syracuseStep 13673123 = 20509685) B20509685
theorem B533275 : Blo 531801 533275 := bstep (se 1 (by rfl) ⟨399956, by rfl⟩ : syracuseStep 533275 = 799913) B799913
theorem B6071111 : Blo 531801 6071111 := bstep (se 1 (by rfl) ⟨4553333, by rfl⟩ : syracuseStep 6071111 = 9106667) B9106667
theorem B1516411 : Blo 531801 1516411 := bstep (se 1 (by rfl) ⟨1137308, by rfl⟩ : syracuseStep 1516411 = 2274617) B2274617
theorem B4334543 : Blo 531801 4334543 := bstep (se 1 (by rfl) ⟨3250907, by rfl⟩ : syracuseStep 4334543 = 6501815) B6501815
theorem B959519 : Blo 531801 959519 := bstep (se 1 (by rfl) ⟨719639, by rfl⟩ : syracuseStep 959519 = 1439279) B1439279
theorem B533575 : Blo 531801 533575 := bstep (se 1 (by rfl) ⟨400181, by rfl⟩ : syracuseStep 533575 = 800363) B800363
theorem B51815497 : Blo 531801 51815497 := bstep (se 2 (by rfl) ⟨19430811, by rfl⟩ : syracuseStep 51815497 = 38861623) B38861623
theorem B533991 : Blo 531801 533991 := bstep (se 1 (by rfl) ⟨400493, by rfl⟩ : syracuseStep 533991 = 800987) B800987
theorem B534015 : Blo 531801 534015 := bstep (se 1 (by rfl) ⟨400511, by rfl⟩ : syracuseStep 534015 = 801023) B801023
theorem B534255 : Blo 531801 534255 := bstep (se 1 (by rfl) ⟨400691, by rfl⟩ : syracuseStep 534255 = 801383) B801383
theorem B10364831 : Blo 531801 10364831 := bstep (se 1 (by rfl) ⟨7773623, by rfl⟩ : syracuseStep 10364831 = 15547247) B15547247
theorem B534431 : Blo 531801 534431 := bstep (se 1 (by rfl) ⟨400823, by rfl⟩ : syracuseStep 534431 = 801647) B801647
theorem B534599 : Blo 531801 534599 := bstep (se 1 (by rfl) ⟨400949, by rfl⟩ : syracuseStep 534599 = 801899) B801899
theorem B534639 : Blo 531801 534639 := bstep (se 1 (by rfl) ⟨400979, by rfl⟩ : syracuseStep 534639 = 801959) B801959
theorem B112208273 : Blo 531801 112208273 := bstep (se 2 (by rfl) ⟨42078102, by rfl⟩ : syracuseStep 112208273 = 84156205) B84156205
theorem B1714601 : Blo 531801 1714601 := bstep (se 2 (by rfl) ⟨642975, by rfl⟩ : syracuseStep 1714601 = 1285951) B1285951
theorem B535007 : Blo 531801 535007 := bstep (se 1 (by rfl) ⟨401255, by rfl⟩ : syracuseStep 535007 = 802511) B802511
theorem B1714729 : Blo 531801 1714729 := bstep (se 2 (by rfl) ⟨643023, by rfl⟩ : syracuseStep 1714729 = 1286047) B1286047
theorem B1354907 : Blo 531801 1354907 := bstep (se 1 (by rfl) ⟨1016180, by rfl⟩ : syracuseStep 1354907 = 2032361) B2032361
theorem B535759 : Blo 531801 535759 := bstep (se 1 (by rfl) ⟨401819, by rfl⟩ : syracuseStep 535759 = 803639) B803639
theorem B535783 : Blo 531801 535783 := bstep (se 1 (by rfl) ⟨401837, by rfl⟩ : syracuseStep 535783 = 803675) B803675
theorem B2076425 : Blo 531801 2076425 := bstep (se 2 (by rfl) ⟨778659, by rfl⟩ : syracuseStep 2076425 = 1557319) B1557319
theorem B4337489 : Blo 531801 4337489 := bstep (se 2 (by rfl) ⟨1626558, by rfl⟩ : syracuseStep 4337489 = 3253117) B3253117
theorem B3421871 : Blo 531801 3421871 := bstep (se 1 (by rfl) ⟨2566403, by rfl⟩ : syracuseStep 3421871 = 5132807) B5132807
theorem B800603 : Blo 531801 800603 := bstep (se 1 (by rfl) ⟨600452, by rfl⟩ : syracuseStep 800603 = 1200905) B1200905
theorem B23018039 : Blo 531801 23018039 := bstep (se 1 (by rfl) ⟨17263529, by rfl⟩ : syracuseStep 23018039 = 34527059) B34527059
theorem B539839 : Blo 531801 539839 := bstep (se 1 (by rfl) ⟨404879, by rfl⟩ : syracuseStep 539839 = 809759) B809759
theorem B2702969 : Blo 531801 2702969 := bstep (se 2 (by rfl) ⟨1013613, by rfl⟩ : syracuseStep 2702969 = 2027227) B2027227
theorem B900767 : Blo 531801 900767 := bstep (se 1 (by rfl) ⟨675575, by rfl⟩ : syracuseStep 900767 = 1351151) B1351151
theorem B1523873 : Blo 531801 1523873 := bstep (se 2 (by rfl) ⟨571452, by rfl⟩ : syracuseStep 1523873 = 1142905) B1142905
theorem B802991 : Blo 531801 802991 := bstep (se 1 (by rfl) ⟨602243, by rfl⟩ : syracuseStep 802991 = 1204487) B1204487
theorem B902711 : Blo 531801 902711 := bstep (se 1 (by rfl) ⟨677033, by rfl⟩ : syracuseStep 902711 = 1354067) B1354067
theorem B15582785 : Blo 531801 15582785 := bstep (se 2 (by rfl) ⟨5843544, by rfl⟩ : syracuseStep 15582785 = 11687089) B11687089
theorem B1197647 : Blo 531801 1197647 := bstep (se 1 (by rfl) ⟨898235, by rfl⟩ : syracuseStep 1197647 = 1796471) B1796471
theorem B1197935 : Blo 531801 1197935 := bstep (se 1 (by rfl) ⟨898451, by rfl⟩ : syracuseStep 1197935 = 1796903) B1796903
theorem B7718813 : Blo 531801 7718813 := bstep (se 3 (by rfl) ⟨1447277, by rfl⟩ : syracuseStep 7718813 = 2894555) B2894555
theorem B4049351 : Blo 531801 4049351 := bstep (se 1 (by rfl) ⟨3037013, by rfl⟩ : syracuseStep 4049351 = 6074027) B6074027
theorem B1198583 : Blo 531801 1198583 := bstep (se 1 (by rfl) ⟨898937, by rfl⟩ : syracuseStep 1198583 = 1797875) B1797875
theorem B903919 : Blo 531801 903919 := bstep (se 1 (by rfl) ⟨677939, by rfl⟩ : syracuseStep 903919 = 1355879) B1355879
theorem B904007 : Blo 531801 904007 := bstep (se 1 (by rfl) ⟨678005, by rfl⟩ : syracuseStep 904007 = 1356011) B1356011
theorem B2083931 : Blo 531801 2083931 := bstep (se 1 (by rfl) ⟨1562948, by rfl⟩ : syracuseStep 2083931 = 3125897) B3125897
theorem B1199519 : Blo 531801 1199519 := bstep (se 1 (by rfl) ⟨899639, by rfl⟩ : syracuseStep 1199519 = 1799279) B1799279
theorem B4312577 : Blo 531801 4312577 := bstep (se 2 (by rfl) ⟨1617216, by rfl⟩ : syracuseStep 4312577 = 3234433) B3234433
theorem B2019437 : Blo 531801 2019437 := bstep (se 3 (by rfl) ⟨378644, by rfl⟩ : syracuseStep 2019437 = 757289) B757289
theorem B1200455 : Blo 531801 1200455 := bstep (se 1 (by rfl) ⟨900341, by rfl⟩ : syracuseStep 1200455 = 1800683) B1800683
theorem B1201391 : Blo 531801 1201391 := bstep (se 1 (by rfl) ⟨901043, by rfl⟩ : syracuseStep 1201391 = 1802087) B1802087
theorem B4118393 : Blo 531801 4118393 := bstep (se 2 (by rfl) ⟨1544397, by rfl⟩ : syracuseStep 4118393 = 3088795) B3088795
theorem B1202399 : Blo 531801 1202399 := bstep (se 1 (by rfl) ⟨901799, by rfl⟩ : syracuseStep 1202399 = 1803599) B1803599
theorem B2023613 : Blo 531801 2023613 := bstep (se 3 (by rfl) ⟨379427, by rfl⟩ : syracuseStep 2023613 = 758855) B758855
theorem B1795283 : Blo 531801 1795283 := bstep (se 1 (by rfl) ⟨1346462, by rfl⟩ : syracuseStep 1795283 = 2692925) B2692925
theorem B35481887 : Blo 531801 35481887 := bstep (se 1 (by rfl) ⟨26611415, by rfl⟩ : syracuseStep 35481887 = 53222831) B53222831
theorem B1666079 : Blo 531801 1666079 := bstep (se 1 (by rfl) ⟨1249559, by rfl⟩ : syracuseStep 1666079 = 2499119) B2499119
theorem B6090065 : Blo 531801 6090065 := bstep (se 2 (by rfl) ⟨2283774, by rfl⟩ : syracuseStep 6090065 = 4567549) B4567549
theorem B8680553 : Blo 531801 8680553 := bstep (se 2 (by rfl) ⟨3255207, by rfl⟩ : syracuseStep 8680553 = 6510415) B6510415
theorem B3044897 : Blo 531801 3044897 := bstep (se 2 (by rfl) ⟨1141836, by rfl⟩ : syracuseStep 3044897 = 2283673) B2283673
theorem B6847739 : Blo 531801 6847739 := bstep (se 1 (by rfl) ⟨5135804, by rfl⟩ : syracuseStep 6847739 = 10271609) B10271609
theorem B1015915 : Blo 531801 1015915 := bstep (se 1 (by rfl) ⟨761936, by rfl⟩ : syracuseStep 1015915 = 1523873) B1523873
theorem B5145875 : Blo 531801 5145875 := bstep (se 1 (by rfl) ⟨3859406, by rfl⟩ : syracuseStep 5145875 = 7718813) B7718813
theorem B1705951 : Blo 531801 1705951 := bstep (se 1 (by rfl) ⟨1279463, by rfl⟩ : syracuseStep 1705951 = 2558927) B2558927
theorem B1346291 : Blo 531801 1346291 := bstep (se 1 (by rfl) ⟨1009718, by rfl⟩ : syracuseStep 1346291 = 2019437) B2019437
theorem B3412799 : Blo 531801 3412799 := bstep (se 1 (by rfl) ⟨2559599, by rfl⟩ : syracuseStep 3412799 = 5119199) B5119199
theorem B6689897 : Blo 531801 6689897 := bstep (se 2 (by rfl) ⟨2508711, by rfl⟩ : syracuseStep 6689897 = 5017423) B5017423
theorem B1349075 : Blo 531801 1349075 := bstep (se 1 (by rfl) ⟨1011806, by rfl⟩ : syracuseStep 1349075 = 2023613) B2023613
theorem B9115415 : Blo 531801 9115415 := bstep (se 1 (by rfl) ⟨6836561, by rfl⟩ : syracuseStep 9115415 = 13673123) B13673123
theorem B2889695 : Blo 531801 2889695 := bstep (se 1 (by rfl) ⟨2167271, by rfl⟩ : syracuseStep 2889695 = 4334543) B4334543
theorem B1384283 : Blo 531801 1384283 := bstep (se 1 (by rfl) ⟨1038212, by rfl⟩ : syracuseStep 1384283 = 2076425) B2076425
theorem B2891659 : Blo 531801 2891659 := bstep (se 1 (by rfl) ⟨2168744, by rfl⟩ : syracuseStep 2891659 = 4337489) B4337489
theorem B3416489 : Blo 531801 3416489 := bstep (se 2 (by rfl) ⟨1281183, by rfl⟩ : syracuseStep 3416489 = 2562367) B2562367
theorem B533735 : Blo 531801 533735 := bstep (se 1 (by rfl) ⟨400301, by rfl⟩ : syracuseStep 533735 = 800603) B800603
theorem B15345359 : Blo 531801 15345359 := bstep (se 1 (by rfl) ⟨11509019, by rfl⟩ : syracuseStep 15345359 = 23018039) B23018039
theorem B20588417 : Blo 531801 20588417 := bstep (se 2 (by rfl) ⟨7720656, by rfl⟩ : syracuseStep 20588417 = 15441313) B15441313
theorem B4565159 : Blo 531801 4565159 := bstep (se 1 (by rfl) ⟨3423869, by rfl⟩ : syracuseStep 4565159 = 6847739) B6847739
theorem B600511 : Blo 531801 600511 := bstep (se 1 (by rfl) ⟨450383, by rfl⟩ : syracuseStep 600511 = 900767) B900767
theorem B535327 : Blo 531801 535327 := bstep (se 1 (by rfl) ⟨401495, by rfl⟩ : syracuseStep 535327 = 802991) B802991
theorem B601807 : Blo 531801 601807 := bstep (se 1 (by rfl) ⟨451355, by rfl⟩ : syracuseStep 601807 = 902711) B902711
theorem B798431 : Blo 531801 798431 := bstep (se 1 (by rfl) ⟨598823, by rfl⟩ : syracuseStep 798431 = 1197647) B1197647
theorem B798623 : Blo 531801 798623 := bstep (se 1 (by rfl) ⟨598967, by rfl⟩ : syracuseStep 798623 = 1197935) B1197935
theorem B1355687 : Blo 531801 1355687 := bstep (se 1 (by rfl) ⟨1016765, by rfl⟩ : syracuseStep 1355687 = 2033531) B2033531
theorem B69087329 : Blo 531801 69087329 := bstep (se 2 (by rfl) ⟨25907748, by rfl⟩ : syracuseStep 69087329 = 51815497) B51815497
theorem B2699567 : Blo 531801 2699567 := bstep (se 1 (by rfl) ⟨2024675, by rfl⟩ : syracuseStep 2699567 = 4049351) B4049351
theorem B799055 : Blo 531801 799055 := bstep (se 1 (by rfl) ⟨599291, by rfl⟩ : syracuseStep 799055 = 1198583) B1198583
theorem B602671 : Blo 531801 602671 := bstep (se 1 (by rfl) ⟨452003, by rfl⟩ : syracuseStep 602671 = 904007) B904007
theorem B1389287 : Blo 531801 1389287 := bstep (se 1 (by rfl) ⟨1041965, by rfl⟩ : syracuseStep 1389287 = 2083931) B2083931
theorem B799679 : Blo 531801 799679 := bstep (se 1 (by rfl) ⟨599759, by rfl⟩ : syracuseStep 799679 = 1199519) B1199519
theorem B800303 : Blo 531801 800303 := bstep (se 1 (by rfl) ⟨600227, by rfl⟩ : syracuseStep 800303 = 1200455) B1200455
theorem B800927 : Blo 531801 800927 := bstep (se 1 (by rfl) ⟨600695, by rfl⟩ : syracuseStep 800927 = 1201391) B1201391
theorem B899687 : Blo 531801 899687 := bstep (se 1 (by rfl) ⟨674765, by rfl⟩ : syracuseStep 899687 = 1349531) B1349531
theorem B801599 : Blo 531801 801599 := bstep (se 1 (by rfl) ⟨601199, by rfl⟩ : syracuseStep 801599 = 1202399) B1202399
theorem B4047407 : Blo 531801 4047407 := bstep (se 1 (by rfl) ⟨3035555, by rfl⟩ : syracuseStep 4047407 = 6071111) B6071111
theorem B166216373 : Blo 531801 166216373 := bstep (se 5 (by rfl) ⟨7791392, by rfl⟩ : syracuseStep 166216373 = 15582785) B15582785
theorem B639679 : Blo 531801 639679 := bstep (se 1 (by rfl) ⟨479759, by rfl⟩ : syracuseStep 639679 = 959519) B959519
theorem B1196855 : Blo 531801 1196855 := bstep (se 1 (by rfl) ⟨897641, by rfl⟩ : syracuseStep 1196855 = 1795283) B1795283
theorem B1098617 : Blo 531801 1098617 := bstep (se 2 (by rfl) ⟨411981, by rfl⟩ : syracuseStep 1098617 = 823963) B823963
theorem B903271 : Blo 531801 903271 := bstep (se 1 (by rfl) ⟨677453, by rfl⟩ : syracuseStep 903271 = 1354907) B1354907
theorem B2279933 : Blo 531801 2279933 := bstep (se 3 (by rfl) ⟨427487, by rfl⟩ : syracuseStep 2279933 = 854975) B854975
theorem B5787035 : Blo 531801 5787035 := bstep (se 1 (by rfl) ⟨4340276, by rfl⟩ : syracuseStep 5787035 = 8680553) B8680553
theorem B2281247 : Blo 531801 2281247 := bstep (se 1 (by rfl) ⟨1710935, by rfl⟩ : syracuseStep 2281247 = 3421871) B3421871
theorem B2021881 : Blo 531801 2021881 := bstep (se 2 (by rfl) ⟨758205, by rfl⟩ : syracuseStep 2021881 = 1516411) B1516411
theorem B2710907 : Blo 531801 2710907 := bstep (se 1 (by rfl) ⟨2033180, by rfl⟩ : syracuseStep 2710907 = 4066361) B4066361
theorem B3235261 : Blo 531801 3235261 := bstep (se 3 (by rfl) ⟨606611, by rfl⟩ : syracuseStep 3235261 = 1213223) B1213223
theorem B2875051 : Blo 531801 2875051 := bstep (se 1 (by rfl) ⟨2156288, by rfl⟩ : syracuseStep 2875051 = 4312577) B4312577
theorem B2286305 : Blo 531801 2286305 := bstep (se 2 (by rfl) ⟨857364, by rfl⟩ : syracuseStep 2286305 = 1714729) B1714729
theorem B1205225 : Blo 531801 1205225 := bstep (se 2 (by rfl) ⟨451959, by rfl⟩ : syracuseStep 1205225 = 903919) B903919
theorem B2745595 : Blo 531801 2745595 := bstep (se 1 (by rfl) ⟨2059196, by rfl⟩ : syracuseStep 2745595 = 4118393) B4118393
theorem B1927081 : Blo 531801 1927081 := bstep (se 2 (by rfl) ⟨722655, by rfl⟩ : syracuseStep 1927081 = 1445311) B1445311
theorem B813439 : Blo 531801 813439 := bstep (se 1 (by rfl) ⟨610079, by rfl⟩ : syracuseStep 813439 = 1220159) B1220159
theorem B6909887 : Blo 531801 6909887 := bstep (se 1 (by rfl) ⟨5182415, by rfl⟩ : syracuseStep 6909887 = 10364831) B10364831
theorem B23654591 : Blo 531801 23654591 := bstep (se 1 (by rfl) ⟨17740943, by rfl⟩ : syracuseStep 23654591 = 35481887) B35481887
theorem B74805515 : Blo 531801 74805515 := bstep (se 1 (by rfl) ⟨56104136, by rfl⟩ : syracuseStep 74805515 = 112208273) B112208273
theorem B1143067 : Blo 531801 1143067 := bstep (se 1 (by rfl) ⟨857300, by rfl⟩ : syracuseStep 1143067 = 1714601) B1714601
theorem B1110719 : Blo 531801 1110719 := bstep (se 1 (by rfl) ⟨833039, by rfl⟩ : syracuseStep 1110719 = 1666079) B1666079
theorem B4060043 : Blo 531801 4060043 := bstep (se 1 (by rfl) ⟨3045032, by rfl⟩ : syracuseStep 4060043 = 6090065) B6090065
theorem B2029931 : Blo 531801 2029931 := bstep (se 1 (by rfl) ⟨1522448, by rfl⟩ : syracuseStep 2029931 = 3044897) B3044897
theorem B719785 : Blo 531801 719785 := bstep (se 2 (by rfl) ⟨269919, by rfl⟩ : syracuseStep 719785 = 539839) B539839
theorem B1801385 : Blo 531801 1801385 := bstep (se 2 (by rfl) ⟨675519, by rfl⟩ : syracuseStep 1801385 = 1351039) B1351039
theorem B1801979 : Blo 531801 1801979 := bstep (se 1 (by rfl) ⟨1351484, by rfl⟩ : syracuseStep 1801979 = 2702969) B2702969
theorem B852905 : Blo 531801 852905 := bstep (se 2 (by rfl) ⟨319839, by rfl⟩ : syracuseStep 852905 = 639679) B639679
theorem B1084585 : Blo 531801 1084585 := bstep (se 2 (by rfl) ⟨406719, by rfl⟩ : syracuseStep 1084585 = 813439) B813439
theorem B4459931 : Blo 531801 4459931 := bstep (se 1 (by rfl) ⟨3344948, by rfl⟩ : syracuseStep 4459931 = 6689897) B6689897
theorem B3838853 : Blo 531801 3838853 := bstep (se 4 (by rfl) ⟨359892, by rfl⟩ : syracuseStep 3838853 = 719785) B719785
theorem B1807271 : Blo 531801 1807271 := bstep (se 1 (by rfl) ⟨1355453, by rfl⟩ : syracuseStep 1807271 = 2710907) B2710907
theorem B922855 : Blo 531801 922855 := bstep (se 1 (by rfl) ⟨692141, by rfl⟩ : syracuseStep 922855 = 1384283) B1384283
theorem B10230239 : Blo 531801 10230239 := bstep (se 1 (by rfl) ⟨7672679, by rfl⟩ : syracuseStep 10230239 = 15345359) B15345359
theorem B532287 : Blo 531801 532287 := bstep (se 1 (by rfl) ⟨399215, by rfl⟩ : syracuseStep 532287 = 798431) B798431
theorem B532415 : Blo 531801 532415 := bstep (se 1 (by rfl) ⟨399311, by rfl⟩ : syracuseStep 532415 = 798623) B798623
theorem B15769727 : Blo 531801 15769727 := bstep (se 1 (by rfl) ⟨11827295, by rfl⟩ : syracuseStep 15769727 = 23654591) B23654591
theorem B532703 : Blo 531801 532703 := bstep (se 1 (by rfl) ⟨399527, by rfl⟩ : syracuseStep 532703 = 799055) B799055
theorem B926191 : Blo 531801 926191 := bstep (se 1 (by rfl) ⟨694643, by rfl⟩ : syracuseStep 926191 = 1389287) B1389287
theorem B533119 : Blo 531801 533119 := bstep (se 1 (by rfl) ⟨399839, by rfl⟩ : syracuseStep 533119 = 799679) B799679
theorem B2695841 : Blo 531801 2695841 := bstep (se 2 (by rfl) ⟨1010940, by rfl⟩ : syracuseStep 2695841 = 2021881) B2021881
theorem B533535 : Blo 531801 533535 := bstep (se 1 (by rfl) ⟨400151, by rfl⟩ : syracuseStep 533535 = 800303) B800303
theorem B533951 : Blo 531801 533951 := bstep (se 1 (by rfl) ⟨400463, by rfl⟩ : syracuseStep 533951 = 800927) B800927
theorem B1353287 : Blo 531801 1353287 := bstep (se 1 (by rfl) ⟨1014965, by rfl⟩ : syracuseStep 1353287 = 2029931) B2029931
theorem B599791 : Blo 531801 599791 := bstep (se 1 (by rfl) ⟨449843, by rfl⟩ : syracuseStep 599791 = 899687) B899687
theorem B534399 : Blo 531801 534399 := bstep (se 1 (by rfl) ⟨400799, by rfl⟩ : syracuseStep 534399 = 801599) B801599
theorem B18426365 : Blo 531801 18426365 := bstep (se 3 (by rfl) ⟨3454943, by rfl⟩ : syracuseStep 18426365 = 6909887) B6909887
theorem B1354553 : Blo 531801 1354553 := bstep (se 2 (by rfl) ⟨507957, by rfl⟩ : syracuseStep 1354553 = 1015915) B1015915
theorem B2698271 : Blo 531801 2698271 := bstep (se 1 (by rfl) ⟨2023703, by rfl⟩ : syracuseStep 2698271 = 4047407) B4047407
theorem B797903 : Blo 531801 797903 := bstep (se 1 (by rfl) ⟨598427, by rfl⟩ : syracuseStep 797903 = 1196855) B1196855
theorem B1519955 : Blo 531801 1519955 := bstep (se 1 (by rfl) ⟨1139966, by rfl⟩ : syracuseStep 1519955 = 2279933) B2279933
theorem B897527 : Blo 531801 897527 := bstep (se 1 (by rfl) ⟨673145, by rfl⟩ : syracuseStep 897527 = 1346291) B1346291
theorem B2961917 : Blo 531801 2961917 := bstep (se 3 (by rfl) ⟨555359, by rfl⟩ : syracuseStep 2961917 = 1110719) B1110719
theorem B2929645 : Blo 531801 2929645 := bstep (se 3 (by rfl) ⟨549308, by rfl⟩ : syracuseStep 2929645 = 1098617) B1098617
theorem B1520831 : Blo 531801 1520831 := bstep (se 1 (by rfl) ⟨1140623, by rfl⟩ : syracuseStep 1520831 = 2281247) B2281247
theorem B2569441 : Blo 531801 2569441 := bstep (se 2 (by rfl) ⟨963540, by rfl⟩ : syracuseStep 2569441 = 1927081) B1927081
theorem B2274601 : Blo 531801 2274601 := bstep (se 2 (by rfl) ⟨852975, by rfl⟩ : syracuseStep 2274601 = 1705951) B1705951
theorem B2275199 : Blo 531801 2275199 := bstep (se 1 (by rfl) ⟨1706399, by rfl⟩ : syracuseStep 2275199 = 3412799) B3412799
theorem B800681 : Blo 531801 800681 := bstep (se 2 (by rfl) ⟨300255, by rfl⟩ : syracuseStep 800681 = 600511) B600511
theorem B899383 : Blo 531801 899383 := bstep (se 1 (by rfl) ⟨674537, by rfl⟩ : syracuseStep 899383 = 1349075) B1349075
theorem B6076943 : Blo 531801 6076943 := bstep (se 1 (by rfl) ⟨4557707, by rfl⟩ : syracuseStep 6076943 = 9115415) B9115415
theorem B802409 : Blo 531801 802409 := bstep (se 2 (by rfl) ⟨300903, by rfl⟩ : syracuseStep 802409 = 601807) B601807
theorem B2277659 : Blo 531801 2277659 := bstep (se 1 (by rfl) ⟨1708244, by rfl⟩ : syracuseStep 2277659 = 3416489) B3416489
theorem B1524089 : Blo 531801 1524089 := bstep (se 2 (by rfl) ⟨571533, by rfl⟩ : syracuseStep 1524089 = 1143067) B1143067
theorem B1524203 : Blo 531801 1524203 := bstep (se 1 (by rfl) ⟨1143152, by rfl⟩ : syracuseStep 1524203 = 2286305) B2286305
theorem B803483 : Blo 531801 803483 := bstep (se 1 (by rfl) ⟨602612, by rfl⟩ : syracuseStep 803483 = 1205225) B1205225
theorem B803561 : Blo 531801 803561 := bstep (se 2 (by rfl) ⟨301335, by rfl⟩ : syracuseStep 803561 = 602671) B602671
theorem B903791 : Blo 531801 903791 := bstep (se 1 (by rfl) ⟨677843, by rfl⟩ : syracuseStep 903791 = 1355687) B1355687
theorem B46058219 : Blo 531801 46058219 := bstep (se 1 (by rfl) ⟨34543664, by rfl⟩ : syracuseStep 46058219 = 69087329) B69087329
theorem B2706695 : Blo 531801 2706695 := bstep (se 1 (by rfl) ⟨2030021, by rfl⟩ : syracuseStep 2706695 = 4060043) B4060043
theorem B4313681 : Blo 531801 4313681 := bstep (se 2 (by rfl) ⟨1617630, by rfl⟩ : syracuseStep 4313681 = 3235261) B3235261
theorem B1200923 : Blo 531801 1200923 := bstep (se 1 (by rfl) ⟨900692, by rfl⟩ : syracuseStep 1200923 = 1801385) B1801385
theorem B1201319 : Blo 531801 1201319 := bstep (se 1 (by rfl) ⟨900989, by rfl⟩ : syracuseStep 1201319 = 1801979) B1801979
theorem B3855545 : Blo 531801 3855545 := bstep (se 2 (by rfl) ⟨1445829, by rfl⟩ : syracuseStep 3855545 = 2891659) B2891659
theorem B110810915 : Blo 531801 110810915 := bstep (se 1 (by rfl) ⟨83108186, by rfl⟩ : syracuseStep 110810915 = 166216373) B166216373
theorem B3430583 : Blo 531801 3430583 := bstep (se 1 (by rfl) ⟨2572937, by rfl⟩ : syracuseStep 3430583 = 5145875) B5145875
theorem B3858023 : Blo 531801 3858023 := bstep (se 1 (by rfl) ⟨2893517, by rfl⟩ : syracuseStep 3858023 = 5787035) B5787035
theorem B1204361 : Blo 531801 1204361 := bstep (se 2 (by rfl) ⟨451635, by rfl⟩ : syracuseStep 1204361 = 903271) B903271
theorem B1926463 : Blo 531801 1926463 := bstep (se 1 (by rfl) ⟨1444847, by rfl⟩ : syracuseStep 1926463 = 2889695) B2889695
theorem B13725611 : Blo 531801 13725611 := bstep (se 1 (by rfl) ⟨10294208, by rfl⟩ : syracuseStep 13725611 = 20588417) B20588417
theorem B14643173 : Blo 531801 14643173 := bstep (se 4 (by rfl) ⟨1372797, by rfl⟩ : syracuseStep 14643173 = 2745595) B2745595
theorem B3043439 : Blo 531801 3043439 := bstep (se 1 (by rfl) ⟨2282579, by rfl⟩ : syracuseStep 3043439 = 4565159) B4565159
theorem B49870343 : Blo 531801 49870343 := bstep (se 1 (by rfl) ⟨37402757, by rfl⟩ : syracuseStep 49870343 = 74805515) B74805515
theorem B1799711 : Blo 531801 1799711 := bstep (se 1 (by rfl) ⟨1349783, by rfl⟩ : syracuseStep 1799711 = 2699567) B2699567
theorem B3833401 : Blo 531801 3833401 := bstep (se 2 (by rfl) ⟨1437525, by rfl⟩ : syracuseStep 3833401 = 2875051) B2875051
theorem B1016059 : Blo 531801 1016059 := bstep (se 1 (by rfl) ⟨762044, by rfl⟩ : syracuseStep 1016059 = 1524089) B1524089
theorem B1016135 : Blo 531801 1016135 := bstep (se 1 (by rfl) ⟨762101, by rfl⟩ : syracuseStep 1016135 = 1524203) B1524203
theorem B30705479 : Blo 531801 30705479 := bstep (se 1 (by rfl) ⟨23029109, by rfl⟩ : syracuseStep 30705479 = 46058219) B46058219
theorem B1804463 : Blo 531801 1804463 := bstep (se 1 (by rfl) ⟨1353347, by rfl⟩ : syracuseStep 1804463 = 2706695) B2706695
theorem B2559235 : Blo 531801 2559235 := bstep (se 1 (by rfl) ⟨1919426, by rfl⟩ : syracuseStep 2559235 = 3838853) B3838853
theorem B1446113 : Blo 531801 1446113 := bstep (se 2 (by rfl) ⟨542292, by rfl⟩ : syracuseStep 1446113 = 1084585) B1084585
theorem B6820159 : Blo 531801 6820159 := bstep (se 1 (by rfl) ⟨5115119, by rfl⟩ : syracuseStep 6820159 = 10230239) B10230239
theorem B3906193 : Blo 531801 3906193 := bstep (se 2 (by rfl) ⟨1464822, by rfl⟩ : syracuseStep 3906193 = 2929645) B2929645
theorem B531935 : Blo 531801 531935 := bstep (se 1 (by rfl) ⟨398951, by rfl⟩ : syracuseStep 531935 = 797903) B797903
theorem B9150407 : Blo 531801 9150407 := bstep (se 1 (by rfl) ⟨6862805, by rfl⟩ : syracuseStep 9150407 = 13725611) B13725611
theorem B598351 : Blo 531801 598351 := bstep (se 1 (by rfl) ⟨448763, by rfl⟩ : syracuseStep 598351 = 897527) B897527
theorem B1974611 : Blo 531801 1974611 := bstep (se 1 (by rfl) ⟨1480958, by rfl⟩ : syracuseStep 1974611 = 2961917) B2961917
theorem B1516799 : Blo 531801 1516799 := bstep (se 1 (by rfl) ⟨1137599, by rfl⟩ : syracuseStep 1516799 = 2275199) B2275199
theorem B533787 : Blo 531801 533787 := bstep (se 1 (by rfl) ⟨400340, by rfl⟩ : syracuseStep 533787 = 800681) B800681
theorem B534939 : Blo 531801 534939 := bstep (se 1 (by rfl) ⟨401204, by rfl⟩ : syracuseStep 534939 = 802409) B802409
theorem B1518439 : Blo 531801 1518439 := bstep (se 1 (by rfl) ⟨1138829, by rfl⟩ : syracuseStep 1518439 = 2277659) B2277659
theorem B535655 : Blo 531801 535655 := bstep (se 1 (by rfl) ⟨401741, by rfl⟩ : syracuseStep 535655 = 803483) B803483
theorem B535707 : Blo 531801 535707 := bstep (se 1 (by rfl) ⟨401780, by rfl⟩ : syracuseStep 535707 = 803561) B803561
theorem B568603 : Blo 531801 568603 := bstep (se 1 (by rfl) ⟨426452, by rfl⟩ : syracuseStep 568603 = 852905) B852905
theorem B602527 : Blo 531801 602527 := bstep (se 1 (by rfl) ⟨451895, by rfl⟩ : syracuseStep 602527 = 903791) B903791
theorem B2568617 : Blo 531801 2568617 := bstep (se 2 (by rfl) ⟨963231, by rfl⟩ : syracuseStep 2568617 = 1926463) B1926463
theorem B799721 : Blo 531801 799721 := bstep (se 2 (by rfl) ⟨299895, by rfl⟩ : syracuseStep 799721 = 599791) B599791
theorem B800615 : Blo 531801 800615 := bstep (se 1 (by rfl) ⟨600461, by rfl⟩ : syracuseStep 800615 = 1200923) B1200923
theorem B800879 : Blo 531801 800879 := bstep (se 1 (by rfl) ⟨600659, by rfl⟩ : syracuseStep 800879 = 1201319) B1201319
theorem B2570363 : Blo 531801 2570363 := bstep (se 1 (by rfl) ⟨1927772, by rfl⟩ : syracuseStep 2570363 = 3855545) B3855545
theorem B73873943 : Blo 531801 73873943 := bstep (se 1 (by rfl) ⟨55405457, by rfl⟩ : syracuseStep 73873943 = 110810915) B110810915
theorem B2572015 : Blo 531801 2572015 := bstep (se 1 (by rfl) ⟨1929011, by rfl⟩ : syracuseStep 2572015 = 3858023) B3858023
theorem B802907 : Blo 531801 802907 := bstep (se 1 (by rfl) ⟨602180, by rfl⟩ : syracuseStep 802907 = 1204361) B1204361
theorem B902191 : Blo 531801 902191 := bstep (se 1 (by rfl) ⟨676643, by rfl⟩ : syracuseStep 902191 = 1353287) B1353287
theorem B3425921 : Blo 531801 3425921 := bstep (se 2 (by rfl) ⟨1284720, by rfl⟩ : syracuseStep 3425921 = 2569441) B2569441
theorem B1230473 : Blo 531801 1230473 := bstep (se 2 (by rfl) ⟨461427, by rfl⟩ : syracuseStep 1230473 = 922855) B922855
theorem B3032801 : Blo 531801 3032801 := bstep (se 2 (by rfl) ⟨1137300, by rfl⟩ : syracuseStep 3032801 = 2274601) B2274601
theorem B903035 : Blo 531801 903035 := bstep (se 1 (by rfl) ⟨677276, by rfl⟩ : syracuseStep 903035 = 1354553) B1354553
theorem B1199177 : Blo 531801 1199177 := bstep (se 2 (by rfl) ⟨449691, by rfl⟩ : syracuseStep 1199177 = 899383) B899383
theorem B33246895 : Blo 531801 33246895 := bstep (se 1 (by rfl) ⟨24935171, by rfl⟩ : syracuseStep 33246895 = 49870343) B49870343
theorem B1199807 : Blo 531801 1199807 := bstep (se 1 (by rfl) ⟨899855, by rfl⟩ : syracuseStep 1199807 = 1799711) B1799711
theorem B4051295 : Blo 531801 4051295 := bstep (se 1 (by rfl) ⟨3038471, by rfl⟩ : syracuseStep 4051295 = 6076943) B6076943
theorem B1234921 : Blo 531801 1234921 := bstep (se 2 (by rfl) ⟨463095, by rfl⟩ : syracuseStep 1234921 = 926191) B926191
theorem B2973287 : Blo 531801 2973287 := bstep (se 1 (by rfl) ⟨2229965, by rfl⟩ : syracuseStep 2973287 = 4459931) B4459931
theorem B2875787 : Blo 531801 2875787 := bstep (se 1 (by rfl) ⟨2156840, by rfl⟩ : syracuseStep 2875787 = 4313681) B4313681
theorem B1204847 : Blo 531801 1204847 := bstep (se 1 (by rfl) ⟨903635, by rfl⟩ : syracuseStep 1204847 = 1807271) B1807271
theorem B2287055 : Blo 531801 2287055 := bstep (se 1 (by rfl) ⟨1715291, by rfl⟩ : syracuseStep 2287055 = 3430583) B3430583
theorem B10513151 : Blo 531801 10513151 := bstep (se 1 (by rfl) ⟨7884863, by rfl⟩ : syracuseStep 10513151 = 15769727) B15769727
theorem B1797227 : Blo 531801 1797227 := bstep (se 1 (by rfl) ⟨1347920, by rfl⟩ : syracuseStep 1797227 = 2695841) B2695841
theorem B12284243 : Blo 531801 12284243 := bstep (se 1 (by rfl) ⟨9213182, by rfl⟩ : syracuseStep 12284243 = 18426365) B18426365
theorem B1798847 : Blo 531801 1798847 := bstep (se 1 (by rfl) ⟨1349135, by rfl⟩ : syracuseStep 1798847 = 2698271) B2698271
theorem B9762115 : Blo 531801 9762115 := bstep (se 1 (by rfl) ⟨7321586, by rfl⟩ : syracuseStep 9762115 = 14643173) B14643173
theorem B2028959 : Blo 531801 2028959 := bstep (se 1 (by rfl) ⟨1521719, by rfl⟩ : syracuseStep 2028959 = 3043439) B3043439
theorem B1013303 : Blo 531801 1013303 := bstep (se 1 (by rfl) ⟨759977, by rfl⟩ : syracuseStep 1013303 = 1519955) B1519955
theorem B1013887 : Blo 531801 1013887 := bstep (se 1 (by rfl) ⟨760415, by rfl⟩ : syracuseStep 1013887 = 1520831) B1520831
theorem B5111201 : Blo 531801 5111201 := bstep (se 2 (by rfl) ⟨1916700, by rfl⟩ : syracuseStep 5111201 = 3833401) B3833401
theorem B820315 : Blo 531801 820315 := bstep (se 1 (by rfl) ⟨615236, by rfl⟩ : syracuseStep 820315 = 1230473) B1230473
theorem B6098813 : Blo 531801 6098813 := bstep (se 3 (by rfl) ⟨1143527, by rfl⟩ : syracuseStep 6098813 = 2287055) B2287055
theorem B3412313 : Blo 531801 3412313 := bstep (se 2 (by rfl) ⟨1279617, by rfl⟩ : syracuseStep 3412313 = 2559235) B2559235
theorem B6100271 : Blo 531801 6100271 := bstep (se 1 (by rfl) ⟨4575203, by rfl⟩ : syracuseStep 6100271 = 9150407) B9150407
theorem B1316407 : Blo 531801 1316407 := bstep (se 1 (by rfl) ⟨987305, by rfl⟩ : syracuseStep 1316407 = 1974611) B1974611
theorem B13016153 : Blo 531801 13016153 := bstep (se 2 (by rfl) ⟨4881057, by rfl⟩ : syracuseStep 13016153 = 9762115) B9762115
theorem B1646561 : Blo 531801 1646561 := bstep (se 2 (by rfl) ⟨617460, by rfl⟩ : syracuseStep 1646561 = 1234921) B1234921
theorem B1351849 : Blo 531801 1351849 := bstep (se 2 (by rfl) ⟨506943, by rfl⟩ : syracuseStep 1351849 = 1013887) B1013887
theorem B1712411 : Blo 531801 1712411 := bstep (se 1 (by rfl) ⟨1284308, by rfl⟩ : syracuseStep 1712411 = 2568617) B2568617
theorem B533147 : Blo 531801 533147 := bstep (se 1 (by rfl) ⟨399860, by rfl⟩ : syracuseStep 533147 = 799721) B799721
theorem B1352639 : Blo 531801 1352639 := bstep (se 1 (by rfl) ⟨1014479, by rfl⟩ : syracuseStep 1352639 = 2028959) B2028959
theorem B533743 : Blo 531801 533743 := bstep (se 1 (by rfl) ⟨400307, by rfl⟩ : syracuseStep 533743 = 800615) B800615
theorem B533919 : Blo 531801 533919 := bstep (se 1 (by rfl) ⟨400439, by rfl⟩ : syracuseStep 533919 = 800879) B800879
theorem B1713575 : Blo 531801 1713575 := bstep (se 1 (by rfl) ⟨1285181, by rfl⟩ : syracuseStep 1713575 = 2570363) B2570363
theorem B535271 : Blo 531801 535271 := bstep (se 1 (by rfl) ⟨401453, by rfl⟩ : syracuseStep 535271 = 802907) B802907
theorem B1354745 : Blo 531801 1354745 := bstep (se 2 (by rfl) ⟨508029, by rfl⟩ : syracuseStep 1354745 = 1016059) B1016059
theorem B797801 : Blo 531801 797801 := bstep (se 2 (by rfl) ⟨299175, by rfl⟩ : syracuseStep 797801 = 598351) B598351
theorem B602023 : Blo 531801 602023 := bstep (se 1 (by rfl) ⟨451517, by rfl⟩ : syracuseStep 602023 = 903035) B903035
theorem B799451 : Blo 531801 799451 := bstep (se 1 (by rfl) ⟨599588, by rfl⟩ : syracuseStep 799451 = 1199177) B1199177
theorem B799871 : Blo 531801 799871 := bstep (se 1 (by rfl) ⟨599903, by rfl⟩ : syracuseStep 799871 = 1199807) B1199807
theorem B964075 : Blo 531801 964075 := bstep (se 1 (by rfl) ⟨723056, by rfl⟩ : syracuseStep 964075 = 1446113) B1446113
theorem B2700863 : Blo 531801 2700863 := bstep (se 1 (by rfl) ⟨2025647, by rfl⟩ : syracuseStep 2700863 = 4051295) B4051295
theorem B1917191 : Blo 531801 1917191 := bstep (se 1 (by rfl) ⟨1437893, by rfl⟩ : syracuseStep 1917191 = 2875787) B2875787
theorem B803231 : Blo 531801 803231 := bstep (se 1 (by rfl) ⟨602423, by rfl⟩ : syracuseStep 803231 = 1204847) B1204847
theorem B9093545 : Blo 531801 9093545 := bstep (se 2 (by rfl) ⟨3410079, by rfl⟩ : syracuseStep 9093545 = 6820159) B6820159
theorem B803369 : Blo 531801 803369 := bstep (se 2 (by rfl) ⟨301263, by rfl⟩ : syracuseStep 803369 = 602527) B602527
theorem B3032549 : Blo 531801 3032549 := bstep (se 4 (by rfl) ⟨284301, by rfl⟩ : syracuseStep 3032549 = 568603) B568603
theorem B1198151 : Blo 531801 1198151 := bstep (se 1 (by rfl) ⟨898613, by rfl⟩ : syracuseStep 1198151 = 1797227) B1797227
theorem B1199231 : Blo 531801 1199231 := bstep (se 1 (by rfl) ⟨899423, by rfl⟩ : syracuseStep 1199231 = 1798847) B1798847
theorem B675535 : Blo 531801 675535 := bstep (se 1 (by rfl) ⟨506651, by rfl⟩ : syracuseStep 675535 = 1013303) B1013303
theorem B3429353 : Blo 531801 3429353 := bstep (se 2 (by rfl) ⟨1286007, by rfl⟩ : syracuseStep 3429353 = 2572015) B2572015
theorem B677423 : Blo 531801 677423 := bstep (se 1 (by rfl) ⟨508067, by rfl⟩ : syracuseStep 677423 = 1016135) B1016135
theorem B2283947 : Blo 531801 2283947 := bstep (se 1 (by rfl) ⟨1712960, by rfl⟩ : syracuseStep 2283947 = 3425921) B3425921
theorem B2021867 : Blo 531801 2021867 := bstep (se 1 (by rfl) ⟨1516400, by rfl⟩ : syracuseStep 2021867 = 3032801) B3032801
theorem B20470319 : Blo 531801 20470319 := bstep (se 1 (by rfl) ⟨15352739, by rfl⟩ : syracuseStep 20470319 = 30705479) B30705479
theorem B1202921 : Blo 531801 1202921 := bstep (se 2 (by rfl) ⟨451095, by rfl⟩ : syracuseStep 1202921 = 902191) B902191
theorem B1202975 : Blo 531801 1202975 := bstep (se 1 (by rfl) ⟨902231, by rfl⟩ : syracuseStep 1202975 = 1804463) B1804463
theorem B2024585 : Blo 531801 2024585 := bstep (se 2 (by rfl) ⟨759219, by rfl⟩ : syracuseStep 2024585 = 1518439) B1518439
theorem B44329193 : Blo 531801 44329193 := bstep (se 2 (by rfl) ⟨16623447, by rfl⟩ : syracuseStep 44329193 = 33246895) B33246895
theorem B1011199 : Blo 531801 1011199 := bstep (se 1 (by rfl) ⟨758399, by rfl⟩ : syracuseStep 1011199 = 1516799) B1516799
theorem B7008767 : Blo 531801 7008767 := bstep (se 1 (by rfl) ⟨5256575, by rfl⟩ : syracuseStep 7008767 = 10513151) B10513151
theorem B8189495 : Blo 531801 8189495 := bstep (se 1 (by rfl) ⟨6142121, by rfl⟩ : syracuseStep 8189495 = 12284243) B12284243
theorem B5208257 : Blo 531801 5208257 := bstep (se 2 (by rfl) ⟨1953096, by rfl⟩ : syracuseStep 5208257 = 3906193) B3906193
theorem B7928765 : Blo 531801 7928765 := bstep (se 3 (by rfl) ⟨1486643, by rfl⟩ : syracuseStep 7928765 = 2973287) B2973287
theorem B49249295 : Blo 531801 49249295 := bstep (se 1 (by rfl) ⟨36936971, by rfl⟩ : syracuseStep 49249295 = 73873943) B73873943
theorem B3407467 : Blo 531801 3407467 := bstep (se 1 (by rfl) ⟨2555600, by rfl⟩ : syracuseStep 3407467 = 5111201) B5111201
theorem B1278127 : Blo 531801 1278127 := bstep (se 1 (by rfl) ⟨958595, by rfl⟩ : syracuseStep 1278127 = 1917191) B1917191
theorem B1802465 : Blo 531801 1802465 := bstep (se 2 (by rfl) ⟨675924, by rfl⟩ : syracuseStep 1802465 = 1351849) B1351849
theorem B6062363 : Blo 531801 6062363 := bstep (se 1 (by rfl) ⟨4546772, by rfl⟩ : syracuseStep 6062363 = 9093545) B9093545
theorem B4065875 : Blo 531801 4065875 := bstep (se 1 (by rfl) ⟨3049406, by rfl⟩ : syracuseStep 4065875 = 6098813) B6098813
theorem B4066847 : Blo 531801 4066847 := bstep (se 1 (by rfl) ⟨3050135, by rfl⟩ : syracuseStep 4066847 = 6100271) B6100271
theorem B1806461 : Blo 531801 1806461 := bstep (se 3 (by rfl) ⟨338711, by rfl⟩ : syracuseStep 1806461 = 677423) B677423
theorem B1347911 : Blo 531801 1347911 := bstep (se 1 (by rfl) ⟨1010933, by rfl⟩ : syracuseStep 1347911 = 2021867) B2021867
theorem B1348265 : Blo 531801 1348265 := bstep (se 2 (by rfl) ⟨505599, by rfl⟩ : syracuseStep 1348265 = 1011199) B1011199
theorem B1349723 : Blo 531801 1349723 := bstep (se 1 (by rfl) ⟨1012292, by rfl⟩ : syracuseStep 1349723 = 2024585) B2024585
theorem B1285433 : Blo 531801 1285433 := bstep (se 2 (by rfl) ⟨482037, by rfl⟩ : syracuseStep 1285433 = 964075) B964075
theorem B531867 : Blo 531801 531867 := bstep (se 1 (by rfl) ⟨398900, by rfl⟩ : syracuseStep 531867 = 797801) B797801
theorem B34709741 : Blo 531801 34709741 := bstep (se 3 (by rfl) ⟨6508076, by rfl⟩ : syracuseStep 34709741 = 13016153) B13016153
theorem B532967 : Blo 531801 532967 := bstep (se 1 (by rfl) ⟨399725, by rfl⟩ : syracuseStep 532967 = 799451) B799451
theorem B533247 : Blo 531801 533247 := bstep (se 1 (by rfl) ⟨399935, by rfl⟩ : syracuseStep 533247 = 799871) B799871
theorem B5285843 : Blo 531801 5285843 := bstep (se 1 (by rfl) ⟨3964382, by rfl⟩ : syracuseStep 5285843 = 7928765) B7928765
theorem B535487 : Blo 531801 535487 := bstep (se 1 (by rfl) ⟨401615, by rfl⟩ : syracuseStep 535487 = 803231) B803231
theorem B535579 : Blo 531801 535579 := bstep (se 1 (by rfl) ⟨401684, by rfl⟩ : syracuseStep 535579 = 803369) B803369
theorem B798767 : Blo 531801 798767 := bstep (se 1 (by rfl) ⟨599075, by rfl⟩ : syracuseStep 798767 = 1198151) B1198151
theorem B1093753 : Blo 531801 1093753 := bstep (se 2 (by rfl) ⟨410157, by rfl⟩ : syracuseStep 1093753 = 820315) B820315
theorem B799487 : Blo 531801 799487 := bstep (se 1 (by rfl) ⟨599615, by rfl⟩ : syracuseStep 799487 = 1199231) B1199231
theorem B2274875 : Blo 531801 2274875 := bstep (se 1 (by rfl) ⟨1706156, by rfl⟩ : syracuseStep 2274875 = 3412313) B3412313
theorem B4569533 : Blo 531801 4569533 := bstep (se 3 (by rfl) ⟨856787, by rfl⟩ : syracuseStep 4569533 = 1713575) B1713575
theorem B1522631 : Blo 531801 1522631 := bstep (se 1 (by rfl) ⟨1141973, by rfl⟩ : syracuseStep 1522631 = 2283947) B2283947
theorem B13646879 : Blo 531801 13646879 := bstep (se 1 (by rfl) ⟨10235159, by rfl⟩ : syracuseStep 13646879 = 20470319) B20470319
theorem B801947 : Blo 531801 801947 := bstep (se 1 (by rfl) ⟨601460, by rfl⟩ : syracuseStep 801947 = 1202921) B1202921
theorem B801983 : Blo 531801 801983 := bstep (se 1 (by rfl) ⟨601487, by rfl⟩ : syracuseStep 801983 = 1202975) B1202975
theorem B900713 : Blo 531801 900713 := bstep (se 2 (by rfl) ⟨337767, by rfl⟩ : syracuseStep 900713 = 675535) B675535
theorem B802697 : Blo 531801 802697 := bstep (se 2 (by rfl) ⟨301011, by rfl⟩ : syracuseStep 802697 = 602023) B602023
theorem B1097707 : Blo 531801 1097707 := bstep (se 1 (by rfl) ⟨823280, by rfl⟩ : syracuseStep 1097707 = 1646561) B1646561
theorem B901759 : Blo 531801 901759 := bstep (se 1 (by rfl) ⟨676319, by rfl⟩ : syracuseStep 901759 = 1352639) B1352639
theorem B903163 : Blo 531801 903163 := bstep (se 1 (by rfl) ⟨677372, by rfl⟩ : syracuseStep 903163 = 1354745) B1354745
theorem B1755209 : Blo 531801 1755209 := bstep (se 2 (by rfl) ⟨658203, by rfl⟩ : syracuseStep 1755209 = 1316407) B1316407
theorem B4672511 : Blo 531801 4672511 := bstep (se 1 (by rfl) ⟨3504383, by rfl⟩ : syracuseStep 4672511 = 7008767) B7008767
theorem B5459663 : Blo 531801 5459663 := bstep (se 1 (by rfl) ⟨4094747, by rfl⟩ : syracuseStep 5459663 = 8189495) B8189495
theorem B4543289 : Blo 531801 4543289 := bstep (se 2 (by rfl) ⟨1703733, by rfl⟩ : syracuseStep 4543289 = 3407467) B3407467
theorem B2021699 : Blo 531801 2021699 := bstep (se 1 (by rfl) ⟨1516274, by rfl⟩ : syracuseStep 2021699 = 3032549) B3032549
theorem B2286235 : Blo 531801 2286235 := bstep (se 1 (by rfl) ⟨1714676, by rfl⟩ : syracuseStep 2286235 = 3429353) B3429353
theorem B1141607 : Blo 531801 1141607 := bstep (se 1 (by rfl) ⟨856205, by rfl⟩ : syracuseStep 1141607 = 1712411) B1712411
theorem B13888685 : Blo 531801 13888685 := bstep (se 3 (by rfl) ⟨2604128, by rfl⟩ : syracuseStep 13888685 = 5208257) B5208257
theorem B29552795 : Blo 531801 29552795 := bstep (se 1 (by rfl) ⟨22164596, by rfl⟩ : syracuseStep 29552795 = 44329193) B44329193
theorem B1800575 : Blo 531801 1800575 := bstep (se 1 (by rfl) ⟨1350431, by rfl⟩ : syracuseStep 1800575 = 2700863) B2700863
theorem B32832863 : Blo 531801 32832863 := bstep (se 1 (by rfl) ⟨24624647, by rfl⟩ : syracuseStep 32832863 = 49249295) B49249295
theorem B1704169 : Blo 531801 1704169 := bstep (se 2 (by rfl) ⟨639063, by rfl⟩ : syracuseStep 1704169 = 1278127) B1278127
theorem B3048313 : Blo 531801 3048313 := bstep (se 2 (by rfl) ⟨1143117, by rfl⟩ : syracuseStep 3048313 = 2286235) B2286235
theorem B3115007 : Blo 531801 3115007 := bstep (se 1 (by rfl) ⟨2336255, by rfl⟩ : syracuseStep 3115007 = 4672511) B4672511
theorem B1347799 : Blo 531801 1347799 := bstep (se 1 (by rfl) ⟨1010849, by rfl⟩ : syracuseStep 1347799 = 2021699) B2021699
theorem B856955 : Blo 531801 856955 := bstep (se 1 (by rfl) ⟨642716, by rfl⟩ : syracuseStep 856955 = 1285433) B1285433
theorem B23139827 : Blo 531801 23139827 := bstep (se 1 (by rfl) ⟨17354870, by rfl⟩ : syracuseStep 23139827 = 34709741) B34709741
theorem B761071 : Blo 531801 761071 := bstep (se 1 (by rfl) ⟨570803, by rfl⟩ : syracuseStep 761071 = 1141607) B1141607
theorem B532511 : Blo 531801 532511 := bstep (se 1 (by rfl) ⟨399383, by rfl⟩ : syracuseStep 532511 = 798767) B798767
theorem B19701863 : Blo 531801 19701863 := bstep (se 1 (by rfl) ⟨14776397, by rfl⟩ : syracuseStep 19701863 = 29552795) B29552795
theorem B532991 : Blo 531801 532991 := bstep (se 1 (by rfl) ⟨399743, by rfl⟩ : syracuseStep 532991 = 799487) B799487
theorem B1516583 : Blo 531801 1516583 := bstep (se 1 (by rfl) ⟨1137437, by rfl⟩ : syracuseStep 1516583 = 2274875) B2274875
theorem B14559101 : Blo 531801 14559101 := bstep (se 3 (by rfl) ⟨2729831, by rfl⟩ : syracuseStep 14559101 = 5459663) B5459663
theorem B534631 : Blo 531801 534631 := bstep (se 1 (by rfl) ⟨400973, by rfl⟩ : syracuseStep 534631 = 801947) B801947
theorem B534655 : Blo 531801 534655 := bstep (se 1 (by rfl) ⟨400991, by rfl⟩ : syracuseStep 534655 = 801983) B801983
theorem B600475 : Blo 531801 600475 := bstep (se 1 (by rfl) ⟨450356, by rfl⟩ : syracuseStep 600475 = 900713) B900713
theorem B535131 : Blo 531801 535131 := bstep (se 1 (by rfl) ⟨401348, by rfl⟩ : syracuseStep 535131 = 802697) B802697
theorem B4041575 : Blo 531801 4041575 := bstep (se 1 (by rfl) ⟨3031181, by rfl⟩ : syracuseStep 4041575 = 6062363) B6062363
theorem B898607 : Blo 531801 898607 := bstep (se 1 (by rfl) ⟨673955, by rfl⟩ : syracuseStep 898607 = 1347911) B1347911
theorem B898843 : Blo 531801 898843 := bstep (se 1 (by rfl) ⟨674132, by rfl⟩ : syracuseStep 898843 = 1348265) B1348265
theorem B3028859 : Blo 531801 3028859 := bstep (se 1 (by rfl) ⟨2271644, by rfl⟩ : syracuseStep 3028859 = 4543289) B4543289
theorem B899815 : Blo 531801 899815 := bstep (se 1 (by rfl) ⟨674861, by rfl⟩ : syracuseStep 899815 = 1349723) B1349723
theorem B1458337 : Blo 531801 1458337 := bstep (se 2 (by rfl) ⟨546876, by rfl⟩ : syracuseStep 1458337 = 1093753) B1093753
theorem B3523895 : Blo 531801 3523895 := bstep (se 1 (by rfl) ⟨2642921, by rfl⟩ : syracuseStep 3523895 = 5285843) B5285843
theorem B9259123 : Blo 531801 9259123 := bstep (se 1 (by rfl) ⟨6944342, by rfl⟩ : syracuseStep 9259123 = 13888685) B13888685
theorem B1200383 : Blo 531801 1200383 := bstep (se 1 (by rfl) ⟨900287, by rfl⟩ : syracuseStep 1200383 = 1800575) B1800575
theorem B9097919 : Blo 531801 9097919 := bstep (se 1 (by rfl) ⟨6823439, by rfl⟩ : syracuseStep 9097919 = 13646879) B13646879
theorem B1463609 : Blo 531801 1463609 := bstep (se 2 (by rfl) ⟨548853, by rfl⟩ : syracuseStep 1463609 = 1097707) B1097707
theorem B1201643 : Blo 531801 1201643 := bstep (se 1 (by rfl) ⟨901232, by rfl⟩ : syracuseStep 1201643 = 1802465) B1802465
theorem B1202345 : Blo 531801 1202345 := bstep (se 2 (by rfl) ⟨450879, by rfl⟩ : syracuseStep 1202345 = 901759) B901759
theorem B2710583 : Blo 531801 2710583 := bstep (se 1 (by rfl) ⟨2032937, by rfl⟩ : syracuseStep 2710583 = 4065875) B4065875
theorem B2711231 : Blo 531801 2711231 := bstep (se 1 (by rfl) ⟨2033423, by rfl⟩ : syracuseStep 2711231 = 4066847) B4066847
theorem B1204217 : Blo 531801 1204217 := bstep (se 2 (by rfl) ⟨451581, by rfl⟩ : syracuseStep 1204217 = 903163) B903163
theorem B1204307 : Blo 531801 1204307 := bstep (se 1 (by rfl) ⟨903230, by rfl⟩ : syracuseStep 1204307 = 1806461) B1806461
theorem B4680557 : Blo 531801 4680557 := bstep (se 3 (by rfl) ⟨877604, by rfl⟩ : syracuseStep 4680557 = 1755209) B1755209
theorem B3046355 : Blo 531801 3046355 := bstep (se 1 (by rfl) ⟨2284766, by rfl⟩ : syracuseStep 3046355 = 4569533) B4569533
theorem B1015087 : Blo 531801 1015087 := bstep (se 1 (by rfl) ⟨761315, by rfl⟩ : syracuseStep 1015087 = 1522631) B1522631
theorem B21888575 : Blo 531801 21888575 := bstep (se 1 (by rfl) ⟨16416431, by rfl⟩ : syracuseStep 21888575 = 32832863) B32832863
theorem B4064417 : Blo 531801 4064417 := bstep (se 2 (by rfl) ⟨1524156, by rfl⟩ : syracuseStep 4064417 = 3048313) B3048313
theorem B6065279 : Blo 531801 6065279 := bstep (se 1 (by rfl) ⟨4548959, by rfl⟩ : syracuseStep 6065279 = 9097919) B9097919
theorem B1807055 : Blo 531801 1807055 := bstep (se 1 (by rfl) ⟨1355291, by rfl⟩ : syracuseStep 1807055 = 2710583) B2710583
theorem B1807487 : Blo 531801 1807487 := bstep (se 1 (by rfl) ⟨1355615, by rfl⟩ : syracuseStep 1807487 = 2711231) B2711231
theorem B9706067 : Blo 531801 9706067 := bstep (se 1 (by rfl) ⟨7279550, by rfl⟩ : syracuseStep 9706067 = 14559101) B14559101
theorem B2694383 : Blo 531801 2694383 := bstep (se 1 (by rfl) ⟨2020787, by rfl⟩ : syracuseStep 2694383 = 4041575) B4041575
theorem B3120371 : Blo 531801 3120371 := bstep (se 1 (by rfl) ⟨2340278, by rfl⟩ : syracuseStep 3120371 = 4680557) B4680557
theorem B599071 : Blo 531801 599071 := bstep (se 1 (by rfl) ⟨449303, by rfl⟩ : syracuseStep 599071 = 898607) B898607
theorem B1353449 : Blo 531801 1353449 := bstep (se 2 (by rfl) ⟨507543, by rfl⟩ : syracuseStep 1353449 = 1015087) B1015087
theorem B14592383 : Blo 531801 14592383 := bstep (se 1 (by rfl) ⟨10944287, by rfl⟩ : syracuseStep 14592383 = 21888575) B21888575
theorem B1944449 : Blo 531801 1944449 := bstep (se 2 (by rfl) ⟨729168, by rfl⟩ : syracuseStep 1944449 = 1458337) B1458337
theorem B2272225 : Blo 531801 2272225 := bstep (se 2 (by rfl) ⟨852084, by rfl⟩ : syracuseStep 2272225 = 1704169) B1704169
theorem B2076671 : Blo 531801 2076671 := bstep (se 1 (by rfl) ⟨1557503, by rfl⟩ : syracuseStep 2076671 = 3115007) B3115007
theorem B800255 : Blo 531801 800255 := bstep (se 1 (by rfl) ⟨600191, by rfl⟩ : syracuseStep 800255 = 1200383) B1200383
theorem B800633 : Blo 531801 800633 := bstep (se 2 (by rfl) ⟨300237, by rfl⟩ : syracuseStep 800633 = 600475) B600475
theorem B571303 : Blo 531801 571303 := bstep (se 1 (by rfl) ⟨428477, by rfl⟩ : syracuseStep 571303 = 856955) B856955
theorem B801095 : Blo 531801 801095 := bstep (se 1 (by rfl) ⟨600821, by rfl⟩ : syracuseStep 801095 = 1201643) B1201643
theorem B801563 : Blo 531801 801563 := bstep (se 1 (by rfl) ⟨601172, by rfl⟩ : syracuseStep 801563 = 1202345) B1202345
theorem B802811 : Blo 531801 802811 := bstep (se 1 (by rfl) ⟨602108, by rfl⟩ : syracuseStep 802811 = 1204217) B1204217
theorem B802871 : Blo 531801 802871 := bstep (se 1 (by rfl) ⟨602153, by rfl⟩ : syracuseStep 802871 = 1204307) B1204307
theorem B1198457 : Blo 531801 1198457 := bstep (se 2 (by rfl) ⟨449421, by rfl⟩ : syracuseStep 1198457 = 898843) B898843
theorem B1199753 : Blo 531801 1199753 := bstep (se 2 (by rfl) ⟨449907, by rfl⟩ : syracuseStep 1199753 = 899815) B899815
theorem B2019239 : Blo 531801 2019239 := bstep (se 1 (by rfl) ⟨1514429, by rfl⟩ : syracuseStep 2019239 = 3028859) B3028859
theorem B2349263 : Blo 531801 2349263 := bstep (se 1 (by rfl) ⟨1761947, by rfl⟩ : syracuseStep 2349263 = 3523895) B3523895
theorem B12345497 : Blo 531801 12345497 := bstep (se 2 (by rfl) ⟨4629561, by rfl⟩ : syracuseStep 12345497 = 9259123) B9259123
theorem B975739 : Blo 531801 975739 := bstep (se 1 (by rfl) ⟨731804, by rfl⟩ : syracuseStep 975739 = 1463609) B1463609
theorem B15426551 : Blo 531801 15426551 := bstep (se 1 (by rfl) ⟨11569913, by rfl⟩ : syracuseStep 15426551 = 23139827) B23139827
theorem B13134575 : Blo 531801 13134575 := bstep (se 1 (by rfl) ⟨9850931, by rfl⟩ : syracuseStep 13134575 = 19701863) B19701863
theorem B1797065 : Blo 531801 1797065 := bstep (se 2 (by rfl) ⟨673899, by rfl⟩ : syracuseStep 1797065 = 1347799) B1347799
theorem B1011055 : Blo 531801 1011055 := bstep (se 1 (by rfl) ⟨758291, by rfl⟩ : syracuseStep 1011055 = 1516583) B1516583
theorem B1014761 : Blo 531801 1014761 := bstep (se 2 (by rfl) ⟨380535, by rfl⟩ : syracuseStep 1014761 = 761071) B761071
theorem B2030903 : Blo 531801 2030903 := bstep (se 1 (by rfl) ⟨1523177, by rfl⟩ : syracuseStep 2030903 = 3046355) B3046355
theorem B1346159 : Blo 531801 1346159 := bstep (se 1 (by rfl) ⟨1009619, by rfl⟩ : syracuseStep 1346159 = 2019239) B2019239
theorem B1348073 : Blo 531801 1348073 := bstep (se 2 (by rfl) ⟨505527, by rfl⟩ : syracuseStep 1348073 = 1011055) B1011055
theorem B8230331 : Blo 531801 8230331 := bstep (se 1 (by rfl) ⟨6172748, by rfl⟩ : syracuseStep 8230331 = 12345497) B12345497
theorem B8756383 : Blo 531801 8756383 := bstep (se 1 (by rfl) ⟨6567287, by rfl⟩ : syracuseStep 8756383 = 13134575) B13134575
theorem B761737 : Blo 531801 761737 := bstep (se 2 (by rfl) ⟨285651, by rfl⟩ : syracuseStep 761737 = 571303) B571303
theorem B1384447 : Blo 531801 1384447 := bstep (se 1 (by rfl) ⟨1038335, by rfl⟩ : syracuseStep 1384447 = 2076671) B2076671
theorem B533503 : Blo 531801 533503 := bstep (se 1 (by rfl) ⟨400127, by rfl⟩ : syracuseStep 533503 = 800255) B800255
theorem B533755 : Blo 531801 533755 := bstep (se 1 (by rfl) ⟨400316, by rfl⟩ : syracuseStep 533755 = 800633) B800633
theorem B534063 : Blo 531801 534063 := bstep (se 1 (by rfl) ⟨400547, by rfl⟩ : syracuseStep 534063 = 801095) B801095
theorem B534375 : Blo 531801 534375 := bstep (se 1 (by rfl) ⟨400781, by rfl⟩ : syracuseStep 534375 = 801563) B801563
theorem B1353935 : Blo 531801 1353935 := bstep (se 1 (by rfl) ⟨1015451, by rfl⟩ : syracuseStep 1353935 = 2030903) B2030903
theorem B535207 : Blo 531801 535207 := bstep (se 1 (by rfl) ⟨401405, by rfl⟩ : syracuseStep 535207 = 802811) B802811
theorem B535247 : Blo 531801 535247 := bstep (se 1 (by rfl) ⟨401435, by rfl⟩ : syracuseStep 535247 = 802871) B802871
theorem B798761 : Blo 531801 798761 := bstep (se 2 (by rfl) ⟨299535, by rfl⟩ : syracuseStep 798761 = 599071) B599071
theorem B798971 : Blo 531801 798971 := bstep (se 1 (by rfl) ⟨599228, by rfl⟩ : syracuseStep 798971 = 1198457) B1198457
theorem B4043519 : Blo 531801 4043519 := bstep (se 1 (by rfl) ⟨3032639, by rfl⟩ : syracuseStep 4043519 = 6065279) B6065279
theorem B799835 : Blo 531801 799835 := bstep (se 1 (by rfl) ⟨599876, by rfl⟩ : syracuseStep 799835 = 1199753) B1199753
theorem B3029633 : Blo 531801 3029633 := bstep (se 2 (by rfl) ⟨1136112, by rfl⟩ : syracuseStep 3029633 = 2272225) B2272225
theorem B6470711 : Blo 531801 6470711 := bstep (se 1 (by rfl) ⟨4853033, by rfl⟩ : syracuseStep 6470711 = 9706067) B9706067
theorem B2080247 : Blo 531801 2080247 := bstep (se 1 (by rfl) ⟨1560185, by rfl⟩ : syracuseStep 2080247 = 3120371) B3120371
theorem B902299 : Blo 531801 902299 := bstep (se 1 (by rfl) ⟨676724, by rfl⟩ : syracuseStep 902299 = 1353449) B1353449
theorem B1296299 : Blo 531801 1296299 := bstep (se 1 (by rfl) ⟨972224, by rfl⟩ : syracuseStep 1296299 = 1944449) B1944449
theorem B1198043 : Blo 531801 1198043 := bstep (se 1 (by rfl) ⟨898532, by rfl⟩ : syracuseStep 1198043 = 1797065) B1797065
theorem B676507 : Blo 531801 676507 := bstep (se 1 (by rfl) ⟨507380, by rfl⟩ : syracuseStep 676507 = 1014761) B1014761
theorem B2709611 : Blo 531801 2709611 := bstep (se 1 (by rfl) ⟨2032208, by rfl⟩ : syracuseStep 2709611 = 4064417) B4064417
theorem B1300985 : Blo 531801 1300985 := bstep (se 2 (by rfl) ⟨487869, by rfl⟩ : syracuseStep 1300985 = 975739) B975739
theorem B1204703 : Blo 531801 1204703 := bstep (se 1 (by rfl) ⟨903527, by rfl⟩ : syracuseStep 1204703 = 1807055) B1807055
theorem B1204991 : Blo 531801 1204991 := bstep (se 1 (by rfl) ⟨903743, by rfl⟩ : syracuseStep 1204991 = 1807487) B1807487
theorem B1566175 : Blo 531801 1566175 := bstep (se 1 (by rfl) ⟨1174631, by rfl⟩ : syracuseStep 1566175 = 2349263) B2349263
theorem B1796255 : Blo 531801 1796255 := bstep (se 1 (by rfl) ⟨1347191, by rfl⟩ : syracuseStep 1796255 = 2694383) B2694383
theorem B10284367 : Blo 531801 10284367 := bstep (se 1 (by rfl) ⟨7713275, by rfl⟩ : syracuseStep 10284367 = 15426551) B15426551
theorem B9728255 : Blo 531801 9728255 := bstep (se 1 (by rfl) ⟨7296191, by rfl⟩ : syracuseStep 9728255 = 14592383) B14592383
theorem B1806407 : Blo 531801 1806407 := bstep (se 1 (by rfl) ⟨1354805, by rfl⟩ : syracuseStep 1806407 = 2709611) B2709611
theorem B532507 : Blo 531801 532507 := bstep (se 1 (by rfl) ⟨399380, by rfl⟩ : syracuseStep 532507 = 798761) B798761
theorem B532647 : Blo 531801 532647 := bstep (se 1 (by rfl) ⟨399485, by rfl⟩ : syracuseStep 532647 = 798971) B798971
theorem B2695679 : Blo 531801 2695679 := bstep (se 1 (by rfl) ⟨2021759, by rfl⟩ : syracuseStep 2695679 = 4043519) B4043519
theorem B533223 : Blo 531801 533223 := bstep (se 1 (by rfl) ⟨399917, by rfl⟩ : syracuseStep 533223 = 799835) B799835
theorem B5547325 : Blo 531801 5547325 := bstep (se 3 (by rfl) ⟨1040123, by rfl⟩ : syracuseStep 5547325 = 2080247) B2080247
theorem B11675177 : Blo 531801 11675177 := bstep (se 2 (by rfl) ⟨4378191, by rfl⟩ : syracuseStep 11675177 = 8756383) B8756383
theorem B1845929 : Blo 531801 1845929 := bstep (se 2 (by rfl) ⟨692223, by rfl⟩ : syracuseStep 1845929 = 1384447) B1384447
theorem B864199 : Blo 531801 864199 := bstep (se 1 (by rfl) ⟨648149, by rfl⟩ : syracuseStep 864199 = 1296299) B1296299
theorem B798695 : Blo 531801 798695 := bstep (se 1 (by rfl) ⟨599021, by rfl⟩ : syracuseStep 798695 = 1198043) B1198043
theorem B897439 : Blo 531801 897439 := bstep (se 1 (by rfl) ⟨673079, by rfl⟩ : syracuseStep 897439 = 1346159) B1346159
theorem B898715 : Blo 531801 898715 := bstep (se 1 (by rfl) ⟨674036, by rfl⟩ : syracuseStep 898715 = 1348073) B1348073
theorem B5486887 : Blo 531801 5486887 := bstep (se 1 (by rfl) ⟨4115165, by rfl⟩ : syracuseStep 5486887 = 8230331) B8230331
theorem B867323 : Blo 531801 867323 := bstep (se 1 (by rfl) ⟨650492, by rfl⟩ : syracuseStep 867323 = 1300985) B1300985
theorem B13712489 : Blo 531801 13712489 := bstep (se 2 (by rfl) ⟨5142183, by rfl⟩ : syracuseStep 13712489 = 10284367) B10284367
theorem B803135 : Blo 531801 803135 := bstep (se 1 (by rfl) ⟨602351, by rfl⟩ : syracuseStep 803135 = 1204703) B1204703
theorem B803327 : Blo 531801 803327 := bstep (se 1 (by rfl) ⟨602495, by rfl⟩ : syracuseStep 803327 = 1204991) B1204991
theorem B902009 : Blo 531801 902009 := bstep (se 2 (by rfl) ⟨338253, by rfl⟩ : syracuseStep 902009 = 676507) B676507
theorem B1197503 : Blo 531801 1197503 := bstep (se 1 (by rfl) ⟨898127, by rfl⟩ : syracuseStep 1197503 = 1796255) B1796255
theorem B902623 : Blo 531801 902623 := bstep (se 1 (by rfl) ⟨676967, by rfl⟩ : syracuseStep 902623 = 1353935) B1353935
theorem B2019755 : Blo 531801 2019755 := bstep (se 1 (by rfl) ⟨1514816, by rfl⟩ : syracuseStep 2019755 = 3029633) B3029633
theorem B4313807 : Blo 531801 4313807 := bstep (se 1 (by rfl) ⟨3235355, by rfl⟩ : syracuseStep 4313807 = 6470711) B6470711
theorem B1203065 : Blo 531801 1203065 := bstep (se 2 (by rfl) ⟨451149, by rfl⟩ : syracuseStep 1203065 = 902299) B902299
theorem B2088233 : Blo 531801 2088233 := bstep (se 2 (by rfl) ⟨783087, by rfl⟩ : syracuseStep 2088233 = 1566175) B1566175
theorem B6485503 : Blo 531801 6485503 := bstep (se 1 (by rfl) ⟨4864127, by rfl⟩ : syracuseStep 6485503 = 9728255) B9728255
theorem B1015649 : Blo 531801 1015649 := bstep (se 2 (by rfl) ⟨380868, by rfl⟩ : syracuseStep 1015649 = 761737) B761737
theorem B1346503 : Blo 531801 1346503 := bstep (se 1 (by rfl) ⟨1009877, by rfl⟩ : syracuseStep 1346503 = 2019755) B2019755
theorem B1152265 : Blo 531801 1152265 := bstep (se 2 (by rfl) ⟨432099, by rfl⟩ : syracuseStep 1152265 = 864199) B864199
theorem B4922477 : Blo 531801 4922477 := bstep (se 3 (by rfl) ⟨922964, by rfl⟩ : syracuseStep 4922477 = 1845929) B1845929
theorem B532463 : Blo 531801 532463 := bstep (se 1 (by rfl) ⟨399347, by rfl⟩ : syracuseStep 532463 = 798695) B798695
theorem B7315849 : Blo 531801 7315849 := bstep (se 2 (by rfl) ⟨2743443, by rfl⟩ : syracuseStep 7315849 = 5486887) B5486887
theorem B599143 : Blo 531801 599143 := bstep (se 1 (by rfl) ⟨449357, by rfl⟩ : syracuseStep 599143 = 898715) B898715
theorem B535423 : Blo 531801 535423 := bstep (se 1 (by rfl) ⟨401567, by rfl⟩ : syracuseStep 535423 = 803135) B803135
theorem B535551 : Blo 531801 535551 := bstep (se 1 (by rfl) ⟨401663, by rfl⟩ : syracuseStep 535551 = 803327) B803327
theorem B601339 : Blo 531801 601339 := bstep (se 1 (by rfl) ⟨451004, by rfl⟩ : syracuseStep 601339 = 902009) B902009
theorem B798335 : Blo 531801 798335 := bstep (se 1 (by rfl) ⟨598751, by rfl⟩ : syracuseStep 798335 = 1197503) B1197503
theorem B802043 : Blo 531801 802043 := bstep (se 1 (by rfl) ⟨601532, by rfl⟩ : syracuseStep 802043 = 1203065) B1203065
theorem B1392155 : Blo 531801 1392155 := bstep (se 1 (by rfl) ⟨1044116, by rfl⟩ : syracuseStep 1392155 = 2088233) B2088233
theorem B1196585 : Blo 531801 1196585 := bstep (se 2 (by rfl) ⟨448719, by rfl⟩ : syracuseStep 1196585 = 897439) B897439
theorem B7783451 : Blo 531801 7783451 := bstep (se 1 (by rfl) ⟨5837588, by rfl⟩ : syracuseStep 7783451 = 11675177) B11675177
theorem B578215 : Blo 531801 578215 := bstep (se 1 (by rfl) ⟨433661, by rfl⟩ : syracuseStep 578215 = 867323) B867323
theorem B677099 : Blo 531801 677099 := bstep (se 1 (by rfl) ⟨507824, by rfl⟩ : syracuseStep 677099 = 1015649) B1015649
theorem B7396433 : Blo 531801 7396433 := bstep (se 2 (by rfl) ⟨2773662, by rfl⟩ : syracuseStep 7396433 = 5547325) B5547325
theorem B1203497 : Blo 531801 1203497 := bstep (se 2 (by rfl) ⟨451311, by rfl⟩ : syracuseStep 1203497 = 902623) B902623
theorem B1204271 : Blo 531801 1204271 := bstep (se 1 (by rfl) ⟨903203, by rfl⟩ : syracuseStep 1204271 = 1806407) B1806407
theorem B2875871 : Blo 531801 2875871 := bstep (se 1 (by rfl) ⟨2156903, by rfl⟩ : syracuseStep 2875871 = 4313807) B4313807
theorem B1797119 : Blo 531801 1797119 := bstep (se 1 (by rfl) ⟨1347839, by rfl⟩ : syracuseStep 1797119 = 2695679) B2695679
theorem B8647337 : Blo 531801 8647337 := bstep (se 2 (by rfl) ⟨3242751, by rfl⟩ : syracuseStep 8647337 = 6485503) B6485503
theorem B9141659 : Blo 531801 9141659 := bstep (se 1 (by rfl) ⟨6856244, by rfl⟩ : syracuseStep 9141659 = 13712489) B13712489
theorem B7668989 : Blo 531801 7668989 := bstep (se 3 (by rfl) ⟨1437935, by rfl⟩ : syracuseStep 7668989 = 2875871) B2875871
theorem B1805597 : Blo 531801 1805597 := bstep (se 3 (by rfl) ⟨338549, by rfl⟩ : syracuseStep 1805597 = 677099) B677099
theorem B3281651 : Blo 531801 3281651 := bstep (se 1 (by rfl) ⟨2461238, by rfl⟩ : syracuseStep 3281651 = 4922477) B4922477
theorem B532223 : Blo 531801 532223 := bstep (se 1 (by rfl) ⟨399167, by rfl⟩ : syracuseStep 532223 = 798335) B798335
theorem B534695 : Blo 531801 534695 := bstep (se 1 (by rfl) ⟨401021, by rfl⟩ : syracuseStep 534695 = 802043) B802043
theorem B928103 : Blo 531801 928103 := bstep (se 1 (by rfl) ⟨696077, by rfl⟩ : syracuseStep 928103 = 1392155) B1392155
theorem B797723 : Blo 531801 797723 := bstep (se 1 (by rfl) ⟨598292, by rfl⟩ : syracuseStep 797723 = 1196585) B1196585
theorem B5188967 : Blo 531801 5188967 := bstep (se 1 (by rfl) ⟨3891725, by rfl⟩ : syracuseStep 5188967 = 7783451) B7783451
theorem B798857 : Blo 531801 798857 := bstep (se 2 (by rfl) ⟨299571, by rfl⟩ : syracuseStep 798857 = 599143) B599143
theorem B801785 : Blo 531801 801785 := bstep (se 2 (by rfl) ⟨300669, by rfl⟩ : syracuseStep 801785 = 601339) B601339
theorem B4930955 : Blo 531801 4930955 := bstep (se 1 (by rfl) ⟨3698216, by rfl⟩ : syracuseStep 4930955 = 7396433) B7396433
theorem B802331 : Blo 531801 802331 := bstep (se 1 (by rfl) ⟨601748, by rfl⟩ : syracuseStep 802331 = 1203497) B1203497
theorem B802847 : Blo 531801 802847 := bstep (se 1 (by rfl) ⟨602135, by rfl⟩ : syracuseStep 802847 = 1204271) B1204271
theorem B770953 : Blo 531801 770953 := bstep (se 2 (by rfl) ⟨289107, by rfl⟩ : syracuseStep 770953 = 578215) B578215
theorem B1198079 : Blo 531801 1198079 := bstep (se 1 (by rfl) ⟨898559, by rfl⟩ : syracuseStep 1198079 = 1797119) B1797119
theorem B9754465 : Blo 531801 9754465 := bstep (se 2 (by rfl) ⟨3657924, by rfl⟩ : syracuseStep 9754465 = 7315849) B7315849
theorem B1795337 : Blo 531801 1795337 := bstep (se 2 (by rfl) ⟨673251, by rfl⟩ : syracuseStep 1795337 = 1346503) B1346503
theorem B1536353 : Blo 531801 1536353 := bstep (se 2 (by rfl) ⟨576132, by rfl⟩ : syracuseStep 1536353 = 1152265) B1152265
theorem B5764891 : Blo 531801 5764891 := bstep (se 1 (by rfl) ⟨4323668, by rfl⟩ : syracuseStep 5764891 = 8647337) B8647337
theorem B6094439 : Blo 531801 6094439 := bstep (se 1 (by rfl) ⟨4570829, by rfl⟩ : syracuseStep 6094439 = 9141659) B9141659
theorem B5112659 : Blo 531801 5112659 := bstep (se 1 (by rfl) ⟨3834494, by rfl⟩ : syracuseStep 5112659 = 7668989) B7668989
theorem B9899765 : Blo 531801 9899765 := bstep (se 5 (by rfl) ⟨464051, by rfl⟩ : syracuseStep 9899765 = 928103) B928103
theorem B531815 : Blo 531801 531815 := bstep (se 1 (by rfl) ⟨398861, by rfl⟩ : syracuseStep 531815 = 797723) B797723
theorem B532571 : Blo 531801 532571 := bstep (se 1 (by rfl) ⟨399428, by rfl⟩ : syracuseStep 532571 = 798857) B798857
theorem B1024235 : Blo 531801 1024235 := bstep (se 1 (by rfl) ⟨768176, by rfl⟩ : syracuseStep 1024235 = 1536353) B1536353
theorem B534523 : Blo 531801 534523 := bstep (se 1 (by rfl) ⟨400892, by rfl⟩ : syracuseStep 534523 = 801785) B801785
theorem B3287303 : Blo 531801 3287303 := bstep (se 1 (by rfl) ⟨2465477, by rfl⟩ : syracuseStep 3287303 = 4930955) B4930955
theorem B534887 : Blo 531801 534887 := bstep (se 1 (by rfl) ⟨401165, by rfl⟩ : syracuseStep 534887 = 802331) B802331
theorem B535231 : Blo 531801 535231 := bstep (se 1 (by rfl) ⟨401423, by rfl⟩ : syracuseStep 535231 = 802847) B802847
theorem B1027937 : Blo 531801 1027937 := bstep (se 2 (by rfl) ⟨385476, by rfl⟩ : syracuseStep 1027937 = 770953) B770953
theorem B798719 : Blo 531801 798719 := bstep (se 1 (by rfl) ⟨599039, by rfl⟩ : syracuseStep 798719 = 1198079) B1198079
theorem B1196891 : Blo 531801 1196891 := bstep (se 1 (by rfl) ⟨897668, by rfl⟩ : syracuseStep 1196891 = 1795337) B1795337
theorem B3459311 : Blo 531801 3459311 := bstep (se 1 (by rfl) ⟨2594483, by rfl⟩ : syracuseStep 3459311 = 5188967) B5188967
theorem B7686521 : Blo 531801 7686521 := bstep (se 2 (by rfl) ⟨2882445, by rfl⟩ : syracuseStep 7686521 = 5764891) B5764891
theorem B1203731 : Blo 531801 1203731 := bstep (se 1 (by rfl) ⟨902798, by rfl⟩ : syracuseStep 1203731 = 1805597) B1805597
theorem B2187767 : Blo 531801 2187767 := bstep (se 1 (by rfl) ⟨1640825, by rfl⟩ : syracuseStep 2187767 = 3281651) B3281651
theorem B13005953 : Blo 531801 13005953 := bstep (se 2 (by rfl) ⟨4877232, by rfl⟩ : syracuseStep 13005953 = 9754465) B9754465
theorem B4062959 : Blo 531801 4062959 := bstep (se 1 (by rfl) ⟨3047219, by rfl⟩ : syracuseStep 4062959 = 6094439) B6094439
theorem B5834045 : Blo 531801 5834045 := bstep (se 3 (by rfl) ⟨1093883, by rfl⟩ : syracuseStep 5834045 = 2187767) B2187767
theorem B13633757 : Blo 531801 13633757 := bstep (se 3 (by rfl) ⟨2556329, by rfl⟩ : syracuseStep 13633757 = 5112659) B5112659
theorem B532479 : Blo 531801 532479 := bstep (se 1 (by rfl) ⟨399359, by rfl⟩ : syracuseStep 532479 = 798719) B798719
theorem B797927 : Blo 531801 797927 := bstep (se 1 (by rfl) ⟨598445, by rfl⟩ : syracuseStep 797927 = 1196891) B1196891
theorem B2306207 : Blo 531801 2306207 := bstep (se 1 (by rfl) ⟨1729655, by rfl⟩ : syracuseStep 2306207 = 3459311) B3459311
theorem B5124347 : Blo 531801 5124347 := bstep (se 1 (by rfl) ⟨3843260, by rfl⟩ : syracuseStep 5124347 = 7686521) B7686521
theorem B6599843 : Blo 531801 6599843 := bstep (se 1 (by rfl) ⟨4949882, by rfl⟩ : syracuseStep 6599843 = 9899765) B9899765
theorem B802487 : Blo 531801 802487 := bstep (se 1 (by rfl) ⟨601865, by rfl⟩ : syracuseStep 802487 = 1203731) B1203731
theorem B8670635 : Blo 531801 8670635 := bstep (se 1 (by rfl) ⟨6502976, by rfl⟩ : syracuseStep 8670635 = 13005953) B13005953
theorem B2708639 : Blo 531801 2708639 := bstep (se 1 (by rfl) ⟨2031479, by rfl⟩ : syracuseStep 2708639 = 4062959) B4062959
theorem B682823 : Blo 531801 682823 := bstep (se 1 (by rfl) ⟨512117, by rfl⟩ : syracuseStep 682823 = 1024235) B1024235
theorem B2191535 : Blo 531801 2191535 := bstep (se 1 (by rfl) ⟨1643651, by rfl⟩ : syracuseStep 2191535 = 3287303) B3287303
theorem B685291 : Blo 531801 685291 := bstep (se 1 (by rfl) ⟨513968, by rfl⟩ : syracuseStep 685291 = 1027937) B1027937
theorem B1805759 : Blo 531801 1805759 := bstep (se 1 (by rfl) ⟨1354319, by rfl⟩ : syracuseStep 1805759 = 2708639) B2708639
theorem B531951 : Blo 531801 531951 := bstep (se 1 (by rfl) ⟨398963, by rfl⟩ : syracuseStep 531951 = 797927) B797927
theorem B3416231 : Blo 531801 3416231 := bstep (se 1 (by rfl) ⟨2562173, by rfl⟩ : syracuseStep 3416231 = 5124347) B5124347
theorem B4399895 : Blo 531801 4399895 := bstep (se 1 (by rfl) ⟨3299921, by rfl⟩ : syracuseStep 4399895 = 6599843) B6599843
theorem B534991 : Blo 531801 534991 := bstep (se 1 (by rfl) ⟨401243, by rfl⟩ : syracuseStep 534991 = 802487) B802487
theorem B9089171 : Blo 531801 9089171 := bstep (se 1 (by rfl) ⟨6816878, by rfl⟩ : syracuseStep 9089171 = 13633757) B13633757
theorem B5780423 : Blo 531801 5780423 := bstep (se 1 (by rfl) ⟨4335317, by rfl⟩ : syracuseStep 5780423 = 8670635) B8670635
theorem B1820861 : Blo 531801 1820861 := bstep (se 3 (by rfl) ⟨341411, by rfl⟩ : syracuseStep 1820861 = 682823) B682823
theorem B1461023 : Blo 531801 1461023 := bstep (se 1 (by rfl) ⟨1095767, by rfl⟩ : syracuseStep 1461023 = 2191535) B2191535
theorem B15557453 : Blo 531801 15557453 := bstep (se 3 (by rfl) ⟨2917022, by rfl⟩ : syracuseStep 15557453 = 5834045) B5834045
theorem B913721 : Blo 531801 913721 := bstep (se 2 (by rfl) ⟨342645, by rfl⟩ : syracuseStep 913721 = 685291) B685291
theorem B1537471 : Blo 531801 1537471 := bstep (se 1 (by rfl) ⟨1153103, by rfl⟩ : syracuseStep 1537471 = 2306207) B2306207
theorem B1213907 : Blo 531801 1213907 := bstep (se 1 (by rfl) ⟨910430, by rfl⟩ : syracuseStep 1213907 = 1820861) B1820861
theorem B2436589 : Blo 531801 2436589 := bstep (se 3 (by rfl) ⟨456860, by rfl⟩ : syracuseStep 2436589 = 913721) B913721
theorem B2277487 : Blo 531801 2277487 := bstep (se 1 (by rfl) ⟨1708115, by rfl⟩ : syracuseStep 2277487 = 3416231) B3416231
theorem B2933263 : Blo 531801 2933263 := bstep (se 1 (by rfl) ⟨2199947, by rfl⟩ : syracuseStep 2933263 = 4399895) B4399895
theorem B10371635 : Blo 531801 10371635 := bstep (se 1 (by rfl) ⟨7778726, by rfl⟩ : syracuseStep 10371635 = 15557453) B15557453
theorem B2049961 : Blo 531801 2049961 := bstep (se 2 (by rfl) ⟨768735, by rfl⟩ : syracuseStep 2049961 = 1537471) B1537471
theorem B3853615 : Blo 531801 3853615 := bstep (se 1 (by rfl) ⟨2890211, by rfl⟩ : syracuseStep 3853615 = 5780423) B5780423
theorem B974015 : Blo 531801 974015 := bstep (se 1 (by rfl) ⟨730511, by rfl⟩ : syracuseStep 974015 = 1461023) B1461023
theorem B1203839 : Blo 531801 1203839 := bstep (se 1 (by rfl) ⟨902879, by rfl⟩ : syracuseStep 1203839 = 1805759) B1805759
theorem B6059447 : Blo 531801 6059447 := bstep (se 1 (by rfl) ⟨4544585, by rfl⟩ : syracuseStep 6059447 = 9089171) B9089171
theorem B6914423 : Blo 531801 6914423 := bstep (se 1 (by rfl) ⟨5185817, by rfl⟩ : syracuseStep 6914423 = 10371635) B10371635
theorem B3248785 : Blo 531801 3248785 := bstep (se 2 (by rfl) ⟨1218294, by rfl⟩ : syracuseStep 3248785 = 2436589) B2436589
theorem B4039631 : Blo 531801 4039631 := bstep (se 1 (by rfl) ⟨3029723, by rfl⟩ : syracuseStep 4039631 = 6059447) B6059447
theorem B3911017 : Blo 531801 3911017 := bstep (se 2 (by rfl) ⟨1466631, by rfl⟩ : syracuseStep 3911017 = 2933263) B2933263
theorem B2733281 : Blo 531801 2733281 := bstep (se 2 (by rfl) ⟨1024980, by rfl⟩ : syracuseStep 2733281 = 2049961) B2049961
theorem B802559 : Blo 531801 802559 := bstep (se 1 (by rfl) ⟨601919, by rfl⟩ : syracuseStep 802559 = 1203839) B1203839
theorem B3036649 : Blo 531801 3036649 := bstep (se 2 (by rfl) ⟨1138743, by rfl⟩ : syracuseStep 3036649 = 2277487) B2277487
theorem B3237085 : Blo 531801 3237085 := bstep (se 3 (by rfl) ⟨606953, by rfl⟩ : syracuseStep 3237085 = 1213907) B1213907
theorem B5138153 : Blo 531801 5138153 := bstep (se 2 (by rfl) ⟨1926807, by rfl⟩ : syracuseStep 5138153 = 3853615) B3853615
theorem B649343 : Blo 531801 649343 := bstep (se 1 (by rfl) ⟨487007, by rfl⟩ : syracuseStep 649343 = 974015) B974015
theorem B5214689 : Blo 531801 5214689 := bstep (se 2 (by rfl) ⟨1955508, by rfl⟩ : syracuseStep 5214689 = 3911017) B3911017
theorem B2693087 : Blo 531801 2693087 := bstep (se 1 (by rfl) ⟨2019815, by rfl⟩ : syracuseStep 2693087 = 4039631) B4039631
theorem B4331713 : Blo 531801 4331713 := bstep (se 2 (by rfl) ⟨1624392, by rfl⟩ : syracuseStep 4331713 = 3248785) B3248785
theorem B535039 : Blo 531801 535039 := bstep (se 1 (by rfl) ⟨401279, by rfl⟩ : syracuseStep 535039 = 802559) B802559
theorem B3425435 : Blo 531801 3425435 := bstep (se 1 (by rfl) ⟨2569076, by rfl⟩ : syracuseStep 3425435 = 5138153) B5138153
theorem B4048865 : Blo 531801 4048865 := bstep (se 2 (by rfl) ⟨1518324, by rfl⟩ : syracuseStep 4048865 = 3036649) B3036649
theorem B1822187 : Blo 531801 1822187 := bstep (se 1 (by rfl) ⟨1366640, by rfl⟩ : syracuseStep 1822187 = 2733281) B2733281
theorem B18438461 : Blo 531801 18438461 := bstep (se 3 (by rfl) ⟨3457211, by rfl⟩ : syracuseStep 18438461 = 6914423) B6914423
theorem B4316113 : Blo 531801 4316113 := bstep (se 2 (by rfl) ⟨1618542, by rfl⟩ : syracuseStep 4316113 = 3237085) B3237085
theorem B1731581 : Blo 531801 1731581 := bstep (se 3 (by rfl) ⟨324671, by rfl⟩ : syracuseStep 1731581 = 649343) B649343
theorem B3476459 : Blo 531801 3476459 := bstep (se 1 (by rfl) ⟨2607344, by rfl⟩ : syracuseStep 3476459 = 5214689) B5214689
theorem B12292307 : Blo 531801 12292307 := bstep (se 1 (by rfl) ⟨9219230, by rfl⟩ : syracuseStep 12292307 = 18438461) B18438461
theorem B1154387 : Blo 531801 1154387 := bstep (se 1 (by rfl) ⟨865790, by rfl⟩ : syracuseStep 1154387 = 1731581) B1731581
theorem B5775617 : Blo 531801 5775617 := bstep (se 2 (by rfl) ⟨2165856, by rfl⟩ : syracuseStep 5775617 = 4331713) B4331713
theorem B4859165 : Blo 531801 4859165 := bstep (se 3 (by rfl) ⟨911093, by rfl⟩ : syracuseStep 4859165 = 1822187) B1822187
theorem B2699243 : Blo 531801 2699243 := bstep (se 1 (by rfl) ⟨2024432, by rfl⟩ : syracuseStep 2699243 = 4048865) B4048865
theorem B5754817 : Blo 531801 5754817 := bstep (se 2 (by rfl) ⟨2158056, by rfl⟩ : syracuseStep 5754817 = 4316113) B4316113
theorem B2283623 : Blo 531801 2283623 := bstep (se 1 (by rfl) ⟨1712717, by rfl⟩ : syracuseStep 2283623 = 3425435) B3425435
theorem B1795391 : Blo 531801 1795391 := bstep (se 1 (by rfl) ⟨1346543, by rfl⟩ : syracuseStep 1795391 = 2693087) B2693087
theorem B8194871 : Blo 531801 8194871 := bstep (se 1 (by rfl) ⟨6146153, by rfl⟩ : syracuseStep 8194871 = 12292307) B12292307
theorem B7673089 : Blo 531801 7673089 := bstep (se 2 (by rfl) ⟨2877408, by rfl⟩ : syracuseStep 7673089 = 5754817) B5754817
theorem B1522415 : Blo 531801 1522415 := bstep (se 1 (by rfl) ⟨1141811, by rfl⟩ : syracuseStep 1522415 = 2283623) B2283623
theorem B769591 : Blo 531801 769591 := bstep (se 1 (by rfl) ⟨577193, by rfl⟩ : syracuseStep 769591 = 1154387) B1154387
theorem B3850411 : Blo 531801 3850411 := bstep (se 1 (by rfl) ⟨2887808, by rfl⟩ : syracuseStep 3850411 = 5775617) B5775617
theorem B1196927 : Blo 531801 1196927 := bstep (se 1 (by rfl) ⟨897695, by rfl⟩ : syracuseStep 1196927 = 1795391) B1795391
theorem B3239443 : Blo 531801 3239443 := bstep (se 1 (by rfl) ⟨2429582, by rfl⟩ : syracuseStep 3239443 = 4859165) B4859165
theorem B9270557 : Blo 531801 9270557 := bstep (se 3 (by rfl) ⟨1738229, by rfl⟩ : syracuseStep 9270557 = 3476459) B3476459
theorem B1799495 : Blo 531801 1799495 := bstep (se 1 (by rfl) ⟨1349621, by rfl⟩ : syracuseStep 1799495 = 2699243) B2699243
theorem B10230785 : Blo 531801 10230785 := bstep (se 2 (by rfl) ⟨3836544, by rfl⟩ : syracuseStep 10230785 = 7673089) B7673089
theorem B1026121 : Blo 531801 1026121 := bstep (se 2 (by rfl) ⟨384795, by rfl⟩ : syracuseStep 1026121 = 769591) B769591
theorem B797951 : Blo 531801 797951 := bstep (se 1 (by rfl) ⟨598463, by rfl⟩ : syracuseStep 797951 = 1196927) B1196927
theorem B6180371 : Blo 531801 6180371 := bstep (se 1 (by rfl) ⟨4635278, by rfl⟩ : syracuseStep 6180371 = 9270557) B9270557
theorem B1199663 : Blo 531801 1199663 := bstep (se 1 (by rfl) ⟨899747, by rfl⟩ : syracuseStep 1199663 = 1799495) B1799495
theorem B5133881 : Blo 531801 5133881 := bstep (se 2 (by rfl) ⟨1925205, by rfl⟩ : syracuseStep 5133881 = 3850411) B3850411
theorem B5463247 : Blo 531801 5463247 := bstep (se 1 (by rfl) ⟨4097435, by rfl⟩ : syracuseStep 5463247 = 8194871) B8194871
theorem B4319257 : Blo 531801 4319257 := bstep (se 2 (by rfl) ⟨1619721, by rfl⟩ : syracuseStep 4319257 = 3239443) B3239443
theorem B1014943 : Blo 531801 1014943 := bstep (se 1 (by rfl) ⟨761207, by rfl⟩ : syracuseStep 1014943 = 1522415) B1522415
theorem B6820523 : Blo 531801 6820523 := bstep (se 1 (by rfl) ⟨5115392, by rfl⟩ : syracuseStep 6820523 = 10230785) B10230785
theorem B531967 : Blo 531801 531967 := bstep (se 1 (by rfl) ⟨398975, by rfl⟩ : syracuseStep 531967 = 797951) B797951
theorem B1353257 : Blo 531801 1353257 := bstep (se 2 (by rfl) ⟨507471, by rfl⟩ : syracuseStep 1353257 = 1014943) B1014943
theorem B7284329 : Blo 531801 7284329 := bstep (se 2 (by rfl) ⟨2731623, by rfl⟩ : syracuseStep 7284329 = 5463247) B5463247
theorem B799775 : Blo 531801 799775 := bstep (se 1 (by rfl) ⟨599831, by rfl⟩ : syracuseStep 799775 = 1199663) B1199663
theorem B3422587 : Blo 531801 3422587 := bstep (se 1 (by rfl) ⟨2566940, by rfl⟩ : syracuseStep 3422587 = 5133881) B5133881
theorem B4120247 : Blo 531801 4120247 := bstep (se 1 (by rfl) ⟨3090185, by rfl⟩ : syracuseStep 4120247 = 6180371) B6180371
theorem B5759009 : Blo 531801 5759009 := bstep (se 2 (by rfl) ⟨2159628, by rfl⟩ : syracuseStep 5759009 = 4319257) B4319257
theorem B1368161 : Blo 531801 1368161 := bstep (se 2 (by rfl) ⟨513060, by rfl⟩ : syracuseStep 1368161 = 1026121) B1026121
theorem B3839339 : Blo 531801 3839339 := bstep (se 1 (by rfl) ⟨2879504, by rfl⟩ : syracuseStep 3839339 = 5759009) B5759009
theorem B4856219 : Blo 531801 4856219 := bstep (se 1 (by rfl) ⟨3642164, by rfl⟩ : syracuseStep 4856219 = 7284329) B7284329
theorem B4563449 : Blo 531801 4563449 := bstep (se 2 (by rfl) ⟨1711293, by rfl⟩ : syracuseStep 4563449 = 3422587) B3422587
theorem B533183 : Blo 531801 533183 := bstep (se 1 (by rfl) ⟨399887, by rfl⟩ : syracuseStep 533183 = 799775) B799775
theorem B902171 : Blo 531801 902171 := bstep (se 1 (by rfl) ⟨676628, by rfl⟩ : syracuseStep 902171 = 1353257) B1353257
theorem B4547015 : Blo 531801 4547015 := bstep (se 1 (by rfl) ⟨3410261, by rfl⟩ : syracuseStep 4547015 = 6820523) B6820523
theorem B2746831 : Blo 531801 2746831 := bstep (se 1 (by rfl) ⟨2060123, by rfl⟩ : syracuseStep 2746831 = 4120247) B4120247
theorem B912107 : Blo 531801 912107 := bstep (se 1 (by rfl) ⟨684080, by rfl⟩ : syracuseStep 912107 = 1368161) B1368161
theorem B601447 : Blo 531801 601447 := bstep (se 1 (by rfl) ⟨451085, by rfl⟩ : syracuseStep 601447 = 902171) B902171
theorem B10238237 : Blo 531801 10238237 := bstep (se 3 (by rfl) ⟨1919669, by rfl⟩ : syracuseStep 10238237 = 3839339) B3839339
theorem B3031343 : Blo 531801 3031343 := bstep (se 1 (by rfl) ⟨2273507, by rfl⟩ : syracuseStep 3031343 = 4547015) B4547015
theorem B608071 : Blo 531801 608071 := bstep (se 1 (by rfl) ⟨456053, by rfl⟩ : syracuseStep 608071 = 912107) B912107
theorem B3662441 : Blo 531801 3662441 := bstep (se 2 (by rfl) ⟨1373415, by rfl⟩ : syracuseStep 3662441 = 2746831) B2746831
theorem B3237479 : Blo 531801 3237479 := bstep (se 1 (by rfl) ⟨2428109, by rfl⟩ : syracuseStep 3237479 = 4856219) B4856219
theorem B3042299 : Blo 531801 3042299 := bstep (se 1 (by rfl) ⟨2281724, by rfl⟩ : syracuseStep 3042299 = 4563449) B4563449
theorem B6825491 : Blo 531801 6825491 := bstep (se 1 (by rfl) ⟨5119118, by rfl⟩ : syracuseStep 6825491 = 10238237) B10238237
theorem B801929 : Blo 531801 801929 := bstep (se 2 (by rfl) ⟨300723, by rfl⟩ : syracuseStep 801929 = 601447) B601447
theorem B2441627 : Blo 531801 2441627 := bstep (se 1 (by rfl) ⟨1831220, by rfl⟩ : syracuseStep 2441627 = 3662441) B3662441
theorem B2020895 : Blo 531801 2020895 := bstep (se 1 (by rfl) ⟨1515671, by rfl⟩ : syracuseStep 2020895 = 3031343) B3031343
theorem B810761 : Blo 531801 810761 := bstep (se 2 (by rfl) ⟨304035, by rfl⟩ : syracuseStep 810761 = 608071) B608071
theorem B2158319 : Blo 531801 2158319 := bstep (se 1 (by rfl) ⟨1618739, by rfl⟩ : syracuseStep 2158319 = 3237479) B3237479
theorem B2028199 : Blo 531801 2028199 := bstep (se 1 (by rfl) ⟨1521149, by rfl⟩ : syracuseStep 2028199 = 3042299) B3042299
theorem B1347263 : Blo 531801 1347263 := bstep (se 1 (by rfl) ⟨1010447, by rfl⟩ : syracuseStep 1347263 = 2020895) B2020895
theorem B534619 : Blo 531801 534619 := bstep (se 1 (by rfl) ⟨400964, by rfl⟩ : syracuseStep 534619 = 801929) B801929
theorem B2704265 : Blo 531801 2704265 := bstep (se 2 (by rfl) ⟨1014099, by rfl⟩ : syracuseStep 2704265 = 2028199) B2028199
theorem B1627751 : Blo 531801 1627751 := bstep (se 1 (by rfl) ⟨1220813, by rfl⟩ : syracuseStep 1627751 = 2441627) B2441627
theorem B4550327 : Blo 531801 4550327 := bstep (se 1 (by rfl) ⟨3412745, by rfl⟩ : syracuseStep 4550327 = 6825491) B6825491
theorem B1438879 : Blo 531801 1438879 := bstep (se 1 (by rfl) ⟨1079159, by rfl⟩ : syracuseStep 1438879 = 2158319) B2158319
theorem B8648117 : Blo 531801 8648117 := bstep (se 5 (by rfl) ⟨405380, by rfl⟩ : syracuseStep 8648117 = 810761) B810761
theorem B1802843 : Blo 531801 1802843 := bstep (se 1 (by rfl) ⟨1352132, by rfl⟩ : syracuseStep 1802843 = 2704265) B2704265
theorem B1085167 : Blo 531801 1085167 := bstep (se 1 (by rfl) ⟨813875, by rfl⟩ : syracuseStep 1085167 = 1627751) B1627751
theorem B898175 : Blo 531801 898175 := bstep (se 1 (by rfl) ⟨673631, by rfl⟩ : syracuseStep 898175 = 1347263) B1347263
theorem B1918505 : Blo 531801 1918505 := bstep (se 2 (by rfl) ⟨719439, by rfl⟩ : syracuseStep 1918505 = 1438879) B1438879
theorem B3033551 : Blo 531801 3033551 := bstep (se 1 (by rfl) ⟨2275163, by rfl⟩ : syracuseStep 3033551 = 4550327) B4550327
theorem B5765411 : Blo 531801 5765411 := bstep (se 1 (by rfl) ⟨4324058, by rfl⟩ : syracuseStep 5765411 = 8648117) B8648117
theorem B1279003 : Blo 531801 1279003 := bstep (se 1 (by rfl) ⟨959252, by rfl⟩ : syracuseStep 1279003 = 1918505) B1918505
theorem B1446889 : Blo 531801 1446889 := bstep (se 2 (by rfl) ⟨542583, by rfl⟩ : syracuseStep 1446889 = 1085167) B1085167
theorem B598783 : Blo 531801 598783 := bstep (se 1 (by rfl) ⟨449087, by rfl⟩ : syracuseStep 598783 = 898175) B898175
theorem B3843607 : Blo 531801 3843607 := bstep (se 1 (by rfl) ⟨2882705, by rfl⟩ : syracuseStep 3843607 = 5765411) B5765411
theorem B1201895 : Blo 531801 1201895 := bstep (se 1 (by rfl) ⟨901421, by rfl⟩ : syracuseStep 1201895 = 1802843) B1802843
theorem B2022367 : Blo 531801 2022367 := bstep (se 1 (by rfl) ⟨1516775, by rfl⟩ : syracuseStep 2022367 = 3033551) B3033551
theorem B1705337 : Blo 531801 1705337 := bstep (se 2 (by rfl) ⟨639501, by rfl⟩ : syracuseStep 1705337 = 1279003) B1279003
theorem B2696489 : Blo 531801 2696489 := bstep (se 2 (by rfl) ⟨1011183, by rfl⟩ : syracuseStep 2696489 = 2022367) B2022367
theorem B798377 : Blo 531801 798377 := bstep (se 2 (by rfl) ⟨299391, by rfl⟩ : syracuseStep 798377 = 598783) B598783
theorem B5124809 : Blo 531801 5124809 := bstep (se 2 (by rfl) ⟨1921803, by rfl⟩ : syracuseStep 5124809 = 3843607) B3843607
theorem B801263 : Blo 531801 801263 := bstep (se 1 (by rfl) ⟨600947, by rfl⟩ : syracuseStep 801263 = 1201895) B1201895
theorem B1929185 : Blo 531801 1929185 := bstep (se 2 (by rfl) ⟨723444, by rfl⟩ : syracuseStep 1929185 = 1446889) B1446889
theorem B532251 : Blo 531801 532251 := bstep (se 1 (by rfl) ⟨399188, by rfl⟩ : syracuseStep 532251 = 798377) B798377
theorem B1286123 : Blo 531801 1286123 := bstep (se 1 (by rfl) ⟨964592, by rfl⟩ : syracuseStep 1286123 = 1929185) B1929185
theorem B3416539 : Blo 531801 3416539 := bstep (se 1 (by rfl) ⟨2562404, by rfl⟩ : syracuseStep 3416539 = 5124809) B5124809
theorem B534175 : Blo 531801 534175 := bstep (se 1 (by rfl) ⟨400631, by rfl⟩ : syracuseStep 534175 = 801263) B801263
theorem B1136891 : Blo 531801 1136891 := bstep (se 1 (by rfl) ⟨852668, by rfl⟩ : syracuseStep 1136891 = 1705337) B1705337
theorem B1797659 : Blo 531801 1797659 := bstep (se 1 (by rfl) ⟨1348244, by rfl⟩ : syracuseStep 1797659 = 2696489) B2696489
theorem B4555385 : Blo 531801 4555385 := bstep (se 2 (by rfl) ⟨1708269, by rfl⟩ : syracuseStep 4555385 = 3416539) B3416539
theorem B757927 : Blo 531801 757927 := bstep (se 1 (by rfl) ⟨568445, by rfl⟩ : syracuseStep 757927 = 1136891) B1136891
theorem B1198439 : Blo 531801 1198439 := bstep (se 1 (by rfl) ⟨898829, by rfl⟩ : syracuseStep 1198439 = 1797659) B1797659
theorem B3429661 : Blo 531801 3429661 := bstep (se 3 (by rfl) ⟨643061, by rfl⟩ : syracuseStep 3429661 = 1286123) B1286123
theorem B798959 : Blo 531801 798959 := bstep (se 1 (by rfl) ⟨599219, by rfl⟩ : syracuseStep 798959 = 1198439) B1198439
theorem B4572881 : Blo 531801 4572881 := bstep (se 2 (by rfl) ⟨1714830, by rfl⟩ : syracuseStep 4572881 = 3429661) B3429661
theorem B3036923 : Blo 531801 3036923 := bstep (se 1 (by rfl) ⟨2277692, by rfl⟩ : syracuseStep 3036923 = 4555385) B4555385
theorem B1010569 : Blo 531801 1010569 := bstep (se 2 (by rfl) ⟨378963, by rfl⟩ : syracuseStep 1010569 = 757927) B757927
theorem B3048587 : Blo 531801 3048587 := bstep (se 1 (by rfl) ⟨2286440, by rfl⟩ : syracuseStep 3048587 = 4572881) B4572881
theorem B1347425 : Blo 531801 1347425 := bstep (se 2 (by rfl) ⟨505284, by rfl⟩ : syracuseStep 1347425 = 1010569) B1010569
theorem B532639 : Blo 531801 532639 := bstep (se 1 (by rfl) ⟨399479, by rfl⟩ : syracuseStep 532639 = 798959) B798959
theorem B2024615 : Blo 531801 2024615 := bstep (se 1 (by rfl) ⟨1518461, by rfl⟩ : syracuseStep 2024615 = 3036923) B3036923
theorem B2032391 : Blo 531801 2032391 := bstep (se 1 (by rfl) ⟨1524293, by rfl⟩ : syracuseStep 2032391 = 3048587) B3048587
theorem B1349743 : Blo 531801 1349743 := bstep (se 1 (by rfl) ⟨1012307, by rfl⟩ : syracuseStep 1349743 = 2024615) B2024615
theorem B898283 : Blo 531801 898283 := bstep (se 1 (by rfl) ⟨673712, by rfl⟩ : syracuseStep 898283 = 1347425) B1347425
theorem B598855 : Blo 531801 598855 := bstep (se 1 (by rfl) ⟨449141, by rfl⟩ : syracuseStep 598855 = 898283) B898283
theorem B1354927 : Blo 531801 1354927 := bstep (se 1 (by rfl) ⟨1016195, by rfl⟩ : syracuseStep 1354927 = 2032391) B2032391
theorem B1799657 : Blo 531801 1799657 := bstep (se 2 (by rfl) ⟨674871, by rfl⟩ : syracuseStep 1799657 = 1349743) B1349743
theorem B1806569 : Blo 531801 1806569 := bstep (se 2 (by rfl) ⟨677463, by rfl⟩ : syracuseStep 1806569 = 1354927) B1354927
theorem B798473 : Blo 531801 798473 := bstep (se 2 (by rfl) ⟨299427, by rfl⟩ : syracuseStep 798473 = 598855) B598855
theorem B1199771 : Blo 531801 1199771 := bstep (se 1 (by rfl) ⟨899828, by rfl⟩ : syracuseStep 1199771 = 1799657) B1799657
theorem B532315 : Blo 531801 532315 := bstep (se 1 (by rfl) ⟨399236, by rfl⟩ : syracuseStep 532315 = 798473) B798473
theorem B799847 : Blo 531801 799847 := bstep (se 1 (by rfl) ⟨599885, by rfl⟩ : syracuseStep 799847 = 1199771) B1199771
theorem B1204379 : Blo 531801 1204379 := bstep (se 1 (by rfl) ⟨903284, by rfl⟩ : syracuseStep 1204379 = 1806569) B1806569
theorem B533231 : Blo 531801 533231 := bstep (se 1 (by rfl) ⟨399923, by rfl⟩ : syracuseStep 533231 = 799847) B799847
theorem B802919 : Blo 531801 802919 := bstep (se 1 (by rfl) ⟨602189, by rfl⟩ : syracuseStep 802919 = 1204379) B1204379
theorem B535279 : Blo 531801 535279 := bstep (se 1 (by rfl) ⟨401459, by rfl⟩ : syracuseStep 535279 = 802919) B802919

theorem C0 (j : ℕ) (h1 : 132950 ≤ j) (h2 : j ≤ 133649) : Blo 531801 (4 * j + 3) := by
  interval_cases j
  · exact B531803
  · exact B531807
  · exact B531811
  · exact B531815
  · exact B531819
  · exact B531823
  · exact B531827
  · exact B531831
  · exact B531835
  · exact B531839
  · exact B531843
  · exact B531847
  · exact B531851
  · exact B531855
  · exact B531859
  · exact B531863
  · exact B531867
  · exact B531871
  · exact B531875
  · exact B531879
  · exact B531883
  · exact B531887
  · exact B531891
  · exact B531895
  · exact B531899
  · exact B531903
  · exact B531907
  · exact B531911
  · exact B531915
  · exact B531919
  · exact B531923
  · exact B531927
  · exact B531931
  · exact B531935
  · exact B531939
  · exact B531943
  · exact B531947
  · exact B531951
  · exact B531955
  · exact B531959
  · exact B531963
  · exact B531967
  · exact B531971
  · exact B531975
  · exact B531979
  · exact B531983
  · exact B531987
  · exact B531991
  · exact B531995
  · exact B531999
  · exact B532003
  · exact B532007
  · exact B532011
  · exact B532015
  · exact B532019
  · exact B532023
  · exact B532027
  · exact B532031
  · exact B532035
  · exact B532039
  · exact B532043
  · exact B532047
  · exact B532051
  · exact B532055
  · exact B532059
  · exact B532063
  · exact B532067
  · exact B532071
  · exact B532075
  · exact B532079
  · exact B532083
  · exact B532087
  · exact B532091
  · exact B532095
  · exact B532099
  · exact B532103
  · exact B532107
  · exact B532111
  · exact B532115
  · exact B532119
  · exact B532123
  · exact B532127
  · exact B532131
  · exact B532135
  · exact B532139
  · exact B532143
  · exact B532147
  · exact B532151
  · exact B532155
  · exact B532159
  · exact B532163
  · exact B532167
  · exact B532171
  · exact B532175
  · exact B532179
  · exact B532183
  · exact B532187
  · exact B532191
  · exact B532195
  · exact B532199
  · exact B532203
  · exact B532207
  · exact B532211
  · exact B532215
  · exact B532219
  · exact B532223
  · exact B532227
  · exact B532231
  · exact B532235
  · exact B532239
  · exact B532243
  · exact B532247
  · exact B532251
  · exact B532255
  · exact B532259
  · exact B532263
  · exact B532267
  · exact B532271
  · exact B532275
  · exact B532279
  · exact B532283
  · exact B532287
  · exact B532291
  · exact B532295
  · exact B532299
  · exact B532303
  · exact B532307
  · exact B532311
  · exact B532315
  · exact B532319
  · exact B532323
  · exact B532327
  · exact B532331
  · exact B532335
  · exact B532339
  · exact B532343
  · exact B532347
  · exact B532351
  · exact B532355
  · exact B532359
  · exact B532363
  · exact B532367
  · exact B532371
  · exact B532375
  · exact B532379
  · exact B532383
  · exact B532387
  · exact B532391
  · exact B532395
  · exact B532399
  · exact B532403
  · exact B532407
  · exact B532411
  · exact B532415
  · exact B532419
  · exact B532423
  · exact B532427
  · exact B532431
  · exact B532435
  · exact B532439
  · exact B532443
  · exact B532447
  · exact B532451
  · exact B532455
  · exact B532459
  · exact B532463
  · exact B532467
  · exact B532471
  · exact B532475
  · exact B532479
  · exact B532483
  · exact B532487
  · exact B532491
  · exact B532495
  · exact B532499
  · exact B532503
  · exact B532507
  · exact B532511
  · exact B532515
  · exact B532519
  · exact B532523
  · exact B532527
  · exact B532531
  · exact B532535
  · exact B532539
  · exact B532543
  · exact B532547
  · exact B532551
  · exact B532555
  · exact B532559
  · exact B532563
  · exact B532567
  · exact B532571
  · exact B532575
  · exact B532579
  · exact B532583
  · exact B532587
  · exact B532591
  · exact B532595
  · exact B532599
  · exact B532603
  · exact B532607
  · exact B532611
  · exact B532615
  · exact B532619
  · exact B532623
  · exact B532627
  · exact B532631
  · exact B532635
  · exact B532639
  · exact B532643
  · exact B532647
  · exact B532651
  · exact B532655
  · exact B532659
  · exact B532663
  · exact B532667
  · exact B532671
  · exact B532675
  · exact B532679
  · exact B532683
  · exact B532687
  · exact B532691
  · exact B532695
  · exact B532699
  · exact B532703
  · exact B532707
  · exact B532711
  · exact B532715
  · exact B532719
  · exact B532723
  · exact B532727
  · exact B532731
  · exact B532735
  · exact B532739
  · exact B532743
  · exact B532747
  · exact B532751
  · exact B532755
  · exact B532759
  · exact B532763
  · exact B532767
  · exact B532771
  · exact B532775
  · exact B532779
  · exact B532783
  · exact B532787
  · exact B532791
  · exact B532795
  · exact B532799
  · exact B532803
  · exact B532807
  · exact B532811
  · exact B532815
  · exact B532819
  · exact B532823
  · exact B532827
  · exact B532831
  · exact B532835
  · exact B532839
  · exact B532843
  · exact B532847
  · exact B532851
  · exact B532855
  · exact B532859
  · exact B532863
  · exact B532867
  · exact B532871
  · exact B532875
  · exact B532879
  · exact B532883
  · exact B532887
  · exact B532891
  · exact B532895
  · exact B532899
  · exact B532903
  · exact B532907
  · exact B532911
  · exact B532915
  · exact B532919
  · exact B532923
  · exact B532927
  · exact B532931
  · exact B532935
  · exact B532939
  · exact B532943
  · exact B532947
  · exact B532951
  · exact B532955
  · exact B532959
  · exact B532963
  · exact B532967
  · exact B532971
  · exact B532975
  · exact B532979
  · exact B532983
  · exact B532987
  · exact B532991
  · exact B532995
  · exact B532999
  · exact B533003
  · exact B533007
  · exact B533011
  · exact B533015
  · exact B533019
  · exact B533023
  · exact B533027
  · exact B533031
  · exact B533035
  · exact B533039
  · exact B533043
  · exact B533047
  · exact B533051
  · exact B533055
  · exact B533059
  · exact B533063
  · exact B533067
  · exact B533071
  · exact B533075
  · exact B533079
  · exact B533083
  · exact B533087
  · exact B533091
  · exact B533095
  · exact B533099
  · exact B533103
  · exact B533107
  · exact B533111
  · exact B533115
  · exact B533119
  · exact B533123
  · exact B533127
  · exact B533131
  · exact B533135
  · exact B533139
  · exact B533143
  · exact B533147
  · exact B533151
  · exact B533155
  · exact B533159
  · exact B533163
  · exact B533167
  · exact B533171
  · exact B533175
  · exact B533179
  · exact B533183
  · exact B533187
  · exact B533191
  · exact B533195
  · exact B533199
  · exact B533203
  · exact B533207
  · exact B533211
  · exact B533215
  · exact B533219
  · exact B533223
  · exact B533227
  · exact B533231
  · exact B533235
  · exact B533239
  · exact B533243
  · exact B533247
  · exact B533251
  · exact B533255
  · exact B533259
  · exact B533263
  · exact B533267
  · exact B533271
  · exact B533275
  · exact B533279
  · exact B533283
  · exact B533287
  · exact B533291
  · exact B533295
  · exact B533299
  · exact B533303
  · exact B533307
  · exact B533311
  · exact B533315
  · exact B533319
  · exact B533323
  · exact B533327
  · exact B533331
  · exact B533335
  · exact B533339
  · exact B533343
  · exact B533347
  · exact B533351
  · exact B533355
  · exact B533359
  · exact B533363
  · exact B533367
  · exact B533371
  · exact B533375
  · exact B533379
  · exact B533383
  · exact B533387
  · exact B533391
  · exact B533395
  · exact B533399
  · exact B533403
  · exact B533407
  · exact B533411
  · exact B533415
  · exact B533419
  · exact B533423
  · exact B533427
  · exact B533431
  · exact B533435
  · exact B533439
  · exact B533443
  · exact B533447
  · exact B533451
  · exact B533455
  · exact B533459
  · exact B533463
  · exact B533467
  · exact B533471
  · exact B533475
  · exact B533479
  · exact B533483
  · exact B533487
  · exact B533491
  · exact B533495
  · exact B533499
  · exact B533503
  · exact B533507
  · exact B533511
  · exact B533515
  · exact B533519
  · exact B533523
  · exact B533527
  · exact B533531
  · exact B533535
  · exact B533539
  · exact B533543
  · exact B533547
  · exact B533551
  · exact B533555
  · exact B533559
  · exact B533563
  · exact B533567
  · exact B533571
  · exact B533575
  · exact B533579
  · exact B533583
  · exact B533587
  · exact B533591
  · exact B533595
  · exact B533599
  · exact B533603
  · exact B533607
  · exact B533611
  · exact B533615
  · exact B533619
  · exact B533623
  · exact B533627
  · exact B533631
  · exact B533635
  · exact B533639
  · exact B533643
  · exact B533647
  · exact B533651
  · exact B533655
  · exact B533659
  · exact B533663
  · exact B533667
  · exact B533671
  · exact B533675
  · exact B533679
  · exact B533683
  · exact B533687
  · exact B533691
  · exact B533695
  · exact B533699
  · exact B533703
  · exact B533707
  · exact B533711
  · exact B533715
  · exact B533719
  · exact B533723
  · exact B533727
  · exact B533731
  · exact B533735
  · exact B533739
  · exact B533743
  · exact B533747
  · exact B533751
  · exact B533755
  · exact B533759
  · exact B533763
  · exact B533767
  · exact B533771
  · exact B533775
  · exact B533779
  · exact B533783
  · exact B533787
  · exact B533791
  · exact B533795
  · exact B533799
  · exact B533803
  · exact B533807
  · exact B533811
  · exact B533815
  · exact B533819
  · exact B533823
  · exact B533827
  · exact B533831
  · exact B533835
  · exact B533839
  · exact B533843
  · exact B533847
  · exact B533851
  · exact B533855
  · exact B533859
  · exact B533863
  · exact B533867
  · exact B533871
  · exact B533875
  · exact B533879
  · exact B533883
  · exact B533887
  · exact B533891
  · exact B533895
  · exact B533899
  · exact B533903
  · exact B533907
  · exact B533911
  · exact B533915
  · exact B533919
  · exact B533923
  · exact B533927
  · exact B533931
  · exact B533935
  · exact B533939
  · exact B533943
  · exact B533947
  · exact B533951
  · exact B533955
  · exact B533959
  · exact B533963
  · exact B533967
  · exact B533971
  · exact B533975
  · exact B533979
  · exact B533983
  · exact B533987
  · exact B533991
  · exact B533995
  · exact B533999
  · exact B534003
  · exact B534007
  · exact B534011
  · exact B534015
  · exact B534019
  · exact B534023
  · exact B534027
  · exact B534031
  · exact B534035
  · exact B534039
  · exact B534043
  · exact B534047
  · exact B534051
  · exact B534055
  · exact B534059
  · exact B534063
  · exact B534067
  · exact B534071
  · exact B534075
  · exact B534079
  · exact B534083
  · exact B534087
  · exact B534091
  · exact B534095
  · exact B534099
  · exact B534103
  · exact B534107
  · exact B534111
  · exact B534115
  · exact B534119
  · exact B534123
  · exact B534127
  · exact B534131
  · exact B534135
  · exact B534139
  · exact B534143
  · exact B534147
  · exact B534151
  · exact B534155
  · exact B534159
  · exact B534163
  · exact B534167
  · exact B534171
  · exact B534175
  · exact B534179
  · exact B534183
  · exact B534187
  · exact B534191
  · exact B534195
  · exact B534199
  · exact B534203
  · exact B534207
  · exact B534211
  · exact B534215
  · exact B534219
  · exact B534223
  · exact B534227
  · exact B534231
  · exact B534235
  · exact B534239
  · exact B534243
  · exact B534247
  · exact B534251
  · exact B534255
  · exact B534259
  · exact B534263
  · exact B534267
  · exact B534271
  · exact B534275
  · exact B534279
  · exact B534283
  · exact B534287
  · exact B534291
  · exact B534295
  · exact B534299
  · exact B534303
  · exact B534307
  · exact B534311
  · exact B534315
  · exact B534319
  · exact B534323
  · exact B534327
  · exact B534331
  · exact B534335
  · exact B534339
  · exact B534343
  · exact B534347
  · exact B534351
  · exact B534355
  · exact B534359
  · exact B534363
  · exact B534367
  · exact B534371
  · exact B534375
  · exact B534379
  · exact B534383
  · exact B534387
  · exact B534391
  · exact B534395
  · exact B534399
  · exact B534403
  · exact B534407
  · exact B534411
  · exact B534415
  · exact B534419
  · exact B534423
  · exact B534427
  · exact B534431
  · exact B534435
  · exact B534439
  · exact B534443
  · exact B534447
  · exact B534451
  · exact B534455
  · exact B534459
  · exact B534463
  · exact B534467
  · exact B534471
  · exact B534475
  · exact B534479
  · exact B534483
  · exact B534487
  · exact B534491
  · exact B534495
  · exact B534499
  · exact B534503
  · exact B534507
  · exact B534511
  · exact B534515
  · exact B534519
  · exact B534523
  · exact B534527
  · exact B534531
  · exact B534535
  · exact B534539
  · exact B534543
  · exact B534547
  · exact B534551
  · exact B534555
  · exact B534559
  · exact B534563
  · exact B534567
  · exact B534571
  · exact B534575
  · exact B534579
  · exact B534583
  · exact B534587
  · exact B534591
  · exact B534595
  · exact B534599

theorem C1 (j : ℕ) (h1 : 133650 ≤ j) (h2 : j ≤ 133949) : Blo 531801 (4 * j + 3) := by
  interval_cases j
  · exact B534603
  · exact B534607
  · exact B534611
  · exact B534615
  · exact B534619
  · exact B534623
  · exact B534627
  · exact B534631
  · exact B534635
  · exact B534639
  · exact B534643
  · exact B534647
  · exact B534651
  · exact B534655
  · exact B534659
  · exact B534663
  · exact B534667
  · exact B534671
  · exact B534675
  · exact B534679
  · exact B534683
  · exact B534687
  · exact B534691
  · exact B534695
  · exact B534699
  · exact B534703
  · exact B534707
  · exact B534711
  · exact B534715
  · exact B534719
  · exact B534723
  · exact B534727
  · exact B534731
  · exact B534735
  · exact B534739
  · exact B534743
  · exact B534747
  · exact B534751
  · exact B534755
  · exact B534759
  · exact B534763
  · exact B534767
  · exact B534771
  · exact B534775
  · exact B534779
  · exact B534783
  · exact B534787
  · exact B534791
  · exact B534795
  · exact B534799
  · exact B534803
  · exact B534807
  · exact B534811
  · exact B534815
  · exact B534819
  · exact B534823
  · exact B534827
  · exact B534831
  · exact B534835
  · exact B534839
  · exact B534843
  · exact B534847
  · exact B534851
  · exact B534855
  · exact B534859
  · exact B534863
  · exact B534867
  · exact B534871
  · exact B534875
  · exact B534879
  · exact B534883
  · exact B534887
  · exact B534891
  · exact B534895
  · exact B534899
  · exact B534903
  · exact B534907
  · exact B534911
  · exact B534915
  · exact B534919
  · exact B534923
  · exact B534927
  · exact B534931
  · exact B534935
  · exact B534939
  · exact B534943
  · exact B534947
  · exact B534951
  · exact B534955
  · exact B534959
  · exact B534963
  · exact B534967
  · exact B534971
  · exact B534975
  · exact B534979
  · exact B534983
  · exact B534987
  · exact B534991
  · exact B534995
  · exact B534999
  · exact B535003
  · exact B535007
  · exact B535011
  · exact B535015
  · exact B535019
  · exact B535023
  · exact B535027
  · exact B535031
  · exact B535035
  · exact B535039
  · exact B535043
  · exact B535047
  · exact B535051
  · exact B535055
  · exact B535059
  · exact B535063
  · exact B535067
  · exact B535071
  · exact B535075
  · exact B535079
  · exact B535083
  · exact B535087
  · exact B535091
  · exact B535095
  · exact B535099
  · exact B535103
  · exact B535107
  · exact B535111
  · exact B535115
  · exact B535119
  · exact B535123
  · exact B535127
  · exact B535131
  · exact B535135
  · exact B535139
  · exact B535143
  · exact B535147
  · exact B535151
  · exact B535155
  · exact B535159
  · exact B535163
  · exact B535167
  · exact B535171
  · exact B535175
  · exact B535179
  · exact B535183
  · exact B535187
  · exact B535191
  · exact B535195
  · exact B535199
  · exact B535203
  · exact B535207
  · exact B535211
  · exact B535215
  · exact B535219
  · exact B535223
  · exact B535227
  · exact B535231
  · exact B535235
  · exact B535239
  · exact B535243
  · exact B535247
  · exact B535251
  · exact B535255
  · exact B535259
  · exact B535263
  · exact B535267
  · exact B535271
  · exact B535275
  · exact B535279
  · exact B535283
  · exact B535287
  · exact B535291
  · exact B535295
  · exact B535299
  · exact B535303
  · exact B535307
  · exact B535311
  · exact B535315
  · exact B535319
  · exact B535323
  · exact B535327
  · exact B535331
  · exact B535335
  · exact B535339
  · exact B535343
  · exact B535347
  · exact B535351
  · exact B535355
  · exact B535359
  · exact B535363
  · exact B535367
  · exact B535371
  · exact B535375
  · exact B535379
  · exact B535383
  · exact B535387
  · exact B535391
  · exact B535395
  · exact B535399
  · exact B535403
  · exact B535407
  · exact B535411
  · exact B535415
  · exact B535419
  · exact B535423
  · exact B535427
  · exact B535431
  · exact B535435
  · exact B535439
  · exact B535443
  · exact B535447
  · exact B535451
  · exact B535455
  · exact B535459
  · exact B535463
  · exact B535467
  · exact B535471
  · exact B535475
  · exact B535479
  · exact B535483
  · exact B535487
  · exact B535491
  · exact B535495
  · exact B535499
  · exact B535503
  · exact B535507
  · exact B535511
  · exact B535515
  · exact B535519
  · exact B535523
  · exact B535527
  · exact B535531
  · exact B535535
  · exact B535539
  · exact B535543
  · exact B535547
  · exact B535551
  · exact B535555
  · exact B535559
  · exact B535563
  · exact B535567
  · exact B535571
  · exact B535575
  · exact B535579
  · exact B535583
  · exact B535587
  · exact B535591
  · exact B535595
  · exact B535599
  · exact B535603
  · exact B535607
  · exact B535611
  · exact B535615
  · exact B535619
  · exact B535623
  · exact B535627
  · exact B535631
  · exact B535635
  · exact B535639
  · exact B535643
  · exact B535647
  · exact B535651
  · exact B535655
  · exact B535659
  · exact B535663
  · exact B535667
  · exact B535671
  · exact B535675
  · exact B535679
  · exact B535683
  · exact B535687
  · exact B535691
  · exact B535695
  · exact B535699
  · exact B535703
  · exact B535707
  · exact B535711
  · exact B535715
  · exact B535719
  · exact B535723
  · exact B535727
  · exact B535731
  · exact B535735
  · exact B535739
  · exact B535743
  · exact B535747
  · exact B535751
  · exact B535755
  · exact B535759
  · exact B535763
  · exact B535767
  · exact B535771
  · exact B535775
  · exact B535779
  · exact B535783
  · exact B535787
  · exact B535791
  · exact B535795
  · exact B535799

theorem solution (m : ℕ) (hlo : 531801 ≤ m) (hhi : m ≤ 535801) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 132950 ≤ j := by omega
    have hj2 : j ≤ 133949 := by omega
    have hb : Blo 531801 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 133650 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
