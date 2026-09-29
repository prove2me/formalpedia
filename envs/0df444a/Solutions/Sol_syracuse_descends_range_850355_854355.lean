-- Prove2me | solution 1 for syracuse_descends_range_850355_854355
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:57.002045+00:00
-- url     : https://prove2.me/submissions/f94e6790-0245-4531-9a58-cfa484465474

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


theorem B1277957 : Blo 850355 1277957 := bbase (se 4 (by rfl) ⟨119808, by rfl⟩ : syracuseStep 1277957 = 239617) (by norm_num)
theorem B1277981 : Blo 850355 1277981 := bbase (se 3 (by rfl) ⟨239621, by rfl⟩ : syracuseStep 1277981 = 479243) (by norm_num)
theorem B1278005 : Blo 850355 1278005 := bbase (se 5 (by rfl) ⟨59906, by rfl⟩ : syracuseStep 1278005 = 119813) (by norm_num)
theorem B1278029 : Blo 850355 1278029 := bbase (se 3 (by rfl) ⟨239630, by rfl⟩ : syracuseStep 1278029 = 479261) (by norm_num)
theorem B2424917 : Blo 850355 2424917 := bbase (se 8 (by rfl) ⟨14208, by rfl⟩ : syracuseStep 2424917 = 28417) (by norm_num)
theorem B1278053 : Blo 850355 1278053 := bbase (se 4 (by rfl) ⟨119817, by rfl⟩ : syracuseStep 1278053 = 239635) (by norm_num)
theorem B1278077 : Blo 850355 1278077 := bbase (se 3 (by rfl) ⟨239639, by rfl⟩ : syracuseStep 1278077 = 479279) (by norm_num)
theorem B1278101 : Blo 850355 1278101 := bbase (se 6 (by rfl) ⟨29955, by rfl⟩ : syracuseStep 1278101 = 59911) (by norm_num)
theorem B1278125 : Blo 850355 1278125 := bbase (se 3 (by rfl) ⟨239648, by rfl⟩ : syracuseStep 1278125 = 479297) (by norm_num)
theorem B1278149 : Blo 850355 1278149 := bbase (se 4 (by rfl) ⟨119826, by rfl⟩ : syracuseStep 1278149 = 239653) (by norm_num)
theorem B1278173 : Blo 850355 1278173 := bbase (se 3 (by rfl) ⟨239657, by rfl⟩ : syracuseStep 1278173 = 479315) (by norm_num)
theorem B1278197 : Blo 850355 1278197 := bbase (se 5 (by rfl) ⟨59915, by rfl⟩ : syracuseStep 1278197 = 119831) (by norm_num)
theorem B1278221 : Blo 850355 1278221 := bbase (se 3 (by rfl) ⟨239666, by rfl⟩ : syracuseStep 1278221 = 479333) (by norm_num)
theorem B2457877 : Blo 850355 2457877 := bbase (se 6 (by rfl) ⟨57606, by rfl⟩ : syracuseStep 2457877 = 115213) (by norm_num)
theorem B1278245 : Blo 850355 1278245 := bbase (se 4 (by rfl) ⟨119835, by rfl⟩ : syracuseStep 1278245 = 239671) (by norm_num)
theorem B1278269 : Blo 850355 1278269 := bbase (se 3 (by rfl) ⟨239675, by rfl⟩ : syracuseStep 1278269 = 479351) (by norm_num)
theorem B1278293 : Blo 850355 1278293 := bbase (se 10 (by rfl) ⟨1872, by rfl⟩ : syracuseStep 1278293 = 3745) (by norm_num)
theorem B1278317 : Blo 850355 1278317 := bbase (se 3 (by rfl) ⟨239684, by rfl⟩ : syracuseStep 1278317 = 479369) (by norm_num)
theorem B1278341 : Blo 850355 1278341 := bbase (se 4 (by rfl) ⟨119844, by rfl⟩ : syracuseStep 1278341 = 239689) (by norm_num)
theorem B1278365 : Blo 850355 1278365 := bbase (se 3 (by rfl) ⟨239693, by rfl⟩ : syracuseStep 1278365 = 479387) (by norm_num)
theorem B1278389 : Blo 850355 1278389 := bbase (se 5 (by rfl) ⟨59924, by rfl⟩ : syracuseStep 1278389 = 119849) (by norm_num)
theorem B1278413 : Blo 850355 1278413 := bbase (se 3 (by rfl) ⟨239702, by rfl⟩ : syracuseStep 1278413 = 479405) (by norm_num)
theorem B1278437 : Blo 850355 1278437 := bbase (se 4 (by rfl) ⟨119853, by rfl⟩ : syracuseStep 1278437 = 239707) (by norm_num)
theorem B1278461 : Blo 850355 1278461 := bbase (se 3 (by rfl) ⟨239711, by rfl⟩ : syracuseStep 1278461 = 479423) (by norm_num)
theorem B1278485 : Blo 850355 1278485 := bbase (se 6 (by rfl) ⟨29964, by rfl⟩ : syracuseStep 1278485 = 59929) (by norm_num)
theorem B1278509 : Blo 850355 1278509 := bbase (se 3 (by rfl) ⟨239720, by rfl⟩ : syracuseStep 1278509 = 479441) (by norm_num)
theorem B1278533 : Blo 850355 1278533 := bbase (se 4 (by rfl) ⟨119862, by rfl⟩ : syracuseStep 1278533 = 239725) (by norm_num)
theorem B1278557 : Blo 850355 1278557 := bbase (se 3 (by rfl) ⟨239729, by rfl⟩ : syracuseStep 1278557 = 479459) (by norm_num)
theorem B1278581 : Blo 850355 1278581 := bbase (se 5 (by rfl) ⟨59933, by rfl⟩ : syracuseStep 1278581 = 119867) (by norm_num)
theorem B1278605 : Blo 850355 1278605 := bbase (se 3 (by rfl) ⟨239738, by rfl⟩ : syracuseStep 1278605 = 479477) (by norm_num)
theorem B1278629 : Blo 850355 1278629 := bbase (se 4 (by rfl) ⟨119871, by rfl⟩ : syracuseStep 1278629 = 239743) (by norm_num)
theorem B1278653 : Blo 850355 1278653 := bbase (se 3 (by rfl) ⟨239747, by rfl⟩ : syracuseStep 1278653 = 479495) (by norm_num)
theorem B3637973 : Blo 850355 3637973 := bbase (se 7 (by rfl) ⟨42632, by rfl⟩ : syracuseStep 3637973 = 85265) (by norm_num)
theorem B1278677 : Blo 850355 1278677 := bbase (se 7 (by rfl) ⟨14984, by rfl⟩ : syracuseStep 1278677 = 29969) (by norm_num)
theorem B1278701 : Blo 850355 1278701 := bbase (se 3 (by rfl) ⟨239756, by rfl⟩ : syracuseStep 1278701 = 479513) (by norm_num)
theorem B2425589 : Blo 850355 2425589 := bbase (se 5 (by rfl) ⟨113699, by rfl⟩ : syracuseStep 2425589 = 227399) (by norm_num)
theorem B4096757 : Blo 850355 4096757 := bbase (se 5 (by rfl) ⟨192035, by rfl⟩ : syracuseStep 4096757 = 384071) (by norm_num)
theorem B1278725 : Blo 850355 1278725 := bbase (se 4 (by rfl) ⟨119880, by rfl⟩ : syracuseStep 1278725 = 239761) (by norm_num)
theorem B1278749 : Blo 850355 1278749 := bbase (se 3 (by rfl) ⟨239765, by rfl⟩ : syracuseStep 1278749 = 479531) (by norm_num)
theorem B1278773 : Blo 850355 1278773 := bbase (se 5 (by rfl) ⟨59942, by rfl⟩ : syracuseStep 1278773 = 119885) (by norm_num)
theorem B1278797 : Blo 850355 1278797 := bbase (se 3 (by rfl) ⟨239774, by rfl⟩ : syracuseStep 1278797 = 479549) (by norm_num)
theorem B1278821 : Blo 850355 1278821 := bbase (se 4 (by rfl) ⟨119889, by rfl⟩ : syracuseStep 1278821 = 239779) (by norm_num)
theorem B1278845 : Blo 850355 1278845 := bbase (se 3 (by rfl) ⟨239783, by rfl⟩ : syracuseStep 1278845 = 479567) (by norm_num)
theorem B1278869 : Blo 850355 1278869 := bbase (se 6 (by rfl) ⟨29973, by rfl⟩ : syracuseStep 1278869 = 59947) (by norm_num)
theorem B1278893 : Blo 850355 1278893 := bbase (se 3 (by rfl) ⟨239792, by rfl⟩ : syracuseStep 1278893 = 479585) (by norm_num)
theorem B1278917 : Blo 850355 1278917 := bbase (se 4 (by rfl) ⟨119898, by rfl⟩ : syracuseStep 1278917 = 239797) (by norm_num)
theorem B1278941 : Blo 850355 1278941 := bbase (se 3 (by rfl) ⟨239801, by rfl⟩ : syracuseStep 1278941 = 479603) (by norm_num)
theorem B1278965 : Blo 850355 1278965 := bbase (se 5 (by rfl) ⟨59951, by rfl⟩ : syracuseStep 1278965 = 119903) (by norm_num)
theorem B1278989 : Blo 850355 1278989 := bbase (se 3 (by rfl) ⟨239810, by rfl⟩ : syracuseStep 1278989 = 479621) (by norm_num)
theorem B1279013 : Blo 850355 1279013 := bbase (se 4 (by rfl) ⟨119907, by rfl⟩ : syracuseStep 1279013 = 239815) (by norm_num)
theorem B1279037 : Blo 850355 1279037 := bbase (se 3 (by rfl) ⟨239819, by rfl⟩ : syracuseStep 1279037 = 479639) (by norm_num)
theorem B1279061 : Blo 850355 1279061 := bbase (se 8 (by rfl) ⟨7494, by rfl⟩ : syracuseStep 1279061 = 14989) (by norm_num)
theorem B1279085 : Blo 850355 1279085 := bbase (se 3 (by rfl) ⟨239828, by rfl⟩ : syracuseStep 1279085 = 479657) (by norm_num)
theorem B1279109 : Blo 850355 1279109 := bbase (se 4 (by rfl) ⟨119916, by rfl⟩ : syracuseStep 1279109 = 239833) (by norm_num)
theorem B1279133 : Blo 850355 1279133 := bbase (se 3 (by rfl) ⟨239837, by rfl⟩ : syracuseStep 1279133 = 479675) (by norm_num)
theorem B2426021 : Blo 850355 2426021 := bbase (se 4 (by rfl) ⟨227439, by rfl⟩ : syracuseStep 2426021 = 454879) (by norm_num)
theorem B1279157 : Blo 850355 1279157 := bbase (se 5 (by rfl) ⟨59960, by rfl⟩ : syracuseStep 1279157 = 119921) (by norm_num)
theorem B1279181 : Blo 850355 1279181 := bbase (se 3 (by rfl) ⟨239846, by rfl⟩ : syracuseStep 1279181 = 479693) (by norm_num)
theorem B5473493 : Blo 850355 5473493 := bbase (se 7 (by rfl) ⟨64142, by rfl⟩ : syracuseStep 5473493 = 128285) (by norm_num)
theorem B1279205 : Blo 850355 1279205 := bbase (se 4 (by rfl) ⟨119925, by rfl⟩ : syracuseStep 1279205 = 239851) (by norm_num)
theorem B1279229 : Blo 850355 1279229 := bbase (se 3 (by rfl) ⟨239855, by rfl⟩ : syracuseStep 1279229 = 479711) (by norm_num)
theorem B1213717 : Blo 850355 1213717 := bbase (se 6 (by rfl) ⟨28446, by rfl⟩ : syracuseStep 1213717 = 56893) (by norm_num)
theorem B1279253 : Blo 850355 1279253 := bbase (se 6 (by rfl) ⟨29982, by rfl⟩ : syracuseStep 1279253 = 59965) (by norm_num)
theorem B1279277 : Blo 850355 1279277 := bbase (se 3 (by rfl) ⟨239864, by rfl⟩ : syracuseStep 1279277 = 479729) (by norm_num)
theorem B1279301 : Blo 850355 1279301 := bbase (se 4 (by rfl) ⟨119934, by rfl⟩ : syracuseStep 1279301 = 239869) (by norm_num)
theorem B1279325 : Blo 850355 1279325 := bbase (se 3 (by rfl) ⟨239873, by rfl⟩ : syracuseStep 1279325 = 479747) (by norm_num)
theorem B1279349 : Blo 850355 1279349 := bbase (se 5 (by rfl) ⟨59969, by rfl⟩ : syracuseStep 1279349 = 119939) (by norm_num)
theorem B1279373 : Blo 850355 1279373 := bbase (se 3 (by rfl) ⟨239882, by rfl⟩ : syracuseStep 1279373 = 479765) (by norm_num)
theorem B1279397 : Blo 850355 1279397 := bbase (se 4 (by rfl) ⟨119943, by rfl⟩ : syracuseStep 1279397 = 239887) (by norm_num)
theorem B1279421 : Blo 850355 1279421 := bbase (se 3 (by rfl) ⟨239891, by rfl⟩ : syracuseStep 1279421 = 479783) (by norm_num)
theorem B1279445 : Blo 850355 1279445 := bbase (se 7 (by rfl) ⟨14993, by rfl⟩ : syracuseStep 1279445 = 29987) (by norm_num)
theorem B1279469 : Blo 850355 1279469 := bbase (se 3 (by rfl) ⟨239900, by rfl⟩ : syracuseStep 1279469 = 479801) (by norm_num)
theorem B1279493 : Blo 850355 1279493 := bbase (se 4 (by rfl) ⟨119952, by rfl⟩ : syracuseStep 1279493 = 239905) (by norm_num)
theorem B1279517 : Blo 850355 1279517 := bbase (se 3 (by rfl) ⟨239909, by rfl⟩ : syracuseStep 1279517 = 479819) (by norm_num)
theorem B1279541 : Blo 850355 1279541 := bbase (se 5 (by rfl) ⟨59978, by rfl⟩ : syracuseStep 1279541 = 119957) (by norm_num)
theorem B1279565 : Blo 850355 1279565 := bbase (se 3 (by rfl) ⟨239918, by rfl⟩ : syracuseStep 1279565 = 479837) (by norm_num)
theorem B1279589 : Blo 850355 1279589 := bbase (se 4 (by rfl) ⟨119961, by rfl⟩ : syracuseStep 1279589 = 239923) (by norm_num)
theorem B1279613 : Blo 850355 1279613 := bbase (se 3 (by rfl) ⟨239927, by rfl⟩ : syracuseStep 1279613 = 479855) (by norm_num)
theorem B1279637 : Blo 850355 1279637 := bbase (se 6 (by rfl) ⟨29991, by rfl⟩ : syracuseStep 1279637 = 59983) (by norm_num)
theorem B1279661 : Blo 850355 1279661 := bbase (se 3 (by rfl) ⟨239936, by rfl⟩ : syracuseStep 1279661 = 479873) (by norm_num)
theorem B1279685 : Blo 850355 1279685 := bbase (se 4 (by rfl) ⟨119970, by rfl⟩ : syracuseStep 1279685 = 239941) (by norm_num)
theorem B1279709 : Blo 850355 1279709 := bbase (se 3 (by rfl) ⟨239945, by rfl⟩ : syracuseStep 1279709 = 479891) (by norm_num)
theorem B1279733 : Blo 850355 1279733 := bbase (se 5 (by rfl) ⟨59987, by rfl⟩ : syracuseStep 1279733 = 119975) (by norm_num)
theorem B1967885 : Blo 850355 1967885 := bbase (se 3 (by rfl) ⟨368978, by rfl⟩ : syracuseStep 1967885 = 737957) (by norm_num)
theorem B1279757 : Blo 850355 1279757 := bbase (se 3 (by rfl) ⟨239954, by rfl⟩ : syracuseStep 1279757 = 479909) (by norm_num)
theorem B1279781 : Blo 850355 1279781 := bbase (se 4 (by rfl) ⟨119979, by rfl⟩ : syracuseStep 1279781 = 239959) (by norm_num)
theorem B1279805 : Blo 850355 1279805 := bbase (se 3 (by rfl) ⟨239963, by rfl⟩ : syracuseStep 1279805 = 479927) (by norm_num)
theorem B1279829 : Blo 850355 1279829 := bbase (se 9 (by rfl) ⟨3749, by rfl⟩ : syracuseStep 1279829 = 7499) (by norm_num)
theorem B1214309 : Blo 850355 1214309 := bbase (se 4 (by rfl) ⟨113841, by rfl⟩ : syracuseStep 1214309 = 227683) (by norm_num)
theorem B1279853 : Blo 850355 1279853 := bbase (se 3 (by rfl) ⟨239972, by rfl⟩ : syracuseStep 1279853 = 479945) (by norm_num)
theorem B1279877 : Blo 850355 1279877 := bbase (se 4 (by rfl) ⟨119988, by rfl⟩ : syracuseStep 1279877 = 239977) (by norm_num)
theorem B2426773 : Blo 850355 2426773 := bbase (se 6 (by rfl) ⟨56877, by rfl⟩ : syracuseStep 2426773 = 113755) (by norm_num)
theorem B1279901 : Blo 850355 1279901 := bbase (se 3 (by rfl) ⟨239981, by rfl⟩ : syracuseStep 1279901 = 479963) (by norm_num)
theorem B1214389 : Blo 850355 1214389 := bbase (se 5 (by rfl) ⟨56924, by rfl⟩ : syracuseStep 1214389 = 113849) (by norm_num)
theorem B1279925 : Blo 850355 1279925 := bbase (se 5 (by rfl) ⟨59996, by rfl⟩ : syracuseStep 1279925 = 119993) (by norm_num)
theorem B1279949 : Blo 850355 1279949 := bbase (se 3 (by rfl) ⟨239990, by rfl⟩ : syracuseStep 1279949 = 479981) (by norm_num)
theorem B1279973 : Blo 850355 1279973 := bbase (se 4 (by rfl) ⟨119997, by rfl⟩ : syracuseStep 1279973 = 239995) (by norm_num)
theorem B1279997 : Blo 850355 1279997 := bbase (se 3 (by rfl) ⟨239999, by rfl⟩ : syracuseStep 1279997 = 479999) (by norm_num)
theorem B1640461 : Blo 850355 1640461 := bbase (se 3 (by rfl) ⟨307586, by rfl⟩ : syracuseStep 1640461 = 615173) (by norm_num)
theorem B1280021 : Blo 850355 1280021 := bbase (se 6 (by rfl) ⟨30000, by rfl⟩ : syracuseStep 1280021 = 60001) (by norm_num)
theorem B1214509 : Blo 850355 1214509 := bbase (se 3 (by rfl) ⟨227720, by rfl⟩ : syracuseStep 1214509 = 455441) (by norm_num)
theorem B1280045 : Blo 850355 1280045 := bbase (se 3 (by rfl) ⟨240008, by rfl⟩ : syracuseStep 1280045 = 480017) (by norm_num)
theorem B1280069 : Blo 850355 1280069 := bbase (se 4 (by rfl) ⟨120006, by rfl⟩ : syracuseStep 1280069 = 240013) (by norm_num)
theorem B1280093 : Blo 850355 1280093 := bbase (se 3 (by rfl) ⟨240017, by rfl⟩ : syracuseStep 1280093 = 480035) (by norm_num)
theorem B1280117 : Blo 850355 1280117 := bbase (se 5 (by rfl) ⟨60005, by rfl⟩ : syracuseStep 1280117 = 120011) (by norm_num)
theorem B1214605 : Blo 850355 1214605 := bbase (se 3 (by rfl) ⟨227738, by rfl⟩ : syracuseStep 1214605 = 455477) (by norm_num)
theorem B1280141 : Blo 850355 1280141 := bbase (se 3 (by rfl) ⟨240026, by rfl⟩ : syracuseStep 1280141 = 480053) (by norm_num)
theorem B1280165 : Blo 850355 1280165 := bbase (se 4 (by rfl) ⟨120015, by rfl⟩ : syracuseStep 1280165 = 240031) (by norm_num)
theorem B1280189 : Blo 850355 1280189 := bbase (se 3 (by rfl) ⟨240035, by rfl⟩ : syracuseStep 1280189 = 480071) (by norm_num)
theorem B1280213 : Blo 850355 1280213 := bbase (se 7 (by rfl) ⟨15002, by rfl⟩ : syracuseStep 1280213 = 30005) (by norm_num)
theorem B1280237 : Blo 850355 1280237 := bbase (se 3 (by rfl) ⟨240044, by rfl⟩ : syracuseStep 1280237 = 480089) (by norm_num)
theorem B2459909 : Blo 850355 2459909 := bbase (se 4 (by rfl) ⟨230616, by rfl⟩ : syracuseStep 2459909 = 461233) (by norm_num)
theorem B1280261 : Blo 850355 1280261 := bbase (se 4 (by rfl) ⟨120024, by rfl⟩ : syracuseStep 1280261 = 240049) (by norm_num)
theorem B1280285 : Blo 850355 1280285 := bbase (se 3 (by rfl) ⟨240053, by rfl⟩ : syracuseStep 1280285 = 480107) (by norm_num)
theorem B1280309 : Blo 850355 1280309 := bbase (se 5 (by rfl) ⟨60014, by rfl⟩ : syracuseStep 1280309 = 120029) (by norm_num)
theorem B1280333 : Blo 850355 1280333 := bbase (se 3 (by rfl) ⟨240062, by rfl⟩ : syracuseStep 1280333 = 480125) (by norm_num)
theorem B1280357 : Blo 850355 1280357 := bbase (se 4 (by rfl) ⟨120033, by rfl⟩ : syracuseStep 1280357 = 240067) (by norm_num)
theorem B1280381 : Blo 850355 1280381 := bbase (se 3 (by rfl) ⟨240071, by rfl⟩ : syracuseStep 1280381 = 480143) (by norm_num)
theorem B8751509 : Blo 850355 8751509 := bbase (se 6 (by rfl) ⟨205113, by rfl⟩ : syracuseStep 8751509 = 410227) (by norm_num)
theorem B1280405 : Blo 850355 1280405 := bbase (se 6 (by rfl) ⟨30009, by rfl⟩ : syracuseStep 1280405 = 60019) (by norm_num)
theorem B1280429 : Blo 850355 1280429 := bbase (se 3 (by rfl) ⟨240080, by rfl⟩ : syracuseStep 1280429 = 480161) (by norm_num)
theorem B1280453 : Blo 850355 1280453 := bbase (se 4 (by rfl) ⟨120042, by rfl⟩ : syracuseStep 1280453 = 240085) (by norm_num)
theorem B1280477 : Blo 850355 1280477 := bbase (se 3 (by rfl) ⟨240089, by rfl⟩ : syracuseStep 1280477 = 480179) (by norm_num)
theorem B1280501 : Blo 850355 1280501 := bbase (se 5 (by rfl) ⟨60023, by rfl⟩ : syracuseStep 1280501 = 120047) (by norm_num)
theorem B1280525 : Blo 850355 1280525 := bbase (se 3 (by rfl) ⟨240098, by rfl⟩ : syracuseStep 1280525 = 480197) (by norm_num)
theorem B1280549 : Blo 850355 1280549 := bbase (se 4 (by rfl) ⟨120051, by rfl⟩ : syracuseStep 1280549 = 240103) (by norm_num)
theorem B1280573 : Blo 850355 1280573 := bbase (se 3 (by rfl) ⟨240107, by rfl⟩ : syracuseStep 1280573 = 480215) (by norm_num)
theorem B1280597 : Blo 850355 1280597 := bbase (se 8 (by rfl) ⟨7503, by rfl⟩ : syracuseStep 1280597 = 15007) (by norm_num)
theorem B1280621 : Blo 850355 1280621 := bbase (se 3 (by rfl) ⟨240116, by rfl⟩ : syracuseStep 1280621 = 480233) (by norm_num)
theorem B1215101 : Blo 850355 1215101 := bbase (se 3 (by rfl) ⟨227831, by rfl⟩ : syracuseStep 1215101 = 455663) (by norm_num)
theorem B1280645 : Blo 850355 1280645 := bbase (se 4 (by rfl) ⟨120060, by rfl⟩ : syracuseStep 1280645 = 240121) (by norm_num)
theorem B1280669 : Blo 850355 1280669 := bbase (se 3 (by rfl) ⟨240125, by rfl⟩ : syracuseStep 1280669 = 480251) (by norm_num)
theorem B1280693 : Blo 850355 1280693 := bbase (se 5 (by rfl) ⟨60032, by rfl⟩ : syracuseStep 1280693 = 120065) (by norm_num)
theorem B1280717 : Blo 850355 1280717 := bbase (se 3 (by rfl) ⟨240134, by rfl⟩ : syracuseStep 1280717 = 480269) (by norm_num)
theorem B1280741 : Blo 850355 1280741 := bbase (se 4 (by rfl) ⟨120069, by rfl⟩ : syracuseStep 1280741 = 240139) (by norm_num)
theorem B1280765 : Blo 850355 1280765 := bbase (se 3 (by rfl) ⟨240143, by rfl⟩ : syracuseStep 1280765 = 480287) (by norm_num)
theorem B1280789 : Blo 850355 1280789 := bbase (se 6 (by rfl) ⟨30018, by rfl⟩ : syracuseStep 1280789 = 60037) (by norm_num)
theorem B1280813 : Blo 850355 1280813 := bbase (se 3 (by rfl) ⟨240152, by rfl⟩ : syracuseStep 1280813 = 480305) (by norm_num)
theorem B1280837 : Blo 850355 1280837 := bbase (se 4 (by rfl) ⟨120078, by rfl⟩ : syracuseStep 1280837 = 240157) (by norm_num)
theorem B1280861 : Blo 850355 1280861 := bbase (se 3 (by rfl) ⟨240161, by rfl⟩ : syracuseStep 1280861 = 480323) (by norm_num)
theorem B1280885 : Blo 850355 1280885 := bbase (se 5 (by rfl) ⟨60041, by rfl⟩ : syracuseStep 1280885 = 120083) (by norm_num)
theorem B1280909 : Blo 850355 1280909 := bbase (se 3 (by rfl) ⟨240170, by rfl⟩ : syracuseStep 1280909 = 480341) (by norm_num)
theorem B920473 : Blo 850355 920473 := bbase (se 2 (by rfl) ⟨345177, by rfl⟩ : syracuseStep 920473 = 690355) (by norm_num)
theorem B1280933 : Blo 850355 1280933 := bbase (se 4 (by rfl) ⟨120087, by rfl⟩ : syracuseStep 1280933 = 240175) (by norm_num)
theorem B1280957 : Blo 850355 1280957 := bbase (se 3 (by rfl) ⟨240179, by rfl⟩ : syracuseStep 1280957 = 480359) (by norm_num)
theorem B1280981 : Blo 850355 1280981 := bbase (se 7 (by rfl) ⟨15011, by rfl⟩ : syracuseStep 1280981 = 30023) (by norm_num)
theorem B1281005 : Blo 850355 1281005 := bbase (se 3 (by rfl) ⟨240188, by rfl⟩ : syracuseStep 1281005 = 480377) (by norm_num)
theorem B1281029 : Blo 850355 1281029 := bbase (se 4 (by rfl) ⟨120096, by rfl⟩ : syracuseStep 1281029 = 240193) (by norm_num)
theorem B1281053 : Blo 850355 1281053 := bbase (se 3 (by rfl) ⟨240197, by rfl⟩ : syracuseStep 1281053 = 480395) (by norm_num)
theorem B1281077 : Blo 850355 1281077 := bbase (se 5 (by rfl) ⟨60050, by rfl⟩ : syracuseStep 1281077 = 120101) (by norm_num)
theorem B1281101 : Blo 850355 1281101 := bbase (se 3 (by rfl) ⟨240206, by rfl⟩ : syracuseStep 1281101 = 480413) (by norm_num)
theorem B6458453 : Blo 850355 6458453 := bbase (se 8 (by rfl) ⟨37842, by rfl⟩ : syracuseStep 6458453 = 75685) (by norm_num)
theorem B1281125 : Blo 850355 1281125 := bbase (se 4 (by rfl) ⟨120105, by rfl⟩ : syracuseStep 1281125 = 240211) (by norm_num)
theorem B1281149 : Blo 850355 1281149 := bbase (se 3 (by rfl) ⟨240215, by rfl⟩ : syracuseStep 1281149 = 480431) (by norm_num)
theorem B1281173 : Blo 850355 1281173 := bbase (se 6 (by rfl) ⟨30027, by rfl⟩ : syracuseStep 1281173 = 60055) (by norm_num)
theorem B1215653 : Blo 850355 1215653 := bbase (se 4 (by rfl) ⟨113967, by rfl⟩ : syracuseStep 1215653 = 227935) (by norm_num)
theorem B1281197 : Blo 850355 1281197 := bbase (se 3 (by rfl) ⟨240224, by rfl⟩ : syracuseStep 1281197 = 480449) (by norm_num)
theorem B1281221 : Blo 850355 1281221 := bbase (se 4 (by rfl) ⟨120114, by rfl⟩ : syracuseStep 1281221 = 240229) (by norm_num)
theorem B1281245 : Blo 850355 1281245 := bbase (se 3 (by rfl) ⟨240233, by rfl⟩ : syracuseStep 1281245 = 480467) (by norm_num)
theorem B1281269 : Blo 850355 1281269 := bbase (se 5 (by rfl) ⟨60059, by rfl⟩ : syracuseStep 1281269 = 120119) (by norm_num)
theorem B1051913 : Blo 850355 1051913 := bbase (se 2 (by rfl) ⟨394467, by rfl⟩ : syracuseStep 1051913 = 788935) (by norm_num)
theorem B1281293 : Blo 850355 1281293 := bbase (se 3 (by rfl) ⟨240242, by rfl⟩ : syracuseStep 1281293 = 480485) (by norm_num)
theorem B1281317 : Blo 850355 1281317 := bbase (se 4 (by rfl) ⟨120123, by rfl⟩ : syracuseStep 1281317 = 240247) (by norm_num)
theorem B1281341 : Blo 850355 1281341 := bbase (se 3 (by rfl) ⟨240251, by rfl⟩ : syracuseStep 1281341 = 480503) (by norm_num)
theorem B1281365 : Blo 850355 1281365 := bbase (se 11 (by rfl) ⟨938, by rfl⟩ : syracuseStep 1281365 = 1877) (by norm_num)
theorem B1281389 : Blo 850355 1281389 := bbase (se 3 (by rfl) ⟨240260, by rfl⟩ : syracuseStep 1281389 = 480521) (by norm_num)
theorem B1281413 : Blo 850355 1281413 := bbase (se 4 (by rfl) ⟨120132, by rfl⟩ : syracuseStep 1281413 = 240265) (by norm_num)
theorem B10390933 : Blo 850355 10390933 := bbase (se 6 (by rfl) ⟨243537, by rfl⟩ : syracuseStep 10390933 = 487075) (by norm_num)
theorem B1478045 : Blo 850355 1478045 := bbase (se 3 (by rfl) ⟨277133, by rfl⟩ : syracuseStep 1478045 = 554267) (by norm_num)
theorem B1281437 : Blo 850355 1281437 := bbase (se 3 (by rfl) ⟨240269, by rfl⟩ : syracuseStep 1281437 = 480539) (by norm_num)
theorem B8195509 : Blo 850355 8195509 := bbase (se 5 (by rfl) ⟨384164, by rfl⟩ : syracuseStep 8195509 = 768329) (by norm_num)
theorem B1281461 : Blo 850355 1281461 := bbase (se 5 (by rfl) ⟨60068, by rfl⟩ : syracuseStep 1281461 = 120137) (by norm_num)
theorem B1281485 : Blo 850355 1281485 := bbase (se 3 (by rfl) ⟨240278, by rfl⟩ : syracuseStep 1281485 = 480557) (by norm_num)
theorem B7769557 : Blo 850355 7769557 := bbase (se 7 (by rfl) ⟨91049, by rfl⟩ : syracuseStep 7769557 = 182099) (by norm_num)
theorem B1281509 : Blo 850355 1281509 := bbase (se 4 (by rfl) ⟨120141, by rfl⟩ : syracuseStep 1281509 = 240283) (by norm_num)
theorem B1281533 : Blo 850355 1281533 := bbase (se 3 (by rfl) ⟨240287, by rfl⟩ : syracuseStep 1281533 = 480575) (by norm_num)
theorem B4918805 : Blo 850355 4918805 := bbase (se 6 (by rfl) ⟨115284, by rfl⟩ : syracuseStep 4918805 = 230569) (by norm_num)
theorem B2428453 : Blo 850355 2428453 := bbase (se 4 (by rfl) ⟨227667, by rfl⟩ : syracuseStep 2428453 = 455335) (by norm_num)
theorem B3935861 : Blo 850355 3935861 := bbase (se 5 (by rfl) ⟨184493, by rfl⟩ : syracuseStep 3935861 = 368987) (by norm_num)
theorem B1642141 : Blo 850355 1642141 := bbase (se 3 (by rfl) ⟨307901, by rfl⟩ : syracuseStep 1642141 = 615803) (by norm_num)
theorem B1052461 : Blo 850355 1052461 := bbase (se 3 (by rfl) ⟨197336, by rfl⟩ : syracuseStep 1052461 = 394673) (by norm_num)
theorem B1216405 : Blo 850355 1216405 := bbase (se 6 (by rfl) ⟨28509, by rfl⟩ : syracuseStep 1216405 = 57019) (by norm_num)
theorem B1642925 : Blo 850355 1642925 := bbase (se 3 (by rfl) ⟨308048, by rfl⟩ : syracuseStep 1642925 = 616097) (by norm_num)
theorem B1151581 : Blo 850355 1151581 := bbase (se 3 (by rfl) ⟨215921, by rfl⟩ : syracuseStep 1151581 = 431843) (by norm_num)
theorem B1151597 : Blo 850355 1151597 := bbase (se 3 (by rfl) ⟨215924, by rfl⟩ : syracuseStep 1151597 = 431849) (by norm_num)
theorem B1380997 : Blo 850355 1380997 := bbase (se 4 (by rfl) ⟨129468, by rfl⟩ : syracuseStep 1380997 = 258937) (by norm_num)
theorem B2429621 : Blo 850355 2429621 := bbase (se 5 (by rfl) ⟨113888, by rfl⟩ : syracuseStep 2429621 = 227777) (by norm_num)
theorem B3642245 : Blo 850355 3642245 := bbase (se 4 (by rfl) ⟨341460, by rfl⟩ : syracuseStep 3642245 = 682921) (by norm_num)
theorem B4101445 : Blo 850355 4101445 := bbase (se 4 (by rfl) ⟨384510, by rfl⟩ : syracuseStep 4101445 = 769021) (by norm_num)
theorem B1873405 : Blo 850355 1873405 := bbase (se 3 (by rfl) ⟨351263, by rfl⟩ : syracuseStep 1873405 = 702527) (by norm_num)
theorem B2397701 : Blo 850355 2397701 := bbase (se 4 (by rfl) ⟨224784, by rfl⟩ : syracuseStep 2397701 = 449569) (by norm_num)
theorem B1152797 : Blo 850355 1152797 := bbase (se 3 (by rfl) ⟨216149, by rfl⟩ : syracuseStep 1152797 = 432299) (by norm_num)
theorem B1021729 : Blo 850355 1021729 := bbase (se 2 (by rfl) ⟨383148, by rfl⟩ : syracuseStep 1021729 = 766297) (by norm_num)
theorem B2430805 : Blo 850355 2430805 := bbase (se 9 (by rfl) ⟨7121, by rfl⟩ : syracuseStep 2430805 = 14243) (by norm_num)
theorem B2135933 : Blo 850355 2135933 := bbase (se 3 (by rfl) ⟨400487, by rfl⟩ : syracuseStep 2135933 = 800975) (by norm_num)
theorem B4855733 : Blo 850355 4855733 := bbase (se 5 (by rfl) ⟨227612, by rfl⟩ : syracuseStep 4855733 = 455225) (by norm_num)
theorem B1152965 : Blo 850355 1152965 := bbase (se 4 (by rfl) ⟨108090, by rfl⟩ : syracuseStep 1152965 = 216181) (by norm_num)
theorem B2430965 : Blo 850355 2430965 := bbase (se 5 (by rfl) ⟨113951, by rfl⟩ : syracuseStep 2430965 = 227903) (by norm_num)
theorem B2431205 : Blo 850355 2431205 := bbase (se 4 (by rfl) ⟨227925, by rfl⟩ : syracuseStep 2431205 = 455851) (by norm_num)
theorem B1022209 : Blo 850355 1022209 := bbase (se 2 (by rfl) ⟨383328, by rfl⟩ : syracuseStep 1022209 = 766657) (by norm_num)
theorem B956677 : Blo 850355 956677 := bbase (se 4 (by rfl) ⟨89688, by rfl⟩ : syracuseStep 956677 = 179377) (by norm_num)
theorem B956713 : Blo 850355 956713 := bbase (se 2 (by rfl) ⟨358767, by rfl⟩ : syracuseStep 956713 = 717535) (by norm_num)
theorem B956749 : Blo 850355 956749 := bbase (se 3 (by rfl) ⟨179390, by rfl⟩ : syracuseStep 956749 = 358781) (by norm_num)
theorem B956785 : Blo 850355 956785 := bbase (se 2 (by rfl) ⟨358794, by rfl⟩ : syracuseStep 956785 = 717589) (by norm_num)
theorem B956821 : Blo 850355 956821 := bbase (se 6 (by rfl) ⟨22425, by rfl⟩ : syracuseStep 956821 = 44851) (by norm_num)
theorem B2431397 : Blo 850355 2431397 := bbase (se 4 (by rfl) ⟨227943, by rfl⟩ : syracuseStep 2431397 = 455887) (by norm_num)
theorem B956857 : Blo 850355 956857 := bbase (se 2 (by rfl) ⟨358821, by rfl⟩ : syracuseStep 956857 = 717643) (by norm_num)
theorem B956893 : Blo 850355 956893 := bbase (se 3 (by rfl) ⟨179417, by rfl⟩ : syracuseStep 956893 = 358835) (by norm_num)
theorem B956929 : Blo 850355 956929 := bbase (se 2 (by rfl) ⟨358848, by rfl⟩ : syracuseStep 956929 = 717697) (by norm_num)
theorem B956965 : Blo 850355 956965 := bbase (se 4 (by rfl) ⟨89715, by rfl⟩ : syracuseStep 956965 = 179431) (by norm_num)
theorem B957001 : Blo 850355 957001 := bbase (se 2 (by rfl) ⟨358875, by rfl⟩ : syracuseStep 957001 = 717751) (by norm_num)
theorem B957037 : Blo 850355 957037 := bbase (se 3 (by rfl) ⟨179444, by rfl⟩ : syracuseStep 957037 = 358889) (by norm_num)
theorem B3644021 : Blo 850355 3644021 := bbase (se 5 (by rfl) ⟨170813, by rfl⟩ : syracuseStep 3644021 = 341627) (by norm_num)
theorem B957073 : Blo 850355 957073 := bbase (se 2 (by rfl) ⟨358902, by rfl⟩ : syracuseStep 957073 = 717805) (by norm_num)
theorem B957109 : Blo 850355 957109 := bbase (se 5 (by rfl) ⟨44864, by rfl⟩ : syracuseStep 957109 = 89729) (by norm_num)
theorem B2726597 : Blo 850355 2726597 := bbase (se 4 (by rfl) ⟨255618, by rfl⟩ : syracuseStep 2726597 = 511237) (by norm_num)
theorem B957145 : Blo 850355 957145 := bbase (se 2 (by rfl) ⟨358929, by rfl⟩ : syracuseStep 957145 = 717859) (by norm_num)
theorem B957181 : Blo 850355 957181 := bbase (se 3 (by rfl) ⟨179471, by rfl⟩ : syracuseStep 957181 = 358943) (by norm_num)
theorem B957217 : Blo 850355 957217 := bbase (se 2 (by rfl) ⟨358956, by rfl⟩ : syracuseStep 957217 = 717913) (by norm_num)
theorem B957253 : Blo 850355 957253 := bbase (se 4 (by rfl) ⟨89742, by rfl⟩ : syracuseStep 957253 = 179485) (by norm_num)
theorem B3644261 : Blo 850355 3644261 := bbase (se 4 (by rfl) ⟨341649, by rfl⟩ : syracuseStep 3644261 = 683299) (by norm_num)
theorem B957289 : Blo 850355 957289 := bbase (se 2 (by rfl) ⟨358983, by rfl⟩ : syracuseStep 957289 = 717967) (by norm_num)
theorem B3152773 : Blo 850355 3152773 := bbase (se 4 (by rfl) ⟨295572, by rfl⟩ : syracuseStep 3152773 = 591145) (by norm_num)
theorem B957325 : Blo 850355 957325 := bbase (se 3 (by rfl) ⟨179498, by rfl⟩ : syracuseStep 957325 = 358997) (by norm_num)
theorem B957361 : Blo 850355 957361 := bbase (se 2 (by rfl) ⟨359010, by rfl⟩ : syracuseStep 957361 = 718021) (by norm_num)
theorem B957397 : Blo 850355 957397 := bbase (se 7 (by rfl) ⟨11219, by rfl⟩ : syracuseStep 957397 = 22439) (by norm_num)
theorem B957433 : Blo 850355 957433 := bbase (se 2 (by rfl) ⟨359037, by rfl⟩ : syracuseStep 957433 = 718075) (by norm_num)
theorem B957469 : Blo 850355 957469 := bbase (se 3 (by rfl) ⟨179525, by rfl⟩ : syracuseStep 957469 = 359051) (by norm_num)
theorem B957505 : Blo 850355 957505 := bbase (se 2 (by rfl) ⟨359064, by rfl⟩ : syracuseStep 957505 = 718129) (by norm_num)
theorem B6134869 : Blo 850355 6134869 := bbase (se 8 (by rfl) ⟨35946, by rfl⟩ : syracuseStep 6134869 = 71893) (by norm_num)
theorem B957541 : Blo 850355 957541 := bbase (se 4 (by rfl) ⟨89769, by rfl⟩ : syracuseStep 957541 = 179539) (by norm_num)
theorem B1023089 : Blo 850355 1023089 := bbase (se 2 (by rfl) ⟨383658, by rfl⟩ : syracuseStep 1023089 = 767317) (by norm_num)
theorem B957577 : Blo 850355 957577 := bbase (se 2 (by rfl) ⟨359091, by rfl⟩ : syracuseStep 957577 = 718183) (by norm_num)
theorem B957613 : Blo 850355 957613 := bbase (se 3 (by rfl) ⟨179552, by rfl⟩ : syracuseStep 957613 = 359105) (by norm_num)
theorem B957649 : Blo 850355 957649 := bbase (se 2 (by rfl) ⟨359118, by rfl⟩ : syracuseStep 957649 = 718237) (by norm_num)
theorem B1023205 : Blo 850355 1023205 := bbase (se 4 (by rfl) ⟨95925, by rfl⟩ : syracuseStep 1023205 = 191851) (by norm_num)
theorem B957685 : Blo 850355 957685 := bbase (se 5 (by rfl) ⟨44891, by rfl⟩ : syracuseStep 957685 = 89783) (by norm_num)
theorem B1842437 : Blo 850355 1842437 := bbase (se 4 (by rfl) ⟨172728, by rfl⟩ : syracuseStep 1842437 = 345457) (by norm_num)
theorem B957721 : Blo 850355 957721 := bbase (se 2 (by rfl) ⟨359145, by rfl⟩ : syracuseStep 957721 = 718291) (by norm_num)
theorem B957757 : Blo 850355 957757 := bbase (se 3 (by rfl) ⟨179579, by rfl⟩ : syracuseStep 957757 = 359159) (by norm_num)
theorem B957793 : Blo 850355 957793 := bbase (se 2 (by rfl) ⟨359172, by rfl⟩ : syracuseStep 957793 = 718345) (by norm_num)
theorem B957829 : Blo 850355 957829 := bbase (se 4 (by rfl) ⟨89796, by rfl⟩ : syracuseStep 957829 = 179593) (by norm_num)
theorem B2432389 : Blo 850355 2432389 := bbase (se 4 (by rfl) ⟨228036, by rfl⟩ : syracuseStep 2432389 = 456073) (by norm_num)
theorem B957865 : Blo 850355 957865 := bbase (se 2 (by rfl) ⟨359199, by rfl⟩ : syracuseStep 957865 = 718399) (by norm_num)
theorem B1023401 : Blo 850355 1023401 := bbase (se 2 (by rfl) ⟨383775, by rfl⟩ : syracuseStep 1023401 = 767551) (by norm_num)
theorem B957901 : Blo 850355 957901 := bbase (se 3 (by rfl) ⟨179606, by rfl⟩ : syracuseStep 957901 = 359213) (by norm_num)
theorem B957937 : Blo 850355 957937 := bbase (se 2 (by rfl) ⟨359226, by rfl⟩ : syracuseStep 957937 = 718453) (by norm_num)
theorem B957973 : Blo 850355 957973 := bbase (se 6 (by rfl) ⟨22452, by rfl⟩ : syracuseStep 957973 = 44905) (by norm_num)
theorem B958009 : Blo 850355 958009 := bbase (se 2 (by rfl) ⟨359253, by rfl⟩ : syracuseStep 958009 = 718507) (by norm_num)
theorem B958045 : Blo 850355 958045 := bbase (se 3 (by rfl) ⟨179633, by rfl⟩ : syracuseStep 958045 = 359267) (by norm_num)
theorem B958081 : Blo 850355 958081 := bbase (se 2 (by rfl) ⟨359280, by rfl⟩ : syracuseStep 958081 = 718561) (by norm_num)
theorem B2301605 : Blo 850355 2301605 := bbase (se 4 (by rfl) ⟨215775, by rfl⟩ : syracuseStep 2301605 = 431551) (by norm_num)
theorem B958117 : Blo 850355 958117 := bbase (se 4 (by rfl) ⟨89823, by rfl⟩ : syracuseStep 958117 = 179647) (by norm_num)
theorem B958153 : Blo 850355 958153 := bbase (se 2 (by rfl) ⟨359307, by rfl⟩ : syracuseStep 958153 = 718615) (by norm_num)
theorem B958189 : Blo 850355 958189 := bbase (se 3 (by rfl) ⟨179660, by rfl⟩ : syracuseStep 958189 = 359321) (by norm_num)
theorem B3448565 : Blo 850355 3448565 := bbase (se 5 (by rfl) ⟨161651, by rfl⟩ : syracuseStep 3448565 = 323303) (by norm_num)
theorem B2727685 : Blo 850355 2727685 := bbase (se 4 (by rfl) ⟨255720, by rfl⟩ : syracuseStep 2727685 = 511441) (by norm_num)
theorem B958225 : Blo 850355 958225 := bbase (se 2 (by rfl) ⟨359334, by rfl⟩ : syracuseStep 958225 = 718669) (by norm_num)
theorem B958261 : Blo 850355 958261 := bbase (se 5 (by rfl) ⟨44918, by rfl⟩ : syracuseStep 958261 = 89837) (by norm_num)
theorem B6922037 : Blo 850355 6922037 := bbase (se 5 (by rfl) ⟨324470, by rfl⟩ : syracuseStep 6922037 = 648941) (by norm_num)
theorem B958297 : Blo 850355 958297 := bbase (se 2 (by rfl) ⟨359361, by rfl⟩ : syracuseStep 958297 = 718723) (by norm_num)
theorem B958333 : Blo 850355 958333 := bbase (se 3 (by rfl) ⟨179687, by rfl⟩ : syracuseStep 958333 = 359375) (by norm_num)
theorem B958369 : Blo 850355 958369 := bbase (se 2 (by rfl) ⟨359388, by rfl⟩ : syracuseStep 958369 = 718777) (by norm_num)
theorem B958405 : Blo 850355 958405 := bbase (se 4 (by rfl) ⟨89850, by rfl⟩ : syracuseStep 958405 = 179701) (by norm_num)
theorem B1023949 : Blo 850355 1023949 := bbase (se 3 (by rfl) ⟨191990, by rfl⟩ : syracuseStep 1023949 = 383981) (by norm_num)
theorem B958441 : Blo 850355 958441 := bbase (se 2 (by rfl) ⟨359415, by rfl⟩ : syracuseStep 958441 = 718831) (by norm_num)
theorem B958477 : Blo 850355 958477 := bbase (se 3 (by rfl) ⟨179714, by rfl⟩ : syracuseStep 958477 = 359429) (by norm_num)
theorem B958513 : Blo 850355 958513 := bbase (se 2 (by rfl) ⟨359442, by rfl⟩ : syracuseStep 958513 = 718885) (by norm_num)
theorem B958549 : Blo 850355 958549 := bbase (se 8 (by rfl) ⟨5616, by rfl⟩ : syracuseStep 958549 = 11233) (by norm_num)
theorem B1024093 : Blo 850355 1024093 := bbase (se 3 (by rfl) ⟨192017, by rfl⟩ : syracuseStep 1024093 = 384035) (by norm_num)
theorem B958585 : Blo 850355 958585 := bbase (se 2 (by rfl) ⟨359469, by rfl⟩ : syracuseStep 958585 = 718939) (by norm_num)
theorem B958621 : Blo 850355 958621 := bbase (se 3 (by rfl) ⟨179741, by rfl⟩ : syracuseStep 958621 = 359483) (by norm_num)
theorem B958657 : Blo 850355 958657 := bbase (se 2 (by rfl) ⟨359496, by rfl⟩ : syracuseStep 958657 = 718993) (by norm_num)
theorem B4923605 : Blo 850355 4923605 := bbase (se 7 (by rfl) ⟨57698, by rfl⟩ : syracuseStep 4923605 = 115397) (by norm_num)
theorem B958693 : Blo 850355 958693 := bbase (se 4 (by rfl) ⟨89877, by rfl⟩ : syracuseStep 958693 = 179755) (by norm_num)
theorem B958729 : Blo 850355 958729 := bbase (se 2 (by rfl) ⟨359523, by rfl⟩ : syracuseStep 958729 = 719047) (by norm_num)
theorem B958765 : Blo 850355 958765 := bbase (se 3 (by rfl) ⟨179768, by rfl⟩ : syracuseStep 958765 = 359537) (by norm_num)
theorem B958801 : Blo 850355 958801 := bbase (se 2 (by rfl) ⟨359550, by rfl⟩ : syracuseStep 958801 = 719101) (by norm_num)
theorem B958837 : Blo 850355 958837 := bbase (se 5 (by rfl) ⟨44945, by rfl⟩ : syracuseStep 958837 = 89891) (by norm_num)
theorem B958873 : Blo 850355 958873 := bbase (se 2 (by rfl) ⟨359577, by rfl⟩ : syracuseStep 958873 = 719155) (by norm_num)
theorem B2597285 : Blo 850355 2597285 := bbase (se 4 (by rfl) ⟨243495, by rfl⟩ : syracuseStep 2597285 = 486991) (by norm_num)
theorem B958909 : Blo 850355 958909 := bbase (se 3 (by rfl) ⟨179795, by rfl⟩ : syracuseStep 958909 = 359591) (by norm_num)
theorem B958945 : Blo 850355 958945 := bbase (se 2 (by rfl) ⟨359604, by rfl⟩ : syracuseStep 958945 = 719209) (by norm_num)
theorem B1516013 : Blo 850355 1516013 := bbase (se 3 (by rfl) ⟨284252, by rfl⟩ : syracuseStep 1516013 = 568505) (by norm_num)
theorem B958981 : Blo 850355 958981 := bbase (se 4 (by rfl) ⟨89904, by rfl⟩ : syracuseStep 958981 = 179809) (by norm_num)
theorem B959017 : Blo 850355 959017 := bbase (se 2 (by rfl) ⟨359631, by rfl⟩ : syracuseStep 959017 = 719263) (by norm_num)
theorem B959053 : Blo 850355 959053 := bbase (se 3 (by rfl) ⟨179822, by rfl⟩ : syracuseStep 959053 = 359645) (by norm_num)
theorem B959089 : Blo 850355 959089 := bbase (se 2 (by rfl) ⟨359658, by rfl⟩ : syracuseStep 959089 = 719317) (by norm_num)
theorem B1614485 : Blo 850355 1614485 := bbase (se 6 (by rfl) ⟨37839, by rfl⟩ : syracuseStep 1614485 = 75679) (by norm_num)
theorem B959125 : Blo 850355 959125 := bbase (se 6 (by rfl) ⟨22479, by rfl⟩ : syracuseStep 959125 = 44959) (by norm_num)
theorem B959161 : Blo 850355 959161 := bbase (se 2 (by rfl) ⟨359685, by rfl⟩ : syracuseStep 959161 = 719371) (by norm_num)
theorem B12264149 : Blo 850355 12264149 := bbase (se 7 (by rfl) ⟨143720, by rfl⟩ : syracuseStep 12264149 = 287441) (by norm_num)
theorem B959197 : Blo 850355 959197 := bbase (se 3 (by rfl) ⟨179849, by rfl⟩ : syracuseStep 959197 = 359699) (by norm_num)
theorem B959233 : Blo 850355 959233 := bbase (se 2 (by rfl) ⟨359712, by rfl⟩ : syracuseStep 959233 = 719425) (by norm_num)
theorem B1614629 : Blo 850355 1614629 := bbase (se 4 (by rfl) ⟨151371, by rfl⟩ : syracuseStep 1614629 = 302743) (by norm_num)
theorem B959269 : Blo 850355 959269 := bbase (se 4 (by rfl) ⟨89931, by rfl⟩ : syracuseStep 959269 = 179863) (by norm_num)
theorem B959305 : Blo 850355 959305 := bbase (se 2 (by rfl) ⟨359739, by rfl⟩ : syracuseStep 959305 = 719479) (by norm_num)
theorem B959341 : Blo 850355 959341 := bbase (se 3 (by rfl) ⟨179876, by rfl⟩ : syracuseStep 959341 = 359753) (by norm_num)
theorem B959377 : Blo 850355 959377 := bbase (se 2 (by rfl) ⟨359766, by rfl⟩ : syracuseStep 959377 = 719533) (by norm_num)
theorem B2728853 : Blo 850355 2728853 := bbase (se 6 (by rfl) ⟨63957, by rfl⟩ : syracuseStep 2728853 = 127915) (by norm_num)
theorem B959413 : Blo 850355 959413 := bbase (se 5 (by rfl) ⟨44972, by rfl⟩ : syracuseStep 959413 = 89945) (by norm_num)
theorem B959449 : Blo 850355 959449 := bbase (se 2 (by rfl) ⟨359793, by rfl⟩ : syracuseStep 959449 = 719587) (by norm_num)
theorem B959485 : Blo 850355 959485 := bbase (se 3 (by rfl) ⟨179903, by rfl⟩ : syracuseStep 959485 = 359807) (by norm_num)
theorem B959521 : Blo 850355 959521 := bbase (se 2 (by rfl) ⟨359820, by rfl⟩ : syracuseStep 959521 = 719641) (by norm_num)
theorem B1614917 : Blo 850355 1614917 := bbase (se 4 (by rfl) ⟨151398, by rfl⟩ : syracuseStep 1614917 = 302797) (by norm_num)
theorem B959557 : Blo 850355 959557 := bbase (se 4 (by rfl) ⟨89958, by rfl⟩ : syracuseStep 959557 = 179917) (by norm_num)
theorem B3646549 : Blo 850355 3646549 := bbase (se 8 (by rfl) ⟨21366, by rfl⟩ : syracuseStep 3646549 = 42733) (by norm_num)
theorem B959593 : Blo 850355 959593 := bbase (se 2 (by rfl) ⟨359847, by rfl⟩ : syracuseStep 959593 = 719695) (by norm_num)
theorem B1025141 : Blo 850355 1025141 := bbase (se 5 (by rfl) ⟨48053, by rfl⟩ : syracuseStep 1025141 = 96107) (by norm_num)
theorem B959629 : Blo 850355 959629 := bbase (se 3 (by rfl) ⟨179930, by rfl⟩ : syracuseStep 959629 = 359861) (by norm_num)
theorem B12297365 : Blo 850355 12297365 := bbase (se 6 (by rfl) ⟨288219, by rfl⟩ : syracuseStep 12297365 = 576439) (by norm_num)
theorem B959665 : Blo 850355 959665 := bbase (se 2 (by rfl) ⟨359874, by rfl⟩ : syracuseStep 959665 = 719749) (by norm_num)
theorem B959701 : Blo 850355 959701 := bbase (se 7 (by rfl) ⟨11246, by rfl⟩ : syracuseStep 959701 = 22493) (by norm_num)
theorem B1615069 : Blo 850355 1615069 := bbase (se 3 (by rfl) ⟨302825, by rfl⟩ : syracuseStep 1615069 = 605651) (by norm_num)
theorem B959737 : Blo 850355 959737 := bbase (se 2 (by rfl) ⟨359901, by rfl⟩ : syracuseStep 959737 = 719803) (by norm_num)
theorem B9708821 : Blo 850355 9708821 := bbase (se 6 (by rfl) ⟨227550, by rfl⟩ : syracuseStep 9708821 = 455101) (by norm_num)
theorem B959773 : Blo 850355 959773 := bbase (se 3 (by rfl) ⟨179957, by rfl⟩ : syracuseStep 959773 = 359915) (by norm_num)
theorem B959809 : Blo 850355 959809 := bbase (se 2 (by rfl) ⟨359928, by rfl⟩ : syracuseStep 959809 = 719857) (by norm_num)
theorem B959845 : Blo 850355 959845 := bbase (se 4 (by rfl) ⟨89985, by rfl⟩ : syracuseStep 959845 = 179971) (by norm_num)
theorem B959881 : Blo 850355 959881 := bbase (se 2 (by rfl) ⟨359955, by rfl⟩ : syracuseStep 959881 = 719911) (by norm_num)
theorem B959917 : Blo 850355 959917 := bbase (se 3 (by rfl) ⟨179984, by rfl⟩ : syracuseStep 959917 = 359969) (by norm_num)
theorem B1090993 : Blo 850355 1090993 := bbase (se 2 (by rfl) ⟨409122, by rfl⟩ : syracuseStep 1090993 = 818245) (by norm_num)
theorem B1025473 : Blo 850355 1025473 := bbase (se 2 (by rfl) ⟨384552, by rfl⟩ : syracuseStep 1025473 = 769105) (by norm_num)
theorem B959953 : Blo 850355 959953 := bbase (se 2 (by rfl) ⟨359982, by rfl⟩ : syracuseStep 959953 = 719965) (by norm_num)
theorem B959989 : Blo 850355 959989 := bbase (se 5 (by rfl) ⟨44999, by rfl⟩ : syracuseStep 959989 = 89999) (by norm_num)
theorem B6235637 : Blo 850355 6235637 := bbase (se 5 (by rfl) ⟨292295, by rfl⟩ : syracuseStep 6235637 = 584591) (by norm_num)
theorem B2336261 : Blo 850355 2336261 := bbase (se 4 (by rfl) ⟨219024, by rfl⟩ : syracuseStep 2336261 = 438049) (by norm_num)
theorem B1615373 : Blo 850355 1615373 := bbase (se 3 (by rfl) ⟨302882, by rfl⟩ : syracuseStep 1615373 = 605765) (by norm_num)
theorem B960025 : Blo 850355 960025 := bbase (se 2 (by rfl) ⟨360009, by rfl⟩ : syracuseStep 960025 = 720019) (by norm_num)
theorem B960061 : Blo 850355 960061 := bbase (se 3 (by rfl) ⟨180011, by rfl⟩ : syracuseStep 960061 = 360023) (by norm_num)
theorem B960097 : Blo 850355 960097 := bbase (se 2 (by rfl) ⟨360036, by rfl⟩ : syracuseStep 960097 = 720073) (by norm_num)
theorem B960133 : Blo 850355 960133 := bbase (se 4 (by rfl) ⟨90012, by rfl⟩ : syracuseStep 960133 = 180025) (by norm_num)
theorem B960169 : Blo 850355 960169 := bbase (se 2 (by rfl) ⟨360063, by rfl⟩ : syracuseStep 960169 = 720127) (by norm_num)
theorem B960205 : Blo 850355 960205 := bbase (se 3 (by rfl) ⟨180038, by rfl⟩ : syracuseStep 960205 = 360077) (by norm_num)
theorem B960241 : Blo 850355 960241 := bbase (se 2 (by rfl) ⟨360090, by rfl⟩ : syracuseStep 960241 = 720181) (by norm_num)
theorem B960277 : Blo 850355 960277 := bbase (se 6 (by rfl) ⟨22506, by rfl⟩ : syracuseStep 960277 = 45013) (by norm_num)
theorem B960313 : Blo 850355 960313 := bbase (se 2 (by rfl) ⟨360117, by rfl⟩ : syracuseStep 960313 = 720235) (by norm_num)
theorem B960349 : Blo 850355 960349 := bbase (se 3 (by rfl) ⟨180065, by rfl⟩ : syracuseStep 960349 = 360131) (by norm_num)
theorem B960385 : Blo 850355 960385 := bbase (se 2 (by rfl) ⟨360144, by rfl⟩ : syracuseStep 960385 = 720289) (by norm_num)
theorem B960421 : Blo 850355 960421 := bbase (se 4 (by rfl) ⟨90039, by rfl⟩ : syracuseStep 960421 = 180079) (by norm_num)
theorem B960457 : Blo 850355 960457 := bbase (se 2 (by rfl) ⟨360171, by rfl⟩ : syracuseStep 960457 = 720343) (by norm_num)
theorem B862165 : Blo 850355 862165 := bbase (se 7 (by rfl) ⟨10103, by rfl⟩ : syracuseStep 862165 = 20207) (by norm_num)
theorem B960493 : Blo 850355 960493 := bbase (se 3 (by rfl) ⟨180092, by rfl⟩ : syracuseStep 960493 = 360185) (by norm_num)
theorem B960529 : Blo 850355 960529 := bbase (se 2 (by rfl) ⟨360198, by rfl⟩ : syracuseStep 960529 = 720397) (by norm_num)
theorem B960565 : Blo 850355 960565 := bbase (se 5 (by rfl) ⟨45026, by rfl⟩ : syracuseStep 960565 = 90053) (by norm_num)
theorem B960601 : Blo 850355 960601 := bbase (se 2 (by rfl) ⟨360225, by rfl⟩ : syracuseStep 960601 = 720451) (by norm_num)
theorem B960637 : Blo 850355 960637 := bbase (se 3 (by rfl) ⟨180119, by rfl⟩ : syracuseStep 960637 = 360239) (by norm_num)
theorem B960673 : Blo 850355 960673 := bbase (se 2 (by rfl) ⟨360252, by rfl⟩ : syracuseStep 960673 = 720505) (by norm_num)
theorem B960709 : Blo 850355 960709 := bbase (se 4 (by rfl) ⟨90066, by rfl⟩ : syracuseStep 960709 = 180133) (by norm_num)
theorem B960745 : Blo 850355 960745 := bbase (se 2 (by rfl) ⟨360279, by rfl⟩ : syracuseStep 960745 = 720559) (by norm_num)
theorem B1845485 : Blo 850355 1845485 := bbase (se 3 (by rfl) ⟨346028, by rfl⟩ : syracuseStep 1845485 = 692057) (by norm_num)
theorem B1616125 : Blo 850355 1616125 := bbase (se 3 (by rfl) ⟨303023, by rfl⟩ : syracuseStep 1616125 = 606047) (by norm_num)
theorem B1943813 : Blo 850355 1943813 := bbase (se 4 (by rfl) ⟨182232, by rfl⟩ : syracuseStep 1943813 = 364465) (by norm_num)
theorem B960781 : Blo 850355 960781 := bbase (se 3 (by rfl) ⟨180146, by rfl⟩ : syracuseStep 960781 = 360293) (by norm_num)
theorem B960817 : Blo 850355 960817 := bbase (se 2 (by rfl) ⟨360306, by rfl⟩ : syracuseStep 960817 = 720613) (by norm_num)
theorem B3451189 : Blo 850355 3451189 := bbase (se 5 (by rfl) ⟨161774, by rfl⟩ : syracuseStep 3451189 = 323549) (by norm_num)
theorem B1026361 : Blo 850355 1026361 := bbase (se 2 (by rfl) ⟨384885, by rfl⟩ : syracuseStep 1026361 = 769771) (by norm_num)
theorem B1091917 : Blo 850355 1091917 := bbase (se 3 (by rfl) ⟨204734, by rfl⟩ : syracuseStep 1091917 = 409469) (by norm_num)
theorem B960853 : Blo 850355 960853 := bbase (se 10 (by rfl) ⟨1407, by rfl⟩ : syracuseStep 960853 = 2815) (by norm_num)
theorem B3451253 : Blo 850355 3451253 := bbase (se 5 (by rfl) ⟨161777, by rfl⟩ : syracuseStep 3451253 = 323555) (by norm_num)
theorem B960889 : Blo 850355 960889 := bbase (se 2 (by rfl) ⟨360333, by rfl⟩ : syracuseStep 960889 = 720667) (by norm_num)
theorem B1616269 : Blo 850355 1616269 := bbase (se 3 (by rfl) ⟨303050, by rfl⟩ : syracuseStep 1616269 = 606101) (by norm_num)
theorem B960925 : Blo 850355 960925 := bbase (se 3 (by rfl) ⟨180173, by rfl⟩ : syracuseStep 960925 = 360347) (by norm_num)
theorem B2992565 : Blo 850355 2992565 := bbase (se 5 (by rfl) ⟨140276, by rfl⟩ : syracuseStep 2992565 = 280553) (by norm_num)
theorem B960961 : Blo 850355 960961 := bbase (se 2 (by rfl) ⟨360360, by rfl⟩ : syracuseStep 960961 = 720721) (by norm_num)
theorem B960997 : Blo 850355 960997 := bbase (se 4 (by rfl) ⟨90093, by rfl⟩ : syracuseStep 960997 = 180187) (by norm_num)
theorem B961033 : Blo 850355 961033 := bbase (se 2 (by rfl) ⟨360387, by rfl⟩ : syracuseStep 961033 = 720775) (by norm_num)
theorem B3648037 : Blo 850355 3648037 := bbase (se 4 (by rfl) ⟨342003, by rfl⟩ : syracuseStep 3648037 = 684007) (by norm_num)
theorem B1616429 : Blo 850355 1616429 := bbase (se 3 (by rfl) ⟨303080, by rfl⟩ : syracuseStep 1616429 = 606161) (by norm_num)
theorem B961069 : Blo 850355 961069 := bbase (se 3 (by rfl) ⟨180200, by rfl⟩ : syracuseStep 961069 = 360401) (by norm_num)
theorem B3648053 : Blo 850355 3648053 := bbase (se 5 (by rfl) ⟨171002, by rfl⟩ : syracuseStep 3648053 = 342005) (by norm_num)
theorem B961105 : Blo 850355 961105 := bbase (se 2 (by rfl) ⟨360414, by rfl⟩ : syracuseStep 961105 = 720829) (by norm_num)
theorem B961141 : Blo 850355 961141 := bbase (se 5 (by rfl) ⟨45053, by rfl⟩ : syracuseStep 961141 = 90107) (by norm_num)
theorem B6466229 : Blo 850355 6466229 := bbase (se 5 (by rfl) ⟨303104, by rfl⟩ : syracuseStep 6466229 = 606209) (by norm_num)
theorem B1616573 : Blo 850355 1616573 := bbase (se 3 (by rfl) ⟨303107, by rfl⟩ : syracuseStep 1616573 = 606215) (by norm_num)
theorem B2730709 : Blo 850355 2730709 := bbase (se 7 (by rfl) ⟨32000, by rfl⟩ : syracuseStep 2730709 = 64001) (by norm_num)
theorem B7875413 : Blo 850355 7875413 := bbase (se 9 (by rfl) ⟨23072, by rfl⟩ : syracuseStep 7875413 = 46145) (by norm_num)
theorem B1616861 : Blo 850355 1616861 := bbase (se 3 (by rfl) ⟨303161, by rfl⟩ : syracuseStep 1616861 = 606323) (by norm_num)
theorem B1617013 : Blo 850355 1617013 := bbase (se 5 (by rfl) ⟨75797, by rfl⟩ : syracuseStep 1617013 = 151595) (by norm_num)
theorem B3452165 : Blo 850355 3452165 := bbase (se 4 (by rfl) ⟨323640, by rfl⟩ : syracuseStep 3452165 = 647281) (by norm_num)
theorem B863641 : Blo 850355 863641 := bbase (se 2 (by rfl) ⟨323865, by rfl⟩ : syracuseStep 863641 = 647731) (by norm_num)
theorem B1617317 : Blo 850355 1617317 := bbase (se 4 (by rfl) ⟨151623, by rfl⟩ : syracuseStep 1617317 = 303247) (by norm_num)
theorem B14561045 : Blo 850355 14561045 := bbase (se 6 (by rfl) ⟨341274, by rfl⟩ : syracuseStep 14561045 = 682549) (by norm_num)
theorem B2732069 : Blo 850355 2732069 := bbase (se 4 (by rfl) ⟨256131, by rfl⟩ : syracuseStep 2732069 = 512263) (by norm_num)
theorem B2043949 : Blo 850355 2043949 := bbase (se 3 (by rfl) ⟨383240, by rfl⟩ : syracuseStep 2043949 = 766481) (by norm_num)
theorem B1618069 : Blo 850355 1618069 := bbase (se 6 (by rfl) ⟨37923, by rfl⟩ : syracuseStep 1618069 = 75847) (by norm_num)
theorem B1618213 : Blo 850355 1618213 := bbase (se 4 (by rfl) ⟨151707, by rfl⟩ : syracuseStep 1618213 = 303415) (by norm_num)
theorem B2077085 : Blo 850355 2077085 := bbase (se 3 (by rfl) ⟨389453, by rfl⟩ : syracuseStep 2077085 = 778907) (by norm_num)
theorem B1618373 : Blo 850355 1618373 := bbase (se 4 (by rfl) ⟨151722, by rfl⟩ : syracuseStep 1618373 = 303445) (by norm_num)
theorem B1913309 : Blo 850355 1913309 := bbase (se 3 (by rfl) ⟨358745, by rfl⟩ : syracuseStep 1913309 = 717491) (by norm_num)
theorem B1913381 : Blo 850355 1913381 := bbase (se 4 (by rfl) ⟨179379, by rfl⟩ : syracuseStep 1913381 = 358759) (by norm_num)
theorem B5452373 : Blo 850355 5452373 := bbase (se 8 (by rfl) ⟨31947, by rfl⟩ : syracuseStep 5452373 = 63895) (by norm_num)
theorem B1618517 : Blo 850355 1618517 := bbase (se 8 (by rfl) ⟨9483, by rfl⟩ : syracuseStep 1618517 = 18967) (by norm_num)
theorem B1913453 : Blo 850355 1913453 := bbase (se 3 (by rfl) ⟨358772, by rfl⟩ : syracuseStep 1913453 = 717545) (by norm_num)
theorem B2044565 : Blo 850355 2044565 := bbase (se 6 (by rfl) ⟨47919, by rfl⟩ : syracuseStep 2044565 = 95839) (by norm_num)
theorem B1913525 : Blo 850355 1913525 := bbase (se 5 (by rfl) ⟨89696, by rfl⟩ : syracuseStep 1913525 = 179393) (by norm_num)
theorem B1913597 : Blo 850355 1913597 := bbase (se 3 (by rfl) ⟨358799, by rfl⟩ : syracuseStep 1913597 = 717599) (by norm_num)
theorem B1913669 : Blo 850355 1913669 := bbase (se 4 (by rfl) ⟨179406, by rfl⟩ : syracuseStep 1913669 = 358813) (by norm_num)
theorem B865117 : Blo 850355 865117 := bbase (se 3 (by rfl) ⟨162209, by rfl⟩ : syracuseStep 865117 = 324419) (by norm_num)
theorem B1618805 : Blo 850355 1618805 := bbase (se 5 (by rfl) ⟨75881, by rfl⟩ : syracuseStep 1618805 = 151763) (by norm_num)
theorem B4305797 : Blo 850355 4305797 := bbase (se 4 (by rfl) ⟨403668, by rfl⟩ : syracuseStep 4305797 = 807337) (by norm_num)
theorem B1913741 : Blo 850355 1913741 := bbase (se 3 (by rfl) ⟨358826, by rfl⟩ : syracuseStep 1913741 = 717653) (by norm_num)
theorem B1455013 : Blo 850355 1455013 := bbase (se 4 (by rfl) ⟨136407, by rfl⟩ : syracuseStep 1455013 = 272815) (by norm_num)
theorem B1946533 : Blo 850355 1946533 := bbase (se 4 (by rfl) ⟨182487, by rfl⟩ : syracuseStep 1946533 = 364975) (by norm_num)
theorem B1913813 : Blo 850355 1913813 := bbase (se 7 (by rfl) ⟨22427, by rfl⟩ : syracuseStep 1913813 = 44855) (by norm_num)
theorem B1618957 : Blo 850355 1618957 := bbase (se 3 (by rfl) ⟨303554, by rfl⟩ : syracuseStep 1618957 = 607109) (by norm_num)
theorem B1913885 : Blo 850355 1913885 := bbase (se 3 (by rfl) ⟨358853, by rfl⟩ : syracuseStep 1913885 = 717707) (by norm_num)
theorem B1913957 : Blo 850355 1913957 := bbase (se 4 (by rfl) ⟨179433, by rfl⟩ : syracuseStep 1913957 = 358867) (by norm_num)
theorem B1914029 : Blo 850355 1914029 := bbase (se 3 (by rfl) ⟨358880, by rfl⟩ : syracuseStep 1914029 = 717761) (by norm_num)
theorem B1455341 : Blo 850355 1455341 := bbase (se 3 (by rfl) ⟨272876, by rfl⟩ : syracuseStep 1455341 = 545753) (by norm_num)
theorem B1914101 : Blo 850355 1914101 := bbase (se 5 (by rfl) ⟨89723, by rfl⟩ : syracuseStep 1914101 = 179447) (by norm_num)
theorem B1914173 : Blo 850355 1914173 := bbase (se 3 (by rfl) ⟨358907, by rfl⟩ : syracuseStep 1914173 = 717815) (by norm_num)
theorem B1619261 : Blo 850355 1619261 := bbase (se 3 (by rfl) ⟨303611, by rfl⟩ : syracuseStep 1619261 = 607223) (by norm_num)
theorem B2667845 : Blo 850355 2667845 := bbase (se 4 (by rfl) ⟨250110, by rfl⟩ : syracuseStep 2667845 = 500221) (by norm_num)
theorem B3880325 : Blo 850355 3880325 := bbase (se 4 (by rfl) ⟨363780, by rfl⟩ : syracuseStep 3880325 = 727561) (by norm_num)
theorem B1914245 : Blo 850355 1914245 := bbase (se 4 (by rfl) ⟨179460, by rfl⟩ : syracuseStep 1914245 = 358921) (by norm_num)
theorem B2045341 : Blo 850355 2045341 := bbase (se 3 (by rfl) ⟨383501, by rfl⟩ : syracuseStep 2045341 = 767003) (by norm_num)
theorem B865733 : Blo 850355 865733 := bbase (se 4 (by rfl) ⟨81162, by rfl⟩ : syracuseStep 865733 = 162325) (by norm_num)
theorem B1914317 : Blo 850355 1914317 := bbase (se 3 (by rfl) ⟨358934, by rfl⟩ : syracuseStep 1914317 = 717869) (by norm_num)
theorem B1914389 : Blo 850355 1914389 := bbase (se 6 (by rfl) ⟨44868, by rfl⟩ : syracuseStep 1914389 = 89737) (by norm_num)
theorem B1914461 : Blo 850355 1914461 := bbase (se 3 (by rfl) ⟨358961, by rfl⟩ : syracuseStep 1914461 = 717923) (by norm_num)
theorem B5060245 : Blo 850355 5060245 := bbase (se 6 (by rfl) ⟨118599, by rfl⟩ : syracuseStep 5060245 = 237199) (by norm_num)
theorem B1914533 : Blo 850355 1914533 := bbase (se 4 (by rfl) ⟨179487, by rfl⟩ : syracuseStep 1914533 = 358975) (by norm_num)
theorem B1816253 : Blo 850355 1816253 := bbase (se 3 (by rfl) ⟨340547, by rfl⟩ : syracuseStep 1816253 = 681095) (by norm_num)
theorem B1914605 : Blo 850355 1914605 := bbase (se 3 (by rfl) ⟨358988, by rfl⟩ : syracuseStep 1914605 = 717977) (by norm_num)
theorem B1914677 : Blo 850355 1914677 := bbase (se 5 (by rfl) ⟨89750, by rfl⟩ : syracuseStep 1914677 = 179501) (by norm_num)
theorem B4863797 : Blo 850355 4863797 := bbase (se 5 (by rfl) ⟨227990, by rfl⟩ : syracuseStep 4863797 = 455981) (by norm_num)
theorem B1947461 : Blo 850355 1947461 := bbase (se 4 (by rfl) ⟨182574, by rfl⟩ : syracuseStep 1947461 = 365149) (by norm_num)
theorem B4372309 : Blo 850355 4372309 := bbase (se 9 (by rfl) ⟨12809, by rfl⟩ : syracuseStep 4372309 = 25619) (by norm_num)
theorem B1914749 : Blo 850355 1914749 := bbase (se 3 (by rfl) ⟨359015, by rfl⟩ : syracuseStep 1914749 = 718031) (by norm_num)
theorem B1816501 : Blo 850355 1816501 := bbase (se 5 (by rfl) ⟨85148, by rfl⟩ : syracuseStep 1816501 = 170297) (by norm_num)
theorem B1914821 : Blo 850355 1914821 := bbase (se 4 (by rfl) ⟨179514, by rfl⟩ : syracuseStep 1914821 = 359029) (by norm_num)
theorem B1914893 : Blo 850355 1914893 := bbase (se 3 (by rfl) ⟨359042, by rfl⟩ : syracuseStep 1914893 = 718085) (by norm_num)
theorem B1620013 : Blo 850355 1620013 := bbase (se 3 (by rfl) ⟨303752, by rfl⟩ : syracuseStep 1620013 = 607505) (by norm_num)
theorem B1914965 : Blo 850355 1914965 := bbase (se 8 (by rfl) ⟨11220, by rfl⟩ : syracuseStep 1914965 = 22441) (by norm_num)
theorem B2046053 : Blo 850355 2046053 := bbase (se 4 (by rfl) ⟨191817, by rfl⟩ : syracuseStep 2046053 = 383635) (by norm_num)
theorem B4307093 : Blo 850355 4307093 := bbase (se 6 (by rfl) ⟨100947, by rfl⟩ : syracuseStep 4307093 = 201895) (by norm_num)
theorem B1915037 : Blo 850355 1915037 := bbase (se 3 (by rfl) ⟨359069, by rfl⟩ : syracuseStep 1915037 = 718139) (by norm_num)
theorem B1620157 : Blo 850355 1620157 := bbase (se 3 (by rfl) ⟨303779, by rfl⟩ : syracuseStep 1620157 = 607559) (by norm_num)
theorem B1915109 : Blo 850355 1915109 := bbase (se 4 (by rfl) ⟨179541, by rfl⟩ : syracuseStep 1915109 = 359083) (by norm_num)
theorem B1915181 : Blo 850355 1915181 := bbase (se 3 (by rfl) ⟨359096, by rfl⟩ : syracuseStep 1915181 = 718193) (by norm_num)
theorem B1620317 : Blo 850355 1620317 := bbase (se 3 (by rfl) ⟨303809, by rfl⟩ : syracuseStep 1620317 = 607619) (by norm_num)
theorem B1096033 : Blo 850355 1096033 := bbase (se 2 (by rfl) ⟨411012, by rfl⟩ : syracuseStep 1096033 = 822025) (by norm_num)
theorem B1915253 : Blo 850355 1915253 := bbase (se 5 (by rfl) ⟨89777, by rfl⟩ : syracuseStep 1915253 = 179555) (by norm_num)
theorem B1948045 : Blo 850355 1948045 := bbase (se 3 (by rfl) ⟨365258, by rfl⟩ : syracuseStep 1948045 = 730517) (by norm_num)
theorem B1817005 : Blo 850355 1817005 := bbase (se 3 (by rfl) ⟨340688, by rfl⟩ : syracuseStep 1817005 = 681377) (by norm_num)
theorem B1915325 : Blo 850355 1915325 := bbase (se 3 (by rfl) ⟨359123, by rfl⟩ : syracuseStep 1915325 = 718247) (by norm_num)
theorem B1620461 : Blo 850355 1620461 := bbase (se 3 (by rfl) ⟨303836, by rfl⟩ : syracuseStep 1620461 = 607673) (by norm_num)
theorem B1915397 : Blo 850355 1915397 := bbase (se 4 (by rfl) ⟨179568, by rfl⟩ : syracuseStep 1915397 = 359137) (by norm_num)
theorem B1915469 : Blo 850355 1915469 := bbase (se 3 (by rfl) ⟨359150, by rfl⟩ : syracuseStep 1915469 = 718301) (by norm_num)
theorem B1915541 : Blo 850355 1915541 := bbase (se 6 (by rfl) ⟨44895, by rfl⟩ : syracuseStep 1915541 = 89791) (by norm_num)
theorem B1293005 : Blo 850355 1293005 := bbase (se 3 (by rfl) ⟨242438, by rfl⟩ : syracuseStep 1293005 = 484877) (by norm_num)
theorem B1915613 : Blo 850355 1915613 := bbase (se 3 (by rfl) ⟨359177, by rfl⟩ : syracuseStep 1915613 = 718355) (by norm_num)
theorem B2046725 : Blo 850355 2046725 := bbase (se 4 (by rfl) ⟨191880, by rfl⟩ : syracuseStep 2046725 = 383761) (by norm_num)
theorem B1620749 : Blo 850355 1620749 := bbase (se 3 (by rfl) ⟨303890, by rfl⟩ : syracuseStep 1620749 = 607781) (by norm_num)
theorem B1915685 : Blo 850355 1915685 := bbase (se 4 (by rfl) ⟨179595, by rfl⟩ : syracuseStep 1915685 = 359191) (by norm_num)
theorem B1915757 : Blo 850355 1915757 := bbase (se 3 (by rfl) ⟨359204, by rfl⟩ : syracuseStep 1915757 = 718409) (by norm_num)
theorem B1620901 : Blo 850355 1620901 := bbase (se 4 (by rfl) ⟨151959, by rfl⟩ : syracuseStep 1620901 = 303919) (by norm_num)
theorem B1915829 : Blo 850355 1915829 := bbase (se 5 (by rfl) ⟨89804, by rfl⟩ : syracuseStep 1915829 = 179609) (by norm_num)
theorem B4864981 : Blo 850355 4864981 := bbase (se 7 (by rfl) ⟨57011, by rfl⟩ : syracuseStep 4864981 = 114023) (by norm_num)
theorem B1915901 : Blo 850355 1915901 := bbase (se 3 (by rfl) ⟨359231, by rfl⟩ : syracuseStep 1915901 = 718463) (by norm_num)
theorem B1915973 : Blo 850355 1915973 := bbase (se 4 (by rfl) ⟨179622, by rfl⟩ : syracuseStep 1915973 = 359245) (by norm_num)
theorem B1916045 : Blo 850355 1916045 := bbase (se 3 (by rfl) ⟨359258, by rfl⟩ : syracuseStep 1916045 = 718517) (by norm_num)
theorem B1916117 : Blo 850355 1916117 := bbase (se 7 (by rfl) ⟨22454, by rfl⟩ : syracuseStep 1916117 = 44909) (by norm_num)
theorem B1621205 : Blo 850355 1621205 := bbase (se 7 (by rfl) ⟨18998, by rfl⟩ : syracuseStep 1621205 = 37997) (by norm_num)
theorem B4668661 : Blo 850355 4668661 := bbase (se 5 (by rfl) ⟨218843, by rfl⟩ : syracuseStep 4668661 = 437687) (by norm_num)
theorem B1916189 : Blo 850355 1916189 := bbase (se 3 (by rfl) ⟨359285, by rfl⟩ : syracuseStep 1916189 = 718571) (by norm_num)
theorem B1817893 : Blo 850355 1817893 := bbase (se 4 (by rfl) ⟨170427, by rfl⟩ : syracuseStep 1817893 = 340855) (by norm_num)
theorem B4930901 : Blo 850355 4930901 := bbase (se 11 (by rfl) ⟨3611, by rfl⟩ : syracuseStep 4930901 = 7223) (by norm_num)
theorem B1916261 : Blo 850355 1916261 := bbase (se 4 (by rfl) ⟨179649, by rfl⟩ : syracuseStep 1916261 = 359299) (by norm_num)
theorem B2735477 : Blo 850355 2735477 := bbase (se 5 (by rfl) ⟨128225, by rfl⟩ : syracuseStep 2735477 = 256451) (by norm_num)
theorem B4308389 : Blo 850355 4308389 := bbase (se 4 (by rfl) ⟨403911, by rfl⟩ : syracuseStep 4308389 = 807823) (by norm_num)
theorem B1916333 : Blo 850355 1916333 := bbase (se 3 (by rfl) ⟨359312, by rfl⟩ : syracuseStep 1916333 = 718625) (by norm_num)
theorem B8764885 : Blo 850355 8764885 := bbase (se 7 (by rfl) ⟨102713, by rfl⟩ : syracuseStep 8764885 = 205427) (by norm_num)
theorem B1916405 : Blo 850355 1916405 := bbase (se 5 (by rfl) ⟨89831, by rfl⟩ : syracuseStep 1916405 = 179663) (by norm_num)
theorem B1916477 : Blo 850355 1916477 := bbase (se 3 (by rfl) ⟨359339, by rfl⟩ : syracuseStep 1916477 = 718679) (by norm_num)
theorem B1916549 : Blo 850355 1916549 := bbase (se 4 (by rfl) ⟨179676, by rfl⟩ : syracuseStep 1916549 = 359353) (by norm_num)
theorem B1916621 : Blo 850355 1916621 := bbase (se 3 (by rfl) ⟨359366, by rfl⟩ : syracuseStep 1916621 = 718733) (by norm_num)
theorem B1818389 : Blo 850355 1818389 := bbase (se 6 (by rfl) ⟨42618, by rfl⟩ : syracuseStep 1818389 = 85237) (by norm_num)
theorem B1916693 : Blo 850355 1916693 := bbase (se 6 (by rfl) ⟨44922, by rfl⟩ : syracuseStep 1916693 = 89845) (by norm_num)
theorem B1916765 : Blo 850355 1916765 := bbase (se 3 (by rfl) ⟨359393, by rfl⟩ : syracuseStep 1916765 = 718787) (by norm_num)
theorem B1916837 : Blo 850355 1916837 := bbase (se 4 (by rfl) ⟨179703, by rfl⟩ : syracuseStep 1916837 = 359407) (by norm_num)
theorem B1916909 : Blo 850355 1916909 := bbase (se 3 (by rfl) ⟨359420, by rfl⟩ : syracuseStep 1916909 = 718841) (by norm_num)
theorem B1916981 : Blo 850355 1916981 := bbase (se 5 (by rfl) ⟨89858, by rfl⟩ : syracuseStep 1916981 = 179717) (by norm_num)
theorem B3457093 : Blo 850355 3457093 := bbase (se 4 (by rfl) ⟨324102, by rfl⟩ : syracuseStep 3457093 = 648205) (by norm_num)
theorem B1917053 : Blo 850355 1917053 := bbase (se 3 (by rfl) ⟨359447, by rfl⟩ : syracuseStep 1917053 = 718895) (by norm_num)
theorem B1917125 : Blo 850355 1917125 := bbase (se 4 (by rfl) ⟨179730, by rfl⟩ : syracuseStep 1917125 = 359461) (by norm_num)
theorem B1917197 : Blo 850355 1917197 := bbase (se 3 (by rfl) ⟨359474, by rfl⟩ : syracuseStep 1917197 = 718949) (by norm_num)
theorem B1917269 : Blo 850355 1917269 := bbase (se 10 (by rfl) ⟨2808, by rfl⟩ : syracuseStep 1917269 = 5617) (by norm_num)
theorem B1917341 : Blo 850355 1917341 := bbase (se 3 (by rfl) ⟨359501, by rfl⟩ : syracuseStep 1917341 = 719003) (by norm_num)
theorem B1917413 : Blo 850355 1917413 := bbase (se 4 (by rfl) ⟨179757, by rfl⟩ : syracuseStep 1917413 = 359515) (by norm_num)
theorem B2048485 : Blo 850355 2048485 := bbase (se 4 (by rfl) ⟨192045, by rfl⟩ : syracuseStep 2048485 = 384091) (by norm_num)
theorem B1917485 : Blo 850355 1917485 := bbase (se 3 (by rfl) ⟨359528, by rfl⟩ : syracuseStep 1917485 = 719057) (by norm_num)
theorem B1917557 : Blo 850355 1917557 := bbase (se 5 (by rfl) ⟨89885, by rfl⟩ : syracuseStep 1917557 = 179771) (by norm_num)
theorem B2736757 : Blo 850355 2736757 := bbase (se 5 (by rfl) ⟨128285, by rfl⟩ : syracuseStep 2736757 = 256571) (by norm_num)
theorem B1819277 : Blo 850355 1819277 := bbase (se 3 (by rfl) ⟨341114, by rfl⟩ : syracuseStep 1819277 = 682229) (by norm_num)
theorem B4309685 : Blo 850355 4309685 := bbase (se 5 (by rfl) ⟨202016, by rfl⟩ : syracuseStep 4309685 = 404033) (by norm_num)
theorem B1917629 : Blo 850355 1917629 := bbase (se 3 (by rfl) ⟨359555, by rfl⟩ : syracuseStep 1917629 = 719111) (by norm_num)
theorem B1819397 : Blo 850355 1819397 := bbase (se 4 (by rfl) ⟨170568, by rfl⟩ : syracuseStep 1819397 = 341137) (by norm_num)
theorem B1917701 : Blo 850355 1917701 := bbase (se 4 (by rfl) ⟨179784, by rfl⟩ : syracuseStep 1917701 = 359569) (by norm_num)
theorem B1917773 : Blo 850355 1917773 := bbase (se 3 (by rfl) ⟨359582, by rfl⟩ : syracuseStep 1917773 = 719165) (by norm_num)
theorem B1459037 : Blo 850355 1459037 := bbase (se 3 (by rfl) ⟨273569, by rfl⟩ : syracuseStep 1459037 = 547139) (by norm_num)
theorem B1917845 : Blo 850355 1917845 := bbase (se 6 (by rfl) ⟨44949, by rfl⟩ : syracuseStep 1917845 = 89899) (by norm_num)
theorem B1917917 : Blo 850355 1917917 := bbase (se 3 (by rfl) ⟨359609, by rfl⟩ : syracuseStep 1917917 = 719219) (by norm_num)
theorem B1295365 : Blo 850355 1295365 := bbase (se 4 (by rfl) ⟨121440, by rfl⟩ : syracuseStep 1295365 = 242881) (by norm_num)
theorem B1917989 : Blo 850355 1917989 := bbase (se 4 (by rfl) ⟨179811, by rfl⟩ : syracuseStep 1917989 = 359623) (by norm_num)
theorem B1295437 : Blo 850355 1295437 := bbase (se 3 (by rfl) ⟨242894, by rfl⟩ : syracuseStep 1295437 = 485789) (by norm_num)
theorem B2049101 : Blo 850355 2049101 := bbase (se 3 (by rfl) ⟨384206, by rfl⟩ : syracuseStep 2049101 = 768413) (by norm_num)
theorem B1918061 : Blo 850355 1918061 := bbase (se 3 (by rfl) ⟨359636, by rfl⟩ : syracuseStep 1918061 = 719273) (by norm_num)
theorem B1918133 : Blo 850355 1918133 := bbase (se 5 (by rfl) ⟨89912, by rfl⟩ : syracuseStep 1918133 = 179825) (by norm_num)
theorem B1918205 : Blo 850355 1918205 := bbase (se 3 (by rfl) ⟨359663, by rfl⟩ : syracuseStep 1918205 = 719327) (by norm_num)
theorem B1918277 : Blo 850355 1918277 := bbase (se 4 (by rfl) ⟨179838, by rfl⟩ : syracuseStep 1918277 = 359677) (by norm_num)
theorem B1820029 : Blo 850355 1820029 := bbase (se 3 (by rfl) ⟨341255, by rfl⟩ : syracuseStep 1820029 = 682511) (by norm_num)
theorem B1918349 : Blo 850355 1918349 := bbase (se 3 (by rfl) ⟨359690, by rfl⟩ : syracuseStep 1918349 = 719381) (by norm_num)
theorem B1459613 : Blo 850355 1459613 := bbase (se 3 (by rfl) ⟨273677, by rfl⟩ : syracuseStep 1459613 = 547355) (by norm_num)
theorem B1918421 : Blo 850355 1918421 := bbase (se 7 (by rfl) ⟨22481, by rfl⟩ : syracuseStep 1918421 = 44963) (by norm_num)
theorem B1918493 : Blo 850355 1918493 := bbase (se 3 (by rfl) ⟨359717, by rfl⟩ : syracuseStep 1918493 = 719435) (by norm_num)
theorem B1918565 : Blo 850355 1918565 := bbase (se 4 (by rfl) ⟨179865, by rfl⟩ : syracuseStep 1918565 = 359731) (by norm_num)
theorem B1918637 : Blo 850355 1918637 := bbase (se 3 (by rfl) ⟨359744, by rfl⟩ : syracuseStep 1918637 = 719489) (by norm_num)
theorem B8406773 : Blo 850355 8406773 := bbase (se 5 (by rfl) ⟨394067, by rfl⟩ : syracuseStep 8406773 = 788135) (by norm_num)
theorem B1918709 : Blo 850355 1918709 := bbase (se 5 (by rfl) ⟨89939, by rfl⟩ : syracuseStep 1918709 = 179879) (by norm_num)
theorem B1918781 : Blo 850355 1918781 := bbase (se 3 (by rfl) ⟨359771, by rfl⟩ : syracuseStep 1918781 = 719543) (by norm_num)
theorem B2049869 : Blo 850355 2049869 := bbase (se 3 (by rfl) ⟨384350, by rfl⟩ : syracuseStep 2049869 = 768701) (by norm_num)
theorem B2049877 : Blo 850355 2049877 := bbase (se 9 (by rfl) ⟨6005, by rfl⟩ : syracuseStep 2049877 = 12011) (by norm_num)
theorem B1918853 : Blo 850355 1918853 := bbase (se 4 (by rfl) ⟨179892, by rfl⟩ : syracuseStep 1918853 = 359785) (by norm_num)
theorem B4310981 : Blo 850355 4310981 := bbase (se 4 (by rfl) ⟨404154, by rfl⟩ : syracuseStep 4310981 = 808309) (by norm_num)
theorem B1918925 : Blo 850355 1918925 := bbase (se 3 (by rfl) ⟨359798, by rfl⟩ : syracuseStep 1918925 = 719597) (by norm_num)
theorem B13125653 : Blo 850355 13125653 := bbase (se 6 (by rfl) ⟨307632, by rfl⟩ : syracuseStep 13125653 = 615265) (by norm_num)
theorem B1918997 : Blo 850355 1918997 := bbase (se 6 (by rfl) ⟨44976, by rfl⟩ : syracuseStep 1918997 = 89953) (by norm_num)
theorem B1919069 : Blo 850355 1919069 := bbase (se 3 (by rfl) ⟨359825, by rfl⟩ : syracuseStep 1919069 = 719651) (by norm_num)
theorem B1919141 : Blo 850355 1919141 := bbase (se 4 (by rfl) ⟨179919, by rfl⟩ : syracuseStep 1919141 = 359839) (by norm_num)
theorem B1919213 : Blo 850355 1919213 := bbase (se 3 (by rfl) ⟨359852, by rfl⟩ : syracuseStep 1919213 = 719705) (by norm_num)
theorem B1231085 : Blo 850355 1231085 := bbase (se 3 (by rfl) ⟨230828, by rfl⟩ : syracuseStep 1231085 = 461657) (by norm_num)
theorem B1820917 : Blo 850355 1820917 := bbase (se 5 (by rfl) ⟨85355, by rfl⟩ : syracuseStep 1820917 = 170711) (by norm_num)
theorem B6474005 : Blo 850355 6474005 := bbase (se 6 (by rfl) ⟨151734, by rfl⟩ : syracuseStep 6474005 = 303469) (by norm_num)
theorem B1919285 : Blo 850355 1919285 := bbase (se 5 (by rfl) ⟨89966, by rfl⟩ : syracuseStep 1919285 = 179933) (by norm_num)
theorem B1821037 : Blo 850355 1821037 := bbase (se 3 (by rfl) ⟨341444, by rfl⟩ : syracuseStep 1821037 = 682889) (by norm_num)
theorem B1919357 : Blo 850355 1919357 := bbase (se 3 (by rfl) ⟨359879, by rfl⟩ : syracuseStep 1919357 = 719759) (by norm_num)
theorem B1919429 : Blo 850355 1919429 := bbase (se 4 (by rfl) ⟨179946, by rfl⟩ : syracuseStep 1919429 = 359893) (by norm_num)
theorem B3459557 : Blo 850355 3459557 := bbase (se 4 (by rfl) ⟨324333, by rfl⟩ : syracuseStep 3459557 = 648667) (by norm_num)
theorem B1919501 : Blo 850355 1919501 := bbase (se 3 (by rfl) ⟨359906, by rfl⟩ : syracuseStep 1919501 = 719813) (by norm_num)
theorem B1919573 : Blo 850355 1919573 := bbase (se 8 (by rfl) ⟨11247, by rfl⟩ : syracuseStep 1919573 = 22495) (by norm_num)
theorem B1821293 : Blo 850355 1821293 := bbase (se 3 (by rfl) ⟨341492, by rfl⟩ : syracuseStep 1821293 = 682985) (by norm_num)
theorem B2050685 : Blo 850355 2050685 := bbase (se 3 (by rfl) ⟨384503, by rfl⟩ : syracuseStep 2050685 = 769007) (by norm_num)
theorem B1919645 : Blo 850355 1919645 := bbase (se 3 (by rfl) ⟨359933, by rfl⟩ : syracuseStep 1919645 = 719867) (by norm_num)
theorem B7785173 : Blo 850355 7785173 := bbase (se 7 (by rfl) ⟨91232, by rfl⟩ : syracuseStep 7785173 = 182465) (by norm_num)
theorem B1919717 : Blo 850355 1919717 := bbase (se 4 (by rfl) ⟨179973, by rfl⟩ : syracuseStep 1919717 = 359947) (by norm_num)
theorem B6146837 : Blo 850355 6146837 := bbase (se 6 (by rfl) ⟨144066, by rfl⟩ : syracuseStep 6146837 = 288133) (by norm_num)
theorem B1919789 : Blo 850355 1919789 := bbase (se 3 (by rfl) ⟨359960, by rfl⟩ : syracuseStep 1919789 = 719921) (by norm_num)
theorem B3230549 : Blo 850355 3230549 := bbase (se 9 (by rfl) ⟨9464, by rfl⟩ : syracuseStep 3230549 = 18929) (by norm_num)
theorem B1919861 : Blo 850355 1919861 := bbase (se 5 (by rfl) ⟨89993, by rfl⟩ : syracuseStep 1919861 = 179987) (by norm_num)
theorem B1919933 : Blo 850355 1919933 := bbase (se 3 (by rfl) ⟨359987, by rfl⟩ : syracuseStep 1919933 = 719975) (by norm_num)
theorem B2870261 : Blo 850355 2870261 := bbase (se 5 (by rfl) ⟨134543, by rfl⟩ : syracuseStep 2870261 = 269087) (by norm_num)
theorem B1920005 : Blo 850355 1920005 := bbase (se 4 (by rfl) ⟨180000, by rfl⟩ : syracuseStep 1920005 = 360001) (by norm_num)
theorem B1362997 : Blo 850355 1362997 := bbase (se 5 (by rfl) ⟨63890, by rfl⟩ : syracuseStep 1362997 = 127781) (by norm_num)
theorem B1920077 : Blo 850355 1920077 := bbase (se 3 (by rfl) ⟨360014, by rfl⟩ : syracuseStep 1920077 = 720029) (by norm_num)
theorem B3230837 : Blo 850355 3230837 := bbase (se 5 (by rfl) ⟨151445, by rfl⟩ : syracuseStep 3230837 = 302891) (by norm_num)
theorem B1264765 : Blo 850355 1264765 := bbase (se 3 (by rfl) ⟨237143, by rfl⟩ : syracuseStep 1264765 = 474287) (by norm_num)
theorem B1920149 : Blo 850355 1920149 := bbase (se 6 (by rfl) ⟨45003, by rfl⟩ : syracuseStep 1920149 = 90007) (by norm_num)
theorem B1166509 : Blo 850355 1166509 := bbase (se 3 (by rfl) ⟨218720, by rfl⟩ : syracuseStep 1166509 = 437441) (by norm_num)
theorem B8735957 : Blo 850355 8735957 := bbase (se 7 (by rfl) ⟨102374, by rfl⟩ : syracuseStep 8735957 = 204749) (by norm_num)
theorem B4312277 : Blo 850355 4312277 := bbase (se 7 (by rfl) ⟨50534, by rfl⟩ : syracuseStep 4312277 = 101069) (by norm_num)
theorem B4607189 : Blo 850355 4607189 := bbase (se 7 (by rfl) ⟨53990, by rfl⟩ : syracuseStep 4607189 = 107981) (by norm_num)
theorem B1920221 : Blo 850355 1920221 := bbase (se 3 (by rfl) ⟨360041, by rfl⟩ : syracuseStep 1920221 = 720083) (by norm_num)
theorem B1920293 : Blo 850355 1920293 := bbase (se 4 (by rfl) ⟨180027, by rfl⟩ : syracuseStep 1920293 = 360055) (by norm_num)
theorem B1920365 : Blo 850355 1920365 := bbase (se 3 (by rfl) ⟨360068, by rfl⟩ : syracuseStep 1920365 = 720137) (by norm_num)
theorem B2870693 : Blo 850355 2870693 := bbase (se 4 (by rfl) ⟨269127, by rfl⟩ : syracuseStep 2870693 = 538255) (by norm_num)
theorem B1920437 : Blo 850355 1920437 := bbase (se 5 (by rfl) ⟨90020, by rfl⟩ : syracuseStep 1920437 = 180041) (by norm_num)
theorem B2215397 : Blo 850355 2215397 := bbase (se 4 (by rfl) ⟨207693, by rfl⟩ : syracuseStep 2215397 = 415387) (by norm_num)
theorem B1822181 : Blo 850355 1822181 := bbase (se 4 (by rfl) ⟨170829, by rfl⟩ : syracuseStep 1822181 = 341659) (by norm_num)
theorem B1920509 : Blo 850355 1920509 := bbase (se 3 (by rfl) ⟨360095, by rfl⟩ : syracuseStep 1920509 = 720191) (by norm_num)
theorem B1920581 : Blo 850355 1920581 := bbase (se 4 (by rfl) ⟨180054, by rfl⟩ : syracuseStep 1920581 = 360109) (by norm_num)
theorem B1035893 : Blo 850355 1035893 := bbase (se 5 (by rfl) ⟨48557, by rfl⟩ : syracuseStep 1035893 = 97115) (by norm_num)
theorem B970373 : Blo 850355 970373 := bbase (se 4 (by rfl) ⟨90972, by rfl⟩ : syracuseStep 970373 = 181945) (by norm_num)
theorem B1920653 : Blo 850355 1920653 := bbase (se 3 (by rfl) ⟨360122, by rfl⟩ : syracuseStep 1920653 = 720245) (by norm_num)
theorem B1822421 : Blo 850355 1822421 := bbase (se 7 (by rfl) ⟨21356, by rfl⟩ : syracuseStep 1822421 = 42713) (by norm_num)
theorem B1920725 : Blo 850355 1920725 := bbase (se 7 (by rfl) ⟨22508, by rfl⟩ : syracuseStep 1920725 = 45017) (by norm_num)
theorem B1036001 : Blo 850355 1036001 := bbase (se 2 (by rfl) ⟨388500, by rfl⟩ : syracuseStep 1036001 = 777001) (by norm_num)
theorem B1363709 : Blo 850355 1363709 := bbase (se 3 (by rfl) ⟨255695, by rfl⟩ : syracuseStep 1363709 = 511391) (by norm_num)
theorem B1920797 : Blo 850355 1920797 := bbase (se 3 (by rfl) ⟨360149, by rfl⟩ : syracuseStep 1920797 = 720299) (by norm_num)
theorem B2772773 : Blo 850355 2772773 := bbase (se 4 (by rfl) ⟨259947, by rfl⟩ : syracuseStep 2772773 = 519895) (by norm_num)
theorem B4378421 : Blo 850355 4378421 := bbase (se 5 (by rfl) ⟨205238, by rfl⟩ : syracuseStep 4378421 = 410477) (by norm_num)
theorem B2871125 : Blo 850355 2871125 := bbase (se 9 (by rfl) ⟨8411, by rfl⟩ : syracuseStep 2871125 = 16823) (by norm_num)
theorem B1920869 : Blo 850355 1920869 := bbase (se 4 (by rfl) ⟨180081, by rfl⟩ : syracuseStep 1920869 = 360163) (by norm_num)
theorem B1920941 : Blo 850355 1920941 := bbase (se 3 (by rfl) ⟨360176, by rfl⟩ : syracuseStep 1920941 = 720353) (by norm_num)
theorem B1298357 : Blo 850355 1298357 := bbase (se 5 (by rfl) ⟨60860, by rfl⟩ : syracuseStep 1298357 = 121721) (by norm_num)
theorem B1921013 : Blo 850355 1921013 := bbase (se 5 (by rfl) ⟨90047, by rfl⟩ : syracuseStep 1921013 = 180095) (by norm_num)
theorem B1921085 : Blo 850355 1921085 := bbase (se 3 (by rfl) ⟨360203, by rfl⟩ : syracuseStep 1921085 = 720407) (by norm_num)
theorem B1921157 : Blo 850355 1921157 := bbase (se 4 (by rfl) ⟨180108, by rfl⟩ : syracuseStep 1921157 = 360217) (by norm_num)
theorem B1724557 : Blo 850355 1724557 := bbase (se 3 (by rfl) ⟨323354, by rfl⟩ : syracuseStep 1724557 = 646709) (by norm_num)
theorem B1822925 : Blo 850355 1822925 := bbase (se 3 (by rfl) ⟨341798, by rfl⟩ : syracuseStep 1822925 = 683597) (by norm_num)
theorem B1921229 : Blo 850355 1921229 := bbase (se 3 (by rfl) ⟨360230, by rfl⟩ : syracuseStep 1921229 = 720461) (by norm_num)
theorem B1822933 : Blo 850355 1822933 := bbase (se 7 (by rfl) ⟨21362, by rfl⟩ : syracuseStep 1822933 = 42725) (by norm_num)
theorem B4608245 : Blo 850355 4608245 := bbase (se 5 (by rfl) ⟨216011, by rfl⟩ : syracuseStep 4608245 = 432023) (by norm_num)
theorem B2871557 : Blo 850355 2871557 := bbase (se 4 (by rfl) ⟨269208, by rfl⟩ : syracuseStep 2871557 = 538417) (by norm_num)
theorem B3232021 : Blo 850355 3232021 := bbase (se 6 (by rfl) ⟨75750, by rfl⟩ : syracuseStep 3232021 = 151501) (by norm_num)
theorem B1921301 : Blo 850355 1921301 := bbase (se 6 (by rfl) ⟨45030, by rfl⟩ : syracuseStep 1921301 = 90061) (by norm_num)
theorem B7295285 : Blo 850355 7295285 := bbase (se 5 (by rfl) ⟨341966, by rfl⟩ : syracuseStep 7295285 = 683933) (by norm_num)
theorem B1921373 : Blo 850355 1921373 := bbase (se 3 (by rfl) ⟨360257, by rfl⟩ : syracuseStep 1921373 = 720515) (by norm_num)
theorem B3887461 : Blo 850355 3887461 := bbase (se 4 (by rfl) ⟨364449, by rfl⟩ : syracuseStep 3887461 = 728899) (by norm_num)
theorem B1364381 : Blo 850355 1364381 := bbase (se 3 (by rfl) ⟨255821, by rfl⟩ : syracuseStep 1364381 = 511643) (by norm_num)
theorem B1921445 : Blo 850355 1921445 := bbase (se 4 (by rfl) ⟨180135, by rfl⟩ : syracuseStep 1921445 = 360271) (by norm_num)
theorem B4313573 : Blo 850355 4313573 := bbase (se 4 (by rfl) ⟨404397, by rfl⟩ : syracuseStep 4313573 = 808795) (by norm_num)
theorem B1921517 : Blo 850355 1921517 := bbase (se 3 (by rfl) ⟨360284, by rfl⟩ : syracuseStep 1921517 = 720569) (by norm_num)
theorem B2183669 : Blo 850355 2183669 := bbase (se 5 (by rfl) ⟨102359, by rfl⟩ : syracuseStep 2183669 = 204719) (by norm_num)
theorem B1921589 : Blo 850355 1921589 := bbase (se 5 (by rfl) ⟨90074, by rfl⟩ : syracuseStep 1921589 = 180149) (by norm_num)
theorem B3232325 : Blo 850355 3232325 := bbase (se 4 (by rfl) ⟨303030, by rfl⟩ : syracuseStep 3232325 = 606061) (by norm_num)
theorem B2183773 : Blo 850355 2183773 := bbase (se 3 (by rfl) ⟨409457, by rfl⟩ : syracuseStep 2183773 = 818915) (by norm_num)
theorem B1921661 : Blo 850355 1921661 := bbase (se 3 (by rfl) ⟨360311, by rfl⟩ : syracuseStep 1921661 = 720623) (by norm_num)
theorem B1725077 : Blo 850355 1725077 := bbase (se 6 (by rfl) ⟨40431, by rfl⟩ : syracuseStep 1725077 = 80863) (by norm_num)
theorem B2871989 : Blo 850355 2871989 := bbase (se 5 (by rfl) ⟨134624, by rfl⟩ : syracuseStep 2871989 = 269249) (by norm_num)
theorem B1921733 : Blo 850355 1921733 := bbase (se 4 (by rfl) ⟨180162, by rfl⟩ : syracuseStep 1921733 = 360325) (by norm_num)
theorem B1921805 : Blo 850355 1921805 := bbase (se 3 (by rfl) ⟨360338, by rfl⟩ : syracuseStep 1921805 = 720677) (by norm_num)
theorem B1921877 : Blo 850355 1921877 := bbase (se 9 (by rfl) ⟨5630, by rfl⟩ : syracuseStep 1921877 = 11261) (by norm_num)
theorem B971669 : Blo 850355 971669 := bbase (se 6 (by rfl) ⟨22773, by rfl⟩ : syracuseStep 971669 = 45547) (by norm_num)
theorem B1364893 : Blo 850355 1364893 := bbase (se 3 (by rfl) ⟨255917, by rfl⟩ : syracuseStep 1364893 = 511835) (by norm_num)
theorem B1921949 : Blo 850355 1921949 := bbase (se 3 (by rfl) ⟨360365, by rfl⟩ : syracuseStep 1921949 = 720731) (by norm_num)
theorem B1922021 : Blo 850355 1922021 := bbase (se 4 (by rfl) ⟨180189, by rfl⟩ : syracuseStep 1922021 = 360379) (by norm_num)
theorem B1922093 : Blo 850355 1922093 := bbase (se 3 (by rfl) ⟨360392, by rfl⟩ : syracuseStep 1922093 = 720785) (by norm_num)
theorem B2872421 : Blo 850355 2872421 := bbase (se 4 (by rfl) ⟨269289, by rfl⟩ : syracuseStep 2872421 = 538579) (by norm_num)
theorem B1922165 : Blo 850355 1922165 := bbase (se 5 (by rfl) ⟨90101, by rfl⟩ : syracuseStep 1922165 = 180203) (by norm_num)
theorem B1922237 : Blo 850355 1922237 := bbase (se 3 (by rfl) ⟨360419, by rfl⟩ : syracuseStep 1922237 = 720839) (by norm_num)
theorem B1824061 : Blo 850355 1824061 := bbase (se 3 (by rfl) ⟨342011, by rfl⟩ : syracuseStep 1824061 = 684023) (by norm_num)
theorem B1365349 : Blo 850355 1365349 := bbase (se 4 (by rfl) ⟨128001, by rfl⟩ : syracuseStep 1365349 = 256003) (by norm_num)
theorem B4216229 : Blo 850355 4216229 := bbase (se 4 (by rfl) ⟨395271, by rfl⟩ : syracuseStep 4216229 = 790543) (by norm_num)
theorem B2184653 : Blo 850355 2184653 := bbase (se 3 (by rfl) ⟨409622, by rfl⟩ : syracuseStep 2184653 = 819245) (by norm_num)
theorem B2872853 : Blo 850355 2872853 := bbase (se 6 (by rfl) ⟨67332, by rfl⟩ : syracuseStep 2872853 = 134665) (by norm_num)
theorem B1037881 : Blo 850355 1037881 := bbase (se 2 (by rfl) ⟨389205, by rfl⟩ : syracuseStep 1037881 = 778411) (by norm_num)
theorem B1824437 : Blo 850355 1824437 := bbase (se 5 (by rfl) ⟨85520, by rfl⟩ : syracuseStep 1824437 = 171041) (by norm_num)
theorem B8410837 : Blo 850355 8410837 := bbase (se 7 (by rfl) ⟨98564, by rfl⟩ : syracuseStep 8410837 = 197129) (by norm_num)
theorem B4314869 : Blo 850355 4314869 := bbase (se 5 (by rfl) ⟨202259, by rfl⟩ : syracuseStep 4314869 = 404519) (by norm_num)
theorem B2873285 : Blo 850355 2873285 := bbase (se 4 (by rfl) ⟨269370, by rfl⟩ : syracuseStep 2873285 = 538741) (by norm_num)
theorem B8181749 : Blo 850355 8181749 := bbase (se 5 (by rfl) ⟨383519, by rfl⟩ : syracuseStep 8181749 = 767039) (by norm_num)
theorem B1366021 : Blo 850355 1366021 := bbase (se 4 (by rfl) ⟨128064, by rfl⟩ : syracuseStep 1366021 = 256129) (by norm_num)
theorem B1169485 : Blo 850355 1169485 := bbase (se 3 (by rfl) ⟨219278, by rfl⟩ : syracuseStep 1169485 = 438557) (by norm_num)
theorem B2152565 : Blo 850355 2152565 := bbase (se 5 (by rfl) ⟨100901, by rfl⟩ : syracuseStep 2152565 = 201803) (by norm_num)
theorem B2152757 : Blo 850355 2152757 := bbase (se 5 (by rfl) ⟨100910, by rfl⟩ : syracuseStep 2152757 = 201821) (by norm_num)
theorem B2873717 : Blo 850355 2873717 := bbase (se 5 (by rfl) ⟨134705, by rfl⟩ : syracuseStep 2873717 = 269411) (by norm_num)
theorem B1366445 : Blo 850355 1366445 := bbase (se 3 (by rfl) ⟨256208, by rfl⟩ : syracuseStep 1366445 = 512417) (by norm_num)
theorem B2185805 : Blo 850355 2185805 := bbase (se 3 (by rfl) ⟨409838, by rfl⟩ : syracuseStep 2185805 = 819677) (by norm_num)
theorem B3234437 : Blo 850355 3234437 := bbase (se 4 (by rfl) ⟨303228, by rfl⟩ : syracuseStep 3234437 = 606457) (by norm_num)
theorem B2153101 : Blo 850355 2153101 := bbase (se 3 (by rfl) ⟨403706, by rfl⟩ : syracuseStep 2153101 = 807413) (by norm_num)
theorem B1366733 : Blo 850355 1366733 := bbase (se 3 (by rfl) ⟨256262, by rfl⟩ : syracuseStep 1366733 = 512525) (by norm_num)
theorem B2153213 : Blo 850355 2153213 := bbase (se 3 (by rfl) ⟨403727, by rfl⟩ : syracuseStep 2153213 = 807455) (by norm_num)
theorem B2874149 : Blo 850355 2874149 := bbase (se 4 (by rfl) ⟨269451, by rfl⟩ : syracuseStep 2874149 = 538903) (by norm_num)
theorem B908101 : Blo 850355 908101 := bbase (se 4 (by rfl) ⟨85134, by rfl⟩ : syracuseStep 908101 = 170269) (by norm_num)
theorem B13130581 : Blo 850355 13130581 := bbase (se 9 (by rfl) ⟨38468, by rfl⟩ : syracuseStep 13130581 = 76937) (by norm_num)
theorem B875405 : Blo 850355 875405 := bbase (se 3 (by rfl) ⟨164138, by rfl⟩ : syracuseStep 875405 = 328277) (by norm_num)
theorem B3234725 : Blo 850355 3234725 := bbase (se 4 (by rfl) ⟨303255, by rfl⟩ : syracuseStep 3234725 = 606511) (by norm_num)
theorem B2153405 : Blo 850355 2153405 := bbase (se 3 (by rfl) ⟨403763, by rfl⟩ : syracuseStep 2153405 = 807527) (by norm_num)
theorem B4316165 : Blo 850355 4316165 := bbase (se 4 (by rfl) ⟨404640, by rfl⟩ : syracuseStep 4316165 = 809281) (by norm_num)
theorem B1727525 : Blo 850355 1727525 := bbase (se 4 (by rfl) ⟨161955, by rfl⟩ : syracuseStep 1727525 = 323911) (by norm_num)
theorem B973873 : Blo 850355 973873 := bbase (se 2 (by rfl) ⟨365202, by rfl⟩ : syracuseStep 973873 = 730405) (by norm_num)
theorem B3071125 : Blo 850355 3071125 := bbase (se 6 (by rfl) ⟨71979, by rfl⟩ : syracuseStep 3071125 = 143959) (by norm_num)
theorem B2874581 : Blo 850355 2874581 := bbase (se 7 (by rfl) ⟨33686, by rfl⟩ : syracuseStep 2874581 = 67373) (by norm_num)
theorem B7298261 : Blo 850355 7298261 := bbase (se 7 (by rfl) ⟨85526, by rfl⟩ : syracuseStep 7298261 = 171053) (by norm_num)
theorem B908545 : Blo 850355 908545 := bbase (se 2 (by rfl) ⟨340704, by rfl⟩ : syracuseStep 908545 = 681409) (by norm_num)
theorem B2153749 : Blo 850355 2153749 := bbase (se 6 (by rfl) ⟨50478, by rfl⟩ : syracuseStep 2153749 = 100957) (by norm_num)
theorem B6151477 : Blo 850355 6151477 := bbase (se 5 (by rfl) ⟨288350, by rfl⟩ : syracuseStep 6151477 = 576701) (by norm_num)
theorem B908605 : Blo 850355 908605 := bbase (se 3 (by rfl) ⟨170363, by rfl⟩ : syracuseStep 908605 = 340727) (by norm_num)
theorem B1039697 : Blo 850355 1039697 := bbase (se 2 (by rfl) ⟨389886, by rfl⟩ : syracuseStep 1039697 = 779773) (by norm_num)
theorem B2153861 : Blo 850355 2153861 := bbase (se 4 (by rfl) ⟨201924, by rfl⟩ : syracuseStep 2153861 = 403849) (by norm_num)
theorem B1367533 : Blo 850355 1367533 := bbase (se 3 (by rfl) ⟨256412, by rfl⟩ : syracuseStep 1367533 = 512825) (by norm_num)
theorem B2154053 : Blo 850355 2154053 := bbase (se 4 (by rfl) ⟨201942, by rfl⟩ : syracuseStep 2154053 = 403885) (by norm_num)
theorem B908921 : Blo 850355 908921 := bbase (se 2 (by rfl) ⟨340845, by rfl⟩ : syracuseStep 908921 = 681691) (by norm_num)
theorem B2875013 : Blo 850355 2875013 := bbase (se 4 (by rfl) ⟨269532, by rfl⟩ : syracuseStep 2875013 = 539065) (by norm_num)
theorem B4087493 : Blo 850355 4087493 := bbase (se 4 (by rfl) ⟨383202, by rfl⟩ : syracuseStep 4087493 = 766405) (by norm_num)
theorem B3890981 : Blo 850355 3890981 := bbase (se 4 (by rfl) ⟨364779, by rfl⟩ : syracuseStep 3890981 = 729559) (by norm_num)
theorem B4087685 : Blo 850355 4087685 := bbase (se 4 (by rfl) ⟨383220, by rfl⟩ : syracuseStep 4087685 = 766441) (by norm_num)
theorem B2154397 : Blo 850355 2154397 := bbase (se 3 (by rfl) ⟨403949, by rfl⟩ : syracuseStep 2154397 = 807899) (by norm_num)
theorem B2154509 : Blo 850355 2154509 := bbase (se 3 (by rfl) ⟨403970, by rfl⟩ : syracuseStep 2154509 = 807941) (by norm_num)
theorem B1368085 : Blo 850355 1368085 := bbase (se 6 (by rfl) ⟨32064, by rfl⟩ : syracuseStep 1368085 = 64129) (by norm_num)
theorem B909365 : Blo 850355 909365 := bbase (se 5 (by rfl) ⟨42626, by rfl⟩ : syracuseStep 909365 = 85253) (by norm_num)
theorem B2875445 : Blo 850355 2875445 := bbase (se 5 (by rfl) ⟨134786, by rfl⟩ : syracuseStep 2875445 = 269573) (by norm_num)
theorem B3235909 : Blo 850355 3235909 := bbase (se 4 (by rfl) ⟨303366, by rfl⟩ : syracuseStep 3235909 = 606733) (by norm_num)
theorem B909425 : Blo 850355 909425 := bbase (se 2 (by rfl) ⟨341034, by rfl⟩ : syracuseStep 909425 = 682069) (by norm_num)
theorem B2154701 : Blo 850355 2154701 := bbase (se 3 (by rfl) ⟨404006, by rfl⟩ : syracuseStep 2154701 = 808013) (by norm_num)
theorem B909553 : Blo 850355 909553 := bbase (se 2 (by rfl) ⟨341082, by rfl⟩ : syracuseStep 909553 = 682165) (by norm_num)
theorem B4153589 : Blo 850355 4153589 := bbase (se 5 (by rfl) ⟨194699, by rfl⟩ : syracuseStep 4153589 = 389399) (by norm_num)
theorem B4088069 : Blo 850355 4088069 := bbase (se 4 (by rfl) ⟨383256, by rfl⟩ : syracuseStep 4088069 = 766513) (by norm_num)
theorem B4382981 : Blo 850355 4382981 := bbase (se 4 (by rfl) ⟨410904, by rfl⟩ : syracuseStep 4382981 = 821809) (by norm_num)
theorem B7266581 : Blo 850355 7266581 := bbase (se 6 (by rfl) ⟨170310, by rfl⟩ : syracuseStep 7266581 = 340621) (by norm_num)
theorem B4317461 : Blo 850355 4317461 := bbase (se 6 (by rfl) ⟨101190, by rfl⟩ : syracuseStep 4317461 = 202381) (by norm_num)
theorem B1368341 : Blo 850355 1368341 := bbase (se 6 (by rfl) ⟨32070, by rfl⟩ : syracuseStep 1368341 = 64141) (by norm_num)
theorem B3236213 : Blo 850355 3236213 := bbase (se 5 (by rfl) ⟨151697, by rfl⟩ : syracuseStep 3236213 = 303395) (by norm_num)
theorem B2875877 : Blo 850355 2875877 := bbase (se 4 (by rfl) ⟨269613, by rfl⟩ : syracuseStep 2875877 = 539227) (by norm_num)
theorem B2155045 : Blo 850355 2155045 := bbase (se 4 (by rfl) ⟨202035, by rfl⟩ : syracuseStep 2155045 = 404071) (by norm_num)
theorem B2155157 : Blo 850355 2155157 := bbase (se 6 (by rfl) ⟨50511, by rfl⟩ : syracuseStep 2155157 = 101023) (by norm_num)
theorem B909997 : Blo 850355 909997 := bbase (se 3 (by rfl) ⟨170624, by rfl⟩ : syracuseStep 909997 = 341249) (by norm_num)
theorem B910117 : Blo 850355 910117 := bbase (se 4 (by rfl) ⟨85323, by rfl⟩ : syracuseStep 910117 = 170647) (by norm_num)
theorem B2155349 : Blo 850355 2155349 := bbase (se 9 (by rfl) ⟨6314, by rfl⟩ : syracuseStep 2155349 = 12629) (by norm_num)
theorem B2876309 : Blo 850355 2876309 := bbase (se 6 (by rfl) ⟨67413, by rfl⟩ : syracuseStep 2876309 = 134827) (by norm_num)
theorem B910369 : Blo 850355 910369 := bbase (se 2 (by rfl) ⟨341388, by rfl⟩ : syracuseStep 910369 = 682777) (by norm_num)
theorem B910373 : Blo 850355 910373 := bbase (se 4 (by rfl) ⟨85347, by rfl⟩ : syracuseStep 910373 = 170695) (by norm_num)
theorem B2155693 : Blo 850355 2155693 := bbase (se 3 (by rfl) ⟨404192, by rfl⟩ : syracuseStep 2155693 = 808385) (by norm_num)
theorem B2155805 : Blo 850355 2155805 := bbase (se 3 (by rfl) ⟨404213, by rfl⟩ : syracuseStep 2155805 = 808427) (by norm_num)
theorem B2876741 : Blo 850355 2876741 := bbase (se 4 (by rfl) ⟨269694, by rfl⟩ : syracuseStep 2876741 = 539389) (by norm_num)
theorem B1434989 : Blo 850355 1434989 := bbase (se 3 (by rfl) ⟨269060, by rfl⟩ : syracuseStep 1434989 = 538121) (by norm_num)
theorem B2155997 : Blo 850355 2155997 := bbase (se 3 (by rfl) ⟨404249, by rfl⟩ : syracuseStep 2155997 = 808499) (by norm_num)
theorem B1435117 : Blo 850355 1435117 := bbase (se 3 (by rfl) ⟨269084, by rfl⟩ : syracuseStep 1435117 = 538169) (by norm_num)
theorem B4318757 : Blo 850355 4318757 := bbase (se 4 (by rfl) ⟨404883, by rfl⟩ : syracuseStep 4318757 = 809767) (by norm_num)
theorem B1435205 : Blo 850355 1435205 := bbase (se 4 (by rfl) ⟨134550, by rfl⟩ : syracuseStep 1435205 = 269101) (by norm_num)
theorem B910937 : Blo 850355 910937 := bbase (se 2 (by rfl) ⟨341601, by rfl⟩ : syracuseStep 910937 = 683203) (by norm_num)
theorem B1435333 : Blo 850355 1435333 := bbase (se 4 (by rfl) ⟨134562, by rfl⟩ : syracuseStep 1435333 = 269125) (by norm_num)
theorem B2877173 : Blo 850355 2877173 := bbase (se 5 (by rfl) ⟨134867, by rfl⟩ : syracuseStep 2877173 = 269735) (by norm_num)
theorem B911125 : Blo 850355 911125 := bbase (se 6 (by rfl) ⟨21354, by rfl⟩ : syracuseStep 911125 = 42709) (by norm_num)
theorem B1435421 : Blo 850355 1435421 := bbase (se 3 (by rfl) ⟨269141, by rfl⟩ : syracuseStep 1435421 = 538283) (by norm_num)
theorem B2156341 : Blo 850355 2156341 := bbase (se 5 (by rfl) ⟨101078, by rfl⟩ : syracuseStep 2156341 = 202157) (by norm_num)
theorem B6481781 : Blo 850355 6481781 := bbase (se 5 (by rfl) ⟨303833, by rfl⟩ : syracuseStep 6481781 = 607667) (by norm_num)
theorem B1435549 : Blo 850355 1435549 := bbase (se 3 (by rfl) ⟨269165, by rfl⟩ : syracuseStep 1435549 = 538331) (by norm_num)
theorem B2156453 : Blo 850355 2156453 := bbase (se 4 (by rfl) ⟨202167, by rfl⟩ : syracuseStep 2156453 = 404335) (by norm_num)
theorem B1435637 : Blo 850355 1435637 := bbase (se 5 (by rfl) ⟨67295, by rfl⟩ : syracuseStep 1435637 = 134591) (by norm_num)
theorem B1730557 : Blo 850355 1730557 := bbase (se 3 (by rfl) ⟨324479, by rfl⟩ : syracuseStep 1730557 = 648959) (by norm_num)
theorem B5466133 : Blo 850355 5466133 := bbase (se 6 (by rfl) ⟨128112, by rfl⟩ : syracuseStep 5466133 = 256225) (by norm_num)
theorem B2156645 : Blo 850355 2156645 := bbase (se 4 (by rfl) ⟨202185, by rfl⟩ : syracuseStep 2156645 = 404371) (by norm_num)
theorem B4843637 : Blo 850355 4843637 := bbase (se 5 (by rfl) ⟨227045, by rfl⟩ : syracuseStep 4843637 = 454091) (by norm_num)
theorem B1435765 : Blo 850355 1435765 := bbase (se 5 (by rfl) ⟨67301, by rfl⟩ : syracuseStep 1435765 = 134603) (by norm_num)
theorem B2877605 : Blo 850355 2877605 := bbase (se 4 (by rfl) ⟨269775, by rfl⟩ : syracuseStep 2877605 = 539551) (by norm_num)
theorem B1435853 : Blo 850355 1435853 := bbase (se 3 (by rfl) ⟨269222, by rfl⟩ : syracuseStep 1435853 = 538445) (by norm_num)
theorem B1435981 : Blo 850355 1435981 := bbase (se 3 (by rfl) ⟨269246, by rfl⟩ : syracuseStep 1435981 = 538493) (by norm_num)
theorem B1730965 : Blo 850355 1730965 := bbase (se 6 (by rfl) ⟨40569, by rfl⟩ : syracuseStep 1730965 = 81139) (by norm_num)
theorem B1436069 : Blo 850355 1436069 := bbase (se 4 (by rfl) ⟨134631, by rfl⟩ : syracuseStep 1436069 = 269263) (by norm_num)
theorem B3238325 : Blo 850355 3238325 := bbase (se 5 (by rfl) ⟨151796, by rfl⟩ : syracuseStep 3238325 = 303593) (by norm_num)
theorem B2156989 : Blo 850355 2156989 := bbase (se 3 (by rfl) ⟨404435, by rfl⟩ : syracuseStep 2156989 = 808871) (by norm_num)
theorem B1436197 : Blo 850355 1436197 := bbase (se 4 (by rfl) ⟨134643, by rfl⟩ : syracuseStep 1436197 = 269287) (by norm_num)
theorem B2157101 : Blo 850355 2157101 := bbase (se 3 (by rfl) ⟨404456, by rfl⟩ : syracuseStep 2157101 = 808913) (by norm_num)
theorem B911945 : Blo 850355 911945 := bbase (se 2 (by rfl) ⟨341979, by rfl⟩ : syracuseStep 911945 = 683959) (by norm_num)
theorem B2878037 : Blo 850355 2878037 := bbase (se 8 (by rfl) ⟨16863, by rfl⟩ : syracuseStep 2878037 = 33727) (by norm_num)
theorem B1436285 : Blo 850355 1436285 := bbase (se 3 (by rfl) ⟨269303, by rfl⟩ : syracuseStep 1436285 = 538607) (by norm_num)
theorem B3238613 : Blo 850355 3238613 := bbase (se 7 (by rfl) ⟨37952, by rfl⟩ : syracuseStep 3238613 = 75905) (by norm_num)
theorem B2157293 : Blo 850355 2157293 := bbase (se 3 (by rfl) ⟨404492, by rfl⟩ : syracuseStep 2157293 = 808985) (by norm_num)
theorem B1436413 : Blo 850355 1436413 := bbase (se 3 (by rfl) ⟨269327, by rfl⟩ : syracuseStep 1436413 = 538655) (by norm_num)
theorem B4320053 : Blo 850355 4320053 := bbase (se 5 (by rfl) ⟨202502, by rfl⟩ : syracuseStep 4320053 = 405005) (by norm_num)
theorem B1436501 : Blo 850355 1436501 := bbase (se 9 (by rfl) ⟨4208, by rfl⟩ : syracuseStep 1436501 = 8417) (by norm_num)
theorem B1436629 : Blo 850355 1436629 := bbase (se 7 (by rfl) ⟨16835, by rfl⟩ : syracuseStep 1436629 = 33671) (by norm_num)
theorem B2878469 : Blo 850355 2878469 := bbase (se 4 (by rfl) ⟨269856, by rfl⟩ : syracuseStep 2878469 = 539713) (by norm_num)
theorem B3075077 : Blo 850355 3075077 := bbase (se 4 (by rfl) ⟨288288, by rfl⟩ : syracuseStep 3075077 = 576577) (by norm_num)
theorem B1076257 : Blo 850355 1076257 := bbase (se 2 (by rfl) ⟨403596, by rfl⟩ : syracuseStep 1076257 = 807193) (by norm_num)
theorem B1436717 : Blo 850355 1436717 := bbase (se 3 (by rfl) ⟨269384, by rfl⟩ : syracuseStep 1436717 = 538769) (by norm_num)
theorem B2157637 : Blo 850355 2157637 := bbase (se 4 (by rfl) ⟨202278, by rfl⟩ : syracuseStep 2157637 = 404557) (by norm_num)
theorem B1731677 : Blo 850355 1731677 := bbase (se 3 (by rfl) ⟨324689, by rfl⟩ : syracuseStep 1731677 = 649379) (by norm_num)
theorem B1436845 : Blo 850355 1436845 := bbase (se 3 (by rfl) ⟨269408, by rfl⟩ : syracuseStep 1436845 = 538817) (by norm_num)
theorem B2157749 : Blo 850355 2157749 := bbase (se 5 (by rfl) ⟨101144, by rfl⟩ : syracuseStep 2157749 = 202289) (by norm_num)
theorem B1076429 : Blo 850355 1076429 := bbase (se 3 (by rfl) ⟨201830, by rfl⟩ : syracuseStep 1076429 = 403661) (by norm_num)
theorem B2911477 : Blo 850355 2911477 := bbase (se 5 (by rfl) ⟨136475, by rfl⟩ : syracuseStep 2911477 = 272951) (by norm_num)
theorem B1076485 : Blo 850355 1076485 := bbase (se 4 (by rfl) ⟨100920, by rfl⟩ : syracuseStep 1076485 = 201841) (by norm_num)
theorem B1436933 : Blo 850355 1436933 := bbase (se 4 (by rfl) ⟨134712, by rfl⟩ : syracuseStep 1436933 = 269425) (by norm_num)
theorem B1535269 : Blo 850355 1535269 := bbase (se 4 (by rfl) ⟨143931, by rfl⟩ : syracuseStep 1535269 = 287863) (by norm_num)
theorem B3108149 : Blo 850355 3108149 := bbase (se 5 (by rfl) ⟨145694, by rfl⟩ : syracuseStep 3108149 = 291389) (by norm_num)
theorem B1076581 : Blo 850355 1076581 := bbase (se 4 (by rfl) ⟨100929, by rfl⟩ : syracuseStep 1076581 = 201859) (by norm_num)
theorem B2157941 : Blo 850355 2157941 := bbase (se 5 (by rfl) ⟨101153, by rfl⟩ : syracuseStep 2157941 = 202307) (by norm_num)
theorem B1437061 : Blo 850355 1437061 := bbase (se 4 (by rfl) ⟨134724, by rfl⟩ : syracuseStep 1437061 = 269449) (by norm_num)
theorem B2878901 : Blo 850355 2878901 := bbase (se 5 (by rfl) ⟨134948, by rfl⟩ : syracuseStep 2878901 = 269897) (by norm_num)
theorem B1437149 : Blo 850355 1437149 := bbase (se 3 (by rfl) ⟨269465, by rfl⟩ : syracuseStep 1437149 = 538931) (by norm_num)
theorem B1076753 : Blo 850355 1076753 := bbase (se 2 (by rfl) ⟨403782, by rfl⟩ : syracuseStep 1076753 = 807565) (by norm_num)
theorem B1535557 : Blo 850355 1535557 := bbase (se 4 (by rfl) ⟨143958, by rfl⟩ : syracuseStep 1535557 = 287917) (by norm_num)
theorem B1076809 : Blo 850355 1076809 := bbase (se 2 (by rfl) ⟨403803, by rfl⟩ : syracuseStep 1076809 = 807607) (by norm_num)
theorem B1437277 : Blo 850355 1437277 := bbase (se 3 (by rfl) ⟨269489, by rfl⟩ : syracuseStep 1437277 = 538979) (by norm_num)
theorem B1109597 : Blo 850355 1109597 := bbase (se 3 (by rfl) ⟨208049, by rfl⟩ : syracuseStep 1109597 = 416099) (by norm_num)
theorem B1076905 : Blo 850355 1076905 := bbase (se 2 (by rfl) ⟨403839, by rfl⟩ : syracuseStep 1076905 = 807679) (by norm_num)
theorem B1437365 : Blo 850355 1437365 := bbase (se 5 (by rfl) ⟨67376, by rfl⟩ : syracuseStep 1437365 = 134753) (by norm_num)
theorem B2158285 : Blo 850355 2158285 := bbase (se 3 (by rfl) ⟨404678, by rfl⟩ : syracuseStep 2158285 = 809357) (by norm_num)
theorem B1437493 : Blo 850355 1437493 := bbase (se 5 (by rfl) ⟨67382, by rfl⟩ : syracuseStep 1437493 = 134765) (by norm_num)
theorem B2158397 : Blo 850355 2158397 := bbase (se 3 (by rfl) ⟨404699, by rfl⟩ : syracuseStep 2158397 = 809399) (by norm_num)
theorem B1077077 : Blo 850355 1077077 := bbase (se 9 (by rfl) ⟨3155, by rfl⟩ : syracuseStep 1077077 = 6311) (by norm_num)
theorem B2879333 : Blo 850355 2879333 := bbase (se 4 (by rfl) ⟨269937, by rfl⟩ : syracuseStep 2879333 = 539875) (by norm_num)
theorem B3239797 : Blo 850355 3239797 := bbase (se 5 (by rfl) ⟨151865, by rfl⟩ : syracuseStep 3239797 = 303731) (by norm_num)
theorem B1077133 : Blo 850355 1077133 := bbase (se 3 (by rfl) ⟨201962, by rfl⟩ : syracuseStep 1077133 = 403925) (by norm_num)
theorem B1437581 : Blo 850355 1437581 := bbase (se 3 (by rfl) ⟨269546, by rfl⟩ : syracuseStep 1437581 = 539093) (by norm_num)
theorem B1077229 : Blo 850355 1077229 := bbase (se 3 (by rfl) ⟨201980, by rfl⟩ : syracuseStep 1077229 = 403961) (by norm_num)
theorem B2158589 : Blo 850355 2158589 := bbase (se 3 (by rfl) ⟨404735, by rfl⟩ : syracuseStep 2158589 = 809471) (by norm_num)
theorem B1437709 : Blo 850355 1437709 := bbase (se 3 (by rfl) ⟨269570, by rfl⟩ : syracuseStep 1437709 = 539141) (by norm_num)
theorem B4321349 : Blo 850355 4321349 := bbase (se 4 (by rfl) ⟨405126, by rfl⟩ : syracuseStep 4321349 = 810253) (by norm_num)
theorem B1437797 : Blo 850355 1437797 := bbase (se 4 (by rfl) ⟨134793, by rfl⟩ : syracuseStep 1437797 = 269587) (by norm_num)
theorem B1077401 : Blo 850355 1077401 := bbase (se 2 (by rfl) ⟨404025, by rfl⟩ : syracuseStep 1077401 = 808051) (by norm_num)
theorem B3240101 : Blo 850355 3240101 := bbase (se 4 (by rfl) ⟨303759, by rfl⟩ : syracuseStep 3240101 = 607519) (by norm_num)
theorem B1077457 : Blo 850355 1077457 := bbase (se 2 (by rfl) ⟨404046, by rfl⟩ : syracuseStep 1077457 = 808093) (by norm_num)
theorem B1437925 : Blo 850355 1437925 := bbase (se 4 (by rfl) ⟨134805, by rfl⟩ : syracuseStep 1437925 = 269611) (by norm_num)
theorem B4845845 : Blo 850355 4845845 := bbase (se 6 (by rfl) ⟨113574, by rfl⟩ : syracuseStep 4845845 = 227149) (by norm_num)
theorem B2879765 : Blo 850355 2879765 := bbase (se 6 (by rfl) ⟨67494, by rfl⟩ : syracuseStep 2879765 = 134989) (by norm_num)
theorem B1077553 : Blo 850355 1077553 := bbase (se 2 (by rfl) ⟨404082, by rfl⟩ : syracuseStep 1077553 = 808165) (by norm_num)
theorem B1438013 : Blo 850355 1438013 := bbase (se 3 (by rfl) ⟨269627, by rfl⟩ : syracuseStep 1438013 = 539255) (by norm_num)
theorem B34959701 : Blo 850355 34959701 := bbase (se 10 (by rfl) ⟨51210, by rfl⟩ : syracuseStep 34959701 = 102421) (by norm_num)
theorem B2158933 : Blo 850355 2158933 := bbase (se 10 (by rfl) ⟨3162, by rfl⟩ : syracuseStep 2158933 = 6325) (by norm_num)
theorem B1438141 : Blo 850355 1438141 := bbase (se 3 (by rfl) ⟨269651, by rfl⟩ : syracuseStep 1438141 = 539303) (by norm_num)
theorem B2159045 : Blo 850355 2159045 := bbase (se 4 (by rfl) ⟨202410, by rfl⟩ : syracuseStep 2159045 = 404821) (by norm_num)
theorem B4092373 : Blo 850355 4092373 := bbase (se 7 (by rfl) ⟨47957, by rfl⟩ : syracuseStep 4092373 = 95915) (by norm_num)
theorem B1077725 : Blo 850355 1077725 := bbase (se 3 (by rfl) ⟨202073, by rfl⟩ : syracuseStep 1077725 = 404147) (by norm_num)
theorem B1077781 : Blo 850355 1077781 := bbase (se 6 (by rfl) ⟨25260, by rfl⟩ : syracuseStep 1077781 = 50521) (by norm_num)
theorem B1438229 : Blo 850355 1438229 := bbase (se 6 (by rfl) ⟨33708, by rfl⟩ : syracuseStep 1438229 = 67417) (by norm_num)
theorem B3076661 : Blo 850355 3076661 := bbase (se 5 (by rfl) ⟨144218, by rfl⟩ : syracuseStep 3076661 = 288437) (by norm_num)
theorem B1077877 : Blo 850355 1077877 := bbase (se 5 (by rfl) ⟨50525, by rfl⟩ : syracuseStep 1077877 = 101051) (by norm_num)
theorem B2159237 : Blo 850355 2159237 := bbase (se 4 (by rfl) ⟨202428, by rfl⟩ : syracuseStep 2159237 = 404857) (by norm_num)
theorem B1536653 : Blo 850355 1536653 := bbase (se 3 (by rfl) ⟨288122, by rfl⟩ : syracuseStep 1536653 = 576245) (by norm_num)
theorem B1438357 : Blo 850355 1438357 := bbase (se 6 (by rfl) ⟨33711, by rfl⟩ : syracuseStep 1438357 = 67423) (by norm_num)
theorem B16642709 : Blo 850355 16642709 := bbase (se 6 (by rfl) ⟨390063, by rfl⟩ : syracuseStep 16642709 = 780127) (by norm_num)
theorem B2880197 : Blo 850355 2880197 := bbase (se 4 (by rfl) ⟨270018, by rfl⟩ : syracuseStep 2880197 = 540037) (by norm_num)
theorem B1438445 : Blo 850355 1438445 := bbase (se 3 (by rfl) ⟨269708, by rfl⟩ : syracuseStep 1438445 = 539417) (by norm_num)
theorem B1078049 : Blo 850355 1078049 := bbase (se 2 (by rfl) ⟨404268, by rfl⟩ : syracuseStep 1078049 = 808537) (by norm_num)
theorem B1078105 : Blo 850355 1078105 := bbase (se 2 (by rfl) ⟨404289, by rfl⟩ : syracuseStep 1078105 = 808579) (by norm_num)
theorem B1438573 : Blo 850355 1438573 := bbase (se 3 (by rfl) ⟨269732, by rfl⟩ : syracuseStep 1438573 = 539465) (by norm_num)
theorem B1078201 : Blo 850355 1078201 := bbase (se 2 (by rfl) ⟨404325, by rfl⟩ : syracuseStep 1078201 = 808651) (by norm_num)
theorem B1438661 : Blo 850355 1438661 := bbase (se 4 (by rfl) ⟨134874, by rfl⟩ : syracuseStep 1438661 = 269749) (by norm_num)
theorem B2159581 : Blo 850355 2159581 := bbase (se 3 (by rfl) ⟨404921, by rfl⟩ : syracuseStep 2159581 = 809843) (by norm_num)
theorem B2421829 : Blo 850355 2421829 := bbase (se 4 (by rfl) ⟨227046, by rfl⟩ : syracuseStep 2421829 = 454093) (by norm_num)
theorem B1438789 : Blo 850355 1438789 := bbase (se 4 (by rfl) ⟨134886, by rfl⟩ : syracuseStep 1438789 = 269773) (by norm_num)
theorem B2159693 : Blo 850355 2159693 := bbase (se 3 (by rfl) ⟨404942, by rfl⟩ : syracuseStep 2159693 = 809885) (by norm_num)
theorem B1078373 : Blo 850355 1078373 := bbase (se 4 (by rfl) ⟨101097, by rfl⟩ : syracuseStep 1078373 = 202195) (by norm_num)
theorem B2880629 : Blo 850355 2880629 := bbase (se 5 (by rfl) ⟨135029, by rfl⟩ : syracuseStep 2880629 = 270059) (by norm_num)
theorem B1078429 : Blo 850355 1078429 := bbase (se 3 (by rfl) ⟨202205, by rfl⟩ : syracuseStep 1078429 = 404411) (by norm_num)
theorem B1438877 : Blo 850355 1438877 := bbase (se 3 (by rfl) ⟨269789, by rfl⟩ : syracuseStep 1438877 = 539579) (by norm_num)
theorem B1078525 : Blo 850355 1078525 := bbase (se 3 (by rfl) ⟨202223, by rfl⟩ : syracuseStep 1078525 = 404447) (by norm_num)
theorem B2159885 : Blo 850355 2159885 := bbase (se 3 (by rfl) ⟨404978, by rfl⟩ : syracuseStep 2159885 = 809957) (by norm_num)
theorem B1439005 : Blo 850355 1439005 := bbase (se 3 (by rfl) ⟨269813, by rfl⟩ : syracuseStep 1439005 = 539627) (by norm_num)
theorem B4322645 : Blo 850355 4322645 := bbase (se 13 (by rfl) ⟨791, by rfl⟩ : syracuseStep 4322645 = 1583) (by norm_num)
theorem B1439093 : Blo 850355 1439093 := bbase (se 5 (by rfl) ⟨67457, by rfl⟩ : syracuseStep 1439093 = 134915) (by norm_num)
theorem B1078697 : Blo 850355 1078697 := bbase (se 2 (by rfl) ⟨404511, by rfl⟩ : syracuseStep 1078697 = 809023) (by norm_num)
theorem B1078753 : Blo 850355 1078753 := bbase (se 2 (by rfl) ⟨404532, by rfl⟩ : syracuseStep 1078753 = 809065) (by norm_num)
theorem B1439221 : Blo 850355 1439221 := bbase (se 5 (by rfl) ⟨67463, by rfl⟩ : syracuseStep 1439221 = 134927) (by norm_num)
theorem B2881061 : Blo 850355 2881061 := bbase (se 4 (by rfl) ⟨270099, by rfl⟩ : syracuseStep 2881061 = 540199) (by norm_num)
theorem B1078849 : Blo 850355 1078849 := bbase (se 2 (by rfl) ⟨404568, by rfl⟩ : syracuseStep 1078849 = 809137) (by norm_num)
theorem B1439309 : Blo 850355 1439309 := bbase (se 3 (by rfl) ⟨269870, by rfl⟩ : syracuseStep 1439309 = 539741) (by norm_num)
theorem B2160229 : Blo 850355 2160229 := bbase (se 4 (by rfl) ⟨202521, by rfl⟩ : syracuseStep 2160229 = 405043) (by norm_num)
theorem B1275533 : Blo 850355 1275533 := bbase (se 3 (by rfl) ⟨239162, by rfl⟩ : syracuseStep 1275533 = 478325) (by norm_num)
theorem B1275557 : Blo 850355 1275557 := bbase (se 4 (by rfl) ⟨119583, by rfl⟩ : syracuseStep 1275557 = 239167) (by norm_num)
theorem B1275581 : Blo 850355 1275581 := bbase (se 3 (by rfl) ⟨239171, by rfl⟩ : syracuseStep 1275581 = 478343) (by norm_num)
theorem B1439437 : Blo 850355 1439437 := bbase (se 3 (by rfl) ⟨269894, by rfl⟩ : syracuseStep 1439437 = 539789) (by norm_num)
theorem B1275605 : Blo 850355 1275605 := bbase (se 7 (by rfl) ⟨14948, by rfl⟩ : syracuseStep 1275605 = 29897) (by norm_num)
theorem B2160341 : Blo 850355 2160341 := bbase (se 7 (by rfl) ⟨25316, by rfl⟩ : syracuseStep 2160341 = 50633) (by norm_num)
theorem B1275629 : Blo 850355 1275629 := bbase (se 3 (by rfl) ⟨239180, by rfl⟩ : syracuseStep 1275629 = 478361) (by norm_num)
theorem B1079021 : Blo 850355 1079021 := bbase (se 3 (by rfl) ⟨202316, by rfl⟩ : syracuseStep 1079021 = 404633) (by norm_num)
theorem B1275653 : Blo 850355 1275653 := bbase (se 4 (by rfl) ⟨119592, by rfl⟩ : syracuseStep 1275653 = 239185) (by norm_num)
theorem B1275677 : Blo 850355 1275677 := bbase (se 3 (by rfl) ⟨239189, by rfl⟩ : syracuseStep 1275677 = 478379) (by norm_num)
theorem B1079077 : Blo 850355 1079077 := bbase (se 4 (by rfl) ⟨101163, by rfl⟩ : syracuseStep 1079077 = 202327) (by norm_num)
theorem B1439525 : Blo 850355 1439525 := bbase (se 4 (by rfl) ⟨134955, by rfl⟩ : syracuseStep 1439525 = 269911) (by norm_num)
theorem B1275701 : Blo 850355 1275701 := bbase (se 5 (by rfl) ⟨59798, by rfl⟩ : syracuseStep 1275701 = 119597) (by norm_num)
theorem B1275725 : Blo 850355 1275725 := bbase (se 3 (by rfl) ⟨239198, by rfl⟩ : syracuseStep 1275725 = 478397) (by norm_num)
theorem B1275749 : Blo 850355 1275749 := bbase (se 4 (by rfl) ⟨119601, by rfl⟩ : syracuseStep 1275749 = 239203) (by norm_num)
theorem B1275773 : Blo 850355 1275773 := bbase (se 3 (by rfl) ⟨239207, by rfl⟩ : syracuseStep 1275773 = 478415) (by norm_num)
theorem B1079173 : Blo 850355 1079173 := bbase (se 4 (by rfl) ⟨101172, by rfl⟩ : syracuseStep 1079173 = 202345) (by norm_num)
theorem B1275797 : Blo 850355 1275797 := bbase (se 6 (by rfl) ⟨29901, by rfl⟩ : syracuseStep 1275797 = 59803) (by norm_num)
theorem B2160533 : Blo 850355 2160533 := bbase (se 6 (by rfl) ⟨50637, by rfl⟩ : syracuseStep 2160533 = 101275) (by norm_num)
theorem B1439653 : Blo 850355 1439653 := bbase (se 4 (by rfl) ⟨134967, by rfl⟩ : syracuseStep 1439653 = 269935) (by norm_num)
theorem B1537957 : Blo 850355 1537957 := bbase (se 4 (by rfl) ⟨144183, by rfl⟩ : syracuseStep 1537957 = 288367) (by norm_num)
theorem B1275821 : Blo 850355 1275821 := bbase (se 3 (by rfl) ⟨239216, by rfl⟩ : syracuseStep 1275821 = 478433) (by norm_num)
theorem B1275845 : Blo 850355 1275845 := bbase (se 4 (by rfl) ⟨119610, by rfl⟩ : syracuseStep 1275845 = 239221) (by norm_num)
theorem B2586581 : Blo 850355 2586581 := bbase (se 7 (by rfl) ⟨30311, by rfl⟩ : syracuseStep 2586581 = 60623) (by norm_num)
theorem B2881493 : Blo 850355 2881493 := bbase (se 7 (by rfl) ⟨33767, by rfl⟩ : syracuseStep 2881493 = 67535) (by norm_num)
theorem B1275869 : Blo 850355 1275869 := bbase (se 3 (by rfl) ⟨239225, by rfl⟩ : syracuseStep 1275869 = 478451) (by norm_num)
theorem B1275893 : Blo 850355 1275893 := bbase (se 5 (by rfl) ⟨59807, by rfl⟩ : syracuseStep 1275893 = 119615) (by norm_num)
theorem B3635189 : Blo 850355 3635189 := bbase (se 5 (by rfl) ⟨170399, by rfl⟩ : syracuseStep 3635189 = 340799) (by norm_num)
theorem B1439741 : Blo 850355 1439741 := bbase (se 3 (by rfl) ⟨269951, by rfl⟩ : syracuseStep 1439741 = 539903) (by norm_num)
theorem B1275917 : Blo 850355 1275917 := bbase (se 3 (by rfl) ⟨239234, by rfl⟩ : syracuseStep 1275917 = 478469) (by norm_num)
theorem B1275941 : Blo 850355 1275941 := bbase (se 4 (by rfl) ⟨119619, by rfl⟩ : syracuseStep 1275941 = 239239) (by norm_num)
theorem B1079345 : Blo 850355 1079345 := bbase (se 2 (by rfl) ⟨404754, by rfl⟩ : syracuseStep 1079345 = 809509) (by norm_num)
theorem B1275965 : Blo 850355 1275965 := bbase (se 3 (by rfl) ⟨239243, by rfl⟩ : syracuseStep 1275965 = 478487) (by norm_num)
theorem B1275989 : Blo 850355 1275989 := bbase (se 8 (by rfl) ⟨7476, by rfl⟩ : syracuseStep 1275989 = 14953) (by norm_num)
theorem B1079401 : Blo 850355 1079401 := bbase (se 2 (by rfl) ⟨404775, by rfl⟩ : syracuseStep 1079401 = 809551) (by norm_num)
theorem B1276013 : Blo 850355 1276013 := bbase (se 3 (by rfl) ⟨239252, by rfl⟩ : syracuseStep 1276013 = 478505) (by norm_num)
theorem B1439869 : Blo 850355 1439869 := bbase (se 3 (by rfl) ⟨269975, by rfl⟩ : syracuseStep 1439869 = 539951) (by norm_num)
theorem B1276037 : Blo 850355 1276037 := bbase (se 4 (by rfl) ⟨119628, by rfl⟩ : syracuseStep 1276037 = 239257) (by norm_num)
theorem B1276061 : Blo 850355 1276061 := bbase (se 3 (by rfl) ⟨239261, by rfl⟩ : syracuseStep 1276061 = 478523) (by norm_num)
theorem B1276085 : Blo 850355 1276085 := bbase (se 5 (by rfl) ⟨59816, by rfl⟩ : syracuseStep 1276085 = 119633) (by norm_num)
theorem B1079497 : Blo 850355 1079497 := bbase (se 2 (by rfl) ⟨404811, by rfl⟩ : syracuseStep 1079497 = 809623) (by norm_num)
theorem B1276109 : Blo 850355 1276109 := bbase (se 3 (by rfl) ⟨239270, by rfl⟩ : syracuseStep 1276109 = 478541) (by norm_num)
theorem B1439957 : Blo 850355 1439957 := bbase (se 7 (by rfl) ⟨16874, by rfl⟩ : syracuseStep 1439957 = 33749) (by norm_num)
theorem B1276133 : Blo 850355 1276133 := bbase (se 4 (by rfl) ⟨119637, by rfl⟩ : syracuseStep 1276133 = 239275) (by norm_num)
theorem B3242213 : Blo 850355 3242213 := bbase (se 4 (by rfl) ⟨303957, by rfl⟩ : syracuseStep 3242213 = 607915) (by norm_num)
theorem B2160877 : Blo 850355 2160877 := bbase (se 3 (by rfl) ⟨405164, by rfl⟩ : syracuseStep 2160877 = 810329) (by norm_num)
theorem B1276157 : Blo 850355 1276157 := bbase (se 3 (by rfl) ⟨239279, by rfl⟩ : syracuseStep 1276157 = 478559) (by norm_num)
theorem B1276181 : Blo 850355 1276181 := bbase (se 6 (by rfl) ⟨29910, by rfl⟩ : syracuseStep 1276181 = 59821) (by norm_num)
theorem B1276205 : Blo 850355 1276205 := bbase (se 3 (by rfl) ⟨239288, by rfl⟩ : syracuseStep 1276205 = 478577) (by norm_num)
theorem B1276229 : Blo 850355 1276229 := bbase (se 4 (by rfl) ⟨119646, by rfl⟩ : syracuseStep 1276229 = 239293) (by norm_num)
theorem B1440085 : Blo 850355 1440085 := bbase (se 10 (by rfl) ⟨2109, by rfl⟩ : syracuseStep 1440085 = 4219) (by norm_num)
theorem B1276253 : Blo 850355 1276253 := bbase (se 3 (by rfl) ⟨239297, by rfl⟩ : syracuseStep 1276253 = 478595) (by norm_num)
theorem B2160989 : Blo 850355 2160989 := bbase (se 3 (by rfl) ⟨405185, by rfl⟩ : syracuseStep 2160989 = 810371) (by norm_num)
theorem B1276277 : Blo 850355 1276277 := bbase (se 5 (by rfl) ⟨59825, by rfl⟩ : syracuseStep 1276277 = 119651) (by norm_num)
theorem B1079669 : Blo 850355 1079669 := bbase (se 5 (by rfl) ⟨50609, by rfl⟩ : syracuseStep 1079669 = 101219) (by norm_num)
theorem B2881925 : Blo 850355 2881925 := bbase (se 4 (by rfl) ⟨270180, by rfl⟩ : syracuseStep 2881925 = 540361) (by norm_num)
theorem B1276301 : Blo 850355 1276301 := bbase (se 3 (by rfl) ⟨239306, by rfl⟩ : syracuseStep 1276301 = 478613) (by norm_num)
theorem B1538461 : Blo 850355 1538461 := bbase (se 3 (by rfl) ⟨288461, by rfl⟩ : syracuseStep 1538461 = 576923) (by norm_num)
theorem B1276325 : Blo 850355 1276325 := bbase (se 4 (by rfl) ⟨119655, by rfl⟩ : syracuseStep 1276325 = 239311) (by norm_num)
theorem B1079725 : Blo 850355 1079725 := bbase (se 3 (by rfl) ⟨202448, by rfl⟩ : syracuseStep 1079725 = 404897) (by norm_num)
theorem B1440173 : Blo 850355 1440173 := bbase (se 3 (by rfl) ⟨270032, by rfl⟩ : syracuseStep 1440173 = 540065) (by norm_num)
theorem B1276349 : Blo 850355 1276349 := bbase (se 3 (by rfl) ⟨239315, by rfl⟩ : syracuseStep 1276349 = 478631) (by norm_num)
theorem B1276373 : Blo 850355 1276373 := bbase (se 7 (by rfl) ⟨14957, by rfl⟩ : syracuseStep 1276373 = 29915) (by norm_num)
theorem B1276397 : Blo 850355 1276397 := bbase (se 3 (by rfl) ⟨239324, by rfl⟩ : syracuseStep 1276397 = 478649) (by norm_num)
theorem B1276421 : Blo 850355 1276421 := bbase (se 4 (by rfl) ⟨119664, by rfl⟩ : syracuseStep 1276421 = 239329) (by norm_num)
theorem B3242501 : Blo 850355 3242501 := bbase (se 4 (by rfl) ⟨303984, by rfl⟩ : syracuseStep 3242501 = 607969) (by norm_num)
theorem B1079821 : Blo 850355 1079821 := bbase (se 3 (by rfl) ⟨202466, by rfl⟩ : syracuseStep 1079821 = 404933) (by norm_num)
theorem B1276445 : Blo 850355 1276445 := bbase (se 3 (by rfl) ⟨239333, by rfl⟩ : syracuseStep 1276445 = 478667) (by norm_num)
theorem B2161181 : Blo 850355 2161181 := bbase (se 3 (by rfl) ⟨405221, by rfl⟩ : syracuseStep 2161181 = 810443) (by norm_num)
theorem B2423333 : Blo 850355 2423333 := bbase (se 4 (by rfl) ⟨227187, by rfl⟩ : syracuseStep 2423333 = 454375) (by norm_num)
theorem B1440301 : Blo 850355 1440301 := bbase (se 3 (by rfl) ⟨270056, by rfl⟩ : syracuseStep 1440301 = 540113) (by norm_num)
theorem B1276469 : Blo 850355 1276469 := bbase (se 5 (by rfl) ⟨59834, by rfl⟩ : syracuseStep 1276469 = 119669) (by norm_num)
theorem B1276493 : Blo 850355 1276493 := bbase (se 3 (by rfl) ⟨239342, by rfl⟩ : syracuseStep 1276493 = 478685) (by norm_num)
theorem B3111509 : Blo 850355 3111509 := bbase (se 8 (by rfl) ⟨18231, by rfl⟩ : syracuseStep 3111509 = 36463) (by norm_num)
theorem B1276517 : Blo 850355 1276517 := bbase (se 4 (by rfl) ⟨119673, by rfl⟩ : syracuseStep 1276517 = 239347) (by norm_num)
theorem B4323941 : Blo 850355 4323941 := bbase (se 4 (by rfl) ⟨405369, by rfl⟩ : syracuseStep 4323941 = 810739) (by norm_num)
theorem B1276541 : Blo 850355 1276541 := bbase (se 3 (by rfl) ⟨239351, by rfl⟩ : syracuseStep 1276541 = 478703) (by norm_num)
theorem B1440389 : Blo 850355 1440389 := bbase (se 4 (by rfl) ⟨135036, by rfl⟩ : syracuseStep 1440389 = 270073) (by norm_num)
theorem B1276565 : Blo 850355 1276565 := bbase (se 6 (by rfl) ⟨29919, by rfl⟩ : syracuseStep 1276565 = 59839) (by norm_num)
theorem B1276589 : Blo 850355 1276589 := bbase (se 3 (by rfl) ⟨239360, by rfl⟩ : syracuseStep 1276589 = 478721) (by norm_num)
theorem B1079993 : Blo 850355 1079993 := bbase (se 2 (by rfl) ⟨404997, by rfl⟩ : syracuseStep 1079993 = 809995) (by norm_num)
theorem B1276613 : Blo 850355 1276613 := bbase (se 4 (by rfl) ⟨119682, by rfl⟩ : syracuseStep 1276613 = 239365) (by norm_num)
theorem B1276637 : Blo 850355 1276637 := bbase (se 3 (by rfl) ⟨239369, by rfl⟩ : syracuseStep 1276637 = 478739) (by norm_num)
theorem B1080049 : Blo 850355 1080049 := bbase (se 2 (by rfl) ⟨405018, by rfl⟩ : syracuseStep 1080049 = 810037) (by norm_num)
theorem B1276661 : Blo 850355 1276661 := bbase (se 5 (by rfl) ⟨59843, by rfl⟩ : syracuseStep 1276661 = 119687) (by norm_num)
theorem B1440517 : Blo 850355 1440517 := bbase (se 4 (by rfl) ⟨135048, by rfl⟩ : syracuseStep 1440517 = 270097) (by norm_num)
theorem B1276685 : Blo 850355 1276685 := bbase (se 3 (by rfl) ⟨239378, by rfl⟩ : syracuseStep 1276685 = 478757) (by norm_num)
theorem B1276709 : Blo 850355 1276709 := bbase (se 4 (by rfl) ⟨119691, by rfl⟩ : syracuseStep 1276709 = 239383) (by norm_num)
theorem B2882357 : Blo 850355 2882357 := bbase (se 5 (by rfl) ⟨135110, by rfl⟩ : syracuseStep 2882357 = 270221) (by norm_num)
theorem B1276733 : Blo 850355 1276733 := bbase (se 3 (by rfl) ⟨239387, by rfl⟩ : syracuseStep 1276733 = 478775) (by norm_num)
theorem B1080145 : Blo 850355 1080145 := bbase (se 2 (by rfl) ⟨405054, by rfl⟩ : syracuseStep 1080145 = 810109) (by norm_num)
theorem B1276757 : Blo 850355 1276757 := bbase (se 9 (by rfl) ⟨3740, by rfl⟩ : syracuseStep 1276757 = 7481) (by norm_num)
theorem B1440605 : Blo 850355 1440605 := bbase (se 3 (by rfl) ⟨270113, by rfl⟩ : syracuseStep 1440605 = 540227) (by norm_num)
theorem B1276781 : Blo 850355 1276781 := bbase (se 3 (by rfl) ⟨239396, by rfl⟩ : syracuseStep 1276781 = 478793) (by norm_num)
theorem B2161525 : Blo 850355 2161525 := bbase (se 5 (by rfl) ⟨101321, by rfl⟩ : syracuseStep 2161525 = 202643) (by norm_num)
theorem B1276805 : Blo 850355 1276805 := bbase (se 4 (by rfl) ⟨119700, by rfl⟩ : syracuseStep 1276805 = 239401) (by norm_num)
theorem B1276829 : Blo 850355 1276829 := bbase (se 3 (by rfl) ⟨239405, by rfl⟩ : syracuseStep 1276829 = 478811) (by norm_num)
theorem B1276853 : Blo 850355 1276853 := bbase (se 5 (by rfl) ⟨59852, by rfl⟩ : syracuseStep 1276853 = 119705) (by norm_num)
theorem B1276877 : Blo 850355 1276877 := bbase (se 3 (by rfl) ⟨239414, by rfl⟩ : syracuseStep 1276877 = 478829) (by norm_num)
theorem B1440733 : Blo 850355 1440733 := bbase (se 3 (by rfl) ⟨270137, by rfl⟩ : syracuseStep 1440733 = 540275) (by norm_num)
theorem B1211365 : Blo 850355 1211365 := bbase (se 4 (by rfl) ⟨113565, by rfl⟩ : syracuseStep 1211365 = 227131) (by norm_num)
theorem B1276901 : Blo 850355 1276901 := bbase (se 4 (by rfl) ⟨119709, by rfl⟩ : syracuseStep 1276901 = 239419) (by norm_num)
theorem B3636197 : Blo 850355 3636197 := bbase (se 4 (by rfl) ⟨340893, by rfl⟩ : syracuseStep 3636197 = 681787) (by norm_num)
theorem B2161637 : Blo 850355 2161637 := bbase (se 4 (by rfl) ⟨202653, by rfl⟩ : syracuseStep 2161637 = 405307) (by norm_num)
theorem B1276925 : Blo 850355 1276925 := bbase (se 3 (by rfl) ⟨239423, by rfl⟩ : syracuseStep 1276925 = 478847) (by norm_num)
theorem B1080317 : Blo 850355 1080317 := bbase (se 3 (by rfl) ⟨202559, by rfl⟩ : syracuseStep 1080317 = 405119) (by norm_num)
theorem B1276949 : Blo 850355 1276949 := bbase (se 6 (by rfl) ⟨29928, by rfl⟩ : syracuseStep 1276949 = 59857) (by norm_num)
theorem B1276973 : Blo 850355 1276973 := bbase (se 3 (by rfl) ⟨239432, by rfl⟩ : syracuseStep 1276973 = 478865) (by norm_num)
theorem B1080373 : Blo 850355 1080373 := bbase (se 5 (by rfl) ⟨50642, by rfl⟩ : syracuseStep 1080373 = 101285) (by norm_num)
theorem B1440821 : Blo 850355 1440821 := bbase (se 5 (by rfl) ⟨67538, by rfl⟩ : syracuseStep 1440821 = 135077) (by norm_num)
theorem B1276997 : Blo 850355 1276997 := bbase (se 4 (by rfl) ⟨119718, by rfl⟩ : syracuseStep 1276997 = 239437) (by norm_num)
theorem B1277021 : Blo 850355 1277021 := bbase (se 3 (by rfl) ⟨239441, by rfl⟩ : syracuseStep 1277021 = 478883) (by norm_num)
theorem B1277045 : Blo 850355 1277045 := bbase (se 5 (by rfl) ⟨59861, by rfl⟩ : syracuseStep 1277045 = 119723) (by norm_num)
theorem B1277069 : Blo 850355 1277069 := bbase (se 3 (by rfl) ⟨239450, by rfl⟩ : syracuseStep 1277069 = 478901) (by norm_num)
theorem B1080469 : Blo 850355 1080469 := bbase (se 6 (by rfl) ⟨25323, by rfl⟩ : syracuseStep 1080469 = 50647) (by norm_num)
theorem B1277093 : Blo 850355 1277093 := bbase (se 4 (by rfl) ⟨119727, by rfl⟩ : syracuseStep 1277093 = 239455) (by norm_num)
theorem B2161829 : Blo 850355 2161829 := bbase (se 4 (by rfl) ⟨202671, by rfl⟩ : syracuseStep 2161829 = 405343) (by norm_num)
theorem B1440949 : Blo 850355 1440949 := bbase (se 5 (by rfl) ⟨67544, by rfl⟩ : syracuseStep 1440949 = 135089) (by norm_num)
theorem B1277117 : Blo 850355 1277117 := bbase (se 3 (by rfl) ⟨239459, by rfl⟩ : syracuseStep 1277117 = 478919) (by norm_num)
theorem B1277141 : Blo 850355 1277141 := bbase (se 7 (by rfl) ⟨14966, by rfl⟩ : syracuseStep 1277141 = 29933) (by norm_num)
theorem B2882789 : Blo 850355 2882789 := bbase (se 4 (by rfl) ⟨270261, by rfl⟩ : syracuseStep 2882789 = 540523) (by norm_num)
theorem B1277165 : Blo 850355 1277165 := bbase (se 3 (by rfl) ⟨239468, by rfl⟩ : syracuseStep 1277165 = 478937) (by norm_num)
theorem B1277189 : Blo 850355 1277189 := bbase (se 4 (by rfl) ⟨119736, by rfl⟩ : syracuseStep 1277189 = 239473) (by norm_num)
theorem B1441037 : Blo 850355 1441037 := bbase (se 3 (by rfl) ⟨270194, by rfl⟩ : syracuseStep 1441037 = 540389) (by norm_num)
theorem B1539341 : Blo 850355 1539341 := bbase (se 3 (by rfl) ⟨288626, by rfl⟩ : syracuseStep 1539341 = 577253) (by norm_num)
theorem B1277213 : Blo 850355 1277213 := bbase (se 3 (by rfl) ⟨239477, by rfl⟩ : syracuseStep 1277213 = 478955) (by norm_num)
theorem B1211701 : Blo 850355 1211701 := bbase (se 5 (by rfl) ⟨56798, by rfl⟩ : syracuseStep 1211701 = 113597) (by norm_num)
theorem B1277237 : Blo 850355 1277237 := bbase (se 5 (by rfl) ⟨59870, by rfl⟩ : syracuseStep 1277237 = 119741) (by norm_num)
theorem B1080641 : Blo 850355 1080641 := bbase (se 2 (by rfl) ⟨405240, by rfl⟩ : syracuseStep 1080641 = 810481) (by norm_num)
theorem B1277261 : Blo 850355 1277261 := bbase (se 3 (by rfl) ⟨239486, by rfl⟩ : syracuseStep 1277261 = 478973) (by norm_num)
theorem B1277285 : Blo 850355 1277285 := bbase (se 4 (by rfl) ⟨119745, by rfl⟩ : syracuseStep 1277285 = 239491) (by norm_num)
theorem B1080697 : Blo 850355 1080697 := bbase (se 2 (by rfl) ⟨405261, by rfl⟩ : syracuseStep 1080697 = 810523) (by norm_num)
theorem B1277309 : Blo 850355 1277309 := bbase (se 3 (by rfl) ⟨239495, by rfl⟩ : syracuseStep 1277309 = 478991) (by norm_num)
theorem B1441165 : Blo 850355 1441165 := bbase (se 3 (by rfl) ⟨270218, by rfl⟩ : syracuseStep 1441165 = 540437) (by norm_num)
theorem B1277333 : Blo 850355 1277333 := bbase (se 6 (by rfl) ⟨29937, by rfl⟩ : syracuseStep 1277333 = 59875) (by norm_num)
theorem B1277357 : Blo 850355 1277357 := bbase (se 3 (by rfl) ⟨239504, by rfl⟩ : syracuseStep 1277357 = 479009) (by norm_num)
theorem B1277381 : Blo 850355 1277381 := bbase (se 4 (by rfl) ⟨119754, by rfl⟩ : syracuseStep 1277381 = 239509) (by norm_num)
theorem B1080793 : Blo 850355 1080793 := bbase (se 2 (by rfl) ⟨405297, by rfl⟩ : syracuseStep 1080793 = 810595) (by norm_num)
theorem B1277405 : Blo 850355 1277405 := bbase (se 3 (by rfl) ⟨239513, by rfl⟩ : syracuseStep 1277405 = 479027) (by norm_num)
theorem B1441253 : Blo 850355 1441253 := bbase (se 4 (by rfl) ⟨135117, by rfl⟩ : syracuseStep 1441253 = 270235) (by norm_num)
theorem B1277429 : Blo 850355 1277429 := bbase (se 5 (by rfl) ⟨59879, by rfl⟩ : syracuseStep 1277429 = 119759) (by norm_num)
theorem B2162173 : Blo 850355 2162173 := bbase (se 3 (by rfl) ⟨405407, by rfl⟩ : syracuseStep 2162173 = 810815) (by norm_num)
theorem B1211917 : Blo 850355 1211917 := bbase (se 3 (by rfl) ⟨227234, by rfl⟩ : syracuseStep 1211917 = 454469) (by norm_num)
theorem B1277453 : Blo 850355 1277453 := bbase (se 3 (by rfl) ⟨239522, by rfl⟩ : syracuseStep 1277453 = 479045) (by norm_num)
theorem B1277477 : Blo 850355 1277477 := bbase (se 4 (by rfl) ⟨119763, by rfl⟩ : syracuseStep 1277477 = 239527) (by norm_num)
theorem B1277501 : Blo 850355 1277501 := bbase (se 3 (by rfl) ⟨239531, by rfl⟩ : syracuseStep 1277501 = 479063) (by norm_num)
theorem B1277525 : Blo 850355 1277525 := bbase (se 8 (by rfl) ⟨7485, by rfl⟩ : syracuseStep 1277525 = 14971) (by norm_num)
theorem B1441381 : Blo 850355 1441381 := bbase (se 4 (by rfl) ⟨135129, by rfl⟩ : syracuseStep 1441381 = 270259) (by norm_num)
theorem B1277549 : Blo 850355 1277549 := bbase (se 3 (by rfl) ⟨239540, by rfl⟩ : syracuseStep 1277549 = 479081) (by norm_num)
theorem B2162285 : Blo 850355 2162285 := bbase (se 3 (by rfl) ⟨405428, by rfl⟩ : syracuseStep 2162285 = 810857) (by norm_num)
theorem B1277573 : Blo 850355 1277573 := bbase (se 4 (by rfl) ⟨119772, by rfl⟩ : syracuseStep 1277573 = 239545) (by norm_num)
theorem B1080965 : Blo 850355 1080965 := bbase (se 4 (by rfl) ⟨101340, by rfl⟩ : syracuseStep 1080965 = 202681) (by norm_num)
theorem B2883221 : Blo 850355 2883221 := bbase (se 6 (by rfl) ⟨67575, by rfl⟩ : syracuseStep 2883221 = 135151) (by norm_num)
theorem B1277597 : Blo 850355 1277597 := bbase (se 3 (by rfl) ⟨239549, by rfl⟩ : syracuseStep 1277597 = 479099) (by norm_num)
theorem B3243685 : Blo 850355 3243685 := bbase (se 4 (by rfl) ⟨304095, by rfl⟩ : syracuseStep 3243685 = 608191) (by norm_num)
theorem B1277621 : Blo 850355 1277621 := bbase (se 5 (by rfl) ⟨59888, by rfl⟩ : syracuseStep 1277621 = 119777) (by norm_num)
theorem B1081021 : Blo 850355 1081021 := bbase (se 3 (by rfl) ⟨202691, by rfl⟩ : syracuseStep 1081021 = 405383) (by norm_num)
theorem B1441469 : Blo 850355 1441469 := bbase (se 3 (by rfl) ⟨270275, by rfl⟩ : syracuseStep 1441469 = 540551) (by norm_num)
theorem B1277645 : Blo 850355 1277645 := bbase (se 3 (by rfl) ⟨239558, by rfl⟩ : syracuseStep 1277645 = 479117) (by norm_num)
theorem B1277669 : Blo 850355 1277669 := bbase (se 4 (by rfl) ⟨119781, by rfl⟩ : syracuseStep 1277669 = 239563) (by norm_num)
theorem B1277693 : Blo 850355 1277693 := bbase (se 3 (by rfl) ⟨239567, by rfl⟩ : syracuseStep 1277693 = 479135) (by norm_num)
theorem B1277717 : Blo 850355 1277717 := bbase (se 6 (by rfl) ⟨29946, by rfl⟩ : syracuseStep 1277717 = 59893) (by norm_num)
theorem B1081117 : Blo 850355 1081117 := bbase (se 3 (by rfl) ⟨202709, by rfl⟩ : syracuseStep 1081117 = 405419) (by norm_num)
theorem B1277741 : Blo 850355 1277741 := bbase (se 3 (by rfl) ⟨239576, by rfl⟩ : syracuseStep 1277741 = 479153) (by norm_num)
theorem B2162477 : Blo 850355 2162477 := bbase (se 3 (by rfl) ⟨405464, by rfl⟩ : syracuseStep 2162477 = 810929) (by norm_num)
theorem B1441597 : Blo 850355 1441597 := bbase (se 3 (by rfl) ⟨270299, by rfl⟩ : syracuseStep 1441597 = 540599) (by norm_num)
theorem B1277765 : Blo 850355 1277765 := bbase (se 4 (by rfl) ⟨119790, by rfl⟩ : syracuseStep 1277765 = 239581) (by norm_num)
theorem B1277789 : Blo 850355 1277789 := bbase (se 3 (by rfl) ⟨239585, by rfl⟩ : syracuseStep 1277789 = 479171) (by norm_num)
theorem B1277813 : Blo 850355 1277813 := bbase (se 5 (by rfl) ⟨59897, by rfl⟩ : syracuseStep 1277813 = 119795) (by norm_num)
theorem B1212293 : Blo 850355 1212293 := bbase (se 4 (by rfl) ⟨113652, by rfl⟩ : syracuseStep 1212293 = 227305) (by norm_num)
theorem B1277837 : Blo 850355 1277837 := bbase (se 3 (by rfl) ⟨239594, by rfl⟩ : syracuseStep 1277837 = 479189) (by norm_num)
theorem B1441685 : Blo 850355 1441685 := bbase (se 6 (by rfl) ⟨33789, by rfl⟩ : syracuseStep 1441685 = 67579) (by norm_num)
theorem B1277861 : Blo 850355 1277861 := bbase (se 4 (by rfl) ⟨119799, by rfl⟩ : syracuseStep 1277861 = 239599) (by norm_num)
theorem B1277885 : Blo 850355 1277885 := bbase (se 3 (by rfl) ⟨239603, by rfl⟩ : syracuseStep 1277885 = 479207) (by norm_num)
theorem B1081289 : Blo 850355 1081289 := bbase (se 2 (by rfl) ⟨405483, by rfl⟩ : syracuseStep 1081289 = 810967) (by norm_num)
theorem B1277909 : Blo 850355 1277909 := bbase (se 7 (by rfl) ⟨14975, by rfl⟩ : syracuseStep 1277909 = 29951) (by norm_num)
theorem B983021 : Blo 850355 983021 := bbase (se 3 (by rfl) ⟨184316, by rfl⟩ : syracuseStep 983021 = 368633) (by norm_num)
theorem B1277933 : Blo 850355 1277933 := bbase (se 3 (by rfl) ⟨239612, by rfl⟩ : syracuseStep 1277933 = 479225) (by norm_num)
theorem B851971 : Blo 850355 851971 := bstep (se 1 (by rfl) ⟨638978, by rfl⟩ : syracuseStep 851971 = 1277957) B1277957
theorem B1277969 : Blo 850355 1277969 := bstep (se 2 (by rfl) ⟨479238, by rfl⟩ : syracuseStep 1277969 = 958477) B958477
theorem B851987 : Blo 850355 851987 := bstep (se 1 (by rfl) ⟨638990, by rfl⟩ : syracuseStep 851987 = 1277981) B1277981
theorem B1277987 : Blo 850355 1277987 := bstep (se 1 (by rfl) ⟨958490, by rfl⟩ : syracuseStep 1277987 = 1916981) B1916981
theorem B852003 : Blo 850355 852003 := bstep (se 1 (by rfl) ⟨639002, by rfl⟩ : syracuseStep 852003 = 1278005) B1278005
theorem B852019 : Blo 850355 852019 := bstep (se 1 (by rfl) ⟨639014, by rfl⟩ : syracuseStep 852019 = 1278029) B1278029
theorem B1278017 : Blo 850355 1278017 := bstep (se 2 (by rfl) ⟨479256, by rfl⟩ : syracuseStep 1278017 = 958513) B958513
theorem B852035 : Blo 850355 852035 := bstep (se 1 (by rfl) ⟨639026, by rfl⟩ : syracuseStep 852035 = 1278053) B1278053
theorem B1278035 : Blo 850355 1278035 := bstep (se 1 (by rfl) ⟨958526, by rfl⟩ : syracuseStep 1278035 = 1917053) B1917053
theorem B852051 : Blo 850355 852051 := bstep (se 1 (by rfl) ⟨639038, by rfl⟩ : syracuseStep 852051 = 1278077) B1278077
theorem B852067 : Blo 850355 852067 := bstep (se 1 (by rfl) ⟨639050, by rfl⟩ : syracuseStep 852067 = 1278101) B1278101
theorem B1278065 : Blo 850355 1278065 := bstep (se 2 (by rfl) ⟨479274, by rfl⟩ : syracuseStep 1278065 = 958549) B958549
theorem B852083 : Blo 850355 852083 := bstep (se 1 (by rfl) ⟨639062, by rfl⟩ : syracuseStep 852083 = 1278125) B1278125
theorem B1278083 : Blo 850355 1278083 := bstep (se 1 (by rfl) ⟨958562, by rfl⟩ : syracuseStep 1278083 = 1917125) B1917125
theorem B852099 : Blo 850355 852099 := bstep (se 1 (by rfl) ⟨639074, by rfl⟩ : syracuseStep 852099 = 1278149) B1278149
theorem B2424973 : Blo 850355 2424973 := bstep (se 3 (by rfl) ⟨454682, by rfl⟩ : syracuseStep 2424973 = 909365) B909365
theorem B852115 : Blo 850355 852115 := bstep (se 1 (by rfl) ⟨639086, by rfl⟩ : syracuseStep 852115 = 1278173) B1278173
theorem B1278113 : Blo 850355 1278113 := bstep (se 2 (by rfl) ⟨479292, by rfl⟩ : syracuseStep 1278113 = 958585) B958585
theorem B852131 : Blo 850355 852131 := bstep (se 1 (by rfl) ⟨639098, by rfl⟩ : syracuseStep 852131 = 1278197) B1278197
theorem B1278131 : Blo 850355 1278131 := bstep (se 1 (by rfl) ⟨958598, by rfl⟩ : syracuseStep 1278131 = 1917197) B1917197
theorem B852147 : Blo 850355 852147 := bstep (se 1 (by rfl) ⟨639110, by rfl⟩ : syracuseStep 852147 = 1278221) B1278221
theorem B852163 : Blo 850355 852163 := bstep (se 1 (by rfl) ⟨639122, by rfl⟩ : syracuseStep 852163 = 1278245) B1278245
theorem B1278161 : Blo 850355 1278161 := bstep (se 2 (by rfl) ⟨479310, by rfl⟩ : syracuseStep 1278161 = 958621) B958621
theorem B852179 : Blo 850355 852179 := bstep (se 1 (by rfl) ⟨639134, by rfl⟩ : syracuseStep 852179 = 1278269) B1278269
theorem B1278179 : Blo 850355 1278179 := bstep (se 1 (by rfl) ⟨958634, by rfl⟩ : syracuseStep 1278179 = 1917269) B1917269
theorem B852195 : Blo 850355 852195 := bstep (se 1 (by rfl) ⟨639146, by rfl⟩ : syracuseStep 852195 = 1278293) B1278293
theorem B852211 : Blo 850355 852211 := bstep (se 1 (by rfl) ⟨639158, by rfl⟩ : syracuseStep 852211 = 1278317) B1278317
theorem B1278209 : Blo 850355 1278209 := bstep (se 2 (by rfl) ⟨479328, by rfl⟩ : syracuseStep 1278209 = 958657) B958657
theorem B852227 : Blo 850355 852227 := bstep (se 1 (by rfl) ⟨639170, by rfl⟩ : syracuseStep 852227 = 1278341) B1278341
theorem B1278227 : Blo 850355 1278227 := bstep (se 1 (by rfl) ⟨958670, by rfl⟩ : syracuseStep 1278227 = 1917341) B1917341
theorem B852243 : Blo 850355 852243 := bstep (se 1 (by rfl) ⟨639182, by rfl⟩ : syracuseStep 852243 = 1278365) B1278365
theorem B852259 : Blo 850355 852259 := bstep (se 1 (by rfl) ⟨639194, by rfl⟩ : syracuseStep 852259 = 1278389) B1278389
theorem B2425133 : Blo 850355 2425133 := bstep (se 3 (by rfl) ⟨454712, by rfl⟩ : syracuseStep 2425133 = 909425) B909425
theorem B1278257 : Blo 850355 1278257 := bstep (se 2 (by rfl) ⟨479346, by rfl⟩ : syracuseStep 1278257 = 958693) B958693
theorem B852275 : Blo 850355 852275 := bstep (se 1 (by rfl) ⟨639206, by rfl⟩ : syracuseStep 852275 = 1278413) B1278413
theorem B1212737 : Blo 850355 1212737 := bstep (se 2 (by rfl) ⟨454776, by rfl⟩ : syracuseStep 1212737 = 909553) B909553
theorem B1278275 : Blo 850355 1278275 := bstep (se 1 (by rfl) ⟨958706, by rfl⟩ : syracuseStep 1278275 = 1917413) B1917413
theorem B852291 : Blo 850355 852291 := bstep (se 1 (by rfl) ⟨639218, by rfl⟩ : syracuseStep 852291 = 1278437) B1278437
theorem B852307 : Blo 850355 852307 := bstep (se 1 (by rfl) ⟨639230, by rfl⟩ : syracuseStep 852307 = 1278461) B1278461
theorem B1278305 : Blo 850355 1278305 := bstep (se 2 (by rfl) ⟨479364, by rfl⟩ : syracuseStep 1278305 = 958729) B958729
theorem B852323 : Blo 850355 852323 := bstep (se 1 (by rfl) ⟨639242, by rfl⟩ : syracuseStep 852323 = 1278485) B1278485
theorem B3277169 : Blo 850355 3277169 := bstep (se 2 (by rfl) ⟨1228938, by rfl⟩ : syracuseStep 3277169 = 2457877) B2457877
theorem B1278323 : Blo 850355 1278323 := bstep (se 1 (by rfl) ⟨958742, by rfl⟩ : syracuseStep 1278323 = 1917485) B1917485
theorem B852339 : Blo 850355 852339 := bstep (se 1 (by rfl) ⟨639254, by rfl⟩ : syracuseStep 852339 = 1278509) B1278509
theorem B852355 : Blo 850355 852355 := bstep (se 1 (by rfl) ⟨639266, by rfl⟩ : syracuseStep 852355 = 1278533) B1278533
theorem B1278353 : Blo 850355 1278353 := bstep (se 2 (by rfl) ⟨479382, by rfl⟩ : syracuseStep 1278353 = 958765) B958765
theorem B852371 : Blo 850355 852371 := bstep (se 1 (by rfl) ⟨639278, by rfl⟩ : syracuseStep 852371 = 1278557) B1278557
theorem B1278371 : Blo 850355 1278371 := bstep (se 1 (by rfl) ⟨958778, by rfl⟩ : syracuseStep 1278371 = 1917557) B1917557
theorem B852387 : Blo 850355 852387 := bstep (se 1 (by rfl) ⟨639290, by rfl⟩ : syracuseStep 852387 = 1278581) B1278581
theorem B1212851 : Blo 850355 1212851 := bstep (se 1 (by rfl) ⟨909638, by rfl⟩ : syracuseStep 1212851 = 1819277) B1819277
theorem B852403 : Blo 850355 852403 := bstep (se 1 (by rfl) ⟨639302, by rfl⟩ : syracuseStep 852403 = 1278605) B1278605
theorem B1278401 : Blo 850355 1278401 := bstep (se 2 (by rfl) ⟨479400, by rfl⟩ : syracuseStep 1278401 = 958801) B958801
theorem B852419 : Blo 850355 852419 := bstep (se 1 (by rfl) ⟨639314, by rfl⟩ : syracuseStep 852419 = 1278629) B1278629
theorem B1278419 : Blo 850355 1278419 := bstep (se 1 (by rfl) ⟨958814, by rfl⟩ : syracuseStep 1278419 = 1917629) B1917629
theorem B852435 : Blo 850355 852435 := bstep (se 1 (by rfl) ⟨639326, by rfl⟩ : syracuseStep 852435 = 1278653) B1278653
theorem B2425315 : Blo 850355 2425315 := bstep (se 1 (by rfl) ⟨1818986, by rfl⟩ : syracuseStep 2425315 = 3637973) B3637973
theorem B852451 : Blo 850355 852451 := bstep (se 1 (by rfl) ⟨639338, by rfl⟩ : syracuseStep 852451 = 1278677) B1278677
theorem B1278449 : Blo 850355 1278449 := bstep (se 2 (by rfl) ⟨479418, by rfl⟩ : syracuseStep 1278449 = 958837) B958837
theorem B852467 : Blo 850355 852467 := bstep (se 1 (by rfl) ⟨639350, by rfl⟩ : syracuseStep 852467 = 1278701) B1278701
theorem B1212931 : Blo 850355 1212931 := bstep (se 1 (by rfl) ⟨909698, by rfl⟩ : syracuseStep 1212931 = 1819397) B1819397
theorem B1278467 : Blo 850355 1278467 := bstep (se 1 (by rfl) ⟨958850, by rfl⟩ : syracuseStep 1278467 = 1917701) B1917701
theorem B852483 : Blo 850355 852483 := bstep (se 1 (by rfl) ⟨639362, by rfl⟩ : syracuseStep 852483 = 1278725) B1278725
theorem B852499 : Blo 850355 852499 := bstep (se 1 (by rfl) ⟨639374, by rfl⟩ : syracuseStep 852499 = 1278749) B1278749
theorem B1278497 : Blo 850355 1278497 := bstep (se 2 (by rfl) ⟨479436, by rfl⟩ : syracuseStep 1278497 = 958873) B958873
theorem B852515 : Blo 850355 852515 := bstep (se 1 (by rfl) ⟨639386, by rfl⟩ : syracuseStep 852515 = 1278773) B1278773
theorem B1278515 : Blo 850355 1278515 := bstep (se 1 (by rfl) ⟨958886, by rfl⟩ : syracuseStep 1278515 = 1917773) B1917773
theorem B852531 : Blo 850355 852531 := bstep (se 1 (by rfl) ⟨639398, by rfl⟩ : syracuseStep 852531 = 1278797) B1278797
theorem B852547 : Blo 850355 852547 := bstep (se 1 (by rfl) ⟨639410, by rfl⟩ : syracuseStep 852547 = 1278821) B1278821
theorem B1278545 : Blo 850355 1278545 := bstep (se 2 (by rfl) ⟨479454, by rfl⟩ : syracuseStep 1278545 = 958909) B958909
theorem B852563 : Blo 850355 852563 := bstep (se 1 (by rfl) ⟨639422, by rfl⟩ : syracuseStep 852563 = 1278845) B1278845
theorem B1278563 : Blo 850355 1278563 := bstep (se 1 (by rfl) ⟨958922, by rfl⟩ : syracuseStep 1278563 = 1917845) B1917845
theorem B852579 : Blo 850355 852579 := bstep (se 1 (by rfl) ⟨639434, by rfl⟩ : syracuseStep 852579 = 1278869) B1278869
theorem B852595 : Blo 850355 852595 := bstep (se 1 (by rfl) ⟨639446, by rfl⟩ : syracuseStep 852595 = 1278893) B1278893
theorem B1278593 : Blo 850355 1278593 := bstep (se 2 (by rfl) ⟨479472, by rfl⟩ : syracuseStep 1278593 = 958945) B958945
theorem B852611 : Blo 850355 852611 := bstep (se 1 (by rfl) ⟨639458, by rfl⟩ : syracuseStep 852611 = 1278917) B1278917
theorem B1278611 : Blo 850355 1278611 := bstep (se 1 (by rfl) ⟨958958, by rfl⟩ : syracuseStep 1278611 = 1917917) B1917917
theorem B852627 : Blo 850355 852627 := bstep (se 1 (by rfl) ⟨639470, by rfl⟩ : syracuseStep 852627 = 1278941) B1278941
theorem B852643 : Blo 850355 852643 := bstep (se 1 (by rfl) ⟨639482, by rfl⟩ : syracuseStep 852643 = 1278965) B1278965
theorem B1278641 : Blo 850355 1278641 := bstep (se 2 (by rfl) ⟨479490, by rfl⟩ : syracuseStep 1278641 = 958981) B958981
theorem B852659 : Blo 850355 852659 := bstep (se 1 (by rfl) ⟨639494, by rfl⟩ : syracuseStep 852659 = 1278989) B1278989
theorem B1278659 : Blo 850355 1278659 := bstep (se 1 (by rfl) ⟨958994, by rfl⟩ : syracuseStep 1278659 = 1917989) B1917989
theorem B852675 : Blo 850355 852675 := bstep (se 1 (by rfl) ⟨639506, by rfl⟩ : syracuseStep 852675 = 1279013) B1279013
theorem B852691 : Blo 850355 852691 := bstep (se 1 (by rfl) ⟨639518, by rfl⟩ : syracuseStep 852691 = 1279037) B1279037
theorem B1278689 : Blo 850355 1278689 := bstep (se 2 (by rfl) ⟨479508, by rfl⟩ : syracuseStep 1278689 = 959017) B959017
theorem B852707 : Blo 850355 852707 := bstep (se 1 (by rfl) ⟨639530, by rfl⟩ : syracuseStep 852707 = 1279061) B1279061
theorem B1278707 : Blo 850355 1278707 := bstep (se 1 (by rfl) ⟨959030, by rfl⟩ : syracuseStep 1278707 = 1918061) B1918061
theorem B852723 : Blo 850355 852723 := bstep (se 1 (by rfl) ⟨639542, by rfl⟩ : syracuseStep 852723 = 1279085) B1279085
theorem B852739 : Blo 850355 852739 := bstep (se 1 (by rfl) ⟨639554, by rfl⟩ : syracuseStep 852739 = 1279109) B1279109
theorem B1278737 : Blo 850355 1278737 := bstep (se 2 (by rfl) ⟨479526, by rfl⟩ : syracuseStep 1278737 = 959053) B959053
theorem B852755 : Blo 850355 852755 := bstep (se 1 (by rfl) ⟨639566, by rfl⟩ : syracuseStep 852755 = 1279133) B1279133
theorem B1278755 : Blo 850355 1278755 := bstep (se 1 (by rfl) ⟨959066, by rfl⟩ : syracuseStep 1278755 = 1918133) B1918133
theorem B852771 : Blo 850355 852771 := bstep (se 1 (by rfl) ⟨639578, by rfl⟩ : syracuseStep 852771 = 1279157) B1279157
theorem B852787 : Blo 850355 852787 := bstep (se 1 (by rfl) ⟨639590, by rfl⟩ : syracuseStep 852787 = 1279181) B1279181
theorem B1278785 : Blo 850355 1278785 := bstep (se 2 (by rfl) ⟨479544, by rfl⟩ : syracuseStep 1278785 = 959089) B959089
theorem B852803 : Blo 850355 852803 := bstep (se 1 (by rfl) ⟨639602, by rfl⟩ : syracuseStep 852803 = 1279205) B1279205
theorem B1278803 : Blo 850355 1278803 := bstep (se 1 (by rfl) ⟨959102, by rfl⟩ : syracuseStep 1278803 = 1918205) B1918205
theorem B852819 : Blo 850355 852819 := bstep (se 1 (by rfl) ⟨639614, by rfl⟩ : syracuseStep 852819 = 1279229) B1279229
theorem B852835 : Blo 850355 852835 := bstep (se 1 (by rfl) ⟨639626, by rfl⟩ : syracuseStep 852835 = 1279253) B1279253
theorem B1278833 : Blo 850355 1278833 := bstep (se 2 (by rfl) ⟨479562, by rfl⟩ : syracuseStep 1278833 = 959125) B959125
theorem B852851 : Blo 850355 852851 := bstep (se 1 (by rfl) ⟨639638, by rfl⟩ : syracuseStep 852851 = 1279277) B1279277
theorem B1278851 : Blo 850355 1278851 := bstep (se 1 (by rfl) ⟨959138, by rfl⟩ : syracuseStep 1278851 = 1918277) B1918277
theorem B852867 : Blo 850355 852867 := bstep (se 1 (by rfl) ⟨639650, by rfl⟩ : syracuseStep 852867 = 1279301) B1279301
theorem B852883 : Blo 850355 852883 := bstep (se 1 (by rfl) ⟨639662, by rfl⟩ : syracuseStep 852883 = 1279325) B1279325
theorem B1278881 : Blo 850355 1278881 := bstep (se 2 (by rfl) ⟨479580, by rfl⟩ : syracuseStep 1278881 = 959161) B959161
theorem B852899 : Blo 850355 852899 := bstep (se 1 (by rfl) ⟨639674, by rfl⟩ : syracuseStep 852899 = 1279349) B1279349
theorem B1278899 : Blo 850355 1278899 := bstep (se 1 (by rfl) ⟨959174, by rfl⟩ : syracuseStep 1278899 = 1918349) B1918349
theorem B852915 : Blo 850355 852915 := bstep (se 1 (by rfl) ⟨639686, by rfl⟩ : syracuseStep 852915 = 1279373) B1279373
theorem B852931 : Blo 850355 852931 := bstep (se 1 (by rfl) ⟨639698, by rfl⟩ : syracuseStep 852931 = 1279397) B1279397
theorem B1278929 : Blo 850355 1278929 := bstep (se 2 (by rfl) ⟨479598, by rfl⟩ : syracuseStep 1278929 = 959197) B959197
theorem B852947 : Blo 850355 852947 := bstep (se 1 (by rfl) ⟨639710, by rfl⟩ : syracuseStep 852947 = 1279421) B1279421
theorem B1278947 : Blo 850355 1278947 := bstep (se 1 (by rfl) ⟨959210, by rfl⟩ : syracuseStep 1278947 = 1918421) B1918421
theorem B852963 : Blo 850355 852963 := bstep (se 1 (by rfl) ⟨639722, by rfl⟩ : syracuseStep 852963 = 1279445) B1279445
theorem B852979 : Blo 850355 852979 := bstep (se 1 (by rfl) ⟨639734, by rfl⟩ : syracuseStep 852979 = 1279469) B1279469
theorem B1278977 : Blo 850355 1278977 := bstep (se 2 (by rfl) ⟨479616, by rfl⟩ : syracuseStep 1278977 = 959233) B959233
theorem B852995 : Blo 850355 852995 := bstep (se 1 (by rfl) ⟨639746, by rfl⟩ : syracuseStep 852995 = 1279493) B1279493
theorem B1278995 : Blo 850355 1278995 := bstep (se 1 (by rfl) ⟨959246, by rfl⟩ : syracuseStep 1278995 = 1918493) B1918493
theorem B853011 : Blo 850355 853011 := bstep (se 1 (by rfl) ⟨639758, by rfl⟩ : syracuseStep 853011 = 1279517) B1279517
theorem B853027 : Blo 850355 853027 := bstep (se 1 (by rfl) ⟨639770, by rfl⟩ : syracuseStep 853027 = 1279541) B1279541
theorem B1213489 : Blo 850355 1213489 := bstep (se 2 (by rfl) ⟨455058, by rfl⟩ : syracuseStep 1213489 = 910117) B910117
theorem B1279025 : Blo 850355 1279025 := bstep (se 2 (by rfl) ⟨479634, by rfl⟩ : syracuseStep 1279025 = 959269) B959269
theorem B853043 : Blo 850355 853043 := bstep (se 1 (by rfl) ⟨639782, by rfl⟩ : syracuseStep 853043 = 1279565) B1279565
theorem B1279043 : Blo 850355 1279043 := bstep (se 1 (by rfl) ⟨959282, by rfl⟩ : syracuseStep 1279043 = 1918565) B1918565
theorem B853059 : Blo 850355 853059 := bstep (se 1 (by rfl) ⟨639794, by rfl⟩ : syracuseStep 853059 = 1279589) B1279589
theorem B5538893 : Blo 850355 5538893 := bstep (se 3 (by rfl) ⟨1038542, by rfl⟩ : syracuseStep 5538893 = 2077085) B2077085
theorem B853075 : Blo 850355 853075 := bstep (se 1 (by rfl) ⟨639806, by rfl⟩ : syracuseStep 853075 = 1279613) B1279613
theorem B1279073 : Blo 850355 1279073 := bstep (se 2 (by rfl) ⟨479652, by rfl⟩ : syracuseStep 1279073 = 959305) B959305
theorem B853091 : Blo 850355 853091 := bstep (se 1 (by rfl) ⟨639818, by rfl⟩ : syracuseStep 853091 = 1279637) B1279637
theorem B1279091 : Blo 850355 1279091 := bstep (se 1 (by rfl) ⟨959318, by rfl⟩ : syracuseStep 1279091 = 1918637) B1918637
theorem B853107 : Blo 850355 853107 := bstep (se 1 (by rfl) ⟨639830, by rfl⟩ : syracuseStep 853107 = 1279661) B1279661
theorem B853123 : Blo 850355 853123 := bstep (se 1 (by rfl) ⟨639842, by rfl⟩ : syracuseStep 853123 = 1279685) B1279685
theorem B1279121 : Blo 850355 1279121 := bstep (se 2 (by rfl) ⟨479670, by rfl⟩ : syracuseStep 1279121 = 959341) B959341
theorem B853139 : Blo 850355 853139 := bstep (se 1 (by rfl) ⟨639854, by rfl⟩ : syracuseStep 853139 = 1279709) B1279709
theorem B5604515 : Blo 850355 5604515 := bstep (se 1 (by rfl) ⟨4203386, by rfl⟩ : syracuseStep 5604515 = 8406773) B8406773
theorem B1279139 : Blo 850355 1279139 := bstep (se 1 (by rfl) ⟨959354, by rfl⟩ : syracuseStep 1279139 = 1918709) B1918709
theorem B853155 : Blo 850355 853155 := bstep (se 1 (by rfl) ⟨639866, by rfl⟩ : syracuseStep 853155 = 1279733) B1279733
theorem B1311923 : Blo 850355 1311923 := bstep (se 1 (by rfl) ⟨983942, by rfl⟩ : syracuseStep 1311923 = 1967885) B1967885
theorem B853171 : Blo 850355 853171 := bstep (se 1 (by rfl) ⟨639878, by rfl⟩ : syracuseStep 853171 = 1279757) B1279757
theorem B1279169 : Blo 850355 1279169 := bstep (se 2 (by rfl) ⟨479688, by rfl⟩ : syracuseStep 1279169 = 959377) B959377
theorem B853187 : Blo 850355 853187 := bstep (se 1 (by rfl) ⟨639890, by rfl⟩ : syracuseStep 853187 = 1279781) B1279781
theorem B1279187 : Blo 850355 1279187 := bstep (se 1 (by rfl) ⟨959390, by rfl⟩ : syracuseStep 1279187 = 1918781) B1918781
theorem B853203 : Blo 850355 853203 := bstep (se 1 (by rfl) ⟨639902, by rfl⟩ : syracuseStep 853203 = 1279805) B1279805
theorem B853219 : Blo 850355 853219 := bstep (se 1 (by rfl) ⟨639914, by rfl⟩ : syracuseStep 853219 = 1279829) B1279829
theorem B1279217 : Blo 850355 1279217 := bstep (se 2 (by rfl) ⟨479706, by rfl⟩ : syracuseStep 1279217 = 959413) B959413
theorem B853235 : Blo 850355 853235 := bstep (se 1 (by rfl) ⟨639926, by rfl⟩ : syracuseStep 853235 = 1279853) B1279853
theorem B1279235 : Blo 850355 1279235 := bstep (se 1 (by rfl) ⟨959426, by rfl⟩ : syracuseStep 1279235 = 1918853) B1918853
theorem B853251 : Blo 850355 853251 := bstep (se 1 (by rfl) ⟨639938, by rfl⟩ : syracuseStep 853251 = 1279877) B1279877
theorem B853267 : Blo 850355 853267 := bstep (se 1 (by rfl) ⟨639950, by rfl⟩ : syracuseStep 853267 = 1279901) B1279901
theorem B1279265 : Blo 850355 1279265 := bstep (se 2 (by rfl) ⟨479724, by rfl⟩ : syracuseStep 1279265 = 959449) B959449
theorem B853283 : Blo 850355 853283 := bstep (se 1 (by rfl) ⟨639962, by rfl⟩ : syracuseStep 853283 = 1279925) B1279925
theorem B1279283 : Blo 850355 1279283 := bstep (se 1 (by rfl) ⟨959462, by rfl⟩ : syracuseStep 1279283 = 1918925) B1918925
theorem B853299 : Blo 850355 853299 := bstep (se 1 (by rfl) ⟨639974, by rfl⟩ : syracuseStep 853299 = 1279949) B1279949
theorem B853315 : Blo 850355 853315 := bstep (se 1 (by rfl) ⟨639986, by rfl⟩ : syracuseStep 853315 = 1279973) B1279973
theorem B1279313 : Blo 850355 1279313 := bstep (se 2 (by rfl) ⟨479742, by rfl⟩ : syracuseStep 1279313 = 959485) B959485
theorem B853331 : Blo 850355 853331 := bstep (se 1 (by rfl) ⟨639998, by rfl⟩ : syracuseStep 853331 = 1279997) B1279997
theorem B8750435 : Blo 850355 8750435 := bstep (se 1 (by rfl) ⟨6562826, by rfl⟩ : syracuseStep 8750435 = 13125653) B13125653
theorem B1279331 : Blo 850355 1279331 := bstep (se 1 (by rfl) ⟨959498, by rfl⟩ : syracuseStep 1279331 = 1918997) B1918997
theorem B853347 : Blo 850355 853347 := bstep (se 1 (by rfl) ⟨640010, by rfl⟩ : syracuseStep 853347 = 1280021) B1280021
theorem B853363 : Blo 850355 853363 := bstep (se 1 (by rfl) ⟨640022, by rfl⟩ : syracuseStep 853363 = 1280045) B1280045
theorem B1279361 : Blo 850355 1279361 := bstep (se 2 (by rfl) ⟨479760, by rfl⟩ : syracuseStep 1279361 = 959521) B959521
theorem B853379 : Blo 850355 853379 := bstep (se 1 (by rfl) ⟨640034, by rfl⟩ : syracuseStep 853379 = 1280069) B1280069
theorem B1279379 : Blo 850355 1279379 := bstep (se 1 (by rfl) ⟨959534, by rfl⟩ : syracuseStep 1279379 = 1919069) B1919069
theorem B853395 : Blo 850355 853395 := bstep (se 1 (by rfl) ⟨640046, by rfl⟩ : syracuseStep 853395 = 1280093) B1280093
theorem B853411 : Blo 850355 853411 := bstep (se 1 (by rfl) ⟨640058, by rfl⟩ : syracuseStep 853411 = 1280117) B1280117
theorem B1279409 : Blo 850355 1279409 := bstep (se 2 (by rfl) ⟨479778, by rfl⟩ : syracuseStep 1279409 = 959557) B959557
theorem B853427 : Blo 850355 853427 := bstep (se 1 (by rfl) ⟨640070, by rfl⟩ : syracuseStep 853427 = 1280141) B1280141
theorem B1279427 : Blo 850355 1279427 := bstep (se 1 (by rfl) ⟨959570, by rfl⟩ : syracuseStep 1279427 = 1919141) B1919141
theorem B853443 : Blo 850355 853443 := bstep (se 1 (by rfl) ⟨640082, by rfl⟩ : syracuseStep 853443 = 1280165) B1280165
theorem B853459 : Blo 850355 853459 := bstep (se 1 (by rfl) ⟨640094, by rfl⟩ : syracuseStep 853459 = 1280189) B1280189
theorem B1279457 : Blo 850355 1279457 := bstep (se 2 (by rfl) ⟨479796, by rfl⟩ : syracuseStep 1279457 = 959593) B959593
theorem B853475 : Blo 850355 853475 := bstep (se 1 (by rfl) ⟨640106, by rfl⟩ : syracuseStep 853475 = 1280213) B1280213
theorem B853491 : Blo 850355 853491 := bstep (se 1 (by rfl) ⟨640118, by rfl⟩ : syracuseStep 853491 = 1280237) B1280237
theorem B1279475 : Blo 850355 1279475 := bstep (se 1 (by rfl) ⟨959606, by rfl⟩ : syracuseStep 1279475 = 1919213) B1919213
theorem B1639939 : Blo 850355 1639939 := bstep (se 1 (by rfl) ⟨1229954, by rfl⟩ : syracuseStep 1639939 = 2459909) B2459909
theorem B853507 : Blo 850355 853507 := bstep (se 1 (by rfl) ⟨640130, by rfl⟩ : syracuseStep 853507 = 1280261) B1280261
theorem B1279505 : Blo 850355 1279505 := bstep (se 2 (by rfl) ⟨479814, by rfl⟩ : syracuseStep 1279505 = 959629) B959629
theorem B853523 : Blo 850355 853523 := bstep (se 1 (by rfl) ⟨640142, by rfl⟩ : syracuseStep 853523 = 1280285) B1280285
theorem B1279523 : Blo 850355 1279523 := bstep (se 1 (by rfl) ⟨959642, by rfl⟩ : syracuseStep 1279523 = 1919285) B1919285
theorem B853539 : Blo 850355 853539 := bstep (se 1 (by rfl) ⟨640154, by rfl⟩ : syracuseStep 853539 = 1280309) B1280309
theorem B853555 : Blo 850355 853555 := bstep (se 1 (by rfl) ⟨640166, by rfl⟩ : syracuseStep 853555 = 1280333) B1280333
theorem B1279553 : Blo 850355 1279553 := bstep (se 2 (by rfl) ⟨479832, by rfl⟩ : syracuseStep 1279553 = 959665) B959665
theorem B853571 : Blo 850355 853571 := bstep (se 1 (by rfl) ⟨640178, by rfl⟩ : syracuseStep 853571 = 1280357) B1280357
theorem B1279571 : Blo 850355 1279571 := bstep (se 1 (by rfl) ⟨959678, by rfl⟩ : syracuseStep 1279571 = 1919357) B1919357
theorem B853587 : Blo 850355 853587 := bstep (se 1 (by rfl) ⟨640190, by rfl⟩ : syracuseStep 853587 = 1280381) B1280381
theorem B5834339 : Blo 850355 5834339 := bstep (se 1 (by rfl) ⟨4375754, by rfl⟩ : syracuseStep 5834339 = 8751509) B8751509
theorem B853603 : Blo 850355 853603 := bstep (se 1 (by rfl) ⟨640202, by rfl⟩ : syracuseStep 853603 = 1280405) B1280405
theorem B1279601 : Blo 850355 1279601 := bstep (se 2 (by rfl) ⟨479850, by rfl⟩ : syracuseStep 1279601 = 959701) B959701
theorem B853619 : Blo 850355 853619 := bstep (se 1 (by rfl) ⟨640214, by rfl⟩ : syracuseStep 853619 = 1280429) B1280429
theorem B1279619 : Blo 850355 1279619 := bstep (se 1 (by rfl) ⟨959714, by rfl⟩ : syracuseStep 1279619 = 1919429) B1919429
theorem B853635 : Blo 850355 853635 := bstep (se 1 (by rfl) ⟨640226, by rfl⟩ : syracuseStep 853635 = 1280453) B1280453
theorem B5473925 : Blo 850355 5473925 := bstep (se 4 (by rfl) ⟨513180, by rfl⟩ : syracuseStep 5473925 = 1026361) B1026361
theorem B853651 : Blo 850355 853651 := bstep (se 1 (by rfl) ⟨640238, by rfl⟩ : syracuseStep 853651 = 1280477) B1280477
theorem B1279649 : Blo 850355 1279649 := bstep (se 2 (by rfl) ⟨479868, by rfl⟩ : syracuseStep 1279649 = 959737) B959737
theorem B853667 : Blo 850355 853667 := bstep (se 1 (by rfl) ⟨640250, by rfl⟩ : syracuseStep 853667 = 1280501) B1280501
theorem B1279667 : Blo 850355 1279667 := bstep (se 1 (by rfl) ⟨959750, by rfl⟩ : syracuseStep 1279667 = 1919501) B1919501
theorem B853683 : Blo 850355 853683 := bstep (se 1 (by rfl) ⟨640262, by rfl⟩ : syracuseStep 853683 = 1280525) B1280525
theorem B853699 : Blo 850355 853699 := bstep (se 1 (by rfl) ⟨640274, by rfl⟩ : syracuseStep 853699 = 1280549) B1280549
theorem B1279697 : Blo 850355 1279697 := bstep (se 2 (by rfl) ⟨479886, by rfl⟩ : syracuseStep 1279697 = 959773) B959773
theorem B853715 : Blo 850355 853715 := bstep (se 1 (by rfl) ⟨640286, by rfl⟩ : syracuseStep 853715 = 1280573) B1280573
theorem B1279715 : Blo 850355 1279715 := bstep (se 1 (by rfl) ⟨959786, by rfl⟩ : syracuseStep 1279715 = 1919573) B1919573
theorem B853731 : Blo 850355 853731 := bstep (se 1 (by rfl) ⟨640298, by rfl⟩ : syracuseStep 853731 = 1280597) B1280597
theorem B1214195 : Blo 850355 1214195 := bstep (se 1 (by rfl) ⟨910646, by rfl⟩ : syracuseStep 1214195 = 1821293) B1821293
theorem B853747 : Blo 850355 853747 := bstep (se 1 (by rfl) ⟨640310, by rfl⟩ : syracuseStep 853747 = 1280621) B1280621
theorem B1279745 : Blo 850355 1279745 := bstep (se 2 (by rfl) ⟨479904, by rfl⟩ : syracuseStep 1279745 = 959809) B959809
theorem B853763 : Blo 850355 853763 := bstep (se 1 (by rfl) ⟨640322, by rfl⟩ : syracuseStep 853763 = 1280645) B1280645
theorem B1279763 : Blo 850355 1279763 := bstep (se 1 (by rfl) ⟨959822, by rfl⟩ : syracuseStep 1279763 = 1919645) B1919645
theorem B853779 : Blo 850355 853779 := bstep (se 1 (by rfl) ⟨640334, by rfl⟩ : syracuseStep 853779 = 1280669) B1280669
theorem B853795 : Blo 850355 853795 := bstep (se 1 (by rfl) ⟨640346, by rfl⟩ : syracuseStep 853795 = 1280693) B1280693
theorem B1279793 : Blo 850355 1279793 := bstep (se 2 (by rfl) ⟨479922, by rfl⟩ : syracuseStep 1279793 = 959845) B959845
theorem B853811 : Blo 850355 853811 := bstep (se 1 (by rfl) ⟨640358, by rfl⟩ : syracuseStep 853811 = 1280717) B1280717
theorem B1279811 : Blo 850355 1279811 := bstep (se 1 (by rfl) ⟨959858, by rfl⟩ : syracuseStep 1279811 = 1919717) B1919717
theorem B853827 : Blo 850355 853827 := bstep (se 1 (by rfl) ⟨640370, by rfl⟩ : syracuseStep 853827 = 1280741) B1280741
theorem B2426705 : Blo 850355 2426705 := bstep (se 2 (by rfl) ⟨910014, by rfl⟩ : syracuseStep 2426705 = 1820029) B1820029
theorem B853843 : Blo 850355 853843 := bstep (se 1 (by rfl) ⟨640382, by rfl⟩ : syracuseStep 853843 = 1280765) B1280765
theorem B1279841 : Blo 850355 1279841 := bstep (se 2 (by rfl) ⟨479940, by rfl⟩ : syracuseStep 1279841 = 959881) B959881
theorem B4097891 : Blo 850355 4097891 := bstep (se 1 (by rfl) ⟨3073418, by rfl⟩ : syracuseStep 4097891 = 6146837) B6146837
theorem B853859 : Blo 850355 853859 := bstep (se 1 (by rfl) ⟨640394, by rfl⟩ : syracuseStep 853859 = 1280789) B1280789
theorem B1279859 : Blo 850355 1279859 := bstep (se 1 (by rfl) ⟨959894, by rfl⟩ : syracuseStep 1279859 = 1919789) B1919789
theorem B853875 : Blo 850355 853875 := bstep (se 1 (by rfl) ⟨640406, by rfl⟩ : syracuseStep 853875 = 1280813) B1280813
theorem B853891 : Blo 850355 853891 := bstep (se 1 (by rfl) ⟨640418, by rfl⟩ : syracuseStep 853891 = 1280837) B1280837
theorem B1279889 : Blo 850355 1279889 := bstep (se 2 (by rfl) ⟨479958, by rfl⟩ : syracuseStep 1279889 = 959917) B959917
theorem B853907 : Blo 850355 853907 := bstep (se 1 (by rfl) ⟨640430, by rfl⟩ : syracuseStep 853907 = 1280861) B1280861
theorem B1279907 : Blo 850355 1279907 := bstep (se 1 (by rfl) ⟨959930, by rfl⟩ : syracuseStep 1279907 = 1919861) B1919861
theorem B853923 : Blo 850355 853923 := bstep (se 1 (by rfl) ⟨640442, by rfl⟩ : syracuseStep 853923 = 1280885) B1280885
theorem B853939 : Blo 850355 853939 := bstep (se 1 (by rfl) ⟨640454, by rfl⟩ : syracuseStep 853939 = 1280909) B1280909
theorem B1279937 : Blo 850355 1279937 := bstep (se 2 (by rfl) ⟨479976, by rfl⟩ : syracuseStep 1279937 = 959953) B959953
theorem B853955 : Blo 850355 853955 := bstep (se 1 (by rfl) ⟨640466, by rfl⟩ : syracuseStep 853955 = 1280933) B1280933
theorem B1279955 : Blo 850355 1279955 := bstep (se 1 (by rfl) ⟨959966, by rfl⟩ : syracuseStep 1279955 = 1919933) B1919933
theorem B853971 : Blo 850355 853971 := bstep (se 1 (by rfl) ⟨640478, by rfl⟩ : syracuseStep 853971 = 1280957) B1280957
theorem B853987 : Blo 850355 853987 := bstep (se 1 (by rfl) ⟨640490, by rfl⟩ : syracuseStep 853987 = 1280981) B1280981
theorem B1279985 : Blo 850355 1279985 := bstep (se 2 (by rfl) ⟨479994, by rfl⟩ : syracuseStep 1279985 = 959989) B959989
theorem B854003 : Blo 850355 854003 := bstep (se 1 (by rfl) ⟨640502, by rfl⟩ : syracuseStep 854003 = 1281005) B1281005
theorem B1280003 : Blo 850355 1280003 := bstep (se 1 (by rfl) ⟨960002, by rfl⟩ : syracuseStep 1280003 = 1920005) B1920005
theorem B854019 : Blo 850355 854019 := bstep (se 1 (by rfl) ⟨640514, by rfl⟩ : syracuseStep 854019 = 1281029) B1281029
theorem B854035 : Blo 850355 854035 := bstep (se 1 (by rfl) ⟨640526, by rfl⟩ : syracuseStep 854035 = 1281053) B1281053
theorem B1280033 : Blo 850355 1280033 := bstep (se 2 (by rfl) ⟨480012, by rfl⟩ : syracuseStep 1280033 = 960025) B960025
theorem B854051 : Blo 850355 854051 := bstep (se 1 (by rfl) ⟨640538, by rfl⟩ : syracuseStep 854051 = 1281077) B1281077
theorem B1280051 : Blo 850355 1280051 := bstep (se 1 (by rfl) ⟨960038, by rfl⟩ : syracuseStep 1280051 = 1920077) B1920077
theorem B854067 : Blo 850355 854067 := bstep (se 1 (by rfl) ⟨640550, by rfl⟩ : syracuseStep 854067 = 1281101) B1281101
theorem B854083 : Blo 850355 854083 := bstep (se 1 (by rfl) ⟨640562, by rfl⟩ : syracuseStep 854083 = 1281125) B1281125
theorem B1280081 : Blo 850355 1280081 := bstep (se 2 (by rfl) ⟨480030, by rfl⟩ : syracuseStep 1280081 = 960061) B960061
theorem B854099 : Blo 850355 854099 := bstep (se 1 (by rfl) ⟨640574, by rfl⟩ : syracuseStep 854099 = 1281149) B1281149
theorem B1280099 : Blo 850355 1280099 := bstep (se 1 (by rfl) ⟨960074, by rfl⟩ : syracuseStep 1280099 = 1920149) B1920149
theorem B854115 : Blo 850355 854115 := bstep (se 1 (by rfl) ⟨640586, by rfl⟩ : syracuseStep 854115 = 1281173) B1281173
theorem B854131 : Blo 850355 854131 := bstep (se 1 (by rfl) ⟨640598, by rfl⟩ : syracuseStep 854131 = 1281197) B1281197
theorem B1280129 : Blo 850355 1280129 := bstep (se 2 (by rfl) ⟨480048, by rfl⟩ : syracuseStep 1280129 = 960097) B960097
theorem B854147 : Blo 850355 854147 := bstep (se 1 (by rfl) ⟨640610, by rfl⟩ : syracuseStep 854147 = 1281221) B1281221
theorem B1280147 : Blo 850355 1280147 := bstep (se 1 (by rfl) ⟨960110, by rfl⟩ : syracuseStep 1280147 = 1920221) B1920221
theorem B854163 : Blo 850355 854163 := bstep (se 1 (by rfl) ⟨640622, by rfl⟩ : syracuseStep 854163 = 1281245) B1281245
theorem B854179 : Blo 850355 854179 := bstep (se 1 (by rfl) ⟨640634, by rfl⟩ : syracuseStep 854179 = 1281269) B1281269
theorem B1280177 : Blo 850355 1280177 := bstep (se 2 (by rfl) ⟨480066, by rfl⟩ : syracuseStep 1280177 = 960133) B960133
theorem B854195 : Blo 850355 854195 := bstep (se 1 (by rfl) ⟨640646, by rfl⟩ : syracuseStep 854195 = 1281293) B1281293
theorem B1280195 : Blo 850355 1280195 := bstep (se 1 (by rfl) ⟨960146, by rfl⟩ : syracuseStep 1280195 = 1920293) B1920293
theorem B854211 : Blo 850355 854211 := bstep (se 1 (by rfl) ⟨640658, by rfl⟩ : syracuseStep 854211 = 1281317) B1281317
theorem B854227 : Blo 850355 854227 := bstep (se 1 (by rfl) ⟨640670, by rfl⟩ : syracuseStep 854227 = 1281341) B1281341
theorem B1280225 : Blo 850355 1280225 := bstep (se 2 (by rfl) ⟨480084, by rfl⟩ : syracuseStep 1280225 = 960169) B960169
theorem B854243 : Blo 850355 854243 := bstep (se 1 (by rfl) ⟨640682, by rfl⟩ : syracuseStep 854243 = 1281365) B1281365
theorem B1280243 : Blo 850355 1280243 := bstep (se 1 (by rfl) ⟨960182, by rfl⟩ : syracuseStep 1280243 = 1920365) B1920365
theorem B854259 : Blo 850355 854259 := bstep (se 1 (by rfl) ⟨640694, by rfl⟩ : syracuseStep 854259 = 1281389) B1281389
theorem B854275 : Blo 850355 854275 := bstep (se 1 (by rfl) ⟨640706, by rfl⟩ : syracuseStep 854275 = 1281413) B1281413
theorem B1280273 : Blo 850355 1280273 := bstep (se 2 (by rfl) ⟨480102, by rfl⟩ : syracuseStep 1280273 = 960205) B960205
theorem B854291 : Blo 850355 854291 := bstep (se 1 (by rfl) ⟨640718, by rfl⟩ : syracuseStep 854291 = 1281437) B1281437
theorem B1280291 : Blo 850355 1280291 := bstep (se 1 (by rfl) ⟨960218, by rfl⟩ : syracuseStep 1280291 = 1920437) B1920437
theorem B854307 : Blo 850355 854307 := bstep (se 1 (by rfl) ⟨640730, by rfl⟩ : syracuseStep 854307 = 1281461) B1281461
theorem B854323 : Blo 850355 854323 := bstep (se 1 (by rfl) ⟨640742, by rfl⟩ : syracuseStep 854323 = 1281485) B1281485
theorem B1280321 : Blo 850355 1280321 := bstep (se 2 (by rfl) ⟨480120, by rfl⟩ : syracuseStep 1280321 = 960241) B960241
theorem B854339 : Blo 850355 854339 := bstep (se 1 (by rfl) ⟨640754, by rfl⟩ : syracuseStep 854339 = 1281509) B1281509
theorem B1280339 : Blo 850355 1280339 := bstep (se 1 (by rfl) ⟨960254, by rfl⟩ : syracuseStep 1280339 = 1920509) B1920509
theorem B854355 : Blo 850355 854355 := bstep (se 1 (by rfl) ⟨640766, by rfl⟩ : syracuseStep 854355 = 1281533) B1281533
theorem B3279203 : Blo 850355 3279203 := bstep (se 1 (by rfl) ⟨2459402, by rfl⟩ : syracuseStep 3279203 = 4918805) B4918805
theorem B1214833 : Blo 850355 1214833 := bstep (se 2 (by rfl) ⟨455562, by rfl⟩ : syracuseStep 1214833 = 911125) B911125
theorem B1280369 : Blo 850355 1280369 := bstep (se 2 (by rfl) ⟨480138, by rfl⟩ : syracuseStep 1280369 = 960277) B960277
theorem B1280387 : Blo 850355 1280387 := bstep (se 1 (by rfl) ⟨960290, by rfl⟩ : syracuseStep 1280387 = 1920581) B1920581
theorem B2591117 : Blo 850355 2591117 := bstep (se 3 (by rfl) ⟨485834, by rfl⟩ : syracuseStep 2591117 = 971669) B971669
theorem B1280417 : Blo 850355 1280417 := bstep (se 2 (by rfl) ⟨480156, by rfl⟩ : syracuseStep 1280417 = 960313) B960313
theorem B2623907 : Blo 850355 2623907 := bstep (se 1 (by rfl) ⟨1967930, by rfl⟩ : syracuseStep 2623907 = 3935861) B3935861
theorem B1280435 : Blo 850355 1280435 := bstep (se 1 (by rfl) ⟨960326, by rfl⟩ : syracuseStep 1280435 = 1920653) B1920653
theorem B1280465 : Blo 850355 1280465 := bstep (se 2 (by rfl) ⟨480174, by rfl⟩ : syracuseStep 1280465 = 960349) B960349
theorem B1214947 : Blo 850355 1214947 := bstep (se 1 (by rfl) ⟨911210, by rfl⟩ : syracuseStep 1214947 = 1822421) B1822421
theorem B1280483 : Blo 850355 1280483 := bstep (se 1 (by rfl) ⟨960362, by rfl⟩ : syracuseStep 1280483 = 1920725) B1920725
theorem B1280513 : Blo 850355 1280513 := bstep (se 2 (by rfl) ⟨480192, by rfl⟩ : syracuseStep 1280513 = 960385) B960385
theorem B1280531 : Blo 850355 1280531 := bstep (se 1 (by rfl) ⟨960398, by rfl⟩ : syracuseStep 1280531 = 1920797) B1920797
theorem B2918947 : Blo 850355 2918947 := bstep (se 1 (by rfl) ⟨2189210, by rfl⟩ : syracuseStep 2918947 = 4378421) B4378421
theorem B1280561 : Blo 850355 1280561 := bstep (se 2 (by rfl) ⟨480210, by rfl⟩ : syracuseStep 1280561 = 960421) B960421
theorem B1280579 : Blo 850355 1280579 := bstep (se 1 (by rfl) ⟨960434, by rfl⟩ : syracuseStep 1280579 = 1920869) B1920869
theorem B1280609 : Blo 850355 1280609 := bstep (se 2 (by rfl) ⟨480228, by rfl⟩ : syracuseStep 1280609 = 960457) B960457
theorem B1149553 : Blo 850355 1149553 := bstep (se 2 (by rfl) ⟨431082, by rfl⟩ : syracuseStep 1149553 = 862165) B862165
theorem B1280627 : Blo 850355 1280627 := bstep (se 1 (by rfl) ⟨960470, by rfl⟩ : syracuseStep 1280627 = 1920941) B1920941
theorem B1280657 : Blo 850355 1280657 := bstep (se 2 (by rfl) ⟨480246, by rfl⟩ : syracuseStep 1280657 = 960493) B960493
theorem B1280675 : Blo 850355 1280675 := bstep (se 1 (by rfl) ⟨960506, by rfl⟩ : syracuseStep 1280675 = 1921013) B1921013
theorem B1280705 : Blo 850355 1280705 := bstep (se 2 (by rfl) ⟨480264, by rfl⟩ : syracuseStep 1280705 = 960529) B960529
theorem B1280723 : Blo 850355 1280723 := bstep (se 1 (by rfl) ⟨960542, by rfl⟩ : syracuseStep 1280723 = 1921085) B1921085
theorem B1280753 : Blo 850355 1280753 := bstep (se 2 (by rfl) ⟨480282, by rfl⟩ : syracuseStep 1280753 = 960565) B960565
theorem B1280771 : Blo 850355 1280771 := bstep (se 1 (by rfl) ⟨960578, by rfl⟩ : syracuseStep 1280771 = 1921157) B1921157
theorem B2427661 : Blo 850355 2427661 := bstep (se 3 (by rfl) ⟨455186, by rfl⟩ : syracuseStep 2427661 = 910373) B910373
theorem B1280801 : Blo 850355 1280801 := bstep (se 2 (by rfl) ⟨480300, by rfl⟩ : syracuseStep 1280801 = 960601) B960601
theorem B1280819 : Blo 850355 1280819 := bstep (se 1 (by rfl) ⟨960614, by rfl⟩ : syracuseStep 1280819 = 1921229) B1921229
theorem B1280849 : Blo 850355 1280849 := bstep (se 2 (by rfl) ⟨480318, by rfl⟩ : syracuseStep 1280849 = 960637) B960637
theorem B1280867 : Blo 850355 1280867 := bstep (se 1 (by rfl) ⟨960650, by rfl⟩ : syracuseStep 1280867 = 1921301) B1921301
theorem B1280897 : Blo 850355 1280897 := bstep (se 2 (by rfl) ⟨480336, by rfl⟩ : syracuseStep 1280897 = 960673) B960673
theorem B1280915 : Blo 850355 1280915 := bstep (se 1 (by rfl) ⟨960686, by rfl⟩ : syracuseStep 1280915 = 1921373) B1921373
theorem B1280945 : Blo 850355 1280945 := bstep (se 2 (by rfl) ⟨480354, by rfl⟩ : syracuseStep 1280945 = 960709) B960709
theorem B1280963 : Blo 850355 1280963 := bstep (se 1 (by rfl) ⟨960722, by rfl⟩ : syracuseStep 1280963 = 1921445) B1921445
theorem B1280993 : Blo 850355 1280993 := bstep (se 2 (by rfl) ⟨480372, by rfl⟩ : syracuseStep 1280993 = 960745) B960745
theorem B2427889 : Blo 850355 2427889 := bstep (se 2 (by rfl) ⟨910458, by rfl⟩ : syracuseStep 2427889 = 1820917) B1820917
theorem B1281011 : Blo 850355 1281011 := bstep (se 1 (by rfl) ⟨960758, by rfl⟩ : syracuseStep 1281011 = 1921517) B1921517
theorem B1281041 : Blo 850355 1281041 := bstep (se 2 (by rfl) ⟨480390, by rfl⟩ : syracuseStep 1281041 = 960781) B960781
theorem B1281059 : Blo 850355 1281059 := bstep (se 1 (by rfl) ⟨960794, by rfl⟩ : syracuseStep 1281059 = 1921589) B1921589
theorem B1281089 : Blo 850355 1281089 := bstep (se 2 (by rfl) ⟨480408, by rfl⟩ : syracuseStep 1281089 = 960817) B960817
theorem B1281107 : Blo 850355 1281107 := bstep (se 1 (by rfl) ⟨960830, by rfl⟩ : syracuseStep 1281107 = 1921661) B1921661
theorem B1150051 : Blo 850355 1150051 := bstep (se 1 (by rfl) ⟨862538, by rfl⟩ : syracuseStep 1150051 = 1725077) B1725077
theorem B1281137 : Blo 850355 1281137 := bstep (se 2 (by rfl) ⟨480426, by rfl⟩ : syracuseStep 1281137 = 960853) B960853
theorem B1281155 : Blo 850355 1281155 := bstep (se 1 (by rfl) ⟨960866, by rfl⟩ : syracuseStep 1281155 = 1921733) B1921733
theorem B2428049 : Blo 850355 2428049 := bstep (se 2 (by rfl) ⟨910518, by rfl⟩ : syracuseStep 2428049 = 1821037) B1821037
theorem B1281185 : Blo 850355 1281185 := bstep (se 2 (by rfl) ⟨480444, by rfl⟩ : syracuseStep 1281185 = 960889) B960889
theorem B1281203 : Blo 850355 1281203 := bstep (se 1 (by rfl) ⟨960902, by rfl⟩ : syracuseStep 1281203 = 1921805) B1921805
theorem B1281233 : Blo 850355 1281233 := bstep (se 2 (by rfl) ⟨480462, by rfl⟩ : syracuseStep 1281233 = 960925) B960925
theorem B1281251 : Blo 850355 1281251 := bstep (se 1 (by rfl) ⟨960938, by rfl⟩ : syracuseStep 1281251 = 1921877) B1921877
theorem B1281281 : Blo 850355 1281281 := bstep (se 2 (by rfl) ⟨480480, by rfl⟩ : syracuseStep 1281281 = 960961) B960961
theorem B2428163 : Blo 850355 2428163 := bstep (se 1 (by rfl) ⟨1821122, by rfl⟩ : syracuseStep 2428163 = 3642245) B3642245
theorem B1281299 : Blo 850355 1281299 := bstep (se 1 (by rfl) ⟨960974, by rfl⟩ : syracuseStep 1281299 = 1921949) B1921949
theorem B1281329 : Blo 850355 1281329 := bstep (se 2 (by rfl) ⟨480498, by rfl⟩ : syracuseStep 1281329 = 960997) B960997
theorem B1281347 : Blo 850355 1281347 := bstep (se 1 (by rfl) ⟨961010, by rfl⟩ : syracuseStep 1281347 = 1922021) B1922021
theorem B1281377 : Blo 850355 1281377 := bstep (se 2 (by rfl) ⟨480516, by rfl⟩ : syracuseStep 1281377 = 961033) B961033
theorem B1281395 : Blo 850355 1281395 := bstep (se 1 (by rfl) ⟨961046, by rfl⟩ : syracuseStep 1281395 = 1922093) B1922093
theorem B1281425 : Blo 850355 1281425 := bstep (se 2 (by rfl) ⟨480534, by rfl⟩ : syracuseStep 1281425 = 961069) B961069
theorem B1281443 : Blo 850355 1281443 := bstep (se 1 (by rfl) ⟨961082, by rfl⟩ : syracuseStep 1281443 = 1922165) B1922165
theorem B1281473 : Blo 850355 1281473 := bstep (se 2 (by rfl) ⟨480552, by rfl⟩ : syracuseStep 1281473 = 961105) B961105
theorem B1281491 : Blo 850355 1281491 := bstep (se 1 (by rfl) ⟨961118, by rfl⟩ : syracuseStep 1281491 = 1922237) B1922237
theorem B1281521 : Blo 850355 1281521 := bstep (se 2 (by rfl) ⟨480570, by rfl⟩ : syracuseStep 1281521 = 961141) B961141
theorem B4853317 : Blo 850355 4853317 := bstep (se 4 (by rfl) ⟨454998, by rfl⟩ : syracuseStep 4853317 = 909997) B909997
theorem B3640945 : Blo 850355 3640945 := bstep (se 2 (by rfl) ⟨1365354, by rfl⟩ : syracuseStep 3640945 = 2730709) B2730709
theorem B1216291 : Blo 850355 1216291 := bstep (se 1 (by rfl) ⟨912218, by rfl⟩ : syracuseStep 1216291 = 1824437) B1824437
theorem B6230029 : Blo 850355 6230029 := bstep (se 3 (by rfl) ⟨1168130, by rfl⟩ : syracuseStep 6230029 = 2336261) B2336261
theorem B2429165 : Blo 850355 2429165 := bstep (se 3 (by rfl) ⟨455468, by rfl⟩ : syracuseStep 2429165 = 910937) B910937
theorem B2429347 : Blo 850355 2429347 := bstep (se 1 (by rfl) ⟨1822010, by rfl⟩ : syracuseStep 2429347 = 3644021) B3644021
theorem B2429507 : Blo 850355 2429507 := bstep (se 1 (by rfl) ⟨1822130, by rfl⟩ : syracuseStep 2429507 = 3644261) B3644261
theorem B10359409 : Blo 850355 10359409 := bstep (se 2 (by rfl) ⟨3884778, by rfl⟩ : syracuseStep 10359409 = 7769557) B7769557
theorem B16814789 : Blo 850355 16814789 := bstep (se 4 (by rfl) ⟨1576386, by rfl⟩ : syracuseStep 16814789 = 3152773) B3152773
theorem B7279429 : Blo 850355 7279429 := bstep (se 4 (by rfl) ⟨682446, by rfl⟩ : syracuseStep 7279429 = 1364893) B1364893
theorem B2724995 : Blo 850355 2724995 := bstep (se 1 (by rfl) ⟨2043746, by rfl⟩ : syracuseStep 2724995 = 4087493) B4087493
theorem B2299043 : Blo 850355 2299043 := bstep (se 1 (by rfl) ⟨1724282, by rfl⟩ : syracuseStep 2299043 = 3448565) B3448565
theorem B2593987 : Blo 850355 2593987 := bstep (se 1 (by rfl) ⟨1945490, by rfl⟩ : syracuseStep 2593987 = 3890981) B3890981
theorem B2725123 : Blo 850355 2725123 := bstep (se 1 (by rfl) ⟨2043842, by rfl⟩ : syracuseStep 2725123 = 4087685) B4087685
theorem B2725265 : Blo 850355 2725265 := bstep (se 2 (by rfl) ⟨1021974, by rfl⟩ : syracuseStep 2725265 = 2043949) B2043949
theorem B3282403 : Blo 850355 3282403 := bstep (se 1 (by rfl) ⟨2461802, by rfl⟩ : syracuseStep 3282403 = 4923605) B4923605
theorem B2725379 : Blo 850355 2725379 := bstep (se 1 (by rfl) ⟨2044034, by rfl⟩ : syracuseStep 2725379 = 4088069) B4088069
theorem B2921987 : Blo 850355 2921987 := bstep (se 1 (by rfl) ⟨2191490, by rfl⟩ : syracuseStep 2921987 = 4382981) B4382981
theorem B4855301 : Blo 850355 4855301 := bstep (se 4 (by rfl) ⟨455184, by rfl⟩ : syracuseStep 4855301 = 910369) B910369
theorem B2299409 : Blo 850355 2299409 := bstep (se 2 (by rfl) ⟨862278, by rfl⟩ : syracuseStep 2299409 = 1724557) B1724557
theorem B2430577 : Blo 850355 2430577 := bstep (se 2 (by rfl) ⟨911466, by rfl⟩ : syracuseStep 2430577 = 1822933) B1822933
theorem B5183281 : Blo 850355 5183281 := bstep (se 2 (by rfl) ⟨1943730, by rfl⟩ : syracuseStep 5183281 = 3887461) B3887461
theorem B3282893 : Blo 850355 3282893 := bstep (se 3 (by rfl) ⟨615542, by rfl⟩ : syracuseStep 3282893 = 1231085) B1231085
theorem B8198243 : Blo 850355 8198243 := bstep (se 1 (by rfl) ⟨6148682, by rfl⟩ : syracuseStep 8198243 = 12297365) B12297365
theorem B1841329 : Blo 850355 1841329 := bstep (se 2 (by rfl) ⟨690498, by rfl⟩ : syracuseStep 1841329 = 1380997) B1380997
theorem B956659 : Blo 850355 956659 := bstep (se 1 (by rfl) ⟨717494, by rfl⟩ : syracuseStep 956659 = 1434989) B1434989
theorem B956803 : Blo 850355 956803 := bstep (se 1 (by rfl) ⟨717602, by rfl⟩ : syracuseStep 956803 = 1435205) B1435205
theorem B1153489 : Blo 850355 1153489 := bstep (se 2 (by rfl) ⟨432558, by rfl⟩ : syracuseStep 1153489 = 865117) B865117
theorem B956947 : Blo 850355 956947 := bstep (se 1 (by rfl) ⟨717710, by rfl⟩ : syracuseStep 956947 = 1435421) B1435421
theorem B2595377 : Blo 850355 2595377 := bstep (se 2 (by rfl) ⟨973266, by rfl⟩ : syracuseStep 2595377 = 1946533) B1946533
theorem B957091 : Blo 850355 957091 := bstep (se 1 (by rfl) ⟨717818, by rfl⟩ : syracuseStep 957091 = 1435637) B1435637
theorem B957235 : Blo 850355 957235 := bstep (se 1 (by rfl) ⟨717926, by rfl⟩ : syracuseStep 957235 = 1435853) B1435853
theorem B2431853 : Blo 850355 2431853 := bstep (se 3 (by rfl) ⟨455972, by rfl⟩ : syracuseStep 2431853 = 911945) B911945
theorem B957379 : Blo 850355 957379 := bstep (se 1 (by rfl) ⟨718034, by rfl⟩ : syracuseStep 957379 = 1436069) B1436069
theorem B2432035 : Blo 850355 2432035 := bstep (se 1 (by rfl) ⟨1824026, by rfl⟩ : syracuseStep 2432035 = 3648053) B3648053
theorem B2432081 : Blo 850355 2432081 := bstep (se 2 (by rfl) ⟨912030, by rfl⟩ : syracuseStep 2432081 = 1824061) B1824061
theorem B957523 : Blo 850355 957523 := bstep (se 1 (by rfl) ⟨718142, by rfl⟩ : syracuseStep 957523 = 1436285) B1436285
theorem B3644621 : Blo 850355 3644621 := bstep (se 3 (by rfl) ⟨683366, by rfl⟩ : syracuseStep 3644621 = 1366733) B1366733
theorem B2727121 : Blo 850355 2727121 := bstep (se 2 (by rfl) ⟨1022670, by rfl⟩ : syracuseStep 2727121 = 2045341) B2045341
theorem B957667 : Blo 850355 957667 := bstep (se 1 (by rfl) ⟨718250, by rfl⟩ : syracuseStep 957667 = 1436501) B1436501
theorem B5250275 : Blo 850355 5250275 := bstep (se 1 (by rfl) ⟨3937706, by rfl⟩ : syracuseStep 5250275 = 7875413) B7875413
theorem B2497873 : Blo 850355 2497873 := bstep (se 2 (by rfl) ⟨936702, by rfl⟩ : syracuseStep 2497873 = 1873405) B1873405
theorem B957811 : Blo 850355 957811 := bstep (se 1 (by rfl) ⟨718358, by rfl⟩ : syracuseStep 957811 = 1436717) B1436717
theorem B1383841 : Blo 850355 1383841 := bstep (se 2 (by rfl) ⟨518940, by rfl⟩ : syracuseStep 1383841 = 1037881) B1037881
theorem B2301443 : Blo 850355 2301443 := bstep (se 1 (by rfl) ⟨1726082, by rfl⟩ : syracuseStep 2301443 = 3452165) B3452165
theorem B957955 : Blo 850355 957955 := bstep (se 1 (by rfl) ⟨718466, by rfl⟩ : syracuseStep 957955 = 1436933) B1436933
theorem B2072099 : Blo 850355 2072099 := bstep (se 1 (by rfl) ⟨1554074, by rfl⟩ : syracuseStep 2072099 = 3108149) B3108149
theorem B11214449 : Blo 850355 11214449 := bstep (se 2 (by rfl) ⟨4205418, by rfl⟩ : syracuseStep 11214449 = 8410837) B8410837
theorem B958099 : Blo 850355 958099 := bstep (se 1 (by rfl) ⟨718574, by rfl⟩ : syracuseStep 958099 = 1437149) B1437149
theorem B2334413 : Blo 850355 2334413 := bstep (se 3 (by rfl) ⟨437702, by rfl⟩ : syracuseStep 2334413 = 875405) B875405
theorem B958243 : Blo 850355 958243 := bstep (se 1 (by rfl) ⟨718682, by rfl⟩ : syracuseStep 958243 = 1437365) B1437365
theorem B9707363 : Blo 850355 9707363 := bstep (se 1 (by rfl) ⟨7280522, by rfl⟩ : syracuseStep 9707363 = 14561045) B14561045
theorem B958387 : Blo 850355 958387 := bstep (se 1 (by rfl) ⟨718790, by rfl⟩ : syracuseStep 958387 = 1437581) B1437581
theorem B958531 : Blo 850355 958531 := bstep (se 1 (by rfl) ⟨718898, by rfl⟩ : syracuseStep 958531 = 1437797) B1437797
theorem B958675 : Blo 850355 958675 := bstep (se 1 (by rfl) ⟨719006, by rfl⟩ : syracuseStep 958675 = 1438013) B1438013
theorem B23306467 : Blo 850355 23306467 := bstep (se 1 (by rfl) ⟨17479850, by rfl⟩ : syracuseStep 23306467 = 34959701) B34959701
theorem B2728237 : Blo 850355 2728237 := bstep (se 3 (by rfl) ⟨511544, by rfl⟩ : syracuseStep 2728237 = 1023089) B1023089
theorem B958819 : Blo 850355 958819 := bstep (se 1 (by rfl) ⟨719114, by rfl⟩ : syracuseStep 958819 = 1438229) B1438229
theorem B1024435 : Blo 850355 1024435 := bstep (se 1 (by rfl) ⟨768326, by rfl⟩ : syracuseStep 1024435 = 1536653) B1536653
theorem B958963 : Blo 850355 958963 := bstep (se 1 (by rfl) ⟨719222, by rfl⟩ : syracuseStep 958963 = 1438445) B1438445
theorem B2597393 : Blo 850355 2597393 := bstep (se 2 (by rfl) ⟨974022, by rfl⟩ : syracuseStep 2597393 = 1948045) B1948045
theorem B959107 : Blo 850355 959107 := bstep (se 1 (by rfl) ⟨719330, by rfl⟩ : syracuseStep 959107 = 1438661) B1438661
theorem B959251 : Blo 850355 959251 := bstep (se 1 (by rfl) ⟨719438, by rfl⟩ : syracuseStep 959251 = 1438877) B1438877
theorem B1778563 : Blo 850355 1778563 := bstep (se 1 (by rfl) ⟨1333922, by rfl⟩ : syracuseStep 1778563 = 2667845) B2667845
theorem B959395 : Blo 850355 959395 := bstep (se 1 (by rfl) ⟨719546, by rfl⟩ : syracuseStep 959395 = 1439093) B1439093
theorem B959539 : Blo 850355 959539 := bstep (se 1 (by rfl) ⟨719654, by rfl⟩ : syracuseStep 959539 = 1439309) B1439309
theorem B3941453 : Blo 850355 3941453 := bstep (se 3 (by rfl) ⟨739022, by rfl⟩ : syracuseStep 3941453 = 1478045) B1478045
theorem B2729069 : Blo 850355 2729069 := bstep (se 3 (by rfl) ⟨511700, by rfl⟩ : syracuseStep 2729069 = 1023401) B1023401
theorem B17507441 : Blo 850355 17507441 := bstep (se 2 (by rfl) ⟨6565290, by rfl⟩ : syracuseStep 17507441 = 13130581) B13130581
theorem B959683 : Blo 850355 959683 := bstep (se 1 (by rfl) ⟨719762, by rfl⟩ : syracuseStep 959683 = 1439525) B1439525
theorem B5907725 : Blo 850355 5907725 := bstep (se 3 (by rfl) ⟨1107698, by rfl⟩ : syracuseStep 5907725 = 2215397) B2215397
theorem B4859149 : Blo 850355 4859149 := bstep (se 3 (by rfl) ⟨911090, by rfl⟩ : syracuseStep 4859149 = 1822181) B1822181
theorem B1615153 : Blo 850355 1615153 := bstep (se 2 (by rfl) ⟨605682, by rfl⟩ : syracuseStep 1615153 = 1211365) B1211365
theorem B959827 : Blo 850355 959827 := bstep (se 1 (by rfl) ⟨719870, by rfl⟩ : syracuseStep 959827 = 1439741) B1439741
theorem B959971 : Blo 850355 959971 := bstep (se 1 (by rfl) ⟨719978, by rfl⟩ : syracuseStep 959971 = 1439957) B1439957
theorem B2958925 : Blo 850355 2958925 := bstep (se 3 (by rfl) ⟨554798, by rfl⟩ : syracuseStep 2958925 = 1109597) B1109597
theorem B960115 : Blo 850355 960115 := bstep (se 1 (by rfl) ⟨720086, by rfl⟩ : syracuseStep 960115 = 1440173) B1440173
theorem B2762381 : Blo 850355 2762381 := bstep (se 3 (by rfl) ⟨517946, by rfl⟩ : syracuseStep 2762381 = 1035893) B1035893
theorem B1615555 : Blo 850355 1615555 := bstep (se 1 (by rfl) ⟨1211666, by rfl⟩ : syracuseStep 1615555 = 2423333) B2423333
theorem B2074339 : Blo 850355 2074339 := bstep (se 1 (by rfl) ⟨1555754, by rfl⟩ : syracuseStep 2074339 = 3111509) B3111509
theorem B1615601 : Blo 850355 1615601 := bstep (se 2 (by rfl) ⟨605850, by rfl⟩ : syracuseStep 1615601 = 1211701) B1211701
theorem B8201969 : Blo 850355 8201969 := bstep (se 2 (by rfl) ⟨3075738, by rfl⟩ : syracuseStep 8201969 = 6151477) B6151477
theorem B960259 : Blo 850355 960259 := bstep (se 1 (by rfl) ⟨720194, by rfl⟩ : syracuseStep 960259 = 1440389) B1440389
theorem B862003 : Blo 850355 862003 := bstep (se 1 (by rfl) ⟨646502, by rfl⟩ : syracuseStep 862003 = 1293005) B1293005
theorem B960403 : Blo 850355 960403 := bstep (se 1 (by rfl) ⟨720302, by rfl⟩ : syracuseStep 960403 = 1440605) B1440605
theorem B2762669 : Blo 850355 2762669 := bstep (se 3 (by rfl) ⟨518000, by rfl⟩ : syracuseStep 2762669 = 1036001) B1036001
theorem B1615889 : Blo 850355 1615889 := bstep (se 2 (by rfl) ⟨605958, by rfl⟩ : syracuseStep 1615889 = 1211917) B1211917
theorem B960547 : Blo 850355 960547 := bstep (se 1 (by rfl) ⟨720410, by rfl⟩ : syracuseStep 960547 = 1440821) B1440821
theorem B960691 : Blo 850355 960691 := bstep (se 1 (by rfl) ⟨720518, by rfl⟩ : syracuseStep 960691 = 1441037) B1441037
theorem B1026227 : Blo 850355 1026227 := bstep (se 1 (by rfl) ⟨769670, by rfl⟩ : syracuseStep 1026227 = 1539341) B1539341
theorem B3287267 : Blo 850355 3287267 := bstep (se 1 (by rfl) ⟨2465450, by rfl⟩ : syracuseStep 3287267 = 4930901) B4930901
theorem B960835 : Blo 850355 960835 := bstep (se 1 (by rfl) ⟨720626, by rfl⟩ : syracuseStep 960835 = 1441253) B1441253
theorem B960979 : Blo 850355 960979 := bstep (se 1 (by rfl) ⟨720734, by rfl⟩ : syracuseStep 960979 = 1441469) B1441469
theorem B961123 : Blo 850355 961123 := bstep (se 1 (by rfl) ⟨720842, by rfl⟩ : syracuseStep 961123 = 1441685) B1441685
theorem B1616611 : Blo 850355 1616611 := bstep (se 1 (by rfl) ⟨1212458, by rfl⟩ : syracuseStep 1616611 = 2424917) B2424917
theorem B6237253 : Blo 850355 6237253 := bstep (se 4 (by rfl) ⟨584742, by rfl⟩ : syracuseStep 6237253 = 1169485) B1169485
theorem B1617059 : Blo 850355 1617059 := bstep (se 1 (by rfl) ⟨1212794, by rfl⟩ : syracuseStep 1617059 = 2425589) B2425589
theorem B2731171 : Blo 850355 2731171 := bstep (se 1 (by rfl) ⟨2048378, by rfl⟩ : syracuseStep 2731171 = 4096757) B4096757
theorem B4861133 : Blo 850355 4861133 := bstep (se 3 (by rfl) ⟨911462, by rfl⟩ : syracuseStep 4861133 = 1822925) B1822925
theorem B2731313 : Blo 850355 2731313 := bstep (se 2 (by rfl) ⟨1024242, by rfl⟩ : syracuseStep 2731313 = 2048485) B2048485
theorem B1617347 : Blo 850355 1617347 := bstep (se 1 (by rfl) ⟨1213010, by rfl⟩ : syracuseStep 1617347 = 2426021) B2426021
theorem B3648995 : Blo 850355 3648995 := bstep (se 1 (by rfl) ⟨2736746, by rfl⟩ : syracuseStep 3648995 = 5473493) B5473493
theorem B6926093 : Blo 850355 6926093 := bstep (se 3 (by rfl) ⟨1298642, by rfl⟩ : syracuseStep 6926093 = 2597285) B2597285
theorem B5451781 : Blo 850355 5451781 := bstep (se 4 (by rfl) ⟨511104, by rfl⟩ : syracuseStep 5451781 = 1022209) B1022209
theorem B4862065 : Blo 850355 4862065 := bstep (se 2 (by rfl) ⟨1823274, by rfl⟩ : syracuseStep 4862065 = 3646549) B3646549
theorem B8204429 : Blo 850355 8204429 := bstep (se 3 (by rfl) ⟨1538330, by rfl⟩ : syracuseStep 8204429 = 3076661) B3076661
theorem B1618289 : Blo 850355 1618289 := bstep (se 2 (by rfl) ⟨606858, by rfl⟩ : syracuseStep 1618289 = 1213717) B1213717
theorem B1454657 : Blo 850355 1454657 := bstep (se 2 (by rfl) ⟨545496, by rfl⟩ : syracuseStep 1454657 = 1090993) B1090993
theorem B1913489 : Blo 850355 1913489 := bstep (se 2 (by rfl) ⟨717558, by rfl⟩ : syracuseStep 1913489 = 1435117) B1435117
theorem B1913507 : Blo 850355 1913507 := bstep (se 1 (by rfl) ⟨1435130, by rfl⟩ : syracuseStep 1913507 = 2870261) B2870261
theorem B4305635 : Blo 850355 4305635 := bstep (se 1 (by rfl) ⟨3229226, by rfl⟩ : syracuseStep 4305635 = 6458453) B6458453
theorem B1913777 : Blo 850355 1913777 := bstep (se 2 (by rfl) ⟨717666, by rfl⟩ : syracuseStep 1913777 = 1435333) B1435333
theorem B1913795 : Blo 850355 1913795 := bstep (se 1 (by rfl) ⟨1435346, by rfl⟩ : syracuseStep 1913795 = 2870693) B2870693
theorem B1848515 : Blo 850355 1848515 := bstep (se 1 (by rfl) ⟨1386386, by rfl⟩ : syracuseStep 1848515 = 2772773) B2772773
theorem B1914065 : Blo 850355 1914065 := bstep (se 2 (by rfl) ⟨717774, by rfl⟩ : syracuseStep 1914065 = 1435549) B1435549
theorem B1914083 : Blo 850355 1914083 := bstep (se 1 (by rfl) ⟨1435562, by rfl⟩ : syracuseStep 1914083 = 2871125) B2871125
theorem B1619185 : Blo 850355 1619185 := bstep (se 2 (by rfl) ⟨607194, by rfl⟩ : syracuseStep 1619185 = 1214389) B1214389
theorem B865571 : Blo 850355 865571 := bstep (se 1 (by rfl) ⟨649178, by rfl⟩ : syracuseStep 865571 = 1298357) B1298357
theorem B2307409 : Blo 850355 2307409 := bstep (se 2 (by rfl) ⟨865278, by rfl⟩ : syracuseStep 2307409 = 1730557) B1730557
theorem B7288177 : Blo 850355 7288177 := bstep (se 2 (by rfl) ⟨2733066, by rfl⟩ : syracuseStep 7288177 = 5466133) B5466133
theorem B1619345 : Blo 850355 1619345 := bstep (se 2 (by rfl) ⟨607254, by rfl⟩ : syracuseStep 1619345 = 1214509) B1214509
theorem B1914353 : Blo 850355 1914353 := bstep (se 2 (by rfl) ⟨717882, by rfl⟩ : syracuseStep 1914353 = 1435765) B1435765
theorem B1914371 : Blo 850355 1914371 := bstep (se 1 (by rfl) ⟨1435778, by rfl⟩ : syracuseStep 1914371 = 2871557) B2871557
theorem B4306445 : Blo 850355 4306445 := bstep (se 3 (by rfl) ⟨807458, by rfl⟩ : syracuseStep 4306445 = 1614917) B1614917
theorem B4863523 : Blo 850355 4863523 := bstep (se 1 (by rfl) ⟨3647642, by rfl⟩ : syracuseStep 4863523 = 7295285) B7295285
theorem B1095283 : Blo 850355 1095283 := bstep (se 1 (by rfl) ⟨821462, by rfl⟩ : syracuseStep 1095283 = 1642925) B1642925
theorem B2733709 : Blo 850355 2733709 := bstep (se 3 (by rfl) ⟨512570, by rfl⟩ : syracuseStep 2733709 = 1025141) B1025141
theorem B1455779 : Blo 850355 1455779 := bstep (se 1 (by rfl) ⟨1091834, by rfl⟩ : syracuseStep 1455779 = 2183669) B2183669
theorem B4601585 : Blo 850355 4601585 := bstep (se 2 (by rfl) ⟨1725594, by rfl⟩ : syracuseStep 4601585 = 3451189) B3451189
theorem B1914641 : Blo 850355 1914641 := bstep (se 2 (by rfl) ⟨717990, by rfl⟩ : syracuseStep 1914641 = 1435981) B1435981
theorem B1455889 : Blo 850355 1455889 := bstep (se 2 (by rfl) ⟨545958, by rfl⟩ : syracuseStep 1455889 = 1091917) B1091917
theorem B1914659 : Blo 850355 1914659 := bstep (se 1 (by rfl) ⟨1435994, by rfl⟩ : syracuseStep 1914659 = 2871989) B2871989
theorem B1619747 : Blo 850355 1619747 := bstep (se 1 (by rfl) ⟨1214810, by rfl⟩ : syracuseStep 1619747 = 2429621) B2429621
theorem B2307953 : Blo 850355 2307953 := bstep (se 2 (by rfl) ⟨865482, by rfl⟩ : syracuseStep 2307953 = 1730965) B1730965
theorem B14596037 : Blo 850355 14596037 := bstep (se 4 (by rfl) ⟨1368378, by rfl⟩ : syracuseStep 14596037 = 2736757) B2736757
theorem B3880909 : Blo 850355 3880909 := bstep (se 3 (by rfl) ⟨727670, by rfl⟩ : syracuseStep 3880909 = 1455341) B1455341
theorem B1914929 : Blo 850355 1914929 := bstep (se 2 (by rfl) ⟨718098, by rfl⟩ : syracuseStep 1914929 = 1436197) B1436197
theorem B4864049 : Blo 850355 4864049 := bstep (se 2 (by rfl) ⟨1824018, by rfl⟩ : syracuseStep 4864049 = 3648037) B3648037
theorem B1914947 : Blo 850355 1914947 := bstep (se 1 (by rfl) ⟨1436210, by rfl⟩ : syracuseStep 1914947 = 2872421) B2872421
theorem B1915217 : Blo 850355 1915217 := bstep (se 2 (by rfl) ⟨718206, by rfl⟩ : syracuseStep 1915217 = 1436413) B1436413
theorem B1915235 : Blo 850355 1915235 := bstep (se 1 (by rfl) ⟨1436426, by rfl⟩ : syracuseStep 1915235 = 2872853) B2872853
theorem B1423955 : Blo 850355 1423955 := bstep (se 1 (by rfl) ⟨1067966, by rfl⟩ : syracuseStep 1423955 = 2135933) B2135933
theorem B1915505 : Blo 850355 1915505 := bstep (se 2 (by rfl) ⟨718314, by rfl⟩ : syracuseStep 1915505 = 1436629) B1436629
theorem B1915523 : Blo 850355 1915523 := bstep (se 1 (by rfl) ⟨1436642, by rfl⟩ : syracuseStep 1915523 = 2873285) B2873285
theorem B16628365 : Blo 850355 16628365 := bstep (se 3 (by rfl) ⟨3117818, by rfl⟩ : syracuseStep 16628365 = 6235637) B6235637
theorem B5454499 : Blo 850355 5454499 := bstep (se 1 (by rfl) ⟨4090874, by rfl⟩ : syracuseStep 5454499 = 8181749) B8181749
theorem B1620643 : Blo 850355 1620643 := bstep (se 1 (by rfl) ⟨1215482, by rfl⟩ : syracuseStep 1620643 = 2430965) B2430965
theorem B1817329 : Blo 850355 1817329 := bstep (se 2 (by rfl) ⟨681498, by rfl⟩ : syracuseStep 1817329 = 1362997) B1362997
theorem B1620803 : Blo 850355 1620803 := bstep (se 1 (by rfl) ⟨1215602, by rfl⟩ : syracuseStep 1620803 = 2431205) B2431205
theorem B1686353 : Blo 850355 1686353 := bstep (se 2 (by rfl) ⟨632382, by rfl⟩ : syracuseStep 1686353 = 1264765) B1264765
theorem B1915793 : Blo 850355 1915793 := bstep (se 2 (by rfl) ⟨718422, by rfl⟩ : syracuseStep 1915793 = 1436845) B1436845
theorem B1555345 : Blo 850355 1555345 := bstep (se 2 (by rfl) ⟨583254, by rfl⟩ : syracuseStep 1555345 = 1166509) B1166509
theorem B1915811 : Blo 850355 1915811 := bstep (se 1 (by rfl) ⟨1436858, by rfl⟩ : syracuseStep 1915811 = 2873717) B2873717
theorem B3881969 : Blo 850355 3881969 := bstep (se 2 (by rfl) ⟨1455738, by rfl⟩ : syracuseStep 3881969 = 2911477) B2911477
theorem B2047025 : Blo 850355 2047025 := bstep (se 2 (by rfl) ⟨767634, by rfl⟩ : syracuseStep 2047025 = 1535269) B1535269
theorem B1457203 : Blo 850355 1457203 := bstep (se 1 (by rfl) ⟨1092902, by rfl⟩ : syracuseStep 1457203 = 2185805) B2185805
theorem B1817731 : Blo 850355 1817731 := bstep (se 1 (by rfl) ⟨1363298, by rfl⟩ : syracuseStep 1817731 = 2726597) B2726597
theorem B1916081 : Blo 850355 1916081 := bstep (se 2 (by rfl) ⟨718530, by rfl⟩ : syracuseStep 1916081 = 1437061) B1437061
theorem B1916099 : Blo 850355 1916099 := bstep (se 1 (by rfl) ⟨1437074, by rfl⟩ : syracuseStep 1916099 = 2874149) B2874149
theorem B10927345 : Blo 850355 10927345 := bstep (se 2 (by rfl) ⟨4097754, by rfl⟩ : syracuseStep 10927345 = 8195509) B8195509
theorem B2047409 : Blo 850355 2047409 := bstep (se 2 (by rfl) ⟨767778, by rfl⟩ : syracuseStep 2047409 = 1535557) B1535557
theorem B1916369 : Blo 850355 1916369 := bstep (se 2 (by rfl) ⟨718638, by rfl⟩ : syracuseStep 1916369 = 1437277) B1437277
theorem B1916387 : Blo 850355 1916387 := bstep (se 1 (by rfl) ⟨1437290, by rfl⟩ : syracuseStep 1916387 = 2874581) B2874581
theorem B4865507 : Blo 850355 4865507 := bstep (se 1 (by rfl) ⟨3649130, by rfl⟩ : syracuseStep 4865507 = 7298261) B7298261
theorem B1228291 : Blo 850355 1228291 := bstep (se 1 (by rfl) ⟨921218, by rfl⟩ : syracuseStep 1228291 = 1842437) B1842437
theorem B5193229 : Blo 850355 5193229 := bstep (se 3 (by rfl) ⟨973730, by rfl⟩ : syracuseStep 5193229 = 1947461) B1947461
theorem B1916657 : Blo 850355 1916657 := bstep (se 2 (by rfl) ⟨718746, by rfl⟩ : syracuseStep 1916657 = 1437493) B1437493
theorem B1916675 : Blo 850355 1916675 := bstep (se 1 (by rfl) ⟨1437506, by rfl⟩ : syracuseStep 1916675 = 2875013) B2875013
theorem B1621873 : Blo 850355 1621873 := bstep (se 2 (by rfl) ⟨608202, by rfl⟩ : syracuseStep 1621873 = 1216405) B1216405
theorem B1916945 : Blo 850355 1916945 := bstep (se 2 (by rfl) ⟨718854, by rfl⟩ : syracuseStep 1916945 = 1437709) B1437709
theorem B1916963 : Blo 850355 1916963 := bstep (se 1 (by rfl) ⟨1437722, by rfl⟩ : syracuseStep 1916963 = 2875445) B2875445
theorem B2769059 : Blo 850355 2769059 := bstep (se 1 (by rfl) ⟨2076794, by rfl⟩ : syracuseStep 2769059 = 4153589) B4153589
theorem B5193989 : Blo 850355 5193989 := bstep (se 4 (by rfl) ⟨486936, by rfl⟩ : syracuseStep 5193989 = 973873) B973873
theorem B1917233 : Blo 850355 1917233 := bstep (se 2 (by rfl) ⟨718962, by rfl⟩ : syracuseStep 1917233 = 1437925) B1437925
theorem B1917251 : Blo 850355 1917251 := bstep (se 1 (by rfl) ⟨1437938, by rfl⟩ : syracuseStep 1917251 = 2875877) B2875877
theorem B4309361 : Blo 850355 4309361 := bstep (se 2 (by rfl) ⟨1616010, by rfl⟩ : syracuseStep 4309361 = 3232021) B3232021
theorem B8176099 : Blo 850355 8176099 := bstep (se 1 (by rfl) ⟨6132074, by rfl⟩ : syracuseStep 8176099 = 12264149) B12264149
theorem B1917521 : Blo 850355 1917521 := bstep (se 2 (by rfl) ⟨719070, by rfl⟩ : syracuseStep 1917521 = 1438141) B1438141
theorem B1819235 : Blo 850355 1819235 := bstep (se 1 (by rfl) ⟨1364426, by rfl⟩ : syracuseStep 1819235 = 2728853) B2728853
theorem B1917539 : Blo 850355 1917539 := bstep (se 1 (by rfl) ⟨1438154, by rfl⟩ : syracuseStep 1917539 = 2876309) B2876309
theorem B5456497 : Blo 850355 5456497 := bstep (se 2 (by rfl) ⟨2046186, by rfl⟩ : syracuseStep 5456497 = 4092373) B4092373
theorem B6472547 : Blo 850355 6472547 := bstep (se 1 (by rfl) ⟨4854410, by rfl⟩ : syracuseStep 6472547 = 9708821) B9708821
theorem B1917809 : Blo 850355 1917809 := bstep (se 2 (by rfl) ⟨719178, by rfl⟩ : syracuseStep 1917809 = 1438357) B1438357
theorem B1917827 : Blo 850355 1917827 := bstep (se 1 (by rfl) ⟨1438370, by rfl⟩ : syracuseStep 1917827 = 2876741) B2876741
theorem B1918097 : Blo 850355 1918097 := bstep (se 2 (by rfl) ⟨719286, by rfl⟩ : syracuseStep 1918097 = 1438573) B1438573
theorem B1918115 : Blo 850355 1918115 := bstep (se 1 (by rfl) ⟨1438586, by rfl⟩ : syracuseStep 1918115 = 2877173) B2877173
theorem B9225485 : Blo 850355 9225485 := bstep (se 3 (by rfl) ⟨1729778, by rfl⟩ : syracuseStep 9225485 = 3459557) B3459557
theorem B3229091 : Blo 850355 3229091 := bstep (se 1 (by rfl) ⟨2421818, by rfl⟩ : syracuseStep 3229091 = 4843637) B4843637
theorem B3229105 : Blo 850355 3229105 := bstep (se 2 (by rfl) ⟨1210914, by rfl⟩ : syracuseStep 3229105 = 2421829) B2421829
theorem B1918385 : Blo 850355 1918385 := bstep (se 2 (by rfl) ⟨719394, by rfl⟩ : syracuseStep 1918385 = 1438789) B1438789
theorem B1918403 : Blo 850355 1918403 := bstep (se 1 (by rfl) ⟨1438802, by rfl⟩ : syracuseStep 1918403 = 2877605) B2877605
theorem B1230323 : Blo 850355 1230323 := bstep (se 1 (by rfl) ⟨922742, by rfl⟩ : syracuseStep 1230323 = 1845485) B1845485
theorem B1295875 : Blo 850355 1295875 := bstep (se 1 (by rfl) ⟨971906, by rfl⟩ : syracuseStep 1295875 = 1943813) B1943813
theorem B21874373 : Blo 850355 21874373 := bstep (se 4 (by rfl) ⟨2050722, by rfl⟩ : syracuseStep 21874373 = 4101445) B4101445
theorem B1918673 : Blo 850355 1918673 := bstep (se 2 (by rfl) ⟨719502, by rfl⟩ : syracuseStep 1918673 = 1439005) B1439005
theorem B1918691 : Blo 850355 1918691 := bstep (se 1 (by rfl) ⟨1439018, by rfl⟩ : syracuseStep 1918691 = 2878037) B2878037
theorem B4310819 : Blo 850355 4310819 := bstep (se 1 (by rfl) ⟨3233114, by rfl⟩ : syracuseStep 4310819 = 6466229) B6466229
theorem B1820465 : Blo 850355 1820465 := bstep (se 2 (by rfl) ⟨682674, by rfl⟩ : syracuseStep 1820465 = 1365349) B1365349
theorem B20760461 : Blo 850355 20760461 := bstep (se 3 (by rfl) ⟨3892586, by rfl⟩ : syracuseStep 20760461 = 7785173) B7785173
theorem B1918961 : Blo 850355 1918961 := bstep (se 2 (by rfl) ⟨719610, by rfl⟩ : syracuseStep 1918961 = 1439221) B1439221
theorem B1918979 : Blo 850355 1918979 := bstep (se 1 (by rfl) ⟨1439234, by rfl⟩ : syracuseStep 1918979 = 2878469) B2878469
theorem B2050051 : Blo 850355 2050051 := bstep (se 1 (by rfl) ⟨1537538, by rfl⟩ : syracuseStep 2050051 = 3075077) B3075077
theorem B4606085 : Blo 850355 4606085 := bstep (se 4 (by rfl) ⟨431820, by rfl⟩ : syracuseStep 4606085 = 863641) B863641
theorem B1919249 : Blo 850355 1919249 := bstep (se 2 (by rfl) ⟨719718, by rfl⟩ : syracuseStep 1919249 = 1439437) B1439437
theorem B1919267 : Blo 850355 1919267 := bstep (se 1 (by rfl) ⟨1439450, by rfl⟩ : syracuseStep 1919267 = 2878901) B2878901
theorem B1362305 : Blo 850355 1362305 := bstep (se 2 (by rfl) ⟨510864, by rfl⟩ : syracuseStep 1362305 = 1021729) B1021729
theorem B1919537 : Blo 850355 1919537 := bstep (se 2 (by rfl) ⟨719826, by rfl⟩ : syracuseStep 1919537 = 1439653) B1439653
theorem B2050609 : Blo 850355 2050609 := bstep (se 2 (by rfl) ⟨768978, by rfl⟩ : syracuseStep 2050609 = 1537957) B1537957
theorem B1919555 : Blo 850355 1919555 := bstep (se 1 (by rfl) ⟨1439666, by rfl⟩ : syracuseStep 1919555 = 2879333) B2879333
theorem B7293509 : Blo 850355 7293509 := bstep (se 4 (by rfl) ⟨683766, by rfl⟩ : syracuseStep 7293509 = 1367533) B1367533
theorem B4311629 : Blo 850355 4311629 := bstep (se 3 (by rfl) ⟨808430, by rfl⟩ : syracuseStep 4311629 = 1616861) B1616861
theorem B1821361 : Blo 850355 1821361 := bstep (se 2 (by rfl) ⟨683010, by rfl⟩ : syracuseStep 1821361 = 1366021) B1366021
theorem B1821379 : Blo 850355 1821379 := bstep (se 1 (by rfl) ⟨1366034, by rfl⟩ : syracuseStep 1821379 = 2732069) B2732069
theorem B4606733 : Blo 850355 4606733 := bstep (se 3 (by rfl) ⟨863762, by rfl⟩ : syracuseStep 4606733 = 1727525) B1727525
theorem B1919825 : Blo 850355 1919825 := bstep (se 2 (by rfl) ⟨719934, by rfl⟩ : syracuseStep 1919825 = 1439869) B1439869
theorem B3230563 : Blo 850355 3230563 := bstep (se 1 (by rfl) ⟨2422922, by rfl⟩ : syracuseStep 3230563 = 4845845) B4845845
theorem B1919843 : Blo 850355 1919843 := bstep (se 1 (by rfl) ⟨1439882, by rfl⟩ : syracuseStep 1919843 = 2879765) B2879765
theorem B1363043 : Blo 850355 1363043 := bstep (se 1 (by rfl) ⟨1022282, by rfl⟩ : syracuseStep 1363043 = 2044565) B2044565
theorem B11095139 : Blo 850355 11095139 := bstep (se 1 (by rfl) ⟨8321354, by rfl⟩ : syracuseStep 11095139 = 16642709) B16642709
theorem B1920113 : Blo 850355 1920113 := bstep (se 2 (by rfl) ⟨720042, by rfl⟩ : syracuseStep 1920113 = 1440085) B1440085
theorem B1461377 : Blo 850355 1461377 := bstep (se 2 (by rfl) ⟨548016, by rfl⟩ : syracuseStep 1461377 = 1096033) B1096033
theorem B1920131 : Blo 850355 1920131 := bstep (se 1 (by rfl) ⟨1440098, by rfl⟩ : syracuseStep 1920131 = 2880197) B2880197
theorem B2870477 : Blo 850355 2870477 := bstep (se 3 (by rfl) ⟨538214, by rfl⟩ : syracuseStep 2870477 = 1076429) B1076429
theorem B2051281 : Blo 850355 2051281 := bstep (se 2 (by rfl) ⟨769230, by rfl⟩ : syracuseStep 2051281 = 1538461) B1538461
theorem B2870531 : Blo 850355 2870531 := bstep (se 1 (by rfl) ⟨2152898, by rfl⟩ : syracuseStep 2870531 = 4305797) B4305797
theorem B2805101 : Blo 850355 2805101 := bstep (se 3 (by rfl) ⟨525956, by rfl⟩ : syracuseStep 2805101 = 1051913) B1051913
theorem B1920401 : Blo 850355 1920401 := bstep (se 2 (by rfl) ⟨720150, by rfl⟩ : syracuseStep 1920401 = 1440301) B1440301
theorem B1920419 : Blo 850355 1920419 := bstep (se 1 (by rfl) ⟨1440314, by rfl⟩ : syracuseStep 1920419 = 2880629) B2880629
theorem B2870801 : Blo 850355 2870801 := bstep (se 2 (by rfl) ⟨1076550, by rfl⟩ : syracuseStep 2870801 = 2153101) B2153101
theorem B1920689 : Blo 850355 1920689 := bstep (se 2 (by rfl) ⟨720258, by rfl⟩ : syracuseStep 1920689 = 1440517) B1440517
theorem B1920707 : Blo 850355 1920707 := bstep (se 1 (by rfl) ⟨1440530, by rfl⟩ : syracuseStep 1920707 = 2881061) B2881061
theorem B1920977 : Blo 850355 1920977 := bstep (se 2 (by rfl) ⟨720366, by rfl⟩ : syracuseStep 1920977 = 1440733) B1440733
theorem B1724387 : Blo 850355 1724387 := bstep (se 1 (by rfl) ⟨1293290, by rfl⟩ : syracuseStep 1724387 = 2586581) B2586581
theorem B1920995 : Blo 850355 1920995 := bstep (se 1 (by rfl) ⟨1440746, by rfl⟩ : syracuseStep 1920995 = 2881493) B2881493
theorem B2871341 : Blo 850355 2871341 := bstep (se 3 (by rfl) ⟨538376, by rfl⟩ : syracuseStep 2871341 = 1076753) B1076753
theorem B1364035 : Blo 850355 1364035 := bstep (se 1 (by rfl) ⟨1023026, by rfl⟩ : syracuseStep 1364035 = 2046053) B2046053
theorem B2871395 : Blo 850355 2871395 := bstep (se 1 (by rfl) ⟨2153546, by rfl⟩ : syracuseStep 2871395 = 4307093) B4307093
theorem B8179825 : Blo 850355 8179825 := bstep (se 2 (by rfl) ⟨3067434, by rfl⟩ : syracuseStep 8179825 = 6134869) B6134869
theorem B1921265 : Blo 850355 1921265 := bstep (se 2 (by rfl) ⟨720474, by rfl⟩ : syracuseStep 1921265 = 1440949) B1440949
theorem B1921283 : Blo 850355 1921283 := bstep (se 1 (by rfl) ⟨1440962, by rfl⟩ : syracuseStep 1921283 = 2881925) B2881925
theorem B1364273 : Blo 850355 1364273 := bstep (se 2 (by rfl) ⟨511602, by rfl⟩ : syracuseStep 1364273 = 1023205) B1023205
theorem B2871665 : Blo 850355 2871665 := bstep (se 2 (by rfl) ⟨1076874, by rfl⟩ : syracuseStep 2871665 = 2153749) B2153749
theorem B10932677 : Blo 850355 10932677 := bstep (se 4 (by rfl) ⟨1024938, by rfl⟩ : syracuseStep 10932677 = 2049877) B2049877
theorem B1364483 : Blo 850355 1364483 := bstep (se 1 (by rfl) ⟨1023362, by rfl⟩ : syracuseStep 1364483 = 2046725) B2046725
theorem B1921553 : Blo 850355 1921553 := bstep (se 2 (by rfl) ⟨720582, by rfl⟩ : syracuseStep 1921553 = 1441165) B1441165
theorem B1921571 : Blo 850355 1921571 := bstep (se 1 (by rfl) ⟨1441178, by rfl⟩ : syracuseStep 1921571 = 2882357) B2882357
theorem B11686513 : Blo 850355 11686513 := bstep (se 2 (by rfl) ⟨4382442, by rfl⟩ : syracuseStep 11686513 = 8764885) B8764885
theorem B1921841 : Blo 850355 1921841 := bstep (se 2 (by rfl) ⟨720690, by rfl⟩ : syracuseStep 1921841 = 1441381) B1441381
theorem B1921859 : Blo 850355 1921859 := bstep (se 1 (by rfl) ⟨1441394, by rfl⟩ : syracuseStep 1921859 = 2882789) B2882789
theorem B2872205 : Blo 850355 2872205 := bstep (se 3 (by rfl) ⟨538538, by rfl⟩ : syracuseStep 2872205 = 1077077) B1077077
theorem B1823651 : Blo 850355 1823651 := bstep (se 1 (by rfl) ⟨1367738, by rfl⟩ : syracuseStep 1823651 = 2735477) B2735477
theorem B2872259 : Blo 850355 2872259 := bstep (se 1 (by rfl) ⟨2154194, by rfl⟩ : syracuseStep 2872259 = 4308389) B4308389
theorem B3232781 : Blo 850355 3232781 := bstep (se 3 (by rfl) ⟨606146, by rfl⟩ : syracuseStep 3232781 = 1212293) B1212293
theorem B1922129 : Blo 850355 1922129 := bstep (se 2 (by rfl) ⟨720798, by rfl⟩ : syracuseStep 1922129 = 1441597) B1441597
theorem B1922147 : Blo 850355 1922147 := bstep (se 1 (by rfl) ⟨1441610, by rfl⟩ : syracuseStep 1922147 = 2883221) B2883221
theorem B2872529 : Blo 850355 2872529 := bstep (se 2 (by rfl) ⟨1077198, by rfl⟩ : syracuseStep 2872529 = 2154397) B2154397
theorem B1365265 : Blo 850355 1365265 := bstep (se 2 (by rfl) ⟨511974, by rfl⟩ : syracuseStep 1365265 = 1023949) B1023949
theorem B1824113 : Blo 850355 1824113 := bstep (se 2 (by rfl) ⟨684042, by rfl⟩ : syracuseStep 1824113 = 1368085) B1368085
theorem B4314545 : Blo 850355 4314545 := bstep (se 2 (by rfl) ⟨1617954, by rfl⟩ : syracuseStep 4314545 = 3235909) B3235909
theorem B4609457 : Blo 850355 4609457 := bstep (se 2 (by rfl) ⟨1728546, by rfl⟩ : syracuseStep 4609457 = 3457093) B3457093
theorem B2873069 : Blo 850355 2873069 := bstep (se 3 (by rfl) ⟨538700, by rfl⟩ : syracuseStep 2873069 = 1077401) B1077401
theorem B2873123 : Blo 850355 2873123 := bstep (se 1 (by rfl) ⟨2154842, by rfl⟩ : syracuseStep 2873123 = 4309685) B4309685
theorem B5461829 : Blo 850355 5461829 := bstep (se 4 (by rfl) ⟨512046, by rfl⟩ : syracuseStep 5461829 = 1024093) B1024093
theorem B972691 : Blo 850355 972691 := bstep (se 1 (by rfl) ⟨729518, by rfl⟩ : syracuseStep 972691 = 1459037) B1459037
theorem B2873393 : Blo 850355 2873393 := bstep (se 2 (by rfl) ⟨1077522, by rfl⟩ : syracuseStep 2873393 = 2155045) B2155045
theorem B1366067 : Blo 850355 1366067 := bstep (se 1 (by rfl) ⟨1024550, by rfl⟩ : syracuseStep 1366067 = 2049101) B2049101
theorem B6477893 : Blo 850355 6477893 := bstep (se 4 (by rfl) ⟨607302, by rfl⟩ : syracuseStep 6477893 = 1214605) B1214605
theorem B973075 : Blo 850355 973075 := bstep (se 1 (by rfl) ⟨729806, by rfl⟩ : syracuseStep 973075 = 1459613) B1459613
theorem B1366579 : Blo 850355 1366579 := bstep (se 1 (by rfl) ⟨1024934, by rfl⟩ : syracuseStep 1366579 = 2049869) B2049869
theorem B2873933 : Blo 850355 2873933 := bstep (se 3 (by rfl) ⟨538862, by rfl⟩ : syracuseStep 2873933 = 1077725) B1077725
theorem B2873987 : Blo 850355 2873987 := bstep (se 1 (by rfl) ⟨2155490, by rfl⟩ : syracuseStep 2873987 = 4310981) B4310981
theorem B1727153 : Blo 850355 1727153 := bstep (se 2 (by rfl) ⟨647682, by rfl⟩ : syracuseStep 1727153 = 1295365) B1295365
theorem B1727249 : Blo 850355 1727249 := bstep (se 2 (by rfl) ⟨647718, by rfl⟩ : syracuseStep 1727249 = 1295437) B1295437
theorem B4316003 : Blo 850355 4316003 := bstep (se 1 (by rfl) ⟨3237002, by rfl⟩ : syracuseStep 4316003 = 6474005) B6474005
theorem B2874257 : Blo 850355 2874257 := bstep (se 2 (by rfl) ⟨1077846, by rfl⟩ : syracuseStep 2874257 = 2155693) B2155693
theorem B3070925 : Blo 850355 3070925 := bstep (se 3 (by rfl) ⟨575798, by rfl⟩ : syracuseStep 3070925 = 1151597) B1151597
theorem B2153425 : Blo 850355 2153425 := bstep (se 2 (by rfl) ⟨807534, by rfl⟩ : syracuseStep 2153425 = 1615069) B1615069
theorem B1367123 : Blo 850355 1367123 := bstep (se 1 (by rfl) ⟨1025342, by rfl⟩ : syracuseStep 1367123 = 2050685) B2050685
theorem B2153699 : Blo 850355 2153699 := bstep (se 1 (by rfl) ⟨1615274, by rfl⟩ : syracuseStep 2153699 = 3230549) B3230549
theorem B1367297 : Blo 850355 1367297 := bstep (se 2 (by rfl) ⟨512736, by rfl⟩ : syracuseStep 1367297 = 1025473) B1025473
theorem B2153891 : Blo 850355 2153891 := bstep (se 1 (by rfl) ⟨1615418, by rfl⟩ : syracuseStep 2153891 = 3230837) B3230837
theorem B2874797 : Blo 850355 2874797 := bstep (se 3 (by rfl) ⟨539024, by rfl⟩ : syracuseStep 2874797 = 1078049) B1078049
theorem B5823971 : Blo 850355 5823971 := bstep (se 1 (by rfl) ⟨4367978, by rfl⟩ : syracuseStep 5823971 = 8735957) B8735957
theorem B2874851 : Blo 850355 2874851 := bstep (se 1 (by rfl) ⟨2156138, by rfl⟩ : syracuseStep 2874851 = 4312277) B4312277
theorem B3071459 : Blo 850355 3071459 := bstep (se 1 (by rfl) ⟨2303594, by rfl⟩ : syracuseStep 3071459 = 4607189) B4607189
theorem B4316813 : Blo 850355 4316813 := bstep (se 3 (by rfl) ⟨809402, by rfl⟩ : syracuseStep 4316813 = 1618805) B1618805
theorem B2875121 : Blo 850355 2875121 := bstep (se 2 (by rfl) ⟨1078170, by rfl⟩ : syracuseStep 2875121 = 2156341) B2156341
theorem B909139 : Blo 850355 909139 := bstep (se 1 (by rfl) ⟨681854, by rfl⟩ : syracuseStep 909139 = 1363709) B1363709
theorem B3235697 : Blo 850355 3235697 := bstep (se 2 (by rfl) ⟨1213386, by rfl⟩ : syracuseStep 3235697 = 2426773) B2426773
theorem B2187281 : Blo 850355 2187281 := bstep (se 2 (by rfl) ⟨820230, by rfl⟩ : syracuseStep 2187281 = 1640461) B1640461
theorem B3072163 : Blo 850355 3072163 := bstep (se 1 (by rfl) ⟨2304122, by rfl⟩ : syracuseStep 3072163 = 4608245) B4608245
theorem B2875661 : Blo 850355 2875661 := bstep (se 3 (by rfl) ⟨539186, by rfl⟩ : syracuseStep 2875661 = 1078373) B1078373
theorem B909587 : Blo 850355 909587 := bstep (se 1 (by rfl) ⟨682190, by rfl⟩ : syracuseStep 909587 = 1364381) B1364381
theorem B2875715 : Blo 850355 2875715 := bstep (se 1 (by rfl) ⟨2156786, by rfl⟩ : syracuseStep 2875715 = 4313573) B4313573
theorem B2154833 : Blo 850355 2154833 := bstep (se 2 (by rfl) ⟨808062, by rfl⟩ : syracuseStep 2154833 = 1616125) B1616125
theorem B2154883 : Blo 850355 2154883 := bstep (se 1 (by rfl) ⟨1616162, by rfl⟩ : syracuseStep 2154883 = 3232325) B3232325
theorem B2155025 : Blo 850355 2155025 := bstep (se 2 (by rfl) ⟨808134, by rfl⟩ : syracuseStep 2155025 = 1616269) B1616269
theorem B2875985 : Blo 850355 2875985 := bstep (se 2 (by rfl) ⟨1078494, by rfl⟩ : syracuseStep 2875985 = 2156989) B2156989
theorem B44360405 : Blo 850355 44360405 := bstep (se 7 (by rfl) ⟨519848, by rfl⟩ : syracuseStep 44360405 = 1039697) B1039697
theorem B2810819 : Blo 850355 2810819 := bstep (se 1 (by rfl) ⟨2108114, by rfl⟩ : syracuseStep 2810819 = 4216229) B4216229
theorem B1598467 : Blo 850355 1598467 := bstep (se 1 (by rfl) ⟨1198850, by rfl⟩ : syracuseStep 1598467 = 2397701) B2397701
theorem B10347533 : Blo 850355 10347533 := bstep (se 3 (by rfl) ⟨1940162, by rfl⟩ : syracuseStep 10347533 = 3880325) B3880325
theorem B2876525 : Blo 850355 2876525 := bstep (se 3 (by rfl) ⟨539348, by rfl⟩ : syracuseStep 2876525 = 1078697) B1078697
theorem B2876579 : Blo 850355 2876579 := bstep (se 1 (by rfl) ⟨2157434, by rfl⟩ : syracuseStep 2876579 = 4314869) B4314869
theorem B5825741 : Blo 850355 5825741 := bstep (se 3 (by rfl) ⟨1092326, by rfl⟩ : syracuseStep 5825741 = 2184653) B2184653
theorem B3237155 : Blo 850355 3237155 := bstep (se 1 (by rfl) ⟨2427866, by rfl⟩ : syracuseStep 3237155 = 4855733) B4855733
theorem B1435009 : Blo 850355 1435009 := bstep (se 2 (by rfl) ⟨538128, by rfl⟩ : syracuseStep 1435009 = 1076257) B1076257
theorem B1435043 : Blo 850355 1435043 := bstep (se 1 (by rfl) ⟨1076282, by rfl⟩ : syracuseStep 1435043 = 2152565) B2152565
theorem B2876849 : Blo 850355 2876849 := bstep (se 2 (by rfl) ⟨1078818, by rfl⟩ : syracuseStep 2876849 = 2157637) B2157637
theorem B2156017 : Blo 850355 2156017 := bstep (se 2 (by rfl) ⟨808506, by rfl⟩ : syracuseStep 2156017 = 1617013) B1617013
theorem B1435171 : Blo 850355 1435171 := bstep (se 1 (by rfl) ⟨1076378, by rfl⟩ : syracuseStep 1435171 = 2152757) B2152757
theorem B910963 : Blo 850355 910963 := bstep (se 1 (by rfl) ⟨683222, by rfl⟩ : syracuseStep 910963 = 1366445) B1366445
theorem B1435313 : Blo 850355 1435313 := bstep (se 2 (by rfl) ⟨538242, by rfl⟩ : syracuseStep 1435313 = 1076485) B1076485
theorem B2156291 : Blo 850355 2156291 := bstep (se 1 (by rfl) ⟨1617218, by rfl⟩ : syracuseStep 2156291 = 3234437) B3234437
theorem B1435441 : Blo 850355 1435441 := bstep (se 2 (by rfl) ⟨538290, by rfl⟩ : syracuseStep 1435441 = 1076581) B1076581
theorem B1435475 : Blo 850355 1435475 := bstep (se 1 (by rfl) ⟨1076606, by rfl⟩ : syracuseStep 1435475 = 2153213) B2153213
theorem B13854577 : Blo 850355 13854577 := bstep (se 2 (by rfl) ⟨5195466, by rfl⟩ : syracuseStep 13854577 = 10390933) B10390933
theorem B2156483 : Blo 850355 2156483 := bstep (se 1 (by rfl) ⟨1617362, by rfl⟩ : syracuseStep 2156483 = 3234725) B3234725
theorem B2877389 : Blo 850355 2877389 := bstep (se 3 (by rfl) ⟨539510, by rfl⟩ : syracuseStep 2877389 = 1079021) B1079021
theorem B1435603 : Blo 850355 1435603 := bstep (se 1 (by rfl) ⟨1076702, by rfl⟩ : syracuseStep 1435603 = 2153405) B2153405
theorem B2877443 : Blo 850355 2877443 := bstep (se 1 (by rfl) ⟨2158082, by rfl⟩ : syracuseStep 2877443 = 4316165) B4316165
theorem B3237937 : Blo 850355 3237937 := bstep (se 2 (by rfl) ⟨1214226, by rfl⟩ : syracuseStep 3237937 = 2428453) B2428453
theorem B9234485 : Blo 850355 9234485 := bstep (se 5 (by rfl) ⟨432866, by rfl⟩ : syracuseStep 9234485 = 865733) B865733
theorem B3074125 : Blo 850355 3074125 := bstep (se 3 (by rfl) ⟨576398, by rfl⟩ : syracuseStep 3074125 = 1152797) B1152797
theorem B1435745 : Blo 850355 1435745 := bstep (se 2 (by rfl) ⟨538404, by rfl⟩ : syracuseStep 1435745 = 1076809) B1076809
theorem B4909189 : Blo 850355 4909189 := bstep (se 4 (by rfl) ⟨460236, by rfl⟩ : syracuseStep 4909189 = 920473) B920473
theorem B7760069 : Blo 850355 7760069 := bstep (se 4 (by rfl) ⟨727506, by rfl⟩ : syracuseStep 7760069 = 1455013) B1455013
theorem B2189521 : Blo 850355 2189521 := bstep (se 2 (by rfl) ⟨821070, by rfl⟩ : syracuseStep 2189521 = 1642141) B1642141
theorem B1435873 : Blo 850355 1435873 := bstep (se 2 (by rfl) ⟨538452, by rfl⟩ : syracuseStep 1435873 = 1076905) B1076905
theorem B1435907 : Blo 850355 1435907 := bstep (se 1 (by rfl) ⟨1076930, by rfl⟩ : syracuseStep 1435907 = 2153861) B2153861
theorem B3238157 : Blo 850355 3238157 := bstep (se 3 (by rfl) ⟨607154, by rfl⟩ : syracuseStep 3238157 = 1214309) B1214309
theorem B2877713 : Blo 850355 2877713 := bstep (se 2 (by rfl) ⟨1079142, by rfl⟩ : syracuseStep 2877713 = 2158285) B2158285
theorem B1436035 : Blo 850355 1436035 := bstep (se 1 (by rfl) ⟨1077026, by rfl⟩ : syracuseStep 1436035 = 2154053) B2154053
theorem B1403281 : Blo 850355 1403281 := bstep (se 2 (by rfl) ⟨526230, by rfl⟩ : syracuseStep 1403281 = 1052461) B1052461
theorem B1534403 : Blo 850355 1534403 := bstep (se 1 (by rfl) ⟨1150802, by rfl⟩ : syracuseStep 1534403 = 2301605) B2301605
theorem B4319729 : Blo 850355 4319729 := bstep (se 2 (by rfl) ⟨1619898, by rfl⟩ : syracuseStep 4319729 = 3239797) B3239797
theorem B3074573 : Blo 850355 3074573 := bstep (se 3 (by rfl) ⟨576482, by rfl⟩ : syracuseStep 3074573 = 1152965) B1152965
theorem B1436177 : Blo 850355 1436177 := bstep (se 2 (by rfl) ⟨538566, by rfl⟩ : syracuseStep 1436177 = 1077133) B1077133
theorem B4614691 : Blo 850355 4614691 := bstep (se 1 (by rfl) ⟨3461018, by rfl⟩ : syracuseStep 4614691 = 6922037) B6922037
theorem B1436305 : Blo 850355 1436305 := bstep (se 2 (by rfl) ⟨538614, by rfl⟩ : syracuseStep 1436305 = 1077229) B1077229
theorem B1436339 : Blo 850355 1436339 := bstep (se 1 (by rfl) ⟨1077254, by rfl⟩ : syracuseStep 1436339 = 2154509) B2154509
theorem B2878253 : Blo 850355 2878253 := bstep (se 3 (by rfl) ⟨539672, by rfl⟩ : syracuseStep 2878253 = 1079345) B1079345
theorem B1436467 : Blo 850355 1436467 := bstep (se 1 (by rfl) ⟨1077350, by rfl⟩ : syracuseStep 1436467 = 2154701) B2154701
theorem B4844387 : Blo 850355 4844387 := bstep (se 1 (by rfl) ⟨3633290, by rfl⟩ : syracuseStep 4844387 = 7266581) B7266581
theorem B2878307 : Blo 850355 2878307 := bstep (se 1 (by rfl) ⟨2158730, by rfl⟩ : syracuseStep 2878307 = 4317461) B4317461
theorem B912227 : Blo 850355 912227 := bstep (se 1 (by rfl) ⟨684170, by rfl⟩ : syracuseStep 912227 = 1368341) B1368341
theorem B2157425 : Blo 850355 2157425 := bstep (se 2 (by rfl) ⟨809034, by rfl⟩ : syracuseStep 2157425 = 1618069) B1618069
theorem B2157475 : Blo 850355 2157475 := bstep (se 1 (by rfl) ⟨1618106, by rfl⟩ : syracuseStep 2157475 = 3236213) B3236213
theorem B1436609 : Blo 850355 1436609 := bstep (se 2 (by rfl) ⟨538728, by rfl⟩ : syracuseStep 1436609 = 1077457) B1077457
theorem B1010675 : Blo 850355 1010675 := bstep (se 1 (by rfl) ⟨758006, by rfl⟩ : syracuseStep 1010675 = 1516013) B1516013
theorem B2157617 : Blo 850355 2157617 := bstep (se 2 (by rfl) ⟨809106, by rfl⟩ : syracuseStep 2157617 = 1618213) B1618213
theorem B1436737 : Blo 850355 1436737 := bstep (se 2 (by rfl) ⟨538776, by rfl⟩ : syracuseStep 1436737 = 1077553) B1077553
theorem B1076323 : Blo 850355 1076323 := bstep (se 1 (by rfl) ⟨807242, by rfl⟩ : syracuseStep 1076323 = 1614485) B1614485
theorem B1436771 : Blo 850355 1436771 := bstep (se 1 (by rfl) ⟨1077578, by rfl⟩ : syracuseStep 1436771 = 2155157) B2155157
theorem B2878577 : Blo 850355 2878577 := bstep (se 2 (by rfl) ⟨1079466, by rfl⟩ : syracuseStep 2878577 = 2158933) B2158933
theorem B1076419 : Blo 850355 1076419 := bstep (se 1 (by rfl) ⟨807314, by rfl⟩ : syracuseStep 1076419 = 1614629) B1614629
theorem B1436899 : Blo 850355 1436899 := bstep (se 1 (by rfl) ⟨1077674, by rfl⟩ : syracuseStep 1436899 = 2155349) B2155349
theorem B1437041 : Blo 850355 1437041 := bstep (se 2 (by rfl) ⟨538890, by rfl⟩ : syracuseStep 1437041 = 1077781) B1077781
theorem B16379333 : Blo 850355 16379333 := bstep (se 4 (by rfl) ⟨1535562, by rfl⟩ : syracuseStep 16379333 = 3071125) B3071125
theorem B2911697 : Blo 850355 2911697 := bstep (se 2 (by rfl) ⟨1091886, by rfl⟩ : syracuseStep 2911697 = 2183773) B2183773
theorem B1535441 : Blo 850355 1535441 := bstep (se 2 (by rfl) ⟨575790, by rfl⟩ : syracuseStep 1535441 = 1151581) B1151581
theorem B1437169 : Blo 850355 1437169 := bstep (se 2 (by rfl) ⟨538938, by rfl⟩ : syracuseStep 1437169 = 1077877) B1077877
theorem B1437203 : Blo 850355 1437203 := bstep (se 1 (by rfl) ⟨1077902, by rfl⟩ : syracuseStep 1437203 = 2155805) B2155805
theorem B9203341 : Blo 850355 9203341 := bstep (se 3 (by rfl) ⟨1725626, by rfl⟩ : syracuseStep 9203341 = 3451253) B3451253
theorem B2879117 : Blo 850355 2879117 := bstep (se 3 (by rfl) ⟨539834, by rfl⟩ : syracuseStep 2879117 = 1079669) B1079669
theorem B1437331 : Blo 850355 1437331 := bstep (se 1 (by rfl) ⟨1077998, by rfl⟩ : syracuseStep 1437331 = 2155997) B2155997
theorem B1076915 : Blo 850355 1076915 := bstep (se 1 (by rfl) ⟨807686, by rfl⟩ : syracuseStep 1076915 = 1615373) B1615373
theorem B2879171 : Blo 850355 2879171 := bstep (se 1 (by rfl) ⟨2159378, by rfl⟩ : syracuseStep 2879171 = 4318757) B4318757
theorem B6483725 : Blo 850355 6483725 := bstep (se 3 (by rfl) ⟨1215698, by rfl⟩ : syracuseStep 6483725 = 2431397) B2431397
theorem B1437473 : Blo 850355 1437473 := bstep (se 2 (by rfl) ⟨539052, by rfl⟩ : syracuseStep 1437473 = 1078105) B1078105
theorem B1437601 : Blo 850355 1437601 := bstep (se 2 (by rfl) ⟨539100, by rfl⟩ : syracuseStep 1437601 = 1078201) B1078201
theorem B4321187 : Blo 850355 4321187 := bstep (se 1 (by rfl) ⟨3240890, by rfl⟩ : syracuseStep 4321187 = 6481781) B6481781
theorem B1437635 : Blo 850355 1437635 := bstep (se 1 (by rfl) ⟨1078226, by rfl⟩ : syracuseStep 1437635 = 2156453) B2156453
theorem B2879441 : Blo 850355 2879441 := bstep (se 2 (by rfl) ⟨1079790, by rfl⟩ : syracuseStep 2879441 = 2159581) B2159581
theorem B2158609 : Blo 850355 2158609 := bstep (se 2 (by rfl) ⟨809478, by rfl⟩ : syracuseStep 2158609 = 1618957) B1618957
theorem B1437763 : Blo 850355 1437763 := bstep (se 1 (by rfl) ⟨1078322, by rfl⟩ : syracuseStep 1437763 = 2156645) B2156645
theorem B1437905 : Blo 850355 1437905 := bstep (se 2 (by rfl) ⟨539214, by rfl⟩ : syracuseStep 1437905 = 1078429) B1078429
theorem B1995043 : Blo 850355 1995043 := bstep (se 1 (by rfl) ⟨1496282, by rfl⟩ : syracuseStep 1995043 = 2992565) B2992565
theorem B2158883 : Blo 850355 2158883 := bstep (se 1 (by rfl) ⟨1619162, by rfl⟩ : syracuseStep 2158883 = 3238325) B3238325
theorem B3240269 : Blo 850355 3240269 := bstep (se 3 (by rfl) ⟨607550, by rfl⟩ : syracuseStep 3240269 = 1215101) B1215101
theorem B1438033 : Blo 850355 1438033 := bstep (se 2 (by rfl) ⟨539262, by rfl⟩ : syracuseStep 1438033 = 1078525) B1078525
theorem B1077619 : Blo 850355 1077619 := bstep (se 1 (by rfl) ⟨808214, by rfl⟩ : syracuseStep 1077619 = 1616429) B1616429
theorem B1438067 : Blo 850355 1438067 := bstep (se 1 (by rfl) ⟨1078550, by rfl⟩ : syracuseStep 1438067 = 2157101) B2157101
theorem B1077715 : Blo 850355 1077715 := bstep (se 1 (by rfl) ⟨808286, by rfl⟩ : syracuseStep 1077715 = 1616573) B1616573
theorem B2159075 : Blo 850355 2159075 := bstep (se 1 (by rfl) ⟨1619306, by rfl⟩ : syracuseStep 2159075 = 3238613) B3238613
theorem B2879981 : Blo 850355 2879981 := bstep (se 3 (by rfl) ⟨539996, by rfl⟩ : syracuseStep 2879981 = 1079993) B1079993
theorem B1438195 : Blo 850355 1438195 := bstep (se 1 (by rfl) ⟨1078646, by rfl⟩ : syracuseStep 1438195 = 2157293) B2157293
theorem B2880035 : Blo 850355 2880035 := bstep (se 1 (by rfl) ⟨2160026, by rfl⟩ : syracuseStep 2880035 = 4320053) B4320053
theorem B1438337 : Blo 850355 1438337 := bstep (se 2 (by rfl) ⟨539376, by rfl⟩ : syracuseStep 1438337 = 1078753) B1078753
theorem B4321997 : Blo 850355 4321997 := bstep (se 3 (by rfl) ⟨810374, by rfl⟩ : syracuseStep 4321997 = 1620749) B1620749
theorem B1438465 : Blo 850355 1438465 := bstep (se 2 (by rfl) ⟨539424, by rfl⟩ : syracuseStep 1438465 = 1078849) B1078849
theorem B1438499 : Blo 850355 1438499 := bstep (se 1 (by rfl) ⟨1078874, by rfl⟩ : syracuseStep 1438499 = 2157749) B2157749
theorem B2880305 : Blo 850355 2880305 := bstep (se 2 (by rfl) ⟨1080114, by rfl⟩ : syracuseStep 2880305 = 2160229) B2160229
theorem B6746993 : Blo 850355 6746993 := bstep (se 2 (by rfl) ⟨2530122, by rfl⟩ : syracuseStep 6746993 = 5060245) B5060245
theorem B1438627 : Blo 850355 1438627 := bstep (se 1 (by rfl) ⟨1078970, by rfl⟩ : syracuseStep 1438627 = 2157941) B2157941
theorem B1078211 : Blo 850355 1078211 := bstep (se 1 (by rfl) ⟨808658, by rfl⟩ : syracuseStep 1078211 = 1617317) B1617317
theorem B1438769 : Blo 850355 1438769 := bstep (se 2 (by rfl) ⟨539538, by rfl⟩ : syracuseStep 1438769 = 1079077) B1079077
theorem B5829745 : Blo 850355 5829745 := bstep (se 2 (by rfl) ⟨2186154, by rfl⟩ : syracuseStep 5829745 = 4372309) B4372309
theorem B3241073 : Blo 850355 3241073 := bstep (se 2 (by rfl) ⟨1215402, by rfl⟩ : syracuseStep 3241073 = 2430805) B2430805
theorem B1438897 : Blo 850355 1438897 := bstep (se 2 (by rfl) ⟨539586, by rfl⟩ : syracuseStep 1438897 = 1079173) B1079173
theorem B1438931 : Blo 850355 1438931 := bstep (se 1 (by rfl) ⟨1079198, by rfl⟩ : syracuseStep 1438931 = 2158397) B2158397
theorem B2422001 : Blo 850355 2422001 := bstep (se 2 (by rfl) ⟨908250, by rfl⟩ : syracuseStep 2422001 = 1816501) B1816501
theorem B2880845 : Blo 850355 2880845 := bstep (se 3 (by rfl) ⟨540158, by rfl⟩ : syracuseStep 2880845 = 1080317) B1080317
theorem B1439059 : Blo 850355 1439059 := bstep (se 1 (by rfl) ⟨1079294, by rfl⟩ : syracuseStep 1439059 = 2158589) B2158589
theorem B2880899 : Blo 850355 2880899 := bstep (se 1 (by rfl) ⟨2160674, by rfl⟩ : syracuseStep 2880899 = 4321349) B4321349
theorem B2160017 : Blo 850355 2160017 := bstep (se 2 (by rfl) ⟨810006, by rfl⟩ : syracuseStep 2160017 = 1620013) B1620013
theorem B2160067 : Blo 850355 2160067 := bstep (se 1 (by rfl) ⟨1620050, by rfl⟩ : syracuseStep 2160067 = 3240101) B3240101
theorem B1439201 : Blo 850355 1439201 := bstep (se 2 (by rfl) ⟨539700, by rfl⟩ : syracuseStep 1439201 = 1079401) B1079401
theorem B4617805 : Blo 850355 4617805 := bstep (se 3 (by rfl) ⟨865838, by rfl⟩ : syracuseStep 4617805 = 1731677) B1731677
theorem B2160209 : Blo 850355 2160209 := bstep (se 2 (by rfl) ⟨810078, by rfl⟩ : syracuseStep 2160209 = 1620157) B1620157
theorem B1439329 : Blo 850355 1439329 := bstep (se 2 (by rfl) ⟨539748, by rfl⟩ : syracuseStep 1439329 = 1079497) B1079497
theorem B1078915 : Blo 850355 1078915 := bstep (se 1 (by rfl) ⟨809186, by rfl⟩ : syracuseStep 1078915 = 1618373) B1618373
theorem B1439363 : Blo 850355 1439363 := bstep (se 1 (by rfl) ⟨1079522, by rfl⟩ : syracuseStep 1439363 = 2159045) B2159045
theorem B2881169 : Blo 850355 2881169 := bstep (se 2 (by rfl) ⟨1080438, by rfl⟩ : syracuseStep 2881169 = 2160877) B2160877
theorem B1275539 : Blo 850355 1275539 := bstep (se 1 (by rfl) ⟨956654, by rfl⟩ : syracuseStep 1275539 = 1913309) B1913309
theorem B1275569 : Blo 850355 1275569 := bstep (se 2 (by rfl) ⟨478338, by rfl⟩ : syracuseStep 1275569 = 956677) B956677
theorem B1275587 : Blo 850355 1275587 := bstep (se 1 (by rfl) ⟨956690, by rfl⟩ : syracuseStep 1275587 = 1913381) B1913381
theorem B1275617 : Blo 850355 1275617 := bstep (se 2 (by rfl) ⟨478356, by rfl⟩ : syracuseStep 1275617 = 956713) B956713
theorem B3634915 : Blo 850355 3634915 := bstep (se 1 (by rfl) ⟨2726186, by rfl⟩ : syracuseStep 3634915 = 5452373) B5452373
theorem B1079011 : Blo 850355 1079011 := bstep (se 1 (by rfl) ⟨809258, by rfl⟩ : syracuseStep 1079011 = 1618517) B1618517
theorem B1275635 : Blo 850355 1275635 := bstep (se 1 (by rfl) ⟨956726, by rfl⟩ : syracuseStep 1275635 = 1913453) B1913453
theorem B1439491 : Blo 850355 1439491 := bstep (se 1 (by rfl) ⟨1079618, by rfl⟩ : syracuseStep 1439491 = 2159237) B2159237
theorem B3241741 : Blo 850355 3241741 := bstep (se 3 (by rfl) ⟨607826, by rfl⟩ : syracuseStep 3241741 = 1215653) B1215653
theorem B1275665 : Blo 850355 1275665 := bstep (se 2 (by rfl) ⟨478374, by rfl⟩ : syracuseStep 1275665 = 956749) B956749
theorem B1275683 : Blo 850355 1275683 := bstep (se 1 (by rfl) ⟨956762, by rfl⟩ : syracuseStep 1275683 = 1913525) B1913525
theorem B1275713 : Blo 850355 1275713 := bstep (se 2 (by rfl) ⟨478392, by rfl⟩ : syracuseStep 1275713 = 956785) B956785
theorem B1275731 : Blo 850355 1275731 := bstep (se 1 (by rfl) ⟨956798, by rfl⟩ : syracuseStep 1275731 = 1913597) B1913597
theorem B1275761 : Blo 850355 1275761 := bstep (se 2 (by rfl) ⟨478410, by rfl⟩ : syracuseStep 1275761 = 956821) B956821
theorem B1275779 : Blo 850355 1275779 := bstep (se 1 (by rfl) ⟨956834, by rfl⟩ : syracuseStep 1275779 = 1913669) B1913669
theorem B2422673 : Blo 850355 2422673 := bstep (se 2 (by rfl) ⟨908502, by rfl⟩ : syracuseStep 2422673 = 1817005) B1817005
theorem B1439633 : Blo 850355 1439633 := bstep (se 2 (by rfl) ⟨539862, by rfl⟩ : syracuseStep 1439633 = 1079725) B1079725
theorem B1275809 : Blo 850355 1275809 := bstep (se 2 (by rfl) ⟨478428, by rfl⟩ : syracuseStep 1275809 = 956857) B956857
theorem B1275827 : Blo 850355 1275827 := bstep (se 1 (by rfl) ⟨956870, by rfl⟩ : syracuseStep 1275827 = 1913741) B1913741
theorem B1275857 : Blo 850355 1275857 := bstep (se 2 (by rfl) ⟨478446, by rfl⟩ : syracuseStep 1275857 = 956893) B956893
theorem B1275875 : Blo 850355 1275875 := bstep (se 1 (by rfl) ⟨956906, by rfl⟩ : syracuseStep 1275875 = 1913813) B1913813
theorem B1275905 : Blo 850355 1275905 := bstep (se 2 (by rfl) ⟨478464, by rfl⟩ : syracuseStep 1275905 = 956929) B956929
theorem B1439761 : Blo 850355 1439761 := bstep (se 2 (by rfl) ⟨539910, by rfl⟩ : syracuseStep 1439761 = 1079821) B1079821
theorem B1275923 : Blo 850355 1275923 := bstep (se 1 (by rfl) ⟨956942, by rfl⟩ : syracuseStep 1275923 = 1913885) B1913885
theorem B1275953 : Blo 850355 1275953 := bstep (se 2 (by rfl) ⟨478482, by rfl⟩ : syracuseStep 1275953 = 956965) B956965
theorem B1439795 : Blo 850355 1439795 := bstep (se 1 (by rfl) ⟨1079846, by rfl⟩ : syracuseStep 1439795 = 2159693) B2159693
theorem B1275971 : Blo 850355 1275971 := bstep (se 1 (by rfl) ⟨956978, by rfl⟩ : syracuseStep 1275971 = 1913957) B1913957
theorem B1276001 : Blo 850355 1276001 := bstep (se 2 (by rfl) ⟨478500, by rfl⟩ : syracuseStep 1276001 = 957001) B957001
theorem B1276019 : Blo 850355 1276019 := bstep (se 1 (by rfl) ⟨957014, by rfl⟩ : syracuseStep 1276019 = 1914029) B1914029
theorem B1276049 : Blo 850355 1276049 := bstep (se 2 (by rfl) ⟨478518, by rfl⟩ : syracuseStep 1276049 = 957037) B957037
theorem B1276067 : Blo 850355 1276067 := bstep (se 1 (by rfl) ⟨957050, by rfl⟩ : syracuseStep 1276067 = 1914101) B1914101
theorem B2881709 : Blo 850355 2881709 := bstep (se 3 (by rfl) ⟨540320, by rfl⟩ : syracuseStep 2881709 = 1080641) B1080641
theorem B1439923 : Blo 850355 1439923 := bstep (se 1 (by rfl) ⟨1079942, by rfl⟩ : syracuseStep 1439923 = 2159885) B2159885
theorem B1276097 : Blo 850355 1276097 := bstep (se 2 (by rfl) ⟨478536, by rfl⟩ : syracuseStep 1276097 = 957073) B957073
theorem B1276115 : Blo 850355 1276115 := bstep (se 1 (by rfl) ⟨957086, by rfl⟩ : syracuseStep 1276115 = 1914173) B1914173
theorem B1079507 : Blo 850355 1079507 := bstep (se 1 (by rfl) ⟨809630, by rfl⟩ : syracuseStep 1079507 = 1619261) B1619261
theorem B2881763 : Blo 850355 2881763 := bstep (se 1 (by rfl) ⟨2161322, by rfl⟩ : syracuseStep 2881763 = 4322645) B4322645
theorem B1276145 : Blo 850355 1276145 := bstep (se 2 (by rfl) ⟨478554, by rfl⟩ : syracuseStep 1276145 = 957109) B957109
theorem B1276163 : Blo 850355 1276163 := bstep (se 1 (by rfl) ⟨957122, by rfl⟩ : syracuseStep 1276163 = 1914245) B1914245
theorem B1276193 : Blo 850355 1276193 := bstep (se 2 (by rfl) ⟨478572, by rfl⟩ : syracuseStep 1276193 = 957145) B957145
theorem B1276211 : Blo 850355 1276211 := bstep (se 1 (by rfl) ⟨957158, by rfl⟩ : syracuseStep 1276211 = 1914317) B1914317
theorem B1440065 : Blo 850355 1440065 := bstep (se 2 (by rfl) ⟨540024, by rfl⟩ : syracuseStep 1440065 = 1080049) B1080049
theorem B1276241 : Blo 850355 1276241 := bstep (se 2 (by rfl) ⟨478590, by rfl⟩ : syracuseStep 1276241 = 957181) B957181
theorem B1276259 : Blo 850355 1276259 := bstep (se 1 (by rfl) ⟨957194, by rfl⟩ : syracuseStep 1276259 = 1914389) B1914389
theorem B1276289 : Blo 850355 1276289 := bstep (se 2 (by rfl) ⟨478608, by rfl⟩ : syracuseStep 1276289 = 957217) B957217
theorem B1276307 : Blo 850355 1276307 := bstep (se 1 (by rfl) ⟨957230, by rfl⟩ : syracuseStep 1276307 = 1914461) B1914461
theorem B1210801 : Blo 850355 1210801 := bstep (se 2 (by rfl) ⟨454050, by rfl⟩ : syracuseStep 1210801 = 908101) B908101
theorem B1276337 : Blo 850355 1276337 := bstep (se 2 (by rfl) ⟨478626, by rfl⟩ : syracuseStep 1276337 = 957253) B957253
theorem B850355 : Blo 850355 850355 := bstep (se 1 (by rfl) ⟨637766, by rfl⟩ : syracuseStep 850355 = 1275533) B1275533
theorem B1440193 : Blo 850355 1440193 := bstep (se 2 (by rfl) ⟨540072, by rfl⟩ : syracuseStep 1440193 = 1080145) B1080145
theorem B850371 : Blo 850355 850371 := bstep (se 1 (by rfl) ⟨637778, by rfl⟩ : syracuseStep 850371 = 1275557) B1275557
theorem B1276355 : Blo 850355 1276355 := bstep (se 1 (by rfl) ⟨957266, by rfl⟩ : syracuseStep 1276355 = 1914533) B1914533
theorem B850387 : Blo 850355 850387 := bstep (se 1 (by rfl) ⟨637790, by rfl⟩ : syracuseStep 850387 = 1275581) B1275581
theorem B1210835 : Blo 850355 1210835 := bstep (se 1 (by rfl) ⟨908126, by rfl⟩ : syracuseStep 1210835 = 1816253) B1816253
theorem B1276385 : Blo 850355 1276385 := bstep (se 2 (by rfl) ⟨478644, by rfl⟩ : syracuseStep 1276385 = 957289) B957289
theorem B850403 : Blo 850355 850403 := bstep (se 1 (by rfl) ⟨637802, by rfl⟩ : syracuseStep 850403 = 1275605) B1275605
theorem B1440227 : Blo 850355 1440227 := bstep (se 1 (by rfl) ⟨1080170, by rfl⟩ : syracuseStep 1440227 = 2160341) B2160341
theorem B2882033 : Blo 850355 2882033 := bstep (se 2 (by rfl) ⟨1080762, by rfl⟩ : syracuseStep 2882033 = 2161525) B2161525
theorem B850419 : Blo 850355 850419 := bstep (se 1 (by rfl) ⟨637814, by rfl⟩ : syracuseStep 850419 = 1275629) B1275629
theorem B1276403 : Blo 850355 1276403 := bstep (se 1 (by rfl) ⟨957302, by rfl⟩ : syracuseStep 1276403 = 1914605) B1914605
theorem B850435 : Blo 850355 850435 := bstep (se 1 (by rfl) ⟨637826, by rfl⟩ : syracuseStep 850435 = 1275653) B1275653
theorem B1276433 : Blo 850355 1276433 := bstep (se 2 (by rfl) ⟨478662, by rfl⟩ : syracuseStep 1276433 = 957325) B957325
theorem B850451 : Blo 850355 850451 := bstep (se 1 (by rfl) ⟨637838, by rfl⟩ : syracuseStep 850451 = 1275677) B1275677
theorem B850467 : Blo 850355 850467 := bstep (se 1 (by rfl) ⟨637850, by rfl⟩ : syracuseStep 850467 = 1275701) B1275701
theorem B1276451 : Blo 850355 1276451 := bstep (se 1 (by rfl) ⟨957338, by rfl⟩ : syracuseStep 1276451 = 1914677) B1914677
theorem B3242531 : Blo 850355 3242531 := bstep (se 1 (by rfl) ⟨2431898, by rfl⟩ : syracuseStep 3242531 = 4863797) B4863797
theorem B2161201 : Blo 850355 2161201 := bstep (se 2 (by rfl) ⟨810450, by rfl⟩ : syracuseStep 2161201 = 1620901) B1620901
theorem B850483 : Blo 850355 850483 := bstep (se 1 (by rfl) ⟨637862, by rfl⟩ : syracuseStep 850483 = 1275725) B1275725
theorem B1276481 : Blo 850355 1276481 := bstep (se 2 (by rfl) ⟨478680, by rfl⟩ : syracuseStep 1276481 = 957361) B957361
theorem B850499 : Blo 850355 850499 := bstep (se 1 (by rfl) ⟨637874, by rfl⟩ : syracuseStep 850499 = 1275749) B1275749
theorem B850515 : Blo 850355 850515 := bstep (se 1 (by rfl) ⟨637886, by rfl⟩ : syracuseStep 850515 = 1275773) B1275773
theorem B1276499 : Blo 850355 1276499 := bstep (se 1 (by rfl) ⟨957374, by rfl⟩ : syracuseStep 1276499 = 1914749) B1914749
theorem B850531 : Blo 850355 850531 := bstep (se 1 (by rfl) ⟨637898, by rfl⟩ : syracuseStep 850531 = 1275797) B1275797
theorem B1440355 : Blo 850355 1440355 := bstep (se 1 (by rfl) ⟨1080266, by rfl⟩ : syracuseStep 1440355 = 2160533) B2160533
theorem B1276529 : Blo 850355 1276529 := bstep (se 2 (by rfl) ⟨478698, by rfl⟩ : syracuseStep 1276529 = 957397) B957397
theorem B6486641 : Blo 850355 6486641 := bstep (se 2 (by rfl) ⟨2432490, by rfl⟩ : syracuseStep 6486641 = 4864981) B4864981
theorem B850547 : Blo 850355 850547 := bstep (se 1 (by rfl) ⟨637910, by rfl⟩ : syracuseStep 850547 = 1275821) B1275821
theorem B850563 : Blo 850355 850563 := bstep (se 1 (by rfl) ⟨637922, by rfl⟩ : syracuseStep 850563 = 1275845) B1275845
theorem B1276547 : Blo 850355 1276547 := bstep (se 1 (by rfl) ⟨957410, by rfl⟩ : syracuseStep 1276547 = 1914821) B1914821
theorem B850579 : Blo 850355 850579 := bstep (se 1 (by rfl) ⟨637934, by rfl⟩ : syracuseStep 850579 = 1275869) B1275869
theorem B1276577 : Blo 850355 1276577 := bstep (se 2 (by rfl) ⟨478716, by rfl⟩ : syracuseStep 1276577 = 957433) B957433
theorem B850595 : Blo 850355 850595 := bstep (se 1 (by rfl) ⟨637946, by rfl⟩ : syracuseStep 850595 = 1275893) B1275893
theorem B2423459 : Blo 850355 2423459 := bstep (se 1 (by rfl) ⟨1817594, by rfl⟩ : syracuseStep 2423459 = 3635189) B3635189
theorem B850611 : Blo 850355 850611 := bstep (se 1 (by rfl) ⟨637958, by rfl⟩ : syracuseStep 850611 = 1275917) B1275917
theorem B1276595 : Blo 850355 1276595 := bstep (se 1 (by rfl) ⟨957446, by rfl⟩ : syracuseStep 1276595 = 1914893) B1914893
theorem B850627 : Blo 850355 850627 := bstep (se 1 (by rfl) ⟨637970, by rfl⟩ : syracuseStep 850627 = 1275941) B1275941
theorem B1276625 : Blo 850355 1276625 := bstep (se 2 (by rfl) ⟨478734, by rfl⟩ : syracuseStep 1276625 = 957469) B957469
theorem B850643 : Blo 850355 850643 := bstep (se 1 (by rfl) ⟨637982, by rfl⟩ : syracuseStep 850643 = 1275965) B1275965
theorem B850659 : Blo 850355 850659 := bstep (se 1 (by rfl) ⟨637994, by rfl⟩ : syracuseStep 850659 = 1275989) B1275989
theorem B1276643 : Blo 850355 1276643 := bstep (se 1 (by rfl) ⟨957482, by rfl⟩ : syracuseStep 1276643 = 1914965) B1914965
theorem B1440497 : Blo 850355 1440497 := bstep (se 2 (by rfl) ⟨540186, by rfl⟩ : syracuseStep 1440497 = 1080373) B1080373
theorem B850675 : Blo 850355 850675 := bstep (se 1 (by rfl) ⟨638006, by rfl⟩ : syracuseStep 850675 = 1276013) B1276013
theorem B1276673 : Blo 850355 1276673 := bstep (se 2 (by rfl) ⟨478752, by rfl⟩ : syracuseStep 1276673 = 957505) B957505
theorem B850691 : Blo 850355 850691 := bstep (se 1 (by rfl) ⟨638018, by rfl⟩ : syracuseStep 850691 = 1276037) B1276037
theorem B850707 : Blo 850355 850707 := bstep (se 1 (by rfl) ⟨638030, by rfl⟩ : syracuseStep 850707 = 1276061) B1276061
theorem B1276691 : Blo 850355 1276691 := bstep (se 1 (by rfl) ⟨957518, by rfl⟩ : syracuseStep 1276691 = 1915037) B1915037
theorem B850723 : Blo 850355 850723 := bstep (se 1 (by rfl) ⟨638042, by rfl⟩ : syracuseStep 850723 = 1276085) B1276085
theorem B1276721 : Blo 850355 1276721 := bstep (se 2 (by rfl) ⟨478770, by rfl⟩ : syracuseStep 1276721 = 957541) B957541
theorem B850739 : Blo 850355 850739 := bstep (se 1 (by rfl) ⟨638054, by rfl⟩ : syracuseStep 850739 = 1276109) B1276109
theorem B850755 : Blo 850355 850755 := bstep (se 1 (by rfl) ⟨638066, by rfl⟩ : syracuseStep 850755 = 1276133) B1276133
theorem B1276739 : Blo 850355 1276739 := bstep (se 1 (by rfl) ⟨957554, by rfl⟩ : syracuseStep 1276739 = 1915109) B1915109
theorem B2161475 : Blo 850355 2161475 := bstep (se 1 (by rfl) ⟨1621106, by rfl⟩ : syracuseStep 2161475 = 3242213) B3242213
theorem B850771 : Blo 850355 850771 := bstep (se 1 (by rfl) ⟨638078, by rfl⟩ : syracuseStep 850771 = 1276157) B1276157
theorem B1276769 : Blo 850355 1276769 := bstep (se 2 (by rfl) ⟨478788, by rfl⟩ : syracuseStep 1276769 = 957577) B957577
theorem B850787 : Blo 850355 850787 := bstep (se 1 (by rfl) ⟨638090, by rfl⟩ : syracuseStep 850787 = 1276181) B1276181
theorem B1440625 : Blo 850355 1440625 := bstep (se 2 (by rfl) ⟨540234, by rfl⟩ : syracuseStep 1440625 = 1080469) B1080469
theorem B850803 : Blo 850355 850803 := bstep (se 1 (by rfl) ⟨638102, by rfl⟩ : syracuseStep 850803 = 1276205) B1276205
theorem B1276787 : Blo 850355 1276787 := bstep (se 1 (by rfl) ⟨957590, by rfl⟩ : syracuseStep 1276787 = 1915181) B1915181
theorem B850819 : Blo 850355 850819 := bstep (se 1 (by rfl) ⟨638114, by rfl⟩ : syracuseStep 850819 = 1276229) B1276229
theorem B1276817 : Blo 850355 1276817 := bstep (se 2 (by rfl) ⟨478806, by rfl⟩ : syracuseStep 1276817 = 957613) B957613
theorem B1080211 : Blo 850355 1080211 := bstep (se 1 (by rfl) ⟨810158, by rfl⟩ : syracuseStep 1080211 = 1620317) B1620317
theorem B850835 : Blo 850355 850835 := bstep (se 1 (by rfl) ⟨638126, by rfl⟩ : syracuseStep 850835 = 1276253) B1276253
theorem B1440659 : Blo 850355 1440659 := bstep (se 1 (by rfl) ⟨1080494, by rfl⟩ : syracuseStep 1440659 = 2160989) B2160989
theorem B850851 : Blo 850355 850851 := bstep (se 1 (by rfl) ⟨638138, by rfl⟩ : syracuseStep 850851 = 1276277) B1276277
theorem B1276835 : Blo 850355 1276835 := bstep (se 1 (by rfl) ⟨957626, by rfl⟩ : syracuseStep 1276835 = 1915253) B1915253
theorem B850867 : Blo 850355 850867 := bstep (se 1 (by rfl) ⟨638150, by rfl⟩ : syracuseStep 850867 = 1276301) B1276301
theorem B1276865 : Blo 850355 1276865 := bstep (se 2 (by rfl) ⟨478824, by rfl⟩ : syracuseStep 1276865 = 957649) B957649
theorem B850883 : Blo 850355 850883 := bstep (se 1 (by rfl) ⟨638162, by rfl⟩ : syracuseStep 850883 = 1276325) B1276325
theorem B850899 : Blo 850355 850899 := bstep (se 1 (by rfl) ⟨638174, by rfl⟩ : syracuseStep 850899 = 1276349) B1276349
theorem B1276883 : Blo 850355 1276883 := bstep (se 1 (by rfl) ⟨957662, by rfl⟩ : syracuseStep 1276883 = 1915325) B1915325
theorem B850915 : Blo 850355 850915 := bstep (se 1 (by rfl) ⟨638186, by rfl⟩ : syracuseStep 850915 = 1276373) B1276373
theorem B2423789 : Blo 850355 2423789 := bstep (se 3 (by rfl) ⟨454460, by rfl⟩ : syracuseStep 2423789 = 908921) B908921
theorem B1276913 : Blo 850355 1276913 := bstep (se 2 (by rfl) ⟨478842, by rfl⟩ : syracuseStep 1276913 = 957685) B957685
theorem B6224881 : Blo 850355 6224881 := bstep (se 2 (by rfl) ⟨2334330, by rfl⟩ : syracuseStep 6224881 = 4668661) B4668661
theorem B1080307 : Blo 850355 1080307 := bstep (se 1 (by rfl) ⟨810230, by rfl⟩ : syracuseStep 1080307 = 1620461) B1620461
theorem B850931 : Blo 850355 850931 := bstep (se 1 (by rfl) ⟨638198, by rfl⟩ : syracuseStep 850931 = 1276397) B1276397
theorem B1211393 : Blo 850355 1211393 := bstep (se 2 (by rfl) ⟨454272, by rfl⟩ : syracuseStep 1211393 = 908545) B908545
theorem B850947 : Blo 850355 850947 := bstep (se 1 (by rfl) ⟨638210, by rfl⟩ : syracuseStep 850947 = 1276421) B1276421
theorem B1276931 : Blo 850355 1276931 := bstep (se 1 (by rfl) ⟨957698, by rfl⟩ : syracuseStep 1276931 = 1915397) B1915397
theorem B2161667 : Blo 850355 2161667 := bstep (se 1 (by rfl) ⟨1621250, by rfl⟩ : syracuseStep 2161667 = 3242501) B3242501
theorem B2587661 : Blo 850355 2587661 := bstep (se 3 (by rfl) ⟨485186, by rfl⟩ : syracuseStep 2587661 = 970373) B970373
theorem B2882573 : Blo 850355 2882573 := bstep (se 3 (by rfl) ⟨540482, by rfl⟩ : syracuseStep 2882573 = 1080965) B1080965
theorem B850963 : Blo 850355 850963 := bstep (se 1 (by rfl) ⟨638222, by rfl⟩ : syracuseStep 850963 = 1276445) B1276445
theorem B1440787 : Blo 850355 1440787 := bstep (se 1 (by rfl) ⟨1080590, by rfl⟩ : syracuseStep 1440787 = 2161181) B2161181
theorem B1276961 : Blo 850355 1276961 := bstep (se 2 (by rfl) ⟨478860, by rfl⟩ : syracuseStep 1276961 = 957721) B957721
theorem B850979 : Blo 850355 850979 := bstep (se 1 (by rfl) ⟨638234, by rfl⟩ : syracuseStep 850979 = 1276469) B1276469
theorem B2423857 : Blo 850355 2423857 := bstep (se 2 (by rfl) ⟨908946, by rfl⟩ : syracuseStep 2423857 = 1817893) B1817893
theorem B850995 : Blo 850355 850995 := bstep (se 1 (by rfl) ⟨638246, by rfl⟩ : syracuseStep 850995 = 1276493) B1276493
theorem B1276979 : Blo 850355 1276979 := bstep (se 1 (by rfl) ⟨957734, by rfl⟩ : syracuseStep 1276979 = 1915469) B1915469
theorem B851011 : Blo 850355 851011 := bstep (se 1 (by rfl) ⟨638258, by rfl⟩ : syracuseStep 851011 = 1276517) B1276517
theorem B2882627 : Blo 850355 2882627 := bstep (se 1 (by rfl) ⟨2161970, by rfl⟩ : syracuseStep 2882627 = 4323941) B4323941
theorem B1211473 : Blo 850355 1211473 := bstep (se 2 (by rfl) ⟨454302, by rfl⟩ : syracuseStep 1211473 = 908605) B908605
theorem B1277009 : Blo 850355 1277009 := bstep (se 2 (by rfl) ⟨478878, by rfl⟩ : syracuseStep 1277009 = 957757) B957757
theorem B851027 : Blo 850355 851027 := bstep (se 1 (by rfl) ⟨638270, by rfl⟩ : syracuseStep 851027 = 1276541) B1276541
theorem B851043 : Blo 850355 851043 := bstep (se 1 (by rfl) ⟨638282, by rfl⟩ : syracuseStep 851043 = 1276565) B1276565
theorem B1277027 : Blo 850355 1277027 := bstep (se 1 (by rfl) ⟨957770, by rfl⟩ : syracuseStep 1277027 = 1915541) B1915541
theorem B851059 : Blo 850355 851059 := bstep (se 1 (by rfl) ⟨638294, by rfl⟩ : syracuseStep 851059 = 1276589) B1276589
theorem B1277057 : Blo 850355 1277057 := bstep (se 2 (by rfl) ⟨478896, by rfl⟩ : syracuseStep 1277057 = 957793) B957793
theorem B851075 : Blo 850355 851075 := bstep (se 1 (by rfl) ⟨638306, by rfl⟩ : syracuseStep 851075 = 1276613) B1276613
theorem B851091 : Blo 850355 851091 := bstep (se 1 (by rfl) ⟨638318, by rfl⟩ : syracuseStep 851091 = 1276637) B1276637
theorem B1277075 : Blo 850355 1277075 := bstep (se 1 (by rfl) ⟨957806, by rfl⟩ : syracuseStep 1277075 = 1915613) B1915613
theorem B1440929 : Blo 850355 1440929 := bstep (se 2 (by rfl) ⟨540348, by rfl⟩ : syracuseStep 1440929 = 1080697) B1080697
theorem B851107 : Blo 850355 851107 := bstep (se 1 (by rfl) ⟨638330, by rfl⟩ : syracuseStep 851107 = 1276661) B1276661
theorem B1277105 : Blo 850355 1277105 := bstep (se 2 (by rfl) ⟨478914, by rfl⟩ : syracuseStep 1277105 = 957829) B957829
theorem B3243185 : Blo 850355 3243185 := bstep (se 2 (by rfl) ⟨1216194, by rfl⟩ : syracuseStep 3243185 = 2432389) B2432389
theorem B851123 : Blo 850355 851123 := bstep (se 1 (by rfl) ⟨638342, by rfl⟩ : syracuseStep 851123 = 1276685) B1276685
theorem B851139 : Blo 850355 851139 := bstep (se 1 (by rfl) ⟨638354, by rfl⟩ : syracuseStep 851139 = 1276709) B1276709
theorem B1277123 : Blo 850355 1277123 := bstep (se 1 (by rfl) ⟨957842, by rfl⟩ : syracuseStep 1277123 = 1915685) B1915685
theorem B851155 : Blo 850355 851155 := bstep (se 1 (by rfl) ⟨638366, by rfl⟩ : syracuseStep 851155 = 1276733) B1276733
theorem B1277153 : Blo 850355 1277153 := bstep (se 2 (by rfl) ⟨478932, by rfl⟩ : syracuseStep 1277153 = 957865) B957865
theorem B851171 : Blo 850355 851171 := bstep (se 1 (by rfl) ⟨638378, by rfl⟩ : syracuseStep 851171 = 1276757) B1276757
theorem B851187 : Blo 850355 851187 := bstep (se 1 (by rfl) ⟨638390, by rfl⟩ : syracuseStep 851187 = 1276781) B1276781
theorem B1277171 : Blo 850355 1277171 := bstep (se 1 (by rfl) ⟨957878, by rfl⟩ : syracuseStep 1277171 = 1915757) B1915757
theorem B851203 : Blo 850355 851203 := bstep (se 1 (by rfl) ⟨638402, by rfl⟩ : syracuseStep 851203 = 1276805) B1276805
theorem B1277201 : Blo 850355 1277201 := bstep (se 2 (by rfl) ⟨478950, by rfl⟩ : syracuseStep 1277201 = 957901) B957901
theorem B851219 : Blo 850355 851219 := bstep (se 1 (by rfl) ⟨638414, by rfl⟩ : syracuseStep 851219 = 1276829) B1276829
theorem B1441057 : Blo 850355 1441057 := bstep (se 2 (by rfl) ⟨540396, by rfl⟩ : syracuseStep 1441057 = 1080793) B1080793
theorem B851235 : Blo 850355 851235 := bstep (se 1 (by rfl) ⟨638426, by rfl⟩ : syracuseStep 851235 = 1276853) B1276853
theorem B1277219 : Blo 850355 1277219 := bstep (se 1 (by rfl) ⟨957914, by rfl⟩ : syracuseStep 1277219 = 1915829) B1915829
theorem B851251 : Blo 850355 851251 := bstep (se 1 (by rfl) ⟨638438, by rfl⟩ : syracuseStep 851251 = 1276877) B1276877
theorem B1277249 : Blo 850355 1277249 := bstep (se 2 (by rfl) ⟨478968, by rfl⟩ : syracuseStep 1277249 = 957937) B957937
theorem B851267 : Blo 850355 851267 := bstep (se 1 (by rfl) ⟨638450, by rfl⟩ : syracuseStep 851267 = 1276901) B1276901
theorem B2424131 : Blo 850355 2424131 := bstep (se 1 (by rfl) ⟨1818098, by rfl⟩ : syracuseStep 2424131 = 3636197) B3636197
theorem B1441091 : Blo 850355 1441091 := bstep (se 1 (by rfl) ⟨1080818, by rfl⟩ : syracuseStep 1441091 = 2161637) B2161637
theorem B2882897 : Blo 850355 2882897 := bstep (se 2 (by rfl) ⟨1081086, by rfl⟩ : syracuseStep 2882897 = 2162173) B2162173
theorem B851283 : Blo 850355 851283 := bstep (se 1 (by rfl) ⟨638462, by rfl⟩ : syracuseStep 851283 = 1276925) B1276925
theorem B1277267 : Blo 850355 1277267 := bstep (se 1 (by rfl) ⟨957950, by rfl⟩ : syracuseStep 1277267 = 1915901) B1915901
theorem B851299 : Blo 850355 851299 := bstep (se 1 (by rfl) ⟨638474, by rfl⟩ : syracuseStep 851299 = 1276949) B1276949
theorem B1277297 : Blo 850355 1277297 := bstep (se 2 (by rfl) ⟨478986, by rfl⟩ : syracuseStep 1277297 = 957973) B957973
theorem B851315 : Blo 850355 851315 := bstep (se 1 (by rfl) ⟨638486, by rfl⟩ : syracuseStep 851315 = 1276973) B1276973
theorem B851331 : Blo 850355 851331 := bstep (se 1 (by rfl) ⟨638498, by rfl⟩ : syracuseStep 851331 = 1276997) B1276997
theorem B1277315 : Blo 850355 1277315 := bstep (se 1 (by rfl) ⟨957986, by rfl⟩ : syracuseStep 1277315 = 1915973) B1915973
theorem B851347 : Blo 850355 851347 := bstep (se 1 (by rfl) ⟨638510, by rfl⟩ : syracuseStep 851347 = 1277021) B1277021
theorem B1277345 : Blo 850355 1277345 := bstep (se 2 (by rfl) ⟨479004, by rfl⟩ : syracuseStep 1277345 = 958009) B958009
theorem B851363 : Blo 850355 851363 := bstep (se 1 (by rfl) ⟨638522, by rfl⟩ : syracuseStep 851363 = 1277045) B1277045
theorem B851379 : Blo 850355 851379 := bstep (se 1 (by rfl) ⟨638534, by rfl⟩ : syracuseStep 851379 = 1277069) B1277069
theorem B1277363 : Blo 850355 1277363 := bstep (se 1 (by rfl) ⟨958022, by rfl⟩ : syracuseStep 1277363 = 1916045) B1916045
theorem B851395 : Blo 850355 851395 := bstep (se 1 (by rfl) ⟨638546, by rfl⟩ : syracuseStep 851395 = 1277093) B1277093
theorem B1441219 : Blo 850355 1441219 := bstep (se 1 (by rfl) ⟨1080914, by rfl⟩ : syracuseStep 1441219 = 2161829) B2161829
theorem B1277393 : Blo 850355 1277393 := bstep (se 2 (by rfl) ⟨479022, by rfl⟩ : syracuseStep 1277393 = 958045) B958045
theorem B851411 : Blo 850355 851411 := bstep (se 1 (by rfl) ⟨638558, by rfl⟩ : syracuseStep 851411 = 1277117) B1277117
theorem B851427 : Blo 850355 851427 := bstep (se 1 (by rfl) ⟨638570, by rfl⟩ : syracuseStep 851427 = 1277141) B1277141
theorem B1277411 : Blo 850355 1277411 := bstep (se 1 (by rfl) ⟨958058, by rfl⟩ : syracuseStep 1277411 = 1916117) B1916117
theorem B1080803 : Blo 850355 1080803 := bstep (se 1 (by rfl) ⟨810602, by rfl⟩ : syracuseStep 1080803 = 1621205) B1621205
theorem B851443 : Blo 850355 851443 := bstep (se 1 (by rfl) ⟨638582, by rfl⟩ : syracuseStep 851443 = 1277165) B1277165
theorem B1277441 : Blo 850355 1277441 := bstep (se 2 (by rfl) ⟨479040, by rfl⟩ : syracuseStep 1277441 = 958081) B958081
theorem B851459 : Blo 850355 851459 := bstep (se 1 (by rfl) ⟨638594, by rfl⟩ : syracuseStep 851459 = 1277189) B1277189
theorem B851475 : Blo 850355 851475 := bstep (se 1 (by rfl) ⟨638606, by rfl⟩ : syracuseStep 851475 = 1277213) B1277213
theorem B1277459 : Blo 850355 1277459 := bstep (se 1 (by rfl) ⟨958094, by rfl⟩ : syracuseStep 1277459 = 1916189) B1916189
theorem B851491 : Blo 850355 851491 := bstep (se 1 (by rfl) ⟨638618, by rfl⟩ : syracuseStep 851491 = 1277237) B1277237
theorem B1277489 : Blo 850355 1277489 := bstep (se 2 (by rfl) ⟨479058, by rfl⟩ : syracuseStep 1277489 = 958117) B958117
theorem B851507 : Blo 850355 851507 := bstep (se 1 (by rfl) ⟨638630, by rfl⟩ : syracuseStep 851507 = 1277261) B1277261
theorem B4324913 : Blo 850355 4324913 := bstep (se 2 (by rfl) ⟨1621842, by rfl⟩ : syracuseStep 4324913 = 3243685) B3243685
theorem B851523 : Blo 850355 851523 := bstep (se 1 (by rfl) ⟨638642, by rfl⟩ : syracuseStep 851523 = 1277285) B1277285
theorem B1277507 : Blo 850355 1277507 := bstep (se 1 (by rfl) ⟨958130, by rfl⟩ : syracuseStep 1277507 = 1916261) B1916261
theorem B1441361 : Blo 850355 1441361 := bstep (se 2 (by rfl) ⟨540510, by rfl⟩ : syracuseStep 1441361 = 1081021) B1081021
theorem B851539 : Blo 850355 851539 := bstep (se 1 (by rfl) ⟨638654, by rfl⟩ : syracuseStep 851539 = 1277309) B1277309
theorem B1277537 : Blo 850355 1277537 := bstep (se 2 (by rfl) ⟨479076, by rfl⟩ : syracuseStep 1277537 = 958153) B958153
theorem B851555 : Blo 850355 851555 := bstep (se 1 (by rfl) ⟨638666, by rfl⟩ : syracuseStep 851555 = 1277333) B1277333
theorem B851571 : Blo 850355 851571 := bstep (se 1 (by rfl) ⟨638678, by rfl⟩ : syracuseStep 851571 = 1277357) B1277357
theorem B1277555 : Blo 850355 1277555 := bstep (se 1 (by rfl) ⟨958166, by rfl⟩ : syracuseStep 1277555 = 1916333) B1916333
theorem B851587 : Blo 850355 851587 := bstep (se 1 (by rfl) ⟨638690, by rfl⟩ : syracuseStep 851587 = 1277381) B1277381
theorem B1277585 : Blo 850355 1277585 := bstep (se 2 (by rfl) ⟨479094, by rfl⟩ : syracuseStep 1277585 = 958189) B958189
theorem B851603 : Blo 850355 851603 := bstep (se 1 (by rfl) ⟨638702, by rfl⟩ : syracuseStep 851603 = 1277405) B1277405
theorem B851619 : Blo 850355 851619 := bstep (se 1 (by rfl) ⟨638714, by rfl⟩ : syracuseStep 851619 = 1277429) B1277429
theorem B1277603 : Blo 850355 1277603 := bstep (se 1 (by rfl) ⟨958202, by rfl⟩ : syracuseStep 1277603 = 1916405) B1916405
theorem B3636913 : Blo 850355 3636913 := bstep (se 2 (by rfl) ⟨1363842, by rfl⟩ : syracuseStep 3636913 = 2727685) B2727685
theorem B851635 : Blo 850355 851635 := bstep (se 1 (by rfl) ⟨638726, by rfl⟩ : syracuseStep 851635 = 1277453) B1277453
theorem B1277633 : Blo 850355 1277633 := bstep (se 2 (by rfl) ⟨479112, by rfl⟩ : syracuseStep 1277633 = 958225) B958225
theorem B851651 : Blo 850355 851651 := bstep (se 1 (by rfl) ⟨638738, by rfl⟩ : syracuseStep 851651 = 1277477) B1277477
theorem B1441489 : Blo 850355 1441489 := bstep (se 2 (by rfl) ⟨540558, by rfl⟩ : syracuseStep 1441489 = 1081117) B1081117
theorem B851667 : Blo 850355 851667 := bstep (se 1 (by rfl) ⟨638750, by rfl⟩ : syracuseStep 851667 = 1277501) B1277501
theorem B1277651 : Blo 850355 1277651 := bstep (se 1 (by rfl) ⟨958238, by rfl⟩ : syracuseStep 1277651 = 1916477) B1916477
theorem B851683 : Blo 850355 851683 := bstep (se 1 (by rfl) ⟨638762, by rfl⟩ : syracuseStep 851683 = 1277525) B1277525
theorem B1277681 : Blo 850355 1277681 := bstep (se 2 (by rfl) ⟨479130, by rfl⟩ : syracuseStep 1277681 = 958261) B958261
theorem B851699 : Blo 850355 851699 := bstep (se 1 (by rfl) ⟨638774, by rfl⟩ : syracuseStep 851699 = 1277549) B1277549
theorem B1441523 : Blo 850355 1441523 := bstep (se 1 (by rfl) ⟨1081142, by rfl⟩ : syracuseStep 1441523 = 2162285) B2162285
theorem B851715 : Blo 850355 851715 := bstep (se 1 (by rfl) ⟨638786, by rfl⟩ : syracuseStep 851715 = 1277573) B1277573
theorem B1277699 : Blo 850355 1277699 := bstep (se 1 (by rfl) ⟨958274, by rfl⟩ : syracuseStep 1277699 = 1916549) B1916549
theorem B851731 : Blo 850355 851731 := bstep (se 1 (by rfl) ⟨638798, by rfl⟩ : syracuseStep 851731 = 1277597) B1277597
theorem B1277729 : Blo 850355 1277729 := bstep (se 2 (by rfl) ⟨479148, by rfl⟩ : syracuseStep 1277729 = 958297) B958297
theorem B851747 : Blo 850355 851747 := bstep (se 1 (by rfl) ⟨638810, by rfl⟩ : syracuseStep 851747 = 1277621) B1277621
theorem B851763 : Blo 850355 851763 := bstep (se 1 (by rfl) ⟨638822, by rfl⟩ : syracuseStep 851763 = 1277645) B1277645
theorem B1277747 : Blo 850355 1277747 := bstep (se 1 (by rfl) ⟨958310, by rfl⟩ : syracuseStep 1277747 = 1916621) B1916621
theorem B10485557 : Blo 850355 10485557 := bstep (se 5 (by rfl) ⟨491510, by rfl⟩ : syracuseStep 10485557 = 983021) B983021
theorem B851779 : Blo 850355 851779 := bstep (se 1 (by rfl) ⟨638834, by rfl⟩ : syracuseStep 851779 = 1277669) B1277669
theorem B1277777 : Blo 850355 1277777 := bstep (se 2 (by rfl) ⟨479166, by rfl⟩ : syracuseStep 1277777 = 958333) B958333
theorem B851795 : Blo 850355 851795 := bstep (se 1 (by rfl) ⟨638846, by rfl⟩ : syracuseStep 851795 = 1277693) B1277693
theorem B1212259 : Blo 850355 1212259 := bstep (se 1 (by rfl) ⟨909194, by rfl⟩ : syracuseStep 1212259 = 1818389) B1818389
theorem B851811 : Blo 850355 851811 := bstep (se 1 (by rfl) ⟨638858, by rfl⟩ : syracuseStep 851811 = 1277717) B1277717
theorem B1277795 : Blo 850355 1277795 := bstep (se 1 (by rfl) ⟨958346, by rfl⟩ : syracuseStep 1277795 = 1916693) B1916693
theorem B2883437 : Blo 850355 2883437 := bstep (se 3 (by rfl) ⟨540644, by rfl⟩ : syracuseStep 2883437 = 1081289) B1081289
theorem B851827 : Blo 850355 851827 := bstep (se 1 (by rfl) ⟨638870, by rfl⟩ : syracuseStep 851827 = 1277741) B1277741
theorem B1441651 : Blo 850355 1441651 := bstep (se 1 (by rfl) ⟨1081238, by rfl⟩ : syracuseStep 1441651 = 2162477) B2162477
theorem B1277825 : Blo 850355 1277825 := bstep (se 2 (by rfl) ⟨479184, by rfl⟩ : syracuseStep 1277825 = 958369) B958369
theorem B851843 : Blo 850355 851843 := bstep (se 1 (by rfl) ⟨638882, by rfl⟩ : syracuseStep 851843 = 1277765) B1277765
theorem B851859 : Blo 850355 851859 := bstep (se 1 (by rfl) ⟨638894, by rfl⟩ : syracuseStep 851859 = 1277789) B1277789
theorem B1277843 : Blo 850355 1277843 := bstep (se 1 (by rfl) ⟨958382, by rfl⟩ : syracuseStep 1277843 = 1916765) B1916765
theorem B851875 : Blo 850355 851875 := bstep (se 1 (by rfl) ⟨638906, by rfl⟩ : syracuseStep 851875 = 1277813) B1277813
theorem B1277873 : Blo 850355 1277873 := bstep (se 2 (by rfl) ⟨479202, by rfl⟩ : syracuseStep 1277873 = 958405) B958405
theorem B851891 : Blo 850355 851891 := bstep (se 1 (by rfl) ⟨638918, by rfl⟩ : syracuseStep 851891 = 1277837) B1277837
theorem B851907 : Blo 850355 851907 := bstep (se 1 (by rfl) ⟨638930, by rfl⟩ : syracuseStep 851907 = 1277861) B1277861
theorem B1277891 : Blo 850355 1277891 := bstep (se 1 (by rfl) ⟨958418, by rfl⟩ : syracuseStep 1277891 = 1916837) B1916837
theorem B851923 : Blo 850355 851923 := bstep (se 1 (by rfl) ⟨638942, by rfl⟩ : syracuseStep 851923 = 1277885) B1277885
theorem B1277921 : Blo 850355 1277921 := bstep (se 2 (by rfl) ⟨479220, by rfl⟩ : syracuseStep 1277921 = 958441) B958441
theorem B851939 : Blo 850355 851939 := bstep (se 1 (by rfl) ⟨638954, by rfl⟩ : syracuseStep 851939 = 1277909) B1277909
theorem B851955 : Blo 850355 851955 := bstep (se 1 (by rfl) ⟨638966, by rfl⟩ : syracuseStep 851955 = 1277933) B1277933
theorem B1277939 : Blo 850355 1277939 := bstep (se 1 (by rfl) ⟨958454, by rfl⟩ : syracuseStep 1277939 = 1916909) B1916909
theorem B1277963 : Blo 850355 1277963 := bstep (se 1 (by rfl) ⟨958472, by rfl⟩ : syracuseStep 1277963 = 1916945) B1916945
theorem B851979 : Blo 850355 851979 := bstep (se 1 (by rfl) ⟨638984, by rfl⟩ : syracuseStep 851979 = 1277969) B1277969
theorem B1277975 : Blo 850355 1277975 := bstep (se 1 (by rfl) ⟨958481, by rfl⟩ : syracuseStep 1277975 = 1916963) B1916963
theorem B851991 : Blo 850355 851991 := bstep (se 1 (by rfl) ⟨638993, by rfl⟩ : syracuseStep 851991 = 1277987) B1277987
theorem B852011 : Blo 850355 852011 := bstep (se 1 (by rfl) ⟨639008, by rfl⟩ : syracuseStep 852011 = 1278017) B1278017
theorem B5832749 : Blo 850355 5832749 := bstep (se 3 (by rfl) ⟨1093640, by rfl⟩ : syracuseStep 5832749 = 2187281) B2187281
theorem B852023 : Blo 850355 852023 := bstep (se 1 (by rfl) ⟨639017, by rfl⟩ : syracuseStep 852023 = 1278035) B1278035
theorem B852043 : Blo 850355 852043 := bstep (se 1 (by rfl) ⟨639032, by rfl⟩ : syracuseStep 852043 = 1278065) B1278065
theorem B852055 : Blo 850355 852055 := bstep (se 1 (by rfl) ⟨639041, by rfl⟩ : syracuseStep 852055 = 1278083) B1278083
theorem B1278041 : Blo 850355 1278041 := bstep (se 2 (by rfl) ⟨479265, by rfl⟩ : syracuseStep 1278041 = 958531) B958531
theorem B852075 : Blo 850355 852075 := bstep (se 1 (by rfl) ⟨639056, by rfl⟩ : syracuseStep 852075 = 1278113) B1278113
theorem B852087 : Blo 850355 852087 := bstep (se 1 (by rfl) ⟨639065, by rfl⟩ : syracuseStep 852087 = 1278131) B1278131
theorem B852107 : Blo 850355 852107 := bstep (se 1 (by rfl) ⟨639080, by rfl⟩ : syracuseStep 852107 = 1278161) B1278161
theorem B852119 : Blo 850355 852119 := bstep (se 1 (by rfl) ⟨639089, by rfl⟩ : syracuseStep 852119 = 1278179) B1278179
theorem B852139 : Blo 850355 852139 := bstep (se 1 (by rfl) ⟨639104, by rfl⟩ : syracuseStep 852139 = 1278209) B1278209
theorem B852151 : Blo 850355 852151 := bstep (se 1 (by rfl) ⟨639113, by rfl⟩ : syracuseStep 852151 = 1278227) B1278227
theorem B1278155 : Blo 850355 1278155 := bstep (se 1 (by rfl) ⟨958616, by rfl⟩ : syracuseStep 1278155 = 1917233) B1917233
theorem B852171 : Blo 850355 852171 := bstep (se 1 (by rfl) ⟨639128, by rfl⟩ : syracuseStep 852171 = 1278257) B1278257
theorem B1278167 : Blo 850355 1278167 := bstep (se 1 (by rfl) ⟨958625, by rfl⟩ : syracuseStep 1278167 = 1917251) B1917251
theorem B852183 : Blo 850355 852183 := bstep (se 1 (by rfl) ⟨639137, by rfl⟩ : syracuseStep 852183 = 1278275) B1278275
theorem B4096217 : Blo 850355 4096217 := bstep (se 2 (by rfl) ⟨1536081, by rfl⟩ : syracuseStep 4096217 = 3072163) B3072163
theorem B852203 : Blo 850355 852203 := bstep (se 1 (by rfl) ⟨639152, by rfl⟩ : syracuseStep 852203 = 1278305) B1278305
theorem B852215 : Blo 850355 852215 := bstep (se 1 (by rfl) ⟨639161, by rfl⟩ : syracuseStep 852215 = 1278323) B1278323
theorem B17268997 : Blo 850355 17268997 := bstep (se 4 (by rfl) ⟨1618968, by rfl⟩ : syracuseStep 17268997 = 3237937) B3237937
theorem B852235 : Blo 850355 852235 := bstep (se 1 (by rfl) ⟨639176, by rfl⟩ : syracuseStep 852235 = 1278353) B1278353
theorem B852247 : Blo 850355 852247 := bstep (se 1 (by rfl) ⟨639185, by rfl⟩ : syracuseStep 852247 = 1278371) B1278371
theorem B1278233 : Blo 850355 1278233 := bstep (se 2 (by rfl) ⟨479337, by rfl⟩ : syracuseStep 1278233 = 958675) B958675
theorem B852267 : Blo 850355 852267 := bstep (se 1 (by rfl) ⟨639200, by rfl⟩ : syracuseStep 852267 = 1278401) B1278401
theorem B852279 : Blo 850355 852279 := bstep (se 1 (by rfl) ⟨639209, by rfl⟩ : syracuseStep 852279 = 1278419) B1278419
theorem B852299 : Blo 850355 852299 := bstep (se 1 (by rfl) ⟨639224, by rfl⟩ : syracuseStep 852299 = 1278449) B1278449
theorem B852311 : Blo 850355 852311 := bstep (se 1 (by rfl) ⟨639233, by rfl⟩ : syracuseStep 852311 = 1278467) B1278467
theorem B852331 : Blo 850355 852331 := bstep (se 1 (by rfl) ⟨639248, by rfl⟩ : syracuseStep 852331 = 1278497) B1278497
theorem B852343 : Blo 850355 852343 := bstep (se 1 (by rfl) ⟨639257, by rfl⟩ : syracuseStep 852343 = 1278515) B1278515
theorem B1278347 : Blo 850355 1278347 := bstep (se 1 (by rfl) ⟨958760, by rfl⟩ : syracuseStep 1278347 = 1917521) B1917521
theorem B852363 : Blo 850355 852363 := bstep (se 1 (by rfl) ⟨639272, by rfl⟩ : syracuseStep 852363 = 1278545) B1278545
theorem B3637649 : Blo 850355 3637649 := bstep (se 2 (by rfl) ⟨1364118, by rfl⟩ : syracuseStep 3637649 = 2728237) B2728237
theorem B1212823 : Blo 850355 1212823 := bstep (se 1 (by rfl) ⟨909617, by rfl⟩ : syracuseStep 1212823 = 1819235) B1819235
theorem B1278359 : Blo 850355 1278359 := bstep (se 1 (by rfl) ⟨958769, by rfl⟩ : syracuseStep 1278359 = 1917539) B1917539
theorem B852375 : Blo 850355 852375 := bstep (se 1 (by rfl) ⟨639281, by rfl⟩ : syracuseStep 852375 = 1278563) B1278563
theorem B852395 : Blo 850355 852395 := bstep (se 1 (by rfl) ⟨639296, by rfl⟩ : syracuseStep 852395 = 1278593) B1278593
theorem B852407 : Blo 850355 852407 := bstep (se 1 (by rfl) ⟨639305, by rfl⟩ : syracuseStep 852407 = 1278611) B1278611
theorem B852427 : Blo 850355 852427 := bstep (se 1 (by rfl) ⟨639320, by rfl⟩ : syracuseStep 852427 = 1278641) B1278641
theorem B852439 : Blo 850355 852439 := bstep (se 1 (by rfl) ⟨639329, by rfl⟩ : syracuseStep 852439 = 1278659) B1278659
theorem B1278425 : Blo 850355 1278425 := bstep (se 2 (by rfl) ⟨479409, by rfl⟩ : syracuseStep 1278425 = 958819) B958819
theorem B852459 : Blo 850355 852459 := bstep (se 1 (by rfl) ⟨639344, by rfl⟩ : syracuseStep 852459 = 1278689) B1278689
theorem B852471 : Blo 850355 852471 := bstep (se 1 (by rfl) ⟨639353, by rfl⟩ : syracuseStep 852471 = 1278707) B1278707
theorem B852491 : Blo 850355 852491 := bstep (se 1 (by rfl) ⟨639368, by rfl⟩ : syracuseStep 852491 = 1278737) B1278737
theorem B852503 : Blo 850355 852503 := bstep (se 1 (by rfl) ⟨639377, by rfl⟩ : syracuseStep 852503 = 1278755) B1278755
theorem B852523 : Blo 850355 852523 := bstep (se 1 (by rfl) ⟨639392, by rfl⟩ : syracuseStep 852523 = 1278785) B1278785
theorem B852535 : Blo 850355 852535 := bstep (se 1 (by rfl) ⟨639401, by rfl⟩ : syracuseStep 852535 = 1278803) B1278803
theorem B1278539 : Blo 850355 1278539 := bstep (se 1 (by rfl) ⟨958904, by rfl⟩ : syracuseStep 1278539 = 1917809) B1917809
theorem B852555 : Blo 850355 852555 := bstep (se 1 (by rfl) ⟨639416, by rfl⟩ : syracuseStep 852555 = 1278833) B1278833
theorem B1278551 : Blo 850355 1278551 := bstep (se 1 (by rfl) ⟨958913, by rfl⟩ : syracuseStep 1278551 = 1917827) B1917827
theorem B852567 : Blo 850355 852567 := bstep (se 1 (by rfl) ⟨639425, by rfl⟩ : syracuseStep 852567 = 1278851) B1278851
theorem B852587 : Blo 850355 852587 := bstep (se 1 (by rfl) ⟨639440, by rfl⟩ : syracuseStep 852587 = 1278881) B1278881
theorem B852599 : Blo 850355 852599 := bstep (se 1 (by rfl) ⟨639449, by rfl⟩ : syracuseStep 852599 = 1278899) B1278899
theorem B852619 : Blo 850355 852619 := bstep (se 1 (by rfl) ⟨639464, by rfl⟩ : syracuseStep 852619 = 1278929) B1278929
theorem B852631 : Blo 850355 852631 := bstep (se 1 (by rfl) ⟨639473, by rfl⟩ : syracuseStep 852631 = 1278947) B1278947
theorem B1278617 : Blo 850355 1278617 := bstep (se 2 (by rfl) ⟨479481, by rfl⟩ : syracuseStep 1278617 = 958963) B958963
theorem B852651 : Blo 850355 852651 := bstep (se 1 (by rfl) ⟨639488, by rfl⟩ : syracuseStep 852651 = 1278977) B1278977
theorem B852663 : Blo 850355 852663 := bstep (se 1 (by rfl) ⟨639497, by rfl⟩ : syracuseStep 852663 = 1278995) B1278995
theorem B852683 : Blo 850355 852683 := bstep (se 1 (by rfl) ⟨639512, by rfl⟩ : syracuseStep 852683 = 1279025) B1279025
theorem B852695 : Blo 850355 852695 := bstep (se 1 (by rfl) ⟨639521, by rfl⟩ : syracuseStep 852695 = 1279043) B1279043
theorem B2425565 : Blo 850355 2425565 := bstep (se 3 (by rfl) ⟨454793, by rfl⟩ : syracuseStep 2425565 = 909587) B909587
theorem B852715 : Blo 850355 852715 := bstep (se 1 (by rfl) ⟨639536, by rfl⟩ : syracuseStep 852715 = 1279073) B1279073
theorem B852727 : Blo 850355 852727 := bstep (se 1 (by rfl) ⟨639545, by rfl⟩ : syracuseStep 852727 = 1279091) B1279091
theorem B1278731 : Blo 850355 1278731 := bstep (se 1 (by rfl) ⟨959048, by rfl⟩ : syracuseStep 1278731 = 1918097) B1918097
theorem B852747 : Blo 850355 852747 := bstep (se 1 (by rfl) ⟨639560, by rfl⟩ : syracuseStep 852747 = 1279121) B1279121
theorem B3736343 : Blo 850355 3736343 := bstep (se 1 (by rfl) ⟨2802257, by rfl⟩ : syracuseStep 3736343 = 5604515) B5604515
theorem B1278743 : Blo 850355 1278743 := bstep (se 1 (by rfl) ⟨959057, by rfl⟩ : syracuseStep 1278743 = 1918115) B1918115
theorem B852759 : Blo 850355 852759 := bstep (se 1 (by rfl) ⟨639569, by rfl⟩ : syracuseStep 852759 = 1279139) B1279139
theorem B852779 : Blo 850355 852779 := bstep (se 1 (by rfl) ⟨639584, by rfl⟩ : syracuseStep 852779 = 1279169) B1279169
theorem B59081525 : Blo 850355 59081525 := bstep (se 5 (by rfl) ⟨2769446, by rfl⟩ : syracuseStep 59081525 = 5538893) B5538893
theorem B852791 : Blo 850355 852791 := bstep (se 1 (by rfl) ⟨639593, by rfl⟩ : syracuseStep 852791 = 1279187) B1279187
theorem B7275329 : Blo 850355 7275329 := bstep (se 2 (by rfl) ⟨2728248, by rfl⟩ : syracuseStep 7275329 = 5456497) B5456497
theorem B852811 : Blo 850355 852811 := bstep (se 1 (by rfl) ⟨639608, by rfl⟩ : syracuseStep 852811 = 1279217) B1279217
theorem B852823 : Blo 850355 852823 := bstep (se 1 (by rfl) ⟨639617, by rfl⟩ : syracuseStep 852823 = 1279235) B1279235
theorem B1278809 : Blo 850355 1278809 := bstep (se 2 (by rfl) ⟨479553, by rfl⟩ : syracuseStep 1278809 = 959107) B959107
theorem B852843 : Blo 850355 852843 := bstep (se 1 (by rfl) ⟨639632, by rfl⟩ : syracuseStep 852843 = 1279265) B1279265
theorem B852855 : Blo 850355 852855 := bstep (se 1 (by rfl) ⟨639641, by rfl⟩ : syracuseStep 852855 = 1279283) B1279283
theorem B852875 : Blo 850355 852875 := bstep (se 1 (by rfl) ⟨639656, by rfl⟩ : syracuseStep 852875 = 1279313) B1279313
theorem B852887 : Blo 850355 852887 := bstep (se 1 (by rfl) ⟨639665, by rfl⟩ : syracuseStep 852887 = 1279331) B1279331
theorem B852907 : Blo 850355 852907 := bstep (se 1 (by rfl) ⟨639680, by rfl⟩ : syracuseStep 852907 = 1279361) B1279361
theorem B852919 : Blo 850355 852919 := bstep (se 1 (by rfl) ⟨639689, by rfl⟩ : syracuseStep 852919 = 1279379) B1279379
theorem B1278923 : Blo 850355 1278923 := bstep (se 1 (by rfl) ⟨959192, by rfl⟩ : syracuseStep 1278923 = 1918385) B1918385
theorem B852939 : Blo 850355 852939 := bstep (se 1 (by rfl) ⟨639704, by rfl⟩ : syracuseStep 852939 = 1279409) B1279409
theorem B1278935 : Blo 850355 1278935 := bstep (se 1 (by rfl) ⟨959201, by rfl⟩ : syracuseStep 1278935 = 1918403) B1918403
theorem B852951 : Blo 850355 852951 := bstep (se 1 (by rfl) ⟨639713, by rfl⟩ : syracuseStep 852951 = 1279427) B1279427
theorem B852971 : Blo 850355 852971 := bstep (se 1 (by rfl) ⟨639728, by rfl⟩ : syracuseStep 852971 = 1279457) B1279457
theorem B852983 : Blo 850355 852983 := bstep (se 1 (by rfl) ⟨639737, by rfl⟩ : syracuseStep 852983 = 1279475) B1279475
theorem B853003 : Blo 850355 853003 := bstep (se 1 (by rfl) ⟨639752, by rfl⟩ : syracuseStep 853003 = 1279505) B1279505
theorem B853015 : Blo 850355 853015 := bstep (se 1 (by rfl) ⟨639761, by rfl⟩ : syracuseStep 853015 = 1279523) B1279523
theorem B1279001 : Blo 850355 1279001 := bstep (se 2 (by rfl) ⟨479625, by rfl⟩ : syracuseStep 1279001 = 959251) B959251
theorem B853035 : Blo 850355 853035 := bstep (se 1 (by rfl) ⟨639776, by rfl⟩ : syracuseStep 853035 = 1279553) B1279553
theorem B853047 : Blo 850355 853047 := bstep (se 1 (by rfl) ⟨639785, by rfl⟩ : syracuseStep 853047 = 1279571) B1279571
theorem B853067 : Blo 850355 853067 := bstep (se 1 (by rfl) ⟨639800, by rfl⟩ : syracuseStep 853067 = 1279601) B1279601
theorem B853079 : Blo 850355 853079 := bstep (se 1 (by rfl) ⟨639809, by rfl⟩ : syracuseStep 853079 = 1279619) B1279619
theorem B853099 : Blo 850355 853099 := bstep (se 1 (by rfl) ⟨639824, by rfl⟩ : syracuseStep 853099 = 1279649) B1279649
theorem B853111 : Blo 850355 853111 := bstep (se 1 (by rfl) ⟨639833, by rfl⟩ : syracuseStep 853111 = 1279667) B1279667
theorem B14582915 : Blo 850355 14582915 := bstep (se 1 (by rfl) ⟨10937186, by rfl⟩ : syracuseStep 14582915 = 21874373) B21874373
theorem B1279115 : Blo 850355 1279115 := bstep (se 1 (by rfl) ⟨959336, by rfl⟩ : syracuseStep 1279115 = 1918673) B1918673
theorem B853131 : Blo 850355 853131 := bstep (se 1 (by rfl) ⟨639848, by rfl⟩ : syracuseStep 853131 = 1279697) B1279697
theorem B1279127 : Blo 850355 1279127 := bstep (se 1 (by rfl) ⟨959345, by rfl⟩ : syracuseStep 1279127 = 1918691) B1918691
theorem B853143 : Blo 850355 853143 := bstep (se 1 (by rfl) ⟨639857, by rfl⟩ : syracuseStep 853143 = 1279715) B1279715
theorem B853163 : Blo 850355 853163 := bstep (se 1 (by rfl) ⟨639872, by rfl⟩ : syracuseStep 853163 = 1279745) B1279745
theorem B853175 : Blo 850355 853175 := bstep (se 1 (by rfl) ⟨639881, by rfl⟩ : syracuseStep 853175 = 1279763) B1279763
theorem B1213643 : Blo 850355 1213643 := bstep (se 1 (by rfl) ⟨910232, by rfl⟩ : syracuseStep 1213643 = 1820465) B1820465
theorem B853195 : Blo 850355 853195 := bstep (se 1 (by rfl) ⟨639896, by rfl⟩ : syracuseStep 853195 = 1279793) B1279793
theorem B853207 : Blo 850355 853207 := bstep (se 1 (by rfl) ⟨639905, by rfl⟩ : syracuseStep 853207 = 1279811) B1279811
theorem B1279193 : Blo 850355 1279193 := bstep (se 2 (by rfl) ⟨479697, by rfl⟩ : syracuseStep 1279193 = 959395) B959395
theorem B853227 : Blo 850355 853227 := bstep (se 1 (by rfl) ⟨639920, by rfl⟩ : syracuseStep 853227 = 1279841) B1279841
theorem B853239 : Blo 850355 853239 := bstep (se 1 (by rfl) ⟨639929, by rfl⟩ : syracuseStep 853239 = 1279859) B1279859
theorem B853259 : Blo 850355 853259 := bstep (se 1 (by rfl) ⟨639944, by rfl⟩ : syracuseStep 853259 = 1279889) B1279889
theorem B853271 : Blo 850355 853271 := bstep (se 1 (by rfl) ⟨639953, by rfl⟩ : syracuseStep 853271 = 1279907) B1279907
theorem B853291 : Blo 850355 853291 := bstep (se 1 (by rfl) ⟨639968, by rfl⟩ : syracuseStep 853291 = 1279937) B1279937
theorem B853303 : Blo 850355 853303 := bstep (se 1 (by rfl) ⟨639977, by rfl⟩ : syracuseStep 853303 = 1279955) B1279955
theorem B1279307 : Blo 850355 1279307 := bstep (se 1 (by rfl) ⟨959480, by rfl⟩ : syracuseStep 1279307 = 1918961) B1918961
theorem B853323 : Blo 850355 853323 := bstep (se 1 (by rfl) ⟨639992, by rfl⟩ : syracuseStep 853323 = 1279985) B1279985
theorem B1279319 : Blo 850355 1279319 := bstep (se 1 (by rfl) ⟨959489, by rfl⟩ : syracuseStep 1279319 = 1918979) B1918979
theorem B853335 : Blo 850355 853335 := bstep (se 1 (by rfl) ⟨640001, by rfl⟩ : syracuseStep 853335 = 1280003) B1280003
theorem B2131289 : Blo 850355 2131289 := bstep (se 2 (by rfl) ⟨799233, by rfl⟩ : syracuseStep 2131289 = 1598467) B1598467
theorem B3638621 : Blo 850355 3638621 := bstep (se 3 (by rfl) ⟨682241, by rfl⟩ : syracuseStep 3638621 = 1364483) B1364483
theorem B853355 : Blo 850355 853355 := bstep (se 1 (by rfl) ⟨640016, by rfl⟩ : syracuseStep 853355 = 1280033) B1280033
theorem B853367 : Blo 850355 853367 := bstep (se 1 (by rfl) ⟨640025, by rfl⟩ : syracuseStep 853367 = 1280051) B1280051
theorem B853387 : Blo 850355 853387 := bstep (se 1 (by rfl) ⟨640040, by rfl⟩ : syracuseStep 853387 = 1280081) B1280081
theorem B853399 : Blo 850355 853399 := bstep (se 1 (by rfl) ⟨640049, by rfl⟩ : syracuseStep 853399 = 1280099) B1280099
theorem B1279385 : Blo 850355 1279385 := bstep (se 2 (by rfl) ⟨479769, by rfl⟩ : syracuseStep 1279385 = 959539) B959539
theorem B853419 : Blo 850355 853419 := bstep (se 1 (by rfl) ⟨640064, by rfl⟩ : syracuseStep 853419 = 1280129) B1280129
theorem B853431 : Blo 850355 853431 := bstep (se 1 (by rfl) ⟨640073, by rfl⟩ : syracuseStep 853431 = 1280147) B1280147
theorem B853451 : Blo 850355 853451 := bstep (se 1 (by rfl) ⟨640088, by rfl⟩ : syracuseStep 853451 = 1280177) B1280177
theorem B853463 : Blo 850355 853463 := bstep (se 1 (by rfl) ⟨640097, by rfl⟩ : syracuseStep 853463 = 1280195) B1280195
theorem B853483 : Blo 850355 853483 := bstep (se 1 (by rfl) ⟨640112, by rfl⟩ : syracuseStep 853483 = 1280225) B1280225
theorem B853495 : Blo 850355 853495 := bstep (se 1 (by rfl) ⟨640121, by rfl⟩ : syracuseStep 853495 = 1280243) B1280243
theorem B1279499 : Blo 850355 1279499 := bstep (se 1 (by rfl) ⟨959624, by rfl⟩ : syracuseStep 1279499 = 1919249) B1919249
theorem B853515 : Blo 850355 853515 := bstep (se 1 (by rfl) ⟨640136, by rfl⟩ : syracuseStep 853515 = 1280273) B1280273
theorem B1279511 : Blo 850355 1279511 := bstep (se 1 (by rfl) ⟨959633, by rfl⟩ : syracuseStep 1279511 = 1919267) B1919267
theorem B853527 : Blo 850355 853527 := bstep (se 1 (by rfl) ⟨640145, by rfl⟩ : syracuseStep 853527 = 1280291) B1280291
theorem B853547 : Blo 850355 853547 := bstep (se 1 (by rfl) ⟨640160, by rfl⟩ : syracuseStep 853547 = 1280321) B1280321
theorem B853559 : Blo 850355 853559 := bstep (se 1 (by rfl) ⟨640169, by rfl⟩ : syracuseStep 853559 = 1280339) B1280339
theorem B853579 : Blo 850355 853579 := bstep (se 1 (by rfl) ⟨640184, by rfl⟩ : syracuseStep 853579 = 1280369) B1280369
theorem B853591 : Blo 850355 853591 := bstep (se 1 (by rfl) ⟨640193, by rfl⟩ : syracuseStep 853591 = 1280387) B1280387
theorem B1279577 : Blo 850355 1279577 := bstep (se 2 (by rfl) ⟨479841, by rfl⟩ : syracuseStep 1279577 = 959683) B959683
theorem B853611 : Blo 850355 853611 := bstep (se 1 (by rfl) ⟨640208, by rfl⟩ : syracuseStep 853611 = 1280417) B1280417
theorem B853623 : Blo 850355 853623 := bstep (se 1 (by rfl) ⟨640217, by rfl⟩ : syracuseStep 853623 = 1280435) B1280435
theorem B853643 : Blo 850355 853643 := bstep (se 1 (by rfl) ⟨640232, by rfl⟩ : syracuseStep 853643 = 1280465) B1280465
theorem B853655 : Blo 850355 853655 := bstep (se 1 (by rfl) ⟨640241, by rfl⟩ : syracuseStep 853655 = 1280483) B1280483
theorem B853675 : Blo 850355 853675 := bstep (se 1 (by rfl) ⟨640256, by rfl⟩ : syracuseStep 853675 = 1280513) B1280513
theorem B853687 : Blo 850355 853687 := bstep (se 1 (by rfl) ⟨640265, by rfl⟩ : syracuseStep 853687 = 1280531) B1280531
theorem B1279691 : Blo 850355 1279691 := bstep (se 1 (by rfl) ⟨959768, by rfl⟩ : syracuseStep 1279691 = 1919537) B1919537
theorem B853707 : Blo 850355 853707 := bstep (se 1 (by rfl) ⟨640280, by rfl⟩ : syracuseStep 853707 = 1280561) B1280561
theorem B1279703 : Blo 850355 1279703 := bstep (se 1 (by rfl) ⟨959777, by rfl⟩ : syracuseStep 1279703 = 1919555) B1919555
theorem B853719 : Blo 850355 853719 := bstep (se 1 (by rfl) ⟨640289, by rfl⟩ : syracuseStep 853719 = 1280579) B1280579
theorem B853739 : Blo 850355 853739 := bstep (se 1 (by rfl) ⟨640304, by rfl⟩ : syracuseStep 853739 = 1280609) B1280609
theorem B853751 : Blo 850355 853751 := bstep (se 1 (by rfl) ⟨640313, by rfl⟩ : syracuseStep 853751 = 1280627) B1280627
theorem B853771 : Blo 850355 853771 := bstep (se 1 (by rfl) ⟨640328, by rfl⟩ : syracuseStep 853771 = 1280657) B1280657
theorem B853783 : Blo 850355 853783 := bstep (se 1 (by rfl) ⟨640337, by rfl⟩ : syracuseStep 853783 = 1280675) B1280675
theorem B1279769 : Blo 850355 1279769 := bstep (se 2 (by rfl) ⟨479913, by rfl⟩ : syracuseStep 1279769 = 959827) B959827
theorem B853803 : Blo 850355 853803 := bstep (se 1 (by rfl) ⟨640352, by rfl⟩ : syracuseStep 853803 = 1280705) B1280705
theorem B853815 : Blo 850355 853815 := bstep (se 1 (by rfl) ⟨640361, by rfl⟩ : syracuseStep 853815 = 1280723) B1280723
theorem B853835 : Blo 850355 853835 := bstep (se 1 (by rfl) ⟨640376, by rfl⟩ : syracuseStep 853835 = 1280753) B1280753
theorem B853847 : Blo 850355 853847 := bstep (se 1 (by rfl) ⟨640385, by rfl⟩ : syracuseStep 853847 = 1280771) B1280771
theorem B853867 : Blo 850355 853867 := bstep (se 1 (by rfl) ⟨640400, by rfl⟩ : syracuseStep 853867 = 1280801) B1280801
theorem B853879 : Blo 850355 853879 := bstep (se 1 (by rfl) ⟨640409, by rfl⟩ : syracuseStep 853879 = 1280819) B1280819
theorem B1279883 : Blo 850355 1279883 := bstep (se 1 (by rfl) ⟨959912, by rfl⟩ : syracuseStep 1279883 = 1919825) B1919825
theorem B853899 : Blo 850355 853899 := bstep (se 1 (by rfl) ⟨640424, by rfl⟩ : syracuseStep 853899 = 1280849) B1280849
theorem B1279895 : Blo 850355 1279895 := bstep (se 1 (by rfl) ⟨959921, by rfl⟩ : syracuseStep 1279895 = 1919843) B1919843
theorem B853911 : Blo 850355 853911 := bstep (se 1 (by rfl) ⟨640433, by rfl⟩ : syracuseStep 853911 = 1280867) B1280867
theorem B853931 : Blo 850355 853931 := bstep (se 1 (by rfl) ⟨640448, by rfl⟩ : syracuseStep 853931 = 1280897) B1280897
theorem B853943 : Blo 850355 853943 := bstep (se 1 (by rfl) ⟨640457, by rfl⟩ : syracuseStep 853943 = 1280915) B1280915
theorem B853963 : Blo 850355 853963 := bstep (se 1 (by rfl) ⟨640472, by rfl⟩ : syracuseStep 853963 = 1280945) B1280945
theorem B853975 : Blo 850355 853975 := bstep (se 1 (by rfl) ⟨640481, by rfl⟩ : syracuseStep 853975 = 1280963) B1280963
theorem B1279961 : Blo 850355 1279961 := bstep (se 2 (by rfl) ⟨479985, by rfl⟩ : syracuseStep 1279961 = 959971) B959971
theorem B853995 : Blo 850355 853995 := bstep (se 1 (by rfl) ⟨640496, by rfl⟩ : syracuseStep 853995 = 1280993) B1280993
theorem B854007 : Blo 850355 854007 := bstep (se 1 (by rfl) ⟨640505, by rfl⟩ : syracuseStep 854007 = 1281011) B1281011
theorem B854027 : Blo 850355 854027 := bstep (se 1 (by rfl) ⟨640520, by rfl⟩ : syracuseStep 854027 = 1281041) B1281041
theorem B854039 : Blo 850355 854039 := bstep (se 1 (by rfl) ⟨640529, by rfl⟩ : syracuseStep 854039 = 1281059) B1281059
theorem B854059 : Blo 850355 854059 := bstep (se 1 (by rfl) ⟨640544, by rfl⟩ : syracuseStep 854059 = 1281089) B1281089
theorem B854071 : Blo 850355 854071 := bstep (se 1 (by rfl) ⟨640553, by rfl⟩ : syracuseStep 854071 = 1281107) B1281107
theorem B1280075 : Blo 850355 1280075 := bstep (se 1 (by rfl) ⟨960056, by rfl⟩ : syracuseStep 1280075 = 1920113) B1920113
theorem B854091 : Blo 850355 854091 := bstep (se 1 (by rfl) ⟨640568, by rfl⟩ : syracuseStep 854091 = 1281137) B1281137
theorem B1280087 : Blo 850355 1280087 := bstep (se 1 (by rfl) ⟨960065, by rfl⟩ : syracuseStep 1280087 = 1920131) B1920131
theorem B854103 : Blo 850355 854103 := bstep (se 1 (by rfl) ⟨640577, by rfl⟩ : syracuseStep 854103 = 1281155) B1281155
theorem B854123 : Blo 850355 854123 := bstep (se 1 (by rfl) ⟨640592, by rfl⟩ : syracuseStep 854123 = 1281185) B1281185
theorem B854135 : Blo 850355 854135 := bstep (se 1 (by rfl) ⟨640601, by rfl⟩ : syracuseStep 854135 = 1281203) B1281203
theorem B854155 : Blo 850355 854155 := bstep (se 1 (by rfl) ⟨640616, by rfl⟩ : syracuseStep 854155 = 1281233) B1281233
theorem B854167 : Blo 850355 854167 := bstep (se 1 (by rfl) ⟨640625, by rfl⟩ : syracuseStep 854167 = 1281251) B1281251
theorem B1214617 : Blo 850355 1214617 := bstep (se 2 (by rfl) ⟨455481, by rfl⟩ : syracuseStep 1214617 = 910963) B910963
theorem B1280153 : Blo 850355 1280153 := bstep (se 2 (by rfl) ⟨480057, by rfl⟩ : syracuseStep 1280153 = 960115) B960115
theorem B854187 : Blo 850355 854187 := bstep (se 1 (by rfl) ⟨640640, by rfl⟩ : syracuseStep 854187 = 1281281) B1281281
theorem B854199 : Blo 850355 854199 := bstep (se 1 (by rfl) ⟨640649, by rfl⟩ : syracuseStep 854199 = 1281299) B1281299
theorem B854219 : Blo 850355 854219 := bstep (se 1 (by rfl) ⟨640664, by rfl⟩ : syracuseStep 854219 = 1281329) B1281329
theorem B854231 : Blo 850355 854231 := bstep (se 1 (by rfl) ⟨640673, by rfl⟩ : syracuseStep 854231 = 1281347) B1281347
theorem B854251 : Blo 850355 854251 := bstep (se 1 (by rfl) ⟨640688, by rfl⟩ : syracuseStep 854251 = 1281377) B1281377
theorem B1870067 : Blo 850355 1870067 := bstep (se 1 (by rfl) ⟨1402550, by rfl⟩ : syracuseStep 1870067 = 2805101) B2805101
theorem B854263 : Blo 850355 854263 := bstep (se 1 (by rfl) ⟨640697, by rfl⟩ : syracuseStep 854263 = 1281395) B1281395
theorem B1280267 : Blo 850355 1280267 := bstep (se 1 (by rfl) ⟨960200, by rfl⟩ : syracuseStep 1280267 = 1920401) B1920401
theorem B854283 : Blo 850355 854283 := bstep (se 1 (by rfl) ⟨640712, by rfl⟩ : syracuseStep 854283 = 1281425) B1281425
theorem B1280279 : Blo 850355 1280279 := bstep (se 1 (by rfl) ⟨960209, by rfl⟩ : syracuseStep 1280279 = 1920419) B1920419
theorem B854295 : Blo 850355 854295 := bstep (se 1 (by rfl) ⟨640721, by rfl⟩ : syracuseStep 854295 = 1281443) B1281443
theorem B854315 : Blo 850355 854315 := bstep (se 1 (by rfl) ⟨640736, by rfl⟩ : syracuseStep 854315 = 1281473) B1281473
theorem B854327 : Blo 850355 854327 := bstep (se 1 (by rfl) ⟨640745, by rfl⟩ : syracuseStep 854327 = 1281491) B1281491
theorem B854347 : Blo 850355 854347 := bstep (se 1 (by rfl) ⟨640760, by rfl⟩ : syracuseStep 854347 = 1281521) B1281521
theorem B1280345 : Blo 850355 1280345 := bstep (se 2 (by rfl) ⟨480129, by rfl⟩ : syracuseStep 1280345 = 960259) B960259
theorem B1149337 : Blo 850355 1149337 := bstep (se 2 (by rfl) ⟨431001, by rfl⟩ : syracuseStep 1149337 = 862003) B862003
theorem B1280459 : Blo 850355 1280459 := bstep (se 1 (by rfl) ⟨960344, by rfl⟩ : syracuseStep 1280459 = 1920689) B1920689
theorem B1280471 : Blo 850355 1280471 := bstep (se 1 (by rfl) ⟨960353, by rfl⟩ : syracuseStep 1280471 = 1920707) B1920707
theorem B1280537 : Blo 850355 1280537 := bstep (se 2 (by rfl) ⟨480201, by rfl⟩ : syracuseStep 1280537 = 960403) B960403
theorem B1280651 : Blo 850355 1280651 := bstep (se 1 (by rfl) ⟨960488, by rfl⟩ : syracuseStep 1280651 = 1920977) B1920977
theorem B1280663 : Blo 850355 1280663 := bstep (se 1 (by rfl) ⟨960497, by rfl⟩ : syracuseStep 1280663 = 1920995) B1920995
theorem B1280729 : Blo 850355 1280729 := bstep (se 2 (by rfl) ⟨480273, by rfl⟩ : syracuseStep 1280729 = 960547) B960547
theorem B4098833 : Blo 850355 4098833 := bstep (se 2 (by rfl) ⟨1537062, by rfl⟩ : syracuseStep 4098833 = 3074125) B3074125
theorem B1280843 : Blo 850355 1280843 := bstep (se 1 (by rfl) ⟨960632, by rfl⟩ : syracuseStep 1280843 = 1921265) B1921265
theorem B1280855 : Blo 850355 1280855 := bstep (se 1 (by rfl) ⟨960641, by rfl⟩ : syracuseStep 1280855 = 1921283) B1921283
theorem B1280921 : Blo 850355 1280921 := bstep (se 2 (by rfl) ⟨480345, by rfl⟩ : syracuseStep 1280921 = 960691) B960691
theorem B2919361 : Blo 850355 2919361 := bstep (se 2 (by rfl) ⟨1094760, by rfl⟩ : syracuseStep 2919361 = 2189521) B2189521
theorem B1281035 : Blo 850355 1281035 := bstep (se 1 (by rfl) ⟨960776, by rfl⟩ : syracuseStep 1281035 = 1921553) B1921553
theorem B1281047 : Blo 850355 1281047 := bstep (se 1 (by rfl) ⟨960785, by rfl⟩ : syracuseStep 1281047 = 1921571) B1921571
theorem B1281113 : Blo 850355 1281113 := bstep (se 2 (by rfl) ⟨480417, by rfl⟩ : syracuseStep 1281113 = 960835) B960835
theorem B11209859 : Blo 850355 11209859 := bstep (se 1 (by rfl) ⟨8407394, by rfl⟩ : syracuseStep 11209859 = 16814789) B16814789
theorem B1281227 : Blo 850355 1281227 := bstep (se 1 (by rfl) ⟨960920, by rfl⟩ : syracuseStep 1281227 = 1921841) B1921841
theorem B15535309 : Blo 850355 15535309 := bstep (se 3 (by rfl) ⟨2912870, by rfl⟩ : syracuseStep 15535309 = 5825741) B5825741
theorem B1281239 : Blo 850355 1281239 := bstep (se 1 (by rfl) ⟨960929, by rfl⟩ : syracuseStep 1281239 = 1921859) B1921859
theorem B1215767 : Blo 850355 1215767 := bstep (se 1 (by rfl) ⟨911825, by rfl⟩ : syracuseStep 1215767 = 1823651) B1823651
theorem B1281305 : Blo 850355 1281305 := bstep (se 2 (by rfl) ⟨480489, by rfl⟩ : syracuseStep 1281305 = 960979) B960979
theorem B1281419 : Blo 850355 1281419 := bstep (se 1 (by rfl) ⟨961064, by rfl⟩ : syracuseStep 1281419 = 1922129) B1922129
theorem B1281431 : Blo 850355 1281431 := bstep (se 1 (by rfl) ⟨961073, by rfl⟩ : syracuseStep 1281431 = 1922147) B1922147
theorem B1281497 : Blo 850355 1281497 := bstep (se 2 (by rfl) ⟨480561, by rfl⟩ : syracuseStep 1281497 = 961123) B961123
theorem B2428481 : Blo 850355 2428481 := bstep (se 2 (by rfl) ⟨910680, by rfl⟩ : syracuseStep 2428481 = 1821361) B1821361
theorem B1216075 : Blo 850355 1216075 := bstep (se 1 (by rfl) ⟨912056, by rfl⟩ : syracuseStep 1216075 = 1824113) B1824113
theorem B2428505 : Blo 850355 2428505 := bstep (se 2 (by rfl) ⟨910689, by rfl⟩ : syracuseStep 2428505 = 1821379) B1821379
theorem B23334493 : Blo 850355 23334493 := bstep (se 3 (by rfl) ⟨4375217, by rfl⟩ : syracuseStep 23334493 = 8750435) B8750435
theorem B3641219 : Blo 850355 3641219 := bstep (se 1 (by rfl) ⟨2730914, by rfl⟩ : syracuseStep 3641219 = 5461829) B5461829
theorem B3280861 : Blo 850355 3280861 := bstep (se 3 (by rfl) ⟨615161, by rfl⟩ : syracuseStep 3280861 = 1230323) B1230323
theorem B3641561 : Blo 850355 3641561 := bstep (se 2 (by rfl) ⟨1365585, by rfl⟩ : syracuseStep 3641561 = 2731171) B2731171
theorem B1151435 : Blo 850355 1151435 := bstep (se 1 (by rfl) ⟨863576, by rfl⟩ : syracuseStep 1151435 = 1727153) B1727153
theorem B8295173 : Blo 850355 8295173 := bstep (se 4 (by rfl) ⟨777672, by rfl⟩ : syracuseStep 8295173 = 1555345) B1555345
theorem B2429747 : Blo 850355 2429747 := bstep (se 1 (by rfl) ⟨1822310, by rfl⟩ : syracuseStep 2429747 = 3644621) B3644621
theorem B4854593 : Blo 850355 4854593 := bstep (se 2 (by rfl) ⟨1820472, by rfl⟩ : syracuseStep 4854593 = 3640945) B3640945
theorem B7476299 : Blo 850355 7476299 := bstep (se 1 (by rfl) ⟨5607224, by rfl⟩ : syracuseStep 7476299 = 11214449) B11214449
theorem B33265349 : Blo 850355 33265349 := bstep (se 4 (by rfl) ⟨3118626, by rfl⟩ : syracuseStep 33265349 = 6237253) B6237253
theorem B2660057 : Blo 850355 2660057 := bstep (se 2 (by rfl) ⟨997521, by rfl⟩ : syracuseStep 2660057 = 1995043) B1995043
theorem B2627635 : Blo 850355 2627635 := bstep (se 1 (by rfl) ⟨1970726, by rfl⟩ : syracuseStep 2627635 = 3941453) B3941453
theorem B11671627 : Blo 850355 11671627 := bstep (se 1 (by rfl) ⟨8753720, by rfl⟩ : syracuseStep 11671627 = 17507441) B17507441
theorem B3938483 : Blo 850355 3938483 := bstep (se 1 (by rfl) ⟨2953862, by rfl⟩ : syracuseStep 3938483 = 5907725) B5907725
theorem B956695 : Blo 850355 956695 := bstep (se 1 (by rfl) ⟨717521, by rfl⟩ : syracuseStep 956695 = 1435043) B1435043
theorem B13834597 : Blo 850355 13834597 := bstep (se 4 (by rfl) ⟨1296993, by rfl⟩ : syracuseStep 13834597 = 2593987) B2593987
theorem B9705905 : Blo 850355 9705905 := bstep (se 2 (by rfl) ⟨3639714, by rfl⟩ : syracuseStep 9705905 = 7279429) B7279429
theorem B956875 : Blo 850355 956875 := bstep (se 1 (by rfl) ⟨717656, by rfl⟩ : syracuseStep 956875 = 1435313) B1435313
theorem B956983 : Blo 850355 956983 := bstep (se 1 (by rfl) ⟨717737, by rfl⟩ : syracuseStep 956983 = 1435475) B1435475
theorem B1841779 : Blo 850355 1841779 := bstep (se 1 (by rfl) ⟨1381334, by rfl⟩ : syracuseStep 1841779 = 2762669) B2762669
theorem B957163 : Blo 850355 957163 := bstep (se 1 (by rfl) ⟨717872, by rfl⟩ : syracuseStep 957163 = 1435745) B1435745
theorem B7281413 : Blo 850355 7281413 := bstep (se 4 (by rfl) ⟨682632, by rfl⟩ : syracuseStep 7281413 = 1365265) B1365265
theorem B7772993 : Blo 850355 7772993 := bstep (se 2 (by rfl) ⟨2914872, by rfl⟩ : syracuseStep 7772993 = 5829745) B5829745
theorem B957271 : Blo 850355 957271 := bstep (se 1 (by rfl) ⟨717953, by rfl⟩ : syracuseStep 957271 = 1435907) B1435907
theorem B957451 : Blo 850355 957451 := bstep (se 1 (by rfl) ⟨718088, by rfl⟩ : syracuseStep 957451 = 1436177) B1436177
theorem B957559 : Blo 850355 957559 := bstep (se 1 (by rfl) ⟨718169, by rfl⟩ : syracuseStep 957559 = 1436339) B1436339
theorem B957739 : Blo 850355 957739 := bstep (se 1 (by rfl) ⟨718304, by rfl⟩ : syracuseStep 957739 = 1436609) B1436609
theorem B957847 : Blo 850355 957847 := bstep (se 1 (by rfl) ⟨718385, by rfl⟩ : syracuseStep 957847 = 1436771) B1436771
theorem B7380485 : Blo 850355 7380485 := bstep (se 4 (by rfl) ⟨691920, by rfl⟩ : syracuseStep 7380485 = 1383841) B1383841
theorem B3644945 : Blo 850355 3644945 := bstep (se 2 (by rfl) ⟨1366854, by rfl⟩ : syracuseStep 3644945 = 2733709) B2733709
theorem B4496941 : Blo 850355 4496941 := bstep (se 3 (by rfl) ⟨843176, by rfl⟩ : syracuseStep 4496941 = 1686353) B1686353
theorem B958027 : Blo 850355 958027 := bstep (se 1 (by rfl) ⟨718520, by rfl⟩ : syracuseStep 958027 = 1437041) B1437041
theorem B2432605 : Blo 850355 2432605 := bstep (se 3 (by rfl) ⟨456113, by rfl⟩ : syracuseStep 2432605 = 912227) B912227
theorem B10919555 : Blo 850355 10919555 := bstep (se 1 (by rfl) ⟨8189666, by rfl⟩ : syracuseStep 10919555 = 16379333) B16379333
theorem B1941131 : Blo 850355 1941131 := bstep (se 1 (by rfl) ⟨1455848, by rfl⟩ : syracuseStep 1941131 = 2911697) B2911697
theorem B2432663 : Blo 850355 2432663 := bstep (se 1 (by rfl) ⟨1824497, by rfl⟩ : syracuseStep 2432663 = 3648995) B3648995
theorem B958135 : Blo 850355 958135 := bstep (se 1 (by rfl) ⟨718601, by rfl⟩ : syracuseStep 958135 = 1437203) B1437203
theorem B1941185 : Blo 850355 1941185 := bstep (se 2 (by rfl) ⟨727944, by rfl⟩ : syracuseStep 1941185 = 1455889) B1455889
theorem B958315 : Blo 850355 958315 := bstep (se 1 (by rfl) ⟨718736, by rfl⟩ : syracuseStep 958315 = 1437473) B1437473
theorem B958423 : Blo 850355 958423 := bstep (se 1 (by rfl) ⟨718817, by rfl⟩ : syracuseStep 958423 = 1437635) B1437635
theorem B2695133 : Blo 850355 2695133 := bstep (se 3 (by rfl) ⟨505337, by rfl⟩ : syracuseStep 2695133 = 1010675) B1010675
theorem B958603 : Blo 850355 958603 := bstep (se 1 (by rfl) ⟨718952, by rfl⟩ : syracuseStep 958603 = 1437905) B1437905
theorem B3645661 : Blo 850355 3645661 := bstep (se 3 (by rfl) ⟨683561, by rfl⟩ : syracuseStep 3645661 = 1367123) B1367123
theorem B958711 : Blo 850355 958711 := bstep (se 1 (by rfl) ⟨719033, by rfl⟩ : syracuseStep 958711 = 1438067) B1438067
theorem B958891 : Blo 850355 958891 := bstep (se 1 (by rfl) ⟨719168, by rfl⟩ : syracuseStep 958891 = 1438337) B1438337
theorem B958999 : Blo 850355 958999 := bstep (se 1 (by rfl) ⟨719249, by rfl⟩ : syracuseStep 958999 = 1438499) B1438499
theorem B1614401 : Blo 850355 1614401 := bstep (se 2 (by rfl) ⟨605400, by rfl⟩ : syracuseStep 1614401 = 1210801) B1210801
theorem B4497995 : Blo 850355 4497995 := bstep (se 1 (by rfl) ⟨3373496, by rfl⟩ : syracuseStep 4497995 = 6746993) B6746993
theorem B959179 : Blo 850355 959179 := bstep (se 1 (by rfl) ⟨719384, by rfl⟩ : syracuseStep 959179 = 1438769) B1438769
theorem B959287 : Blo 850355 959287 := bstep (se 1 (by rfl) ⟨719465, by rfl⟩ : syracuseStep 959287 = 1438931) B1438931
theorem B1614667 : Blo 850355 1614667 := bstep (se 1 (by rfl) ⟨1211000, by rfl⟩ : syracuseStep 1614667 = 2422001) B2422001
theorem B959467 : Blo 850355 959467 := bstep (se 1 (by rfl) ⟨719600, by rfl⟩ : syracuseStep 959467 = 1439201) B1439201
theorem B959575 : Blo 850355 959575 := bstep (se 1 (by rfl) ⟨719681, by rfl⟩ : syracuseStep 959575 = 1439363) B1439363
theorem B1615115 : Blo 850355 1615115 := bstep (se 1 (by rfl) ⟨1211336, by rfl⟩ : syracuseStep 1615115 = 2422673) B2422673
theorem B959755 : Blo 850355 959755 := bstep (se 1 (by rfl) ⟨719816, by rfl⟩ : syracuseStep 959755 = 1439633) B1439633
theorem B8299841 : Blo 850355 8299841 := bstep (se 2 (by rfl) ⟨3112440, by rfl⟩ : syracuseStep 8299841 = 6224881) B6224881
theorem B959863 : Blo 850355 959863 := bstep (se 1 (by rfl) ⟨719897, by rfl⟩ : syracuseStep 959863 = 1439795) B1439795
theorem B1942937 : Blo 850355 1942937 := bstep (se 2 (by rfl) ⟨728601, by rfl⟩ : syracuseStep 1942937 = 1457203) B1457203
theorem B1615297 : Blo 850355 1615297 := bstep (se 2 (by rfl) ⟨605736, by rfl⟩ : syracuseStep 1615297 = 1211473) B1211473
theorem B960043 : Blo 850355 960043 := bstep (se 1 (by rfl) ⟨720032, by rfl⟩ : syracuseStep 960043 = 1440065) B1440065
theorem B960151 : Blo 850355 960151 := bstep (se 1 (by rfl) ⟨720113, by rfl⟩ : syracuseStep 960151 = 1440227) B1440227
theorem B1615639 : Blo 850355 1615639 := bstep (se 1 (by rfl) ⟨1211729, by rfl⟩ : syracuseStep 1615639 = 2423459) B2423459
theorem B960331 : Blo 850355 960331 := bstep (se 1 (by rfl) ⟨720248, by rfl⟩ : syracuseStep 960331 = 1440497) B1440497
theorem B960439 : Blo 850355 960439 := bstep (se 1 (by rfl) ⟨720329, by rfl⟩ : syracuseStep 960439 = 1440659) B1440659
theorem B1615859 : Blo 850355 1615859 := bstep (se 1 (by rfl) ⟨1211894, by rfl⟩ : syracuseStep 1615859 = 2423789) B2423789
theorem B6924305 : Blo 850355 6924305 := bstep (se 2 (by rfl) ⟨2596614, by rfl⟩ : syracuseStep 6924305 = 5193229) B5193229
theorem B5187685 : Blo 850355 5187685 := bstep (se 4 (by rfl) ⟨486345, by rfl⟩ : syracuseStep 5187685 = 972691) B972691
theorem B960619 : Blo 850355 960619 := bstep (se 1 (by rfl) ⟨720464, by rfl⟩ : syracuseStep 960619 = 1440929) B1440929
theorem B1616087 : Blo 850355 1616087 := bstep (se 1 (by rfl) ⟨1212065, by rfl⟩ : syracuseStep 1616087 = 2424131) B2424131
theorem B960727 : Blo 850355 960727 := bstep (se 1 (by rfl) ⟨720545, by rfl⟩ : syracuseStep 960727 = 1441091) B1441091
theorem B960907 : Blo 850355 960907 := bstep (se 1 (by rfl) ⟨720680, by rfl⟩ : syracuseStep 960907 = 1441361) B1441361
theorem B1616345 : Blo 850355 1616345 := bstep (se 2 (by rfl) ⟨606129, by rfl⟩ : syracuseStep 1616345 = 1212259) B1212259
theorem B961015 : Blo 850355 961015 := bstep (se 1 (by rfl) ⟨720761, by rfl⟩ : syracuseStep 961015 = 1441523) B1441523
theorem B6990371 : Blo 850355 6990371 := bstep (se 1 (by rfl) ⟨5242778, by rfl⟩ : syracuseStep 6990371 = 10485557) B10485557
theorem B4598365 : Blo 850355 4598365 := bstep (se 3 (by rfl) ⟨862193, by rfl⟩ : syracuseStep 4598365 = 1724387) B1724387
theorem B1846039 : Blo 850355 1846039 := bstep (se 1 (by rfl) ⟨1384529, by rfl⟩ : syracuseStep 1846039 = 2769059) B2769059
theorem B27601717 : Blo 850355 27601717 := bstep (se 5 (by rfl) ⟨1293830, by rfl⟩ : syracuseStep 27601717 = 2587661) B2587661
theorem B1616755 : Blo 850355 1616755 := bstep (se 1 (by rfl) ⟨1212566, by rfl⟩ : syracuseStep 1616755 = 2425133) B2425133
theorem B31075289 : Blo 850355 31075289 := bstep (se 2 (by rfl) ⟨11653233, by rfl⟩ : syracuseStep 31075289 = 23306467) B23306467
theorem B1617241 : Blo 850355 1617241 := bstep (se 2 (by rfl) ⟨606465, by rfl⟩ : syracuseStep 1617241 = 1212931) B1212931
theorem B3649283 : Blo 850355 3649283 := bstep (se 1 (by rfl) ⟨2736962, by rfl⟩ : syracuseStep 3649283 = 5473925) B5473925
theorem B1617803 : Blo 850355 1617803 := bstep (se 1 (by rfl) ⟨1213352, by rfl⟩ : syracuseStep 1617803 = 2426705) B2426705
theorem B13840307 : Blo 850355 13840307 := bstep (se 1 (by rfl) ⟨10380230, by rfl⟩ : syracuseStep 13840307 = 20760461) B20760461
theorem B6926381 : Blo 850355 6926381 := bstep (se 3 (by rfl) ⟨1298696, by rfl⟩ : syracuseStep 6926381 = 2597393) B2597393
theorem B1617985 : Blo 850355 1617985 := bstep (se 2 (by rfl) ⟨606744, by rfl⟩ : syracuseStep 1617985 = 1213489) B1213489
theorem B3879085 : Blo 850355 3879085 := bstep (se 3 (by rfl) ⟨727328, by rfl⟩ : syracuseStep 3879085 = 1454657) B1454657
theorem B1749271 : Blo 850355 1749271 := bstep (se 1 (by rfl) ⟨1311953, by rfl⟩ : syracuseStep 1749271 = 2623907) B2623907
theorem B4862339 : Blo 850355 4862339 := bstep (se 1 (by rfl) ⟨3646754, by rfl⟩ : syracuseStep 4862339 = 7293509) B7293509
theorem B1913345 : Blo 850355 1913345 := bstep (se 2 (by rfl) ⟨717504, by rfl⟩ : syracuseStep 1913345 = 1435009) B1435009
theorem B4305473 : Blo 850355 4305473 := bstep (se 2 (by rfl) ⟨1614552, by rfl⟩ : syracuseStep 4305473 = 3229105) B3229105
theorem B1913561 : Blo 850355 1913561 := bstep (se 2 (by rfl) ⟨717585, by rfl⟩ : syracuseStep 1913561 = 1435171) B1435171
theorem B7484165 : Blo 850355 7484165 := bstep (se 4 (by rfl) ⟨701640, by rfl⟩ : syracuseStep 7484165 = 1403281) B1403281
theorem B1618699 : Blo 850355 1618699 := bstep (se 1 (by rfl) ⟨1214024, by rfl⟩ : syracuseStep 1618699 = 2428049) B2428049
theorem B3945233 : Blo 850355 3945233 := bstep (se 2 (by rfl) ⟨1479462, by rfl⟩ : syracuseStep 3945233 = 2958925) B2958925
theorem B1913651 : Blo 850355 1913651 := bstep (se 1 (by rfl) ⟨1435238, by rfl⟩ : syracuseStep 1913651 = 2870477) B2870477
theorem B1913687 : Blo 850355 1913687 := bstep (se 1 (by rfl) ⟨1435265, by rfl⟩ : syracuseStep 1913687 = 2870531) B2870531
theorem B1618775 : Blo 850355 1618775 := bstep (se 1 (by rfl) ⟨1214081, by rfl⟩ : syracuseStep 1618775 = 2428163) B2428163
theorem B2765785 : Blo 850355 2765785 := bstep (se 2 (by rfl) ⟨1037169, by rfl⟩ : syracuseStep 2765785 = 2074339) B2074339
theorem B1913867 : Blo 850355 1913867 := bstep (se 1 (by rfl) ⟨1435400, by rfl⟩ : syracuseStep 1913867 = 2870801) B2870801
theorem B1913921 : Blo 850355 1913921 := bstep (se 2 (by rfl) ⟨717720, by rfl⟩ : syracuseStep 1913921 = 1435441) B1435441
theorem B1914137 : Blo 850355 1914137 := bstep (se 2 (by rfl) ⟨717801, by rfl⟩ : syracuseStep 1914137 = 1435603) B1435603
theorem B2733401 : Blo 850355 2733401 := bstep (se 2 (by rfl) ⟨1025025, by rfl⟩ : syracuseStep 2733401 = 2050051) B2050051
theorem B1914227 : Blo 850355 1914227 := bstep (se 1 (by rfl) ⟨1435670, by rfl⟩ : syracuseStep 1914227 = 2871341) B2871341
theorem B1914263 : Blo 850355 1914263 := bstep (se 1 (by rfl) ⟨1435697, by rfl⟩ : syracuseStep 1914263 = 2871395) B2871395
theorem B1619443 : Blo 850355 1619443 := bstep (se 1 (by rfl) ⟨1214582, by rfl⟩ : syracuseStep 1619443 = 2429165) B2429165
theorem B1914443 : Blo 850355 1914443 := bstep (se 1 (by rfl) ⟨1435832, by rfl⟩ : syracuseStep 1914443 = 2871665) B2871665
theorem B1914497 : Blo 850355 1914497 := bstep (se 2 (by rfl) ⟨717936, by rfl⟩ : syracuseStep 1914497 = 1435873) B1435873
theorem B7288451 : Blo 850355 7288451 := bstep (se 1 (by rfl) ⟨5466338, by rfl⟩ : syracuseStep 7288451 = 10932677) B10932677
theorem B1619671 : Blo 850355 1619671 := bstep (se 1 (by rfl) ⟨1214753, by rfl⟩ : syracuseStep 1619671 = 2429507) B2429507
theorem B1619777 : Blo 850355 1619777 := bstep (se 2 (by rfl) ⟨607416, by rfl⟩ : syracuseStep 1619777 = 1214833) B1214833
theorem B1914713 : Blo 850355 1914713 := bstep (se 2 (by rfl) ⟨718017, by rfl⟩ : syracuseStep 1914713 = 1436035) B1436035
theorem B4929373 : Blo 850355 4929373 := bstep (se 3 (by rfl) ⟨924257, by rfl⟩ : syracuseStep 4929373 = 1848515) B1848515
theorem B1914803 : Blo 850355 1914803 := bstep (se 1 (by rfl) ⟨1436102, by rfl⟩ : syracuseStep 1914803 = 2872205) B2872205
theorem B1914839 : Blo 850355 1914839 := bstep (se 1 (by rfl) ⟨1436129, by rfl⟩ : syracuseStep 1914839 = 2872259) B2872259
theorem B1619929 : Blo 850355 1619929 := bstep (se 2 (by rfl) ⟨607473, by rfl⟩ : syracuseStep 1619929 = 1214947) B1214947
theorem B2734145 : Blo 850355 2734145 := bstep (se 2 (by rfl) ⟨1025304, by rfl⟩ : syracuseStep 2734145 = 2050609) B2050609
theorem B1816663 : Blo 850355 1816663 := bstep (se 1 (by rfl) ⟨1362497, by rfl⟩ : syracuseStep 1816663 = 2724995) B2724995
theorem B2308189 : Blo 850355 2308189 := bstep (se 3 (by rfl) ⟨432785, by rfl⟩ : syracuseStep 2308189 = 865571) B865571
theorem B1915019 : Blo 850355 1915019 := bstep (se 1 (by rfl) ⟨1436264, by rfl⟩ : syracuseStep 1915019 = 2872529) B2872529
theorem B1915073 : Blo 850355 1915073 := bstep (se 2 (by rfl) ⟨718152, by rfl⟩ : syracuseStep 1915073 = 1436305) B1436305
theorem B1816843 : Blo 850355 1816843 := bstep (se 1 (by rfl) ⟨1362632, by rfl⟩ : syracuseStep 1816843 = 2725265) B2725265
theorem B1816919 : Blo 850355 1816919 := bstep (se 1 (by rfl) ⟨1362689, by rfl⟩ : syracuseStep 1816919 = 2725379) B2725379
theorem B1947991 : Blo 850355 1947991 := bstep (se 1 (by rfl) ⟨1460993, by rfl⟩ : syracuseStep 1947991 = 2921987) B2921987
theorem B1915289 : Blo 850355 1915289 := bstep (se 2 (by rfl) ⟨718233, by rfl⟩ : syracuseStep 1915289 = 1436467) B1436467
theorem B4307417 : Blo 850355 4307417 := bstep (se 2 (by rfl) ⟨1615281, by rfl⟩ : syracuseStep 4307417 = 3230563) B3230563
theorem B1915379 : Blo 850355 1915379 := bstep (se 1 (by rfl) ⟨1436534, by rfl⟩ : syracuseStep 1915379 = 2873069) B2873069
theorem B1915415 : Blo 850355 1915415 := bstep (se 1 (by rfl) ⟨1436561, by rfl⟩ : syracuseStep 1915415 = 2873123) B2873123
theorem B1915595 : Blo 850355 1915595 := bstep (se 1 (by rfl) ⟨1436696, by rfl⟩ : syracuseStep 1915595 = 2873393) B2873393
theorem B1915649 : Blo 850355 1915649 := bstep (se 2 (by rfl) ⟨718368, by rfl⟩ : syracuseStep 1915649 = 1436737) B1436737
theorem B2735041 : Blo 850355 2735041 := bstep (se 2 (by rfl) ⟨1025640, by rfl⟩ : syracuseStep 2735041 = 2051281) B2051281
theorem B1915865 : Blo 850355 1915865 := bstep (se 2 (by rfl) ⟨718449, by rfl⟩ : syracuseStep 1915865 = 1436899) B1436899
theorem B1915955 : Blo 850355 1915955 := bstep (se 1 (by rfl) ⟨1436966, by rfl⟩ : syracuseStep 1915955 = 2873933) B2873933
theorem B1915991 : Blo 850355 1915991 := bstep (se 1 (by rfl) ⟨1436993, by rfl⟩ : syracuseStep 1915991 = 2873987) B2873987
theorem B3882077 : Blo 850355 3882077 := bstep (se 3 (by rfl) ⟨727889, by rfl⟩ : syracuseStep 3882077 = 1455779) B1455779
theorem B1621235 : Blo 850355 1621235 := bstep (se 1 (by rfl) ⟨1215926, by rfl⟩ : syracuseStep 1621235 = 2431853) B2431853
theorem B1916171 : Blo 850355 1916171 := bstep (se 1 (by rfl) ⟨1437128, by rfl⟩ : syracuseStep 1916171 = 2874257) B2874257
theorem B2047283 : Blo 850355 2047283 := bstep (se 1 (by rfl) ⟨1535462, by rfl⟩ : syracuseStep 2047283 = 3070925) B3070925
theorem B1916225 : Blo 850355 1916225 := bstep (se 2 (by rfl) ⟨718584, by rfl⟩ : syracuseStep 1916225 = 1437169) B1437169
theorem B9485669 : Blo 850355 9485669 := bstep (se 4 (by rfl) ⟨889281, by rfl⟩ : syracuseStep 9485669 = 1778563) B1778563
theorem B1621387 : Blo 850355 1621387 := bstep (se 1 (by rfl) ⟨1216040, by rfl⟩ : syracuseStep 1621387 = 2432081) B2432081
theorem B6471089 : Blo 850355 6471089 := bstep (se 2 (by rfl) ⟨2426658, by rfl⟩ : syracuseStep 6471089 = 4853317) B4853317
theorem B12271121 : Blo 850355 12271121 := bstep (se 2 (by rfl) ⟨4601670, by rfl⟩ : syracuseStep 12271121 = 9203341) B9203341
theorem B1916441 : Blo 850355 1916441 := bstep (se 2 (by rfl) ⟨718665, by rfl⟩ : syracuseStep 1916441 = 1437331) B1437331
theorem B10927709 : Blo 850355 10927709 := bstep (se 3 (by rfl) ⟨2048945, by rfl⟩ : syracuseStep 10927709 = 4097891) B4097891
theorem B1916531 : Blo 850355 1916531 := bstep (se 1 (by rfl) ⟨1437398, by rfl⟩ : syracuseStep 1916531 = 2874797) B2874797
theorem B3882647 : Blo 850355 3882647 := bstep (se 1 (by rfl) ⟨2911985, by rfl⟩ : syracuseStep 3882647 = 5823971) B5823971
theorem B1916567 : Blo 850355 1916567 := bstep (se 1 (by rfl) ⟨1437425, by rfl⟩ : syracuseStep 1916567 = 2874851) B2874851
theorem B1621721 : Blo 850355 1621721 := bstep (se 2 (by rfl) ⟨608145, by rfl⟩ : syracuseStep 1621721 = 1216291) B1216291
theorem B1556275 : Blo 850355 1556275 := bstep (se 1 (by rfl) ⟨1167206, by rfl⟩ : syracuseStep 1556275 = 2334413) B2334413
theorem B1916747 : Blo 850355 1916747 := bstep (se 1 (by rfl) ⟨1437560, by rfl⟩ : syracuseStep 1916747 = 2875121) B2875121
theorem B1916801 : Blo 850355 1916801 := bstep (se 2 (by rfl) ⟨718800, by rfl⟩ : syracuseStep 1916801 = 1437601) B1437601
theorem B6471575 : Blo 850355 6471575 := bstep (se 1 (by rfl) ⟨4853681, by rfl⟩ : syracuseStep 6471575 = 9707363) B9707363
theorem B8306705 : Blo 850355 8306705 := bstep (se 2 (by rfl) ⟨3115014, by rfl⟩ : syracuseStep 8306705 = 6230029) B6230029
theorem B4309037 : Blo 850355 4309037 := bstep (se 3 (by rfl) ⟨807944, by rfl⟩ : syracuseStep 4309037 = 1615889) B1615889
theorem B1818713 : Blo 850355 1818713 := bstep (se 2 (by rfl) ⟨682017, by rfl⟩ : syracuseStep 1818713 = 1364035) B1364035
theorem B1917017 : Blo 850355 1917017 := bstep (se 2 (by rfl) ⟨718881, by rfl⟩ : syracuseStep 1917017 = 1437763) B1437763
theorem B1917107 : Blo 850355 1917107 := bstep (se 1 (by rfl) ⟨1437830, by rfl⟩ : syracuseStep 1917107 = 2875661) B2875661
theorem B1917143 : Blo 850355 1917143 := bstep (se 1 (by rfl) ⟨1437857, by rfl⟩ : syracuseStep 1917143 = 2875715) B2875715
theorem B1917323 : Blo 850355 1917323 := bstep (se 1 (by rfl) ⟨1437992, by rfl⟩ : syracuseStep 1917323 = 2875985) B2875985
theorem B1917377 : Blo 850355 1917377 := bstep (se 2 (by rfl) ⟨719016, by rfl⟩ : syracuseStep 1917377 = 1438033) B1438033
theorem B2736605 : Blo 850355 2736605 := bstep (se 3 (by rfl) ⟨513113, by rfl⟩ : syracuseStep 2736605 = 1026227) B1026227
theorem B29573603 : Blo 850355 29573603 := bstep (se 1 (by rfl) ⟨22180202, by rfl⟩ : syracuseStep 29573603 = 44360405) B44360405
theorem B1917593 : Blo 850355 1917593 := bstep (se 2 (by rfl) ⟨719097, by rfl⟩ : syracuseStep 1917593 = 1438195) B1438195
theorem B6898355 : Blo 850355 6898355 := bstep (se 1 (by rfl) ⟨5173766, by rfl⟩ : syracuseStep 6898355 = 10347533) B10347533
theorem B1819379 : Blo 850355 1819379 := bstep (se 1 (by rfl) ⟨1364534, by rfl⟩ : syracuseStep 1819379 = 2729069) B2729069
theorem B1917683 : Blo 850355 1917683 := bstep (se 1 (by rfl) ⟨1438262, by rfl⟩ : syracuseStep 1917683 = 2876525) B2876525
theorem B1917719 : Blo 850355 1917719 := bstep (se 1 (by rfl) ⟨1438289, by rfl⟩ : syracuseStep 1917719 = 2876579) B2876579
theorem B13812545 : Blo 850355 13812545 := bstep (se 2 (by rfl) ⟨5179704, by rfl⟩ : syracuseStep 13812545 = 10359409) B10359409
theorem B15582017 : Blo 850355 15582017 := bstep (se 2 (by rfl) ⟨5843256, by rfl⟩ : syracuseStep 15582017 = 11686513) B11686513
theorem B1917899 : Blo 850355 1917899 := bstep (se 1 (by rfl) ⟨1438424, by rfl⟩ : syracuseStep 1917899 = 2876849) B2876849
theorem B1917953 : Blo 850355 1917953 := bstep (se 2 (by rfl) ⟨719232, by rfl⟩ : syracuseStep 1917953 = 1438465) B1438465
theorem B1918169 : Blo 850355 1918169 := bstep (se 2 (by rfl) ⟨719313, by rfl⟩ : syracuseStep 1918169 = 1438627) B1438627
theorem B3228893 : Blo 850355 3228893 := bstep (se 3 (by rfl) ⟨605417, by rfl⟩ : syracuseStep 3228893 = 1210835) B1210835
theorem B1918259 : Blo 850355 1918259 := bstep (se 1 (by rfl) ⟨1438694, by rfl⟩ : syracuseStep 1918259 = 2877389) B2877389
theorem B1918295 : Blo 850355 1918295 := bstep (se 1 (by rfl) ⟨1438721, by rfl⟩ : syracuseStep 1918295 = 2877443) B2877443
theorem B1918475 : Blo 850355 1918475 := bstep (se 1 (by rfl) ⟨1438856, by rfl⟩ : syracuseStep 1918475 = 2877713) B2877713
theorem B1918529 : Blo 850355 1918529 := bstep (se 2 (by rfl) ⟨719448, by rfl⟩ : syracuseStep 1918529 = 1438897) B1438897
theorem B2049715 : Blo 850355 2049715 := bstep (se 1 (by rfl) ⟨1537286, by rfl⟩ : syracuseStep 2049715 = 3074573) B3074573
theorem B12306181 : Blo 850355 12306181 := bstep (se 4 (by rfl) ⟨1153704, by rfl⟩ : syracuseStep 12306181 = 2307409) B2307409
theorem B1918745 : Blo 850355 1918745 := bstep (se 2 (by rfl) ⟨719529, by rfl⟩ : syracuseStep 1918745 = 1439059) B1439059
theorem B9717569 : Blo 850355 9717569 := bstep (se 2 (by rfl) ⟨3644088, by rfl⟩ : syracuseStep 9717569 = 7288177) B7288177
theorem B1918835 : Blo 850355 1918835 := bstep (se 1 (by rfl) ⟨1439126, by rfl⟩ : syracuseStep 1918835 = 2878253) B2878253
theorem B3229591 : Blo 850355 3229591 := bstep (se 1 (by rfl) ⟨2422193, by rfl⟩ : syracuseStep 3229591 = 4844387) B4844387
theorem B1918871 : Blo 850355 1918871 := bstep (se 1 (by rfl) ⟨1439153, by rfl⟩ : syracuseStep 1918871 = 2878307) B2878307
theorem B4376537 : Blo 850355 4376537 := bstep (se 2 (by rfl) ⟨1641201, by rfl⟩ : syracuseStep 4376537 = 3282403) B3282403
theorem B4605997 : Blo 850355 4605997 := bstep (se 3 (by rfl) ⟨863624, by rfl⟩ : syracuseStep 4605997 = 1727249) B1727249
theorem B1919051 : Blo 850355 1919051 := bstep (se 1 (by rfl) ⟨1439288, by rfl⟩ : syracuseStep 1919051 = 2878577) B2878577
theorem B1919105 : Blo 850355 1919105 := bstep (se 2 (by rfl) ⟨719664, by rfl⟩ : syracuseStep 1919105 = 1439329) B1439329
theorem B1460377 : Blo 850355 1460377 := bstep (se 2 (by rfl) ⟨547641, by rfl⟩ : syracuseStep 1460377 = 1095283) B1095283
theorem B1820875 : Blo 850355 1820875 := bstep (se 1 (by rfl) ⟨1365656, by rfl⟩ : syracuseStep 1820875 = 2731313) B2731313
theorem B1919321 : Blo 850355 1919321 := bstep (se 2 (by rfl) ⟨719745, by rfl⟩ : syracuseStep 1919321 = 1439491) B1439491
theorem B1919411 : Blo 850355 1919411 := bstep (se 1 (by rfl) ⟨1439558, by rfl⟩ : syracuseStep 1919411 = 2879117) B2879117
theorem B1919447 : Blo 850355 1919447 := bstep (se 1 (by rfl) ⟨1439585, by rfl⟩ : syracuseStep 1919447 = 2879171) B2879171
theorem B1919627 : Blo 850355 1919627 := bstep (se 1 (by rfl) ⟨1439720, by rfl⟩ : syracuseStep 1919627 = 2879441) B2879441
theorem B3230381 : Blo 850355 3230381 := bstep (se 3 (by rfl) ⟨605696, by rfl⟩ : syracuseStep 3230381 = 1211393) B1211393
theorem B1919681 : Blo 850355 1919681 := bstep (se 2 (by rfl) ⟨719880, by rfl⟩ : syracuseStep 1919681 = 1439761) B1439761
theorem B1919897 : Blo 850355 1919897 := bstep (se 2 (by rfl) ⟨719961, by rfl⟩ : syracuseStep 1919897 = 1439923) B1439923
theorem B1919987 : Blo 850355 1919987 := bstep (se 1 (by rfl) ⟨1439990, by rfl⟩ : syracuseStep 1919987 = 2879981) B2879981
theorem B1920023 : Blo 850355 1920023 := bstep (se 1 (by rfl) ⟨1440017, by rfl⟩ : syracuseStep 1920023 = 2880035) B2880035
theorem B1297433 : Blo 850355 1297433 := bstep (se 2 (by rfl) ⟨486537, by rfl⟩ : syracuseStep 1297433 = 973075) B973075
theorem B2870423 : Blo 850355 2870423 := bstep (se 1 (by rfl) ⟨2152817, by rfl⟩ : syracuseStep 2870423 = 4305635) B4305635
theorem B1920203 : Blo 850355 1920203 := bstep (se 1 (by rfl) ⟨1440152, by rfl⟩ : syracuseStep 1920203 = 2880305) B2880305
theorem B1920257 : Blo 850355 1920257 := bstep (se 2 (by rfl) ⟨720096, by rfl⟩ : syracuseStep 1920257 = 1440193) B1440193
theorem B1822105 : Blo 850355 1822105 := bstep (se 2 (by rfl) ⟨683289, by rfl⟩ : syracuseStep 1822105 = 1366579) B1366579
theorem B1920473 : Blo 850355 1920473 := bstep (se 2 (by rfl) ⟨720177, by rfl⟩ : syracuseStep 1920473 = 1440355) B1440355
theorem B22171153 : Blo 850355 22171153 := bstep (se 2 (by rfl) ⟨8314182, by rfl⟩ : syracuseStep 22171153 = 16628365) B16628365
theorem B1920563 : Blo 850355 1920563 := bstep (se 1 (by rfl) ⟨1440422, by rfl⟩ : syracuseStep 1920563 = 2880845) B2880845
theorem B1920599 : Blo 850355 1920599 := bstep (se 1 (by rfl) ⟨1440449, by rfl⟩ : syracuseStep 1920599 = 2880899) B2880899
theorem B2870963 : Blo 850355 2870963 := bstep (se 1 (by rfl) ⟨2153222, by rfl⟩ : syracuseStep 2870963 = 4306445) B4306445
theorem B1920779 : Blo 850355 1920779 := bstep (se 1 (by rfl) ⟨1440584, by rfl⟩ : syracuseStep 1920779 = 2881169) B2881169
theorem B1920833 : Blo 850355 1920833 := bstep (se 2 (by rfl) ⟨720312, by rfl⟩ : syracuseStep 1920833 = 1440625) B1440625
theorem B3067723 : Blo 850355 3067723 := bstep (se 1 (by rfl) ⟨2300792, by rfl⟩ : syracuseStep 3067723 = 4601585) B4601585
theorem B4312925 : Blo 850355 4312925 := bstep (se 3 (by rfl) ⟨808673, by rfl⟩ : syracuseStep 4312925 = 1617347) B1617347
theorem B2871233 : Blo 850355 2871233 := bstep (se 2 (by rfl) ⟨1076712, by rfl⟩ : syracuseStep 2871233 = 2153425) B2153425
theorem B1921049 : Blo 850355 1921049 := bstep (se 2 (by rfl) ⟨720393, by rfl⟩ : syracuseStep 1921049 = 1440787) B1440787
theorem B3231809 : Blo 850355 3231809 := bstep (se 2 (by rfl) ⟨1211928, by rfl⟩ : syracuseStep 3231809 = 2423857) B2423857
theorem B5525597 : Blo 850355 5525597 := bstep (se 3 (by rfl) ⟨1036049, by rfl⟩ : syracuseStep 5525597 = 2072099) B2072099
theorem B1921139 : Blo 850355 1921139 := bstep (se 1 (by rfl) ⟨1440854, by rfl⟩ : syracuseStep 1921139 = 2881709) B2881709
theorem B1921175 : Blo 850355 1921175 := bstep (se 1 (by rfl) ⟨1440881, by rfl⟩ : syracuseStep 1921175 = 2881763) B2881763
theorem B14569793 : Blo 850355 14569793 := bstep (se 2 (by rfl) ⟨5463672, by rfl⟩ : syracuseStep 14569793 = 10927345) B10927345
theorem B1921355 : Blo 850355 1921355 := bstep (se 1 (by rfl) ⟨1441016, by rfl⟩ : syracuseStep 1921355 = 2882033) B2882033
theorem B1921409 : Blo 850355 1921409 := bstep (se 2 (by rfl) ⟨720528, by rfl⟩ : syracuseStep 1921409 = 1441057) B1441057
theorem B3330497 : Blo 850355 3330497 := bstep (se 2 (by rfl) ⟨1248936, by rfl⟩ : syracuseStep 3330497 = 2497873) B2497873
theorem B2871773 : Blo 850355 2871773 := bstep (se 3 (by rfl) ⟨538457, by rfl⟩ : syracuseStep 2871773 = 1076915) B1076915
theorem B1921625 : Blo 850355 1921625 := bstep (se 2 (by rfl) ⟨720609, by rfl⟩ : syracuseStep 1921625 = 1441219) B1441219
theorem B1921715 : Blo 850355 1921715 := bstep (se 1 (by rfl) ⟨1441286, by rfl⟩ : syracuseStep 1921715 = 2882573) B2882573
theorem B1364683 : Blo 850355 1364683 := bstep (se 1 (by rfl) ⟨1023512, by rfl⟩ : syracuseStep 1364683 = 2047025) B2047025
theorem B1921751 : Blo 850355 1921751 := bstep (se 1 (by rfl) ⟨1441313, by rfl⟩ : syracuseStep 1921751 = 2882627) B2882627
theorem B1921931 : Blo 850355 1921931 := bstep (se 1 (by rfl) ⟨1441448, by rfl⟩ : syracuseStep 1921931 = 2882897) B2882897
theorem B1921985 : Blo 850355 1921985 := bstep (se 2 (by rfl) ⟨720744, by rfl⟩ : syracuseStep 1921985 = 1441489) B1441489
theorem B1364939 : Blo 850355 1364939 := bstep (se 1 (by rfl) ⟨1023704, by rfl⟩ : syracuseStep 1364939 = 2047409) B2047409
theorem B1922201 : Blo 850355 1922201 := bstep (se 2 (by rfl) ⟨720825, by rfl⟩ : syracuseStep 1922201 = 1441651) B1441651
theorem B1922291 : Blo 850355 1922291 := bstep (se 1 (by rfl) ⟨1441718, by rfl⟩ : syracuseStep 1922291 = 2883437) B2883437
theorem B3462659 : Blo 850355 3462659 := bstep (se 1 (by rfl) ⟨2596994, by rfl⟩ : syracuseStep 3462659 = 5193989) B5193989
theorem B3233297 : Blo 850355 3233297 := bstep (se 2 (by rfl) ⟨1212486, by rfl⟩ : syracuseStep 3233297 = 2424973) B2424973
theorem B2872907 : Blo 850355 2872907 := bstep (se 1 (by rfl) ⟨2154680, by rfl⟩ : syracuseStep 2872907 = 4309361) B4309361
theorem B2184779 : Blo 850355 2184779 := bstep (se 1 (by rfl) ⟨1638584, by rfl⟩ : syracuseStep 2184779 = 3277169) B3277169
theorem B2873177 : Blo 850355 2873177 := bstep (se 2 (by rfl) ⟨1077441, by rfl⟩ : syracuseStep 2873177 = 2154883) B2154883
theorem B4315031 : Blo 850355 4315031 := bstep (se 1 (by rfl) ⟨3236273, by rfl⟩ : syracuseStep 4315031 = 6472547) B6472547
theorem B1365913 : Blo 850355 1365913 := bstep (se 2 (by rfl) ⟨512217, by rfl⟩ : syracuseStep 1365913 = 1024435) B1024435
theorem B10901465 : Blo 850355 10901465 := bstep (se 2 (by rfl) ⟨4088049, by rfl⟩ : syracuseStep 10901465 = 8176099) B8176099
theorem B3233753 : Blo 850355 3233753 := bstep (se 2 (by rfl) ⟨1212657, by rfl⟩ : syracuseStep 3233753 = 2425315) B2425315
theorem B3233965 : Blo 850355 3233965 := bstep (se 3 (by rfl) ⟨606368, by rfl⟩ : syracuseStep 3233965 = 1212737) B1212737
theorem B6150323 : Blo 850355 6150323 := bstep (se 1 (by rfl) ⟨4612742, by rfl⟩ : syracuseStep 6150323 = 9225485) B9225485
theorem B2152727 : Blo 850355 2152727 := bstep (se 1 (by rfl) ⟨1614545, by rfl⟩ : syracuseStep 2152727 = 3229091) B3229091
theorem B3889559 : Blo 850355 3889559 := bstep (se 1 (by rfl) ⟨2917169, by rfl⟩ : syracuseStep 3889559 = 5834339) B5834339
theorem B3234269 : Blo 850355 3234269 := bstep (se 3 (by rfl) ⟨606425, by rfl⟩ : syracuseStep 3234269 = 1212851) B1212851
theorem B2873879 : Blo 850355 2873879 := bstep (se 1 (by rfl) ⟨2155409, by rfl⟩ : syracuseStep 2873879 = 4310819) B4310819
theorem B3070723 : Blo 850355 3070723 := bstep (se 1 (by rfl) ⟨2303042, by rfl⟩ : syracuseStep 3070723 = 4606085) B4606085
theorem B2186135 : Blo 850355 2186135 := bstep (se 1 (by rfl) ⟨1639601, by rfl⟩ : syracuseStep 2186135 = 3279203) B3279203
theorem B1727411 : Blo 850355 1727411 := bstep (se 1 (by rfl) ⟨1295558, by rfl⟩ : syracuseStep 1727411 = 2591117) B2591117
theorem B6478865 : Blo 850355 6478865 := bstep (se 2 (by rfl) ⟨2429574, by rfl⟩ : syracuseStep 6478865 = 4859149) B4859149
theorem B2874419 : Blo 850355 2874419 := bstep (se 1 (by rfl) ⟨2155814, by rfl⟩ : syracuseStep 2874419 = 4311629) B4311629
theorem B2153537 : Blo 850355 2153537 := bstep (se 2 (by rfl) ⟨807576, by rfl⟩ : syracuseStep 2153537 = 1615153) B1615153
theorem B2874689 : Blo 850355 2874689 := bstep (se 2 (by rfl) ⟨1078008, by rfl⟩ : syracuseStep 2874689 = 2156017) B2156017
theorem B2186585 : Blo 850355 2186585 := bstep (se 2 (by rfl) ⟨819969, by rfl⟩ : syracuseStep 2186585 = 1639939) B1639939
theorem B1727833 : Blo 850355 1727833 := bstep (se 2 (by rfl) ⟨647937, by rfl⟩ : syracuseStep 1727833 = 1295875) B1295875
theorem B908695 : Blo 850355 908695 := bstep (se 1 (by rfl) ⟨681521, by rfl⟩ : syracuseStep 908695 = 1363043) B1363043
theorem B7396759 : Blo 850355 7396759 := bstep (se 1 (by rfl) ⟨5547569, by rfl⟩ : syracuseStep 7396759 = 11095139) B11095139
theorem B974251 : Blo 850355 974251 := bstep (se 1 (by rfl) ⟨730688, by rfl⟩ : syracuseStep 974251 = 1461377) B1461377
theorem B2154073 : Blo 850355 2154073 := bstep (se 2 (by rfl) ⟨807777, by rfl⟩ : syracuseStep 2154073 = 1615555) B1615555
theorem B18472769 : Blo 850355 18472769 := bstep (se 2 (by rfl) ⟨6927288, by rfl⟩ : syracuseStep 18472769 = 13854577) B13854577
theorem B2875229 : Blo 850355 2875229 := bstep (se 3 (by rfl) ⟨539105, by rfl⟩ : syracuseStep 2875229 = 1078211) B1078211
theorem B7495517 : Blo 850355 7495517 := bstep (se 3 (by rfl) ⟨1405409, by rfl⟩ : syracuseStep 7495517 = 2810819) B2810819
theorem B6545585 : Blo 850355 6545585 := bstep (se 2 (by rfl) ⟨2454594, by rfl⟩ : syracuseStep 6545585 = 4909189) B4909189
theorem B909515 : Blo 850355 909515 := bstep (se 1 (by rfl) ⟨682136, by rfl⟩ : syracuseStep 909515 = 1364273) B1364273
theorem B3498461 : Blo 850355 3498461 := bstep (se 3 (by rfl) ⟨655961, by rfl⟩ : syracuseStep 3498461 = 1311923) B1311923
theorem B2155187 : Blo 850355 2155187 := bstep (se 1 (by rfl) ⟨1616390, by rfl⟩ : syracuseStep 2155187 = 3232781) B3232781
theorem B3891929 : Blo 850355 3891929 := bstep (se 2 (by rfl) ⟨1459473, by rfl⟩ : syracuseStep 3891929 = 2918947) B2918947
theorem B6152921 : Blo 850355 6152921 := bstep (se 2 (by rfl) ⟨2307345, by rfl⟩ : syracuseStep 6152921 = 4614691) B4614691
theorem B1532695 : Blo 850355 1532695 := bstep (se 1 (by rfl) ⟨1149521, by rfl⟩ : syracuseStep 1532695 = 2299043) B2299043
theorem B1532737 : Blo 850355 1532737 := bstep (se 2 (by rfl) ⟨574776, by rfl⟩ : syracuseStep 1532737 = 1149553) B1149553
theorem B2876363 : Blo 850355 2876363 := bstep (se 1 (by rfl) ⟨2157272, by rfl⟩ : syracuseStep 2876363 = 4314545) B4314545
theorem B3072971 : Blo 850355 3072971 := bstep (se 1 (by rfl) ⟨2304728, by rfl⟩ : syracuseStep 3072971 = 4609457) B4609457
theorem B2155481 : Blo 850355 2155481 := bstep (se 2 (by rfl) ⟨808305, by rfl⟩ : syracuseStep 2155481 = 1616611) B1616611
theorem B3236867 : Blo 850355 3236867 := bstep (se 1 (by rfl) ⟨2427650, by rfl⟩ : syracuseStep 3236867 = 4855301) B4855301
theorem B1532939 : Blo 850355 1532939 := bstep (se 1 (by rfl) ⟨1149704, by rfl⟩ : syracuseStep 1532939 = 2299409) B2299409
theorem B3236881 : Blo 850355 3236881 := bstep (se 2 (by rfl) ⟨1213830, by rfl⟩ : syracuseStep 3236881 = 2427661) B2427661
theorem B2876633 : Blo 850355 2876633 := bstep (se 2 (by rfl) ⟨1078737, by rfl⟩ : syracuseStep 2876633 = 2157475) B2157475
theorem B2188595 : Blo 850355 2188595 := bstep (se 1 (by rfl) ⟨1641446, by rfl⟩ : syracuseStep 2188595 = 3282893) B3282893
theorem B3237185 : Blo 850355 3237185 := bstep (se 2 (by rfl) ⟨1213944, by rfl⟩ : syracuseStep 3237185 = 2427889) B2427889
theorem B910711 : Blo 850355 910711 := bstep (se 1 (by rfl) ⟨683033, by rfl⟩ : syracuseStep 910711 = 1366067) B1366067
theorem B4318595 : Blo 850355 4318595 := bstep (se 1 (by rfl) ⟨3238946, by rfl⟩ : syracuseStep 4318595 = 6477893) B6477893
theorem B5465495 : Blo 850355 5465495 := bstep (se 1 (by rfl) ⟨4099121, by rfl⟩ : syracuseStep 5465495 = 8198243) B8198243
theorem B1435097 : Blo 850355 1435097 := bstep (se 2 (by rfl) ⟨538161, by rfl⟩ : syracuseStep 1435097 = 1076323) B1076323
theorem B1533401 : Blo 850355 1533401 := bstep (se 2 (by rfl) ⟨575025, by rfl⟩ : syracuseStep 1533401 = 1150051) B1150051
theorem B1435225 : Blo 850355 1435225 := bstep (se 2 (by rfl) ⟨538209, by rfl⟩ : syracuseStep 1435225 = 1076419) B1076419
theorem B1730251 : Blo 850355 1730251 := bstep (se 1 (by rfl) ⟨1297688, by rfl⟩ : syracuseStep 1730251 = 2595377) B2595377
theorem B7366349 : Blo 850355 7366349 := bstep (se 3 (by rfl) ⟨1381190, by rfl⟩ : syracuseStep 7366349 = 2762381) B2762381
theorem B2877335 : Blo 850355 2877335 := bstep (se 1 (by rfl) ⟨2158001, by rfl⟩ : syracuseStep 2877335 = 4316003) B4316003
theorem B3237853 : Blo 850355 3237853 := bstep (se 3 (by rfl) ⟨607097, by rfl⟩ : syracuseStep 3237853 = 1214195) B1214195
theorem B1435799 : Blo 850355 1435799 := bstep (se 1 (by rfl) ⟨1076849, by rfl⟩ : syracuseStep 1435799 = 2153699) B2153699
theorem B3500183 : Blo 850355 3500183 := bstep (se 1 (by rfl) ⟨2625137, by rfl⟩ : syracuseStep 3500183 = 5250275) B5250275
theorem B911531 : Blo 850355 911531 := bstep (se 1 (by rfl) ⟨683648, by rfl⟩ : syracuseStep 911531 = 1367297) B1367297
theorem B1435927 : Blo 850355 1435927 := bstep (se 1 (by rfl) ⟨1076945, by rfl⟩ : syracuseStep 1435927 = 2153891) B2153891
theorem B1534295 : Blo 850355 1534295 := bstep (se 1 (by rfl) ⟨1150721, by rfl⟩ : syracuseStep 1534295 = 2301443) B2301443
theorem B2877875 : Blo 850355 2877875 := bstep (se 1 (by rfl) ⟨2158406, by rfl⟩ : syracuseStep 2877875 = 4316813) B4316813
theorem B2157131 : Blo 850355 2157131 := bstep (se 1 (by rfl) ⟨1617848, by rfl⟩ : syracuseStep 2157131 = 3235697) B3235697
theorem B7269041 : Blo 850355 7269041 := bstep (se 2 (by rfl) ⟨2725890, by rfl⟩ : syracuseStep 7269041 = 5451781) B5451781
theorem B2878145 : Blo 850355 2878145 := bstep (se 2 (by rfl) ⟨1079304, by rfl⟩ : syracuseStep 2878145 = 2158609) B2158609
theorem B10906433 : Blo 850355 10906433 := bstep (se 2 (by rfl) ⟨4089912, by rfl⟩ : syracuseStep 10906433 = 8179825) B8179825
theorem B6482753 : Blo 850355 6482753 := bstep (se 2 (by rfl) ⟨2431032, by rfl⟩ : syracuseStep 6482753 = 4862065) B4862065
theorem B1436555 : Blo 850355 1436555 := bstep (se 1 (by rfl) ⟨1077416, by rfl⟩ : syracuseStep 1436555 = 2154833) B2154833
theorem B1436683 : Blo 850355 1436683 := bstep (se 1 (by rfl) ⟨1077512, by rfl⟩ : syracuseStep 1436683 = 2155025) B2155025
theorem B1436825 : Blo 850355 1436825 := bstep (se 2 (by rfl) ⟨538809, by rfl⟩ : syracuseStep 1436825 = 1077619) B1077619
theorem B3239129 : Blo 850355 3239129 := bstep (se 2 (by rfl) ⟨1214673, by rfl⟩ : syracuseStep 3239129 = 2429347) B2429347
theorem B2878685 : Blo 850355 2878685 := bstep (se 3 (by rfl) ⟨539753, by rfl⟩ : syracuseStep 2878685 = 1079507) B1079507
theorem B1436953 : Blo 850355 1436953 := bstep (se 2 (by rfl) ⟨538857, by rfl⟩ : syracuseStep 1436953 = 1077715) B1077715
theorem B2158103 : Blo 850355 2158103 := bstep (se 1 (by rfl) ⟨1618577, by rfl⟩ : syracuseStep 2158103 = 3237155) B3237155
theorem B3632813 : Blo 850355 3632813 := bstep (se 3 (by rfl) ⟨681152, by rfl⟩ : syracuseStep 3632813 = 1362305) B1362305
theorem B1077067 : Blo 850355 1077067 := bstep (se 1 (by rfl) ⟨807800, by rfl⟩ : syracuseStep 1077067 = 1615601) B1615601
theorem B5467979 : Blo 850355 5467979 := bstep (se 1 (by rfl) ⟨4100984, by rfl⟩ : syracuseStep 5467979 = 8201969) B8201969
theorem B1437527 : Blo 850355 1437527 := bstep (se 1 (by rfl) ⟨1078145, by rfl⟩ : syracuseStep 1437527 = 2156291) B2156291
theorem B4091741 : Blo 850355 4091741 := bstep (se 3 (by rfl) ⟨767201, by rfl⟩ : syracuseStep 4091741 = 1534403) B1534403
theorem B1437655 : Blo 850355 1437655 := bstep (se 1 (by rfl) ⟨1078241, by rfl⟩ : syracuseStep 1437655 = 2156483) B2156483
theorem B6156323 : Blo 850355 6156323 := bstep (se 1 (by rfl) ⟨4617242, by rfl⟩ : syracuseStep 6156323 = 9234485) B9234485
theorem B5173379 : Blo 850355 5173379 := bstep (se 1 (by rfl) ⟨3880034, by rfl⟩ : syracuseStep 5173379 = 7760069) B7760069
theorem B2191511 : Blo 850355 2191511 := bstep (se 1 (by rfl) ⟨1643633, by rfl⟩ : syracuseStep 2191511 = 3287267) B3287267
theorem B2158771 : Blo 850355 2158771 := bstep (se 1 (by rfl) ⟨1619078, by rfl⟩ : syracuseStep 2158771 = 3238157) B3238157
theorem B2158913 : Blo 850355 2158913 := bstep (se 2 (by rfl) ⟨809592, by rfl⟩ : syracuseStep 2158913 = 1619185) B1619185
theorem B2879819 : Blo 850355 2879819 := bstep (se 1 (by rfl) ⟨2159864, by rfl⟩ : syracuseStep 2879819 = 4319729) B4319729
theorem B3633497 : Blo 850355 3633497 := bstep (se 2 (by rfl) ⟨1362561, by rfl⟩ : syracuseStep 3633497 = 2725123) B2725123
theorem B1438283 : Blo 850355 1438283 := bstep (se 1 (by rfl) ⟨1078712, by rfl⟩ : syracuseStep 1438283 = 2157425) B2157425
theorem B2880089 : Blo 850355 2880089 := bstep (se 2 (by rfl) ⟨1080033, by rfl⟩ : syracuseStep 2880089 = 2160067) B2160067
theorem B1438411 : Blo 850355 1438411 := bstep (se 1 (by rfl) ⟨1078808, by rfl⟩ : syracuseStep 1438411 = 2157617) B2157617
theorem B12284621 : Blo 850355 12284621 := bstep (se 3 (by rfl) ⟨2303366, by rfl⟩ : syracuseStep 12284621 = 4606733) B4606733
theorem B6484697 : Blo 850355 6484697 := bstep (se 2 (by rfl) ⟨2431761, by rfl⟩ : syracuseStep 6484697 = 4863523) B4863523
theorem B6157073 : Blo 850355 6157073 := bstep (se 2 (by rfl) ⟨2308902, by rfl⟩ : syracuseStep 6157073 = 4617805) B4617805
theorem B1078039 : Blo 850355 1078039 := bstep (se 1 (by rfl) ⟨808529, by rfl⟩ : syracuseStep 1078039 = 1617059) B1617059
theorem B3240755 : Blo 850355 3240755 := bstep (se 1 (by rfl) ⟨2430566, by rfl⟩ : syracuseStep 3240755 = 4861133) B4861133
theorem B3240769 : Blo 850355 3240769 := bstep (se 2 (by rfl) ⟨1215288, by rfl⟩ : syracuseStep 3240769 = 2430577) B2430577
theorem B1438553 : Blo 850355 1438553 := bstep (se 2 (by rfl) ⟨539457, by rfl⟩ : syracuseStep 1438553 = 1078915) B1078915
theorem B4846553 : Blo 850355 4846553 := bstep (se 2 (by rfl) ⟨1817457, by rfl⟩ : syracuseStep 4846553 = 3634915) B3634915
theorem B1438681 : Blo 850355 1438681 := bstep (se 2 (by rfl) ⟨539505, by rfl⟩ : syracuseStep 1438681 = 1079011) B1079011
theorem B4322321 : Blo 850355 4322321 := bstep (se 2 (by rfl) ⟨1620870, by rfl⟩ : syracuseStep 4322321 = 3241741) B3241741
theorem B6911041 : Blo 850355 6911041 := bstep (se 2 (by rfl) ⟨2591640, by rfl⟩ : syracuseStep 6911041 = 5183281) B5183281
theorem B4322483 : Blo 850355 4322483 := bstep (se 1 (by rfl) ⟨3241862, by rfl⟩ : syracuseStep 4322483 = 6483725) B6483725
theorem B4617395 : Blo 850355 4617395 := bstep (se 1 (by rfl) ⟨3463046, by rfl⟩ : syracuseStep 4617395 = 6926093) B6926093
theorem B5174545 : Blo 850355 5174545 := bstep (se 2 (by rfl) ⟨1940454, by rfl⟩ : syracuseStep 5174545 = 3880909) B3880909
theorem B2880791 : Blo 850355 2880791 := bstep (se 1 (by rfl) ⟨2160593, by rfl⟩ : syracuseStep 2880791 = 4321187) B4321187
theorem B6550885 : Blo 850355 6550885 := bstep (se 4 (by rfl) ⟨614145, by rfl⟩ : syracuseStep 6550885 = 1228291) B1228291
theorem B5469619 : Blo 850355 5469619 := bstep (se 1 (by rfl) ⟨4102214, by rfl⟩ : syracuseStep 5469619 = 8204429) B8204429
theorem B1439255 : Blo 850355 1439255 := bstep (se 1 (by rfl) ⟨1079441, by rfl⟩ : syracuseStep 1439255 = 2158883) B2158883
theorem B2160179 : Blo 850355 2160179 := bstep (se 1 (by rfl) ⟨1620134, by rfl⟩ : syracuseStep 2160179 = 3240269) B3240269
theorem B2455105 : Blo 850355 2455105 := bstep (se 2 (by rfl) ⟨920664, by rfl⟩ : syracuseStep 2455105 = 1841329) B1841329
theorem B1078859 : Blo 850355 1078859 := bstep (se 1 (by rfl) ⟨809144, by rfl⟩ : syracuseStep 1078859 = 1618289) B1618289
theorem B1439383 : Blo 850355 1439383 := bstep (se 1 (by rfl) ⟨1079537, by rfl⟩ : syracuseStep 1439383 = 2159075) B2159075
theorem B1275545 : Blo 850355 1275545 := bstep (se 2 (by rfl) ⟨478329, by rfl⟩ : syracuseStep 1275545 = 956659) B956659
theorem B1275659 : Blo 850355 1275659 := bstep (se 1 (by rfl) ⟨956744, by rfl⟩ : syracuseStep 1275659 = 1913489) B1913489
theorem B1275671 : Blo 850355 1275671 := bstep (se 1 (by rfl) ⟨956753, by rfl⟩ : syracuseStep 1275671 = 1913507) B1913507
theorem B2881331 : Blo 850355 2881331 := bstep (se 1 (by rfl) ⟨2160998, by rfl⟩ : syracuseStep 2881331 = 4321997) B4321997
theorem B1275737 : Blo 850355 1275737 := bstep (se 2 (by rfl) ⟨478401, by rfl⟩ : syracuseStep 1275737 = 956803) B956803
theorem B1537985 : Blo 850355 1537985 := bstep (se 2 (by rfl) ⟨576744, by rfl⟩ : syracuseStep 1537985 = 1153489) B1153489
theorem B1275851 : Blo 850355 1275851 := bstep (se 1 (by rfl) ⟨956888, by rfl⟩ : syracuseStep 1275851 = 1913777) B1913777
theorem B1275863 : Blo 850355 1275863 := bstep (se 1 (by rfl) ⟨956897, by rfl⟩ : syracuseStep 1275863 = 1913795) B1913795
theorem B1275929 : Blo 850355 1275929 := bstep (se 2 (by rfl) ⟨478473, by rfl⟩ : syracuseStep 1275929 = 956947) B956947
theorem B2881601 : Blo 850355 2881601 := bstep (se 2 (by rfl) ⟨1080600, by rfl⟩ : syracuseStep 2881601 = 2161201) B2161201
theorem B2160715 : Blo 850355 2160715 := bstep (se 1 (by rfl) ⟨1620536, by rfl⟩ : syracuseStep 2160715 = 3241073) B3241073
theorem B1276043 : Blo 850355 1276043 := bstep (se 1 (by rfl) ⟨957032, by rfl⟩ : syracuseStep 1276043 = 1914065) B1914065
theorem B1276055 : Blo 850355 1276055 := bstep (se 1 (by rfl) ⟨957041, by rfl⟩ : syracuseStep 1276055 = 1914083) B1914083
theorem B1276121 : Blo 850355 1276121 := bstep (se 2 (by rfl) ⟨478545, by rfl⟩ : syracuseStep 1276121 = 957091) B957091
theorem B7272665 : Blo 850355 7272665 := bstep (se 2 (by rfl) ⟨2727249, by rfl⟩ : syracuseStep 7272665 = 5454499) B5454499
theorem B2160857 : Blo 850355 2160857 := bstep (se 2 (by rfl) ⟨810321, by rfl⟩ : syracuseStep 2160857 = 1620643) B1620643
theorem B1079563 : Blo 850355 1079563 := bstep (se 1 (by rfl) ⟨809672, by rfl⟩ : syracuseStep 1079563 = 1619345) B1619345
theorem B1440011 : Blo 850355 1440011 := bstep (se 1 (by rfl) ⟨1080008, by rfl⟩ : syracuseStep 1440011 = 2160017) B2160017
theorem B2423105 : Blo 850355 2423105 := bstep (se 2 (by rfl) ⟨908664, by rfl⟩ : syracuseStep 2423105 = 1817329) B1817329
theorem B1276235 : Blo 850355 1276235 := bstep (se 1 (by rfl) ⟨957176, by rfl⟩ : syracuseStep 1276235 = 1914353) B1914353
theorem B1276247 : Blo 850355 1276247 := bstep (se 1 (by rfl) ⟨957185, by rfl⟩ : syracuseStep 1276247 = 1914371) B1914371
theorem B1440139 : Blo 850355 1440139 := bstep (se 1 (by rfl) ⟨1080104, by rfl⟩ : syracuseStep 1440139 = 2160209) B2160209
theorem B1276313 : Blo 850355 1276313 := bstep (se 2 (by rfl) ⟨478617, by rfl⟩ : syracuseStep 1276313 = 957235) B957235
theorem B850359 : Blo 850355 850359 := bstep (se 1 (by rfl) ⟨637769, by rfl⟩ : syracuseStep 850359 = 1275539) B1275539
theorem B850379 : Blo 850355 850379 := bstep (se 1 (by rfl) ⟨637784, by rfl⟩ : syracuseStep 850379 = 1275569) B1275569
theorem B850391 : Blo 850355 850391 := bstep (se 1 (by rfl) ⟨637793, by rfl⟩ : syracuseStep 850391 = 1275587) B1275587
theorem B850411 : Blo 850355 850411 := bstep (se 1 (by rfl) ⟨637808, by rfl⟩ : syracuseStep 850411 = 1275617) B1275617
theorem B850423 : Blo 850355 850423 := bstep (se 1 (by rfl) ⟨637817, by rfl⟩ : syracuseStep 850423 = 1275635) B1275635
theorem B850443 : Blo 850355 850443 := bstep (se 1 (by rfl) ⟨637832, by rfl⟩ : syracuseStep 850443 = 1275665) B1275665
theorem B1276427 : Blo 850355 1276427 := bstep (se 1 (by rfl) ⟨957320, by rfl⟩ : syracuseStep 1276427 = 1914641) B1914641
theorem B850455 : Blo 850355 850455 := bstep (se 1 (by rfl) ⟨637841, by rfl⟩ : syracuseStep 850455 = 1275683) B1275683
theorem B1276439 : Blo 850355 1276439 := bstep (se 1 (by rfl) ⟨957329, by rfl⟩ : syracuseStep 1276439 = 1914659) B1914659
theorem B1440281 : Blo 850355 1440281 := bstep (se 2 (by rfl) ⟨540105, by rfl⟩ : syracuseStep 1440281 = 1080211) B1080211
theorem B1079831 : Blo 850355 1079831 := bstep (se 1 (by rfl) ⟨809873, by rfl⟩ : syracuseStep 1079831 = 1619747) B1619747
theorem B850475 : Blo 850355 850475 := bstep (se 1 (by rfl) ⟨637856, by rfl⟩ : syracuseStep 850475 = 1275713) B1275713
theorem B4094509 : Blo 850355 4094509 := bstep (se 3 (by rfl) ⟨767720, by rfl⟩ : syracuseStep 4094509 = 1535441) B1535441
theorem B850487 : Blo 850355 850487 := bstep (se 1 (by rfl) ⟨637865, by rfl⟩ : syracuseStep 850487 = 1275731) B1275731
theorem B850507 : Blo 850355 850507 := bstep (se 1 (by rfl) ⟨637880, by rfl⟩ : syracuseStep 850507 = 1275761) B1275761
theorem B1538635 : Blo 850355 1538635 := bstep (se 1 (by rfl) ⟨1153976, by rfl⟩ : syracuseStep 1538635 = 2307953) B2307953
theorem B850519 : Blo 850355 850519 := bstep (se 1 (by rfl) ⟨637889, by rfl⟩ : syracuseStep 850519 = 1275779) B1275779
theorem B1276505 : Blo 850355 1276505 := bstep (se 2 (by rfl) ⟨478689, by rfl⟩ : syracuseStep 1276505 = 957379) B957379
theorem B8190557 : Blo 850355 8190557 := bstep (se 3 (by rfl) ⟨1535729, by rfl⟩ : syracuseStep 8190557 = 3071459) B3071459
theorem B2882141 : Blo 850355 2882141 := bstep (se 3 (by rfl) ⟨540401, by rfl⟩ : syracuseStep 2882141 = 1080803) B1080803
theorem B850539 : Blo 850355 850539 := bstep (se 1 (by rfl) ⟨637904, by rfl⟩ : syracuseStep 850539 = 1275809) B1275809
theorem B850551 : Blo 850355 850551 := bstep (se 1 (by rfl) ⟨637913, by rfl⟩ : syracuseStep 850551 = 1275827) B1275827
theorem B9730691 : Blo 850355 9730691 := bstep (se 1 (by rfl) ⟨7298018, by rfl⟩ : syracuseStep 9730691 = 14596037) B14596037
theorem B850571 : Blo 850355 850571 := bstep (se 1 (by rfl) ⟨637928, by rfl⟩ : syracuseStep 850571 = 1275857) B1275857
theorem B850583 : Blo 850355 850583 := bstep (se 1 (by rfl) ⟨637937, by rfl⟩ : syracuseStep 850583 = 1275875) B1275875
theorem B1440409 : Blo 850355 1440409 := bstep (se 2 (by rfl) ⟨540153, by rfl⟩ : syracuseStep 1440409 = 1080307) B1080307
theorem B850603 : Blo 850355 850603 := bstep (se 1 (by rfl) ⟨637952, by rfl⟩ : syracuseStep 850603 = 1275905) B1275905
theorem B850615 : Blo 850355 850615 := bstep (se 1 (by rfl) ⟨637961, by rfl⟩ : syracuseStep 850615 = 1275923) B1275923
theorem B850635 : Blo 850355 850635 := bstep (se 1 (by rfl) ⟨637976, by rfl⟩ : syracuseStep 850635 = 1275953) B1275953
theorem B1276619 : Blo 850355 1276619 := bstep (se 1 (by rfl) ⟨957464, by rfl⟩ : syracuseStep 1276619 = 1914929) B1914929
theorem B3242699 : Blo 850355 3242699 := bstep (se 1 (by rfl) ⟨2432024, by rfl⟩ : syracuseStep 3242699 = 4864049) B4864049
theorem B850647 : Blo 850355 850647 := bstep (se 1 (by rfl) ⟨637985, by rfl⟩ : syracuseStep 850647 = 1275971) B1275971
theorem B1276631 : Blo 850355 1276631 := bstep (se 1 (by rfl) ⟨957473, by rfl⟩ : syracuseStep 1276631 = 1914947) B1914947
theorem B3242713 : Blo 850355 3242713 := bstep (se 2 (by rfl) ⟨1216017, by rfl⟩ : syracuseStep 3242713 = 2432035) B2432035
theorem B850667 : Blo 850355 850667 := bstep (se 1 (by rfl) ⟨638000, by rfl⟩ : syracuseStep 850667 = 1276001) B1276001
theorem B850679 : Blo 850355 850679 := bstep (se 1 (by rfl) ⟨638009, by rfl⟩ : syracuseStep 850679 = 1276019) B1276019
theorem B850699 : Blo 850355 850699 := bstep (se 1 (by rfl) ⟨638024, by rfl⟩ : syracuseStep 850699 = 1276049) B1276049
theorem B850711 : Blo 850355 850711 := bstep (se 1 (by rfl) ⟨638033, by rfl⟩ : syracuseStep 850711 = 1276067) B1276067
theorem B1276697 : Blo 850355 1276697 := bstep (se 2 (by rfl) ⟨478761, by rfl⟩ : syracuseStep 1276697 = 957523) B957523
theorem B850731 : Blo 850355 850731 := bstep (se 1 (by rfl) ⟨638048, by rfl⟩ : syracuseStep 850731 = 1276097) B1276097
theorem B850743 : Blo 850355 850743 := bstep (se 1 (by rfl) ⟨638057, by rfl⟩ : syracuseStep 850743 = 1276115) B1276115
theorem B850763 : Blo 850355 850763 := bstep (se 1 (by rfl) ⟨638072, by rfl⟩ : syracuseStep 850763 = 1276145) B1276145
theorem B850775 : Blo 850355 850775 := bstep (se 1 (by rfl) ⟨638081, by rfl⟩ : syracuseStep 850775 = 1276163) B1276163
theorem B2423641 : Blo 850355 2423641 := bstep (se 2 (by rfl) ⟨908865, by rfl⟩ : syracuseStep 2423641 = 1817731) B1817731
theorem B850795 : Blo 850355 850795 := bstep (se 1 (by rfl) ⟨638096, by rfl⟩ : syracuseStep 850795 = 1276193) B1276193
theorem B850807 : Blo 850355 850807 := bstep (se 1 (by rfl) ⟨638105, by rfl⟩ : syracuseStep 850807 = 1276211) B1276211
theorem B850827 : Blo 850355 850827 := bstep (se 1 (by rfl) ⟨638120, by rfl⟩ : syracuseStep 850827 = 1276241) B1276241
theorem B1276811 : Blo 850355 1276811 := bstep (se 1 (by rfl) ⟨957608, by rfl⟩ : syracuseStep 1276811 = 1915217) B1915217
theorem B850839 : Blo 850355 850839 := bstep (se 1 (by rfl) ⟨638129, by rfl⟩ : syracuseStep 850839 = 1276259) B1276259
theorem B1276823 : Blo 850355 1276823 := bstep (se 1 (by rfl) ⟨957617, by rfl⟩ : syracuseStep 1276823 = 1915235) B1915235
theorem B850859 : Blo 850355 850859 := bstep (se 1 (by rfl) ⟨638144, by rfl⟩ : syracuseStep 850859 = 1276289) B1276289
theorem B850871 : Blo 850355 850871 := bstep (se 1 (by rfl) ⟨638153, by rfl⟩ : syracuseStep 850871 = 1276307) B1276307
theorem B3636161 : Blo 850355 3636161 := bstep (se 2 (by rfl) ⟨1363560, by rfl⟩ : syracuseStep 3636161 = 2727121) B2727121
theorem B850891 : Blo 850355 850891 := bstep (se 1 (by rfl) ⟨638168, by rfl⟩ : syracuseStep 850891 = 1276337) B1276337
theorem B850903 : Blo 850355 850903 := bstep (se 1 (by rfl) ⟨638177, by rfl⟩ : syracuseStep 850903 = 1276355) B1276355
theorem B1276889 : Blo 850355 1276889 := bstep (se 2 (by rfl) ⟨478833, by rfl⟩ : syracuseStep 1276889 = 957667) B957667
theorem B850923 : Blo 850355 850923 := bstep (se 1 (by rfl) ⟨638192, by rfl⟩ : syracuseStep 850923 = 1276385) B1276385
theorem B850935 : Blo 850355 850935 := bstep (se 1 (by rfl) ⟨638201, by rfl⟩ : syracuseStep 850935 = 1276403) B1276403
theorem B850955 : Blo 850355 850955 := bstep (se 1 (by rfl) ⟨638216, by rfl⟩ : syracuseStep 850955 = 1276433) B1276433
theorem B850967 : Blo 850355 850967 := bstep (se 1 (by rfl) ⟨638225, by rfl⟩ : syracuseStep 850967 = 1276451) B1276451
theorem B2161687 : Blo 850355 2161687 := bstep (se 1 (by rfl) ⟨1621265, by rfl⟩ : syracuseStep 2161687 = 3242531) B3242531
theorem B850987 : Blo 850355 850987 := bstep (se 1 (by rfl) ⟨638240, by rfl⟩ : syracuseStep 850987 = 1276481) B1276481
theorem B850999 : Blo 850355 850999 := bstep (se 1 (by rfl) ⟨638249, by rfl⟩ : syracuseStep 850999 = 1276499) B1276499
theorem B949303 : Blo 850355 949303 := bstep (se 1 (by rfl) ⟨711977, by rfl⟩ : syracuseStep 949303 = 1423955) B1423955
theorem B851019 : Blo 850355 851019 := bstep (se 1 (by rfl) ⟨638264, by rfl⟩ : syracuseStep 851019 = 1276529) B1276529
theorem B1277003 : Blo 850355 1277003 := bstep (se 1 (by rfl) ⟨957752, by rfl⟩ : syracuseStep 1277003 = 1915505) B1915505
theorem B4324427 : Blo 850355 4324427 := bstep (se 1 (by rfl) ⟨3243320, by rfl⟩ : syracuseStep 4324427 = 6486641) B6486641
theorem B851031 : Blo 850355 851031 := bstep (se 1 (by rfl) ⟨638273, by rfl⟩ : syracuseStep 851031 = 1276547) B1276547
theorem B1277015 : Blo 850355 1277015 := bstep (se 1 (by rfl) ⟨957761, by rfl⟩ : syracuseStep 1277015 = 1915523) B1915523
theorem B851051 : Blo 850355 851051 := bstep (se 1 (by rfl) ⟨638288, by rfl⟩ : syracuseStep 851051 = 1276577) B1276577
theorem B851063 : Blo 850355 851063 := bstep (se 1 (by rfl) ⟨638297, by rfl⟩ : syracuseStep 851063 = 1276595) B1276595
theorem B851083 : Blo 850355 851083 := bstep (se 1 (by rfl) ⟨638312, by rfl⟩ : syracuseStep 851083 = 1276625) B1276625
theorem B851095 : Blo 850355 851095 := bstep (se 1 (by rfl) ⟨638321, by rfl⟩ : syracuseStep 851095 = 1276643) B1276643
theorem B1277081 : Blo 850355 1277081 := bstep (se 2 (by rfl) ⟨478905, by rfl⟩ : syracuseStep 1277081 = 957811) B957811
theorem B851115 : Blo 850355 851115 := bstep (se 1 (by rfl) ⟨638336, by rfl⟩ : syracuseStep 851115 = 1276673) B1276673
theorem B851127 : Blo 850355 851127 := bstep (se 1 (by rfl) ⟨638345, by rfl⟩ : syracuseStep 851127 = 1276691) B1276691
theorem B851147 : Blo 850355 851147 := bstep (se 1 (by rfl) ⟨638360, by rfl⟩ : syracuseStep 851147 = 1276721) B1276721
theorem B851159 : Blo 850355 851159 := bstep (se 1 (by rfl) ⟨638369, by rfl⟩ : syracuseStep 851159 = 1276739) B1276739
theorem B1080535 : Blo 850355 1080535 := bstep (se 1 (by rfl) ⟨810401, by rfl⟩ : syracuseStep 1080535 = 1620803) B1620803
theorem B1440983 : Blo 850355 1440983 := bstep (se 1 (by rfl) ⟨1080737, by rfl⟩ : syracuseStep 1440983 = 2161475) B2161475
theorem B851179 : Blo 850355 851179 := bstep (se 1 (by rfl) ⟨638384, by rfl⟩ : syracuseStep 851179 = 1276769) B1276769
theorem B851191 : Blo 850355 851191 := bstep (se 1 (by rfl) ⟨638393, by rfl⟩ : syracuseStep 851191 = 1276787) B1276787
theorem B851211 : Blo 850355 851211 := bstep (se 1 (by rfl) ⟨638408, by rfl⟩ : syracuseStep 851211 = 1276817) B1276817
theorem B1277195 : Blo 850355 1277195 := bstep (se 1 (by rfl) ⟨957896, by rfl⟩ : syracuseStep 1277195 = 1915793) B1915793
theorem B851223 : Blo 850355 851223 := bstep (se 1 (by rfl) ⟨638417, by rfl⟩ : syracuseStep 851223 = 1276835) B1276835
theorem B1277207 : Blo 850355 1277207 := bstep (se 1 (by rfl) ⟨957905, by rfl⟩ : syracuseStep 1277207 = 1915811) B1915811
theorem B851243 : Blo 850355 851243 := bstep (se 1 (by rfl) ⟨638432, by rfl⟩ : syracuseStep 851243 = 1276865) B1276865
theorem B851255 : Blo 850355 851255 := bstep (se 1 (by rfl) ⟨638441, by rfl⟩ : syracuseStep 851255 = 1276883) B1276883
theorem B2587979 : Blo 850355 2587979 := bstep (se 1 (by rfl) ⟨1940984, by rfl⟩ : syracuseStep 2587979 = 3881969) B3881969
theorem B851275 : Blo 850355 851275 := bstep (se 1 (by rfl) ⟨638456, by rfl⟩ : syracuseStep 851275 = 1276913) B1276913
theorem B851287 : Blo 850355 851287 := bstep (se 1 (by rfl) ⟨638465, by rfl⟩ : syracuseStep 851287 = 1276931) B1276931
theorem B1441111 : Blo 850355 1441111 := bstep (se 1 (by rfl) ⟨1080833, by rfl⟩ : syracuseStep 1441111 = 2161667) B2161667
theorem B1277273 : Blo 850355 1277273 := bstep (se 2 (by rfl) ⟨478977, by rfl⟩ : syracuseStep 1277273 = 957955) B957955
theorem B851307 : Blo 850355 851307 := bstep (se 1 (by rfl) ⟨638480, by rfl⟩ : syracuseStep 851307 = 1276961) B1276961
theorem B851319 : Blo 850355 851319 := bstep (se 1 (by rfl) ⟨638489, by rfl⟩ : syracuseStep 851319 = 1276979) B1276979
theorem B851339 : Blo 850355 851339 := bstep (se 1 (by rfl) ⟨638504, by rfl⟩ : syracuseStep 851339 = 1277009) B1277009
theorem B851351 : Blo 850355 851351 := bstep (se 1 (by rfl) ⟨638513, by rfl⟩ : syracuseStep 851351 = 1277027) B1277027
theorem B851371 : Blo 850355 851371 := bstep (se 1 (by rfl) ⟨638528, by rfl⟩ : syracuseStep 851371 = 1277057) B1277057
theorem B851383 : Blo 850355 851383 := bstep (se 1 (by rfl) ⟨638537, by rfl⟩ : syracuseStep 851383 = 1277075) B1277075
theorem B851403 : Blo 850355 851403 := bstep (se 1 (by rfl) ⟨638552, by rfl⟩ : syracuseStep 851403 = 1277105) B1277105
theorem B1277387 : Blo 850355 1277387 := bstep (se 1 (by rfl) ⟨958040, by rfl⟩ : syracuseStep 1277387 = 1916081) B1916081
theorem B2162123 : Blo 850355 2162123 := bstep (se 1 (by rfl) ⟨1621592, by rfl⟩ : syracuseStep 2162123 = 3243185) B3243185
theorem B851415 : Blo 850355 851415 := bstep (se 1 (by rfl) ⟨638561, by rfl⟩ : syracuseStep 851415 = 1277123) B1277123
theorem B1277399 : Blo 850355 1277399 := bstep (se 1 (by rfl) ⟨958049, by rfl⟩ : syracuseStep 1277399 = 1916099) B1916099
theorem B851435 : Blo 850355 851435 := bstep (se 1 (by rfl) ⟨638576, by rfl⟩ : syracuseStep 851435 = 1277153) B1277153
theorem B851447 : Blo 850355 851447 := bstep (se 1 (by rfl) ⟨638585, by rfl⟩ : syracuseStep 851447 = 1277171) B1277171
theorem B851467 : Blo 850355 851467 := bstep (se 1 (by rfl) ⟨638600, by rfl⟩ : syracuseStep 851467 = 1277201) B1277201
theorem B851479 : Blo 850355 851479 := bstep (se 1 (by rfl) ⟨638609, by rfl⟩ : syracuseStep 851479 = 1277219) B1277219
theorem B1277465 : Blo 850355 1277465 := bstep (se 2 (by rfl) ⟨479049, by rfl⟩ : syracuseStep 1277465 = 958099) B958099
theorem B851499 : Blo 850355 851499 := bstep (se 1 (by rfl) ⟨638624, by rfl⟩ : syracuseStep 851499 = 1277249) B1277249
theorem B851511 : Blo 850355 851511 := bstep (se 1 (by rfl) ⟨638633, by rfl⟩ : syracuseStep 851511 = 1277267) B1277267
theorem B4849217 : Blo 850355 4849217 := bstep (se 2 (by rfl) ⟨1818456, by rfl⟩ : syracuseStep 4849217 = 3636913) B3636913
theorem B851531 : Blo 850355 851531 := bstep (se 1 (by rfl) ⟨638648, by rfl⟩ : syracuseStep 851531 = 1277297) B1277297
theorem B851543 : Blo 850355 851543 := bstep (se 1 (by rfl) ⟨638657, by rfl⟩ : syracuseStep 851543 = 1277315) B1277315
theorem B851563 : Blo 850355 851563 := bstep (se 1 (by rfl) ⟨638672, by rfl⟩ : syracuseStep 851563 = 1277345) B1277345
theorem B851575 : Blo 850355 851575 := bstep (se 1 (by rfl) ⟨638681, by rfl⟩ : syracuseStep 851575 = 1277363) B1277363
theorem B851595 : Blo 850355 851595 := bstep (se 1 (by rfl) ⟨638696, by rfl⟩ : syracuseStep 851595 = 1277393) B1277393
theorem B1277579 : Blo 850355 1277579 := bstep (se 1 (by rfl) ⟨958184, by rfl⟩ : syracuseStep 1277579 = 1916369) B1916369
theorem B851607 : Blo 850355 851607 := bstep (se 1 (by rfl) ⟨638705, by rfl⟩ : syracuseStep 851607 = 1277411) B1277411
theorem B1277591 : Blo 850355 1277591 := bstep (se 1 (by rfl) ⟨958193, by rfl⟩ : syracuseStep 1277591 = 1916387) B1916387
theorem B3243671 : Blo 850355 3243671 := bstep (se 1 (by rfl) ⟨2432753, by rfl⟩ : syracuseStep 3243671 = 4865507) B4865507
theorem B851627 : Blo 850355 851627 := bstep (se 1 (by rfl) ⟨638720, by rfl⟩ : syracuseStep 851627 = 1277441) B1277441
theorem B851639 : Blo 850355 851639 := bstep (se 1 (by rfl) ⟨638729, by rfl⟩ : syracuseStep 851639 = 1277459) B1277459
theorem B851659 : Blo 850355 851659 := bstep (se 1 (by rfl) ⟨638744, by rfl⟩ : syracuseStep 851659 = 1277489) B1277489
theorem B2883275 : Blo 850355 2883275 := bstep (se 1 (by rfl) ⟨2162456, by rfl⟩ : syracuseStep 2883275 = 4324913) B4324913
theorem B851671 : Blo 850355 851671 := bstep (se 1 (by rfl) ⟨638753, by rfl⟩ : syracuseStep 851671 = 1277507) B1277507
theorem B1277657 : Blo 850355 1277657 := bstep (se 2 (by rfl) ⟨479121, by rfl⟩ : syracuseStep 1277657 = 958243) B958243
theorem B851691 : Blo 850355 851691 := bstep (se 1 (by rfl) ⟨638768, by rfl⟩ : syracuseStep 851691 = 1277537) B1277537
theorem B851703 : Blo 850355 851703 := bstep (se 1 (by rfl) ⟨638777, by rfl⟩ : syracuseStep 851703 = 1277555) B1277555
theorem B851723 : Blo 850355 851723 := bstep (se 1 (by rfl) ⟨638792, by rfl⟩ : syracuseStep 851723 = 1277585) B1277585
theorem B851735 : Blo 850355 851735 := bstep (se 1 (by rfl) ⟨638801, by rfl⟩ : syracuseStep 851735 = 1277603) B1277603
theorem B1212185 : Blo 850355 1212185 := bstep (se 2 (by rfl) ⟨454569, by rfl⟩ : syracuseStep 1212185 = 909139) B909139
theorem B851755 : Blo 850355 851755 := bstep (se 1 (by rfl) ⟨638816, by rfl⟩ : syracuseStep 851755 = 1277633) B1277633
theorem B851767 : Blo 850355 851767 := bstep (se 1 (by rfl) ⟨638825, by rfl⟩ : syracuseStep 851767 = 1277651) B1277651
theorem B2162497 : Blo 850355 2162497 := bstep (se 2 (by rfl) ⟨810936, by rfl⟩ : syracuseStep 2162497 = 1621873) B1621873
theorem B851787 : Blo 850355 851787 := bstep (se 1 (by rfl) ⟨638840, by rfl⟩ : syracuseStep 851787 = 1277681) B1277681
theorem B1277771 : Blo 850355 1277771 := bstep (se 1 (by rfl) ⟨958328, by rfl⟩ : syracuseStep 1277771 = 1916657) B1916657
theorem B851799 : Blo 850355 851799 := bstep (se 1 (by rfl) ⟨638849, by rfl⟩ : syracuseStep 851799 = 1277699) B1277699
theorem B1277783 : Blo 850355 1277783 := bstep (se 1 (by rfl) ⟨958337, by rfl⟩ : syracuseStep 1277783 = 1916675) B1916675
theorem B851819 : Blo 850355 851819 := bstep (se 1 (by rfl) ⟨638864, by rfl⟩ : syracuseStep 851819 = 1277729) B1277729
theorem B851831 : Blo 850355 851831 := bstep (se 1 (by rfl) ⟨638873, by rfl⟩ : syracuseStep 851831 = 1277747) B1277747
theorem B851851 : Blo 850355 851851 := bstep (se 1 (by rfl) ⟨638888, by rfl⟩ : syracuseStep 851851 = 1277777) B1277777
theorem B851863 : Blo 850355 851863 := bstep (se 1 (by rfl) ⟨638897, by rfl⟩ : syracuseStep 851863 = 1277795) B1277795
theorem B1277849 : Blo 850355 1277849 := bstep (se 2 (by rfl) ⟨479193, by rfl⟩ : syracuseStep 1277849 = 958387) B958387
theorem B851883 : Blo 850355 851883 := bstep (se 1 (by rfl) ⟨638912, by rfl⟩ : syracuseStep 851883 = 1277825) B1277825
theorem B851895 : Blo 850355 851895 := bstep (se 1 (by rfl) ⟨638921, by rfl⟩ : syracuseStep 851895 = 1277843) B1277843
theorem B851915 : Blo 850355 851915 := bstep (se 1 (by rfl) ⟨638936, by rfl⟩ : syracuseStep 851915 = 1277873) B1277873
theorem B851927 : Blo 850355 851927 := bstep (se 1 (by rfl) ⟨638945, by rfl⟩ : syracuseStep 851927 = 1277891) B1277891
theorem B851947 : Blo 850355 851947 := bstep (se 1 (by rfl) ⟨638960, by rfl⟩ : syracuseStep 851947 = 1277921) B1277921
theorem B851959 : Blo 850355 851959 := bstep (se 1 (by rfl) ⟨638969, by rfl⟩ : syracuseStep 851959 = 1277939) B1277939
theorem B851975 : Blo 850355 851975 := bstep (se 1 (by rfl) ⟨638981, by rfl⟩ : syracuseStep 851975 = 1277963) B1277963
theorem B5537803 : Blo 850355 5537803 := bstep (se 1 (by rfl) ⟨4153352, by rfl⟩ : syracuseStep 5537803 = 8306705) B8306705
theorem B851983 : Blo 850355 851983 := bstep (se 1 (by rfl) ⟨638987, by rfl⟩ : syracuseStep 851983 = 1277975) B1277975
theorem B1278011 : Blo 850355 1278011 := bstep (se 1 (by rfl) ⟨958508, by rfl⟩ : syracuseStep 1278011 = 1917017) B1917017
theorem B852027 : Blo 850355 852027 := bstep (se 1 (by rfl) ⟨639020, by rfl⟩ : syracuseStep 852027 = 1278041) B1278041
theorem B1278071 : Blo 850355 1278071 := bstep (se 1 (by rfl) ⟨958553, by rfl⟩ : syracuseStep 1278071 = 1917107) B1917107
theorem B852103 : Blo 850355 852103 := bstep (se 1 (by rfl) ⟨639077, by rfl⟩ : syracuseStep 852103 = 1278155) B1278155
theorem B1278095 : Blo 850355 1278095 := bstep (se 1 (by rfl) ⟨958571, by rfl⟩ : syracuseStep 1278095 = 1917143) B1917143
theorem B852111 : Blo 850355 852111 := bstep (se 1 (by rfl) ⟨639083, by rfl⟩ : syracuseStep 852111 = 1278167) B1278167
theorem B1278137 : Blo 850355 1278137 := bstep (se 2 (by rfl) ⟨479301, by rfl⟩ : syracuseStep 1278137 = 958603) B958603
theorem B852155 : Blo 850355 852155 := bstep (se 1 (by rfl) ⟨639116, by rfl⟩ : syracuseStep 852155 = 1278233) B1278233
theorem B4849901 : Blo 850355 4849901 := bstep (se 3 (by rfl) ⟨909356, by rfl⟩ : syracuseStep 4849901 = 1818713) B1818713
theorem B1278215 : Blo 850355 1278215 := bstep (se 1 (by rfl) ⟨958661, by rfl⟩ : syracuseStep 1278215 = 1917323) B1917323
theorem B852231 : Blo 850355 852231 := bstep (se 1 (by rfl) ⟨639173, by rfl⟩ : syracuseStep 852231 = 1278347) B1278347
theorem B2425099 : Blo 850355 2425099 := bstep (se 1 (by rfl) ⟨1818824, by rfl⟩ : syracuseStep 2425099 = 3637649) B3637649
theorem B852239 : Blo 850355 852239 := bstep (se 1 (by rfl) ⟨639179, by rfl⟩ : syracuseStep 852239 = 1278359) B1278359
theorem B1278251 : Blo 850355 1278251 := bstep (se 1 (by rfl) ⟨958688, by rfl⟩ : syracuseStep 1278251 = 1917377) B1917377
theorem B852283 : Blo 850355 852283 := bstep (se 1 (by rfl) ⟨639212, by rfl⟩ : syracuseStep 852283 = 1278425) B1278425
theorem B1278281 : Blo 850355 1278281 := bstep (se 2 (by rfl) ⟨479355, by rfl⟩ : syracuseStep 1278281 = 958711) B958711
theorem B852359 : Blo 850355 852359 := bstep (se 1 (by rfl) ⟨639269, by rfl⟩ : syracuseStep 852359 = 1278539) B1278539
theorem B852367 : Blo 850355 852367 := bstep (se 1 (by rfl) ⟨639275, by rfl⟩ : syracuseStep 852367 = 1278551) B1278551
theorem B1278395 : Blo 850355 1278395 := bstep (se 1 (by rfl) ⟨958796, by rfl⟩ : syracuseStep 1278395 = 1917593) B1917593
theorem B852411 : Blo 850355 852411 := bstep (se 1 (by rfl) ⟨639308, by rfl⟩ : syracuseStep 852411 = 1278617) B1278617
theorem B1278455 : Blo 850355 1278455 := bstep (se 1 (by rfl) ⟨958841, by rfl⟩ : syracuseStep 1278455 = 1917683) B1917683
theorem B852487 : Blo 850355 852487 := bstep (se 1 (by rfl) ⟨639365, by rfl⟩ : syracuseStep 852487 = 1278731) B1278731
theorem B2490895 : Blo 850355 2490895 := bstep (se 1 (by rfl) ⟨1868171, by rfl⟩ : syracuseStep 2490895 = 3736343) B3736343
theorem B1278479 : Blo 850355 1278479 := bstep (se 1 (by rfl) ⟨958859, by rfl⟩ : syracuseStep 1278479 = 1917719) B1917719
theorem B852495 : Blo 850355 852495 := bstep (se 1 (by rfl) ⟨639371, by rfl⟩ : syracuseStep 852495 = 1278743) B1278743
theorem B2425373 : Blo 850355 2425373 := bstep (se 3 (by rfl) ⟨454757, by rfl⟩ : syracuseStep 2425373 = 909515) B909515
theorem B39387683 : Blo 850355 39387683 := bstep (se 1 (by rfl) ⟨29540762, by rfl⟩ : syracuseStep 39387683 = 59081525) B59081525
theorem B4850219 : Blo 850355 4850219 := bstep (se 1 (by rfl) ⟨3637664, by rfl⟩ : syracuseStep 4850219 = 7275329) B7275329
theorem B9208363 : Blo 850355 9208363 := bstep (se 1 (by rfl) ⟨6906272, by rfl⟩ : syracuseStep 9208363 = 13812545) B13812545
theorem B10388011 : Blo 850355 10388011 := bstep (se 1 (by rfl) ⟨7791008, by rfl⟩ : syracuseStep 10388011 = 15582017) B15582017
theorem B1278521 : Blo 850355 1278521 := bstep (se 2 (by rfl) ⟨479445, by rfl⟩ : syracuseStep 1278521 = 958891) B958891
theorem B852539 : Blo 850355 852539 := bstep (se 1 (by rfl) ⟨639404, by rfl⟩ : syracuseStep 852539 = 1278809) B1278809
theorem B1278599 : Blo 850355 1278599 := bstep (se 1 (by rfl) ⟨958949, by rfl⟩ : syracuseStep 1278599 = 1917899) B1917899
theorem B852615 : Blo 850355 852615 := bstep (se 1 (by rfl) ⟨639461, by rfl⟩ : syracuseStep 852615 = 1278923) B1278923
theorem B852623 : Blo 850355 852623 := bstep (se 1 (by rfl) ⟨639467, by rfl⟩ : syracuseStep 852623 = 1278935) B1278935
theorem B1278635 : Blo 850355 1278635 := bstep (se 1 (by rfl) ⟨958976, by rfl⟩ : syracuseStep 1278635 = 1917953) B1917953
theorem B852667 : Blo 850355 852667 := bstep (se 1 (by rfl) ⟨639500, by rfl⟩ : syracuseStep 852667 = 1279001) B1279001
theorem B1278665 : Blo 850355 1278665 := bstep (se 2 (by rfl) ⟨479499, by rfl⟩ : syracuseStep 1278665 = 958999) B958999
theorem B852743 : Blo 850355 852743 := bstep (se 1 (by rfl) ⟨639557, by rfl⟩ : syracuseStep 852743 = 1279115) B1279115
theorem B852751 : Blo 850355 852751 := bstep (se 1 (by rfl) ⟨639563, by rfl⟩ : syracuseStep 852751 = 1279127) B1279127
theorem B1278779 : Blo 850355 1278779 := bstep (se 1 (by rfl) ⟨959084, by rfl⟩ : syracuseStep 1278779 = 1918169) B1918169
theorem B852795 : Blo 850355 852795 := bstep (se 1 (by rfl) ⟨639596, by rfl⟩ : syracuseStep 852795 = 1279193) B1279193
theorem B1278839 : Blo 850355 1278839 := bstep (se 1 (by rfl) ⟨959129, by rfl⟩ : syracuseStep 1278839 = 1918259) B1918259
theorem B852871 : Blo 850355 852871 := bstep (se 1 (by rfl) ⟨639653, by rfl⟩ : syracuseStep 852871 = 1279307) B1279307
theorem B1278863 : Blo 850355 1278863 := bstep (se 1 (by rfl) ⟨959147, by rfl⟩ : syracuseStep 1278863 = 1918295) B1918295
theorem B852879 : Blo 850355 852879 := bstep (se 1 (by rfl) ⟨639659, by rfl⟩ : syracuseStep 852879 = 1279319) B1279319
theorem B1278905 : Blo 850355 1278905 := bstep (se 2 (by rfl) ⟨479589, by rfl⟩ : syracuseStep 1278905 = 959179) B959179
theorem B852923 : Blo 850355 852923 := bstep (se 1 (by rfl) ⟨639692, by rfl⟩ : syracuseStep 852923 = 1279385) B1279385
theorem B1278983 : Blo 850355 1278983 := bstep (se 1 (by rfl) ⟨959237, by rfl⟩ : syracuseStep 1278983 = 1918475) B1918475
theorem B852999 : Blo 850355 852999 := bstep (se 1 (by rfl) ⟨639749, by rfl⟩ : syracuseStep 852999 = 1279499) B1279499
theorem B853007 : Blo 850355 853007 := bstep (se 1 (by rfl) ⟨639755, by rfl⟩ : syracuseStep 853007 = 1279511) B1279511
theorem B1279019 : Blo 850355 1279019 := bstep (se 1 (by rfl) ⟨959264, by rfl⟩ : syracuseStep 1279019 = 1918529) B1918529
theorem B853051 : Blo 850355 853051 := bstep (se 1 (by rfl) ⟨639788, by rfl⟩ : syracuseStep 853051 = 1279577) B1279577
theorem B1279049 : Blo 850355 1279049 := bstep (se 2 (by rfl) ⟨479643, by rfl⟩ : syracuseStep 1279049 = 959287) B959287
theorem B853127 : Blo 850355 853127 := bstep (se 1 (by rfl) ⟨639845, by rfl⟩ : syracuseStep 853127 = 1279691) B1279691
theorem B853135 : Blo 850355 853135 := bstep (se 1 (by rfl) ⟨639851, by rfl⟩ : syracuseStep 853135 = 1279703) B1279703
theorem B8881325 : Blo 850355 8881325 := bstep (se 3 (by rfl) ⟨1665248, by rfl⟩ : syracuseStep 8881325 = 3330497) B3330497
theorem B1279163 : Blo 850355 1279163 := bstep (se 1 (by rfl) ⟨959372, by rfl⟩ : syracuseStep 1279163 = 1918745) B1918745
theorem B853179 : Blo 850355 853179 := bstep (se 1 (by rfl) ⟨639884, by rfl⟩ : syracuseStep 853179 = 1279769) B1279769
theorem B1279223 : Blo 850355 1279223 := bstep (se 1 (by rfl) ⟨959417, by rfl⟩ : syracuseStep 1279223 = 1918835) B1918835
theorem B853255 : Blo 850355 853255 := bstep (se 1 (by rfl) ⟨639941, by rfl⟩ : syracuseStep 853255 = 1279883) B1279883
theorem B1279247 : Blo 850355 1279247 := bstep (se 1 (by rfl) ⟨959435, by rfl⟩ : syracuseStep 1279247 = 1918871) B1918871
theorem B853263 : Blo 850355 853263 := bstep (se 1 (by rfl) ⟨639947, by rfl⟩ : syracuseStep 853263 = 1279895) B1279895
theorem B1279289 : Blo 850355 1279289 := bstep (se 2 (by rfl) ⟨479733, by rfl⟩ : syracuseStep 1279289 = 959467) B959467
theorem B2917691 : Blo 850355 2917691 := bstep (se 1 (by rfl) ⟨2188268, by rfl⟩ : syracuseStep 2917691 = 4376537) B4376537
theorem B853307 : Blo 850355 853307 := bstep (se 1 (by rfl) ⟨639980, by rfl⟩ : syracuseStep 853307 = 1279961) B1279961
theorem B1279367 : Blo 850355 1279367 := bstep (se 1 (by rfl) ⟨959525, by rfl⟩ : syracuseStep 1279367 = 1919051) B1919051
theorem B853383 : Blo 850355 853383 := bstep (se 1 (by rfl) ⟨640037, by rfl⟩ : syracuseStep 853383 = 1280075) B1280075
theorem B853391 : Blo 850355 853391 := bstep (se 1 (by rfl) ⟨640043, by rfl⟩ : syracuseStep 853391 = 1280087) B1280087
theorem B1279403 : Blo 850355 1279403 := bstep (se 1 (by rfl) ⟨959552, by rfl⟩ : syracuseStep 1279403 = 1919105) B1919105
theorem B853435 : Blo 850355 853435 := bstep (se 1 (by rfl) ⟨640076, by rfl⟩ : syracuseStep 853435 = 1280153) B1280153
theorem B1279433 : Blo 850355 1279433 := bstep (se 2 (by rfl) ⟨479787, by rfl⟩ : syracuseStep 1279433 = 959575) B959575
theorem B853511 : Blo 850355 853511 := bstep (se 1 (by rfl) ⟨640133, by rfl⟩ : syracuseStep 853511 = 1280267) B1280267
theorem B853519 : Blo 850355 853519 := bstep (se 1 (by rfl) ⟨640139, by rfl⟩ : syracuseStep 853519 = 1280279) B1280279
theorem B1279547 : Blo 850355 1279547 := bstep (se 1 (by rfl) ⟨959660, by rfl⟩ : syracuseStep 1279547 = 1919321) B1919321
theorem B853563 : Blo 850355 853563 := bstep (se 1 (by rfl) ⟨640172, by rfl⟩ : syracuseStep 853563 = 1280345) B1280345
theorem B1279607 : Blo 850355 1279607 := bstep (se 1 (by rfl) ⟨959705, by rfl⟩ : syracuseStep 1279607 = 1919411) B1919411
theorem B853639 : Blo 850355 853639 := bstep (se 1 (by rfl) ⟨640229, by rfl⟩ : syracuseStep 853639 = 1280459) B1280459
theorem B1279631 : Blo 850355 1279631 := bstep (se 1 (by rfl) ⟨959723, by rfl⟩ : syracuseStep 1279631 = 1919447) B1919447
theorem B853647 : Blo 850355 853647 := bstep (se 1 (by rfl) ⟨640235, by rfl⟩ : syracuseStep 853647 = 1280471) B1280471
theorem B1279673 : Blo 850355 1279673 := bstep (se 2 (by rfl) ⟨479877, by rfl⟩ : syracuseStep 1279673 = 959755) B959755
theorem B853691 : Blo 850355 853691 := bstep (se 1 (by rfl) ⟨640268, by rfl⟩ : syracuseStep 853691 = 1280537) B1280537
theorem B1279751 : Blo 850355 1279751 := bstep (se 1 (by rfl) ⟨959813, by rfl⟩ : syracuseStep 1279751 = 1919627) B1919627
theorem B853767 : Blo 850355 853767 := bstep (se 1 (by rfl) ⟨640325, by rfl⟩ : syracuseStep 853767 = 1280651) B1280651
theorem B853775 : Blo 850355 853775 := bstep (se 1 (by rfl) ⟨640331, by rfl⟩ : syracuseStep 853775 = 1280663) B1280663
theorem B1279787 : Blo 850355 1279787 := bstep (se 1 (by rfl) ⟨959840, by rfl⟩ : syracuseStep 1279787 = 1919681) B1919681
theorem B853819 : Blo 850355 853819 := bstep (se 1 (by rfl) ⟨640364, by rfl⟩ : syracuseStep 853819 = 1280729) B1280729
theorem B1214281 : Blo 850355 1214281 := bstep (se 2 (by rfl) ⟨455355, by rfl⟩ : syracuseStep 1214281 = 910711) B910711
theorem B1279817 : Blo 850355 1279817 := bstep (se 2 (by rfl) ⟨479931, by rfl⟩ : syracuseStep 1279817 = 959863) B959863
theorem B853895 : Blo 850355 853895 := bstep (se 1 (by rfl) ⟨640421, by rfl⟩ : syracuseStep 853895 = 1280843) B1280843
theorem B853903 : Blo 850355 853903 := bstep (se 1 (by rfl) ⟨640427, by rfl⟩ : syracuseStep 853903 = 1280855) B1280855
theorem B1279931 : Blo 850355 1279931 := bstep (se 1 (by rfl) ⟨959948, by rfl⟩ : syracuseStep 1279931 = 1919897) B1919897
theorem B853947 : Blo 850355 853947 := bstep (se 1 (by rfl) ⟨640460, by rfl⟩ : syracuseStep 853947 = 1280921) B1280921
theorem B4851677 : Blo 850355 4851677 := bstep (se 3 (by rfl) ⟨909689, by rfl⟩ : syracuseStep 4851677 = 1819379) B1819379
theorem B1279991 : Blo 850355 1279991 := bstep (se 1 (by rfl) ⟨959993, by rfl⟩ : syracuseStep 1279991 = 1919987) B1919987
theorem B854023 : Blo 850355 854023 := bstep (se 1 (by rfl) ⟨640517, by rfl⟩ : syracuseStep 854023 = 1281035) B1281035
theorem B1280015 : Blo 850355 1280015 := bstep (se 1 (by rfl) ⟨960011, by rfl⟩ : syracuseStep 1280015 = 1920023) B1920023
theorem B854031 : Blo 850355 854031 := bstep (se 1 (by rfl) ⟨640523, by rfl⟩ : syracuseStep 854031 = 1281047) B1281047
theorem B10520621 : Blo 850355 10520621 := bstep (se 3 (by rfl) ⟨1972616, by rfl⟩ : syracuseStep 10520621 = 3945233) B3945233
theorem B1280057 : Blo 850355 1280057 := bstep (se 2 (by rfl) ⟨480021, by rfl⟩ : syracuseStep 1280057 = 960043) B960043
theorem B854075 : Blo 850355 854075 := bstep (se 1 (by rfl) ⟨640556, by rfl⟩ : syracuseStep 854075 = 1281113) B1281113
theorem B7473239 : Blo 850355 7473239 := bstep (se 1 (by rfl) ⟨5604929, by rfl⟩ : syracuseStep 7473239 = 11209859) B11209859
theorem B1280135 : Blo 850355 1280135 := bstep (se 1 (by rfl) ⟨960101, by rfl⟩ : syracuseStep 1280135 = 1920203) B1920203
theorem B854151 : Blo 850355 854151 := bstep (se 1 (by rfl) ⟨640613, by rfl⟩ : syracuseStep 854151 = 1281227) B1281227
theorem B854159 : Blo 850355 854159 := bstep (se 1 (by rfl) ⟨640619, by rfl⟩ : syracuseStep 854159 = 1281239) B1281239
theorem B1280171 : Blo 850355 1280171 := bstep (se 1 (by rfl) ⟨960128, by rfl⟩ : syracuseStep 1280171 = 1920257) B1920257
theorem B854203 : Blo 850355 854203 := bstep (se 1 (by rfl) ⟨640652, by rfl⟩ : syracuseStep 854203 = 1281305) B1281305
theorem B1280201 : Blo 850355 1280201 := bstep (se 2 (by rfl) ⟨480075, by rfl⟩ : syracuseStep 1280201 = 960151) B960151
theorem B854279 : Blo 850355 854279 := bstep (se 1 (by rfl) ⟨640709, by rfl⟩ : syracuseStep 854279 = 1281419) B1281419
theorem B854287 : Blo 850355 854287 := bstep (se 1 (by rfl) ⟨640715, by rfl⟩ : syracuseStep 854287 = 1281431) B1281431
theorem B1280315 : Blo 850355 1280315 := bstep (se 1 (by rfl) ⟨960236, by rfl⟩ : syracuseStep 1280315 = 1920473) B1920473
theorem B854331 : Blo 850355 854331 := bstep (se 1 (by rfl) ⟨640748, by rfl⟩ : syracuseStep 854331 = 1281497) B1281497
theorem B1280375 : Blo 850355 1280375 := bstep (se 1 (by rfl) ⟨960281, by rfl⟩ : syracuseStep 1280375 = 1920563) B1920563
theorem B1280399 : Blo 850355 1280399 := bstep (se 1 (by rfl) ⟨960299, by rfl⟩ : syracuseStep 1280399 = 1920599) B1920599
theorem B1280441 : Blo 850355 1280441 := bstep (se 2 (by rfl) ⟨480165, by rfl⟩ : syracuseStep 1280441 = 960331) B960331
theorem B1280519 : Blo 850355 1280519 := bstep (se 1 (by rfl) ⟨960389, by rfl⟩ : syracuseStep 1280519 = 1920779) B1920779
theorem B1280555 : Blo 850355 1280555 := bstep (se 1 (by rfl) ⟨960416, by rfl⟩ : syracuseStep 1280555 = 1920833) B1920833
theorem B1280585 : Blo 850355 1280585 := bstep (se 2 (by rfl) ⟨480219, by rfl⟩ : syracuseStep 1280585 = 960439) B960439
theorem B2427479 : Blo 850355 2427479 := bstep (se 1 (by rfl) ⟨1820609, by rfl⟩ : syracuseStep 2427479 = 3641219) B3641219
theorem B1280699 : Blo 850355 1280699 := bstep (se 1 (by rfl) ⟨960524, by rfl⟩ : syracuseStep 1280699 = 1921049) B1921049
theorem B1280759 : Blo 850355 1280759 := bstep (se 1 (by rfl) ⟨960569, by rfl⟩ : syracuseStep 1280759 = 1921139) B1921139
theorem B1280783 : Blo 850355 1280783 := bstep (se 1 (by rfl) ⟨960587, by rfl⟩ : syracuseStep 1280783 = 1921175) B1921175
theorem B6916913 : Blo 850355 6916913 := bstep (se 2 (by rfl) ⟨2593842, by rfl⟩ : syracuseStep 6916913 = 5187685) B5187685
theorem B1280825 : Blo 850355 1280825 := bstep (se 2 (by rfl) ⟨480309, by rfl⟩ : syracuseStep 1280825 = 960619) B960619
theorem B2427707 : Blo 850355 2427707 := bstep (se 1 (by rfl) ⟨1820780, by rfl⟩ : syracuseStep 2427707 = 3641561) B3641561
theorem B1280903 : Blo 850355 1280903 := bstep (se 1 (by rfl) ⟨960677, by rfl⟩ : syracuseStep 1280903 = 1921355) B1921355
theorem B1280939 : Blo 850355 1280939 := bstep (se 1 (by rfl) ⟨960704, by rfl⟩ : syracuseStep 1280939 = 1921409) B1921409
theorem B2427833 : Blo 850355 2427833 := bstep (se 2 (by rfl) ⟨910437, by rfl⟩ : syracuseStep 2427833 = 1820875) B1820875
theorem B1280969 : Blo 850355 1280969 := bstep (se 2 (by rfl) ⟨480363, by rfl⟩ : syracuseStep 1280969 = 960727) B960727
theorem B1281083 : Blo 850355 1281083 := bstep (se 1 (by rfl) ⟨960812, by rfl⟩ : syracuseStep 1281083 = 1921625) B1921625
theorem B1281143 : Blo 850355 1281143 := bstep (se 1 (by rfl) ⟨960857, by rfl⟩ : syracuseStep 1281143 = 1921715) B1921715
theorem B1281167 : Blo 850355 1281167 := bstep (se 1 (by rfl) ⟨960875, by rfl⟩ : syracuseStep 1281167 = 1921751) B1921751
theorem B1281209 : Blo 850355 1281209 := bstep (se 2 (by rfl) ⟨480453, by rfl⟩ : syracuseStep 1281209 = 960907) B960907
theorem B1281287 : Blo 850355 1281287 := bstep (se 1 (by rfl) ⟨960965, by rfl⟩ : syracuseStep 1281287 = 1921931) B1921931
theorem B1281323 : Blo 850355 1281323 := bstep (se 1 (by rfl) ⟨960992, by rfl⟩ : syracuseStep 1281323 = 1921985) B1921985
theorem B1281353 : Blo 850355 1281353 := bstep (se 2 (by rfl) ⟨480507, by rfl⟩ : syracuseStep 1281353 = 961015) B961015
theorem B4984199 : Blo 850355 4984199 := bstep (se 1 (by rfl) ⟨3738149, by rfl⟩ : syracuseStep 4984199 = 7476299) B7476299
theorem B1281467 : Blo 850355 1281467 := bstep (se 1 (by rfl) ⟨961100, by rfl⟩ : syracuseStep 1281467 = 1922201) B1922201
theorem B6131153 : Blo 850355 6131153 := bstep (se 2 (by rfl) ⟨2299182, by rfl⟩ : syracuseStep 6131153 = 4598365) B4598365
theorem B1281527 : Blo 850355 1281527 := bstep (se 1 (by rfl) ⟨961145, by rfl⟩ : syracuseStep 1281527 = 1922291) B1922291
theorem B9702989 : Blo 850355 9702989 := bstep (se 3 (by rfl) ⟨1819310, by rfl⟩ : syracuseStep 9702989 = 3638621) B3638621
theorem B2461385 : Blo 850355 2461385 := bstep (se 2 (by rfl) ⟨923019, by rfl⟩ : syracuseStep 2461385 = 1846039) B1846039
theorem B36802289 : Blo 850355 36802289 := bstep (se 2 (by rfl) ⟨13800858, by rfl⟩ : syracuseStep 36802289 = 27601717) B27601717
theorem B1773371 : Blo 850355 1773371 := bstep (se 1 (by rfl) ⟨1330028, by rfl⟩ : syracuseStep 1773371 = 2660057) B2660057
theorem B4100215 : Blo 850355 4100215 := bstep (se 1 (by rfl) ⟨3075161, by rfl⟩ : syracuseStep 4100215 = 6150323) B6150323
theorem B20713745 : Blo 850355 20713745 := bstep (se 2 (by rfl) ⟨7767654, by rfl⟩ : syracuseStep 20713745 = 15535309) B15535309
theorem B4854275 : Blo 850355 4854275 := bstep (se 1 (by rfl) ⟨3640706, by rfl⟩ : syracuseStep 4854275 = 7281413) B7281413
theorem B2429473 : Blo 850355 2429473 := bstep (se 2 (by rfl) ⟨911052, by rfl⟩ : syracuseStep 2429473 = 1822105) B1822105
theorem B5181995 : Blo 850355 5181995 := bstep (se 1 (by rfl) ⟨3886496, by rfl⟩ : syracuseStep 5181995 = 7772993) B7772993
theorem B29561537 : Blo 850355 29561537 := bstep (se 2 (by rfl) ⟨11085576, by rfl⟩ : syracuseStep 29561537 = 22171153) B22171153
theorem B4920323 : Blo 850355 4920323 := bstep (se 1 (by rfl) ⟨3690242, by rfl⟩ : syracuseStep 4920323 = 7380485) B7380485
theorem B2429963 : Blo 850355 2429963 := bstep (se 1 (by rfl) ⟨1822472, by rfl⟩ : syracuseStep 2429963 = 3644945) B3644945
theorem B7279703 : Blo 850355 7279703 := bstep (se 1 (by rfl) ⟨5459777, by rfl⟩ : syracuseStep 7279703 = 10919555) B10919555
theorem B4101293 : Blo 850355 4101293 := bstep (se 3 (by rfl) ⟨768992, by rfl⟩ : syracuseStep 4101293 = 1537985) B1537985
theorem B4363723 : Blo 850355 4363723 := bstep (se 1 (by rfl) ⟨3272792, by rfl⟩ : syracuseStep 4363723 = 6545585) B6545585
theorem B2332307 : Blo 850355 2332307 := bstep (se 1 (by rfl) ⟨1749230, by rfl⟩ : syracuseStep 2332307 = 3498461) B3498461
theorem B2332361 : Blo 850355 2332361 := bstep (se 2 (by rfl) ⟨874635, by rfl⟩ : syracuseStep 2332361 = 1749271) B1749271
theorem B2430749 : Blo 850355 2430749 := bstep (se 3 (by rfl) ⟨455765, by rfl⟩ : syracuseStep 2430749 = 911531) B911531
theorem B4101947 : Blo 850355 4101947 := bstep (se 1 (by rfl) ⟨3076460, by rfl⟩ : syracuseStep 4101947 = 6152921) B6152921
theorem B4986845 : Blo 850355 4986845 := bstep (se 3 (by rfl) ⟨935033, by rfl⟩ : syracuseStep 4986845 = 1870067) B1870067
theorem B3643663 : Blo 850355 3643663 := bstep (se 1 (by rfl) ⟨2732747, by rfl⟩ : syracuseStep 3643663 = 5465495) B5465495
theorem B956731 : Blo 850355 956731 := bstep (se 1 (by rfl) ⟨717548, by rfl⟩ : syracuseStep 956731 = 1435097) B1435097
theorem B1022267 : Blo 850355 1022267 := bstep (se 1 (by rfl) ⟨766700, by rfl⟩ : syracuseStep 1022267 = 1533401) B1533401
theorem B9214721 : Blo 850355 9214721 := bstep (se 2 (by rfl) ⟨3455520, by rfl⟩ : syracuseStep 9214721 = 6911041) B6911041
theorem B957199 : Blo 850355 957199 := bstep (se 1 (by rfl) ⟨717899, by rfl⟩ : syracuseStep 957199 = 1435799) B1435799
theorem B2333455 : Blo 850355 2333455 := bstep (se 1 (by rfl) ⟨1750091, by rfl⟩ : syracuseStep 2333455 = 3500183) B3500183
theorem B1022863 : Blo 850355 1022863 := bstep (se 1 (by rfl) ⟨767147, by rfl⟩ : syracuseStep 1022863 = 1534295) B1534295
theorem B4660247 : Blo 850355 4660247 := bstep (se 1 (by rfl) ⟨3495185, by rfl⟩ : syracuseStep 4660247 = 6990371) B6990371
theorem B957703 : Blo 850355 957703 := bstep (se 1 (by rfl) ⟨718277, by rfl⟩ : syracuseStep 957703 = 1436555) B1436555
theorem B20716859 : Blo 850355 20716859 := bstep (se 1 (by rfl) ⟨15537644, by rfl⟩ : syracuseStep 20716859 = 31075289) B31075289
theorem B957883 : Blo 850355 957883 := bstep (se 1 (by rfl) ⟨718412, by rfl⟩ : syracuseStep 957883 = 1436825) B1436825
theorem B2432855 : Blo 850355 2432855 := bstep (se 1 (by rfl) ⟨1824641, by rfl⟩ : syracuseStep 2432855 = 3649283) B3649283
theorem B3645319 : Blo 850355 3645319 := bstep (se 1 (by rfl) ⟨2733989, by rfl⟩ : syracuseStep 3645319 = 5467979) B5467979
theorem B958351 : Blo 850355 958351 := bstep (se 1 (by rfl) ⟨718763, by rfl⟩ : syracuseStep 958351 = 1437527) B1437527
theorem B2727827 : Blo 850355 2727827 := bstep (se 1 (by rfl) ⟨2045870, by rfl⟩ : syracuseStep 2727827 = 4091741) B4091741
theorem B4104215 : Blo 850355 4104215 := bstep (se 1 (by rfl) ⟨3078161, by rfl⟩ : syracuseStep 4104215 = 6156323) B6156323
theorem B3448919 : Blo 850355 3448919 := bstep (se 1 (by rfl) ⟨2586689, by rfl⟩ : syracuseStep 3448919 = 5173379) B5173379
theorem B958855 : Blo 850355 958855 := bstep (se 1 (by rfl) ⟨719141, by rfl⟩ : syracuseStep 958855 = 1438283) B1438283
theorem B2597321 : Blo 850355 2597321 := bstep (se 2 (by rfl) ⟨973995, by rfl⟩ : syracuseStep 2597321 = 1947991) B1947991
theorem B4989443 : Blo 850355 4989443 := bstep (se 1 (by rfl) ⟨3742082, by rfl⟩ : syracuseStep 4989443 = 7484165) B7484165
theorem B4104715 : Blo 850355 4104715 := bstep (se 1 (by rfl) ⟨3078536, by rfl⟩ : syracuseStep 4104715 = 6157073) B6157073
theorem B959035 : Blo 850355 959035 := bstep (se 1 (by rfl) ⟨719276, by rfl⟩ : syracuseStep 959035 = 1438553) B1438553
theorem B959503 : Blo 850355 959503 := bstep (se 1 (by rfl) ⟨719627, by rfl⟩ : syracuseStep 959503 = 1439255) B1439255
theorem B4858967 : Blo 850355 4858967 := bstep (se 1 (by rfl) ⟨3644225, by rfl⟩ : syracuseStep 4858967 = 7288451) B7288451
theorem B3646721 : Blo 850355 3646721 := bstep (se 2 (by rfl) ⟨1367520, by rfl⟩ : syracuseStep 3646721 = 2735041) B2735041
theorem B960007 : Blo 850355 960007 := bstep (se 1 (by rfl) ⟨720005, by rfl⟩ : syracuseStep 960007 = 1440011) B1440011
theorem B1615403 : Blo 850355 1615403 := bstep (se 1 (by rfl) ⟨1211552, by rfl⟩ : syracuseStep 1615403 = 2423105) B2423105
theorem B960187 : Blo 850355 960187 := bstep (se 1 (by rfl) ⟨720140, by rfl⟩ : syracuseStep 960187 = 1440281) B1440281
theorem B16361189 : Blo 850355 16361189 := bstep (se 4 (by rfl) ⟨1533861, by rfl⟩ : syracuseStep 16361189 = 3067723) B3067723
theorem B2303777 : Blo 850355 2303777 := bstep (se 2 (by rfl) ⟨863916, by rfl⟩ : syracuseStep 2303777 = 1727833) B1727833
theorem B18425717 : Blo 850355 18425717 := bstep (se 5 (by rfl) ⟨863705, by rfl⟩ : syracuseStep 18425717 = 1727411) B1727411
theorem B960655 : Blo 850355 960655 := bstep (se 1 (by rfl) ⟨720491, by rfl⟩ : syracuseStep 960655 = 1440983) B1440983
theorem B7285139 : Blo 850355 7285139 := bstep (se 1 (by rfl) ⟨5463854, by rfl⟩ : syracuseStep 7285139 = 10927709) B10927709
theorem B2075033 : Blo 850355 2075033 := bstep (se 2 (by rfl) ⟨778137, by rfl⟩ : syracuseStep 2075033 = 1556275) B1556275
theorem B4860881 : Blo 850355 4860881 := bstep (se 2 (by rfl) ⟨1822830, by rfl⟩ : syracuseStep 4860881 = 3645661) B3645661
theorem B4598903 : Blo 850355 4598903 := bstep (se 1 (by rfl) ⟨3449177, by rfl⟩ : syracuseStep 4598903 = 6898355) B6898355
theorem B1617097 : Blo 850355 1617097 := bstep (se 2 (by rfl) ⟨606411, by rfl⟩ : syracuseStep 1617097 = 1212823) B1212823
theorem B10923245 : Blo 850355 10923245 := bstep (se 3 (by rfl) ⟨2048108, by rfl⟩ : syracuseStep 10923245 = 4096217) B4096217
theorem B1420859 : Blo 850355 1420859 := bstep (se 1 (by rfl) ⟨1065644, by rfl⟩ : syracuseStep 1420859 = 2131289) B2131289
theorem B2043593 : Blo 850355 2043593 := bstep (se 2 (by rfl) ⟨766347, by rfl⟩ : syracuseStep 2043593 = 1532695) B1532695
theorem B2043649 : Blo 850355 2043649 := bstep (se 2 (by rfl) ⟨766368, by rfl⟩ : syracuseStep 2043649 = 1532737) B1532737
theorem B2732555 : Blo 850355 2732555 := bstep (se 1 (by rfl) ⟨2049416, by rfl⟩ : syracuseStep 2732555 = 4098833) B4098833
theorem B6468173 : Blo 850355 6468173 := bstep (se 3 (by rfl) ⟨1212782, by rfl⟩ : syracuseStep 6468173 = 2425565) B2425565
theorem B864955 : Blo 850355 864955 := bstep (se 1 (by rfl) ⟨648716, by rfl⟩ : syracuseStep 864955 = 1297433) B1297433
theorem B1913615 : Blo 850355 1913615 := bstep (se 1 (by rfl) ⟨1435211, by rfl⟩ : syracuseStep 1913615 = 2870423) B2870423
theorem B1913633 : Blo 850355 1913633 := bstep (se 2 (by rfl) ⟨717612, by rfl⟩ : syracuseStep 1913633 = 1435225) B1435225
theorem B2732953 : Blo 850355 2732953 := bstep (se 2 (by rfl) ⟨1024857, by rfl⟩ : syracuseStep 2732953 = 2049715) B2049715
theorem B2307001 : Blo 850355 2307001 := bstep (se 2 (by rfl) ⟨865125, by rfl⟩ : syracuseStep 2307001 = 1730251) B1730251
theorem B1619003 : Blo 850355 1619003 := bstep (se 1 (by rfl) ⟨1214252, by rfl⟩ : syracuseStep 1619003 = 2428505) B2428505
theorem B1913975 : Blo 850355 1913975 := bstep (se 1 (by rfl) ⟨1435481, by rfl⟩ : syracuseStep 1913975 = 2870963) B2870963
theorem B4306121 : Blo 850355 4306121 := bstep (se 2 (by rfl) ⟨1614795, by rfl⟩ : syracuseStep 4306121 = 3229591) B3229591
theorem B1914155 : Blo 850355 1914155 := bstep (se 1 (by rfl) ⟨1435616, by rfl⟩ : syracuseStep 1914155 = 2871233) B2871233
theorem B6141329 : Blo 850355 6141329 := bstep (se 2 (by rfl) ⟨2302998, by rfl⟩ : syracuseStep 6141329 = 4605997) B4605997
theorem B3683731 : Blo 850355 3683731 := bstep (se 1 (by rfl) ⟨2762798, by rfl⟩ : syracuseStep 3683731 = 5525597) B5525597
theorem B1619489 : Blo 850355 1619489 := bstep (se 2 (by rfl) ⟨607308, by rfl⟩ : syracuseStep 1619489 = 1214617) B1214617
theorem B1947169 : Blo 850355 1947169 := bstep (se 2 (by rfl) ⟨730188, by rfl⟩ : syracuseStep 1947169 = 1460377) B1460377
theorem B9713195 : Blo 850355 9713195 := bstep (se 1 (by rfl) ⟨7284896, by rfl⟩ : syracuseStep 9713195 = 14569793) B14569793
theorem B1914515 : Blo 850355 1914515 := bstep (se 1 (by rfl) ⟨1435886, by rfl⟩ : syracuseStep 1914515 = 2871773) B2871773
theorem B1914569 : Blo 850355 1914569 := bstep (se 2 (by rfl) ⟨717963, by rfl⟩ : syracuseStep 1914569 = 1435927) B1435927
theorem B1619831 : Blo 850355 1619831 := bstep (se 1 (by rfl) ⟨1214873, by rfl⟩ : syracuseStep 1619831 = 2429747) B2429747
theorem B22132909 : Blo 850355 22132909 := bstep (se 3 (by rfl) ⟨4149920, by rfl⟩ : syracuseStep 22132909 = 8299841) B8299841
theorem B2308439 : Blo 850355 2308439 := bstep (se 1 (by rfl) ⟨1731329, by rfl⟩ : syracuseStep 2308439 = 3462659) B3462659
theorem B1915271 : Blo 850355 1915271 := bstep (se 1 (by rfl) ⟨1436453, by rfl⟩ : syracuseStep 1915271 = 2872907) B2872907
theorem B1915451 : Blo 850355 1915451 := bstep (se 1 (by rfl) ⟨1436588, by rfl⟩ : syracuseStep 1915451 = 2873177) B2873177
theorem B1915577 : Blo 850355 1915577 := bstep (se 2 (by rfl) ⟨718341, by rfl⟩ : syracuseStep 1915577 = 1436683) B1436683
theorem B6470603 : Blo 850355 6470603 := bstep (se 1 (by rfl) ⟨4852952, by rfl⟩ : syracuseStep 6470603 = 9705905) B9705905
theorem B1915919 : Blo 850355 1915919 := bstep (se 1 (by rfl) ⟨1436939, by rfl⟩ : syracuseStep 1915919 = 2873879) B2873879
theorem B1915937 : Blo 850355 1915937 := bstep (se 2 (by rfl) ⟨718476, by rfl⟩ : syracuseStep 1915937 = 1436953) B1436953
theorem B19643597 : Blo 850355 19643597 := bstep (se 3 (by rfl) ⟨3683174, by rfl⟩ : syracuseStep 19643597 = 7366349) B7366349
theorem B1457423 : Blo 850355 1457423 := bstep (se 1 (by rfl) ⟨1093067, by rfl⟩ : syracuseStep 1457423 = 2186135) B2186135
theorem B1916279 : Blo 850355 1916279 := bstep (se 1 (by rfl) ⟨1437209, by rfl⟩ : syracuseStep 1916279 = 2874419) B2874419
theorem B1621433 : Blo 850355 1621433 := bstep (se 2 (by rfl) ⟨608037, by rfl⟩ : syracuseStep 1621433 = 1216075) B1216075
theorem B31112657 : Blo 850355 31112657 := bstep (se 2 (by rfl) ⟨11667246, by rfl⟩ : syracuseStep 31112657 = 23334493) B23334493
theorem B1916459 : Blo 850355 1916459 := bstep (se 1 (by rfl) ⟨1437344, by rfl⟩ : syracuseStep 1916459 = 2874689) B2874689
theorem B1457723 : Blo 850355 1457723 := bstep (se 1 (by rfl) ⟨1093292, by rfl⟩ : syracuseStep 1457723 = 2186585) B2186585
theorem B1621775 : Blo 850355 1621775 := bstep (se 1 (by rfl) ⟨1216331, by rfl⟩ : syracuseStep 1621775 = 2432663) B2432663
theorem B1916819 : Blo 850355 1916819 := bstep (se 1 (by rfl) ⟨1437614, by rfl⟩ : syracuseStep 1916819 = 2875229) B2875229
theorem B4997011 : Blo 850355 4997011 := bstep (se 1 (by rfl) ⟨3747758, by rfl⟩ : syracuseStep 4997011 = 7495517) B7495517
theorem B1916873 : Blo 850355 1916873 := bstep (se 2 (by rfl) ⟨718827, by rfl⟩ : syracuseStep 1916873 = 1437655) B1437655
theorem B4374481 : Blo 850355 4374481 := bstep (se 2 (by rfl) ⟨1640430, by rfl⟩ : syracuseStep 4374481 = 3280861) B3280861
theorem B2998663 : Blo 850355 2998663 := bstep (se 1 (by rfl) ⟨2248997, by rfl⟩ : syracuseStep 2998663 = 4497995) B4497995
theorem B10502621 : Blo 850355 10502621 := bstep (se 3 (by rfl) ⟨1969241, by rfl⟩ : syracuseStep 10502621 = 3938483) B3938483
theorem B1917575 : Blo 850355 1917575 := bstep (se 1 (by rfl) ⟨1438181, by rfl⟩ : syracuseStep 1917575 = 2876363) B2876363
theorem B2048647 : Blo 850355 2048647 := bstep (se 1 (by rfl) ⟨1536485, by rfl⟩ : syracuseStep 2048647 = 3072971) B3072971
theorem B1917755 : Blo 850355 1917755 := bstep (se 1 (by rfl) ⟨1438316, by rfl⟩ : syracuseStep 1917755 = 2876633) B2876633
theorem B1459063 : Blo 850355 1459063 := bstep (se 1 (by rfl) ⟨1094297, by rfl⟩ : syracuseStep 1459063 = 2188595) B2188595
theorem B1819577 : Blo 850355 1819577 := bstep (se 2 (by rfl) ⟨682341, by rfl⟩ : syracuseStep 1819577 = 1364683) B1364683
theorem B1917881 : Blo 850355 1917881 := bstep (se 2 (by rfl) ⟨719205, by rfl⟩ : syracuseStep 1917881 = 1438411) B1438411
theorem B1295291 : Blo 850355 1295291 := bstep (se 1 (by rfl) ⟨971468, by rfl⟩ : syracuseStep 1295291 = 1942937) B1942937
theorem B10372157 : Blo 850355 10372157 := bstep (se 3 (by rfl) ⟨1944779, by rfl⟩ : syracuseStep 10372157 = 3889559) B3889559
theorem B1918223 : Blo 850355 1918223 := bstep (se 1 (by rfl) ⟨1438667, by rfl⟩ : syracuseStep 1918223 = 2877335) B2877335
theorem B3687713 : Blo 850355 3687713 := bstep (se 2 (by rfl) ⟨1382892, by rfl⟩ : syracuseStep 3687713 = 2765785) B2765785
theorem B1918241 : Blo 850355 1918241 := bstep (se 2 (by rfl) ⟨719340, by rfl⟩ : syracuseStep 1918241 = 1438681) B1438681
theorem B1918583 : Blo 850355 1918583 := bstep (se 1 (by rfl) ⟨1438937, by rfl⟩ : syracuseStep 1918583 = 2877875) B2877875
theorem B6899393 : Blo 850355 6899393 := bstep (se 2 (by rfl) ⟨2587272, by rfl⟩ : syracuseStep 6899393 = 5174545) B5174545
theorem B1918763 : Blo 850355 1918763 := bstep (se 1 (by rfl) ⟨1439072, by rfl⟩ : syracuseStep 1918763 = 2878145) B2878145
theorem B8734513 : Blo 850355 8734513 := bstep (se 2 (by rfl) ⟨3275442, by rfl⟩ : syracuseStep 8734513 = 6550885) B6550885
theorem B7292825 : Blo 850355 7292825 := bstep (se 2 (by rfl) ⟨2734809, by rfl⟩ : syracuseStep 7292825 = 5469619) B5469619
theorem B1919123 : Blo 850355 1919123 := bstep (se 1 (by rfl) ⟨1439342, by rfl⟩ : syracuseStep 1919123 = 2878685) B2878685
theorem B1919177 : Blo 850355 1919177 := bstep (se 2 (by rfl) ⟨719691, by rfl⟩ : syracuseStep 1919177 = 1439383) B1439383
theorem B5196005 : Blo 850355 5196005 := bstep (se 4 (by rfl) ⟨487125, by rfl⟩ : syracuseStep 5196005 = 974251) B974251
theorem B6572497 : Blo 850355 6572497 := bstep (se 2 (by rfl) ⟨2464686, by rfl⟩ : syracuseStep 6572497 = 4929373) B4929373
theorem B1821217 : Blo 850355 1821217 := bstep (se 2 (by rfl) ⟨682956, by rfl⟩ : syracuseStep 1821217 = 1365913) B1365913
theorem B9226871 : Blo 850355 9226871 := bstep (se 1 (by rfl) ⟨6920153, by rfl⟩ : syracuseStep 9226871 = 13840307) B13840307
theorem B1461007 : Blo 850355 1461007 := bstep (se 1 (by rfl) ⟨1095755, by rfl⟩ : syracuseStep 1461007 = 2191511) B2191511
theorem B1919879 : Blo 850355 1919879 := bstep (se 1 (by rfl) ⟨1439909, by rfl⟩ : syracuseStep 1919879 = 2879819) B2879819
theorem B4311953 : Blo 850355 4311953 := bstep (se 2 (by rfl) ⟨1616982, by rfl⟩ : syracuseStep 4311953 = 3233965) B3233965
theorem B2870315 : Blo 850355 2870315 := bstep (se 1 (by rfl) ⟨2152736, by rfl⟩ : syracuseStep 2870315 = 4305473) B4305473
theorem B1920059 : Blo 850355 1920059 := bstep (se 1 (by rfl) ⟨1440044, by rfl⟩ : syracuseStep 1920059 = 2880089) B2880089
theorem B1920185 : Blo 850355 1920185 := bstep (se 2 (by rfl) ⟨720069, by rfl⟩ : syracuseStep 1920185 = 1440139) B1440139
theorem B3231035 : Blo 850355 3231035 := bstep (se 1 (by rfl) ⟨2423276, by rfl⟩ : syracuseStep 3231035 = 4846553) B4846553
theorem B5459345 : Blo 850355 5459345 := bstep (se 2 (by rfl) ⟨2047254, by rfl⟩ : syracuseStep 5459345 = 4094509) B4094509
theorem B2051513 : Blo 850355 2051513 := bstep (se 2 (by rfl) ⟨769317, by rfl⟩ : syracuseStep 2051513 = 1538635) B1538635
theorem B1920527 : Blo 850355 1920527 := bstep (se 1 (by rfl) ⟨1440395, by rfl⟩ : syracuseStep 1920527 = 2880791) B2880791
theorem B1920545 : Blo 850355 1920545 := bstep (se 2 (by rfl) ⟨720204, by rfl⟩ : syracuseStep 1920545 = 1440409) B1440409
theorem B1822267 : Blo 850355 1822267 := bstep (se 1 (by rfl) ⟨1366700, by rfl⟩ : syracuseStep 1822267 = 2733401) B2733401
theorem B3231521 : Blo 850355 3231521 := bstep (se 2 (by rfl) ⟨1211820, by rfl⟩ : syracuseStep 3231521 = 2423641) B2423641
theorem B1920887 : Blo 850355 1920887 := bstep (se 1 (by rfl) ⟨1440665, by rfl⟩ : syracuseStep 1920887 = 2881331) B2881331
theorem B1822763 : Blo 850355 1822763 := bstep (se 1 (by rfl) ⟨1367072, by rfl⟩ : syracuseStep 1822763 = 2734145) B2734145
theorem B1921067 : Blo 850355 1921067 := bstep (se 1 (by rfl) ⟨1440800, by rfl⟩ : syracuseStep 1921067 = 2881601) B2881601
theorem B1265737 : Blo 850355 1265737 := bstep (se 2 (by rfl) ⟨474651, by rfl⟩ : syracuseStep 1265737 = 949303) B949303
theorem B6475949 : Blo 850355 6475949 := bstep (se 3 (by rfl) ⟨1214240, by rfl⟩ : syracuseStep 6475949 = 2428481) B2428481
theorem B2871611 : Blo 850355 2871611 := bstep (se 1 (by rfl) ⟨2153708, by rfl⟩ : syracuseStep 2871611 = 4307417) B4307417
theorem B5460371 : Blo 850355 5460371 := bstep (se 1 (by rfl) ⟨4095278, by rfl⟩ : syracuseStep 5460371 = 8190557) B8190557
theorem B1921427 : Blo 850355 1921427 := bstep (se 1 (by rfl) ⟨1441070, by rfl⟩ : syracuseStep 1921427 = 2882141) B2882141
theorem B1921481 : Blo 850355 1921481 := bstep (se 2 (by rfl) ⟨720555, by rfl⟩ : syracuseStep 1921481 = 1441111) B1441111
theorem B3232493 : Blo 850355 3232493 := bstep (se 3 (by rfl) ⟨606092, by rfl⟩ : syracuseStep 3232493 = 1212185) B1212185
theorem B2872097 : Blo 850355 2872097 := bstep (se 2 (by rfl) ⟨1077036, by rfl⟩ : syracuseStep 2872097 = 2154073) B2154073
theorem B1364855 : Blo 850355 1364855 := bstep (se 1 (by rfl) ⟨1023641, by rfl⟩ : syracuseStep 1364855 = 2047283) B2047283
theorem B1725319 : Blo 850355 1725319 := bstep (se 1 (by rfl) ⟨1293989, by rfl⟩ : syracuseStep 1725319 = 2587979) B2587979
theorem B4314059 : Blo 850355 4314059 := bstep (se 1 (by rfl) ⟨3235544, by rfl⟩ : syracuseStep 4314059 = 6471089) B6471089
theorem B8180747 : Blo 850355 8180747 := bstep (se 1 (by rfl) ⟨6135560, by rfl⟩ : syracuseStep 8180747 = 12271121) B12271121
theorem B3232811 : Blo 850355 3232811 := bstep (se 1 (by rfl) ⟨2424608, by rfl⟩ : syracuseStep 3232811 = 4849217) B4849217
theorem B1922183 : Blo 850355 1922183 := bstep (se 1 (by rfl) ⟨1441637, by rfl⟩ : syracuseStep 1922183 = 2883275) B2883275
theorem B4314383 : Blo 850355 4314383 := bstep (se 1 (by rfl) ⟨3235787, by rfl⟩ : syracuseStep 4314383 = 6471575) B6471575
theorem B2872691 : Blo 850355 2872691 := bstep (se 1 (by rfl) ⟨2154518, by rfl⟩ : syracuseStep 2872691 = 4309037) B4309037
theorem B3888499 : Blo 850355 3888499 := bstep (se 1 (by rfl) ⟨2916374, by rfl⟩ : syracuseStep 3888499 = 5832749) B5832749
theorem B1824403 : Blo 850355 1824403 := bstep (se 1 (by rfl) ⟨1368302, by rfl⟩ : syracuseStep 1824403 = 2736605) B2736605
theorem B19715735 : Blo 850355 19715735 := bstep (se 1 (by rfl) ⟨14786801, by rfl⟩ : syracuseStep 19715735 = 29573603) B29573603
theorem B23025329 : Blo 850355 23025329 := bstep (se 2 (by rfl) ⟨8634498, by rfl⟩ : syracuseStep 23025329 = 17268997) B17268997
theorem B9721943 : Blo 850355 9721943 := bstep (se 1 (by rfl) ⟨7291457, by rfl⟩ : syracuseStep 9721943 = 14582915) B14582915
theorem B2152595 : Blo 850355 2152595 := bstep (se 1 (by rfl) ⟨1614446, by rfl⟩ : syracuseStep 2152595 = 3228893) B3228893
theorem B2152889 : Blo 850355 2152889 := bstep (se 2 (by rfl) ⟨807333, by rfl⟩ : syracuseStep 2152889 = 1614667) B1614667
theorem B3070493 : Blo 850355 3070493 := bstep (se 3 (by rfl) ⟨575717, by rfl⟩ : syracuseStep 3070493 = 1151435) B1151435
theorem B6478379 : Blo 850355 6478379 := bstep (se 1 (by rfl) ⟨4858784, by rfl⟩ : syracuseStep 6478379 = 9717569) B9717569
theorem B4315841 : Blo 850355 4315841 := bstep (se 2 (by rfl) ⟨1618440, by rfl⟩ : syracuseStep 4315841 = 3236881) B3236881
theorem B2153587 : Blo 850355 2153587 := bstep (se 1 (by rfl) ⟨1615190, by rfl⟩ : syracuseStep 2153587 = 3230381) B3230381
theorem B10378477 : Blo 850355 10378477 := bstep (se 3 (by rfl) ⟨1945964, by rfl⟩ : syracuseStep 10378477 = 3891929) B3891929
theorem B2153729 : Blo 850355 2153729 := bstep (se 2 (by rfl) ⟨807648, by rfl⟩ : syracuseStep 2153729 = 1615297) B1615297
theorem B16408241 : Blo 850355 16408241 := bstep (se 2 (by rfl) ⟨6153090, by rfl⟩ : syracuseStep 16408241 = 12306181) B12306181
theorem B2154185 : Blo 850355 2154185 := bstep (se 2 (by rfl) ⟨807819, by rfl⟩ : syracuseStep 2154185 = 1615639) B1615639
theorem B2875283 : Blo 850355 2875283 := bstep (se 1 (by rfl) ⟨2156462, by rfl⟩ : syracuseStep 2875283 = 4312925) B4312925
theorem B4317137 : Blo 850355 4317137 := bstep (se 2 (by rfl) ⟨1618926, by rfl⟩ : syracuseStep 4317137 = 3237853) B3237853
theorem B4087837 : Blo 850355 4087837 := bstep (se 3 (by rfl) ⟨766469, by rfl⟩ : syracuseStep 4087837 = 1532939) B1532939
theorem B2154539 : Blo 850355 2154539 := bstep (se 1 (by rfl) ⟨1615904, by rfl⟩ : syracuseStep 2154539 = 3231809) B3231809
theorem B5530115 : Blo 850355 5530115 := bstep (se 1 (by rfl) ⟨4147586, by rfl⟩ : syracuseStep 5530115 = 8295173) B8295173
theorem B3236381 : Blo 850355 3236381 := bstep (se 3 (by rfl) ⟨606821, by rfl⟩ : syracuseStep 3236381 = 1213643) B1213643
theorem B1532449 : Blo 850355 1532449 := bstep (se 2 (by rfl) ⟨574668, by rfl⟩ : syracuseStep 1532449 = 1149337) B1149337
theorem B3236395 : Blo 850355 3236395 := bstep (se 1 (by rfl) ⟨2427296, by rfl⟩ : syracuseStep 3236395 = 4854593) B4854593
theorem B909959 : Blo 850355 909959 := bstep (se 1 (by rfl) ⟨682469, by rfl⟩ : syracuseStep 909959 = 1364939) B1364939
theorem B2155531 : Blo 850355 2155531 := bstep (se 1 (by rfl) ⟨1616648, by rfl⟩ : syracuseStep 2155531 = 3233297) B3233297
theorem B22176899 : Blo 850355 22176899 := bstep (se 1 (by rfl) ⟨16632674, by rfl⟩ : syracuseStep 22176899 = 33265349) B33265349
theorem B2155673 : Blo 850355 2155673 := bstep (se 2 (by rfl) ⟨808377, by rfl⟩ : syracuseStep 2155673 = 1616755) B1616755
theorem B3892481 : Blo 850355 3892481 := bstep (se 2 (by rfl) ⟨1459680, by rfl⟩ : syracuseStep 3892481 = 2919361) B2919361
theorem B2876687 : Blo 850355 2876687 := bstep (se 1 (by rfl) ⟨2157515, by rfl⟩ : syracuseStep 2876687 = 4315031) B4315031
theorem B7267643 : Blo 850355 7267643 := bstep (se 1 (by rfl) ⟨5450732, by rfl⟩ : syracuseStep 7267643 = 10901465) B10901465
theorem B2155835 : Blo 850355 2155835 := bstep (se 1 (by rfl) ⟨1616876, by rfl⟩ : syracuseStep 2155835 = 3233753) B3233753
theorem B1435151 : Blo 850355 1435151 := bstep (se 1 (by rfl) ⟨1076363, by rfl⟩ : syracuseStep 1435151 = 2152727) B2152727
theorem B5826077 : Blo 850355 5826077 := bstep (se 3 (by rfl) ⟨1092389, by rfl⟩ : syracuseStep 5826077 = 2184779) B2184779
theorem B2876957 : Blo 850355 2876957 := bstep (se 3 (by rfl) ⟨539429, by rfl⟩ : syracuseStep 2876957 = 1078859) B1078859
theorem B2156179 : Blo 850355 2156179 := bstep (se 1 (by rfl) ⟨1617134, by rfl⟩ : syracuseStep 2156179 = 3234269) B3234269
theorem B2156321 : Blo 850355 2156321 := bstep (se 2 (by rfl) ⟨808620, by rfl⟩ : syracuseStep 2156321 = 1617241) B1617241
theorem B4319243 : Blo 850355 4319243 := bstep (se 1 (by rfl) ⟨3239432, by rfl⟩ : syracuseStep 4319243 = 6478865) B6478865
theorem B1435691 : Blo 850355 1435691 := bstep (se 1 (by rfl) ⟨1076768, by rfl⟩ : syracuseStep 1435691 = 2153537) B2153537
theorem B4319405 : Blo 850355 4319405 := bstep (se 3 (by rfl) ⟨809888, by rfl⟩ : syracuseStep 4319405 = 1619777) B1619777
theorem B1436089 : Blo 850355 1436089 := bstep (se 2 (by rfl) ⟨538533, by rfl⟩ : syracuseStep 1436089 = 1077067) B1077067
theorem B12315179 : Blo 850355 12315179 := bstep (se 1 (by rfl) ⟨9236384, by rfl⟩ : syracuseStep 12315179 = 18472769) B18472769
theorem B1796755 : Blo 850355 1796755 := bstep (se 1 (by rfl) ⟨1347566, by rfl⟩ : syracuseStep 1796755 = 2695133) B2695133
theorem B2157313 : Blo 850355 2157313 := bstep (se 2 (by rfl) ⟨808992, by rfl⟩ : syracuseStep 2157313 = 1617985) B1617985
theorem B5172113 : Blo 850355 5172113 := bstep (se 2 (by rfl) ⟨1939542, by rfl⟩ : syracuseStep 5172113 = 3879085) B3879085
theorem B2878361 : Blo 850355 2878361 := bstep (se 2 (by rfl) ⟨1079385, by rfl⟩ : syracuseStep 2878361 = 2158771) B2158771
theorem B1076267 : Blo 850355 1076267 := bstep (se 1 (by rfl) ⟨807200, by rfl⟩ : syracuseStep 1076267 = 1614401) B1614401
theorem B1436791 : Blo 850355 1436791 := bstep (se 1 (by rfl) ⟨1077593, by rfl⟩ : syracuseStep 1436791 = 2155187) B2155187
theorem B1436987 : Blo 850355 1436987 := bstep (se 1 (by rfl) ⟨1077740, by rfl⟩ : syracuseStep 1436987 = 2155481) B2155481
theorem B2157911 : Blo 850355 2157911 := bstep (se 1 (by rfl) ⟨1618433, by rfl⟩ : syracuseStep 2157911 = 3236867) B3236867
theorem B1076743 : Blo 850355 1076743 := bstep (se 1 (by rfl) ⟨807557, by rfl⟩ : syracuseStep 1076743 = 1615115) B1615115
theorem B2158123 : Blo 850355 2158123 := bstep (se 1 (by rfl) ⟨1618592, by rfl⟩ : syracuseStep 2158123 = 3237185) B3237185
theorem B2879063 : Blo 850355 2879063 := bstep (se 1 (by rfl) ⟨2159297, by rfl⟩ : syracuseStep 2879063 = 4318595) B4318595
theorem B2158265 : Blo 850355 2158265 := bstep (se 2 (by rfl) ⟨809349, by rfl⟩ : syracuseStep 2158265 = 1618699) B1618699
theorem B1437385 : Blo 850355 1437385 := bstep (se 2 (by rfl) ⟨539019, by rfl⟩ : syracuseStep 1437385 = 1078039) B1078039
theorem B4321025 : Blo 850355 4321025 := bstep (se 2 (by rfl) ⟨1620384, by rfl⟩ : syracuseStep 4321025 = 3240769) B3240769
theorem B1077239 : Blo 850355 1077239 := bstep (se 1 (by rfl) ⟨807929, by rfl⟩ : syracuseStep 1077239 = 1615859) B1615859
theorem B4616203 : Blo 850355 4616203 := bstep (se 1 (by rfl) ⟨3462152, by rfl⟩ : syracuseStep 4616203 = 6924305) B6924305
theorem B2879549 : Blo 850355 2879549 := bstep (se 3 (by rfl) ⟨539915, by rfl⟩ : syracuseStep 2879549 = 1079831) B1079831
theorem B1077391 : Blo 850355 1077391 := bstep (se 1 (by rfl) ⟨808043, by rfl⟩ : syracuseStep 1077391 = 1616087) B1616087
theorem B1077563 : Blo 850355 1077563 := bstep (se 1 (by rfl) ⟨808172, by rfl⟩ : syracuseStep 1077563 = 1616345) B1616345
theorem B1438087 : Blo 850355 1438087 := bstep (se 1 (by rfl) ⟨1078565, by rfl⟩ : syracuseStep 1438087 = 2157131) B2157131
theorem B4846027 : Blo 850355 4846027 := bstep (se 1 (by rfl) ⟨3634520, by rfl⟩ : syracuseStep 4846027 = 7269041) B7269041
theorem B7270955 : Blo 850355 7270955 := bstep (se 1 (by rfl) ⟨5453216, by rfl⟩ : syracuseStep 7270955 = 10906433) B10906433
theorem B4321835 : Blo 850355 4321835 := bstep (se 1 (by rfl) ⟨3241376, by rfl⟩ : syracuseStep 4321835 = 6482753) B6482753
theorem B2159257 : Blo 850355 2159257 := bstep (se 2 (by rfl) ⟨809721, by rfl⟩ : syracuseStep 2159257 = 1619443) B1619443
theorem B3273473 : Blo 850355 3273473 := bstep (se 2 (by rfl) ⟨1227552, by rfl⟩ : syracuseStep 3273473 = 2455105) B2455105
theorem B2159419 : Blo 850355 2159419 := bstep (se 1 (by rfl) ⟨1619564, by rfl⟩ : syracuseStep 2159419 = 3239129) B3239129
theorem B2159561 : Blo 850355 2159561 := bstep (se 2 (by rfl) ⟨809835, by rfl⟩ : syracuseStep 2159561 = 1619671) B1619671
theorem B1438735 : Blo 850355 1438735 := bstep (se 1 (by rfl) ⟨1079051, by rfl⟩ : syracuseStep 1438735 = 2158103) B2158103
theorem B2421875 : Blo 850355 2421875 := bstep (se 1 (by rfl) ⟨1816406, by rfl⟩ : syracuseStep 2421875 = 3632813) B3632813
theorem B1078535 : Blo 850355 1078535 := bstep (se 1 (by rfl) ⟨808901, by rfl⟩ : syracuseStep 1078535 = 1617803) B1617803
theorem B2159905 : Blo 850355 2159905 := bstep (se 2 (by rfl) ⟨809964, by rfl⟩ : syracuseStep 2159905 = 1619929) B1619929
theorem B4617587 : Blo 850355 4617587 := bstep (se 1 (by rfl) ⟨3463190, by rfl⟩ : syracuseStep 4617587 = 6926381) B6926381
theorem B3503513 : Blo 850355 3503513 := bstep (se 2 (by rfl) ⟨1313817, by rfl⟩ : syracuseStep 3503513 = 2627635) B2627635
theorem B15562169 : Blo 850355 15562169 := bstep (se 2 (by rfl) ⟨5835813, by rfl⟩ : syracuseStep 15562169 = 11671627) B11671627
theorem B2880953 : Blo 850355 2880953 := bstep (se 2 (by rfl) ⟨1080357, by rfl⟩ : syracuseStep 2880953 = 2160715) B2160715
theorem B2422217 : Blo 850355 2422217 := bstep (se 2 (by rfl) ⟨908331, by rfl⟩ : syracuseStep 2422217 = 1816663) B1816663
theorem B3077585 : Blo 850355 3077585 := bstep (se 2 (by rfl) ⟨1154094, by rfl⟩ : syracuseStep 3077585 = 2308189) B2308189
theorem B1439275 : Blo 850355 1439275 := bstep (se 1 (by rfl) ⟨1079456, by rfl⟩ : syracuseStep 1439275 = 2158913) B2158913
theorem B2422331 : Blo 850355 2422331 := bstep (se 1 (by rfl) ⟨1816748, by rfl⟩ : syracuseStep 2422331 = 3633497) B3633497
theorem B23983685 : Blo 850355 23983685 := bstep (se 4 (by rfl) ⟨2248470, by rfl⟩ : syracuseStep 23983685 = 4496941) B4496941
theorem B3241559 : Blo 850355 3241559 := bstep (se 1 (by rfl) ⟨2431169, by rfl⟩ : syracuseStep 3241559 = 4862339) B4862339
theorem B1275563 : Blo 850355 1275563 := bstep (se 1 (by rfl) ⟨956672, by rfl⟩ : syracuseStep 1275563 = 1913345) B1913345
theorem B2422457 : Blo 850355 2422457 := bstep (se 2 (by rfl) ⟨908421, by rfl⟩ : syracuseStep 2422457 = 1816843) B1816843
theorem B1439417 : Blo 850355 1439417 := bstep (se 2 (by rfl) ⟨539781, by rfl⟩ : syracuseStep 1439417 = 1079563) B1079563
theorem B1275593 : Blo 850355 1275593 := bstep (se 2 (by rfl) ⟨478347, by rfl⟩ : syracuseStep 1275593 = 956695) B956695
theorem B18446129 : Blo 850355 18446129 := bstep (se 2 (by rfl) ⟨6917298, by rfl⟩ : syracuseStep 18446129 = 13834597) B13834597
theorem B8189747 : Blo 850355 8189747 := bstep (se 1 (by rfl) ⟨6142310, by rfl⟩ : syracuseStep 8189747 = 12284621) B12284621
theorem B1275707 : Blo 850355 1275707 := bstep (se 1 (by rfl) ⟨956780, by rfl⟩ : syracuseStep 1275707 = 1913561) B1913561
theorem B4323131 : Blo 850355 4323131 := bstep (se 1 (by rfl) ⟨3242348, by rfl⟩ : syracuseStep 4323131 = 6484697) B6484697
theorem B1275767 : Blo 850355 1275767 := bstep (se 1 (by rfl) ⟨956825, by rfl⟩ : syracuseStep 1275767 = 1913651) B1913651
theorem B2160503 : Blo 850355 2160503 := bstep (se 1 (by rfl) ⟨1620377, by rfl⟩ : syracuseStep 2160503 = 3240755) B3240755
theorem B1275791 : Blo 850355 1275791 := bstep (se 1 (by rfl) ⟨956843, by rfl⟩ : syracuseStep 1275791 = 1913687) B1913687
theorem B1079183 : Blo 850355 1079183 := bstep (se 1 (by rfl) ⟨809387, by rfl⟩ : syracuseStep 1079183 = 1618775) B1618775
theorem B1275833 : Blo 850355 1275833 := bstep (se 2 (by rfl) ⟨478437, by rfl⟩ : syracuseStep 1275833 = 956875) B956875
theorem B4323293 : Blo 850355 4323293 := bstep (se 3 (by rfl) ⟨810617, by rfl⟩ : syracuseStep 4323293 = 1621235) B1621235
theorem B1275911 : Blo 850355 1275911 := bstep (se 1 (by rfl) ⟨956933, by rfl⟩ : syracuseStep 1275911 = 1913867) B1913867
theorem B2881547 : Blo 850355 2881547 := bstep (se 1 (by rfl) ⟨2161160, by rfl⟩ : syracuseStep 2881547 = 4322321) B4322321
theorem B1275947 : Blo 850355 1275947 := bstep (se 1 (by rfl) ⟨956960, by rfl⟩ : syracuseStep 1275947 = 1913921) B1913921
theorem B3242045 : Blo 850355 3242045 := bstep (se 3 (by rfl) ⟨607883, by rfl⟩ : syracuseStep 3242045 = 1215767) B1215767
theorem B1275977 : Blo 850355 1275977 := bstep (se 2 (by rfl) ⟨478491, by rfl⟩ : syracuseStep 1275977 = 956983) B956983
theorem B2881655 : Blo 850355 2881655 := bstep (se 1 (by rfl) ⟨2161241, by rfl⟩ : syracuseStep 2881655 = 4322483) B4322483
theorem B3078263 : Blo 850355 3078263 := bstep (se 1 (by rfl) ⟨2308697, by rfl⟩ : syracuseStep 3078263 = 4617395) B4617395
theorem B2455705 : Blo 850355 2455705 := bstep (se 2 (by rfl) ⟨920889, by rfl⟩ : syracuseStep 2455705 = 1841779) B1841779
theorem B1276091 : Blo 850355 1276091 := bstep (se 1 (by rfl) ⟨957068, by rfl⟩ : syracuseStep 1276091 = 1914137) B1914137
theorem B1276151 : Blo 850355 1276151 := bstep (se 1 (by rfl) ⟨957113, by rfl⟩ : syracuseStep 1276151 = 1914227) B1914227
theorem B1276175 : Blo 850355 1276175 := bstep (se 1 (by rfl) ⟨957131, by rfl⟩ : syracuseStep 1276175 = 1914263) B1914263
theorem B4323617 : Blo 850355 4323617 := bstep (se 2 (by rfl) ⟨1621356, by rfl⟩ : syracuseStep 4323617 = 3242713) B3242713
theorem B1276217 : Blo 850355 1276217 := bstep (se 2 (by rfl) ⟨478581, by rfl⟩ : syracuseStep 1276217 = 957163) B957163
theorem B4094297 : Blo 850355 4094297 := bstep (se 2 (by rfl) ⟨1535361, by rfl⟩ : syracuseStep 4094297 = 3070723) B3070723
theorem B1440119 : Blo 850355 1440119 := bstep (se 1 (by rfl) ⟨1080089, by rfl⟩ : syracuseStep 1440119 = 2160179) B2160179
theorem B1276295 : Blo 850355 1276295 := bstep (se 1 (by rfl) ⟨957221, by rfl⟩ : syracuseStep 1276295 = 1914443) B1914443
theorem B1276331 : Blo 850355 1276331 := bstep (se 1 (by rfl) ⟨957248, by rfl⟩ : syracuseStep 1276331 = 1914497) B1914497
theorem B850363 : Blo 850355 850363 := bstep (se 1 (by rfl) ⟨637772, by rfl⟩ : syracuseStep 850363 = 1275545) B1275545
theorem B1276361 : Blo 850355 1276361 := bstep (se 2 (by rfl) ⟨478635, by rfl⟩ : syracuseStep 1276361 = 957271) B957271
theorem B850439 : Blo 850355 850439 := bstep (se 1 (by rfl) ⟨637829, by rfl⟩ : syracuseStep 850439 = 1275659) B1275659
theorem B850447 : Blo 850355 850447 := bstep (se 1 (by rfl) ⟨637835, by rfl⟩ : syracuseStep 850447 = 1275671) B1275671
theorem B850491 : Blo 850355 850491 := bstep (se 1 (by rfl) ⟨637868, by rfl⟩ : syracuseStep 850491 = 1275737) B1275737
theorem B1276475 : Blo 850355 1276475 := bstep (se 1 (by rfl) ⟨957356, by rfl⟩ : syracuseStep 1276475 = 1914713) B1914713
theorem B1276535 : Blo 850355 1276535 := bstep (se 1 (by rfl) ⟨957401, by rfl⟩ : syracuseStep 1276535 = 1914803) B1914803
theorem B850567 : Blo 850355 850567 := bstep (se 1 (by rfl) ⟨637925, by rfl⟩ : syracuseStep 850567 = 1275851) B1275851
theorem B1276559 : Blo 850355 1276559 := bstep (se 1 (by rfl) ⟨957419, by rfl⟩ : syracuseStep 1276559 = 1914839) B1914839
theorem B850575 : Blo 850355 850575 := bstep (se 1 (by rfl) ⟨637931, by rfl⟩ : syracuseStep 850575 = 1275863) B1275863
theorem B1276601 : Blo 850355 1276601 := bstep (se 2 (by rfl) ⟨478725, by rfl⟩ : syracuseStep 1276601 = 957451) B957451
theorem B850619 : Blo 850355 850619 := bstep (se 1 (by rfl) ⟨637964, by rfl⟩ : syracuseStep 850619 = 1275929) B1275929
theorem B2882249 : Blo 850355 2882249 := bstep (se 2 (by rfl) ⟨1080843, by rfl⟩ : syracuseStep 2882249 = 2161687) B2161687
theorem B850695 : Blo 850355 850695 := bstep (se 1 (by rfl) ⟨638021, by rfl⟩ : syracuseStep 850695 = 1276043) B1276043
theorem B1276679 : Blo 850355 1276679 := bstep (se 1 (by rfl) ⟨957509, by rfl⟩ : syracuseStep 1276679 = 1915019) B1915019
theorem B850703 : Blo 850355 850703 := bstep (se 1 (by rfl) ⟨638027, by rfl⟩ : syracuseStep 850703 = 1276055) B1276055
theorem B1276715 : Blo 850355 1276715 := bstep (se 1 (by rfl) ⟨957536, by rfl⟩ : syracuseStep 1276715 = 1915073) B1915073
theorem B850747 : Blo 850355 850747 := bstep (se 1 (by rfl) ⟨638060, by rfl⟩ : syracuseStep 850747 = 1276121) B1276121
theorem B4848443 : Blo 850355 4848443 := bstep (se 1 (by rfl) ⟨3636332, by rfl⟩ : syracuseStep 4848443 = 7272665) B7272665
theorem B1440571 : Blo 850355 1440571 := bstep (se 1 (by rfl) ⟨1080428, by rfl⟩ : syracuseStep 1440571 = 2160857) B2160857
theorem B1276745 : Blo 850355 1276745 := bstep (se 2 (by rfl) ⟨478779, by rfl⟩ : syracuseStep 1276745 = 957559) B957559
theorem B850823 : Blo 850355 850823 := bstep (se 1 (by rfl) ⟨638117, by rfl⟩ : syracuseStep 850823 = 1276235) B1276235
theorem B1211279 : Blo 850355 1211279 := bstep (se 1 (by rfl) ⟨908459, by rfl⟩ : syracuseStep 1211279 = 1816919) B1816919
theorem B850831 : Blo 850355 850831 := bstep (se 1 (by rfl) ⟨638123, by rfl⟩ : syracuseStep 850831 = 1276247) B1276247
theorem B850875 : Blo 850355 850875 := bstep (se 1 (by rfl) ⟨638156, by rfl⟩ : syracuseStep 850875 = 1276313) B1276313
theorem B1276859 : Blo 850355 1276859 := bstep (se 1 (by rfl) ⟨957644, by rfl⟩ : syracuseStep 1276859 = 1915289) B1915289
theorem B1440713 : Blo 850355 1440713 := bstep (se 2 (by rfl) ⟨540267, by rfl⟩ : syracuseStep 1440713 = 1080535) B1080535
theorem B1276919 : Blo 850355 1276919 := bstep (se 1 (by rfl) ⟨957689, by rfl⟩ : syracuseStep 1276919 = 1915379) B1915379
theorem B850951 : Blo 850355 850951 := bstep (se 1 (by rfl) ⟨638213, by rfl⟩ : syracuseStep 850951 = 1276427) B1276427
theorem B850959 : Blo 850355 850959 := bstep (se 1 (by rfl) ⟨638219, by rfl⟩ : syracuseStep 850959 = 1276439) B1276439
theorem B1276943 : Blo 850355 1276943 := bstep (se 1 (by rfl) ⟨957707, by rfl⟩ : syracuseStep 1276943 = 1915415) B1915415
theorem B5176349 : Blo 850355 5176349 := bstep (se 3 (by rfl) ⟨970565, by rfl⟩ : syracuseStep 5176349 = 1941131) B1941131
theorem B1276985 : Blo 850355 1276985 := bstep (se 2 (by rfl) ⟨478869, by rfl⟩ : syracuseStep 1276985 = 957739) B957739
theorem B851003 : Blo 850355 851003 := bstep (se 1 (by rfl) ⟨638252, by rfl⟩ : syracuseStep 851003 = 1276505) B1276505
theorem B6487127 : Blo 850355 6487127 := bstep (se 1 (by rfl) ⟨4865345, by rfl⟩ : syracuseStep 6487127 = 9730691) B9730691
theorem B851079 : Blo 850355 851079 := bstep (se 1 (by rfl) ⟨638309, by rfl⟩ : syracuseStep 851079 = 1276619) B1276619
theorem B1277063 : Blo 850355 1277063 := bstep (se 1 (by rfl) ⟨957797, by rfl⟩ : syracuseStep 1277063 = 1915595) B1915595
theorem B2161799 : Blo 850355 2161799 := bstep (se 1 (by rfl) ⟨1621349, by rfl⟩ : syracuseStep 2161799 = 3242699) B3242699
theorem B851087 : Blo 850355 851087 := bstep (se 1 (by rfl) ⟨638315, by rfl⟩ : syracuseStep 851087 = 1276631) B1276631
theorem B1277099 : Blo 850355 1277099 := bstep (se 1 (by rfl) ⟨957824, by rfl⟩ : syracuseStep 1277099 = 1915649) B1915649
theorem B5176493 : Blo 850355 5176493 := bstep (se 3 (by rfl) ⟨970592, by rfl⟩ : syracuseStep 5176493 = 1941185) B1941185
theorem B2161849 : Blo 850355 2161849 := bstep (se 2 (by rfl) ⟨810693, by rfl⟩ : syracuseStep 2161849 = 1621387) B1621387
theorem B851131 : Blo 850355 851131 := bstep (se 1 (by rfl) ⟨638348, by rfl⟩ : syracuseStep 851131 = 1276697) B1276697
theorem B1211593 : Blo 850355 1211593 := bstep (se 2 (by rfl) ⟨454347, by rfl⟩ : syracuseStep 1211593 = 908695) B908695
theorem B1277129 : Blo 850355 1277129 := bstep (se 2 (by rfl) ⟨478923, by rfl⟩ : syracuseStep 1277129 = 957847) B957847
theorem B9862345 : Blo 850355 9862345 := bstep (se 2 (by rfl) ⟨3698379, by rfl⟩ : syracuseStep 9862345 = 7396759) B7396759
theorem B4324589 : Blo 850355 4324589 := bstep (se 3 (by rfl) ⟨810860, by rfl⟩ : syracuseStep 4324589 = 1621721) B1621721
theorem B851207 : Blo 850355 851207 := bstep (se 1 (by rfl) ⟨638405, by rfl⟩ : syracuseStep 851207 = 1276811) B1276811
theorem B851215 : Blo 850355 851215 := bstep (se 1 (by rfl) ⟨638411, by rfl⟩ : syracuseStep 851215 = 1276823) B1276823
theorem B2424107 : Blo 850355 2424107 := bstep (se 1 (by rfl) ⟨1818080, by rfl⟩ : syracuseStep 2424107 = 3636161) B3636161
theorem B851259 : Blo 850355 851259 := bstep (se 1 (by rfl) ⟨638444, by rfl⟩ : syracuseStep 851259 = 1276889) B1276889
theorem B1277243 : Blo 850355 1277243 := bstep (se 1 (by rfl) ⟨957932, by rfl⟩ : syracuseStep 1277243 = 1915865) B1915865
theorem B1277303 : Blo 850355 1277303 := bstep (se 1 (by rfl) ⟨957977, by rfl⟩ : syracuseStep 1277303 = 1915955) B1915955
theorem B851335 : Blo 850355 851335 := bstep (se 1 (by rfl) ⟨638501, by rfl⟩ : syracuseStep 851335 = 1277003) B1277003
theorem B2882951 : Blo 850355 2882951 := bstep (se 1 (by rfl) ⟨2162213, by rfl⟩ : syracuseStep 2882951 = 4324427) B4324427
theorem B851343 : Blo 850355 851343 := bstep (se 1 (by rfl) ⟨638507, by rfl⟩ : syracuseStep 851343 = 1277015) B1277015
theorem B1277327 : Blo 850355 1277327 := bstep (se 1 (by rfl) ⟨957995, by rfl⟩ : syracuseStep 1277327 = 1915991) B1915991
theorem B2588051 : Blo 850355 2588051 := bstep (se 1 (by rfl) ⟨1941038, by rfl⟩ : syracuseStep 2588051 = 3882077) B3882077
theorem B1277369 : Blo 850355 1277369 := bstep (se 2 (by rfl) ⟨479013, by rfl⟩ : syracuseStep 1277369 = 958027) B958027
theorem B851387 : Blo 850355 851387 := bstep (se 1 (by rfl) ⟨638540, by rfl⟩ : syracuseStep 851387 = 1277081) B1277081
theorem B3243473 : Blo 850355 3243473 := bstep (se 2 (by rfl) ⟨1216302, by rfl⟩ : syracuseStep 3243473 = 2432605) B2432605
theorem B851463 : Blo 850355 851463 := bstep (se 1 (by rfl) ⟨638597, by rfl⟩ : syracuseStep 851463 = 1277195) B1277195
theorem B1277447 : Blo 850355 1277447 := bstep (se 1 (by rfl) ⟨958085, by rfl⟩ : syracuseStep 1277447 = 1916171) B1916171
theorem B851471 : Blo 850355 851471 := bstep (se 1 (by rfl) ⟨638603, by rfl⟩ : syracuseStep 851471 = 1277207) B1277207
theorem B1277483 : Blo 850355 1277483 := bstep (se 1 (by rfl) ⟨958112, by rfl⟩ : syracuseStep 1277483 = 1916225) B1916225
theorem B851515 : Blo 850355 851515 := bstep (se 1 (by rfl) ⟨638636, by rfl⟩ : syracuseStep 851515 = 1277273) B1277273
theorem B6323779 : Blo 850355 6323779 := bstep (se 1 (by rfl) ⟨4742834, by rfl⟩ : syracuseStep 6323779 = 9485669) B9485669
theorem B1277513 : Blo 850355 1277513 := bstep (se 2 (by rfl) ⟨479067, by rfl⟩ : syracuseStep 1277513 = 958135) B958135
theorem B851591 : Blo 850355 851591 := bstep (se 1 (by rfl) ⟨638693, by rfl⟩ : syracuseStep 851591 = 1277387) B1277387
theorem B1441415 : Blo 850355 1441415 := bstep (se 1 (by rfl) ⟨1081061, by rfl⟩ : syracuseStep 1441415 = 2162123) B2162123
theorem B851599 : Blo 850355 851599 := bstep (se 1 (by rfl) ⟨638699, by rfl⟩ : syracuseStep 851599 = 1277399) B1277399
theorem B851643 : Blo 850355 851643 := bstep (se 1 (by rfl) ⟨638732, by rfl⟩ : syracuseStep 851643 = 1277465) B1277465
theorem B1277627 : Blo 850355 1277627 := bstep (se 1 (by rfl) ⟨958220, by rfl⟩ : syracuseStep 1277627 = 1916441) B1916441
theorem B1277687 : Blo 850355 1277687 := bstep (se 1 (by rfl) ⟨958265, by rfl⟩ : syracuseStep 1277687 = 1916531) B1916531
theorem B2883329 : Blo 850355 2883329 := bstep (se 2 (by rfl) ⟨1081248, by rfl⟩ : syracuseStep 2883329 = 2162497) B2162497
theorem B851719 : Blo 850355 851719 := bstep (se 1 (by rfl) ⟨638789, by rfl⟩ : syracuseStep 851719 = 1277579) B1277579
theorem B2588431 : Blo 850355 2588431 := bstep (se 1 (by rfl) ⟨1941323, by rfl⟩ : syracuseStep 2588431 = 3882647) B3882647
theorem B851727 : Blo 850355 851727 := bstep (se 1 (by rfl) ⟨638795, by rfl⟩ : syracuseStep 851727 = 1277591) B1277591
theorem B1277711 : Blo 850355 1277711 := bstep (se 1 (by rfl) ⟨958283, by rfl⟩ : syracuseStep 1277711 = 1916567) B1916567
theorem B2162447 : Blo 850355 2162447 := bstep (se 1 (by rfl) ⟨1621835, by rfl⟩ : syracuseStep 2162447 = 3243671) B3243671
theorem B1277753 : Blo 850355 1277753 := bstep (se 2 (by rfl) ⟨479157, by rfl⟩ : syracuseStep 1277753 = 958315) B958315
theorem B851771 : Blo 850355 851771 := bstep (se 1 (by rfl) ⟨638828, by rfl⟩ : syracuseStep 851771 = 1277657) B1277657
theorem B851847 : Blo 850355 851847 := bstep (se 1 (by rfl) ⟨638885, by rfl⟩ : syracuseStep 851847 = 1277771) B1277771
theorem B1277831 : Blo 850355 1277831 := bstep (se 1 (by rfl) ⟨958373, by rfl⟩ : syracuseStep 1277831 = 1916747) B1916747
theorem B851855 : Blo 850355 851855 := bstep (se 1 (by rfl) ⟨638891, by rfl⟩ : syracuseStep 851855 = 1277783) B1277783
theorem B1277867 : Blo 850355 1277867 := bstep (se 1 (by rfl) ⟨958400, by rfl⟩ : syracuseStep 1277867 = 1916801) B1916801
theorem B851899 : Blo 850355 851899 := bstep (se 1 (by rfl) ⟨638924, by rfl⟩ : syracuseStep 851899 = 1277849) B1277849
theorem B1277897 : Blo 850355 1277897 := bstep (se 2 (by rfl) ⟨479211, by rfl⟩ : syracuseStep 1277897 = 958423) B958423
theorem B852007 : Blo 850355 852007 := bstep (se 1 (by rfl) ⟨639005, by rfl⟩ : syracuseStep 852007 = 1278011) B1278011
theorem B852047 : Blo 850355 852047 := bstep (se 1 (by rfl) ⟨639035, by rfl⟩ : syracuseStep 852047 = 1278071) B1278071
theorem B852063 : Blo 850355 852063 := bstep (se 1 (by rfl) ⟨639047, by rfl⟩ : syracuseStep 852063 = 1278095) B1278095
theorem B852091 : Blo 850355 852091 := bstep (se 1 (by rfl) ⟨639068, by rfl⟩ : syracuseStep 852091 = 1278137) B1278137
theorem B852143 : Blo 850355 852143 := bstep (se 1 (by rfl) ⟨639107, by rfl⟩ : syracuseStep 852143 = 1278215) B1278215
theorem B852167 : Blo 850355 852167 := bstep (se 1 (by rfl) ⟨639125, by rfl⟩ : syracuseStep 852167 = 1278251) B1278251
theorem B852187 : Blo 850355 852187 := bstep (se 1 (by rfl) ⟨639140, by rfl⟩ : syracuseStep 852187 = 1278281) B1278281
theorem B852263 : Blo 850355 852263 := bstep (se 1 (by rfl) ⟨639197, by rfl⟩ : syracuseStep 852263 = 1278395) B1278395
theorem B852303 : Blo 850355 852303 := bstep (se 1 (by rfl) ⟨639227, by rfl⟩ : syracuseStep 852303 = 1278455) B1278455
theorem B852319 : Blo 850355 852319 := bstep (se 1 (by rfl) ⟨639239, by rfl⟩ : syracuseStep 852319 = 1278479) B1278479
theorem B852347 : Blo 850355 852347 := bstep (se 1 (by rfl) ⟨639260, by rfl⟩ : syracuseStep 852347 = 1278521) B1278521
theorem B1278383 : Blo 850355 1278383 := bstep (se 1 (by rfl) ⟨958787, by rfl⟩ : syracuseStep 1278383 = 1917575) B1917575
theorem B852399 : Blo 850355 852399 := bstep (se 1 (by rfl) ⟨639299, by rfl⟩ : syracuseStep 852399 = 1278599) B1278599
theorem B852423 : Blo 850355 852423 := bstep (se 1 (by rfl) ⟨639317, by rfl⟩ : syracuseStep 852423 = 1278635) B1278635
theorem B852443 : Blo 850355 852443 := bstep (se 1 (by rfl) ⟨639332, by rfl⟩ : syracuseStep 852443 = 1278665) B1278665
theorem B1278473 : Blo 850355 1278473 := bstep (se 2 (by rfl) ⟨479427, by rfl⟩ : syracuseStep 1278473 = 958855) B958855
theorem B1278503 : Blo 850355 1278503 := bstep (se 1 (by rfl) ⟨958877, by rfl⟩ : syracuseStep 1278503 = 1917755) B1917755
theorem B852519 : Blo 850355 852519 := bstep (se 1 (by rfl) ⟨639389, by rfl⟩ : syracuseStep 852519 = 1278779) B1278779
theorem B852559 : Blo 850355 852559 := bstep (se 1 (by rfl) ⟨639419, by rfl⟩ : syracuseStep 852559 = 1278839) B1278839
theorem B852575 : Blo 850355 852575 := bstep (se 1 (by rfl) ⟨639431, by rfl⟩ : syracuseStep 852575 = 1278863) B1278863
theorem B1213051 : Blo 850355 1213051 := bstep (se 1 (by rfl) ⟨909788, by rfl⟩ : syracuseStep 1213051 = 1819577) B1819577
theorem B1278587 : Blo 850355 1278587 := bstep (se 1 (by rfl) ⟨958940, by rfl⟩ : syracuseStep 1278587 = 1917881) B1917881
theorem B852603 : Blo 850355 852603 := bstep (se 1 (by rfl) ⟨639452, by rfl⟩ : syracuseStep 852603 = 1278905) B1278905
theorem B852655 : Blo 850355 852655 := bstep (se 1 (by rfl) ⟨639491, by rfl⟩ : syracuseStep 852655 = 1278983) B1278983
theorem B5472953 : Blo 850355 5472953 := bstep (se 2 (by rfl) ⟨2052357, by rfl⟩ : syracuseStep 5472953 = 4104715) B4104715
theorem B852679 : Blo 850355 852679 := bstep (se 1 (by rfl) ⟨639509, by rfl⟩ : syracuseStep 852679 = 1279019) B1279019
theorem B6914771 : Blo 850355 6914771 := bstep (se 1 (by rfl) ⟨5186078, by rfl⟩ : syracuseStep 6914771 = 10372157) B10372157
theorem B852699 : Blo 850355 852699 := bstep (se 1 (by rfl) ⟨639524, by rfl⟩ : syracuseStep 852699 = 1279049) B1279049
theorem B1278713 : Blo 850355 1278713 := bstep (se 2 (by rfl) ⟨479517, by rfl⟩ : syracuseStep 1278713 = 959035) B959035
theorem B852775 : Blo 850355 852775 := bstep (se 1 (by rfl) ⟨639581, by rfl⟩ : syracuseStep 852775 = 1279163) B1279163
theorem B852815 : Blo 850355 852815 := bstep (se 1 (by rfl) ⟨639611, by rfl⟩ : syracuseStep 852815 = 1279223) B1279223
theorem B1278815 : Blo 850355 1278815 := bstep (se 1 (by rfl) ⟨959111, by rfl⟩ : syracuseStep 1278815 = 1918223) B1918223
theorem B852831 : Blo 850355 852831 := bstep (se 1 (by rfl) ⟨639623, by rfl⟩ : syracuseStep 852831 = 1279247) B1279247
theorem B2458475 : Blo 850355 2458475 := bstep (se 1 (by rfl) ⟨1843856, by rfl⟩ : syracuseStep 2458475 = 3687713) B3687713
theorem B1278827 : Blo 850355 1278827 := bstep (se 1 (by rfl) ⟨959120, by rfl⟩ : syracuseStep 1278827 = 1918241) B1918241
theorem B852859 : Blo 850355 852859 := bstep (se 1 (by rfl) ⟨639644, by rfl⟩ : syracuseStep 852859 = 1279289) B1279289
theorem B852911 : Blo 850355 852911 := bstep (se 1 (by rfl) ⟨639683, by rfl⟩ : syracuseStep 852911 = 1279367) B1279367
theorem B852935 : Blo 850355 852935 := bstep (se 1 (by rfl) ⟨639701, by rfl⟩ : syracuseStep 852935 = 1279403) B1279403
theorem B852955 : Blo 850355 852955 := bstep (se 1 (by rfl) ⟨639716, by rfl⟩ : syracuseStep 852955 = 1279433) B1279433
theorem B853031 : Blo 850355 853031 := bstep (se 1 (by rfl) ⟨639773, by rfl⟩ : syracuseStep 853031 = 1279547) B1279547
theorem B1279055 : Blo 850355 1279055 := bstep (se 1 (by rfl) ⟨959291, by rfl⟩ : syracuseStep 1279055 = 1918583) B1918583
theorem B853071 : Blo 850355 853071 := bstep (se 1 (by rfl) ⟨639803, by rfl⟩ : syracuseStep 853071 = 1279607) B1279607
theorem B853087 : Blo 850355 853087 := bstep (se 1 (by rfl) ⟨639815, by rfl⟩ : syracuseStep 853087 = 1279631) B1279631
theorem B853115 : Blo 850355 853115 := bstep (se 1 (by rfl) ⟨639836, by rfl⟩ : syracuseStep 853115 = 1279673) B1279673
theorem B853167 : Blo 850355 853167 := bstep (se 1 (by rfl) ⟨639875, by rfl⟩ : syracuseStep 853167 = 1279751) B1279751
theorem B1279175 : Blo 850355 1279175 := bstep (se 1 (by rfl) ⟨959381, by rfl⟩ : syracuseStep 1279175 = 1918763) B1918763
theorem B853191 : Blo 850355 853191 := bstep (se 1 (by rfl) ⟨639893, by rfl⟩ : syracuseStep 853191 = 1279787) B1279787
theorem B853211 : Blo 850355 853211 := bstep (se 1 (by rfl) ⟨639908, by rfl⟩ : syracuseStep 853211 = 1279817) B1279817
theorem B853287 : Blo 850355 853287 := bstep (se 1 (by rfl) ⟨639965, by rfl⟩ : syracuseStep 853287 = 1279931) B1279931
theorem B853327 : Blo 850355 853327 := bstep (se 1 (by rfl) ⟨639995, by rfl⟩ : syracuseStep 853327 = 1279991) B1279991
theorem B13305181 : Blo 850355 13305181 := bstep (se 3 (by rfl) ⟨2494721, by rfl⟩ : syracuseStep 13305181 = 4989443) B4989443
theorem B853343 : Blo 850355 853343 := bstep (se 1 (by rfl) ⟨640007, by rfl⟩ : syracuseStep 853343 = 1280015) B1280015
theorem B1279337 : Blo 850355 1279337 := bstep (se 2 (by rfl) ⟨479751, by rfl⟩ : syracuseStep 1279337 = 959503) B959503
theorem B7013747 : Blo 850355 7013747 := bstep (se 1 (by rfl) ⟨5260310, by rfl⟩ : syracuseStep 7013747 = 10520621) B10520621
theorem B853371 : Blo 850355 853371 := bstep (se 1 (by rfl) ⟨640028, by rfl⟩ : syracuseStep 853371 = 1280057) B1280057
theorem B4982159 : Blo 850355 4982159 := bstep (se 1 (by rfl) ⟨3736619, by rfl⟩ : syracuseStep 4982159 = 7473239) B7473239
theorem B853423 : Blo 850355 853423 := bstep (se 1 (by rfl) ⟨640067, by rfl⟩ : syracuseStep 853423 = 1280135) B1280135
theorem B1279415 : Blo 850355 1279415 := bstep (se 1 (by rfl) ⟨959561, by rfl⟩ : syracuseStep 1279415 = 1919123) B1919123
theorem B853447 : Blo 850355 853447 := bstep (se 1 (by rfl) ⟨640085, by rfl⟩ : syracuseStep 853447 = 1280171) B1280171
theorem B1279451 : Blo 850355 1279451 := bstep (se 1 (by rfl) ⟨959588, by rfl⟩ : syracuseStep 1279451 = 1919177) B1919177
theorem B853467 : Blo 850355 853467 := bstep (se 1 (by rfl) ⟨640100, by rfl⟩ : syracuseStep 853467 = 1280201) B1280201
theorem B853543 : Blo 850355 853543 := bstep (se 1 (by rfl) ⟨640157, by rfl⟩ : syracuseStep 853543 = 1280315) B1280315
theorem B853583 : Blo 850355 853583 := bstep (se 1 (by rfl) ⟨640187, by rfl⟩ : syracuseStep 853583 = 1280375) B1280375
theorem B853599 : Blo 850355 853599 := bstep (se 1 (by rfl) ⟨640199, by rfl⟩ : syracuseStep 853599 = 1280399) B1280399
theorem B853627 : Blo 850355 853627 := bstep (se 1 (by rfl) ⟨640220, by rfl⟩ : syracuseStep 853627 = 1280441) B1280441
theorem B853679 : Blo 850355 853679 := bstep (se 1 (by rfl) ⟨640259, by rfl⟩ : syracuseStep 853679 = 1280519) B1280519
theorem B2426557 : Blo 850355 2426557 := bstep (se 3 (by rfl) ⟨454979, by rfl⟩ : syracuseStep 2426557 = 909959) B909959
theorem B853703 : Blo 850355 853703 := bstep (se 1 (by rfl) ⟨640277, by rfl⟩ : syracuseStep 853703 = 1280555) B1280555
theorem B853723 : Blo 850355 853723 := bstep (se 1 (by rfl) ⟨640292, by rfl⟩ : syracuseStep 853723 = 1280585) B1280585
theorem B853799 : Blo 850355 853799 := bstep (se 1 (by rfl) ⟨640349, by rfl⟩ : syracuseStep 853799 = 1280699) B1280699
theorem B853839 : Blo 850355 853839 := bstep (se 1 (by rfl) ⟨640379, by rfl⟩ : syracuseStep 853839 = 1280759) B1280759
theorem B853855 : Blo 850355 853855 := bstep (se 1 (by rfl) ⟨640391, by rfl⟩ : syracuseStep 853855 = 1280783) B1280783
theorem B853883 : Blo 850355 853883 := bstep (se 1 (by rfl) ⟨640412, by rfl⟩ : syracuseStep 853883 = 1280825) B1280825
theorem B1279919 : Blo 850355 1279919 := bstep (se 1 (by rfl) ⟨959939, by rfl⟩ : syracuseStep 1279919 = 1919879) B1919879
theorem B853935 : Blo 850355 853935 := bstep (se 1 (by rfl) ⟨640451, by rfl⟩ : syracuseStep 853935 = 1280903) B1280903
theorem B853959 : Blo 850355 853959 := bstep (se 1 (by rfl) ⟨640469, by rfl⟩ : syracuseStep 853959 = 1280939) B1280939
theorem B853979 : Blo 850355 853979 := bstep (se 1 (by rfl) ⟨640484, by rfl⟩ : syracuseStep 853979 = 1280969) B1280969
theorem B1280009 : Blo 850355 1280009 := bstep (se 2 (by rfl) ⟨480003, by rfl⟩ : syracuseStep 1280009 = 960007) B960007
theorem B1280039 : Blo 850355 1280039 := bstep (se 1 (by rfl) ⟨960029, by rfl⟩ : syracuseStep 1280039 = 1920059) B1920059
theorem B854055 : Blo 850355 854055 := bstep (se 1 (by rfl) ⟨640541, by rfl⟩ : syracuseStep 854055 = 1281083) B1281083
theorem B854095 : Blo 850355 854095 := bstep (se 1 (by rfl) ⟨640571, by rfl⟩ : syracuseStep 854095 = 1281143) B1281143
theorem B854111 : Blo 850355 854111 := bstep (se 1 (by rfl) ⟨640583, by rfl⟩ : syracuseStep 854111 = 1281167) B1281167
theorem B1280123 : Blo 850355 1280123 := bstep (se 1 (by rfl) ⟨960092, by rfl⟩ : syracuseStep 1280123 = 1920185) B1920185
theorem B854139 : Blo 850355 854139 := bstep (se 1 (by rfl) ⟨640604, by rfl⟩ : syracuseStep 854139 = 1281209) B1281209
theorem B854191 : Blo 850355 854191 := bstep (se 1 (by rfl) ⟨640643, by rfl⟩ : syracuseStep 854191 = 1281287) B1281287
theorem B854215 : Blo 850355 854215 := bstep (se 1 (by rfl) ⟨640661, by rfl⟩ : syracuseStep 854215 = 1281323) B1281323
theorem B854235 : Blo 850355 854235 := bstep (se 1 (by rfl) ⟨640676, by rfl⟩ : syracuseStep 854235 = 1281353) B1281353
theorem B1280249 : Blo 850355 1280249 := bstep (se 2 (by rfl) ⟨480093, by rfl⟩ : syracuseStep 1280249 = 960187) B960187
theorem B3639563 : Blo 850355 3639563 := bstep (se 1 (by rfl) ⟨2729672, by rfl⟩ : syracuseStep 3639563 = 5459345) B5459345
theorem B854311 : Blo 850355 854311 := bstep (se 1 (by rfl) ⟨640733, by rfl⟩ : syracuseStep 854311 = 1281467) B1281467
theorem B3639613 : Blo 850355 3639613 := bstep (se 3 (by rfl) ⟨682427, by rfl⟩ : syracuseStep 3639613 = 1364855) B1364855
theorem B854351 : Blo 850355 854351 := bstep (se 1 (by rfl) ⟨640763, by rfl⟩ : syracuseStep 854351 = 1281527) B1281527
theorem B1280351 : Blo 850355 1280351 := bstep (se 1 (by rfl) ⟨960263, by rfl⟩ : syracuseStep 1280351 = 1920527) B1920527
theorem B1280363 : Blo 850355 1280363 := bstep (se 1 (by rfl) ⟨960272, by rfl⟩ : syracuseStep 1280363 = 1920545) B1920545
theorem B1280591 : Blo 850355 1280591 := bstep (se 1 (by rfl) ⟨960443, by rfl⟩ : syracuseStep 1280591 = 1920887) B1920887
theorem B1215175 : Blo 850355 1215175 := bstep (se 1 (by rfl) ⟨911381, by rfl⟩ : syracuseStep 1215175 = 1822763) B1822763
theorem B1280711 : Blo 850355 1280711 := bstep (se 1 (by rfl) ⟨960533, by rfl⟩ : syracuseStep 1280711 = 1921067) B1921067
theorem B1280873 : Blo 850355 1280873 := bstep (se 2 (by rfl) ⟨480327, by rfl⟩ : syracuseStep 1280873 = 960655) B960655
theorem B3640247 : Blo 850355 3640247 := bstep (se 1 (by rfl) ⟨2730185, by rfl⟩ : syracuseStep 3640247 = 5460371) B5460371
theorem B1280951 : Blo 850355 1280951 := bstep (se 1 (by rfl) ⟨960713, by rfl⟩ : syracuseStep 1280951 = 1921427) B1921427
theorem B1280987 : Blo 850355 1280987 := bstep (se 1 (by rfl) ⟨960740, by rfl⟩ : syracuseStep 1280987 = 1921481) B1921481
theorem B2428289 : Blo 850355 2428289 := bstep (se 2 (by rfl) ⟨910608, by rfl⟩ : syracuseStep 2428289 = 1821217) B1821217
theorem B4853135 : Blo 850355 4853135 := bstep (se 1 (by rfl) ⟨3639851, by rfl⟩ : syracuseStep 4853135 = 7279703) B7279703
theorem B1281455 : Blo 850355 1281455 := bstep (se 1 (by rfl) ⟨961091, by rfl⟩ : syracuseStep 1281455 = 1922183) B1922183
theorem B2395673 : Blo 850355 2395673 := bstep (se 2 (by rfl) ⟨898377, by rfl⟩ : syracuseStep 2395673 = 1796755) B1796755
theorem B2429689 : Blo 850355 2429689 := bstep (se 2 (by rfl) ⟨911133, by rfl⟩ : syracuseStep 2429689 = 1822267) B1822267
theorem B2299279 : Blo 850355 2299279 := bstep (se 1 (by rfl) ⟨1724459, by rfl⟩ : syracuseStep 2299279 = 3448919) B3448919
theorem B6461369 : Blo 850355 6461369 := bstep (se 2 (by rfl) ⟨2423013, by rfl⟩ : syracuseStep 6461369 = 4846027) B4846027
theorem B14784599 : Blo 850355 14784599 := bstep (se 1 (by rfl) ⟨11088449, by rfl⟩ : syracuseStep 14784599 = 22176899) B22176899
theorem B2726045 : Blo 850355 2726045 := bstep (se 3 (by rfl) ⟨511133, by rfl⟩ : syracuseStep 2726045 = 1022267) B1022267
theorem B2594987 : Blo 850355 2594987 := bstep (se 1 (by rfl) ⟨1946240, by rfl⟩ : syracuseStep 2594987 = 3892481) B3892481
theorem B2431147 : Blo 850355 2431147 := bstep (se 1 (by rfl) ⟨1823360, by rfl⟩ : syracuseStep 2431147 = 3646721) B3646721
theorem B1153273 : Blo 850355 1153273 := bstep (se 2 (by rfl) ⟨432477, by rfl⟩ : syracuseStep 1153273 = 864955) B864955
theorem B956767 : Blo 850355 956767 := bstep (se 1 (by rfl) ⟨717575, by rfl⟩ : syracuseStep 956767 = 1435151) B1435151
theorem B3643937 : Blo 850355 3643937 := bstep (se 2 (by rfl) ⟨1366476, by rfl⟩ : syracuseStep 3643937 = 2732953) B2732953
theorem B957127 : Blo 850355 957127 := bstep (se 1 (by rfl) ⟨717845, by rfl⟩ : syracuseStep 957127 = 1435691) B1435691
theorem B4856759 : Blo 850355 4856759 := bstep (se 1 (by rfl) ⟨3642569, by rfl⟩ : syracuseStep 4856759 = 7285139) B7285139
theorem B1383355 : Blo 850355 1383355 := bstep (se 1 (by rfl) ⟨1037516, by rfl⟩ : syracuseStep 1383355 = 2075033) B2075033
theorem B5184665 : Blo 850355 5184665 := bstep (se 2 (by rfl) ⟨1944249, by rfl⟩ : syracuseStep 5184665 = 3888499) B3888499
theorem B2596225 : Blo 850355 2596225 := bstep (se 2 (by rfl) ⟨973584, by rfl⟩ : syracuseStep 2596225 = 1947169) B1947169
theorem B7282163 : Blo 850355 7282163 := bstep (se 1 (by rfl) ⟨5461622, by rfl⟩ : syracuseStep 7282163 = 10923245) B10923245
theorem B2432537 : Blo 850355 2432537 := bstep (se 2 (by rfl) ⟨912201, by rfl⟩ : syracuseStep 2432537 = 1824403) B1824403
theorem B957991 : Blo 850355 957991 := bstep (se 1 (by rfl) ⟨718493, by rfl⟩ : syracuseStep 957991 = 1436987) B1436987
theorem B23273189 : Blo 850355 23273189 := bstep (se 4 (by rfl) ⟨2181861, by rfl⟩ : syracuseStep 23273189 = 4363723) B4363723
theorem B63971477 : Blo 850355 63971477 := bstep (se 6 (by rfl) ⟨1499331, by rfl⟩ : syracuseStep 63971477 = 2998663) B2998663
theorem B4858217 : Blo 850355 4858217 := bstep (se 2 (by rfl) ⟨1821831, by rfl⟩ : syracuseStep 4858217 = 3643663) B3643663
theorem B1614583 : Blo 850355 1614583 := bstep (se 1 (by rfl) ⟨1210937, by rfl⟩ : syracuseStep 1614583 = 2421875) B2421875
theorem B6464285 : Blo 850355 6464285 := bstep (se 3 (by rfl) ⟨1212053, by rfl⟩ : syracuseStep 6464285 = 2424107) B2424107
theorem B2335675 : Blo 850355 2335675 := bstep (se 1 (by rfl) ⟨1751756, by rfl⟩ : syracuseStep 2335675 = 3503513) B3503513
theorem B1614811 : Blo 850355 1614811 := bstep (se 1 (by rfl) ⟨1211108, by rfl⟩ : syracuseStep 1614811 = 2422217) B2422217
theorem B1614887 : Blo 850355 1614887 := bstep (se 1 (by rfl) ⟨1211165, by rfl⟩ : syracuseStep 1614887 = 2422331) B2422331
theorem B1614971 : Blo 850355 1614971 := bstep (se 1 (by rfl) ⟨1211228, by rfl⟩ : syracuseStep 1614971 = 2422457) B2422457
theorem B959611 : Blo 850355 959611 := bstep (se 1 (by rfl) ⟨719708, by rfl⟩ : syracuseStep 959611 = 1439417) B1439417
theorem B12297419 : Blo 850355 12297419 := bstep (se 1 (by rfl) ⟨9223064, by rfl⟩ : syracuseStep 12297419 = 18446129) B18446129
theorem B2729531 : Blo 850355 2729531 := bstep (se 1 (by rfl) ⟨2047148, by rfl⟩ : syracuseStep 2729531 = 4094297) B4094297
theorem B960079 : Blo 850355 960079 := bstep (se 1 (by rfl) ⟨720059, by rfl⟩ : syracuseStep 960079 = 1440119) B1440119
theorem B1615457 : Blo 850355 1615457 := bstep (se 2 (by rfl) ⟨605796, by rfl⟩ : syracuseStep 1615457 = 1211593) B1211593
theorem B13149793 : Blo 850355 13149793 := bstep (se 2 (by rfl) ⟨4931172, by rfl⟩ : syracuseStep 13149793 = 9862345) B9862345
theorem B13837969 : Blo 850355 13837969 := bstep (se 2 (by rfl) ⟨5189238, by rfl⟩ : syracuseStep 13837969 = 10378477) B10378477
theorem B6563693 : Blo 850355 6563693 := bstep (se 3 (by rfl) ⟨1230692, by rfl⟩ : syracuseStep 6563693 = 2461385) B2461385
theorem B960475 : Blo 850355 960475 := bstep (se 1 (by rfl) ⟨720356, by rfl⟩ : syracuseStep 960475 = 1440713) B1440713
theorem B3450899 : Blo 850355 3450899 := bstep (se 1 (by rfl) ⟨2588174, by rfl⟩ : syracuseStep 3450899 = 5176349) B5176349
theorem B8431705 : Blo 850355 8431705 := bstep (se 2 (by rfl) ⟨3161889, by rfl⟩ : syracuseStep 8431705 = 6323779) B6323779
theorem B3450995 : Blo 850355 3450995 := bstep (se 1 (by rfl) ⟨2588246, by rfl⟩ : syracuseStep 3450995 = 5176493) B5176493
theorem B4728989 : Blo 850355 4728989 := bstep (se 3 (by rfl) ⟨886685, by rfl⟩ : syracuseStep 4728989 = 1773371) B1773371
theorem B3451241 : Blo 850355 3451241 := bstep (se 2 (by rfl) ⟨1294215, by rfl⟩ : syracuseStep 3451241 = 2588431) B2588431
theorem B960943 : Blo 850355 960943 := bstep (se 1 (by rfl) ⟨720707, by rfl⟩ : syracuseStep 960943 = 1441415) B1441415
theorem B4860425 : Blo 850355 4860425 := bstep (se 2 (by rfl) ⟨1822659, by rfl⟩ : syracuseStep 4860425 = 3645319) B3645319
theorem B6662681 : Blo 850355 6662681 := bstep (se 2 (by rfl) ⟨2498505, by rfl⟩ : syracuseStep 6662681 = 4997011) B4997011
theorem B7383737 : Blo 850355 7383737 := bstep (se 2 (by rfl) ⟨2768901, by rfl⟩ : syracuseStep 7383737 = 5537803) B5537803
theorem B5450449 : Blo 850355 5450449 := bstep (se 2 (by rfl) ⟨2043918, by rfl⟩ : syracuseStep 5450449 = 4087837) B4087837
theorem B1616915 : Blo 850355 1616915 := bstep (se 1 (by rfl) ⟨1212686, by rfl⟩ : syracuseStep 1616915 = 2425373) B2425373
theorem B26258455 : Blo 850355 26258455 := bstep (se 1 (by rfl) ⟨19693841, by rfl⟩ : syracuseStep 26258455 = 39387683) B39387683
theorem B2731529 : Blo 850355 2731529 := bstep (se 2 (by rfl) ⟨1024323, by rfl⟩ : syracuseStep 2731529 = 2048647) B2048647
theorem B1945127 : Blo 850355 1945127 := bstep (se 1 (by rfl) ⟨1458845, by rfl⟩ : syracuseStep 1945127 = 2917691) B2917691
theorem B118042181 : Blo 850355 118042181 := bstep (se 4 (by rfl) ⟨11066454, by rfl⟩ : syracuseStep 118042181 = 22132909) B22132909
theorem B4599595 : Blo 850355 4599595 := bstep (se 1 (by rfl) ⟨3449696, by rfl⟩ : syracuseStep 4599595 = 6899393) B6899393
theorem B4861883 : Blo 850355 4861883 := bstep (se 1 (by rfl) ⟨3646412, by rfl⟩ : syracuseStep 4861883 = 7292825) B7292825
theorem B1618319 : Blo 850355 1618319 := bstep (se 1 (by rfl) ⟨1213739, by rfl⟩ : syracuseStep 1618319 = 2427479) B2427479
theorem B1618471 : Blo 850355 1618471 := bstep (se 1 (by rfl) ⟨1213853, by rfl⟩ : syracuseStep 1618471 = 2427707) B2427707
theorem B1618555 : Blo 850355 1618555 := bstep (se 1 (by rfl) ⟨1213916, by rfl⟩ : syracuseStep 1618555 = 2427833) B2427833
theorem B1913543 : Blo 850355 1913543 := bstep (se 1 (by rfl) ⟨1435157, by rfl⟩ : syracuseStep 1913543 = 2870315) B2870315
theorem B3322799 : Blo 850355 3322799 := bstep (se 1 (by rfl) ⟨2492099, by rfl⟩ : syracuseStep 3322799 = 4984199) B4984199
theorem B6468659 : Blo 850355 6468659 := bstep (se 1 (by rfl) ⟨4851494, by rfl⟩ : syracuseStep 6468659 = 9702989) B9702989
theorem B11646017 : Blo 850355 11646017 := bstep (se 2 (by rfl) ⟨4367256, by rfl⟩ : syracuseStep 11646017 = 8734513) B8734513
theorem B1619041 : Blo 850355 1619041 := bstep (se 2 (by rfl) ⟨607140, by rfl⟩ : syracuseStep 1619041 = 1214281) B1214281
theorem B3454109 : Blo 850355 3454109 := bstep (se 3 (by rfl) ⟨647645, by rfl⟩ : syracuseStep 3454109 = 1295291) B1295291
theorem B13120861 : Blo 850355 13120861 := bstep (se 3 (by rfl) ⟨2460161, by rfl⟩ : syracuseStep 13120861 = 4920323) B4920323
theorem B13284773 : Blo 850355 13284773 := bstep (se 4 (by rfl) ⟨1245447, by rfl⟩ : syracuseStep 13284773 = 2490895) B2490895
theorem B8173061 : Blo 850355 8173061 := bstep (se 4 (by rfl) ⟨766224, by rfl⟩ : syracuseStep 8173061 = 1532449) B1532449
theorem B13809163 : Blo 850355 13809163 := bstep (se 1 (by rfl) ⟨10356872, by rfl⟩ : syracuseStep 13809163 = 20713745) B20713745
theorem B1914407 : Blo 850355 1914407 := bstep (se 1 (by rfl) ⟨1435805, by rfl⟩ : syracuseStep 1914407 = 2871611) B2871611
theorem B3454663 : Blo 850355 3454663 := bstep (se 1 (by rfl) ⟨2590997, by rfl⟩ : syracuseStep 3454663 = 5181995) B5181995
theorem B1914731 : Blo 850355 1914731 := bstep (se 1 (by rfl) ⟨1436048, by rfl⟩ : syracuseStep 1914731 = 2872097) B2872097
theorem B1914785 : Blo 850355 1914785 := bstep (se 2 (by rfl) ⟨718044, by rfl⟩ : syracuseStep 1914785 = 1436089) B1436089
theorem B8763329 : Blo 850355 8763329 := bstep (se 2 (by rfl) ⟨3286248, by rfl⟩ : syracuseStep 8763329 = 6572497) B6572497
theorem B5453831 : Blo 850355 5453831 := bstep (se 1 (by rfl) ⟨4090373, by rfl⟩ : syracuseStep 5453831 = 8180747) B8180747
theorem B1619975 : Blo 850355 1619975 := bstep (se 1 (by rfl) ⟨1214981, by rfl⟩ : syracuseStep 1619975 = 2429963) B2429963
theorem B2734195 : Blo 850355 2734195 := bstep (se 1 (by rfl) ⟨2050646, by rfl⟩ : syracuseStep 2734195 = 4101293) B4101293
theorem B1915127 : Blo 850355 1915127 := bstep (se 1 (by rfl) ⟨1436345, by rfl⟩ : syracuseStep 1915127 = 2872691) B2872691
theorem B1554871 : Blo 850355 1554871 := bstep (se 1 (by rfl) ⟨1166153, by rfl⟩ : syracuseStep 1554871 = 2332307) B2332307
theorem B15350219 : Blo 850355 15350219 := bstep (se 1 (by rfl) ⟨11512664, by rfl⟩ : syracuseStep 15350219 = 23025329) B23025329
theorem B1554907 : Blo 850355 1554907 := bstep (se 1 (by rfl) ⟨1166180, by rfl⟩ : syracuseStep 1554907 = 2332361) B2332361
theorem B1620499 : Blo 850355 1620499 := bstep (se 1 (by rfl) ⟨1215374, by rfl⟩ : syracuseStep 1620499 = 2430749) B2430749
theorem B2734631 : Blo 850355 2734631 := bstep (se 1 (by rfl) ⟨2050973, by rfl⟩ : syracuseStep 2734631 = 4101947) B4101947
theorem B3324563 : Blo 850355 3324563 := bstep (se 1 (by rfl) ⟨2493422, by rfl⟩ : syracuseStep 3324563 = 4986845) B4986845
theorem B4307741 : Blo 850355 4307741 := bstep (se 3 (by rfl) ⟨807701, by rfl⟩ : syracuseStep 4307741 = 1615403) B1615403
theorem B1915721 : Blo 850355 1915721 := bstep (se 2 (by rfl) ⟨718395, by rfl⟩ : syracuseStep 1915721 = 1436791) B1436791
theorem B2046995 : Blo 850355 2046995 := bstep (se 1 (by rfl) ⟨1535246, by rfl⟩ : syracuseStep 2046995 = 3070493) B3070493
theorem B52575293 : Blo 850355 52575293 := bstep (se 3 (by rfl) ⟨9857867, by rfl⟩ : syracuseStep 52575293 = 19715735) B19715735
theorem B6143147 : Blo 850355 6143147 := bstep (se 1 (by rfl) ⟨4607360, by rfl⟩ : syracuseStep 6143147 = 9214721) B9214721
theorem B7781669 : Blo 850355 7781669 := bstep (se 4 (by rfl) ⟨729531, by rfl⟩ : syracuseStep 7781669 = 1459063) B1459063
theorem B13811239 : Blo 850355 13811239 := bstep (se 1 (by rfl) ⟨10358429, by rfl⟩ : syracuseStep 13811239 = 20716859) B20716859
theorem B1916513 : Blo 850355 1916513 := bstep (se 2 (by rfl) ⟨718692, by rfl⟩ : syracuseStep 1916513 = 1437385) B1437385
theorem B1818551 : Blo 850355 1818551 := bstep (se 1 (by rfl) ⟨1363913, by rfl⟩ : syracuseStep 1818551 = 2727827) B2727827
theorem B1916855 : Blo 850355 1916855 := bstep (se 1 (by rfl) ⟨1437641, by rfl⟩ : syracuseStep 1916855 = 2875283) B2875283
theorem B2736143 : Blo 850355 2736143 := bstep (se 1 (by rfl) ⟨2052107, by rfl⟩ : syracuseStep 2736143 = 4104215) B4104215
theorem B1687649 : Blo 850355 1687649 := bstep (se 2 (by rfl) ⟨632868, by rfl⟩ : syracuseStep 1687649 = 1265737) B1265737
theorem B8208701 : Blo 850355 8208701 := bstep (se 3 (by rfl) ⟨1539131, by rfl⟩ : syracuseStep 8208701 = 3078263) B3078263
theorem B3686743 : Blo 850355 3686743 := bstep (se 1 (by rfl) ⟨2765057, by rfl⟩ : syracuseStep 3686743 = 5530115) B5530115
theorem B1917449 : Blo 850355 1917449 := bstep (se 2 (by rfl) ⟨719043, by rfl⟩ : syracuseStep 1917449 = 1438087) B1438087
theorem B1917791 : Blo 850355 1917791 := bstep (se 1 (by rfl) ⟨1438343, by rfl⟩ : syracuseStep 1917791 = 2876687) B2876687
theorem B3884051 : Blo 850355 3884051 := bstep (se 1 (by rfl) ⟨2913038, by rfl⟩ : syracuseStep 3884051 = 5826077) B5826077
theorem B1917971 : Blo 850355 1917971 := bstep (se 1 (by rfl) ⟨1438478, by rfl⟩ : syracuseStep 1917971 = 2876957) B2876957
theorem B1918313 : Blo 850355 1918313 := bstep (se 2 (by rfl) ⟨719367, by rfl⟩ : syracuseStep 1918313 = 1438735) B1438735
theorem B8210119 : Blo 850355 8210119 := bstep (se 1 (by rfl) ⟨6157589, by rfl⟩ : syracuseStep 8210119 = 12315179) B12315179
theorem B1918907 : Blo 850355 1918907 := bstep (se 1 (by rfl) ⟨1439180, by rfl⟩ : syracuseStep 1918907 = 2878361) B2878361
theorem B1919033 : Blo 850355 1919033 := bstep (se 2 (by rfl) ⟨719637, by rfl⟩ : syracuseStep 1919033 = 1439275) B1439275
theorem B3065935 : Blo 850355 3065935 := bstep (se 1 (by rfl) ⟨2299451, by rfl⟩ : syracuseStep 3065935 = 4598903) B4598903
theorem B3230077 : Blo 850355 3230077 := bstep (se 3 (by rfl) ⟨605639, by rfl⟩ : syracuseStep 3230077 = 1211279) B1211279
theorem B1919375 : Blo 850355 1919375 := bstep (se 1 (by rfl) ⟨1439531, by rfl⟩ : syracuseStep 1919375 = 2879063) B2879063
theorem B1362395 : Blo 850355 1362395 := bstep (se 1 (by rfl) ⟨1021796, by rfl⟩ : syracuseStep 1362395 = 2043593) B2043593
theorem B1919699 : Blo 850355 1919699 := bstep (se 1 (by rfl) ⟨1439774, by rfl⟩ : syracuseStep 1919699 = 2879549) B2879549
theorem B2870045 : Blo 850355 2870045 := bstep (se 3 (by rfl) ⟨538133, by rfl⟩ : syracuseStep 2870045 = 1076267) B1076267
theorem B1821703 : Blo 850355 1821703 := bstep (se 1 (by rfl) ⟨1366277, by rfl⟩ : syracuseStep 1821703 = 2732555) B2732555
theorem B4312115 : Blo 850355 4312115 := bstep (se 1 (by rfl) ⟨3234086, by rfl⟩ : syracuseStep 4312115 = 6468173) B6468173
theorem B2182315 : Blo 850355 2182315 := bstep (se 1 (by rfl) ⟨1636736, by rfl⟩ : syracuseStep 2182315 = 3273473) B3273473
theorem B2870747 : Blo 850355 2870747 := bstep (se 1 (by rfl) ⟨2153060, by rfl⟩ : syracuseStep 2870747 = 4306121) B4306121
theorem B10374779 : Blo 850355 10374779 := bstep (se 1 (by rfl) ⟨7781084, by rfl⟩ : syracuseStep 10374779 = 15562169) B15562169
theorem B1920635 : Blo 850355 1920635 := bstep (se 1 (by rfl) ⟨1440476, by rfl⟩ : syracuseStep 1920635 = 2880953) B2880953
theorem B2051723 : Blo 850355 2051723 := bstep (se 1 (by rfl) ⟨1538792, by rfl⟩ : syracuseStep 2051723 = 3077585) B3077585
theorem B6475463 : Blo 850355 6475463 := bstep (se 1 (by rfl) ⟨4856597, by rfl⟩ : syracuseStep 6475463 = 9713195) B9713195
theorem B6901469 : Blo 850355 6901469 := bstep (se 3 (by rfl) ⟨1294025, by rfl⟩ : syracuseStep 6901469 = 2588051) B2588051
theorem B1920761 : Blo 850355 1920761 := bstep (se 2 (by rfl) ⟨720285, by rfl⟩ : syracuseStep 1920761 = 1440571) B1440571
theorem B1363817 : Blo 850355 1363817 := bstep (se 2 (by rfl) ⟨511431, by rfl⟩ : syracuseStep 1363817 = 1022863) B1022863
theorem B5459831 : Blo 850355 5459831 := bstep (se 1 (by rfl) ⟨4094873, by rfl⟩ : syracuseStep 5459831 = 8189747) B8189747
theorem B10899461 : Blo 850355 10899461 := bstep (se 4 (by rfl) ⟨1021824, by rfl⟩ : syracuseStep 10899461 = 2043649) B2043649
theorem B1921031 : Blo 850355 1921031 := bstep (se 1 (by rfl) ⟨1440773, by rfl⟩ : syracuseStep 1921031 = 2881547) B2881547
theorem B1921103 : Blo 850355 1921103 := bstep (se 1 (by rfl) ⟨1440827, by rfl⟩ : syracuseStep 1921103 = 2881655) B2881655
theorem B2871449 : Blo 850355 2871449 := bstep (se 2 (by rfl) ⟨1076793, by rfl⟩ : syracuseStep 2871449 = 2153587) B2153587
theorem B3788957 : Blo 850355 3788957 := bstep (se 3 (by rfl) ⟨710429, by rfl⟩ : syracuseStep 3788957 = 1420859) B1420859
theorem B3887261 : Blo 850355 3887261 := bstep (se 3 (by rfl) ⟨728861, by rfl⟩ : syracuseStep 3887261 = 1457723) B1457723
theorem B1921499 : Blo 850355 1921499 := bstep (se 1 (by rfl) ⟨1441124, by rfl⟩ : syracuseStep 1921499 = 2882249) B2882249
theorem B3232295 : Blo 850355 3232295 := bstep (se 1 (by rfl) ⟨2424221, by rfl⟩ : syracuseStep 3232295 = 4848443) B4848443
theorem B4313735 : Blo 850355 4313735 := bstep (se 1 (by rfl) ⟨3235301, by rfl⟩ : syracuseStep 4313735 = 6470603) B6470603
theorem B13095731 : Blo 850355 13095731 := bstep (se 1 (by rfl) ⟨9821798, by rfl⟩ : syracuseStep 13095731 = 19643597) B19643597
theorem B971615 : Blo 850355 971615 := bstep (se 1 (by rfl) ⟨728711, by rfl⟩ : syracuseStep 971615 = 1457423) B1457423
theorem B1921967 : Blo 850355 1921967 := bstep (se 1 (by rfl) ⟨1441475, by rfl⟩ : syracuseStep 1921967 = 2882951) B2882951
theorem B1922219 : Blo 850355 1922219 := bstep (se 1 (by rfl) ⟨1441664, by rfl⟩ : syracuseStep 1922219 = 2883329) B2883329
theorem B2872637 : Blo 850355 2872637 := bstep (se 3 (by rfl) ⟨538619, by rfl⟩ : syracuseStep 2872637 = 1077239) B1077239
theorem B3233267 : Blo 850355 3233267 := bstep (se 1 (by rfl) ⟨2424950, by rfl⟩ : syracuseStep 3233267 = 4849901) B4849901
theorem B7001747 : Blo 850355 7001747 := bstep (se 1 (by rfl) ⟨5251310, by rfl⟩ : syracuseStep 7001747 = 10502621) B10502621
theorem B3233465 : Blo 850355 3233465 := bstep (se 2 (by rfl) ⟨1212549, by rfl⟩ : syracuseStep 3233465 = 2425099) B2425099
theorem B3233479 : Blo 850355 3233479 := bstep (se 1 (by rfl) ⟨2425109, by rfl⟩ : syracuseStep 3233479 = 4850219) B4850219
theorem B12277817 : Blo 850355 12277817 := bstep (se 2 (by rfl) ⟨4604181, by rfl⟩ : syracuseStep 12277817 = 9208363) B9208363
theorem B4315193 : Blo 850355 4315193 := bstep (se 2 (by rfl) ⟨1618197, by rfl⟩ : syracuseStep 4315193 = 3236395) B3236395
theorem B13850681 : Blo 850355 13850681 := bstep (se 2 (by rfl) ⟨5194005, by rfl⟩ : syracuseStep 13850681 = 10388011) B10388011
theorem B5920883 : Blo 850355 5920883 := bstep (se 1 (by rfl) ⟨4440662, by rfl⟩ : syracuseStep 5920883 = 8881325) B8881325
theorem B2873501 : Blo 850355 2873501 := bstep (se 3 (by rfl) ⟨538781, by rfl⟩ : syracuseStep 2873501 = 1077563) B1077563
theorem B3234451 : Blo 850355 3234451 := bstep (se 1 (by rfl) ⟨2425838, by rfl⟩ : syracuseStep 3234451 = 4851677) B4851677
theorem B2874041 : Blo 850355 2874041 := bstep (se 2 (by rfl) ⟨1077765, by rfl⟩ : syracuseStep 2874041 = 2155531) B2155531
theorem B3464003 : Blo 850355 3464003 := bstep (se 1 (by rfl) ⟨2598002, by rfl⟩ : syracuseStep 3464003 = 5196005) B5196005
theorem B6151247 : Blo 850355 6151247 := bstep (se 1 (by rfl) ⟨4613435, by rfl⟩ : syracuseStep 6151247 = 9226871) B9226871
theorem B78830765 : Blo 850355 78830765 := bstep (se 3 (by rfl) ⟨14780768, by rfl⟩ : syracuseStep 78830765 = 29561537) B29561537
theorem B4611275 : Blo 850355 4611275 := bstep (se 1 (by rfl) ⟨3458456, by rfl⟩ : syracuseStep 4611275 = 6916913) B6916913
theorem B2874635 : Blo 850355 2874635 := bstep (se 1 (by rfl) ⟨2155976, by rfl⟩ : syracuseStep 2874635 = 4311953) B4311953
theorem B2874905 : Blo 850355 2874905 := bstep (se 2 (by rfl) ⟨1078089, by rfl⟩ : syracuseStep 2874905 = 2156179) B2156179
theorem B2154023 : Blo 850355 2154023 := bstep (se 1 (by rfl) ⟨1615517, by rfl⟩ : syracuseStep 2154023 = 3231035) B3231035
theorem B1367675 : Blo 850355 1367675 := bstep (se 1 (by rfl) ⟨1025756, by rfl⟩ : syracuseStep 1367675 = 2051513) B2051513
theorem B4087435 : Blo 850355 4087435 := bstep (se 1 (by rfl) ⟨3065576, by rfl⟩ : syracuseStep 4087435 = 6131153) B6131153
theorem B24534859 : Blo 850355 24534859 := bstep (se 1 (by rfl) ⟨18401144, by rfl⟩ : syracuseStep 24534859 = 36802289) B36802289
theorem B2154347 : Blo 850355 2154347 := bstep (se 1 (by rfl) ⟨1615760, by rfl⟩ : syracuseStep 2154347 = 3231521) B3231521
theorem B4317299 : Blo 850355 4317299 := bstep (se 1 (by rfl) ⟨3237974, by rfl⟩ : syracuseStep 4317299 = 6475949) B6475949
theorem B3236183 : Blo 850355 3236183 := bstep (se 1 (by rfl) ⟨2427137, by rfl⟩ : syracuseStep 3236183 = 4854275) B4854275
theorem B2154995 : Blo 850355 2154995 := bstep (se 1 (by rfl) ⟨1616246, by rfl⟩ : syracuseStep 2154995 = 3232493) B3232493
theorem B2876039 : Blo 850355 2876039 := bstep (se 1 (by rfl) ⟨2157029, by rfl⟩ : syracuseStep 2876039 = 4314059) B4314059
theorem B2876093 : Blo 850355 2876093 := bstep (se 3 (by rfl) ⟨539267, by rfl⟩ : syracuseStep 2876093 = 1078535) B1078535
theorem B2155207 : Blo 850355 2155207 := bstep (se 1 (by rfl) ⟨1616405, by rfl⟩ : syracuseStep 2155207 = 3232811) B3232811
theorem B2876255 : Blo 850355 2876255 := bstep (se 1 (by rfl) ⟨2157191, by rfl⟩ : syracuseStep 2876255 = 4314383) B4314383
theorem B2876417 : Blo 850355 2876417 := bstep (se 2 (by rfl) ⟨1078656, by rfl⟩ : syracuseStep 2876417 = 2157313) B2157313
theorem B6481295 : Blo 850355 6481295 := bstep (se 1 (by rfl) ⟨4860971, by rfl⟩ : syracuseStep 6481295 = 9721943) B9721943
theorem B12445093 : Blo 850355 12445093 := bstep (se 4 (by rfl) ⟨1166727, by rfl⟩ : syracuseStep 12445093 = 2333455) B2333455
theorem B7792037 : Blo 850355 7792037 := bstep (se 4 (by rfl) ⟨730503, by rfl⟩ : syracuseStep 7792037 = 1461007) B1461007
theorem B1435063 : Blo 850355 1435063 := bstep (se 1 (by rfl) ⟨1076297, by rfl⟩ : syracuseStep 1435063 = 2152595) B2152595
theorem B2156129 : Blo 850355 2156129 := bstep (se 2 (by rfl) ⟨808548, by rfl⟩ : syracuseStep 2156129 = 1617097) B1617097
theorem B1435259 : Blo 850355 1435259 := bstep (se 1 (by rfl) ⟨1076444, by rfl⟩ : syracuseStep 1435259 = 2152889) B2152889
theorem B4318919 : Blo 850355 4318919 := bstep (se 1 (by rfl) ⟨3239189, by rfl⟩ : syracuseStep 4318919 = 6478379) B6478379
theorem B2877227 : Blo 850355 2877227 := bstep (se 1 (by rfl) ⟨2157920, by rfl⟩ : syracuseStep 2877227 = 4315841) B4315841
theorem B1435657 : Blo 850355 1435657 := bstep (se 2 (by rfl) ⟨538371, by rfl⟩ : syracuseStep 1435657 = 1076743) B1076743
theorem B3106831 : Blo 850355 3106831 := bstep (se 1 (by rfl) ⟨2330123, by rfl⟩ : syracuseStep 3106831 = 4660247) B4660247
theorem B9201701 : Blo 850355 9201701 := bstep (se 4 (by rfl) ⟨862659, by rfl⟩ : syracuseStep 9201701 = 1725319) B1725319
theorem B2877497 : Blo 850355 2877497 := bstep (se 2 (by rfl) ⟨1079061, by rfl⟩ : syracuseStep 2877497 = 2158123) B2158123
theorem B1435819 : Blo 850355 1435819 := bstep (se 1 (by rfl) ⟨1076864, by rfl⟩ : syracuseStep 1435819 = 2153729) B2153729
theorem B2877821 : Blo 850355 2877821 := bstep (se 3 (by rfl) ⟨539591, by rfl⟩ : syracuseStep 2877821 = 1079183) B1079183
theorem B10938827 : Blo 850355 10938827 := bstep (se 1 (by rfl) ⟨8204120, by rfl⟩ : syracuseStep 10938827 = 16408241) B16408241
theorem B1436123 : Blo 850355 1436123 := bstep (se 1 (by rfl) ⟨1077092, by rfl⟩ : syracuseStep 1436123 = 2154185) B2154185
theorem B2878091 : Blo 850355 2878091 := bstep (se 1 (by rfl) ⟨2158568, by rfl⟩ : syracuseStep 2878091 = 4317137) B4317137
theorem B6154937 : Blo 850355 6154937 := bstep (se 2 (by rfl) ⟨2308101, by rfl⟩ : syracuseStep 6154937 = 4616203) B4616203
theorem B1436359 : Blo 850355 1436359 := bstep (se 1 (by rfl) ⟨1077269, by rfl⟩ : syracuseStep 1436359 = 2154539) B2154539
theorem B5466953 : Blo 850355 5466953 := bstep (se 2 (by rfl) ⟨2050107, by rfl⟩ : syracuseStep 5466953 = 4100215) B4100215
theorem B1436521 : Blo 850355 1436521 := bstep (se 2 (by rfl) ⟨538695, by rfl⟩ : syracuseStep 1436521 = 1077391) B1077391
theorem B1731547 : Blo 850355 1731547 := bstep (se 1 (by rfl) ⟨1298660, by rfl⟩ : syracuseStep 1731547 = 2597321) B2597321
theorem B2157587 : Blo 850355 2157587 := bstep (se 1 (by rfl) ⟨1618190, by rfl⟩ : syracuseStep 2157587 = 3236381) B3236381
theorem B3239297 : Blo 850355 3239297 := bstep (se 2 (by rfl) ⟨1214736, by rfl⟩ : syracuseStep 3239297 = 2429473) B2429473
theorem B3239311 : Blo 850355 3239311 := bstep (se 1 (by rfl) ⟨2429483, by rfl⟩ : syracuseStep 3239311 = 4858967) B4858967
theorem B1437115 : Blo 850355 1437115 := bstep (se 1 (by rfl) ⟨1077836, by rfl⟩ : syracuseStep 1437115 = 2155673) B2155673
theorem B2879009 : Blo 850355 2879009 := bstep (se 2 (by rfl) ⟨1079628, by rfl⟩ : syracuseStep 2879009 = 2159257) B2159257
theorem B4845095 : Blo 850355 4845095 := bstep (se 1 (by rfl) ⟨3633821, by rfl⟩ : syracuseStep 4845095 = 7267643) B7267643
theorem B1437223 : Blo 850355 1437223 := bstep (se 1 (by rfl) ⟨1077917, by rfl⟩ : syracuseStep 1437223 = 2155835) B2155835
theorem B6155837 : Blo 850355 6155837 := bstep (se 3 (by rfl) ⟨1154219, by rfl⟩ : syracuseStep 6155837 = 2308439) B2308439
theorem B2879225 : Blo 850355 2879225 := bstep (se 2 (by rfl) ⟨1079709, by rfl⟩ : syracuseStep 2879225 = 2159419) B2159419
theorem B10907459 : Blo 850355 10907459 := bstep (se 1 (by rfl) ⟨8180594, by rfl⟩ : syracuseStep 10907459 = 16361189) B16361189
theorem B1437547 : Blo 850355 1437547 := bstep (se 1 (by rfl) ⟨1078160, by rfl⟩ : syracuseStep 1437547 = 2156321) B2156321
theorem B1535851 : Blo 850355 1535851 := bstep (se 1 (by rfl) ⟨1151888, by rfl⟩ : syracuseStep 1535851 = 2303777) B2303777
theorem B3076001 : Blo 850355 3076001 := bstep (se 2 (by rfl) ⟨1153500, by rfl⟩ : syracuseStep 3076001 = 2307001) B2307001
theorem B12283811 : Blo 850355 12283811 := bstep (se 1 (by rfl) ⟨9212858, by rfl⟩ : syracuseStep 12283811 = 18425717) B18425717
theorem B2879495 : Blo 850355 2879495 := bstep (se 1 (by rfl) ⟨2159621, by rfl⟩ : syracuseStep 2879495 = 4319243) B4319243
theorem B2879603 : Blo 850355 2879603 := bstep (se 1 (by rfl) ⟨2159702, by rfl⟩ : syracuseStep 2879603 = 4319405) B4319405
theorem B2879873 : Blo 850355 2879873 := bstep (se 2 (by rfl) ⟨1079952, by rfl⟩ : syracuseStep 2879873 = 2159905) B2159905
theorem B4911641 : Blo 850355 4911641 := bstep (se 2 (by rfl) ⟨1841865, by rfl⟩ : syracuseStep 4911641 = 3683731) B3683731
theorem B3240587 : Blo 850355 3240587 := bstep (se 1 (by rfl) ⟨2430440, by rfl⟩ : syracuseStep 3240587 = 4860881) B4860881
theorem B1438607 : Blo 850355 1438607 := bstep (se 1 (by rfl) ⟨1078955, by rfl⟩ : syracuseStep 1438607 = 2157911) B2157911
theorem B13792301 : Blo 850355 13792301 := bstep (se 3 (by rfl) ⟨2586056, by rfl⟩ : syracuseStep 13792301 = 5172113) B5172113
theorem B1438843 : Blo 850355 1438843 := bstep (se 1 (by rfl) ⟨1079132, by rfl⟩ : syracuseStep 1438843 = 2158265) B2158265
theorem B2880683 : Blo 850355 2880683 := bstep (se 1 (by rfl) ⟨2160512, by rfl⟩ : syracuseStep 2880683 = 4321025) B4321025
theorem B3274273 : Blo 850355 3274273 := bstep (se 2 (by rfl) ⟨1227852, by rfl⟩ : syracuseStep 3274273 = 2455705) B2455705
theorem B4847303 : Blo 850355 4847303 := bstep (se 1 (by rfl) ⟨3635477, by rfl⟩ : syracuseStep 4847303 = 7270955) B7270955
theorem B2881223 : Blo 850355 2881223 := bstep (se 1 (by rfl) ⟨2160917, by rfl⟩ : syracuseStep 2881223 = 4321835) B4321835
theorem B1275641 : Blo 850355 1275641 := bstep (se 2 (by rfl) ⟨478365, by rfl⟩ : syracuseStep 1275641 = 956731) B956731
theorem B1275743 : Blo 850355 1275743 := bstep (se 1 (by rfl) ⟨956807, by rfl⟩ : syracuseStep 1275743 = 1913615) B1913615
theorem B1275755 : Blo 850355 1275755 := bstep (se 1 (by rfl) ⟨956816, by rfl⟩ : syracuseStep 1275755 = 1913633) B1913633
theorem B1439707 : Blo 850355 1439707 := bstep (se 1 (by rfl) ⟨1079780, by rfl⟩ : syracuseStep 1439707 = 2159561) B2159561
theorem B1079335 : Blo 850355 1079335 := bstep (se 1 (by rfl) ⟨809501, by rfl⟩ : syracuseStep 1079335 = 1619003) B1619003
theorem B1275983 : Blo 850355 1275983 := bstep (se 1 (by rfl) ⟨956987, by rfl⟩ : syracuseStep 1275983 = 1913975) B1913975
theorem B1276103 : Blo 850355 1276103 := bstep (se 1 (by rfl) ⟨957077, by rfl⟩ : syracuseStep 1276103 = 1914155) B1914155
theorem B3078391 : Blo 850355 3078391 := bstep (se 1 (by rfl) ⟨2308793, by rfl⟩ : syracuseStep 3078391 = 4617587) B4617587
theorem B4094219 : Blo 850355 4094219 := bstep (se 1 (by rfl) ⟨3070664, by rfl⟩ : syracuseStep 4094219 = 6141329) B6141329
theorem B1276265 : Blo 850355 1276265 := bstep (se 2 (by rfl) ⟨478599, by rfl⟩ : syracuseStep 1276265 = 957199) B957199
theorem B1079659 : Blo 850355 1079659 := bstep (se 1 (by rfl) ⟨809744, by rfl⟩ : syracuseStep 1079659 = 1619489) B1619489
theorem B15989123 : Blo 850355 15989123 := bstep (se 1 (by rfl) ⟨11991842, by rfl⟩ : syracuseStep 15989123 = 23983685) B23983685
theorem B2161039 : Blo 850355 2161039 := bstep (se 1 (by rfl) ⟨1620779, by rfl⟩ : syracuseStep 2161039 = 3241559) B3241559
theorem B1276343 : Blo 850355 1276343 := bstep (se 1 (by rfl) ⟨957257, by rfl⟩ : syracuseStep 1276343 = 1914515) B1914515
theorem B850375 : Blo 850355 850375 := bstep (se 1 (by rfl) ⟨637781, by rfl⟩ : syracuseStep 850375 = 1275563) B1275563
theorem B850395 : Blo 850355 850395 := bstep (se 1 (by rfl) ⟨637796, by rfl⟩ : syracuseStep 850395 = 1275593) B1275593
theorem B1276379 : Blo 850355 1276379 := bstep (se 1 (by rfl) ⟨957284, by rfl⟩ : syracuseStep 1276379 = 1914569) B1914569
theorem B850471 : Blo 850355 850471 := bstep (se 1 (by rfl) ⟨637853, by rfl⟩ : syracuseStep 850471 = 1275707) B1275707
theorem B2882087 : Blo 850355 2882087 := bstep (se 1 (by rfl) ⟨2161565, by rfl⟩ : syracuseStep 2882087 = 4323131) B4323131
theorem B850511 : Blo 850355 850511 := bstep (se 1 (by rfl) ⟨637883, by rfl⟩ : syracuseStep 850511 = 1275767) B1275767
theorem B1079887 : Blo 850355 1079887 := bstep (se 1 (by rfl) ⟨809915, by rfl⟩ : syracuseStep 1079887 = 1619831) B1619831
theorem B1440335 : Blo 850355 1440335 := bstep (se 1 (by rfl) ⟨1080251, by rfl⟩ : syracuseStep 1440335 = 2160503) B2160503
theorem B850527 : Blo 850355 850527 := bstep (se 1 (by rfl) ⟨637895, by rfl⟩ : syracuseStep 850527 = 1275791) B1275791
theorem B850555 : Blo 850355 850555 := bstep (se 1 (by rfl) ⟨637916, by rfl⟩ : syracuseStep 850555 = 1275833) B1275833
theorem B2882195 : Blo 850355 2882195 := bstep (se 1 (by rfl) ⟨2161646, by rfl⟩ : syracuseStep 2882195 = 4323293) B4323293
theorem B850607 : Blo 850355 850607 := bstep (se 1 (by rfl) ⟨637955, by rfl⟩ : syracuseStep 850607 = 1275911) B1275911
theorem B850631 : Blo 850355 850631 := bstep (se 1 (by rfl) ⟨637973, by rfl⟩ : syracuseStep 850631 = 1275947) B1275947
theorem B2161363 : Blo 850355 2161363 := bstep (se 1 (by rfl) ⟨1621022, by rfl⟩ : syracuseStep 2161363 = 3242045) B3242045
theorem B850651 : Blo 850355 850651 := bstep (se 1 (by rfl) ⟨637988, by rfl⟩ : syracuseStep 850651 = 1275977) B1275977
theorem B850727 : Blo 850355 850727 := bstep (se 1 (by rfl) ⟨638045, by rfl⟩ : syracuseStep 850727 = 1276091) B1276091
theorem B850767 : Blo 850355 850767 := bstep (se 1 (by rfl) ⟨638075, by rfl⟩ : syracuseStep 850767 = 1276151) B1276151
theorem B850783 : Blo 850355 850783 := bstep (se 1 (by rfl) ⟨638087, by rfl⟩ : syracuseStep 850783 = 1276175) B1276175
theorem B2882411 : Blo 850355 2882411 := bstep (se 1 (by rfl) ⟨2161808, by rfl⟩ : syracuseStep 2882411 = 4323617) B4323617
theorem B850811 : Blo 850355 850811 := bstep (se 1 (by rfl) ⟨638108, by rfl⟩ : syracuseStep 850811 = 1276217) B1276217
theorem B2882465 : Blo 850355 2882465 := bstep (se 2 (by rfl) ⟨1080924, by rfl⟩ : syracuseStep 2882465 = 2161849) B2161849
theorem B850863 : Blo 850355 850863 := bstep (se 1 (by rfl) ⟨638147, by rfl⟩ : syracuseStep 850863 = 1276295) B1276295
theorem B1276847 : Blo 850355 1276847 := bstep (se 1 (by rfl) ⟨957635, by rfl⟩ : syracuseStep 1276847 = 1915271) B1915271
theorem B850887 : Blo 850355 850887 := bstep (se 1 (by rfl) ⟨638165, by rfl⟩ : syracuseStep 850887 = 1276331) B1276331
theorem B850907 : Blo 850355 850907 := bstep (se 1 (by rfl) ⟨638180, by rfl⟩ : syracuseStep 850907 = 1276361) B1276361
theorem B1276937 : Blo 850355 1276937 := bstep (se 2 (by rfl) ⟨478851, by rfl⟩ : syracuseStep 1276937 = 957703) B957703
theorem B850983 : Blo 850355 850983 := bstep (se 1 (by rfl) ⟨638237, by rfl⟩ : syracuseStep 850983 = 1276475) B1276475
theorem B1276967 : Blo 850355 1276967 := bstep (se 1 (by rfl) ⟨957725, by rfl⟩ : syracuseStep 1276967 = 1915451) B1915451
theorem B851023 : Blo 850355 851023 := bstep (se 1 (by rfl) ⟨638267, by rfl⟩ : syracuseStep 851023 = 1276535) B1276535
theorem B851039 : Blo 850355 851039 := bstep (se 1 (by rfl) ⟨638279, by rfl⟩ : syracuseStep 851039 = 1276559) B1276559
theorem B851067 : Blo 850355 851067 := bstep (se 1 (by rfl) ⟨638300, by rfl⟩ : syracuseStep 851067 = 1276601) B1276601
theorem B1277051 : Blo 850355 1277051 := bstep (se 1 (by rfl) ⟨957788, by rfl⟩ : syracuseStep 1277051 = 1915577) B1915577
theorem B851119 : Blo 850355 851119 := bstep (se 1 (by rfl) ⟨638339, by rfl⟩ : syracuseStep 851119 = 1276679) B1276679
theorem B851143 : Blo 850355 851143 := bstep (se 1 (by rfl) ⟨638357, by rfl⟩ : syracuseStep 851143 = 1276715) B1276715
theorem B851163 : Blo 850355 851163 := bstep (se 1 (by rfl) ⟨638372, by rfl⟩ : syracuseStep 851163 = 1276745) B1276745
theorem B1277177 : Blo 850355 1277177 := bstep (se 2 (by rfl) ⟨478941, by rfl⟩ : syracuseStep 1277177 = 957883) B957883
theorem B851239 : Blo 850355 851239 := bstep (se 1 (by rfl) ⟨638429, by rfl⟩ : syracuseStep 851239 = 1276859) B1276859
theorem B851279 : Blo 850355 851279 := bstep (se 1 (by rfl) ⟨638459, by rfl⟩ : syracuseStep 851279 = 1276919) B1276919
theorem B851295 : Blo 850355 851295 := bstep (se 1 (by rfl) ⟨638471, by rfl⟩ : syracuseStep 851295 = 1276943) B1276943
theorem B1277279 : Blo 850355 1277279 := bstep (se 1 (by rfl) ⟨957959, by rfl⟩ : syracuseStep 1277279 = 1915919) B1915919
theorem B1277291 : Blo 850355 1277291 := bstep (se 1 (by rfl) ⟨957968, by rfl⟩ : syracuseStep 1277291 = 1915937) B1915937
theorem B851323 : Blo 850355 851323 := bstep (se 1 (by rfl) ⟨638492, by rfl⟩ : syracuseStep 851323 = 1276985) B1276985
theorem B4324751 : Blo 850355 4324751 := bstep (se 1 (by rfl) ⟨3243563, by rfl⟩ : syracuseStep 4324751 = 6487127) B6487127
theorem B851375 : Blo 850355 851375 := bstep (se 1 (by rfl) ⟨638531, by rfl⟩ : syracuseStep 851375 = 1277063) B1277063
theorem B1441199 : Blo 850355 1441199 := bstep (se 1 (by rfl) ⟨1080899, by rfl⟩ : syracuseStep 1441199 = 2161799) B2161799
theorem B851399 : Blo 850355 851399 := bstep (se 1 (by rfl) ⟨638549, by rfl⟩ : syracuseStep 851399 = 1277099) B1277099
theorem B851419 : Blo 850355 851419 := bstep (se 1 (by rfl) ⟨638564, by rfl⟩ : syracuseStep 851419 = 1277129) B1277129
theorem B2883059 : Blo 850355 2883059 := bstep (se 1 (by rfl) ⟨2162294, by rfl⟩ : syracuseStep 2883059 = 4324589) B4324589
theorem B851495 : Blo 850355 851495 := bstep (se 1 (by rfl) ⟨638621, by rfl⟩ : syracuseStep 851495 = 1277243) B1277243
theorem B6487613 : Blo 850355 6487613 := bstep (se 3 (by rfl) ⟨1216427, by rfl⟩ : syracuseStep 6487613 = 2432855) B2432855
theorem B851535 : Blo 850355 851535 := bstep (se 1 (by rfl) ⟨638651, by rfl⟩ : syracuseStep 851535 = 1277303) B1277303
theorem B1277519 : Blo 850355 1277519 := bstep (se 1 (by rfl) ⟨958139, by rfl⟩ : syracuseStep 1277519 = 1916279) B1916279
theorem B851551 : Blo 850355 851551 := bstep (se 1 (by rfl) ⟨638663, by rfl⟩ : syracuseStep 851551 = 1277327) B1277327
theorem B851579 : Blo 850355 851579 := bstep (se 1 (by rfl) ⟨638684, by rfl⟩ : syracuseStep 851579 = 1277369) B1277369
theorem B1080955 : Blo 850355 1080955 := bstep (se 1 (by rfl) ⟨810716, by rfl⟩ : syracuseStep 1080955 = 1621433) B1621433
theorem B20741771 : Blo 850355 20741771 := bstep (se 1 (by rfl) ⟨15556328, by rfl⟩ : syracuseStep 20741771 = 31112657) B31112657
theorem B2162315 : Blo 850355 2162315 := bstep (se 1 (by rfl) ⟨1621736, by rfl⟩ : syracuseStep 2162315 = 3243473) B3243473
theorem B851631 : Blo 850355 851631 := bstep (se 1 (by rfl) ⟨638723, by rfl⟩ : syracuseStep 851631 = 1277447) B1277447
theorem B851655 : Blo 850355 851655 := bstep (se 1 (by rfl) ⟨638741, by rfl⟩ : syracuseStep 851655 = 1277483) B1277483
theorem B1277639 : Blo 850355 1277639 := bstep (se 1 (by rfl) ⟨958229, by rfl⟩ : syracuseStep 1277639 = 1916459) B1916459
theorem B851675 : Blo 850355 851675 := bstep (se 1 (by rfl) ⟨638756, by rfl⟩ : syracuseStep 851675 = 1277513) B1277513
theorem B851751 : Blo 850355 851751 := bstep (se 1 (by rfl) ⟨638813, by rfl⟩ : syracuseStep 851751 = 1277627) B1277627
theorem B851791 : Blo 850355 851791 := bstep (se 1 (by rfl) ⟨638843, by rfl⟩ : syracuseStep 851791 = 1277687) B1277687
theorem B851807 : Blo 850355 851807 := bstep (se 1 (by rfl) ⟨638855, by rfl⟩ : syracuseStep 851807 = 1277711) B1277711
theorem B1081183 : Blo 850355 1081183 := bstep (se 1 (by rfl) ⟨810887, by rfl⟩ : syracuseStep 1081183 = 1621775) B1621775
theorem B1441631 : Blo 850355 1441631 := bstep (se 1 (by rfl) ⟨1081223, by rfl⟩ : syracuseStep 1441631 = 2162447) B2162447
theorem B1277801 : Blo 850355 1277801 := bstep (se 2 (by rfl) ⟨479175, by rfl⟩ : syracuseStep 1277801 = 958351) B958351
theorem B851835 : Blo 850355 851835 := bstep (se 1 (by rfl) ⟨638876, by rfl⟩ : syracuseStep 851835 = 1277753) B1277753
theorem B851887 : Blo 850355 851887 := bstep (se 1 (by rfl) ⟨638915, by rfl⟩ : syracuseStep 851887 = 1277831) B1277831
theorem B1277879 : Blo 850355 1277879 := bstep (se 1 (by rfl) ⟨958409, by rfl⟩ : syracuseStep 1277879 = 1916819) B1916819
theorem B5832641 : Blo 850355 5832641 := bstep (se 2 (by rfl) ⟨2187240, by rfl⟩ : syracuseStep 5832641 = 4374481) B4374481
theorem B851911 : Blo 850355 851911 := bstep (se 1 (by rfl) ⟨638933, by rfl⟩ : syracuseStep 851911 = 1277867) B1277867
theorem B851931 : Blo 850355 851931 := bstep (se 1 (by rfl) ⟨638948, by rfl⟩ : syracuseStep 851931 = 1277897) B1277897
theorem B1277915 : Blo 850355 1277915 := bstep (se 1 (by rfl) ⟨958436, by rfl⟩ : syracuseStep 1277915 = 1916873) B1916873
theorem B5472467 : Blo 850355 5472467 := bstep (se 1 (by rfl) ⟨4104350, by rfl⟩ : syracuseStep 5472467 = 8208701) B8208701
theorem B852255 : Blo 850355 852255 := bstep (se 1 (by rfl) ⟨639191, by rfl⟩ : syracuseStep 852255 = 1278383) B1278383
theorem B1278299 : Blo 850355 1278299 := bstep (se 1 (by rfl) ⟨958724, by rfl⟩ : syracuseStep 1278299 = 1917449) B1917449
theorem B852315 : Blo 850355 852315 := bstep (se 1 (by rfl) ⟨639236, by rfl⟩ : syracuseStep 852315 = 1278473) B1278473
theorem B852335 : Blo 850355 852335 := bstep (se 1 (by rfl) ⟨639251, by rfl⟩ : syracuseStep 852335 = 1278503) B1278503
theorem B852391 : Blo 850355 852391 := bstep (se 1 (by rfl) ⟨639293, by rfl⟩ : syracuseStep 852391 = 1278587) B1278587
theorem B4915657 : Blo 850355 4915657 := bstep (se 2 (by rfl) ⟨1843371, by rfl⟩ : syracuseStep 4915657 = 3686743) B3686743
theorem B852475 : Blo 850355 852475 := bstep (se 1 (by rfl) ⟨639356, by rfl⟩ : syracuseStep 852475 = 1278713) B1278713
theorem B1278527 : Blo 850355 1278527 := bstep (se 1 (by rfl) ⟨958895, by rfl⟩ : syracuseStep 1278527 = 1917791) B1917791
theorem B852543 : Blo 850355 852543 := bstep (se 1 (by rfl) ⟨639407, by rfl⟩ : syracuseStep 852543 = 1278815) B1278815
theorem B1638983 : Blo 850355 1638983 := bstep (se 1 (by rfl) ⟨1229237, by rfl⟩ : syracuseStep 1638983 = 2458475) B2458475
theorem B852551 : Blo 850355 852551 := bstep (se 1 (by rfl) ⟨639413, by rfl⟩ : syracuseStep 852551 = 1278827) B1278827
theorem B2589367 : Blo 850355 2589367 := bstep (se 1 (by rfl) ⟨1942025, by rfl⟩ : syracuseStep 2589367 = 3884051) B3884051
theorem B1278647 : Blo 850355 1278647 := bstep (se 1 (by rfl) ⟨958985, by rfl⟩ : syracuseStep 1278647 = 1917971) B1917971
theorem B852703 : Blo 850355 852703 := bstep (se 1 (by rfl) ⟨639527, by rfl⟩ : syracuseStep 852703 = 1279055) B1279055
theorem B852783 : Blo 850355 852783 := bstep (se 1 (by rfl) ⟨639587, by rfl⟩ : syracuseStep 852783 = 1279175) B1279175
theorem B1278875 : Blo 850355 1278875 := bstep (se 1 (by rfl) ⟨959156, by rfl⟩ : syracuseStep 1278875 = 1918313) B1918313
theorem B852891 : Blo 850355 852891 := bstep (se 1 (by rfl) ⟨639668, by rfl⟩ : syracuseStep 852891 = 1279337) B1279337
theorem B852943 : Blo 850355 852943 := bstep (se 1 (by rfl) ⟨639707, by rfl⟩ : syracuseStep 852943 = 1279415) B1279415
theorem B852967 : Blo 850355 852967 := bstep (se 1 (by rfl) ⟨639725, by rfl⟩ : syracuseStep 852967 = 1279451) B1279451
theorem B3114233 : Blo 850355 3114233 := bstep (se 2 (by rfl) ⟨1167837, by rfl⟩ : syracuseStep 3114233 = 2335675) B2335675
theorem B853279 : Blo 850355 853279 := bstep (se 1 (by rfl) ⟨639959, by rfl⟩ : syracuseStep 853279 = 1279919) B1279919
theorem B1279271 : Blo 850355 1279271 := bstep (se 1 (by rfl) ⟨959453, by rfl⟩ : syracuseStep 1279271 = 1918907) B1918907
theorem B853339 : Blo 850355 853339 := bstep (se 1 (by rfl) ⟨640004, by rfl⟩ : syracuseStep 853339 = 1280009) B1280009
theorem B853359 : Blo 850355 853359 := bstep (se 1 (by rfl) ⟨640019, by rfl⟩ : syracuseStep 853359 = 1280039) B1280039
theorem B1279355 : Blo 850355 1279355 := bstep (se 1 (by rfl) ⟨959516, by rfl⟩ : syracuseStep 1279355 = 1919033) B1919033
theorem B853415 : Blo 850355 853415 := bstep (se 1 (by rfl) ⟨640061, by rfl⟩ : syracuseStep 853415 = 1280123) B1280123
theorem B1279481 : Blo 850355 1279481 := bstep (se 2 (by rfl) ⟨479805, by rfl⟩ : syracuseStep 1279481 = 959611) B959611
theorem B853499 : Blo 850355 853499 := bstep (se 1 (by rfl) ⟨640124, by rfl⟩ : syracuseStep 853499 = 1280249) B1280249
theorem B2426375 : Blo 850355 2426375 := bstep (se 1 (by rfl) ⟨1819781, by rfl⟩ : syracuseStep 2426375 = 3639563) B3639563
theorem B853567 : Blo 850355 853567 := bstep (se 1 (by rfl) ⟨640175, by rfl⟩ : syracuseStep 853567 = 1280351) B1280351
theorem B853575 : Blo 850355 853575 := bstep (se 1 (by rfl) ⟨640181, by rfl⟩ : syracuseStep 853575 = 1280363) B1280363
theorem B1279583 : Blo 850355 1279583 := bstep (se 1 (by rfl) ⟨959687, by rfl⟩ : syracuseStep 1279583 = 1919375) B1919375
theorem B853727 : Blo 850355 853727 := bstep (se 1 (by rfl) ⟨640295, by rfl⟩ : syracuseStep 853727 = 1280591) B1280591
theorem B853807 : Blo 850355 853807 := bstep (se 1 (by rfl) ⟨640355, by rfl⟩ : syracuseStep 853807 = 1280711) B1280711
theorem B1279799 : Blo 850355 1279799 := bstep (se 1 (by rfl) ⟨959849, by rfl⟩ : syracuseStep 1279799 = 1919699) B1919699
theorem B853915 : Blo 850355 853915 := bstep (se 1 (by rfl) ⟨640436, by rfl⟩ : syracuseStep 853915 = 1280873) B1280873
theorem B2426831 : Blo 850355 2426831 := bstep (se 1 (by rfl) ⟨1820123, by rfl⟩ : syracuseStep 2426831 = 3640247) B3640247
theorem B853967 : Blo 850355 853967 := bstep (se 1 (by rfl) ⟨640475, by rfl⟩ : syracuseStep 853967 = 1280951) B1280951
theorem B853991 : Blo 850355 853991 := bstep (se 1 (by rfl) ⟨640493, by rfl⟩ : syracuseStep 853991 = 1280987) B1280987
theorem B1280105 : Blo 850355 1280105 := bstep (se 2 (by rfl) ⟨480039, by rfl⟩ : syracuseStep 1280105 = 960079) B960079
theorem B17533057 : Blo 850355 17533057 := bstep (se 2 (by rfl) ⟨6574896, by rfl⟩ : syracuseStep 17533057 = 13149793) B13149793
theorem B18450625 : Blo 850355 18450625 := bstep (se 2 (by rfl) ⟨6918984, by rfl⟩ : syracuseStep 18450625 = 13837969) B13837969
theorem B2590973 : Blo 850355 2590973 := bstep (se 3 (by rfl) ⟨485807, by rfl⟩ : syracuseStep 2590973 = 971615) B971615
theorem B10946825 : Blo 850355 10946825 := bstep (se 2 (by rfl) ⟨4105059, by rfl⟩ : syracuseStep 10946825 = 8210119) B8210119
theorem B854303 : Blo 850355 854303 := bstep (se 1 (by rfl) ⟨640727, by rfl⟩ : syracuseStep 854303 = 1281455) B1281455
theorem B6916519 : Blo 850355 6916519 := bstep (se 1 (by rfl) ⟨5187389, by rfl⟩ : syracuseStep 6916519 = 10374779) B10374779
theorem B1280423 : Blo 850355 1280423 := bstep (se 1 (by rfl) ⟨960317, by rfl⟩ : syracuseStep 1280423 = 1920635) B1920635
theorem B1280507 : Blo 850355 1280507 := bstep (se 1 (by rfl) ⟨960380, by rfl⟩ : syracuseStep 1280507 = 1920761) B1920761
theorem B3639887 : Blo 850355 3639887 := bstep (se 1 (by rfl) ⟨2729915, by rfl⟩ : syracuseStep 3639887 = 5459831) B5459831
theorem B1280633 : Blo 850355 1280633 := bstep (se 2 (by rfl) ⟨480237, by rfl⟩ : syracuseStep 1280633 = 960475) B960475
theorem B1280687 : Blo 850355 1280687 := bstep (se 1 (by rfl) ⟨960515, by rfl⟩ : syracuseStep 1280687 = 1921031) B1921031
theorem B1280735 : Blo 850355 1280735 := bstep (se 1 (by rfl) ⟨960551, by rfl⟩ : syracuseStep 1280735 = 1921103) B1921103
theorem B2525971 : Blo 850355 2525971 := bstep (se 1 (by rfl) ⟨1894478, by rfl⟩ : syracuseStep 2525971 = 3788957) B3788957
theorem B2591507 : Blo 850355 2591507 := bstep (se 1 (by rfl) ⟨1943630, by rfl⟩ : syracuseStep 2591507 = 3887261) B3887261
theorem B1280999 : Blo 850355 1280999 := bstep (se 1 (by rfl) ⟨960749, by rfl⟩ : syracuseStep 1280999 = 1921499) B1921499
theorem B4852817 : Blo 850355 4852817 := bstep (se 2 (by rfl) ⟨1819806, by rfl⟩ : syracuseStep 4852817 = 3639613) B3639613
theorem B1281257 : Blo 850355 1281257 := bstep (se 2 (by rfl) ⟨480471, by rfl⟩ : syracuseStep 1281257 = 960943) B960943
theorem B1281311 : Blo 850355 1281311 := bstep (se 1 (by rfl) ⟨960983, by rfl⟩ : syracuseStep 1281311 = 1921967) B1921967
theorem B1281479 : Blo 850355 1281479 := bstep (se 1 (by rfl) ⟨961109, by rfl⟩ : syracuseStep 1281479 = 1922219) B1922219
theorem B2428937 : Blo 850355 2428937 := bstep (se 2 (by rfl) ⟨910851, by rfl⟩ : syracuseStep 2428937 = 1821703) B1821703
theorem B2429291 : Blo 850355 2429291 := bstep (se 1 (by rfl) ⟨1821968, by rfl⟩ : syracuseStep 2429291 = 3643937) B3643937
theorem B4100831 : Blo 850355 4100831 := bstep (se 1 (by rfl) ⟨3075623, by rfl⟩ : syracuseStep 4100831 = 6151247) B6151247
theorem B4854775 : Blo 850355 4854775 := bstep (se 1 (by rfl) ⟨3641081, by rfl⟩ : syracuseStep 4854775 = 7282163) B7282163
theorem B6132793 : Blo 850355 6132793 := bstep (se 2 (by rfl) ⟨2299797, by rfl⟩ : syracuseStep 6132793 = 4599595) B4599595
theorem B36935149 : Blo 850355 36935149 := bstep (se 3 (by rfl) ⟨6925340, by rfl⟩ : syracuseStep 36935149 = 13850681) B13850681
theorem B8198279 : Blo 850355 8198279 := bstep (se 1 (by rfl) ⟨6148709, by rfl⟩ : syracuseStep 8198279 = 12297419) B12297419
theorem B42637661 : Blo 850355 42637661 := bstep (se 3 (by rfl) ⟨7994561, by rfl⟩ : syracuseStep 42637661 = 15989123) B15989123
theorem B956839 : Blo 850355 956839 := bstep (se 1 (by rfl) ⟨717629, by rfl⟩ : syracuseStep 956839 = 1435259) B1435259
theorem B2300599 : Blo 850355 2300599 := bstep (se 1 (by rfl) ⟨1725449, by rfl⟩ : syracuseStep 2300599 = 3450899) B3450899
theorem B6134467 : Blo 850355 6134467 := bstep (se 1 (by rfl) ⟨4600850, by rfl⟩ : syracuseStep 6134467 = 9201701) B9201701
theorem B2300663 : Blo 850355 2300663 := bstep (se 1 (by rfl) ⟨1725497, by rfl⟩ : syracuseStep 2300663 = 3450995) B3450995
theorem B2300827 : Blo 850355 2300827 := bstep (se 1 (by rfl) ⟨1725620, by rfl⟩ : syracuseStep 2300827 = 3451241) B3451241
theorem B957415 : Blo 850355 957415 := bstep (se 1 (by rfl) ⟨718061, by rfl⟩ : syracuseStep 957415 = 1436123) B1436123
theorem B4922491 : Blo 850355 4922491 := bstep (se 1 (by rfl) ⟨3691868, by rfl⟩ : syracuseStep 4922491 = 7383737) B7383737
theorem B4103291 : Blo 850355 4103291 := bstep (se 1 (by rfl) ⟨3077468, by rfl⟩ : syracuseStep 4103291 = 6154937) B6154937
theorem B4365697 : Blo 850355 4365697 := bstep (se 2 (by rfl) ⟨1637136, by rfl⟩ : syracuseStep 4365697 = 3274273) B3274273
theorem B4103891 : Blo 850355 4103891 := bstep (se 1 (by rfl) ⟨3077918, by rfl⟩ : syracuseStep 4103891 = 6155837) B6155837
theorem B3645593 : Blo 850355 3645593 := bstep (se 2 (by rfl) ⟨1367097, by rfl⟩ : syracuseStep 3645593 = 2734195) B2734195
theorem B4104521 : Blo 850355 4104521 := bstep (se 2 (by rfl) ⟨1539195, by rfl⟩ : syracuseStep 4104521 = 3078391) B3078391
theorem B2073161 : Blo 850355 2073161 := bstep (se 2 (by rfl) ⟨777435, by rfl⟩ : syracuseStep 2073161 = 1554871) B1554871
theorem B959071 : Blo 850355 959071 := bstep (se 1 (by rfl) ⟨719303, by rfl⟩ : syracuseStep 959071 = 1438607) B1438607
theorem B2073209 : Blo 850355 2073209 := bstep (se 2 (by rfl) ⟨777453, by rfl⟩ : syracuseStep 2073209 = 1554907) B1554907
theorem B2302739 : Blo 850355 2302739 := bstep (se 1 (by rfl) ⟨1727054, by rfl⟩ : syracuseStep 2302739 = 3454109) B3454109
theorem B8856515 : Blo 850355 8856515 := bstep (se 1 (by rfl) ⟨6642386, by rfl⟩ : syracuseStep 8856515 = 13284773) B13284773
theorem B5448707 : Blo 850355 5448707 := bstep (se 1 (by rfl) ⟨4086530, by rfl⟩ : syracuseStep 5448707 = 8173061) B8173061
theorem B1844473 : Blo 850355 1844473 := bstep (se 2 (by rfl) ⟨691677, by rfl⟩ : syracuseStep 1844473 = 1383355) B1383355
theorem B5842219 : Blo 850355 5842219 := bstep (se 1 (by rfl) ⟨4381664, by rfl⟩ : syracuseStep 5842219 = 8763329) B8763329
theorem B7284077 : Blo 850355 7284077 := bstep (se 3 (by rfl) ⟨1365764, by rfl⟩ : syracuseStep 7284077 = 2731529) B2731529
theorem B2729479 : Blo 850355 2729479 := bstep (se 1 (by rfl) ⟨2047109, by rfl⟩ : syracuseStep 2729479 = 4094219) B4094219
theorem B10233479 : Blo 850355 10233479 := bstep (se 1 (by rfl) ⟨7675109, by rfl⟩ : syracuseStep 10233479 = 15350219) B15350219
theorem B960223 : Blo 850355 960223 := bstep (se 1 (by rfl) ⟨720167, by rfl⟩ : syracuseStep 960223 = 1440335) B1440335
theorem B5449913 : Blo 850355 5449913 := bstep (se 2 (by rfl) ⟨2043717, by rfl⟩ : syracuseStep 5449913 = 4087435) B4087435
theorem B5187779 : Blo 850355 5187779 := bstep (se 1 (by rfl) ⟨3890834, by rfl⟩ : syracuseStep 5187779 = 7781669) B7781669
theorem B960799 : Blo 850355 960799 := bstep (se 1 (by rfl) ⟨720599, by rfl⟩ : syracuseStep 960799 = 1441199) B1441199
theorem B32713145 : Blo 850355 32713145 := bstep (se 2 (by rfl) ⟨12267429, by rfl⟩ : syracuseStep 32713145 = 24534859) B24534859
theorem B961087 : Blo 850355 961087 := bstep (se 1 (by rfl) ⟨720815, by rfl⟩ : syracuseStep 961087 = 1441631) B1441631
theorem B4500397 : Blo 850355 4500397 := bstep (se 3 (by rfl) ⟨843824, by rfl⟩ : syracuseStep 4500397 = 1687649) B1687649
theorem B3648635 : Blo 850355 3648635 := bstep (se 1 (by rfl) ⟨2736476, by rfl⟩ : syracuseStep 3648635 = 5472953) B5472953
theorem B44969093 : Blo 850355 44969093 := bstep (se 4 (by rfl) ⟨4215852, by rfl⟩ : syracuseStep 44969093 = 8431705) B8431705
theorem B1617401 : Blo 850355 1617401 := bstep (se 2 (by rfl) ⟨606525, by rfl⟩ : syracuseStep 1617401 = 1213051) B1213051
theorem B17740241 : Blo 850355 17740241 := bstep (se 2 (by rfl) ⟨6652590, by rfl⟩ : syracuseStep 17740241 = 13305181) B13305181
theorem B1913363 : Blo 850355 1913363 := bstep (se 1 (by rfl) ⟨1435022, by rfl⟩ : syracuseStep 1913363 = 2870045) B2870045
theorem B16593457 : Blo 850355 16593457 := bstep (se 2 (by rfl) ⟨6222546, by rfl⟩ : syracuseStep 16593457 = 12445093) B12445093
theorem B1913417 : Blo 850355 1913417 := bstep (se 2 (by rfl) ⟨717531, by rfl⟩ : syracuseStep 1913417 = 1435063) B1435063
theorem B1618859 : Blo 850355 1618859 := bstep (se 1 (by rfl) ⟨1214144, by rfl⟩ : syracuseStep 1618859 = 2428289) B2428289
theorem B1913831 : Blo 850355 1913831 := bstep (se 1 (by rfl) ⟨1435373, by rfl⟩ : syracuseStep 1913831 = 2870747) B2870747
theorem B4600979 : Blo 850355 4600979 := bstep (se 1 (by rfl) ⟨3450734, by rfl⟩ : syracuseStep 4600979 = 6901469) B6901469
theorem B1914209 : Blo 850355 1914209 := bstep (se 2 (by rfl) ⟨717828, by rfl⟩ : syracuseStep 1914209 = 1435657) B1435657
theorem B4142441 : Blo 850355 4142441 := bstep (se 2 (by rfl) ⟨1553415, by rfl⟩ : syracuseStep 4142441 = 3106831) B3106831
theorem B1914299 : Blo 850355 1914299 := bstep (se 1 (by rfl) ⟨1435724, by rfl⟩ : syracuseStep 1914299 = 2871449) B2871449
theorem B1914425 : Blo 850355 1914425 := bstep (se 2 (by rfl) ⟨717909, by rfl⟩ : syracuseStep 1914425 = 1435819) B1435819
theorem B4306769 : Blo 850355 4306769 := bstep (se 2 (by rfl) ⟨1615038, by rfl⟩ : syracuseStep 4306769 = 3230077) B3230077
theorem B8730487 : Blo 850355 8730487 := bstep (se 1 (by rfl) ⟨6547865, by rfl⟩ : syracuseStep 8730487 = 13095731) B13095731
theorem B1915091 : Blo 850355 1915091 := bstep (se 1 (by rfl) ⟨1436318, by rfl⟩ : syracuseStep 1915091 = 2872637) B2872637
theorem B1915145 : Blo 850355 1915145 := bstep (se 2 (by rfl) ⟨718179, by rfl⟩ : syracuseStep 1915145 = 1436359) B1436359
theorem B1620233 : Blo 850355 1620233 := bstep (se 2 (by rfl) ⟨607587, by rfl⟩ : syracuseStep 1620233 = 1215175) B1215175
theorem B13285757 : Blo 850355 13285757 := bstep (se 3 (by rfl) ⟨2491079, by rfl⟩ : syracuseStep 13285757 = 4982159) B4982159
theorem B4667831 : Blo 850355 4667831 := bstep (se 1 (by rfl) ⟨3500873, by rfl⟩ : syracuseStep 4667831 = 7001747) B7001747
theorem B1915361 : Blo 850355 1915361 := bstep (se 2 (by rfl) ⟨718260, by rfl⟩ : syracuseStep 1915361 = 1436521) B1436521
theorem B4307579 : Blo 850355 4307579 := bstep (se 1 (by rfl) ⟨3230684, by rfl⟩ : syracuseStep 4307579 = 6461369) B6461369
theorem B35011273 : Blo 850355 35011273 := bstep (se 2 (by rfl) ⟨13129227, by rfl⟩ : syracuseStep 35011273 = 26258455) B26258455
theorem B3947255 : Blo 850355 3947255 := bstep (se 1 (by rfl) ⟨2960441, by rfl⟩ : syracuseStep 3947255 = 5920883) B5920883
theorem B1817363 : Blo 850355 1817363 := bstep (se 1 (by rfl) ⟨1363022, by rfl⟩ : syracuseStep 1817363 = 2726045) B2726045
theorem B1915667 : Blo 850355 1915667 := bstep (se 1 (by rfl) ⟨1436750, by rfl⟩ : syracuseStep 1915667 = 2873501) B2873501
theorem B1916027 : Blo 850355 1916027 := bstep (se 1 (by rfl) ⟨1437020, by rfl⟩ : syracuseStep 1916027 = 2874041) B2874041
theorem B1916153 : Blo 850355 1916153 := bstep (se 2 (by rfl) ⟨718557, by rfl⟩ : syracuseStep 1916153 = 1437115) B1437115
theorem B1916297 : Blo 850355 1916297 := bstep (se 2 (by rfl) ⟨718611, by rfl⟩ : syracuseStep 1916297 = 1437223) B1437223
theorem B3456443 : Blo 850355 3456443 := bstep (se 1 (by rfl) ⟨2592332, by rfl⟩ : syracuseStep 3456443 = 5184665) B5184665
theorem B1916423 : Blo 850355 1916423 := bstep (se 1 (by rfl) ⟨1437317, by rfl⟩ : syracuseStep 1916423 = 2874635) B2874635
theorem B1916603 : Blo 850355 1916603 := bstep (se 1 (by rfl) ⟨1437452, by rfl⟩ : syracuseStep 1916603 = 2874905) B2874905
theorem B1621691 : Blo 850355 1621691 := bstep (se 1 (by rfl) ⟨1216268, by rfl⟩ : syracuseStep 1621691 = 2432537) B2432537
theorem B1916729 : Blo 850355 1916729 := bstep (se 2 (by rfl) ⟨718773, by rfl⟩ : syracuseStep 1916729 = 1437547) B1437547
theorem B15515459 : Blo 850355 15515459 := bstep (se 1 (by rfl) ⟨11636594, by rfl⟩ : syracuseStep 15515459 = 23273189) B23273189
theorem B42647651 : Blo 850355 42647651 := bstep (se 1 (by rfl) ⟨31985738, by rfl⟩ : syracuseStep 42647651 = 63971477) B63971477
theorem B1917359 : Blo 850355 1917359 := bstep (se 1 (by rfl) ⟨1438019, by rfl⟩ : syracuseStep 1917359 = 2876039) B2876039
theorem B1917395 : Blo 850355 1917395 := bstep (se 1 (by rfl) ⟨1438046, by rfl⟩ : syracuseStep 1917395 = 2876093) B2876093
theorem B4309523 : Blo 850355 4309523 := bstep (se 1 (by rfl) ⟨3232142, by rfl⟩ : syracuseStep 4309523 = 6464285) B6464285
theorem B1917503 : Blo 850355 1917503 := bstep (se 1 (by rfl) ⟨1438127, by rfl⟩ : syracuseStep 1917503 = 2876255) B2876255
theorem B1917611 : Blo 850355 1917611 := bstep (se 1 (by rfl) ⟨1438208, by rfl⟩ : syracuseStep 1917611 = 2876417) B2876417
theorem B5194691 : Blo 850355 5194691 := bstep (se 1 (by rfl) ⟨3896018, by rfl⟩ : syracuseStep 5194691 = 7792037) B7792037
theorem B1819687 : Blo 850355 1819687 := bstep (se 1 (by rfl) ⟨1364765, by rfl⟩ : syracuseStep 1819687 = 2729531) B2729531
theorem B1918151 : Blo 850355 1918151 := bstep (se 1 (by rfl) ⟨1438613, by rfl⟩ : syracuseStep 1918151 = 2877227) B2877227
theorem B4375795 : Blo 850355 4375795 := bstep (se 1 (by rfl) ⟨3281846, by rfl⟩ : syracuseStep 4375795 = 6563693) B6563693
theorem B1918331 : Blo 850355 1918331 := bstep (se 1 (by rfl) ⟨1438748, by rfl⟩ : syracuseStep 1918331 = 2877497) B2877497
theorem B1918457 : Blo 850355 1918457 := bstep (se 2 (by rfl) ⟨719421, by rfl⟩ : syracuseStep 1918457 = 1438843) B1438843
theorem B1918547 : Blo 850355 1918547 := bstep (se 1 (by rfl) ⟨1438910, by rfl⟩ : syracuseStep 1918547 = 2877821) B2877821
theorem B7292551 : Blo 850355 7292551 := bstep (se 1 (by rfl) ⟨5469413, by rfl⟩ : syracuseStep 7292551 = 10938827) B10938827
theorem B4441787 : Blo 850355 4441787 := bstep (se 1 (by rfl) ⟨3331340, by rfl⟩ : syracuseStep 4441787 = 6662681) B6662681
theorem B1918727 : Blo 850355 1918727 := bstep (se 1 (by rfl) ⟨1439045, by rfl⟩ : syracuseStep 1918727 = 2878091) B2878091
theorem B3065705 : Blo 850355 3065705 := bstep (se 2 (by rfl) ⟨1149639, by rfl⟩ : syracuseStep 3065705 = 2299279) B2299279
theorem B4311305 : Blo 850355 4311305 := bstep (se 2 (by rfl) ⟨1616739, by rfl⟩ : syracuseStep 4311305 = 3233479) B3233479
theorem B4606217 : Blo 850355 4606217 := bstep (se 2 (by rfl) ⟨1727331, by rfl⟩ : syracuseStep 4606217 = 3454663) B3454663
theorem B1919339 : Blo 850355 1919339 := bstep (se 1 (by rfl) ⟨1439504, by rfl⟩ : syracuseStep 1919339 = 2879009) B2879009
theorem B3230063 : Blo 850355 3230063 := bstep (se 1 (by rfl) ⟨2422547, by rfl⟩ : syracuseStep 3230063 = 4845095) B4845095
theorem B1296751 : Blo 850355 1296751 := bstep (se 1 (by rfl) ⟨972563, by rfl⟩ : syracuseStep 1296751 = 1945127) B1945127
theorem B78694787 : Blo 850355 78694787 := bstep (se 1 (by rfl) ⟨59021090, by rfl⟩ : syracuseStep 78694787 = 118042181) B118042181
theorem B1919483 : Blo 850355 1919483 := bstep (se 1 (by rfl) ⟨1439612, by rfl⟩ : syracuseStep 1919483 = 2879225) B2879225
theorem B2050667 : Blo 850355 2050667 := bstep (se 1 (by rfl) ⟨1538000, by rfl⟩ : syracuseStep 2050667 = 3076001) B3076001
theorem B1919609 : Blo 850355 1919609 := bstep (se 2 (by rfl) ⟨719853, by rfl⟩ : syracuseStep 1919609 = 1439707) B1439707
theorem B1919663 : Blo 850355 1919663 := bstep (se 1 (by rfl) ⟨1439747, by rfl⟩ : syracuseStep 1919663 = 2879495) B2879495
theorem B1919735 : Blo 850355 1919735 := bstep (se 1 (by rfl) ⟨1439801, by rfl⟩ : syracuseStep 1919735 = 2879603) B2879603
theorem B1919915 : Blo 850355 1919915 := bstep (se 1 (by rfl) ⟨1439936, by rfl⟩ : syracuseStep 1919915 = 2879873) B2879873
theorem B2215199 : Blo 850355 2215199 := bstep (se 1 (by rfl) ⟨1661399, by rfl⟩ : syracuseStep 2215199 = 3322799) B3322799
theorem B9194867 : Blo 850355 9194867 := bstep (se 1 (by rfl) ⟨6896150, by rfl⟩ : syracuseStep 9194867 = 13792301) B13792301
theorem B4312439 : Blo 850355 4312439 := bstep (se 1 (by rfl) ⟨3234329, by rfl⟩ : syracuseStep 4312439 = 6468659) B6468659
theorem B1920455 : Blo 850355 1920455 := bstep (se 1 (by rfl) ⟨1440341, by rfl⟩ : syracuseStep 1920455 = 2880683) B2880683
theorem B4312601 : Blo 850355 4312601 := bstep (se 2 (by rfl) ⟨1617225, by rfl⟩ : syracuseStep 4312601 = 3234451) B3234451
theorem B3231535 : Blo 850355 3231535 := bstep (se 1 (by rfl) ⟨2423651, by rfl⟩ : syracuseStep 3231535 = 4847303) B4847303
theorem B1920815 : Blo 850355 1920815 := bstep (se 1 (by rfl) ⟨1440611, by rfl⟩ : syracuseStep 1920815 = 2881223) B2881223
theorem B1823087 : Blo 850355 1823087 := bstep (se 1 (by rfl) ⟨1367315, by rfl⟩ : syracuseStep 1823087 = 2734631) B2734631
theorem B1921391 : Blo 850355 1921391 := bstep (se 1 (by rfl) ⟨1441043, by rfl⟩ : syracuseStep 1921391 = 2882087) B2882087
theorem B2216375 : Blo 850355 2216375 := bstep (se 1 (by rfl) ⟨1662281, by rfl⟩ : syracuseStep 2216375 = 3324563) B3324563
theorem B1921463 : Blo 850355 1921463 := bstep (se 1 (by rfl) ⟨1441097, by rfl⟩ : syracuseStep 1921463 = 2882195) B2882195
theorem B3461633 : Blo 850355 3461633 := bstep (se 2 (by rfl) ⟨1298112, by rfl⟩ : syracuseStep 3461633 = 2596225) B2596225
theorem B2871827 : Blo 850355 2871827 := bstep (se 1 (by rfl) ⟨2153870, by rfl⟩ : syracuseStep 2871827 = 4307741) B4307741
theorem B1921607 : Blo 850355 1921607 := bstep (se 1 (by rfl) ⟨1441205, by rfl⟩ : syracuseStep 1921607 = 2882411) B2882411
theorem B1921643 : Blo 850355 1921643 := bstep (se 1 (by rfl) ⟨1441232, by rfl⟩ : syracuseStep 1921643 = 2882465) B2882465
theorem B1364663 : Blo 850355 1364663 := bstep (se 1 (by rfl) ⟨1023497, by rfl⟩ : syracuseStep 1364663 = 2046995) B2046995
theorem B35050195 : Blo 850355 35050195 := bstep (se 1 (by rfl) ⟨26287646, by rfl⟩ : syracuseStep 35050195 = 52575293) B52575293
theorem B1922039 : Blo 850355 1922039 := bstep (se 1 (by rfl) ⟨1441529, by rfl⟩ : syracuseStep 1922039 = 2883059) B2883059
theorem B3888427 : Blo 850355 3888427 := bstep (se 1 (by rfl) ⟨2916320, by rfl⟩ : syracuseStep 3888427 = 5832641) B5832641
theorem B1824095 : Blo 850355 1824095 := bstep (se 1 (by rfl) ⟨1368071, by rfl⟩ : syracuseStep 1824095 = 2736143) B2736143
theorem B4609847 : Blo 850355 4609847 := bstep (se 1 (by rfl) ⟨3457385, by rfl⟩ : syracuseStep 4609847 = 6914771) B6914771
theorem B4675831 : Blo 850355 4675831 := bstep (se 1 (by rfl) ⟨3506873, by rfl⟩ : syracuseStep 4675831 = 7013747) B7013747
theorem B2873609 : Blo 850355 2873609 := bstep (se 2 (by rfl) ⟨1077603, by rfl⟩ : syracuseStep 2873609 = 2155207) B2155207
theorem B2152777 : Blo 850355 2152777 := bstep (se 2 (by rfl) ⟨807291, by rfl⟩ : syracuseStep 2152777 = 1614583) B1614583
theorem B4315517 : Blo 850355 4315517 := bstep (se 3 (by rfl) ⟨809159, by rfl⟩ : syracuseStep 4315517 = 1618319) B1618319
theorem B2153081 : Blo 850355 2153081 := bstep (se 2 (by rfl) ⟨807405, by rfl⟩ : syracuseStep 2153081 = 1614811) B1614811
theorem B908263 : Blo 850355 908263 := bstep (se 1 (by rfl) ⟨681197, by rfl⟩ : syracuseStep 908263 = 1362395) B1362395
theorem B2874743 : Blo 850355 2874743 := bstep (se 1 (by rfl) ⟨2156057, by rfl⟩ : syracuseStep 2874743 = 4312115) B4312115
theorem B3235409 : Blo 850355 3235409 := bstep (se 2 (by rfl) ⟨1213278, by rfl⟩ : syracuseStep 3235409 = 2426557) B2426557
theorem B3235423 : Blo 850355 3235423 := bstep (se 1 (by rfl) ⟨2426567, by rfl⟩ : syracuseStep 3235423 = 4853135) B4853135
theorem B1597115 : Blo 850355 1597115 := bstep (se 1 (by rfl) ⟨1197836, by rfl⟩ : syracuseStep 1597115 = 2395673) B2395673
theorem B1367815 : Blo 850355 1367815 := bstep (se 1 (by rfl) ⟨1025861, by rfl⟩ : syracuseStep 1367815 = 2051723) B2051723
theorem B4316975 : Blo 850355 4316975 := bstep (se 1 (by rfl) ⟨3237731, by rfl⟩ : syracuseStep 4316975 = 6475463) B6475463
theorem B7266307 : Blo 850355 7266307 := bstep (se 1 (by rfl) ⟨5449730, by rfl⟩ : syracuseStep 7266307 = 10899461) B10899461
theorem B4087913 : Blo 850355 4087913 := bstep (se 2 (by rfl) ⟨1532967, by rfl⟩ : syracuseStep 4087913 = 3065935) B3065935
theorem B2154863 : Blo 850355 2154863 := bstep (se 1 (by rfl) ⟨1616147, by rfl⟩ : syracuseStep 2154863 = 3232295) B3232295
theorem B2875823 : Blo 850355 2875823 := bstep (se 1 (by rfl) ⟨2156867, by rfl⟩ : syracuseStep 2875823 = 4313735) B4313735
theorem B7267265 : Blo 850355 7267265 := bstep (se 2 (by rfl) ⟨2725224, by rfl⟩ : syracuseStep 7267265 = 5450449) B5450449
theorem B2155511 : Blo 850355 2155511 := bstep (se 1 (by rfl) ⟨1616633, by rfl⟩ : syracuseStep 2155511 = 3233267) B3233267
theorem B2155643 : Blo 850355 2155643 := bstep (se 1 (by rfl) ⟨1616732, by rfl⟩ : syracuseStep 2155643 = 3233465) B3233465
theorem B8185211 : Blo 850355 8185211 := bstep (se 1 (by rfl) ⟨6138908, by rfl⟩ : syracuseStep 8185211 = 12277817) B12277817
theorem B2876795 : Blo 850355 2876795 := bstep (se 1 (by rfl) ⟨2157596, by rfl⟩ : syracuseStep 2876795 = 4315193) B4315193
theorem B9856399 : Blo 850355 9856399 := bstep (se 1 (by rfl) ⟨7392299, by rfl⟩ : syracuseStep 9856399 = 14784599) B14784599
theorem B1729991 : Blo 850355 1729991 := bstep (se 1 (by rfl) ⟨1297493, by rfl⟩ : syracuseStep 1729991 = 2594987) B2594987
theorem B2909753 : Blo 850355 2909753 := bstep (se 2 (by rfl) ⟨1091157, by rfl⟩ : syracuseStep 2909753 = 2182315) B2182315
theorem B4319081 : Blo 850355 4319081 := bstep (se 2 (by rfl) ⟨1619655, by rfl⟩ : syracuseStep 4319081 = 3239311) B3239311
theorem B3237839 : Blo 850355 3237839 := bstep (se 1 (by rfl) ⟨2428379, by rfl⟩ : syracuseStep 3237839 = 4856759) B4856759
theorem B52553843 : Blo 850355 52553843 := bstep (se 1 (by rfl) ⟨39415382, by rfl⟩ : syracuseStep 52553843 = 78830765) B78830765
theorem B3074183 : Blo 850355 3074183 := bstep (se 1 (by rfl) ⟨2305637, by rfl⟩ : syracuseStep 3074183 = 4611275) B4611275
theorem B1436015 : Blo 850355 1436015 := bstep (se 1 (by rfl) ⟨1077011, by rfl⟩ : syracuseStep 1436015 = 2154023) B2154023
theorem B911783 : Blo 850355 911783 := bstep (se 1 (by rfl) ⟨683837, by rfl⟩ : syracuseStep 911783 = 1367675) B1367675
theorem B9234917 : Blo 850355 9234917 := bstep (se 4 (by rfl) ⟨865773, by rfl⟩ : syracuseStep 9234917 = 1731547) B1731547
theorem B1436231 : Blo 850355 1436231 := bstep (se 1 (by rfl) ⟨1077173, by rfl⟩ : syracuseStep 1436231 = 2154347) B2154347
theorem B14543549 : Blo 850355 14543549 := bstep (se 3 (by rfl) ⟨2726915, by rfl⟩ : syracuseStep 14543549 = 5453831) B5453831
theorem B2878199 : Blo 850355 2878199 := bstep (se 1 (by rfl) ⟨2158649, by rfl⟩ : syracuseStep 2878199 = 4317299) B4317299
theorem B2157455 : Blo 850355 2157455 := bstep (se 1 (by rfl) ⟨1618091, by rfl⟩ : syracuseStep 2157455 = 3236183) B3236183
theorem B3238811 : Blo 850355 3238811 := bstep (se 1 (by rfl) ⟨2429108, by rfl⟩ : syracuseStep 3238811 = 4858217) B4858217
theorem B1436663 : Blo 850355 1436663 := bstep (se 1 (by rfl) ⟨1077497, by rfl⟩ : syracuseStep 1436663 = 2154995) B2154995
theorem B12610637 : Blo 850355 12610637 := bstep (se 3 (by rfl) ⟨2364494, by rfl⟩ : syracuseStep 12610637 = 4728989) B4728989
theorem B1076591 : Blo 850355 1076591 := bstep (se 1 (by rfl) ⟨807443, by rfl⟩ : syracuseStep 1076591 = 1614887) B1614887
theorem B2157961 : Blo 850355 2157961 := bstep (se 2 (by rfl) ⟨809235, by rfl⟩ : syracuseStep 2157961 = 1618471) B1618471
theorem B1076647 : Blo 850355 1076647 := bstep (se 1 (by rfl) ⟨807485, by rfl⟩ : syracuseStep 1076647 = 1614971) B1614971
theorem B2158073 : Blo 850355 2158073 := bstep (se 2 (by rfl) ⟨809277, by rfl⟩ : syracuseStep 2158073 = 1618555) B1618555
theorem B4320863 : Blo 850355 4320863 := bstep (se 1 (by rfl) ⟨3240647, by rfl⟩ : syracuseStep 4320863 = 6481295) B6481295
theorem B3239585 : Blo 850355 3239585 := bstep (se 2 (by rfl) ⟨1214844, by rfl⟩ : syracuseStep 3239585 = 2429689) B2429689
theorem B1076971 : Blo 850355 1076971 := bstep (se 1 (by rfl) ⟨807728, by rfl⟩ : syracuseStep 1076971 = 1615457) B1615457
theorem B1437419 : Blo 850355 1437419 := bstep (se 1 (by rfl) ⟨1078064, by rfl⟩ : syracuseStep 1437419 = 2156129) B2156129
theorem B2879279 : Blo 850355 2879279 := bstep (se 1 (by rfl) ⟨2159459, by rfl⟩ : syracuseStep 2879279 = 4318919) B4318919
theorem B2158721 : Blo 850355 2158721 := bstep (se 2 (by rfl) ⟨809520, by rfl⟩ : syracuseStep 2158721 = 1619041) B1619041
theorem B3240283 : Blo 850355 3240283 := bstep (se 1 (by rfl) ⟨2430212, by rfl⟩ : syracuseStep 3240283 = 4860425) B4860425
theorem B17494481 : Blo 850355 17494481 := bstep (se 2 (by rfl) ⟨6560430, by rfl⟩ : syracuseStep 17494481 = 13120861) B13120861
theorem B1077943 : Blo 850355 1077943 := bstep (se 1 (by rfl) ⟨808457, by rfl⟩ : syracuseStep 1077943 = 1616915) B1616915
theorem B1438391 : Blo 850355 1438391 := bstep (se 1 (by rfl) ⟨1078793, by rfl⟩ : syracuseStep 1438391 = 2157587) B2157587
theorem B18412217 : Blo 850355 18412217 := bstep (se 2 (by rfl) ⟨6904581, by rfl⟩ : syracuseStep 18412217 = 13809163) B13809163
theorem B9237341 : Blo 850355 9237341 := bstep (se 3 (by rfl) ⟨1732001, by rfl⟩ : syracuseStep 9237341 = 3464003) B3464003
theorem B14578541 : Blo 850355 14578541 := bstep (se 3 (by rfl) ⟨2733476, by rfl⟩ : syracuseStep 14578541 = 5466953) B5466953
theorem B2159531 : Blo 850355 2159531 := bstep (se 1 (by rfl) ⟨1619648, by rfl⟩ : syracuseStep 2159531 = 3239297) B3239297
theorem B7271639 : Blo 850355 7271639 := bstep (se 1 (by rfl) ⟨5453729, by rfl⟩ : syracuseStep 7271639 = 10907459) B10907459
theorem B8189207 : Blo 850355 8189207 := bstep (se 1 (by rfl) ⟨6141905, by rfl⟩ : syracuseStep 8189207 = 12283811) B12283811
theorem B3241255 : Blo 850355 3241255 := bstep (se 1 (by rfl) ⟨2430941, by rfl⟩ : syracuseStep 3241255 = 4861883) B4861883
theorem B1439113 : Blo 850355 1439113 := bstep (se 2 (by rfl) ⟨539667, by rfl⟩ : syracuseStep 1439113 = 1079335) B1079335
theorem B3241529 : Blo 850355 3241529 := bstep (se 2 (by rfl) ⟨1215573, by rfl⟩ : syracuseStep 3241529 = 2431147) B2431147
theorem B1537697 : Blo 850355 1537697 := bstep (se 2 (by rfl) ⟨576636, by rfl⟩ : syracuseStep 1537697 = 1153273) B1153273
theorem B3274427 : Blo 850355 3274427 := bstep (se 1 (by rfl) ⟨2455820, by rfl⟩ : syracuseStep 3274427 = 4911641) B4911641
theorem B2160391 : Blo 850355 2160391 := bstep (se 1 (by rfl) ⟨1620293, by rfl⟩ : syracuseStep 2160391 = 3240587) B3240587
theorem B1275689 : Blo 850355 1275689 := bstep (se 2 (by rfl) ⟨478383, by rfl⟩ : syracuseStep 1275689 = 956767) B956767
theorem B1275695 : Blo 850355 1275695 := bstep (se 1 (by rfl) ⟨956771, by rfl⟩ : syracuseStep 1275695 = 1913543) B1913543
theorem B1439545 : Blo 850355 1439545 := bstep (se 2 (by rfl) ⟨539829, by rfl⟩ : syracuseStep 1439545 = 1079659) B1079659
theorem B2881385 : Blo 850355 2881385 := bstep (se 2 (by rfl) ⟨1080519, by rfl⟩ : syracuseStep 2881385 = 2161039) B2161039
theorem B2160665 : Blo 850355 2160665 := bstep (se 2 (by rfl) ⟨810249, by rfl⟩ : syracuseStep 2160665 = 1620499) B1620499
theorem B7764011 : Blo 850355 7764011 := bstep (se 1 (by rfl) ⟨5823008, by rfl⟩ : syracuseStep 7764011 = 11646017) B11646017
theorem B1439849 : Blo 850355 1439849 := bstep (se 2 (by rfl) ⟨539943, by rfl⟩ : syracuseStep 1439849 = 1079887) B1079887
theorem B1276169 : Blo 850355 1276169 := bstep (se 2 (by rfl) ⟨478563, by rfl⟩ : syracuseStep 1276169 = 957127) B957127
theorem B2881817 : Blo 850355 2881817 := bstep (se 2 (by rfl) ⟨1080681, by rfl⟩ : syracuseStep 2881817 = 2161363) B2161363
theorem B1276271 : Blo 850355 1276271 := bstep (se 1 (by rfl) ⟨957203, by rfl⟩ : syracuseStep 1276271 = 1914407) B1914407
theorem B850427 : Blo 850355 850427 := bstep (se 1 (by rfl) ⟨637820, by rfl⟩ : syracuseStep 850427 = 1275641) B1275641
theorem B850495 : Blo 850355 850495 := bstep (se 1 (by rfl) ⟨637871, by rfl⟩ : syracuseStep 850495 = 1275743) B1275743
theorem B850503 : Blo 850355 850503 := bstep (se 1 (by rfl) ⟨637877, by rfl⟩ : syracuseStep 850503 = 1275755) B1275755
theorem B1276487 : Blo 850355 1276487 := bstep (se 1 (by rfl) ⟨957365, by rfl⟩ : syracuseStep 1276487 = 1914731) B1914731
theorem B1276523 : Blo 850355 1276523 := bstep (se 1 (by rfl) ⟨957392, by rfl⟩ : syracuseStep 1276523 = 1914785) B1914785
theorem B1079983 : Blo 850355 1079983 := bstep (se 1 (by rfl) ⟨809987, by rfl⟩ : syracuseStep 1079983 = 1619975) B1619975
theorem B850655 : Blo 850355 850655 := bstep (se 1 (by rfl) ⟨637991, by rfl⟩ : syracuseStep 850655 = 1275983) B1275983
theorem B850735 : Blo 850355 850735 := bstep (se 1 (by rfl) ⟨638051, by rfl⟩ : syracuseStep 850735 = 1276103) B1276103
theorem B1276751 : Blo 850355 1276751 := bstep (se 1 (by rfl) ⟨957563, by rfl⟩ : syracuseStep 1276751 = 1915127) B1915127
theorem B850843 : Blo 850355 850843 := bstep (se 1 (by rfl) ⟨638132, by rfl⟩ : syracuseStep 850843 = 1276265) B1276265
theorem B850895 : Blo 850355 850895 := bstep (se 1 (by rfl) ⟨638171, by rfl⟩ : syracuseStep 850895 = 1276343) B1276343
theorem B850919 : Blo 850355 850919 := bstep (se 1 (by rfl) ⟨638189, by rfl⟩ : syracuseStep 850919 = 1276379) B1276379
theorem B1277147 : Blo 850355 1277147 := bstep (se 1 (by rfl) ⟨957860, by rfl⟩ : syracuseStep 1277147 = 1915721) B1915721
theorem B8191205 : Blo 850355 8191205 := bstep (se 4 (by rfl) ⟨767925, by rfl⟩ : syracuseStep 8191205 = 1535851) B1535851
theorem B851231 : Blo 850355 851231 := bstep (se 1 (by rfl) ⟨638423, by rfl⟩ : syracuseStep 851231 = 1276847) B1276847
theorem B851291 : Blo 850355 851291 := bstep (se 1 (by rfl) ⟨638468, by rfl⟩ : syracuseStep 851291 = 1276937) B1276937
theorem B851311 : Blo 850355 851311 := bstep (se 1 (by rfl) ⟨638483, by rfl⟩ : syracuseStep 851311 = 1276967) B1276967
theorem B1277321 : Blo 850355 1277321 := bstep (se 2 (by rfl) ⟨478995, by rfl⟩ : syracuseStep 1277321 = 957991) B957991
theorem B18414985 : Blo 850355 18414985 := bstep (se 2 (by rfl) ⟨6905619, by rfl⟩ : syracuseStep 18414985 = 13811239) B13811239
theorem B851367 : Blo 850355 851367 := bstep (se 1 (by rfl) ⟨638525, by rfl⟩ : syracuseStep 851367 = 1277051) B1277051
theorem B4095431 : Blo 850355 4095431 := bstep (se 1 (by rfl) ⟨3071573, by rfl⟩ : syracuseStep 4095431 = 6143147) B6143147
theorem B1441273 : Blo 850355 1441273 := bstep (se 2 (by rfl) ⟨540477, by rfl⟩ : syracuseStep 1441273 = 1080955) B1080955
theorem B851451 : Blo 850355 851451 := bstep (se 1 (by rfl) ⟨638588, by rfl⟩ : syracuseStep 851451 = 1277177) B1277177
theorem B851519 : Blo 850355 851519 := bstep (se 1 (by rfl) ⟨638639, by rfl⟩ : syracuseStep 851519 = 1277279) B1277279
theorem B851527 : Blo 850355 851527 := bstep (se 1 (by rfl) ⟨638645, by rfl⟩ : syracuseStep 851527 = 1277291) B1277291
theorem B2883167 : Blo 850355 2883167 := bstep (se 1 (by rfl) ⟨2162375, by rfl⟩ : syracuseStep 2883167 = 4324751) B4324751
theorem B3636845 : Blo 850355 3636845 := bstep (se 3 (by rfl) ⟨681908, by rfl⟩ : syracuseStep 3636845 = 1363817) B1363817
theorem B4325075 : Blo 850355 4325075 := bstep (se 1 (by rfl) ⟨3243806, by rfl⟩ : syracuseStep 4325075 = 6487613) B6487613
theorem B851679 : Blo 850355 851679 := bstep (se 1 (by rfl) ⟨638759, by rfl⟩ : syracuseStep 851679 = 1277519) B1277519
theorem B1277675 : Blo 850355 1277675 := bstep (se 1 (by rfl) ⟨958256, by rfl⟩ : syracuseStep 1277675 = 1916513) B1916513
theorem B13827847 : Blo 850355 13827847 := bstep (se 1 (by rfl) ⟨10370885, by rfl⟩ : syracuseStep 13827847 = 20741771) B20741771
theorem B1441543 : Blo 850355 1441543 := bstep (se 1 (by rfl) ⟨1081157, by rfl⟩ : syracuseStep 1441543 = 2162315) B2162315
theorem B1441577 : Blo 850355 1441577 := bstep (se 2 (by rfl) ⟨540591, by rfl⟩ : syracuseStep 1441577 = 1081183) B1081183
theorem B851759 : Blo 850355 851759 := bstep (se 1 (by rfl) ⟨638819, by rfl⟩ : syracuseStep 851759 = 1277639) B1277639
theorem B4849469 : Blo 850355 4849469 := bstep (se 3 (by rfl) ⟨909275, by rfl⟩ : syracuseStep 4849469 = 1818551) B1818551
theorem B851867 : Blo 850355 851867 := bstep (se 1 (by rfl) ⟨638900, by rfl⟩ : syracuseStep 851867 = 1277801) B1277801
theorem B851919 : Blo 850355 851919 := bstep (se 1 (by rfl) ⟨638939, by rfl⟩ : syracuseStep 851919 = 1277879) B1277879
theorem B1277903 : Blo 850355 1277903 := bstep (se 1 (by rfl) ⟨958427, by rfl⟩ : syracuseStep 1277903 = 1916855) B1916855
theorem B851943 : Blo 850355 851943 := bstep (se 1 (by rfl) ⟨638957, by rfl⟩ : syracuseStep 851943 = 1277915) B1277915
theorem B852199 : Blo 850355 852199 := bstep (se 1 (by rfl) ⟨639149, by rfl⟩ : syracuseStep 852199 = 1278299) B1278299
theorem B1278239 : Blo 850355 1278239 := bstep (se 1 (by rfl) ⟨958679, by rfl⟩ : syracuseStep 1278239 = 1917359) B1917359
theorem B1278263 : Blo 850355 1278263 := bstep (se 1 (by rfl) ⟨958697, by rfl⟩ : syracuseStep 1278263 = 1917395) B1917395
theorem B1278335 : Blo 850355 1278335 := bstep (se 1 (by rfl) ⟨958751, by rfl⟩ : syracuseStep 1278335 = 1917503) B1917503
theorem B852351 : Blo 850355 852351 := bstep (se 1 (by rfl) ⟨639263, by rfl⟩ : syracuseStep 852351 = 1278527) B1278527
theorem B1278407 : Blo 850355 1278407 := bstep (se 1 (by rfl) ⟨958805, by rfl⟩ : syracuseStep 1278407 = 1917611) B1917611
theorem B852431 : Blo 850355 852431 := bstep (se 1 (by rfl) ⟨639323, by rfl⟩ : syracuseStep 852431 = 1278647) B1278647
theorem B6554209 : Blo 850355 6554209 := bstep (se 2 (by rfl) ⟨2457828, by rfl⟩ : syracuseStep 6554209 = 4915657) B4915657
theorem B852583 : Blo 850355 852583 := bstep (se 1 (by rfl) ⟨639437, by rfl⟩ : syracuseStep 852583 = 1278875) B1278875
theorem B1278761 : Blo 850355 1278761 := bstep (se 2 (by rfl) ⟨479535, by rfl⟩ : syracuseStep 1278761 = 959071) B959071
theorem B1278767 : Blo 850355 1278767 := bstep (se 1 (by rfl) ⟨959075, by rfl⟩ : syracuseStep 1278767 = 1918151) B1918151
theorem B852847 : Blo 850355 852847 := bstep (se 1 (by rfl) ⟨639635, by rfl⟩ : syracuseStep 852847 = 1279271) B1279271
theorem B1278887 : Blo 850355 1278887 := bstep (se 1 (by rfl) ⟨959165, by rfl⟩ : syracuseStep 1278887 = 1918331) B1918331
theorem B852903 : Blo 850355 852903 := bstep (se 1 (by rfl) ⟨639677, by rfl⟩ : syracuseStep 852903 = 1279355) B1279355
theorem B1278971 : Blo 850355 1278971 := bstep (se 1 (by rfl) ⟨959228, by rfl⟩ : syracuseStep 1278971 = 1918457) B1918457
theorem B852987 : Blo 850355 852987 := bstep (se 1 (by rfl) ⟨639740, by rfl⟩ : syracuseStep 852987 = 1279481) B1279481
theorem B1279031 : Blo 850355 1279031 := bstep (se 1 (by rfl) ⟨959273, by rfl⟩ : syracuseStep 1279031 = 1918547) B1918547
theorem B853055 : Blo 850355 853055 := bstep (se 1 (by rfl) ⟨639791, by rfl⟩ : syracuseStep 853055 = 1279583) B1279583
theorem B1279151 : Blo 850355 1279151 := bstep (se 1 (by rfl) ⟨959363, by rfl⟩ : syracuseStep 1279151 = 1918727) B1918727
theorem B853199 : Blo 850355 853199 := bstep (se 1 (by rfl) ⟨639899, by rfl⟩ : syracuseStep 853199 = 1279799) B1279799
theorem B2426249 : Blo 850355 2426249 := bstep (se 2 (by rfl) ⟨909843, by rfl⟩ : syracuseStep 2426249 = 1819687) B1819687
theorem B853403 : Blo 850355 853403 := bstep (se 1 (by rfl) ⟨640052, by rfl⟩ : syracuseStep 853403 = 1280105) B1280105
theorem B1279559 : Blo 850355 1279559 := bstep (se 1 (by rfl) ⟨959669, by rfl⟩ : syracuseStep 1279559 = 1919339) B1919339
theorem B215549525 : Blo 850355 215549525 := bstep (se 8 (by rfl) ⟨1262985, by rfl⟩ : syracuseStep 215549525 = 2525971) B2525971
theorem B853615 : Blo 850355 853615 := bstep (se 1 (by rfl) ⟨640211, by rfl⟩ : syracuseStep 853615 = 1280423) B1280423
theorem B5834393 : Blo 850355 5834393 := bstep (se 2 (by rfl) ⟨2187897, by rfl⟩ : syracuseStep 5834393 = 4375795) B4375795
theorem B2459297 : Blo 850355 2459297 := bstep (se 2 (by rfl) ⟨922236, by rfl⟩ : syracuseStep 2459297 = 1844473) B1844473
theorem B1279655 : Blo 850355 1279655 := bstep (se 1 (by rfl) ⟨959741, by rfl⟩ : syracuseStep 1279655 = 1919483) B1919483
theorem B853671 : Blo 850355 853671 := bstep (se 1 (by rfl) ⟨640253, by rfl⟩ : syracuseStep 853671 = 1280507) B1280507
theorem B2426591 : Blo 850355 2426591 := bstep (se 1 (by rfl) ⟨1819943, by rfl⟩ : syracuseStep 2426591 = 3639887) B3639887
theorem B1279739 : Blo 850355 1279739 := bstep (se 1 (by rfl) ⟨959804, by rfl⟩ : syracuseStep 1279739 = 1919609) B1919609
theorem B853755 : Blo 850355 853755 := bstep (se 1 (by rfl) ⟨640316, by rfl⟩ : syracuseStep 853755 = 1280633) B1280633
theorem B1279775 : Blo 850355 1279775 := bstep (se 1 (by rfl) ⟨959831, by rfl⟩ : syracuseStep 1279775 = 1919663) B1919663
theorem B853791 : Blo 850355 853791 := bstep (se 1 (by rfl) ⟨640343, by rfl⟩ : syracuseStep 853791 = 1280687) B1280687
theorem B853823 : Blo 850355 853823 := bstep (se 1 (by rfl) ⟨640367, by rfl⟩ : syracuseStep 853823 = 1280735) B1280735
theorem B1279823 : Blo 850355 1279823 := bstep (se 1 (by rfl) ⟨959867, by rfl⟩ : syracuseStep 1279823 = 1919735) B1919735
theorem B13141865 : Blo 850355 13141865 := bstep (se 2 (by rfl) ⟨4928199, by rfl⟩ : syracuseStep 13141865 = 9856399) B9856399
theorem B1279943 : Blo 850355 1279943 := bstep (se 1 (by rfl) ⟨959957, by rfl⟩ : syracuseStep 1279943 = 1919915) B1919915
theorem B853999 : Blo 850355 853999 := bstep (se 1 (by rfl) ⟨640499, by rfl⟩ : syracuseStep 853999 = 1280999) B1280999
theorem B3639305 : Blo 850355 3639305 := bstep (se 2 (by rfl) ⟨1364739, by rfl⟩ : syracuseStep 3639305 = 2729479) B2729479
theorem B854171 : Blo 850355 854171 := bstep (se 1 (by rfl) ⟨640628, by rfl⟩ : syracuseStep 854171 = 1281257) B1281257
theorem B1476799 : Blo 850355 1476799 := bstep (se 1 (by rfl) ⟨1107599, by rfl⟩ : syracuseStep 1476799 = 2215199) B2215199
theorem B854207 : Blo 850355 854207 := bstep (se 1 (by rfl) ⟨640655, by rfl⟩ : syracuseStep 854207 = 1281311) B1281311
theorem B6129911 : Blo 850355 6129911 := bstep (se 1 (by rfl) ⟨4597433, by rfl⟩ : syracuseStep 6129911 = 9194867) B9194867
theorem B1280297 : Blo 850355 1280297 := bstep (se 2 (by rfl) ⟨480111, by rfl⟩ : syracuseStep 1280297 = 960223) B960223
theorem B1280303 : Blo 850355 1280303 := bstep (se 1 (by rfl) ⟨960227, by rfl⟩ : syracuseStep 1280303 = 1920455) B1920455
theorem B854319 : Blo 850355 854319 := bstep (se 1 (by rfl) ⟨640739, by rfl⟩ : syracuseStep 854319 = 1281479) B1281479
theorem B1280543 : Blo 850355 1280543 := bstep (se 1 (by rfl) ⟨960407, by rfl⟩ : syracuseStep 1280543 = 1920815) B1920815
theorem B1280927 : Blo 850355 1280927 := bstep (se 1 (by rfl) ⟨960695, by rfl⟩ : syracuseStep 1280927 = 1921391) B1921391
theorem B1280975 : Blo 850355 1280975 := bstep (se 1 (by rfl) ⟨960731, by rfl⟩ : syracuseStep 1280975 = 1921463) B1921463
theorem B1281065 : Blo 850355 1281065 := bstep (se 2 (by rfl) ⟨480399, by rfl⟩ : syracuseStep 1281065 = 960799) B960799
theorem B1281071 : Blo 850355 1281071 := bstep (se 1 (by rfl) ⟨960803, by rfl⟩ : syracuseStep 1281071 = 1921607) B1921607
theorem B1281095 : Blo 850355 1281095 := bstep (se 1 (by rfl) ⟨960821, by rfl⟩ : syracuseStep 1281095 = 1921643) B1921643
theorem B1281359 : Blo 850355 1281359 := bstep (se 1 (by rfl) ⟨961019, by rfl⟩ : syracuseStep 1281359 = 1922039) B1922039
theorem B1281449 : Blo 850355 1281449 := bstep (se 2 (by rfl) ⟨480543, by rfl⟩ : syracuseStep 1281449 = 961087) B961087
theorem B1216063 : Blo 850355 1216063 := bstep (se 1 (by rfl) ⟨912047, by rfl⟩ : syracuseStep 1216063 = 1824095) B1824095
theorem B6000529 : Blo 850355 6000529 := bstep (se 2 (by rfl) ⟨2250198, by rfl⟩ : syracuseStep 6000529 = 4500397) B4500397
theorem B99751061 : Blo 850355 99751061 := bstep (se 6 (by rfl) ⟨2337915, by rfl⟩ : syracuseStep 99751061 = 4675831) B4675831
theorem B2430395 : Blo 850355 2430395 := bstep (se 1 (by rfl) ⟨1822796, by rfl⟩ : syracuseStep 2430395 = 3645593) B3645593
theorem B5904343 : Blo 850355 5904343 := bstep (se 1 (by rfl) ⟨4428257, by rfl⟩ : syracuseStep 5904343 = 8856515) B8856515
theorem B22124609 : Blo 850355 22124609 := bstep (se 2 (by rfl) ⟨8296728, by rfl⟩ : syracuseStep 22124609 = 16593457) B16593457
theorem B4856051 : Blo 850355 4856051 := bstep (se 1 (by rfl) ⟨3642038, by rfl⟩ : syracuseStep 4856051 = 7284077) B7284077
theorem B46733593 : Blo 850355 46733593 := bstep (se 2 (by rfl) ⟨17525097, by rfl⟩ : syracuseStep 46733593 = 35050195) B35050195
theorem B1153327 : Blo 850355 1153327 := bstep (se 1 (by rfl) ⟨864995, by rfl⟩ : syracuseStep 1153327 = 1729991) B1729991
theorem B209852765 : Blo 850355 209852765 := bstep (se 3 (by rfl) ⟨39347393, by rfl⟩ : syracuseStep 209852765 = 78694787) B78694787
theorem B1939835 : Blo 850355 1939835 := bstep (se 1 (by rfl) ⟨1454876, by rfl⟩ : syracuseStep 1939835 = 2909753) B2909753
theorem B6822319 : Blo 850355 6822319 := bstep (se 1 (by rfl) ⟨5116739, by rfl⟩ : syracuseStep 6822319 = 10233479) B10233479
theorem B2431421 : Blo 850355 2431421 := bstep (se 3 (by rfl) ⟨455891, by rfl⟩ : syracuseStep 2431421 = 911783) B911783
theorem B35035895 : Blo 850355 35035895 := bstep (se 1 (by rfl) ⟨26276921, by rfl⟩ : syracuseStep 35035895 = 52553843) B52553843
theorem B957343 : Blo 850355 957343 := bstep (se 1 (by rfl) ⟨718007, by rfl⟩ : syracuseStep 957343 = 1436015) B1436015
theorem B957487 : Blo 850355 957487 := bstep (se 1 (by rfl) ⟨718115, by rfl⟩ : syracuseStep 957487 = 1436231) B1436231
theorem B5184569 : Blo 850355 5184569 := bstep (se 2 (by rfl) ⟨1944213, by rfl⟩ : syracuseStep 5184569 = 3888427) B3888427
theorem B6135101 : Blo 850355 6135101 := bstep (se 3 (by rfl) ⟨1150331, by rfl⟩ : syracuseStep 6135101 = 2300663) B2300663
theorem B957775 : Blo 850355 957775 := bstep (se 1 (by rfl) ⟨718331, by rfl⟩ : syracuseStep 957775 = 1436663) B1436663
theorem B2432423 : Blo 850355 2432423 := bstep (se 1 (by rfl) ⟨1824317, by rfl⟩ : syracuseStep 2432423 = 3648635) B3648635
theorem B958279 : Blo 850355 958279 := bstep (se 1 (by rfl) ⟨718709, by rfl⟩ : syracuseStep 958279 = 1437419) B1437419
theorem B958927 : Blo 850355 958927 := bstep (se 1 (by rfl) ⟨719195, by rfl⟩ : syracuseStep 958927 = 1438391) B1438391
theorem B2761627 : Blo 850355 2761627 := bstep (se 1 (by rfl) ⟨2071220, by rfl⟩ : syracuseStep 2761627 = 4142441) B4142441
theorem B1025131 : Blo 850355 1025131 := bstep (se 1 (by rfl) ⟨768848, by rfl⟩ : syracuseStep 1025131 = 1537697) B1537697
theorem B959899 : Blo 850355 959899 := bstep (se 1 (by rfl) ⟨719924, by rfl⟩ : syracuseStep 959899 = 1439849) B1439849
theorem B6563321 : Blo 850355 6563321 := bstep (se 2 (by rfl) ⟨2461245, by rfl⟩ : syracuseStep 6563321 = 4922491) B4922491
theorem B8857171 : Blo 850355 8857171 := bstep (se 1 (by rfl) ⟨6642878, by rfl⟩ : syracuseStep 8857171 = 13285757) B13285757
theorem B2631503 : Blo 850355 2631503 := bstep (se 1 (by rfl) ⟨1973627, by rfl⟩ : syracuseStep 2631503 = 3947255) B3947255
theorem B24553313 : Blo 850355 24553313 := bstep (se 2 (by rfl) ⟨9207492, by rfl⟩ : syracuseStep 24553313 = 18414985) B18414985
theorem B2304295 : Blo 850355 2304295 := bstep (se 1 (by rfl) ⟨1728221, by rfl⟩ : syracuseStep 2304295 = 3456443) B3456443
theorem B2730287 : Blo 850355 2730287 := bstep (se 1 (by rfl) ⟨2047715, by rfl⟩ : syracuseStep 2730287 = 4095431) B4095431
theorem B961051 : Blo 850355 961051 := bstep (se 1 (by rfl) ⟨720788, by rfl⟩ : syracuseStep 961051 = 1441577) B1441577
theorem B3648311 : Blo 850355 3648311 := bstep (se 1 (by rfl) ⟨2736233, by rfl⟩ : syracuseStep 3648311 = 5472467) B5472467
theorem B1092655 : Blo 850355 1092655 := bstep (se 1 (by rfl) ⟨819491, by rfl⟩ : syracuseStep 1092655 = 1638983) B1638983
theorem B2076155 : Blo 850355 2076155 := bstep (se 1 (by rfl) ⟨1557116, by rfl⟩ : syracuseStep 2076155 = 3114233) B3114233
theorem B3452489 : Blo 850355 3452489 := bstep (se 2 (by rfl) ⟨1294683, by rfl⟩ : syracuseStep 3452489 = 2589367) B2589367
theorem B4861565 : Blo 850355 4861565 := bstep (se 3 (by rfl) ⟨911543, by rfl⟩ : syracuseStep 4861565 = 1823087) B1823087
theorem B1617583 : Blo 850355 1617583 := bstep (se 1 (by rfl) ⟨1213187, by rfl⟩ : syracuseStep 1617583 = 2426375) B2426375
theorem B2961191 : Blo 850355 2961191 := bstep (se 1 (by rfl) ⟨2220893, by rfl⟩ : syracuseStep 2961191 = 4441787) B4441787
theorem B2043803 : Blo 850355 2043803 := bstep (se 1 (by rfl) ⟨1532852, by rfl⟩ : syracuseStep 2043803 = 3065705) B3065705
theorem B1617887 : Blo 850355 1617887 := bstep (se 1 (by rfl) ⟨1213415, by rfl⟩ : syracuseStep 1617887 = 2426831) B2426831
theorem B1619291 : Blo 850355 1619291 := bstep (se 1 (by rfl) ⟨1214468, by rfl⟩ : syracuseStep 1619291 = 2428937) B2428937
theorem B23377409 : Blo 850355 23377409 := bstep (se 2 (by rfl) ⟨8766528, by rfl⟩ : syracuseStep 23377409 = 17533057) B17533057
theorem B1619527 : Blo 850355 1619527 := bstep (se 1 (by rfl) ⟨1214645, by rfl⟩ : syracuseStep 1619527 = 2429291) B2429291
theorem B2307755 : Blo 850355 2307755 := bstep (se 1 (by rfl) ⟨1730816, by rfl⟩ : syracuseStep 2307755 = 3461633) B3461633
theorem B1914551 : Blo 850355 1914551 := bstep (se 1 (by rfl) ⟨1435913, by rfl⟩ : syracuseStep 1914551 = 2871827) B2871827
theorem B2733887 : Blo 850355 2733887 := bstep (se 1 (by rfl) ⟨2050415, by rfl⟩ : syracuseStep 2733887 = 4100831) B4100831
theorem B9222025 : Blo 850355 9222025 := bstep (se 2 (by rfl) ⟨3458259, by rfl⟩ : syracuseStep 9222025 = 6916519) B6916519
theorem B1915739 : Blo 850355 1915739 := bstep (se 1 (by rfl) ⟨1436804, by rfl⟩ : syracuseStep 1915739 = 2873609) B2873609
theorem B28425107 : Blo 850355 28425107 := bstep (se 1 (by rfl) ⟨21318830, by rfl⟩ : syracuseStep 28425107 = 42637661) B42637661
theorem B2735527 : Blo 850355 2735527 := bstep (se 1 (by rfl) ⟨2051645, by rfl⟩ : syracuseStep 2735527 = 4103291) B4103291
theorem B1916495 : Blo 850355 1916495 := bstep (se 1 (by rfl) ⟨1437371, by rfl⟩ : syracuseStep 1916495 = 2874743) B2874743
theorem B4308713 : Blo 850355 4308713 := bstep (se 2 (by rfl) ⟨1615767, by rfl⟩ : syracuseStep 4308713 = 3231535) B3231535
theorem B1064743 : Blo 850355 1064743 := bstep (se 1 (by rfl) ⟨798557, by rfl⟩ : syracuseStep 1064743 = 1597115) B1597115
theorem B2735927 : Blo 850355 2735927 := bstep (se 1 (by rfl) ⟨2051945, by rfl⟩ : syracuseStep 2735927 = 4103891) B4103891
theorem B2736347 : Blo 850355 2736347 := bstep (se 1 (by rfl) ⟨2052260, by rfl⟩ : syracuseStep 2736347 = 4104521) B4104521
theorem B1917215 : Blo 850355 1917215 := bstep (se 1 (by rfl) ⟨1437911, by rfl⟩ : syracuseStep 1917215 = 2875823) B2875823
theorem B5456807 : Blo 850355 5456807 := bstep (se 1 (by rfl) ⟨4092605, by rfl⟩ : syracuseStep 5456807 = 8185211) B8185211
theorem B1917863 : Blo 850355 1917863 := bstep (se 1 (by rfl) ⟨1438397, by rfl⟩ : syracuseStep 1917863 = 2876795) B2876795
theorem B6473033 : Blo 850355 6473033 := bstep (se 2 (by rfl) ⟨2427387, by rfl⟩ : syracuseStep 6473033 = 4854775) B4854775
theorem B8177057 : Blo 850355 8177057 := bstep (se 2 (by rfl) ⟨3066396, by rfl⟩ : syracuseStep 8177057 = 6132793) B6132793
theorem B2049455 : Blo 850355 2049455 := bstep (se 1 (by rfl) ⟨1537091, by rfl⟩ : syracuseStep 2049455 = 3074183) B3074183
theorem B3458519 : Blo 850355 3458519 := bstep (se 1 (by rfl) ⟨2593889, by rfl⟩ : syracuseStep 3458519 = 5187779) B5187779
theorem B21808763 : Blo 850355 21808763 := bstep (se 1 (by rfl) ⟨16356572, by rfl⟩ : syracuseStep 21808763 = 32713145) B32713145
theorem B1918799 : Blo 850355 1918799 := bstep (se 1 (by rfl) ⟨1439099, by rfl⟩ : syracuseStep 1918799 = 2878199) B2878199
theorem B1918817 : Blo 850355 1918817 := bstep (se 2 (by rfl) ⟨719556, by rfl⟩ : syracuseStep 1918817 = 1439113) B1439113
theorem B8407091 : Blo 850355 8407091 := bstep (se 1 (by rfl) ⟨6305318, by rfl⟩ : syracuseStep 8407091 = 12610637) B12610637
theorem B1919393 : Blo 850355 1919393 := bstep (se 2 (by rfl) ⟨719772, by rfl⟩ : syracuseStep 1919393 = 1439545) B1439545
theorem B1919519 : Blo 850355 1919519 := bstep (se 1 (by rfl) ⟨1439639, by rfl⟩ : syracuseStep 1919519 = 2879279) B2879279
theorem B2870369 : Blo 850355 2870369 := bstep (se 2 (by rfl) ⟨1076388, by rfl⟩ : syracuseStep 2870369 = 2152777) B2152777
theorem B12274811 : Blo 850355 12274811 := bstep (se 1 (by rfl) ⟨9206108, by rfl⟩ : syracuseStep 12274811 = 18412217) B18412217
theorem B9719027 : Blo 850355 9719027 := bstep (se 1 (by rfl) ⟨7289270, by rfl⟩ : syracuseStep 9719027 = 14578541) B14578541
theorem B3067319 : Blo 850355 3067319 := bstep (se 1 (by rfl) ⟨2300489, by rfl⟩ : syracuseStep 3067319 = 4600979) B4600979
theorem B5459471 : Blo 850355 5459471 := bstep (se 1 (by rfl) ⟨4094603, by rfl⟩ : syracuseStep 5459471 = 8189207) B8189207
theorem B3067465 : Blo 850355 3067465 := bstep (se 2 (by rfl) ⟨1150299, by rfl⟩ : syracuseStep 3067465 = 2300599) B2300599
theorem B8179289 : Blo 850355 8179289 := bstep (se 2 (by rfl) ⟨3067233, by rfl⟩ : syracuseStep 8179289 = 6134467) B6134467
theorem B46681697 : Blo 850355 46681697 := bstep (se 2 (by rfl) ⟨17505636, by rfl⟩ : syracuseStep 46681697 = 35011273) B35011273
theorem B2870909 : Blo 850355 2870909 := bstep (se 3 (by rfl) ⟨538295, by rfl⟩ : syracuseStep 2870909 = 1076591) B1076591
theorem B2182951 : Blo 850355 2182951 := bstep (se 1 (by rfl) ⟨1637213, by rfl⟩ : syracuseStep 2182951 = 3274427) B3274427
theorem B3067769 : Blo 850355 3067769 := bstep (se 2 (by rfl) ⟨1150413, by rfl⟩ : syracuseStep 3067769 = 2300827) B2300827
theorem B2871179 : Blo 850355 2871179 := bstep (se 1 (by rfl) ⟨2153384, by rfl⟩ : syracuseStep 2871179 = 4306769) B4306769
theorem B1920923 : Blo 850355 1920923 := bstep (se 1 (by rfl) ⟨1440692, by rfl⟩ : syracuseStep 1920923 = 2881385) B2881385
theorem B1921211 : Blo 850355 1921211 := bstep (se 1 (by rfl) ⟨1440908, by rfl⟩ : syracuseStep 1921211 = 2881817) B2881817
theorem B2871719 : Blo 850355 2871719 := bstep (se 1 (by rfl) ⟨2153789, by rfl⟩ : syracuseStep 2871719 = 4307579) B4307579
theorem B5820929 : Blo 850355 5820929 := bstep (se 2 (by rfl) ⟨2182848, by rfl⟩ : syracuseStep 5820929 = 4365697) B4365697
theorem B1921697 : Blo 850355 1921697 := bstep (se 2 (by rfl) ⟨720636, by rfl⟩ : syracuseStep 1921697 = 1441273) B1441273
theorem B4313897 : Blo 850355 4313897 := bstep (se 2 (by rfl) ⟨1617711, by rfl⟩ : syracuseStep 4313897 = 3235423) B3235423
theorem B5460803 : Blo 850355 5460803 := bstep (se 1 (by rfl) ⟨4095602, by rfl⟩ : syracuseStep 5460803 = 8191205) B8191205
theorem B18437129 : Blo 850355 18437129 := bstep (se 2 (by rfl) ⟨6913923, by rfl⟩ : syracuseStep 18437129 = 13827847) B13827847
theorem B1823753 : Blo 850355 1823753 := bstep (se 2 (by rfl) ⟨683907, by rfl⟩ : syracuseStep 1823753 = 1367815) B1367815
theorem B1922057 : Blo 850355 1922057 := bstep (se 2 (by rfl) ⟨720771, by rfl⟩ : syracuseStep 1922057 = 1441543) B1441543
theorem B1922111 : Blo 850355 1922111 := bstep (se 1 (by rfl) ⟨1441583, by rfl⟩ : syracuseStep 1922111 = 2883167) B2883167
theorem B3232979 : Blo 850355 3232979 := bstep (se 1 (by rfl) ⟨2424734, by rfl⟩ : syracuseStep 3232979 = 4849469) B4849469
theorem B10343639 : Blo 850355 10343639 := bstep (se 1 (by rfl) ⟨7757729, by rfl⟩ : syracuseStep 10343639 = 15515459) B15515459
theorem B9688409 : Blo 850355 9688409 := bstep (se 2 (by rfl) ⟨3633153, by rfl⟩ : syracuseStep 9688409 = 7266307) B7266307
theorem B28431767 : Blo 850355 28431767 := bstep (se 1 (by rfl) ⟨21323825, by rfl⟩ : syracuseStep 28431767 = 42647651) B42647651
theorem B10901101 : Blo 850355 10901101 := bstep (se 3 (by rfl) ⟨2043956, by rfl⟩ : syracuseStep 10901101 = 4087913) B4087913
theorem B2873015 : Blo 850355 2873015 := bstep (se 1 (by rfl) ⟨2154761, by rfl⟩ : syracuseStep 2873015 = 4309523) B4309523
theorem B3463127 : Blo 850355 3463127 := bstep (se 1 (by rfl) ⟨2597345, by rfl⟩ : syracuseStep 3463127 = 5194691) B5194691
theorem B1727315 : Blo 850355 1727315 := bstep (se 1 (by rfl) ⟨1295486, by rfl⟩ : syracuseStep 1727315 = 2590973) B2590973
theorem B2874203 : Blo 850355 2874203 := bstep (se 1 (by rfl) ⟨2155652, by rfl⟩ : syracuseStep 2874203 = 4311305) B4311305
theorem B3070811 : Blo 850355 3070811 := bstep (se 1 (by rfl) ⟨2303108, by rfl⟩ : syracuseStep 3070811 = 4606217) B4606217
theorem B7297883 : Blo 850355 7297883 := bstep (se 1 (by rfl) ⟨5473412, by rfl⟩ : syracuseStep 7297883 = 10946825) B10946825
theorem B5528429 : Blo 850355 5528429 := bstep (se 3 (by rfl) ⟨1036580, by rfl⟩ : syracuseStep 5528429 = 2073161) B2073161
theorem B2153375 : Blo 850355 2153375 := bstep (se 1 (by rfl) ⟨1615031, by rfl⟩ : syracuseStep 2153375 = 3230063) B3230063
theorem B5528557 : Blo 850355 5528557 := bstep (se 3 (by rfl) ⟨1036604, by rfl⟩ : syracuseStep 5528557 = 2073209) B2073209
theorem B7789625 : Blo 850355 7789625 := bstep (se 2 (by rfl) ⟨2921109, by rfl⟩ : syracuseStep 7789625 = 5842219) B5842219
theorem B1367111 : Blo 850355 1367111 := bstep (se 1 (by rfl) ⟨1025333, by rfl⟩ : syracuseStep 1367111 = 2050667) B2050667
theorem B1727671 : Blo 850355 1727671 := bstep (se 1 (by rfl) ⟨1295753, by rfl⟩ : syracuseStep 1727671 = 2591507) B2591507
theorem B3235211 : Blo 850355 3235211 := bstep (se 1 (by rfl) ⟨2426408, by rfl⟩ : syracuseStep 3235211 = 4852817) B4852817
theorem B9723401 : Blo 850355 9723401 := bstep (se 2 (by rfl) ⟨3646275, by rfl⟩ : syracuseStep 9723401 = 7292551) B7292551
theorem B2874959 : Blo 850355 2874959 := bstep (se 1 (by rfl) ⟨2156219, by rfl⟩ : syracuseStep 2874959 = 4312439) B4312439
theorem B2875067 : Blo 850355 2875067 := bstep (se 1 (by rfl) ⟨2156300, by rfl⟩ : syracuseStep 2875067 = 4312601) B4312601
theorem B24600833 : Blo 850355 24600833 := bstep (se 2 (by rfl) ⟨9225312, by rfl⟩ : syracuseStep 24600833 = 18450625) B18450625
theorem B909775 : Blo 850355 909775 := bstep (se 1 (by rfl) ⟨682331, by rfl⟩ : syracuseStep 909775 = 1364663) B1364663
theorem B1729001 : Blo 850355 1729001 := bstep (se 2 (by rfl) ⟨648375, by rfl⟩ : syracuseStep 1729001 = 1296751) B1296751
theorem B3073231 : Blo 850355 3073231 := bstep (se 1 (by rfl) ⟨2304923, by rfl⟩ : syracuseStep 3073231 = 4609847) B4609847
theorem B5465519 : Blo 850355 5465519 := bstep (se 1 (by rfl) ⟨4099139, by rfl⟩ : syracuseStep 5465519 = 8198279) B8198279
theorem B2877011 : Blo 850355 2877011 := bstep (se 1 (by rfl) ⟨2157758, by rfl⟩ : syracuseStep 2877011 = 4315517) B4315517
theorem B1435387 : Blo 850355 1435387 := bstep (se 1 (by rfl) ⟨1076540, by rfl⟩ : syracuseStep 1435387 = 2153081) B2153081
theorem B2877281 : Blo 850355 2877281 := bstep (se 2 (by rfl) ⟨1078980, by rfl⟩ : syracuseStep 2877281 = 2157961) B2157961
theorem B1435529 : Blo 850355 1435529 := bstep (se 2 (by rfl) ⟨538323, by rfl⟩ : syracuseStep 1435529 = 1076647) B1076647
theorem B1435961 : Blo 850355 1435961 := bstep (se 2 (by rfl) ⟨538485, by rfl⟩ : syracuseStep 1435961 = 1076971) B1076971
theorem B2156939 : Blo 850355 2156939 := bstep (se 1 (by rfl) ⟨1617704, by rfl⟩ : syracuseStep 2156939 = 3235409) B3235409
theorem B2877983 : Blo 850355 2877983 := bstep (se 1 (by rfl) ⟨2158487, by rfl⟩ : syracuseStep 2877983 = 4316975) B4316975
theorem B4844069 : Blo 850355 4844069 := bstep (se 4 (by rfl) ⟨454131, by rfl⟩ : syracuseStep 4844069 = 908263) B908263
theorem B1436575 : Blo 850355 1436575 := bstep (se 1 (by rfl) ⟨1077431, by rfl⟩ : syracuseStep 1436575 = 2154863) B2154863
theorem B4320377 : Blo 850355 4320377 := bstep (se 2 (by rfl) ⟨1620141, by rfl⟩ : syracuseStep 4320377 = 3240283) B3240283
theorem B1535159 : Blo 850355 1535159 := bstep (se 1 (by rfl) ⟨1151369, by rfl⟩ : syracuseStep 1535159 = 2302739) B2302739
theorem B4844843 : Blo 850355 4844843 := bstep (se 1 (by rfl) ⟨3633632, by rfl⟩ : syracuseStep 4844843 = 7267265) B7267265
theorem B1437007 : Blo 850355 1437007 := bstep (se 1 (by rfl) ⟨1077755, by rfl⟩ : syracuseStep 1437007 = 2155511) B2155511
theorem B3632471 : Blo 850355 3632471 := bstep (se 1 (by rfl) ⟨2724353, by rfl⟩ : syracuseStep 3632471 = 5448707) B5448707
theorem B1437095 : Blo 850355 1437095 := bstep (se 1 (by rfl) ⟨1077821, by rfl⟩ : syracuseStep 1437095 = 2155643) B2155643
theorem B1437257 : Blo 850355 1437257 := bstep (se 2 (by rfl) ⟨538971, by rfl⟩ : syracuseStep 1437257 = 1077943) B1077943
theorem B2879387 : Blo 850355 2879387 := bstep (se 1 (by rfl) ⟨2159540, by rfl⟩ : syracuseStep 2879387 = 4319081) B4319081
theorem B2158559 : Blo 850355 2158559 := bstep (se 1 (by rfl) ⟨1618919, by rfl⟩ : syracuseStep 2158559 = 3237839) B3237839
theorem B3633275 : Blo 850355 3633275 := bstep (se 1 (by rfl) ⟨2724956, by rfl⟩ : syracuseStep 3633275 = 5449913) B5449913
theorem B6156611 : Blo 850355 6156611 := bstep (se 1 (by rfl) ⟨4617458, by rfl⟩ : syracuseStep 6156611 = 9234917) B9234917
theorem B4321673 : Blo 850355 4321673 := bstep (se 2 (by rfl) ⟨1620627, by rfl⟩ : syracuseStep 4321673 = 3241255) B3241255
theorem B9695699 : Blo 850355 9695699 := bstep (se 1 (by rfl) ⟨7271774, by rfl⟩ : syracuseStep 9695699 = 14543549) B14543549
theorem B1438303 : Blo 850355 1438303 := bstep (se 1 (by rfl) ⟨1078727, by rfl⟩ : syracuseStep 1438303 = 2157455) B2157455
theorem B2159207 : Blo 850355 2159207 := bstep (se 1 (by rfl) ⟨1619405, by rfl⟩ : syracuseStep 2159207 = 3238811) B3238811
theorem B49246865 : Blo 850355 49246865 := bstep (se 2 (by rfl) ⟨18467574, by rfl⟩ : syracuseStep 49246865 = 36935149) B36935149
theorem B4846301 : Blo 850355 4846301 := bstep (se 3 (by rfl) ⟨908681, by rfl⟩ : syracuseStep 4846301 = 1817363) B1817363
theorem B29979395 : Blo 850355 29979395 := bstep (se 1 (by rfl) ⟨22484546, by rfl⟩ : syracuseStep 29979395 = 44969093) B44969093
theorem B94565333 : Blo 850355 94565333 := bstep (se 7 (by rfl) ⟨1108187, by rfl⟩ : syracuseStep 94565333 = 2216375) B2216375
theorem B1078267 : Blo 850355 1078267 := bstep (se 1 (by rfl) ⟨808700, by rfl⟩ : syracuseStep 1078267 = 1617401) B1617401
theorem B1438715 : Blo 850355 1438715 := bstep (se 1 (by rfl) ⟨1079036, by rfl⟩ : syracuseStep 1438715 = 2158073) B2158073
theorem B2880521 : Blo 850355 2880521 := bstep (se 2 (by rfl) ⟨1080195, by rfl⟩ : syracuseStep 2880521 = 2160391) B2160391
theorem B2880575 : Blo 850355 2880575 := bstep (se 1 (by rfl) ⟨2160431, by rfl⟩ : syracuseStep 2880575 = 4320863) B4320863
theorem B2159723 : Blo 850355 2159723 := bstep (se 1 (by rfl) ⟨1619792, by rfl⟩ : syracuseStep 2159723 = 3239585) B3239585
theorem B1439147 : Blo 850355 1439147 := bstep (se 1 (by rfl) ⟨1079360, by rfl⟩ : syracuseStep 1439147 = 2158721) B2158721
theorem B11662987 : Blo 850355 11662987 := bstep (se 1 (by rfl) ⟨8747240, by rfl⟩ : syracuseStep 11662987 = 17494481) B17494481
theorem B11826827 : Blo 850355 11826827 := bstep (se 1 (by rfl) ⟨8870120, by rfl⟩ : syracuseStep 11826827 = 17740241) B17740241
theorem B1275575 : Blo 850355 1275575 := bstep (se 1 (by rfl) ⟨956681, by rfl⟩ : syracuseStep 1275575 = 1913363) B1913363
theorem B1275611 : Blo 850355 1275611 := bstep (se 1 (by rfl) ⟨956708, by rfl⟩ : syracuseStep 1275611 = 1913417) B1913417
theorem B1275785 : Blo 850355 1275785 := bstep (se 2 (by rfl) ⟨478419, by rfl⟩ : syracuseStep 1275785 = 956839) B956839
theorem B6158227 : Blo 850355 6158227 := bstep (se 1 (by rfl) ⟨4618670, by rfl⟩ : syracuseStep 6158227 = 9237341) B9237341
theorem B1079239 : Blo 850355 1079239 := bstep (se 1 (by rfl) ⟨809429, by rfl⟩ : syracuseStep 1079239 = 1618859) B1618859
theorem B1439687 : Blo 850355 1439687 := bstep (se 1 (by rfl) ⟨1079765, by rfl⟩ : syracuseStep 1439687 = 2159531) B2159531
theorem B1275887 : Blo 850355 1275887 := bstep (se 1 (by rfl) ⟨956915, by rfl⟩ : syracuseStep 1275887 = 1913831) B1913831
theorem B4847759 : Blo 850355 4847759 := bstep (se 1 (by rfl) ⟨3635819, by rfl⟩ : syracuseStep 4847759 = 7271639) B7271639
theorem B1439977 : Blo 850355 1439977 := bstep (se 2 (by rfl) ⟨539991, by rfl⟩ : syracuseStep 1439977 = 1079983) B1079983
theorem B1276139 : Blo 850355 1276139 := bstep (se 1 (by rfl) ⟨957104, by rfl⟩ : syracuseStep 1276139 = 1914209) B1914209
theorem B1276199 : Blo 850355 1276199 := bstep (se 1 (by rfl) ⟨957149, by rfl⟩ : syracuseStep 1276199 = 1914299) B1914299
theorem B1276283 : Blo 850355 1276283 := bstep (se 1 (by rfl) ⟨957212, by rfl⟩ : syracuseStep 1276283 = 1914425) B1914425
theorem B2161019 : Blo 850355 2161019 := bstep (se 1 (by rfl) ⟨1620764, by rfl⟩ : syracuseStep 2161019 = 3241529) B3241529
theorem B850459 : Blo 850355 850459 := bstep (se 1 (by rfl) ⟨637844, by rfl⟩ : syracuseStep 850459 = 1275689) B1275689
theorem B850463 : Blo 850355 850463 := bstep (se 1 (by rfl) ⟨637847, by rfl⟩ : syracuseStep 850463 = 1275695) B1275695
theorem B1276553 : Blo 850355 1276553 := bstep (se 2 (by rfl) ⟨478707, by rfl⟩ : syracuseStep 1276553 = 957415) B957415
theorem B1440443 : Blo 850355 1440443 := bstep (se 1 (by rfl) ⟨1080332, by rfl⟩ : syracuseStep 1440443 = 2160665) B2160665
theorem B5176007 : Blo 850355 5176007 := bstep (se 1 (by rfl) ⟨3882005, by rfl⟩ : syracuseStep 5176007 = 7764011) B7764011
theorem B1276727 : Blo 850355 1276727 := bstep (se 1 (by rfl) ⟨957545, by rfl⟩ : syracuseStep 1276727 = 1915091) B1915091
theorem B850779 : Blo 850355 850779 := bstep (se 1 (by rfl) ⟨638084, by rfl⟩ : syracuseStep 850779 = 1276169) B1276169
theorem B1276763 : Blo 850355 1276763 := bstep (se 1 (by rfl) ⟨957572, by rfl⟩ : syracuseStep 1276763 = 1915145) B1915145
theorem B1080155 : Blo 850355 1080155 := bstep (se 1 (by rfl) ⟨810116, by rfl⟩ : syracuseStep 1080155 = 1620233) B1620233
theorem B850847 : Blo 850355 850847 := bstep (se 1 (by rfl) ⟨638135, by rfl⟩ : syracuseStep 850847 = 1276271) B1276271
theorem B3111887 : Blo 850355 3111887 := bstep (se 1 (by rfl) ⟨2333915, by rfl⟩ : syracuseStep 3111887 = 4667831) B4667831
theorem B1276907 : Blo 850355 1276907 := bstep (se 1 (by rfl) ⟨957680, by rfl⟩ : syracuseStep 1276907 = 1915361) B1915361
theorem B850991 : Blo 850355 850991 := bstep (se 1 (by rfl) ⟨638243, by rfl⟩ : syracuseStep 850991 = 1276487) B1276487
theorem B851015 : Blo 850355 851015 := bstep (se 1 (by rfl) ⟨638261, by rfl⟩ : syracuseStep 851015 = 1276523) B1276523
theorem B1277111 : Blo 850355 1277111 := bstep (se 1 (by rfl) ⟨957833, by rfl⟩ : syracuseStep 1277111 = 1915667) B1915667
theorem B851167 : Blo 850355 851167 := bstep (se 1 (by rfl) ⟨638375, by rfl⟩ : syracuseStep 851167 = 1276751) B1276751
theorem B46562597 : Blo 850355 46562597 := bstep (se 4 (by rfl) ⟨4365243, by rfl⟩ : syracuseStep 46562597 = 8730487) B8730487
theorem B1277351 : Blo 850355 1277351 := bstep (se 1 (by rfl) ⟨958013, by rfl⟩ : syracuseStep 1277351 = 1916027) B1916027
theorem B851431 : Blo 850355 851431 := bstep (se 1 (by rfl) ⟨638573, by rfl⟩ : syracuseStep 851431 = 1277147) B1277147
theorem B1277435 : Blo 850355 1277435 := bstep (se 1 (by rfl) ⟨958076, by rfl⟩ : syracuseStep 1277435 = 1916153) B1916153
theorem B851547 : Blo 850355 851547 := bstep (se 1 (by rfl) ⟨638660, by rfl⟩ : syracuseStep 851547 = 1277321) B1277321
theorem B1277531 : Blo 850355 1277531 := bstep (se 1 (by rfl) ⟨958148, by rfl⟩ : syracuseStep 1277531 = 1916297) B1916297
theorem B1277615 : Blo 850355 1277615 := bstep (se 1 (by rfl) ⟨958211, by rfl⟩ : syracuseStep 1277615 = 1916423) B1916423
theorem B2424563 : Blo 850355 2424563 := bstep (se 1 (by rfl) ⟨1818422, by rfl⟩ : syracuseStep 2424563 = 3636845) B3636845
theorem B1277735 : Blo 850355 1277735 := bstep (se 1 (by rfl) ⟨958301, by rfl⟩ : syracuseStep 1277735 = 1916603) B1916603
theorem B1081127 : Blo 850355 1081127 := bstep (se 1 (by rfl) ⟨810845, by rfl⟩ : syracuseStep 1081127 = 1621691) B1621691
theorem B2883383 : Blo 850355 2883383 := bstep (se 1 (by rfl) ⟨2162537, by rfl⟩ : syracuseStep 2883383 = 4325075) B4325075
theorem B851783 : Blo 850355 851783 := bstep (se 1 (by rfl) ⟨638837, by rfl⟩ : syracuseStep 851783 = 1277675) B1277675
theorem B1277819 : Blo 850355 1277819 := bstep (se 1 (by rfl) ⟨958364, by rfl⟩ : syracuseStep 1277819 = 1916729) B1916729
theorem B851935 : Blo 850355 851935 := bstep (se 1 (by rfl) ⟨638951, by rfl⟩ : syracuseStep 851935 = 1277903) B1277903
theorem B1278143 : Blo 850355 1278143 := bstep (se 1 (by rfl) ⟨958607, by rfl⟩ : syracuseStep 1278143 = 1917215) B1917215
theorem B852159 : Blo 850355 852159 := bstep (se 1 (by rfl) ⟨639119, by rfl⟩ : syracuseStep 852159 = 1278239) B1278239
theorem B852175 : Blo 850355 852175 := bstep (se 1 (by rfl) ⟨639131, by rfl⟩ : syracuseStep 852175 = 1278263) B1278263
theorem B852223 : Blo 850355 852223 := bstep (se 1 (by rfl) ⟨639167, by rfl⟩ : syracuseStep 852223 = 1278335) B1278335
theorem B852271 : Blo 850355 852271 := bstep (se 1 (by rfl) ⟨639203, by rfl⟩ : syracuseStep 852271 = 1278407) B1278407
theorem B852507 : Blo 850355 852507 := bstep (se 1 (by rfl) ⟨639380, by rfl⟩ : syracuseStep 852507 = 1278761) B1278761
theorem B852511 : Blo 850355 852511 := bstep (se 1 (by rfl) ⟨639383, by rfl⟩ : syracuseStep 852511 = 1278767) B1278767
theorem B1278569 : Blo 850355 1278569 := bstep (se 2 (by rfl) ⟨479463, by rfl⟩ : syracuseStep 1278569 = 958927) B958927
theorem B3637871 : Blo 850355 3637871 := bstep (se 1 (by rfl) ⟨2728403, by rfl⟩ : syracuseStep 3637871 = 5456807) B5456807
theorem B1278575 : Blo 850355 1278575 := bstep (se 1 (by rfl) ⟨958931, by rfl⟩ : syracuseStep 1278575 = 1917863) B1917863
theorem B852591 : Blo 850355 852591 := bstep (se 1 (by rfl) ⟨639443, by rfl⟩ : syracuseStep 852591 = 1278887) B1278887
theorem B852647 : Blo 850355 852647 := bstep (se 1 (by rfl) ⟨639485, by rfl⟩ : syracuseStep 852647 = 1278971) B1278971
theorem B852687 : Blo 850355 852687 := bstep (se 1 (by rfl) ⟨639515, by rfl⟩ : syracuseStep 852687 = 1279031) B1279031
theorem B852767 : Blo 850355 852767 := bstep (se 1 (by rfl) ⟨639575, by rfl⟩ : syracuseStep 852767 = 1279151) B1279151
theorem B853039 : Blo 850355 853039 := bstep (se 1 (by rfl) ⟨639779, by rfl⟩ : syracuseStep 853039 = 1279559) B1279559
theorem B1639531 : Blo 850355 1639531 := bstep (se 1 (by rfl) ⟨1229648, by rfl⟩ : syracuseStep 1639531 = 2459297) B2459297
theorem B853103 : Blo 850355 853103 := bstep (se 1 (by rfl) ⟨639827, by rfl⟩ : syracuseStep 853103 = 1279655) B1279655
theorem B853159 : Blo 850355 853159 := bstep (se 1 (by rfl) ⟨639869, by rfl⟩ : syracuseStep 853159 = 1279739) B1279739
theorem B853183 : Blo 850355 853183 := bstep (se 1 (by rfl) ⟨639887, by rfl⟩ : syracuseStep 853183 = 1279775) B1279775
theorem B1279199 : Blo 850355 1279199 := bstep (se 1 (by rfl) ⟨959399, by rfl⟩ : syracuseStep 1279199 = 1918799) B1918799
theorem B853215 : Blo 850355 853215 := bstep (se 1 (by rfl) ⟨639911, by rfl⟩ : syracuseStep 853215 = 1279823) B1279823
theorem B1279211 : Blo 850355 1279211 := bstep (se 1 (by rfl) ⟨959408, by rfl⟩ : syracuseStep 1279211 = 1918817) B1918817
theorem B853295 : Blo 850355 853295 := bstep (se 1 (by rfl) ⟨639971, by rfl⟩ : syracuseStep 853295 = 1279943) B1279943
theorem B2426203 : Blo 850355 2426203 := bstep (se 1 (by rfl) ⟨1819652, by rfl⟩ : syracuseStep 2426203 = 3639305) B3639305
theorem B5604727 : Blo 850355 5604727 := bstep (se 1 (by rfl) ⟨4203545, by rfl⟩ : syracuseStep 5604727 = 8407091) B8407091
theorem B853531 : Blo 850355 853531 := bstep (se 1 (by rfl) ⟨640148, by rfl⟩ : syracuseStep 853531 = 1280297) B1280297
theorem B853535 : Blo 850355 853535 := bstep (se 1 (by rfl) ⟨640151, by rfl⟩ : syracuseStep 853535 = 1280303) B1280303
theorem B12289573 : Blo 850355 12289573 := bstep (se 4 (by rfl) ⟨1152147, by rfl⟩ : syracuseStep 12289573 = 2304295) B2304295
theorem B4097641 : Blo 850355 4097641 := bstep (se 2 (by rfl) ⟨1536615, by rfl⟩ : syracuseStep 4097641 = 3073231) B3073231
theorem B1279595 : Blo 850355 1279595 := bstep (se 1 (by rfl) ⟨959696, by rfl⟩ : syracuseStep 1279595 = 1919393) B1919393
theorem B1279679 : Blo 850355 1279679 := bstep (se 1 (by rfl) ⟨959759, by rfl⟩ : syracuseStep 1279679 = 1919519) B1919519
theorem B853695 : Blo 850355 853695 := bstep (se 1 (by rfl) ⟨640271, by rfl⟩ : syracuseStep 853695 = 1280543) B1280543
theorem B1279865 : Blo 850355 1279865 := bstep (se 2 (by rfl) ⟨479949, by rfl⟩ : syracuseStep 1279865 = 959899) B959899
theorem B853951 : Blo 850355 853951 := bstep (se 1 (by rfl) ⟨640463, by rfl⟩ : syracuseStep 853951 = 1280927) B1280927
theorem B853983 : Blo 850355 853983 := bstep (se 1 (by rfl) ⟨640487, by rfl⟩ : syracuseStep 853983 = 1280975) B1280975
theorem B854043 : Blo 850355 854043 := bstep (se 1 (by rfl) ⟨640532, by rfl⟩ : syracuseStep 854043 = 1281065) B1281065
theorem B854047 : Blo 850355 854047 := bstep (se 1 (by rfl) ⟨640535, by rfl⟩ : syracuseStep 854047 = 1281071) B1281071
theorem B854063 : Blo 850355 854063 := bstep (se 1 (by rfl) ⟨640547, by rfl⟩ : syracuseStep 854063 = 1281095) B1281095
theorem B854239 : Blo 850355 854239 := bstep (se 1 (by rfl) ⟨640679, by rfl⟩ : syracuseStep 854239 = 1281359) B1281359
theorem B854299 : Blo 850355 854299 := bstep (se 1 (by rfl) ⟨640724, by rfl⟩ : syracuseStep 854299 = 1281449) B1281449
theorem B3639647 : Blo 850355 3639647 := bstep (se 1 (by rfl) ⟨2729735, by rfl⟩ : syracuseStep 3639647 = 5459471) B5459471
theorem B4852133 : Blo 850355 4852133 := bstep (se 4 (by rfl) ⟨454887, by rfl⟩ : syracuseStep 4852133 = 909775) B909775
theorem B1280615 : Blo 850355 1280615 := bstep (se 1 (by rfl) ⟨960461, by rfl⟩ : syracuseStep 1280615 = 1920923) B1920923
theorem B1280807 : Blo 850355 1280807 := bstep (se 1 (by rfl) ⟨960605, by rfl⟩ : syracuseStep 1280807 = 1921211) B1921211
theorem B1281131 : Blo 850355 1281131 := bstep (se 1 (by rfl) ⟨960848, by rfl⟩ : syracuseStep 1281131 = 1921697) B1921697
theorem B3640535 : Blo 850355 3640535 := bstep (se 1 (by rfl) ⟨2730401, by rfl⟩ : syracuseStep 3640535 = 5460803) B5460803
theorem B12291419 : Blo 850355 12291419 := bstep (se 1 (by rfl) ⟨9218564, by rfl⟩ : syracuseStep 12291419 = 18437129) B18437129
theorem B1281371 : Blo 850355 1281371 := bstep (se 1 (by rfl) ⟨961028, by rfl⟩ : syracuseStep 1281371 = 1922057) B1922057
theorem B1281401 : Blo 850355 1281401 := bstep (se 2 (by rfl) ⟨480525, by rfl⟩ : syracuseStep 1281401 = 961051) B961051
theorem B1281407 : Blo 850355 1281407 := bstep (se 1 (by rfl) ⟨961055, by rfl⟩ : syracuseStep 1281407 = 1922111) B1922111
theorem B6458939 : Blo 850355 6458939 := bstep (se 1 (by rfl) ⟨4844204, by rfl⟩ : syracuseStep 6458939 = 9688409) B9688409
theorem B14749739 : Blo 850355 14749739 := bstep (se 1 (by rfl) ⟨11062304, by rfl⟩ : syracuseStep 14749739 = 22124609) B22124609
theorem B1151543 : Blo 850355 1151543 := bstep (se 1 (by rfl) ⟨863657, by rfl⟩ : syracuseStep 1151543 = 1727315) B1727315
theorem B8000705 : Blo 850355 8000705 := bstep (se 2 (by rfl) ⟨3000264, by rfl⟩ : syracuseStep 8000705 = 6000529) B6000529
theorem B1152667 : Blo 850355 1152667 := bstep (se 1 (by rfl) ⟨864500, by rfl⟩ : syracuseStep 1152667 = 1729001) B1729001
theorem B7280765 : Blo 850355 7280765 := bstep (se 3 (by rfl) ⟨1365143, by rfl⟩ : syracuseStep 7280765 = 2730287) B2730287
theorem B3643679 : Blo 850355 3643679 := bstep (se 1 (by rfl) ⟨2732759, by rfl⟩ : syracuseStep 3643679 = 5465519) B5465519
theorem B957019 : Blo 850355 957019 := bstep (se 1 (by rfl) ⟨717764, by rfl⟩ : syracuseStep 957019 = 1435529) B1435529
theorem B957307 : Blo 850355 957307 := bstep (se 1 (by rfl) ⟨717980, by rfl⟩ : syracuseStep 957307 = 1435961) B1435961
theorem B2432207 : Blo 850355 2432207 := bstep (se 1 (by rfl) ⟨1824155, by rfl⟩ : syracuseStep 2432207 = 3648311) B3648311
theorem B958063 : Blo 850355 958063 := bstep (se 1 (by rfl) ⟨718547, by rfl⟩ : syracuseStep 958063 = 1437095) B1437095
theorem B1384103 : Blo 850355 1384103 := bstep (se 1 (by rfl) ⟨1038077, by rfl⟩ : syracuseStep 1384103 = 2076155) B2076155
theorem B2301659 : Blo 850355 2301659 := bstep (se 1 (by rfl) ⟨1726244, by rfl⟩ : syracuseStep 2301659 = 3452489) B3452489
theorem B958171 : Blo 850355 958171 := bstep (se 1 (by rfl) ⟨718628, by rfl⟩ : syracuseStep 958171 = 1437257) B1437257
theorem B12296033 : Blo 850355 12296033 := bstep (se 2 (by rfl) ⟨4611012, by rfl⟩ : syracuseStep 12296033 = 9222025) B9222025
theorem B1974127 : Blo 850355 1974127 := bstep (se 1 (by rfl) ⟨1480595, by rfl⟩ : syracuseStep 1974127 = 2961191) B2961191
theorem B4104407 : Blo 850355 4104407 := bstep (se 1 (by rfl) ⟨3078305, by rfl⟩ : syracuseStep 4104407 = 6156611) B6156611
theorem B6463799 : Blo 850355 6463799 := bstep (se 1 (by rfl) ⟨4847849, by rfl⟩ : syracuseStep 6463799 = 9695699) B9695699
theorem B959143 : Blo 850355 959143 := bstep (se 1 (by rfl) ⟨719357, by rfl⟩ : syracuseStep 959143 = 1438715) B1438715
theorem B959431 : Blo 850355 959431 := bstep (se 1 (by rfl) ⟨719573, by rfl⟩ : syracuseStep 959431 = 1439147) B1439147
theorem B959791 : Blo 850355 959791 := bstep (se 1 (by rfl) ⟨719843, by rfl⟩ : syracuseStep 959791 = 1439687) B1439687
theorem B5678629 : Blo 850355 5678629 := bstep (se 4 (by rfl) ⟨532371, by rfl⟩ : syracuseStep 5678629 = 1064743) B1064743
theorem B2303561 : Blo 850355 2303561 := bstep (se 2 (by rfl) ⟨863835, by rfl⟩ : syracuseStep 2303561 = 1727671) B1727671
theorem B960295 : Blo 850355 960295 := bstep (se 1 (by rfl) ⟨720221, by rfl⟩ : syracuseStep 960295 = 1440443) B1440443
theorem B3450671 : Blo 850355 3450671 := bstep (se 1 (by rfl) ⟨2588003, by rfl⟩ : syracuseStep 3450671 = 5176007) B5176007
theorem B3647369 : Blo 850355 3647369 := bstep (se 2 (by rfl) ⟨1367763, by rfl⟩ : syracuseStep 3647369 = 2735527) B2735527
theorem B18950071 : Blo 850355 18950071 := bstep (se 1 (by rfl) ⟨14212553, by rfl⟩ : syracuseStep 18950071 = 28425107) B28425107
theorem B2074591 : Blo 850355 2074591 := bstep (se 1 (by rfl) ⟨1555943, by rfl⟩ : syracuseStep 2074591 = 3111887) B3111887
theorem B31041731 : Blo 850355 31041731 := bstep (se 1 (by rfl) ⟨23281298, by rfl⟩ : syracuseStep 31041731 = 46562597) B46562597
theorem B5450141 : Blo 850355 5450141 := bstep (se 3 (by rfl) ⟨1021901, by rfl⟩ : syracuseStep 5450141 = 2043803) B2043803
theorem B1616375 : Blo 850355 1616375 := bstep (se 1 (by rfl) ⟨1212281, by rfl⟩ : syracuseStep 1616375 = 2424563) B2424563
theorem B1617499 : Blo 850355 1617499 := bstep (se 1 (by rfl) ⟨1213124, by rfl⟩ : syracuseStep 1617499 = 2426249) B2426249
theorem B5451371 : Blo 850355 5451371 := bstep (se 1 (by rfl) ⟨4088528, by rfl⟩ : syracuseStep 5451371 = 8177057) B8177057
theorem B2305679 : Blo 850355 2305679 := bstep (se 1 (by rfl) ⟨1729259, by rfl⟩ : syracuseStep 2305679 = 3458519) B3458519
theorem B7876261 : Blo 850355 7876261 := bstep (se 4 (by rfl) ⟨738399, by rfl⟩ : syracuseStep 7876261 = 1476799) B1476799
theorem B143699683 : Blo 850355 143699683 := bstep (se 1 (by rfl) ⟨107774762, by rfl⟩ : syracuseStep 143699683 = 215549525) B215549525
theorem B1617727 : Blo 850355 1617727 := bstep (se 1 (by rfl) ⟨1213295, by rfl⟩ : syracuseStep 1617727 = 2426591) B2426591
theorem B3682169 : Blo 850355 3682169 := bstep (se 2 (by rfl) ⟨1380813, by rfl⟩ : syracuseStep 3682169 = 2761627) B2761627
theorem B8761243 : Blo 850355 8761243 := bstep (se 1 (by rfl) ⟨6570932, by rfl⟩ : syracuseStep 8761243 = 13141865) B13141865
theorem B1913579 : Blo 850355 1913579 := bstep (se 1 (by rfl) ⟨1435184, by rfl⟩ : syracuseStep 1913579 = 2870369) B2870369
theorem B11809561 : Blo 850355 11809561 := bstep (se 2 (by rfl) ⟨4428585, by rfl⟩ : syracuseStep 11809561 = 8857171) B8857171
theorem B1913849 : Blo 850355 1913849 := bstep (se 2 (by rfl) ⟨717693, by rfl⟩ : syracuseStep 1913849 = 1435387) B1435387
theorem B5452859 : Blo 850355 5452859 := bstep (se 1 (by rfl) ⟨4089644, by rfl⟩ : syracuseStep 5452859 = 8179289) B8179289
theorem B1913939 : Blo 850355 1913939 := bstep (se 1 (by rfl) ⟨1435454, by rfl⟩ : syracuseStep 1913939 = 2870909) B2870909
theorem B2045179 : Blo 850355 2045179 := bstep (se 1 (by rfl) ⟨1533884, by rfl⟩ : syracuseStep 2045179 = 3067769) B3067769
theorem B1914119 : Blo 850355 1914119 := bstep (se 1 (by rfl) ⟨1435589, by rfl⟩ : syracuseStep 1914119 = 2871179) B2871179
theorem B4863341 : Blo 850355 4863341 := bstep (se 3 (by rfl) ⟨911876, by rfl⟩ : syracuseStep 4863341 = 1823753) B1823753
theorem B1914479 : Blo 850355 1914479 := bstep (se 1 (by rfl) ⟨1435859, by rfl⟩ : syracuseStep 1914479 = 2871719) B2871719
theorem B3880619 : Blo 850355 3880619 := bstep (se 1 (by rfl) ⟨2910464, by rfl⟩ : syracuseStep 3880619 = 5820929) B5820929
theorem B1620263 : Blo 850355 1620263 := bstep (se 1 (by rfl) ⟨1215197, by rfl⟩ : syracuseStep 1620263 = 2430395) B2430395
theorem B1915343 : Blo 850355 1915343 := bstep (se 1 (by rfl) ⟨1436507, by rfl⟩ : syracuseStep 1915343 = 2873015) B2873015
theorem B1915433 : Blo 850355 1915433 := bstep (se 2 (by rfl) ⟨718287, by rfl⟩ : syracuseStep 1915433 = 1436575) B1436575
theorem B2308751 : Blo 850355 2308751 := bstep (se 1 (by rfl) ⟨1731563, by rfl⟩ : syracuseStep 2308751 = 3463127) B3463127
theorem B139901843 : Blo 850355 139901843 := bstep (se 1 (by rfl) ⟨104926382, by rfl⟩ : syracuseStep 139901843 = 209852765) B209852765
theorem B1620947 : Blo 850355 1620947 := bstep (se 1 (by rfl) ⟨1215710, by rfl⟩ : syracuseStep 1620947 = 2431421) B2431421
theorem B1916009 : Blo 850355 1916009 := bstep (se 2 (by rfl) ⟨718503, by rfl⟩ : syracuseStep 1916009 = 1437007) B1437007
theorem B1916135 : Blo 850355 1916135 := bstep (se 1 (by rfl) ⟨1437101, by rfl⟩ : syracuseStep 1916135 = 2874203) B2874203
theorem B2047207 : Blo 850355 2047207 := bstep (se 1 (by rfl) ⟨1535405, by rfl⟩ : syracuseStep 2047207 = 3070811) B3070811
theorem B4865255 : Blo 850355 4865255 := bstep (se 1 (by rfl) ⟨3648941, by rfl⟩ : syracuseStep 4865255 = 7297883) B7297883
theorem B3685619 : Blo 850355 3685619 := bstep (se 1 (by rfl) ⟨2764214, by rfl⟩ : syracuseStep 3685619 = 5528429) B5528429
theorem B3456379 : Blo 850355 3456379 := bstep (se 1 (by rfl) ⟨2592284, by rfl⟩ : syracuseStep 3456379 = 5184569) B5184569
theorem B5193083 : Blo 850355 5193083 := bstep (se 1 (by rfl) ⟨3894812, by rfl⟩ : syracuseStep 5193083 = 7789625) B7789625
theorem B1621615 : Blo 850355 1621615 := bstep (se 1 (by rfl) ⟨1216211, by rfl⟩ : syracuseStep 1621615 = 2432423) B2432423
theorem B1916639 : Blo 850355 1916639 := bstep (se 1 (by rfl) ⟨1437479, by rfl⟩ : syracuseStep 1916639 = 2874959) B2874959
theorem B1916711 : Blo 850355 1916711 := bstep (se 1 (by rfl) ⟨1437533, by rfl⟩ : syracuseStep 1916711 = 2875067) B2875067
theorem B16400555 : Blo 850355 16400555 := bstep (se 1 (by rfl) ⟨12300416, by rfl⟩ : syracuseStep 16400555 = 24600833) B24600833
theorem B1917737 : Blo 850355 1917737 := bstep (se 2 (by rfl) ⟨719151, by rfl⟩ : syracuseStep 1917737 = 1438303) B1438303
theorem B4375547 : Blo 850355 4375547 := bstep (se 1 (by rfl) ⟨3281660, by rfl⟩ : syracuseStep 4375547 = 6563321) B6563321
theorem B1918007 : Blo 850355 1918007 := bstep (se 1 (by rfl) ⟨1438505, by rfl⟩ : syracuseStep 1918007 = 2877011) B2877011
theorem B1754335 : Blo 850355 1754335 := bstep (se 1 (by rfl) ⟨1315751, by rfl⟩ : syracuseStep 1754335 = 2631503) B2631503
theorem B16368875 : Blo 850355 16368875 := bstep (se 1 (by rfl) ⟨12276656, by rfl⟩ : syracuseStep 16368875 = 24553313) B24553313
theorem B1918187 : Blo 850355 1918187 := bstep (se 1 (by rfl) ⟨1438640, by rfl⟩ : syracuseStep 1918187 = 2877281) B2877281
theorem B1918655 : Blo 850355 1918655 := bstep (se 1 (by rfl) ⟨1438991, by rfl⟩ : syracuseStep 1918655 = 2877983) B2877983
theorem B3229379 : Blo 850355 3229379 := bstep (se 1 (by rfl) ⟨2422034, by rfl⟩ : syracuseStep 3229379 = 4844069) B4844069
theorem B14534801 : Blo 850355 14534801 := bstep (se 2 (by rfl) ⟨5450550, by rfl⟩ : syracuseStep 14534801 = 10901101) B10901101
theorem B15550649 : Blo 850355 15550649 := bstep (se 2 (by rfl) ⟨5831493, by rfl⟩ : syracuseStep 15550649 = 11662987) B11662987
theorem B3229895 : Blo 850355 3229895 := bstep (se 1 (by rfl) ⟨2422421, by rfl⟩ : syracuseStep 3229895 = 4844843) B4844843
theorem B8210969 : Blo 850355 8210969 := bstep (se 2 (by rfl) ⟨3079113, by rfl⟩ : syracuseStep 8210969 = 6158227) B6158227
theorem B1919591 : Blo 850355 1919591 := bstep (se 1 (by rfl) ⟨1439693, by rfl⟩ : syracuseStep 1919591 = 2879387) B2879387
theorem B1919969 : Blo 850355 1919969 := bstep (se 2 (by rfl) ⟨719988, by rfl⟩ : syracuseStep 1919969 = 1439977) B1439977
theorem B62311457 : Blo 850355 62311457 := bstep (se 2 (by rfl) ⟨23366796, by rfl⟩ : syracuseStep 62311457 = 46733593) B46733593
theorem B3230867 : Blo 850355 3230867 := bstep (se 1 (by rfl) ⟨2423150, by rfl⟩ : syracuseStep 3230867 = 4846301) B4846301
theorem B9096425 : Blo 850355 9096425 := bstep (se 2 (by rfl) ⟨3411159, by rfl⟩ : syracuseStep 9096425 = 6822319) B6822319
theorem B1920347 : Blo 850355 1920347 := bstep (se 1 (by rfl) ⟨1440260, by rfl⟩ : syracuseStep 1920347 = 2880521) B2880521
theorem B1920383 : Blo 850355 1920383 := bstep (se 1 (by rfl) ⟨1440287, by rfl⟩ : syracuseStep 1920383 = 2880575) B2880575
theorem B15584939 : Blo 850355 15584939 := bstep (se 1 (by rfl) ⟨11688704, by rfl⟩ : syracuseStep 15584939 = 23377409) B23377409
theorem B7884551 : Blo 850355 7884551 := bstep (se 1 (by rfl) ⟨5913413, by rfl⟩ : syracuseStep 7884551 = 11826827) B11826827
theorem B8179517 : Blo 850355 8179517 := bstep (se 3 (by rfl) ⟨1533659, by rfl⟩ : syracuseStep 8179517 = 3067319) B3067319
theorem B1822591 : Blo 850355 1822591 := bstep (se 1 (by rfl) ⟨1366943, by rfl⟩ : syracuseStep 1822591 = 2733887) B2733887
theorem B3231839 : Blo 850355 3231839 := bstep (se 1 (by rfl) ⟨2423879, by rfl⟩ : syracuseStep 3231839 = 4847759) B4847759
theorem B2872475 : Blo 850355 2872475 := bstep (se 1 (by rfl) ⟨2154356, by rfl⟩ : syracuseStep 2872475 = 4308713) B4308713
theorem B1823951 : Blo 850355 1823951 := bstep (se 1 (by rfl) ⟨1367963, by rfl⟩ : syracuseStep 1823951 = 2735927) B2735927
theorem B1922255 : Blo 850355 1922255 := bstep (se 1 (by rfl) ⟨1441691, by rfl⟩ : syracuseStep 1922255 = 2883383) B2883383
theorem B7296925 : Blo 850355 7296925 := bstep (se 3 (by rfl) ⟨1368173, by rfl⟩ : syracuseStep 7296925 = 2736347) B2736347
theorem B8738945 : Blo 850355 8738945 := bstep (se 2 (by rfl) ⟨3277104, by rfl⟩ : syracuseStep 8738945 = 6554209) B6554209
theorem B4315355 : Blo 850355 4315355 := bstep (se 1 (by rfl) ⟨3236516, by rfl⟩ : syracuseStep 4315355 = 6473033) B6473033
theorem B1366303 : Blo 850355 1366303 := bstep (se 1 (by rfl) ⟨1024727, by rfl⟩ : syracuseStep 1366303 = 2049455) B2049455
theorem B14539175 : Blo 850355 14539175 := bstep (se 1 (by rfl) ⟨10904381, by rfl⟩ : syracuseStep 14539175 = 21808763) B21808763
theorem B3889595 : Blo 850355 3889595 := bstep (se 1 (by rfl) ⟨2917196, by rfl⟩ : syracuseStep 3889595 = 5834393) B5834393
theorem B1366841 : Blo 850355 1366841 := bstep (se 2 (by rfl) ⟨512565, by rfl⟩ : syracuseStep 1366841 = 1025131) B1025131
theorem B4086607 : Blo 850355 4086607 := bstep (se 1 (by rfl) ⟨3064955, by rfl⟩ : syracuseStep 4086607 = 6129911) B6129911
theorem B8183207 : Blo 850355 8183207 := bstep (se 1 (by rfl) ⟨6137405, by rfl⟩ : syracuseStep 8183207 = 12274811) B12274811
theorem B6479351 : Blo 850355 6479351 := bstep (se 1 (by rfl) ⟨4859513, by rfl⟩ : syracuseStep 6479351 = 9719027) B9719027
theorem B31121131 : Blo 850355 31121131 := bstep (se 1 (by rfl) ⟨23340848, by rfl⟩ : syracuseStep 31121131 = 46681697) B46681697
theorem B252174221 : Blo 850355 252174221 := bstep (se 3 (by rfl) ⟨47282666, by rfl⟩ : syracuseStep 252174221 = 94565333) B94565333
theorem B266002829 : Blo 850355 266002829 := bstep (se 3 (by rfl) ⟨49875530, by rfl⟩ : syracuseStep 266002829 = 99751061) B99751061
theorem B2875931 : Blo 850355 2875931 := bstep (se 1 (by rfl) ⟨2156948, by rfl⟩ : syracuseStep 2875931 = 4313897) B4313897
theorem B27583037 : Blo 850355 27583037 := bstep (se 3 (by rfl) ⟨5171819, by rfl⟩ : syracuseStep 27583037 = 10343639) B10343639
theorem B2155319 : Blo 850355 2155319 := bstep (se 1 (by rfl) ⟨1616489, by rfl⟩ : syracuseStep 2155319 = 3232979) B3232979
theorem B4318109 : Blo 850355 4318109 := bstep (se 3 (by rfl) ⟨809645, by rfl⟩ : syracuseStep 4318109 = 1619291) B1619291
theorem B75818045 : Blo 850355 75818045 := bstep (se 3 (by rfl) ⟨14215883, by rfl⟩ : syracuseStep 75818045 = 28431767) B28431767
theorem B3237367 : Blo 850355 3237367 := bstep (se 1 (by rfl) ⟨2428025, by rfl⟩ : syracuseStep 3237367 = 4856051) B4856051
theorem B6154013 : Blo 850355 6154013 := bstep (se 3 (by rfl) ⟨1153877, by rfl⟩ : syracuseStep 6154013 = 2307755) B2307755
theorem B23357263 : Blo 850355 23357263 := bstep (se 1 (by rfl) ⟨17517947, by rfl⟩ : syracuseStep 23357263 = 35035895) B35035895
theorem B1435583 : Blo 850355 1435583 := bstep (se 1 (by rfl) ⟨1076687, by rfl⟩ : syracuseStep 1435583 = 2153375) B2153375
theorem B911407 : Blo 850355 911407 := bstep (se 1 (by rfl) ⟨683555, by rfl⟩ : syracuseStep 911407 = 1367111) B1367111
theorem B4089953 : Blo 850355 4089953 := bstep (se 2 (by rfl) ⟨1533732, by rfl⟩ : syracuseStep 4089953 = 3067465) B3067465
theorem B4090067 : Blo 850355 4090067 := bstep (se 1 (by rfl) ⟨3067550, by rfl⟩ : syracuseStep 4090067 = 6135101) B6135101
theorem B2156777 : Blo 850355 2156777 := bstep (se 2 (by rfl) ⟨808791, by rfl⟩ : syracuseStep 2156777 = 1617583) B1617583
theorem B2156807 : Blo 850355 2156807 := bstep (se 1 (by rfl) ⟨1617605, by rfl⟩ : syracuseStep 2156807 = 3235211) B3235211
theorem B6482267 : Blo 850355 6482267 := bstep (se 1 (by rfl) ⟨4861700, by rfl⟩ : syracuseStep 6482267 = 9723401) B9723401
theorem B2910601 : Blo 850355 2910601 := bstep (se 2 (by rfl) ⟨1091475, by rfl⟩ : syracuseStep 2910601 = 2182951) B2182951
theorem B5827493 : Blo 850355 5827493 := bstep (se 4 (by rfl) ⟨546327, by rfl⟩ : syracuseStep 5827493 = 1092655) B1092655
theorem B5172893 : Blo 850355 5172893 := bstep (se 3 (by rfl) ⟨969917, by rfl⟩ : syracuseStep 5172893 = 1939835) B1939835
theorem B1437689 : Blo 850355 1437689 := bstep (se 2 (by rfl) ⟨539133, by rfl⟩ : syracuseStep 1437689 = 1078267) B1078267
theorem B1437959 : Blo 850355 1437959 := bstep (se 1 (by rfl) ⟨1078469, by rfl⟩ : syracuseStep 1437959 = 2156939) B2156939
theorem B2880251 : Blo 850355 2880251 := bstep (se 1 (by rfl) ⟨2160188, by rfl⟩ : syracuseStep 2880251 = 4320377) B4320377
theorem B2159369 : Blo 850355 2159369 := bstep (se 2 (by rfl) ⟨809763, by rfl⟩ : syracuseStep 2159369 = 1619527) B1619527
theorem B2421647 : Blo 850355 2421647 := bstep (se 1 (by rfl) ⟨1816235, by rfl⟩ : syracuseStep 2421647 = 3632471) B3632471
theorem B2880413 : Blo 850355 2880413 := bstep (se 3 (by rfl) ⟨540077, by rfl⟩ : syracuseStep 2880413 = 1080155) B1080155
theorem B3241043 : Blo 850355 3241043 := bstep (se 1 (by rfl) ⟨2430782, by rfl⟩ : syracuseStep 3241043 = 4861565) B4861565
theorem B1438985 : Blo 850355 1438985 := bstep (se 2 (by rfl) ⟨539619, by rfl⟩ : syracuseStep 1438985 = 1079239) B1079239
theorem B1078591 : Blo 850355 1078591 := bstep (se 1 (by rfl) ⟨808943, by rfl⟩ : syracuseStep 1078591 = 1617887) B1617887
theorem B1439039 : Blo 850355 1439039 := bstep (se 1 (by rfl) ⟨1079279, by rfl⟩ : syracuseStep 1439039 = 2158559) B2158559
theorem B2422183 : Blo 850355 2422183 := bstep (se 1 (by rfl) ⟨1816637, by rfl⟩ : syracuseStep 2422183 = 3633275) B3633275
theorem B2881115 : Blo 850355 2881115 := bstep (se 1 (by rfl) ⟨2160836, by rfl⟩ : syracuseStep 2881115 = 4321673) B4321673
theorem B6485669 : Blo 850355 6485669 := bstep (se 4 (by rfl) ⟨608031, by rfl⟩ : syracuseStep 6485669 = 1216063) B1216063
theorem B1537769 : Blo 850355 1537769 := bstep (se 2 (by rfl) ⟨576663, by rfl⟩ : syracuseStep 1537769 = 1153327) B1153327
theorem B1439471 : Blo 850355 1439471 := bstep (se 1 (by rfl) ⟨1079603, by rfl⟩ : syracuseStep 1439471 = 2159207) B2159207
theorem B32831243 : Blo 850355 32831243 := bstep (se 1 (by rfl) ⟨24623432, by rfl⟩ : syracuseStep 32831243 = 49246865) B49246865
theorem B4093757 : Blo 850355 4093757 := bstep (se 3 (by rfl) ⟨767579, by rfl⟩ : syracuseStep 4093757 = 1535159) B1535159
theorem B19986263 : Blo 850355 19986263 := bstep (se 1 (by rfl) ⟨14989697, by rfl⟩ : syracuseStep 19986263 = 29979395) B29979395
theorem B1439815 : Blo 850355 1439815 := bstep (se 1 (by rfl) ⟨1079861, by rfl⟩ : syracuseStep 1439815 = 2159723) B2159723
theorem B850383 : Blo 850355 850383 := bstep (se 1 (by rfl) ⟨637787, by rfl⟩ : syracuseStep 850383 = 1275575) B1275575
theorem B1276367 : Blo 850355 1276367 := bstep (se 1 (by rfl) ⟨957275, by rfl⟩ : syracuseStep 1276367 = 1914551) B1914551
theorem B850407 : Blo 850355 850407 := bstep (se 1 (by rfl) ⟨637805, by rfl⟩ : syracuseStep 850407 = 1275611) B1275611
theorem B1276457 : Blo 850355 1276457 := bstep (se 2 (by rfl) ⟨478671, by rfl⟩ : syracuseStep 1276457 = 957343) B957343
theorem B850523 : Blo 850355 850523 := bstep (se 1 (by rfl) ⟨637892, by rfl⟩ : syracuseStep 850523 = 1275785) B1275785
theorem B7371409 : Blo 850355 7371409 := bstep (se 2 (by rfl) ⟨2764278, by rfl⟩ : syracuseStep 7371409 = 5528557) B5528557
theorem B850591 : Blo 850355 850591 := bstep (se 1 (by rfl) ⟨637943, by rfl⟩ : syracuseStep 850591 = 1275887) B1275887
theorem B1276649 : Blo 850355 1276649 := bstep (se 2 (by rfl) ⟨478743, by rfl⟩ : syracuseStep 1276649 = 957487) B957487
theorem B850759 : Blo 850355 850759 := bstep (se 1 (by rfl) ⟨638069, by rfl⟩ : syracuseStep 850759 = 1276139) B1276139
theorem B850799 : Blo 850355 850799 := bstep (se 1 (by rfl) ⟨638099, by rfl⟩ : syracuseStep 850799 = 1276199) B1276199
theorem B850855 : Blo 850355 850855 := bstep (se 1 (by rfl) ⟨638141, by rfl⟩ : syracuseStep 850855 = 1276283) B1276283
theorem B1440679 : Blo 850355 1440679 := bstep (se 1 (by rfl) ⟨1080509, by rfl⟩ : syracuseStep 1440679 = 2161019) B2161019
theorem B851035 : Blo 850355 851035 := bstep (se 1 (by rfl) ⟨638276, by rfl⟩ : syracuseStep 851035 = 1276553) B1276553
theorem B1277033 : Blo 850355 1277033 := bstep (se 2 (by rfl) ⟨478887, by rfl⟩ : syracuseStep 1277033 = 957775) B957775
theorem B851151 : Blo 850355 851151 := bstep (se 1 (by rfl) ⟨638363, by rfl⟩ : syracuseStep 851151 = 1276727) B1276727
theorem B851175 : Blo 850355 851175 := bstep (se 1 (by rfl) ⟨638381, by rfl⟩ : syracuseStep 851175 = 1276763) B1276763
theorem B1277159 : Blo 850355 1277159 := bstep (se 1 (by rfl) ⟨957869, by rfl⟩ : syracuseStep 1277159 = 1915739) B1915739
theorem B851271 : Blo 850355 851271 := bstep (se 1 (by rfl) ⟨638453, by rfl⟩ : syracuseStep 851271 = 1276907) B1276907
theorem B2883005 : Blo 850355 2883005 := bstep (se 3 (by rfl) ⟨540563, by rfl⟩ : syracuseStep 2883005 = 1081127) B1081127
theorem B851407 : Blo 850355 851407 := bstep (se 1 (by rfl) ⟨638555, by rfl⟩ : syracuseStep 851407 = 1277111) B1277111
theorem B851567 : Blo 850355 851567 := bstep (se 1 (by rfl) ⟨638675, by rfl⟩ : syracuseStep 851567 = 1277351) B1277351
theorem B851623 : Blo 850355 851623 := bstep (se 1 (by rfl) ⟨638717, by rfl⟩ : syracuseStep 851623 = 1277435) B1277435
theorem B1277663 : Blo 850355 1277663 := bstep (se 1 (by rfl) ⟨958247, by rfl⟩ : syracuseStep 1277663 = 1916495) B1916495
theorem B851687 : Blo 850355 851687 := bstep (se 1 (by rfl) ⟨638765, by rfl⟩ : syracuseStep 851687 = 1277531) B1277531
theorem B1277705 : Blo 850355 1277705 := bstep (se 2 (by rfl) ⟨479139, by rfl⟩ : syracuseStep 1277705 = 958279) B958279
theorem B851743 : Blo 850355 851743 := bstep (se 1 (by rfl) ⟨638807, by rfl⟩ : syracuseStep 851743 = 1277615) B1277615
theorem B31489829 : Blo 850355 31489829 := bstep (se 4 (by rfl) ⟨2952171, by rfl⟩ : syracuseStep 31489829 = 5904343) B5904343
theorem B851823 : Blo 850355 851823 := bstep (se 1 (by rfl) ⟨638867, by rfl⟩ : syracuseStep 851823 = 1277735) B1277735
theorem B851879 : Blo 850355 851879 := bstep (se 1 (by rfl) ⟨638909, by rfl⟩ : syracuseStep 851879 = 1277819) B1277819
theorem B852095 : Blo 850355 852095 := bstep (se 1 (by rfl) ⟨639071, by rfl⟩ : syracuseStep 852095 = 1278143) B1278143
theorem B852379 : Blo 850355 852379 := bstep (se 1 (by rfl) ⟨639284, by rfl⟩ : syracuseStep 852379 = 1278569) B1278569
theorem B2425247 : Blo 850355 2425247 := bstep (se 1 (by rfl) ⟨1818935, by rfl⟩ : syracuseStep 2425247 = 3637871) B3637871
theorem B852383 : Blo 850355 852383 := bstep (se 1 (by rfl) ⟨639287, by rfl⟩ : syracuseStep 852383 = 1278575) B1278575
theorem B1278491 : Blo 850355 1278491 := bstep (se 1 (by rfl) ⟨958868, by rfl⟩ : syracuseStep 1278491 = 1917737) B1917737
theorem B2917031 : Blo 850355 2917031 := bstep (se 1 (by rfl) ⟨2187773, by rfl⟩ : syracuseStep 2917031 = 4375547) B4375547
theorem B1278671 : Blo 850355 1278671 := bstep (se 1 (by rfl) ⟨959003, by rfl⟩ : syracuseStep 1278671 = 1918007) B1918007
theorem B852799 : Blo 850355 852799 := bstep (se 1 (by rfl) ⟨639599, by rfl⟩ : syracuseStep 852799 = 1279199) B1279199
theorem B10912583 : Blo 850355 10912583 := bstep (se 1 (by rfl) ⟨8184437, by rfl⟩ : syracuseStep 10912583 = 16368875) B16368875
theorem B1278791 : Blo 850355 1278791 := bstep (se 1 (by rfl) ⟨959093, by rfl⟩ : syracuseStep 1278791 = 1918187) B1918187
theorem B852807 : Blo 850355 852807 := bstep (se 1 (by rfl) ⟨639605, by rfl⟩ : syracuseStep 852807 = 1279211) B1279211
theorem B1278857 : Blo 850355 1278857 := bstep (se 2 (by rfl) ⟨479571, by rfl⟩ : syracuseStep 1278857 = 959143) B959143
theorem B853063 : Blo 850355 853063 := bstep (se 1 (by rfl) ⟨639797, by rfl⟩ : syracuseStep 853063 = 1279595) B1279595
theorem B1279103 : Blo 850355 1279103 := bstep (se 1 (by rfl) ⟨959327, by rfl⟩ : syracuseStep 1279103 = 1918655) B1918655
theorem B853119 : Blo 850355 853119 := bstep (se 1 (by rfl) ⟨639839, by rfl⟩ : syracuseStep 853119 = 1279679) B1279679
theorem B853243 : Blo 850355 853243 := bstep (se 1 (by rfl) ⟨639932, by rfl⟩ : syracuseStep 853243 = 1279865) B1279865
theorem B1279241 : Blo 850355 1279241 := bstep (se 2 (by rfl) ⟨479715, by rfl⟩ : syracuseStep 1279241 = 959431) B959431
theorem B2426431 : Blo 850355 2426431 := bstep (se 1 (by rfl) ⟨1819823, by rfl⟩ : syracuseStep 2426431 = 3639647) B3639647
theorem B5473979 : Blo 850355 5473979 := bstep (se 1 (by rfl) ⟨4105484, by rfl⟩ : syracuseStep 5473979 = 8210969) B8210969
theorem B1279721 : Blo 850355 1279721 := bstep (se 2 (by rfl) ⟨479895, by rfl⟩ : syracuseStep 1279721 = 959791) B959791
theorem B1279727 : Blo 850355 1279727 := bstep (se 1 (by rfl) ⟨959795, by rfl⟩ : syracuseStep 1279727 = 1919591) B1919591
theorem B853743 : Blo 850355 853743 := bstep (se 1 (by rfl) ⟨640307, by rfl⟩ : syracuseStep 853743 = 1280615) B1280615
theorem B7472969 : Blo 850355 7472969 := bstep (se 2 (by rfl) ⟨2802363, by rfl⟩ : syracuseStep 7472969 = 5604727) B5604727
theorem B853871 : Blo 850355 853871 := bstep (se 1 (by rfl) ⟨640403, by rfl⟩ : syracuseStep 853871 = 1280807) B1280807
theorem B1279979 : Blo 850355 1279979 := bstep (se 1 (by rfl) ⟨959984, by rfl⟩ : syracuseStep 1279979 = 1919969) B1919969
theorem B16386097 : Blo 850355 16386097 := bstep (se 2 (by rfl) ⟨6144786, by rfl⟩ : syracuseStep 16386097 = 12289573) B12289573
theorem B854087 : Blo 850355 854087 := bstep (se 1 (by rfl) ⟨640565, by rfl⟩ : syracuseStep 854087 = 1281131) B1281131
theorem B2427023 : Blo 850355 2427023 := bstep (se 1 (by rfl) ⟨1820267, by rfl⟩ : syracuseStep 2427023 = 3640535) B3640535
theorem B6064283 : Blo 850355 6064283 := bstep (se 1 (by rfl) ⟨4548212, by rfl⟩ : syracuseStep 6064283 = 9096425) B9096425
theorem B8194279 : Blo 850355 8194279 := bstep (se 1 (by rfl) ⟨6145709, by rfl⟩ : syracuseStep 8194279 = 12291419) B12291419
theorem B1280231 : Blo 850355 1280231 := bstep (se 1 (by rfl) ⟨960173, by rfl⟩ : syracuseStep 1280231 = 1920347) B1920347
theorem B854247 : Blo 850355 854247 := bstep (se 1 (by rfl) ⟨640685, by rfl⟩ : syracuseStep 854247 = 1281371) B1281371
theorem B854267 : Blo 850355 854267 := bstep (se 1 (by rfl) ⟨640700, by rfl⟩ : syracuseStep 854267 = 1281401) B1281401
theorem B1280255 : Blo 850355 1280255 := bstep (se 1 (by rfl) ⟨960191, by rfl⟩ : syracuseStep 1280255 = 1920383) B1920383
theorem B854271 : Blo 850355 854271 := bstep (se 1 (by rfl) ⟨640703, by rfl⟩ : syracuseStep 854271 = 1281407) B1281407
theorem B1280393 : Blo 850355 1280393 := bstep (se 2 (by rfl) ⟨480147, by rfl⟩ : syracuseStep 1280393 = 960295) B960295
theorem B10389959 : Blo 850355 10389959 := bstep (se 1 (by rfl) ⟨7792469, by rfl⟩ : syracuseStep 10389959 = 15584939) B15584939
theorem B25266761 : Blo 850355 25266761 := bstep (se 2 (by rfl) ⟨9475035, by rfl⟩ : syracuseStep 25266761 = 18950071) B18950071
theorem B9833159 : Blo 850355 9833159 := bstep (se 1 (by rfl) ⟨7374869, by rfl⟩ : syracuseStep 9833159 = 14749739) B14749739
theorem B1215209 : Blo 850355 1215209 := bstep (se 2 (by rfl) ⟨455703, by rfl⟩ : syracuseStep 1215209 = 911407) B911407
theorem B202181453 : Blo 850355 202181453 := bstep (se 3 (by rfl) ⟨37909022, by rfl⟩ : syracuseStep 202181453 = 75818045) B75818045
theorem B21335213 : Blo 850355 21335213 := bstep (se 3 (by rfl) ⟨4000352, by rfl⟩ : syracuseStep 21335213 = 8000705) B8000705
theorem B1215967 : Blo 850355 1215967 := bstep (se 1 (by rfl) ⟨911975, by rfl⟩ : syracuseStep 1215967 = 1823951) B1823951
theorem B1281503 : Blo 850355 1281503 := bstep (se 1 (by rfl) ⟨961127, by rfl⟩ : syracuseStep 1281503 = 1922255) B1922255
theorem B4853843 : Blo 850355 4853843 := bstep (se 1 (by rfl) ⟨3640382, by rfl⟩ : syracuseStep 4853843 = 7280765) B7280765
theorem B2429119 : Blo 850355 2429119 := bstep (se 1 (by rfl) ⟨1821839, by rfl⟩ : syracuseStep 2429119 = 3643679) B3643679
theorem B2593063 : Blo 850355 2593063 := bstep (se 1 (by rfl) ⟨1944797, by rfl⟩ : syracuseStep 2593063 = 3889595) B3889595
theorem B191599577 : Blo 850355 191599577 := bstep (se 2 (by rfl) ⟨71849841, by rfl⟩ : syracuseStep 191599577 = 143699683) B143699683
theorem B922735 : Blo 850355 922735 := bstep (se 1 (by rfl) ⟨692051, by rfl⟩ : syracuseStep 922735 = 1384103) B1384103
theorem B8197355 : Blo 850355 8197355 := bstep (se 1 (by rfl) ⟨6148016, by rfl⟩ : syracuseStep 8197355 = 12296033) B12296033
theorem B18388691 : Blo 850355 18388691 := bstep (se 1 (by rfl) ⟨13791518, by rfl⟩ : syracuseStep 18388691 = 27583037) B27583037
theorem B2300447 : Blo 850355 2300447 := bstep (se 1 (by rfl) ⟨1725335, by rfl⟩ : syracuseStep 2300447 = 3450671) B3450671
theorem B957055 : Blo 850355 957055 := bstep (se 1 (by rfl) ⟨717791, by rfl⟩ : syracuseStep 957055 = 1435583) B1435583
theorem B2726635 : Blo 850355 2726635 := bstep (se 1 (by rfl) ⟨2044976, by rfl⟩ : syracuseStep 2726635 = 4089953) B4089953
theorem B2726711 : Blo 850355 2726711 := bstep (se 1 (by rfl) ⟨2045033, by rfl⟩ : syracuseStep 2726711 = 4090067) B4090067
theorem B2726905 : Blo 850355 2726905 := bstep (se 2 (by rfl) ⟨1022589, by rfl⟩ : syracuseStep 2726905 = 2045179) B2045179
theorem B3644909 : Blo 850355 3644909 := bstep (se 3 (by rfl) ⟨683420, by rfl⟩ : syracuseStep 3644909 = 1366841) B1366841
theorem B373071581 : Blo 850355 373071581 := bstep (se 3 (by rfl) ⟨69950921, by rfl⟩ : syracuseStep 373071581 = 139901843) B139901843
theorem B3448595 : Blo 850355 3448595 := bstep (se 1 (by rfl) ⟨2586446, by rfl⟩ : syracuseStep 3448595 = 5172893) B5172893
theorem B958459 : Blo 850355 958459 := bstep (se 1 (by rfl) ⟨718844, by rfl⟩ : syracuseStep 958459 = 1437689) B1437689
theorem B958639 : Blo 850355 958639 := bstep (se 1 (by rfl) ⟨718979, by rfl⟩ : syracuseStep 958639 = 1437959) B1437959
theorem B30286021 : Blo 850355 30286021 := bstep (se 4 (by rfl) ⟨2839314, by rfl⟩ : syracuseStep 30286021 = 5678629) B5678629
theorem B1614431 : Blo 850355 1614431 := bstep (se 1 (by rfl) ⟨1210823, by rfl⟩ : syracuseStep 1614431 = 2421647) B2421647
theorem B959323 : Blo 850355 959323 := bstep (se 1 (by rfl) ⟨719492, by rfl⟩ : syracuseStep 959323 = 1438985) B1438985
theorem B959359 : Blo 850355 959359 := bstep (se 1 (by rfl) ⟨719519, by rfl⟩ : syracuseStep 959359 = 1439039) B1439039
theorem B5448809 : Blo 850355 5448809 := bstep (se 2 (by rfl) ⟨2043303, by rfl⟩ : syracuseStep 5448809 = 4086607) B4086607
theorem B1025179 : Blo 850355 1025179 := bstep (se 1 (by rfl) ⟨768884, by rfl⟩ : syracuseStep 1025179 = 1537769) B1537769
theorem B959647 : Blo 850355 959647 := bstep (se 1 (by rfl) ⟨719735, by rfl⟩ : syracuseStep 959647 = 1439471) B1439471
theorem B2729171 : Blo 850355 2729171 := bstep (se 1 (by rfl) ⟨2046878, by rfl⟩ : syracuseStep 2729171 = 4093757) B4093757
theorem B2729609 : Blo 850355 2729609 := bstep (se 2 (by rfl) ⟨1023603, by rfl⟩ : syracuseStep 2729609 = 2047207) B2047207
theorem B41494841 : Blo 850355 41494841 := bstep (se 2 (by rfl) ⟨15560565, by rfl⟩ : syracuseStep 41494841 = 31121131) B31121131
theorem B2632169 : Blo 850355 2632169 := bstep (se 2 (by rfl) ⟨987063, by rfl⟩ : syracuseStep 2632169 = 1974127) B1974127
theorem B10367099 : Blo 850355 10367099 := bstep (se 1 (by rfl) ⟨7775324, by rfl⟩ : syracuseStep 10367099 = 15550649) B15550649
theorem B2339113 : Blo 850355 2339113 := bstep (se 2 (by rfl) ⟨877167, by rfl⟩ : syracuseStep 2339113 = 1754335) B1754335
theorem B4305959 : Blo 850355 4305959 := bstep (se 1 (by rfl) ⟨3229469, by rfl⟩ : syracuseStep 4305959 = 6458939) B6458939
theorem B31143017 : Blo 850355 31143017 := bstep (se 2 (by rfl) ⟨11678631, by rfl⟩ : syracuseStep 31143017 = 23357263) B23357263
theorem B5453011 : Blo 850355 5453011 := bstep (se 1 (by rfl) ⟨4089758, by rfl⟩ : syracuseStep 5453011 = 8179517) B8179517
theorem B3880801 : Blo 850355 3880801 := bstep (se 2 (by rfl) ⟨1455300, by rfl⟩ : syracuseStep 3880801 = 2910601) B2910601
theorem B1914983 : Blo 850355 1914983 := bstep (se 1 (by rfl) ⟨1436237, by rfl⟩ : syracuseStep 1914983 = 2872475) B2872475
theorem B1621471 : Blo 850355 1621471 := bstep (se 1 (by rfl) ⟨1216103, by rfl⟩ : syracuseStep 1621471 = 2432207) B2432207
theorem B11681657 : Blo 850355 11681657 := bstep (se 2 (by rfl) ⟨4380621, by rfl⟩ : syracuseStep 11681657 = 8761243) B8761243
theorem B168116147 : Blo 850355 168116147 := bstep (se 1 (by rfl) ⟨126087110, by rfl⟩ : syracuseStep 168116147 = 252174221) B252174221
theorem B2736271 : Blo 850355 2736271 := bstep (se 1 (by rfl) ⟨2052203, by rfl⟩ : syracuseStep 2736271 = 4104407) B4104407
theorem B4309199 : Blo 850355 4309199 := bstep (se 1 (by rfl) ⟨3231899, by rfl⟩ : syracuseStep 4309199 = 6463799) B6463799
theorem B1917287 : Blo 850355 1917287 := bstep (se 1 (by rfl) ⟨1437965, by rfl⟩ : syracuseStep 1917287 = 2875931) B2875931
theorem B15746081 : Blo 850355 15746081 := bstep (se 2 (by rfl) ⟨5904780, by rfl⟩ : syracuseStep 15746081 = 11809561) B11809561
theorem B4310333 : Blo 850355 4310333 := bstep (se 3 (by rfl) ⟨808187, by rfl⟩ : syracuseStep 4310333 = 1616375) B1616375
theorem B20694487 : Blo 850355 20694487 := bstep (se 1 (by rfl) ⟨15520865, by rfl⟩ : syracuseStep 20694487 = 31041731) B31041731
theorem B3229577 : Blo 850355 3229577 := bstep (se 2 (by rfl) ⟨1211091, by rfl⟩ : syracuseStep 3229577 = 2422183) B2422183
theorem B3884995 : Blo 850355 3884995 := bstep (se 1 (by rfl) ⟨2913746, by rfl⟩ : syracuseStep 3884995 = 5827493) B5827493
theorem B1919753 : Blo 850355 1919753 := bstep (se 2 (by rfl) ⟨719907, by rfl⟩ : syracuseStep 1919753 = 1439815) B1439815
theorem B1821737 : Blo 850355 1821737 := bstep (se 2 (by rfl) ⟨683151, by rfl⟩ : syracuseStep 1821737 = 1366303) B1366303
theorem B1920167 : Blo 850355 1920167 := bstep (se 1 (by rfl) ⟨1440125, by rfl⟩ : syracuseStep 1920167 = 2880251) B2880251
theorem B1920275 : Blo 850355 1920275 := bstep (se 1 (by rfl) ⟨1440206, by rfl⟩ : syracuseStep 1920275 = 2880413) B2880413
theorem B13848221 : Blo 850355 13848221 := bstep (se 3 (by rfl) ⟨2596541, by rfl⟩ : syracuseStep 13848221 = 5193083) B5193083
theorem B1920743 : Blo 850355 1920743 := bstep (se 1 (by rfl) ⟨1440557, by rfl⟩ : syracuseStep 1920743 = 2881115) B2881115
theorem B1920905 : Blo 850355 1920905 := bstep (se 2 (by rfl) ⟨720339, by rfl⟩ : syracuseStep 1920905 = 1440679) B1440679
theorem B13324175 : Blo 850355 13324175 := bstep (se 1 (by rfl) ⟨9993131, by rfl⟩ : syracuseStep 13324175 = 19986263) B19986263
theorem B6148477 : Blo 850355 6148477 := bstep (se 3 (by rfl) ⟨1152839, by rfl⟩ : syracuseStep 6148477 = 2305679) B2305679
theorem B4608505 : Blo 850355 4608505 := bstep (se 2 (by rfl) ⟨1728189, by rfl⟩ : syracuseStep 4608505 = 3456379) B3456379
theorem B9720485 : Blo 850355 9720485 := bstep (se 4 (by rfl) ⟨911295, by rfl⟩ : syracuseStep 9720485 = 1822591) B1822591
theorem B21025469 : Blo 850355 21025469 := bstep (se 3 (by rfl) ⟨3942275, by rfl⟩ : syracuseStep 21025469 = 7884551) B7884551
theorem B1922003 : Blo 850355 1922003 := bstep (se 1 (by rfl) ⟨1441502, by rfl⟩ : syracuseStep 1922003 = 2883005) B2883005
theorem B11064485 : Blo 850355 11064485 := bstep (se 4 (by rfl) ⟨1037295, by rfl⟩ : syracuseStep 11064485 = 2074591) B2074591
theorem B20993219 : Blo 850355 20993219 := bstep (se 1 (by rfl) ⟨15744914, by rfl⟩ : syracuseStep 20993219 = 31489829) B31489829
theorem B10933703 : Blo 850355 10933703 := bstep (se 1 (by rfl) ⟨8200277, by rfl⟩ : syracuseStep 10933703 = 16400555) B16400555
theorem B2152919 : Blo 850355 2152919 := bstep (se 1 (by rfl) ⟨1614689, by rfl⟩ : syracuseStep 2152919 = 3229379) B3229379
theorem B9689867 : Blo 850355 9689867 := bstep (se 1 (by rfl) ⟨7267400, by rfl⟩ : syracuseStep 9689867 = 14534801) B14534801
theorem B2153263 : Blo 850355 2153263 := bstep (se 1 (by rfl) ⟨1614947, by rfl⟩ : syracuseStep 2153263 = 3229895) B3229895
theorem B2186041 : Blo 850355 2186041 := bstep (se 2 (by rfl) ⟨819765, by rfl⟩ : syracuseStep 2186041 = 1639531) B1639531
theorem B3070781 : Blo 850355 3070781 := bstep (se 3 (by rfl) ⟨575771, by rfl⟩ : syracuseStep 3070781 = 1151543) B1151543
theorem B3234755 : Blo 850355 3234755 := bstep (se 1 (by rfl) ⟨2426066, by rfl⟩ : syracuseStep 3234755 = 4852133) B4852133
theorem B3234937 : Blo 850355 3234937 := bstep (se 2 (by rfl) ⟨1213101, by rfl⟩ : syracuseStep 3234937 = 2426203) B2426203
theorem B4316489 : Blo 850355 4316489 := bstep (se 2 (by rfl) ⟨1618683, by rfl⟩ : syracuseStep 4316489 = 3237367) B3237367
theorem B41540971 : Blo 850355 41540971 := bstep (se 1 (by rfl) ⟨31155728, by rfl⟩ : syracuseStep 41540971 = 62311457) B62311457
theorem B2153911 : Blo 850355 2153911 := bstep (se 1 (by rfl) ⟨1615433, by rfl⟩ : syracuseStep 2153911 = 3230867) B3230867
theorem B5463521 : Blo 850355 5463521 := bstep (se 2 (by rfl) ⟨2048820, by rfl⟩ : syracuseStep 5463521 = 4097641) B4097641
theorem B2154559 : Blo 850355 2154559 := bstep (se 1 (by rfl) ⟨1615919, by rfl⟩ : syracuseStep 2154559 = 3231839) B3231839
theorem B5825963 : Blo 850355 5825963 := bstep (se 1 (by rfl) ⟨4369472, by rfl⟩ : syracuseStep 5825963 = 8738945) B8738945
theorem B2876903 : Blo 850355 2876903 := bstep (se 1 (by rfl) ⟨2157677, by rfl⟩ : syracuseStep 2876903 = 4315355) B4315355
theorem B9692783 : Blo 850355 9692783 := bstep (se 1 (by rfl) ⟨7269587, by rfl⟩ : syracuseStep 9692783 = 14539175) B14539175
theorem B16410701 : Blo 850355 16410701 := bstep (se 3 (by rfl) ⟨3077006, by rfl⟩ : syracuseStep 16410701 = 6154013) B6154013
theorem B2156665 : Blo 850355 2156665 := bstep (se 2 (by rfl) ⟨808749, by rfl⟩ : syracuseStep 2156665 = 1617499) B1617499
theorem B4319567 : Blo 850355 4319567 := bstep (se 1 (by rfl) ⟨3239675, by rfl⟩ : syracuseStep 4319567 = 6479351) B6479351
theorem B9726317 : Blo 850355 9726317 := bstep (se 3 (by rfl) ⟨1823684, by rfl⟩ : syracuseStep 9726317 = 3647369) B3647369
theorem B2156969 : Blo 850355 2156969 := bstep (se 2 (by rfl) ⟨808863, by rfl⟩ : syracuseStep 2156969 = 1617727) B1617727
theorem B1534439 : Blo 850355 1534439 := bstep (se 1 (by rfl) ⟨1150829, by rfl⟩ : syracuseStep 1534439 = 2301659) B2301659
theorem B177335219 : Blo 850355 177335219 := bstep (se 1 (by rfl) ⟨133001414, by rfl⟩ : syracuseStep 177335219 = 266002829) B266002829
theorem B1436879 : Blo 850355 1436879 := bstep (se 1 (by rfl) ⟨1077659, by rfl⟩ : syracuseStep 1436879 = 2155319) B2155319
theorem B2878739 : Blo 850355 2878739 := bstep (se 1 (by rfl) ⟨2159054, by rfl⟩ : syracuseStep 2878739 = 4318109) B4318109
theorem B4320701 : Blo 850355 4320701 := bstep (se 3 (by rfl) ⟨810131, by rfl⟩ : syracuseStep 4320701 = 1620263) B1620263
theorem B1535707 : Blo 850355 1535707 := bstep (se 1 (by rfl) ⟨1151780, by rfl⟩ : syracuseStep 1535707 = 2303561) B2303561
theorem B1437851 : Blo 850355 1437851 := bstep (se 1 (by rfl) ⟨1078388, by rfl⟩ : syracuseStep 1437851 = 2156777) B2156777
theorem B1437871 : Blo 850355 1437871 := bstep (se 1 (by rfl) ⟨1078403, by rfl⟩ : syracuseStep 1437871 = 2156807) B2156807
theorem B4321511 : Blo 850355 4321511 := bstep (se 1 (by rfl) ⟨3241133, by rfl⟩ : syracuseStep 4321511 = 6482267) B6482267
theorem B3633427 : Blo 850355 3633427 := bstep (se 1 (by rfl) ⟨2725070, by rfl⟩ : syracuseStep 3633427 = 5450141) B5450141
theorem B1438121 : Blo 850355 1438121 := bstep (se 2 (by rfl) ⟨539295, by rfl⟩ : syracuseStep 1438121 = 1078591) B1078591
theorem B1536889 : Blo 850355 1536889 := bstep (se 2 (by rfl) ⟨576333, by rfl⟩ : syracuseStep 1536889 = 1152667) B1152667
theorem B3634247 : Blo 850355 3634247 := bstep (se 1 (by rfl) ⟨2725685, by rfl⟩ : syracuseStep 3634247 = 5451371) B5451371
theorem B9729233 : Blo 850355 9729233 := bstep (se 2 (by rfl) ⟨3648462, by rfl⟩ : syracuseStep 9729233 = 7296925) B7296925
theorem B2454779 : Blo 850355 2454779 := bstep (se 1 (by rfl) ⟨1841084, by rfl⟩ : syracuseStep 2454779 = 3682169) B3682169
theorem B1275719 : Blo 850355 1275719 := bstep (se 1 (by rfl) ⟨956789, by rfl⟩ : syracuseStep 1275719 = 1913579) B1913579
theorem B1439579 : Blo 850355 1439579 := bstep (se 1 (by rfl) ⟨1079684, by rfl⟩ : syracuseStep 1439579 = 2159369) B2159369
theorem B9828317 : Blo 850355 9828317 := bstep (se 3 (by rfl) ⟨1842809, by rfl⟩ : syracuseStep 9828317 = 3685619) B3685619
theorem B1275899 : Blo 850355 1275899 := bstep (se 1 (by rfl) ⟨956924, by rfl⟩ : syracuseStep 1275899 = 1913849) B1913849
theorem B3635239 : Blo 850355 3635239 := bstep (se 1 (by rfl) ⟨2726429, by rfl⟩ : syracuseStep 3635239 = 5452859) B5452859
theorem B1275959 : Blo 850355 1275959 := bstep (se 1 (by rfl) ⟨956969, by rfl⟩ : syracuseStep 1275959 = 1913939) B1913939
theorem B2160695 : Blo 850355 2160695 := bstep (se 1 (by rfl) ⟨1620521, by rfl⟩ : syracuseStep 2160695 = 3241043) B3241043
theorem B1276025 : Blo 850355 1276025 := bstep (se 2 (by rfl) ⟨478509, by rfl⟩ : syracuseStep 1276025 = 957019) B957019
theorem B1276079 : Blo 850355 1276079 := bstep (se 1 (by rfl) ⟨957059, by rfl⟩ : syracuseStep 1276079 = 1914119) B1914119
theorem B9828545 : Blo 850355 9828545 := bstep (se 2 (by rfl) ⟨3685704, by rfl⟩ : syracuseStep 9828545 = 7371409) B7371409
theorem B42006725 : Blo 850355 42006725 := bstep (se 4 (by rfl) ⟨3938130, by rfl⟩ : syracuseStep 42006725 = 7876261) B7876261
theorem B3242227 : Blo 850355 3242227 := bstep (se 1 (by rfl) ⟨2431670, by rfl⟩ : syracuseStep 3242227 = 4863341) B4863341
theorem B1276319 : Blo 850355 1276319 := bstep (se 1 (by rfl) ⟨957239, by rfl⟩ : syracuseStep 1276319 = 1914479) B1914479
theorem B21821885 : Blo 850355 21821885 := bstep (se 3 (by rfl) ⟨4091603, by rfl⟩ : syracuseStep 21821885 = 8183207) B8183207
theorem B4323779 : Blo 850355 4323779 := bstep (se 1 (by rfl) ⟨3242834, by rfl⟩ : syracuseStep 4323779 = 6485669) B6485669
theorem B2587079 : Blo 850355 2587079 := bstep (se 1 (by rfl) ⟨1940309, by rfl⟩ : syracuseStep 2587079 = 3880619) B3880619
theorem B1276409 : Blo 850355 1276409 := bstep (se 2 (by rfl) ⟨478653, by rfl⟩ : syracuseStep 1276409 = 957307) B957307
theorem B21887495 : Blo 850355 21887495 := bstep (se 1 (by rfl) ⟨16415621, by rfl⟩ : syracuseStep 21887495 = 32831243) B32831243
theorem B850911 : Blo 850355 850911 := bstep (se 1 (by rfl) ⟨638183, by rfl⟩ : syracuseStep 850911 = 1276367) B1276367
theorem B1276895 : Blo 850355 1276895 := bstep (se 1 (by rfl) ⟨957671, by rfl⟩ : syracuseStep 1276895 = 1915343) B1915343
theorem B850971 : Blo 850355 850971 := bstep (se 1 (by rfl) ⟨638228, by rfl⟩ : syracuseStep 850971 = 1276457) B1276457
theorem B1276955 : Blo 850355 1276955 := bstep (se 1 (by rfl) ⟨957716, by rfl⟩ : syracuseStep 1276955 = 1915433) B1915433
theorem B1539167 : Blo 850355 1539167 := bstep (se 1 (by rfl) ⟨1154375, by rfl⟩ : syracuseStep 1539167 = 2308751) B2308751
theorem B851099 : Blo 850355 851099 := bstep (se 1 (by rfl) ⟨638324, by rfl⟩ : syracuseStep 851099 = 1276649) B1276649
theorem B1080631 : Blo 850355 1080631 := bstep (se 1 (by rfl) ⟨810473, by rfl⟩ : syracuseStep 1080631 = 1620947) B1620947
theorem B851355 : Blo 850355 851355 := bstep (se 1 (by rfl) ⟨638516, by rfl⟩ : syracuseStep 851355 = 1277033) B1277033
theorem B1277339 : Blo 850355 1277339 := bstep (se 1 (by rfl) ⟨958004, by rfl⟩ : syracuseStep 1277339 = 1916009) B1916009
theorem B1277417 : Blo 850355 1277417 := bstep (se 2 (by rfl) ⟨479031, by rfl⟩ : syracuseStep 1277417 = 958063) B958063
theorem B2162153 : Blo 850355 2162153 := bstep (se 2 (by rfl) ⟨810807, by rfl⟩ : syracuseStep 2162153 = 1621615) B1621615
theorem B851439 : Blo 850355 851439 := bstep (se 1 (by rfl) ⟨638579, by rfl⟩ : syracuseStep 851439 = 1277159) B1277159
theorem B1277423 : Blo 850355 1277423 := bstep (se 1 (by rfl) ⟨958067, by rfl⟩ : syracuseStep 1277423 = 1916135) B1916135
theorem B3243503 : Blo 850355 3243503 := bstep (se 1 (by rfl) ⟨2432627, by rfl⟩ : syracuseStep 3243503 = 4865255) B4865255
theorem B1277561 : Blo 850355 1277561 := bstep (se 2 (by rfl) ⟨479085, by rfl⟩ : syracuseStep 1277561 = 958171) B958171
theorem B851775 : Blo 850355 851775 := bstep (se 1 (by rfl) ⟨638831, by rfl⟩ : syracuseStep 851775 = 1277663) B1277663
theorem B1277759 : Blo 850355 1277759 := bstep (se 1 (by rfl) ⟨958319, by rfl⟩ : syracuseStep 1277759 = 1916639) B1916639
theorem B851803 : Blo 850355 851803 := bstep (se 1 (by rfl) ⟨638852, by rfl⟩ : syracuseStep 851803 = 1277705) B1277705
theorem B1277807 : Blo 850355 1277807 := bstep (se 1 (by rfl) ⟨958355, by rfl⟩ : syracuseStep 1277807 = 1916711) B1916711
theorem B1278185 : Blo 850355 1278185 := bstep (se 2 (by rfl) ⟨479319, by rfl⟩ : syracuseStep 1278185 = 958639) B958639
theorem B1278191 : Blo 850355 1278191 := bstep (se 1 (by rfl) ⟨958643, by rfl⟩ : syracuseStep 1278191 = 1917287) B1917287
theorem B852327 : Blo 850355 852327 := bstep (se 1 (by rfl) ⟨639245, by rfl⟩ : syracuseStep 852327 = 1278491) B1278491
theorem B852447 : Blo 850355 852447 := bstep (se 1 (by rfl) ⟨639335, by rfl⟩ : syracuseStep 852447 = 1278671) B1278671
theorem B7275055 : Blo 850355 7275055 := bstep (se 1 (by rfl) ⟨5456291, by rfl⟩ : syracuseStep 7275055 = 10912583) B10912583
theorem B852527 : Blo 850355 852527 := bstep (se 1 (by rfl) ⟨639395, by rfl⟩ : syracuseStep 852527 = 1278791) B1278791
theorem B852571 : Blo 850355 852571 := bstep (se 1 (by rfl) ⟨639428, by rfl⟩ : syracuseStep 852571 = 1278857) B1278857
theorem B852735 : Blo 850355 852735 := bstep (se 1 (by rfl) ⟨639551, by rfl⟩ : syracuseStep 852735 = 1279103) B1279103
theorem B852827 : Blo 850355 852827 := bstep (se 1 (by rfl) ⟨639620, by rfl⟩ : syracuseStep 852827 = 1279241) B1279241
theorem B1279097 : Blo 850355 1279097 := bstep (se 2 (by rfl) ⟨479661, by rfl⟩ : syracuseStep 1279097 = 959323) B959323
theorem B853147 : Blo 850355 853147 := bstep (se 1 (by rfl) ⟨639860, by rfl⟩ : syracuseStep 853147 = 1279721) B1279721
theorem B853151 : Blo 850355 853151 := bstep (se 1 (by rfl) ⟨639863, by rfl⟩ : syracuseStep 853151 = 1279727) B1279727
theorem B1279145 : Blo 850355 1279145 := bstep (se 2 (by rfl) ⟨479679, by rfl⟩ : syracuseStep 1279145 = 959359) B959359
theorem B4981979 : Blo 850355 4981979 := bstep (se 1 (by rfl) ⟨3736484, by rfl⟩ : syracuseStep 4981979 = 7472969) B7472969
theorem B853319 : Blo 850355 853319 := bstep (se 1 (by rfl) ⟨639989, by rfl⟩ : syracuseStep 853319 = 1279979) B1279979
theorem B853487 : Blo 850355 853487 := bstep (se 1 (by rfl) ⟨640115, by rfl⟩ : syracuseStep 853487 = 1280231) B1280231
theorem B853503 : Blo 850355 853503 := bstep (se 1 (by rfl) ⟨640127, by rfl⟩ : syracuseStep 853503 = 1280255) B1280255
theorem B1279529 : Blo 850355 1279529 := bstep (se 2 (by rfl) ⟨479823, by rfl⟩ : syracuseStep 1279529 = 959647) B959647
theorem B853595 : Blo 850355 853595 := bstep (se 1 (by rfl) ⟨640196, by rfl⟩ : syracuseStep 853595 = 1280393) B1280393
theorem B16844507 : Blo 850355 16844507 := bstep (se 1 (by rfl) ⟨12633380, by rfl⟩ : syracuseStep 16844507 = 25266761) B25266761
theorem B6555439 : Blo 850355 6555439 := bstep (se 1 (by rfl) ⟨4916579, by rfl⟩ : syracuseStep 6555439 = 9833159) B9833159
theorem B1279835 : Blo 850355 1279835 := bstep (se 1 (by rfl) ⟨959876, by rfl⟩ : syracuseStep 1279835 = 1919753) B1919753
theorem B27592649 : Blo 850355 27592649 := bstep (se 2 (by rfl) ⟨10347243, by rfl⟩ : syracuseStep 27592649 = 20694487) B20694487
theorem B1280111 : Blo 850355 1280111 := bstep (se 1 (by rfl) ⟨960083, by rfl⟩ : syracuseStep 1280111 = 1920167) B1920167
theorem B14223475 : Blo 850355 14223475 := bstep (se 1 (by rfl) ⟨10667606, by rfl⟩ : syracuseStep 14223475 = 21335213) B21335213
theorem B1280183 : Blo 850355 1280183 := bstep (se 1 (by rfl) ⟨960137, by rfl⟩ : syracuseStep 1280183 = 1920275) B1920275
theorem B854335 : Blo 850355 854335 := bstep (se 1 (by rfl) ⟨640751, by rfl⟩ : syracuseStep 854335 = 1281503) B1281503
theorem B1280495 : Blo 850355 1280495 := bstep (se 1 (by rfl) ⟨960371, by rfl⟩ : syracuseStep 1280495 = 1920743) B1920743
theorem B5179993 : Blo 850355 5179993 := bstep (se 2 (by rfl) ⟨1942497, by rfl⟩ : syracuseStep 5179993 = 3884995) B3884995
theorem B1280603 : Blo 850355 1280603 := bstep (se 1 (by rfl) ⟨960452, by rfl⟩ : syracuseStep 1280603 = 1920905) B1920905
theorem B8882783 : Blo 850355 8882783 := bstep (se 1 (by rfl) ⟨6662087, by rfl⟩ : syracuseStep 8882783 = 13324175) B13324175
theorem B7277789 : Blo 850355 7277789 := bstep (se 3 (by rfl) ⟨1364585, by rfl⟩ : syracuseStep 7277789 = 2729171) B2729171
theorem B1281335 : Blo 850355 1281335 := bstep (se 1 (by rfl) ⟨961001, by rfl⟩ : syracuseStep 1281335 = 1922003) B1922003
theorem B127733051 : Blo 850355 127733051 := bstep (se 1 (by rfl) ⟨95799788, by rfl⟩ : syracuseStep 127733051 = 191599577) B191599577
theorem B13995479 : Blo 850355 13995479 := bstep (se 1 (by rfl) ⟨10496609, by rfl⟩ : syracuseStep 13995479 = 20993219) B20993219
theorem B15535901 : Blo 850355 15535901 := bstep (se 3 (by rfl) ⟨2912981, by rfl⟩ : syracuseStep 15535901 = 5825963) B5825963
theorem B12259127 : Blo 850355 12259127 := bstep (se 1 (by rfl) ⟨9194345, by rfl⟩ : syracuseStep 12259127 = 18388691) B18388691
theorem B6459911 : Blo 850355 6459911 := bstep (se 1 (by rfl) ⟨4844933, by rfl⟩ : syracuseStep 6459911 = 9689867) B9689867
theorem B3642347 : Blo 850355 3642347 := bstep (se 1 (by rfl) ⟨2731760, by rfl⟩ : syracuseStep 3642347 = 5463521) B5463521
theorem B2429939 : Blo 850355 2429939 := bstep (se 1 (by rfl) ⟨1822454, by rfl⟩ : syracuseStep 2429939 = 3644909) B3644909
theorem B248714387 : Blo 850355 248714387 := bstep (se 1 (by rfl) ⟨186535790, by rfl⟩ : syracuseStep 248714387 = 373071581) B373071581
theorem B3118817 : Blo 850355 3118817 := bstep (se 2 (by rfl) ⟨1169556, by rfl⟩ : syracuseStep 3118817 = 2339113) B2339113
theorem B6461855 : Blo 850355 6461855 := bstep (se 1 (by rfl) ⟨4846391, by rfl⟩ : syracuseStep 6461855 = 9692783) B9692783
theorem B6134525 : Blo 850355 6134525 := bstep (se 3 (by rfl) ⟨1150223, by rfl⟩ : syracuseStep 6134525 = 2300447) B2300447
theorem B27663227 : Blo 850355 27663227 := bstep (se 1 (by rfl) ⟨20747420, by rfl⟩ : syracuseStep 27663227 = 41494841) B41494841
theorem B1022959 : Blo 850355 1022959 := bstep (se 1 (by rfl) ⟨767219, by rfl⟩ : syracuseStep 1022959 = 1534439) B1534439
theorem B957919 : Blo 850355 957919 := bstep (se 1 (by rfl) ⟨718439, by rfl⟩ : syracuseStep 957919 = 1436879) B1436879
theorem B958567 : Blo 850355 958567 := bstep (se 1 (by rfl) ⟨718925, by rfl⟩ : syracuseStep 958567 = 1437851) B1437851
theorem B4857965 : Blo 850355 4857965 := bstep (se 3 (by rfl) ⟨910868, by rfl⟩ : syracuseStep 4857965 = 1821737) B1821737
theorem B4104445 : Blo 850355 4104445 := bstep (se 3 (by rfl) ⟨769583, by rfl⟩ : syracuseStep 4104445 = 1539167) B1539167
theorem B958747 : Blo 850355 958747 := bstep (se 1 (by rfl) ⟨719060, by rfl⟩ : syracuseStep 958747 = 1438121) B1438121
theorem B959719 : Blo 850355 959719 := bstep (se 1 (by rfl) ⟨719789, by rfl⟩ : syracuseStep 959719 = 1439579) B1439579
theorem B14591663 : Blo 850355 14591663 := bstep (se 1 (by rfl) ⟨10943747, by rfl⟩ : syracuseStep 14591663 = 21887495) B21887495
theorem B55387961 : Blo 850355 55387961 := bstep (se 2 (by rfl) ⟨20770485, by rfl⟩ : syracuseStep 55387961 = 41540971) B41540971
theorem B112077431 : Blo 850355 112077431 := bstep (se 1 (by rfl) ⟨84058073, by rfl⟩ : syracuseStep 112077431 = 168116147) B168116147
theorem B3648361 : Blo 850355 3648361 := bstep (se 2 (by rfl) ⟨1368135, by rfl⟩ : syracuseStep 3648361 = 2736271) B2736271
theorem B40381361 : Blo 850355 40381361 := bstep (se 2 (by rfl) ⟨15143010, by rfl⟩ : syracuseStep 40381361 = 30286021) B30286021
theorem B1616831 : Blo 850355 1616831 := bstep (se 1 (by rfl) ⟨1212623, by rfl⟩ : syracuseStep 1616831 = 2425247) B2425247
theorem B3649319 : Blo 850355 3649319 := bstep (se 1 (by rfl) ⟨2736989, by rfl⟩ : syracuseStep 3649319 = 5473979) B5473979
theorem B4042855 : Blo 850355 4042855 := bstep (se 1 (by rfl) ⟨3032141, by rfl⟩ : syracuseStep 4042855 = 6064283) B6064283
theorem B4305149 : Blo 850355 4305149 := bstep (se 3 (by rfl) ⟨807215, by rfl⟩ : syracuseStep 4305149 = 1614431) B1614431
theorem B6926639 : Blo 850355 6926639 := bstep (se 1 (by rfl) ⟨5194979, by rfl⟩ : syracuseStep 6926639 = 10389959) B10389959
theorem B7778749 : Blo 850355 7778749 := bstep (se 3 (by rfl) ⟨1458515, by rfl⟩ : syracuseStep 7778749 = 2917031) B2917031
theorem B134787635 : Blo 850355 134787635 := bstep (se 1 (by rfl) ⟨101090726, by rfl⟩ : syracuseStep 134787635 = 202181453) B202181453
theorem B10925705 : Blo 850355 10925705 := bstep (se 2 (by rfl) ⟨4097139, by rfl⟩ : syracuseStep 10925705 = 8194279) B8194279
theorem B29505293 : Blo 850355 29505293 := bstep (se 3 (by rfl) ⟨5532242, by rfl⟩ : syracuseStep 29505293 = 11064485) B11064485
theorem B7289135 : Blo 850355 7289135 := bstep (se 1 (by rfl) ⟨5466851, by rfl⟩ : syracuseStep 7289135 = 10933703) B10933703
theorem B1817807 : Blo 850355 1817807 := bstep (se 1 (by rfl) ⟨1363355, by rfl⟩ : syracuseStep 1817807 = 2726711) B2726711
theorem B2047187 : Blo 850355 2047187 := bstep (se 1 (by rfl) ⟨1535390, by rfl⟩ : syracuseStep 2047187 = 3070781) B3070781
theorem B1621289 : Blo 850355 1621289 := bstep (se 2 (by rfl) ⟨607983, by rfl⟩ : syracuseStep 1621289 = 1215967) B1215967
theorem B2047609 : Blo 850355 2047609 := bstep (se 2 (by rfl) ⟨767853, by rfl⟩ : syracuseStep 2047609 = 1535707) B1535707
theorem B1917161 : Blo 850355 1917161 := bstep (se 2 (by rfl) ⟨718935, by rfl⟩ : syracuseStep 1917161 = 1437871) B1437871
theorem B6472061 : Blo 850355 6472061 := bstep (se 3 (by rfl) ⟨1213511, by rfl⟩ : syracuseStep 6472061 = 2427023) B2427023
theorem B3457417 : Blo 850355 3457417 := bstep (se 2 (by rfl) ⟨1296531, by rfl⟩ : syracuseStep 3457417 = 2593063) B2593063
theorem B6144673 : Blo 850355 6144673 := bstep (se 2 (by rfl) ⟨2304252, by rfl⟩ : syracuseStep 6144673 = 4608505) B4608505
theorem B1917935 : Blo 850355 1917935 := bstep (se 1 (by rfl) ⟨1438451, by rfl⟩ : syracuseStep 1917935 = 2876903) B2876903
theorem B1819739 : Blo 850355 1819739 := bstep (se 1 (by rfl) ⟨1364804, by rfl⟩ : syracuseStep 1819739 = 2729609) B2729609
theorem B2049185 : Blo 850355 2049185 := bstep (se 2 (by rfl) ⟨768444, by rfl⟩ : syracuseStep 2049185 = 1536889) B1536889
theorem B6898877 : Blo 850355 6898877 := bstep (se 3 (by rfl) ⟨1293539, by rfl⟩ : syracuseStep 6898877 = 2587079) B2587079
theorem B1230313 : Blo 850355 1230313 := bstep (se 2 (by rfl) ⟨461367, by rfl⟩ : syracuseStep 1230313 = 922735) B922735
theorem B1754779 : Blo 850355 1754779 := bstep (se 1 (by rfl) ⟨1316084, by rfl⟩ : syracuseStep 1754779 = 2632169) B2632169
theorem B1919159 : Blo 850355 1919159 := bstep (se 1 (by rfl) ⟨1439369, by rfl⟩ : syracuseStep 1919159 = 2878739) B2878739
theorem B2870639 : Blo 850355 2870639 := bstep (se 1 (by rfl) ⟨2152979, by rfl⟩ : syracuseStep 2870639 = 4305959) B4305959
theorem B20762011 : Blo 850355 20762011 := bstep (se 1 (by rfl) ⟨15571508, by rfl⟩ : syracuseStep 20762011 = 31143017) B31143017
theorem B2871017 : Blo 850355 2871017 := bstep (se 2 (by rfl) ⟨1076631, by rfl⟩ : syracuseStep 2871017 = 2153263) B2153263
theorem B28004483 : Blo 850355 28004483 := bstep (se 1 (by rfl) ⟨21003362, by rfl⟩ : syracuseStep 28004483 = 42006725) B42006725
theorem B4313249 : Blo 850355 4313249 := bstep (se 2 (by rfl) ⟨1617468, by rfl⟩ : syracuseStep 4313249 = 3234937) B3234937
theorem B2871881 : Blo 850355 2871881 := bstep (se 2 (by rfl) ⟨1076955, by rfl⟩ : syracuseStep 2871881 = 2153911) B2153911
theorem B9196253 : Blo 850355 9196253 := bstep (se 3 (by rfl) ⟨1724297, by rfl⟩ : syracuseStep 9196253 = 3448595) B3448595
theorem B7787771 : Blo 850355 7787771 := bstep (se 1 (by rfl) ⟨5840828, by rfl⟩ : syracuseStep 7787771 = 11681657) B11681657
theorem B2872745 : Blo 850355 2872745 := bstep (se 2 (by rfl) ⟨1077279, by rfl⟩ : syracuseStep 2872745 = 2154559) B2154559
theorem B2872799 : Blo 850355 2872799 := bstep (se 1 (by rfl) ⟨2154599, by rfl⟩ : syracuseStep 2872799 = 4309199) B4309199
theorem B167958197 : Blo 850355 167958197 := bstep (se 5 (by rfl) ⟨7873040, by rfl⟩ : syracuseStep 167958197 = 15746081) B15746081
theorem B2873555 : Blo 850355 2873555 := bstep (se 1 (by rfl) ⟨2155166, by rfl⟩ : syracuseStep 2873555 = 4310333) B4310333
theorem B2153051 : Blo 850355 2153051 := bstep (se 1 (by rfl) ⟨1614788, by rfl⟩ : syracuseStep 2153051 = 3229577) B3229577
theorem B32791877 : Blo 850355 32791877 := bstep (se 4 (by rfl) ⟨3074238, by rfl⟩ : syracuseStep 32791877 = 6148477) B6148477
theorem B3235241 : Blo 850355 3235241 := bstep (se 2 (by rfl) ⟨1213215, by rfl⟩ : syracuseStep 3235241 = 2426431) B2426431
theorem B9232147 : Blo 850355 9232147 := bstep (se 1 (by rfl) ⟨6924110, by rfl⟩ : syracuseStep 9232147 = 13848221) B13848221
theorem B3235895 : Blo 850355 3235895 := bstep (se 1 (by rfl) ⟨2426921, by rfl⟩ : syracuseStep 3235895 = 4853843) B4853843
theorem B21848129 : Blo 850355 21848129 := bstep (se 2 (by rfl) ⟨8193048, by rfl⟩ : syracuseStep 21848129 = 16386097) B16386097
theorem B2875553 : Blo 850355 2875553 := bstep (se 2 (by rfl) ⟨1078332, by rfl⟩ : syracuseStep 2875553 = 2156665) B2156665
theorem B9691325 : Blo 850355 9691325 := bstep (se 3 (by rfl) ⟨1817123, by rfl⟩ : syracuseStep 9691325 = 3634247) B3634247
theorem B6480323 : Blo 850355 6480323 := bstep (se 1 (by rfl) ⟨4860242, by rfl⟩ : syracuseStep 6480323 = 9720485) B9720485
theorem B14016979 : Blo 850355 14016979 := bstep (se 1 (by rfl) ⟨10512734, by rfl⟩ : syracuseStep 14016979 = 21025469) B21025469
theorem B6546077 : Blo 850355 6546077 := bstep (se 3 (by rfl) ⟨1227389, by rfl⟩ : syracuseStep 6546077 = 2454779) B2454779
theorem B5464903 : Blo 850355 5464903 := bstep (se 1 (by rfl) ⟨4098677, by rfl⟩ : syracuseStep 5464903 = 8197355) B8197355
theorem B1435279 : Blo 850355 1435279 := bstep (se 1 (by rfl) ⟨1076459, by rfl⟩ : syracuseStep 1435279 = 2152919) B2152919
theorem B2156503 : Blo 850355 2156503 := bstep (se 1 (by rfl) ⟨1617377, by rfl⟩ : syracuseStep 2156503 = 3234755) B3234755
theorem B2877659 : Blo 850355 2877659 := bstep (se 1 (by rfl) ⟨2158244, by rfl⟩ : syracuseStep 2877659 = 4316489) B4316489
theorem B3238825 : Blo 850355 3238825 := bstep (se 2 (by rfl) ⟨1214559, by rfl⟩ : syracuseStep 3238825 = 2429119) B2429119
theorem B4844569 : Blo 850355 4844569 := bstep (se 2 (by rfl) ⟨1816713, by rfl⟩ : syracuseStep 4844569 = 3633427) B3633427
theorem B26209453 : Blo 850355 26209453 := bstep (se 3 (by rfl) ⟨4914272, by rfl⟩ : syracuseStep 26209453 = 9828545) B9828545
theorem B3632539 : Blo 850355 3632539 := bstep (se 1 (by rfl) ⟨2724404, by rfl⟩ : syracuseStep 3632539 = 5448809) B5448809
theorem B5467621 : Blo 850355 5467621 := bstep (se 4 (by rfl) ⟨512589, by rfl⟩ : syracuseStep 5467621 = 1025179) B1025179
theorem B10940467 : Blo 850355 10940467 := bstep (se 1 (by rfl) ⟨8205350, by rfl⟩ : syracuseStep 10940467 = 16410701) B16410701
theorem B2879711 : Blo 850355 2879711 := bstep (se 1 (by rfl) ⟨2159783, by rfl⟩ : syracuseStep 2879711 = 4319567) B4319567
theorem B6484211 : Blo 850355 6484211 := bstep (se 1 (by rfl) ⟨4863158, by rfl⟩ : syracuseStep 6484211 = 9726317) B9726317
theorem B7270681 : Blo 850355 7270681 := bstep (se 2 (by rfl) ⟨2726505, by rfl⟩ : syracuseStep 7270681 = 5453011) B5453011
theorem B1437979 : Blo 850355 1437979 := bstep (se 1 (by rfl) ⟨1078484, by rfl⟩ : syracuseStep 1437979 = 2156969) B2156969
theorem B3240557 : Blo 850355 3240557 := bstep (se 3 (by rfl) ⟨607604, by rfl⟩ : syracuseStep 3240557 = 1215209) B1215209
theorem B118223479 : Blo 850355 118223479 := bstep (se 1 (by rfl) ⟨88667609, by rfl⟩ : syracuseStep 118223479 = 177335219) B177335219
theorem B2880467 : Blo 850355 2880467 := bstep (se 1 (by rfl) ⟨2160350, by rfl⟩ : syracuseStep 2880467 = 4320701) B4320701
theorem B5174401 : Blo 850355 5174401 := bstep (se 2 (by rfl) ⟨1940400, by rfl⟩ : syracuseStep 5174401 = 3880801) B3880801
theorem B4846985 : Blo 850355 4846985 := bstep (se 2 (by rfl) ⟨1817619, by rfl⟩ : syracuseStep 4846985 = 3635239) B3635239
theorem B6911399 : Blo 850355 6911399 := bstep (se 1 (by rfl) ⟨5183549, by rfl⟩ : syracuseStep 6911399 = 10367099) B10367099
theorem B2881007 : Blo 850355 2881007 := bstep (se 1 (by rfl) ⟨2160755, by rfl⟩ : syracuseStep 2881007 = 4321511) B4321511
theorem B4322969 : Blo 850355 4322969 := bstep (se 2 (by rfl) ⟨1621113, by rfl⟩ : syracuseStep 4322969 = 3242227) B3242227
theorem B6486155 : Blo 850355 6486155 := bstep (se 1 (by rfl) ⟨4864616, by rfl⟩ : syracuseStep 6486155 = 9729233) B9729233
theorem B1276073 : Blo 850355 1276073 := bstep (se 2 (by rfl) ⟨478527, by rfl⟩ : syracuseStep 1276073 = 957055) B957055
theorem B3635513 : Blo 850355 3635513 := bstep (se 2 (by rfl) ⟨1363317, by rfl⟩ : syracuseStep 3635513 = 2726635) B2726635
theorem B2914721 : Blo 850355 2914721 := bstep (se 2 (by rfl) ⟨1093020, by rfl⟩ : syracuseStep 2914721 = 2186041) B2186041
theorem B850479 : Blo 850355 850479 := bstep (se 1 (by rfl) ⟨637859, by rfl⟩ : syracuseStep 850479 = 1275719) B1275719
theorem B6552211 : Blo 850355 6552211 := bstep (se 1 (by rfl) ⟨4914158, by rfl⟩ : syracuseStep 6552211 = 9828317) B9828317
theorem B3635873 : Blo 850355 3635873 := bstep (se 2 (by rfl) ⟨1363452, by rfl⟩ : syracuseStep 3635873 = 2726905) B2726905
theorem B850599 : Blo 850355 850599 := bstep (se 1 (by rfl) ⟨637949, by rfl⟩ : syracuseStep 850599 = 1275899) B1275899
theorem B850639 : Blo 850355 850639 := bstep (se 1 (by rfl) ⟨637979, by rfl⟩ : syracuseStep 850639 = 1275959) B1275959
theorem B1440463 : Blo 850355 1440463 := bstep (se 1 (by rfl) ⟨1080347, by rfl⟩ : syracuseStep 1440463 = 2160695) B2160695
theorem B1276655 : Blo 850355 1276655 := bstep (se 1 (by rfl) ⟨957491, by rfl⟩ : syracuseStep 1276655 = 1914983) B1914983
theorem B850683 : Blo 850355 850683 := bstep (se 1 (by rfl) ⟨638012, by rfl⟩ : syracuseStep 850683 = 1276025) B1276025
theorem B850719 : Blo 850355 850719 := bstep (se 1 (by rfl) ⟨638039, by rfl⟩ : syracuseStep 850719 = 1276079) B1276079
theorem B850879 : Blo 850355 850879 := bstep (se 1 (by rfl) ⟨638159, by rfl⟩ : syracuseStep 850879 = 1276319) B1276319
theorem B14547923 : Blo 850355 14547923 := bstep (se 1 (by rfl) ⟨10910942, by rfl⟩ : syracuseStep 14547923 = 21821885) B21821885
theorem B2882519 : Blo 850355 2882519 := bstep (se 1 (by rfl) ⟨2161889, by rfl⟩ : syracuseStep 2882519 = 4323779) B4323779
theorem B850939 : Blo 850355 850939 := bstep (se 1 (by rfl) ⟨638204, by rfl⟩ : syracuseStep 850939 = 1276409) B1276409
theorem B1440841 : Blo 850355 1440841 := bstep (se 2 (by rfl) ⟨540315, by rfl⟩ : syracuseStep 1440841 = 1080631) B1080631
theorem B2161961 : Blo 850355 2161961 := bstep (se 2 (by rfl) ⟨810735, by rfl⟩ : syracuseStep 2161961 = 1621471) B1621471
theorem B851263 : Blo 850355 851263 := bstep (se 1 (by rfl) ⟨638447, by rfl⟩ : syracuseStep 851263 = 1276895) B1276895
theorem B851303 : Blo 850355 851303 := bstep (se 1 (by rfl) ⟨638477, by rfl⟩ : syracuseStep 851303 = 1276955) B1276955
theorem B851559 : Blo 850355 851559 := bstep (se 1 (by rfl) ⟨638669, by rfl⟩ : syracuseStep 851559 = 1277339) B1277339
theorem B851611 : Blo 850355 851611 := bstep (se 1 (by rfl) ⟨638708, by rfl⟩ : syracuseStep 851611 = 1277417) B1277417
theorem B1441435 : Blo 850355 1441435 := bstep (se 1 (by rfl) ⟨1081076, by rfl⟩ : syracuseStep 1441435 = 2162153) B2162153
theorem B851615 : Blo 850355 851615 := bstep (se 1 (by rfl) ⟨638711, by rfl⟩ : syracuseStep 851615 = 1277423) B1277423
theorem B2162335 : Blo 850355 2162335 := bstep (se 1 (by rfl) ⟨1621751, by rfl⟩ : syracuseStep 2162335 = 3243503) B3243503
theorem B851707 : Blo 850355 851707 := bstep (se 1 (by rfl) ⟨638780, by rfl⟩ : syracuseStep 851707 = 1277561) B1277561
theorem B851839 : Blo 850355 851839 := bstep (se 1 (by rfl) ⟨638879, by rfl⟩ : syracuseStep 851839 = 1277759) B1277759
theorem B851871 : Blo 850355 851871 := bstep (se 1 (by rfl) ⟨638903, by rfl⟩ : syracuseStep 851871 = 1277807) B1277807
theorem B1277945 : Blo 850355 1277945 := bstep (se 2 (by rfl) ⟨479229, by rfl⟩ : syracuseStep 1277945 = 958459) B958459
theorem B1278089 : Blo 850355 1278089 := bstep (se 2 (by rfl) ⟨479283, by rfl⟩ : syracuseStep 1278089 = 958567) B958567
theorem B1278107 : Blo 850355 1278107 := bstep (se 1 (by rfl) ⟨958580, by rfl⟩ : syracuseStep 1278107 = 1917161) B1917161
theorem B852123 : Blo 850355 852123 := bstep (se 1 (by rfl) ⟨639092, by rfl⟩ : syracuseStep 852123 = 1278185) B1278185
theorem B852127 : Blo 850355 852127 := bstep (se 1 (by rfl) ⟨639095, by rfl⟩ : syracuseStep 852127 = 1278191) B1278191
theorem B5472593 : Blo 850355 5472593 := bstep (se 2 (by rfl) ⟨2052222, by rfl⟩ : syracuseStep 5472593 = 4104445) B4104445
theorem B1278329 : Blo 850355 1278329 := bstep (se 2 (by rfl) ⟨479373, by rfl⟩ : syracuseStep 1278329 = 958747) B958747
theorem B75858533 : Blo 850355 75858533 := bstep (se 4 (by rfl) ⟨7111737, by rfl⟩ : syracuseStep 75858533 = 14223475) B14223475
theorem B1278623 : Blo 850355 1278623 := bstep (se 1 (by rfl) ⟨958967, by rfl⟩ : syracuseStep 1278623 = 1917935) B1917935
theorem B1213159 : Blo 850355 1213159 := bstep (se 1 (by rfl) ⟨909869, by rfl⟩ : syracuseStep 1213159 = 1819739) B1819739
theorem B9700073 : Blo 850355 9700073 := bstep (se 2 (by rfl) ⟨3637527, by rfl⟩ : syracuseStep 9700073 = 7275055) B7275055
theorem B852731 : Blo 850355 852731 := bstep (se 1 (by rfl) ⟨639548, by rfl⟩ : syracuseStep 852731 = 1279097) B1279097
theorem B852763 : Blo 850355 852763 := bstep (se 1 (by rfl) ⟨639572, by rfl⟩ : syracuseStep 852763 = 1279145) B1279145
theorem B8192897 : Blo 850355 8192897 := bstep (se 2 (by rfl) ⟨3072336, by rfl⟩ : syracuseStep 8192897 = 6144673) B6144673
theorem B853019 : Blo 850355 853019 := bstep (se 1 (by rfl) ⟨639764, by rfl⟩ : syracuseStep 853019 = 1279529) B1279529
theorem B853223 : Blo 850355 853223 := bstep (se 1 (by rfl) ⟨639917, by rfl⟩ : syracuseStep 853223 = 1279835) B1279835
theorem B853407 : Blo 850355 853407 := bstep (se 1 (by rfl) ⟨640055, by rfl⟩ : syracuseStep 853407 = 1280111) B1280111
theorem B1279439 : Blo 850355 1279439 := bstep (se 1 (by rfl) ⟨959579, by rfl⟩ : syracuseStep 1279439 = 1919159) B1919159
theorem B853455 : Blo 850355 853455 := bstep (se 1 (by rfl) ⟨640091, by rfl⟩ : syracuseStep 853455 = 1280183) B1280183
theorem B1279625 : Blo 850355 1279625 := bstep (se 2 (by rfl) ⟨479859, by rfl⟩ : syracuseStep 1279625 = 959719) B959719
theorem B853663 : Blo 850355 853663 := bstep (se 1 (by rfl) ⟨640247, by rfl⟩ : syracuseStep 853663 = 1280495) B1280495
theorem B853735 : Blo 850355 853735 := bstep (se 1 (by rfl) ⟨640301, by rfl⟩ : syracuseStep 853735 = 1280603) B1280603
theorem B1640417 : Blo 850355 1640417 := bstep (se 2 (by rfl) ⟨615156, by rfl⟩ : syracuseStep 1640417 = 1230313) B1230313
theorem B4851859 : Blo 850355 4851859 := bstep (se 1 (by rfl) ⟨3638894, by rfl⟩ : syracuseStep 4851859 = 7277789) B7277789
theorem B854223 : Blo 850355 854223 := bstep (se 1 (by rfl) ⟨640667, by rfl⟩ : syracuseStep 854223 = 1281335) B1281335
theorem B10357267 : Blo 850355 10357267 := bstep (se 1 (by rfl) ⟨7767950, by rfl⟩ : syracuseStep 10357267 = 15535901) B15535901
theorem B27626629 : Blo 850355 27626629 := bstep (se 4 (by rfl) ⟨2589996, by rfl⟩ : syracuseStep 27626629 = 5179993) B5179993
theorem B6130835 : Blo 850355 6130835 := bstep (se 1 (by rfl) ⟨4598126, by rfl⟩ : syracuseStep 6130835 = 9196253) B9196253
theorem B2428231 : Blo 850355 2428231 := bstep (se 1 (by rfl) ⟨1821173, by rfl⟩ : syracuseStep 2428231 = 3642347) B3642347
theorem B165809591 : Blo 850355 165809591 := bstep (se 1 (by rfl) ⟨124357193, by rfl⟩ : syracuseStep 165809591 = 248714387) B248714387
theorem B111972131 : Blo 850355 111972131 := bstep (se 1 (by rfl) ⟨83979098, by rfl⟩ : syracuseStep 111972131 = 167958197) B167958197
theorem B6459425 : Blo 850355 6459425 := bstep (se 2 (by rfl) ⟨2422284, by rfl⟩ : syracuseStep 6459425 = 4844569) B4844569
theorem B21861251 : Blo 850355 21861251 := bstep (se 1 (by rfl) ⟨16395938, by rfl⟩ : syracuseStep 21861251 = 32791877) B32791877
theorem B14587289 : Blo 850355 14587289 := bstep (se 2 (by rfl) ⟨5470233, by rfl⟩ : syracuseStep 14587289 = 10940467) B10940467
theorem B6460883 : Blo 850355 6460883 := bstep (se 1 (by rfl) ⟨4845662, by rfl⟩ : syracuseStep 6460883 = 9691325) B9691325
theorem B4364051 : Blo 850355 4364051 := bstep (se 1 (by rfl) ⟨3273038, by rfl⟩ : syracuseStep 4364051 = 6546077) B6546077
theorem B74718287 : Blo 850355 74718287 := bstep (se 1 (by rfl) ⟨56038715, by rfl⟩ : syracuseStep 74718287 = 112077431) B112077431
theorem B2432879 : Blo 850355 2432879 := bstep (se 1 (by rfl) ⟨1824659, by rfl⟩ : syracuseStep 2432879 = 3649319) B3649319
theorem B89858423 : Blo 850355 89858423 := bstep (se 1 (by rfl) ⟨67393817, by rfl⟩ : syracuseStep 89858423 = 134787635) B134787635
theorem B10920581 : Blo 850355 10920581 := bstep (se 4 (by rfl) ⟨1023804, by rfl⟩ : syracuseStep 10920581 = 2047609) B2047609
theorem B7283803 : Blo 850355 7283803 := bstep (se 1 (by rfl) ⟨5462852, by rfl⟩ : syracuseStep 7283803 = 10925705) B10925705
theorem B19670195 : Blo 850355 19670195 := bstep (se 1 (by rfl) ⟨14752646, by rfl⟩ : syracuseStep 19670195 = 29505293) B29505293
theorem B4859423 : Blo 850355 4859423 := bstep (se 1 (by rfl) ⟨3644567, by rfl⟩ : syracuseStep 4859423 = 7289135) B7289135
theorem B1943147 : Blo 850355 1943147 := bstep (se 1 (by rfl) ⟨1457360, by rfl⟩ : syracuseStep 1943147 = 2914721) B2914721
theorem B18689305 : Blo 850355 18689305 := bstep (se 2 (by rfl) ⟨7008489, by rfl⟩ : syracuseStep 18689305 = 14016979) B14016979
theorem B4599251 : Blo 850355 4599251 := bstep (se 1 (by rfl) ⟨3449438, by rfl⟩ : syracuseStep 4599251 = 6898877) B6898877
theorem B3321319 : Blo 850355 3321319 := bstep (se 1 (by rfl) ⟨2490989, by rfl⟩ : syracuseStep 3321319 = 4981979) B4981979
theorem B7286537 : Blo 850355 7286537 := bstep (se 2 (by rfl) ⟨2732451, by rfl⟩ : syracuseStep 7286537 = 5464903) B5464903
theorem B18395099 : Blo 850355 18395099 := bstep (se 1 (by rfl) ⟨13796324, by rfl⟩ : syracuseStep 18395099 = 27592649) B27592649
theorem B1913705 : Blo 850355 1913705 := bstep (se 2 (by rfl) ⟨717639, by rfl⟩ : syracuseStep 1913705 = 1435279) B1435279
theorem B2339705 : Blo 850355 2339705 := bstep (se 2 (by rfl) ⟨877389, by rfl⟩ : syracuseStep 2339705 = 1754779) B1754779
theorem B1913759 : Blo 850355 1913759 := bstep (se 1 (by rfl) ⟨1435319, by rfl⟩ : syracuseStep 1913759 = 2870639) B2870639
theorem B1914011 : Blo 850355 1914011 := bstep (se 1 (by rfl) ⟨1435508, by rfl⟩ : syracuseStep 1914011 = 2871017) B2871017
theorem B8172751 : Blo 850355 8172751 := bstep (se 1 (by rfl) ⟨6129563, by rfl⟩ : syracuseStep 8172751 = 12259127) B12259127
theorem B4306607 : Blo 850355 4306607 := bstep (se 1 (by rfl) ⟨3229955, by rfl⟩ : syracuseStep 4306607 = 6459911) B6459911
theorem B1914587 : Blo 850355 1914587 := bstep (se 1 (by rfl) ⟨1435940, by rfl⟩ : syracuseStep 1914587 = 2871881) B2871881
theorem B5191847 : Blo 850355 5191847 := bstep (se 1 (by rfl) ⟨3893885, by rfl⟩ : syracuseStep 5191847 = 7787771) B7787771
theorem B1915163 : Blo 850355 1915163 := bstep (se 1 (by rfl) ⟨1436372, by rfl⟩ : syracuseStep 1915163 = 2872745) B2872745
theorem B1915199 : Blo 850355 1915199 := bstep (se 1 (by rfl) ⟨1436399, by rfl⟩ : syracuseStep 1915199 = 2872799) B2872799
theorem B4864481 : Blo 850355 4864481 := bstep (se 2 (by rfl) ⟨1824180, by rfl⟩ : syracuseStep 4864481 = 3648361) B3648361
theorem B2079211 : Blo 850355 2079211 := bstep (se 1 (by rfl) ⟨1559408, by rfl⟩ : syracuseStep 2079211 = 3118817) B3118817
theorem B1915703 : Blo 850355 1915703 := bstep (se 1 (by rfl) ⟨1436777, by rfl⟩ : syracuseStep 1915703 = 2873555) B2873555
theorem B34945937 : Blo 850355 34945937 := bstep (se 2 (by rfl) ⟨13104726, by rfl⟩ : syracuseStep 34945937 = 26209453) B26209453
theorem B4307903 : Blo 850355 4307903 := bstep (se 1 (by rfl) ⟨3230927, by rfl⟩ : syracuseStep 4307903 = 6461855) B6461855
theorem B7290161 : Blo 850355 7290161 := bstep (se 2 (by rfl) ⟨2733810, by rfl⟩ : syracuseStep 7290161 = 5467621) B5467621
theorem B5455781 : Blo 850355 5455781 := bstep (se 4 (by rfl) ⟨511479, by rfl⟩ : syracuseStep 5455781 = 1022959) B1022959
theorem B14565419 : Blo 850355 14565419 := bstep (se 1 (by rfl) ⟨10924064, by rfl⟩ : syracuseStep 14565419 = 21848129) B21848129
theorem B1917035 : Blo 850355 1917035 := bstep (se 1 (by rfl) ⟨1437776, by rfl⟩ : syracuseStep 1917035 = 2875553) B2875553
theorem B5390473 : Blo 850355 5390473 := bstep (se 2 (by rfl) ⟨2021427, by rfl⟩ : syracuseStep 5390473 = 4042855) B4042855
theorem B1917305 : Blo 850355 1917305 := bstep (se 2 (by rfl) ⟨718989, by rfl⟩ : syracuseStep 1917305 = 1437979) B1437979
theorem B10371665 : Blo 850355 10371665 := bstep (se 2 (by rfl) ⟨3889374, by rfl⟩ : syracuseStep 10371665 = 7778749) B7778749
theorem B157631305 : Blo 850355 157631305 := bstep (se 2 (by rfl) ⟨59111739, by rfl⟩ : syracuseStep 157631305 = 118223479) B118223479
theorem B1918439 : Blo 850355 1918439 := bstep (se 1 (by rfl) ⟨1438829, by rfl⟩ : syracuseStep 1918439 = 2877659) B2877659
theorem B6899201 : Blo 850355 6899201 := bstep (se 2 (by rfl) ⟨2587200, by rfl⟩ : syracuseStep 6899201 = 5174401) B5174401
theorem B26920907 : Blo 850355 26920907 := bstep (se 1 (by rfl) ⟨20190680, by rfl⟩ : syracuseStep 26920907 = 40381361) B40381361
theorem B1919807 : Blo 850355 1919807 := bstep (se 1 (by rfl) ⟨1439855, by rfl⟩ : syracuseStep 1919807 = 2879711) B2879711
theorem B2870099 : Blo 850355 2870099 := bstep (se 1 (by rfl) ⟨2152574, by rfl⟩ : syracuseStep 2870099 = 4305149) B4305149
theorem B1920311 : Blo 850355 1920311 := bstep (se 1 (by rfl) ⟨1440233, by rfl⟩ : syracuseStep 1920311 = 2880467) B2880467
theorem B8736281 : Blo 850355 8736281 := bstep (se 2 (by rfl) ⟨3276105, by rfl⟩ : syracuseStep 8736281 = 6552211) B6552211
theorem B3231323 : Blo 850355 3231323 := bstep (se 1 (by rfl) ⟨2423492, by rfl⟩ : syracuseStep 3231323 = 4846985) B4846985
theorem B1920617 : Blo 850355 1920617 := bstep (se 2 (by rfl) ⟨720231, by rfl⟩ : syracuseStep 1920617 = 1440463) B1440463
theorem B4607599 : Blo 850355 4607599 := bstep (se 1 (by rfl) ⟨3455699, by rfl⟩ : syracuseStep 4607599 = 6911399) B6911399
theorem B1920671 : Blo 850355 1920671 := bstep (se 1 (by rfl) ⟨1440503, by rfl⟩ : syracuseStep 1920671 = 2881007) B2881007
theorem B1921121 : Blo 850355 1921121 := bstep (se 2 (by rfl) ⟨720420, by rfl⟩ : syracuseStep 1921121 = 1440841) B1440841
theorem B1921679 : Blo 850355 1921679 := bstep (se 1 (by rfl) ⟨1441259, by rfl⟩ : syracuseStep 1921679 = 2882519) B2882519
theorem B1364791 : Blo 850355 1364791 := bstep (se 1 (by rfl) ⟨1023593, by rfl⟩ : syracuseStep 1364791 = 2047187) B2047187
theorem B1921913 : Blo 850355 1921913 := bstep (se 2 (by rfl) ⟨720717, by rfl⟩ : syracuseStep 1921913 = 1441435) B1441435
theorem B12309529 : Blo 850355 12309529 := bstep (se 2 (by rfl) ⟨4616073, by rfl⟩ : syracuseStep 12309529 = 9232147) B9232147
theorem B4314707 : Blo 850355 4314707 := bstep (se 1 (by rfl) ⟨3236030, by rfl⟩ : syracuseStep 4314707 = 6472061) B6472061
theorem B4609889 : Blo 850355 4609889 := bstep (se 2 (by rfl) ⟨1728708, by rfl⟩ : syracuseStep 4609889 = 3457417) B3457417
theorem B18471037 : Blo 850355 18471037 := bstep (se 3 (by rfl) ⟨3463319, by rfl⟩ : syracuseStep 18471037 = 6926639) B6926639
theorem B11229671 : Blo 850355 11229671 := bstep (se 1 (by rfl) ⟨8422253, by rfl⟩ : syracuseStep 11229671 = 16844507) B16844507
theorem B5921855 : Blo 850355 5921855 := bstep (se 1 (by rfl) ⟨4441391, by rfl⟩ : syracuseStep 5921855 = 8882783) B8882783
theorem B9330319 : Blo 850355 9330319 := bstep (se 1 (by rfl) ⟨6997739, by rfl⟩ : syracuseStep 9330319 = 13995479) B13995479
theorem B8740585 : Blo 850355 8740585 := bstep (se 2 (by rfl) ⟨3277719, by rfl⟩ : syracuseStep 8740585 = 6555439) B6555439
theorem B2875337 : Blo 850355 2875337 := bstep (se 2 (by rfl) ⟨1078251, by rfl⟩ : syracuseStep 2875337 = 2156503) B2156503
theorem B6479837 : Blo 850355 6479837 := bstep (se 3 (by rfl) ⟨1214969, by rfl⟩ : syracuseStep 6479837 = 2429939) B2429939
theorem B18669655 : Blo 850355 18669655 := bstep (se 1 (by rfl) ⟨14002241, by rfl⟩ : syracuseStep 18669655 = 28004483) B28004483
theorem B2875499 : Blo 850355 2875499 := bstep (se 1 (by rfl) ⟨2156624, by rfl⟩ : syracuseStep 2875499 = 4313249) B4313249
theorem B5464493 : Blo 850355 5464493 := bstep (se 3 (by rfl) ⟨1024592, by rfl⟩ : syracuseStep 5464493 = 2049185) B2049185
theorem B4318433 : Blo 850355 4318433 := bstep (se 2 (by rfl) ⟨1619412, by rfl⟩ : syracuseStep 4318433 = 3238825) B3238825
theorem B1435367 : Blo 850355 1435367 := bstep (se 1 (by rfl) ⟨1076525, by rfl⟩ : syracuseStep 1435367 = 2153051) B2153051
theorem B4089683 : Blo 850355 4089683 := bstep (se 1 (by rfl) ⟨3067262, by rfl⟩ : syracuseStep 4089683 = 6134525) B6134525
theorem B4843385 : Blo 850355 4843385 := bstep (se 2 (by rfl) ⟨1816269, by rfl⟩ : syracuseStep 4843385 = 3632539) B3632539
theorem B27682681 : Blo 850355 27682681 := bstep (se 2 (by rfl) ⟨10381005, by rfl⟩ : syracuseStep 27682681 = 20762011) B20762011
theorem B18442151 : Blo 850355 18442151 := bstep (se 1 (by rfl) ⟨13831613, by rfl⟩ : syracuseStep 18442151 = 27663227) B27663227
theorem B2156827 : Blo 850355 2156827 := bstep (se 1 (by rfl) ⟨1617620, by rfl⟩ : syracuseStep 2156827 = 3235241) B3235241
theorem B2157263 : Blo 850355 2157263 := bstep (se 1 (by rfl) ⟨1617947, by rfl⟩ : syracuseStep 2157263 = 3235895) B3235895
theorem B3238643 : Blo 850355 3238643 := bstep (se 1 (by rfl) ⟨2428982, by rfl⟩ : syracuseStep 3238643 = 4857965) B4857965
theorem B4320215 : Blo 850355 4320215 := bstep (se 1 (by rfl) ⟨3240161, by rfl⟩ : syracuseStep 4320215 = 6480323) B6480323
theorem B9694241 : Blo 850355 9694241 := bstep (se 2 (by rfl) ⟨3635340, by rfl⟩ : syracuseStep 9694241 = 7270681) B7270681
theorem B9727775 : Blo 850355 9727775 := bstep (se 1 (by rfl) ⟨7295831, by rfl⟩ : syracuseStep 9727775 = 14591663) B14591663
theorem B36925307 : Blo 850355 36925307 := bstep (se 1 (by rfl) ⟨27693980, by rfl⟩ : syracuseStep 36925307 = 55387961) B55387961
theorem B1077887 : Blo 850355 1077887 := bstep (se 1 (by rfl) ⟨808415, by rfl⟩ : syracuseStep 1077887 = 1616831) B1616831
theorem B4322807 : Blo 850355 4322807 := bstep (se 1 (by rfl) ⟨3242105, by rfl⟩ : syracuseStep 4322807 = 6484211) B6484211
theorem B2160371 : Blo 850355 2160371 := bstep (se 1 (by rfl) ⟨1620278, by rfl⟩ : syracuseStep 2160371 = 3240557) B3240557
theorem B4847485 : Blo 850355 4847485 := bstep (se 3 (by rfl) ⟨908903, by rfl⟩ : syracuseStep 4847485 = 1817807) B1817807
theorem B340621469 : Blo 850355 340621469 := bstep (se 3 (by rfl) ⟨63866525, by rfl⟩ : syracuseStep 340621469 = 127733051) B127733051
theorem B2881979 : Blo 850355 2881979 := bstep (se 1 (by rfl) ⟨2161484, by rfl⟩ : syracuseStep 2881979 = 4322969) B4322969
theorem B4324103 : Blo 850355 4324103 := bstep (se 1 (by rfl) ⟨3243077, by rfl⟩ : syracuseStep 4324103 = 6486155) B6486155
theorem B850715 : Blo 850355 850715 := bstep (se 1 (by rfl) ⟨638036, by rfl⟩ : syracuseStep 850715 = 1276073) B1276073
theorem B2423675 : Blo 850355 2423675 := bstep (se 1 (by rfl) ⟨1817756, by rfl⟩ : syracuseStep 2423675 = 3635513) B3635513
theorem B2423915 : Blo 850355 2423915 := bstep (se 1 (by rfl) ⟨1817936, by rfl⟩ : syracuseStep 2423915 = 3635873) B3635873
theorem B851103 : Blo 850355 851103 := bstep (se 1 (by rfl) ⟨638327, by rfl⟩ : syracuseStep 851103 = 1276655) B1276655
theorem B1277225 : Blo 850355 1277225 := bstep (se 2 (by rfl) ⟨478959, by rfl⟩ : syracuseStep 1277225 = 957919) B957919
theorem B9698615 : Blo 850355 9698615 := bstep (se 1 (by rfl) ⟨7273961, by rfl⟩ : syracuseStep 9698615 = 14547923) B14547923
theorem B1080859 : Blo 850355 1080859 := bstep (se 1 (by rfl) ⟨810644, by rfl⟩ : syracuseStep 1080859 = 1621289) B1621289
theorem B1441307 : Blo 850355 1441307 := bstep (se 1 (by rfl) ⟨1080980, by rfl⟩ : syracuseStep 1441307 = 2161961) B2161961
theorem B2883113 : Blo 850355 2883113 := bstep (se 2 (by rfl) ⟨1081167, by rfl⟩ : syracuseStep 2883113 = 2162335) B2162335
theorem B851963 : Blo 850355 851963 := bstep (se 1 (by rfl) ⟨638972, by rfl⟩ : syracuseStep 851963 = 1277945) B1277945
theorem B1278023 : Blo 850355 1278023 := bstep (se 1 (by rfl) ⟨958517, by rfl⟩ : syracuseStep 1278023 = 1917035) B1917035
theorem B852059 : Blo 850355 852059 := bstep (se 1 (by rfl) ⟨639044, by rfl⟩ : syracuseStep 852059 = 1278089) B1278089
theorem B852071 : Blo 850355 852071 := bstep (se 1 (by rfl) ⟨639053, by rfl⟩ : syracuseStep 852071 = 1278107) B1278107
theorem B1278203 : Blo 850355 1278203 := bstep (se 1 (by rfl) ⟨958652, by rfl⟩ : syracuseStep 1278203 = 1917305) B1917305
theorem B852219 : Blo 850355 852219 := bstep (se 1 (by rfl) ⟨639164, by rfl⟩ : syracuseStep 852219 = 1278329) B1278329
theorem B852415 : Blo 850355 852415 := bstep (se 1 (by rfl) ⟨639311, by rfl⟩ : syracuseStep 852415 = 1278623) B1278623
theorem B852959 : Blo 850355 852959 := bstep (se 1 (by rfl) ⟨639719, by rfl⟩ : syracuseStep 852959 = 1279439) B1279439
theorem B1278959 : Blo 850355 1278959 := bstep (se 1 (by rfl) ⟨959219, by rfl⟩ : syracuseStep 1278959 = 1918439) B1918439
theorem B853083 : Blo 850355 853083 := bstep (se 1 (by rfl) ⟨639812, by rfl⟩ : syracuseStep 853083 = 1279625) B1279625
theorem B210175073 : Blo 850355 210175073 := bstep (se 2 (by rfl) ⟨78815652, by rfl⟩ : syracuseStep 210175073 = 157631305) B157631305
theorem B27657773 : Blo 850355 27657773 := bstep (se 3 (by rfl) ⟨5185832, by rfl⟩ : syracuseStep 27657773 = 10371665) B10371665
theorem B1279871 : Blo 850355 1279871 := bstep (se 1 (by rfl) ⟨959903, by rfl⟩ : syracuseStep 1279871 = 1919807) B1919807
theorem B1280207 : Blo 850355 1280207 := bstep (se 1 (by rfl) ⟨960155, by rfl⟩ : syracuseStep 1280207 = 1920311) B1920311
theorem B1280411 : Blo 850355 1280411 := bstep (se 1 (by rfl) ⟨960308, by rfl⟩ : syracuseStep 1280411 = 1920617) B1920617
theorem B1280447 : Blo 850355 1280447 := bstep (se 1 (by rfl) ⟨960335, by rfl⟩ : syracuseStep 1280447 = 1920671) B1920671
theorem B74648087 : Blo 850355 74648087 := bstep (se 1 (by rfl) ⟨55986065, by rfl⟩ : syracuseStep 74648087 = 111972131) B111972131
theorem B1280747 : Blo 850355 1280747 := bstep (se 1 (by rfl) ⟨960560, by rfl⟩ : syracuseStep 1280747 = 1921121) B1921121
theorem B1281119 : Blo 850355 1281119 := bstep (se 1 (by rfl) ⟨960839, by rfl⟩ : syracuseStep 1281119 = 1921679) B1921679
theorem B1281275 : Blo 850355 1281275 := bstep (se 1 (by rfl) ⟨960956, by rfl⟩ : syracuseStep 1281275 = 1921913) B1921913
theorem B36835505 : Blo 850355 36835505 := bstep (se 2 (by rfl) ⟨13813314, by rfl⟩ : syracuseStep 36835505 = 27626629) B27626629
theorem B5181725 : Blo 850355 5181725 := bstep (se 3 (by rfl) ⟨971573, by rfl⟩ : syracuseStep 5181725 = 1943147) B1943147
theorem B4428425 : Blo 850355 4428425 := bstep (se 2 (by rfl) ⟨1660659, by rfl⟩ : syracuseStep 4428425 = 3321319) B3321319
theorem B11637469 : Blo 850355 11637469 := bstep (se 3 (by rfl) ⟨2182025, by rfl⟩ : syracuseStep 11637469 = 4364051) B4364051
theorem B49812191 : Blo 850355 49812191 := bstep (se 1 (by rfl) ⟨37359143, by rfl⟩ : syracuseStep 49812191 = 74718287) B74718287
theorem B3642995 : Blo 850355 3642995 := bstep (se 1 (by rfl) ⟨2732246, by rfl⟩ : syracuseStep 3642995 = 5464493) B5464493
theorem B7280387 : Blo 850355 7280387 := bstep (se 1 (by rfl) ⟨5460290, by rfl⟩ : syracuseStep 7280387 = 10920581) B10920581
theorem B13113463 : Blo 850355 13113463 := bstep (se 1 (by rfl) ⟨9835097, by rfl⟩ : syracuseStep 13113463 = 19670195) B19670195
theorem B956911 : Blo 850355 956911 := bstep (se 1 (by rfl) ⟨717683, by rfl⟩ : syracuseStep 956911 = 1435367) B1435367
theorem B2726455 : Blo 850355 2726455 := bstep (se 1 (by rfl) ⟨2044841, by rfl⟩ : syracuseStep 2726455 = 4089683) B4089683
theorem B12294767 : Blo 850355 12294767 := bstep (se 1 (by rfl) ⟨9221075, by rfl⟩ : syracuseStep 12294767 = 18442151) B18442151
theorem B6462827 : Blo 850355 6462827 := bstep (se 1 (by rfl) ⟨4847120, by rfl⟩ : syracuseStep 6462827 = 9694241) B9694241
theorem B6463313 : Blo 850355 6463313 := bstep (se 2 (by rfl) ⟨2423742, by rfl⟩ : syracuseStep 6463313 = 4847485) B4847485
theorem B4857691 : Blo 850355 4857691 := bstep (se 1 (by rfl) ⟨3643268, by rfl⟩ : syracuseStep 4857691 = 7286537) B7286537
theorem B24616871 : Blo 850355 24616871 := bstep (se 1 (by rfl) ⟨18462653, by rfl⟩ : syracuseStep 24616871 = 36925307) B36925307
theorem B12263399 : Blo 850355 12263399 := bstep (se 1 (by rfl) ⟨9197549, by rfl⟩ : syracuseStep 12263399 = 18395099) B18395099
theorem B1615783 : Blo 850355 1615783 := bstep (se 1 (by rfl) ⟨1211837, by rfl⟩ : syracuseStep 1615783 = 2423675) B2423675
theorem B1615943 : Blo 850355 1615943 := bstep (se 1 (by rfl) ⟨1211957, by rfl⟩ : syracuseStep 1615943 = 2423915) B2423915
theorem B4860107 : Blo 850355 4860107 := bstep (se 1 (by rfl) ⟨3645080, by rfl⟩ : syracuseStep 4860107 = 7290161) B7290161
theorem B6465743 : Blo 850355 6465743 := bstep (se 1 (by rfl) ⟨4849307, by rfl⟩ : syracuseStep 6465743 = 9698615) B9698615
theorem B960871 : Blo 850355 960871 := bstep (se 1 (by rfl) ⟨720653, by rfl⟩ : syracuseStep 960871 = 1441307) B1441307
theorem B9710279 : Blo 850355 9710279 := bstep (se 1 (by rfl) ⟨7282709, by rfl⟩ : syracuseStep 9710279 = 14565419) B14565419
theorem B7187297 : Blo 850355 7187297 := bstep (se 2 (by rfl) ⟨2695236, by rfl⟩ : syracuseStep 7187297 = 5390473) B5390473
theorem B3648395 : Blo 850355 3648395 := bstep (se 1 (by rfl) ⟨2736296, by rfl⟩ : syracuseStep 3648395 = 5472593) B5472593
theorem B50572355 : Blo 850355 50572355 := bstep (se 1 (by rfl) ⟨37929266, by rfl⟩ : syracuseStep 50572355 = 75858533) B75858533
theorem B6466715 : Blo 850355 6466715 := bstep (se 1 (by rfl) ⟨4850036, by rfl⟩ : syracuseStep 6466715 = 9700073) B9700073
theorem B1617545 : Blo 850355 1617545 := bstep (se 2 (by rfl) ⟨606579, by rfl⟩ : syracuseStep 1617545 = 1213159) B1213159
theorem B4599467 : Blo 850355 4599467 := bstep (se 1 (by rfl) ⟨3449600, by rfl⟩ : syracuseStep 4599467 = 6899201) B6899201
theorem B9711737 : Blo 850355 9711737 := bstep (se 2 (by rfl) ⟨3641901, by rfl⟩ : syracuseStep 9711737 = 7283803) B7283803
theorem B1913399 : Blo 850355 1913399 := bstep (se 1 (by rfl) ⟨1435049, by rfl⟩ : syracuseStep 1913399 = 2870099) B2870099
theorem B110539727 : Blo 850355 110539727 := bstep (se 1 (by rfl) ⟨82904795, by rfl⟩ : syracuseStep 110539727 = 165809591) B165809591
theorem B6239213 : Blo 850355 6239213 := bstep (se 3 (by rfl) ⟨1169852, by rfl⟩ : syracuseStep 6239213 = 2339705) B2339705
theorem B36910241 : Blo 850355 36910241 := bstep (se 2 (by rfl) ⟨13841340, by rfl⟩ : syracuseStep 36910241 = 27682681) B27682681
theorem B4306283 : Blo 850355 4306283 := bstep (se 1 (by rfl) ⟨3229712, by rfl⟩ : syracuseStep 4306283 = 6459425) B6459425
theorem B6469145 : Blo 850355 6469145 := bstep (se 2 (by rfl) ⟨2425929, by rfl⟩ : syracuseStep 6469145 = 4851859) B4851859
theorem B13809689 : Blo 850355 13809689 := bstep (se 2 (by rfl) ⟨5178633, by rfl⟩ : syracuseStep 13809689 = 10357267) B10357267
theorem B4307255 : Blo 850355 4307255 := bstep (se 1 (by rfl) ⟨3230441, by rfl⟩ : syracuseStep 4307255 = 6460883) B6460883
theorem B7486447 : Blo 850355 7486447 := bstep (se 1 (by rfl) ⟨5614835, by rfl⟩ : syracuseStep 7486447 = 11229671) B11229671
theorem B24919073 : Blo 850355 24919073 := bstep (se 2 (by rfl) ⟨9344652, by rfl⟩ : syracuseStep 24919073 = 18689305) B18689305
theorem B3947903 : Blo 850355 3947903 := bstep (se 1 (by rfl) ⟨2960927, by rfl⟩ : syracuseStep 3947903 = 5921855) B5921855
theorem B6143465 : Blo 850355 6143465 := bstep (se 2 (by rfl) ⟨2303799, by rfl⟩ : syracuseStep 6143465 = 4607599) B4607599
theorem B1621919 : Blo 850355 1621919 := bstep (se 1 (by rfl) ⟨1216439, by rfl⟩ : syracuseStep 1621919 = 2432879) B2432879
theorem B4374445 : Blo 850355 4374445 := bstep (se 3 (by rfl) ⟨820208, by rfl⟩ : syracuseStep 4374445 = 1640417) B1640417
theorem B1916891 : Blo 850355 1916891 := bstep (se 1 (by rfl) ⟨1437668, by rfl⟩ : syracuseStep 1916891 = 2875337) B2875337
theorem B1916999 : Blo 850355 1916999 := bstep (se 1 (by rfl) ⟨1437749, by rfl⟩ : syracuseStep 1916999 = 2875499) B2875499
theorem B1819721 : Blo 850355 1819721 := bstep (se 2 (by rfl) ⟨682395, by rfl⟩ : syracuseStep 1819721 = 1364791) B1364791
theorem B3228923 : Blo 850355 3228923 := bstep (se 1 (by rfl) ⟨2421692, by rfl⟩ : syracuseStep 3228923 = 4843385) B4843385
theorem B10897001 : Blo 850355 10897001 := bstep (se 2 (by rfl) ⟨4086375, by rfl⟩ : syracuseStep 10897001 = 8172751) B8172751
theorem B3066167 : Blo 850355 3066167 := bstep (se 1 (by rfl) ⟨2299625, by rfl⟩ : syracuseStep 3066167 = 4599251) B4599251
theorem B24628049 : Blo 850355 24628049 := bstep (se 2 (by rfl) ⟨9235518, by rfl⟩ : syracuseStep 24628049 = 18471037) B18471037
theorem B2772281 : Blo 850355 2772281 := bstep (se 2 (by rfl) ⟨1039605, by rfl⟩ : syracuseStep 2772281 = 2079211) B2079211
theorem B49761701 : Blo 850355 49761701 := bstep (se 4 (by rfl) ⟨4665159, by rfl⟩ : syracuseStep 49761701 = 9330319) B9330319
theorem B2871071 : Blo 850355 2871071 := bstep (se 1 (by rfl) ⟨2153303, by rfl⟩ : syracuseStep 2871071 = 4306607) B4306607
theorem B3461231 : Blo 850355 3461231 := bstep (se 1 (by rfl) ⟨2595923, by rfl⟩ : syracuseStep 3461231 = 5191847) B5191847
theorem B1921319 : Blo 850355 1921319 := bstep (se 1 (by rfl) ⟨1440989, by rfl⟩ : syracuseStep 1921319 = 2881979) B2881979
theorem B2871935 : Blo 850355 2871935 := bstep (se 1 (by rfl) ⟨2153951, by rfl⟩ : syracuseStep 2871935 = 4307903) B4307903
theorem B11654113 : Blo 850355 11654113 := bstep (se 2 (by rfl) ⟨4370292, by rfl⟩ : syracuseStep 11654113 = 8740585) B8740585
theorem B1922075 : Blo 850355 1922075 := bstep (se 1 (by rfl) ⟨1441556, by rfl⟩ : syracuseStep 1922075 = 2883113) B2883113
theorem B99571493 : Blo 850355 99571493 := bstep (se 4 (by rfl) ⟨9334827, by rfl⟩ : syracuseStep 99571493 = 18669655) B18669655
theorem B5461931 : Blo 850355 5461931 := bstep (se 1 (by rfl) ⟨4096448, by rfl⟩ : syracuseStep 5461931 = 8192897) B8192897
theorem B239622461 : Blo 850355 239622461 := bstep (se 3 (by rfl) ⟨44929211, by rfl⟩ : syracuseStep 239622461 = 89858423) B89858423
theorem B17947271 : Blo 850355 17947271 := bstep (se 1 (by rfl) ⟨13460453, by rfl⟩ : syracuseStep 17947271 = 26920907) B26920907
theorem B2874365 : Blo 850355 2874365 := bstep (se 3 (by rfl) ⟨538943, by rfl⟩ : syracuseStep 2874365 = 1077887) B1077887
theorem B4087223 : Blo 850355 4087223 := bstep (se 1 (by rfl) ⟨3065417, by rfl⟩ : syracuseStep 4087223 = 6130835) B6130835
theorem B5824187 : Blo 850355 5824187 := bstep (se 1 (by rfl) ⟨4368140, by rfl⟩ : syracuseStep 5824187 = 8736281) B8736281
theorem B2154215 : Blo 850355 2154215 := bstep (se 1 (by rfl) ⟨1615661, by rfl⟩ : syracuseStep 2154215 = 3231323) B3231323
theorem B2875769 : Blo 850355 2875769 := bstep (se 2 (by rfl) ⟨1078413, by rfl⟩ : syracuseStep 2875769 = 2156827) B2156827
theorem B14574167 : Blo 850355 14574167 := bstep (se 1 (by rfl) ⟨10930625, by rfl⟩ : syracuseStep 14574167 = 21861251) B21861251
theorem B9724859 : Blo 850355 9724859 := bstep (se 1 (by rfl) ⟨7293644, by rfl⟩ : syracuseStep 9724859 = 14587289) B14587289
theorem B2876471 : Blo 850355 2876471 := bstep (se 1 (by rfl) ⟨2157353, by rfl⟩ : syracuseStep 2876471 = 4314707) B4314707
theorem B3073259 : Blo 850355 3073259 := bstep (se 1 (by rfl) ⟨2304944, by rfl⟩ : syracuseStep 3073259 = 4609889) B4609889
theorem B3237641 : Blo 850355 3237641 := bstep (se 2 (by rfl) ⟨1214115, by rfl⟩ : syracuseStep 3237641 = 2428231) B2428231
theorem B4319891 : Blo 850355 4319891 := bstep (se 1 (by rfl) ⟨3239918, by rfl⟩ : syracuseStep 4319891 = 6479837) B6479837
theorem B2878955 : Blo 850355 2878955 := bstep (se 1 (by rfl) ⟨2159216, by rfl⟩ : syracuseStep 2878955 = 4318433) B4318433
theorem B3239615 : Blo 850355 3239615 := bstep (se 1 (by rfl) ⟨2429711, by rfl⟩ : syracuseStep 3239615 = 4859423) B4859423
theorem B16412705 : Blo 850355 16412705 := bstep (se 2 (by rfl) ⟨6154764, by rfl⟩ : syracuseStep 16412705 = 12309529) B12309529
theorem B1438175 : Blo 850355 1438175 := bstep (se 1 (by rfl) ⟨1078631, by rfl⟩ : syracuseStep 1438175 = 2157263) B2157263
theorem B2159095 : Blo 850355 2159095 := bstep (se 1 (by rfl) ⟨1619321, by rfl⟩ : syracuseStep 2159095 = 3238643) B3238643
theorem B2880143 : Blo 850355 2880143 := bstep (se 1 (by rfl) ⟨2160107, by rfl⟩ : syracuseStep 2880143 = 4320215) B4320215
theorem B6485183 : Blo 850355 6485183 := bstep (se 1 (by rfl) ⟨4863887, by rfl⟩ : syracuseStep 6485183 = 9727775) B9727775
theorem B1275803 : Blo 850355 1275803 := bstep (se 1 (by rfl) ⟨956852, by rfl⟩ : syracuseStep 1275803 = 1913705) B1913705
theorem B1275839 : Blo 850355 1275839 := bstep (se 1 (by rfl) ⟨956879, by rfl⟩ : syracuseStep 1275839 = 1913759) B1913759
theorem B1276007 : Blo 850355 1276007 := bstep (se 1 (by rfl) ⟨957005, by rfl⟩ : syracuseStep 1276007 = 1914011) B1914011
theorem B2881871 : Blo 850355 2881871 := bstep (se 1 (by rfl) ⟨2161403, by rfl⟩ : syracuseStep 2881871 = 4322807) B4322807
theorem B1276391 : Blo 850355 1276391 := bstep (se 1 (by rfl) ⟨957293, by rfl⟩ : syracuseStep 1276391 = 1914587) B1914587
theorem B1440247 : Blo 850355 1440247 := bstep (se 1 (by rfl) ⟨1080185, by rfl⟩ : syracuseStep 1440247 = 2160371) B2160371
theorem B227080979 : Blo 850355 227080979 := bstep (se 1 (by rfl) ⟨170310734, by rfl⟩ : syracuseStep 227080979 = 340621469) B340621469
theorem B1276775 : Blo 850355 1276775 := bstep (se 1 (by rfl) ⟨957581, by rfl⟩ : syracuseStep 1276775 = 1915163) B1915163
theorem B1276799 : Blo 850355 1276799 := bstep (se 1 (by rfl) ⟨957599, by rfl⟩ : syracuseStep 1276799 = 1915199) B1915199
theorem B3242987 : Blo 850355 3242987 := bstep (se 1 (by rfl) ⟨2432240, by rfl⟩ : syracuseStep 3242987 = 4864481) B4864481
theorem B2882735 : Blo 850355 2882735 := bstep (se 1 (by rfl) ⟨2162051, by rfl⟩ : syracuseStep 2882735 = 4324103) B4324103
theorem B1277135 : Blo 850355 1277135 := bstep (se 1 (by rfl) ⟨957851, by rfl⟩ : syracuseStep 1277135 = 1915703) B1915703
theorem B23297291 : Blo 850355 23297291 := bstep (se 1 (by rfl) ⟨17472968, by rfl⟩ : syracuseStep 23297291 = 34945937) B34945937
theorem B1441145 : Blo 850355 1441145 := bstep (se 2 (by rfl) ⟨540429, by rfl⟩ : syracuseStep 1441145 = 1080859) B1080859
theorem B851483 : Blo 850355 851483 := bstep (se 1 (by rfl) ⟨638612, by rfl⟩ : syracuseStep 851483 = 1277225) B1277225
theorem B3637187 : Blo 850355 3637187 := bstep (se 1 (by rfl) ⟨2727890, by rfl⟩ : syracuseStep 3637187 = 5455781) B5455781
theorem B1277999 : Blo 850355 1277999 := bstep (se 1 (by rfl) ⟨958499, by rfl⟩ : syracuseStep 1277999 = 1916999) B1916999
theorem B852015 : Blo 850355 852015 := bstep (se 1 (by rfl) ⟨639011, by rfl⟩ : syracuseStep 852015 = 1278023) B1278023
theorem B852135 : Blo 850355 852135 := bstep (se 1 (by rfl) ⟨639101, by rfl⟩ : syracuseStep 852135 = 1278203) B1278203
theorem B852639 : Blo 850355 852639 := bstep (se 1 (by rfl) ⟨639479, by rfl⟩ : syracuseStep 852639 = 1278959) B1278959
theorem B1213147 : Blo 850355 1213147 := bstep (se 1 (by rfl) ⟨909860, by rfl⟩ : syracuseStep 1213147 = 1819721) B1819721
theorem B140116715 : Blo 850355 140116715 := bstep (se 1 (by rfl) ⟨105087536, by rfl⟩ : syracuseStep 140116715 = 210175073) B210175073
theorem B853247 : Blo 850355 853247 := bstep (se 1 (by rfl) ⟨639935, by rfl⟩ : syracuseStep 853247 = 1279871) B1279871
theorem B853471 : Blo 850355 853471 := bstep (se 1 (by rfl) ⟨640103, by rfl⟩ : syracuseStep 853471 = 1280207) B1280207
theorem B853607 : Blo 850355 853607 := bstep (se 1 (by rfl) ⟨640205, by rfl⟩ : syracuseStep 853607 = 1280411) B1280411
theorem B853631 : Blo 850355 853631 := bstep (se 1 (by rfl) ⟨640223, by rfl⟩ : syracuseStep 853631 = 1280447) B1280447
theorem B853831 : Blo 850355 853831 := bstep (se 1 (by rfl) ⟨640373, by rfl⟩ : syracuseStep 853831 = 1280747) B1280747
theorem B16418699 : Blo 850355 16418699 := bstep (se 1 (by rfl) ⟨12314024, by rfl⟩ : syracuseStep 16418699 = 24628049) B24628049
theorem B854079 : Blo 850355 854079 := bstep (se 1 (by rfl) ⟨640559, by rfl⟩ : syracuseStep 854079 = 1281119) B1281119
theorem B854183 : Blo 850355 854183 := bstep (se 1 (by rfl) ⟨640637, by rfl⟩ : syracuseStep 854183 = 1281275) B1281275
theorem B1280879 : Blo 850355 1280879 := bstep (se 1 (by rfl) ⟨960659, by rfl⟩ : syracuseStep 1280879 = 1921319) B1921319
theorem B2952283 : Blo 850355 2952283 := bstep (se 1 (by rfl) ⟨2214212, by rfl⟩ : syracuseStep 2952283 = 4428425) B4428425
theorem B1281161 : Blo 850355 1281161 := bstep (se 2 (by rfl) ⟨480435, by rfl⟩ : syracuseStep 1281161 = 960871) B960871
theorem B8195357 : Blo 850355 8195357 := bstep (se 3 (by rfl) ⟨1536629, by rfl⟩ : syracuseStep 8195357 = 3073259) B3073259
theorem B1281383 : Blo 850355 1281383 := bstep (se 1 (by rfl) ⟨961037, by rfl⟩ : syracuseStep 1281383 = 1922075) B1922075
theorem B4853591 : Blo 850355 4853591 := bstep (se 1 (by rfl) ⟨3640193, by rfl⟩ : syracuseStep 4853591 = 7280387) B7280387
theorem B3641287 : Blo 850355 3641287 := bstep (se 1 (by rfl) ⟨2730965, by rfl⟩ : syracuseStep 3641287 = 5461931) B5461931
theorem B159748307 : Blo 850355 159748307 := bstep (se 1 (by rfl) ⟨119811230, by rfl⟩ : syracuseStep 159748307 = 239622461) B239622461
theorem B8196511 : Blo 850355 8196511 := bstep (se 1 (by rfl) ⟨6147383, by rfl⟩ : syracuseStep 8196511 = 12294767) B12294767
theorem B11964847 : Blo 850355 11964847 := bstep (se 1 (by rfl) ⟨8973635, by rfl⟩ : syracuseStep 11964847 = 17947271) B17947271
theorem B2724815 : Blo 850355 2724815 := bstep (se 1 (by rfl) ⟨2043611, by rfl⟩ : syracuseStep 2724815 = 4087223) B4087223
theorem B15538817 : Blo 850355 15538817 := bstep (se 2 (by rfl) ⟨5827056, by rfl⟩ : syracuseStep 15538817 = 11654113) B11654113
theorem B2432263 : Blo 850355 2432263 := bstep (se 1 (by rfl) ⟨1824197, by rfl⟩ : syracuseStep 2432263 = 3648395) B3648395
theorem B958783 : Blo 850355 958783 := bstep (se 1 (by rfl) ⟨719087, by rfl⟩ : syracuseStep 958783 = 1438175) B1438175
theorem B960763 : Blo 850355 960763 := bstep (se 1 (by rfl) ⟨720572, by rfl⟩ : syracuseStep 960763 = 1441145) B1441145
theorem B2631935 : Blo 850355 2631935 := bstep (se 1 (by rfl) ⟨1973951, by rfl⟩ : syracuseStep 2631935 = 3947903) B3947903
theorem B2044111 : Blo 850355 2044111 := bstep (se 1 (by rfl) ⟨1533083, by rfl⟩ : syracuseStep 2044111 = 3066167) B3066167
theorem B1848187 : Blo 850355 1848187 := bstep (se 1 (by rfl) ⟨1386140, by rfl⟩ : syracuseStep 1848187 = 2772281) B2772281
theorem B33174467 : Blo 850355 33174467 := bstep (se 1 (by rfl) ⟨24880850, by rfl⟩ : syracuseStep 33174467 = 49761701) B49761701
theorem B1914047 : Blo 850355 1914047 := bstep (se 1 (by rfl) ⟨1435535, by rfl⟩ : syracuseStep 1914047 = 2871071) B2871071
theorem B2307487 : Blo 850355 2307487 := bstep (se 1 (by rfl) ⟨1730615, by rfl⟩ : syracuseStep 2307487 = 3461231) B3461231
theorem B24557003 : Blo 850355 24557003 := bstep (se 1 (by rfl) ⟨18417752, by rfl⟩ : syracuseStep 24557003 = 36835505) B36835505
theorem B3454483 : Blo 850355 3454483 := bstep (se 1 (by rfl) ⟨2590862, by rfl⟩ : syracuseStep 3454483 = 5181725) B5181725
theorem B1914623 : Blo 850355 1914623 := bstep (se 1 (by rfl) ⟨1435967, by rfl⟩ : syracuseStep 1914623 = 2871935) B2871935
theorem B33208127 : Blo 850355 33208127 := bstep (se 1 (by rfl) ⟨24906095, by rfl⟩ : syracuseStep 33208127 = 49812191) B49812191
theorem B9714653 : Blo 850355 9714653 := bstep (se 3 (by rfl) ⟨1821497, by rfl⟩ : syracuseStep 9714653 = 3642995) B3642995
theorem B1916243 : Blo 850355 1916243 := bstep (se 1 (by rfl) ⟨1437182, by rfl⟩ : syracuseStep 1916243 = 2874365) B2874365
theorem B4308551 : Blo 850355 4308551 := bstep (se 1 (by rfl) ⟨3231413, by rfl⟩ : syracuseStep 4308551 = 6462827) B6462827
theorem B3882791 : Blo 850355 3882791 := bstep (se 1 (by rfl) ⟨2912093, by rfl⟩ : syracuseStep 3882791 = 5824187) B5824187
theorem B4308875 : Blo 850355 4308875 := bstep (se 1 (by rfl) ⟨3231656, by rfl⟩ : syracuseStep 4308875 = 6463313) B6463313
theorem B8175599 : Blo 850355 8175599 := bstep (se 1 (by rfl) ⟨6131699, by rfl⟩ : syracuseStep 8175599 = 12263399) B12263399
theorem B1917179 : Blo 850355 1917179 := bstep (se 1 (by rfl) ⟨1437884, by rfl⟩ : syracuseStep 1917179 = 2875769) B2875769
theorem B9716111 : Blo 850355 9716111 := bstep (se 1 (by rfl) ⟨7287083, by rfl⟩ : syracuseStep 9716111 = 14574167) B14574167
theorem B1917647 : Blo 850355 1917647 := bstep (se 1 (by rfl) ⟨1438235, by rfl⟩ : syracuseStep 1917647 = 2876471) B2876471
theorem B15516625 : Blo 850355 15516625 := bstep (se 2 (by rfl) ⟨5818734, by rfl⟩ : syracuseStep 15516625 = 11637469) B11637469
theorem B4310495 : Blo 850355 4310495 := bstep (se 1 (by rfl) ⟨3232871, by rfl⟩ : syracuseStep 4310495 = 6465743) B6465743
theorem B6473519 : Blo 850355 6473519 := bstep (se 1 (by rfl) ⟨4855139, by rfl⟩ : syracuseStep 6473519 = 9710279) B9710279
theorem B4311143 : Blo 850355 4311143 := bstep (se 1 (by rfl) ⟨3233357, by rfl⟩ : syracuseStep 4311143 = 6466715) B6466715
theorem B1919303 : Blo 850355 1919303 := bstep (se 1 (by rfl) ⟨1439477, by rfl⟩ : syracuseStep 1919303 = 2878955) B2878955
theorem B3066311 : Blo 850355 3066311 := bstep (se 1 (by rfl) ⟨2299733, by rfl⟩ : syracuseStep 3066311 = 4599467) B4599467
theorem B6474491 : Blo 850355 6474491 := bstep (se 1 (by rfl) ⟨4855868, by rfl⟩ : syracuseStep 6474491 = 9711737) B9711737
theorem B17484617 : Blo 850355 17484617 := bstep (se 2 (by rfl) ⟨6556731, by rfl⟩ : syracuseStep 17484617 = 13113463) B13113463
theorem B134859613 : Blo 850355 134859613 := bstep (se 3 (by rfl) ⟨25286177, by rfl⟩ : syracuseStep 134859613 = 50572355) B50572355
theorem B1920095 : Blo 850355 1920095 := bstep (se 1 (by rfl) ⟨1440071, by rfl⟩ : syracuseStep 1920095 = 2880143) B2880143
theorem B1920329 : Blo 850355 1920329 := bstep (se 2 (by rfl) ⟨720123, by rfl⟩ : syracuseStep 1920329 = 1440247) B1440247
theorem B2870855 : Blo 850355 2870855 := bstep (se 1 (by rfl) ⟨2153141, by rfl⟩ : syracuseStep 2870855 = 4306283) B4306283
theorem B76664501 : Blo 850355 76664501 := bstep (se 5 (by rfl) ⟨3593648, by rfl⟩ : syracuseStep 76664501 = 7187297) B7187297
theorem B4312763 : Blo 850355 4312763 := bstep (se 1 (by rfl) ⟨3234572, by rfl⟩ : syracuseStep 4312763 = 6469145) B6469145
theorem B9981929 : Blo 850355 9981929 := bstep (se 2 (by rfl) ⟨3743223, by rfl⟩ : syracuseStep 9981929 = 7486447) B7486447
theorem B2871503 : Blo 850355 2871503 := bstep (se 1 (by rfl) ⟨2153627, by rfl⟩ : syracuseStep 2871503 = 4307255) B4307255
theorem B1921247 : Blo 850355 1921247 := bstep (se 1 (by rfl) ⟨1440935, by rfl⟩ : syracuseStep 1921247 = 2881871) B2881871
theorem B1921823 : Blo 850355 1921823 := bstep (se 1 (by rfl) ⟨1441367, by rfl⟩ : syracuseStep 1921823 = 2882735) B2882735
theorem B6476921 : Blo 850355 6476921 := bstep (se 2 (by rfl) ⟨2428845, by rfl⟩ : syracuseStep 6476921 = 4857691) B4857691
theorem B2152615 : Blo 850355 2152615 := bstep (se 1 (by rfl) ⟨1614461, by rfl⟩ : syracuseStep 2152615 = 3228923) B3228923
theorem B18438515 : Blo 850355 18438515 := bstep (se 1 (by rfl) ⟨13828886, by rfl⟩ : syracuseStep 18438515 = 27657773) B27657773
theorem B7264667 : Blo 850355 7264667 := bstep (se 1 (by rfl) ⟨5448500, by rfl⟩ : syracuseStep 7264667 = 10897001) B10897001
theorem B49765391 : Blo 850355 49765391 := bstep (se 1 (by rfl) ⟨37324043, by rfl⟩ : syracuseStep 49765391 = 74648087) B74648087
theorem B2154377 : Blo 850355 2154377 := bstep (se 2 (by rfl) ⟨807891, by rfl⟩ : syracuseStep 2154377 = 1615783) B1615783
theorem B66380995 : Blo 850355 66380995 := bstep (se 1 (by rfl) ⟨49785746, by rfl⟩ : syracuseStep 66380995 = 99571493) B99571493
theorem B1436143 : Blo 850355 1436143 := bstep (se 1 (by rfl) ⟨1077107, by rfl⟩ : syracuseStep 1436143 = 2154215) B2154215
theorem B16411247 : Blo 850355 16411247 := bstep (se 1 (by rfl) ⟨12308435, by rfl⟩ : syracuseStep 16411247 = 24616871) B24616871
theorem B6483239 : Blo 850355 6483239 := bstep (se 1 (by rfl) ⟨4862429, by rfl⟩ : syracuseStep 6483239 = 9724859) B9724859
theorem B2878793 : Blo 850355 2878793 := bstep (se 2 (by rfl) ⟨1079547, by rfl⟩ : syracuseStep 2878793 = 2159095) B2159095
theorem B2158427 : Blo 850355 2158427 := bstep (se 1 (by rfl) ⟨1618820, by rfl⟩ : syracuseStep 2158427 = 3237641) B3237641
theorem B1077295 : Blo 850355 1077295 := bstep (se 1 (by rfl) ⟨807971, by rfl⟩ : syracuseStep 1077295 = 1615943) B1615943
theorem B3240071 : Blo 850355 3240071 := bstep (se 1 (by rfl) ⟨2430053, by rfl⟩ : syracuseStep 3240071 = 4860107) B4860107
theorem B2879927 : Blo 850355 2879927 := bstep (se 1 (by rfl) ⟨2159945, by rfl⟩ : syracuseStep 2879927 = 4319891) B4319891
theorem B1078363 : Blo 850355 1078363 := bstep (se 1 (by rfl) ⟨808772, by rfl⟩ : syracuseStep 1078363 = 1617545) B1617545
theorem B2159743 : Blo 850355 2159743 := bstep (se 1 (by rfl) ⟨1619807, by rfl⟩ : syracuseStep 2159743 = 3239615) B3239615
theorem B10941803 : Blo 850355 10941803 := bstep (se 1 (by rfl) ⟨8206352, by rfl⟩ : syracuseStep 10941803 = 16412705) B16412705
theorem B1275599 : Blo 850355 1275599 := bstep (se 1 (by rfl) ⟨956699, by rfl⟩ : syracuseStep 1275599 = 1913399) B1913399
theorem B73693151 : Blo 850355 73693151 := bstep (se 1 (by rfl) ⟨55269863, by rfl⟩ : syracuseStep 73693151 = 110539727) B110539727
theorem B1275881 : Blo 850355 1275881 := bstep (se 2 (by rfl) ⟨478455, by rfl⟩ : syracuseStep 1275881 = 956911) B956911
theorem B4159475 : Blo 850355 4159475 := bstep (se 1 (by rfl) ⟨3119606, by rfl⟩ : syracuseStep 4159475 = 6239213) B6239213
theorem B3635273 : Blo 850355 3635273 := bstep (se 2 (by rfl) ⟨1363227, by rfl⟩ : syracuseStep 3635273 = 2726455) B2726455
theorem B24606827 : Blo 850355 24606827 := bstep (se 1 (by rfl) ⟨18455120, by rfl⟩ : syracuseStep 24606827 = 36910241) B36910241
theorem B4323455 : Blo 850355 4323455 := bstep (se 1 (by rfl) ⟨3242591, by rfl⟩ : syracuseStep 4323455 = 6485183) B6485183
theorem B850535 : Blo 850355 850535 := bstep (se 1 (by rfl) ⟨637901, by rfl⟩ : syracuseStep 850535 = 1275803) B1275803
theorem B850559 : Blo 850355 850559 := bstep (se 1 (by rfl) ⟨637919, by rfl⟩ : syracuseStep 850559 = 1275839) B1275839
theorem B9206459 : Blo 850355 9206459 := bstep (se 1 (by rfl) ⟨6904844, by rfl⟩ : syracuseStep 9206459 = 13809689) B13809689
theorem B850671 : Blo 850355 850671 := bstep (se 1 (by rfl) ⟨638003, by rfl⟩ : syracuseStep 850671 = 1276007) B1276007
theorem B850927 : Blo 850355 850927 := bstep (se 1 (by rfl) ⟨638195, by rfl⟩ : syracuseStep 850927 = 1276391) B1276391
theorem B151387319 : Blo 850355 151387319 := bstep (se 1 (by rfl) ⟨113540489, by rfl⟩ : syracuseStep 151387319 = 227080979) B227080979
theorem B851183 : Blo 850355 851183 := bstep (se 1 (by rfl) ⟨638387, by rfl⟩ : syracuseStep 851183 = 1276775) B1276775
theorem B851199 : Blo 850355 851199 := bstep (se 1 (by rfl) ⟨638399, by rfl⟩ : syracuseStep 851199 = 1276799) B1276799
theorem B2161991 : Blo 850355 2161991 := bstep (se 1 (by rfl) ⟨1621493, by rfl⟩ : syracuseStep 2161991 = 3242987) B3242987
theorem B16612715 : Blo 850355 16612715 := bstep (se 1 (by rfl) ⟨12459536, by rfl⟩ : syracuseStep 16612715 = 24919073) B24919073
theorem B851423 : Blo 850355 851423 := bstep (se 1 (by rfl) ⟨638567, by rfl⟩ : syracuseStep 851423 = 1277135) B1277135
theorem B15531527 : Blo 850355 15531527 := bstep (se 1 (by rfl) ⟨11648645, by rfl⟩ : syracuseStep 15531527 = 23297291) B23297291
theorem B4095643 : Blo 850355 4095643 := bstep (se 1 (by rfl) ⟨3071732, by rfl⟩ : syracuseStep 4095643 = 6143465) B6143465
theorem B5832593 : Blo 850355 5832593 := bstep (se 2 (by rfl) ⟨2187222, by rfl⟩ : syracuseStep 5832593 = 4374445) B4374445
theorem B1081279 : Blo 850355 1081279 := bstep (se 1 (by rfl) ⟨810959, by rfl⟩ : syracuseStep 1081279 = 1621919) B1621919
theorem B2424791 : Blo 850355 2424791 := bstep (se 1 (by rfl) ⟨1818593, by rfl⟩ : syracuseStep 2424791 = 3637187) B3637187
theorem B1277927 : Blo 850355 1277927 := bstep (se 1 (by rfl) ⟨958445, by rfl⟩ : syracuseStep 1277927 = 1916891) B1916891
theorem B851999 : Blo 850355 851999 := bstep (se 1 (by rfl) ⟨638999, by rfl⟩ : syracuseStep 851999 = 1277999) B1277999
theorem B1278119 : Blo 850355 1278119 := bstep (se 1 (by rfl) ⟨958589, by rfl⟩ : syracuseStep 1278119 = 1917179) B1917179
theorem B1278377 : Blo 850355 1278377 := bstep (se 2 (by rfl) ⟨479391, by rfl⟩ : syracuseStep 1278377 = 958783) B958783
theorem B1278431 : Blo 850355 1278431 := bstep (se 1 (by rfl) ⟨958823, by rfl⟩ : syracuseStep 1278431 = 1917647) B1917647
theorem B10945799 : Blo 850355 10945799 := bstep (se 1 (by rfl) ⟨8209349, by rfl⟩ : syracuseStep 10945799 = 16418699) B16418699
theorem B1279535 : Blo 850355 1279535 := bstep (se 1 (by rfl) ⟨959651, by rfl⟩ : syracuseStep 1279535 = 1919303) B1919303
theorem B88507993 : Blo 850355 88507993 := bstep (se 2 (by rfl) ⟨33190497, by rfl⟩ : syracuseStep 88507993 = 66380995) B66380995
theorem B853919 : Blo 850355 853919 := bstep (se 1 (by rfl) ⟨640439, by rfl⟩ : syracuseStep 853919 = 1280879) B1280879
theorem B1280063 : Blo 850355 1280063 := bstep (se 1 (by rfl) ⟨960047, by rfl⟩ : syracuseStep 1280063 = 1920095) B1920095
theorem B854107 : Blo 850355 854107 := bstep (se 1 (by rfl) ⟨640580, by rfl⟩ : syracuseStep 854107 = 1281161) B1281161
theorem B1280219 : Blo 850355 1280219 := bstep (se 1 (by rfl) ⟨960164, by rfl⟩ : syracuseStep 1280219 = 1920329) B1920329
theorem B854255 : Blo 850355 854255 := bstep (se 1 (by rfl) ⟨640691, by rfl⟩ : syracuseStep 854255 = 1281383) B1281383
theorem B6654619 : Blo 850355 6654619 := bstep (se 1 (by rfl) ⟨4990964, by rfl⟩ : syracuseStep 6654619 = 9981929) B9981929
theorem B106498871 : Blo 850355 106498871 := bstep (se 1 (by rfl) ⟨79874153, by rfl⟩ : syracuseStep 106498871 = 159748307) B159748307
theorem B1280831 : Blo 850355 1280831 := bstep (se 1 (by rfl) ⟨960623, by rfl⟩ : syracuseStep 1280831 = 1921247) B1921247
theorem B1281017 : Blo 850355 1281017 := bstep (se 2 (by rfl) ⟨480381, by rfl⟩ : syracuseStep 1281017 = 960763) B960763
theorem B1281215 : Blo 850355 1281215 := bstep (se 1 (by rfl) ⟨960911, by rfl⟩ : syracuseStep 1281215 = 1921823) B1921823
theorem B3936377 : Blo 850355 3936377 := bstep (se 2 (by rfl) ⟨1476141, by rfl⟩ : syracuseStep 3936377 = 2952283) B2952283
theorem B12292343 : Blo 850355 12292343 := bstep (se 1 (by rfl) ⟨9219257, by rfl⟩ : syracuseStep 12292343 = 18438515) B18438515
theorem B10359211 : Blo 850355 10359211 := bstep (se 1 (by rfl) ⟨7769408, by rfl⟩ : syracuseStep 10359211 = 15538817) B15538817
theorem B4855049 : Blo 850355 4855049 := bstep (se 2 (by rfl) ⟨1820643, by rfl⟩ : syracuseStep 4855049 = 3641287) B3641287
theorem B2725481 : Blo 850355 2725481 := bstep (se 2 (by rfl) ⟨1022055, by rfl⟩ : syracuseStep 2725481 = 2044111) B2044111
theorem B7018493 : Blo 850355 7018493 := bstep (se 3 (by rfl) ⟨1315967, by rfl⟩ : syracuseStep 7018493 = 2631935) B2631935
theorem B2464249 : Blo 850355 2464249 := bstep (se 2 (by rfl) ⟨924093, by rfl⟩ : syracuseStep 2464249 = 1848187) B1848187
theorem B49128767 : Blo 850355 49128767 := bstep (se 1 (by rfl) ⟨36846575, by rfl⟩ : syracuseStep 49128767 = 73693151) B73693151
theorem B6137639 : Blo 850355 6137639 := bstep (se 1 (by rfl) ⟨4603229, by rfl⟩ : syracuseStep 6137639 = 9206459) B9206459
theorem B1616527 : Blo 850355 1616527 := bstep (se 1 (by rfl) ⟨1212395, by rfl⟩ : syracuseStep 1616527 = 2424791) B2424791
theorem B5450399 : Blo 850355 5450399 := bstep (se 1 (by rfl) ⟨4087799, by rfl⟩ : syracuseStep 5450399 = 8175599) B8175599
theorem B20688833 : Blo 850355 20688833 := bstep (se 2 (by rfl) ⟨7758312, by rfl⟩ : syracuseStep 20688833 = 15516625) B15516625
theorem B2044207 : Blo 850355 2044207 := bstep (se 1 (by rfl) ⟨1533155, by rfl⟩ : syracuseStep 2044207 = 3066311) B3066311
theorem B1913903 : Blo 850355 1913903 := bstep (se 1 (by rfl) ⟨1435427, by rfl⟩ : syracuseStep 1913903 = 2870855) B2870855
theorem B1914335 : Blo 850355 1914335 := bstep (se 1 (by rfl) ⟨1435751, by rfl⟩ : syracuseStep 1914335 = 2871503) B2871503
theorem B1816543 : Blo 850355 1816543 := bstep (se 1 (by rfl) ⟨1362407, by rfl⟩ : syracuseStep 1816543 = 2724815) B2724815
theorem B1914857 : Blo 850355 1914857 := bstep (se 2 (by rfl) ⟨718071, by rfl⟩ : syracuseStep 1914857 = 1436143) B1436143
theorem B179812817 : Blo 850355 179812817 := bstep (se 2 (by rfl) ⟨67429806, by rfl⟩ : syracuseStep 179812817 = 134859613) B134859613
theorem B6470117 : Blo 850355 6470117 := bstep (se 4 (by rfl) ⟨606573, by rfl⟩ : syracuseStep 6470117 = 1213147) B1213147
theorem B33176927 : Blo 850355 33176927 := bstep (se 1 (by rfl) ⟨24882695, by rfl⟩ : syracuseStep 33176927 = 49765391) B49765391
theorem B10928681 : Blo 850355 10928681 := bstep (se 2 (by rfl) ⟨4098255, by rfl⟩ : syracuseStep 10928681 = 8196511) B8196511
theorem B4605977 : Blo 850355 4605977 := bstep (se 2 (by rfl) ⟨1727241, by rfl⟩ : syracuseStep 4605977 = 3454483) B3454483
theorem B1919195 : Blo 850355 1919195 := bstep (se 1 (by rfl) ⟨1439396, by rfl⟩ : syracuseStep 1919195 = 2878793) B2878793
theorem B2870153 : Blo 850355 2870153 := bstep (se 2 (by rfl) ⟨1076307, by rfl⟩ : syracuseStep 2870153 = 2152615) B2152615
theorem B1919951 : Blo 850355 1919951 := bstep (se 1 (by rfl) ⟨1439963, by rfl⟩ : syracuseStep 1919951 = 2879927) B2879927
theorem B7294535 : Blo 850355 7294535 := bstep (se 1 (by rfl) ⟨5470901, by rfl⟩ : syracuseStep 7294535 = 10941803) B10941803
theorem B16371335 : Blo 850355 16371335 := bstep (se 1 (by rfl) ⟨12278501, by rfl⟩ : syracuseStep 16371335 = 24557003) B24557003
theorem B22138751 : Blo 850355 22138751 := bstep (se 1 (by rfl) ⟨16604063, by rfl⟩ : syracuseStep 22138751 = 33208127) B33208127
theorem B2772983 : Blo 850355 2772983 := bstep (se 1 (by rfl) ⟨2079737, by rfl⟩ : syracuseStep 2772983 = 4159475) B4159475
theorem B16404551 : Blo 850355 16404551 := bstep (se 1 (by rfl) ⟨12303413, by rfl⟩ : syracuseStep 16404551 = 24606827) B24606827
theorem B6476435 : Blo 850355 6476435 := bstep (se 1 (by rfl) ⟨4857326, by rfl⟩ : syracuseStep 6476435 = 9714653) B9714653
theorem B5460857 : Blo 850355 5460857 := bstep (se 2 (by rfl) ⟨2047821, by rfl⟩ : syracuseStep 5460857 = 4095643) B4095643
theorem B2872367 : Blo 850355 2872367 := bstep (se 1 (by rfl) ⟨2154275, by rfl⟩ : syracuseStep 2872367 = 4308551) B4308551
theorem B2872583 : Blo 850355 2872583 := bstep (se 1 (by rfl) ⟨2154437, by rfl⟩ : syracuseStep 2872583 = 4308875) B4308875
theorem B3888395 : Blo 850355 3888395 := bstep (se 1 (by rfl) ⟨2916296, by rfl⟩ : syracuseStep 3888395 = 5832593) B5832593
theorem B6477407 : Blo 850355 6477407 := bstep (se 1 (by rfl) ⟨4858055, by rfl⟩ : syracuseStep 6477407 = 9716111) B9716111
theorem B93411143 : Blo 850355 93411143 := bstep (se 1 (by rfl) ⟨70058357, by rfl⟩ : syracuseStep 93411143 = 140116715) B140116715
theorem B2873663 : Blo 850355 2873663 := bstep (se 1 (by rfl) ⟨2155247, by rfl⟩ : syracuseStep 2873663 = 4310495) B4310495
theorem B4315679 : Blo 850355 4315679 := bstep (se 1 (by rfl) ⟨3236759, by rfl⟩ : syracuseStep 4315679 = 6473519) B6473519
theorem B2874095 : Blo 850355 2874095 := bstep (se 1 (by rfl) ⟨2155571, by rfl⟩ : syracuseStep 2874095 = 4311143) B4311143
theorem B4316327 : Blo 850355 4316327 := bstep (se 1 (by rfl) ⟨3237245, by rfl⟩ : syracuseStep 4316327 = 6474491) B6474491
theorem B5463571 : Blo 850355 5463571 := bstep (se 1 (by rfl) ⟨4097678, by rfl⟩ : syracuseStep 5463571 = 8195357) B8195357
theorem B51109667 : Blo 850355 51109667 := bstep (se 1 (by rfl) ⟨38332250, by rfl⟩ : syracuseStep 51109667 = 76664501) B76664501
theorem B2875175 : Blo 850355 2875175 := bstep (se 1 (by rfl) ⟨2156381, by rfl⟩ : syracuseStep 2875175 = 4312763) B4312763
theorem B3235727 : Blo 850355 3235727 := bstep (se 1 (by rfl) ⟨2426795, by rfl⟩ : syracuseStep 3235727 = 4853591) B4853591
theorem B4317947 : Blo 850355 4317947 := bstep (se 1 (by rfl) ⟨3238460, by rfl⟩ : syracuseStep 4317947 = 6476921) B6476921
theorem B4843111 : Blo 850355 4843111 := bstep (se 1 (by rfl) ⟨3632333, by rfl⟩ : syracuseStep 4843111 = 7264667) B7264667
theorem B1436251 : Blo 850355 1436251 := bstep (se 1 (by rfl) ⟨1077188, by rfl⟩ : syracuseStep 1436251 = 2154377) B2154377
theorem B1436393 : Blo 850355 1436393 := bstep (se 2 (by rfl) ⟨538647, by rfl⟩ : syracuseStep 1436393 = 1077295) B1077295
theorem B15953129 : Blo 850355 15953129 := bstep (se 2 (by rfl) ⟨5982423, by rfl⟩ : syracuseStep 15953129 = 11964847) B11964847
theorem B1437817 : Blo 850355 1437817 := bstep (se 2 (by rfl) ⟨539181, by rfl⟩ : syracuseStep 1437817 = 1078363) B1078363
theorem B2879657 : Blo 850355 2879657 := bstep (se 2 (by rfl) ⟨1079871, by rfl⟩ : syracuseStep 2879657 = 2159743) B2159743
theorem B10940831 : Blo 850355 10940831 := bstep (se 1 (by rfl) ⟨8205623, by rfl⟩ : syracuseStep 10940831 = 16411247) B16411247
theorem B3076649 : Blo 850355 3076649 := bstep (se 2 (by rfl) ⟨1153743, by rfl⟩ : syracuseStep 3076649 = 2307487) B2307487
theorem B46625645 : Blo 850355 46625645 := bstep (se 3 (by rfl) ⟨8742308, by rfl⟩ : syracuseStep 46625645 = 17484617) B17484617
theorem B4322159 : Blo 850355 4322159 := bstep (se 1 (by rfl) ⟨3241619, by rfl⟩ : syracuseStep 4322159 = 6483239) B6483239
theorem B1438951 : Blo 850355 1438951 := bstep (se 1 (by rfl) ⟨1079213, by rfl⟩ : syracuseStep 1438951 = 2158427) B2158427
theorem B2160047 : Blo 850355 2160047 := bstep (se 1 (by rfl) ⟨1620035, by rfl⟩ : syracuseStep 2160047 = 3240071) B3240071
theorem B22116311 : Blo 850355 22116311 := bstep (se 1 (by rfl) ⟨16587233, by rfl⟩ : syracuseStep 22116311 = 33174467) B33174467
theorem B1276031 : Blo 850355 1276031 := bstep (se 1 (by rfl) ⟨957023, by rfl⟩ : syracuseStep 1276031 = 1914047) B1914047
theorem B850399 : Blo 850355 850399 := bstep (se 1 (by rfl) ⟨637799, by rfl⟩ : syracuseStep 850399 = 1275599) B1275599
theorem B1276415 : Blo 850355 1276415 := bstep (se 1 (by rfl) ⟨957311, by rfl⟩ : syracuseStep 1276415 = 1914623) B1914623
theorem B850587 : Blo 850355 850587 := bstep (se 1 (by rfl) ⟨637940, by rfl⟩ : syracuseStep 850587 = 1275881) B1275881
theorem B2423515 : Blo 850355 2423515 := bstep (se 1 (by rfl) ⟨1817636, by rfl⟩ : syracuseStep 2423515 = 3635273) B3635273
theorem B2882303 : Blo 850355 2882303 := bstep (se 1 (by rfl) ⟨2161727, by rfl⟩ : syracuseStep 2882303 = 4323455) B4323455
theorem B3243017 : Blo 850355 3243017 := bstep (se 2 (by rfl) ⟨1216131, by rfl⟩ : syracuseStep 3243017 = 2432263) B2432263
theorem B100924879 : Blo 850355 100924879 := bstep (se 1 (by rfl) ⟨75693659, by rfl⟩ : syracuseStep 100924879 = 151387319) B151387319
theorem B1441327 : Blo 850355 1441327 := bstep (se 1 (by rfl) ⟨1080995, by rfl⟩ : syracuseStep 1441327 = 2161991) B2161991
theorem B1277495 : Blo 850355 1277495 := bstep (se 1 (by rfl) ⟨958121, by rfl⟩ : syracuseStep 1277495 = 1916243) B1916243
theorem B11075143 : Blo 850355 11075143 := bstep (se 1 (by rfl) ⟨8306357, by rfl⟩ : syracuseStep 11075143 = 16612715) B16612715
theorem B10354351 : Blo 850355 10354351 := bstep (se 1 (by rfl) ⟨7765763, by rfl⟩ : syracuseStep 10354351 = 15531527) B15531527
theorem B2588527 : Blo 850355 2588527 := bstep (se 1 (by rfl) ⟨1941395, by rfl⟩ : syracuseStep 2588527 = 3882791) B3882791
theorem B1441705 : Blo 850355 1441705 := bstep (se 2 (by rfl) ⟨540639, by rfl⟩ : syracuseStep 1441705 = 1081279) B1081279
theorem B851951 : Blo 850355 851951 := bstep (se 1 (by rfl) ⟨638963, by rfl⟩ : syracuseStep 851951 = 1277927) B1277927
theorem B852079 : Blo 850355 852079 := bstep (se 1 (by rfl) ⟨639059, by rfl⟩ : syracuseStep 852079 = 1278119) B1278119
theorem B852251 : Blo 850355 852251 := bstep (se 1 (by rfl) ⟨639188, by rfl⟩ : syracuseStep 852251 = 1278377) B1278377
theorem B852287 : Blo 850355 852287 := bstep (se 1 (by rfl) ⟨639215, by rfl⟩ : syracuseStep 852287 = 1278431) B1278431
theorem B853023 : Blo 850355 853023 := bstep (se 1 (by rfl) ⟨639767, by rfl⟩ : syracuseStep 853023 = 1279535) B1279535
theorem B853375 : Blo 850355 853375 := bstep (se 1 (by rfl) ⟨640031, by rfl⟩ : syracuseStep 853375 = 1280063) B1280063
theorem B1279463 : Blo 850355 1279463 := bstep (se 1 (by rfl) ⟨959597, by rfl⟩ : syracuseStep 1279463 = 1919195) B1919195
theorem B853479 : Blo 850355 853479 := bstep (se 1 (by rfl) ⟨640109, by rfl⟩ : syracuseStep 853479 = 1280219) B1280219
theorem B853887 : Blo 850355 853887 := bstep (se 1 (by rfl) ⟨640415, by rfl⟩ : syracuseStep 853887 = 1280831) B1280831
theorem B1279967 : Blo 850355 1279967 := bstep (se 1 (by rfl) ⟨959975, by rfl⟩ : syracuseStep 1279967 = 1919951) B1919951
theorem B854011 : Blo 850355 854011 := bstep (se 1 (by rfl) ⟨640508, by rfl⟩ : syracuseStep 854011 = 1281017) B1281017
theorem B854143 : Blo 850355 854143 := bstep (se 1 (by rfl) ⟨640607, by rfl⟩ : syracuseStep 854143 = 1281215) B1281215
theorem B6457481 : Blo 850355 6457481 := bstep (se 2 (by rfl) ⟨2421555, by rfl⟩ : syracuseStep 6457481 = 4843111) B4843111
theorem B10914223 : Blo 850355 10914223 := bstep (se 1 (by rfl) ⟨8185667, by rfl⟩ : syracuseStep 10914223 = 16371335) B16371335
theorem B2624251 : Blo 850355 2624251 := bstep (se 1 (by rfl) ⟨1968188, by rfl⟩ : syracuseStep 2624251 = 3936377) B3936377
theorem B8194895 : Blo 850355 8194895 := bstep (se 1 (by rfl) ⟨6146171, by rfl⟩ : syracuseStep 8194895 = 12292343) B12292343
theorem B3640571 : Blo 850355 3640571 := bstep (se 1 (by rfl) ⟨2730428, by rfl⟩ : syracuseStep 3640571 = 5460857) B5460857
theorem B35491301 : Blo 850355 35491301 := bstep (se 4 (by rfl) ⟨3327309, by rfl⟩ : syracuseStep 35491301 = 6654619) B6654619
theorem B2592263 : Blo 850355 2592263 := bstep (se 1 (by rfl) ⟨1944197, by rfl⟩ : syracuseStep 2592263 = 3888395) B3888395
theorem B18715981 : Blo 850355 18715981 := bstep (se 3 (by rfl) ⟨3509246, by rfl⟩ : syracuseStep 18715981 = 7018493) B7018493
theorem B957595 : Blo 850355 957595 := bstep (se 1 (by rfl) ⟨718196, by rfl⟩ : syracuseStep 957595 = 1436393) B1436393
theorem B3285665 : Blo 850355 3285665 := bstep (se 2 (by rfl) ⟨1232124, by rfl⟩ : syracuseStep 3285665 = 2464249) B2464249
theorem B119875211 : Blo 850355 119875211 := bstep (se 1 (by rfl) ⟨89906408, by rfl⟩ : syracuseStep 119875211 = 179812817) B179812817
theorem B7284761 : Blo 850355 7284761 := bstep (se 2 (by rfl) ⟨2731785, by rfl⟩ : syracuseStep 7284761 = 5463571) B5463571
theorem B13805801 : Blo 850355 13805801 := bstep (se 2 (by rfl) ⟨5177175, by rfl⟩ : syracuseStep 13805801 = 10354351) B10354351
theorem B3451369 : Blo 850355 3451369 := bstep (se 2 (by rfl) ⟨1294263, by rfl⟩ : syracuseStep 3451369 = 2588527) B2588527
theorem B7285787 : Blo 850355 7285787 := bstep (se 1 (by rfl) ⟨5464340, by rfl⟩ : syracuseStep 7285787 = 10928681) B10928681
theorem B1913435 : Blo 850355 1913435 := bstep (se 1 (by rfl) ⟨1435076, by rfl⟩ : syracuseStep 1913435 = 2870153) B2870153
theorem B118010657 : Blo 850355 118010657 := bstep (se 2 (by rfl) ⟨44253996, by rfl⟩ : syracuseStep 118010657 = 88507993) B88507993
theorem B4863023 : Blo 850355 4863023 := bstep (se 1 (by rfl) ⟨3647267, by rfl⟩ : syracuseStep 4863023 = 7294535) B7294535
theorem B14759167 : Blo 850355 14759167 := bstep (se 1 (by rfl) ⟨11069375, by rfl⟩ : syracuseStep 14759167 = 22138751) B22138751
theorem B1848655 : Blo 850355 1848655 := bstep (se 1 (by rfl) ⟨1386491, by rfl⟩ : syracuseStep 1848655 = 2772983) B2772983
theorem B1914911 : Blo 850355 1914911 := bstep (se 1 (by rfl) ⟨1436183, by rfl⟩ : syracuseStep 1914911 = 2872367) B2872367
theorem B1915001 : Blo 850355 1915001 := bstep (se 2 (by rfl) ⟨718125, by rfl⟩ : syracuseStep 1915001 = 1436251) B1436251
theorem B1915055 : Blo 850355 1915055 := bstep (se 1 (by rfl) ⟨1436291, by rfl⟩ : syracuseStep 1915055 = 2872583) B2872583
theorem B1816987 : Blo 850355 1816987 := bstep (se 1 (by rfl) ⟨1362740, by rfl⟩ : syracuseStep 1816987 = 2725481) B2725481
theorem B62274095 : Blo 850355 62274095 := bstep (se 1 (by rfl) ⟨46705571, by rfl⟩ : syracuseStep 62274095 = 93411143) B93411143
theorem B1915775 : Blo 850355 1915775 := bstep (se 1 (by rfl) ⟨1436831, by rfl⟩ : syracuseStep 1915775 = 2873663) B2873663
theorem B1916063 : Blo 850355 1916063 := bstep (se 1 (by rfl) ⟨1437047, by rfl⟩ : syracuseStep 1916063 = 2874095) B2874095
theorem B1916783 : Blo 850355 1916783 := bstep (se 1 (by rfl) ⟨1437587, by rfl⟩ : syracuseStep 1916783 = 2875175) B2875175
theorem B1917089 : Blo 850355 1917089 := bstep (se 2 (by rfl) ⟨718908, by rfl⟩ : syracuseStep 1917089 = 1437817) B1437817
theorem B13812281 : Blo 850355 13812281 := bstep (se 2 (by rfl) ⟨5179605, by rfl⟩ : syracuseStep 13812281 = 10359211) B10359211
theorem B32752511 : Blo 850355 32752511 := bstep (se 1 (by rfl) ⟨24564383, by rfl⟩ : syracuseStep 32752511 = 49128767) B49128767
theorem B1918601 : Blo 850355 1918601 := bstep (se 2 (by rfl) ⟨719475, by rfl⟩ : syracuseStep 1918601 = 1438951) B1438951
theorem B10635419 : Blo 850355 10635419 := bstep (se 1 (by rfl) ⟨7976564, by rfl⟩ : syracuseStep 10635419 = 15953129) B15953129
theorem B1919771 : Blo 850355 1919771 := bstep (se 1 (by rfl) ⟨1439828, by rfl⟩ : syracuseStep 1919771 = 2879657) B2879657
theorem B7293887 : Blo 850355 7293887 := bstep (se 1 (by rfl) ⟨5470415, by rfl⟩ : syracuseStep 7293887 = 10940831) B10940831
theorem B2051099 : Blo 850355 2051099 := bstep (se 1 (by rfl) ⟨1538324, by rfl⟩ : syracuseStep 2051099 = 3076649) B3076649
theorem B31083763 : Blo 850355 31083763 := bstep (se 1 (by rfl) ⟨23312822, by rfl⟩ : syracuseStep 31083763 = 46625645) B46625645
theorem B3231353 : Blo 850355 3231353 := bstep (se 2 (by rfl) ⟨1211757, by rfl⟩ : syracuseStep 3231353 = 2423515) B2423515
theorem B4313411 : Blo 850355 4313411 := bstep (se 1 (by rfl) ⟨3235058, by rfl⟩ : syracuseStep 4313411 = 6470117) B6470117
theorem B1921535 : Blo 850355 1921535 := bstep (se 1 (by rfl) ⟨1441151, by rfl⟩ : syracuseStep 1921535 = 2882303) B2882303
theorem B134566505 : Blo 850355 134566505 := bstep (se 2 (by rfl) ⟨50462439, by rfl⟩ : syracuseStep 134566505 = 100924879) B100924879
theorem B1921769 : Blo 850355 1921769 := bstep (se 2 (by rfl) ⟨720663, by rfl⟩ : syracuseStep 1921769 = 1441327) B1441327
theorem B14766857 : Blo 850355 14766857 := bstep (se 2 (by rfl) ⟨5537571, by rfl⟩ : syracuseStep 14766857 = 11075143) B11075143
theorem B1922273 : Blo 850355 1922273 := bstep (se 2 (by rfl) ⟨720852, by rfl⟩ : syracuseStep 1922273 = 1441705) B1441705
theorem B7297199 : Blo 850355 7297199 := bstep (se 1 (by rfl) ⟨5472899, by rfl⟩ : syracuseStep 7297199 = 10945799) B10945799
theorem B3070651 : Blo 850355 3070651 := bstep (se 1 (by rfl) ⟨2302988, by rfl⟩ : syracuseStep 3070651 = 4605977) B4605977
theorem B10902437 : Blo 850355 10902437 := bstep (se 4 (by rfl) ⟨1022103, by rfl⟩ : syracuseStep 10902437 = 2044207) B2044207
theorem B70999247 : Blo 850355 70999247 := bstep (se 1 (by rfl) ⟨53249435, by rfl⟩ : syracuseStep 70999247 = 106498871) B106498871
theorem B10936367 : Blo 850355 10936367 := bstep (se 1 (by rfl) ⟨8202275, by rfl⟩ : syracuseStep 10936367 = 16404551) B16404551
theorem B4317623 : Blo 850355 4317623 := bstep (se 1 (by rfl) ⟨3238217, by rfl⟩ : syracuseStep 4317623 = 6476435) B6476435
theorem B3236699 : Blo 850355 3236699 := bstep (se 1 (by rfl) ⟨2427524, by rfl⟩ : syracuseStep 3236699 = 4855049) B4855049
theorem B2155369 : Blo 850355 2155369 := bstep (se 2 (by rfl) ⟨808263, by rfl⟩ : syracuseStep 2155369 = 1616527) B1616527
theorem B4318271 : Blo 850355 4318271 := bstep (se 1 (by rfl) ⟨3238703, by rfl⟩ : syracuseStep 4318271 = 6477407) B6477407
theorem B2877119 : Blo 850355 2877119 := bstep (se 1 (by rfl) ⟨2157839, by rfl⟩ : syracuseStep 2877119 = 4315679) B4315679
theorem B2877551 : Blo 850355 2877551 := bstep (se 1 (by rfl) ⟨2158163, by rfl⟩ : syracuseStep 2877551 = 4316327) B4316327
theorem B34073111 : Blo 850355 34073111 := bstep (se 1 (by rfl) ⟨25554833, by rfl⟩ : syracuseStep 34073111 = 51109667) B51109667
theorem B2157151 : Blo 850355 2157151 := bstep (se 1 (by rfl) ⟨1617863, by rfl⟩ : syracuseStep 2157151 = 3235727) B3235727
theorem B2878631 : Blo 850355 2878631 := bstep (se 1 (by rfl) ⟨2158973, by rfl⟩ : syracuseStep 2878631 = 4317947) B4317947
theorem B4091759 : Blo 850355 4091759 := bstep (se 1 (by rfl) ⟨3068819, by rfl⟩ : syracuseStep 4091759 = 6137639) B6137639
theorem B3633599 : Blo 850355 3633599 := bstep (se 1 (by rfl) ⟨2725199, by rfl⟩ : syracuseStep 3633599 = 5450399) B5450399
theorem B2422057 : Blo 850355 2422057 := bstep (se 2 (by rfl) ⟨908271, by rfl⟩ : syracuseStep 2422057 = 1816543) B1816543
theorem B13792555 : Blo 850355 13792555 := bstep (se 1 (by rfl) ⟨10344416, by rfl⟩ : syracuseStep 13792555 = 20688833) B20688833
theorem B2881439 : Blo 850355 2881439 := bstep (se 1 (by rfl) ⟨2161079, by rfl⟩ : syracuseStep 2881439 = 4322159) B4322159
theorem B1275935 : Blo 850355 1275935 := bstep (se 1 (by rfl) ⟨956951, by rfl⟩ : syracuseStep 1275935 = 1913903) B1913903
theorem B1440031 : Blo 850355 1440031 := bstep (se 1 (by rfl) ⟨1080023, by rfl⟩ : syracuseStep 1440031 = 2160047) B2160047
theorem B1276223 : Blo 850355 1276223 := bstep (se 1 (by rfl) ⟨957167, by rfl⟩ : syracuseStep 1276223 = 1914335) B1914335
theorem B14744207 : Blo 850355 14744207 := bstep (se 1 (by rfl) ⟨11058155, by rfl⟩ : syracuseStep 14744207 = 22116311) B22116311
theorem B1276571 : Blo 850355 1276571 := bstep (se 1 (by rfl) ⟨957428, by rfl⟩ : syracuseStep 1276571 = 1914857) B1914857
theorem B850687 : Blo 850355 850687 := bstep (se 1 (by rfl) ⟨638015, by rfl⟩ : syracuseStep 850687 = 1276031) B1276031
theorem B850943 : Blo 850355 850943 := bstep (se 1 (by rfl) ⟨638207, by rfl⟩ : syracuseStep 850943 = 1276415) B1276415
theorem B2162011 : Blo 850355 2162011 := bstep (se 1 (by rfl) ⟨1621508, by rfl⟩ : syracuseStep 2162011 = 3243017) B3243017
theorem B22117951 : Blo 850355 22117951 := bstep (se 1 (by rfl) ⟨16588463, by rfl⟩ : syracuseStep 22117951 = 33176927) B33176927
theorem B851663 : Blo 850355 851663 := bstep (se 1 (by rfl) ⟨638747, by rfl⟩ : syracuseStep 851663 = 1277495) B1277495
theorem B1278059 : Blo 850355 1278059 := bstep (se 1 (by rfl) ⟨958544, by rfl⟩ : syracuseStep 1278059 = 1917089) B1917089
theorem B9208187 : Blo 850355 9208187 := bstep (se 1 (by rfl) ⟨6906140, by rfl⟩ : syracuseStep 9208187 = 13812281) B13812281
theorem B852975 : Blo 850355 852975 := bstep (se 1 (by rfl) ⟨639731, by rfl⟩ : syracuseStep 852975 = 1279463) B1279463
theorem B1279067 : Blo 850355 1279067 := bstep (se 1 (by rfl) ⟨959300, by rfl⟩ : syracuseStep 1279067 = 1918601) B1918601
theorem B853311 : Blo 850355 853311 := bstep (se 1 (by rfl) ⟨639983, by rfl⟩ : syracuseStep 853311 = 1279967) B1279967
theorem B1279847 : Blo 850355 1279847 := bstep (se 1 (by rfl) ⟨959885, by rfl⟩ : syracuseStep 1279847 = 1919771) B1919771
theorem B2427047 : Blo 850355 2427047 := bstep (se 1 (by rfl) ⟨1820285, by rfl⟩ : syracuseStep 2427047 = 3640571) B3640571
theorem B23660867 : Blo 850355 23660867 := bstep (se 1 (by rfl) ⟨17745650, by rfl⟩ : syracuseStep 23660867 = 35491301) B35491301
theorem B1281023 : Blo 850355 1281023 := bstep (se 1 (by rfl) ⟨960767, by rfl⟩ : syracuseStep 1281023 = 1921535) B1921535
theorem B1281179 : Blo 850355 1281179 := bstep (se 1 (by rfl) ⟨960884, by rfl⟩ : syracuseStep 1281179 = 1921769) B1921769
theorem B14552297 : Blo 850355 14552297 := bstep (se 2 (by rfl) ⟨5457111, by rfl⟩ : syracuseStep 14552297 = 10914223) B10914223
theorem B1281515 : Blo 850355 1281515 := bstep (se 1 (by rfl) ⟨961136, by rfl⟩ : syracuseStep 1281515 = 1922273) B1922273
theorem B4856507 : Blo 850355 4856507 := bstep (se 1 (by rfl) ⟨3642380, by rfl⟩ : syracuseStep 4856507 = 7284761) B7284761
theorem B22715407 : Blo 850355 22715407 := bstep (se 1 (by rfl) ⟨17036555, by rfl⟩ : syracuseStep 22715407 = 34073111) B34073111
theorem B18390073 : Blo 850355 18390073 := bstep (se 2 (by rfl) ⟨6896277, by rfl⟩ : syracuseStep 18390073 = 13792555) B13792555
theorem B2464873 : Blo 850355 2464873 := bstep (se 2 (by rfl) ⟨924327, by rfl⟩ : syracuseStep 2464873 = 1848655) B1848655
theorem B4857191 : Blo 850355 4857191 := bstep (se 1 (by rfl) ⟨3642893, by rfl⟩ : syracuseStep 4857191 = 7285787) B7285787
theorem B2727839 : Blo 850355 2727839 := bstep (se 1 (by rfl) ⟨2045879, by rfl⟩ : syracuseStep 2727839 = 4091759) B4091759
theorem B21835007 : Blo 850355 21835007 := bstep (se 1 (by rfl) ⟨16376255, by rfl⟩ : syracuseStep 21835007 = 32752511) B32752511
theorem B4304987 : Blo 850355 4304987 := bstep (se 1 (by rfl) ⟨3228740, by rfl⟩ : syracuseStep 4304987 = 6457481) B6457481
theorem B4862591 : Blo 850355 4862591 := bstep (se 1 (by rfl) ⟨3646943, by rfl⟩ : syracuseStep 4862591 = 7293887) B7293887
theorem B9844571 : Blo 850355 9844571 := bstep (se 1 (by rfl) ⟨7383428, by rfl⟩ : syracuseStep 9844571 = 14766857) B14766857
theorem B4601825 : Blo 850355 4601825 := bstep (se 2 (by rfl) ⟨1725684, by rfl⟩ : syracuseStep 4601825 = 3451369) B3451369
theorem B4864799 : Blo 850355 4864799 := bstep (se 1 (by rfl) ⟨3648599, by rfl⟩ : syracuseStep 4864799 = 7297199) B7297199
theorem B47332831 : Blo 850355 47332831 := bstep (se 1 (by rfl) ⟨35499623, by rfl⟩ : syracuseStep 47332831 = 70999247) B70999247
theorem B7290911 : Blo 850355 7290911 := bstep (se 1 (by rfl) ⟨5468183, by rfl⟩ : syracuseStep 7290911 = 10936367) B10936367
theorem B28361117 : Blo 850355 28361117 := bstep (se 3 (by rfl) ⟨5317709, by rfl⟩ : syracuseStep 28361117 = 10635419) B10635419
theorem B1918079 : Blo 850355 1918079 := bstep (se 1 (by rfl) ⟨1438559, by rfl⟩ : syracuseStep 1918079 = 2877119) B2877119
theorem B1918367 : Blo 850355 1918367 := bstep (se 1 (by rfl) ⟨1438775, by rfl⟩ : syracuseStep 1918367 = 2877551) B2877551
theorem B19678889 : Blo 850355 19678889 := bstep (se 2 (by rfl) ⟨7379583, by rfl⟩ : syracuseStep 19678889 = 14759167) B14759167
theorem B3229409 : Blo 850355 3229409 := bstep (se 2 (by rfl) ⟨1211028, by rfl⟩ : syracuseStep 3229409 = 2422057) B2422057
theorem B24954641 : Blo 850355 24954641 := bstep (se 2 (by rfl) ⟨9357990, by rfl⟩ : syracuseStep 24954641 = 18715981) B18715981
theorem B1919087 : Blo 850355 1919087 := bstep (se 1 (by rfl) ⟨1439315, by rfl⟩ : syracuseStep 1919087 = 2878631) B2878631
theorem B1920041 : Blo 850355 1920041 := bstep (se 2 (by rfl) ⟨720015, by rfl⟩ : syracuseStep 1920041 = 1440031) B1440031
theorem B1920959 : Blo 850355 1920959 := bstep (se 1 (by rfl) ⟨1440719, by rfl⟩ : syracuseStep 1920959 = 2881439) B2881439
theorem B2873825 : Blo 850355 2873825 := bstep (se 2 (by rfl) ⟨1077684, by rfl⟩ : syracuseStep 2873825 = 2155369) B2155369
theorem B5463263 : Blo 850355 5463263 := bstep (se 1 (by rfl) ⟨4097447, by rfl⟩ : syracuseStep 5463263 = 8194895) B8194895
theorem B1367399 : Blo 850355 1367399 := bstep (se 1 (by rfl) ⟨1025549, by rfl⟩ : syracuseStep 1367399 = 2051099) B2051099
theorem B1728175 : Blo 850355 1728175 := bstep (se 1 (by rfl) ⟨1296131, by rfl⟩ : syracuseStep 1728175 = 2592263) B2592263
theorem B2154235 : Blo 850355 2154235 := bstep (se 1 (by rfl) ⟨1615676, by rfl⟩ : syracuseStep 2154235 = 3231353) B3231353
theorem B2875607 : Blo 850355 2875607 := bstep (se 1 (by rfl) ⟨2156705, by rfl⟩ : syracuseStep 2875607 = 4313411) B4313411
theorem B89711003 : Blo 850355 89711003 := bstep (se 1 (by rfl) ⟨67283252, by rfl⟩ : syracuseStep 89711003 = 134566505) B134566505
theorem B2876201 : Blo 850355 2876201 := bstep (se 2 (by rfl) ⟨1078575, by rfl⟩ : syracuseStep 2876201 = 2157151) B2157151
theorem B3499001 : Blo 850355 3499001 := bstep (se 2 (by rfl) ⟨1312125, by rfl⟩ : syracuseStep 3499001 = 2624251) B2624251
theorem B41445017 : Blo 850355 41445017 := bstep (se 2 (by rfl) ⟨15541881, by rfl⟩ : syracuseStep 41445017 = 31083763) B31083763
theorem B7268291 : Blo 850355 7268291 := bstep (se 1 (by rfl) ⟨5451218, by rfl⟩ : syracuseStep 7268291 = 10902437) B10902437
theorem B2878415 : Blo 850355 2878415 := bstep (se 1 (by rfl) ⟨2158811, by rfl⟩ : syracuseStep 2878415 = 4317623) B4317623
theorem B2190443 : Blo 850355 2190443 := bstep (se 1 (by rfl) ⟨1642832, by rfl⟩ : syracuseStep 2190443 = 3285665) B3285665
theorem B2157799 : Blo 850355 2157799 := bstep (se 1 (by rfl) ⟨1618349, by rfl⟩ : syracuseStep 2157799 = 3236699) B3236699
theorem B2878847 : Blo 850355 2878847 := bstep (se 1 (by rfl) ⟨2159135, by rfl⟩ : syracuseStep 2878847 = 4318271) B4318271
theorem B79916807 : Blo 850355 79916807 := bstep (se 1 (by rfl) ⟨59937605, by rfl⟩ : syracuseStep 79916807 = 119875211) B119875211
theorem B9203867 : Blo 850355 9203867 := bstep (se 1 (by rfl) ⟨6902900, by rfl⟩ : syracuseStep 9203867 = 13805801) B13805801
theorem B2422399 : Blo 850355 2422399 := bstep (se 1 (by rfl) ⟨1816799, by rfl⟩ : syracuseStep 2422399 = 3633599) B3633599
theorem B117962405 : Blo 850355 117962405 := bstep (se 4 (by rfl) ⟨11058975, by rfl⟩ : syracuseStep 117962405 = 22117951) B22117951
theorem B1275623 : Blo 850355 1275623 := bstep (se 1 (by rfl) ⟨956717, by rfl⟩ : syracuseStep 1275623 = 1913435) B1913435
theorem B78673771 : Blo 850355 78673771 := bstep (se 1 (by rfl) ⟨59005328, by rfl⟩ : syracuseStep 78673771 = 118010657) B118010657
theorem B2422649 : Blo 850355 2422649 := bstep (se 2 (by rfl) ⟨908493, by rfl⟩ : syracuseStep 2422649 = 1816987) B1816987
theorem B3242015 : Blo 850355 3242015 := bstep (se 1 (by rfl) ⟨2431511, by rfl⟩ : syracuseStep 3242015 = 4863023) B4863023
theorem B4094201 : Blo 850355 4094201 := bstep (se 2 (by rfl) ⟨1535325, by rfl⟩ : syracuseStep 4094201 = 3070651) B3070651
theorem B850623 : Blo 850355 850623 := bstep (se 1 (by rfl) ⟨637967, by rfl⟩ : syracuseStep 850623 = 1275935) B1275935
theorem B1276607 : Blo 850355 1276607 := bstep (se 1 (by rfl) ⟨957455, by rfl⟩ : syracuseStep 1276607 = 1914911) B1914911
theorem B1276667 : Blo 850355 1276667 := bstep (se 1 (by rfl) ⟨957500, by rfl⟩ : syracuseStep 1276667 = 1915001) B1915001
theorem B1276703 : Blo 850355 1276703 := bstep (se 1 (by rfl) ⟨957527, by rfl⟩ : syracuseStep 1276703 = 1915055) B1915055
theorem B1276793 : Blo 850355 1276793 := bstep (se 2 (by rfl) ⟨478797, by rfl⟩ : syracuseStep 1276793 = 957595) B957595
theorem B850815 : Blo 850355 850815 := bstep (se 1 (by rfl) ⟨638111, by rfl⟩ : syracuseStep 850815 = 1276223) B1276223
theorem B41516063 : Blo 850355 41516063 := bstep (se 1 (by rfl) ⟨31137047, by rfl⟩ : syracuseStep 41516063 = 62274095) B62274095
theorem B9829471 : Blo 850355 9829471 := bstep (se 1 (by rfl) ⟨7372103, by rfl⟩ : syracuseStep 9829471 = 14744207) B14744207
theorem B851047 : Blo 850355 851047 := bstep (se 1 (by rfl) ⟨638285, by rfl⟩ : syracuseStep 851047 = 1276571) B1276571
theorem B2882681 : Blo 850355 2882681 := bstep (se 2 (by rfl) ⟨1081005, by rfl⟩ : syracuseStep 2882681 = 2162011) B2162011
theorem B1277183 : Blo 850355 1277183 := bstep (se 1 (by rfl) ⟨957887, by rfl⟩ : syracuseStep 1277183 = 1915775) B1915775
theorem B1277375 : Blo 850355 1277375 := bstep (se 1 (by rfl) ⟨958031, by rfl⟩ : syracuseStep 1277375 = 1916063) B1916063
theorem B1277855 : Blo 850355 1277855 := bstep (se 1 (by rfl) ⟨958391, by rfl⟩ : syracuseStep 1277855 = 1916783) B1916783
theorem B852039 : Blo 850355 852039 := bstep (se 1 (by rfl) ⟨639029, by rfl⟩ : syracuseStep 852039 = 1278059) B1278059
theorem B18907411 : Blo 850355 18907411 := bstep (se 1 (by rfl) ⟨14180558, by rfl⟩ : syracuseStep 18907411 = 28361117) B28361117
theorem B852711 : Blo 850355 852711 := bstep (se 1 (by rfl) ⟨639533, by rfl⟩ : syracuseStep 852711 = 1279067) B1279067
theorem B1278719 : Blo 850355 1278719 := bstep (se 1 (by rfl) ⟨959039, by rfl⟩ : syracuseStep 1278719 = 1918079) B1918079
theorem B1278911 : Blo 850355 1278911 := bstep (se 1 (by rfl) ⟨959183, by rfl⟩ : syracuseStep 1278911 = 1918367) B1918367
theorem B853231 : Blo 850355 853231 := bstep (se 1 (by rfl) ⟨639923, by rfl⟩ : syracuseStep 853231 = 1279847) B1279847
theorem B1279391 : Blo 850355 1279391 := bstep (se 1 (by rfl) ⟨959543, by rfl⟩ : syracuseStep 1279391 = 1919087) B1919087
theorem B854015 : Blo 850355 854015 := bstep (se 1 (by rfl) ⟨640511, by rfl⟩ : syracuseStep 854015 = 1281023) B1281023
theorem B1280027 : Blo 850355 1280027 := bstep (se 1 (by rfl) ⟨960020, by rfl⟩ : syracuseStep 1280027 = 1920041) B1920041
theorem B854119 : Blo 850355 854119 := bstep (se 1 (by rfl) ⟨640589, by rfl⟩ : syracuseStep 854119 = 1281179) B1281179
theorem B9701531 : Blo 850355 9701531 := bstep (se 1 (by rfl) ⟨7276148, by rfl⟩ : syracuseStep 9701531 = 14552297) B14552297
theorem B854343 : Blo 850355 854343 := bstep (se 1 (by rfl) ⟨640757, by rfl⟩ : syracuseStep 854343 = 1281515) B1281515
theorem B1280639 : Blo 850355 1280639 := bstep (se 1 (by rfl) ⟨960479, by rfl⟩ : syracuseStep 1280639 = 1920959) B1920959
theorem B3642175 : Blo 850355 3642175 := bstep (se 1 (by rfl) ⟨2731631, by rfl⟩ : syracuseStep 3642175 = 5463263) B5463263
theorem B6460397 : Blo 850355 6460397 := bstep (se 3 (by rfl) ⟨1211324, by rfl⟩ : syracuseStep 6460397 = 2422649) B2422649
theorem B59807335 : Blo 850355 59807335 := bstep (se 1 (by rfl) ⟨44855501, by rfl⟩ : syracuseStep 59807335 = 89711003) B89711003
theorem B13145989 : Blo 850355 13145989 := bstep (se 4 (by rfl) ⟨1232436, by rfl⟩ : syracuseStep 13145989 = 2464873) B2464873
theorem B2332667 : Blo 850355 2332667 := bstep (se 1 (by rfl) ⟨1749500, by rfl⟩ : syracuseStep 2332667 = 3499001) B3499001
theorem B27630011 : Blo 850355 27630011 := bstep (se 1 (by rfl) ⟨20722508, by rfl⟩ : syracuseStep 27630011 = 41445017) B41445017
theorem B14556671 : Blo 850355 14556671 := bstep (se 1 (by rfl) ⟨10917503, by rfl⟩ : syracuseStep 14556671 = 21835007) B21835007
theorem B104898361 : Blo 850355 104898361 := bstep (se 2 (by rfl) ⟨39336885, by rfl⟩ : syracuseStep 104898361 = 78673771) B78673771
theorem B6135911 : Blo 850355 6135911 := bstep (se 1 (by rfl) ⟨4601933, by rfl⟩ : syracuseStep 6135911 = 9203867) B9203867
theorem B5841181 : Blo 850355 5841181 := bstep (se 3 (by rfl) ⟨1095221, by rfl⟩ : syracuseStep 5841181 = 2190443) B2190443
theorem B3646397 : Blo 850355 3646397 := bstep (se 3 (by rfl) ⟨683699, by rfl⟩ : syracuseStep 3646397 = 1367399) B1367399
theorem B6563047 : Blo 850355 6563047 := bstep (se 1 (by rfl) ⟨4922285, by rfl⟩ : syracuseStep 6563047 = 9844571) B9844571
theorem B30287209 : Blo 850355 30287209 := bstep (se 2 (by rfl) ⟨11357703, by rfl⟩ : syracuseStep 30287209 = 22715407) B22715407
theorem B24520097 : Blo 850355 24520097 := bstep (se 2 (by rfl) ⟨9195036, by rfl⟩ : syracuseStep 24520097 = 18390073) B18390073
theorem B2729467 : Blo 850355 2729467 := bstep (se 1 (by rfl) ⟨2047100, by rfl⟩ : syracuseStep 2729467 = 4094201) B4094201
theorem B2304233 : Blo 850355 2304233 := bstep (se 2 (by rfl) ⟨864087, by rfl⟩ : syracuseStep 2304233 = 1728175) B1728175
theorem B4860607 : Blo 850355 4860607 := bstep (se 1 (by rfl) ⟨3645455, by rfl⟩ : syracuseStep 4860607 = 7290911) B7290911
theorem B6138791 : Blo 850355 6138791 := bstep (se 1 (by rfl) ⟨4604093, by rfl⟩ : syracuseStep 6138791 = 9208187) B9208187
theorem B13119259 : Blo 850355 13119259 := bstep (se 1 (by rfl) ⟨9839444, by rfl⟩ : syracuseStep 13119259 = 19678889) B19678889
theorem B1618031 : Blo 850355 1618031 := bstep (se 1 (by rfl) ⟨1213523, by rfl⟩ : syracuseStep 1618031 = 2427047) B2427047
theorem B1915883 : Blo 850355 1915883 := bstep (se 1 (by rfl) ⟨1436912, by rfl⟩ : syracuseStep 1915883 = 2873825) B2873825
theorem B1818559 : Blo 850355 1818559 := bstep (se 1 (by rfl) ⟨1363919, by rfl⟩ : syracuseStep 1818559 = 2727839) B2727839
theorem B1917071 : Blo 850355 1917071 := bstep (se 1 (by rfl) ⟨1437803, by rfl⟩ : syracuseStep 1917071 = 2875607) B2875607
theorem B1917467 : Blo 850355 1917467 := bstep (se 1 (by rfl) ⟨1438100, by rfl⟩ : syracuseStep 1917467 = 2876201) B2876201
theorem B63095645 : Blo 850355 63095645 := bstep (se 3 (by rfl) ⟨11830433, by rfl⟩ : syracuseStep 63095645 = 23660867) B23660867
theorem B1918943 : Blo 850355 1918943 := bstep (se 1 (by rfl) ⟨1439207, by rfl⟩ : syracuseStep 1918943 = 2878415) B2878415
theorem B3229865 : Blo 850355 3229865 := bstep (se 2 (by rfl) ⟨1211199, by rfl⟩ : syracuseStep 3229865 = 2422399) B2422399
theorem B1919231 : Blo 850355 1919231 := bstep (se 1 (by rfl) ⟨1439423, by rfl⟩ : syracuseStep 1919231 = 2878847) B2878847
theorem B2869991 : Blo 850355 2869991 := bstep (se 1 (by rfl) ⟨2152493, by rfl⟩ : syracuseStep 2869991 = 4304987) B4304987
theorem B3067883 : Blo 850355 3067883 := bstep (se 1 (by rfl) ⟨2300912, by rfl⟩ : syracuseStep 3067883 = 4601825) B4601825
theorem B213111485 : Blo 850355 213111485 := bstep (se 3 (by rfl) ⟨39958403, by rfl⟩ : syracuseStep 213111485 = 79916807) B79916807
theorem B27677375 : Blo 850355 27677375 := bstep (se 1 (by rfl) ⟨20758031, by rfl⟩ : syracuseStep 27677375 = 41516063) B41516063
theorem B1921787 : Blo 850355 1921787 := bstep (se 1 (by rfl) ⟨1441340, by rfl⟩ : syracuseStep 1921787 = 2882681) B2882681
theorem B2872313 : Blo 850355 2872313 := bstep (se 2 (by rfl) ⟨1077117, by rfl⟩ : syracuseStep 2872313 = 2154235) B2154235
theorem B2152939 : Blo 850355 2152939 := bstep (se 1 (by rfl) ⟨1614704, by rfl⟩ : syracuseStep 2152939 = 3229409) B3229409
theorem B16636427 : Blo 850355 16636427 := bstep (se 1 (by rfl) ⟨12477320, by rfl⟩ : syracuseStep 16636427 = 24954641) B24954641
theorem B2877065 : Blo 850355 2877065 := bstep (se 2 (by rfl) ⟨1078899, by rfl⟩ : syracuseStep 2877065 = 2157799) B2157799
theorem B3237671 : Blo 850355 3237671 := bstep (se 1 (by rfl) ⟨2428253, by rfl⟩ : syracuseStep 3237671 = 4856507) B4856507
theorem B3238127 : Blo 850355 3238127 := bstep (se 1 (by rfl) ⟨2428595, by rfl⟩ : syracuseStep 3238127 = 4857191) B4857191
theorem B4845527 : Blo 850355 4845527 := bstep (se 1 (by rfl) ⟨3634145, by rfl⟩ : syracuseStep 4845527 = 7268291) B7268291
theorem B3241727 : Blo 850355 3241727 := bstep (se 1 (by rfl) ⟨2431295, by rfl⟩ : syracuseStep 3241727 = 4862591) B4862591
theorem B78641603 : Blo 850355 78641603 := bstep (se 1 (by rfl) ⟨58981202, by rfl⟩ : syracuseStep 78641603 = 117962405) B117962405
theorem B850415 : Blo 850355 850415 := bstep (se 1 (by rfl) ⟨637811, by rfl⟩ : syracuseStep 850415 = 1275623) B1275623
theorem B2161343 : Blo 850355 2161343 := bstep (se 1 (by rfl) ⟨1621007, by rfl⟩ : syracuseStep 2161343 = 3242015) B3242015
theorem B13105961 : Blo 850355 13105961 := bstep (se 2 (by rfl) ⟨4914735, by rfl⟩ : syracuseStep 13105961 = 9829471) B9829471
theorem B851071 : Blo 850355 851071 := bstep (se 1 (by rfl) ⟨638303, by rfl⟩ : syracuseStep 851071 = 1276607) B1276607
theorem B851111 : Blo 850355 851111 := bstep (se 1 (by rfl) ⟨638333, by rfl⟩ : syracuseStep 851111 = 1276667) B1276667
theorem B851135 : Blo 850355 851135 := bstep (se 1 (by rfl) ⟨638351, by rfl⟩ : syracuseStep 851135 = 1276703) B1276703
theorem B3243199 : Blo 850355 3243199 := bstep (se 1 (by rfl) ⟨2432399, by rfl⟩ : syracuseStep 3243199 = 4864799) B4864799
theorem B851195 : Blo 850355 851195 := bstep (se 1 (by rfl) ⟨638396, by rfl⟩ : syracuseStep 851195 = 1276793) B1276793
theorem B63110441 : Blo 850355 63110441 := bstep (se 2 (by rfl) ⟨23666415, by rfl⟩ : syracuseStep 63110441 = 47332831) B47332831
theorem B851455 : Blo 850355 851455 := bstep (se 1 (by rfl) ⟨638591, by rfl⟩ : syracuseStep 851455 = 1277183) B1277183
theorem B851583 : Blo 850355 851583 := bstep (se 1 (by rfl) ⟨638687, by rfl⟩ : syracuseStep 851583 = 1277375) B1277375
theorem B851903 : Blo 850355 851903 := bstep (se 1 (by rfl) ⟨638927, by rfl⟩ : syracuseStep 851903 = 1277855) B1277855
theorem B1278047 : Blo 850355 1278047 := bstep (se 1 (by rfl) ⟨958535, by rfl⟩ : syracuseStep 1278047 = 1917071) B1917071
theorem B1278311 : Blo 850355 1278311 := bstep (se 1 (by rfl) ⟨958733, by rfl⟩ : syracuseStep 1278311 = 1917467) B1917467
theorem B852479 : Blo 850355 852479 := bstep (se 1 (by rfl) ⟨639359, by rfl⟩ : syracuseStep 852479 = 1278719) B1278719
theorem B852607 : Blo 850355 852607 := bstep (se 1 (by rfl) ⟨639455, by rfl⟩ : syracuseStep 852607 = 1278911) B1278911
theorem B852927 : Blo 850355 852927 := bstep (se 1 (by rfl) ⟨639695, by rfl⟩ : syracuseStep 852927 = 1279391) B1279391
theorem B1279295 : Blo 850355 1279295 := bstep (se 1 (by rfl) ⟨959471, by rfl⟩ : syracuseStep 1279295 = 1918943) B1918943
theorem B853351 : Blo 850355 853351 := bstep (se 1 (by rfl) ⟨640013, by rfl⟩ : syracuseStep 853351 = 1280027) B1280027
theorem B1279487 : Blo 850355 1279487 := bstep (se 1 (by rfl) ⟨959615, by rfl⟩ : syracuseStep 1279487 = 1919231) B1919231
theorem B8750729 : Blo 850355 8750729 := bstep (se 2 (by rfl) ⟨3281523, by rfl⟩ : syracuseStep 8750729 = 6563047) B6563047
theorem B853759 : Blo 850355 853759 := bstep (se 1 (by rfl) ⟨640319, by rfl⟩ : syracuseStep 853759 = 1280639) B1280639
theorem B3639289 : Blo 850355 3639289 := bstep (se 2 (by rfl) ⟨1364733, by rfl⟩ : syracuseStep 3639289 = 2729467) B2729467
theorem B18451583 : Blo 850355 18451583 := bstep (se 1 (by rfl) ⟨13838687, by rfl⟩ : syracuseStep 18451583 = 27677375) B27677375
theorem B1281191 : Blo 850355 1281191 := bstep (se 1 (by rfl) ⟨960893, by rfl⟩ : syracuseStep 1281191 = 1921787) B1921787
theorem B18420007 : Blo 850355 18420007 := bstep (se 1 (by rfl) ⟨13815005, by rfl⟩ : syracuseStep 18420007 = 27630011) B27630011
theorem B9704447 : Blo 850355 9704447 := bstep (se 1 (by rfl) ⟨7278335, by rfl⟩ : syracuseStep 9704447 = 14556671) B14556671
theorem B2430931 : Blo 850355 2430931 := bstep (se 1 (by rfl) ⟨1823198, by rfl⟩ : syracuseStep 2430931 = 3646397) B3646397
theorem B4856233 : Blo 850355 4856233 := bstep (se 2 (by rfl) ⟨1821087, by rfl⟩ : syracuseStep 4856233 = 3642175) B3642175
theorem B139864481 : Blo 850355 139864481 := bstep (se 2 (by rfl) ⟨52449180, by rfl⟩ : syracuseStep 139864481 = 104898361) B104898361
theorem B25209881 : Blo 850355 25209881 := bstep (se 2 (by rfl) ⟨9453705, by rfl⟩ : syracuseStep 25209881 = 18907411) B18907411
theorem B6467687 : Blo 850355 6467687 := bstep (se 1 (by rfl) ⟨4850765, by rfl⟩ : syracuseStep 6467687 = 9701531) B9701531
theorem B40382945 : Blo 850355 40382945 := bstep (se 2 (by rfl) ⟨15143604, by rfl⟩ : syracuseStep 40382945 = 30287209) B30287209
theorem B1913327 : Blo 850355 1913327 := bstep (se 1 (by rfl) ⟨1434995, by rfl⟩ : syracuseStep 1913327 = 2869991) B2869991
theorem B2045255 : Blo 850355 2045255 := bstep (se 1 (by rfl) ⟨1533941, by rfl⟩ : syracuseStep 2045255 = 3067883) B3067883
theorem B4306931 : Blo 850355 4306931 := bstep (se 1 (by rfl) ⟨3230198, by rfl⟩ : syracuseStep 4306931 = 6460397) B6460397
theorem B1914875 : Blo 850355 1914875 := bstep (se 1 (by rfl) ⟨1436156, by rfl⟩ : syracuseStep 1914875 = 2872313) B2872313
theorem B1555111 : Blo 850355 1555111 := bstep (se 1 (by rfl) ⟨1166333, by rfl⟩ : syracuseStep 1555111 = 2332667) B2332667
theorem B11090951 : Blo 850355 11090951 := bstep (se 1 (by rfl) ⟨8318213, by rfl⟩ : syracuseStep 11090951 = 16636427) B16636427
theorem B1918043 : Blo 850355 1918043 := bstep (se 1 (by rfl) ⟨1438532, by rfl⟩ : syracuseStep 1918043 = 2877065) B2877065
theorem B79743113 : Blo 850355 79743113 := bstep (se 2 (by rfl) ⟨29903667, by rfl⟩ : syracuseStep 79743113 = 59807335) B59807335
theorem B3230351 : Blo 850355 3230351 := bstep (se 1 (by rfl) ⟨2422763, by rfl⟩ : syracuseStep 3230351 = 4845527) B4845527
theorem B2870585 : Blo 850355 2870585 := bstep (se 2 (by rfl) ⟨1076469, by rfl⟩ : syracuseStep 2870585 = 2152939) B2152939
theorem B8737307 : Blo 850355 8737307 := bstep (se 1 (by rfl) ⟨6552980, by rfl⟩ : syracuseStep 8737307 = 13105961) B13105961
theorem B7788241 : Blo 850355 7788241 := bstep (se 2 (by rfl) ⟨2920590, by rfl⟩ : syracuseStep 7788241 = 5841181) B5841181
theorem B2153243 : Blo 850355 2153243 := bstep (se 1 (by rfl) ⟨1614932, by rfl⟩ : syracuseStep 2153243 = 3229865) B3229865
theorem B168255053 : Blo 850355 168255053 := bstep (se 3 (by rfl) ⟨31547822, by rfl⟩ : syracuseStep 168255053 = 63095645) B63095645
theorem B142074323 : Blo 850355 142074323 := bstep (se 1 (by rfl) ⟨106555742, by rfl⟩ : syracuseStep 142074323 = 213111485) B213111485
theorem B6480809 : Blo 850355 6480809 := bstep (se 2 (by rfl) ⟨2430303, by rfl⟩ : syracuseStep 6480809 = 4860607) B4860607
theorem B17492345 : Blo 850355 17492345 := bstep (se 2 (by rfl) ⟨6559629, by rfl⟩ : syracuseStep 17492345 = 13119259) B13119259
theorem B4090607 : Blo 850355 4090607 := bstep (se 1 (by rfl) ⟨3067955, by rfl⟩ : syracuseStep 4090607 = 6135911) B6135911
theorem B16346731 : Blo 850355 16346731 := bstep (se 1 (by rfl) ⟨12260048, by rfl⟩ : syracuseStep 16346731 = 24520097) B24520097
theorem B2158447 : Blo 850355 2158447 := bstep (se 1 (by rfl) ⟨1618835, by rfl⟩ : syracuseStep 2158447 = 3237671) B3237671
theorem B1536155 : Blo 850355 1536155 := bstep (se 1 (by rfl) ⟨1152116, by rfl⟩ : syracuseStep 1536155 = 2304233) B2304233
theorem B2158751 : Blo 850355 2158751 := bstep (se 1 (by rfl) ⟨1619063, by rfl⟩ : syracuseStep 2158751 = 3238127) B3238127
theorem B4092527 : Blo 850355 4092527 := bstep (se 1 (by rfl) ⟨3069395, by rfl⟩ : syracuseStep 4092527 = 6138791) B6138791
theorem B17527985 : Blo 850355 17527985 := bstep (se 2 (by rfl) ⟨6572994, by rfl⟩ : syracuseStep 17527985 = 13145989) B13145989
theorem B1078687 : Blo 850355 1078687 := bstep (se 1 (by rfl) ⟨809015, by rfl⟩ : syracuseStep 1078687 = 1618031) B1618031
theorem B2161151 : Blo 850355 2161151 := bstep (se 1 (by rfl) ⟨1620863, by rfl⟩ : syracuseStep 2161151 = 3241727) B3241727
theorem B4324265 : Blo 850355 4324265 := bstep (se 2 (by rfl) ⟨1621599, by rfl⟩ : syracuseStep 4324265 = 3243199) B3243199
theorem B52427735 : Blo 850355 52427735 := bstep (se 1 (by rfl) ⟨39320801, by rfl⟩ : syracuseStep 52427735 = 78641603) B78641603
theorem B1440895 : Blo 850355 1440895 := bstep (se 1 (by rfl) ⟨1080671, by rfl⟩ : syracuseStep 1440895 = 2161343) B2161343
theorem B1277255 : Blo 850355 1277255 := bstep (se 1 (by rfl) ⟨957941, by rfl⟩ : syracuseStep 1277255 = 1915883) B1915883
theorem B42073627 : Blo 850355 42073627 := bstep (se 1 (by rfl) ⟨31555220, by rfl⟩ : syracuseStep 42073627 = 63110441) B63110441
theorem B2424745 : Blo 850355 2424745 := bstep (se 2 (by rfl) ⟨909279, by rfl⟩ : syracuseStep 2424745 = 1818559) B1818559
theorem B852031 : Blo 850355 852031 := bstep (se 1 (by rfl) ⟨639023, by rfl⟩ : syracuseStep 852031 = 1278047) B1278047
theorem B852207 : Blo 850355 852207 := bstep (se 1 (by rfl) ⟨639155, by rfl⟩ : syracuseStep 852207 = 1278311) B1278311
theorem B1278695 : Blo 850355 1278695 := bstep (se 1 (by rfl) ⟨959021, by rfl⟩ : syracuseStep 1278695 = 1918043) B1918043
theorem B852863 : Blo 850355 852863 := bstep (se 1 (by rfl) ⟨639647, by rfl⟩ : syracuseStep 852863 = 1279295) B1279295
theorem B852991 : Blo 850355 852991 := bstep (se 1 (by rfl) ⟨639743, by rfl⟩ : syracuseStep 852991 = 1279487) B1279487
theorem B5833819 : Blo 850355 5833819 := bstep (se 1 (by rfl) ⟨4375364, by rfl⟩ : syracuseStep 5833819 = 8750729) B8750729
theorem B854127 : Blo 850355 854127 := bstep (se 1 (by rfl) ⟨640595, by rfl⟩ : syracuseStep 854127 = 1281191) B1281191
theorem B4852385 : Blo 850355 4852385 := bstep (se 2 (by rfl) ⟨1819644, by rfl⟩ : syracuseStep 4852385 = 3639289) B3639289
theorem B21795641 : Blo 850355 21795641 := bstep (se 2 (by rfl) ⟨8173365, by rfl⟩ : syracuseStep 21795641 = 16346731) B16346731
theorem B112170035 : Blo 850355 112170035 := bstep (se 1 (by rfl) ⟨84127526, by rfl⟩ : syracuseStep 112170035 = 168255053) B168255053
theorem B2727071 : Blo 850355 2727071 := bstep (se 1 (by rfl) ⟨2045303, by rfl⟩ : syracuseStep 2727071 = 4090607) B4090607
theorem B1024103 : Blo 850355 1024103 := bstep (se 1 (by rfl) ⟨768077, by rfl⟩ : syracuseStep 1024103 = 1536155) B1536155
theorem B2728351 : Blo 850355 2728351 := bstep (se 1 (by rfl) ⟨2046263, by rfl⟩ : syracuseStep 2728351 = 4092527) B4092527
theorem B2073481 : Blo 850355 2073481 := bstep (se 2 (by rfl) ⟨777555, by rfl⟩ : syracuseStep 2073481 = 1555111) B1555111
theorem B53162075 : Blo 850355 53162075 := bstep (se 1 (by rfl) ⟨39871556, by rfl⟩ : syracuseStep 53162075 = 79743113) B79743113
theorem B12301055 : Blo 850355 12301055 := bstep (se 1 (by rfl) ⟨9225791, by rfl⟩ : syracuseStep 12301055 = 18451583) B18451583
theorem B1913723 : Blo 850355 1913723 := bstep (se 1 (by rfl) ⟨1435292, by rfl⟩ : syracuseStep 1913723 = 2870585) B2870585
theorem B6469631 : Blo 850355 6469631 := bstep (se 1 (by rfl) ⟨4852223, by rfl⟩ : syracuseStep 6469631 = 9704447) B9704447
theorem B5454013 : Blo 850355 5454013 := bstep (se 3 (by rfl) ⟨1022627, by rfl⟩ : syracuseStep 5454013 = 2045255) B2045255
theorem B94716215 : Blo 850355 94716215 := bstep (se 1 (by rfl) ⟨71037161, by rfl⟩ : syracuseStep 94716215 = 142074323) B142074323
theorem B24560009 : Blo 850355 24560009 := bstep (se 2 (by rfl) ⟨9210003, by rfl⟩ : syracuseStep 24560009 = 18420007) B18420007
theorem B93242987 : Blo 850355 93242987 := bstep (se 1 (by rfl) ⟨69932240, by rfl⟩ : syracuseStep 93242987 = 139864481) B139864481
theorem B4311791 : Blo 850355 4311791 := bstep (se 1 (by rfl) ⟨3233843, by rfl⟩ : syracuseStep 4311791 = 6467687) B6467687
theorem B26921963 : Blo 850355 26921963 := bstep (se 1 (by rfl) ⟨20191472, by rfl⟩ : syracuseStep 26921963 = 40382945) B40382945
theorem B6474977 : Blo 850355 6474977 := bstep (se 2 (by rfl) ⟨2428116, by rfl⟩ : syracuseStep 6474977 = 4856233) B4856233
theorem B11685323 : Blo 850355 11685323 := bstep (se 1 (by rfl) ⟨8763992, by rfl⟩ : syracuseStep 11685323 = 17527985) B17527985
theorem B2871287 : Blo 850355 2871287 := bstep (se 1 (by rfl) ⟨2153465, by rfl⟩ : syracuseStep 2871287 = 4306931) B4306931
theorem B1921193 : Blo 850355 1921193 := bstep (se 2 (by rfl) ⟨720447, by rfl⟩ : syracuseStep 1921193 = 1440895) B1440895
theorem B34951823 : Blo 850355 34951823 := bstep (se 1 (by rfl) ⟨26213867, by rfl⟩ : syracuseStep 34951823 = 52427735) B52427735
theorem B7393967 : Blo 850355 7393967 := bstep (se 1 (by rfl) ⟨5545475, by rfl⟩ : syracuseStep 7393967 = 11090951) B11090951
theorem B3232993 : Blo 850355 3232993 := bstep (se 2 (by rfl) ⟨1212372, by rfl⟩ : syracuseStep 3232993 = 2424745) B2424745
theorem B2153567 : Blo 850355 2153567 := bstep (se 1 (by rfl) ⟨1615175, by rfl⟩ : syracuseStep 2153567 = 3230351) B3230351
theorem B5824871 : Blo 850355 5824871 := bstep (se 1 (by rfl) ⟨4368653, by rfl⟩ : syracuseStep 5824871 = 8737307) B8737307
theorem B1435495 : Blo 850355 1435495 := bstep (se 1 (by rfl) ⟨1076621, by rfl⟩ : syracuseStep 1435495 = 2153243) B2153243
theorem B2877929 : Blo 850355 2877929 := bstep (se 2 (by rfl) ⟨1079223, by rfl⟩ : syracuseStep 2877929 = 2158447) B2158447
theorem B4320539 : Blo 850355 4320539 := bstep (se 1 (by rfl) ⟨3240404, by rfl⟩ : syracuseStep 4320539 = 6480809) B6480809
theorem B11661563 : Blo 850355 11661563 := bstep (se 1 (by rfl) ⟨8746172, by rfl⟩ : syracuseStep 11661563 = 17492345) B17492345
theorem B1438249 : Blo 850355 1438249 := bstep (se 2 (by rfl) ⟨539343, by rfl⟩ : syracuseStep 1438249 = 1078687) B1078687
theorem B16806587 : Blo 850355 16806587 := bstep (se 1 (by rfl) ⟨12604940, by rfl⟩ : syracuseStep 16806587 = 25209881) B25209881
theorem B10384321 : Blo 850355 10384321 := bstep (se 2 (by rfl) ⟨3894120, by rfl⟩ : syracuseStep 10384321 = 7788241) B7788241
theorem B3241241 : Blo 850355 3241241 := bstep (se 2 (by rfl) ⟨1215465, by rfl⟩ : syracuseStep 3241241 = 2430931) B2430931
theorem B1439167 : Blo 850355 1439167 := bstep (se 1 (by rfl) ⟨1079375, by rfl⟩ : syracuseStep 1439167 = 2158751) B2158751
theorem B1275551 : Blo 850355 1275551 := bstep (se 1 (by rfl) ⟨956663, by rfl⟩ : syracuseStep 1275551 = 1913327) B1913327
theorem B1276583 : Blo 850355 1276583 := bstep (se 1 (by rfl) ⟨957437, by rfl⟩ : syracuseStep 1276583 = 1914875) B1914875
theorem B1440767 : Blo 850355 1440767 := bstep (se 1 (by rfl) ⟨1080575, by rfl⟩ : syracuseStep 1440767 = 2161151) B2161151
theorem B2882843 : Blo 850355 2882843 := bstep (se 1 (by rfl) ⟨2162132, by rfl⟩ : syracuseStep 2882843 = 4324265) B4324265
theorem B56098169 : Blo 850355 56098169 := bstep (se 2 (by rfl) ⟨21036813, by rfl⟩ : syracuseStep 56098169 = 42073627) B42073627
theorem B851503 : Blo 850355 851503 := bstep (se 1 (by rfl) ⟨638627, by rfl⟩ : syracuseStep 851503 = 1277255) B1277255
theorem B63144143 : Blo 850355 63144143 := bstep (se 1 (by rfl) ⟨47358107, by rfl⟩ : syracuseStep 63144143 = 94716215) B94716215
theorem B852463 : Blo 850355 852463 := bstep (se 1 (by rfl) ⟨639347, by rfl⟩ : syracuseStep 852463 = 1278695) B1278695
theorem B3637801 : Blo 850355 3637801 := bstep (se 2 (by rfl) ⟨1364175, by rfl⟩ : syracuseStep 3637801 = 2728351) B2728351
theorem B62161991 : Blo 850355 62161991 := bstep (se 1 (by rfl) ⟨46621493, by rfl⟩ : syracuseStep 62161991 = 93242987) B93242987
theorem B1280795 : Blo 850355 1280795 := bstep (se 1 (by rfl) ⟨960596, by rfl⟩ : syracuseStep 1280795 = 1921193) B1921193
theorem B23301215 : Blo 850355 23301215 := bstep (se 1 (by rfl) ⟨17475911, by rfl⟩ : syracuseStep 23301215 = 34951823) B34951823
theorem B74780023 : Blo 850355 74780023 := bstep (se 1 (by rfl) ⟨56085017, by rfl⟩ : syracuseStep 74780023 = 112170035) B112170035
theorem B7774375 : Blo 850355 7774375 := bstep (se 1 (by rfl) ⟨5830781, by rfl⟩ : syracuseStep 7774375 = 11661563) B11661563
theorem B8200703 : Blo 850355 8200703 := bstep (se 1 (by rfl) ⟨6150527, by rfl⟩ : syracuseStep 8200703 = 12301055) B12301055
theorem B960511 : Blo 850355 960511 := bstep (se 1 (by rfl) ⟨720383, by rfl⟩ : syracuseStep 960511 = 1440767) B1440767
theorem B37398779 : Blo 850355 37398779 := bstep (se 1 (by rfl) ⟨28049084, by rfl⟩ : syracuseStep 37398779 = 56098169) B56098169
theorem B2730941 : Blo 850355 2730941 := bstep (se 3 (by rfl) ⟨512051, by rfl⟩ : syracuseStep 2730941 = 1024103) B1024103
theorem B7778425 : Blo 850355 7778425 := bstep (se 2 (by rfl) ⟨2916909, by rfl⟩ : syracuseStep 7778425 = 5833819) B5833819
theorem B1913993 : Blo 850355 1913993 := bstep (se 2 (by rfl) ⟨717747, by rfl⟩ : syracuseStep 1913993 = 1435495) B1435495
theorem B1914191 : Blo 850355 1914191 := bstep (se 1 (by rfl) ⟨1435643, by rfl⟩ : syracuseStep 1914191 = 2871287) B2871287
theorem B4929311 : Blo 850355 4929311 := bstep (se 1 (by rfl) ⟨3696983, by rfl⟩ : syracuseStep 4929311 = 7393967) B7393967
theorem B14530427 : Blo 850355 14530427 := bstep (se 1 (by rfl) ⟨10897820, by rfl⟩ : syracuseStep 14530427 = 21795641) B21795641
theorem B1818047 : Blo 850355 1818047 := bstep (se 1 (by rfl) ⟨1363535, by rfl⟩ : syracuseStep 1818047 = 2727071) B2727071
theorem B3883247 : Blo 850355 3883247 := bstep (se 1 (by rfl) ⟨2912435, by rfl⟩ : syracuseStep 3883247 = 5824871) B5824871
theorem B1917665 : Blo 850355 1917665 := bstep (se 2 (by rfl) ⟨719124, by rfl⟩ : syracuseStep 1917665 = 1438249) B1438249
theorem B13845761 : Blo 850355 13845761 := bstep (se 2 (by rfl) ⟨5192160, by rfl⟩ : syracuseStep 13845761 = 10384321) B10384321
theorem B4310657 : Blo 850355 4310657 := bstep (se 2 (by rfl) ⟨1616496, by rfl⟩ : syracuseStep 4310657 = 3232993) B3232993
theorem B1918619 : Blo 850355 1918619 := bstep (se 1 (by rfl) ⟨1438964, by rfl⟩ : syracuseStep 1918619 = 2877929) B2877929
theorem B1918889 : Blo 850355 1918889 := bstep (se 2 (by rfl) ⟨719583, by rfl⟩ : syracuseStep 1918889 = 1439167) B1439167
theorem B35441383 : Blo 850355 35441383 := bstep (se 1 (by rfl) ⟨26581037, by rfl⟩ : syracuseStep 35441383 = 53162075) B53162075
theorem B4313087 : Blo 850355 4313087 := bstep (se 1 (by rfl) ⟨3234815, by rfl⟩ : syracuseStep 4313087 = 6469631) B6469631
theorem B1921895 : Blo 850355 1921895 := bstep (se 1 (by rfl) ⟨1441421, by rfl⟩ : syracuseStep 1921895 = 2882843) B2882843
theorem B16373339 : Blo 850355 16373339 := bstep (se 1 (by rfl) ⟨12280004, by rfl⟩ : syracuseStep 16373339 = 24560009) B24560009
theorem B3234923 : Blo 850355 3234923 := bstep (se 1 (by rfl) ⟨2426192, by rfl⟩ : syracuseStep 3234923 = 4852385) B4852385
theorem B44817565 : Blo 850355 44817565 := bstep (se 3 (by rfl) ⟨8403293, by rfl⟩ : syracuseStep 44817565 = 16806587) B16806587
theorem B2874527 : Blo 850355 2874527 := bstep (se 1 (by rfl) ⟨2155895, by rfl⟩ : syracuseStep 2874527 = 4311791) B4311791
theorem B17947975 : Blo 850355 17947975 := bstep (se 1 (by rfl) ⟨13460981, by rfl⟩ : syracuseStep 17947975 = 26921963) B26921963
theorem B4316651 : Blo 850355 4316651 := bstep (se 1 (by rfl) ⟨3237488, by rfl⟩ : syracuseStep 4316651 = 6474977) B6474977
theorem B7790215 : Blo 850355 7790215 := bstep (se 1 (by rfl) ⟨5842661, by rfl⟩ : syracuseStep 7790215 = 11685323) B11685323
theorem B1435711 : Blo 850355 1435711 := bstep (se 1 (by rfl) ⟨1076783, by rfl⟩ : syracuseStep 1435711 = 2153567) B2153567
theorem B2880359 : Blo 850355 2880359 := bstep (se 1 (by rfl) ⟨2160269, by rfl⟩ : syracuseStep 2880359 = 4320539) B4320539
theorem B44234261 : Blo 850355 44234261 := bstep (se 6 (by rfl) ⟨1036740, by rfl⟩ : syracuseStep 44234261 = 2073481) B2073481
theorem B7272017 : Blo 850355 7272017 := bstep (se 2 (by rfl) ⟨2727006, by rfl⟩ : syracuseStep 7272017 = 5454013) B5454013
theorem B1275815 : Blo 850355 1275815 := bstep (se 1 (by rfl) ⟨956861, by rfl⟩ : syracuseStep 1275815 = 1913723) B1913723
theorem B2160827 : Blo 850355 2160827 := bstep (se 1 (by rfl) ⟨1620620, by rfl⟩ : syracuseStep 2160827 = 3241241) B3241241
theorem B850367 : Blo 850355 850367 := bstep (se 1 (by rfl) ⟨637775, by rfl⟩ : syracuseStep 850367 = 1275551) B1275551
theorem B851055 : Blo 850355 851055 := bstep (se 1 (by rfl) ⟨638291, by rfl⟩ : syracuseStep 851055 = 1276583) B1276583
theorem B2588831 : Blo 850355 2588831 := bstep (se 1 (by rfl) ⟨1941623, by rfl⟩ : syracuseStep 2588831 = 3883247) B3883247
theorem B1278443 : Blo 850355 1278443 := bstep (se 1 (by rfl) ⟨958832, by rfl⟩ : syracuseStep 1278443 = 1917665) B1917665
theorem B4850401 : Blo 850355 4850401 := bstep (se 2 (by rfl) ⟨1818900, by rfl⟩ : syracuseStep 4850401 = 3637801) B3637801
theorem B1279079 : Blo 850355 1279079 := bstep (se 1 (by rfl) ⟨959309, by rfl⟩ : syracuseStep 1279079 = 1918619) B1918619
theorem B1279259 : Blo 850355 1279259 := bstep (se 1 (by rfl) ⟨959444, by rfl⟩ : syracuseStep 1279259 = 1918889) B1918889
theorem B853863 : Blo 850355 853863 := bstep (se 1 (by rfl) ⟨640397, by rfl⟩ : syracuseStep 853863 = 1280795) B1280795
theorem B15534143 : Blo 850355 15534143 := bstep (se 1 (by rfl) ⟨11650607, by rfl⟩ : syracuseStep 15534143 = 23301215) B23301215
theorem B1280681 : Blo 850355 1280681 := bstep (se 2 (by rfl) ⟨480255, by rfl⟩ : syracuseStep 1280681 = 960511) B960511
theorem B1281263 : Blo 850355 1281263 := bstep (se 1 (by rfl) ⟨960947, by rfl⟩ : syracuseStep 1281263 = 1921895) B1921895
theorem B47255177 : Blo 850355 47255177 := bstep (se 2 (by rfl) ⟨17720691, by rfl⟩ : syracuseStep 47255177 = 35441383) B35441383
theorem B10915559 : Blo 850355 10915559 := bstep (se 1 (by rfl) ⟨8186669, by rfl⟩ : syracuseStep 10915559 = 16373339) B16373339
theorem B3286207 : Blo 850355 3286207 := bstep (se 1 (by rfl) ⟨2464655, by rfl⟩ : syracuseStep 3286207 = 4929311) B4929311
theorem B23930633 : Blo 850355 23930633 := bstep (se 2 (by rfl) ⟨8973987, by rfl⟩ : syracuseStep 23930633 = 17947975) B17947975
theorem B10365833 : Blo 850355 10365833 := bstep (se 2 (by rfl) ⟨3887187, by rfl⟩ : syracuseStep 10365833 = 7774375) B7774375
theorem B1914281 : Blo 850355 1914281 := bstep (se 2 (by rfl) ⟨717855, by rfl⟩ : syracuseStep 1914281 = 1435711) B1435711
theorem B1916351 : Blo 850355 1916351 := bstep (se 1 (by rfl) ⟨1437263, by rfl⟩ : syracuseStep 1916351 = 2874527) B2874527
theorem B10371233 : Blo 850355 10371233 := bstep (se 2 (by rfl) ⟨3889212, by rfl⟩ : syracuseStep 10371233 = 7778425) B7778425
theorem B1820627 : Blo 850355 1820627 := bstep (se 1 (by rfl) ⟨1365470, by rfl⟩ : syracuseStep 1820627 = 2730941) B2730941
theorem B1920239 : Blo 850355 1920239 := bstep (se 1 (by rfl) ⟨1440179, by rfl⟩ : syracuseStep 1920239 = 2880359) B2880359
theorem B9686951 : Blo 850355 9686951 := bstep (se 1 (by rfl) ⟨7265213, by rfl⟩ : syracuseStep 9686951 = 14530427) B14530427
theorem B59756753 : Blo 850355 59756753 := bstep (se 2 (by rfl) ⟨22408782, by rfl⟩ : syracuseStep 59756753 = 44817565) B44817565
theorem B42096095 : Blo 850355 42096095 := bstep (se 1 (by rfl) ⟨31572071, by rfl⟩ : syracuseStep 42096095 = 63144143) B63144143
theorem B41441327 : Blo 850355 41441327 := bstep (se 1 (by rfl) ⟨31080995, by rfl⟩ : syracuseStep 41441327 = 62161991) B62161991
theorem B9230507 : Blo 850355 9230507 := bstep (se 1 (by rfl) ⟨6922880, by rfl⟩ : syracuseStep 9230507 = 13845761) B13845761
theorem B2873771 : Blo 850355 2873771 := bstep (se 1 (by rfl) ⟨2155328, by rfl⟩ : syracuseStep 2873771 = 4310657) B4310657
theorem B2875391 : Blo 850355 2875391 := bstep (se 1 (by rfl) ⟨2156543, by rfl⟩ : syracuseStep 2875391 = 4313087) B4313087
theorem B99706697 : Blo 850355 99706697 := bstep (se 2 (by rfl) ⟨37390011, by rfl⟩ : syracuseStep 99706697 = 74780023) B74780023
theorem B2156615 : Blo 850355 2156615 := bstep (se 1 (by rfl) ⟨1617461, by rfl⟩ : syracuseStep 2156615 = 3234923) B3234923
theorem B2877767 : Blo 850355 2877767 := bstep (se 1 (by rfl) ⟨2158325, by rfl⟩ : syracuseStep 2877767 = 4316651) B4316651
theorem B5467135 : Blo 850355 5467135 := bstep (se 1 (by rfl) ⟨4100351, by rfl⟩ : syracuseStep 5467135 = 8200703) B8200703
theorem B24932519 : Blo 850355 24932519 := bstep (se 1 (by rfl) ⟨18699389, by rfl⟩ : syracuseStep 24932519 = 37398779) B37398779
theorem B1275995 : Blo 850355 1275995 := bstep (se 1 (by rfl) ⟨956996, by rfl⟩ : syracuseStep 1275995 = 1913993) B1913993
theorem B1276127 : Blo 850355 1276127 := bstep (se 1 (by rfl) ⟨957095, by rfl⟩ : syracuseStep 1276127 = 1914191) B1914191
theorem B29489507 : Blo 850355 29489507 := bstep (se 1 (by rfl) ⟨22117130, by rfl⟩ : syracuseStep 29489507 = 44234261) B44234261
theorem B4848011 : Blo 850355 4848011 := bstep (se 1 (by rfl) ⟨3636008, by rfl⟩ : syracuseStep 4848011 = 7272017) B7272017
theorem B850543 : Blo 850355 850543 := bstep (se 1 (by rfl) ⟨637907, by rfl⟩ : syracuseStep 850543 = 1275815) B1275815
theorem B1440551 : Blo 850355 1440551 := bstep (se 1 (by rfl) ⟨1080413, by rfl⟩ : syracuseStep 1440551 = 2160827) B2160827
theorem B10386953 : Blo 850355 10386953 := bstep (se 2 (by rfl) ⟨3895107, by rfl⟩ : syracuseStep 10386953 = 7790215) B7790215
theorem B1212031 : Blo 850355 1212031 := bstep (se 1 (by rfl) ⟨909023, by rfl⟩ : syracuseStep 1212031 = 1818047) B1818047
theorem B6914155 : Blo 850355 6914155 := bstep (se 1 (by rfl) ⟨5185616, by rfl⟩ : syracuseStep 6914155 = 10371233) B10371233
theorem B852295 : Blo 850355 852295 := bstep (se 1 (by rfl) ⟨639221, by rfl⟩ : syracuseStep 852295 = 1278443) B1278443
theorem B852719 : Blo 850355 852719 := bstep (se 1 (by rfl) ⟨639539, by rfl⟩ : syracuseStep 852719 = 1279079) B1279079
theorem B852839 : Blo 850355 852839 := bstep (se 1 (by rfl) ⟨639629, by rfl⟩ : syracuseStep 852839 = 1279259) B1279259
theorem B1213751 : Blo 850355 1213751 := bstep (se 1 (by rfl) ⟨910313, by rfl⟩ : syracuseStep 1213751 = 1820627) B1820627
theorem B10356095 : Blo 850355 10356095 := bstep (se 1 (by rfl) ⟨7767071, by rfl⟩ : syracuseStep 10356095 = 15534143) B15534143
theorem B853787 : Blo 850355 853787 := bstep (se 1 (by rfl) ⟨640340, by rfl⟩ : syracuseStep 853787 = 1280681) B1280681
theorem B1280159 : Blo 850355 1280159 := bstep (se 1 (by rfl) ⟨960119, by rfl⟩ : syracuseStep 1280159 = 1920239) B1920239
theorem B854175 : Blo 850355 854175 := bstep (se 1 (by rfl) ⟨640631, by rfl⟩ : syracuseStep 854175 = 1281263) B1281263
theorem B7277039 : Blo 850355 7277039 := bstep (se 1 (by rfl) ⟨5457779, by rfl⟩ : syracuseStep 7277039 = 10915559) B10915559
theorem B6457967 : Blo 850355 6457967 := bstep (se 1 (by rfl) ⟨4843475, by rfl⟩ : syracuseStep 6457967 = 9686951) B9686951
theorem B27627551 : Blo 850355 27627551 := bstep (se 1 (by rfl) ⟨20720663, by rfl⟩ : syracuseStep 27627551 = 41441327) B41441327
theorem B16621679 : Blo 850355 16621679 := bstep (se 1 (by rfl) ⟨12466259, by rfl⟩ : syracuseStep 16621679 = 24932519) B24932519
theorem B960367 : Blo 850355 960367 := bstep (se 1 (by rfl) ⟨720275, by rfl⟩ : syracuseStep 960367 = 1440551) B1440551
theorem B1616041 : Blo 850355 1616041 := bstep (se 2 (by rfl) ⟨606015, by rfl⟩ : syracuseStep 1616041 = 1212031) B1212031
theorem B6924635 : Blo 850355 6924635 := bstep (se 1 (by rfl) ⟨5193476, by rfl⟩ : syracuseStep 6924635 = 10386953) B10386953
theorem B6467201 : Blo 850355 6467201 := bstep (se 2 (by rfl) ⟨2425200, by rfl⟩ : syracuseStep 6467201 = 4850401) B4850401
theorem B31503451 : Blo 850355 31503451 := bstep (se 1 (by rfl) ⟨23627588, by rfl⟩ : syracuseStep 31503451 = 47255177) B47255177
theorem B28064063 : Blo 850355 28064063 := bstep (se 1 (by rfl) ⟨21048047, by rfl⟩ : syracuseStep 28064063 = 42096095) B42096095
theorem B7289513 : Blo 850355 7289513 := bstep (se 2 (by rfl) ⟨2733567, by rfl⟩ : syracuseStep 7289513 = 5467135) B5467135
theorem B1915847 : Blo 850355 1915847 := bstep (se 1 (by rfl) ⟨1436885, by rfl⟩ : syracuseStep 1915847 = 2873771) B2873771
theorem B1916927 : Blo 850355 1916927 := bstep (se 1 (by rfl) ⟨1437695, by rfl⟩ : syracuseStep 1916927 = 2875391) B2875391
theorem B66471131 : Blo 850355 66471131 := bstep (se 1 (by rfl) ⟨49853348, by rfl⟩ : syracuseStep 66471131 = 99706697) B99706697
theorem B1918511 : Blo 850355 1918511 := bstep (se 1 (by rfl) ⟨1438883, by rfl⟩ : syracuseStep 1918511 = 2877767) B2877767
theorem B3232007 : Blo 850355 3232007 := bstep (se 1 (by rfl) ⟨2424005, by rfl⟩ : syracuseStep 3232007 = 4848011) B4848011
theorem B1725887 : Blo 850355 1725887 := bstep (se 1 (by rfl) ⟨1294415, by rfl⟩ : syracuseStep 1725887 = 2588831) B2588831
theorem B4381609 : Blo 850355 4381609 := bstep (se 2 (by rfl) ⟨1643103, by rfl⟩ : syracuseStep 4381609 = 3286207) B3286207
theorem B39837835 : Blo 850355 39837835 := bstep (se 1 (by rfl) ⟨29878376, by rfl⟩ : syracuseStep 39837835 = 59756753) B59756753
theorem B6153671 : Blo 850355 6153671 := bstep (se 1 (by rfl) ⟨4615253, by rfl⟩ : syracuseStep 6153671 = 9230507) B9230507
theorem B15953755 : Blo 850355 15953755 := bstep (se 1 (by rfl) ⟨11965316, by rfl⟩ : syracuseStep 15953755 = 23930633) B23930633
theorem B1437743 : Blo 850355 1437743 := bstep (se 1 (by rfl) ⟨1078307, by rfl⟩ : syracuseStep 1437743 = 2156615) B2156615
theorem B6910555 : Blo 850355 6910555 := bstep (se 1 (by rfl) ⟨5182916, by rfl⟩ : syracuseStep 6910555 = 10365833) B10365833
theorem B1276187 : Blo 850355 1276187 := bstep (se 1 (by rfl) ⟨957140, by rfl⟩ : syracuseStep 1276187 = 1914281) B1914281
theorem B850663 : Blo 850355 850663 := bstep (se 1 (by rfl) ⟨637997, by rfl⟩ : syracuseStep 850663 = 1275995) B1275995
theorem B850751 : Blo 850355 850751 := bstep (se 1 (by rfl) ⟨638063, by rfl⟩ : syracuseStep 850751 = 1276127) B1276127
theorem B19659671 : Blo 850355 19659671 := bstep (se 1 (by rfl) ⟨14744753, by rfl⟩ : syracuseStep 19659671 = 29489507) B29489507
theorem B1277567 : Blo 850355 1277567 := bstep (se 1 (by rfl) ⟨958175, by rfl⟩ : syracuseStep 1277567 = 1916351) B1916351
theorem B212468453 : Blo 850355 212468453 := bstep (se 4 (by rfl) ⟨19918917, by rfl⟩ : syracuseStep 212468453 = 39837835) B39837835
theorem B1279007 : Blo 850355 1279007 := bstep (se 1 (by rfl) ⟨959255, by rfl⟩ : syracuseStep 1279007 = 1918511) B1918511
theorem B853439 : Blo 850355 853439 := bstep (se 1 (by rfl) ⟨640079, by rfl⟩ : syracuseStep 853439 = 1280159) B1280159
theorem B4851359 : Blo 850355 4851359 := bstep (se 1 (by rfl) ⟨3638519, by rfl⟩ : syracuseStep 4851359 = 7277039) B7277039
theorem B1280489 : Blo 850355 1280489 := bstep (se 2 (by rfl) ⟨480183, by rfl⟩ : syracuseStep 1280489 = 960367) B960367
theorem B18418367 : Blo 850355 18418367 := bstep (se 1 (by rfl) ⟨13813775, by rfl⟩ : syracuseStep 18418367 = 27627551) B27627551
theorem B21271673 : Blo 850355 21271673 := bstep (se 2 (by rfl) ⟨7976877, by rfl⟩ : syracuseStep 21271673 = 15953755) B15953755
theorem B11081119 : Blo 850355 11081119 := bstep (se 1 (by rfl) ⟨8310839, by rfl⟩ : syracuseStep 11081119 = 16621679) B16621679
theorem B9214073 : Blo 850355 9214073 := bstep (se 2 (by rfl) ⟨3455277, by rfl⟩ : syracuseStep 9214073 = 6910555) B6910555
theorem B4102447 : Blo 850355 4102447 := bstep (se 1 (by rfl) ⟨3076835, by rfl⟩ : syracuseStep 4102447 = 6153671) B6153671
theorem B958495 : Blo 850355 958495 := bstep (se 1 (by rfl) ⟨718871, by rfl⟩ : syracuseStep 958495 = 1437743) B1437743
theorem B5842145 : Blo 850355 5842145 := bstep (se 2 (by rfl) ⟨2190804, by rfl⟩ : syracuseStep 5842145 = 4381609) B4381609
theorem B4859675 : Blo 850355 4859675 := bstep (se 1 (by rfl) ⟨3644756, by rfl⟩ : syracuseStep 4859675 = 7289513) B7289513
theorem B9218873 : Blo 850355 9218873 := bstep (se 2 (by rfl) ⟨3457077, by rfl⟩ : syracuseStep 9218873 = 6914155) B6914155
theorem B44314087 : Blo 850355 44314087 := bstep (se 1 (by rfl) ⟨33235565, by rfl⟩ : syracuseStep 44314087 = 66471131) B66471131
theorem B4305311 : Blo 850355 4305311 := bstep (se 1 (by rfl) ⟨3228983, by rfl⟩ : syracuseStep 4305311 = 6457967) B6457967
theorem B4602365 : Blo 850355 4602365 := bstep (se 3 (by rfl) ⟨862943, by rfl⟩ : syracuseStep 4602365 = 1725887) B1725887
theorem B4311467 : Blo 850355 4311467 := bstep (se 1 (by rfl) ⟨3233600, by rfl⟩ : syracuseStep 4311467 = 6467201) B6467201
theorem B6904063 : Blo 850355 6904063 := bstep (se 1 (by rfl) ⟨5178047, by rfl⟩ : syracuseStep 6904063 = 10356095) B10356095
theorem B2154671 : Blo 850355 2154671 := bstep (se 1 (by rfl) ⟨1616003, by rfl⟩ : syracuseStep 2154671 = 3232007) B3232007
theorem B2154721 : Blo 850355 2154721 := bstep (se 2 (by rfl) ⟨808020, by rfl⟩ : syracuseStep 2154721 = 1616041) B1616041
theorem B3236669 : Blo 850355 3236669 := bstep (se 3 (by rfl) ⟨606875, by rfl⟩ : syracuseStep 3236669 = 1213751) B1213751
theorem B42004601 : Blo 850355 42004601 := bstep (se 2 (by rfl) ⟨15751725, by rfl⟩ : syracuseStep 42004601 = 31503451) B31503451
theorem B4616423 : Blo 850355 4616423 := bstep (se 1 (by rfl) ⟨3462317, by rfl⟩ : syracuseStep 4616423 = 6924635) B6924635
theorem B850791 : Blo 850355 850791 := bstep (se 1 (by rfl) ⟨638093, by rfl⟩ : syracuseStep 850791 = 1276187) B1276187
theorem B18709375 : Blo 850355 18709375 := bstep (se 1 (by rfl) ⟨14032031, by rfl⟩ : syracuseStep 18709375 = 28064063) B28064063
theorem B13106447 : Blo 850355 13106447 := bstep (se 1 (by rfl) ⟨9829835, by rfl⟩ : syracuseStep 13106447 = 19659671) B19659671
theorem B1277231 : Blo 850355 1277231 := bstep (se 1 (by rfl) ⟨957923, by rfl⟩ : syracuseStep 1277231 = 1915847) B1915847
theorem B851711 : Blo 850355 851711 := bstep (se 1 (by rfl) ⟨638783, by rfl⟩ : syracuseStep 851711 = 1277567) B1277567
theorem B1277951 : Blo 850355 1277951 := bstep (se 1 (by rfl) ⟨958463, by rfl⟩ : syracuseStep 1277951 = 1916927) B1916927
theorem B1277993 : Blo 850355 1277993 := bstep (se 2 (by rfl) ⟨479247, by rfl⟩ : syracuseStep 1277993 = 958495) B958495
theorem B852671 : Blo 850355 852671 := bstep (se 1 (by rfl) ⟨639503, by rfl⟩ : syracuseStep 852671 = 1279007) B1279007
theorem B853659 : Blo 850355 853659 := bstep (se 1 (by rfl) ⟨640244, by rfl⟩ : syracuseStep 853659 = 1280489) B1280489
theorem B56724461 : Blo 850355 56724461 := bstep (se 3 (by rfl) ⟨10635836, by rfl⟩ : syracuseStep 56724461 = 21271673) B21271673
theorem B59085449 : Blo 850355 59085449 := bstep (se 2 (by rfl) ⟨22157043, by rfl⟩ : syracuseStep 59085449 = 44314087) B44314087
theorem B24945833 : Blo 850355 24945833 := bstep (se 2 (by rfl) ⟨9354687, by rfl⟩ : syracuseStep 24945833 = 18709375) B18709375
theorem B6142715 : Blo 850355 6142715 := bstep (se 1 (by rfl) ⟨4607036, by rfl⟩ : syracuseStep 6142715 = 9214073) B9214073
theorem B6145915 : Blo 850355 6145915 := bstep (se 1 (by rfl) ⟨4609436, by rfl⟩ : syracuseStep 6145915 = 9218873) B9218873
theorem B28003067 : Blo 850355 28003067 := bstep (se 1 (by rfl) ⟨21002300, by rfl⟩ : syracuseStep 28003067 = 42004601) B42004601
theorem B2870207 : Blo 850355 2870207 := bstep (se 1 (by rfl) ⟨2152655, by rfl⟩ : syracuseStep 2870207 = 4305311) B4305311
theorem B3068243 : Blo 850355 3068243 := bstep (se 1 (by rfl) ⟨2301182, by rfl⟩ : syracuseStep 3068243 = 4602365) B4602365
theorem B8737631 : Blo 850355 8737631 := bstep (se 1 (by rfl) ⟨6553223, by rfl⟩ : syracuseStep 8737631 = 13106447) B13106447
theorem B2872961 : Blo 850355 2872961 := bstep (se 2 (by rfl) ⟨1077360, by rfl⟩ : syracuseStep 2872961 = 2154721) B2154721
theorem B141645635 : Blo 850355 141645635 := bstep (se 1 (by rfl) ⟨106234226, by rfl⟩ : syracuseStep 141645635 = 212468453) B212468453
theorem B3234239 : Blo 850355 3234239 := bstep (se 1 (by rfl) ⟨2425679, by rfl⟩ : syracuseStep 3234239 = 4851359) B4851359
theorem B2874311 : Blo 850355 2874311 := bstep (se 1 (by rfl) ⟨2155733, by rfl⟩ : syracuseStep 2874311 = 4311467) B4311467
theorem B12278911 : Blo 850355 12278911 := bstep (se 1 (by rfl) ⟨9209183, by rfl⟩ : syracuseStep 12278911 = 18418367) B18418367
theorem B851967 : Blo 850355 851967 := bstep (se 1 (by rfl) ⟨638975, by rfl⟩ : syracuseStep 851967 = 1277951) B1277951
theorem B1436447 : Blo 850355 1436447 := bstep (se 1 (by rfl) ⟨1077335, by rfl⟩ : syracuseStep 1436447 = 2154671) B2154671
theorem B2157779 : Blo 850355 2157779 := bstep (se 1 (by rfl) ⟨1618334, by rfl⟩ : syracuseStep 2157779 = 3236669) B3236669
theorem B3894763 : Blo 850355 3894763 := bstep (se 1 (by rfl) ⟨2921072, by rfl⟩ : syracuseStep 3894763 = 5842145) B5842145
theorem B3239783 : Blo 850355 3239783 := bstep (se 1 (by rfl) ⟨2429837, by rfl⟩ : syracuseStep 3239783 = 4859675) B4859675
theorem B14774825 : Blo 850355 14774825 := bstep (se 2 (by rfl) ⟨5540559, by rfl⟩ : syracuseStep 14774825 = 11081119) B11081119
theorem B3077615 : Blo 850355 3077615 := bstep (se 1 (by rfl) ⟨2308211, by rfl⟩ : syracuseStep 3077615 = 4616423) B4616423
theorem B9205417 : Blo 850355 9205417 := bstep (se 2 (by rfl) ⟨3452031, by rfl⟩ : syracuseStep 9205417 = 6904063) B6904063
theorem B5469929 : Blo 850355 5469929 := bstep (se 2 (by rfl) ⟨2051223, by rfl⟩ : syracuseStep 5469929 = 4102447) B4102447
theorem B851487 : Blo 850355 851487 := bstep (se 1 (by rfl) ⟨638615, by rfl⟩ : syracuseStep 851487 = 1277231) B1277231
theorem B851995 : Blo 850355 851995 := bstep (se 1 (by rfl) ⟨638996, by rfl⟩ : syracuseStep 851995 = 1277993) B1277993
theorem B37816307 : Blo 850355 37816307 := bstep (se 1 (by rfl) ⟨28362230, by rfl⟩ : syracuseStep 37816307 = 56724461) B56724461
theorem B8194553 : Blo 850355 8194553 := bstep (se 2 (by rfl) ⟨3072957, by rfl⟩ : syracuseStep 8194553 = 6145915) B6145915
theorem B39390299 : Blo 850355 39390299 := bstep (se 1 (by rfl) ⟨29542724, by rfl⟩ : syracuseStep 39390299 = 59085449) B59085449
theorem B66522221 : Blo 850355 66522221 := bstep (se 3 (by rfl) ⟨12472916, by rfl⟩ : syracuseStep 66522221 = 24945833) B24945833
theorem B957631 : Blo 850355 957631 := bstep (se 1 (by rfl) ⟨718223, by rfl⟩ : syracuseStep 957631 = 1436447) B1436447
theorem B3646619 : Blo 850355 3646619 := bstep (se 1 (by rfl) ⟨2734964, by rfl⟩ : syracuseStep 3646619 = 5469929) B5469929
theorem B1913471 : Blo 850355 1913471 := bstep (se 1 (by rfl) ⟨1435103, by rfl⟩ : syracuseStep 1913471 = 2870207) B2870207
theorem B2045495 : Blo 850355 2045495 := bstep (se 1 (by rfl) ⟨1534121, by rfl⟩ : syracuseStep 2045495 = 3068243) B3068243
theorem B1915307 : Blo 850355 1915307 := bstep (se 1 (by rfl) ⟨1436480, by rfl⟩ : syracuseStep 1915307 = 2872961) B2872961
theorem B1916207 : Blo 850355 1916207 := bstep (se 1 (by rfl) ⟨1437155, by rfl⟩ : syracuseStep 1916207 = 2874311) B2874311
theorem B5193017 : Blo 850355 5193017 := bstep (se 2 (by rfl) ⟨1947381, by rfl⟩ : syracuseStep 5193017 = 3894763) B3894763
theorem B12273889 : Blo 850355 12273889 := bstep (se 2 (by rfl) ⟨4602708, by rfl⟩ : syracuseStep 12273889 = 9205417) B9205417
theorem B9849883 : Blo 850355 9849883 := bstep (se 1 (by rfl) ⟨7387412, by rfl⟩ : syracuseStep 9849883 = 14774825) B14774825
theorem B2051743 : Blo 850355 2051743 := bstep (se 1 (by rfl) ⟨1538807, by rfl⟩ : syracuseStep 2051743 = 3077615) B3077615
theorem B16371881 : Blo 850355 16371881 := bstep (se 2 (by rfl) ⟨6139455, by rfl⟩ : syracuseStep 16371881 = 12278911) B12278911
theorem B18668711 : Blo 850355 18668711 := bstep (se 1 (by rfl) ⟨14001533, by rfl⟩ : syracuseStep 18668711 = 28003067) B28003067
theorem B5825087 : Blo 850355 5825087 := bstep (se 1 (by rfl) ⟨4368815, by rfl⟩ : syracuseStep 5825087 = 8737631) B8737631
theorem B94430423 : Blo 850355 94430423 := bstep (se 1 (by rfl) ⟨70822817, by rfl⟩ : syracuseStep 94430423 = 141645635) B141645635
theorem B2156159 : Blo 850355 2156159 := bstep (se 1 (by rfl) ⟨1617119, by rfl⟩ : syracuseStep 2156159 = 3234239) B3234239
theorem B1438519 : Blo 850355 1438519 := bstep (se 1 (by rfl) ⟨1078889, by rfl⟩ : syracuseStep 1438519 = 2157779) B2157779
theorem B2159855 : Blo 850355 2159855 := bstep (se 1 (by rfl) ⟨1619891, by rfl⟩ : syracuseStep 2159855 = 3239783) B3239783
theorem B4095143 : Blo 850355 4095143 := bstep (se 1 (by rfl) ⟨3071357, by rfl⟩ : syracuseStep 4095143 = 6142715) B6142715
theorem B10914587 : Blo 850355 10914587 := bstep (se 1 (by rfl) ⟨8185940, by rfl⟩ : syracuseStep 10914587 = 16371881) B16371881
theorem B2431079 : Blo 850355 2431079 := bstep (se 1 (by rfl) ⟨1823309, by rfl⟩ : syracuseStep 2431079 = 3646619) B3646619
theorem B62953615 : Blo 850355 62953615 := bstep (se 1 (by rfl) ⟨47215211, by rfl⟩ : syracuseStep 62953615 = 94430423) B94430423
theorem B2730095 : Blo 850355 2730095 := bstep (se 1 (by rfl) ⟨2047571, by rfl⟩ : syracuseStep 2730095 = 4095143) B4095143
theorem B25210871 : Blo 850355 25210871 := bstep (se 1 (by rfl) ⟨18908153, by rfl⟩ : syracuseStep 25210871 = 37816307) B37816307
theorem B26260199 : Blo 850355 26260199 := bstep (se 1 (by rfl) ⟨19695149, by rfl⟩ : syracuseStep 26260199 = 39390299) B39390299
theorem B44348147 : Blo 850355 44348147 := bstep (se 1 (by rfl) ⟨33261110, by rfl⟩ : syracuseStep 44348147 = 66522221) B66522221
theorem B16365185 : Blo 850355 16365185 := bstep (se 2 (by rfl) ⟨6136944, by rfl⟩ : syracuseStep 16365185 = 12273889) B12273889
theorem B2735657 : Blo 850355 2735657 := bstep (se 2 (by rfl) ⟨1025871, by rfl⟩ : syracuseStep 2735657 = 2051743) B2051743
theorem B3883391 : Blo 850355 3883391 := bstep (se 1 (by rfl) ⟨2912543, by rfl⟩ : syracuseStep 3883391 = 5825087) B5825087
theorem B1918025 : Blo 850355 1918025 := bstep (se 2 (by rfl) ⟨719259, by rfl⟩ : syracuseStep 1918025 = 1438519) B1438519
theorem B1363663 : Blo 850355 1363663 := bstep (se 1 (by rfl) ⟨1022747, by rfl⟩ : syracuseStep 1363663 = 2045495) B2045495
theorem B3462011 : Blo 850355 3462011 := bstep (se 1 (by rfl) ⟨2596508, by rfl⟩ : syracuseStep 3462011 = 5193017) B5193017
theorem B5463035 : Blo 850355 5463035 := bstep (se 1 (by rfl) ⟨4097276, by rfl⟩ : syracuseStep 5463035 = 8194553) B8194553
theorem B13133177 : Blo 850355 13133177 := bstep (se 2 (by rfl) ⟨4924941, by rfl⟩ : syracuseStep 13133177 = 9849883) B9849883
theorem B12445807 : Blo 850355 12445807 := bstep (se 1 (by rfl) ⟨9334355, by rfl⟩ : syracuseStep 12445807 = 18668711) B18668711
theorem B1437439 : Blo 850355 1437439 := bstep (se 1 (by rfl) ⟨1078079, by rfl⟩ : syracuseStep 1437439 = 2156159) B2156159
theorem B1275647 : Blo 850355 1275647 := bstep (se 1 (by rfl) ⟨956735, by rfl⟩ : syracuseStep 1275647 = 1913471) B1913471
theorem B1439903 : Blo 850355 1439903 := bstep (se 1 (by rfl) ⟨1079927, by rfl⟩ : syracuseStep 1439903 = 2159855) B2159855
theorem B1276841 : Blo 850355 1276841 := bstep (se 2 (by rfl) ⟨478815, by rfl⟩ : syracuseStep 1276841 = 957631) B957631
theorem B1276871 : Blo 850355 1276871 := bstep (se 1 (by rfl) ⟨957653, by rfl⟩ : syracuseStep 1276871 = 1915307) B1915307
theorem B1277471 : Blo 850355 1277471 := bstep (se 1 (by rfl) ⟨958103, by rfl⟩ : syracuseStep 1277471 = 1916207) B1916207
theorem B2588927 : Blo 850355 2588927 := bstep (se 1 (by rfl) ⟨1941695, by rfl⟩ : syracuseStep 2588927 = 3883391) B3883391
theorem B1278683 : Blo 850355 1278683 := bstep (se 1 (by rfl) ⟨959012, by rfl⟩ : syracuseStep 1278683 = 1918025) B1918025
theorem B7276391 : Blo 850355 7276391 := bstep (se 1 (by rfl) ⟨5457293, by rfl⟩ : syracuseStep 7276391 = 10914587) B10914587
theorem B3642023 : Blo 850355 3642023 := bstep (se 1 (by rfl) ⟨2731517, by rfl⟩ : syracuseStep 3642023 = 5463035) B5463035
theorem B8755451 : Blo 850355 8755451 := bstep (se 1 (by rfl) ⟨6566588, by rfl⟩ : syracuseStep 8755451 = 13133177) B13133177
theorem B17506799 : Blo 850355 17506799 := bstep (se 1 (by rfl) ⟨13130099, by rfl⟩ : syracuseStep 17506799 = 26260199) B26260199
theorem B29565431 : Blo 850355 29565431 := bstep (se 1 (by rfl) ⟨22174073, by rfl⟩ : syracuseStep 29565431 = 44348147) B44348147
theorem B959935 : Blo 850355 959935 := bstep (se 1 (by rfl) ⟨719951, by rfl⟩ : syracuseStep 959935 = 1439903) B1439903
theorem B16594409 : Blo 850355 16594409 := bstep (se 2 (by rfl) ⟨6222903, by rfl⟩ : syracuseStep 16594409 = 12445807) B12445807
theorem B2308007 : Blo 850355 2308007 := bstep (se 1 (by rfl) ⟨1731005, by rfl⟩ : syracuseStep 2308007 = 3462011) B3462011
theorem B1620719 : Blo 850355 1620719 := bstep (se 1 (by rfl) ⟨1215539, by rfl⟩ : syracuseStep 1620719 = 2431079) B2431079
theorem B1818217 : Blo 850355 1818217 := bstep (se 2 (by rfl) ⟨681831, by rfl⟩ : syracuseStep 1818217 = 1363663) B1363663
theorem B1916585 : Blo 850355 1916585 := bstep (se 2 (by rfl) ⟨718719, by rfl⟩ : syracuseStep 1916585 = 1437439) B1437439
theorem B1820063 : Blo 850355 1820063 := bstep (se 1 (by rfl) ⟨1365047, by rfl⟩ : syracuseStep 1820063 = 2730095) B2730095
theorem B83938153 : Blo 850355 83938153 := bstep (se 2 (by rfl) ⟨31476807, by rfl⟩ : syracuseStep 83938153 = 62953615) B62953615
theorem B1823771 : Blo 850355 1823771 := bstep (se 1 (by rfl) ⟨1367828, by rfl⟩ : syracuseStep 1823771 = 2735657) B2735657
theorem B16807247 : Blo 850355 16807247 := bstep (se 1 (by rfl) ⟨12605435, by rfl⟩ : syracuseStep 16807247 = 25210871) B25210871
theorem B10910123 : Blo 850355 10910123 := bstep (se 1 (by rfl) ⟨8182592, by rfl⟩ : syracuseStep 10910123 = 16365185) B16365185
theorem B850431 : Blo 850355 850431 := bstep (se 1 (by rfl) ⟨637823, by rfl⟩ : syracuseStep 850431 = 1275647) B1275647
theorem B851227 : Blo 850355 851227 := bstep (se 1 (by rfl) ⟨638420, by rfl⟩ : syracuseStep 851227 = 1276841) B1276841
theorem B851247 : Blo 850355 851247 := bstep (se 1 (by rfl) ⟨638435, by rfl⟩ : syracuseStep 851247 = 1276871) B1276871
theorem B851647 : Blo 850355 851647 := bstep (se 1 (by rfl) ⟨638735, by rfl⟩ : syracuseStep 851647 = 1277471) B1277471
theorem B852455 : Blo 850355 852455 := bstep (se 1 (by rfl) ⟨639341, by rfl⟩ : syracuseStep 852455 = 1278683) B1278683
theorem B1213375 : Blo 850355 1213375 := bstep (se 1 (by rfl) ⟨910031, by rfl⟩ : syracuseStep 1213375 = 1820063) B1820063
theorem B4850927 : Blo 850355 4850927 := bstep (se 1 (by rfl) ⟨3638195, by rfl⟩ : syracuseStep 4850927 = 7276391) B7276391
theorem B1279913 : Blo 850355 1279913 := bstep (se 2 (by rfl) ⟨479967, by rfl⟩ : syracuseStep 1279913 = 959935) B959935
theorem B2428015 : Blo 850355 2428015 := bstep (se 1 (by rfl) ⟨1821011, by rfl⟩ : syracuseStep 2428015 = 3642023) B3642023
theorem B1215847 : Blo 850355 1215847 := bstep (se 1 (by rfl) ⟨911885, by rfl⟩ : syracuseStep 1215847 = 1823771) B1823771
theorem B5836967 : Blo 850355 5836967 := bstep (se 1 (by rfl) ⟨4377725, by rfl⟩ : syracuseStep 5836967 = 8755451) B8755451
theorem B11671199 : Blo 850355 11671199 := bstep (se 1 (by rfl) ⟨8753399, by rfl⟩ : syracuseStep 11671199 = 17506799) B17506799
theorem B111917537 : Blo 850355 111917537 := bstep (se 2 (by rfl) ⟨41969076, by rfl⟩ : syracuseStep 111917537 = 83938153) B83938153
theorem B19710287 : Blo 850355 19710287 := bstep (se 1 (by rfl) ⟨14782715, by rfl⟩ : syracuseStep 19710287 = 29565431) B29565431
theorem B11062939 : Blo 850355 11062939 := bstep (se 1 (by rfl) ⟨8297204, by rfl⟩ : syracuseStep 11062939 = 16594409) B16594409
theorem B6903805 : Blo 850355 6903805 := bstep (se 3 (by rfl) ⟨1294463, by rfl⟩ : syracuseStep 6903805 = 2588927) B2588927
theorem B9697157 : Blo 850355 9697157 := bstep (se 4 (by rfl) ⟨909108, by rfl⟩ : syracuseStep 9697157 = 1818217) B1818217
theorem B11204831 : Blo 850355 11204831 := bstep (se 1 (by rfl) ⟨8403623, by rfl⟩ : syracuseStep 11204831 = 16807247) B16807247
theorem B1538671 : Blo 850355 1538671 := bstep (se 1 (by rfl) ⟨1154003, by rfl⟩ : syracuseStep 1538671 = 2308007) B2308007
theorem B7273415 : Blo 850355 7273415 := bstep (se 1 (by rfl) ⟨5455061, by rfl⟩ : syracuseStep 7273415 = 10910123) B10910123
theorem B1080479 : Blo 850355 1080479 := bstep (se 1 (by rfl) ⟨810359, by rfl⟩ : syracuseStep 1080479 = 1620719) B1620719
theorem B1277723 : Blo 850355 1277723 := bstep (se 1 (by rfl) ⟨958292, by rfl⟩ : syracuseStep 1277723 = 1916585) B1916585
theorem B13140191 : Blo 850355 13140191 := bstep (se 1 (by rfl) ⟨9855143, by rfl⟩ : syracuseStep 13140191 = 19710287) B19710287
theorem B853275 : Blo 850355 853275 := bstep (se 1 (by rfl) ⟨639956, by rfl⟩ : syracuseStep 853275 = 1279913) B1279913
theorem B14750585 : Blo 850355 14750585 := bstep (se 2 (by rfl) ⟨5531469, by rfl⟩ : syracuseStep 14750585 = 11062939) B11062939
theorem B6464771 : Blo 850355 6464771 := bstep (se 1 (by rfl) ⟨4848578, by rfl⟩ : syracuseStep 6464771 = 9697157) B9697157
theorem B1617833 : Blo 850355 1617833 := bstep (se 2 (by rfl) ⟨606687, by rfl⟩ : syracuseStep 1617833 = 1213375) B1213375
theorem B7780799 : Blo 850355 7780799 := bstep (se 1 (by rfl) ⟨5835599, by rfl⟩ : syracuseStep 7780799 = 11671199) B11671199
theorem B1621129 : Blo 850355 1621129 := bstep (se 2 (by rfl) ⟨607923, by rfl⟩ : syracuseStep 1621129 = 1215847) B1215847
theorem B2051561 : Blo 850355 2051561 := bstep (se 2 (by rfl) ⟨769335, by rfl⟩ : syracuseStep 2051561 = 1538671) B1538671
theorem B3233951 : Blo 850355 3233951 := bstep (se 1 (by rfl) ⟨2425463, by rfl⟩ : syracuseStep 3233951 = 4850927) B4850927
theorem B3891311 : Blo 850355 3891311 := bstep (se 1 (by rfl) ⟨2918483, by rfl⟩ : syracuseStep 3891311 = 5836967) B5836967
theorem B3237353 : Blo 850355 3237353 := bstep (se 2 (by rfl) ⟨1214007, by rfl⟩ : syracuseStep 3237353 = 2428015) B2428015
theorem B9205073 : Blo 850355 9205073 := bstep (se 2 (by rfl) ⟨3451902, by rfl⟩ : syracuseStep 9205073 = 6903805) B6903805
theorem B2881277 : Blo 850355 2881277 := bstep (se 3 (by rfl) ⟨540239, by rfl⟩ : syracuseStep 2881277 = 1080479) B1080479
theorem B7469887 : Blo 850355 7469887 := bstep (se 1 (by rfl) ⟨5602415, by rfl⟩ : syracuseStep 7469887 = 11204831) B11204831
theorem B74611691 : Blo 850355 74611691 := bstep (se 1 (by rfl) ⟨55958768, by rfl⟩ : syracuseStep 74611691 = 111917537) B111917537
theorem B4848943 : Blo 850355 4848943 := bstep (se 1 (by rfl) ⟨3636707, by rfl⟩ : syracuseStep 4848943 = 7273415) B7273415
theorem B851815 : Blo 850355 851815 := bstep (se 1 (by rfl) ⟨638861, by rfl⟩ : syracuseStep 851815 = 1277723) B1277723
theorem B9833723 : Blo 850355 9833723 := bstep (se 1 (by rfl) ⟨7375292, by rfl⟩ : syracuseStep 9833723 = 14750585) B14750585
theorem B2594207 : Blo 850355 2594207 := bstep (se 1 (by rfl) ⟨1945655, by rfl⟩ : syracuseStep 2594207 = 3891311) B3891311
theorem B6136715 : Blo 850355 6136715 := bstep (se 1 (by rfl) ⟨4602536, by rfl⟩ : syracuseStep 6136715 = 9205073) B9205073
theorem B5187199 : Blo 850355 5187199 := bstep (se 1 (by rfl) ⟨3890399, by rfl⟩ : syracuseStep 5187199 = 7780799) B7780799
theorem B6465257 : Blo 850355 6465257 := bstep (se 2 (by rfl) ⟨2424471, by rfl⟩ : syracuseStep 6465257 = 4848943) B4848943
theorem B35040509 : Blo 850355 35040509 := bstep (se 3 (by rfl) ⟨6570095, by rfl⟩ : syracuseStep 35040509 = 13140191) B13140191
theorem B4309847 : Blo 850355 4309847 := bstep (se 1 (by rfl) ⟨3232385, by rfl⟩ : syracuseStep 4309847 = 6464771) B6464771
theorem B1920851 : Blo 850355 1920851 := bstep (se 1 (by rfl) ⟨1440638, by rfl⟩ : syracuseStep 1920851 = 2881277) B2881277
theorem B4314221 : Blo 850355 4314221 := bstep (se 3 (by rfl) ⟨808916, by rfl⟩ : syracuseStep 4314221 = 1617833) B1617833
theorem B1367707 : Blo 850355 1367707 := bstep (se 1 (by rfl) ⟨1025780, by rfl⟩ : syracuseStep 1367707 = 2051561) B2051561
theorem B2155967 : Blo 850355 2155967 := bstep (se 1 (by rfl) ⟨1616975, by rfl⟩ : syracuseStep 2155967 = 3233951) B3233951
theorem B2158235 : Blo 850355 2158235 := bstep (se 1 (by rfl) ⟨1618676, by rfl⟩ : syracuseStep 2158235 = 3237353) B3237353
theorem B9959849 : Blo 850355 9959849 := bstep (se 2 (by rfl) ⟨3734943, by rfl⟩ : syracuseStep 9959849 = 7469887) B7469887
theorem B2161505 : Blo 850355 2161505 := bstep (se 2 (by rfl) ⟨810564, by rfl⟩ : syracuseStep 2161505 = 1621129) B1621129
theorem B49741127 : Blo 850355 49741127 := bstep (se 1 (by rfl) ⟨37305845, by rfl⟩ : syracuseStep 49741127 = 74611691) B74611691
theorem B6555815 : Blo 850355 6555815 := bstep (se 1 (by rfl) ⟨4916861, by rfl⟩ : syracuseStep 6555815 = 9833723) B9833723
theorem B6916265 : Blo 850355 6916265 := bstep (se 2 (by rfl) ⟨2593599, by rfl⟩ : syracuseStep 6916265 = 5187199) B5187199
theorem B1280567 : Blo 850355 1280567 := bstep (se 1 (by rfl) ⟨960425, by rfl⟩ : syracuseStep 1280567 = 1920851) B1920851
theorem B6917885 : Blo 850355 6917885 := bstep (se 3 (by rfl) ⟨1297103, by rfl⟩ : syracuseStep 6917885 = 2594207) B2594207
theorem B4310171 : Blo 850355 4310171 := bstep (se 1 (by rfl) ⟨3232628, by rfl⟩ : syracuseStep 4310171 = 6465257) B6465257
theorem B6639899 : Blo 850355 6639899 := bstep (se 1 (by rfl) ⟨4979924, by rfl⟩ : syracuseStep 6639899 = 9959849) B9959849
theorem B1823609 : Blo 850355 1823609 := bstep (se 2 (by rfl) ⟨683853, by rfl⟩ : syracuseStep 1823609 = 1367707) B1367707
theorem B2873231 : Blo 850355 2873231 := bstep (se 1 (by rfl) ⟨2154923, by rfl⟩ : syracuseStep 2873231 = 4309847) B4309847
theorem B2876147 : Blo 850355 2876147 := bstep (se 1 (by rfl) ⟨2157110, by rfl⟩ : syracuseStep 2876147 = 4314221) B4314221
theorem B4091143 : Blo 850355 4091143 := bstep (se 1 (by rfl) ⟨3068357, by rfl⟩ : syracuseStep 4091143 = 6136715) B6136715
theorem B1437311 : Blo 850355 1437311 := bstep (se 1 (by rfl) ⟨1077983, by rfl⟩ : syracuseStep 1437311 = 2155967) B2155967
theorem B23360339 : Blo 850355 23360339 := bstep (se 1 (by rfl) ⟨17520254, by rfl⟩ : syracuseStep 23360339 = 35040509) B35040509
theorem B1438823 : Blo 850355 1438823 := bstep (se 1 (by rfl) ⟨1079117, by rfl⟩ : syracuseStep 1438823 = 2158235) B2158235
theorem B1441003 : Blo 850355 1441003 := bstep (se 1 (by rfl) ⟨1080752, by rfl⟩ : syracuseStep 1441003 = 2161505) B2161505
theorem B33160751 : Blo 850355 33160751 := bstep (se 1 (by rfl) ⟨24870563, by rfl⟩ : syracuseStep 33160751 = 49741127) B49741127
theorem B853711 : Blo 850355 853711 := bstep (se 1 (by rfl) ⟨640283, by rfl⟩ : syracuseStep 853711 = 1280567) B1280567
theorem B1215739 : Blo 850355 1215739 := bstep (se 1 (by rfl) ⟨911804, by rfl⟩ : syracuseStep 1215739 = 1823609) B1823609
theorem B958207 : Blo 850355 958207 := bstep (se 1 (by rfl) ⟨718655, by rfl⟩ : syracuseStep 958207 = 1437311) B1437311
theorem B15573559 : Blo 850355 15573559 := bstep (se 1 (by rfl) ⟨11680169, by rfl⟩ : syracuseStep 15573559 = 23360339) B23360339
theorem B959215 : Blo 850355 959215 := bstep (se 1 (by rfl) ⟨719411, by rfl⟩ : syracuseStep 959215 = 1438823) B1438823
theorem B17706397 : Blo 850355 17706397 := bstep (se 3 (by rfl) ⟨3319949, by rfl⟩ : syracuseStep 17706397 = 6639899) B6639899
theorem B4370543 : Blo 850355 4370543 := bstep (se 1 (by rfl) ⟨3277907, by rfl⟩ : syracuseStep 4370543 = 6555815) B6555815
theorem B1915487 : Blo 850355 1915487 := bstep (se 1 (by rfl) ⟨1436615, by rfl⟩ : syracuseStep 1915487 = 2873231) B2873231
theorem B5454857 : Blo 850355 5454857 := bstep (se 2 (by rfl) ⟨2045571, by rfl⟩ : syracuseStep 5454857 = 4091143) B4091143
theorem B1917431 : Blo 850355 1917431 := bstep (se 1 (by rfl) ⟨1438073, by rfl⟩ : syracuseStep 1917431 = 2876147) B2876147
theorem B1921337 : Blo 850355 1921337 := bstep (se 2 (by rfl) ⟨720501, by rfl⟩ : syracuseStep 1921337 = 1441003) B1441003
theorem B22107167 : Blo 850355 22107167 := bstep (se 1 (by rfl) ⟨16580375, by rfl⟩ : syracuseStep 22107167 = 33160751) B33160751
theorem B2873447 : Blo 850355 2873447 := bstep (se 1 (by rfl) ⟨2155085, by rfl⟩ : syracuseStep 2873447 = 4310171) B4310171
theorem B4610843 : Blo 850355 4610843 := bstep (se 1 (by rfl) ⟨3458132, by rfl⟩ : syracuseStep 4610843 = 6916265) B6916265
theorem B4611923 : Blo 850355 4611923 := bstep (se 1 (by rfl) ⟨3458942, by rfl⟩ : syracuseStep 4611923 = 6917885) B6917885
theorem B1278287 : Blo 850355 1278287 := bstep (se 1 (by rfl) ⟨958715, by rfl⟩ : syracuseStep 1278287 = 1917431) B1917431
theorem B1278953 : Blo 850355 1278953 := bstep (se 2 (by rfl) ⟨479607, by rfl⟩ : syracuseStep 1278953 = 959215) B959215
theorem B1280891 : Blo 850355 1280891 := bstep (se 1 (by rfl) ⟨960668, by rfl⟩ : syracuseStep 1280891 = 1921337) B1921337
theorem B1915631 : Blo 850355 1915631 := bstep (se 1 (by rfl) ⟨1436723, by rfl⟩ : syracuseStep 1915631 = 2873447) B2873447
theorem B1620985 : Blo 850355 1620985 := bstep (se 2 (by rfl) ⟨607869, by rfl⟩ : syracuseStep 1620985 = 1215739) B1215739
theorem B23608529 : Blo 850355 23608529 := bstep (se 2 (by rfl) ⟨8853198, by rfl⟩ : syracuseStep 23608529 = 17706397) B17706397
theorem B20764745 : Blo 850355 20764745 := bstep (se 2 (by rfl) ⟨7786779, by rfl⟩ : syracuseStep 20764745 = 15573559) B15573559
theorem B14738111 : Blo 850355 14738111 := bstep (se 1 (by rfl) ⟨11053583, by rfl⟩ : syracuseStep 14738111 = 22107167) B22107167
theorem B3073895 : Blo 850355 3073895 := bstep (se 1 (by rfl) ⟨2305421, by rfl⟩ : syracuseStep 3073895 = 4610843) B4610843
theorem B3074615 : Blo 850355 3074615 := bstep (se 1 (by rfl) ⟨2305961, by rfl⟩ : syracuseStep 3074615 = 4611923) B4611923
theorem B2913695 : Blo 850355 2913695 := bstep (se 1 (by rfl) ⟨2185271, by rfl⟩ : syracuseStep 2913695 = 4370543) B4370543
theorem B1276991 : Blo 850355 1276991 := bstep (se 1 (by rfl) ⟨957743, by rfl⟩ : syracuseStep 1276991 = 1915487) B1915487
theorem B3636571 : Blo 850355 3636571 := bstep (se 1 (by rfl) ⟨2727428, by rfl⟩ : syracuseStep 3636571 = 5454857) B5454857
theorem B1277609 : Blo 850355 1277609 := bstep (se 2 (by rfl) ⟨479103, by rfl⟩ : syracuseStep 1277609 = 958207) B958207
theorem B852191 : Blo 850355 852191 := bstep (se 1 (by rfl) ⟨639143, by rfl⟩ : syracuseStep 852191 = 1278287) B1278287
theorem B852635 : Blo 850355 852635 := bstep (se 1 (by rfl) ⟨639476, by rfl⟩ : syracuseStep 852635 = 1278953) B1278953
theorem B853927 : Blo 850355 853927 := bstep (se 1 (by rfl) ⟨640445, by rfl⟩ : syracuseStep 853927 = 1280891) B1280891
theorem B1942463 : Blo 850355 1942463 := bstep (se 1 (by rfl) ⟨1456847, by rfl⟩ : syracuseStep 1942463 = 2913695) B2913695
theorem B15739019 : Blo 850355 15739019 := bstep (se 1 (by rfl) ⟨11804264, by rfl⟩ : syracuseStep 15739019 = 23608529) B23608529
theorem B13843163 : Blo 850355 13843163 := bstep (se 1 (by rfl) ⟨10382372, by rfl⟩ : syracuseStep 13843163 = 20764745) B20764745
theorem B2049263 : Blo 850355 2049263 := bstep (se 1 (by rfl) ⟨1536947, by rfl⟩ : syracuseStep 2049263 = 3073895) B3073895
theorem B2049743 : Blo 850355 2049743 := bstep (se 1 (by rfl) ⟨1537307, by rfl⟩ : syracuseStep 2049743 = 3074615) B3074615
theorem B9825407 : Blo 850355 9825407 := bstep (se 1 (by rfl) ⟨7369055, by rfl⟩ : syracuseStep 9825407 = 14738111) B14738111
theorem B2161313 : Blo 850355 2161313 := bstep (se 2 (by rfl) ⟨810492, by rfl⟩ : syracuseStep 2161313 = 1620985) B1620985
theorem B4848761 : Blo 850355 4848761 := bstep (se 2 (by rfl) ⟨1818285, by rfl⟩ : syracuseStep 4848761 = 3636571) B3636571
theorem B1277087 : Blo 850355 1277087 := bstep (se 1 (by rfl) ⟨957815, by rfl⟩ : syracuseStep 1277087 = 1915631) B1915631
theorem B851327 : Blo 850355 851327 := bstep (se 1 (by rfl) ⟨638495, by rfl⟩ : syracuseStep 851327 = 1276991) B1276991
theorem B851739 : Blo 850355 851739 := bstep (se 1 (by rfl) ⟨638804, by rfl⟩ : syracuseStep 851739 = 1277609) B1277609
theorem B10492679 : Blo 850355 10492679 := bstep (se 1 (by rfl) ⟨7869509, by rfl⟩ : syracuseStep 10492679 = 15739019) B15739019
theorem B1294975 : Blo 850355 1294975 := bstep (se 1 (by rfl) ⟨971231, by rfl⟩ : syracuseStep 1294975 = 1942463) B1942463
theorem B9228775 : Blo 850355 9228775 := bstep (se 1 (by rfl) ⟨6921581, by rfl⟩ : syracuseStep 9228775 = 13843163) B13843163
theorem B3232507 : Blo 850355 3232507 := bstep (se 1 (by rfl) ⟨2424380, by rfl⟩ : syracuseStep 3232507 = 4848761) B4848761
theorem B1366175 : Blo 850355 1366175 := bstep (se 1 (by rfl) ⟨1024631, by rfl⟩ : syracuseStep 1366175 = 2049263) B2049263
theorem B5465981 : Blo 850355 5465981 := bstep (se 3 (by rfl) ⟨1024871, by rfl⟩ : syracuseStep 5465981 = 2049743) B2049743
theorem B6550271 : Blo 850355 6550271 := bstep (se 1 (by rfl) ⟨4912703, by rfl⟩ : syracuseStep 6550271 = 9825407) B9825407
theorem B1440875 : Blo 850355 1440875 := bstep (se 1 (by rfl) ⟨1080656, by rfl⟩ : syracuseStep 1440875 = 2161313) B2161313
theorem B851391 : Blo 850355 851391 := bstep (se 1 (by rfl) ⟨638543, by rfl⟩ : syracuseStep 851391 = 1277087) B1277087
theorem B3643987 : Blo 850355 3643987 := bstep (se 1 (by rfl) ⟨2732990, by rfl⟩ : syracuseStep 3643987 = 5465981) B5465981
theorem B4366847 : Blo 850355 4366847 := bstep (se 1 (by rfl) ⟨3275135, by rfl⟩ : syracuseStep 4366847 = 6550271) B6550271
theorem B960583 : Blo 850355 960583 := bstep (se 1 (by rfl) ⟨720437, by rfl⟩ : syracuseStep 960583 = 1440875) B1440875
theorem B6995119 : Blo 850355 6995119 := bstep (se 1 (by rfl) ⟨5246339, by rfl⟩ : syracuseStep 6995119 = 10492679) B10492679
theorem B12305033 : Blo 850355 12305033 := bstep (se 2 (by rfl) ⟨4614387, by rfl⟩ : syracuseStep 12305033 = 9228775) B9228775
theorem B4310009 : Blo 850355 4310009 := bstep (se 2 (by rfl) ⟨1616253, by rfl⟩ : syracuseStep 4310009 = 3232507) B3232507
theorem B1726633 : Blo 850355 1726633 := bstep (se 2 (by rfl) ⟨647487, by rfl⟩ : syracuseStep 1726633 = 1294975) B1294975
theorem B910783 : Blo 850355 910783 := bstep (se 1 (by rfl) ⟨683087, by rfl⟩ : syracuseStep 910783 = 1366175) B1366175
theorem B1280777 : Blo 850355 1280777 := bstep (se 2 (by rfl) ⟨480291, by rfl⟩ : syracuseStep 1280777 = 960583) B960583
theorem B4857509 : Blo 850355 4857509 := bstep (se 4 (by rfl) ⟨455391, by rfl⟩ : syracuseStep 4857509 = 910783) B910783
theorem B2302177 : Blo 850355 2302177 := bstep (se 2 (by rfl) ⟨863316, by rfl⟩ : syracuseStep 2302177 = 1726633) B1726633
theorem B4858649 : Blo 850355 4858649 := bstep (se 2 (by rfl) ⟨1821993, by rfl⟩ : syracuseStep 4858649 = 3643987) B3643987
theorem B8203355 : Blo 850355 8203355 := bstep (se 1 (by rfl) ⟨6152516, by rfl⟩ : syracuseStep 8203355 = 12305033) B12305033
theorem B9326825 : Blo 850355 9326825 := bstep (se 2 (by rfl) ⟨3497559, by rfl⟩ : syracuseStep 9326825 = 6995119) B6995119
theorem B2873339 : Blo 850355 2873339 := bstep (se 1 (by rfl) ⟨2155004, by rfl⟩ : syracuseStep 2873339 = 4310009) B4310009
theorem B2911231 : Blo 850355 2911231 := bstep (se 1 (by rfl) ⟨2183423, by rfl⟩ : syracuseStep 2911231 = 4366847) B4366847
theorem B853851 : Blo 850355 853851 := bstep (se 1 (by rfl) ⟨640388, by rfl⟩ : syracuseStep 853851 = 1280777) B1280777
theorem B1915559 : Blo 850355 1915559 := bstep (se 1 (by rfl) ⟨1436669, by rfl⟩ : syracuseStep 1915559 = 2873339) B2873339
theorem B3881641 : Blo 850355 3881641 := bstep (se 2 (by rfl) ⟨1455615, by rfl⟩ : syracuseStep 3881641 = 2911231) B2911231
theorem B3069569 : Blo 850355 3069569 := bstep (se 2 (by rfl) ⟨1151088, by rfl⟩ : syracuseStep 3069569 = 2302177) B2302177
theorem B6217883 : Blo 850355 6217883 := bstep (se 1 (by rfl) ⟨4663412, by rfl⟩ : syracuseStep 6217883 = 9326825) B9326825
theorem B3238339 : Blo 850355 3238339 := bstep (se 1 (by rfl) ⟨2428754, by rfl⟩ : syracuseStep 3238339 = 4857509) B4857509
theorem B3239099 : Blo 850355 3239099 := bstep (se 1 (by rfl) ⟨2429324, by rfl⟩ : syracuseStep 3239099 = 4858649) B4858649
theorem B5468903 : Blo 850355 5468903 := bstep (se 1 (by rfl) ⟨4101677, by rfl⟩ : syracuseStep 5468903 = 8203355) B8203355
theorem B3645935 : Blo 850355 3645935 := bstep (se 1 (by rfl) ⟨2734451, by rfl⟩ : syracuseStep 3645935 = 5468903) B5468903
theorem B2046379 : Blo 850355 2046379 := bstep (se 1 (by rfl) ⟨1534784, by rfl⟩ : syracuseStep 2046379 = 3069569) B3069569
theorem B4145255 : Blo 850355 4145255 := bstep (se 1 (by rfl) ⟨3108941, by rfl⟩ : syracuseStep 4145255 = 6217883) B6217883
theorem B4317785 : Blo 850355 4317785 := bstep (se 2 (by rfl) ⟨1619169, by rfl⟩ : syracuseStep 4317785 = 3238339) B3238339
theorem B2159399 : Blo 850355 2159399 := bstep (se 1 (by rfl) ⟨1619549, by rfl⟩ : syracuseStep 2159399 = 3239099) B3239099
theorem B5175521 : Blo 850355 5175521 := bstep (se 2 (by rfl) ⟨1940820, by rfl⟩ : syracuseStep 5175521 = 3881641) B3881641
theorem B1277039 : Blo 850355 1277039 := bstep (se 1 (by rfl) ⟨957779, by rfl⟩ : syracuseStep 1277039 = 1915559) B1915559
theorem B2430623 : Blo 850355 2430623 := bstep (se 1 (by rfl) ⟨1822967, by rfl⟩ : syracuseStep 2430623 = 3645935) B3645935
theorem B2728505 : Blo 850355 2728505 := bstep (se 2 (by rfl) ⟨1023189, by rfl⟩ : syracuseStep 2728505 = 2046379) B2046379
theorem B3450347 : Blo 850355 3450347 := bstep (se 1 (by rfl) ⟨2587760, by rfl⟩ : syracuseStep 3450347 = 5175521) B5175521
theorem B2763503 : Blo 850355 2763503 := bstep (se 1 (by rfl) ⟨2072627, by rfl⟩ : syracuseStep 2763503 = 4145255) B4145255
theorem B2878523 : Blo 850355 2878523 := bstep (se 1 (by rfl) ⟨2158892, by rfl⟩ : syracuseStep 2878523 = 4317785) B4317785
theorem B1439599 : Blo 850355 1439599 := bstep (se 1 (by rfl) ⟨1079699, by rfl⟩ : syracuseStep 1439599 = 2159399) B2159399
theorem B851359 : Blo 850355 851359 := bstep (se 1 (by rfl) ⟨638519, by rfl⟩ : syracuseStep 851359 = 1277039) B1277039
theorem B7276013 : Blo 850355 7276013 := bstep (se 3 (by rfl) ⟨1364252, by rfl⟩ : syracuseStep 7276013 = 2728505) B2728505
theorem B2300231 : Blo 850355 2300231 := bstep (se 1 (by rfl) ⟨1725173, by rfl⟩ : syracuseStep 2300231 = 3450347) B3450347
theorem B1842335 : Blo 850355 1842335 := bstep (se 1 (by rfl) ⟨1381751, by rfl⟩ : syracuseStep 1842335 = 2763503) B2763503
theorem B1620415 : Blo 850355 1620415 := bstep (se 1 (by rfl) ⟨1215311, by rfl⟩ : syracuseStep 1620415 = 2430623) B2430623
theorem B1919015 : Blo 850355 1919015 := bstep (se 1 (by rfl) ⟨1439261, by rfl⟩ : syracuseStep 1919015 = 2878523) B2878523
theorem B1919465 : Blo 850355 1919465 := bstep (se 2 (by rfl) ⟨719799, by rfl⟩ : syracuseStep 1919465 = 1439599) B1439599
theorem B4850675 : Blo 850355 4850675 := bstep (se 1 (by rfl) ⟨3638006, by rfl⟩ : syracuseStep 4850675 = 7276013) B7276013
theorem B1279343 : Blo 850355 1279343 := bstep (se 1 (by rfl) ⟨959507, by rfl⟩ : syracuseStep 1279343 = 1919015) B1919015
theorem B1279643 : Blo 850355 1279643 := bstep (se 1 (by rfl) ⟨959732, by rfl⟩ : syracuseStep 1279643 = 1919465) B1919465
theorem B1228223 : Blo 850355 1228223 := bstep (se 1 (by rfl) ⟨921167, by rfl⟩ : syracuseStep 1228223 = 1842335) B1842335
theorem B1533487 : Blo 850355 1533487 := bstep (se 1 (by rfl) ⟨1150115, by rfl⟩ : syracuseStep 1533487 = 2300231) B2300231
theorem B2160553 : Blo 850355 2160553 := bstep (se 2 (by rfl) ⟨810207, by rfl⟩ : syracuseStep 2160553 = 1620415) B1620415
theorem B852895 : Blo 850355 852895 := bstep (se 1 (by rfl) ⟨639671, by rfl⟩ : syracuseStep 852895 = 1279343) B1279343
theorem B853095 : Blo 850355 853095 := bstep (se 1 (by rfl) ⟨639821, by rfl⟩ : syracuseStep 853095 = 1279643) B1279643
theorem B2044649 : Blo 850355 2044649 := bstep (se 2 (by rfl) ⟨766743, by rfl⟩ : syracuseStep 2044649 = 1533487) B1533487
theorem B3233783 : Blo 850355 3233783 := bstep (se 1 (by rfl) ⟨2425337, by rfl⟩ : syracuseStep 3233783 = 4850675) B4850675
theorem B2880737 : Blo 850355 2880737 := bstep (se 2 (by rfl) ⟨1080276, by rfl⟩ : syracuseStep 2880737 = 2160553) B2160553
theorem B3275261 : Blo 850355 3275261 := bstep (se 3 (by rfl) ⟨614111, by rfl⟩ : syracuseStep 3275261 = 1228223) B1228223
theorem B5452397 : Blo 850355 5452397 := bstep (se 3 (by rfl) ⟨1022324, by rfl⟩ : syracuseStep 5452397 = 2044649) B2044649
theorem B1920491 : Blo 850355 1920491 := bstep (se 1 (by rfl) ⟨1440368, by rfl⟩ : syracuseStep 1920491 = 2880737) B2880737
theorem B2183507 : Blo 850355 2183507 := bstep (se 1 (by rfl) ⟨1637630, by rfl⟩ : syracuseStep 2183507 = 3275261) B3275261
theorem B2155855 : Blo 850355 2155855 := bstep (se 1 (by rfl) ⟨1616891, by rfl⟩ : syracuseStep 2155855 = 3233783) B3233783
theorem B1280327 : Blo 850355 1280327 := bstep (se 1 (by rfl) ⟨960245, by rfl⟩ : syracuseStep 1280327 = 1920491) B1920491
theorem B1455671 : Blo 850355 1455671 := bstep (se 1 (by rfl) ⟨1091753, by rfl⟩ : syracuseStep 1455671 = 2183507) B2183507
theorem B2874473 : Blo 850355 2874473 := bstep (se 2 (by rfl) ⟨1077927, by rfl⟩ : syracuseStep 2874473 = 2155855) B2155855
theorem B3634931 : Blo 850355 3634931 := bstep (se 1 (by rfl) ⟨2726198, by rfl⟩ : syracuseStep 3634931 = 5452397) B5452397
theorem B853551 : Blo 850355 853551 := bstep (se 1 (by rfl) ⟨640163, by rfl⟩ : syracuseStep 853551 = 1280327) B1280327
theorem B3881789 : Blo 850355 3881789 := bstep (se 3 (by rfl) ⟨727835, by rfl⟩ : syracuseStep 3881789 = 1455671) B1455671
theorem B1916315 : Blo 850355 1916315 := bstep (se 1 (by rfl) ⟨1437236, by rfl⟩ : syracuseStep 1916315 = 2874473) B2874473
theorem B2423287 : Blo 850355 2423287 := bstep (se 1 (by rfl) ⟨1817465, by rfl⟩ : syracuseStep 2423287 = 3634931) B3634931
theorem B3231049 : Blo 850355 3231049 := bstep (se 2 (by rfl) ⟨1211643, by rfl⟩ : syracuseStep 3231049 = 2423287) B2423287
theorem B2587859 : Blo 850355 2587859 := bstep (se 1 (by rfl) ⟨1940894, by rfl⟩ : syracuseStep 2587859 = 3881789) B3881789
theorem B1277543 : Blo 850355 1277543 := bstep (se 1 (by rfl) ⟨958157, by rfl⟩ : syracuseStep 1277543 = 1916315) B1916315
theorem B4308065 : Blo 850355 4308065 := bstep (se 2 (by rfl) ⟨1615524, by rfl⟩ : syracuseStep 4308065 = 3231049) B3231049
theorem B1725239 : Blo 850355 1725239 := bstep (se 1 (by rfl) ⟨1293929, by rfl⟩ : syracuseStep 1725239 = 2587859) B2587859
theorem B851695 : Blo 850355 851695 := bstep (se 1 (by rfl) ⟨638771, by rfl⟩ : syracuseStep 851695 = 1277543) B1277543
theorem B4600637 : Blo 850355 4600637 := bstep (se 3 (by rfl) ⟨862619, by rfl⟩ : syracuseStep 4600637 = 1725239) B1725239
theorem B2872043 : Blo 850355 2872043 := bstep (se 1 (by rfl) ⟨2154032, by rfl⟩ : syracuseStep 2872043 = 4308065) B4308065
theorem B1914695 : Blo 850355 1914695 := bstep (se 1 (by rfl) ⟨1436021, by rfl⟩ : syracuseStep 1914695 = 2872043) B2872043
theorem B3067091 : Blo 850355 3067091 := bstep (se 1 (by rfl) ⟨2300318, by rfl⟩ : syracuseStep 3067091 = 4600637) B4600637
theorem B2044727 : Blo 850355 2044727 := bstep (se 1 (by rfl) ⟨1533545, by rfl⟩ : syracuseStep 2044727 = 3067091) B3067091
theorem B1276463 : Blo 850355 1276463 := bstep (se 1 (by rfl) ⟨957347, by rfl⟩ : syracuseStep 1276463 = 1914695) B1914695
theorem B1363151 : Blo 850355 1363151 := bstep (se 1 (by rfl) ⟨1022363, by rfl⟩ : syracuseStep 1363151 = 2044727) B2044727
theorem B850975 : Blo 850355 850975 := bstep (se 1 (by rfl) ⟨638231, by rfl⟩ : syracuseStep 850975 = 1276463) B1276463
theorem B908767 : Blo 850355 908767 := bstep (se 1 (by rfl) ⟨681575, by rfl⟩ : syracuseStep 908767 = 1363151) B1363151
theorem B1211689 : Blo 850355 1211689 := bstep (se 2 (by rfl) ⟨454383, by rfl⟩ : syracuseStep 1211689 = 908767) B908767
theorem B6462341 : Blo 850355 6462341 := bstep (se 4 (by rfl) ⟨605844, by rfl⟩ : syracuseStep 6462341 = 1211689) B1211689
theorem B4308227 : Blo 850355 4308227 := bstep (se 1 (by rfl) ⟨3231170, by rfl⟩ : syracuseStep 4308227 = 6462341) B6462341
theorem B2872151 : Blo 850355 2872151 := bstep (se 1 (by rfl) ⟨2154113, by rfl⟩ : syracuseStep 2872151 = 4308227) B4308227
theorem B1914767 : Blo 850355 1914767 := bstep (se 1 (by rfl) ⟨1436075, by rfl⟩ : syracuseStep 1914767 = 2872151) B2872151
theorem B1276511 : Blo 850355 1276511 := bstep (se 1 (by rfl) ⟨957383, by rfl⟩ : syracuseStep 1276511 = 1914767) B1914767
theorem B851007 : Blo 850355 851007 := bstep (se 1 (by rfl) ⟨638255, by rfl⟩ : syracuseStep 851007 = 1276511) B1276511

theorem C0 (j : ℕ) (h1 : 212588 ≤ j) (h2 : j ≤ 213287) : Blo 850355 (4 * j + 3) := by
  interval_cases j
  · exact B850355
  · exact B850359
  · exact B850363
  · exact B850367
  · exact B850371
  · exact B850375
  · exact B850379
  · exact B850383
  · exact B850387
  · exact B850391
  · exact B850395
  · exact B850399
  · exact B850403
  · exact B850407
  · exact B850411
  · exact B850415
  · exact B850419
  · exact B850423
  · exact B850427
  · exact B850431
  · exact B850435
  · exact B850439
  · exact B850443
  · exact B850447
  · exact B850451
  · exact B850455
  · exact B850459
  · exact B850463
  · exact B850467
  · exact B850471
  · exact B850475
  · exact B850479
  · exact B850483
  · exact B850487
  · exact B850491
  · exact B850495
  · exact B850499
  · exact B850503
  · exact B850507
  · exact B850511
  · exact B850515
  · exact B850519
  · exact B850523
  · exact B850527
  · exact B850531
  · exact B850535
  · exact B850539
  · exact B850543
  · exact B850547
  · exact B850551
  · exact B850555
  · exact B850559
  · exact B850563
  · exact B850567
  · exact B850571
  · exact B850575
  · exact B850579
  · exact B850583
  · exact B850587
  · exact B850591
  · exact B850595
  · exact B850599
  · exact B850603
  · exact B850607
  · exact B850611
  · exact B850615
  · exact B850619
  · exact B850623
  · exact B850627
  · exact B850631
  · exact B850635
  · exact B850639
  · exact B850643
  · exact B850647
  · exact B850651
  · exact B850655
  · exact B850659
  · exact B850663
  · exact B850667
  · exact B850671
  · exact B850675
  · exact B850679
  · exact B850683
  · exact B850687
  · exact B850691
  · exact B850695
  · exact B850699
  · exact B850703
  · exact B850707
  · exact B850711
  · exact B850715
  · exact B850719
  · exact B850723
  · exact B850727
  · exact B850731
  · exact B850735
  · exact B850739
  · exact B850743
  · exact B850747
  · exact B850751
  · exact B850755
  · exact B850759
  · exact B850763
  · exact B850767
  · exact B850771
  · exact B850775
  · exact B850779
  · exact B850783
  · exact B850787
  · exact B850791
  · exact B850795
  · exact B850799
  · exact B850803
  · exact B850807
  · exact B850811
  · exact B850815
  · exact B850819
  · exact B850823
  · exact B850827
  · exact B850831
  · exact B850835
  · exact B850839
  · exact B850843
  · exact B850847
  · exact B850851
  · exact B850855
  · exact B850859
  · exact B850863
  · exact B850867
  · exact B850871
  · exact B850875
  · exact B850879
  · exact B850883
  · exact B850887
  · exact B850891
  · exact B850895
  · exact B850899
  · exact B850903
  · exact B850907
  · exact B850911
  · exact B850915
  · exact B850919
  · exact B850923
  · exact B850927
  · exact B850931
  · exact B850935
  · exact B850939
  · exact B850943
  · exact B850947
  · exact B850951
  · exact B850955
  · exact B850959
  · exact B850963
  · exact B850967
  · exact B850971
  · exact B850975
  · exact B850979
  · exact B850983
  · exact B850987
  · exact B850991
  · exact B850995
  · exact B850999
  · exact B851003
  · exact B851007
  · exact B851011
  · exact B851015
  · exact B851019
  · exact B851023
  · exact B851027
  · exact B851031
  · exact B851035
  · exact B851039
  · exact B851043
  · exact B851047
  · exact B851051
  · exact B851055
  · exact B851059
  · exact B851063
  · exact B851067
  · exact B851071
  · exact B851075
  · exact B851079
  · exact B851083
  · exact B851087
  · exact B851091
  · exact B851095
  · exact B851099
  · exact B851103
  · exact B851107
  · exact B851111
  · exact B851115
  · exact B851119
  · exact B851123
  · exact B851127
  · exact B851131
  · exact B851135
  · exact B851139
  · exact B851143
  · exact B851147
  · exact B851151
  · exact B851155
  · exact B851159
  · exact B851163
  · exact B851167
  · exact B851171
  · exact B851175
  · exact B851179
  · exact B851183
  · exact B851187
  · exact B851191
  · exact B851195
  · exact B851199
  · exact B851203
  · exact B851207
  · exact B851211
  · exact B851215
  · exact B851219
  · exact B851223
  · exact B851227
  · exact B851231
  · exact B851235
  · exact B851239
  · exact B851243
  · exact B851247
  · exact B851251
  · exact B851255
  · exact B851259
  · exact B851263
  · exact B851267
  · exact B851271
  · exact B851275
  · exact B851279
  · exact B851283
  · exact B851287
  · exact B851291
  · exact B851295
  · exact B851299
  · exact B851303
  · exact B851307
  · exact B851311
  · exact B851315
  · exact B851319
  · exact B851323
  · exact B851327
  · exact B851331
  · exact B851335
  · exact B851339
  · exact B851343
  · exact B851347
  · exact B851351
  · exact B851355
  · exact B851359
  · exact B851363
  · exact B851367
  · exact B851371
  · exact B851375
  · exact B851379
  · exact B851383
  · exact B851387
  · exact B851391
  · exact B851395
  · exact B851399
  · exact B851403
  · exact B851407
  · exact B851411
  · exact B851415
  · exact B851419
  · exact B851423
  · exact B851427
  · exact B851431
  · exact B851435
  · exact B851439
  · exact B851443
  · exact B851447
  · exact B851451
  · exact B851455
  · exact B851459
  · exact B851463
  · exact B851467
  · exact B851471
  · exact B851475
  · exact B851479
  · exact B851483
  · exact B851487
  · exact B851491
  · exact B851495
  · exact B851499
  · exact B851503
  · exact B851507
  · exact B851511
  · exact B851515
  · exact B851519
  · exact B851523
  · exact B851527
  · exact B851531
  · exact B851535
  · exact B851539
  · exact B851543
  · exact B851547
  · exact B851551
  · exact B851555
  · exact B851559
  · exact B851563
  · exact B851567
  · exact B851571
  · exact B851575
  · exact B851579
  · exact B851583
  · exact B851587
  · exact B851591
  · exact B851595
  · exact B851599
  · exact B851603
  · exact B851607
  · exact B851611
  · exact B851615
  · exact B851619
  · exact B851623
  · exact B851627
  · exact B851631
  · exact B851635
  · exact B851639
  · exact B851643
  · exact B851647
  · exact B851651
  · exact B851655
  · exact B851659
  · exact B851663
  · exact B851667
  · exact B851671
  · exact B851675
  · exact B851679
  · exact B851683
  · exact B851687
  · exact B851691
  · exact B851695
  · exact B851699
  · exact B851703
  · exact B851707
  · exact B851711
  · exact B851715
  · exact B851719
  · exact B851723
  · exact B851727
  · exact B851731
  · exact B851735
  · exact B851739
  · exact B851743
  · exact B851747
  · exact B851751
  · exact B851755
  · exact B851759
  · exact B851763
  · exact B851767
  · exact B851771
  · exact B851775
  · exact B851779
  · exact B851783
  · exact B851787
  · exact B851791
  · exact B851795
  · exact B851799
  · exact B851803
  · exact B851807
  · exact B851811
  · exact B851815
  · exact B851819
  · exact B851823
  · exact B851827
  · exact B851831
  · exact B851835
  · exact B851839
  · exact B851843
  · exact B851847
  · exact B851851
  · exact B851855
  · exact B851859
  · exact B851863
  · exact B851867
  · exact B851871
  · exact B851875
  · exact B851879
  · exact B851883
  · exact B851887
  · exact B851891
  · exact B851895
  · exact B851899
  · exact B851903
  · exact B851907
  · exact B851911
  · exact B851915
  · exact B851919
  · exact B851923
  · exact B851927
  · exact B851931
  · exact B851935
  · exact B851939
  · exact B851943
  · exact B851947
  · exact B851951
  · exact B851955
  · exact B851959
  · exact B851963
  · exact B851967
  · exact B851971
  · exact B851975
  · exact B851979
  · exact B851983
  · exact B851987
  · exact B851991
  · exact B851995
  · exact B851999
  · exact B852003
  · exact B852007
  · exact B852011
  · exact B852015
  · exact B852019
  · exact B852023
  · exact B852027
  · exact B852031
  · exact B852035
  · exact B852039
  · exact B852043
  · exact B852047
  · exact B852051
  · exact B852055
  · exact B852059
  · exact B852063
  · exact B852067
  · exact B852071
  · exact B852075
  · exact B852079
  · exact B852083
  · exact B852087
  · exact B852091
  · exact B852095
  · exact B852099
  · exact B852103
  · exact B852107
  · exact B852111
  · exact B852115
  · exact B852119
  · exact B852123
  · exact B852127
  · exact B852131
  · exact B852135
  · exact B852139
  · exact B852143
  · exact B852147
  · exact B852151
  · exact B852155
  · exact B852159
  · exact B852163
  · exact B852167
  · exact B852171
  · exact B852175
  · exact B852179
  · exact B852183
  · exact B852187
  · exact B852191
  · exact B852195
  · exact B852199
  · exact B852203
  · exact B852207
  · exact B852211
  · exact B852215
  · exact B852219
  · exact B852223
  · exact B852227
  · exact B852231
  · exact B852235
  · exact B852239
  · exact B852243
  · exact B852247
  · exact B852251
  · exact B852255
  · exact B852259
  · exact B852263
  · exact B852267
  · exact B852271
  · exact B852275
  · exact B852279
  · exact B852283
  · exact B852287
  · exact B852291
  · exact B852295
  · exact B852299
  · exact B852303
  · exact B852307
  · exact B852311
  · exact B852315
  · exact B852319
  · exact B852323
  · exact B852327
  · exact B852331
  · exact B852335
  · exact B852339
  · exact B852343
  · exact B852347
  · exact B852351
  · exact B852355
  · exact B852359
  · exact B852363
  · exact B852367
  · exact B852371
  · exact B852375
  · exact B852379
  · exact B852383
  · exact B852387
  · exact B852391
  · exact B852395
  · exact B852399
  · exact B852403
  · exact B852407
  · exact B852411
  · exact B852415
  · exact B852419
  · exact B852423
  · exact B852427
  · exact B852431
  · exact B852435
  · exact B852439
  · exact B852443
  · exact B852447
  · exact B852451
  · exact B852455
  · exact B852459
  · exact B852463
  · exact B852467
  · exact B852471
  · exact B852475
  · exact B852479
  · exact B852483
  · exact B852487
  · exact B852491
  · exact B852495
  · exact B852499
  · exact B852503
  · exact B852507
  · exact B852511
  · exact B852515
  · exact B852519
  · exact B852523
  · exact B852527
  · exact B852531
  · exact B852535
  · exact B852539
  · exact B852543
  · exact B852547
  · exact B852551
  · exact B852555
  · exact B852559
  · exact B852563
  · exact B852567
  · exact B852571
  · exact B852575
  · exact B852579
  · exact B852583
  · exact B852587
  · exact B852591
  · exact B852595
  · exact B852599
  · exact B852603
  · exact B852607
  · exact B852611
  · exact B852615
  · exact B852619
  · exact B852623
  · exact B852627
  · exact B852631
  · exact B852635
  · exact B852639
  · exact B852643
  · exact B852647
  · exact B852651
  · exact B852655
  · exact B852659
  · exact B852663
  · exact B852667
  · exact B852671
  · exact B852675
  · exact B852679
  · exact B852683
  · exact B852687
  · exact B852691
  · exact B852695
  · exact B852699
  · exact B852703
  · exact B852707
  · exact B852711
  · exact B852715
  · exact B852719
  · exact B852723
  · exact B852727
  · exact B852731
  · exact B852735
  · exact B852739
  · exact B852743
  · exact B852747
  · exact B852751
  · exact B852755
  · exact B852759
  · exact B852763
  · exact B852767
  · exact B852771
  · exact B852775
  · exact B852779
  · exact B852783
  · exact B852787
  · exact B852791
  · exact B852795
  · exact B852799
  · exact B852803
  · exact B852807
  · exact B852811
  · exact B852815
  · exact B852819
  · exact B852823
  · exact B852827
  · exact B852831
  · exact B852835
  · exact B852839
  · exact B852843
  · exact B852847
  · exact B852851
  · exact B852855
  · exact B852859
  · exact B852863
  · exact B852867
  · exact B852871
  · exact B852875
  · exact B852879
  · exact B852883
  · exact B852887
  · exact B852891
  · exact B852895
  · exact B852899
  · exact B852903
  · exact B852907
  · exact B852911
  · exact B852915
  · exact B852919
  · exact B852923
  · exact B852927
  · exact B852931
  · exact B852935
  · exact B852939
  · exact B852943
  · exact B852947
  · exact B852951
  · exact B852955
  · exact B852959
  · exact B852963
  · exact B852967
  · exact B852971
  · exact B852975
  · exact B852979
  · exact B852983
  · exact B852987
  · exact B852991
  · exact B852995
  · exact B852999
  · exact B853003
  · exact B853007
  · exact B853011
  · exact B853015
  · exact B853019
  · exact B853023
  · exact B853027
  · exact B853031
  · exact B853035
  · exact B853039
  · exact B853043
  · exact B853047
  · exact B853051
  · exact B853055
  · exact B853059
  · exact B853063
  · exact B853067
  · exact B853071
  · exact B853075
  · exact B853079
  · exact B853083
  · exact B853087
  · exact B853091
  · exact B853095
  · exact B853099
  · exact B853103
  · exact B853107
  · exact B853111
  · exact B853115
  · exact B853119
  · exact B853123
  · exact B853127
  · exact B853131
  · exact B853135
  · exact B853139
  · exact B853143
  · exact B853147
  · exact B853151

theorem C1 (j : ℕ) (h1 : 213288 ≤ j) (h2 : j ≤ 213588) : Blo 850355 (4 * j + 3) := by
  interval_cases j
  · exact B853155
  · exact B853159
  · exact B853163
  · exact B853167
  · exact B853171
  · exact B853175
  · exact B853179
  · exact B853183
  · exact B853187
  · exact B853191
  · exact B853195
  · exact B853199
  · exact B853203
  · exact B853207
  · exact B853211
  · exact B853215
  · exact B853219
  · exact B853223
  · exact B853227
  · exact B853231
  · exact B853235
  · exact B853239
  · exact B853243
  · exact B853247
  · exact B853251
  · exact B853255
  · exact B853259
  · exact B853263
  · exact B853267
  · exact B853271
  · exact B853275
  · exact B853279
  · exact B853283
  · exact B853287
  · exact B853291
  · exact B853295
  · exact B853299
  · exact B853303
  · exact B853307
  · exact B853311
  · exact B853315
  · exact B853319
  · exact B853323
  · exact B853327
  · exact B853331
  · exact B853335
  · exact B853339
  · exact B853343
  · exact B853347
  · exact B853351
  · exact B853355
  · exact B853359
  · exact B853363
  · exact B853367
  · exact B853371
  · exact B853375
  · exact B853379
  · exact B853383
  · exact B853387
  · exact B853391
  · exact B853395
  · exact B853399
  · exact B853403
  · exact B853407
  · exact B853411
  · exact B853415
  · exact B853419
  · exact B853423
  · exact B853427
  · exact B853431
  · exact B853435
  · exact B853439
  · exact B853443
  · exact B853447
  · exact B853451
  · exact B853455
  · exact B853459
  · exact B853463
  · exact B853467
  · exact B853471
  · exact B853475
  · exact B853479
  · exact B853483
  · exact B853487
  · exact B853491
  · exact B853495
  · exact B853499
  · exact B853503
  · exact B853507
  · exact B853511
  · exact B853515
  · exact B853519
  · exact B853523
  · exact B853527
  · exact B853531
  · exact B853535
  · exact B853539
  · exact B853543
  · exact B853547
  · exact B853551
  · exact B853555
  · exact B853559
  · exact B853563
  · exact B853567
  · exact B853571
  · exact B853575
  · exact B853579
  · exact B853583
  · exact B853587
  · exact B853591
  · exact B853595
  · exact B853599
  · exact B853603
  · exact B853607
  · exact B853611
  · exact B853615
  · exact B853619
  · exact B853623
  · exact B853627
  · exact B853631
  · exact B853635
  · exact B853639
  · exact B853643
  · exact B853647
  · exact B853651
  · exact B853655
  · exact B853659
  · exact B853663
  · exact B853667
  · exact B853671
  · exact B853675
  · exact B853679
  · exact B853683
  · exact B853687
  · exact B853691
  · exact B853695
  · exact B853699
  · exact B853703
  · exact B853707
  · exact B853711
  · exact B853715
  · exact B853719
  · exact B853723
  · exact B853727
  · exact B853731
  · exact B853735
  · exact B853739
  · exact B853743
  · exact B853747
  · exact B853751
  · exact B853755
  · exact B853759
  · exact B853763
  · exact B853767
  · exact B853771
  · exact B853775
  · exact B853779
  · exact B853783
  · exact B853787
  · exact B853791
  · exact B853795
  · exact B853799
  · exact B853803
  · exact B853807
  · exact B853811
  · exact B853815
  · exact B853819
  · exact B853823
  · exact B853827
  · exact B853831
  · exact B853835
  · exact B853839
  · exact B853843
  · exact B853847
  · exact B853851
  · exact B853855
  · exact B853859
  · exact B853863
  · exact B853867
  · exact B853871
  · exact B853875
  · exact B853879
  · exact B853883
  · exact B853887
  · exact B853891
  · exact B853895
  · exact B853899
  · exact B853903
  · exact B853907
  · exact B853911
  · exact B853915
  · exact B853919
  · exact B853923
  · exact B853927
  · exact B853931
  · exact B853935
  · exact B853939
  · exact B853943
  · exact B853947
  · exact B853951
  · exact B853955
  · exact B853959
  · exact B853963
  · exact B853967
  · exact B853971
  · exact B853975
  · exact B853979
  · exact B853983
  · exact B853987
  · exact B853991
  · exact B853995
  · exact B853999
  · exact B854003
  · exact B854007
  · exact B854011
  · exact B854015
  · exact B854019
  · exact B854023
  · exact B854027
  · exact B854031
  · exact B854035
  · exact B854039
  · exact B854043
  · exact B854047
  · exact B854051
  · exact B854055
  · exact B854059
  · exact B854063
  · exact B854067
  · exact B854071
  · exact B854075
  · exact B854079
  · exact B854083
  · exact B854087
  · exact B854091
  · exact B854095
  · exact B854099
  · exact B854103
  · exact B854107
  · exact B854111
  · exact B854115
  · exact B854119
  · exact B854123
  · exact B854127
  · exact B854131
  · exact B854135
  · exact B854139
  · exact B854143
  · exact B854147
  · exact B854151
  · exact B854155
  · exact B854159
  · exact B854163
  · exact B854167
  · exact B854171
  · exact B854175
  · exact B854179
  · exact B854183
  · exact B854187
  · exact B854191
  · exact B854195
  · exact B854199
  · exact B854203
  · exact B854207
  · exact B854211
  · exact B854215
  · exact B854219
  · exact B854223
  · exact B854227
  · exact B854231
  · exact B854235
  · exact B854239
  · exact B854243
  · exact B854247
  · exact B854251
  · exact B854255
  · exact B854259
  · exact B854263
  · exact B854267
  · exact B854271
  · exact B854275
  · exact B854279
  · exact B854283
  · exact B854287
  · exact B854291
  · exact B854295
  · exact B854299
  · exact B854303
  · exact B854307
  · exact B854311
  · exact B854315
  · exact B854319
  · exact B854323
  · exact B854327
  · exact B854331
  · exact B854335
  · exact B854339
  · exact B854343
  · exact B854347
  · exact B854351
  · exact B854355

theorem solution (m : ℕ) (hlo : 850355 ≤ m) (hhi : m ≤ 854355) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 212588 ≤ j := by omega
    have hj2 : j ≤ 213588 := by omega
    have hb : Blo 850355 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 213288 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
