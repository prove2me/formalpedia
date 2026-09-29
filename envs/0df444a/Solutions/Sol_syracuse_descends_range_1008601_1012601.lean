-- Prove2me | solution 1 for syracuse_descends_range_1008601_1012601
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:15.721157+00:00
-- url     : https://prove2.me/submissions/6e4dd78b-3d41-4ccd-a5b0-08adb979af9c

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


theorem B1277957 : Blo 1008601 1277957 := bbase (se 4 (by rfl) ⟨119808, by rfl⟩ : syracuseStep 1277957 = 239617) (by norm_num)
theorem B1278013 : Blo 1008601 1278013 := bbase (se 3 (by rfl) ⟨239627, by rfl⟩ : syracuseStep 1278013 = 479255) (by norm_num)
theorem B5111909 : Blo 1008601 5111909 := bbase (se 4 (by rfl) ⟨479241, by rfl⟩ : syracuseStep 5111909 = 958483) (by norm_num)
theorem B1704037 : Blo 1008601 1704037 := bbase (se 4 (by rfl) ⟨159753, by rfl⟩ : syracuseStep 1704037 = 319507) (by norm_num)
theorem B9863317 : Blo 1008601 9863317 := bbase (se 6 (by rfl) ⟨231171, by rfl⟩ : syracuseStep 9863317 = 462343) (by norm_num)
theorem B1278109 : Blo 1008601 1278109 := bbase (se 3 (by rfl) ⟨239645, by rfl⟩ : syracuseStep 1278109 = 479291) (by norm_num)
theorem B1704125 : Blo 1008601 1704125 := bbase (se 3 (by rfl) ⟨319523, by rfl⟩ : syracuseStep 1704125 = 639047) (by norm_num)
theorem B1212629 : Blo 1008601 1212629 := bbase (se 7 (by rfl) ⟨14210, by rfl⟩ : syracuseStep 1212629 = 28421) (by norm_num)
theorem B3408101 : Blo 1008601 3408101 := bbase (se 4 (by rfl) ⟨319509, by rfl⟩ : syracuseStep 3408101 = 639019) (by norm_num)
theorem B2556157 : Blo 1008601 2556157 := bbase (se 3 (by rfl) ⟨479279, by rfl⟩ : syracuseStep 2556157 = 958559) (by norm_num)
theorem B1704253 : Blo 1008601 1704253 := bbase (se 3 (by rfl) ⟨319547, by rfl⟩ : syracuseStep 1704253 = 639095) (by norm_num)
theorem B1212745 : Blo 1008601 1212745 := bbase (se 2 (by rfl) ⟨454779, by rfl⟩ : syracuseStep 1212745 = 909559) (by norm_num)
theorem B1278281 : Blo 1008601 1278281 := bbase (se 2 (by rfl) ⟨479355, by rfl⟩ : syracuseStep 1278281 = 958711) (by norm_num)
theorem B1212769 : Blo 1008601 1212769 := bbase (se 2 (by rfl) ⟨454788, by rfl⟩ : syracuseStep 1212769 = 909577) (by norm_num)
theorem B2556269 : Blo 1008601 2556269 := bbase (se 3 (by rfl) ⟨479300, by rfl⟩ : syracuseStep 2556269 = 958601) (by norm_num)
theorem B1278337 : Blo 1008601 1278337 := bbase (se 2 (by rfl) ⟨479376, by rfl⟩ : syracuseStep 1278337 = 958753) (by norm_num)
theorem B1704341 : Blo 1008601 1704341 := bbase (se 6 (by rfl) ⟨39945, by rfl⟩ : syracuseStep 1704341 = 79891) (by norm_num)
theorem B2425277 : Blo 1008601 2425277 := bbase (se 3 (by rfl) ⟨454739, by rfl⟩ : syracuseStep 2425277 = 909479) (by norm_num)
theorem B1278433 : Blo 1008601 1278433 := bbase (se 2 (by rfl) ⟨479412, by rfl⟩ : syracuseStep 1278433 = 958825) (by norm_num)
theorem B1704469 : Blo 1008601 1704469 := bbase (se 6 (by rfl) ⟨39948, by rfl⟩ : syracuseStep 1704469 = 79897) (by norm_num)
theorem B2556461 : Blo 1008601 2556461 := bbase (se 3 (by rfl) ⟨479336, by rfl⟩ : syracuseStep 2556461 = 958673) (by norm_num)
theorem B1704557 : Blo 1008601 1704557 := bbase (se 3 (by rfl) ⟨319604, by rfl⟩ : syracuseStep 1704557 = 639209) (by norm_num)
theorem B1278605 : Blo 1008601 1278605 := bbase (se 3 (by rfl) ⟨239738, by rfl⟩ : syracuseStep 1278605 = 479477) (by norm_num)
theorem B3408533 : Blo 1008601 3408533 := bbase (se 6 (by rfl) ⟨79887, by rfl⟩ : syracuseStep 3408533 = 159775) (by norm_num)
theorem B1278661 : Blo 1008601 1278661 := bbase (se 4 (by rfl) ⟨119874, by rfl⟩ : syracuseStep 1278661 = 239749) (by norm_num)
theorem B1704685 : Blo 1008601 1704685 := bbase (se 3 (by rfl) ⟨319628, by rfl⟩ : syracuseStep 1704685 = 639257) (by norm_num)
theorem B7275253 : Blo 1008601 7275253 := bbase (se 5 (by rfl) ⟨341027, by rfl⟩ : syracuseStep 7275253 = 682055) (by norm_num)
theorem B3834661 : Blo 1008601 3834661 := bbase (se 4 (by rfl) ⟨359499, by rfl⟩ : syracuseStep 3834661 = 718999) (by norm_num)
theorem B1278757 : Blo 1008601 1278757 := bbase (se 4 (by rfl) ⟨119883, by rfl⟩ : syracuseStep 1278757 = 239767) (by norm_num)
theorem B1704773 : Blo 1008601 1704773 := bbase (se 4 (by rfl) ⟨159822, by rfl⟩ : syracuseStep 1704773 = 319645) (by norm_num)
theorem B2556805 : Blo 1008601 2556805 := bbase (se 4 (by rfl) ⟨239700, by rfl⟩ : syracuseStep 2556805 = 479401) (by norm_num)
theorem B1704901 : Blo 1008601 1704901 := bbase (se 4 (by rfl) ⟨159834, by rfl⟩ : syracuseStep 1704901 = 319669) (by norm_num)
theorem B1278929 : Blo 1008601 1278929 := bbase (se 2 (by rfl) ⟨479598, by rfl⟩ : syracuseStep 1278929 = 959197) (by norm_num)
theorem B2556917 : Blo 1008601 2556917 := bbase (se 5 (by rfl) ⟨119855, by rfl⟩ : syracuseStep 2556917 = 239711) (by norm_num)
theorem B1278985 : Blo 1008601 1278985 := bbase (se 2 (by rfl) ⟨479619, by rfl⟩ : syracuseStep 1278985 = 959239) (by norm_num)
theorem B1213465 : Blo 1008601 1213465 := bbase (se 2 (by rfl) ⟨455049, by rfl⟩ : syracuseStep 1213465 = 910099) (by norm_num)
theorem B1704989 : Blo 1008601 1704989 := bbase (se 3 (by rfl) ⟨319685, by rfl⟩ : syracuseStep 1704989 = 639371) (by norm_num)
theorem B3408965 : Blo 1008601 3408965 := bbase (se 4 (by rfl) ⟨319590, by rfl⟩ : syracuseStep 3408965 = 639181) (by norm_num)
theorem B3834965 : Blo 1008601 3834965 := bbase (se 8 (by rfl) ⟨22470, by rfl⟩ : syracuseStep 3834965 = 44941) (by norm_num)
theorem B1279081 : Blo 1008601 1279081 := bbase (se 2 (by rfl) ⟨479655, by rfl⟩ : syracuseStep 1279081 = 959311) (by norm_num)
theorem B1213561 : Blo 1008601 1213561 := bbase (se 2 (by rfl) ⟨455085, by rfl⟩ : syracuseStep 1213561 = 910171) (by norm_num)
theorem B6915221 : Blo 1008601 6915221 := bbase (se 6 (by rfl) ⟨162075, by rfl⟩ : syracuseStep 6915221 = 324151) (by norm_num)
theorem B1705117 : Blo 1008601 1705117 := bbase (se 3 (by rfl) ⟨319709, by rfl⟩ : syracuseStep 1705117 = 639419) (by norm_num)
theorem B2557109 : Blo 1008601 2557109 := bbase (se 5 (by rfl) ⟨119864, by rfl⟩ : syracuseStep 2557109 = 239729) (by norm_num)
theorem B1705205 : Blo 1008601 1705205 := bbase (se 5 (by rfl) ⟨79931, by rfl⟩ : syracuseStep 1705205 = 159863) (by norm_num)
theorem B1279253 : Blo 1008601 1279253 := bbase (se 6 (by rfl) ⟨29982, by rfl⟩ : syracuseStep 1279253 = 59965) (by norm_num)
theorem B1279309 : Blo 1008601 1279309 := bbase (se 3 (by rfl) ⟨239870, by rfl⟩ : syracuseStep 1279309 = 479741) (by norm_num)
theorem B5113205 : Blo 1008601 5113205 := bbase (se 5 (by rfl) ⟨239681, by rfl⟩ : syracuseStep 5113205 = 479363) (by norm_num)
theorem B1705333 : Blo 1008601 1705333 := bbase (se 5 (by rfl) ⟨79937, by rfl⟩ : syracuseStep 1705333 = 159875) (by norm_num)
theorem B1279405 : Blo 1008601 1279405 := bbase (se 3 (by rfl) ⟨239888, by rfl⟩ : syracuseStep 1279405 = 479777) (by norm_num)
theorem B1705421 : Blo 1008601 1705421 := bbase (se 3 (by rfl) ⟨319766, by rfl⟩ : syracuseStep 1705421 = 639533) (by norm_num)
theorem B3409397 : Blo 1008601 3409397 := bbase (se 5 (by rfl) ⟨159815, by rfl⟩ : syracuseStep 3409397 = 319631) (by norm_num)
theorem B2557453 : Blo 1008601 2557453 := bbase (se 3 (by rfl) ⟨479522, by rfl⟩ : syracuseStep 2557453 = 959045) (by norm_num)
theorem B1705549 : Blo 1008601 1705549 := bbase (se 3 (by rfl) ⟨319790, by rfl⟩ : syracuseStep 1705549 = 639581) (by norm_num)
theorem B1279577 : Blo 1008601 1279577 := bbase (se 2 (by rfl) ⟨479841, by rfl⟩ : syracuseStep 1279577 = 959683) (by norm_num)
theorem B2557565 : Blo 1008601 2557565 := bbase (se 3 (by rfl) ⟨479543, by rfl⟩ : syracuseStep 2557565 = 959087) (by norm_num)
theorem B1279633 : Blo 1008601 1279633 := bbase (se 2 (by rfl) ⟨479862, by rfl⟩ : syracuseStep 1279633 = 959725) (by norm_num)
theorem B2459285 : Blo 1008601 2459285 := bbase (se 6 (by rfl) ⟨57639, by rfl⟩ : syracuseStep 2459285 = 115279) (by norm_num)
theorem B1705637 : Blo 1008601 1705637 := bbase (se 4 (by rfl) ⟨159903, by rfl⟩ : syracuseStep 1705637 = 319807) (by norm_num)
theorem B1279729 : Blo 1008601 1279729 := bbase (se 2 (by rfl) ⟨479898, by rfl⟩ : syracuseStep 1279729 = 959797) (by norm_num)
theorem B1705765 : Blo 1008601 1705765 := bbase (se 4 (by rfl) ⟨159915, by rfl⟩ : syracuseStep 1705765 = 319831) (by norm_num)
theorem B2557757 : Blo 1008601 2557757 := bbase (se 3 (by rfl) ⟨479579, by rfl⟩ : syracuseStep 2557757 = 959159) (by norm_num)
theorem B1705853 : Blo 1008601 1705853 := bbase (se 3 (by rfl) ⟨319847, by rfl⟩ : syracuseStep 1705853 = 639695) (by norm_num)
theorem B1279901 : Blo 1008601 1279901 := bbase (se 3 (by rfl) ⟨239981, by rfl⟩ : syracuseStep 1279901 = 479963) (by norm_num)
theorem B3409829 : Blo 1008601 3409829 := bbase (se 4 (by rfl) ⟨319671, by rfl⟩ : syracuseStep 3409829 = 639343) (by norm_num)
theorem B1279957 : Blo 1008601 1279957 := bbase (se 7 (by rfl) ⟨14999, by rfl⟩ : syracuseStep 1279957 = 29999) (by norm_num)
theorem B1705981 : Blo 1008601 1705981 := bbase (se 3 (by rfl) ⟨319871, by rfl⟩ : syracuseStep 1705981 = 639743) (by norm_num)
theorem B1280053 : Blo 1008601 1280053 := bbase (se 5 (by rfl) ⟨60002, by rfl⟩ : syracuseStep 1280053 = 120005) (by norm_num)
theorem B1706069 : Blo 1008601 1706069 := bbase (se 8 (by rfl) ⟨9996, by rfl⟩ : syracuseStep 1706069 = 19993) (by norm_num)
theorem B1214561 : Blo 1008601 1214561 := bbase (se 2 (by rfl) ⟨455460, by rfl⟩ : syracuseStep 1214561 = 910921) (by norm_num)
theorem B4851845 : Blo 1008601 4851845 := bbase (se 4 (by rfl) ⟨454860, by rfl⟩ : syracuseStep 4851845 = 909721) (by norm_num)
theorem B2558101 : Blo 1008601 2558101 := bbase (se 6 (by rfl) ⟨59955, by rfl⟩ : syracuseStep 2558101 = 119911) (by norm_num)
theorem B1706197 : Blo 1008601 1706197 := bbase (se 7 (by rfl) ⟨19994, by rfl⟩ : syracuseStep 1706197 = 39989) (by norm_num)
theorem B1280225 : Blo 1008601 1280225 := bbase (se 2 (by rfl) ⟨480084, by rfl⟩ : syracuseStep 1280225 = 960169) (by norm_num)
theorem B2459909 : Blo 1008601 2459909 := bbase (se 4 (by rfl) ⟨230616, by rfl⟩ : syracuseStep 2459909 = 461233) (by norm_num)
theorem B2558213 : Blo 1008601 2558213 := bbase (se 4 (by rfl) ⟨239832, by rfl⟩ : syracuseStep 2558213 = 479665) (by norm_num)
theorem B1280281 : Blo 1008601 1280281 := bbase (se 2 (by rfl) ⟨480105, by rfl⟩ : syracuseStep 1280281 = 960211) (by norm_num)
theorem B1706285 : Blo 1008601 1706285 := bbase (se 3 (by rfl) ⟨319928, by rfl⟩ : syracuseStep 1706285 = 639857) (by norm_num)
theorem B3410261 : Blo 1008601 3410261 := bbase (se 10 (by rfl) ⟨4995, by rfl⟩ : syracuseStep 3410261 = 9991) (by norm_num)
theorem B1280377 : Blo 1008601 1280377 := bbase (se 2 (by rfl) ⟨480141, by rfl⟩ : syracuseStep 1280377 = 960283) (by norm_num)
theorem B1214849 : Blo 1008601 1214849 := bbase (se 2 (by rfl) ⟨455568, by rfl⟩ : syracuseStep 1214849 = 911137) (by norm_num)
theorem B2591117 : Blo 1008601 2591117 := bbase (se 3 (by rfl) ⟨485834, by rfl⟩ : syracuseStep 2591117 = 971669) (by norm_num)
theorem B3279253 : Blo 1008601 3279253 := bbase (se 6 (by rfl) ⟨76857, by rfl⟩ : syracuseStep 3279253 = 153715) (by norm_num)
theorem B1706413 : Blo 1008601 1706413 := bbase (se 3 (by rfl) ⟨319952, by rfl⟩ : syracuseStep 1706413 = 639905) (by norm_num)
theorem B2558405 : Blo 1008601 2558405 := bbase (se 4 (by rfl) ⟨239850, by rfl⟩ : syracuseStep 2558405 = 479701) (by norm_num)
theorem B1706501 : Blo 1008601 1706501 := bbase (se 4 (by rfl) ⟨159984, by rfl⟩ : syracuseStep 1706501 = 319969) (by norm_num)
theorem B1215013 : Blo 1008601 1215013 := bbase (se 4 (by rfl) ⟨113907, by rfl⟩ : syracuseStep 1215013 = 227815) (by norm_num)
theorem B1280549 : Blo 1008601 1280549 := bbase (se 4 (by rfl) ⟨120051, by rfl⟩ : syracuseStep 1280549 = 240103) (by norm_num)
theorem B1215041 : Blo 1008601 1215041 := bbase (se 2 (by rfl) ⟨455640, by rfl⟩ : syracuseStep 1215041 = 911281) (by norm_num)
theorem B1280605 : Blo 1008601 1280605 := bbase (se 3 (by rfl) ⟨240113, by rfl⟩ : syracuseStep 1280605 = 480227) (by norm_num)
theorem B5114501 : Blo 1008601 5114501 := bbase (se 4 (by rfl) ⟨479484, by rfl⟩ : syracuseStep 5114501 = 958969) (by norm_num)
theorem B1706629 : Blo 1008601 1706629 := bbase (se 4 (by rfl) ⟨159996, by rfl⟩ : syracuseStep 1706629 = 319993) (by norm_num)
theorem B2427565 : Blo 1008601 2427565 := bbase (se 3 (by rfl) ⟨455168, by rfl⟩ : syracuseStep 2427565 = 910337) (by norm_num)
theorem B1215157 : Blo 1008601 1215157 := bbase (se 5 (by rfl) ⟨56960, by rfl⟩ : syracuseStep 1215157 = 113921) (by norm_num)
theorem B1280701 : Blo 1008601 1280701 := bbase (se 3 (by rfl) ⟨240131, by rfl⟩ : syracuseStep 1280701 = 480263) (by norm_num)
theorem B1706717 : Blo 1008601 1706717 := bbase (se 3 (by rfl) ⟨320009, by rfl⟩ : syracuseStep 1706717 = 640019) (by norm_num)
theorem B3410693 : Blo 1008601 3410693 := bbase (se 4 (by rfl) ⟨319752, by rfl⟩ : syracuseStep 3410693 = 639505) (by norm_num)
theorem B2427661 : Blo 1008601 2427661 := bbase (se 3 (by rfl) ⟨455186, by rfl⟩ : syracuseStep 2427661 = 910373) (by norm_num)
theorem B1215253 : Blo 1008601 1215253 := bbase (se 6 (by rfl) ⟨28482, by rfl⟩ : syracuseStep 1215253 = 56965) (by norm_num)
theorem B2558749 : Blo 1008601 2558749 := bbase (se 3 (by rfl) ⟨479765, by rfl⟩ : syracuseStep 2558749 = 959531) (by norm_num)
theorem B1706845 : Blo 1008601 1706845 := bbase (se 3 (by rfl) ⟨320033, by rfl⟩ : syracuseStep 1706845 = 640067) (by norm_num)
theorem B1280873 : Blo 1008601 1280873 := bbase (se 2 (by rfl) ⟨480327, by rfl⟩ : syracuseStep 1280873 = 960655) (by norm_num)
theorem B2558861 : Blo 1008601 2558861 := bbase (se 3 (by rfl) ⟨479786, by rfl⟩ : syracuseStep 2558861 = 959573) (by norm_num)
theorem B1280929 : Blo 1008601 1280929 := bbase (se 2 (by rfl) ⟨480348, by rfl⟩ : syracuseStep 1280929 = 960697) (by norm_num)
theorem B1706933 : Blo 1008601 1706933 := bbase (se 5 (by rfl) ⟨80012, by rfl⟩ : syracuseStep 1706933 = 160025) (by norm_num)
theorem B2427853 : Blo 1008601 2427853 := bbase (se 3 (by rfl) ⟨455222, by rfl⟩ : syracuseStep 2427853 = 910445) (by norm_num)
theorem B1281025 : Blo 1008601 1281025 := bbase (se 2 (by rfl) ⟨480384, by rfl⟩ : syracuseStep 1281025 = 960769) (by norm_num)
theorem B1707061 : Blo 1008601 1707061 := bbase (se 5 (by rfl) ⟨80018, by rfl⟩ : syracuseStep 1707061 = 160037) (by norm_num)
theorem B2591813 : Blo 1008601 2591813 := bbase (se 4 (by rfl) ⟨242982, by rfl⟩ : syracuseStep 2591813 = 485965) (by norm_num)
theorem B2559053 : Blo 1008601 2559053 := bbase (se 3 (by rfl) ⟨479822, by rfl⟩ : syracuseStep 2559053 = 959645) (by norm_num)
theorem B1707149 : Blo 1008601 1707149 := bbase (se 3 (by rfl) ⟨320090, by rfl⟩ : syracuseStep 1707149 = 640181) (by norm_num)
theorem B3837077 : Blo 1008601 3837077 := bbase (se 6 (by rfl) ⟨89931, by rfl⟩ : syracuseStep 3837077 = 179863) (by norm_num)
theorem B1281197 : Blo 1008601 1281197 := bbase (se 3 (by rfl) ⟨240224, by rfl⟩ : syracuseStep 1281197 = 480449) (by norm_num)
theorem B3411125 : Blo 1008601 3411125 := bbase (se 5 (by rfl) ⟨159896, by rfl⟩ : syracuseStep 3411125 = 319793) (by norm_num)
theorem B1281253 : Blo 1008601 1281253 := bbase (se 4 (by rfl) ⟨120117, by rfl⟩ : syracuseStep 1281253 = 240235) (by norm_num)
theorem B1215733 : Blo 1008601 1215733 := bbase (se 5 (by rfl) ⟨56987, by rfl⟩ : syracuseStep 1215733 = 113975) (by norm_num)
theorem B1707277 : Blo 1008601 1707277 := bbase (se 3 (by rfl) ⟨320114, by rfl⟩ : syracuseStep 1707277 = 640229) (by norm_num)
theorem B2428181 : Blo 1008601 2428181 := bbase (se 6 (by rfl) ⟨56910, by rfl⟩ : syracuseStep 2428181 = 113821) (by norm_num)
theorem B1281349 : Blo 1008601 1281349 := bbase (se 4 (by rfl) ⟨120126, by rfl⟩ : syracuseStep 1281349 = 240253) (by norm_num)
theorem B1707365 : Blo 1008601 1707365 := bbase (se 4 (by rfl) ⟨160065, by rfl⟩ : syracuseStep 1707365 = 320131) (by norm_num)
theorem B2559397 : Blo 1008601 2559397 := bbase (se 4 (by rfl) ⟨239943, by rfl⟩ : syracuseStep 2559397 = 479887) (by norm_num)
theorem B3837365 : Blo 1008601 3837365 := bbase (se 5 (by rfl) ⟨179876, by rfl⟩ : syracuseStep 3837365 = 359753) (by norm_num)
theorem B1707493 : Blo 1008601 1707493 := bbase (se 4 (by rfl) ⟨160077, by rfl⟩ : syracuseStep 1707493 = 320155) (by norm_num)
theorem B1281521 : Blo 1008601 1281521 := bbase (se 2 (by rfl) ⟨480570, by rfl⟩ : syracuseStep 1281521 = 961141) (by norm_num)
theorem B2559509 : Blo 1008601 2559509 := bbase (se 6 (by rfl) ⟨59988, by rfl⟩ : syracuseStep 2559509 = 119977) (by norm_num)
theorem B1707581 : Blo 1008601 1707581 := bbase (se 3 (by rfl) ⟨320171, by rfl⟩ : syracuseStep 1707581 = 640343) (by norm_num)
theorem B3411557 : Blo 1008601 3411557 := bbase (se 4 (by rfl) ⟨319833, by rfl⟩ : syracuseStep 3411557 = 639667) (by norm_num)
theorem B1707709 : Blo 1008601 1707709 := bbase (se 3 (by rfl) ⟨320195, by rfl⟩ : syracuseStep 1707709 = 640391) (by norm_num)
theorem B2428613 : Blo 1008601 2428613 := bbase (se 4 (by rfl) ⟨227682, by rfl⟩ : syracuseStep 2428613 = 455365) (by norm_num)
theorem B2920133 : Blo 1008601 2920133 := bbase (se 4 (by rfl) ⟨273762, by rfl⟩ : syracuseStep 2920133 = 547525) (by norm_num)
theorem B7671509 : Blo 1008601 7671509 := bbase (se 7 (by rfl) ⟨89900, by rfl⟩ : syracuseStep 7671509 = 179801) (by norm_num)
theorem B2559701 : Blo 1008601 2559701 := bbase (se 7 (by rfl) ⟨29996, by rfl⟩ : syracuseStep 2559701 = 59993) (by norm_num)
theorem B19402517 : Blo 1008601 19402517 := bbase (se 6 (by rfl) ⟨454746, by rfl⟩ : syracuseStep 19402517 = 909493) (by norm_num)
theorem B1707797 : Blo 1008601 1707797 := bbase (se 6 (by rfl) ⟨40026, by rfl⟩ : syracuseStep 1707797 = 80053) (by norm_num)
theorem B5115797 : Blo 1008601 5115797 := bbase (se 6 (by rfl) ⟨119901, by rfl⟩ : syracuseStep 5115797 = 239803) (by norm_num)
theorem B1707925 : Blo 1008601 1707925 := bbase (se 6 (by rfl) ⟨40029, by rfl⟩ : syracuseStep 1707925 = 80059) (by norm_num)
theorem B1708013 : Blo 1008601 1708013 := bbase (se 3 (by rfl) ⟨320252, by rfl⟩ : syracuseStep 1708013 = 640505) (by norm_num)
theorem B2428949 : Blo 1008601 2428949 := bbase (se 6 (by rfl) ⟨56928, by rfl⟩ : syracuseStep 2428949 = 113857) (by norm_num)
theorem B3411989 : Blo 1008601 3411989 := bbase (se 6 (by rfl) ⟨79968, by rfl⟩ : syracuseStep 3411989 = 159937) (by norm_num)
theorem B2560045 : Blo 1008601 2560045 := bbase (se 3 (by rfl) ⟨480008, by rfl⟩ : syracuseStep 2560045 = 960017) (by norm_num)
theorem B1708141 : Blo 1008601 1708141 := bbase (se 3 (by rfl) ⟨320276, by rfl⟩ : syracuseStep 1708141 = 640553) (by norm_num)
theorem B2560157 : Blo 1008601 2560157 := bbase (se 3 (by rfl) ⟨480029, by rfl⟩ : syracuseStep 2560157 = 960059) (by norm_num)
theorem B1708229 : Blo 1008601 1708229 := bbase (se 4 (by rfl) ⟨160146, by rfl⟩ : syracuseStep 1708229 = 320293) (by norm_num)
theorem B19435733 : Blo 1008601 19435733 := bbase (se 7 (by rfl) ⟨227762, by rfl⟩ : syracuseStep 19435733 = 455525) (by norm_num)
theorem B1708357 : Blo 1008601 1708357 := bbase (se 4 (by rfl) ⟨160158, by rfl⟩ : syracuseStep 1708357 = 320317) (by norm_num)
theorem B2560349 : Blo 1008601 2560349 := bbase (se 3 (by rfl) ⟨480065, by rfl⟩ : syracuseStep 2560349 = 960131) (by norm_num)
theorem B1708445 : Blo 1008601 1708445 := bbase (se 3 (by rfl) ⟨320333, by rfl⟩ : syracuseStep 1708445 = 640667) (by norm_num)
theorem B3641765 : Blo 1008601 3641765 := bbase (se 4 (by rfl) ⟨341415, by rfl⟩ : syracuseStep 3641765 = 682831) (by norm_num)
theorem B3412421 : Blo 1008601 3412421 := bbase (se 4 (by rfl) ⟨319914, by rfl⟩ : syracuseStep 3412421 = 639829) (by norm_num)
theorem B1151453 : Blo 1008601 1151453 := bbase (se 3 (by rfl) ⟨215897, by rfl⟩ : syracuseStep 1151453 = 431795) (by norm_num)
theorem B1708573 : Blo 1008601 1708573 := bbase (se 3 (by rfl) ⟨320357, by rfl⟩ : syracuseStep 1708573 = 640715) (by norm_num)
theorem B3838549 : Blo 1008601 3838549 := bbase (se 8 (by rfl) ⟨22491, by rfl⟩ : syracuseStep 3838549 = 44983) (by norm_num)
theorem B1708661 : Blo 1008601 1708661 := bbase (se 5 (by rfl) ⟨80093, by rfl⟩ : syracuseStep 1708661 = 160187) (by norm_num)
theorem B2560693 : Blo 1008601 2560693 := bbase (se 5 (by rfl) ⟨120032, by rfl⟩ : syracuseStep 2560693 = 240065) (by norm_num)
theorem B2560805 : Blo 1008601 2560805 := bbase (se 4 (by rfl) ⟨240075, by rfl⟩ : syracuseStep 2560805 = 480151) (by norm_num)
theorem B3412853 : Blo 1008601 3412853 := bbase (se 5 (by rfl) ⟨159977, by rfl⟩ : syracuseStep 3412853 = 319955) (by norm_num)
theorem B3838853 : Blo 1008601 3838853 := bbase (se 4 (by rfl) ⟨359892, by rfl⟩ : syracuseStep 3838853 = 719785) (by norm_num)
theorem B2560997 : Blo 1008601 2560997 := bbase (se 4 (by rfl) ⟨240093, by rfl⟩ : syracuseStep 2560997 = 480187) (by norm_num)
theorem B2430005 : Blo 1008601 2430005 := bbase (se 5 (by rfl) ⟨113906, by rfl⟩ : syracuseStep 2430005 = 227813) (by norm_num)
theorem B1315921 : Blo 1008601 1315921 := bbase (se 2 (by rfl) ⟨493470, by rfl⟩ : syracuseStep 1315921 = 986941) (by norm_num)
theorem B5117093 : Blo 1008601 5117093 := bbase (se 4 (by rfl) ⟨479727, by rfl⟩ : syracuseStep 5117093 = 959455) (by norm_num)
theorem B2495701 : Blo 1008601 2495701 := bbase (se 7 (by rfl) ⟨29246, by rfl⟩ : syracuseStep 2495701 = 58493) (by norm_num)
theorem B3413285 : Blo 1008601 3413285 := bbase (se 4 (by rfl) ⟨319995, by rfl⟩ : syracuseStep 3413285 = 639991) (by norm_num)
theorem B2561341 : Blo 1008601 2561341 := bbase (se 3 (by rfl) ⟨480251, by rfl⟩ : syracuseStep 2561341 = 960503) (by norm_num)
theorem B2561453 : Blo 1008601 2561453 := bbase (se 3 (by rfl) ⟨480272, by rfl⟩ : syracuseStep 2561453 = 960545) (by norm_num)
theorem B1512917 : Blo 1008601 1512917 := bbase (se 7 (by rfl) ⟨17729, by rfl⟩ : syracuseStep 1512917 = 35459) (by norm_num)
theorem B1512941 : Blo 1008601 1512941 := bbase (se 3 (by rfl) ⟨283676, by rfl⟩ : syracuseStep 1512941 = 567353) (by norm_num)
theorem B1512965 : Blo 1008601 1512965 := bbase (se 4 (by rfl) ⟨141840, by rfl⟩ : syracuseStep 1512965 = 283681) (by norm_num)
theorem B1512989 : Blo 1008601 1512989 := bbase (se 3 (by rfl) ⟨283685, by rfl⟩ : syracuseStep 1512989 = 567371) (by norm_num)
theorem B1513013 : Blo 1008601 1513013 := bbase (se 5 (by rfl) ⟨70922, by rfl⟩ : syracuseStep 1513013 = 141845) (by norm_num)
theorem B1513037 : Blo 1008601 1513037 := bbase (se 3 (by rfl) ⟨283694, by rfl⟩ : syracuseStep 1513037 = 567389) (by norm_num)
theorem B1513061 : Blo 1008601 1513061 := bbase (se 4 (by rfl) ⟨141849, by rfl⟩ : syracuseStep 1513061 = 283699) (by norm_num)
theorem B2561645 : Blo 1008601 2561645 := bbase (se 3 (by rfl) ⟨480308, by rfl⟩ : syracuseStep 2561645 = 960617) (by norm_num)
theorem B1513085 : Blo 1008601 1513085 := bbase (se 3 (by rfl) ⟨283703, by rfl⟩ : syracuseStep 1513085 = 567407) (by norm_num)
theorem B1513109 : Blo 1008601 1513109 := bbase (se 6 (by rfl) ⟨35463, by rfl⟩ : syracuseStep 1513109 = 70927) (by norm_num)
theorem B1513133 : Blo 1008601 1513133 := bbase (se 3 (by rfl) ⟨283712, by rfl⟩ : syracuseStep 1513133 = 567425) (by norm_num)
theorem B1513157 : Blo 1008601 1513157 := bbase (se 4 (by rfl) ⟨141858, by rfl⟩ : syracuseStep 1513157 = 283717) (by norm_num)
theorem B3413717 : Blo 1008601 3413717 := bbase (se 7 (by rfl) ⟨40004, by rfl⟩ : syracuseStep 3413717 = 80009) (by norm_num)
theorem B1513181 : Blo 1008601 1513181 := bbase (se 3 (by rfl) ⟨283721, by rfl⟩ : syracuseStep 1513181 = 567443) (by norm_num)
theorem B1513205 : Blo 1008601 1513205 := bbase (se 5 (by rfl) ⟨70931, by rfl⟩ : syracuseStep 1513205 = 141863) (by norm_num)
theorem B1513229 : Blo 1008601 1513229 := bbase (se 3 (by rfl) ⟨283730, by rfl⟩ : syracuseStep 1513229 = 567461) (by norm_num)
theorem B1513253 : Blo 1008601 1513253 := bbase (se 4 (by rfl) ⟨141867, by rfl⟩ : syracuseStep 1513253 = 283735) (by norm_num)
theorem B1513277 : Blo 1008601 1513277 := bbase (se 3 (by rfl) ⟨283739, by rfl⟩ : syracuseStep 1513277 = 567479) (by norm_num)
theorem B1513301 : Blo 1008601 1513301 := bbase (se 9 (by rfl) ⟨4433, by rfl⟩ : syracuseStep 1513301 = 8867) (by norm_num)
theorem B1513325 : Blo 1008601 1513325 := bbase (se 3 (by rfl) ⟨283748, by rfl⟩ : syracuseStep 1513325 = 567497) (by norm_num)
theorem B1513349 : Blo 1008601 1513349 := bbase (se 4 (by rfl) ⟨141876, by rfl⟩ : syracuseStep 1513349 = 283753) (by norm_num)
theorem B1513373 : Blo 1008601 1513373 := bbase (se 3 (by rfl) ⟨283757, by rfl⟩ : syracuseStep 1513373 = 567515) (by norm_num)
theorem B1513397 : Blo 1008601 1513397 := bbase (se 5 (by rfl) ⟨70940, by rfl⟩ : syracuseStep 1513397 = 141881) (by norm_num)
theorem B2561989 : Blo 1008601 2561989 := bbase (se 4 (by rfl) ⟨240186, by rfl⟩ : syracuseStep 2561989 = 480373) (by norm_num)
theorem B1513421 : Blo 1008601 1513421 := bbase (se 3 (by rfl) ⟨283766, by rfl⟩ : syracuseStep 1513421 = 567533) (by norm_num)
theorem B1513445 : Blo 1008601 1513445 := bbase (se 4 (by rfl) ⟨141885, by rfl⟩ : syracuseStep 1513445 = 283771) (by norm_num)
theorem B5183461 : Blo 1008601 5183461 := bbase (se 4 (by rfl) ⟨485949, by rfl⟩ : syracuseStep 5183461 = 971899) (by norm_num)
theorem B1513469 : Blo 1008601 1513469 := bbase (se 3 (by rfl) ⟨283775, by rfl⟩ : syracuseStep 1513469 = 567551) (by norm_num)
theorem B1513493 : Blo 1008601 1513493 := bbase (se 6 (by rfl) ⟨35472, by rfl⟩ : syracuseStep 1513493 = 70945) (by norm_num)
theorem B2922533 : Blo 1008601 2922533 := bbase (se 4 (by rfl) ⟨273987, by rfl⟩ : syracuseStep 2922533 = 547975) (by norm_num)
theorem B1513517 : Blo 1008601 1513517 := bbase (se 3 (by rfl) ⟨283784, by rfl⟩ : syracuseStep 1513517 = 567569) (by norm_num)
theorem B2562101 : Blo 1008601 2562101 := bbase (se 5 (by rfl) ⟨120098, by rfl⟩ : syracuseStep 2562101 = 240197) (by norm_num)
theorem B1513541 : Blo 1008601 1513541 := bbase (se 4 (by rfl) ⟨141894, by rfl⟩ : syracuseStep 1513541 = 283789) (by norm_num)
theorem B1513565 : Blo 1008601 1513565 := bbase (se 3 (by rfl) ⟨283793, by rfl⟩ : syracuseStep 1513565 = 567587) (by norm_num)
theorem B1153121 : Blo 1008601 1153121 := bbase (se 2 (by rfl) ⟨432420, by rfl⟩ : syracuseStep 1153121 = 864841) (by norm_num)
theorem B1513589 : Blo 1008601 1513589 := bbase (se 5 (by rfl) ⟨70949, by rfl⟩ : syracuseStep 1513589 = 141899) (by norm_num)
theorem B3414149 : Blo 1008601 3414149 := bbase (se 4 (by rfl) ⟨320076, by rfl⟩ : syracuseStep 3414149 = 640153) (by norm_num)
theorem B1513613 : Blo 1008601 1513613 := bbase (se 3 (by rfl) ⟨283802, by rfl⟩ : syracuseStep 1513613 = 567605) (by norm_num)
theorem B1513637 : Blo 1008601 1513637 := bbase (se 4 (by rfl) ⟨141903, by rfl⟩ : syracuseStep 1513637 = 283807) (by norm_num)
theorem B1513661 : Blo 1008601 1513661 := bbase (se 3 (by rfl) ⟨283811, by rfl⟩ : syracuseStep 1513661 = 567623) (by norm_num)
theorem B1513685 : Blo 1008601 1513685 := bbase (se 7 (by rfl) ⟨17738, by rfl⟩ : syracuseStep 1513685 = 35477) (by norm_num)
theorem B1513709 : Blo 1008601 1513709 := bbase (se 3 (by rfl) ⟨283820, by rfl⟩ : syracuseStep 1513709 = 567641) (by norm_num)
theorem B2562293 : Blo 1008601 2562293 := bbase (se 5 (by rfl) ⟨120107, by rfl⟩ : syracuseStep 2562293 = 240215) (by norm_num)
theorem B1513733 : Blo 1008601 1513733 := bbase (se 4 (by rfl) ⟨141912, by rfl⟩ : syracuseStep 1513733 = 283825) (by norm_num)
theorem B1513757 : Blo 1008601 1513757 := bbase (se 3 (by rfl) ⟨283829, by rfl⟩ : syracuseStep 1513757 = 567659) (by norm_num)
theorem B1513781 : Blo 1008601 1513781 := bbase (se 5 (by rfl) ⟨70958, by rfl⟩ : syracuseStep 1513781 = 141917) (by norm_num)
theorem B1513805 : Blo 1008601 1513805 := bbase (se 3 (by rfl) ⟨283838, by rfl⟩ : syracuseStep 1513805 = 567677) (by norm_num)
theorem B4921685 : Blo 1008601 4921685 := bbase (se 10 (by rfl) ⟨7209, by rfl⟩ : syracuseStep 4921685 = 14419) (by norm_num)
theorem B1513829 : Blo 1008601 1513829 := bbase (se 4 (by rfl) ⟨141921, by rfl⟩ : syracuseStep 1513829 = 283843) (by norm_num)
theorem B1513853 : Blo 1008601 1513853 := bbase (se 3 (by rfl) ⟨283847, by rfl⟩ : syracuseStep 1513853 = 567695) (by norm_num)
theorem B2660741 : Blo 1008601 2660741 := bbase (se 4 (by rfl) ⟨249444, by rfl⟩ : syracuseStep 2660741 = 498889) (by norm_num)
theorem B1513877 : Blo 1008601 1513877 := bbase (se 6 (by rfl) ⟨35481, by rfl⟩ : syracuseStep 1513877 = 70963) (by norm_num)
theorem B1513901 : Blo 1008601 1513901 := bbase (se 3 (by rfl) ⟨283856, by rfl⟩ : syracuseStep 1513901 = 567713) (by norm_num)
theorem B5118389 : Blo 1008601 5118389 := bbase (se 5 (by rfl) ⟨239924, by rfl⟩ : syracuseStep 5118389 = 479849) (by norm_num)
theorem B1513925 : Blo 1008601 1513925 := bbase (se 4 (by rfl) ⟨141930, by rfl⟩ : syracuseStep 1513925 = 283861) (by norm_num)
theorem B1513949 : Blo 1008601 1513949 := bbase (se 3 (by rfl) ⟨283865, by rfl⟩ : syracuseStep 1513949 = 567731) (by norm_num)
theorem B1513973 : Blo 1008601 1513973 := bbase (se 5 (by rfl) ⟨70967, by rfl⟩ : syracuseStep 1513973 = 141935) (by norm_num)
theorem B1513997 : Blo 1008601 1513997 := bbase (se 3 (by rfl) ⟨283874, by rfl⟩ : syracuseStep 1513997 = 567749) (by norm_num)
theorem B1514021 : Blo 1008601 1514021 := bbase (se 4 (by rfl) ⟨141939, by rfl⟩ : syracuseStep 1514021 = 283879) (by norm_num)
theorem B3414581 : Blo 1008601 3414581 := bbase (se 5 (by rfl) ⟨160058, by rfl⟩ : syracuseStep 3414581 = 320117) (by norm_num)
theorem B1514045 : Blo 1008601 1514045 := bbase (se 3 (by rfl) ⟨283883, by rfl⟩ : syracuseStep 1514045 = 567767) (by norm_num)
theorem B2562637 : Blo 1008601 2562637 := bbase (se 3 (by rfl) ⟨480494, by rfl⟩ : syracuseStep 2562637 = 960989) (by norm_num)
theorem B1514069 : Blo 1008601 1514069 := bbase (se 8 (by rfl) ⟨8871, by rfl⟩ : syracuseStep 1514069 = 17743) (by norm_num)
theorem B1514093 : Blo 1008601 1514093 := bbase (se 3 (by rfl) ⟨283892, by rfl⟩ : syracuseStep 1514093 = 567785) (by norm_num)
theorem B1514117 : Blo 1008601 1514117 := bbase (se 4 (by rfl) ⟨141948, by rfl⟩ : syracuseStep 1514117 = 283897) (by norm_num)
theorem B1514141 : Blo 1008601 1514141 := bbase (se 3 (by rfl) ⟨283901, by rfl⟩ : syracuseStep 1514141 = 567803) (by norm_num)
theorem B1514165 : Blo 1008601 1514165 := bbase (se 5 (by rfl) ⟨70976, by rfl⟩ : syracuseStep 1514165 = 141953) (by norm_num)
theorem B2562749 : Blo 1008601 2562749 := bbase (se 3 (by rfl) ⟨480515, by rfl⟩ : syracuseStep 2562749 = 961031) (by norm_num)
theorem B1514189 : Blo 1008601 1514189 := bbase (se 3 (by rfl) ⟨283910, by rfl⟩ : syracuseStep 1514189 = 567821) (by norm_num)
theorem B1514213 : Blo 1008601 1514213 := bbase (se 4 (by rfl) ⟨141957, by rfl⟩ : syracuseStep 1514213 = 283915) (by norm_num)
theorem B1514237 : Blo 1008601 1514237 := bbase (se 3 (by rfl) ⟨283919, by rfl⟩ : syracuseStep 1514237 = 567839) (by norm_num)
theorem B4922117 : Blo 1008601 4922117 := bbase (se 4 (by rfl) ⟨461448, by rfl⟩ : syracuseStep 4922117 = 922897) (by norm_num)
theorem B1514261 : Blo 1008601 1514261 := bbase (se 6 (by rfl) ⟨35490, by rfl⟩ : syracuseStep 1514261 = 70981) (by norm_num)
theorem B1514285 : Blo 1008601 1514285 := bbase (se 3 (by rfl) ⟨283928, by rfl⟩ : syracuseStep 1514285 = 567857) (by norm_num)
theorem B1514309 : Blo 1008601 1514309 := bbase (se 4 (by rfl) ⟨141966, by rfl⟩ : syracuseStep 1514309 = 283933) (by norm_num)
theorem B8624981 : Blo 1008601 8624981 := bbase (se 9 (by rfl) ⟨25268, by rfl⟩ : syracuseStep 8624981 = 50537) (by norm_num)
theorem B1514333 : Blo 1008601 1514333 := bbase (se 3 (by rfl) ⟨283937, by rfl⟩ : syracuseStep 1514333 = 567875) (by norm_num)
theorem B3644261 : Blo 1008601 3644261 := bbase (se 4 (by rfl) ⟨341649, by rfl⟩ : syracuseStep 3644261 = 683299) (by norm_num)
theorem B1514357 : Blo 1008601 1514357 := bbase (se 5 (by rfl) ⟨70985, by rfl⟩ : syracuseStep 1514357 = 141971) (by norm_num)
theorem B2562941 : Blo 1008601 2562941 := bbase (se 3 (by rfl) ⟨480551, by rfl⟩ : syracuseStep 2562941 = 961103) (by norm_num)
theorem B1514381 : Blo 1008601 1514381 := bbase (se 3 (by rfl) ⟨283946, by rfl⟩ : syracuseStep 1514381 = 567893) (by norm_num)
theorem B1514405 : Blo 1008601 1514405 := bbase (se 4 (by rfl) ⟨141975, by rfl⟩ : syracuseStep 1514405 = 283951) (by norm_num)
theorem B2726837 : Blo 1008601 2726837 := bbase (se 5 (by rfl) ⟨127820, by rfl⟩ : syracuseStep 2726837 = 255641) (by norm_num)
theorem B1022905 : Blo 1008601 1022905 := bbase (se 2 (by rfl) ⟨383589, by rfl⟩ : syracuseStep 1022905 = 767179) (by norm_num)
theorem B1514429 : Blo 1008601 1514429 := bbase (se 3 (by rfl) ⟨283955, by rfl⟩ : syracuseStep 1514429 = 567911) (by norm_num)
theorem B3840965 : Blo 1008601 3840965 := bbase (se 4 (by rfl) ⟨360090, by rfl⟩ : syracuseStep 3840965 = 720181) (by norm_num)
theorem B1153993 : Blo 1008601 1153993 := bbase (se 2 (by rfl) ⟨432747, by rfl⟩ : syracuseStep 1153993 = 865495) (by norm_num)
theorem B1514453 : Blo 1008601 1514453 := bbase (se 7 (by rfl) ⟨17747, by rfl⟩ : syracuseStep 1514453 = 35495) (by norm_num)
theorem B3415013 : Blo 1008601 3415013 := bbase (se 4 (by rfl) ⟨320157, by rfl⟩ : syracuseStep 3415013 = 640315) (by norm_num)
theorem B1514477 : Blo 1008601 1514477 := bbase (se 3 (by rfl) ⟨283964, by rfl⟩ : syracuseStep 1514477 = 567929) (by norm_num)
theorem B1514501 : Blo 1008601 1514501 := bbase (se 4 (by rfl) ⟨141984, by rfl⟩ : syracuseStep 1514501 = 283969) (by norm_num)
theorem B1514525 : Blo 1008601 1514525 := bbase (se 3 (by rfl) ⟨283973, by rfl⟩ : syracuseStep 1514525 = 567947) (by norm_num)
theorem B1514549 : Blo 1008601 1514549 := bbase (se 5 (by rfl) ⟨70994, by rfl⟩ : syracuseStep 1514549 = 141989) (by norm_num)
theorem B1514573 : Blo 1008601 1514573 := bbase (se 3 (by rfl) ⟨283982, by rfl⟩ : syracuseStep 1514573 = 567965) (by norm_num)
theorem B4856917 : Blo 1008601 4856917 := bbase (se 8 (by rfl) ⟨28458, by rfl⟩ : syracuseStep 4856917 = 56917) (by norm_num)
theorem B1514597 : Blo 1008601 1514597 := bbase (se 4 (by rfl) ⟨141993, by rfl⟩ : syracuseStep 1514597 = 283987) (by norm_num)
theorem B1514621 : Blo 1008601 1514621 := bbase (se 3 (by rfl) ⟨283991, by rfl⟩ : syracuseStep 1514621 = 567983) (by norm_num)
theorem B1514645 : Blo 1008601 1514645 := bbase (se 6 (by rfl) ⟨35499, by rfl⟩ : syracuseStep 1514645 = 70999) (by norm_num)
theorem B1514669 : Blo 1008601 1514669 := bbase (se 3 (by rfl) ⟨284000, by rfl⟩ : syracuseStep 1514669 = 568001) (by norm_num)
theorem B1514693 : Blo 1008601 1514693 := bbase (se 4 (by rfl) ⟨142002, by rfl⟩ : syracuseStep 1514693 = 284005) (by norm_num)
theorem B2432197 : Blo 1008601 2432197 := bbase (se 4 (by rfl) ⟨228018, by rfl⟩ : syracuseStep 2432197 = 456037) (by norm_num)
theorem B1514717 : Blo 1008601 1514717 := bbase (se 3 (by rfl) ⟨284009, by rfl⟩ : syracuseStep 1514717 = 568019) (by norm_num)
theorem B3841253 : Blo 1008601 3841253 := bbase (se 4 (by rfl) ⟨360117, by rfl⟩ : syracuseStep 3841253 = 720235) (by norm_num)
theorem B1514741 : Blo 1008601 1514741 := bbase (se 5 (by rfl) ⟨71003, by rfl⟩ : syracuseStep 1514741 = 142007) (by norm_num)
theorem B1514765 : Blo 1008601 1514765 := bbase (se 3 (by rfl) ⟨284018, by rfl⟩ : syracuseStep 1514765 = 568037) (by norm_num)
theorem B1514789 : Blo 1008601 1514789 := bbase (se 4 (by rfl) ⟨142011, by rfl⟩ : syracuseStep 1514789 = 284023) (by norm_num)
theorem B1514813 : Blo 1008601 1514813 := bbase (se 3 (by rfl) ⟨284027, by rfl⟩ : syracuseStep 1514813 = 568055) (by norm_num)
theorem B1514837 : Blo 1008601 1514837 := bbase (se 11 (by rfl) ⟨1109, by rfl⟩ : syracuseStep 1514837 = 2219) (by norm_num)
theorem B1514861 : Blo 1008601 1514861 := bbase (se 3 (by rfl) ⟨284036, by rfl⟩ : syracuseStep 1514861 = 568073) (by norm_num)
theorem B1154417 : Blo 1008601 1154417 := bbase (se 2 (by rfl) ⟨432906, by rfl⟩ : syracuseStep 1154417 = 865813) (by norm_num)
theorem B1514885 : Blo 1008601 1514885 := bbase (se 4 (by rfl) ⟨142020, by rfl⟩ : syracuseStep 1514885 = 284041) (by norm_num)
theorem B3415445 : Blo 1008601 3415445 := bbase (se 6 (by rfl) ⟨80049, by rfl⟩ : syracuseStep 3415445 = 160099) (by norm_num)
theorem B1514909 : Blo 1008601 1514909 := bbase (se 3 (by rfl) ⟨284045, by rfl⟩ : syracuseStep 1514909 = 568091) (by norm_num)
theorem B3644837 : Blo 1008601 3644837 := bbase (se 4 (by rfl) ⟨341703, by rfl⟩ : syracuseStep 3644837 = 683407) (by norm_num)
theorem B1514933 : Blo 1008601 1514933 := bbase (se 5 (by rfl) ⟨71012, by rfl⟩ : syracuseStep 1514933 = 142025) (by norm_num)
theorem B1514957 : Blo 1008601 1514957 := bbase (se 3 (by rfl) ⟨284054, by rfl⟩ : syracuseStep 1514957 = 568109) (by norm_num)
theorem B1514981 : Blo 1008601 1514981 := bbase (se 4 (by rfl) ⟨142029, by rfl⟩ : syracuseStep 1514981 = 284059) (by norm_num)
theorem B1515005 : Blo 1008601 1515005 := bbase (se 3 (by rfl) ⟨284063, by rfl⟩ : syracuseStep 1515005 = 568127) (by norm_num)
theorem B1515029 : Blo 1008601 1515029 := bbase (se 6 (by rfl) ⟨35508, by rfl⟩ : syracuseStep 1515029 = 71017) (by norm_num)
theorem B3939877 : Blo 1008601 3939877 := bbase (se 4 (by rfl) ⟨369363, by rfl⟩ : syracuseStep 3939877 = 738727) (by norm_num)
theorem B1515053 : Blo 1008601 1515053 := bbase (se 3 (by rfl) ⟨284072, by rfl⟩ : syracuseStep 1515053 = 568145) (by norm_num)
theorem B1515077 : Blo 1008601 1515077 := bbase (se 4 (by rfl) ⟨142038, by rfl⟩ : syracuseStep 1515077 = 284077) (by norm_num)
theorem B1515101 : Blo 1008601 1515101 := bbase (se 3 (by rfl) ⟨284081, by rfl⟩ : syracuseStep 1515101 = 568163) (by norm_num)
theorem B1515125 : Blo 1008601 1515125 := bbase (se 5 (by rfl) ⟨71021, by rfl⟩ : syracuseStep 1515125 = 142043) (by norm_num)
theorem B1515149 : Blo 1008601 1515149 := bbase (se 3 (by rfl) ⟨284090, by rfl⟩ : syracuseStep 1515149 = 568181) (by norm_num)
theorem B1515173 : Blo 1008601 1515173 := bbase (se 4 (by rfl) ⟨142047, by rfl⟩ : syracuseStep 1515173 = 284095) (by norm_num)
theorem B1515197 : Blo 1008601 1515197 := bbase (se 3 (by rfl) ⟨284099, by rfl⟩ : syracuseStep 1515197 = 568199) (by norm_num)
theorem B5119685 : Blo 1008601 5119685 := bbase (se 4 (by rfl) ⟨479970, by rfl⟩ : syracuseStep 5119685 = 959941) (by norm_num)
theorem B1515221 : Blo 1008601 1515221 := bbase (se 7 (by rfl) ⟨17756, by rfl⟩ : syracuseStep 1515221 = 35513) (by norm_num)
theorem B1515245 : Blo 1008601 1515245 := bbase (se 3 (by rfl) ⟨284108, by rfl⟩ : syracuseStep 1515245 = 568217) (by norm_num)
theorem B5840629 : Blo 1008601 5840629 := bbase (se 5 (by rfl) ⟨273779, by rfl⟩ : syracuseStep 5840629 = 547559) (by norm_num)
theorem B1515269 : Blo 1008601 1515269 := bbase (se 4 (by rfl) ⟨142056, by rfl⟩ : syracuseStep 1515269 = 284113) (by norm_num)
theorem B6463253 : Blo 1008601 6463253 := bbase (se 6 (by rfl) ⟨151482, by rfl⟩ : syracuseStep 6463253 = 302965) (by norm_num)
theorem B1515293 : Blo 1008601 1515293 := bbase (se 3 (by rfl) ⟨284117, by rfl⟩ : syracuseStep 1515293 = 568235) (by norm_num)
theorem B1515317 : Blo 1008601 1515317 := bbase (se 5 (by rfl) ⟨71030, by rfl⟩ : syracuseStep 1515317 = 142061) (by norm_num)
theorem B3415877 : Blo 1008601 3415877 := bbase (se 4 (by rfl) ⟨320238, by rfl⟩ : syracuseStep 3415877 = 640477) (by norm_num)
theorem B1515341 : Blo 1008601 1515341 := bbase (se 3 (by rfl) ⟨284126, by rfl⟩ : syracuseStep 1515341 = 568253) (by norm_num)
theorem B3645269 : Blo 1008601 3645269 := bbase (se 9 (by rfl) ⟨10679, by rfl⟩ : syracuseStep 3645269 = 21359) (by norm_num)
theorem B1515365 : Blo 1008601 1515365 := bbase (se 4 (by rfl) ⟨142065, by rfl⟩ : syracuseStep 1515365 = 284131) (by norm_num)
theorem B1515389 : Blo 1008601 1515389 := bbase (se 3 (by rfl) ⟨284135, by rfl⟩ : syracuseStep 1515389 = 568271) (by norm_num)
theorem B1515413 : Blo 1008601 1515413 := bbase (se 6 (by rfl) ⟨35517, by rfl⟩ : syracuseStep 1515413 = 71035) (by norm_num)
theorem B1515437 : Blo 1008601 1515437 := bbase (se 3 (by rfl) ⟨284144, by rfl⟩ : syracuseStep 1515437 = 568289) (by norm_num)
theorem B1515461 : Blo 1008601 1515461 := bbase (se 4 (by rfl) ⟨142074, by rfl⟩ : syracuseStep 1515461 = 284149) (by norm_num)
theorem B1515485 : Blo 1008601 1515485 := bbase (se 3 (by rfl) ⟨284153, by rfl⟩ : syracuseStep 1515485 = 568307) (by norm_num)
theorem B1515509 : Blo 1008601 1515509 := bbase (se 5 (by rfl) ⟨71039, by rfl⟩ : syracuseStep 1515509 = 142079) (by norm_num)
theorem B1515533 : Blo 1008601 1515533 := bbase (se 3 (by rfl) ⟨284162, by rfl⟩ : syracuseStep 1515533 = 568325) (by norm_num)
theorem B1515557 : Blo 1008601 1515557 := bbase (se 4 (by rfl) ⟨142083, by rfl⟩ : syracuseStep 1515557 = 284167) (by norm_num)
theorem B1515581 : Blo 1008601 1515581 := bbase (se 3 (by rfl) ⟨284171, by rfl⟩ : syracuseStep 1515581 = 568343) (by norm_num)
theorem B1515605 : Blo 1008601 1515605 := bbase (se 8 (by rfl) ⟨8880, by rfl⟩ : syracuseStep 1515605 = 17761) (by norm_num)
theorem B1515629 : Blo 1008601 1515629 := bbase (se 3 (by rfl) ⟨284180, by rfl⟩ : syracuseStep 1515629 = 568361) (by norm_num)
theorem B1024121 : Blo 1008601 1024121 := bbase (se 2 (by rfl) ⟨384045, by rfl⟩ : syracuseStep 1024121 = 768091) (by norm_num)
theorem B1515653 : Blo 1008601 1515653 := bbase (se 4 (by rfl) ⟨142092, by rfl⟩ : syracuseStep 1515653 = 284185) (by norm_num)
theorem B1024153 : Blo 1008601 1024153 := bbase (se 2 (by rfl) ⟨384057, by rfl⟩ : syracuseStep 1024153 = 768115) (by norm_num)
theorem B1515677 : Blo 1008601 1515677 := bbase (se 3 (by rfl) ⟨284189, by rfl⟩ : syracuseStep 1515677 = 568379) (by norm_num)
theorem B1515701 : Blo 1008601 1515701 := bbase (se 5 (by rfl) ⟨71048, by rfl⟩ : syracuseStep 1515701 = 142097) (by norm_num)
theorem B1515725 : Blo 1008601 1515725 := bbase (se 3 (by rfl) ⟨284198, by rfl⟩ : syracuseStep 1515725 = 568397) (by norm_num)
theorem B2597069 : Blo 1008601 2597069 := bbase (se 3 (by rfl) ⟨486950, by rfl⟩ : syracuseStep 2597069 = 973901) (by norm_num)
theorem B1515749 : Blo 1008601 1515749 := bbase (se 4 (by rfl) ⟨142101, by rfl⟩ : syracuseStep 1515749 = 284203) (by norm_num)
theorem B2269421 : Blo 1008601 2269421 := bbase (se 3 (by rfl) ⟨425516, by rfl⟩ : syracuseStep 2269421 = 851033) (by norm_num)
theorem B3416309 : Blo 1008601 3416309 := bbase (se 5 (by rfl) ⟨160139, by rfl⟩ : syracuseStep 3416309 = 320279) (by norm_num)
theorem B1515773 : Blo 1008601 1515773 := bbase (se 3 (by rfl) ⟨284207, by rfl⟩ : syracuseStep 1515773 = 568415) (by norm_num)
theorem B1515797 : Blo 1008601 1515797 := bbase (se 6 (by rfl) ⟨35526, by rfl⟩ : syracuseStep 1515797 = 71053) (by norm_num)
theorem B1515821 : Blo 1008601 1515821 := bbase (se 3 (by rfl) ⟨284216, by rfl⟩ : syracuseStep 1515821 = 568433) (by norm_num)
theorem B2269493 : Blo 1008601 2269493 := bbase (se 5 (by rfl) ⟨106382, by rfl⟩ : syracuseStep 2269493 = 212765) (by norm_num)
theorem B1515845 : Blo 1008601 1515845 := bbase (se 4 (by rfl) ⟨142110, by rfl⟩ : syracuseStep 1515845 = 284221) (by norm_num)
theorem B1515869 : Blo 1008601 1515869 := bbase (se 3 (by rfl) ⟨284225, by rfl⟩ : syracuseStep 1515869 = 568451) (by norm_num)
theorem B1515893 : Blo 1008601 1515893 := bbase (se 5 (by rfl) ⟨71057, by rfl⟩ : syracuseStep 1515893 = 142115) (by norm_num)
theorem B2269565 : Blo 1008601 2269565 := bbase (se 3 (by rfl) ⟨425543, by rfl⟩ : syracuseStep 2269565 = 851087) (by norm_num)
theorem B3842437 : Blo 1008601 3842437 := bbase (se 4 (by rfl) ⟨360228, by rfl⟩ : syracuseStep 3842437 = 720457) (by norm_num)
theorem B1515917 : Blo 1008601 1515917 := bbase (se 3 (by rfl) ⟨284234, by rfl⟩ : syracuseStep 1515917 = 568469) (by norm_num)
theorem B1515941 : Blo 1008601 1515941 := bbase (se 4 (by rfl) ⟨142119, by rfl⟩ : syracuseStep 1515941 = 284239) (by norm_num)
theorem B1515965 : Blo 1008601 1515965 := bbase (se 3 (by rfl) ⟨284243, by rfl⟩ : syracuseStep 1515965 = 568487) (by norm_num)
theorem B2269637 : Blo 1008601 2269637 := bbase (se 4 (by rfl) ⟨212778, by rfl⟩ : syracuseStep 2269637 = 425557) (by norm_num)
theorem B1515989 : Blo 1008601 1515989 := bbase (se 7 (by rfl) ⟨17765, by rfl⟩ : syracuseStep 1515989 = 35531) (by norm_num)
theorem B1516013 : Blo 1008601 1516013 := bbase (se 3 (by rfl) ⟨284252, by rfl⟩ : syracuseStep 1516013 = 568505) (by norm_num)
theorem B1516037 : Blo 1008601 1516037 := bbase (se 4 (by rfl) ⟨142128, by rfl⟩ : syracuseStep 1516037 = 284257) (by norm_num)
theorem B2269709 : Blo 1008601 2269709 := bbase (se 3 (by rfl) ⟨425570, by rfl⟩ : syracuseStep 2269709 = 851141) (by norm_num)
theorem B1516061 : Blo 1008601 1516061 := bbase (se 3 (by rfl) ⟨284261, by rfl⟩ : syracuseStep 1516061 = 568523) (by norm_num)
theorem B1516085 : Blo 1008601 1516085 := bbase (se 5 (by rfl) ⟨71066, by rfl⟩ : syracuseStep 1516085 = 142133) (by norm_num)
theorem B1516109 : Blo 1008601 1516109 := bbase (se 3 (by rfl) ⟨284270, by rfl⟩ : syracuseStep 1516109 = 568541) (by norm_num)
theorem B2269781 : Blo 1008601 2269781 := bbase (se 8 (by rfl) ⟨13299, by rfl⟩ : syracuseStep 2269781 = 26599) (by norm_num)
theorem B1516133 : Blo 1008601 1516133 := bbase (se 4 (by rfl) ⟨142137, by rfl⟩ : syracuseStep 1516133 = 284275) (by norm_num)
theorem B1516157 : Blo 1008601 1516157 := bbase (se 3 (by rfl) ⟨284279, by rfl⟩ : syracuseStep 1516157 = 568559) (by norm_num)
theorem B1516181 : Blo 1008601 1516181 := bbase (se 6 (by rfl) ⟨35535, by rfl⟩ : syracuseStep 1516181 = 71071) (by norm_num)
theorem B2269853 : Blo 1008601 2269853 := bbase (se 3 (by rfl) ⟨425597, by rfl⟩ : syracuseStep 2269853 = 851195) (by norm_num)
theorem B3416741 : Blo 1008601 3416741 := bbase (se 4 (by rfl) ⟨320319, by rfl⟩ : syracuseStep 3416741 = 640639) (by norm_num)
theorem B1516205 : Blo 1008601 1516205 := bbase (se 3 (by rfl) ⟨284288, by rfl⟩ : syracuseStep 1516205 = 568577) (by norm_num)
theorem B3842741 : Blo 1008601 3842741 := bbase (se 5 (by rfl) ⟨180128, by rfl⟩ : syracuseStep 3842741 = 360257) (by norm_num)
theorem B1516229 : Blo 1008601 1516229 := bbase (se 4 (by rfl) ⟨142146, by rfl⟩ : syracuseStep 1516229 = 284293) (by norm_num)
theorem B1516253 : Blo 1008601 1516253 := bbase (se 3 (by rfl) ⟨284297, by rfl⟩ : syracuseStep 1516253 = 568595) (by norm_num)
theorem B2269925 : Blo 1008601 2269925 := bbase (se 4 (by rfl) ⟨212805, by rfl⟩ : syracuseStep 2269925 = 425611) (by norm_num)
theorem B1516277 : Blo 1008601 1516277 := bbase (se 5 (by rfl) ⟨71075, by rfl⟩ : syracuseStep 1516277 = 142151) (by norm_num)
theorem B1516301 : Blo 1008601 1516301 := bbase (se 3 (by rfl) ⟨284306, by rfl⟩ : syracuseStep 1516301 = 568613) (by norm_num)
theorem B1516325 : Blo 1008601 1516325 := bbase (se 4 (by rfl) ⟨142155, by rfl⟩ : syracuseStep 1516325 = 284311) (by norm_num)
theorem B2269997 : Blo 1008601 2269997 := bbase (se 3 (by rfl) ⟨425624, by rfl⟩ : syracuseStep 2269997 = 851249) (by norm_num)
theorem B1516349 : Blo 1008601 1516349 := bbase (se 3 (by rfl) ⟨284315, by rfl⟩ : syracuseStep 1516349 = 568631) (by norm_num)
theorem B1516373 : Blo 1008601 1516373 := bbase (se 9 (by rfl) ⟨4442, by rfl⟩ : syracuseStep 1516373 = 8885) (by norm_num)
theorem B1516397 : Blo 1008601 1516397 := bbase (se 3 (by rfl) ⟨284324, by rfl⟩ : syracuseStep 1516397 = 568649) (by norm_num)
theorem B2270069 : Blo 1008601 2270069 := bbase (se 5 (by rfl) ⟨106409, by rfl⟩ : syracuseStep 2270069 = 212819) (by norm_num)
theorem B1516421 : Blo 1008601 1516421 := bbase (se 4 (by rfl) ⟨142164, by rfl⟩ : syracuseStep 1516421 = 284329) (by norm_num)
theorem B1516445 : Blo 1008601 1516445 := bbase (se 3 (by rfl) ⟨284333, by rfl⟩ : syracuseStep 1516445 = 568667) (by norm_num)
theorem B1516469 : Blo 1008601 1516469 := bbase (se 5 (by rfl) ⟨71084, by rfl⟩ : syracuseStep 1516469 = 142169) (by norm_num)
theorem B2270141 : Blo 1008601 2270141 := bbase (se 3 (by rfl) ⟨425651, by rfl⟩ : syracuseStep 2270141 = 851303) (by norm_num)
theorem B1516493 : Blo 1008601 1516493 := bbase (se 3 (by rfl) ⟨284342, by rfl⟩ : syracuseStep 1516493 = 568685) (by norm_num)
theorem B5120981 : Blo 1008601 5120981 := bbase (se 7 (by rfl) ⟨60011, by rfl⟩ : syracuseStep 5120981 = 120023) (by norm_num)
theorem B1516517 : Blo 1008601 1516517 := bbase (se 4 (by rfl) ⟨142173, by rfl⟩ : syracuseStep 1516517 = 284347) (by norm_num)
theorem B1516541 : Blo 1008601 1516541 := bbase (se 3 (by rfl) ⟨284351, by rfl⟩ : syracuseStep 1516541 = 568703) (by norm_num)
theorem B2270213 : Blo 1008601 2270213 := bbase (se 4 (by rfl) ⟨212832, by rfl⟩ : syracuseStep 2270213 = 425665) (by norm_num)
theorem B1516565 : Blo 1008601 1516565 := bbase (se 6 (by rfl) ⟨35544, by rfl⟩ : syracuseStep 1516565 = 71089) (by norm_num)
theorem B1516589 : Blo 1008601 1516589 := bbase (se 3 (by rfl) ⟨284360, by rfl⟩ : syracuseStep 1516589 = 568721) (by norm_num)
theorem B1516613 : Blo 1008601 1516613 := bbase (se 4 (by rfl) ⟨142182, by rfl⟩ : syracuseStep 1516613 = 284365) (by norm_num)
theorem B2270285 : Blo 1008601 2270285 := bbase (se 3 (by rfl) ⟨425678, by rfl⟩ : syracuseStep 2270285 = 851357) (by norm_num)
theorem B3417173 : Blo 1008601 3417173 := bbase (se 8 (by rfl) ⟨20022, by rfl⟩ : syracuseStep 3417173 = 40045) (by norm_num)
theorem B1516637 : Blo 1008601 1516637 := bbase (se 3 (by rfl) ⟨284369, by rfl⟩ : syracuseStep 1516637 = 568739) (by norm_num)
theorem B1516661 : Blo 1008601 1516661 := bbase (se 5 (by rfl) ⟨71093, by rfl⟩ : syracuseStep 1516661 = 142187) (by norm_num)
theorem B1516685 : Blo 1008601 1516685 := bbase (se 3 (by rfl) ⟨284378, by rfl⟩ : syracuseStep 1516685 = 568757) (by norm_num)
theorem B2270357 : Blo 1008601 2270357 := bbase (se 6 (by rfl) ⟨53211, by rfl⟩ : syracuseStep 2270357 = 106423) (by norm_num)
theorem B1516709 : Blo 1008601 1516709 := bbase (se 4 (by rfl) ⟨142191, by rfl⟩ : syracuseStep 1516709 = 284383) (by norm_num)
theorem B2335925 : Blo 1008601 2335925 := bbase (se 5 (by rfl) ⟨109496, by rfl⟩ : syracuseStep 2335925 = 218993) (by norm_num)
theorem B1516733 : Blo 1008601 1516733 := bbase (se 3 (by rfl) ⟨284387, by rfl⟩ : syracuseStep 1516733 = 568775) (by norm_num)
theorem B1516757 : Blo 1008601 1516757 := bbase (se 7 (by rfl) ⟨17774, by rfl⟩ : syracuseStep 1516757 = 35549) (by norm_num)
theorem B2270429 : Blo 1008601 2270429 := bbase (se 3 (by rfl) ⟨425705, by rfl⟩ : syracuseStep 2270429 = 851411) (by norm_num)
theorem B1516781 : Blo 1008601 1516781 := bbase (se 3 (by rfl) ⟨284396, by rfl⟩ : syracuseStep 1516781 = 568793) (by norm_num)
theorem B2073853 : Blo 1008601 2073853 := bbase (se 3 (by rfl) ⟨388847, by rfl⟩ : syracuseStep 2073853 = 777695) (by norm_num)
theorem B1516805 : Blo 1008601 1516805 := bbase (se 4 (by rfl) ⟨142200, by rfl⟩ : syracuseStep 1516805 = 284401) (by norm_num)
theorem B1516829 : Blo 1008601 1516829 := bbase (se 3 (by rfl) ⟨284405, by rfl⟩ : syracuseStep 1516829 = 568811) (by norm_num)
theorem B2270501 : Blo 1008601 2270501 := bbase (se 4 (by rfl) ⟨212859, by rfl⟩ : syracuseStep 2270501 = 425719) (by norm_num)
theorem B1516853 : Blo 1008601 1516853 := bbase (se 5 (by rfl) ⟨71102, by rfl⟩ : syracuseStep 1516853 = 142205) (by norm_num)
theorem B1516877 : Blo 1008601 1516877 := bbase (se 3 (by rfl) ⟨284414, by rfl⟩ : syracuseStep 1516877 = 568829) (by norm_num)
theorem B1516901 : Blo 1008601 1516901 := bbase (se 4 (by rfl) ⟨142209, by rfl⟩ : syracuseStep 1516901 = 284419) (by norm_num)
theorem B2270573 : Blo 1008601 2270573 := bbase (se 3 (by rfl) ⟨425732, by rfl⟩ : syracuseStep 2270573 = 851465) (by norm_num)
theorem B1516925 : Blo 1008601 1516925 := bbase (se 3 (by rfl) ⟨284423, by rfl⟩ : syracuseStep 1516925 = 568847) (by norm_num)
theorem B1516949 : Blo 1008601 1516949 := bbase (se 6 (by rfl) ⟨35553, by rfl⟩ : syracuseStep 1516949 = 71107) (by norm_num)
theorem B1516973 : Blo 1008601 1516973 := bbase (se 3 (by rfl) ⟨284432, by rfl⟩ : syracuseStep 1516973 = 568865) (by norm_num)
theorem B2270645 : Blo 1008601 2270645 := bbase (se 5 (by rfl) ⟨106436, by rfl⟩ : syracuseStep 2270645 = 212873) (by norm_num)
theorem B1516997 : Blo 1008601 1516997 := bbase (se 4 (by rfl) ⟨142218, by rfl⟩ : syracuseStep 1516997 = 284437) (by norm_num)
theorem B1517021 : Blo 1008601 1517021 := bbase (se 3 (by rfl) ⟨284441, by rfl⟩ : syracuseStep 1517021 = 568883) (by norm_num)
theorem B1517045 : Blo 1008601 1517045 := bbase (se 5 (by rfl) ⟨71111, by rfl⟩ : syracuseStep 1517045 = 142223) (by norm_num)
theorem B6235637 : Blo 1008601 6235637 := bbase (se 5 (by rfl) ⟨292295, by rfl⟩ : syracuseStep 6235637 = 584591) (by norm_num)
theorem B2270717 : Blo 1008601 2270717 := bbase (se 3 (by rfl) ⟨425759, by rfl⟩ : syracuseStep 2270717 = 851519) (by norm_num)
theorem B1517069 : Blo 1008601 1517069 := bbase (se 3 (by rfl) ⟨284450, by rfl⟩ : syracuseStep 1517069 = 568901) (by norm_num)
theorem B1517093 : Blo 1008601 1517093 := bbase (se 4 (by rfl) ⟨142227, by rfl⟩ : syracuseStep 1517093 = 284455) (by norm_num)
theorem B1517117 : Blo 1008601 1517117 := bbase (se 3 (by rfl) ⟨284459, by rfl⟩ : syracuseStep 1517117 = 568919) (by norm_num)
theorem B2270789 : Blo 1008601 2270789 := bbase (se 4 (by rfl) ⟨212886, by rfl⟩ : syracuseStep 2270789 = 425773) (by norm_num)
theorem B1517141 : Blo 1008601 1517141 := bbase (se 8 (by rfl) ⟨8889, by rfl⟩ : syracuseStep 1517141 = 17779) (by norm_num)
theorem B1025629 : Blo 1008601 1025629 := bbase (se 3 (by rfl) ⟨192305, by rfl⟩ : syracuseStep 1025629 = 384611) (by norm_num)
theorem B1517165 : Blo 1008601 1517165 := bbase (se 3 (by rfl) ⟨284468, by rfl⟩ : syracuseStep 1517165 = 568937) (by norm_num)
theorem B1517189 : Blo 1008601 1517189 := bbase (se 4 (by rfl) ⟨142236, by rfl⟩ : syracuseStep 1517189 = 284473) (by norm_num)
theorem B2270861 : Blo 1008601 2270861 := bbase (se 3 (by rfl) ⟨425786, by rfl⟩ : syracuseStep 2270861 = 851573) (by norm_num)
theorem B1517213 : Blo 1008601 1517213 := bbase (se 3 (by rfl) ⟨284477, by rfl⟩ : syracuseStep 1517213 = 568955) (by norm_num)
theorem B1517237 : Blo 1008601 1517237 := bbase (se 5 (by rfl) ⟨71120, by rfl⟩ : syracuseStep 1517237 = 142241) (by norm_num)
theorem B1517261 : Blo 1008601 1517261 := bbase (se 3 (by rfl) ⟨284486, by rfl⟩ : syracuseStep 1517261 = 568973) (by norm_num)
theorem B2270933 : Blo 1008601 2270933 := bbase (se 7 (by rfl) ⟨26612, by rfl⟩ : syracuseStep 2270933 = 53225) (by norm_num)
theorem B1517285 : Blo 1008601 1517285 := bbase (se 4 (by rfl) ⟨142245, by rfl⟩ : syracuseStep 1517285 = 284491) (by norm_num)
theorem B8627957 : Blo 1008601 8627957 := bbase (se 5 (by rfl) ⟨404435, by rfl⟩ : syracuseStep 8627957 = 808871) (by norm_num)
theorem B1386229 : Blo 1008601 1386229 := bbase (se 5 (by rfl) ⟨64979, by rfl⟩ : syracuseStep 1386229 = 129959) (by norm_num)
theorem B1517309 : Blo 1008601 1517309 := bbase (se 3 (by rfl) ⟨284495, by rfl⟩ : syracuseStep 1517309 = 568991) (by norm_num)
theorem B1615621 : Blo 1008601 1615621 := bbase (se 4 (by rfl) ⟨151464, by rfl⟩ : syracuseStep 1615621 = 302929) (by norm_num)
theorem B1517333 : Blo 1008601 1517333 := bbase (se 6 (by rfl) ⟨35562, by rfl⟩ : syracuseStep 1517333 = 71125) (by norm_num)
theorem B2271005 : Blo 1008601 2271005 := bbase (se 3 (by rfl) ⟨425813, by rfl⟩ : syracuseStep 2271005 = 851627) (by norm_num)
theorem B1517357 : Blo 1008601 1517357 := bbase (se 3 (by rfl) ⟨284504, by rfl⟩ : syracuseStep 1517357 = 569009) (by norm_num)
theorem B2107181 : Blo 1008601 2107181 := bbase (se 3 (by rfl) ⟨395096, by rfl⟩ : syracuseStep 2107181 = 790193) (by norm_num)
theorem B1517381 : Blo 1008601 1517381 := bbase (se 4 (by rfl) ⟨142254, by rfl⟩ : syracuseStep 1517381 = 284509) (by norm_num)
theorem B1517405 : Blo 1008601 1517405 := bbase (se 3 (by rfl) ⟨284513, by rfl⟩ : syracuseStep 1517405 = 569027) (by norm_num)
theorem B2271077 : Blo 1008601 2271077 := bbase (se 4 (by rfl) ⟨212913, by rfl⟩ : syracuseStep 2271077 = 425827) (by norm_num)
theorem B1517429 : Blo 1008601 1517429 := bbase (se 5 (by rfl) ⟨71129, by rfl⟩ : syracuseStep 1517429 = 142259) (by norm_num)
theorem B2074493 : Blo 1008601 2074493 := bbase (se 3 (by rfl) ⟨388967, by rfl⟩ : syracuseStep 2074493 = 777935) (by norm_num)
theorem B1517453 : Blo 1008601 1517453 := bbase (se 3 (by rfl) ⟨284522, by rfl⟩ : syracuseStep 1517453 = 569045) (by norm_num)
theorem B1517477 : Blo 1008601 1517477 := bbase (se 4 (by rfl) ⟨142263, by rfl⟩ : syracuseStep 1517477 = 284527) (by norm_num)
theorem B2271149 : Blo 1008601 2271149 := bbase (se 3 (by rfl) ⟨425840, by rfl⟩ : syracuseStep 2271149 = 851681) (by norm_num)
theorem B1517501 : Blo 1008601 1517501 := bbase (se 3 (by rfl) ⟨284531, by rfl⟩ : syracuseStep 1517501 = 569063) (by norm_num)
theorem B1517525 : Blo 1008601 1517525 := bbase (se 7 (by rfl) ⟨17783, by rfl⟩ : syracuseStep 1517525 = 35567) (by norm_num)
theorem B1517549 : Blo 1008601 1517549 := bbase (se 3 (by rfl) ⟨284540, by rfl⟩ : syracuseStep 1517549 = 569081) (by norm_num)
theorem B2271221 : Blo 1008601 2271221 := bbase (se 5 (by rfl) ⟨106463, by rfl⟩ : syracuseStep 2271221 = 212927) (by norm_num)
theorem B1517573 : Blo 1008601 1517573 := bbase (se 4 (by rfl) ⟨142272, by rfl⟩ : syracuseStep 1517573 = 284545) (by norm_num)
theorem B1517597 : Blo 1008601 1517597 := bbase (se 3 (by rfl) ⟨284549, by rfl⟩ : syracuseStep 1517597 = 569099) (by norm_num)
theorem B2730037 : Blo 1008601 2730037 := bbase (se 5 (by rfl) ⟨127970, by rfl⟩ : syracuseStep 2730037 = 255941) (by norm_num)
theorem B1517621 : Blo 1008601 1517621 := bbase (se 5 (by rfl) ⟨71138, by rfl⟩ : syracuseStep 1517621 = 142277) (by norm_num)
theorem B2271293 : Blo 1008601 2271293 := bbase (se 3 (by rfl) ⟨425867, by rfl⟩ : syracuseStep 2271293 = 851735) (by norm_num)
theorem B1517645 : Blo 1008601 1517645 := bbase (se 3 (by rfl) ⟨284558, by rfl⟩ : syracuseStep 1517645 = 569117) (by norm_num)
theorem B13674581 : Blo 1008601 13674581 := bbase (se 8 (by rfl) ⟨80124, by rfl⟩ : syracuseStep 13674581 = 160249) (by norm_num)
theorem B1517669 : Blo 1008601 1517669 := bbase (se 4 (by rfl) ⟨142281, by rfl⟩ : syracuseStep 1517669 = 284563) (by norm_num)
theorem B1517693 : Blo 1008601 1517693 := bbase (se 3 (by rfl) ⟨284567, by rfl⟩ : syracuseStep 1517693 = 569135) (by norm_num)
theorem B2271365 : Blo 1008601 2271365 := bbase (se 4 (by rfl) ⟨212940, by rfl⟩ : syracuseStep 2271365 = 425881) (by norm_num)
theorem B1026193 : Blo 1008601 1026193 := bbase (se 2 (by rfl) ⟨384822, by rfl⟩ : syracuseStep 1026193 = 769645) (by norm_num)
theorem B1517717 : Blo 1008601 1517717 := bbase (se 6 (by rfl) ⟨35571, by rfl⟩ : syracuseStep 1517717 = 71143) (by norm_num)
theorem B3451045 : Blo 1008601 3451045 := bbase (se 4 (by rfl) ⟨323535, by rfl⟩ : syracuseStep 3451045 = 647071) (by norm_num)
theorem B1517741 : Blo 1008601 1517741 := bbase (se 3 (by rfl) ⟨284576, by rfl⟩ : syracuseStep 1517741 = 569153) (by norm_num)
theorem B1517765 : Blo 1008601 1517765 := bbase (se 4 (by rfl) ⟨142290, by rfl⟩ : syracuseStep 1517765 = 284581) (by norm_num)
theorem B2271437 : Blo 1008601 2271437 := bbase (se 3 (by rfl) ⟨425894, by rfl⟩ : syracuseStep 2271437 = 851789) (by norm_num)
theorem B1517789 : Blo 1008601 1517789 := bbase (se 3 (by rfl) ⟨284585, by rfl⟩ : syracuseStep 1517789 = 569171) (by norm_num)
theorem B5122277 : Blo 1008601 5122277 := bbase (se 4 (by rfl) ⟨480213, by rfl⟩ : syracuseStep 5122277 = 960427) (by norm_num)
theorem B1517813 : Blo 1008601 1517813 := bbase (se 5 (by rfl) ⟨71147, by rfl⟩ : syracuseStep 1517813 = 142295) (by norm_num)
theorem B1517837 : Blo 1008601 1517837 := bbase (se 3 (by rfl) ⟨284594, by rfl⟩ : syracuseStep 1517837 = 569189) (by norm_num)
theorem B2271509 : Blo 1008601 2271509 := bbase (se 6 (by rfl) ⟨53238, by rfl⟩ : syracuseStep 2271509 = 106477) (by norm_num)
theorem B1517861 : Blo 1008601 1517861 := bbase (se 4 (by rfl) ⟨142299, by rfl⟩ : syracuseStep 1517861 = 284599) (by norm_num)
theorem B1517885 : Blo 1008601 1517885 := bbase (se 3 (by rfl) ⟨284603, by rfl⟩ : syracuseStep 1517885 = 569207) (by norm_num)
theorem B1517909 : Blo 1008601 1517909 := bbase (se 10 (by rfl) ⟨2223, by rfl⟩ : syracuseStep 1517909 = 4447) (by norm_num)
theorem B2271581 : Blo 1008601 2271581 := bbase (se 3 (by rfl) ⟨425921, by rfl⟩ : syracuseStep 2271581 = 851843) (by norm_num)
theorem B1517933 : Blo 1008601 1517933 := bbase (se 3 (by rfl) ⟨284612, by rfl⟩ : syracuseStep 1517933 = 569225) (by norm_num)
theorem B1517957 : Blo 1008601 1517957 := bbase (se 4 (by rfl) ⟨142308, by rfl⟩ : syracuseStep 1517957 = 284617) (by norm_num)
theorem B1517981 : Blo 1008601 1517981 := bbase (se 3 (by rfl) ⟨284621, by rfl⟩ : syracuseStep 1517981 = 569243) (by norm_num)
theorem B2271653 : Blo 1008601 2271653 := bbase (se 4 (by rfl) ⟨212967, by rfl⟩ : syracuseStep 2271653 = 425935) (by norm_num)
theorem B1518005 : Blo 1008601 1518005 := bbase (se 5 (by rfl) ⟨71156, by rfl⟩ : syracuseStep 1518005 = 142313) (by norm_num)
theorem B2075069 : Blo 1008601 2075069 := bbase (se 3 (by rfl) ⟨389075, by rfl⟩ : syracuseStep 2075069 = 778151) (by norm_num)
theorem B1518029 : Blo 1008601 1518029 := bbase (se 3 (by rfl) ⟨284630, by rfl⟩ : syracuseStep 1518029 = 569261) (by norm_num)
theorem B1518053 : Blo 1008601 1518053 := bbase (se 4 (by rfl) ⟨142317, by rfl⟩ : syracuseStep 1518053 = 284635) (by norm_num)
theorem B2271725 : Blo 1008601 2271725 := bbase (se 3 (by rfl) ⟨425948, by rfl⟩ : syracuseStep 2271725 = 851897) (by norm_num)
theorem B1518077 : Blo 1008601 1518077 := bbase (se 3 (by rfl) ⟨284639, by rfl⟩ : syracuseStep 1518077 = 569279) (by norm_num)
theorem B1518101 : Blo 1008601 1518101 := bbase (se 6 (by rfl) ⟨35580, by rfl⟩ : syracuseStep 1518101 = 71161) (by norm_num)
theorem B1944101 : Blo 1008601 1944101 := bbase (se 4 (by rfl) ⟨182259, by rfl⟩ : syracuseStep 1944101 = 364519) (by norm_num)
theorem B3648037 : Blo 1008601 3648037 := bbase (se 4 (by rfl) ⟨342003, by rfl⟩ : syracuseStep 3648037 = 684007) (by norm_num)
theorem B1616429 : Blo 1008601 1616429 := bbase (se 3 (by rfl) ⟨303080, by rfl⟩ : syracuseStep 1616429 = 606161) (by norm_num)
theorem B1518125 : Blo 1008601 1518125 := bbase (se 3 (by rfl) ⟨284648, by rfl⟩ : syracuseStep 1518125 = 569297) (by norm_num)
theorem B2271797 : Blo 1008601 2271797 := bbase (se 5 (by rfl) ⟨106490, by rfl⟩ : syracuseStep 2271797 = 212981) (by norm_num)
theorem B1518149 : Blo 1008601 1518149 := bbase (se 4 (by rfl) ⟨142326, by rfl⟩ : syracuseStep 1518149 = 284653) (by norm_num)
theorem B1518173 : Blo 1008601 1518173 := bbase (se 3 (by rfl) ⟨284657, by rfl⟩ : syracuseStep 1518173 = 569315) (by norm_num)
theorem B1518197 : Blo 1008601 1518197 := bbase (se 5 (by rfl) ⟨71165, by rfl⟩ : syracuseStep 1518197 = 142331) (by norm_num)
theorem B2271869 : Blo 1008601 2271869 := bbase (se 3 (by rfl) ⟨425975, by rfl⟩ : syracuseStep 2271869 = 851951) (by norm_num)
theorem B1518221 : Blo 1008601 1518221 := bbase (se 3 (by rfl) ⟨284666, by rfl⟩ : syracuseStep 1518221 = 569333) (by norm_num)
theorem B1518245 : Blo 1008601 1518245 := bbase (se 4 (by rfl) ⟨142335, by rfl⟩ : syracuseStep 1518245 = 284671) (by norm_num)
theorem B1518269 : Blo 1008601 1518269 := bbase (se 3 (by rfl) ⟨284675, by rfl⟩ : syracuseStep 1518269 = 569351) (by norm_num)
theorem B2271941 : Blo 1008601 2271941 := bbase (se 4 (by rfl) ⟨212994, by rfl⟩ : syracuseStep 2271941 = 425989) (by norm_num)
theorem B38775509 : Blo 1008601 38775509 := bbase (se 7 (by rfl) ⟨454400, by rfl⟩ : syracuseStep 38775509 = 908801) (by norm_num)
theorem B1518293 : Blo 1008601 1518293 := bbase (se 7 (by rfl) ⟨17792, by rfl⟩ : syracuseStep 1518293 = 35585) (by norm_num)
theorem B2304749 : Blo 1008601 2304749 := bbase (se 3 (by rfl) ⟨432140, by rfl⟩ : syracuseStep 2304749 = 864281) (by norm_num)
theorem B1518317 : Blo 1008601 1518317 := bbase (se 3 (by rfl) ⟨284684, by rfl⟩ : syracuseStep 1518317 = 569369) (by norm_num)
theorem B1518341 : Blo 1008601 1518341 := bbase (se 4 (by rfl) ⟨142344, by rfl⟩ : syracuseStep 1518341 = 284689) (by norm_num)
theorem B2272013 : Blo 1008601 2272013 := bbase (se 3 (by rfl) ⟨426002, by rfl⟩ : syracuseStep 2272013 = 852005) (by norm_num)
theorem B1518365 : Blo 1008601 1518365 := bbase (se 3 (by rfl) ⟨284693, by rfl⟩ : syracuseStep 1518365 = 569387) (by norm_num)
theorem B1518389 : Blo 1008601 1518389 := bbase (se 5 (by rfl) ⟨71174, by rfl⟩ : syracuseStep 1518389 = 142349) (by norm_num)
theorem B1616717 : Blo 1008601 1616717 := bbase (se 3 (by rfl) ⟨303134, by rfl⟩ : syracuseStep 1616717 = 606269) (by norm_num)
theorem B1518413 : Blo 1008601 1518413 := bbase (se 3 (by rfl) ⟨284702, by rfl⟩ : syracuseStep 1518413 = 569405) (by norm_num)
theorem B7875413 : Blo 1008601 7875413 := bbase (se 9 (by rfl) ⟨23072, by rfl⟩ : syracuseStep 7875413 = 46145) (by norm_num)
theorem B2272085 : Blo 1008601 2272085 := bbase (se 9 (by rfl) ⟨6656, by rfl⟩ : syracuseStep 2272085 = 13313) (by norm_num)
theorem B1518437 : Blo 1008601 1518437 := bbase (se 4 (by rfl) ⟨142353, by rfl⟩ : syracuseStep 1518437 = 284707) (by norm_num)
theorem B1518461 : Blo 1008601 1518461 := bbase (se 3 (by rfl) ⟨284711, by rfl⟩ : syracuseStep 1518461 = 569423) (by norm_num)
theorem B1518485 : Blo 1008601 1518485 := bbase (se 6 (by rfl) ⟨35589, by rfl⟩ : syracuseStep 1518485 = 71179) (by norm_num)
theorem B2272157 : Blo 1008601 2272157 := bbase (se 3 (by rfl) ⟨426029, by rfl⟩ : syracuseStep 2272157 = 852059) (by norm_num)
theorem B1518509 : Blo 1008601 1518509 := bbase (se 3 (by rfl) ⟨284720, by rfl⟩ : syracuseStep 1518509 = 569441) (by norm_num)
theorem B1518533 : Blo 1008601 1518533 := bbase (se 4 (by rfl) ⟨142362, by rfl⟩ : syracuseStep 1518533 = 284725) (by norm_num)
theorem B1518557 : Blo 1008601 1518557 := bbase (se 3 (by rfl) ⟨284729, by rfl⟩ : syracuseStep 1518557 = 569459) (by norm_num)
theorem B2272229 : Blo 1008601 2272229 := bbase (se 4 (by rfl) ⟨213021, by rfl⟩ : syracuseStep 2272229 = 426043) (by norm_num)
theorem B4860917 : Blo 1008601 4860917 := bbase (se 5 (by rfl) ⟨227855, by rfl⟩ : syracuseStep 4860917 = 455711) (by norm_num)
theorem B1518581 : Blo 1008601 1518581 := bbase (se 5 (by rfl) ⟨71183, by rfl⟩ : syracuseStep 1518581 = 142367) (by norm_num)
theorem B1518605 : Blo 1008601 1518605 := bbase (se 3 (by rfl) ⟨284738, by rfl⟩ : syracuseStep 1518605 = 569477) (by norm_num)
theorem B1518629 : Blo 1008601 1518629 := bbase (se 4 (by rfl) ⟨142371, by rfl⟩ : syracuseStep 1518629 = 284743) (by norm_num)
theorem B2272301 : Blo 1008601 2272301 := bbase (se 3 (by rfl) ⟨426056, by rfl⟩ : syracuseStep 2272301 = 852113) (by norm_num)
theorem B1518653 : Blo 1008601 1518653 := bbase (se 3 (by rfl) ⟨284747, by rfl⟩ : syracuseStep 1518653 = 569495) (by norm_num)
theorem B1944661 : Blo 1008601 1944661 := bbase (se 8 (by rfl) ⟨11394, by rfl⟩ : syracuseStep 1944661 = 22789) (by norm_num)
theorem B1518677 : Blo 1008601 1518677 := bbase (se 8 (by rfl) ⟨8898, by rfl⟩ : syracuseStep 1518677 = 17797) (by norm_num)
theorem B1518701 : Blo 1008601 1518701 := bbase (se 3 (by rfl) ⟨284756, by rfl⟩ : syracuseStep 1518701 = 569513) (by norm_num)
theorem B2272373 : Blo 1008601 2272373 := bbase (se 5 (by rfl) ⟨106517, by rfl⟩ : syracuseStep 2272373 = 213035) (by norm_num)
theorem B1518725 : Blo 1008601 1518725 := bbase (se 4 (by rfl) ⟨142380, by rfl⟩ : syracuseStep 1518725 = 284761) (by norm_num)
theorem B1518749 : Blo 1008601 1518749 := bbase (se 3 (by rfl) ⟨284765, by rfl⟩ : syracuseStep 1518749 = 569531) (by norm_num)
theorem B1518773 : Blo 1008601 1518773 := bbase (se 5 (by rfl) ⟨71192, by rfl⟩ : syracuseStep 1518773 = 142385) (by norm_num)
theorem B2272445 : Blo 1008601 2272445 := bbase (se 3 (by rfl) ⟨426083, by rfl⟩ : syracuseStep 2272445 = 852167) (by norm_num)
theorem B2731205 : Blo 1008601 2731205 := bbase (se 4 (by rfl) ⟨256050, by rfl⟩ : syracuseStep 2731205 = 512101) (by norm_num)
theorem B1518797 : Blo 1008601 1518797 := bbase (se 3 (by rfl) ⟨284774, by rfl⟩ : syracuseStep 1518797 = 569549) (by norm_num)
theorem B1518821 : Blo 1008601 1518821 := bbase (se 4 (by rfl) ⟨142389, by rfl⟩ : syracuseStep 1518821 = 284779) (by norm_num)
theorem B1617133 : Blo 1008601 1617133 := bbase (se 3 (by rfl) ⟨303212, by rfl⟩ : syracuseStep 1617133 = 606425) (by norm_num)
theorem B1518845 : Blo 1008601 1518845 := bbase (se 3 (by rfl) ⟨284783, by rfl⟩ : syracuseStep 1518845 = 569567) (by norm_num)
theorem B2272517 : Blo 1008601 2272517 := bbase (se 4 (by rfl) ⟨213048, by rfl⟩ : syracuseStep 2272517 = 426097) (by norm_num)
theorem B1518869 : Blo 1008601 1518869 := bbase (se 6 (by rfl) ⟨35598, by rfl⟩ : syracuseStep 1518869 = 71197) (by norm_num)
theorem B1518893 : Blo 1008601 1518893 := bbase (se 3 (by rfl) ⟨284792, by rfl⟩ : syracuseStep 1518893 = 569585) (by norm_num)
theorem B7679285 : Blo 1008601 7679285 := bbase (se 5 (by rfl) ⟨359966, by rfl⟩ : syracuseStep 7679285 = 719933) (by norm_num)
theorem B2272589 : Blo 1008601 2272589 := bbase (se 3 (by rfl) ⟨426110, by rfl⟩ : syracuseStep 2272589 = 852221) (by norm_num)
theorem B2272661 : Blo 1008601 2272661 := bbase (se 6 (by rfl) ⟨53265, by rfl⟩ : syracuseStep 2272661 = 106531) (by norm_num)
theorem B2731445 : Blo 1008601 2731445 := bbase (se 5 (by rfl) ⟨128036, by rfl⟩ : syracuseStep 2731445 = 256073) (by norm_num)
theorem B3452357 : Blo 1008601 3452357 := bbase (se 4 (by rfl) ⟨323658, by rfl⟩ : syracuseStep 3452357 = 647317) (by norm_num)
theorem B2272733 : Blo 1008601 2272733 := bbase (se 3 (by rfl) ⟨426137, by rfl⟩ : syracuseStep 2272733 = 852275) (by norm_num)
theorem B5123573 : Blo 1008601 5123573 := bbase (se 5 (by rfl) ⟨240167, by rfl⟩ : syracuseStep 5123573 = 480335) (by norm_num)
theorem B1945109 : Blo 1008601 1945109 := bbase (se 6 (by rfl) ⟨45588, by rfl⟩ : syracuseStep 1945109 = 91177) (by norm_num)
theorem B2272805 : Blo 1008601 2272805 := bbase (se 4 (by rfl) ⟨213075, by rfl⟩ : syracuseStep 2272805 = 426151) (by norm_num)
theorem B10923605 : Blo 1008601 10923605 := bbase (se 8 (by rfl) ⟨64005, by rfl⟩ : syracuseStep 10923605 = 128011) (by norm_num)
theorem B2272877 : Blo 1008601 2272877 := bbase (se 3 (by rfl) ⟨426164, by rfl⟩ : syracuseStep 2272877 = 852329) (by norm_num)
theorem B2272949 : Blo 1008601 2272949 := bbase (se 5 (by rfl) ⟨106544, by rfl⟩ : syracuseStep 2272949 = 213089) (by norm_num)
theorem B2273021 : Blo 1008601 2273021 := bbase (se 3 (by rfl) ⟨426191, by rfl⟩ : syracuseStep 2273021 = 852383) (by norm_num)
theorem B2273093 : Blo 1008601 2273093 := bbase (se 4 (by rfl) ⟨213102, by rfl⟩ : syracuseStep 2273093 = 426205) (by norm_num)
theorem B2273165 : Blo 1008601 2273165 := bbase (se 3 (by rfl) ⟨426218, by rfl⟩ : syracuseStep 2273165 = 852437) (by norm_num)
theorem B2273237 : Blo 1008601 2273237 := bbase (se 7 (by rfl) ⟨26639, by rfl⟩ : syracuseStep 2273237 = 53279) (by norm_num)
theorem B2273309 : Blo 1008601 2273309 := bbase (se 3 (by rfl) ⟨426245, by rfl⟩ : syracuseStep 2273309 = 852491) (by norm_num)
theorem B2273381 : Blo 1008601 2273381 := bbase (se 4 (by rfl) ⟨213129, by rfl⟩ : syracuseStep 2273381 = 426259) (by norm_num)
theorem B1945709 : Blo 1008601 1945709 := bbase (se 3 (by rfl) ⟨364820, by rfl⟩ : syracuseStep 1945709 = 729641) (by norm_num)
theorem B1618069 : Blo 1008601 1618069 := bbase (se 6 (by rfl) ⟨37923, by rfl⟩ : syracuseStep 1618069 = 75847) (by norm_num)
theorem B2273453 : Blo 1008601 2273453 := bbase (se 3 (by rfl) ⟨426272, by rfl⟩ : syracuseStep 2273453 = 852545) (by norm_num)
theorem B2273525 : Blo 1008601 2273525 := bbase (se 5 (by rfl) ⟨106571, by rfl⟩ : syracuseStep 2273525 = 213143) (by norm_num)
theorem B2273597 : Blo 1008601 2273597 := bbase (se 3 (by rfl) ⟨426299, by rfl⟩ : syracuseStep 2273597 = 852599) (by norm_num)
theorem B2273669 : Blo 1008601 2273669 := bbase (se 4 (by rfl) ⟨213156, by rfl⟩ : syracuseStep 2273669 = 426313) (by norm_num)
theorem B7287221 : Blo 1008601 7287221 := bbase (se 5 (by rfl) ⟨341588, by rfl⟩ : syracuseStep 7287221 = 683177) (by norm_num)
theorem B2273741 : Blo 1008601 2273741 := bbase (se 3 (by rfl) ⟨426326, by rfl⟩ : syracuseStep 2273741 = 852653) (by norm_num)
theorem B2273813 : Blo 1008601 2273813 := bbase (se 6 (by rfl) ⟨53292, by rfl⟩ : syracuseStep 2273813 = 106585) (by norm_num)
theorem B2273885 : Blo 1008601 2273885 := bbase (se 3 (by rfl) ⟨426353, by rfl⟩ : syracuseStep 2273885 = 852707) (by norm_num)
theorem B2273957 : Blo 1008601 2273957 := bbase (se 4 (by rfl) ⟨213183, by rfl⟩ : syracuseStep 2273957 = 426367) (by norm_num)
theorem B1094357 : Blo 1008601 1094357 := bbase (se 7 (by rfl) ⟨12824, by rfl⟩ : syracuseStep 1094357 = 25649) (by norm_num)
theorem B2274029 : Blo 1008601 2274029 := bbase (se 3 (by rfl) ⟨426380, by rfl⟩ : syracuseStep 2274029 = 852761) (by norm_num)
theorem B5124869 : Blo 1008601 5124869 := bbase (se 4 (by rfl) ⟨480456, by rfl⟩ : syracuseStep 5124869 = 960913) (by norm_num)
theorem B2274101 : Blo 1008601 2274101 := bbase (se 5 (by rfl) ⟨106598, by rfl⟩ : syracuseStep 2274101 = 213197) (by norm_num)
theorem B2274173 : Blo 1008601 2274173 := bbase (se 3 (by rfl) ⟨426407, by rfl⟩ : syracuseStep 2274173 = 852815) (by norm_num)
theorem B2274245 : Blo 1008601 2274245 := bbase (se 4 (by rfl) ⟨213210, by rfl⟩ : syracuseStep 2274245 = 426421) (by norm_num)
theorem B2274317 : Blo 1008601 2274317 := bbase (se 3 (by rfl) ⟨426434, by rfl⟩ : syracuseStep 2274317 = 852869) (by norm_num)
theorem B2274389 : Blo 1008601 2274389 := bbase (se 8 (by rfl) ⟨13326, by rfl⟩ : syracuseStep 2274389 = 26653) (by norm_num)
theorem B2274461 : Blo 1008601 2274461 := bbase (se 3 (by rfl) ⟨426461, by rfl⟩ : syracuseStep 2274461 = 852923) (by norm_num)
theorem B7779509 : Blo 1008601 7779509 := bbase (se 5 (by rfl) ⟨364664, by rfl⟩ : syracuseStep 7779509 = 729329) (by norm_num)
theorem B2274533 : Blo 1008601 2274533 := bbase (se 4 (by rfl) ⟨213237, by rfl⟩ : syracuseStep 2274533 = 426475) (by norm_num)
theorem B2274605 : Blo 1008601 2274605 := bbase (se 3 (by rfl) ⟨426488, by rfl⟩ : syracuseStep 2274605 = 852977) (by norm_num)
theorem B1946933 : Blo 1008601 1946933 := bbase (se 5 (by rfl) ⟨91262, by rfl⟩ : syracuseStep 1946933 = 182525) (by norm_num)
theorem B1619261 : Blo 1008601 1619261 := bbase (se 3 (by rfl) ⟨303611, by rfl⟩ : syracuseStep 1619261 = 607223) (by norm_num)
theorem B2274677 : Blo 1008601 2274677 := bbase (se 5 (by rfl) ⟨106625, by rfl⟩ : syracuseStep 2274677 = 213251) (by norm_num)
theorem B2274749 : Blo 1008601 2274749 := bbase (se 3 (by rfl) ⟨426515, by rfl⟩ : syracuseStep 2274749 = 853031) (by norm_num)
theorem B1619453 : Blo 1008601 1619453 := bbase (se 3 (by rfl) ⟨303647, by rfl⟩ : syracuseStep 1619453 = 607295) (by norm_num)
theorem B2274821 : Blo 1008601 2274821 := bbase (se 4 (by rfl) ⟨213264, by rfl⟩ : syracuseStep 2274821 = 426529) (by norm_num)
theorem B2274893 : Blo 1008601 2274893 := bbase (se 3 (by rfl) ⟨426542, by rfl⟩ : syracuseStep 2274893 = 853085) (by norm_num)
theorem B2274965 : Blo 1008601 2274965 := bbase (se 6 (by rfl) ⟨53319, by rfl⟩ : syracuseStep 2274965 = 106639) (by norm_num)
theorem B4863701 : Blo 1008601 4863701 := bbase (se 7 (by rfl) ⟨56996, by rfl⟩ : syracuseStep 4863701 = 113993) (by norm_num)
theorem B2275037 : Blo 1008601 2275037 := bbase (se 3 (by rfl) ⟨426569, by rfl⟩ : syracuseStep 2275037 = 853139) (by norm_num)
theorem B8206069 : Blo 1008601 8206069 := bbase (se 5 (by rfl) ⟨384659, by rfl⟩ : syracuseStep 8206069 = 769319) (by norm_num)
theorem B1095449 : Blo 1008601 1095449 := bbase (se 2 (by rfl) ⟨410793, by rfl⟩ : syracuseStep 1095449 = 821587) (by norm_num)
theorem B2275109 : Blo 1008601 2275109 := bbase (se 4 (by rfl) ⟨213291, by rfl⟩ : syracuseStep 2275109 = 426583) (by norm_num)
theorem B1947493 : Blo 1008601 1947493 := bbase (se 4 (by rfl) ⟨182577, by rfl⟩ : syracuseStep 1947493 = 365155) (by norm_num)
theorem B2275181 : Blo 1008601 2275181 := bbase (se 3 (by rfl) ⟨426596, by rfl⟩ : syracuseStep 2275181 = 853193) (by norm_num)
theorem B4437925 : Blo 1008601 4437925 := bbase (se 4 (by rfl) ⟨416055, by rfl⟩ : syracuseStep 4437925 = 832111) (by norm_num)
theorem B2275253 : Blo 1008601 2275253 := bbase (se 5 (by rfl) ⟨106652, by rfl⟩ : syracuseStep 2275253 = 213305) (by norm_num)
theorem B2275325 : Blo 1008601 2275325 := bbase (se 3 (by rfl) ⟨426623, by rfl⟩ : syracuseStep 2275325 = 853247) (by norm_num)
theorem B5126165 : Blo 1008601 5126165 := bbase (se 6 (by rfl) ⟨120144, by rfl⟩ : syracuseStep 5126165 = 240289) (by norm_num)
theorem B2668589 : Blo 1008601 2668589 := bbase (se 3 (by rfl) ⟨500360, by rfl⟩ : syracuseStep 2668589 = 1000721) (by norm_num)
theorem B2275397 : Blo 1008601 2275397 := bbase (se 4 (by rfl) ⟨213318, by rfl⟩ : syracuseStep 2275397 = 426637) (by norm_num)
theorem B1095773 : Blo 1008601 1095773 := bbase (se 3 (by rfl) ⟨205457, by rfl⟩ : syracuseStep 1095773 = 410915) (by norm_num)
theorem B2046053 : Blo 1008601 2046053 := bbase (se 4 (by rfl) ⟨191817, by rfl⟩ : syracuseStep 2046053 = 383635) (by norm_num)
theorem B2275469 : Blo 1008601 2275469 := bbase (se 3 (by rfl) ⟨426650, by rfl⟩ : syracuseStep 2275469 = 853301) (by norm_num)
theorem B2275541 : Blo 1008601 2275541 := bbase (se 7 (by rfl) ⟨26666, by rfl⟩ : syracuseStep 2275541 = 53333) (by norm_num)
theorem B2275613 : Blo 1008601 2275613 := bbase (se 3 (by rfl) ⟨426677, by rfl⟩ : syracuseStep 2275613 = 853355) (by norm_num)
theorem B2275685 : Blo 1008601 2275685 := bbase (se 4 (by rfl) ⟨213345, by rfl⟩ : syracuseStep 2275685 = 426691) (by norm_num)
theorem B2275757 : Blo 1008601 2275757 := bbase (se 3 (by rfl) ⟨426704, by rfl⟩ : syracuseStep 2275757 = 853409) (by norm_num)
theorem B2308541 : Blo 1008601 2308541 := bbase (se 3 (by rfl) ⟨432851, by rfl⟩ : syracuseStep 2308541 = 865703) (by norm_num)
theorem B2275829 : Blo 1008601 2275829 := bbase (se 5 (by rfl) ⟨106679, by rfl⟩ : syracuseStep 2275829 = 213359) (by norm_num)
theorem B2275901 : Blo 1008601 2275901 := bbase (se 3 (by rfl) ⟨426731, by rfl⟩ : syracuseStep 2275901 = 853463) (by norm_num)
theorem B1915501 : Blo 1008601 1915501 := bbase (se 3 (by rfl) ⟨359156, by rfl⟩ : syracuseStep 1915501 = 718313) (by norm_num)
theorem B2275973 : Blo 1008601 2275973 := bbase (se 4 (by rfl) ⟨213372, by rfl⟩ : syracuseStep 2275973 = 426745) (by norm_num)
theorem B2276045 : Blo 1008601 2276045 := bbase (se 3 (by rfl) ⟨426758, by rfl⟩ : syracuseStep 2276045 = 853517) (by norm_num)
theorem B27605717 : Blo 1008601 27605717 := bbase (se 7 (by rfl) ⟨323504, by rfl⟩ : syracuseStep 27605717 = 647009) (by norm_num)
theorem B1915645 : Blo 1008601 1915645 := bbase (se 3 (by rfl) ⟨359183, by rfl⟩ : syracuseStep 1915645 = 718367) (by norm_num)
theorem B2276117 : Blo 1008601 2276117 := bbase (se 6 (by rfl) ⟨53346, by rfl⟩ : syracuseStep 2276117 = 106693) (by norm_num)
theorem B2276189 : Blo 1008601 2276189 := bbase (se 3 (by rfl) ⟨426785, by rfl⟩ : syracuseStep 2276189 = 853571) (by norm_num)
theorem B1915805 : Blo 1008601 1915805 := bbase (se 3 (by rfl) ⟨359213, by rfl⟩ : syracuseStep 1915805 = 718427) (by norm_num)
theorem B2276261 : Blo 1008601 2276261 := bbase (se 4 (by rfl) ⟨213399, by rfl⟩ : syracuseStep 2276261 = 426799) (by norm_num)
theorem B1620901 : Blo 1008601 1620901 := bbase (se 4 (by rfl) ⟨151959, by rfl⟩ : syracuseStep 1620901 = 303919) (by norm_num)
theorem B2276333 : Blo 1008601 2276333 := bbase (se 3 (by rfl) ⟨426812, by rfl⟩ : syracuseStep 2276333 = 853625) (by norm_num)
theorem B1915949 : Blo 1008601 1915949 := bbase (se 3 (by rfl) ⟨359240, by rfl⟩ : syracuseStep 1915949 = 718481) (by norm_num)
theorem B2276405 : Blo 1008601 2276405 := bbase (se 5 (by rfl) ⟨106706, by rfl⟩ : syracuseStep 2276405 = 213413) (by norm_num)
theorem B4602997 : Blo 1008601 4602997 := bbase (se 5 (by rfl) ⟨215765, by rfl⟩ : syracuseStep 4602997 = 431531) (by norm_num)
theorem B2276477 : Blo 1008601 2276477 := bbase (se 3 (by rfl) ⟨426839, by rfl⟩ : syracuseStep 2276477 = 853679) (by norm_num)
theorem B2276549 : Blo 1008601 2276549 := bbase (se 4 (by rfl) ⟨213426, by rfl⟩ : syracuseStep 2276549 = 426853) (by norm_num)
theorem B2276621 : Blo 1008601 2276621 := bbase (se 3 (by rfl) ⟨426866, by rfl⟩ : syracuseStep 2276621 = 853733) (by norm_num)
theorem B1817885 : Blo 1008601 1817885 := bbase (se 3 (by rfl) ⟨340853, by rfl⟩ : syracuseStep 1817885 = 681707) (by norm_num)
theorem B1916237 : Blo 1008601 1916237 := bbase (se 3 (by rfl) ⟨359294, by rfl⟩ : syracuseStep 1916237 = 718589) (by norm_num)
theorem B2276693 : Blo 1008601 2276693 := bbase (se 11 (by rfl) ⟨1667, by rfl⟩ : syracuseStep 2276693 = 3335) (by norm_num)
theorem B2735477 : Blo 1008601 2735477 := bbase (se 5 (by rfl) ⟨128225, by rfl⟩ : syracuseStep 2735477 = 256451) (by norm_num)
theorem B2276765 : Blo 1008601 2276765 := bbase (se 3 (by rfl) ⟨426893, by rfl⟩ : syracuseStep 2276765 = 853787) (by norm_num)
theorem B1916389 : Blo 1008601 1916389 := bbase (se 4 (by rfl) ⟨179661, by rfl⟩ : syracuseStep 1916389 = 359323) (by norm_num)
theorem B2276837 : Blo 1008601 2276837 := bbase (se 4 (by rfl) ⟨213453, by rfl⟩ : syracuseStep 2276837 = 426907) (by norm_num)
theorem B5750261 : Blo 1008601 5750261 := bbase (se 5 (by rfl) ⟨269543, by rfl⟩ : syracuseStep 5750261 = 539087) (by norm_num)
theorem B4439573 : Blo 1008601 4439573 := bbase (se 6 (by rfl) ⟨104052, by rfl⟩ : syracuseStep 4439573 = 208105) (by norm_num)
theorem B2276909 : Blo 1008601 2276909 := bbase (se 3 (by rfl) ⟨426920, by rfl⟩ : syracuseStep 2276909 = 853841) (by norm_num)
theorem B2276981 : Blo 1008601 2276981 := bbase (se 5 (by rfl) ⟨106733, by rfl⟩ : syracuseStep 2276981 = 213467) (by norm_num)
theorem B2277053 : Blo 1008601 2277053 := bbase (se 3 (by rfl) ⟨426947, by rfl⟩ : syracuseStep 2277053 = 853895) (by norm_num)
theorem B2277125 : Blo 1008601 2277125 := bbase (se 4 (by rfl) ⟨213480, by rfl⟩ : syracuseStep 2277125 = 426961) (by norm_num)
theorem B1916693 : Blo 1008601 1916693 := bbase (se 6 (by rfl) ⟨44922, by rfl⟩ : syracuseStep 1916693 = 89845) (by norm_num)
theorem B1457941 : Blo 1008601 1457941 := bbase (se 6 (by rfl) ⟨34170, by rfl⟩ : syracuseStep 1457941 = 68341) (by norm_num)
theorem B2277197 : Blo 1008601 2277197 := bbase (se 3 (by rfl) ⟨426974, by rfl⟩ : syracuseStep 2277197 = 853949) (by norm_num)
theorem B4308869 : Blo 1008601 4308869 := bbase (se 4 (by rfl) ⟨403956, by rfl⟩ : syracuseStep 4308869 = 807913) (by norm_num)
theorem B2277269 : Blo 1008601 2277269 := bbase (se 6 (by rfl) ⟨53373, by rfl⟩ : syracuseStep 2277269 = 106747) (by norm_num)
theorem B2277341 : Blo 1008601 2277341 := bbase (se 3 (by rfl) ⟨427001, by rfl⟩ : syracuseStep 2277341 = 854003) (by norm_num)
theorem B2277413 : Blo 1008601 2277413 := bbase (se 4 (by rfl) ⟨213507, by rfl⟩ : syracuseStep 2277413 = 427015) (by norm_num)
theorem B3457093 : Blo 1008601 3457093 := bbase (se 4 (by rfl) ⟨324102, by rfl⟩ : syracuseStep 3457093 = 648205) (by norm_num)
theorem B2277485 : Blo 1008601 2277485 := bbase (se 3 (by rfl) ⟨427028, by rfl⟩ : syracuseStep 2277485 = 854057) (by norm_num)
theorem B4309109 : Blo 1008601 4309109 := bbase (se 5 (by rfl) ⟨201989, by rfl⟩ : syracuseStep 4309109 = 403979) (by norm_num)
theorem B2277557 : Blo 1008601 2277557 := bbase (se 5 (by rfl) ⟨106760, by rfl⟩ : syracuseStep 2277557 = 213521) (by norm_num)
theorem B2277629 : Blo 1008601 2277629 := bbase (se 3 (by rfl) ⟨427055, by rfl⟩ : syracuseStep 2277629 = 854111) (by norm_num)
theorem B9716021 : Blo 1008601 9716021 := bbase (se 5 (by rfl) ⟨455438, by rfl⟩ : syracuseStep 9716021 = 910877) (by norm_num)
theorem B2736437 : Blo 1008601 2736437 := bbase (se 5 (by rfl) ⟨128270, by rfl⟩ : syracuseStep 2736437 = 256541) (by norm_num)
theorem B2277701 : Blo 1008601 2277701 := bbase (se 4 (by rfl) ⟨213534, by rfl⟩ : syracuseStep 2277701 = 427069) (by norm_num)
theorem B2277773 : Blo 1008601 2277773 := bbase (se 3 (by rfl) ⟨427082, by rfl⟩ : syracuseStep 2277773 = 854165) (by norm_num)
theorem B1458589 : Blo 1008601 1458589 := bbase (se 3 (by rfl) ⟨273485, by rfl⟩ : syracuseStep 1458589 = 546971) (by norm_num)
theorem B2277845 : Blo 1008601 2277845 := bbase (se 7 (by rfl) ⟨26693, by rfl⟩ : syracuseStep 2277845 = 53387) (by norm_num)
theorem B1917445 : Blo 1008601 1917445 := bbase (se 4 (by rfl) ⟨179760, by rfl⟩ : syracuseStep 1917445 = 359521) (by norm_num)
theorem B2277917 : Blo 1008601 2277917 := bbase (se 3 (by rfl) ⟨427109, by rfl⟩ : syracuseStep 2277917 = 854219) (by norm_num)
theorem B1819189 : Blo 1008601 1819189 := bbase (se 5 (by rfl) ⟨85274, by rfl⟩ : syracuseStep 1819189 = 170549) (by norm_num)
theorem B2277989 : Blo 1008601 2277989 := bbase (se 4 (by rfl) ⟨213561, by rfl⟩ : syracuseStep 2277989 = 427123) (by norm_num)
theorem B5751445 : Blo 1008601 5751445 := bbase (se 6 (by rfl) ⟨134799, by rfl⟩ : syracuseStep 5751445 = 269599) (by norm_num)
theorem B1917589 : Blo 1008601 1917589 := bbase (se 6 (by rfl) ⟨44943, by rfl⟩ : syracuseStep 1917589 = 89887) (by norm_num)
theorem B2278061 : Blo 1008601 2278061 := bbase (se 3 (by rfl) ⟨427136, by rfl⟩ : syracuseStep 2278061 = 854273) (by norm_num)
theorem B2769653 : Blo 1008601 2769653 := bbase (se 5 (by rfl) ⟨129827, by rfl⟩ : syracuseStep 2769653 = 259655) (by norm_num)
theorem B2278133 : Blo 1008601 2278133 := bbase (se 5 (by rfl) ⟨106787, by rfl⟩ : syracuseStep 2278133 = 213575) (by norm_num)
theorem B20726549 : Blo 1008601 20726549 := bbase (se 6 (by rfl) ⟨485778, by rfl⟩ : syracuseStep 20726549 = 971557) (by norm_num)
theorem B1917749 : Blo 1008601 1917749 := bbase (se 5 (by rfl) ⟨89894, by rfl⟩ : syracuseStep 1917749 = 179789) (by norm_num)
theorem B2278205 : Blo 1008601 2278205 := bbase (se 3 (by rfl) ⟨427163, by rfl⟩ : syracuseStep 2278205 = 854327) (by norm_num)
theorem B2278277 : Blo 1008601 2278277 := bbase (se 4 (by rfl) ⟨213588, by rfl⟩ : syracuseStep 2278277 = 427177) (by norm_num)
theorem B1917893 : Blo 1008601 1917893 := bbase (se 4 (by rfl) ⟨179802, by rfl⟩ : syracuseStep 1917893 = 359605) (by norm_num)
theorem B2278349 : Blo 1008601 2278349 := bbase (se 3 (by rfl) ⟨427190, by rfl⟩ : syracuseStep 2278349 = 854381) (by norm_num)
theorem B2245853 : Blo 1008601 2245853 := bbase (se 3 (by rfl) ⟨421097, by rfl⟩ : syracuseStep 2245853 = 842195) (by norm_num)
theorem B1918181 : Blo 1008601 1918181 := bbase (se 4 (by rfl) ⟨179829, by rfl⟩ : syracuseStep 1918181 = 359659) (by norm_num)
theorem B1557733 : Blo 1008601 1557733 := bbase (se 4 (by rfl) ⟨146037, by rfl⟩ : syracuseStep 1557733 = 292075) (by norm_num)
theorem B1819909 : Blo 1008601 1819909 := bbase (se 4 (by rfl) ⟨170616, by rfl⟩ : syracuseStep 1819909 = 341233) (by norm_num)
theorem B1918333 : Blo 1008601 1918333 := bbase (se 3 (by rfl) ⟨359687, by rfl⟩ : syracuseStep 1918333 = 719375) (by norm_num)
theorem B1918637 : Blo 1008601 1918637 := bbase (se 3 (by rfl) ⟨359744, by rfl⟩ : syracuseStep 1918637 = 719489) (by norm_num)
theorem B6473429 : Blo 1008601 6473429 := bbase (se 7 (by rfl) ⟨75860, by rfl⟩ : syracuseStep 6473429 = 151721) (by norm_num)
theorem B1820573 : Blo 1008601 1820573 := bbase (se 3 (by rfl) ⟨341357, by rfl⟩ : syracuseStep 1820573 = 682715) (by norm_num)
theorem B4605989 : Blo 1008601 4605989 := bbase (se 4 (by rfl) ⟨431811, by rfl⟩ : syracuseStep 4605989 = 863623) (by norm_num)
theorem B1558669 : Blo 1008601 1558669 := bbase (se 3 (by rfl) ⟨292250, by rfl⟩ : syracuseStep 1558669 = 584501) (by norm_num)
theorem B7293077 : Blo 1008601 7293077 := bbase (se 6 (by rfl) ⟨170931, by rfl⟩ : syracuseStep 7293077 = 341863) (by norm_num)
theorem B4311397 : Blo 1008601 4311397 := bbase (se 4 (by rfl) ⟨404193, by rfl⟩ : syracuseStep 4311397 = 808387) (by norm_num)
theorem B5196149 : Blo 1008601 5196149 := bbase (se 5 (by rfl) ⟨243569, by rfl⟩ : syracuseStep 5196149 = 487139) (by norm_num)
theorem B1919389 : Blo 1008601 1919389 := bbase (se 3 (by rfl) ⟨359885, by rfl⟩ : syracuseStep 1919389 = 719771) (by norm_num)
theorem B1296821 : Blo 1008601 1296821 := bbase (se 5 (by rfl) ⟨60788, by rfl⟩ : syracuseStep 1296821 = 121577) (by norm_num)
theorem B20761109 : Blo 1008601 20761109 := bbase (se 6 (by rfl) ⟨486588, by rfl⟩ : syracuseStep 20761109 = 973177) (by norm_num)
theorem B1296929 : Blo 1008601 1296929 := bbase (se 2 (by rfl) ⟨486348, by rfl⟩ : syracuseStep 1296929 = 972697) (by norm_num)
theorem B1919533 : Blo 1008601 1919533 := bbase (se 3 (by rfl) ⟨359912, by rfl⟩ : syracuseStep 1919533 = 719825) (by norm_num)
theorem B5753429 : Blo 1008601 5753429 := bbase (se 8 (by rfl) ⟨33711, by rfl⟩ : syracuseStep 5753429 = 67423) (by norm_num)
theorem B1919693 : Blo 1008601 1919693 := bbase (se 3 (by rfl) ⟨359942, by rfl⟩ : syracuseStep 1919693 = 719885) (by norm_num)
theorem B7785173 : Blo 1008601 7785173 := bbase (se 7 (by rfl) ⟨91232, by rfl⟩ : syracuseStep 7785173 = 182465) (by norm_num)
theorem B1919837 : Blo 1008601 1919837 := bbase (se 3 (by rfl) ⟨359969, by rfl⟩ : syracuseStep 1919837 = 719939) (by norm_num)
theorem B2804597 : Blo 1008601 2804597 := bbase (se 5 (by rfl) ⟨131465, by rfl⟩ : syracuseStep 2804597 = 262931) (by norm_num)
theorem B7687061 : Blo 1008601 7687061 := bbase (se 6 (by rfl) ⟨180165, by rfl⟩ : syracuseStep 7687061 = 360331) (by norm_num)
theorem B1920125 : Blo 1008601 1920125 := bbase (se 3 (by rfl) ⟨360023, by rfl⟩ : syracuseStep 1920125 = 720047) (by norm_num)
theorem B3067109 : Blo 1008601 3067109 := bbase (se 4 (by rfl) ⟨287541, by rfl⟩ : syracuseStep 3067109 = 575083) (by norm_num)
theorem B1920277 : Blo 1008601 1920277 := bbase (se 6 (by rfl) ⟨45006, by rfl⟩ : syracuseStep 1920277 = 90013) (by norm_num)
theorem B1297981 : Blo 1008601 1297981 := bbase (se 3 (by rfl) ⟨243371, by rfl⟩ : syracuseStep 1297981 = 486743) (by norm_num)
theorem B1920581 : Blo 1008601 1920581 := bbase (se 4 (by rfl) ⟨180054, by rfl⟩ : syracuseStep 1920581 = 360109) (by norm_num)
theorem B4312885 : Blo 1008601 4312885 := bbase (se 5 (by rfl) ⟨202166, by rfl⟩ : syracuseStep 4312885 = 404333) (by norm_num)
theorem B4312901 : Blo 1008601 4312901 := bbase (se 4 (by rfl) ⟨404334, by rfl⟩ : syracuseStep 4312901 = 808669) (by norm_num)
theorem B3231589 : Blo 1008601 3231589 := bbase (se 4 (by rfl) ⟨302961, by rfl⟩ : syracuseStep 3231589 = 605923) (by norm_num)
theorem B1560421 : Blo 1008601 1560421 := bbase (se 4 (by rfl) ⟨146289, by rfl⟩ : syracuseStep 1560421 = 292579) (by norm_num)
theorem B1134697 : Blo 1008601 1134697 := bbase (se 2 (by rfl) ⟨425511, by rfl⟩ : syracuseStep 1134697 = 851023) (by norm_num)
theorem B1134733 : Blo 1008601 1134733 := bbase (se 3 (by rfl) ⟨212762, by rfl⟩ : syracuseStep 1134733 = 425525) (by norm_num)
theorem B1134769 : Blo 1008601 1134769 := bbase (se 2 (by rfl) ⟨425538, by rfl⟩ : syracuseStep 1134769 = 851077) (by norm_num)
theorem B1134805 : Blo 1008601 1134805 := bbase (se 7 (by rfl) ⟨13298, by rfl⟩ : syracuseStep 1134805 = 26597) (by norm_num)
theorem B1134841 : Blo 1008601 1134841 := bbase (se 2 (by rfl) ⟨425565, by rfl⟩ : syracuseStep 1134841 = 851131) (by norm_num)
theorem B1822981 : Blo 1008601 1822981 := bbase (se 4 (by rfl) ⟨170904, by rfl⟩ : syracuseStep 1822981 = 341809) (by norm_num)
theorem B1134877 : Blo 1008601 1134877 := bbase (se 3 (by rfl) ⟨212789, by rfl⟩ : syracuseStep 1134877 = 425579) (by norm_num)
theorem B3232037 : Blo 1008601 3232037 := bbase (se 4 (by rfl) ⟨303003, by rfl⟩ : syracuseStep 3232037 = 606007) (by norm_num)
theorem B1921333 : Blo 1008601 1921333 := bbase (se 5 (by rfl) ⟨90062, by rfl⟩ : syracuseStep 1921333 = 180125) (by norm_num)
theorem B1134913 : Blo 1008601 1134913 := bbase (se 2 (by rfl) ⟨425592, by rfl⟩ : syracuseStep 1134913 = 851185) (by norm_num)
theorem B1134949 : Blo 1008601 1134949 := bbase (se 4 (by rfl) ⟨106401, by rfl⟩ : syracuseStep 1134949 = 212803) (by norm_num)
theorem B3887461 : Blo 1008601 3887461 := bbase (se 4 (by rfl) ⟨364449, by rfl⟩ : syracuseStep 3887461 = 728899) (by norm_num)
theorem B1134985 : Blo 1008601 1134985 := bbase (se 2 (by rfl) ⟨425619, by rfl⟩ : syracuseStep 1134985 = 851239) (by norm_num)
theorem B1135021 : Blo 1008601 1135021 := bbase (se 3 (by rfl) ⟨212816, by rfl⟩ : syracuseStep 1135021 = 425633) (by norm_num)
theorem B1364413 : Blo 1008601 1364413 := bbase (se 3 (by rfl) ⟨255827, by rfl⟩ : syracuseStep 1364413 = 511655) (by norm_num)
theorem B1921477 : Blo 1008601 1921477 := bbase (se 4 (by rfl) ⟨180138, by rfl⟩ : syracuseStep 1921477 = 360277) (by norm_num)
theorem B1135057 : Blo 1008601 1135057 := bbase (se 2 (by rfl) ⟨425646, by rfl⟩ : syracuseStep 1135057 = 851293) (by norm_num)
theorem B1135093 : Blo 1008601 1135093 := bbase (se 5 (by rfl) ⟨53207, by rfl⟩ : syracuseStep 1135093 = 106415) (by norm_num)
theorem B1135129 : Blo 1008601 1135129 := bbase (se 2 (by rfl) ⟨425673, by rfl⟩ : syracuseStep 1135129 = 851347) (by norm_num)
theorem B1135165 : Blo 1008601 1135165 := bbase (se 3 (by rfl) ⟨212843, by rfl⟩ : syracuseStep 1135165 = 425687) (by norm_num)
theorem B1135201 : Blo 1008601 1135201 := bbase (se 2 (by rfl) ⟨425700, by rfl⟩ : syracuseStep 1135201 = 851401) (by norm_num)
theorem B1921637 : Blo 1008601 1921637 := bbase (se 4 (by rfl) ⟨180153, by rfl⟩ : syracuseStep 1921637 = 360307) (by norm_num)
theorem B1135237 : Blo 1008601 1135237 := bbase (se 4 (by rfl) ⟨106428, by rfl⟩ : syracuseStep 1135237 = 212857) (by norm_num)
theorem B1135273 : Blo 1008601 1135273 := bbase (se 2 (by rfl) ⟨425727, by rfl⟩ : syracuseStep 1135273 = 851455) (by norm_num)
theorem B1036973 : Blo 1008601 1036973 := bbase (se 3 (by rfl) ⟨194432, by rfl⟩ : syracuseStep 1036973 = 388865) (by norm_num)
theorem B1135309 : Blo 1008601 1135309 := bbase (se 3 (by rfl) ⟨212870, by rfl⟩ : syracuseStep 1135309 = 425741) (by norm_num)
theorem B1135345 : Blo 1008601 1135345 := bbase (se 2 (by rfl) ⟨425754, by rfl⟩ : syracuseStep 1135345 = 851509) (by norm_num)
theorem B5755637 : Blo 1008601 5755637 := bbase (se 5 (by rfl) ⟨269795, by rfl⟩ : syracuseStep 5755637 = 539591) (by norm_num)
theorem B1921781 : Blo 1008601 1921781 := bbase (se 5 (by rfl) ⟨90083, by rfl⟩ : syracuseStep 1921781 = 180167) (by norm_num)
theorem B1823485 : Blo 1008601 1823485 := bbase (se 3 (by rfl) ⟨341903, by rfl⟩ : syracuseStep 1823485 = 683807) (by norm_num)
theorem B1135381 : Blo 1008601 1135381 := bbase (se 6 (by rfl) ⟨26610, by rfl⟩ : syracuseStep 1135381 = 53221) (by norm_num)
theorem B1135417 : Blo 1008601 1135417 := bbase (se 2 (by rfl) ⟨425781, by rfl⟩ : syracuseStep 1135417 = 851563) (by norm_num)
theorem B1135453 : Blo 1008601 1135453 := bbase (se 3 (by rfl) ⟨212897, by rfl⟩ : syracuseStep 1135453 = 425795) (by norm_num)
theorem B1135489 : Blo 1008601 1135489 := bbase (se 2 (by rfl) ⟨425808, by rfl⟩ : syracuseStep 1135489 = 851617) (by norm_num)
theorem B1135525 : Blo 1008601 1135525 := bbase (se 4 (by rfl) ⟨106455, by rfl⟩ : syracuseStep 1135525 = 212911) (by norm_num)
theorem B1135561 : Blo 1008601 1135561 := bbase (se 2 (by rfl) ⟨425835, by rfl⟩ : syracuseStep 1135561 = 851671) (by norm_num)
theorem B1135597 : Blo 1008601 1135597 := bbase (se 3 (by rfl) ⟨212924, by rfl⟩ : syracuseStep 1135597 = 425849) (by norm_num)
theorem B1135633 : Blo 1008601 1135633 := bbase (se 2 (by rfl) ⟨425862, by rfl⟩ : syracuseStep 1135633 = 851725) (by norm_num)
theorem B1922069 : Blo 1008601 1922069 := bbase (se 6 (by rfl) ⟨45048, by rfl⟩ : syracuseStep 1922069 = 90097) (by norm_num)
theorem B1135669 : Blo 1008601 1135669 := bbase (se 5 (by rfl) ⟨53234, by rfl⟩ : syracuseStep 1135669 = 106469) (by norm_num)
theorem B1135705 : Blo 1008601 1135705 := bbase (se 2 (by rfl) ⟨425889, by rfl⟩ : syracuseStep 1135705 = 851779) (by norm_num)
theorem B1135741 : Blo 1008601 1135741 := bbase (se 3 (by rfl) ⟨212951, by rfl⟩ : syracuseStep 1135741 = 425903) (by norm_num)
theorem B1135777 : Blo 1008601 1135777 := bbase (se 2 (by rfl) ⟨425916, by rfl⟩ : syracuseStep 1135777 = 851833) (by norm_num)
theorem B1922221 : Blo 1008601 1922221 := bbase (se 3 (by rfl) ⟨360416, by rfl⟩ : syracuseStep 1922221 = 720833) (by norm_num)
theorem B1135813 : Blo 1008601 1135813 := bbase (se 4 (by rfl) ⟨106482, by rfl⟩ : syracuseStep 1135813 = 212965) (by norm_num)
theorem B2184421 : Blo 1008601 2184421 := bbase (se 4 (by rfl) ⟨204789, by rfl⟩ : syracuseStep 2184421 = 409579) (by norm_num)
theorem B1135849 : Blo 1008601 1135849 := bbase (se 2 (by rfl) ⟨425943, by rfl⟩ : syracuseStep 1135849 = 851887) (by norm_num)
theorem B1135885 : Blo 1008601 1135885 := bbase (se 3 (by rfl) ⟨212978, by rfl⟩ : syracuseStep 1135885 = 425957) (by norm_num)
theorem B1135921 : Blo 1008601 1135921 := bbase (se 2 (by rfl) ⟨425970, by rfl⟩ : syracuseStep 1135921 = 851941) (by norm_num)
theorem B1135957 : Blo 1008601 1135957 := bbase (se 18 (by rfl) ⟨6, by rfl⟩ : syracuseStep 1135957 = 13) (by norm_num)
theorem B1135993 : Blo 1008601 1135993 := bbase (se 2 (by rfl) ⟨425997, by rfl⟩ : syracuseStep 1135993 = 851995) (by norm_num)
theorem B1136029 : Blo 1008601 1136029 := bbase (se 3 (by rfl) ⟨213005, by rfl⟩ : syracuseStep 1136029 = 426011) (by norm_num)
theorem B1136065 : Blo 1008601 1136065 := bbase (se 2 (by rfl) ⟨426024, by rfl⟩ : syracuseStep 1136065 = 852049) (by norm_num)
theorem B1136101 : Blo 1008601 1136101 := bbase (se 4 (by rfl) ⟨106509, by rfl⟩ : syracuseStep 1136101 = 213019) (by norm_num)
theorem B1136137 : Blo 1008601 1136137 := bbase (se 2 (by rfl) ⟨426051, by rfl⟩ : syracuseStep 1136137 = 852103) (by norm_num)
theorem B2872853 : Blo 1008601 2872853 := bbase (se 6 (by rfl) ⟨67332, by rfl⟩ : syracuseStep 2872853 = 134665) (by norm_num)
theorem B1136173 : Blo 1008601 1136173 := bbase (se 3 (by rfl) ⟨213032, by rfl⟩ : syracuseStep 1136173 = 426065) (by norm_num)
theorem B1037881 : Blo 1008601 1037881 := bbase (se 2 (by rfl) ⟨389205, by rfl⟩ : syracuseStep 1037881 = 778411) (by norm_num)
theorem B1136209 : Blo 1008601 1136209 := bbase (se 2 (by rfl) ⟨426078, by rfl⟩ : syracuseStep 1136209 = 852157) (by norm_num)
theorem B1824365 : Blo 1008601 1824365 := bbase (se 3 (by rfl) ⟨342068, by rfl⟩ : syracuseStep 1824365 = 684137) (by norm_num)
theorem B1726069 : Blo 1008601 1726069 := bbase (se 5 (by rfl) ⟨80909, by rfl⟩ : syracuseStep 1726069 = 161819) (by norm_num)
theorem B1136245 : Blo 1008601 1136245 := bbase (se 5 (by rfl) ⟨53261, by rfl⟩ : syracuseStep 1136245 = 106523) (by norm_num)
theorem B1136281 : Blo 1008601 1136281 := bbase (se 2 (by rfl) ⟨426105, by rfl⟩ : syracuseStep 1136281 = 852211) (by norm_num)
theorem B1824437 : Blo 1008601 1824437 := bbase (se 5 (by rfl) ⟨85520, by rfl⟩ : syracuseStep 1824437 = 171041) (by norm_num)
theorem B1136317 : Blo 1008601 1136317 := bbase (se 3 (by rfl) ⟨213059, by rfl⟩ : syracuseStep 1136317 = 426119) (by norm_num)
theorem B1136353 : Blo 1008601 1136353 := bbase (se 2 (by rfl) ⟨426132, by rfl⟩ : syracuseStep 1136353 = 852265) (by norm_num)
theorem B1136389 : Blo 1008601 1136389 := bbase (se 4 (by rfl) ⟨106536, by rfl⟩ : syracuseStep 1136389 = 213073) (by norm_num)
theorem B1136425 : Blo 1008601 1136425 := bbase (se 2 (by rfl) ⟨426159, by rfl⟩ : syracuseStep 1136425 = 852319) (by norm_num)
theorem B1824581 : Blo 1008601 1824581 := bbase (se 4 (by rfl) ⟨171054, by rfl⟩ : syracuseStep 1824581 = 342109) (by norm_num)
theorem B1136461 : Blo 1008601 1136461 := bbase (se 3 (by rfl) ⟨213086, by rfl⟩ : syracuseStep 1136461 = 426173) (by norm_num)
theorem B1136497 : Blo 1008601 1136497 := bbase (se 2 (by rfl) ⟨426186, by rfl⟩ : syracuseStep 1136497 = 852373) (by norm_num)
theorem B1824653 : Blo 1008601 1824653 := bbase (se 3 (by rfl) ⟨342122, by rfl⟩ : syracuseStep 1824653 = 684245) (by norm_num)
theorem B1136533 : Blo 1008601 1136533 := bbase (se 6 (by rfl) ⟨26637, by rfl⟩ : syracuseStep 1136533 = 53275) (by norm_num)
theorem B1136569 : Blo 1008601 1136569 := bbase (se 2 (by rfl) ⟨426213, by rfl⟩ : syracuseStep 1136569 = 852427) (by norm_num)
theorem B1136605 : Blo 1008601 1136605 := bbase (se 3 (by rfl) ⟨213113, by rfl⟩ : syracuseStep 1136605 = 426227) (by norm_num)
theorem B1136641 : Blo 1008601 1136641 := bbase (se 2 (by rfl) ⟨426240, by rfl⟩ : syracuseStep 1136641 = 852481) (by norm_num)
theorem B4315157 : Blo 1008601 4315157 := bbase (se 6 (by rfl) ⟨101136, by rfl⟩ : syracuseStep 4315157 = 202273) (by norm_num)
theorem B1136677 : Blo 1008601 1136677 := bbase (se 4 (by rfl) ⟨106563, by rfl⟩ : syracuseStep 1136677 = 213127) (by norm_num)
theorem B1136713 : Blo 1008601 1136713 := bbase (se 2 (by rfl) ⟨426267, by rfl⟩ : syracuseStep 1136713 = 852535) (by norm_num)
theorem B1136749 : Blo 1008601 1136749 := bbase (se 3 (by rfl) ⟨213140, by rfl⟩ : syracuseStep 1136749 = 426281) (by norm_num)
theorem B1136785 : Blo 1008601 1136785 := bbase (se 2 (by rfl) ⟨426294, by rfl⟩ : syracuseStep 1136785 = 852589) (by norm_num)
theorem B1136821 : Blo 1008601 1136821 := bbase (se 5 (by rfl) ⟨53288, by rfl⟩ : syracuseStep 1136821 = 106577) (by norm_num)
theorem B1136857 : Blo 1008601 1136857 := bbase (se 2 (by rfl) ⟨426321, by rfl⟩ : syracuseStep 1136857 = 852643) (by norm_num)
theorem B1136893 : Blo 1008601 1136893 := bbase (se 3 (by rfl) ⟨213167, by rfl⟩ : syracuseStep 1136893 = 426335) (by norm_num)
theorem B1136929 : Blo 1008601 1136929 := bbase (se 2 (by rfl) ⟨426348, by rfl⟩ : syracuseStep 1136929 = 852697) (by norm_num)
theorem B1136965 : Blo 1008601 1136965 := bbase (se 4 (by rfl) ⟨106590, by rfl⟩ : syracuseStep 1136965 = 213181) (by norm_num)
theorem B1137001 : Blo 1008601 1137001 := bbase (se 2 (by rfl) ⟨426375, by rfl⟩ : syracuseStep 1137001 = 852751) (by norm_num)
theorem B8182133 : Blo 1008601 8182133 := bbase (se 5 (by rfl) ⟨383537, by rfl⟩ : syracuseStep 8182133 = 767075) (by norm_num)
theorem B7297397 : Blo 1008601 7297397 := bbase (se 5 (by rfl) ⟨342065, by rfl⟩ : syracuseStep 7297397 = 684131) (by norm_num)
theorem B1137037 : Blo 1008601 1137037 := bbase (se 3 (by rfl) ⟨213194, by rfl⟩ : syracuseStep 1137037 = 426389) (by norm_num)
theorem B1137073 : Blo 1008601 1137073 := bbase (se 2 (by rfl) ⟨426402, by rfl⟩ : syracuseStep 1137073 = 852805) (by norm_num)
theorem B3037637 : Blo 1008601 3037637 := bbase (se 4 (by rfl) ⟨284778, by rfl⟩ : syracuseStep 3037637 = 569557) (by norm_num)
theorem B1137109 : Blo 1008601 1137109 := bbase (se 7 (by rfl) ⟨13325, by rfl⟩ : syracuseStep 1137109 = 26651) (by norm_num)
theorem B3234293 : Blo 1008601 3234293 := bbase (se 5 (by rfl) ⟨151607, by rfl⟩ : syracuseStep 3234293 = 303215) (by norm_num)
theorem B1137145 : Blo 1008601 1137145 := bbase (se 2 (by rfl) ⟨426429, by rfl⟩ : syracuseStep 1137145 = 852859) (by norm_num)
theorem B1137181 : Blo 1008601 1137181 := bbase (se 3 (by rfl) ⟨213221, by rfl⟩ : syracuseStep 1137181 = 426443) (by norm_num)
theorem B1137217 : Blo 1008601 1137217 := bbase (se 2 (by rfl) ⟨426456, by rfl⟩ : syracuseStep 1137217 = 852913) (by norm_num)
theorem B1137253 : Blo 1008601 1137253 := bbase (se 4 (by rfl) ⟨106617, by rfl⟩ : syracuseStep 1137253 = 213235) (by norm_num)
theorem B1137289 : Blo 1008601 1137289 := bbase (se 2 (by rfl) ⟨426483, by rfl⟩ : syracuseStep 1137289 = 852967) (by norm_num)
theorem B1137325 : Blo 1008601 1137325 := bbase (se 3 (by rfl) ⟨213248, by rfl⟩ : syracuseStep 1137325 = 426497) (by norm_num)
theorem B2874037 : Blo 1008601 2874037 := bbase (se 5 (by rfl) ⟨134720, by rfl⟩ : syracuseStep 2874037 = 269441) (by norm_num)
theorem B1727165 : Blo 1008601 1727165 := bbase (se 3 (by rfl) ⟨323843, by rfl⟩ : syracuseStep 1727165 = 647687) (by norm_num)
theorem B1137361 : Blo 1008601 1137361 := bbase (se 2 (by rfl) ⟨426510, by rfl⟩ : syracuseStep 1137361 = 853021) (by norm_num)
theorem B1137397 : Blo 1008601 1137397 := bbase (se 5 (by rfl) ⟨53315, by rfl⟩ : syracuseStep 1137397 = 106631) (by norm_num)
theorem B1137433 : Blo 1008601 1137433 := bbase (se 2 (by rfl) ⟨426537, by rfl⟩ : syracuseStep 1137433 = 853075) (by norm_num)
theorem B1137469 : Blo 1008601 1137469 := bbase (se 3 (by rfl) ⟨213275, by rfl⟩ : syracuseStep 1137469 = 426551) (by norm_num)
theorem B2874197 : Blo 1008601 2874197 := bbase (se 9 (by rfl) ⟨8420, by rfl⟩ : syracuseStep 2874197 = 16841) (by norm_num)
theorem B1137505 : Blo 1008601 1137505 := bbase (se 2 (by rfl) ⟨426564, by rfl⟩ : syracuseStep 1137505 = 853129) (by norm_num)
theorem B1137541 : Blo 1008601 1137541 := bbase (se 4 (by rfl) ⟨106644, by rfl⟩ : syracuseStep 1137541 = 213289) (by norm_num)
theorem B1137577 : Blo 1008601 1137577 := bbase (se 2 (by rfl) ⟨426591, by rfl⟩ : syracuseStep 1137577 = 853183) (by norm_num)
theorem B1137613 : Blo 1008601 1137613 := bbase (se 3 (by rfl) ⟨213302, by rfl⟩ : syracuseStep 1137613 = 426605) (by norm_num)
theorem B1727453 : Blo 1008601 1727453 := bbase (se 3 (by rfl) ⟨323897, by rfl⟩ : syracuseStep 1727453 = 647795) (by norm_num)
theorem B1137649 : Blo 1008601 1137649 := bbase (se 2 (by rfl) ⟨426618, by rfl⟩ : syracuseStep 1137649 = 853237) (by norm_num)
theorem B4676597 : Blo 1008601 4676597 := bbase (se 5 (by rfl) ⟨219215, by rfl⟩ : syracuseStep 4676597 = 438431) (by norm_num)
theorem B1137685 : Blo 1008601 1137685 := bbase (se 6 (by rfl) ⟨26664, by rfl⟩ : syracuseStep 1137685 = 53329) (by norm_num)
theorem B1137721 : Blo 1008601 1137721 := bbase (se 2 (by rfl) ⟨426645, by rfl⟩ : syracuseStep 1137721 = 853291) (by norm_num)
theorem B2874437 : Blo 1008601 2874437 := bbase (se 4 (by rfl) ⟨269478, by rfl⟩ : syracuseStep 2874437 = 538957) (by norm_num)
theorem B1137757 : Blo 1008601 1137757 := bbase (se 3 (by rfl) ⟨213329, by rfl⟩ : syracuseStep 1137757 = 426659) (by norm_num)
theorem B1137793 : Blo 1008601 1137793 := bbase (se 2 (by rfl) ⟨426672, by rfl⟩ : syracuseStep 1137793 = 853345) (by norm_num)
theorem B1137829 : Blo 1008601 1137829 := bbase (se 4 (by rfl) ⟨106671, by rfl⟩ : syracuseStep 1137829 = 213343) (by norm_num)
theorem B1137865 : Blo 1008601 1137865 := bbase (se 2 (by rfl) ⟨426699, by rfl⟩ : syracuseStep 1137865 = 853399) (by norm_num)
theorem B1137901 : Blo 1008601 1137901 := bbase (se 3 (by rfl) ⟨213356, by rfl⟩ : syracuseStep 1137901 = 426713) (by norm_num)
theorem B2874629 : Blo 1008601 2874629 := bbase (se 4 (by rfl) ⟨269496, by rfl⟩ : syracuseStep 2874629 = 538993) (by norm_num)
theorem B1137937 : Blo 1008601 1137937 := bbase (se 2 (by rfl) ⟨426726, by rfl⟩ : syracuseStep 1137937 = 853453) (by norm_num)
theorem B1137973 : Blo 1008601 1137973 := bbase (se 5 (by rfl) ⟨53342, by rfl⟩ : syracuseStep 1137973 = 106685) (by norm_num)
theorem B1138009 : Blo 1008601 1138009 := bbase (se 2 (by rfl) ⟨426753, by rfl⟩ : syracuseStep 1138009 = 853507) (by norm_num)
theorem B1138045 : Blo 1008601 1138045 := bbase (se 3 (by rfl) ⟨213383, by rfl⟩ : syracuseStep 1138045 = 426767) (by norm_num)
theorem B1138081 : Blo 1008601 1138081 := bbase (se 2 (by rfl) ⟨426780, by rfl⟩ : syracuseStep 1138081 = 853561) (by norm_num)
theorem B1138117 : Blo 1008601 1138117 := bbase (se 4 (by rfl) ⟨106698, by rfl⟩ : syracuseStep 1138117 = 213397) (by norm_num)
theorem B1138153 : Blo 1008601 1138153 := bbase (se 2 (by rfl) ⟨426807, by rfl⟩ : syracuseStep 1138153 = 853615) (by norm_num)
theorem B1138189 : Blo 1008601 1138189 := bbase (se 3 (by rfl) ⟨213410, by rfl⟩ : syracuseStep 1138189 = 426821) (by norm_num)
theorem B1138225 : Blo 1008601 1138225 := bbase (se 2 (by rfl) ⟨426834, by rfl⟩ : syracuseStep 1138225 = 853669) (by norm_num)
theorem B1138261 : Blo 1008601 1138261 := bbase (se 8 (by rfl) ⟨6669, by rfl⟩ : syracuseStep 1138261 = 13339) (by norm_num)
theorem B1138297 : Blo 1008601 1138297 := bbase (se 2 (by rfl) ⟨426861, by rfl⟩ : syracuseStep 1138297 = 853723) (by norm_num)
theorem B1138333 : Blo 1008601 1138333 := bbase (se 3 (by rfl) ⟨213437, by rfl⟩ : syracuseStep 1138333 = 426875) (by norm_num)
theorem B1138369 : Blo 1008601 1138369 := bbase (se 2 (by rfl) ⟨426888, by rfl⟩ : syracuseStep 1138369 = 853777) (by norm_num)
theorem B1138405 : Blo 1008601 1138405 := bbase (se 4 (by rfl) ⟨106725, by rfl⟩ : syracuseStep 1138405 = 213451) (by norm_num)
theorem B1138441 : Blo 1008601 1138441 := bbase (se 2 (by rfl) ⟨426915, by rfl⟩ : syracuseStep 1138441 = 853831) (by norm_num)
theorem B1138477 : Blo 1008601 1138477 := bbase (se 3 (by rfl) ⟨213464, by rfl⟩ : syracuseStep 1138477 = 426929) (by norm_num)
theorem B1138513 : Blo 1008601 1138513 := bbase (se 2 (by rfl) ⟨426942, by rfl⟩ : syracuseStep 1138513 = 853885) (by norm_num)
theorem B1138549 : Blo 1008601 1138549 := bbase (se 5 (by rfl) ⟨53369, by rfl⟩ : syracuseStep 1138549 = 106739) (by norm_num)
theorem B1138585 : Blo 1008601 1138585 := bbase (se 2 (by rfl) ⟨426969, by rfl⟩ : syracuseStep 1138585 = 853939) (by norm_num)
theorem B1138621 : Blo 1008601 1138621 := bbase (se 3 (by rfl) ⟨213491, by rfl⟩ : syracuseStep 1138621 = 426983) (by norm_num)
theorem B1138657 : Blo 1008601 1138657 := bbase (se 2 (by rfl) ⟨426996, by rfl⟩ : syracuseStep 1138657 = 853993) (by norm_num)
theorem B4382693 : Blo 1008601 4382693 := bbase (se 4 (by rfl) ⟨410877, by rfl⟩ : syracuseStep 4382693 = 821755) (by norm_num)
theorem B1138693 : Blo 1008601 1138693 := bbase (se 4 (by rfl) ⟨106752, by rfl⟩ : syracuseStep 1138693 = 213505) (by norm_num)
theorem B1368085 : Blo 1008601 1368085 := bbase (se 6 (by rfl) ⟨32064, by rfl⟩ : syracuseStep 1368085 = 64129) (by norm_num)
theorem B1138729 : Blo 1008601 1138729 := bbase (se 2 (by rfl) ⟨427023, by rfl⟩ : syracuseStep 1138729 = 854047) (by norm_num)
theorem B1138765 : Blo 1008601 1138765 := bbase (se 3 (by rfl) ⟨213518, by rfl⟩ : syracuseStep 1138765 = 427037) (by norm_num)
theorem B2154605 : Blo 1008601 2154605 := bbase (se 3 (by rfl) ⟨403988, by rfl⟩ : syracuseStep 2154605 = 807977) (by norm_num)
theorem B1138801 : Blo 1008601 1138801 := bbase (se 2 (by rfl) ⟨427050, by rfl⟩ : syracuseStep 1138801 = 854101) (by norm_num)
theorem B1138837 : Blo 1008601 1138837 := bbase (se 6 (by rfl) ⟨26691, by rfl⟩ : syracuseStep 1138837 = 53383) (by norm_num)
theorem B1138873 : Blo 1008601 1138873 := bbase (se 2 (by rfl) ⟨427077, by rfl⟩ : syracuseStep 1138873 = 854155) (by norm_num)
theorem B1138909 : Blo 1008601 1138909 := bbase (se 3 (by rfl) ⟨213545, by rfl⟩ : syracuseStep 1138909 = 427091) (by norm_num)
theorem B2875621 : Blo 1008601 2875621 := bbase (se 4 (by rfl) ⟨269589, by rfl⟩ : syracuseStep 2875621 = 539179) (by norm_num)
theorem B1138945 : Blo 1008601 1138945 := bbase (se 2 (by rfl) ⟨427104, by rfl⟩ : syracuseStep 1138945 = 854209) (by norm_num)
theorem B1138981 : Blo 1008601 1138981 := bbase (se 4 (by rfl) ⟨106779, by rfl⟩ : syracuseStep 1138981 = 213559) (by norm_num)
theorem B1139017 : Blo 1008601 1139017 := bbase (se 2 (by rfl) ⟨427131, by rfl⟩ : syracuseStep 1139017 = 854263) (by norm_num)
theorem B2154845 : Blo 1008601 2154845 := bbase (se 3 (by rfl) ⟨404033, by rfl⟩ : syracuseStep 2154845 = 808067) (by norm_num)
theorem B1139053 : Blo 1008601 1139053 := bbase (se 3 (by rfl) ⟨213572, by rfl⟩ : syracuseStep 1139053 = 427145) (by norm_num)
theorem B1139089 : Blo 1008601 1139089 := bbase (se 2 (by rfl) ⟨427158, by rfl⟩ : syracuseStep 1139089 = 854317) (by norm_num)
theorem B1139125 : Blo 1008601 1139125 := bbase (se 5 (by rfl) ⟨53396, by rfl⟩ : syracuseStep 1139125 = 106793) (by norm_num)
theorem B1139161 : Blo 1008601 1139161 := bbase (se 2 (by rfl) ⟨427185, by rfl⟩ : syracuseStep 1139161 = 854371) (by norm_num)
theorem B2155349 : Blo 1008601 2155349 := bbase (se 9 (by rfl) ⟨6314, by rfl⟩ : syracuseStep 2155349 = 12629) (by norm_num)
theorem B2155357 : Blo 1008601 2155357 := bbase (se 3 (by rfl) ⟨404129, by rfl⟩ : syracuseStep 2155357 = 808259) (by norm_num)
theorem B1663997 : Blo 1008601 1663997 := bbase (se 3 (by rfl) ⟨311999, by rfl⟩ : syracuseStep 1663997 = 623999) (by norm_num)
theorem B1729765 : Blo 1008601 1729765 := bbase (se 4 (by rfl) ⟨162165, by rfl⟩ : syracuseStep 1729765 = 324331) (by norm_num)
theorem B2876725 : Blo 1008601 2876725 := bbase (se 5 (by rfl) ⟨134846, by rfl⟩ : syracuseStep 2876725 = 269693) (by norm_num)
theorem B8644117 : Blo 1008601 8644117 := bbase (se 6 (by rfl) ⟨202596, by rfl⟩ : syracuseStep 8644117 = 405193) (by norm_num)
theorem B3073909 : Blo 1008601 3073909 := bbase (se 5 (by rfl) ⟨144089, by rfl⟩ : syracuseStep 3073909 = 288179) (by norm_num)
theorem B2156485 : Blo 1008601 2156485 := bbase (se 4 (by rfl) ⟨202170, by rfl⟩ : syracuseStep 2156485 = 404341) (by norm_num)
theorem B4319189 : Blo 1008601 4319189 := bbase (se 7 (by rfl) ⟨50615, by rfl⟩ : syracuseStep 4319189 = 101231) (by norm_num)
theorem B1730717 : Blo 1008601 1730717 := bbase (se 3 (by rfl) ⟨324509, by rfl⟩ : syracuseStep 1730717 = 649019) (by norm_num)
theorem B11528405 : Blo 1008601 11528405 := bbase (se 7 (by rfl) ⟨135098, by rfl⟩ : syracuseStep 11528405 = 270197) (by norm_num)
theorem B2156861 : Blo 1008601 2156861 := bbase (se 3 (by rfl) ⟨404411, by rfl⟩ : syracuseStep 2156861 = 808823) (by norm_num)
theorem B3238213 : Blo 1008601 3238213 := bbase (se 4 (by rfl) ⟨303582, by rfl⟩ : syracuseStep 3238213 = 607165) (by norm_num)
theorem B1436125 : Blo 1008601 1436125 := bbase (se 3 (by rfl) ⟨269273, by rfl⟩ : syracuseStep 1436125 = 538547) (by norm_num)
theorem B1436221 : Blo 1008601 1436221 := bbase (se 3 (by rfl) ⟨269291, by rfl⟩ : syracuseStep 1436221 = 538583) (by norm_num)
theorem B3238469 : Blo 1008601 3238469 := bbase (se 4 (by rfl) ⟨303606, by rfl⟩ : syracuseStep 3238469 = 607213) (by norm_num)
theorem B2878229 : Blo 1008601 2878229 := bbase (se 6 (by rfl) ⟨67458, by rfl⟩ : syracuseStep 2878229 = 134917) (by norm_num)
theorem B3075077 : Blo 1008601 3075077 := bbase (se 4 (by rfl) ⟨288288, by rfl⟩ : syracuseStep 3075077 = 576577) (by norm_num)
theorem B5106725 : Blo 1008601 5106725 := bbase (se 4 (by rfl) ⟨478755, by rfl⟩ : syracuseStep 5106725 = 957511) (by norm_num)
theorem B1436717 : Blo 1008601 1436717 := bbase (se 3 (by rfl) ⟨269384, by rfl⟩ : syracuseStep 1436717 = 538769) (by norm_num)
theorem B8646101 : Blo 1008601 8646101 := bbase (se 7 (by rfl) ⟨101321, by rfl⟩ : syracuseStep 8646101 = 202643) (by norm_num)
theorem B1437269 : Blo 1008601 1437269 := bbase (se 8 (by rfl) ⟨8421, by rfl⟩ : syracuseStep 1437269 = 16843) (by norm_num)
theorem B4320965 : Blo 1008601 4320965 := bbase (se 4 (by rfl) ⟨405090, by rfl⟩ : syracuseStep 4320965 = 810181) (by norm_num)
theorem B3829589 : Blo 1008601 3829589 := bbase (se 9 (by rfl) ⟨11219, by rfl⟩ : syracuseStep 3829589 = 22439) (by norm_num)
theorem B1077149 : Blo 1008601 1077149 := bbase (se 3 (by rfl) ⟨201965, by rfl⟩ : syracuseStep 1077149 = 403931) (by norm_num)
theorem B2158501 : Blo 1008601 2158501 := bbase (se 4 (by rfl) ⟨202359, by rfl⟩ : syracuseStep 2158501 = 404719) (by norm_num)
theorem B3698597 : Blo 1008601 3698597 := bbase (se 4 (by rfl) ⟨346743, by rfl⟩ : syracuseStep 3698597 = 693487) (by norm_num)
theorem B14544917 : Blo 1008601 14544917 := bbase (se 6 (by rfl) ⟨340896, by rfl⟩ : syracuseStep 14544917 = 681793) (by norm_num)
theorem B1077337 : Blo 1008601 1077337 := bbase (se 2 (by rfl) ⟨404001, by rfl⟩ : syracuseStep 1077337 = 808003) (by norm_num)
theorem B7663733 : Blo 1008601 7663733 := bbase (se 5 (by rfl) ⟨359237, by rfl⟩ : syracuseStep 7663733 = 718475) (by norm_num)
theorem B5108021 : Blo 1008601 5108021 := bbase (se 5 (by rfl) ⟨239438, by rfl⟩ : syracuseStep 5108021 = 478877) (by norm_num)
theorem B1438021 : Blo 1008601 1438021 := bbase (se 4 (by rfl) ⟨134814, by rfl⟩ : syracuseStep 1438021 = 269629) (by norm_num)
theorem B2879813 : Blo 1008601 2879813 := bbase (se 4 (by rfl) ⟨269982, by rfl⟩ : syracuseStep 2879813 = 539965) (by norm_num)
theorem B6484373 : Blo 1008601 6484373 := bbase (se 6 (by rfl) ⟨151977, by rfl⟩ : syracuseStep 6484373 = 303955) (by norm_num)
theorem B3404213 : Blo 1008601 3404213 := bbase (se 5 (by rfl) ⟨159572, by rfl⟩ : syracuseStep 3404213 = 319145) (by norm_num)
theorem B4321957 : Blo 1008601 4321957 := bbase (se 4 (by rfl) ⟨405183, by rfl⟩ : syracuseStep 4321957 = 810367) (by norm_num)
theorem B2159389 : Blo 1008601 2159389 := bbase (se 3 (by rfl) ⟨404885, by rfl⟩ : syracuseStep 2159389 = 809771) (by norm_num)
theorem B3404645 : Blo 1008601 3404645 := bbase (se 4 (by rfl) ⟨319185, by rfl⟩ : syracuseStep 3404645 = 638371) (by norm_num)
theorem B1078157 : Blo 1008601 1078157 := bbase (se 3 (by rfl) ⟨202154, by rfl⟩ : syracuseStep 1078157 = 404309) (by norm_num)
theorem B2880485 : Blo 1008601 2880485 := bbase (se 4 (by rfl) ⟨270045, by rfl⟩ : syracuseStep 2880485 = 540091) (by norm_num)
theorem B3830773 : Blo 1008601 3830773 := bbase (se 5 (by rfl) ⟨179567, by rfl⟩ : syracuseStep 3830773 = 359135) (by norm_num)
theorem B1438813 : Blo 1008601 1438813 := bbase (se 3 (by rfl) ⟨269777, by rfl⟩ : syracuseStep 1438813 = 539555) (by norm_num)
theorem B2553029 : Blo 1008601 2553029 := bbase (se 4 (by rfl) ⟨239346, by rfl⟩ : syracuseStep 2553029 = 478693) (by norm_num)
theorem B2159885 : Blo 1008601 2159885 := bbase (se 3 (by rfl) ⟨404978, by rfl⟩ : syracuseStep 2159885 = 809957) (by norm_num)
theorem B3405077 : Blo 1008601 3405077 := bbase (se 6 (by rfl) ⟨79806, by rfl⟩ : syracuseStep 3405077 = 159613) (by norm_num)
theorem B3241237 : Blo 1008601 3241237 := bbase (se 6 (by rfl) ⟨75966, by rfl⟩ : syracuseStep 3241237 = 151933) (by norm_num)
theorem B3831077 : Blo 1008601 3831077 := bbase (se 4 (by rfl) ⟨359163, by rfl⟩ : syracuseStep 3831077 = 718327) (by norm_num)
theorem B1078601 : Blo 1008601 1078601 := bbase (se 2 (by rfl) ⟨404475, by rfl⟩ : syracuseStep 1078601 = 808951) (by norm_num)
theorem B12285269 : Blo 1008601 12285269 := bbase (se 13 (by rfl) ⟨2249, by rfl⟩ : syracuseStep 12285269 = 4499) (by norm_num)
theorem B2553221 : Blo 1008601 2553221 := bbase (se 4 (by rfl) ⟨239364, by rfl⟩ : syracuseStep 2553221 = 478729) (by norm_num)
theorem B2880917 : Blo 1008601 2880917 := bbase (se 6 (by rfl) ⟨67521, by rfl⟩ : syracuseStep 2880917 = 135043) (by norm_num)
theorem B1439149 : Blo 1008601 1439149 := bbase (se 3 (by rfl) ⟨269840, by rfl⟩ : syracuseStep 1439149 = 539681) (by norm_num)
theorem B8189461 : Blo 1008601 8189461 := bbase (se 6 (by rfl) ⟨191940, by rfl⟩ : syracuseStep 8189461 = 383881) (by norm_num)
theorem B1078849 : Blo 1008601 1078849 := bbase (se 2 (by rfl) ⟨404568, by rfl⟩ : syracuseStep 1078849 = 809137) (by norm_num)
theorem B5109317 : Blo 1008601 5109317 := bbase (se 4 (by rfl) ⟨478998, by rfl⟩ : syracuseStep 5109317 = 957997) (by norm_num)
theorem B1439365 : Blo 1008601 1439365 := bbase (se 4 (by rfl) ⟨134940, by rfl⟩ : syracuseStep 1439365 = 269881) (by norm_num)
theorem B3405509 : Blo 1008601 3405509 := bbase (se 4 (by rfl) ⟨319266, by rfl⟩ : syracuseStep 3405509 = 638533) (by norm_num)
theorem B1537733 : Blo 1008601 1537733 := bbase (se 4 (by rfl) ⟨144162, by rfl⟩ : syracuseStep 1537733 = 288325) (by norm_num)
theorem B2553565 : Blo 1008601 2553565 := bbase (se 3 (by rfl) ⟨478793, by rfl⟩ : syracuseStep 2553565 = 957587) (by norm_num)
theorem B3077909 : Blo 1008601 3077909 := bbase (se 6 (by rfl) ⟨72138, by rfl⟩ : syracuseStep 3077909 = 144277) (by norm_num)
theorem B2553677 : Blo 1008601 2553677 := bbase (se 3 (by rfl) ⟨478814, by rfl⟩ : syracuseStep 2553677 = 957629) (by norm_num)
theorem B1079281 : Blo 1008601 1079281 := bbase (se 2 (by rfl) ⟨404730, by rfl⟩ : syracuseStep 1079281 = 809461) (by norm_num)
theorem B1439741 : Blo 1008601 1439741 := bbase (se 3 (by rfl) ⟨269951, by rfl⟩ : syracuseStep 1439741 = 539903) (by norm_num)
theorem B2553869 : Blo 1008601 2553869 := bbase (se 3 (by rfl) ⟨478850, by rfl⟩ : syracuseStep 2553869 = 957701) (by norm_num)
theorem B1079353 : Blo 1008601 1079353 := bbase (se 2 (by rfl) ⟨404757, by rfl⟩ : syracuseStep 1079353 = 809515) (by norm_num)
theorem B2160749 : Blo 1008601 2160749 := bbase (se 3 (by rfl) ⟨405140, by rfl⟩ : syracuseStep 2160749 = 810281) (by norm_num)
theorem B3405941 : Blo 1008601 3405941 := bbase (se 5 (by rfl) ⟨159653, by rfl⟩ : syracuseStep 3405941 = 319307) (by norm_num)
theorem B5470325 : Blo 1008601 5470325 := bbase (se 5 (by rfl) ⟨256421, by rfl⟩ : syracuseStep 5470325 = 512843) (by norm_num)
theorem B2881669 : Blo 1008601 2881669 := bbase (se 4 (by rfl) ⟨270156, by rfl⟩ : syracuseStep 2881669 = 540313) (by norm_num)
theorem B1702093 : Blo 1008601 1702093 := bbase (se 3 (by rfl) ⟨319142, by rfl⟩ : syracuseStep 1702093 = 638285) (by norm_num)
theorem B2160893 : Blo 1008601 2160893 := bbase (se 3 (by rfl) ⟨405167, by rfl⟩ : syracuseStep 2160893 = 810335) (by norm_num)
theorem B1702181 : Blo 1008601 1702181 := bbase (se 4 (by rfl) ⟨159579, by rfl⟩ : syracuseStep 1702181 = 319159) (by norm_num)
theorem B2554213 : Blo 1008601 2554213 := bbase (se 4 (by rfl) ⟨239457, by rfl⟩ : syracuseStep 2554213 = 478915) (by norm_num)
theorem B5765525 : Blo 1008601 5765525 := bbase (se 6 (by rfl) ⟨135129, by rfl⟩ : syracuseStep 5765525 = 270259) (by norm_num)
theorem B1702309 : Blo 1008601 1702309 := bbase (se 4 (by rfl) ⟨159591, by rfl⟩ : syracuseStep 1702309 = 319183) (by norm_num)
theorem B1079725 : Blo 1008601 1079725 := bbase (se 3 (by rfl) ⟨202448, by rfl⟩ : syracuseStep 1079725 = 404897) (by norm_num)
theorem B2554325 : Blo 1008601 2554325 := bbase (se 7 (by rfl) ⟨29933, by rfl⟩ : syracuseStep 2554325 = 59867) (by norm_num)
theorem B1702397 : Blo 1008601 1702397 := bbase (se 3 (by rfl) ⟨319199, by rfl⟩ : syracuseStep 1702397 = 638399) (by norm_num)
theorem B3406373 : Blo 1008601 3406373 := bbase (se 4 (by rfl) ⟨319347, by rfl⟩ : syracuseStep 3406373 = 638695) (by norm_num)
theorem B9697877 : Blo 1008601 9697877 := bbase (se 8 (by rfl) ⟨56823, by rfl⟩ : syracuseStep 9697877 = 113647) (by norm_num)
theorem B3111509 : Blo 1008601 3111509 := bbase (se 8 (by rfl) ⟨18231, by rfl⟩ : syracuseStep 3111509 = 36463) (by norm_num)
theorem B1702525 : Blo 1008601 1702525 := bbase (se 3 (by rfl) ⟨319223, by rfl⟩ : syracuseStep 1702525 = 638447) (by norm_num)
theorem B2554517 : Blo 1008601 2554517 := bbase (se 6 (by rfl) ⟨59871, by rfl⟩ : syracuseStep 2554517 = 119743) (by norm_num)
theorem B12974741 : Blo 1008601 12974741 := bbase (se 6 (by rfl) ⟨304095, by rfl⟩ : syracuseStep 12974741 = 608191) (by norm_num)
theorem B1702613 : Blo 1008601 1702613 := bbase (se 7 (by rfl) ⟨19952, by rfl⟩ : syracuseStep 1702613 = 39905) (by norm_num)
theorem B1276661 : Blo 1008601 1276661 := bbase (se 5 (by rfl) ⟨59843, by rfl⟩ : syracuseStep 1276661 = 119687) (by norm_num)
theorem B1080101 : Blo 1008601 1080101 := bbase (se 4 (by rfl) ⟨101259, by rfl⟩ : syracuseStep 1080101 = 202519) (by norm_num)
theorem B1276717 : Blo 1008601 1276717 := bbase (se 3 (by rfl) ⟨239384, by rfl⟩ : syracuseStep 1276717 = 478769) (by norm_num)
theorem B1702741 : Blo 1008601 1702741 := bbase (se 9 (by rfl) ⟨4988, by rfl⟩ : syracuseStep 1702741 = 9977) (by norm_num)
theorem B5110613 : Blo 1008601 5110613 := bbase (se 9 (by rfl) ⟨14972, by rfl⟩ : syracuseStep 5110613 = 29945) (by norm_num)
theorem B2423645 : Blo 1008601 2423645 := bbase (se 3 (by rfl) ⟨454433, by rfl⟩ : syracuseStep 2423645 = 908867) (by norm_num)
theorem B1080173 : Blo 1008601 1080173 := bbase (se 3 (by rfl) ⟨202532, by rfl⟩ : syracuseStep 1080173 = 405065) (by norm_num)
theorem B1276813 : Blo 1008601 1276813 := bbase (se 3 (by rfl) ⟨239402, by rfl⟩ : syracuseStep 1276813 = 478805) (by norm_num)
theorem B1702829 : Blo 1008601 1702829 := bbase (se 3 (by rfl) ⟨319280, by rfl⟩ : syracuseStep 1702829 = 638561) (by norm_num)
theorem B3406805 : Blo 1008601 3406805 := bbase (se 7 (by rfl) ⟨39923, by rfl⟩ : syracuseStep 3406805 = 79847) (by norm_num)
theorem B2161637 : Blo 1008601 2161637 := bbase (se 4 (by rfl) ⟨202653, by rfl⟩ : syracuseStep 2161637 = 405307) (by norm_num)
theorem B2554861 : Blo 1008601 2554861 := bbase (se 3 (by rfl) ⟨479036, by rfl⟩ : syracuseStep 2554861 = 958073) (by norm_num)
theorem B1080361 : Blo 1008601 1080361 := bbase (se 2 (by rfl) ⟨405135, by rfl⟩ : syracuseStep 1080361 = 810271) (by norm_num)
theorem B1702957 : Blo 1008601 1702957 := bbase (se 3 (by rfl) ⟨319304, by rfl⟩ : syracuseStep 1702957 = 638609) (by norm_num)
theorem B1276985 : Blo 1008601 1276985 := bbase (se 2 (by rfl) ⟨478869, by rfl⟩ : syracuseStep 1276985 = 957739) (by norm_num)
theorem B2554973 : Blo 1008601 2554973 := bbase (se 3 (by rfl) ⟨479057, by rfl⟩ : syracuseStep 2554973 = 958115) (by norm_num)
theorem B1277041 : Blo 1008601 1277041 := bbase (se 2 (by rfl) ⟨478890, by rfl⟩ : syracuseStep 1277041 = 957781) (by norm_num)
theorem B1703045 : Blo 1008601 1703045 := bbase (se 4 (by rfl) ⟨159660, by rfl⟩ : syracuseStep 1703045 = 319321) (by norm_num)
theorem B3636389 : Blo 1008601 3636389 := bbase (se 4 (by rfl) ⟨340911, by rfl⟩ : syracuseStep 3636389 = 681823) (by norm_num)
theorem B1277137 : Blo 1008601 1277137 := bbase (se 2 (by rfl) ⟨478926, by rfl⟩ : syracuseStep 1277137 = 957853) (by norm_num)
theorem B13991125 : Blo 1008601 13991125 := bbase (se 7 (by rfl) ⟨163958, by rfl⟩ : syracuseStep 13991125 = 327917) (by norm_num)
theorem B1080545 : Blo 1008601 1080545 := bbase (se 2 (by rfl) ⟨405204, by rfl⟩ : syracuseStep 1080545 = 810409) (by norm_num)
theorem B1703173 : Blo 1008601 1703173 := bbase (se 4 (by rfl) ⟨159672, by rfl⟩ : syracuseStep 1703173 = 319345) (by norm_num)
theorem B2424077 : Blo 1008601 2424077 := bbase (se 3 (by rfl) ⟨454514, by rfl⟩ : syracuseStep 2424077 = 909029) (by norm_num)
theorem B2555165 : Blo 1008601 2555165 := bbase (se 3 (by rfl) ⟨479093, by rfl⟩ : syracuseStep 2555165 = 958187) (by norm_num)
theorem B1703261 : Blo 1008601 1703261 := bbase (se 3 (by rfl) ⟨319361, by rfl⟩ : syracuseStep 1703261 = 638723) (by norm_num)
theorem B3833189 : Blo 1008601 3833189 := bbase (se 4 (by rfl) ⟨359361, by rfl⟩ : syracuseStep 3833189 = 718723) (by norm_num)
theorem B1277309 : Blo 1008601 1277309 := bbase (se 3 (by rfl) ⟨239495, by rfl⟩ : syracuseStep 1277309 = 478991) (by norm_num)
theorem B3407237 : Blo 1008601 3407237 := bbase (se 4 (by rfl) ⟨319428, by rfl⟩ : syracuseStep 3407237 = 638857) (by norm_num)
theorem B1441165 : Blo 1008601 1441165 := bbase (se 3 (by rfl) ⟨270218, by rfl⟩ : syracuseStep 1441165 = 540437) (by norm_num)
theorem B1277365 : Blo 1008601 1277365 := bbase (se 5 (by rfl) ⟨59876, by rfl⟩ : syracuseStep 1277365 = 119753) (by norm_num)
theorem B1703389 : Blo 1008601 1703389 := bbase (se 3 (by rfl) ⟨319385, by rfl⟩ : syracuseStep 1703389 = 638771) (by norm_num)
theorem B20708885 : Blo 1008601 20708885 := bbase (se 6 (by rfl) ⟨485364, by rfl⟩ : syracuseStep 20708885 = 970729) (by norm_num)
theorem B1277461 : Blo 1008601 1277461 := bbase (se 6 (by rfl) ⟨29940, by rfl⟩ : syracuseStep 1277461 = 59881) (by norm_num)
theorem B1703477 : Blo 1008601 1703477 := bbase (se 5 (by rfl) ⟨79850, by rfl⟩ : syracuseStep 1703477 = 159701) (by norm_num)
theorem B2555509 : Blo 1008601 2555509 := bbase (se 5 (by rfl) ⟨119789, by rfl⟩ : syracuseStep 2555509 = 239579) (by norm_num)
theorem B3833477 : Blo 1008601 3833477 := bbase (se 4 (by rfl) ⟨359388, by rfl⟩ : syracuseStep 3833477 = 718777) (by norm_num)
theorem B1703605 : Blo 1008601 1703605 := bbase (se 5 (by rfl) ⟨79856, by rfl⟩ : syracuseStep 1703605 = 159713) (by norm_num)
theorem B1277633 : Blo 1008601 1277633 := bbase (se 2 (by rfl) ⟨479112, by rfl⟩ : syracuseStep 1277633 = 958225) (by norm_num)
theorem B2162389 : Blo 1008601 2162389 := bbase (se 7 (by rfl) ⟨25340, by rfl⟩ : syracuseStep 2162389 = 50681) (by norm_num)
theorem B2457317 : Blo 1008601 2457317 := bbase (se 4 (by rfl) ⟨230373, by rfl⟩ : syracuseStep 2457317 = 460747) (by norm_num)
theorem B2555621 : Blo 1008601 2555621 := bbase (se 4 (by rfl) ⟨239589, by rfl⟩ : syracuseStep 2555621 = 479179) (by norm_num)
theorem B1277689 : Blo 1008601 1277689 := bbase (se 2 (by rfl) ⟨479133, by rfl⟩ : syracuseStep 1277689 = 958267) (by norm_num)
theorem B1703693 : Blo 1008601 1703693 := bbase (se 3 (by rfl) ⟨319442, by rfl⟩ : syracuseStep 1703693 = 638885) (by norm_num)
theorem B5177141 : Blo 1008601 5177141 := bbase (se 5 (by rfl) ⟨242678, by rfl⟩ : syracuseStep 5177141 = 485357) (by norm_num)
theorem B3407669 : Blo 1008601 3407669 := bbase (se 5 (by rfl) ⟨159734, by rfl⟩ : syracuseStep 3407669 = 319469) (by norm_num)
theorem B1277785 : Blo 1008601 1277785 := bbase (se 2 (by rfl) ⟨479169, by rfl⟩ : syracuseStep 1277785 = 958339) (by norm_num)
theorem B2162533 : Blo 1008601 2162533 := bbase (se 4 (by rfl) ⟨202737, by rfl⟩ : syracuseStep 2162533 = 405475) (by norm_num)
theorem B1212293 : Blo 1008601 1212293 := bbase (se 4 (by rfl) ⟨113652, by rfl⟩ : syracuseStep 1212293 = 227305) (by norm_num)
theorem B1703821 : Blo 1008601 1703821 := bbase (se 3 (by rfl) ⟨319466, by rfl⟩ : syracuseStep 1703821 = 638933) (by norm_num)
theorem B2555813 : Blo 1008601 2555813 := bbase (se 4 (by rfl) ⟨239607, by rfl⟩ : syracuseStep 2555813 = 479215) (by norm_num)
theorem B1081297 : Blo 1008601 1081297 := bbase (se 2 (by rfl) ⟨405486, by rfl⟩ : syracuseStep 1081297 = 810973) (by norm_num)
theorem B1441757 : Blo 1008601 1441757 := bbase (se 3 (by rfl) ⟨270329, by rfl⟩ : syracuseStep 1441757 = 540659) (by norm_num)
theorem B1703909 : Blo 1008601 1703909 := bbase (se 4 (by rfl) ⟨159741, by rfl⟩ : syracuseStep 1703909 = 319483) (by norm_num)
theorem B3407885 : Blo 1008601 3407885 := bstep (se 3 (by rfl) ⟨638978, by rfl⟩ : syracuseStep 3407885 = 1277957) B1277957
theorem B3407939 : Blo 1008601 3407939 := bstep (se 1 (by rfl) ⟨2555954, by rfl⟩ : syracuseStep 3407939 = 5111909) B5111909
theorem B1704017 : Blo 1008601 1704017 := bstep (se 2 (by rfl) ⟨639006, by rfl⟩ : syracuseStep 1704017 = 1278013) B1278013
theorem B1704145 : Blo 1008601 1704145 := bstep (se 2 (by rfl) ⟨639054, by rfl⟩ : syracuseStep 1704145 = 1278109) B1278109
theorem B1704179 : Blo 1008601 1704179 := bstep (se 1 (by rfl) ⟨1278134, by rfl⟩ : syracuseStep 1704179 = 2556269) B2556269
theorem B3834161 : Blo 1008601 3834161 := bstep (se 2 (by rfl) ⟨1437810, by rfl⟩ : syracuseStep 3834161 = 2875621) B2875621
theorem B3408209 : Blo 1008601 3408209 := bstep (se 2 (by rfl) ⟨1278078, by rfl⟩ : syracuseStep 3408209 = 2556157) B2556157
theorem B1704307 : Blo 1008601 1704307 := bstep (se 1 (by rfl) ⟨1278230, by rfl⟩ : syracuseStep 1704307 = 2556461) B2556461
theorem B1704449 : Blo 1008601 1704449 := bstep (se 2 (by rfl) ⟨639168, by rfl⟩ : syracuseStep 1704449 = 1278337) B1278337
theorem B1278499 : Blo 1008601 1278499 := bstep (se 1 (by rfl) ⟨958874, by rfl⟩ : syracuseStep 1278499 = 1917749) B1917749
theorem B1704577 : Blo 1008601 1704577 := bstep (se 2 (by rfl) ⟨639216, by rfl⟩ : syracuseStep 1704577 = 1278433) B1278433
theorem B1278595 : Blo 1008601 1278595 := bstep (se 1 (by rfl) ⟨958946, by rfl⟩ : syracuseStep 1278595 = 1917893) B1917893
theorem B1704611 : Blo 1008601 1704611 := bstep (se 1 (by rfl) ⟨1278458, by rfl⟩ : syracuseStep 1704611 = 2556917) B2556917
theorem B2556593 : Blo 1008601 2556593 := bstep (se 2 (by rfl) ⟨958722, by rfl⟩ : syracuseStep 2556593 = 1917445) B1917445
theorem B2556643 : Blo 1008601 2556643 := bstep (se 1 (by rfl) ⟨1917482, by rfl⟩ : syracuseStep 2556643 = 3834965) B3834965
theorem B2425585 : Blo 1008601 2425585 := bstep (se 2 (by rfl) ⟨909594, by rfl⟩ : syracuseStep 2425585 = 1819189) B1819189
theorem B1704739 : Blo 1008601 1704739 := bstep (se 1 (by rfl) ⟨1278554, by rfl⟩ : syracuseStep 1704739 = 2557109) B2557109
theorem B3408749 : Blo 1008601 3408749 := bstep (se 3 (by rfl) ⟨639140, by rfl⟩ : syracuseStep 3408749 = 1278281) B1278281
theorem B7668593 : Blo 1008601 7668593 := bstep (se 2 (by rfl) ⟨2875722, by rfl⟩ : syracuseStep 7668593 = 5751445) B5751445
theorem B2556785 : Blo 1008601 2556785 := bstep (se 2 (by rfl) ⟨958794, by rfl⟩ : syracuseStep 2556785 = 1917589) B1917589
theorem B3408803 : Blo 1008601 3408803 := bstep (se 1 (by rfl) ⟨2556602, by rfl⟩ : syracuseStep 3408803 = 5113205) B5113205
theorem B1704881 : Blo 1008601 1704881 := bstep (se 2 (by rfl) ⟨639330, by rfl⟩ : syracuseStep 1704881 = 1278661) B1278661
theorem B9700337 : Blo 1008601 9700337 := bstep (se 2 (by rfl) ⟨3637626, by rfl⟩ : syracuseStep 9700337 = 7275253) B7275253
theorem B5112881 : Blo 1008601 5112881 := bstep (se 2 (by rfl) ⟨1917330, by rfl⟩ : syracuseStep 5112881 = 3834661) B3834661
theorem B1705009 : Blo 1008601 1705009 := bstep (se 2 (by rfl) ⟨639378, by rfl⟩ : syracuseStep 1705009 = 1278757) B1278757
theorem B1705043 : Blo 1008601 1705043 := bstep (se 1 (by rfl) ⟨1278782, by rfl⟩ : syracuseStep 1705043 = 2557565) B2557565
theorem B1639523 : Blo 1008601 1639523 := bstep (se 1 (by rfl) ⟨1229642, by rfl⟩ : syracuseStep 1639523 = 2459285) B2459285
theorem B1279091 : Blo 1008601 1279091 := bstep (se 1 (by rfl) ⟨959318, by rfl⟩ : syracuseStep 1279091 = 1918637) B1918637
theorem B3409073 : Blo 1008601 3409073 := bstep (se 2 (by rfl) ⟨1278402, by rfl⟩ : syracuseStep 3409073 = 2556805) B2556805
theorem B1705171 : Blo 1008601 1705171 := bstep (se 1 (by rfl) ⟨1278878, by rfl⟩ : syracuseStep 1705171 = 2557757) B2557757
theorem B1213715 : Blo 1008601 1213715 := bstep (se 1 (by rfl) ⟨910286, by rfl⟩ : syracuseStep 1213715 = 1820573) B1820573
theorem B1705313 : Blo 1008601 1705313 := bstep (se 2 (by rfl) ⟨639492, by rfl⟩ : syracuseStep 1705313 = 1278985) B1278985
theorem B1705441 : Blo 1008601 1705441 := bstep (se 2 (by rfl) ⟨639540, by rfl⟩ : syracuseStep 1705441 = 1279081) B1279081
theorem B1639939 : Blo 1008601 1639939 := bstep (se 1 (by rfl) ⟨1229954, by rfl⟩ : syracuseStep 1639939 = 2459909) B2459909
theorem B1705475 : Blo 1008601 1705475 := bstep (se 1 (by rfl) ⟨1279106, by rfl⟩ : syracuseStep 1705475 = 2558213) B2558213
theorem B1705603 : Blo 1008601 1705603 := bstep (se 1 (by rfl) ⟨1279202, by rfl⟩ : syracuseStep 1705603 = 2558405) B2558405
theorem B2426545 : Blo 1008601 2426545 := bstep (se 2 (by rfl) ⟨909954, by rfl⟩ : syracuseStep 2426545 = 1819909) B1819909
theorem B3409613 : Blo 1008601 3409613 := bstep (se 3 (by rfl) ⟨639302, by rfl⟩ : syracuseStep 3409613 = 1278605) B1278605
theorem B3835619 : Blo 1008601 3835619 := bstep (se 1 (by rfl) ⟨2876714, by rfl⟩ : syracuseStep 3835619 = 5753429) B5753429
theorem B3835633 : Blo 1008601 3835633 := bstep (se 2 (by rfl) ⟨1438362, by rfl⟩ : syracuseStep 3835633 = 2876725) B2876725
theorem B3409667 : Blo 1008601 3409667 := bstep (se 1 (by rfl) ⟨2557250, by rfl⟩ : syracuseStep 3409667 = 5114501) B5114501
theorem B1705745 : Blo 1008601 1705745 := bstep (se 2 (by rfl) ⟨639654, by rfl⟩ : syracuseStep 1705745 = 1279309) B1279309
theorem B1279795 : Blo 1008601 1279795 := bstep (se 1 (by rfl) ⟨959846, by rfl⟩ : syracuseStep 1279795 = 1919693) B1919693
theorem B2557777 : Blo 1008601 2557777 := bstep (se 2 (by rfl) ⟨959166, by rfl⟩ : syracuseStep 2557777 = 1918333) B1918333
theorem B2918285 : Blo 1008601 2918285 := bstep (se 3 (by rfl) ⟨547178, by rfl⟩ : syracuseStep 2918285 = 1094357) B1094357
theorem B1705873 : Blo 1008601 1705873 := bstep (se 2 (by rfl) ⟨639702, by rfl⟩ : syracuseStep 1705873 = 1279405) B1279405
theorem B1279891 : Blo 1008601 1279891 := bstep (se 1 (by rfl) ⟨959918, by rfl⟩ : syracuseStep 1279891 = 1919837) B1919837
theorem B1869731 : Blo 1008601 1869731 := bstep (se 1 (by rfl) ⟨1402298, by rfl⟩ : syracuseStep 1869731 = 2804597) B2804597
theorem B1705907 : Blo 1008601 1705907 := bstep (se 1 (by rfl) ⟨1279430, by rfl⟩ : syracuseStep 1705907 = 2558861) B2558861
theorem B3409937 : Blo 1008601 3409937 := bstep (se 2 (by rfl) ⟨1278726, by rfl⟩ : syracuseStep 3409937 = 2557453) B2557453
theorem B1706035 : Blo 1008601 1706035 := bstep (se 1 (by rfl) ⟨1279526, by rfl⟩ : syracuseStep 1706035 = 2559053) B2559053
theorem B2558051 : Blo 1008601 2558051 := bstep (se 1 (by rfl) ⟨1918538, by rfl⟩ : syracuseStep 2558051 = 3837077) B3837077
theorem B1706177 : Blo 1008601 1706177 := bstep (se 2 (by rfl) ⟨639816, by rfl⟩ : syracuseStep 1706177 = 1279633) B1279633
theorem B2558243 : Blo 1008601 2558243 := bstep (se 1 (by rfl) ⟨1918682, by rfl⟩ : syracuseStep 2558243 = 3837365) B3837365
theorem B1706305 : Blo 1008601 1706305 := bstep (se 2 (by rfl) ⟨639864, by rfl⟩ : syracuseStep 1706305 = 1279729) B1279729
theorem B1706339 : Blo 1008601 1706339 := bstep (se 1 (by rfl) ⟨1279754, by rfl⟩ : syracuseStep 1706339 = 2559509) B2559509
theorem B1280387 : Blo 1008601 1280387 := bstep (se 1 (by rfl) ⟨960290, by rfl⟩ : syracuseStep 1280387 = 1920581) B1920581
theorem B5114339 : Blo 1008601 5114339 := bstep (se 1 (by rfl) ⟨3835754, by rfl⟩ : syracuseStep 5114339 = 7671509) B7671509
theorem B1706467 : Blo 1008601 1706467 := bstep (se 1 (by rfl) ⟨1279850, by rfl⟩ : syracuseStep 1706467 = 2559701) B2559701
theorem B4098545 : Blo 1008601 4098545 := bstep (se 2 (by rfl) ⟨1536954, by rfl⟩ : syracuseStep 4098545 = 3073909) B3073909
theorem B3410477 : Blo 1008601 3410477 := bstep (se 3 (by rfl) ⟨639464, by rfl⟩ : syracuseStep 3410477 = 1278929) B1278929
theorem B3410531 : Blo 1008601 3410531 := bstep (se 1 (by rfl) ⟨2557898, by rfl⟩ : syracuseStep 3410531 = 5115797) B5115797
theorem B1706609 : Blo 1008601 1706609 := bstep (se 2 (by rfl) ⟨639978, by rfl⟩ : syracuseStep 1706609 = 1279957) B1279957
theorem B3640049 : Blo 1008601 3640049 := bstep (se 2 (by rfl) ⟨1365018, by rfl⟩ : syracuseStep 3640049 = 2730037) B2730037
theorem B1706737 : Blo 1008601 1706737 := bstep (se 2 (by rfl) ⟨640026, by rfl⟩ : syracuseStep 1706737 = 1280053) B1280053
theorem B1706771 : Blo 1008601 1706771 := bstep (se 1 (by rfl) ⟨1280078, by rfl⟩ : syracuseStep 1706771 = 2560157) B2560157
theorem B3410801 : Blo 1008601 3410801 := bstep (se 2 (by rfl) ⟨1279050, by rfl⟩ : syracuseStep 3410801 = 2558101) B2558101
theorem B1706899 : Blo 1008601 1706899 := bstep (se 1 (by rfl) ⟨1280174, by rfl⟩ : syracuseStep 1706899 = 2560349) B2560349
theorem B1707041 : Blo 1008601 1707041 := bstep (se 2 (by rfl) ⟨640140, by rfl⟩ : syracuseStep 1707041 = 1280281) B1280281
theorem B1281091 : Blo 1008601 1281091 := bstep (se 1 (by rfl) ⟨960818, by rfl⟩ : syracuseStep 1281091 = 1921637) B1921637
theorem B6229133 : Blo 1008601 6229133 := bstep (se 3 (by rfl) ⟨1167962, by rfl⟩ : syracuseStep 6229133 = 2335925) B2335925
theorem B1707169 : Blo 1008601 1707169 := bstep (se 2 (by rfl) ⟨640188, by rfl⟩ : syracuseStep 1707169 = 1280377) B1280377
theorem B3837091 : Blo 1008601 3837091 := bstep (se 1 (by rfl) ⟨2877818, by rfl⟩ : syracuseStep 3837091 = 5755637) B5755637
theorem B1281187 : Blo 1008601 1281187 := bstep (se 1 (by rfl) ⟨960890, by rfl⟩ : syracuseStep 1281187 = 1921781) B1921781
theorem B1707203 : Blo 1008601 1707203 := bstep (se 1 (by rfl) ⟨1280402, by rfl⟩ : syracuseStep 1707203 = 2560805) B2560805
theorem B2559185 : Blo 1008601 2559185 := bstep (se 2 (by rfl) ⟨959694, by rfl⟩ : syracuseStep 2559185 = 1919389) B1919389
theorem B2559235 : Blo 1008601 2559235 := bstep (se 1 (by rfl) ⟨1919426, by rfl⟩ : syracuseStep 2559235 = 3838853) B3838853
theorem B5115149 : Blo 1008601 5115149 := bstep (se 3 (by rfl) ⟨959090, by rfl⟩ : syracuseStep 5115149 = 1918181) B1918181
theorem B1707331 : Blo 1008601 1707331 := bstep (se 1 (by rfl) ⟨1280498, by rfl⟩ : syracuseStep 1707331 = 2560997) B2560997
theorem B3411341 : Blo 1008601 3411341 := bstep (se 3 (by rfl) ⟨639626, by rfl⟩ : syracuseStep 3411341 = 1279253) B1279253
theorem B2559377 : Blo 1008601 2559377 := bstep (se 2 (by rfl) ⟨959766, by rfl⟩ : syracuseStep 2559377 = 1919533) B1919533
theorem B11505077 : Blo 1008601 11505077 := bstep (se 5 (by rfl) ⟨539300, by rfl⟩ : syracuseStep 11505077 = 1078601) B1078601
theorem B3411395 : Blo 1008601 3411395 := bstep (se 1 (by rfl) ⟨2558546, by rfl⟩ : syracuseStep 3411395 = 5117093) B5117093
theorem B1707473 : Blo 1008601 1707473 := bstep (se 2 (by rfl) ⟨640302, by rfl⟩ : syracuseStep 1707473 = 1280605) B1280605
theorem B1707601 : Blo 1008601 1707601 := bstep (se 2 (by rfl) ⟨640350, by rfl⟩ : syracuseStep 1707601 = 1280701) B1280701
theorem B1707635 : Blo 1008601 1707635 := bstep (se 1 (by rfl) ⟨1280726, by rfl⟩ : syracuseStep 1707635 = 2561453) B2561453
theorem B3411665 : Blo 1008601 3411665 := bstep (se 2 (by rfl) ⟨1279374, by rfl⟩ : syracuseStep 3411665 = 2558749) B2558749
theorem B1707763 : Blo 1008601 1707763 := bstep (se 1 (by rfl) ⟨1280822, by rfl⟩ : syracuseStep 1707763 = 2561645) B2561645
theorem B1216243 : Blo 1008601 1216243 := bstep (se 1 (by rfl) ⟨912182, by rfl⟩ : syracuseStep 1216243 = 1824365) B1824365
theorem B1216291 : Blo 1008601 1216291 := bstep (se 1 (by rfl) ⟨912218, by rfl⟩ : syracuseStep 1216291 = 1824437) B1824437
theorem B1707905 : Blo 1008601 1707905 := bstep (se 2 (by rfl) ⟨640464, by rfl⟩ : syracuseStep 1707905 = 1280929) B1280929
theorem B1216387 : Blo 1008601 1216387 := bstep (se 1 (by rfl) ⟨912290, by rfl⟩ : syracuseStep 1216387 = 1824581) B1824581
theorem B1708033 : Blo 1008601 1708033 := bstep (se 2 (by rfl) ⟨640512, by rfl⟩ : syracuseStep 1708033 = 1281025) B1281025
theorem B1708067 : Blo 1008601 1708067 := bstep (se 1 (by rfl) ⟨1281050, by rfl⟩ : syracuseStep 1708067 = 2562101) B2562101
theorem B2592881 : Blo 1008601 2592881 := bstep (se 2 (by rfl) ⟨972330, by rfl⟩ : syracuseStep 2592881 = 1944661) B1944661
theorem B1708195 : Blo 1008601 1708195 := bstep (se 1 (by rfl) ⟨1281146, by rfl⟩ : syracuseStep 1708195 = 2562293) B2562293
theorem B3281123 : Blo 1008601 3281123 := bstep (se 1 (by rfl) ⟨2460842, by rfl⟩ : syracuseStep 3281123 = 4921685) B4921685
theorem B3412205 : Blo 1008601 3412205 := bstep (se 3 (by rfl) ⟨639788, by rfl⟩ : syracuseStep 3412205 = 1279577) B1279577
theorem B1773827 : Blo 1008601 1773827 := bstep (se 1 (by rfl) ⟨1330370, by rfl⟩ : syracuseStep 1773827 = 2660741) B2660741
theorem B3412259 : Blo 1008601 3412259 := bstep (se 1 (by rfl) ⟨2559194, by rfl⟩ : syracuseStep 3412259 = 5118389) B5118389
theorem B1708337 : Blo 1008601 1708337 := bstep (se 2 (by rfl) ⟨640626, by rfl⟩ : syracuseStep 1708337 = 1281253) B1281253
theorem B2560369 : Blo 1008601 2560369 := bstep (se 2 (by rfl) ⟨960138, by rfl⟩ : syracuseStep 2560369 = 1920277) B1920277
theorem B1708465 : Blo 1008601 1708465 := bstep (se 2 (by rfl) ⟨640674, by rfl⟩ : syracuseStep 1708465 = 1281349) B1281349
theorem B1151443 : Blo 1008601 1151443 := bstep (se 1 (by rfl) ⟨863582, by rfl⟩ : syracuseStep 1151443 = 1727165) B1727165
theorem B1708499 : Blo 1008601 1708499 := bstep (se 1 (by rfl) ⟨1281374, by rfl⟩ : syracuseStep 1708499 = 2562749) B2562749
theorem B3281411 : Blo 1008601 3281411 := bstep (se 1 (by rfl) ⟨2461058, by rfl⟩ : syracuseStep 3281411 = 4922117) B4922117
theorem B3412529 : Blo 1008601 3412529 := bstep (se 2 (by rfl) ⟨1279698, by rfl⟩ : syracuseStep 3412529 = 2559397) B2559397
theorem B2429507 : Blo 1008601 2429507 := bstep (se 1 (by rfl) ⟨1822130, by rfl⟩ : syracuseStep 2429507 = 3644261) B3644261
theorem B1708627 : Blo 1008601 1708627 := bstep (se 1 (by rfl) ⟨1281470, by rfl⟩ : syracuseStep 1708627 = 2562941) B2562941
theorem B2560643 : Blo 1008601 2560643 := bstep (se 1 (by rfl) ⟨1920482, by rfl⟩ : syracuseStep 2560643 = 3840965) B3840965
theorem B3117731 : Blo 1008601 3117731 := bstep (se 1 (by rfl) ⟨2338298, by rfl⟩ : syracuseStep 3117731 = 4676597) B4676597
theorem B2921197 : Blo 1008601 2921197 := bstep (se 3 (by rfl) ⟨547724, by rfl⟩ : syracuseStep 2921197 = 1095449) B1095449
theorem B2560835 : Blo 1008601 2560835 := bstep (se 1 (by rfl) ⟨1920626, by rfl⟩ : syracuseStep 2560835 = 3841253) B3841253
theorem B2429891 : Blo 1008601 2429891 := bstep (se 1 (by rfl) ⟨1822418, by rfl⟩ : syracuseStep 2429891 = 3644837) B3644837
theorem B3413069 : Blo 1008601 3413069 := bstep (se 3 (by rfl) ⟨639950, by rfl⟩ : syracuseStep 3413069 = 1279901) B1279901
theorem B3413123 : Blo 1008601 3413123 := bstep (se 1 (by rfl) ⟨2559842, by rfl⟩ : syracuseStep 3413123 = 5119685) B5119685
theorem B2430179 : Blo 1008601 2430179 := bstep (se 1 (by rfl) ⟨1822634, by rfl⟩ : syracuseStep 2430179 = 3645269) B3645269
theorem B2921795 : Blo 1008601 2921795 := bstep (se 1 (by rfl) ⟨2191346, by rfl⟩ : syracuseStep 2921795 = 4382693) B4382693
theorem B3839309 : Blo 1008601 3839309 := bstep (se 3 (by rfl) ⟨719870, by rfl⟩ : syracuseStep 3839309 = 1439741) B1439741
theorem B3413393 : Blo 1008601 3413393 := bstep (se 2 (by rfl) ⟨1280022, by rfl⟩ : syracuseStep 3413393 = 2560045) B2560045
theorem B1512929 : Blo 1008601 1512929 := bstep (se 2 (by rfl) ⟨567348, by rfl⟩ : syracuseStep 1512929 = 1134697) B1134697
theorem B1512947 : Blo 1008601 1512947 := bstep (se 1 (by rfl) ⟨1134710, by rfl⟩ : syracuseStep 1512947 = 2269421) B2269421
theorem B1512977 : Blo 1008601 1512977 := bstep (se 2 (by rfl) ⟨567366, by rfl⟩ : syracuseStep 1512977 = 1134733) B1134733
theorem B1512995 : Blo 1008601 1512995 := bstep (se 1 (by rfl) ⟨1134746, by rfl⟩ : syracuseStep 1512995 = 2269493) B2269493
theorem B1513025 : Blo 1008601 1513025 := bstep (se 2 (by rfl) ⟨567384, by rfl⟩ : syracuseStep 1513025 = 1134769) B1134769
theorem B1513043 : Blo 1008601 1513043 := bstep (se 1 (by rfl) ⟨1134782, by rfl⟩ : syracuseStep 1513043 = 2269565) B2269565
theorem B1513073 : Blo 1008601 1513073 := bstep (se 2 (by rfl) ⟨567402, by rfl⟩ : syracuseStep 1513073 = 1134805) B1134805
theorem B1513091 : Blo 1008601 1513091 := bstep (se 1 (by rfl) ⟨1134818, by rfl⟩ : syracuseStep 1513091 = 2269637) B2269637
theorem B1513121 : Blo 1008601 1513121 := bstep (se 2 (by rfl) ⟨567420, by rfl⟩ : syracuseStep 1513121 = 1134841) B1134841
theorem B2430641 : Blo 1008601 2430641 := bstep (se 2 (by rfl) ⟨911490, by rfl⟩ : syracuseStep 2430641 = 1822981) B1822981
theorem B1513139 : Blo 1008601 1513139 := bstep (se 1 (by rfl) ⟨1134854, by rfl⟩ : syracuseStep 1513139 = 2269709) B2269709
theorem B1513169 : Blo 1008601 1513169 := bstep (se 2 (by rfl) ⟨567438, by rfl⟩ : syracuseStep 1513169 = 1134877) B1134877
theorem B1513187 : Blo 1008601 1513187 := bstep (se 1 (by rfl) ⟨1134890, by rfl⟩ : syracuseStep 1513187 = 2269781) B2269781
theorem B2561777 : Blo 1008601 2561777 := bstep (se 2 (by rfl) ⟨960666, by rfl⟩ : syracuseStep 2561777 = 1921333) B1921333
theorem B1513217 : Blo 1008601 1513217 := bstep (se 2 (by rfl) ⟨567456, by rfl⟩ : syracuseStep 1513217 = 1134913) B1134913
theorem B1513235 : Blo 1008601 1513235 := bstep (se 1 (by rfl) ⟨1134926, by rfl⟩ : syracuseStep 1513235 = 2269853) B2269853
theorem B2561827 : Blo 1008601 2561827 := bstep (se 1 (by rfl) ⟨1921370, by rfl⟩ : syracuseStep 2561827 = 3842741) B3842741
theorem B1513265 : Blo 1008601 1513265 := bstep (se 2 (by rfl) ⟨567474, by rfl⟩ : syracuseStep 1513265 = 1134949) B1134949
theorem B5183281 : Blo 1008601 5183281 := bstep (se 2 (by rfl) ⟨1943730, by rfl⟩ : syracuseStep 5183281 = 3887461) B3887461
theorem B1513283 : Blo 1008601 1513283 := bstep (se 1 (by rfl) ⟨1134962, by rfl⟩ : syracuseStep 1513283 = 2269925) B2269925
theorem B1513313 : Blo 1008601 1513313 := bstep (se 2 (by rfl) ⟨567492, by rfl⟩ : syracuseStep 1513313 = 1134985) B1134985
theorem B1513331 : Blo 1008601 1513331 := bstep (se 1 (by rfl) ⟨1134998, by rfl⟩ : syracuseStep 1513331 = 2269997) B2269997
theorem B1513361 : Blo 1008601 1513361 := bstep (se 2 (by rfl) ⟨567510, by rfl⟩ : syracuseStep 1513361 = 1135021) B1135021
theorem B1513379 : Blo 1008601 1513379 := bstep (se 1 (by rfl) ⟨1135034, by rfl⟩ : syracuseStep 1513379 = 2270069) B2270069
theorem B3413933 : Blo 1008601 3413933 := bstep (se 3 (by rfl) ⟨640112, by rfl⟩ : syracuseStep 3413933 = 1280225) B1280225
theorem B2561969 : Blo 1008601 2561969 := bstep (se 2 (by rfl) ⟨960738, by rfl⟩ : syracuseStep 2561969 = 1921477) B1921477
theorem B1513409 : Blo 1008601 1513409 := bstep (se 2 (by rfl) ⟨567528, by rfl⟩ : syracuseStep 1513409 = 1135057) B1135057
theorem B24549317 : Blo 1008601 24549317 := bstep (se 4 (by rfl) ⟨2301498, by rfl⟩ : syracuseStep 24549317 = 4602997) B4602997
theorem B1513427 : Blo 1008601 1513427 := bstep (se 1 (by rfl) ⟨1135070, by rfl⟩ : syracuseStep 1513427 = 2270141) B2270141
theorem B3413987 : Blo 1008601 3413987 := bstep (se 1 (by rfl) ⟨2560490, by rfl⟩ : syracuseStep 3413987 = 5120981) B5120981
theorem B1513457 : Blo 1008601 1513457 := bstep (se 2 (by rfl) ⟨567546, by rfl⟩ : syracuseStep 1513457 = 1135093) B1135093
theorem B1513475 : Blo 1008601 1513475 := bstep (se 1 (by rfl) ⟨1135106, by rfl⟩ : syracuseStep 1513475 = 2270213) B2270213
theorem B1513505 : Blo 1008601 1513505 := bstep (se 2 (by rfl) ⟨567564, by rfl⟩ : syracuseStep 1513505 = 1135129) B1135129
theorem B1513523 : Blo 1008601 1513523 := bstep (se 1 (by rfl) ⟨1135142, by rfl⟩ : syracuseStep 1513523 = 2270285) B2270285
theorem B1513553 : Blo 1008601 1513553 := bstep (se 2 (by rfl) ⟨567582, by rfl⟩ : syracuseStep 1513553 = 1135165) B1135165
theorem B1513571 : Blo 1008601 1513571 := bstep (se 1 (by rfl) ⟨1135178, by rfl⟩ : syracuseStep 1513571 = 2270357) B2270357
theorem B5118065 : Blo 1008601 5118065 := bstep (se 2 (by rfl) ⟨1919274, by rfl⟩ : syracuseStep 5118065 = 3838549) B3838549
theorem B1513601 : Blo 1008601 1513601 := bstep (se 2 (by rfl) ⟨567600, by rfl⟩ : syracuseStep 1513601 = 1135201) B1135201
theorem B1513619 : Blo 1008601 1513619 := bstep (se 1 (by rfl) ⟨1135214, by rfl⟩ : syracuseStep 1513619 = 2270429) B2270429
theorem B1513649 : Blo 1008601 1513649 := bstep (se 2 (by rfl) ⟨567618, by rfl⟩ : syracuseStep 1513649 = 1135237) B1135237
theorem B1513667 : Blo 1008601 1513667 := bstep (se 1 (by rfl) ⟨1135250, by rfl⟩ : syracuseStep 1513667 = 2270501) B2270501
theorem B1513697 : Blo 1008601 1513697 := bstep (se 2 (by rfl) ⟨567636, by rfl⟩ : syracuseStep 1513697 = 1135273) B1135273
theorem B3414257 : Blo 1008601 3414257 := bstep (se 2 (by rfl) ⟨1280346, by rfl⟩ : syracuseStep 3414257 = 2560693) B2560693
theorem B1513715 : Blo 1008601 1513715 := bstep (se 1 (by rfl) ⟨1135286, by rfl⟩ : syracuseStep 1513715 = 2270573) B2270573
theorem B1513745 : Blo 1008601 1513745 := bstep (se 2 (by rfl) ⟨567654, by rfl⟩ : syracuseStep 1513745 = 1135309) B1135309
theorem B1513763 : Blo 1008601 1513763 := bstep (se 1 (by rfl) ⟨1135322, by rfl⟩ : syracuseStep 1513763 = 2270645) B2270645
theorem B1513793 : Blo 1008601 1513793 := bstep (se 2 (by rfl) ⟨567672, by rfl⟩ : syracuseStep 1513793 = 1135345) B1135345
theorem B2431313 : Blo 1008601 2431313 := bstep (se 2 (by rfl) ⟨911742, by rfl⟩ : syracuseStep 2431313 = 1823485) B1823485
theorem B1513811 : Blo 1008601 1513811 := bstep (se 1 (by rfl) ⟨1135358, by rfl⟩ : syracuseStep 1513811 = 2270717) B2270717
theorem B1513841 : Blo 1008601 1513841 := bstep (se 2 (by rfl) ⟨567690, by rfl⟩ : syracuseStep 1513841 = 1135381) B1135381
theorem B1513859 : Blo 1008601 1513859 := bstep (se 1 (by rfl) ⟨1135394, by rfl⟩ : syracuseStep 1513859 = 2270789) B2270789
theorem B1513889 : Blo 1008601 1513889 := bstep (se 2 (by rfl) ⟨567708, by rfl⟩ : syracuseStep 1513889 = 1135417) B1135417
theorem B1513907 : Blo 1008601 1513907 := bstep (se 1 (by rfl) ⟨1135430, by rfl⟩ : syracuseStep 1513907 = 2270861) B2270861
theorem B1513937 : Blo 1008601 1513937 := bstep (se 2 (by rfl) ⟨567726, by rfl⟩ : syracuseStep 1513937 = 1135453) B1135453
theorem B1513955 : Blo 1008601 1513955 := bstep (se 1 (by rfl) ⟨1135466, by rfl⟩ : syracuseStep 1513955 = 2270933) B2270933
theorem B1513985 : Blo 1008601 1513985 := bstep (se 2 (by rfl) ⟨567744, by rfl⟩ : syracuseStep 1513985 = 1135489) B1135489
theorem B1514003 : Blo 1008601 1514003 := bstep (se 1 (by rfl) ⟨1135502, by rfl⟩ : syracuseStep 1514003 = 2271005) B2271005
theorem B1514033 : Blo 1008601 1514033 := bstep (se 2 (by rfl) ⟨567762, by rfl⟩ : syracuseStep 1514033 = 1135525) B1135525
theorem B1514051 : Blo 1008601 1514051 := bstep (se 1 (by rfl) ⟨1135538, by rfl⟩ : syracuseStep 1514051 = 2271077) B2271077
theorem B1514081 : Blo 1008601 1514081 := bstep (se 2 (by rfl) ⟨567780, by rfl⟩ : syracuseStep 1514081 = 1135561) B1135561
theorem B1514099 : Blo 1008601 1514099 := bstep (se 1 (by rfl) ⟨1135574, by rfl⟩ : syracuseStep 1514099 = 2271149) B2271149
theorem B1514129 : Blo 1008601 1514129 := bstep (se 2 (by rfl) ⟨567798, by rfl⟩ : syracuseStep 1514129 = 1135597) B1135597
theorem B1514147 : Blo 1008601 1514147 := bstep (se 1 (by rfl) ⟨1135610, by rfl⟩ : syracuseStep 1514147 = 2271221) B2271221
theorem B1514177 : Blo 1008601 1514177 := bstep (se 2 (by rfl) ⟨567816, by rfl⟩ : syracuseStep 1514177 = 1135633) B1135633
theorem B1514195 : Blo 1008601 1514195 := bstep (se 1 (by rfl) ⟨1135646, by rfl⟩ : syracuseStep 1514195 = 2271293) B2271293
theorem B9116387 : Blo 1008601 9116387 := bstep (se 1 (by rfl) ⟨6837290, by rfl⟩ : syracuseStep 9116387 = 13674581) B13674581
theorem B1514225 : Blo 1008601 1514225 := bstep (se 2 (by rfl) ⟨567834, by rfl⟩ : syracuseStep 1514225 = 1135669) B1135669
theorem B1514243 : Blo 1008601 1514243 := bstep (se 1 (by rfl) ⟨1135682, by rfl⟩ : syracuseStep 1514243 = 2271365) B2271365
theorem B5184269 : Blo 1008601 5184269 := bstep (se 3 (by rfl) ⟨972050, by rfl⟩ : syracuseStep 5184269 = 1944101) B1944101
theorem B3414797 : Blo 1008601 3414797 := bstep (se 3 (by rfl) ⟨640274, by rfl⟩ : syracuseStep 3414797 = 1280549) B1280549
theorem B1153811 : Blo 1008601 1153811 := bstep (se 1 (by rfl) ⟨865358, by rfl⟩ : syracuseStep 1153811 = 1730717) B1730717
theorem B1514273 : Blo 1008601 1514273 := bstep (se 2 (by rfl) ⟨567852, by rfl⟩ : syracuseStep 1514273 = 1135705) B1135705
theorem B1514291 : Blo 1008601 1514291 := bstep (se 1 (by rfl) ⟨1135718, by rfl⟩ : syracuseStep 1514291 = 2271437) B2271437
theorem B3414851 : Blo 1008601 3414851 := bstep (se 1 (by rfl) ⟨2561138, by rfl⟩ : syracuseStep 3414851 = 5122277) B5122277
theorem B1514321 : Blo 1008601 1514321 := bstep (se 2 (by rfl) ⟨567870, by rfl⟩ : syracuseStep 1514321 = 1135741) B1135741
theorem B1514339 : Blo 1008601 1514339 := bstep (se 1 (by rfl) ⟨1135754, by rfl⟩ : syracuseStep 1514339 = 2271509) B2271509
theorem B1514369 : Blo 1008601 1514369 := bstep (se 2 (by rfl) ⟨567888, by rfl⟩ : syracuseStep 1514369 = 1135777) B1135777
theorem B2562961 : Blo 1008601 2562961 := bstep (se 2 (by rfl) ⟨961110, by rfl⟩ : syracuseStep 2562961 = 1922221) B1922221
theorem B1514387 : Blo 1008601 1514387 := bstep (se 1 (by rfl) ⟨1135790, by rfl⟩ : syracuseStep 1514387 = 2271581) B2271581
theorem B1514417 : Blo 1008601 1514417 := bstep (se 2 (by rfl) ⟨567906, by rfl⟩ : syracuseStep 1514417 = 1135813) B1135813
theorem B1514435 : Blo 1008601 1514435 := bstep (se 1 (by rfl) ⟨1135826, by rfl⟩ : syracuseStep 1514435 = 2271653) B2271653
theorem B1514465 : Blo 1008601 1514465 := bstep (se 2 (by rfl) ⟨567924, by rfl⟩ : syracuseStep 1514465 = 1135849) B1135849
theorem B1514483 : Blo 1008601 1514483 := bstep (se 1 (by rfl) ⟨1135862, by rfl⟩ : syracuseStep 1514483 = 2271725) B2271725
theorem B1514513 : Blo 1008601 1514513 := bstep (se 2 (by rfl) ⟨567942, by rfl⟩ : syracuseStep 1514513 = 1135885) B1135885
theorem B1514531 : Blo 1008601 1514531 := bstep (se 1 (by rfl) ⟨1135898, by rfl⟩ : syracuseStep 1514531 = 2271797) B2271797
theorem B1514561 : Blo 1008601 1514561 := bstep (se 2 (by rfl) ⟨567960, by rfl⟩ : syracuseStep 1514561 = 1135921) B1135921
theorem B3415121 : Blo 1008601 3415121 := bstep (se 2 (by rfl) ⟨1280670, by rfl⟩ : syracuseStep 3415121 = 2561341) B2561341
theorem B1514579 : Blo 1008601 1514579 := bstep (se 1 (by rfl) ⟨1135934, by rfl⟩ : syracuseStep 1514579 = 2271869) B2271869
theorem B1514609 : Blo 1008601 1514609 := bstep (se 2 (by rfl) ⟨567978, by rfl⟩ : syracuseStep 1514609 = 1135957) B1135957
theorem B1514627 : Blo 1008601 1514627 := bstep (se 1 (by rfl) ⟨1135970, by rfl⟩ : syracuseStep 1514627 = 2271941) B2271941
theorem B1514657 : Blo 1008601 1514657 := bstep (se 2 (by rfl) ⟨567996, by rfl⟩ : syracuseStep 1514657 = 1135993) B1135993
theorem B1514675 : Blo 1008601 1514675 := bstep (se 1 (by rfl) ⟨1136006, by rfl⟩ : syracuseStep 1514675 = 2272013) B2272013
theorem B1514705 : Blo 1008601 1514705 := bstep (se 2 (by rfl) ⟨568014, by rfl⟩ : syracuseStep 1514705 = 1136029) B1136029
theorem B5250275 : Blo 1008601 5250275 := bstep (se 1 (by rfl) ⟨3937706, by rfl⟩ : syracuseStep 5250275 = 7875413) B7875413
theorem B1514723 : Blo 1008601 1514723 := bstep (se 1 (by rfl) ⟨1136042, by rfl⟩ : syracuseStep 1514723 = 2272085) B2272085
theorem B1514753 : Blo 1008601 1514753 := bstep (se 2 (by rfl) ⟨568032, by rfl⟩ : syracuseStep 1514753 = 1136065) B1136065
theorem B1514771 : Blo 1008601 1514771 := bstep (se 1 (by rfl) ⟨1136078, by rfl⟩ : syracuseStep 1514771 = 2272157) B2272157
theorem B1514801 : Blo 1008601 1514801 := bstep (se 2 (by rfl) ⟨568050, by rfl⟩ : syracuseStep 1514801 = 1136101) B1136101
theorem B1514819 : Blo 1008601 1514819 := bstep (se 1 (by rfl) ⟨1136114, by rfl⟩ : syracuseStep 1514819 = 2272229) B2272229
theorem B1514849 : Blo 1008601 1514849 := bstep (se 2 (by rfl) ⟨568068, by rfl⟩ : syracuseStep 1514849 = 1136137) B1136137
theorem B10919281 : Blo 1008601 10919281 := bstep (se 2 (by rfl) ⟨4094730, by rfl⟩ : syracuseStep 10919281 = 8189461) B8189461
theorem B1514867 : Blo 1008601 1514867 := bstep (se 1 (by rfl) ⟨1136150, by rfl⟩ : syracuseStep 1514867 = 2272301) B2272301
theorem B1514897 : Blo 1008601 1514897 := bstep (se 2 (by rfl) ⟨568086, by rfl⟩ : syracuseStep 1514897 = 1136173) B1136173
theorem B1383841 : Blo 1008601 1383841 := bstep (se 2 (by rfl) ⟨518940, by rfl⟩ : syracuseStep 1383841 = 1037881) B1037881
theorem B1514915 : Blo 1008601 1514915 := bstep (se 1 (by rfl) ⟨1136186, by rfl⟩ : syracuseStep 1514915 = 2272373) B2272373
theorem B1514945 : Blo 1008601 1514945 := bstep (se 2 (by rfl) ⟨568104, by rfl⟩ : syracuseStep 1514945 = 1136209) B1136209
theorem B1514963 : Blo 1008601 1514963 := bstep (se 1 (by rfl) ⟨1136222, by rfl⟩ : syracuseStep 1514963 = 2272445) B2272445
theorem B2301425 : Blo 1008601 2301425 := bstep (se 2 (by rfl) ⟨863034, by rfl⟩ : syracuseStep 2301425 = 1726069) B1726069
theorem B1514993 : Blo 1008601 1514993 := bstep (se 2 (by rfl) ⟨568122, by rfl⟩ : syracuseStep 1514993 = 1136245) B1136245
theorem B1515011 : Blo 1008601 1515011 := bstep (se 1 (by rfl) ⟨1136258, by rfl⟩ : syracuseStep 1515011 = 2272517) B2272517
theorem B1515041 : Blo 1008601 1515041 := bstep (se 2 (by rfl) ⟨568140, by rfl⟩ : syracuseStep 1515041 = 1136281) B1136281
theorem B5119523 : Blo 1008601 5119523 := bstep (se 1 (by rfl) ⟨3839642, by rfl⟩ : syracuseStep 5119523 = 7679285) B7679285
theorem B1515059 : Blo 1008601 1515059 := bstep (se 1 (by rfl) ⟨1136294, by rfl⟩ : syracuseStep 1515059 = 2272589) B2272589
theorem B1515089 : Blo 1008601 1515089 := bstep (se 2 (by rfl) ⟨568158, by rfl⟩ : syracuseStep 1515089 = 1136317) B1136317
theorem B1515107 : Blo 1008601 1515107 := bstep (se 1 (by rfl) ⟨1136330, by rfl⟩ : syracuseStep 1515107 = 2272661) B2272661
theorem B3415661 : Blo 1008601 3415661 := bstep (se 3 (by rfl) ⟨640436, by rfl⟩ : syracuseStep 3415661 = 1280873) B1280873
theorem B1515137 : Blo 1008601 1515137 := bstep (se 2 (by rfl) ⟨568176, by rfl⟩ : syracuseStep 1515137 = 1136353) B1136353
theorem B2301571 : Blo 1008601 2301571 := bstep (se 1 (by rfl) ⟨1726178, by rfl⟩ : syracuseStep 2301571 = 3452357) B3452357
theorem B1515155 : Blo 1008601 1515155 := bstep (se 1 (by rfl) ⟨1136366, by rfl⟩ : syracuseStep 1515155 = 2272733) B2272733
theorem B3415715 : Blo 1008601 3415715 := bstep (se 1 (by rfl) ⟨2561786, by rfl⟩ : syracuseStep 3415715 = 5123573) B5123573
theorem B1515185 : Blo 1008601 1515185 := bstep (se 2 (by rfl) ⟨568194, by rfl⟩ : syracuseStep 1515185 = 1136389) B1136389
theorem B1515203 : Blo 1008601 1515203 := bstep (se 1 (by rfl) ⟨1136402, by rfl⟩ : syracuseStep 1515203 = 2272805) B2272805
theorem B1515233 : Blo 1008601 1515233 := bstep (se 2 (by rfl) ⟨568212, by rfl⟩ : syracuseStep 1515233 = 1136425) B1136425
theorem B7282403 : Blo 1008601 7282403 := bstep (se 1 (by rfl) ⟨5461802, by rfl⟩ : syracuseStep 7282403 = 10923605) B10923605
theorem B1515251 : Blo 1008601 1515251 := bstep (se 1 (by rfl) ⟨1136438, by rfl⟩ : syracuseStep 1515251 = 2272877) B2272877
theorem B1515281 : Blo 1008601 1515281 := bstep (se 2 (by rfl) ⟨568230, by rfl⟩ : syracuseStep 1515281 = 1136461) B1136461
theorem B1515299 : Blo 1008601 1515299 := bstep (se 1 (by rfl) ⟨1136474, by rfl⟩ : syracuseStep 1515299 = 2272949) B2272949
theorem B1515329 : Blo 1008601 1515329 := bstep (se 2 (by rfl) ⟨568248, by rfl⟩ : syracuseStep 1515329 = 1136497) B1136497
theorem B1515347 : Blo 1008601 1515347 := bstep (se 1 (by rfl) ⟨1136510, by rfl⟩ : syracuseStep 1515347 = 2273021) B2273021
theorem B1515377 : Blo 1008601 1515377 := bstep (se 2 (by rfl) ⟨568266, by rfl⟩ : syracuseStep 1515377 = 1136533) B1136533
theorem B1515395 : Blo 1008601 1515395 := bstep (se 1 (by rfl) ⟨1136546, by rfl⟩ : syracuseStep 1515395 = 2273093) B2273093
theorem B1515425 : Blo 1008601 1515425 := bstep (se 2 (by rfl) ⟨568284, by rfl⟩ : syracuseStep 1515425 = 1136569) B1136569
theorem B3415985 : Blo 1008601 3415985 := bstep (se 2 (by rfl) ⟨1280994, by rfl⟩ : syracuseStep 3415985 = 2561989) B2561989
theorem B1515443 : Blo 1008601 1515443 := bstep (se 1 (by rfl) ⟨1136582, by rfl⟩ : syracuseStep 1515443 = 2273165) B2273165
theorem B2465731 : Blo 1008601 2465731 := bstep (se 1 (by rfl) ⟨1849298, by rfl⟩ : syracuseStep 2465731 = 3698597) B3698597
theorem B1515473 : Blo 1008601 1515473 := bstep (se 2 (by rfl) ⟨568302, by rfl⟩ : syracuseStep 1515473 = 1136605) B1136605
theorem B1515491 : Blo 1008601 1515491 := bstep (se 1 (by rfl) ⟨1136618, by rfl⟩ : syracuseStep 1515491 = 2273237) B2273237
theorem B1515521 : Blo 1008601 1515521 := bstep (se 2 (by rfl) ⟨568320, by rfl⟩ : syracuseStep 1515521 = 1136641) B1136641
theorem B1515539 : Blo 1008601 1515539 := bstep (se 1 (by rfl) ⟨1136654, by rfl⟩ : syracuseStep 1515539 = 2273309) B2273309
theorem B1515569 : Blo 1008601 1515569 := bstep (se 2 (by rfl) ⟨568338, by rfl⟩ : syracuseStep 1515569 = 1136677) B1136677
theorem B1515587 : Blo 1008601 1515587 := bstep (se 1 (by rfl) ⟨1136690, by rfl⟩ : syracuseStep 1515587 = 2273381) B2273381
theorem B1515617 : Blo 1008601 1515617 := bstep (se 2 (by rfl) ⟨568356, by rfl⟩ : syracuseStep 1515617 = 1136713) B1136713
theorem B1515635 : Blo 1008601 1515635 := bstep (se 1 (by rfl) ⟨1136726, by rfl⟩ : syracuseStep 1515635 = 2273453) B2273453
theorem B1515665 : Blo 1008601 1515665 := bstep (se 2 (by rfl) ⟨568374, by rfl⟩ : syracuseStep 1515665 = 1136749) B1136749
theorem B1515683 : Blo 1008601 1515683 := bstep (se 1 (by rfl) ⟨1136762, by rfl⟩ : syracuseStep 1515683 = 2273525) B2273525
theorem B3842225 : Blo 1008601 3842225 := bstep (se 2 (by rfl) ⟨1440834, by rfl⟩ : syracuseStep 3842225 = 2881669) B2881669
theorem B1515713 : Blo 1008601 1515713 := bstep (se 2 (by rfl) ⟨568392, by rfl⟩ : syracuseStep 1515713 = 1136785) B1136785
theorem B1515731 : Blo 1008601 1515731 := bstep (se 1 (by rfl) ⟨1136798, by rfl⟩ : syracuseStep 1515731 = 2273597) B2273597
theorem B1515761 : Blo 1008601 1515761 := bstep (se 2 (by rfl) ⟨568410, by rfl⟩ : syracuseStep 1515761 = 1136821) B1136821
theorem B1515779 : Blo 1008601 1515779 := bstep (se 1 (by rfl) ⟨1136834, by rfl⟩ : syracuseStep 1515779 = 2273669) B2273669
theorem B2269457 : Blo 1008601 2269457 := bstep (se 2 (by rfl) ⟨851046, by rfl⟩ : syracuseStep 2269457 = 1702093) B1702093
theorem B1515809 : Blo 1008601 1515809 := bstep (se 2 (by rfl) ⟨568428, by rfl⟩ : syracuseStep 1515809 = 1136857) B1136857
theorem B2269475 : Blo 1008601 2269475 := bstep (se 1 (by rfl) ⟨1702106, by rfl⟩ : syracuseStep 2269475 = 3404213) B3404213
theorem B4858147 : Blo 1008601 4858147 := bstep (se 1 (by rfl) ⟨3643610, by rfl⟩ : syracuseStep 4858147 = 7287221) B7287221
theorem B1515827 : Blo 1008601 1515827 := bstep (se 1 (by rfl) ⟨1136870, by rfl⟩ : syracuseStep 1515827 = 2273741) B2273741
theorem B5120333 : Blo 1008601 5120333 := bstep (se 3 (by rfl) ⟨960062, by rfl⟩ : syracuseStep 5120333 = 1920125) B1920125
theorem B1515857 : Blo 1008601 1515857 := bstep (se 2 (by rfl) ⟨568446, by rfl⟩ : syracuseStep 1515857 = 1136893) B1136893
theorem B1515875 : Blo 1008601 1515875 := bstep (se 1 (by rfl) ⟨1136906, by rfl⟩ : syracuseStep 1515875 = 2273813) B2273813
theorem B1515905 : Blo 1008601 1515905 := bstep (se 2 (by rfl) ⟨568464, by rfl⟩ : syracuseStep 1515905 = 1136929) B1136929
theorem B1515923 : Blo 1008601 1515923 := bstep (se 1 (by rfl) ⟨1136942, by rfl⟩ : syracuseStep 1515923 = 2273885) B2273885
theorem B1515953 : Blo 1008601 1515953 := bstep (se 2 (by rfl) ⟨568482, by rfl⟩ : syracuseStep 1515953 = 1136965) B1136965
theorem B1515971 : Blo 1008601 1515971 := bstep (se 1 (by rfl) ⟨1136978, by rfl⟩ : syracuseStep 1515971 = 2273957) B2273957
theorem B3416525 : Blo 1008601 3416525 := bstep (se 3 (by rfl) ⟨640598, by rfl⟩ : syracuseStep 3416525 = 1281197) B1281197
theorem B1516001 : Blo 1008601 1516001 := bstep (se 2 (by rfl) ⟨568500, by rfl⟩ : syracuseStep 1516001 = 1137001) B1137001
theorem B1516019 : Blo 1008601 1516019 := bstep (se 1 (by rfl) ⟨1137014, by rfl⟩ : syracuseStep 1516019 = 2274029) B2274029
theorem B3416579 : Blo 1008601 3416579 := bstep (se 1 (by rfl) ⟨2562434, by rfl⟩ : syracuseStep 3416579 = 5124869) B5124869
theorem B1516049 : Blo 1008601 1516049 := bstep (se 2 (by rfl) ⟨568518, by rfl⟩ : syracuseStep 1516049 = 1137037) B1137037
theorem B1516067 : Blo 1008601 1516067 := bstep (se 1 (by rfl) ⟨1137050, by rfl⟩ : syracuseStep 1516067 = 2274101) B2274101
theorem B2269745 : Blo 1008601 2269745 := bstep (se 2 (by rfl) ⟨851154, by rfl⟩ : syracuseStep 2269745 = 1702309) B1702309
theorem B1516097 : Blo 1008601 1516097 := bstep (se 2 (by rfl) ⟨568536, by rfl⟩ : syracuseStep 1516097 = 1137073) B1137073
theorem B2269763 : Blo 1008601 2269763 := bstep (se 1 (by rfl) ⟨1702322, by rfl⟩ : syracuseStep 2269763 = 3404645) B3404645
theorem B1516115 : Blo 1008601 1516115 := bstep (se 1 (by rfl) ⟨1137086, by rfl⟩ : syracuseStep 1516115 = 2274173) B2274173
theorem B1516145 : Blo 1008601 1516145 := bstep (se 2 (by rfl) ⟨568554, by rfl⟩ : syracuseStep 1516145 = 1137109) B1137109
theorem B1516163 : Blo 1008601 1516163 := bstep (se 1 (by rfl) ⟨1137122, by rfl⟩ : syracuseStep 1516163 = 2274245) B2274245
theorem B1516193 : Blo 1008601 1516193 := bstep (se 2 (by rfl) ⟨568572, by rfl⟩ : syracuseStep 1516193 = 1137145) B1137145
theorem B1516211 : Blo 1008601 1516211 := bstep (se 1 (by rfl) ⟨1137158, by rfl⟩ : syracuseStep 1516211 = 2274317) B2274317
theorem B1516241 : Blo 1008601 1516241 := bstep (se 2 (by rfl) ⟨568590, by rfl⟩ : syracuseStep 1516241 = 1137181) B1137181
theorem B1516259 : Blo 1008601 1516259 := bstep (se 1 (by rfl) ⟨1137194, by rfl⟩ : syracuseStep 1516259 = 2274389) B2274389
theorem B1516289 : Blo 1008601 1516289 := bstep (se 2 (by rfl) ⟨568608, by rfl⟩ : syracuseStep 1516289 = 1137217) B1137217
theorem B3416849 : Blo 1008601 3416849 := bstep (se 2 (by rfl) ⟨1281318, by rfl⟩ : syracuseStep 3416849 = 2562637) B2562637
theorem B1516307 : Blo 1008601 1516307 := bstep (se 1 (by rfl) ⟨1137230, by rfl⟩ : syracuseStep 1516307 = 2274461) B2274461
theorem B5186339 : Blo 1008601 5186339 := bstep (se 1 (by rfl) ⟨3889754, by rfl⟩ : syracuseStep 5186339 = 7779509) B7779509
theorem B1516337 : Blo 1008601 1516337 := bstep (se 2 (by rfl) ⟨568626, by rfl⟩ : syracuseStep 1516337 = 1137253) B1137253
theorem B1516355 : Blo 1008601 1516355 := bstep (se 1 (by rfl) ⟨1137266, by rfl⟩ : syracuseStep 1516355 = 2274533) B2274533
theorem B2270033 : Blo 1008601 2270033 := bstep (se 2 (by rfl) ⟨851262, by rfl⟩ : syracuseStep 2270033 = 1702525) B1702525
theorem B1516385 : Blo 1008601 1516385 := bstep (se 2 (by rfl) ⟨568644, by rfl⟩ : syracuseStep 1516385 = 1137289) B1137289
theorem B2270051 : Blo 1008601 2270051 := bstep (se 1 (by rfl) ⟨1702538, by rfl⟩ : syracuseStep 2270051 = 3405077) B3405077
theorem B1516403 : Blo 1008601 1516403 := bstep (se 1 (by rfl) ⟨1137302, by rfl⟩ : syracuseStep 1516403 = 2274605) B2274605
theorem B1516433 : Blo 1008601 1516433 := bstep (se 2 (by rfl) ⟨568662, by rfl⟩ : syracuseStep 1516433 = 1137325) B1137325
theorem B1516451 : Blo 1008601 1516451 := bstep (se 1 (by rfl) ⟨1137338, by rfl⟩ : syracuseStep 1516451 = 2274677) B2274677
theorem B1516481 : Blo 1008601 1516481 := bstep (se 2 (by rfl) ⟨568680, by rfl⟩ : syracuseStep 1516481 = 1137361) B1137361
theorem B1516499 : Blo 1008601 1516499 := bstep (se 1 (by rfl) ⟨1137374, by rfl⟩ : syracuseStep 1516499 = 2274749) B2274749
theorem B1516529 : Blo 1008601 1516529 := bstep (se 2 (by rfl) ⟨568698, by rfl⟩ : syracuseStep 1516529 = 1137397) B1137397
theorem B1516547 : Blo 1008601 1516547 := bstep (se 1 (by rfl) ⟨1137410, by rfl⟩ : syracuseStep 1516547 = 2274821) B2274821
theorem B1516577 : Blo 1008601 1516577 := bstep (se 2 (by rfl) ⟨568716, by rfl⟩ : syracuseStep 1516577 = 1137433) B1137433
theorem B1516595 : Blo 1008601 1516595 := bstep (se 1 (by rfl) ⟨1137446, by rfl⟩ : syracuseStep 1516595 = 2274893) B2274893
theorem B1516625 : Blo 1008601 1516625 := bstep (se 2 (by rfl) ⟨568734, by rfl⟩ : syracuseStep 1516625 = 1137469) B1137469
theorem B1516643 : Blo 1008601 1516643 := bstep (se 1 (by rfl) ⟨1137482, by rfl⟩ : syracuseStep 1516643 = 2274965) B2274965
theorem B2270321 : Blo 1008601 2270321 := bstep (se 2 (by rfl) ⟨851370, by rfl⟩ : syracuseStep 2270321 = 1702741) B1702741
theorem B1516673 : Blo 1008601 1516673 := bstep (se 2 (by rfl) ⟨568752, by rfl⟩ : syracuseStep 1516673 = 1137505) B1137505
theorem B2270339 : Blo 1008601 2270339 := bstep (se 1 (by rfl) ⟨1702754, by rfl⟩ : syracuseStep 2270339 = 3405509) B3405509
theorem B1025155 : Blo 1008601 1025155 := bstep (se 1 (by rfl) ⟨768866, by rfl⟩ : syracuseStep 1025155 = 1537733) B1537733
theorem B1516691 : Blo 1008601 1516691 := bstep (se 1 (by rfl) ⟨1137518, by rfl⟩ : syracuseStep 1516691 = 2275037) B2275037
theorem B1516721 : Blo 1008601 1516721 := bstep (se 2 (by rfl) ⟨568770, by rfl⟩ : syracuseStep 1516721 = 1137541) B1137541
theorem B1516739 : Blo 1008601 1516739 := bstep (se 1 (by rfl) ⟨1137554, by rfl⟩ : syracuseStep 1516739 = 2275109) B2275109
theorem B1516769 : Blo 1008601 1516769 := bstep (se 2 (by rfl) ⟨568788, by rfl⟩ : syracuseStep 1516769 = 1137577) B1137577
theorem B1516787 : Blo 1008601 1516787 := bstep (se 1 (by rfl) ⟨1137590, by rfl⟩ : syracuseStep 1516787 = 2275181) B2275181
theorem B1516817 : Blo 1008601 1516817 := bstep (se 2 (by rfl) ⟨568806, by rfl⟩ : syracuseStep 1516817 = 1137613) B1137613
theorem B1516835 : Blo 1008601 1516835 := bstep (se 1 (by rfl) ⟨1137626, by rfl⟩ : syracuseStep 1516835 = 2275253) B2275253
theorem B3417389 : Blo 1008601 3417389 := bstep (se 3 (by rfl) ⟨640760, by rfl⟩ : syracuseStep 3417389 = 1281521) B1281521
theorem B1516865 : Blo 1008601 1516865 := bstep (se 2 (by rfl) ⟨568824, by rfl⟩ : syracuseStep 1516865 = 1137649) B1137649
theorem B1516883 : Blo 1008601 1516883 := bstep (se 1 (by rfl) ⟨1137662, by rfl⟩ : syracuseStep 1516883 = 2275325) B2275325
theorem B3417443 : Blo 1008601 3417443 := bstep (se 1 (by rfl) ⟨2563082, by rfl⟩ : syracuseStep 3417443 = 5126165) B5126165
theorem B1516913 : Blo 1008601 1516913 := bstep (se 2 (by rfl) ⟨568842, by rfl⟩ : syracuseStep 1516913 = 1137685) B1137685
theorem B1779059 : Blo 1008601 1779059 := bstep (se 1 (by rfl) ⟨1334294, by rfl⟩ : syracuseStep 1779059 = 2668589) B2668589
theorem B1516931 : Blo 1008601 1516931 := bstep (se 1 (by rfl) ⟨1137698, by rfl⟩ : syracuseStep 1516931 = 2275397) B2275397
theorem B2270609 : Blo 1008601 2270609 := bstep (se 2 (by rfl) ⟨851478, by rfl⟩ : syracuseStep 2270609 = 1702957) B1702957
theorem B1516961 : Blo 1008601 1516961 := bstep (se 2 (by rfl) ⟨568860, by rfl⟩ : syracuseStep 1516961 = 1137721) B1137721
theorem B2270627 : Blo 1008601 2270627 := bstep (se 1 (by rfl) ⟨1702970, by rfl⟩ : syracuseStep 2270627 = 3405941) B3405941
theorem B3646883 : Blo 1008601 3646883 := bstep (se 1 (by rfl) ⟨2735162, by rfl⟩ : syracuseStep 3646883 = 5470325) B5470325
theorem B1516979 : Blo 1008601 1516979 := bstep (se 1 (by rfl) ⟨1137734, by rfl⟩ : syracuseStep 1516979 = 2275469) B2275469
theorem B1517009 : Blo 1008601 1517009 := bstep (se 2 (by rfl) ⟨568878, by rfl⟩ : syracuseStep 1517009 = 1137757) B1137757
theorem B1517027 : Blo 1008601 1517027 := bstep (se 1 (by rfl) ⟨1137770, by rfl⟩ : syracuseStep 1517027 = 2275541) B2275541
theorem B1517057 : Blo 1008601 1517057 := bstep (se 2 (by rfl) ⟨568896, by rfl⟩ : syracuseStep 1517057 = 1137793) B1137793
theorem B1517075 : Blo 1008601 1517075 := bstep (se 1 (by rfl) ⟨1137806, by rfl⟩ : syracuseStep 1517075 = 2275613) B2275613
theorem B1517105 : Blo 1008601 1517105 := bstep (se 2 (by rfl) ⟨568914, by rfl⟩ : syracuseStep 1517105 = 1137829) B1137829
theorem B1517123 : Blo 1008601 1517123 := bstep (se 1 (by rfl) ⟨1137842, by rfl⟩ : syracuseStep 1517123 = 2275685) B2275685
theorem B1517153 : Blo 1008601 1517153 := bstep (se 2 (by rfl) ⟨568932, by rfl⟩ : syracuseStep 1517153 = 1137865) B1137865
theorem B3843683 : Blo 1008601 3843683 := bstep (se 1 (by rfl) ⟨2882762, by rfl⟩ : syracuseStep 3843683 = 5765525) B5765525
theorem B18654833 : Blo 1008601 18654833 := bstep (se 2 (by rfl) ⟨6995562, by rfl⟩ : syracuseStep 18654833 = 13991125) B13991125
theorem B1517171 : Blo 1008601 1517171 := bstep (se 1 (by rfl) ⟨1137878, by rfl⟩ : syracuseStep 1517171 = 2275757) B2275757
theorem B1517201 : Blo 1008601 1517201 := bstep (se 2 (by rfl) ⟨568950, by rfl⟩ : syracuseStep 1517201 = 1137901) B1137901
theorem B1517219 : Blo 1008601 1517219 := bstep (se 1 (by rfl) ⟨1137914, by rfl⟩ : syracuseStep 1517219 = 2275829) B2275829
theorem B2270897 : Blo 1008601 2270897 := bstep (se 2 (by rfl) ⟨851586, by rfl⟩ : syracuseStep 2270897 = 1703173) B1703173
theorem B1517249 : Blo 1008601 1517249 := bstep (se 2 (by rfl) ⟨568968, by rfl⟩ : syracuseStep 1517249 = 1137937) B1137937
theorem B2270915 : Blo 1008601 2270915 := bstep (se 1 (by rfl) ⟨1703186, by rfl⟩ : syracuseStep 2270915 = 3406373) B3406373
theorem B1517267 : Blo 1008601 1517267 := bstep (se 1 (by rfl) ⟨1137950, by rfl⟩ : syracuseStep 1517267 = 2275901) B2275901
theorem B6465251 : Blo 1008601 6465251 := bstep (se 1 (by rfl) ⟨4848938, by rfl⟩ : syracuseStep 6465251 = 9697877) B9697877
theorem B2074339 : Blo 1008601 2074339 := bstep (se 1 (by rfl) ⟨1555754, by rfl⟩ : syracuseStep 2074339 = 3111509) B3111509
theorem B1517297 : Blo 1008601 1517297 := bstep (se 2 (by rfl) ⟨568986, by rfl⟩ : syracuseStep 1517297 = 1137973) B1137973
theorem B1517315 : Blo 1008601 1517315 := bstep (se 1 (by rfl) ⟨1137986, by rfl⟩ : syracuseStep 1517315 = 2275973) B2275973
theorem B1517345 : Blo 1008601 1517345 := bstep (se 2 (by rfl) ⟨569004, by rfl⟩ : syracuseStep 1517345 = 1138009) B1138009
theorem B1517363 : Blo 1008601 1517363 := bstep (se 1 (by rfl) ⟨1138022, by rfl⟩ : syracuseStep 1517363 = 2276045) B2276045
theorem B1517393 : Blo 1008601 1517393 := bstep (se 2 (by rfl) ⟨569022, by rfl⟩ : syracuseStep 1517393 = 1138045) B1138045
theorem B1517411 : Blo 1008601 1517411 := bstep (se 1 (by rfl) ⟨1138058, by rfl⟩ : syracuseStep 1517411 = 2276117) B2276117
theorem B1517441 : Blo 1008601 1517441 := bstep (se 2 (by rfl) ⟨569040, by rfl⟩ : syracuseStep 1517441 = 1138081) B1138081
theorem B1615763 : Blo 1008601 1615763 := bstep (se 1 (by rfl) ⟨1211822, by rfl⟩ : syracuseStep 1615763 = 2423645) B2423645
theorem B1517459 : Blo 1008601 1517459 := bstep (se 1 (by rfl) ⟨1138094, by rfl⟩ : syracuseStep 1517459 = 2276189) B2276189
theorem B1517489 : Blo 1008601 1517489 := bstep (se 2 (by rfl) ⟨569058, by rfl⟩ : syracuseStep 1517489 = 1138117) B1138117
theorem B1517507 : Blo 1008601 1517507 := bstep (se 1 (by rfl) ⟨1138130, by rfl⟩ : syracuseStep 1517507 = 2276261) B2276261
theorem B2271185 : Blo 1008601 2271185 := bstep (se 2 (by rfl) ⟨851694, by rfl⟩ : syracuseStep 2271185 = 1703389) B1703389
theorem B1517537 : Blo 1008601 1517537 := bstep (se 2 (by rfl) ⟨569076, by rfl⟩ : syracuseStep 1517537 = 1138153) B1138153
theorem B2271203 : Blo 1008601 2271203 := bstep (se 1 (by rfl) ⟨1703402, by rfl⟩ : syracuseStep 2271203 = 3406805) B3406805
theorem B1517555 : Blo 1008601 1517555 := bstep (se 1 (by rfl) ⟨1138166, by rfl⟩ : syracuseStep 1517555 = 2276333) B2276333
theorem B1517585 : Blo 1008601 1517585 := bstep (se 2 (by rfl) ⟨569094, by rfl⟩ : syracuseStep 1517585 = 1138189) B1138189
theorem B1517603 : Blo 1008601 1517603 := bstep (se 1 (by rfl) ⟨1138202, by rfl⟩ : syracuseStep 1517603 = 2276405) B2276405
theorem B5253169 : Blo 1008601 5253169 := bstep (se 2 (by rfl) ⟨1969938, by rfl⟩ : syracuseStep 5253169 = 3939877) B3939877
theorem B1517633 : Blo 1008601 1517633 := bstep (se 2 (by rfl) ⟨569112, by rfl⟩ : syracuseStep 1517633 = 1138225) B1138225
theorem B1517651 : Blo 1008601 1517651 := bstep (se 1 (by rfl) ⟨1138238, by rfl⟩ : syracuseStep 1517651 = 2276477) B2276477
theorem B1517681 : Blo 1008601 1517681 := bstep (se 2 (by rfl) ⟨569130, by rfl⟩ : syracuseStep 1517681 = 1138261) B1138261
theorem B1517699 : Blo 1008601 1517699 := bstep (se 1 (by rfl) ⟨1138274, by rfl⟩ : syracuseStep 1517699 = 2276549) B2276549
theorem B1517729 : Blo 1008601 1517729 := bstep (se 2 (by rfl) ⟨569148, by rfl⟩ : syracuseStep 1517729 = 1138297) B1138297
theorem B1616051 : Blo 1008601 1616051 := bstep (se 1 (by rfl) ⟨1212038, by rfl⟩ : syracuseStep 1616051 = 2424077) B2424077
theorem B1517747 : Blo 1008601 1517747 := bstep (se 1 (by rfl) ⟨1138310, by rfl⟩ : syracuseStep 1517747 = 2276621) B2276621
theorem B23668933 : Blo 1008601 23668933 := bstep (se 4 (by rfl) ⟨2218962, by rfl⟩ : syracuseStep 23668933 = 4437925) B4437925
theorem B1517777 : Blo 1008601 1517777 := bstep (se 2 (by rfl) ⟨569166, by rfl⟩ : syracuseStep 1517777 = 1138333) B1138333
theorem B1517795 : Blo 1008601 1517795 := bstep (se 1 (by rfl) ⟨1138346, by rfl⟩ : syracuseStep 1517795 = 2276693) B2276693
theorem B2271473 : Blo 1008601 2271473 := bstep (se 2 (by rfl) ⟨851802, by rfl⟩ : syracuseStep 2271473 = 1703605) B1703605
theorem B1517825 : Blo 1008601 1517825 := bstep (se 2 (by rfl) ⟨569184, by rfl⟩ : syracuseStep 1517825 = 1138369) B1138369
theorem B2271491 : Blo 1008601 2271491 := bstep (se 1 (by rfl) ⟨1703618, by rfl⟩ : syracuseStep 2271491 = 3407237) B3407237
theorem B1517843 : Blo 1008601 1517843 := bstep (se 1 (by rfl) ⟨1138382, by rfl⟩ : syracuseStep 1517843 = 2276765) B2276765
theorem B1517873 : Blo 1008601 1517873 := bstep (se 2 (by rfl) ⟨569202, by rfl⟩ : syracuseStep 1517873 = 1138405) B1138405
theorem B1517891 : Blo 1008601 1517891 := bstep (se 1 (by rfl) ⟨1138418, by rfl⟩ : syracuseStep 1517891 = 2276837) B2276837
theorem B1517921 : Blo 1008601 1517921 := bstep (se 2 (by rfl) ⟨569220, by rfl⟩ : syracuseStep 1517921 = 1138441) B1138441
theorem B13805923 : Blo 1008601 13805923 := bstep (se 1 (by rfl) ⟨10354442, by rfl⟩ : syracuseStep 13805923 = 20708885) B20708885
theorem B2959715 : Blo 1008601 2959715 := bstep (se 1 (by rfl) ⟨2219786, by rfl⟩ : syracuseStep 2959715 = 4439573) B4439573
theorem B1943921 : Blo 1008601 1943921 := bstep (se 2 (by rfl) ⟨728970, by rfl⟩ : syracuseStep 1943921 = 1457941) B1457941
theorem B1517939 : Blo 1008601 1517939 := bstep (se 1 (by rfl) ⟨1138454, by rfl⟩ : syracuseStep 1517939 = 2276909) B2276909
theorem B1517969 : Blo 1008601 1517969 := bstep (se 2 (by rfl) ⟨569238, by rfl⟩ : syracuseStep 1517969 = 1138477) B1138477
theorem B1517987 : Blo 1008601 1517987 := bstep (se 1 (by rfl) ⟨1138490, by rfl⟩ : syracuseStep 1517987 = 2276981) B2276981
theorem B1518017 : Blo 1008601 1518017 := bstep (se 2 (by rfl) ⟨569256, by rfl⟩ : syracuseStep 1518017 = 1138513) B1138513
theorem B1518035 : Blo 1008601 1518035 := bstep (se 1 (by rfl) ⟨1138526, by rfl⟩ : syracuseStep 1518035 = 2277053) B2277053
theorem B1518065 : Blo 1008601 1518065 := bstep (se 2 (by rfl) ⟨569274, by rfl⟩ : syracuseStep 1518065 = 1138549) B1138549
theorem B1518083 : Blo 1008601 1518083 := bstep (se 1 (by rfl) ⟨1138562, by rfl⟩ : syracuseStep 1518083 = 2277125) B2277125
theorem B2271761 : Blo 1008601 2271761 := bstep (se 2 (by rfl) ⟨851910, by rfl⟩ : syracuseStep 2271761 = 1703821) B1703821
theorem B1518113 : Blo 1008601 1518113 := bstep (se 2 (by rfl) ⟨569292, by rfl⟩ : syracuseStep 1518113 = 1138585) B1138585
theorem B3451427 : Blo 1008601 3451427 := bstep (se 1 (by rfl) ⟨2588570, by rfl⟩ : syracuseStep 3451427 = 5177141) B5177141
theorem B2271779 : Blo 1008601 2271779 := bstep (se 1 (by rfl) ⟨1703834, by rfl⟩ : syracuseStep 2271779 = 3407669) B3407669
theorem B1518131 : Blo 1008601 1518131 := bstep (se 1 (by rfl) ⟨1138598, by rfl⟩ : syracuseStep 1518131 = 2277197) B2277197
theorem B3844685 : Blo 1008601 3844685 := bstep (se 3 (by rfl) ⟨720878, by rfl⟩ : syracuseStep 3844685 = 1441757) B1441757
theorem B1518161 : Blo 1008601 1518161 := bstep (se 2 (by rfl) ⟨569310, by rfl⟩ : syracuseStep 1518161 = 1138621) B1138621
theorem B1518179 : Blo 1008601 1518179 := bstep (se 1 (by rfl) ⟨1138634, by rfl⟩ : syracuseStep 1518179 = 2277269) B2277269
theorem B1518209 : Blo 1008601 1518209 := bstep (se 2 (by rfl) ⟨569328, by rfl⟩ : syracuseStep 1518209 = 1138657) B1138657
theorem B1518227 : Blo 1008601 1518227 := bstep (se 1 (by rfl) ⟨1138670, by rfl⟩ : syracuseStep 1518227 = 2277341) B2277341
theorem B1518257 : Blo 1008601 1518257 := bstep (se 2 (by rfl) ⟨569346, by rfl⟩ : syracuseStep 1518257 = 1138693) B1138693
theorem B1518275 : Blo 1008601 1518275 := bstep (se 1 (by rfl) ⟨1138706, by rfl⟩ : syracuseStep 1518275 = 2277413) B2277413
theorem B1518305 : Blo 1008601 1518305 := bstep (se 2 (by rfl) ⟨569364, by rfl⟩ : syracuseStep 1518305 = 1138729) B1138729
theorem B1518323 : Blo 1008601 1518323 := bstep (se 1 (by rfl) ⟨1138742, by rfl⟩ : syracuseStep 1518323 = 2277485) B2277485
theorem B1518353 : Blo 1008601 1518353 := bstep (se 2 (by rfl) ⟨569382, by rfl⟩ : syracuseStep 1518353 = 1138765) B1138765
theorem B1518371 : Blo 1008601 1518371 := bstep (se 1 (by rfl) ⟨1138778, by rfl⟩ : syracuseStep 1518371 = 2277557) B2277557
theorem B2272049 : Blo 1008601 2272049 := bstep (se 2 (by rfl) ⟨852018, by rfl⟩ : syracuseStep 2272049 = 1704037) B1704037
theorem B1518401 : Blo 1008601 1518401 := bstep (se 2 (by rfl) ⟨569400, by rfl⟩ : syracuseStep 1518401 = 1138801) B1138801
theorem B2272067 : Blo 1008601 2272067 := bstep (se 1 (by rfl) ⟨1704050, by rfl⟩ : syracuseStep 2272067 = 3408101) B3408101
theorem B1518419 : Blo 1008601 1518419 := bstep (se 1 (by rfl) ⟨1138814, by rfl⟩ : syracuseStep 1518419 = 2277629) B2277629
theorem B1518449 : Blo 1008601 1518449 := bstep (se 2 (by rfl) ⟨569418, by rfl⟩ : syracuseStep 1518449 = 1138837) B1138837
theorem B13151089 : Blo 1008601 13151089 := bstep (se 2 (by rfl) ⟨4931658, by rfl⟩ : syracuseStep 13151089 = 9863317) B9863317
theorem B1518467 : Blo 1008601 1518467 := bstep (se 1 (by rfl) ⟨1138850, by rfl⟩ : syracuseStep 1518467 = 2277701) B2277701
theorem B1518497 : Blo 1008601 1518497 := bstep (se 2 (by rfl) ⟨569436, by rfl⟩ : syracuseStep 1518497 = 1138873) B1138873
theorem B1518515 : Blo 1008601 1518515 := bstep (se 1 (by rfl) ⟨1138886, by rfl⟩ : syracuseStep 1518515 = 2277773) B2277773
theorem B5745613 : Blo 1008601 5745613 := bstep (se 3 (by rfl) ⟨1077302, by rfl⟩ : syracuseStep 5745613 = 2154605) B2154605
theorem B1518545 : Blo 1008601 1518545 := bstep (se 2 (by rfl) ⟨569454, by rfl⟩ : syracuseStep 1518545 = 1138909) B1138909
theorem B1616851 : Blo 1008601 1616851 := bstep (se 1 (by rfl) ⟨1212638, by rfl⟩ : syracuseStep 1616851 = 2425277) B2425277
theorem B1518563 : Blo 1008601 1518563 := bstep (se 1 (by rfl) ⟨1138922, by rfl⟩ : syracuseStep 1518563 = 2277845) B2277845
theorem B2730989 : Blo 1008601 2730989 := bstep (se 3 (by rfl) ⟨512060, by rfl⟩ : syracuseStep 2730989 = 1024121) B1024121
theorem B1518593 : Blo 1008601 1518593 := bstep (se 2 (by rfl) ⟨569472, by rfl⟩ : syracuseStep 1518593 = 1138945) B1138945
theorem B1518611 : Blo 1008601 1518611 := bstep (se 1 (by rfl) ⟨1138958, by rfl⟩ : syracuseStep 1518611 = 2277917) B2277917
theorem B1518641 : Blo 1008601 1518641 := bstep (se 2 (by rfl) ⟨569490, by rfl⟩ : syracuseStep 1518641 = 1138981) B1138981
theorem B1518659 : Blo 1008601 1518659 := bstep (se 1 (by rfl) ⟨1138994, by rfl⟩ : syracuseStep 1518659 = 2277989) B2277989
theorem B2272337 : Blo 1008601 2272337 := bstep (se 2 (by rfl) ⟨852126, by rfl⟩ : syracuseStep 2272337 = 1704253) B1704253
theorem B1616993 : Blo 1008601 1616993 := bstep (se 2 (by rfl) ⟨606372, by rfl⟩ : syracuseStep 1616993 = 1212745) B1212745
theorem B1518689 : Blo 1008601 1518689 := bstep (se 2 (by rfl) ⟨569508, by rfl⟩ : syracuseStep 1518689 = 1139017) B1139017
theorem B2272355 : Blo 1008601 2272355 := bstep (se 1 (by rfl) ⟨1704266, by rfl⟩ : syracuseStep 2272355 = 3408533) B3408533
theorem B1518707 : Blo 1008601 1518707 := bstep (se 1 (by rfl) ⟨1139030, by rfl⟩ : syracuseStep 1518707 = 2278061) B2278061
theorem B1617025 : Blo 1008601 1617025 := bstep (se 2 (by rfl) ⟨606384, by rfl⟩ : syracuseStep 1617025 = 1212769) B1212769
theorem B1518737 : Blo 1008601 1518737 := bstep (se 2 (by rfl) ⟨569526, by rfl⟩ : syracuseStep 1518737 = 1139053) B1139053
theorem B1846435 : Blo 1008601 1846435 := bstep (se 1 (by rfl) ⟨1384826, by rfl⟩ : syracuseStep 1846435 = 2769653) B2769653
theorem B1518755 : Blo 1008601 1518755 := bstep (se 1 (by rfl) ⟨1139066, by rfl⟩ : syracuseStep 1518755 = 2278133) B2278133
theorem B5123249 : Blo 1008601 5123249 := bstep (se 2 (by rfl) ⟨1921218, by rfl⟩ : syracuseStep 5123249 = 3842437) B3842437
theorem B1518785 : Blo 1008601 1518785 := bstep (se 2 (by rfl) ⟨569544, by rfl⟩ : syracuseStep 1518785 = 1139089) B1139089
theorem B1944785 : Blo 1008601 1944785 := bstep (se 2 (by rfl) ⟨729294, by rfl⟩ : syracuseStep 1944785 = 1458589) B1458589
theorem B1518803 : Blo 1008601 1518803 := bstep (se 1 (by rfl) ⟨1139102, by rfl⟩ : syracuseStep 1518803 = 2278205) B2278205
theorem B1518833 : Blo 1008601 1518833 := bstep (se 2 (by rfl) ⟨569562, by rfl⟩ : syracuseStep 1518833 = 1139125) B1139125
theorem B1518851 : Blo 1008601 1518851 := bstep (se 1 (by rfl) ⟨1139138, by rfl⟩ : syracuseStep 1518851 = 2278277) B2278277
theorem B1518881 : Blo 1008601 1518881 := bstep (se 2 (by rfl) ⟨569580, by rfl⟩ : syracuseStep 1518881 = 1139161) B1139161
theorem B1518899 : Blo 1008601 1518899 := bstep (se 1 (by rfl) ⟨1139174, by rfl⟩ : syracuseStep 1518899 = 2278349) B2278349
theorem B2272625 : Blo 1008601 2272625 := bstep (se 2 (by rfl) ⟨852234, by rfl⟩ : syracuseStep 2272625 = 1704469) B1704469
theorem B2272643 : Blo 1008601 2272643 := bstep (se 1 (by rfl) ⟨1704482, by rfl⟩ : syracuseStep 2272643 = 3408965) B3408965
theorem B2272913 : Blo 1008601 2272913 := bstep (se 2 (by rfl) ⟨852342, by rfl⟩ : syracuseStep 2272913 = 1704685) B1704685
theorem B2272931 : Blo 1008601 2272931 := bstep (se 1 (by rfl) ⟨1704698, by rfl⟩ : syracuseStep 2272931 = 3409397) B3409397
theorem B9711373 : Blo 1008601 9711373 := bstep (se 3 (by rfl) ⟨1820882, by rfl⟩ : syracuseStep 9711373 = 3641765) B3641765
theorem B2273201 : Blo 1008601 2273201 := bstep (se 2 (by rfl) ⟨852450, by rfl⟩ : syracuseStep 2273201 = 1704901) B1704901
theorem B2273219 : Blo 1008601 2273219 := bstep (se 1 (by rfl) ⟨1704914, by rfl⟩ : syracuseStep 2273219 = 3409829) B3409829
theorem B1617953 : Blo 1008601 1617953 := bstep (se 2 (by rfl) ⟨606732, by rfl⟩ : syracuseStep 1617953 = 1213465) B1213465
theorem B4862051 : Blo 1008601 4862051 := bstep (se 1 (by rfl) ⟨3646538, by rfl⟩ : syracuseStep 4862051 = 7293077) B7293077
theorem B2273489 : Blo 1008601 2273489 := bstep (se 2 (by rfl) ⟨852558, by rfl⟩ : syracuseStep 2273489 = 1705117) B1705117
theorem B2273507 : Blo 1008601 2273507 := bstep (se 1 (by rfl) ⟨1705130, by rfl⟩ : syracuseStep 2273507 = 3410261) B3410261
theorem B2076977 : Blo 1008601 2076977 := bstep (se 2 (by rfl) ⟨778866, by rfl⟩ : syracuseStep 2076977 = 1557733) B1557733
theorem B2306353 : Blo 1008601 2306353 := bstep (se 2 (by rfl) ⟨864882, by rfl⟩ : syracuseStep 2306353 = 1729765) B1729765
theorem B2765137 : Blo 1008601 2765137 := bstep (se 2 (by rfl) ⟨1036926, by rfl⟩ : syracuseStep 2765137 = 2073853) B2073853
theorem B13840739 : Blo 1008601 13840739 := bstep (se 1 (by rfl) ⟨10380554, by rfl⟩ : syracuseStep 13840739 = 20761109) B20761109
theorem B2765261 : Blo 1008601 2765261 := bstep (se 3 (by rfl) ⟨518486, by rfl⟩ : syracuseStep 2765261 = 1036973) B1036973
theorem B2273777 : Blo 1008601 2273777 := bstep (se 2 (by rfl) ⟨852666, by rfl⟩ : syracuseStep 2273777 = 1705333) B1705333
theorem B2273795 : Blo 1008601 2273795 := bstep (se 1 (by rfl) ⟨1705346, by rfl⟩ : syracuseStep 2273795 = 3410693) B3410693
theorem B5124707 : Blo 1008601 5124707 := bstep (se 1 (by rfl) ⟨3843530, by rfl⟩ : syracuseStep 5124707 = 7687061) B7687061
theorem B2274065 : Blo 1008601 2274065 := bstep (se 2 (by rfl) ⟨852774, by rfl⟩ : syracuseStep 2274065 = 1705549) B1705549
theorem B2274083 : Blo 1008601 2274083 := bstep (se 1 (by rfl) ⟨1705562, by rfl⟩ : syracuseStep 2274083 = 3411125) B3411125
theorem B2044739 : Blo 1008601 2044739 := bstep (se 1 (by rfl) ⟨1533554, by rfl⟩ : syracuseStep 2044739 = 3067109) B3067109
theorem B1618787 : Blo 1008601 1618787 := bstep (se 1 (by rfl) ⟨1214090, by rfl⟩ : syracuseStep 1618787 = 2428181) B2428181
theorem B5747597 : Blo 1008601 5747597 := bstep (se 3 (by rfl) ⟨1077674, by rfl⟩ : syracuseStep 5747597 = 2155349) B2155349
theorem B1848305 : Blo 1008601 1848305 := bstep (se 2 (by rfl) ⟨693114, by rfl⟩ : syracuseStep 1848305 = 1386229) B1386229
theorem B2274353 : Blo 1008601 2274353 := bstep (se 2 (by rfl) ⟨852882, by rfl⟩ : syracuseStep 2274353 = 1705765) B1705765
theorem B2274371 : Blo 1008601 2274371 := bstep (se 1 (by rfl) ⟨1705778, by rfl⟩ : syracuseStep 2274371 = 3411557) B3411557
theorem B1619075 : Blo 1008601 1619075 := bstep (se 1 (by rfl) ⟨1214306, by rfl⟩ : syracuseStep 1619075 = 2428613) B2428613
theorem B1946755 : Blo 1008601 1946755 := bstep (se 1 (by rfl) ⟨1460066, by rfl⟩ : syracuseStep 1946755 = 2920133) B2920133
theorem B4437325 : Blo 1008601 4437325 := bstep (se 3 (by rfl) ⟨831998, by rfl⟩ : syracuseStep 4437325 = 1663997) B1663997
theorem B2274641 : Blo 1008601 2274641 := bstep (se 2 (by rfl) ⟨852990, by rfl⟩ : syracuseStep 2274641 = 1705981) B1705981
theorem B1619299 : Blo 1008601 1619299 := bstep (se 1 (by rfl) ⟨1214474, by rfl⟩ : syracuseStep 1619299 = 2428949) B2428949
theorem B2274659 : Blo 1008601 2274659 := bstep (se 1 (by rfl) ⟨1705994, by rfl⟩ : syracuseStep 2274659 = 3411989) B3411989
theorem B5125517 : Blo 1008601 5125517 := bstep (se 3 (by rfl) ⟨961034, by rfl⟩ : syracuseStep 5125517 = 1922069) B1922069
theorem B12957155 : Blo 1008601 12957155 := bstep (se 1 (by rfl) ⟨9717866, by rfl⟩ : syracuseStep 12957155 = 19435733) B19435733
theorem B2078225 : Blo 1008601 2078225 := bstep (se 2 (by rfl) ⟨779334, by rfl⟩ : syracuseStep 2078225 = 1558669) B1558669
theorem B4601393 : Blo 1008601 4601393 := bstep (se 2 (by rfl) ⟨1725522, by rfl⟩ : syracuseStep 4601393 = 3451045) B3451045
theorem B2274929 : Blo 1008601 2274929 := bstep (se 2 (by rfl) ⟨853098, by rfl⟩ : syracuseStep 2274929 = 1706197) B1706197
theorem B2274947 : Blo 1008601 2274947 := bstep (se 1 (by rfl) ⟨1706210, by rfl⟩ : syracuseStep 2274947 = 3412421) B3412421
theorem B5748529 : Blo 1008601 5748529 := bstep (se 2 (by rfl) ⟨2155698, by rfl⟩ : syracuseStep 5748529 = 4311397) B4311397
theorem B4372337 : Blo 1008601 4372337 := bstep (se 2 (by rfl) ⟨1639626, by rfl⟩ : syracuseStep 4372337 = 3279253) B3279253
theorem B2275217 : Blo 1008601 2275217 := bstep (se 2 (by rfl) ⟨853206, by rfl⟩ : syracuseStep 2275217 = 1706413) B1706413
theorem B2275235 : Blo 1008601 2275235 := bstep (se 1 (by rfl) ⟨1706426, by rfl⟩ : syracuseStep 2275235 = 3412853) B3412853
theorem B1914833 : Blo 1008601 1914833 := bstep (se 2 (by rfl) ⟨718062, by rfl⟩ : syracuseStep 1914833 = 1436125) B1436125
theorem B1620017 : Blo 1008601 1620017 := bstep (se 2 (by rfl) ⟨607506, by rfl⟩ : syracuseStep 1620017 = 1215013) B1215013
theorem B4864049 : Blo 1008601 4864049 := bstep (se 2 (by rfl) ⟨1824018, by rfl⟩ : syracuseStep 4864049 = 3648037) B3648037
theorem B2275505 : Blo 1008601 2275505 := bstep (se 2 (by rfl) ⟨853314, by rfl⟩ : syracuseStep 2275505 = 1706629) B1706629
theorem B2275523 : Blo 1008601 2275523 := bstep (se 1 (by rfl) ⟨1706642, by rfl⟩ : syracuseStep 2275523 = 3413285) B3413285
theorem B1620209 : Blo 1008601 1620209 := bstep (se 2 (by rfl) ⟨607578, by rfl⟩ : syracuseStep 1620209 = 1215157) B1215157
theorem B1915235 : Blo 1008601 1915235 := bstep (se 1 (by rfl) ⟨1436426, by rfl⟩ : syracuseStep 1915235 = 2872853) B2872853
theorem B1620337 : Blo 1008601 1620337 := bstep (se 2 (by rfl) ⟨607626, by rfl⟩ : syracuseStep 1620337 = 1215253) B1215253
theorem B2275793 : Blo 1008601 2275793 := bstep (se 2 (by rfl) ⟨853422, by rfl⟩ : syracuseStep 2275793 = 1706845) B1706845
theorem B2275811 : Blo 1008601 2275811 := bstep (se 1 (by rfl) ⟨1706858, by rfl⟩ : syracuseStep 2275811 = 3413717) B3413717
theorem B16628365 : Blo 1008601 16628365 := bstep (se 3 (by rfl) ⟨3117818, by rfl⟩ : syracuseStep 16628365 = 6235637) B6235637
theorem B1948355 : Blo 1008601 1948355 := bstep (se 1 (by rfl) ⟨1461266, by rfl⟩ : syracuseStep 1948355 = 2922533) B2922533
theorem B2276081 : Blo 1008601 2276081 := bstep (se 2 (by rfl) ⟨853530, by rfl⟩ : syracuseStep 2276081 = 1707061) B1707061
theorem B2276099 : Blo 1008601 2276099 := bstep (se 1 (by rfl) ⟨1707074, by rfl⟩ : syracuseStep 2276099 = 3414149) B3414149
theorem B11516741 : Blo 1008601 11516741 := bstep (se 4 (by rfl) ⟨1079694, by rfl⟩ : syracuseStep 11516741 = 2159389) B2159389
theorem B5454755 : Blo 1008601 5454755 := bstep (se 1 (by rfl) ⟨4091066, by rfl⟩ : syracuseStep 5454755 = 8182133) B8182133
theorem B4864931 : Blo 1008601 4864931 := bstep (se 1 (by rfl) ⟨3648698, by rfl⟩ : syracuseStep 4864931 = 7297397) B7297397
theorem B1620977 : Blo 1008601 1620977 := bstep (se 2 (by rfl) ⟨607866, by rfl⟩ : syracuseStep 1620977 = 1215733) B1215733
theorem B2276369 : Blo 1008601 2276369 := bstep (se 2 (by rfl) ⟨853638, by rfl⟩ : syracuseStep 2276369 = 1707277) B1707277
theorem B2276387 : Blo 1008601 2276387 := bstep (se 1 (by rfl) ⟨1707290, by rfl⟩ : syracuseStep 2276387 = 3414581) B3414581
theorem B1916131 : Blo 1008601 1916131 := bstep (se 1 (by rfl) ⟨1437098, by rfl⟩ : syracuseStep 1916131 = 2874197) B2874197
theorem B5749987 : Blo 1008601 5749987 := bstep (se 1 (by rfl) ⟨4312490, by rfl⟩ : syracuseStep 5749987 = 8624981) B8624981
theorem B1817891 : Blo 1008601 1817891 := bstep (se 1 (by rfl) ⟨1363418, by rfl⟩ : syracuseStep 1817891 = 2726837) B2726837
theorem B2276657 : Blo 1008601 2276657 := bstep (se 2 (by rfl) ⟨853746, by rfl⟩ : syracuseStep 2276657 = 1707493) B1707493
theorem B2276675 : Blo 1008601 2276675 := bstep (se 1 (by rfl) ⟨1707506, by rfl⟩ : syracuseStep 2276675 = 3415013) B3415013
theorem B1916291 : Blo 1008601 1916291 := bstep (se 1 (by rfl) ⟨1437218, by rfl⟩ : syracuseStep 1916291 = 2874437) B2874437
theorem B2276945 : Blo 1008601 2276945 := bstep (se 2 (by rfl) ⟨853854, by rfl⟩ : syracuseStep 2276945 = 1707709) B1707709
theorem B2276963 : Blo 1008601 2276963 := bstep (se 1 (by rfl) ⟨1707722, by rfl⟩ : syracuseStep 2276963 = 3415445) B3415445
theorem B4865741 : Blo 1008601 4865741 := bstep (se 3 (by rfl) ⟨912326, by rfl⟩ : syracuseStep 4865741 = 1824653) B1824653
theorem B5750513 : Blo 1008601 5750513 := bstep (se 2 (by rfl) ⟨2156442, by rfl⟩ : syracuseStep 5750513 = 4312885) B4312885
theorem B4308785 : Blo 1008601 4308785 := bstep (se 2 (by rfl) ⟨1615794, by rfl⟩ : syracuseStep 4308785 = 3231589) B3231589
theorem B2080561 : Blo 1008601 2080561 := bstep (se 2 (by rfl) ⟨780210, by rfl⟩ : syracuseStep 2080561 = 1560421) B1560421
theorem B4308835 : Blo 1008601 4308835 := bstep (se 1 (by rfl) ⟨3231626, by rfl⟩ : syracuseStep 4308835 = 6463253) B6463253
theorem B2277233 : Blo 1008601 2277233 := bstep (se 2 (by rfl) ⟨853962, by rfl⟩ : syracuseStep 2277233 = 1707925) B1707925
theorem B2277251 : Blo 1008601 2277251 := bstep (se 1 (by rfl) ⟨1707938, by rfl⟩ : syracuseStep 2277251 = 3415877) B3415877
theorem B2277521 : Blo 1008601 2277521 := bstep (se 2 (by rfl) ⟨854070, by rfl⟩ : syracuseStep 2277521 = 1708141) B1708141
theorem B2277539 : Blo 1008601 2277539 := bstep (se 1 (by rfl) ⟨1708154, by rfl⟩ : syracuseStep 2277539 = 3416309) B3416309
theorem B1917361 : Blo 1008601 1917361 := bstep (se 2 (by rfl) ⟨719010, by rfl⟩ : syracuseStep 1917361 = 1438021) B1438021
theorem B2277809 : Blo 1008601 2277809 := bstep (se 2 (by rfl) ⟨854178, by rfl⟩ : syracuseStep 2277809 = 1708357) B1708357
theorem B2277827 : Blo 1008601 2277827 := bstep (se 1 (by rfl) ⟨1708370, by rfl⟩ : syracuseStep 2277827 = 3416741) B3416741
theorem B1819217 : Blo 1008601 1819217 := bstep (se 2 (by rfl) ⟨682206, by rfl⟩ : syracuseStep 1819217 = 1364413) B1364413
theorem B6472325 : Blo 1008601 6472325 := bstep (se 4 (by rfl) ⟨606780, by rfl⟩ : syracuseStep 6472325 = 1213561) B1213561
theorem B2278097 : Blo 1008601 2278097 := bstep (se 2 (by rfl) ⟨854286, by rfl⟩ : syracuseStep 2278097 = 1708573) B1708573
theorem B2278115 : Blo 1008601 2278115 := bstep (se 1 (by rfl) ⟨1708586, by rfl⟩ : syracuseStep 2278115 = 3417173) B3417173
theorem B3458189 : Blo 1008601 3458189 := bstep (se 3 (by rfl) ⟨648410, by rfl⟩ : syracuseStep 3458189 = 1296821) B1296821
theorem B5751971 : Blo 1008601 5751971 := bstep (se 1 (by rfl) ⟨4313978, by rfl⟩ : syracuseStep 5751971 = 8627957) B8627957
theorem B3458477 : Blo 1008601 3458477 := bstep (se 3 (by rfl) ⟨648464, by rfl⟩ : syracuseStep 3458477 = 1296929) B1296929
theorem B1754561 : Blo 1008601 1754561 := bstep (se 2 (by rfl) ⟨657960, by rfl⟩ : syracuseStep 1754561 = 1315921) B1315921
theorem B1918417 : Blo 1008601 1918417 := bstep (se 2 (by rfl) ⟨719406, by rfl⟩ : syracuseStep 1918417 = 1438813) B1438813
theorem B7685603 : Blo 1008601 7685603 := bstep (se 1 (by rfl) ⟨5764202, by rfl⟩ : syracuseStep 7685603 = 11528405) B11528405
theorem B3327601 : Blo 1008601 3327601 := bstep (se 2 (by rfl) ⟨1247850, by rfl⟩ : syracuseStep 3327601 = 2495701) B2495701
theorem B1918819 : Blo 1008601 1918819 := bstep (se 1 (by rfl) ⟨1439114, by rfl⟩ : syracuseStep 1918819 = 2878229) B2878229
theorem B20760461 : Blo 1008601 20760461 := bstep (se 3 (by rfl) ⟨3892586, by rfl⟩ : syracuseStep 20760461 = 7785173) B7785173
theorem B1918865 : Blo 1008601 1918865 := bstep (se 2 (by rfl) ⟨719574, by rfl⟩ : syracuseStep 1918865 = 1439149) B1439149
theorem B2050051 : Blo 1008601 2050051 := bstep (se 1 (by rfl) ⟨1537538, by rfl⟩ : syracuseStep 2050051 = 3075077) B3075077
theorem B1820803 : Blo 1008601 1820803 := bstep (se 1 (by rfl) ⟨1365602, by rfl⟩ : syracuseStep 1820803 = 2731205) B2731205
theorem B1919153 : Blo 1008601 1919153 := bstep (se 2 (by rfl) ⟨719682, by rfl⟩ : syracuseStep 1919153 = 1439365) B1439365
theorem B4311245 : Blo 1008601 4311245 := bstep (se 3 (by rfl) ⟨808358, by rfl⟩ : syracuseStep 4311245 = 1616717) B1616717
theorem B1820963 : Blo 1008601 1820963 := bstep (se 1 (by rfl) ⟨1365722, by rfl⟩ : syracuseStep 1820963 = 2731445) B2731445
theorem B1296739 : Blo 1008601 1296739 := bstep (se 1 (by rfl) ⟨972554, by rfl⟩ : syracuseStep 1296739 = 1945109) B1945109
theorem B4606541 : Blo 1008601 4606541 := bstep (se 3 (by rfl) ⟨863726, by rfl⟩ : syracuseStep 4606541 = 1727453) B1727453
theorem B1297139 : Blo 1008601 1297139 := bstep (se 1 (by rfl) ⟨972854, by rfl⟩ : syracuseStep 1297139 = 1945709) B1945709
theorem B1919875 : Blo 1008601 1919875 := bstep (se 1 (by rfl) ⟨1439906, by rfl⟩ : syracuseStep 1919875 = 2879813) B2879813
theorem B5753861 : Blo 1008601 5753861 := bstep (se 4 (by rfl) ⟨539424, by rfl⟩ : syracuseStep 5753861 = 1078849) B1078849
theorem B1920323 : Blo 1008601 1920323 := bstep (se 1 (by rfl) ⟨1440242, by rfl⟩ : syracuseStep 1920323 = 2880485) B2880485
theorem B1297955 : Blo 1008601 1297955 := bstep (se 1 (by rfl) ⟨973466, by rfl⟩ : syracuseStep 1297955 = 1946933) B1946933
theorem B1920611 : Blo 1008601 1920611 := bstep (se 1 (by rfl) ⟨1440458, by rfl⟩ : syracuseStep 1920611 = 2880917) B2880917
theorem B2051939 : Blo 1008601 2051939 := bstep (se 1 (by rfl) ⟨1538954, by rfl⟩ : syracuseStep 2051939 = 3077909) B3077909
theorem B1363873 : Blo 1008601 1363873 := bstep (se 2 (by rfl) ⟨511452, by rfl⟩ : syracuseStep 1363873 = 1022905) B1022905
theorem B31150021 : Blo 1008601 31150021 := bstep (se 4 (by rfl) ⟨2920314, by rfl⟩ : syracuseStep 31150021 = 5840629) B5840629
theorem B1364035 : Blo 1008601 1364035 := bstep (se 1 (by rfl) ⟨1023026, by rfl⟩ : syracuseStep 1364035 = 2046053) B2046053
theorem B6475889 : Blo 1008601 6475889 := bstep (se 2 (by rfl) ⟨2428458, by rfl⟩ : syracuseStep 6475889 = 4856917) B4856917
theorem B1134787 : Blo 1008601 1134787 := bstep (se 1 (by rfl) ⟨851090, by rfl⟩ : syracuseStep 1134787 = 1702181) B1702181
theorem B1134931 : Blo 1008601 1134931 := bstep (se 1 (by rfl) ⟨851198, by rfl⟩ : syracuseStep 1134931 = 1702397) B1702397
theorem B18403811 : Blo 1008601 18403811 := bstep (se 1 (by rfl) ⟨13802858, by rfl⟩ : syracuseStep 18403811 = 27605717) B27605717
theorem B1135075 : Blo 1008601 1135075 := bstep (se 1 (by rfl) ⟨851306, by rfl⟩ : syracuseStep 1135075 = 1702613) B1702613
theorem B11522573 : Blo 1008601 11522573 := bstep (se 3 (by rfl) ⟨2160482, by rfl⟩ : syracuseStep 11522573 = 4320965) B4320965
theorem B1921553 : Blo 1008601 1921553 := bstep (se 2 (by rfl) ⟨720582, by rfl⟩ : syracuseStep 1921553 = 1441165) B1441165
theorem B1135219 : Blo 1008601 1135219 := bstep (se 1 (by rfl) ⟨851414, by rfl⟩ : syracuseStep 1135219 = 1702829) B1702829
theorem B1135363 : Blo 1008601 1135363 := bstep (se 1 (by rfl) ⟨851522, by rfl⟩ : syracuseStep 1135363 = 1703045) B1703045
theorem B1135507 : Blo 1008601 1135507 := bstep (se 1 (by rfl) ⟨851630, by rfl⟩ : syracuseStep 1135507 = 1703261) B1703261
theorem B1823651 : Blo 1008601 1823651 := bstep (se 1 (by rfl) ⟨1367738, by rfl⟩ : syracuseStep 1823651 = 2735477) B2735477
theorem B3232781 : Blo 1008601 3232781 := bstep (se 3 (by rfl) ⟨606146, by rfl⟩ : syracuseStep 3232781 = 1212293) B1212293
theorem B1135651 : Blo 1008601 1135651 := bstep (se 1 (by rfl) ⟨851738, by rfl⟩ : syracuseStep 1135651 = 1703477) B1703477
theorem B2872397 : Blo 1008601 2872397 := bstep (se 3 (by rfl) ⟨538574, by rfl⟩ : syracuseStep 2872397 = 1077149) B1077149
theorem B1135795 : Blo 1008601 1135795 := bstep (se 1 (by rfl) ⟨851846, by rfl⟩ : syracuseStep 1135795 = 1703693) B1703693
theorem B2872579 : Blo 1008601 2872579 := bstep (se 1 (by rfl) ⟨2154434, by rfl⟩ : syracuseStep 2872579 = 4308869) B4308869
theorem B1135939 : Blo 1008601 1135939 := bstep (se 1 (by rfl) ⟨851954, by rfl⟩ : syracuseStep 1135939 = 1703909) B1703909
theorem B1824113 : Blo 1008601 1824113 := bstep (se 2 (by rfl) ⟨684042, by rfl⟩ : syracuseStep 1824113 = 1368085) B1368085
theorem B2872739 : Blo 1008601 2872739 := bstep (se 1 (by rfl) ⟨2154554, by rfl⟩ : syracuseStep 2872739 = 4309109) B4309109
theorem B4609457 : Blo 1008601 4609457 := bstep (se 2 (by rfl) ⟨1728546, by rfl⟩ : syracuseStep 4609457 = 3457093) B3457093
theorem B1136083 : Blo 1008601 1136083 := bstep (se 1 (by rfl) ⟨852062, by rfl⟩ : syracuseStep 1136083 = 1704125) B1704125
theorem B6477347 : Blo 1008601 6477347 := bstep (se 1 (by rfl) ⟨4858010, by rfl⟩ : syracuseStep 6477347 = 9716021) B9716021
theorem B1136227 : Blo 1008601 1136227 := bstep (se 1 (by rfl) ⟨852170, by rfl⟩ : syracuseStep 1136227 = 1704341) B1704341
theorem B1136371 : Blo 1008601 1136371 := bstep (se 1 (by rfl) ⟨852278, by rfl⟩ : syracuseStep 1136371 = 1704557) B1704557
theorem B13817699 : Blo 1008601 13817699 := bstep (se 1 (by rfl) ⟨10363274, by rfl⟩ : syracuseStep 13817699 = 20726549) B20726549
theorem B1136515 : Blo 1008601 1136515 := bstep (se 1 (by rfl) ⟨852386, by rfl⟩ : syracuseStep 1136515 = 1704773) B1704773
theorem B3233677 : Blo 1008601 3233677 := bstep (se 3 (by rfl) ⟨606314, by rfl⟩ : syracuseStep 3233677 = 1212629) B1212629
theorem B1136659 : Blo 1008601 1136659 := bstep (se 1 (by rfl) ⟨852494, by rfl⟩ : syracuseStep 1136659 = 1704989) B1704989
theorem B4610147 : Blo 1008601 4610147 := bstep (se 1 (by rfl) ⟨3457610, by rfl⟩ : syracuseStep 4610147 = 6915221) B6915221
theorem B5462149 : Blo 1008601 5462149 := bstep (se 4 (by rfl) ⟨512076, by rfl⟩ : syracuseStep 5462149 = 1024153) B1024153
theorem B7297165 : Blo 1008601 7297165 := bstep (se 3 (by rfl) ⟨1368218, by rfl⟩ : syracuseStep 7297165 = 2736437) B2736437
theorem B1136803 : Blo 1008601 1136803 := bstep (se 1 (by rfl) ⟨852602, by rfl⟩ : syracuseStep 1136803 = 1705205) B1705205
theorem B1136947 : Blo 1008601 1136947 := bstep (se 1 (by rfl) ⟨852710, by rfl⟩ : syracuseStep 1136947 = 1705421) B1705421
theorem B11688245 : Blo 1008601 11688245 := bstep (se 5 (by rfl) ⟨547886, by rfl⟩ : syracuseStep 11688245 = 1095773) B1095773
theorem B1137091 : Blo 1008601 1137091 := bstep (se 1 (by rfl) ⟨852818, by rfl⟩ : syracuseStep 1137091 = 1705637) B1705637
theorem B2873809 : Blo 1008601 2873809 := bstep (se 2 (by rfl) ⟨1077678, by rfl⟩ : syracuseStep 2873809 = 2155357) B2155357
theorem B4315619 : Blo 1008601 4315619 := bstep (se 1 (by rfl) ⟨3236714, by rfl⟩ : syracuseStep 4315619 = 6473429) B6473429
theorem B3070541 : Blo 1008601 3070541 := bstep (se 3 (by rfl) ⟨575726, by rfl⟩ : syracuseStep 3070541 = 1151453) B1151453
theorem B1137235 : Blo 1008601 1137235 := bstep (se 1 (by rfl) ⟨852926, by rfl⟩ : syracuseStep 1137235 = 1705853) B1705853
theorem B1137379 : Blo 1008601 1137379 := bstep (se 1 (by rfl) ⟨853034, by rfl⟩ : syracuseStep 1137379 = 1706069) B1706069
theorem B3234563 : Blo 1008601 3234563 := bstep (se 1 (by rfl) ⟨2425922, by rfl⟩ : syracuseStep 3234563 = 4851845) B4851845
theorem B1137523 : Blo 1008601 1137523 := bstep (se 1 (by rfl) ⟨853142, by rfl⟩ : syracuseStep 1137523 = 1706285) B1706285
theorem B3464099 : Blo 1008601 3464099 := bstep (se 1 (by rfl) ⟨2598074, by rfl⟩ : syracuseStep 3464099 = 5196149) B5196149
theorem B1727411 : Blo 1008601 1727411 := bstep (se 1 (by rfl) ⟨1295558, by rfl⟩ : syracuseStep 1727411 = 2591117) B2591117
theorem B1137667 : Blo 1008601 1137667 := bstep (se 1 (by rfl) ⟨853250, by rfl⟩ : syracuseStep 1137667 = 1706501) B1706501
theorem B1137811 : Blo 1008601 1137811 := bstep (se 1 (by rfl) ⟨853358, by rfl⟩ : syracuseStep 1137811 = 1706717) B1706717
theorem B1137955 : Blo 1008601 1137955 := bstep (se 1 (by rfl) ⟨853466, by rfl⟩ : syracuseStep 1137955 = 1706933) B1706933
theorem B11525489 : Blo 1008601 11525489 := bstep (se 2 (by rfl) ⟨4322058, by rfl⟩ : syracuseStep 11525489 = 8644117) B8644117
theorem B1138099 : Blo 1008601 1138099 := bstep (se 1 (by rfl) ⟨853574, by rfl⟩ : syracuseStep 1138099 = 1707149) B1707149
theorem B1138243 : Blo 1008601 1138243 := bstep (se 1 (by rfl) ⟨853682, by rfl⟩ : syracuseStep 1138243 = 1707365) B1707365
theorem B2154161 : Blo 1008601 2154161 := bstep (se 2 (by rfl) ⟨807810, by rfl⟩ : syracuseStep 2154161 = 1615621) B1615621
theorem B2875085 : Blo 1008601 2875085 := bstep (se 3 (by rfl) ⟨539078, by rfl⟩ : syracuseStep 2875085 = 1078157) B1078157
theorem B1138387 : Blo 1008601 1138387 := bstep (se 1 (by rfl) ⟨853790, by rfl⟩ : syracuseStep 1138387 = 1707581) B1707581
theorem B12935011 : Blo 1008601 12935011 := bstep (se 1 (by rfl) ⟨9701258, by rfl⟩ : syracuseStep 12935011 = 19402517) B19402517
theorem B1138531 : Blo 1008601 1138531 := bstep (se 1 (by rfl) ⟨853898, by rfl⟩ : syracuseStep 1138531 = 1707797) B1707797
theorem B2875267 : Blo 1008601 2875267 := bstep (se 1 (by rfl) ⟨2156450, by rfl⟩ : syracuseStep 2875267 = 4312901) B4312901
theorem B2875313 : Blo 1008601 2875313 := bstep (se 2 (by rfl) ⟨1078242, by rfl⟩ : syracuseStep 2875313 = 2156485) B2156485
theorem B1138675 : Blo 1008601 1138675 := bstep (se 1 (by rfl) ⟨854006, by rfl⟩ : syracuseStep 1138675 = 1708013) B1708013
theorem B1138819 : Blo 1008601 1138819 := bstep (se 1 (by rfl) ⟨854114, by rfl⟩ : syracuseStep 1138819 = 1708229) B1708229
theorem B6480013 : Blo 1008601 6480013 := bstep (se 3 (by rfl) ⟨1215002, by rfl⟩ : syracuseStep 6480013 = 2430005) B2430005
theorem B1368257 : Blo 1008601 1368257 := bstep (se 2 (by rfl) ⟨513096, by rfl⟩ : syracuseStep 1368257 = 1026193) B1026193
theorem B2154691 : Blo 1008601 2154691 := bstep (se 1 (by rfl) ⟨1616018, by rfl⟩ : syracuseStep 2154691 = 3232037) B3232037
theorem B1138963 : Blo 1008601 1138963 := bstep (se 1 (by rfl) ⟨854222, by rfl⟩ : syracuseStep 1138963 = 1708445) B1708445
theorem B7659845 : Blo 1008601 7659845 := bstep (se 4 (by rfl) ⟨718110, by rfl⟩ : syracuseStep 7659845 = 1436221) B1436221
theorem B1139107 : Blo 1008601 1139107 := bstep (se 1 (by rfl) ⟨854330, by rfl⟩ : syracuseStep 1139107 = 1708661) B1708661
theorem B4317617 : Blo 1008601 4317617 := bstep (se 2 (by rfl) ⟨1619106, by rfl⟩ : syracuseStep 4317617 = 3238213) B3238213
theorem B5988941 : Blo 1008601 5988941 := bstep (se 3 (by rfl) ⟨1122926, by rfl⟩ : syracuseStep 5988941 = 2245853) B2245853
theorem B5759693 : Blo 1008601 5759693 := bstep (se 3 (by rfl) ⟨1079942, by rfl⟩ : syracuseStep 5759693 = 2159885) B2159885
theorem B3236753 : Blo 1008601 3236753 := bstep (se 2 (by rfl) ⟨1213782, by rfl⟩ : syracuseStep 3236753 = 2427565) B2427565
theorem B1008611 : Blo 1008601 1008611 := bstep (se 1 (by rfl) ⟨756458, by rfl⟩ : syracuseStep 1008611 = 1512917) B1512917
theorem B1008627 : Blo 1008601 1008627 := bstep (se 1 (by rfl) ⟨756470, by rfl⟩ : syracuseStep 1008627 = 1512941) B1512941
theorem B1008643 : Blo 1008601 1008643 := bstep (se 1 (by rfl) ⟨756482, by rfl⟩ : syracuseStep 1008643 = 1512965) B1512965
theorem B3236881 : Blo 1008601 3236881 := bstep (se 2 (by rfl) ⟨1213830, by rfl⟩ : syracuseStep 3236881 = 2427661) B2427661
theorem B1008659 : Blo 1008601 1008659 := bstep (se 1 (by rfl) ⟨756494, by rfl⟩ : syracuseStep 1008659 = 1512989) B1512989
theorem B1008675 : Blo 1008601 1008675 := bstep (se 1 (by rfl) ⟨756506, by rfl⟩ : syracuseStep 1008675 = 1513013) B1513013
theorem B1008691 : Blo 1008601 1008691 := bstep (se 1 (by rfl) ⟨756518, by rfl⟩ : syracuseStep 1008691 = 1513037) B1513037
theorem B1008707 : Blo 1008601 1008707 := bstep (se 1 (by rfl) ⟨756530, by rfl⟩ : syracuseStep 1008707 = 1513061) B1513061
theorem B1008723 : Blo 1008601 1008723 := bstep (se 1 (by rfl) ⟨756542, by rfl⟩ : syracuseStep 1008723 = 1513085) B1513085
theorem B1008739 : Blo 1008601 1008739 := bstep (se 1 (by rfl) ⟨756554, by rfl⟩ : syracuseStep 1008739 = 1513109) B1513109
theorem B1008755 : Blo 1008601 1008755 := bstep (se 1 (by rfl) ⟨756566, by rfl⟩ : syracuseStep 1008755 = 1513133) B1513133
theorem B1008771 : Blo 1008601 1008771 := bstep (se 1 (by rfl) ⟨756578, by rfl⟩ : syracuseStep 1008771 = 1513157) B1513157
theorem B1008787 : Blo 1008601 1008787 := bstep (se 1 (by rfl) ⟨756590, by rfl⟩ : syracuseStep 1008787 = 1513181) B1513181
theorem B1008803 : Blo 1008601 1008803 := bstep (se 1 (by rfl) ⟨756602, by rfl⟩ : syracuseStep 1008803 = 1513205) B1513205
theorem B1008819 : Blo 1008601 1008819 := bstep (se 1 (by rfl) ⟨756614, by rfl⟩ : syracuseStep 1008819 = 1513229) B1513229
theorem B12313781 : Blo 1008601 12313781 := bstep (se 5 (by rfl) ⟨577208, by rfl⟩ : syracuseStep 12313781 = 1154417) B1154417
theorem B1008835 : Blo 1008601 1008835 := bstep (se 1 (by rfl) ⟨756626, by rfl⟩ : syracuseStep 1008835 = 1513253) B1513253
theorem B1008851 : Blo 1008601 1008851 := bstep (se 1 (by rfl) ⟨756638, by rfl⟩ : syracuseStep 1008851 = 1513277) B1513277
theorem B1008867 : Blo 1008601 1008867 := bstep (se 1 (by rfl) ⟨756650, by rfl⟩ : syracuseStep 1008867 = 1513301) B1513301
theorem B1008883 : Blo 1008601 1008883 := bstep (se 1 (by rfl) ⟨756662, by rfl⟩ : syracuseStep 1008883 = 1513325) B1513325
theorem B1008899 : Blo 1008601 1008899 := bstep (se 1 (by rfl) ⟨756674, by rfl⟩ : syracuseStep 1008899 = 1513349) B1513349
theorem B3237137 : Blo 1008601 3237137 := bstep (se 2 (by rfl) ⟨1213926, by rfl⟩ : syracuseStep 3237137 = 2427853) B2427853
theorem B1008915 : Blo 1008601 1008915 := bstep (se 1 (by rfl) ⟨756686, by rfl⟩ : syracuseStep 1008915 = 1513373) B1513373
theorem B1008931 : Blo 1008601 1008931 := bstep (se 1 (by rfl) ⟨756698, by rfl⟩ : syracuseStep 1008931 = 1513397) B1513397
theorem B1008947 : Blo 1008601 1008947 := bstep (se 1 (by rfl) ⟨756710, by rfl⟩ : syracuseStep 1008947 = 1513421) B1513421
theorem B1008963 : Blo 1008601 1008963 := bstep (se 1 (by rfl) ⟨756722, by rfl⟩ : syracuseStep 1008963 = 1513445) B1513445
theorem B4318541 : Blo 1008601 4318541 := bstep (se 3 (by rfl) ⟨809726, by rfl⟩ : syracuseStep 4318541 = 1619453) B1619453
theorem B1008979 : Blo 1008601 1008979 := bstep (se 1 (by rfl) ⟨756734, by rfl⟩ : syracuseStep 1008979 = 1513469) B1513469
theorem B1008995 : Blo 1008601 1008995 := bstep (se 1 (by rfl) ⟨756746, by rfl⟩ : syracuseStep 1008995 = 1513493) B1513493
theorem B2876771 : Blo 1008601 2876771 := bstep (se 1 (by rfl) ⟨2157578, by rfl⟩ : syracuseStep 2876771 = 4315157) B4315157
theorem B1009011 : Blo 1008601 1009011 := bstep (se 1 (by rfl) ⟨756758, by rfl⟩ : syracuseStep 1009011 = 1513517) B1513517
theorem B1009027 : Blo 1008601 1009027 := bstep (se 1 (by rfl) ⟨756770, by rfl⟩ : syracuseStep 1009027 = 1513541) B1513541
theorem B1009043 : Blo 1008601 1009043 := bstep (se 1 (by rfl) ⟨756782, by rfl⟩ : syracuseStep 1009043 = 1513565) B1513565
theorem B1009059 : Blo 1008601 1009059 := bstep (se 1 (by rfl) ⟨756794, by rfl⟩ : syracuseStep 1009059 = 1513589) B1513589
theorem B1009075 : Blo 1008601 1009075 := bstep (se 1 (by rfl) ⟨756806, by rfl⟩ : syracuseStep 1009075 = 1513613) B1513613
theorem B1009091 : Blo 1008601 1009091 := bstep (se 1 (by rfl) ⟨756818, by rfl⟩ : syracuseStep 1009091 = 1513637) B1513637
theorem B1009107 : Blo 1008601 1009107 := bstep (se 1 (by rfl) ⟨756830, by rfl⟩ : syracuseStep 1009107 = 1513661) B1513661
theorem B1009123 : Blo 1008601 1009123 := bstep (se 1 (by rfl) ⟨756842, by rfl⟩ : syracuseStep 1009123 = 1513685) B1513685
theorem B1009139 : Blo 1008601 1009139 := bstep (se 1 (by rfl) ⟨756854, by rfl⟩ : syracuseStep 1009139 = 1513709) B1513709
theorem B1009155 : Blo 1008601 1009155 := bstep (se 1 (by rfl) ⟨756866, by rfl⟩ : syracuseStep 1009155 = 1513733) B1513733
theorem B1009171 : Blo 1008601 1009171 := bstep (se 1 (by rfl) ⟨756878, by rfl⟩ : syracuseStep 1009171 = 1513757) B1513757
theorem B1009187 : Blo 1008601 1009187 := bstep (se 1 (by rfl) ⟨756890, by rfl⟩ : syracuseStep 1009187 = 1513781) B1513781
theorem B1009203 : Blo 1008601 1009203 := bstep (se 1 (by rfl) ⟨756902, by rfl⟩ : syracuseStep 1009203 = 1513805) B1513805
theorem B1009219 : Blo 1008601 1009219 := bstep (se 1 (by rfl) ⟨756914, by rfl⟩ : syracuseStep 1009219 = 1513829) B1513829
theorem B1009235 : Blo 1008601 1009235 := bstep (se 1 (by rfl) ⟨756926, by rfl⟩ : syracuseStep 1009235 = 1513853) B1513853
theorem B1009251 : Blo 1008601 1009251 := bstep (se 1 (by rfl) ⟨756938, by rfl⟩ : syracuseStep 1009251 = 1513877) B1513877
theorem B1009267 : Blo 1008601 1009267 := bstep (se 1 (by rfl) ⟨756950, by rfl⟩ : syracuseStep 1009267 = 1513901) B1513901
theorem B1009283 : Blo 1008601 1009283 := bstep (se 1 (by rfl) ⟨756962, by rfl⟩ : syracuseStep 1009283 = 1513925) B1513925
theorem B2025091 : Blo 1008601 2025091 := bstep (se 1 (by rfl) ⟨1518818, by rfl⟩ : syracuseStep 2025091 = 3037637) B3037637
theorem B2156177 : Blo 1008601 2156177 := bstep (se 2 (by rfl) ⟨808566, by rfl⟩ : syracuseStep 2156177 = 1617133) B1617133
theorem B1009299 : Blo 1008601 1009299 := bstep (se 1 (by rfl) ⟨756974, by rfl⟩ : syracuseStep 1009299 = 1513949) B1513949
theorem B1009315 : Blo 1008601 1009315 := bstep (se 1 (by rfl) ⟨756986, by rfl⟩ : syracuseStep 1009315 = 1513973) B1513973
theorem B2156195 : Blo 1008601 2156195 := bstep (se 1 (by rfl) ⟨1617146, by rfl⟩ : syracuseStep 2156195 = 3234293) B3234293
theorem B1009331 : Blo 1008601 1009331 := bstep (se 1 (by rfl) ⟨756998, by rfl⟩ : syracuseStep 1009331 = 1513997) B1513997
theorem B1009347 : Blo 1008601 1009347 := bstep (se 1 (by rfl) ⟨757010, by rfl⟩ : syracuseStep 1009347 = 1514021) B1514021
theorem B1009363 : Blo 1008601 1009363 := bstep (se 1 (by rfl) ⟨757022, by rfl⟩ : syracuseStep 1009363 = 1514045) B1514045
theorem B1009379 : Blo 1008601 1009379 := bstep (se 1 (by rfl) ⟨757034, by rfl⟩ : syracuseStep 1009379 = 1514069) B1514069
theorem B1009395 : Blo 1008601 1009395 := bstep (se 1 (by rfl) ⟨757046, by rfl⟩ : syracuseStep 1009395 = 1514093) B1514093
theorem B1009411 : Blo 1008601 1009411 := bstep (se 1 (by rfl) ⟨757058, by rfl⟩ : syracuseStep 1009411 = 1514117) B1514117
theorem B1009427 : Blo 1008601 1009427 := bstep (se 1 (by rfl) ⟨757070, by rfl⟩ : syracuseStep 1009427 = 1514141) B1514141
theorem B1009443 : Blo 1008601 1009443 := bstep (se 1 (by rfl) ⟨757082, by rfl⟩ : syracuseStep 1009443 = 1514165) B1514165
theorem B1009459 : Blo 1008601 1009459 := bstep (se 1 (by rfl) ⟨757094, by rfl⟩ : syracuseStep 1009459 = 1514189) B1514189
theorem B1009475 : Blo 1008601 1009475 := bstep (se 1 (by rfl) ⟨757106, by rfl⟩ : syracuseStep 1009475 = 1514213) B1514213
theorem B1009491 : Blo 1008601 1009491 := bstep (se 1 (by rfl) ⟨757118, by rfl⟩ : syracuseStep 1009491 = 1514237) B1514237
theorem B1009507 : Blo 1008601 1009507 := bstep (se 1 (by rfl) ⟨757130, by rfl⟩ : syracuseStep 1009507 = 1514261) B1514261
theorem B1009523 : Blo 1008601 1009523 := bstep (se 1 (by rfl) ⟨757142, by rfl⟩ : syracuseStep 1009523 = 1514285) B1514285
theorem B1009539 : Blo 1008601 1009539 := bstep (se 1 (by rfl) ⟨757154, by rfl⟩ : syracuseStep 1009539 = 1514309) B1514309
theorem B1009555 : Blo 1008601 1009555 := bstep (se 1 (by rfl) ⟨757166, by rfl⟩ : syracuseStep 1009555 = 1514333) B1514333
theorem B1009571 : Blo 1008601 1009571 := bstep (se 1 (by rfl) ⟨757178, by rfl⟩ : syracuseStep 1009571 = 1514357) B1514357
theorem B1009587 : Blo 1008601 1009587 := bstep (se 1 (by rfl) ⟨757190, by rfl⟩ : syracuseStep 1009587 = 1514381) B1514381
theorem B1009603 : Blo 1008601 1009603 := bstep (se 1 (by rfl) ⟨757202, by rfl⟩ : syracuseStep 1009603 = 1514405) B1514405
theorem B1009619 : Blo 1008601 1009619 := bstep (se 1 (by rfl) ⟨757214, by rfl⟩ : syracuseStep 1009619 = 1514429) B1514429
theorem B1009635 : Blo 1008601 1009635 := bstep (se 1 (by rfl) ⟨757226, by rfl⟩ : syracuseStep 1009635 = 1514453) B1514453
theorem B1009651 : Blo 1008601 1009651 := bstep (se 1 (by rfl) ⟨757238, by rfl⟩ : syracuseStep 1009651 = 1514477) B1514477
theorem B1009667 : Blo 1008601 1009667 := bstep (se 1 (by rfl) ⟨757250, by rfl⟩ : syracuseStep 1009667 = 1514501) B1514501
theorem B1009683 : Blo 1008601 1009683 := bstep (se 1 (by rfl) ⟨757262, by rfl⟩ : syracuseStep 1009683 = 1514525) B1514525
theorem B1009699 : Blo 1008601 1009699 := bstep (se 1 (by rfl) ⟨757274, by rfl⟩ : syracuseStep 1009699 = 1514549) B1514549
theorem B1009715 : Blo 1008601 1009715 := bstep (se 1 (by rfl) ⟨757286, by rfl⟩ : syracuseStep 1009715 = 1514573) B1514573
theorem B1009731 : Blo 1008601 1009731 := bstep (se 1 (by rfl) ⟨757298, by rfl⟩ : syracuseStep 1009731 = 1514597) B1514597
theorem B1730641 : Blo 1008601 1730641 := bstep (se 2 (by rfl) ⟨648990, by rfl⟩ : syracuseStep 1730641 = 1297981) B1297981
theorem B1009747 : Blo 1008601 1009747 := bstep (se 1 (by rfl) ⟨757310, by rfl⟩ : syracuseStep 1009747 = 1514621) B1514621
theorem B1009763 : Blo 1008601 1009763 := bstep (se 1 (by rfl) ⟨757322, by rfl⟩ : syracuseStep 1009763 = 1514645) B1514645
theorem B1009779 : Blo 1008601 1009779 := bstep (se 1 (by rfl) ⟨757334, by rfl⟩ : syracuseStep 1009779 = 1514669) B1514669
theorem B1009795 : Blo 1008601 1009795 := bstep (se 1 (by rfl) ⟨757346, by rfl⟩ : syracuseStep 1009795 = 1514693) B1514693
theorem B1009811 : Blo 1008601 1009811 := bstep (se 1 (by rfl) ⟨757358, by rfl⟩ : syracuseStep 1009811 = 1514717) B1514717
theorem B1009827 : Blo 1008601 1009827 := bstep (se 1 (by rfl) ⟨757370, by rfl⟩ : syracuseStep 1009827 = 1514741) B1514741
theorem B1009843 : Blo 1008601 1009843 := bstep (se 1 (by rfl) ⟨757382, by rfl⟩ : syracuseStep 1009843 = 1514765) B1514765
theorem B1009859 : Blo 1008601 1009859 := bstep (se 1 (by rfl) ⟨757394, by rfl⟩ : syracuseStep 1009859 = 1514789) B1514789
theorem B1009875 : Blo 1008601 1009875 := bstep (se 1 (by rfl) ⟨757406, by rfl⟩ : syracuseStep 1009875 = 1514813) B1514813
theorem B1009891 : Blo 1008601 1009891 := bstep (se 1 (by rfl) ⟨757418, by rfl⟩ : syracuseStep 1009891 = 1514837) B1514837
theorem B1009907 : Blo 1008601 1009907 := bstep (se 1 (by rfl) ⟨757430, by rfl⟩ : syracuseStep 1009907 = 1514861) B1514861
theorem B1009923 : Blo 1008601 1009923 := bstep (se 1 (by rfl) ⟨757442, by rfl⟩ : syracuseStep 1009923 = 1514885) B1514885
theorem B1009939 : Blo 1008601 1009939 := bstep (se 1 (by rfl) ⟨757454, by rfl⟩ : syracuseStep 1009939 = 1514909) B1514909
theorem B1009955 : Blo 1008601 1009955 := bstep (se 1 (by rfl) ⟨757466, by rfl⟩ : syracuseStep 1009955 = 1514933) B1514933
theorem B1009971 : Blo 1008601 1009971 := bstep (se 1 (by rfl) ⟨757478, by rfl⟩ : syracuseStep 1009971 = 1514957) B1514957
theorem B1009987 : Blo 1008601 1009987 := bstep (se 1 (by rfl) ⟨757490, by rfl⟩ : syracuseStep 1009987 = 1514981) B1514981
theorem B5531981 : Blo 1008601 5531981 := bstep (se 3 (by rfl) ⟨1037246, by rfl⟩ : syracuseStep 5531981 = 2074493) B2074493
theorem B1010003 : Blo 1008601 1010003 := bstep (se 1 (by rfl) ⟨757502, by rfl⟩ : syracuseStep 1010003 = 1515005) B1515005
theorem B1010019 : Blo 1008601 1010019 := bstep (se 1 (by rfl) ⟨757514, by rfl⟩ : syracuseStep 1010019 = 1515029) B1515029
theorem B1010035 : Blo 1008601 1010035 := bstep (se 1 (by rfl) ⟨757526, by rfl⟩ : syracuseStep 1010035 = 1515053) B1515053
theorem B1010051 : Blo 1008601 1010051 := bstep (se 1 (by rfl) ⟨757538, by rfl⟩ : syracuseStep 1010051 = 1515077) B1515077
theorem B1010067 : Blo 1008601 1010067 := bstep (se 1 (by rfl) ⟨757550, by rfl⟩ : syracuseStep 1010067 = 1515101) B1515101
theorem B1010083 : Blo 1008601 1010083 := bstep (se 1 (by rfl) ⟨757562, by rfl⟩ : syracuseStep 1010083 = 1515125) B1515125
theorem B1010099 : Blo 1008601 1010099 := bstep (se 1 (by rfl) ⟨757574, by rfl⟩ : syracuseStep 1010099 = 1515149) B1515149
theorem B1010115 : Blo 1008601 1010115 := bstep (se 1 (by rfl) ⟨757586, by rfl⟩ : syracuseStep 1010115 = 1515173) B1515173
theorem B1010131 : Blo 1008601 1010131 := bstep (se 1 (by rfl) ⟨757598, by rfl⟩ : syracuseStep 1010131 = 1515197) B1515197
theorem B1010147 : Blo 1008601 1010147 := bstep (se 1 (by rfl) ⟨757610, by rfl⟩ : syracuseStep 1010147 = 1515221) B1515221
theorem B1010163 : Blo 1008601 1010163 := bstep (se 1 (by rfl) ⟨757622, by rfl⟩ : syracuseStep 1010163 = 1515245) B1515245
theorem B1010179 : Blo 1008601 1010179 := bstep (se 1 (by rfl) ⟨757634, by rfl⟩ : syracuseStep 1010179 = 1515269) B1515269
theorem B1010195 : Blo 1008601 1010195 := bstep (se 1 (by rfl) ⟨757646, by rfl⟩ : syracuseStep 1010195 = 1515293) B1515293
theorem B1010211 : Blo 1008601 1010211 := bstep (se 1 (by rfl) ⟨757658, by rfl⟩ : syracuseStep 1010211 = 1515317) B1515317
theorem B2878001 : Blo 1008601 2878001 := bstep (se 2 (by rfl) ⟨1079250, by rfl⟩ : syracuseStep 2878001 = 2158501) B2158501
theorem B1010227 : Blo 1008601 1010227 := bstep (se 1 (by rfl) ⟨757670, by rfl⟩ : syracuseStep 1010227 = 1515341) B1515341
theorem B1010243 : Blo 1008601 1010243 := bstep (se 1 (by rfl) ⟨757682, by rfl⟩ : syracuseStep 1010243 = 1515365) B1515365
theorem B1010259 : Blo 1008601 1010259 := bstep (se 1 (by rfl) ⟨757694, by rfl⟩ : syracuseStep 1010259 = 1515389) B1515389
theorem B1010275 : Blo 1008601 1010275 := bstep (se 1 (by rfl) ⟨757706, by rfl⟩ : syracuseStep 1010275 = 1515413) B1515413
theorem B1010291 : Blo 1008601 1010291 := bstep (se 1 (by rfl) ⟨757718, by rfl⟩ : syracuseStep 1010291 = 1515437) B1515437
theorem B1010307 : Blo 1008601 1010307 := bstep (se 1 (by rfl) ⟨757730, by rfl⟩ : syracuseStep 1010307 = 1515461) B1515461
theorem B1010323 : Blo 1008601 1010323 := bstep (se 1 (by rfl) ⟨757742, by rfl⟩ : syracuseStep 1010323 = 1515485) B1515485
theorem B1010339 : Blo 1008601 1010339 := bstep (se 1 (by rfl) ⟨757754, by rfl⟩ : syracuseStep 1010339 = 1515509) B1515509
theorem B1010355 : Blo 1008601 1010355 := bstep (se 1 (by rfl) ⟨757766, by rfl⟩ : syracuseStep 1010355 = 1515533) B1515533
theorem B1010371 : Blo 1008601 1010371 := bstep (se 1 (by rfl) ⟨757778, by rfl⟩ : syracuseStep 1010371 = 1515557) B1515557
theorem B1010387 : Blo 1008601 1010387 := bstep (se 1 (by rfl) ⟨757790, by rfl⟩ : syracuseStep 1010387 = 1515581) B1515581
theorem B1010403 : Blo 1008601 1010403 := bstep (se 1 (by rfl) ⟨757802, by rfl⟩ : syracuseStep 1010403 = 1515605) B1515605
theorem B1010419 : Blo 1008601 1010419 := bstep (se 1 (by rfl) ⟨757814, by rfl⟩ : syracuseStep 1010419 = 1515629) B1515629
theorem B1010435 : Blo 1008601 1010435 := bstep (se 1 (by rfl) ⟨757826, by rfl⟩ : syracuseStep 1010435 = 1515653) B1515653
theorem B12282637 : Blo 1008601 12282637 := bstep (se 3 (by rfl) ⟨2302994, by rfl⟩ : syracuseStep 12282637 = 4605989) B4605989
theorem B1010451 : Blo 1008601 1010451 := bstep (se 1 (by rfl) ⟨757838, by rfl⟩ : syracuseStep 1010451 = 1515677) B1515677
theorem B1436449 : Blo 1008601 1436449 := bstep (se 2 (by rfl) ⟨538668, by rfl⟩ : syracuseStep 1436449 = 1077337) B1077337
theorem B1010467 : Blo 1008601 1010467 := bstep (se 1 (by rfl) ⟨757850, by rfl⟩ : syracuseStep 1010467 = 1515701) B1515701
theorem B1010483 : Blo 1008601 1010483 := bstep (se 1 (by rfl) ⟨757862, by rfl⟩ : syracuseStep 1010483 = 1515725) B1515725
theorem B1731379 : Blo 1008601 1731379 := bstep (se 1 (by rfl) ⟨1298534, by rfl⟩ : syracuseStep 1731379 = 2597069) B2597069
theorem B1010499 : Blo 1008601 1010499 := bstep (se 1 (by rfl) ⟨757874, by rfl⟩ : syracuseStep 1010499 = 1515749) B1515749
theorem B1010515 : Blo 1008601 1010515 := bstep (se 1 (by rfl) ⟨757886, by rfl⟩ : syracuseStep 1010515 = 1515773) B1515773
theorem B1010531 : Blo 1008601 1010531 := bstep (se 1 (by rfl) ⟨757898, by rfl⟩ : syracuseStep 1010531 = 1515797) B1515797
theorem B2157425 : Blo 1008601 2157425 := bstep (se 2 (by rfl) ⟨809034, by rfl⟩ : syracuseStep 2157425 = 1618069) B1618069
theorem B1010547 : Blo 1008601 1010547 := bstep (se 1 (by rfl) ⟨757910, by rfl⟩ : syracuseStep 1010547 = 1515821) B1515821
theorem B1010563 : Blo 1008601 1010563 := bstep (se 1 (by rfl) ⟨757922, by rfl⟩ : syracuseStep 1010563 = 1515845) B1515845
theorem B5761925 : Blo 1008601 5761925 := bstep (se 4 (by rfl) ⟨540180, by rfl⟩ : syracuseStep 5761925 = 1080361) B1080361
theorem B1436563 : Blo 1008601 1436563 := bstep (se 1 (by rfl) ⟨1077422, by rfl⟩ : syracuseStep 1436563 = 2154845) B2154845
theorem B1010579 : Blo 1008601 1010579 := bstep (se 1 (by rfl) ⟨757934, by rfl⟩ : syracuseStep 1010579 = 1515869) B1515869
theorem B1010595 : Blo 1008601 1010595 := bstep (se 1 (by rfl) ⟨757946, by rfl⟩ : syracuseStep 1010595 = 1515893) B1515893
theorem B3238829 : Blo 1008601 3238829 := bstep (se 3 (by rfl) ⟨607280, by rfl⟩ : syracuseStep 3238829 = 1214561) B1214561
theorem B3074989 : Blo 1008601 3074989 := bstep (se 3 (by rfl) ⟨576560, by rfl⟩ : syracuseStep 3074989 = 1153121) B1153121
theorem B1010611 : Blo 1008601 1010611 := bstep (se 1 (by rfl) ⟨757958, by rfl⟩ : syracuseStep 1010611 = 1515917) B1515917
theorem B1010627 : Blo 1008601 1010627 := bstep (se 1 (by rfl) ⟨757970, by rfl⟩ : syracuseStep 1010627 = 1515941) B1515941
theorem B1010643 : Blo 1008601 1010643 := bstep (se 1 (by rfl) ⟨757982, by rfl⟩ : syracuseStep 1010643 = 1515965) B1515965
theorem B1010659 : Blo 1008601 1010659 := bstep (se 1 (by rfl) ⟨757994, by rfl⟩ : syracuseStep 1010659 = 1515989) B1515989
theorem B1010675 : Blo 1008601 1010675 := bstep (se 1 (by rfl) ⟨758006, by rfl⟩ : syracuseStep 1010675 = 1516013) B1516013
theorem B1010691 : Blo 1008601 1010691 := bstep (se 1 (by rfl) ⟨758018, by rfl⟩ : syracuseStep 1010691 = 1516037) B1516037
theorem B1010707 : Blo 1008601 1010707 := bstep (se 1 (by rfl) ⟨758030, by rfl⟩ : syracuseStep 1010707 = 1516061) B1516061
theorem B1010723 : Blo 1008601 1010723 := bstep (se 1 (by rfl) ⟨758042, by rfl⟩ : syracuseStep 1010723 = 1516085) B1516085
theorem B1010739 : Blo 1008601 1010739 := bstep (se 1 (by rfl) ⟨758054, by rfl⟩ : syracuseStep 1010739 = 1516109) B1516109
theorem B1010755 : Blo 1008601 1010755 := bstep (se 1 (by rfl) ⟨758066, by rfl⟩ : syracuseStep 1010755 = 1516133) B1516133
theorem B1010771 : Blo 1008601 1010771 := bstep (se 1 (by rfl) ⟨758078, by rfl⟩ : syracuseStep 1010771 = 1516157) B1516157
theorem B1010787 : Blo 1008601 1010787 := bstep (se 1 (by rfl) ⟨758090, by rfl⟩ : syracuseStep 1010787 = 1516181) B1516181
theorem B1010803 : Blo 1008601 1010803 := bstep (se 1 (by rfl) ⟨758102, by rfl⟩ : syracuseStep 1010803 = 1516205) B1516205
theorem B1010819 : Blo 1008601 1010819 := bstep (se 1 (by rfl) ⟨758114, by rfl⟩ : syracuseStep 1010819 = 1516229) B1516229
theorem B1010835 : Blo 1008601 1010835 := bstep (se 1 (by rfl) ⟨758126, by rfl⟩ : syracuseStep 1010835 = 1516253) B1516253
theorem B1010851 : Blo 1008601 1010851 := bstep (se 1 (by rfl) ⟨758138, by rfl⟩ : syracuseStep 1010851 = 1516277) B1516277
theorem B1010867 : Blo 1008601 1010867 := bstep (se 1 (by rfl) ⟨758150, by rfl⟩ : syracuseStep 1010867 = 1516301) B1516301
theorem B1010883 : Blo 1008601 1010883 := bstep (se 1 (by rfl) ⟨758162, by rfl⟩ : syracuseStep 1010883 = 1516325) B1516325
theorem B1010899 : Blo 1008601 1010899 := bstep (se 1 (by rfl) ⟨758174, by rfl⟩ : syracuseStep 1010899 = 1516349) B1516349
theorem B1010915 : Blo 1008601 1010915 := bstep (se 1 (by rfl) ⟨758186, by rfl⟩ : syracuseStep 1010915 = 1516373) B1516373
theorem B1010931 : Blo 1008601 1010931 := bstep (se 1 (by rfl) ⟨758198, by rfl⟩ : syracuseStep 1010931 = 1516397) B1516397
theorem B1010947 : Blo 1008601 1010947 := bstep (se 1 (by rfl) ⟨758210, by rfl⟩ : syracuseStep 1010947 = 1516421) B1516421
theorem B1010963 : Blo 1008601 1010963 := bstep (se 1 (by rfl) ⟨758222, by rfl⟩ : syracuseStep 1010963 = 1516445) B1516445
theorem B1010979 : Blo 1008601 1010979 := bstep (se 1 (by rfl) ⟨758234, by rfl⟩ : syracuseStep 1010979 = 1516469) B1516469
theorem B1010995 : Blo 1008601 1010995 := bstep (se 1 (by rfl) ⟨758246, by rfl⟩ : syracuseStep 1010995 = 1516493) B1516493
theorem B1011011 : Blo 1008601 1011011 := bstep (se 1 (by rfl) ⟨758258, by rfl⟩ : syracuseStep 1011011 = 1516517) B1516517
theorem B1011027 : Blo 1008601 1011027 := bstep (se 1 (by rfl) ⟨758270, by rfl⟩ : syracuseStep 1011027 = 1516541) B1516541
theorem B1011043 : Blo 1008601 1011043 := bstep (se 1 (by rfl) ⟨758282, by rfl⟩ : syracuseStep 1011043 = 1516565) B1516565
theorem B1011059 : Blo 1008601 1011059 := bstep (se 1 (by rfl) ⟨758294, by rfl⟩ : syracuseStep 1011059 = 1516589) B1516589
theorem B1011075 : Blo 1008601 1011075 := bstep (se 1 (by rfl) ⟨758306, by rfl⟩ : syracuseStep 1011075 = 1516613) B1516613
theorem B1011091 : Blo 1008601 1011091 := bstep (se 1 (by rfl) ⟨758318, by rfl⟩ : syracuseStep 1011091 = 1516637) B1516637
theorem B1011107 : Blo 1008601 1011107 := bstep (se 1 (by rfl) ⟨758330, by rfl⟩ : syracuseStep 1011107 = 1516661) B1516661
theorem B1011123 : Blo 1008601 1011123 := bstep (se 1 (by rfl) ⟨758342, by rfl⟩ : syracuseStep 1011123 = 1516685) B1516685
theorem B1011139 : Blo 1008601 1011139 := bstep (se 1 (by rfl) ⟨758354, by rfl⟩ : syracuseStep 1011139 = 1516709) B1516709
theorem B1011155 : Blo 1008601 1011155 := bstep (se 1 (by rfl) ⟨758366, by rfl⟩ : syracuseStep 1011155 = 1516733) B1516733
theorem B1011171 : Blo 1008601 1011171 := bstep (se 1 (by rfl) ⟨758378, by rfl⟩ : syracuseStep 1011171 = 1516757) B1516757
theorem B1011187 : Blo 1008601 1011187 := bstep (se 1 (by rfl) ⟨758390, by rfl⟩ : syracuseStep 1011187 = 1516781) B1516781
theorem B1011203 : Blo 1008601 1011203 := bstep (se 1 (by rfl) ⟨758402, by rfl⟩ : syracuseStep 1011203 = 1516805) B1516805
theorem B1011219 : Blo 1008601 1011219 := bstep (se 1 (by rfl) ⟨758414, by rfl⟩ : syracuseStep 1011219 = 1516829) B1516829
theorem B1011235 : Blo 1008601 1011235 := bstep (se 1 (by rfl) ⟨758426, by rfl⟩ : syracuseStep 1011235 = 1516853) B1516853
theorem B5762609 : Blo 1008601 5762609 := bstep (se 2 (by rfl) ⟨2160978, by rfl⟩ : syracuseStep 5762609 = 4321957) B4321957
theorem B1011251 : Blo 1008601 1011251 := bstep (se 1 (by rfl) ⟨758438, by rfl⟩ : syracuseStep 1011251 = 1516877) B1516877
theorem B1011267 : Blo 1008601 1011267 := bstep (se 1 (by rfl) ⟨758450, by rfl⟩ : syracuseStep 1011267 = 1516901) B1516901
theorem B1011283 : Blo 1008601 1011283 := bstep (se 1 (by rfl) ⟨758462, by rfl⟩ : syracuseStep 1011283 = 1516925) B1516925
theorem B1011299 : Blo 1008601 1011299 := bstep (se 1 (by rfl) ⟨758474, by rfl⟩ : syracuseStep 1011299 = 1516949) B1516949
theorem B1011315 : Blo 1008601 1011315 := bstep (se 1 (by rfl) ⟨758486, by rfl⟩ : syracuseStep 1011315 = 1516973) B1516973
theorem B1011331 : Blo 1008601 1011331 := bstep (se 1 (by rfl) ⟨758498, by rfl⟩ : syracuseStep 1011331 = 1516997) B1516997
theorem B1011347 : Blo 1008601 1011347 := bstep (se 1 (by rfl) ⟨758510, by rfl⟩ : syracuseStep 1011347 = 1517021) B1517021
theorem B1011363 : Blo 1008601 1011363 := bstep (se 1 (by rfl) ⟨758522, by rfl⟩ : syracuseStep 1011363 = 1517045) B1517045
theorem B3239597 : Blo 1008601 3239597 := bstep (se 3 (by rfl) ⟨607424, by rfl⟩ : syracuseStep 3239597 = 1214849) B1214849
theorem B1011379 : Blo 1008601 1011379 := bstep (se 1 (by rfl) ⟨758534, by rfl⟩ : syracuseStep 1011379 = 1517069) B1517069
theorem B1011395 : Blo 1008601 1011395 := bstep (se 1 (by rfl) ⟨758546, by rfl⟩ : syracuseStep 1011395 = 1517093) B1517093
theorem B1011411 : Blo 1008601 1011411 := bstep (se 1 (by rfl) ⟨758558, by rfl⟩ : syracuseStep 1011411 = 1517117) B1517117
theorem B1011427 : Blo 1008601 1011427 := bstep (se 1 (by rfl) ⟨758570, by rfl⟩ : syracuseStep 1011427 = 1517141) B1517141
theorem B1011443 : Blo 1008601 1011443 := bstep (se 1 (by rfl) ⟨758582, by rfl⟩ : syracuseStep 1011443 = 1517165) B1517165
theorem B1011459 : Blo 1008601 1011459 := bstep (se 1 (by rfl) ⟨758594, by rfl⟩ : syracuseStep 1011459 = 1517189) B1517189
theorem B1011475 : Blo 1008601 1011475 := bstep (se 1 (by rfl) ⟨758606, by rfl⟩ : syracuseStep 1011475 = 1517213) B1517213
theorem B1011491 : Blo 1008601 1011491 := bstep (se 1 (by rfl) ⟨758618, by rfl⟩ : syracuseStep 1011491 = 1517237) B1517237
theorem B1011507 : Blo 1008601 1011507 := bstep (se 1 (by rfl) ⟨758630, by rfl⟩ : syracuseStep 1011507 = 1517261) B1517261
theorem B1011523 : Blo 1008601 1011523 := bstep (se 1 (by rfl) ⟨758642, by rfl⟩ : syracuseStep 1011523 = 1517285) B1517285
theorem B5533517 : Blo 1008601 5533517 := bstep (se 3 (by rfl) ⟨1037534, by rfl⟩ : syracuseStep 5533517 = 2075069) B2075069
theorem B6156109 : Blo 1008601 6156109 := bstep (se 3 (by rfl) ⟨1154270, by rfl⟩ : syracuseStep 6156109 = 2308541) B2308541
theorem B1011539 : Blo 1008601 1011539 := bstep (se 1 (by rfl) ⟨758654, by rfl⟩ : syracuseStep 1011539 = 1517309) B1517309
theorem B1011555 : Blo 1008601 1011555 := bstep (se 1 (by rfl) ⟨758666, by rfl⟩ : syracuseStep 1011555 = 1517333) B1517333
theorem B1011571 : Blo 1008601 1011571 := bstep (se 1 (by rfl) ⟨758678, by rfl⟩ : syracuseStep 1011571 = 1517357) B1517357
theorem B1404787 : Blo 1008601 1404787 := bstep (se 1 (by rfl) ⟨1053590, by rfl⟩ : syracuseStep 1404787 = 2107181) B2107181
theorem B1011587 : Blo 1008601 1011587 := bstep (se 1 (by rfl) ⟨758690, by rfl⟩ : syracuseStep 1011587 = 1517381) B1517381
theorem B1011603 : Blo 1008601 1011603 := bstep (se 1 (by rfl) ⟨758702, by rfl⟩ : syracuseStep 1011603 = 1517405) B1517405
theorem B1011619 : Blo 1008601 1011619 := bstep (se 1 (by rfl) ⟨758714, by rfl⟩ : syracuseStep 1011619 = 1517429) B1517429
theorem B1011635 : Blo 1008601 1011635 := bstep (se 1 (by rfl) ⟨758726, by rfl⟩ : syracuseStep 1011635 = 1517453) B1517453
theorem B1011651 : Blo 1008601 1011651 := bstep (se 1 (by rfl) ⟨758738, by rfl⟩ : syracuseStep 1011651 = 1517477) B1517477
theorem B1011667 : Blo 1008601 1011667 := bstep (se 1 (by rfl) ⟨758750, by rfl⟩ : syracuseStep 1011667 = 1517501) B1517501
theorem B2879459 : Blo 1008601 2879459 := bstep (se 1 (by rfl) ⟨2159594, by rfl⟩ : syracuseStep 2879459 = 4319189) B4319189
theorem B1011683 : Blo 1008601 1011683 := bstep (se 1 (by rfl) ⟨758762, by rfl⟩ : syracuseStep 1011683 = 1517525) B1517525
theorem B5107697 : Blo 1008601 5107697 := bstep (se 2 (by rfl) ⟨1915386, by rfl⟩ : syracuseStep 5107697 = 3830773) B3830773
theorem B1011699 : Blo 1008601 1011699 := bstep (se 1 (by rfl) ⟨758774, by rfl⟩ : syracuseStep 1011699 = 1517549) B1517549
theorem B1011715 : Blo 1008601 1011715 := bstep (se 1 (by rfl) ⟨758786, by rfl⟩ : syracuseStep 1011715 = 1517573) B1517573
theorem B1011731 : Blo 1008601 1011731 := bstep (se 1 (by rfl) ⟨758798, by rfl⟩ : syracuseStep 1011731 = 1517597) B1517597
theorem B1011747 : Blo 1008601 1011747 := bstep (se 1 (by rfl) ⟨758810, by rfl⟩ : syracuseStep 1011747 = 1517621) B1517621
theorem B1011763 : Blo 1008601 1011763 := bstep (se 1 (by rfl) ⟨758822, by rfl⟩ : syracuseStep 1011763 = 1517645) B1517645
theorem B1011779 : Blo 1008601 1011779 := bstep (se 1 (by rfl) ⟨758834, by rfl⟩ : syracuseStep 1011779 = 1517669) B1517669
theorem B1011795 : Blo 1008601 1011795 := bstep (se 1 (by rfl) ⟨758846, by rfl⟩ : syracuseStep 1011795 = 1517693) B1517693
theorem B1011811 : Blo 1008601 1011811 := bstep (se 1 (by rfl) ⟨758858, by rfl⟩ : syracuseStep 1011811 = 1517717) B1517717
theorem B1011827 : Blo 1008601 1011827 := bstep (se 1 (by rfl) ⟨758870, by rfl⟩ : syracuseStep 1011827 = 1517741) B1517741
theorem B1011843 : Blo 1008601 1011843 := bstep (se 1 (by rfl) ⟨758882, by rfl⟩ : syracuseStep 1011843 = 1517765) B1517765
theorem B1011859 : Blo 1008601 1011859 := bstep (se 1 (by rfl) ⟨758894, by rfl⟩ : syracuseStep 1011859 = 1517789) B1517789
theorem B1011875 : Blo 1008601 1011875 := bstep (se 1 (by rfl) ⟨758906, by rfl⟩ : syracuseStep 1011875 = 1517813) B1517813
theorem B3240109 : Blo 1008601 3240109 := bstep (se 3 (by rfl) ⟨607520, by rfl⟩ : syracuseStep 3240109 = 1215041) B1215041
theorem B1011891 : Blo 1008601 1011891 := bstep (se 1 (by rfl) ⟨758918, by rfl⟩ : syracuseStep 1011891 = 1517837) B1517837
theorem B1011907 : Blo 1008601 1011907 := bstep (se 1 (by rfl) ⟨758930, by rfl⟩ : syracuseStep 1011907 = 1517861) B1517861
theorem B1437907 : Blo 1008601 1437907 := bstep (se 1 (by rfl) ⟨1078430, by rfl⟩ : syracuseStep 1437907 = 2156861) B2156861
theorem B1011923 : Blo 1008601 1011923 := bstep (se 1 (by rfl) ⟨758942, by rfl⟩ : syracuseStep 1011923 = 1517885) B1517885
theorem B1011939 : Blo 1008601 1011939 := bstep (se 1 (by rfl) ⟨758954, by rfl⟩ : syracuseStep 1011939 = 1517909) B1517909
theorem B1011955 : Blo 1008601 1011955 := bstep (se 1 (by rfl) ⟨758966, by rfl⟩ : syracuseStep 1011955 = 1517933) B1517933
theorem B1011971 : Blo 1008601 1011971 := bstep (se 1 (by rfl) ⟨758978, by rfl⟩ : syracuseStep 1011971 = 1517957) B1517957
theorem B1011987 : Blo 1008601 1011987 := bstep (se 1 (by rfl) ⟨758990, by rfl⟩ : syracuseStep 1011987 = 1517981) B1517981
theorem B1012003 : Blo 1008601 1012003 := bstep (se 1 (by rfl) ⟨759002, by rfl⟩ : syracuseStep 1012003 = 1518005) B1518005
theorem B2912561 : Blo 1008601 2912561 := bstep (se 2 (by rfl) ⟨1092210, by rfl⟩ : syracuseStep 2912561 = 2184421) B2184421
theorem B1012019 : Blo 1008601 1012019 := bstep (se 1 (by rfl) ⟨759014, by rfl⟩ : syracuseStep 1012019 = 1518029) B1518029
theorem B1012035 : Blo 1008601 1012035 := bstep (se 1 (by rfl) ⟨759026, by rfl⟩ : syracuseStep 1012035 = 1518053) B1518053
theorem B1012051 : Blo 1008601 1012051 := bstep (se 1 (by rfl) ⟨759038, by rfl⟩ : syracuseStep 1012051 = 1518077) B1518077
theorem B1012067 : Blo 1008601 1012067 := bstep (se 1 (by rfl) ⟨759050, by rfl⟩ : syracuseStep 1012067 = 1518101) B1518101
theorem B4321649 : Blo 1008601 4321649 := bstep (se 2 (by rfl) ⟨1620618, by rfl⟩ : syracuseStep 4321649 = 3241237) B3241237
theorem B1077619 : Blo 1008601 1077619 := bstep (se 1 (by rfl) ⟨808214, by rfl⟩ : syracuseStep 1077619 = 1616429) B1616429
theorem B1012083 : Blo 1008601 1012083 := bstep (se 1 (by rfl) ⟨759062, by rfl⟩ : syracuseStep 1012083 = 1518125) B1518125
theorem B2158979 : Blo 1008601 2158979 := bstep (se 1 (by rfl) ⟨1619234, by rfl⟩ : syracuseStep 2158979 = 3238469) B3238469
theorem B1012099 : Blo 1008601 1012099 := bstep (se 1 (by rfl) ⟨759074, by rfl⟩ : syracuseStep 1012099 = 1518149) B1518149
theorem B1012115 : Blo 1008601 1012115 := bstep (se 1 (by rfl) ⟨759086, by rfl⟩ : syracuseStep 1012115 = 1518173) B1518173
theorem B1012131 : Blo 1008601 1012131 := bstep (se 1 (by rfl) ⟨759098, by rfl⟩ : syracuseStep 1012131 = 1518197) B1518197
theorem B1012147 : Blo 1008601 1012147 := bstep (se 1 (by rfl) ⟨759110, by rfl⟩ : syracuseStep 1012147 = 1518221) B1518221
theorem B1012163 : Blo 1008601 1012163 := bstep (se 1 (by rfl) ⟨759122, by rfl⟩ : syracuseStep 1012163 = 1518245) B1518245
theorem B1012179 : Blo 1008601 1012179 := bstep (se 1 (by rfl) ⟨759134, by rfl⟩ : syracuseStep 1012179 = 1518269) B1518269
theorem B25850339 : Blo 1008601 25850339 := bstep (se 1 (by rfl) ⟨19387754, by rfl⟩ : syracuseStep 25850339 = 38775509) B38775509
theorem B1012195 : Blo 1008601 1012195 := bstep (se 1 (by rfl) ⟨759146, by rfl⟩ : syracuseStep 1012195 = 1518293) B1518293
theorem B1536499 : Blo 1008601 1536499 := bstep (se 1 (by rfl) ⟨1152374, by rfl⟩ : syracuseStep 1536499 = 2304749) B2304749
theorem B1012211 : Blo 1008601 1012211 := bstep (se 1 (by rfl) ⟨759158, by rfl⟩ : syracuseStep 1012211 = 1518317) B1518317
theorem B1012227 : Blo 1008601 1012227 := bstep (se 1 (by rfl) ⟨759170, by rfl⟩ : syracuseStep 1012227 = 1518341) B1518341
theorem B1012243 : Blo 1008601 1012243 := bstep (se 1 (by rfl) ⟨759182, by rfl⟩ : syracuseStep 1012243 = 1518365) B1518365
theorem B1012259 : Blo 1008601 1012259 := bstep (se 1 (by rfl) ⟨759194, by rfl⟩ : syracuseStep 1012259 = 1518389) B1518389
theorem B1012275 : Blo 1008601 1012275 := bstep (se 1 (by rfl) ⟨759206, by rfl⟩ : syracuseStep 1012275 = 1518413) B1518413
theorem B1012291 : Blo 1008601 1012291 := bstep (se 1 (by rfl) ⟨759218, by rfl⟩ : syracuseStep 1012291 = 1518437) B1518437
theorem B1012307 : Blo 1008601 1012307 := bstep (se 1 (by rfl) ⟨759230, by rfl⟩ : syracuseStep 1012307 = 1518461) B1518461
theorem B1012323 : Blo 1008601 1012323 := bstep (se 1 (by rfl) ⟨759242, by rfl⟩ : syracuseStep 1012323 = 1518485) B1518485
theorem B1012339 : Blo 1008601 1012339 := bstep (se 1 (by rfl) ⟨759254, by rfl⟩ : syracuseStep 1012339 = 1518509) B1518509
theorem B1012355 : Blo 1008601 1012355 := bstep (se 1 (by rfl) ⟨759266, by rfl⟩ : syracuseStep 1012355 = 1518533) B1518533
theorem B3404429 : Blo 1008601 3404429 := bstep (se 3 (by rfl) ⟨638330, by rfl⟩ : syracuseStep 3404429 = 1276661) B1276661
theorem B1012371 : Blo 1008601 1012371 := bstep (se 1 (by rfl) ⟨759278, by rfl⟩ : syracuseStep 1012371 = 1518557) B1518557
theorem B3240611 : Blo 1008601 3240611 := bstep (se 1 (by rfl) ⟨2430458, by rfl⟩ : syracuseStep 3240611 = 4860917) B4860917
theorem B1012387 : Blo 1008601 1012387 := bstep (se 1 (by rfl) ⟨759290, by rfl⟩ : syracuseStep 1012387 = 1518581) B1518581
theorem B1012403 : Blo 1008601 1012403 := bstep (se 1 (by rfl) ⟨759302, by rfl⟩ : syracuseStep 1012403 = 1518605) B1518605
theorem B3404483 : Blo 1008601 3404483 := bstep (se 1 (by rfl) ⟨2553362, by rfl⟩ : syracuseStep 3404483 = 5106725) B5106725
theorem B1012419 : Blo 1008601 1012419 := bstep (se 1 (by rfl) ⟨759314, by rfl⟩ : syracuseStep 1012419 = 1518629) B1518629
theorem B1012435 : Blo 1008601 1012435 := bstep (se 1 (by rfl) ⟨759326, by rfl⟩ : syracuseStep 1012435 = 1518653) B1518653
theorem B1012451 : Blo 1008601 1012451 := bstep (se 1 (by rfl) ⟨759338, by rfl⟩ : syracuseStep 1012451 = 1518677) B1518677
theorem B1012467 : Blo 1008601 1012467 := bstep (se 1 (by rfl) ⟨759350, by rfl⟩ : syracuseStep 1012467 = 1518701) B1518701
theorem B1012483 : Blo 1008601 1012483 := bstep (se 1 (by rfl) ⟨759362, by rfl⟩ : syracuseStep 1012483 = 1518725) B1518725
theorem B2880269 : Blo 1008601 2880269 := bstep (se 3 (by rfl) ⟨540050, by rfl⟩ : syracuseStep 2880269 = 1080101) B1080101
theorem B1012499 : Blo 1008601 1012499 := bstep (se 1 (by rfl) ⟨759374, by rfl⟩ : syracuseStep 1012499 = 1518749) B1518749
theorem B1012515 : Blo 1008601 1012515 := bstep (se 1 (by rfl) ⟨759386, by rfl⟩ : syracuseStep 1012515 = 1518773) B1518773
theorem B1012531 : Blo 1008601 1012531 := bstep (se 1 (by rfl) ⟨759398, by rfl⟩ : syracuseStep 1012531 = 1518797) B1518797
theorem B1012547 : Blo 1008601 1012547 := bstep (se 1 (by rfl) ⟨759410, by rfl⟩ : syracuseStep 1012547 = 1518821) B1518821
theorem B1012563 : Blo 1008601 1012563 := bstep (se 1 (by rfl) ⟨759422, by rfl⟩ : syracuseStep 1012563 = 1518845) B1518845
theorem B1012579 : Blo 1008601 1012579 := bstep (se 1 (by rfl) ⟨759434, by rfl⟩ : syracuseStep 1012579 = 1518869) B1518869
theorem B1012595 : Blo 1008601 1012595 := bstep (se 1 (by rfl) ⟨759446, by rfl⟩ : syracuseStep 1012595 = 1518893) B1518893
theorem B2880461 : Blo 1008601 2880461 := bstep (se 3 (by rfl) ⟨540086, by rfl⟩ : syracuseStep 2880461 = 1080173) B1080173
theorem B3404753 : Blo 1008601 3404753 := bstep (se 2 (by rfl) ⟨1276782, by rfl⟩ : syracuseStep 3404753 = 2553565) B2553565
theorem B5764067 : Blo 1008601 5764067 := bstep (se 1 (by rfl) ⟨4323050, by rfl⟩ : syracuseStep 5764067 = 8646101) B8646101
theorem B10941425 : Blo 1008601 10941425 := bstep (se 2 (by rfl) ⟨4103034, by rfl⟩ : syracuseStep 10941425 = 8206069) B8206069
theorem B2553059 : Blo 1008601 2553059 := bstep (se 1 (by rfl) ⟨1914794, by rfl⟩ : syracuseStep 2553059 = 3829589) B3829589
theorem B6911281 : Blo 1008601 6911281 := bstep (se 2 (by rfl) ⟨2591730, by rfl⟩ : syracuseStep 6911281 = 5183461) B5183461
theorem B1439041 : Blo 1008601 1439041 := bstep (se 2 (by rfl) ⟨539640, by rfl⟩ : syracuseStep 1439041 = 1079281) B1079281
theorem B9696611 : Blo 1008601 9696611 := bstep (se 1 (by rfl) ⟨7272458, by rfl⟩ : syracuseStep 9696611 = 14544917) B14544917
theorem B1439137 : Blo 1008601 1439137 := bstep (se 2 (by rfl) ⟨539676, by rfl⟩ : syracuseStep 1439137 = 1079353) B1079353
theorem B5109155 : Blo 1008601 5109155 := bstep (se 1 (by rfl) ⟨3831866, by rfl⟩ : syracuseStep 5109155 = 7663733) B7663733
theorem B3831245 : Blo 1008601 3831245 := bstep (se 3 (by rfl) ⟨718358, by rfl⟩ : syracuseStep 3831245 = 1436717) B1436717
theorem B3405293 : Blo 1008601 3405293 := bstep (se 3 (by rfl) ⟨638492, by rfl⟩ : syracuseStep 3405293 = 1276985) B1276985
theorem B6911501 : Blo 1008601 6911501 := bstep (se 3 (by rfl) ⟨1295906, by rfl⟩ : syracuseStep 6911501 = 2591813) B2591813
theorem B3405347 : Blo 1008601 3405347 := bstep (se 1 (by rfl) ⟨2554010, by rfl⟩ : syracuseStep 3405347 = 5108021) B5108021
theorem B4322915 : Blo 1008601 4322915 := bstep (se 1 (by rfl) ⟨3242186, by rfl⟩ : syracuseStep 4322915 = 6484373) B6484373
theorem B3405617 : Blo 1008601 3405617 := bstep (se 2 (by rfl) ⟨1277106, by rfl⟩ : syracuseStep 3405617 = 2554213) B2554213
theorem B5470021 : Blo 1008601 5470021 := bstep (se 4 (by rfl) ⟨512814, by rfl⟩ : syracuseStep 5470021 = 1025629) B1025629
theorem B1439633 : Blo 1008601 1439633 := bstep (se 2 (by rfl) ⟨539862, by rfl⟩ : syracuseStep 1439633 = 1079725) B1079725
theorem B2881453 : Blo 1008601 2881453 := bstep (se 3 (by rfl) ⟨540272, by rfl⟩ : syracuseStep 2881453 = 1080545) B1080545
theorem B7665677 : Blo 1008601 7665677 := bstep (se 3 (by rfl) ⟨1437314, by rfl⟩ : syracuseStep 7665677 = 2874629) B2874629
theorem B1702019 : Blo 1008601 1702019 := bstep (se 1 (by rfl) ⟨1276514, by rfl⟩ : syracuseStep 1702019 = 2553029) B2553029
theorem B2554001 : Blo 1008601 2554001 := bstep (se 2 (by rfl) ⟨957750, by rfl⟩ : syracuseStep 2554001 = 1915501) B1915501
theorem B2554051 : Blo 1008601 2554051 := bstep (se 1 (by rfl) ⟨1915538, by rfl⟩ : syracuseStep 2554051 = 3831077) B3831077
theorem B5109965 : Blo 1008601 5109965 := bstep (se 3 (by rfl) ⟨958118, by rfl⟩ : syracuseStep 5109965 = 1916237) B1916237
theorem B1079507 : Blo 1008601 1079507 := bstep (se 1 (by rfl) ⟨809630, by rfl⟩ : syracuseStep 1079507 = 1619261) B1619261
theorem B8190179 : Blo 1008601 8190179 := bstep (se 1 (by rfl) ⟨6142634, by rfl⟩ : syracuseStep 8190179 = 12285269) B12285269
theorem B3832049 : Blo 1008601 3832049 := bstep (se 2 (by rfl) ⟨1437018, by rfl⟩ : syracuseStep 3832049 = 2874037) B2874037
theorem B1702147 : Blo 1008601 1702147 := bstep (se 1 (by rfl) ⟨1276610, by rfl⟩ : syracuseStep 1702147 = 2553221) B2553221
theorem B3406157 : Blo 1008601 3406157 := bstep (se 3 (by rfl) ⟨638654, by rfl⟩ : syracuseStep 3406157 = 1277309) B1277309
theorem B2554193 : Blo 1008601 2554193 := bstep (se 2 (by rfl) ⟨957822, by rfl⟩ : syracuseStep 2554193 = 1915645) B1915645
theorem B3406211 : Blo 1008601 3406211 := bstep (se 1 (by rfl) ⟨2554658, by rfl⟩ : syracuseStep 3406211 = 5109317) B5109317
theorem B1702289 : Blo 1008601 1702289 := bstep (se 2 (by rfl) ⟨638358, by rfl⟩ : syracuseStep 1702289 = 1276717) B1276717
theorem B3242467 : Blo 1008601 3242467 := bstep (se 1 (by rfl) ⟨2431850, by rfl⟩ : syracuseStep 3242467 = 4863701) B4863701
theorem B1702417 : Blo 1008601 1702417 := bstep (se 2 (by rfl) ⟨638406, by rfl⟩ : syracuseStep 1702417 = 1276813) B1276813
theorem B2161201 : Blo 1008601 2161201 := bstep (se 2 (by rfl) ⟨810450, by rfl⟩ : syracuseStep 2161201 = 1620901) B1620901
theorem B1702451 : Blo 1008601 1702451 := bstep (se 1 (by rfl) ⟨1276838, by rfl⟩ : syracuseStep 1702451 = 2553677) B2553677
theorem B1538657 : Blo 1008601 1538657 := bstep (se 2 (by rfl) ⟨576996, by rfl⟩ : syracuseStep 1538657 = 1153993) B1153993
theorem B3406481 : Blo 1008601 3406481 := bstep (se 2 (by rfl) ⟨1277430, by rfl⟩ : syracuseStep 3406481 = 2554861) B2554861
theorem B1702579 : Blo 1008601 1702579 := bstep (se 1 (by rfl) ⟨1276934, by rfl⟩ : syracuseStep 1702579 = 2553869) B2553869
theorem B1440499 : Blo 1008601 1440499 := bstep (se 1 (by rfl) ⟨1080374, by rfl⟩ : syracuseStep 1440499 = 2160749) B2160749
theorem B1702721 : Blo 1008601 1702721 := bstep (se 2 (by rfl) ⟨638520, by rfl⟩ : syracuseStep 1702721 = 1277041) B1277041
theorem B1440595 : Blo 1008601 1440595 := bstep (se 1 (by rfl) ⟨1080446, by rfl⟩ : syracuseStep 1440595 = 2160893) B2160893
theorem B3832717 : Blo 1008601 3832717 := bstep (se 3 (by rfl) ⟨718634, by rfl⟩ : syracuseStep 3832717 = 1437269) B1437269
theorem B3242929 : Blo 1008601 3242929 := bstep (se 2 (by rfl) ⟨1216098, by rfl⟩ : syracuseStep 3242929 = 2432197) B2432197
theorem B1702849 : Blo 1008601 1702849 := bstep (se 2 (by rfl) ⟨638568, by rfl⟩ : syracuseStep 1702849 = 1277137) B1277137
theorem B1702883 : Blo 1008601 1702883 := bstep (se 1 (by rfl) ⟨1277162, by rfl⟩ : syracuseStep 1702883 = 2554325) B2554325
theorem B1703011 : Blo 1008601 1703011 := bstep (se 1 (by rfl) ⟨1277258, by rfl⟩ : syracuseStep 1703011 = 2554517) B2554517
theorem B8649827 : Blo 1008601 8649827 := bstep (se 1 (by rfl) ⟨6487370, by rfl⟩ : syracuseStep 8649827 = 12974741) B12974741
theorem B3407021 : Blo 1008601 3407021 := bstep (se 3 (by rfl) ⟨638816, by rfl⟩ : syracuseStep 3407021 = 1277633) B1277633
theorem B10386629 : Blo 1008601 10386629 := bstep (se 4 (by rfl) ⟨973746, by rfl⟩ : syracuseStep 10386629 = 1947493) B1947493
theorem B3407075 : Blo 1008601 3407075 := bstep (se 1 (by rfl) ⟨2555306, by rfl⟩ : syracuseStep 3407075 = 5110613) B5110613
theorem B1703153 : Blo 1008601 1703153 := bstep (se 2 (by rfl) ⟨638682, by rfl⟩ : syracuseStep 1703153 = 1277365) B1277365
theorem B6552845 : Blo 1008601 6552845 := bstep (se 3 (by rfl) ⟨1228658, by rfl⟩ : syracuseStep 6552845 = 2457317) B2457317
theorem B1277203 : Blo 1008601 1277203 := bstep (se 1 (by rfl) ⟨957902, by rfl⟩ : syracuseStep 1277203 = 1915805) B1915805
theorem B2555185 : Blo 1008601 2555185 := bstep (se 2 (by rfl) ⟨958194, by rfl⟩ : syracuseStep 2555185 = 1916389) B1916389
theorem B1441091 : Blo 1008601 1441091 := bstep (se 1 (by rfl) ⟨1080818, by rfl⟩ : syracuseStep 1441091 = 2161637) B2161637
theorem B1703281 : Blo 1008601 1703281 := bstep (se 2 (by rfl) ⟨638730, by rfl⟩ : syracuseStep 1703281 = 1277461) B1277461
theorem B1277299 : Blo 1008601 1277299 := bstep (se 1 (by rfl) ⟨957974, by rfl⟩ : syracuseStep 1277299 = 1915949) B1915949
theorem B1703315 : Blo 1008601 1703315 := bstep (se 1 (by rfl) ⟨1277486, by rfl⟩ : syracuseStep 1703315 = 2554973) B2554973
theorem B2424259 : Blo 1008601 2424259 := bstep (se 1 (by rfl) ⟨1818194, by rfl⟩ : syracuseStep 2424259 = 3636389) B3636389
theorem B3407345 : Blo 1008601 3407345 := bstep (se 2 (by rfl) ⟨1277754, by rfl⟩ : syracuseStep 3407345 = 2555509) B2555509
theorem B1211923 : Blo 1008601 1211923 := bstep (se 1 (by rfl) ⟨908942, by rfl⟩ : syracuseStep 1211923 = 1817885) B1817885
theorem B1703443 : Blo 1008601 1703443 := bstep (se 1 (by rfl) ⟨1277582, by rfl⟩ : syracuseStep 1703443 = 2555165) B2555165
theorem B2555459 : Blo 1008601 2555459 := bstep (se 1 (by rfl) ⟨1916594, by rfl⟩ : syracuseStep 2555459 = 3833189) B3833189
theorem B2883185 : Blo 1008601 2883185 := bstep (se 2 (by rfl) ⟨1081194, by rfl⟩ : syracuseStep 2883185 = 2162389) B2162389
theorem B1703585 : Blo 1008601 1703585 := bstep (se 2 (by rfl) ⟨638844, by rfl⟩ : syracuseStep 1703585 = 1277689) B1277689
theorem B3833507 : Blo 1008601 3833507 := bstep (se 1 (by rfl) ⟨2875130, by rfl⟩ : syracuseStep 3833507 = 5750261) B5750261
theorem B2555651 : Blo 1008601 2555651 := bstep (se 1 (by rfl) ⟨1916738, by rfl⟩ : syracuseStep 2555651 = 3833477) B3833477
theorem B1703713 : Blo 1008601 1703713 := bstep (se 2 (by rfl) ⟨638892, by rfl⟩ : syracuseStep 1703713 = 1277785) B1277785
theorem B2883377 : Blo 1008601 2883377 := bstep (se 2 (by rfl) ⟨1081266, by rfl⟩ : syracuseStep 2883377 = 2162533) B2162533
theorem B1703747 : Blo 1008601 1703747 := bstep (se 1 (by rfl) ⟨1277810, by rfl⟩ : syracuseStep 1703747 = 2555621) B2555621
theorem B1277795 : Blo 1008601 1277795 := bstep (se 1 (by rfl) ⟨958346, by rfl⟩ : syracuseStep 1277795 = 1916693) B1916693
theorem B1441729 : Blo 1008601 1441729 := bstep (se 2 (by rfl) ⟨540648, by rfl⟩ : syracuseStep 1441729 = 1081297) B1081297
theorem B1703875 : Blo 1008601 1703875 := bstep (se 1 (by rfl) ⟨1277906, by rfl⟩ : syracuseStep 1703875 = 2555813) B2555813
theorem B2556107 : Blo 1008601 2556107 := bstep (se 1 (by rfl) ⟨1917080, by rfl⟩ : syracuseStep 2556107 = 3834161) B3834161
theorem B1704395 : Blo 1008601 1704395 := bstep (se 1 (by rfl) ⟨1278296, by rfl⟩ : syracuseStep 1704395 = 2556593) B2556593
theorem B2556481 : Blo 1008601 2556481 := bstep (se 2 (by rfl) ⟨958680, by rfl⟩ : syracuseStep 2556481 = 1917361) B1917361
theorem B5112395 : Blo 1008601 5112395 := bstep (se 1 (by rfl) ⟨3834296, by rfl⟩ : syracuseStep 5112395 = 7668593) B7668593
theorem B1704523 : Blo 1008601 1704523 := bstep (se 1 (by rfl) ⟨1278392, by rfl⟩ : syracuseStep 1704523 = 2556785) B2556785
theorem B3408587 : Blo 1008601 3408587 := bstep (se 1 (by rfl) ⟨2556440, by rfl⟩ : syracuseStep 3408587 = 5112881) B5112881
theorem B1704665 : Blo 1008601 1704665 := bstep (se 2 (by rfl) ⟨639249, by rfl⟩ : syracuseStep 1704665 = 1278499) B1278499
theorem B3834647 : Blo 1008601 3834647 := bstep (se 1 (by rfl) ⟨2875985, by rfl⟩ : syracuseStep 3834647 = 5751971) B5751971
theorem B1704793 : Blo 1008601 1704793 := bstep (se 2 (by rfl) ⟨639297, by rfl⟩ : syracuseStep 1704793 = 1278595) B1278595
theorem B3408857 : Blo 1008601 3408857 := bstep (se 2 (by rfl) ⟨1278321, by rfl⟩ : syracuseStep 3408857 = 2556643) B2556643
theorem B2557079 : Blo 1008601 2557079 := bstep (se 1 (by rfl) ⟨1917809, by rfl⟩ : syracuseStep 2557079 = 3835619) B3835619
theorem B1279243 : Blo 1008601 1279243 := bstep (se 1 (by rfl) ⟨959432, by rfl⟩ : syracuseStep 1279243 = 1918865) B1918865
theorem B1246487 : Blo 1008601 1246487 := bstep (se 1 (by rfl) ⟨934865, by rfl⟩ : syracuseStep 1246487 = 1869731) B1869731
theorem B8750429 : Blo 1008601 8750429 := bstep (se 3 (by rfl) ⟨1640705, by rfl⟩ : syracuseStep 8750429 = 3281411) B3281411
theorem B1705367 : Blo 1008601 1705367 := bstep (se 1 (by rfl) ⟨1279025, by rfl⟩ : syracuseStep 1705367 = 2558051) B2558051
theorem B1213975 : Blo 1008601 1213975 := bstep (se 1 (by rfl) ⟨910481, by rfl⟩ : syracuseStep 1213975 = 1820963) B1820963
theorem B1705495 : Blo 1008601 1705495 := bstep (se 1 (by rfl) ⟨1279121, by rfl⟩ : syracuseStep 1705495 = 2558243) B2558243
theorem B4851245 : Blo 1008601 4851245 := bstep (se 3 (by rfl) ⟨909608, by rfl⟩ : syracuseStep 4851245 = 1819217) B1819217
theorem B3409559 : Blo 1008601 3409559 := bstep (se 1 (by rfl) ⟨2557169, by rfl⟩ : syracuseStep 3409559 = 5114339) B5114339
theorem B2426699 : Blo 1008601 2426699 := bstep (se 1 (by rfl) ⟨1820024, by rfl⟩ : syracuseStep 2426699 = 3640049) B3640049
theorem B2557889 : Blo 1008601 2557889 := bstep (se 2 (by rfl) ⟨959208, by rfl⟩ : syracuseStep 2557889 = 1918417) B1918417
theorem B3835907 : Blo 1008601 3835907 := bstep (se 1 (by rfl) ⟨2876930, by rfl⟩ : syracuseStep 3835907 = 5753861) B5753861
theorem B1706123 : Blo 1008601 1706123 := bstep (se 1 (by rfl) ⟨1279592, by rfl⟩ : syracuseStep 1706123 = 2559185) B2559185
theorem B3410099 : Blo 1008601 3410099 := bstep (se 1 (by rfl) ⟨2557574, by rfl⟩ : syracuseStep 3410099 = 5115149) B5115149
theorem B1280215 : Blo 1008601 1280215 := bstep (se 1 (by rfl) ⟨960161, by rfl⟩ : syracuseStep 1280215 = 1920323) B1920323
theorem B1706251 : Blo 1008601 1706251 := bstep (se 1 (by rfl) ⟨1279688, by rfl⟩ : syracuseStep 1706251 = 2559377) B2559377
theorem B7670051 : Blo 1008601 7670051 := bstep (se 1 (by rfl) ⟨5752538, by rfl⟩ : syracuseStep 7670051 = 11505077) B11505077
theorem B5114177 : Blo 1008601 5114177 := bstep (se 2 (by rfl) ⟨1917816, by rfl⟩ : syracuseStep 5114177 = 3835633) B3835633
theorem B1706393 : Blo 1008601 1706393 := bstep (se 2 (by rfl) ⟨639897, by rfl⟩ : syracuseStep 1706393 = 1279795) B1279795
theorem B3410369 : Blo 1008601 3410369 := bstep (se 2 (by rfl) ⟨1278888, by rfl⟩ : syracuseStep 3410369 = 2557777) B2557777
theorem B2558425 : Blo 1008601 2558425 := bstep (se 2 (by rfl) ⟨959409, by rfl⟩ : syracuseStep 2558425 = 1918819) B1918819
theorem B1706521 : Blo 1008601 1706521 := bstep (se 2 (by rfl) ⟨639945, by rfl⟩ : syracuseStep 1706521 = 1279891) B1279891
theorem B1182551 : Blo 1008601 1182551 := bstep (se 1 (by rfl) ⟨886913, by rfl⟩ : syracuseStep 1182551 = 1773827) B1773827
theorem B2427737 : Blo 1008601 2427737 := bstep (se 2 (by rfl) ⟨910401, by rfl⟩ : syracuseStep 2427737 = 1820803) B1820803
theorem B31558577 : Blo 1008601 31558577 := bstep (se 2 (by rfl) ⟨11834466, by rfl⟩ : syracuseStep 31558577 = 23668933) B23668933
theorem B3410909 : Blo 1008601 3410909 := bstep (se 3 (by rfl) ⟨639545, by rfl⟩ : syracuseStep 3410909 = 1279091) B1279091
theorem B1281035 : Blo 1008601 1281035 := bstep (se 1 (by rfl) ⟨960776, by rfl⟩ : syracuseStep 1281035 = 1921553) B1921553
theorem B1707095 : Blo 1008601 1707095 := bstep (se 1 (by rfl) ⟨1280321, by rfl⟩ : syracuseStep 1707095 = 2560643) B2560643
theorem B1707223 : Blo 1008601 1707223 := bstep (se 1 (by rfl) ⟨1280417, by rfl⟩ : syracuseStep 1707223 = 2560835) B2560835
theorem B1215767 : Blo 1008601 1215767 := bstep (se 1 (by rfl) ⟨911825, by rfl⟩ : syracuseStep 1215767 = 1823651) B1823651
theorem B2559539 : Blo 1008601 2559539 := bstep (se 1 (by rfl) ⟨1919654, by rfl⟩ : syracuseStep 2559539 = 3839309) B3839309
theorem B1216075 : Blo 1008601 1216075 := bstep (se 1 (by rfl) ⟨912056, by rfl⟩ : syracuseStep 1216075 = 1824113) B1824113
theorem B1707851 : Blo 1008601 1707851 := bstep (se 1 (by rfl) ⟨1280888, by rfl⟩ : syracuseStep 1707851 = 2561777) B2561777
theorem B2559833 : Blo 1008601 2559833 := bstep (se 2 (by rfl) ⟨959937, by rfl⟩ : syracuseStep 2559833 = 1919875) B1919875
theorem B4099985 : Blo 1008601 4099985 := bstep (se 2 (by rfl) ⟨1537494, by rfl⟩ : syracuseStep 4099985 = 3074989) B3074989
theorem B9211799 : Blo 1008601 9211799 := bstep (se 1 (by rfl) ⟨6908849, by rfl⟩ : syracuseStep 9211799 = 13817699) B13817699
theorem B1707979 : Blo 1008601 1707979 := bstep (se 1 (by rfl) ⟨1280984, by rfl⟩ : syracuseStep 1707979 = 2561969) B2561969
theorem B3412043 : Blo 1008601 3412043 := bstep (se 1 (by rfl) ⟨2559032, by rfl⟩ : syracuseStep 3412043 = 5118065) B5118065
theorem B1708121 : Blo 1008601 1708121 := bstep (se 2 (by rfl) ⟨640545, by rfl⟩ : syracuseStep 1708121 = 1281091) B1281091
theorem B17272925 : Blo 1008601 17272925 := bstep (se 3 (by rfl) ⟨3238673, by rfl⟩ : syracuseStep 17272925 = 6477347) B6477347
theorem B5116121 : Blo 1008601 5116121 := bstep (se 2 (by rfl) ⟨1918545, by rfl⟩ : syracuseStep 5116121 = 3837091) B3837091
theorem B2461913 : Blo 1008601 2461913 := bstep (se 2 (by rfl) ⟨923217, by rfl⟩ : syracuseStep 2461913 = 1846435) B1846435
theorem B1708249 : Blo 1008601 1708249 := bstep (se 2 (by rfl) ⟨640593, by rfl⟩ : syracuseStep 1708249 = 1281187) B1281187
theorem B49746221 : Blo 1008601 49746221 := bstep (se 3 (by rfl) ⟨9327416, by rfl⟩ : syracuseStep 49746221 = 18654833) B18654833
theorem B3412313 : Blo 1008601 3412313 := bstep (se 2 (by rfl) ⟨1279617, by rfl⟩ : syracuseStep 3412313 = 2559235) B2559235
theorem B12948497 : Blo 1008601 12948497 := bstep (se 2 (by rfl) ⟨4855686, by rfl⟩ : syracuseStep 12948497 = 9711373) B9711373
theorem B3413015 : Blo 1008601 3413015 := bstep (se 1 (by rfl) ⟨2559761, by rfl⟩ : syracuseStep 3413015 = 5119523) B5119523
theorem B3839021 : Blo 1008601 3839021 := bstep (se 3 (by rfl) ⟨719816, by rfl⟩ : syracuseStep 3839021 = 1439633) B1439633
theorem B8623205 : Blo 1008601 8623205 := bstep (se 4 (by rfl) ⟨808425, by rfl⟩ : syracuseStep 8623205 = 1616851) B1616851
theorem B4854935 : Blo 1008601 4854935 := bstep (se 1 (by rfl) ⟨3641201, by rfl⟩ : syracuseStep 4854935 = 7282403) B7282403
theorem B1873049 : Blo 1008601 1873049 := bstep (se 2 (by rfl) ⟨702393, by rfl⟩ : syracuseStep 1873049 = 1404787) B1404787
theorem B2561483 : Blo 1008601 2561483 := bstep (se 1 (by rfl) ⟨1921112, by rfl⟩ : syracuseStep 2561483 = 3842225) B3842225
theorem B1512971 : Blo 1008601 1512971 := bstep (se 1 (by rfl) ⟨1134728, by rfl⟩ : syracuseStep 1512971 = 2269457) B2269457
theorem B1512983 : Blo 1008601 1512983 := bstep (se 1 (by rfl) ⟨1134737, by rfl⟩ : syracuseStep 1512983 = 2269475) B2269475
theorem B3413555 : Blo 1008601 3413555 := bstep (se 1 (by rfl) ⟨2560166, by rfl⟩ : syracuseStep 3413555 = 5120333) B5120333
theorem B1513049 : Blo 1008601 1513049 := bstep (se 2 (by rfl) ⟨567393, by rfl⟩ : syracuseStep 1513049 = 1134787) B1134787
theorem B1513163 : Blo 1008601 1513163 := bstep (se 1 (by rfl) ⟨1134872, by rfl⟩ : syracuseStep 1513163 = 2269745) B2269745
theorem B1513175 : Blo 1008601 1513175 := bstep (se 1 (by rfl) ⟨1134881, by rfl⟩ : syracuseStep 1513175 = 2269763) B2269763
theorem B1513241 : Blo 1008601 1513241 := bstep (se 2 (by rfl) ⟨567465, by rfl⟩ : syracuseStep 1513241 = 1134931) B1134931
theorem B5117741 : Blo 1008601 5117741 := bstep (se 3 (by rfl) ⟨959576, by rfl⟩ : syracuseStep 5117741 = 1919153) B1919153
theorem B3839795 : Blo 1008601 3839795 := bstep (se 1 (by rfl) ⟨2879846, by rfl⟩ : syracuseStep 3839795 = 5759693) B5759693
theorem B3413825 : Blo 1008601 3413825 := bstep (se 2 (by rfl) ⟨1280184, by rfl⟩ : syracuseStep 3413825 = 2560369) B2560369
theorem B1513355 : Blo 1008601 1513355 := bstep (se 1 (by rfl) ⟨1135016, by rfl⟩ : syracuseStep 1513355 = 2270033) B2270033
theorem B1513367 : Blo 1008601 1513367 := bstep (se 1 (by rfl) ⟨1135025, by rfl⟩ : syracuseStep 1513367 = 2270051) B2270051
theorem B1513433 : Blo 1008601 1513433 := bstep (se 2 (by rfl) ⟨567537, by rfl⟩ : syracuseStep 1513433 = 1135075) B1135075
theorem B1513547 : Blo 1008601 1513547 := bstep (se 1 (by rfl) ⟨1135160, by rfl⟩ : syracuseStep 1513547 = 2270321) B2270321
theorem B1513559 : Blo 1008601 1513559 := bstep (se 1 (by rfl) ⟨1135169, by rfl⟩ : syracuseStep 1513559 = 2270339) B2270339
theorem B1513625 : Blo 1008601 1513625 := bstep (se 2 (by rfl) ⟨567609, by rfl⟩ : syracuseStep 1513625 = 1135219) B1135219
theorem B1186039 : Blo 1008601 1186039 := bstep (se 1 (by rfl) ⟨889529, by rfl⟩ : syracuseStep 1186039 = 1779059) B1779059
theorem B1513739 : Blo 1008601 1513739 := bstep (se 1 (by rfl) ⟨1135304, by rfl⟩ : syracuseStep 1513739 = 2270609) B2270609
theorem B1513751 : Blo 1008601 1513751 := bstep (se 1 (by rfl) ⟨1135313, by rfl⟩ : syracuseStep 1513751 = 2270627) B2270627
theorem B1513817 : Blo 1008601 1513817 := bstep (se 2 (by rfl) ⟨567681, by rfl⟩ : syracuseStep 1513817 = 1135363) B1135363
theorem B3414365 : Blo 1008601 3414365 := bstep (se 3 (by rfl) ⟨640193, by rfl⟩ : syracuseStep 3414365 = 1280387) B1280387
theorem B2562455 : Blo 1008601 2562455 := bstep (se 1 (by rfl) ⟨1921841, by rfl⟩ : syracuseStep 2562455 = 3843683) B3843683
theorem B1513931 : Blo 1008601 1513931 := bstep (se 1 (by rfl) ⟨1135448, by rfl⟩ : syracuseStep 1513931 = 2270897) B2270897
theorem B1513943 : Blo 1008601 1513943 := bstep (se 1 (by rfl) ⟨1135457, by rfl⟩ : syracuseStep 1513943 = 2270915) B2270915
theorem B1514009 : Blo 1008601 1514009 := bstep (se 2 (by rfl) ⟨567753, by rfl⟩ : syracuseStep 1514009 = 1135507) B1135507
theorem B1514123 : Blo 1008601 1514123 := bstep (se 1 (by rfl) ⟨1135592, by rfl⟩ : syracuseStep 1514123 = 2271185) B2271185
theorem B1514135 : Blo 1008601 1514135 := bstep (se 1 (by rfl) ⟨1135601, by rfl⟩ : syracuseStep 1514135 = 2271203) B2271203
theorem B1514201 : Blo 1008601 1514201 := bstep (se 2 (by rfl) ⟨567825, by rfl⟩ : syracuseStep 1514201 = 1135651) B1135651
theorem B1514315 : Blo 1008601 1514315 := bstep (se 1 (by rfl) ⟨1135736, by rfl⟩ : syracuseStep 1514315 = 2271473) B2271473
theorem B1514327 : Blo 1008601 1514327 := bstep (se 1 (by rfl) ⟨1135745, by rfl⟩ : syracuseStep 1514327 = 2271491) B2271491
theorem B2595673 : Blo 1008601 2595673 := bstep (se 2 (by rfl) ⟨973377, by rfl⟩ : syracuseStep 2595673 = 1946755) B1946755
theorem B1973143 : Blo 1008601 1973143 := bstep (se 1 (by rfl) ⟨1479857, by rfl⟩ : syracuseStep 1973143 = 2959715) B2959715
theorem B1514393 : Blo 1008601 1514393 := bstep (se 2 (by rfl) ⟨567897, by rfl⟩ : syracuseStep 1514393 = 1135795) B1135795
theorem B1514507 : Blo 1008601 1514507 := bstep (se 1 (by rfl) ⟨1135880, by rfl⟩ : syracuseStep 1514507 = 2271761) B2271761
theorem B2300951 : Blo 1008601 2300951 := bstep (se 1 (by rfl) ⟨1725713, by rfl⟩ : syracuseStep 2300951 = 3451427) B3451427
theorem B1514519 : Blo 1008601 1514519 := bstep (se 1 (by rfl) ⟨1135889, by rfl⟩ : syracuseStep 1514519 = 2271779) B2271779
theorem B2563123 : Blo 1008601 2563123 := bstep (se 1 (by rfl) ⟨1922342, by rfl⟩ : syracuseStep 2563123 = 3844685) B3844685
theorem B9215041 : Blo 1008601 9215041 := bstep (se 2 (by rfl) ⟨3455640, by rfl⟩ : syracuseStep 9215041 = 6911281) B6911281
theorem B1514585 : Blo 1008601 1514585 := bstep (se 2 (by rfl) ⟨567969, by rfl⟩ : syracuseStep 1514585 = 1135939) B1135939
theorem B1514699 : Blo 1008601 1514699 := bstep (se 1 (by rfl) ⟨1136024, by rfl⟩ : syracuseStep 1514699 = 2272049) B2272049
theorem B1514711 : Blo 1008601 1514711 := bstep (se 1 (by rfl) ⟨1136033, by rfl⟩ : syracuseStep 1514711 = 2272067) B2272067
theorem B3841283 : Blo 1008601 3841283 := bstep (se 1 (by rfl) ⟨2880962, by rfl⟩ : syracuseStep 3841283 = 5761925) B5761925
theorem B1514777 : Blo 1008601 1514777 := bstep (se 2 (by rfl) ⟨568041, by rfl⟩ : syracuseStep 1514777 = 1136083) B1136083
theorem B1514891 : Blo 1008601 1514891 := bstep (se 1 (by rfl) ⟨1136168, by rfl⟩ : syracuseStep 1514891 = 2272337) B2272337
theorem B1514903 : Blo 1008601 1514903 := bstep (se 1 (by rfl) ⟨1136177, by rfl⟩ : syracuseStep 1514903 = 2272355) B2272355
theorem B3415499 : Blo 1008601 3415499 := bstep (se 1 (by rfl) ⟨2561624, by rfl⟩ : syracuseStep 3415499 = 5123249) B5123249
theorem B1514969 : Blo 1008601 1514969 := bstep (se 2 (by rfl) ⟨568113, by rfl⟩ : syracuseStep 1514969 = 1136227) B1136227
theorem B7380485 : Blo 1008601 7380485 := bstep (se 4 (by rfl) ⟨691920, by rfl⟩ : syracuseStep 7380485 = 1383841) B1383841
theorem B7675397 : Blo 1008601 7675397 := bstep (se 4 (by rfl) ⟨719568, by rfl⟩ : syracuseStep 7675397 = 1439137) B1439137
theorem B1515083 : Blo 1008601 1515083 := bstep (se 1 (by rfl) ⟨1136312, by rfl⟩ : syracuseStep 1515083 = 2272625) B2272625
theorem B1515095 : Blo 1008601 1515095 := bstep (se 1 (by rfl) ⟨1136321, by rfl⟩ : syracuseStep 1515095 = 2272643) B2272643
theorem B1515161 : Blo 1008601 1515161 := bstep (se 2 (by rfl) ⟨568185, by rfl⟩ : syracuseStep 1515161 = 1136371) B1136371
theorem B3841739 : Blo 1008601 3841739 := bstep (se 1 (by rfl) ⟨2881304, by rfl⟩ : syracuseStep 3841739 = 5762609) B5762609
theorem B3415769 : Blo 1008601 3415769 := bstep (se 2 (by rfl) ⟨1280913, by rfl⟩ : syracuseStep 3415769 = 2561827) B2561827
theorem B1515275 : Blo 1008601 1515275 := bstep (se 1 (by rfl) ⟨1136456, by rfl⟩ : syracuseStep 1515275 = 2272913) B2272913
theorem B1515287 : Blo 1008601 1515287 := bstep (se 1 (by rfl) ⟨1136465, by rfl⟩ : syracuseStep 1515287 = 2272931) B2272931
theorem B1515353 : Blo 1008601 1515353 := bstep (se 2 (by rfl) ⟨568257, by rfl⟩ : syracuseStep 1515353 = 1136515) B1136515
theorem B3841937 : Blo 1008601 3841937 := bstep (se 2 (by rfl) ⟨1440726, by rfl⟩ : syracuseStep 3841937 = 2881453) B2881453
theorem B1515467 : Blo 1008601 1515467 := bstep (se 1 (by rfl) ⟨1136600, by rfl⟩ : syracuseStep 1515467 = 2273201) B2273201
theorem B1515479 : Blo 1008601 1515479 := bstep (se 1 (by rfl) ⟨1136609, by rfl⟩ : syracuseStep 1515479 = 2273219) B2273219
theorem B1515545 : Blo 1008601 1515545 := bstep (se 2 (by rfl) ⟨568329, by rfl⟩ : syracuseStep 1515545 = 1136659) B1136659
theorem B1515659 : Blo 1008601 1515659 := bstep (se 1 (by rfl) ⟨1136744, by rfl⟩ : syracuseStep 1515659 = 2273489) B2273489
theorem B1515671 : Blo 1008601 1515671 := bstep (se 1 (by rfl) ⟨1136753, by rfl⟩ : syracuseStep 1515671 = 2273507) B2273507
theorem B7282865 : Blo 1008601 7282865 := bstep (se 2 (by rfl) ⟨2731074, by rfl⟩ : syracuseStep 7282865 = 5462149) B5462149
theorem B1941707 : Blo 1008601 1941707 := bstep (se 1 (by rfl) ⟨1456280, by rfl⟩ : syracuseStep 1941707 = 2912561) B2912561
theorem B1384651 : Blo 1008601 1384651 := bstep (se 1 (by rfl) ⟨1038488, by rfl⟩ : syracuseStep 1384651 = 2076977) B2076977
theorem B1515737 : Blo 1008601 1515737 := bstep (se 2 (by rfl) ⟨568401, by rfl⟩ : syracuseStep 1515737 = 1136803) B1136803
theorem B1843507 : Blo 1008601 1843507 := bstep (se 1 (by rfl) ⟨1382630, by rfl⟩ : syracuseStep 1843507 = 2765261) B2765261
theorem B1515851 : Blo 1008601 1515851 := bstep (se 1 (by rfl) ⟨1136888, by rfl⟩ : syracuseStep 1515851 = 2273777) B2273777
theorem B1515863 : Blo 1008601 1515863 := bstep (se 1 (by rfl) ⟨1136897, by rfl⟩ : syracuseStep 1515863 = 2273795) B2273795
theorem B2269529 : Blo 1008601 2269529 := bstep (se 2 (by rfl) ⟨851073, by rfl⟩ : syracuseStep 2269529 = 1702147) B1702147
theorem B3416471 : Blo 1008601 3416471 := bstep (se 1 (by rfl) ⟨2562353, by rfl⟩ : syracuseStep 3416471 = 5124707) B5124707
theorem B1515929 : Blo 1008601 1515929 := bstep (se 2 (by rfl) ⟨568473, by rfl⟩ : syracuseStep 1515929 = 1136947) B1136947
theorem B2269619 : Blo 1008601 2269619 := bstep (se 1 (by rfl) ⟨1702214, by rfl⟩ : syracuseStep 2269619 = 3404429) B3404429
theorem B2269655 : Blo 1008601 2269655 := bstep (se 1 (by rfl) ⟨1702241, by rfl⟩ : syracuseStep 2269655 = 3404483) B3404483
theorem B1516043 : Blo 1008601 1516043 := bstep (se 1 (by rfl) ⟨1137032, by rfl⟩ : syracuseStep 1516043 = 2274065) B2274065
theorem B1516055 : Blo 1008601 1516055 := bstep (se 1 (by rfl) ⟨1137041, by rfl⟩ : syracuseStep 1516055 = 2274083) B2274083
theorem B1516121 : Blo 1008601 1516121 := bstep (se 2 (by rfl) ⟨568545, by rfl⟩ : syracuseStep 1516121 = 1137091) B1137091
theorem B2269835 : Blo 1008601 2269835 := bstep (se 1 (by rfl) ⟨1702376, by rfl⟩ : syracuseStep 2269835 = 3404753) B3404753
theorem B3842711 : Blo 1008601 3842711 := bstep (se 1 (by rfl) ⟨2882033, by rfl⟩ : syracuseStep 3842711 = 5764067) B5764067
theorem B2269889 : Blo 1008601 2269889 := bstep (se 2 (by rfl) ⟨851208, by rfl⟩ : syracuseStep 2269889 = 1702417) B1702417
theorem B1516235 : Blo 1008601 1516235 := bstep (se 1 (by rfl) ⟨1137176, by rfl⟩ : syracuseStep 1516235 = 2274353) B2274353
theorem B1516247 : Blo 1008601 1516247 := bstep (se 1 (by rfl) ⟨1137185, by rfl⟩ : syracuseStep 1516247 = 2274371) B2274371
theorem B1516313 : Blo 1008601 1516313 := bstep (se 2 (by rfl) ⟨568617, by rfl⟩ : syracuseStep 1516313 = 1137235) B1137235
theorem B3842909 : Blo 1008601 3842909 := bstep (se 3 (by rfl) ⟨720545, by rfl⟩ : syracuseStep 3842909 = 1441091) B1441091
theorem B1516427 : Blo 1008601 1516427 := bstep (se 1 (by rfl) ⟨1137320, by rfl⟩ : syracuseStep 1516427 = 2274641) B2274641
theorem B6464407 : Blo 1008601 6464407 := bstep (se 1 (by rfl) ⟨4848305, by rfl⟩ : syracuseStep 6464407 = 9696611) B9696611
theorem B1516439 : Blo 1008601 1516439 := bstep (se 1 (by rfl) ⟨1137329, by rfl⟩ : syracuseStep 1516439 = 2274659) B2274659
theorem B2270105 : Blo 1008601 2270105 := bstep (se 2 (by rfl) ⟨851289, by rfl⟩ : syracuseStep 2270105 = 1702579) B1702579
theorem B3417011 : Blo 1008601 3417011 := bstep (se 1 (by rfl) ⟨2562758, by rfl⟩ : syracuseStep 3417011 = 5125517) B5125517
theorem B1516505 : Blo 1008601 1516505 := bstep (se 2 (by rfl) ⟨568689, by rfl⟩ : syracuseStep 1516505 = 1137379) B1137379
theorem B2270195 : Blo 1008601 2270195 := bstep (se 1 (by rfl) ⟨1702646, by rfl⟩ : syracuseStep 2270195 = 3405293) B3405293
theorem B1385483 : Blo 1008601 1385483 := bstep (se 1 (by rfl) ⟨1039112, by rfl⟩ : syracuseStep 1385483 = 2078225) B2078225
theorem B2270231 : Blo 1008601 2270231 := bstep (se 1 (by rfl) ⟨1702673, by rfl⟩ : syracuseStep 2270231 = 3405347) B3405347
theorem B1516619 : Blo 1008601 1516619 := bstep (se 1 (by rfl) ⟨1137464, by rfl⟩ : syracuseStep 1516619 = 2274929) B2274929
theorem B1516631 : Blo 1008601 1516631 := bstep (se 1 (by rfl) ⟨1137473, by rfl⟩ : syracuseStep 1516631 = 2274947) B2274947
theorem B1516697 : Blo 1008601 1516697 := bstep (se 2 (by rfl) ⟨568761, by rfl⟩ : syracuseStep 1516697 = 1137523) B1137523
theorem B3417281 : Blo 1008601 3417281 := bstep (se 2 (by rfl) ⟨1281480, by rfl⟩ : syracuseStep 3417281 = 2562961) B2562961
theorem B2270411 : Blo 1008601 2270411 := bstep (se 1 (by rfl) ⟨1702808, by rfl⟩ : syracuseStep 2270411 = 3405617) B3405617
theorem B2270465 : Blo 1008601 2270465 := bstep (se 2 (by rfl) ⟨851424, by rfl⟩ : syracuseStep 2270465 = 1702849) B1702849
theorem B1516811 : Blo 1008601 1516811 := bstep (se 1 (by rfl) ⟨1137608, by rfl⟩ : syracuseStep 1516811 = 2275217) B2275217
theorem B1516823 : Blo 1008601 1516823 := bstep (se 1 (by rfl) ⟨1137617, by rfl⟩ : syracuseStep 1516823 = 2275235) B2275235
theorem B1516889 : Blo 1008601 1516889 := bstep (se 2 (by rfl) ⟨568833, by rfl⟩ : syracuseStep 1516889 = 1137667) B1137667
theorem B1517003 : Blo 1008601 1517003 := bstep (se 1 (by rfl) ⟨1137752, by rfl⟩ : syracuseStep 1517003 = 2275505) B2275505
theorem B1517015 : Blo 1008601 1517015 := bstep (se 1 (by rfl) ⟨1137761, by rfl⟩ : syracuseStep 1517015 = 2275523) B2275523
theorem B2270681 : Blo 1008601 2270681 := bstep (se 2 (by rfl) ⟨851505, by rfl⟩ : syracuseStep 2270681 = 1703011) B1703011
theorem B1517081 : Blo 1008601 1517081 := bstep (se 2 (by rfl) ⟨568905, by rfl⟩ : syracuseStep 1517081 = 1137811) B1137811
theorem B2270771 : Blo 1008601 2270771 := bstep (se 1 (by rfl) ⟨1703078, by rfl⟩ : syracuseStep 2270771 = 3406157) B3406157
theorem B2270807 : Blo 1008601 2270807 := bstep (se 1 (by rfl) ⟨1703105, by rfl⟩ : syracuseStep 2270807 = 3406211) B3406211
theorem B5121629 : Blo 1008601 5121629 := bstep (se 3 (by rfl) ⟨960305, by rfl⟩ : syracuseStep 5121629 = 1920611) B1920611
theorem B1517195 : Blo 1008601 1517195 := bstep (se 1 (by rfl) ⟨1137896, by rfl⟩ : syracuseStep 1517195 = 2275793) B2275793
theorem B1517207 : Blo 1008601 1517207 := bstep (se 1 (by rfl) ⟨1137905, by rfl⟩ : syracuseStep 1517207 = 2275811) B2275811
theorem B1517273 : Blo 1008601 1517273 := bstep (se 2 (by rfl) ⟨568977, by rfl⟩ : syracuseStep 1517273 = 1137955) B1137955
theorem B2270987 : Blo 1008601 2270987 := bstep (se 1 (by rfl) ⟨1703240, by rfl⟩ : syracuseStep 2270987 = 3406481) B3406481
theorem B5744429 : Blo 1008601 5744429 := bstep (se 3 (by rfl) ⟨1077080, by rfl⟩ : syracuseStep 5744429 = 2154161) B2154161
theorem B2271041 : Blo 1008601 2271041 := bstep (se 2 (by rfl) ⟨851640, by rfl⟩ : syracuseStep 2271041 = 1703281) B1703281
theorem B14559041 : Blo 1008601 14559041 := bstep (se 2 (by rfl) ⟨5459640, by rfl⟩ : syracuseStep 14559041 = 10919281) B10919281
theorem B1517387 : Blo 1008601 1517387 := bstep (se 1 (by rfl) ⟨1138040, by rfl⟩ : syracuseStep 1517387 = 2276081) B2276081
theorem B1517399 : Blo 1008601 1517399 := bstep (se 1 (by rfl) ⟨1138049, by rfl⟩ : syracuseStep 1517399 = 2276099) B2276099
theorem B18425717 : Blo 1008601 18425717 := bstep (se 5 (by rfl) ⟨863705, by rfl⟩ : syracuseStep 18425717 = 1727411) B1727411
theorem B7677827 : Blo 1008601 7677827 := bstep (se 1 (by rfl) ⟨5758370, by rfl⟩ : syracuseStep 7677827 = 11516741) B11516741
theorem B1517465 : Blo 1008601 1517465 := bstep (se 2 (by rfl) ⟨569049, by rfl⟩ : syracuseStep 1517465 = 1138099) B1138099
theorem B1517579 : Blo 1008601 1517579 := bstep (se 1 (by rfl) ⟨1138184, by rfl⟩ : syracuseStep 1517579 = 2276369) B2276369
theorem B1517591 : Blo 1008601 1517591 := bstep (se 1 (by rfl) ⟨1138193, by rfl⟩ : syracuseStep 1517591 = 2276387) B2276387
theorem B1615897 : Blo 1008601 1615897 := bstep (se 2 (by rfl) ⟨605961, by rfl⟩ : syracuseStep 1615897 = 1211923) B1211923
theorem B2271257 : Blo 1008601 2271257 := bstep (se 2 (by rfl) ⟨851721, by rfl⟩ : syracuseStep 2271257 = 1703443) B1703443
theorem B1517657 : Blo 1008601 1517657 := bstep (se 2 (by rfl) ⟨569121, by rfl⟩ : syracuseStep 1517657 = 1138243) B1138243
theorem B2271347 : Blo 1008601 2271347 := bstep (se 1 (by rfl) ⟨1703510, by rfl⟩ : syracuseStep 2271347 = 3407021) B3407021
theorem B6924419 : Blo 1008601 6924419 := bstep (se 1 (by rfl) ⟨5193314, by rfl⟩ : syracuseStep 6924419 = 10386629) B10386629
theorem B2271383 : Blo 1008601 2271383 := bstep (se 1 (by rfl) ⟨1703537, by rfl⟩ : syracuseStep 2271383 = 3407075) B3407075
theorem B4368563 : Blo 1008601 4368563 := bstep (se 1 (by rfl) ⟨3276422, by rfl⟩ : syracuseStep 4368563 = 6552845) B6552845
theorem B1517771 : Blo 1008601 1517771 := bstep (se 1 (by rfl) ⟨1138328, by rfl⟩ : syracuseStep 1517771 = 2276657) B2276657
theorem B1517783 : Blo 1008601 1517783 := bstep (se 1 (by rfl) ⟨1138337, by rfl⟩ : syracuseStep 1517783 = 2276675) B2276675
theorem B1517849 : Blo 1008601 1517849 := bstep (se 2 (by rfl) ⟨569193, by rfl⟩ : syracuseStep 1517849 = 1138387) B1138387
theorem B2271563 : Blo 1008601 2271563 := bstep (se 1 (by rfl) ⟨1703672, by rfl⟩ : syracuseStep 2271563 = 3407345) B3407345
theorem B13150565 : Blo 1008601 13150565 := bstep (se 4 (by rfl) ⟨1232865, by rfl⟩ : syracuseStep 13150565 = 2465731) B2465731
theorem B2271617 : Blo 1008601 2271617 := bstep (se 2 (by rfl) ⟨851856, by rfl⟩ : syracuseStep 2271617 = 1703713) B1703713
theorem B1517963 : Blo 1008601 1517963 := bstep (se 1 (by rfl) ⟨1138472, by rfl⟩ : syracuseStep 1517963 = 2276945) B2276945
theorem B1517975 : Blo 1008601 1517975 := bstep (se 1 (by rfl) ⟨1138481, by rfl⟩ : syracuseStep 1517975 = 2276963) B2276963
theorem B5745113 : Blo 1008601 5745113 := bstep (se 2 (by rfl) ⟨2154417, by rfl⟩ : syracuseStep 5745113 = 4308835) B4308835
theorem B17246681 : Blo 1008601 17246681 := bstep (se 2 (by rfl) ⟨6467505, by rfl⟩ : syracuseStep 17246681 = 12935011) B12935011
theorem B1518041 : Blo 1008601 1518041 := bstep (se 2 (by rfl) ⟨569265, by rfl⟩ : syracuseStep 1518041 = 1138531) B1138531
theorem B1518155 : Blo 1008601 1518155 := bstep (se 1 (by rfl) ⟨1138616, by rfl⟩ : syracuseStep 1518155 = 2277233) B2277233
theorem B1518167 : Blo 1008601 1518167 := bstep (se 1 (by rfl) ⟨1138625, by rfl⟩ : syracuseStep 1518167 = 2277251) B2277251
theorem B2271833 : Blo 1008601 2271833 := bstep (se 2 (by rfl) ⟨851937, by rfl⟩ : syracuseStep 2271833 = 1703875) B1703875
theorem B1518233 : Blo 1008601 1518233 := bstep (se 2 (by rfl) ⟨569337, by rfl⟩ : syracuseStep 1518233 = 1138675) B1138675
theorem B2271923 : Blo 1008601 2271923 := bstep (se 1 (by rfl) ⟨1703942, by rfl⟩ : syracuseStep 2271923 = 3407885) B3407885
theorem B2271959 : Blo 1008601 2271959 := bstep (se 1 (by rfl) ⟨1703969, by rfl⟩ : syracuseStep 2271959 = 3407939) B3407939
theorem B1518347 : Blo 1008601 1518347 := bstep (se 1 (by rfl) ⟨1138760, by rfl⟩ : syracuseStep 1518347 = 2277521) B2277521
theorem B1518359 : Blo 1008601 1518359 := bstep (se 1 (by rfl) ⟨1138769, by rfl⟩ : syracuseStep 1518359 = 2277539) B2277539
theorem B1518425 : Blo 1008601 1518425 := bstep (se 2 (by rfl) ⟨569409, by rfl⟩ : syracuseStep 1518425 = 1138819) B1138819
theorem B2272139 : Blo 1008601 2272139 := bstep (se 1 (by rfl) ⟨1704104, by rfl⟩ : syracuseStep 2272139 = 3408209) B3408209
theorem B2272193 : Blo 1008601 2272193 := bstep (se 2 (by rfl) ⟨852072, by rfl⟩ : syracuseStep 2272193 = 1704145) B1704145
theorem B1518539 : Blo 1008601 1518539 := bstep (se 1 (by rfl) ⟨1138904, by rfl⟩ : syracuseStep 1518539 = 2277809) B2277809
theorem B1518551 : Blo 1008601 1518551 := bstep (se 1 (by rfl) ⟨1138913, by rfl⟩ : syracuseStep 1518551 = 2277827) B2277827
theorem B1518617 : Blo 1008601 1518617 := bstep (se 2 (by rfl) ⟨569481, by rfl⟩ : syracuseStep 1518617 = 1138963) B1138963
theorem B1518731 : Blo 1008601 1518731 := bstep (se 1 (by rfl) ⟨1139048, by rfl⟩ : syracuseStep 1518731 = 2278097) B2278097
theorem B1518743 : Blo 1008601 1518743 := bstep (se 1 (by rfl) ⟨1139057, by rfl⟩ : syracuseStep 1518743 = 2278115) B2278115
theorem B2272409 : Blo 1008601 2272409 := bstep (se 2 (by rfl) ⟨852153, by rfl⟩ : syracuseStep 2272409 = 1704307) B1704307
theorem B1518809 : Blo 1008601 1518809 := bstep (se 2 (by rfl) ⟨569553, by rfl⟩ : syracuseStep 1518809 = 1139107) B1139107
theorem B2272499 : Blo 1008601 2272499 := bstep (se 1 (by rfl) ⟨1704374, by rfl⟩ : syracuseStep 2272499 = 3408749) B3408749
theorem B2272535 : Blo 1008601 2272535 := bstep (se 1 (by rfl) ⟨1704401, by rfl⟩ : syracuseStep 2272535 = 3408803) B3408803
theorem B6466891 : Blo 1008601 6466891 := bstep (se 1 (by rfl) ⟨4850168, by rfl⟩ : syracuseStep 6466891 = 9700337) B9700337
theorem B1093015 : Blo 1008601 1093015 := bstep (se 1 (by rfl) ⟨819761, by rfl⟩ : syracuseStep 1093015 = 1639523) B1639523
theorem B2305459 : Blo 1008601 2305459 := bstep (se 1 (by rfl) ⟨1729094, by rfl⟩ : syracuseStep 2305459 = 3458189) B3458189
theorem B2272715 : Blo 1008601 2272715 := bstep (se 1 (by rfl) ⟨1704536, by rfl⟩ : syracuseStep 2272715 = 3409073) B3409073
theorem B2272769 : Blo 1008601 2272769 := bstep (se 2 (by rfl) ⟨852288, by rfl⟩ : syracuseStep 2272769 = 1704577) B1704577
theorem B2305651 : Blo 1008601 2305651 := bstep (se 1 (by rfl) ⟨1729238, by rfl⟩ : syracuseStep 2305651 = 3458477) B3458477
theorem B5123735 : Blo 1008601 5123735 := bstep (se 1 (by rfl) ⟨3842801, by rfl⟩ : syracuseStep 5123735 = 7685603) B7685603
theorem B2272985 : Blo 1008601 2272985 := bstep (se 2 (by rfl) ⟨852369, by rfl⟩ : syracuseStep 2272985 = 1704739) B1704739
theorem B2273075 : Blo 1008601 2273075 := bstep (se 1 (by rfl) ⟨1704806, by rfl⟩ : syracuseStep 2273075 = 3409613) B3409613
theorem B2273111 : Blo 1008601 2273111 := bstep (se 1 (by rfl) ⟨1704833, by rfl⟩ : syracuseStep 2273111 = 3409667) B3409667
theorem B1945523 : Blo 1008601 1945523 := bstep (se 1 (by rfl) ⟨1459142, by rfl⟩ : syracuseStep 1945523 = 2918285) B2918285
theorem B13840307 : Blo 1008601 13840307 := bstep (se 1 (by rfl) ⟨10380230, by rfl⟩ : syracuseStep 13840307 = 20760461) B20760461
theorem B2273291 : Blo 1008601 2273291 := bstep (se 1 (by rfl) ⟨1704968, by rfl⟩ : syracuseStep 2273291 = 3409937) B3409937
theorem B2273345 : Blo 1008601 2273345 := bstep (se 2 (by rfl) ⟨852504, by rfl⟩ : syracuseStep 2273345 = 1705009) B1705009
theorem B2273561 : Blo 1008601 2273561 := bstep (se 2 (by rfl) ⟨852585, by rfl⟩ : syracuseStep 2273561 = 1705171) B1705171
theorem B2732363 : Blo 1008601 2732363 := bstep (se 1 (by rfl) ⟨2049272, by rfl⟩ : syracuseStep 2732363 = 4098545) B4098545
theorem B2273651 : Blo 1008601 2273651 := bstep (se 1 (by rfl) ⟨1705238, by rfl⟩ : syracuseStep 2273651 = 3410477) B3410477
theorem B2273687 : Blo 1008601 2273687 := bstep (se 1 (by rfl) ⟨1705265, by rfl⟩ : syracuseStep 2273687 = 3410531) B3410531
theorem B2273867 : Blo 1008601 2273867 := bstep (se 1 (by rfl) ⟨1705400, by rfl⟩ : syracuseStep 2273867 = 3410801) B3410801
theorem B2273921 : Blo 1008601 2273921 := bstep (se 2 (by rfl) ⟨852720, by rfl⟩ : syracuseStep 2273921 = 1705441) B1705441
theorem B14594741 : Blo 1008601 14594741 := bstep (se 5 (by rfl) ⟨684128, by rfl⟩ : syracuseStep 14594741 = 1368257) B1368257
theorem B4436801 : Blo 1008601 4436801 := bstep (se 2 (by rfl) ⟨1663800, by rfl⟩ : syracuseStep 4436801 = 3327601) B3327601
theorem B2274137 : Blo 1008601 2274137 := bstep (se 2 (by rfl) ⟨852801, by rfl⟩ : syracuseStep 2274137 = 1705603) B1705603
theorem B2274227 : Blo 1008601 2274227 := bstep (se 1 (by rfl) ⟨1705670, by rfl⟩ : syracuseStep 2274227 = 3411341) B3411341
theorem B2274263 : Blo 1008601 2274263 := bstep (se 1 (by rfl) ⟨1705697, by rfl⟩ : syracuseStep 2274263 = 3411395) B3411395
theorem B2765785 : Blo 1008601 2765785 := bstep (se 2 (by rfl) ⟨1037169, by rfl⟩ : syracuseStep 2765785 = 2074339) B2074339
theorem B2274443 : Blo 1008601 2274443 := bstep (se 1 (by rfl) ⟨1705832, by rfl⟩ : syracuseStep 2274443 = 3411665) B3411665
theorem B2274497 : Blo 1008601 2274497 := bstep (se 2 (by rfl) ⟨852936, by rfl⟩ : syracuseStep 2274497 = 1705873) B1705873
theorem B7681229 : Blo 1008601 7681229 := bstep (se 3 (by rfl) ⟨1440230, by rfl⟩ : syracuseStep 7681229 = 2880461) B2880461
theorem B4928813 : Blo 1008601 4928813 := bstep (se 3 (by rfl) ⟨924152, by rfl⟩ : syracuseStep 4928813 = 1848305) B1848305
theorem B2733401 : Blo 1008601 2733401 := bstep (se 2 (by rfl) ⟨1025025, by rfl⟩ : syracuseStep 2733401 = 2050051) B2050051
theorem B2274713 : Blo 1008601 2274713 := bstep (se 2 (by rfl) ⟨853017, by rfl⟩ : syracuseStep 2274713 = 1706035) B1706035
theorem B2307521 : Blo 1008601 2307521 := bstep (se 2 (by rfl) ⟨865320, by rfl⟩ : syracuseStep 2307521 = 1730641) B1730641
theorem B2274803 : Blo 1008601 2274803 := bstep (se 1 (by rfl) ⟨1706102, by rfl⟩ : syracuseStep 2274803 = 3412205) B3412205
theorem B2274839 : Blo 1008601 2274839 := bstep (se 1 (by rfl) ⟨1706129, by rfl⟩ : syracuseStep 2274839 = 3412259) B3412259
theorem B12269207 : Blo 1008601 12269207 := bstep (se 1 (by rfl) ⟨9201905, by rfl⟩ : syracuseStep 12269207 = 18403811) B18403811
theorem B7681715 : Blo 1008601 7681715 := bstep (se 1 (by rfl) ⟨5761286, by rfl⟩ : syracuseStep 7681715 = 11522573) B11522573
theorem B2275019 : Blo 1008601 2275019 := bstep (se 1 (by rfl) ⟨1706264, by rfl⟩ : syracuseStep 2275019 = 3412529) B3412529
theorem B1619671 : Blo 1008601 1619671 := bstep (se 1 (by rfl) ⟨1214753, by rfl⟩ : syracuseStep 1619671 = 2429507) B2429507
theorem B2275073 : Blo 1008601 2275073 := bstep (se 2 (by rfl) ⟨853152, by rfl⟩ : syracuseStep 2275073 = 1706305) B1706305
theorem B1619927 : Blo 1008601 1619927 := bstep (se 1 (by rfl) ⟨1214945, by rfl⟩ : syracuseStep 1619927 = 2429891) B2429891
theorem B2275289 : Blo 1008601 2275289 := bstep (se 2 (by rfl) ⟨853233, by rfl⟩ : syracuseStep 2275289 = 1706467) B1706467
theorem B1914931 : Blo 1008601 1914931 := bstep (se 1 (by rfl) ⟨1436198, by rfl⟩ : syracuseStep 1914931 = 2872397) B2872397
theorem B2275379 : Blo 1008601 2275379 := bstep (se 1 (by rfl) ⟨1706534, by rfl⟩ : syracuseStep 2275379 = 3413069) B3413069
theorem B2275415 : Blo 1008601 2275415 := bstep (se 1 (by rfl) ⟨1706561, by rfl⟩ : syracuseStep 2275415 = 3413123) B3413123
theorem B1620119 : Blo 1008601 1620119 := bstep (se 1 (by rfl) ⟨1215089, by rfl⟩ : syracuseStep 1620119 = 2430179) B2430179
theorem B1947863 : Blo 1008601 1947863 := bstep (se 1 (by rfl) ⟨1460897, by rfl⟩ : syracuseStep 1947863 = 2921795) B2921795
theorem B2275595 : Blo 1008601 2275595 := bstep (se 1 (by rfl) ⟨1706696, by rfl⟩ : syracuseStep 2275595 = 3413393) B3413393
theorem B1915159 : Blo 1008601 1915159 := bstep (se 1 (by rfl) ⟨1436369, by rfl⟩ : syracuseStep 1915159 = 2872739) B2872739
theorem B2275649 : Blo 1008601 2275649 := bstep (se 2 (by rfl) ⟨853368, by rfl⟩ : syracuseStep 2275649 = 1706737) B1706737
theorem B1915265 : Blo 1008601 1915265 := bstep (se 2 (by rfl) ⟨718224, by rfl⟩ : syracuseStep 1915265 = 1436449) B1436449
theorem B2308505 : Blo 1008601 2308505 := bstep (se 2 (by rfl) ⟨865689, by rfl⟩ : syracuseStep 2308505 = 1731379) B1731379
theorem B1620427 : Blo 1008601 1620427 := bstep (se 1 (by rfl) ⟨1215320, by rfl⟩ : syracuseStep 1620427 = 2430641) B2430641
theorem B1915417 : Blo 1008601 1915417 := bstep (se 2 (by rfl) ⟨718281, by rfl⟩ : syracuseStep 1915417 = 1436563) B1436563
theorem B2275865 : Blo 1008601 2275865 := bstep (se 2 (by rfl) ⟨853449, by rfl⟩ : syracuseStep 2275865 = 1706899) B1706899
theorem B2275955 : Blo 1008601 2275955 := bstep (se 1 (by rfl) ⟨1706966, by rfl⟩ : syracuseStep 2275955 = 3413933) B3413933
theorem B16366211 : Blo 1008601 16366211 := bstep (se 1 (by rfl) ⟨12274658, by rfl⟩ : syracuseStep 16366211 = 24549317) B24549317
theorem B2275991 : Blo 1008601 2275991 := bstep (se 1 (by rfl) ⟨1706993, by rfl⟩ : syracuseStep 2275991 = 3413987) B3413987
theorem B18430669 : Blo 1008601 18430669 := bstep (se 3 (by rfl) ⟨3455750, by rfl⟩ : syracuseStep 18430669 = 6911501) B6911501
theorem B2276171 : Blo 1008601 2276171 := bstep (se 1 (by rfl) ⟨1707128, by rfl⟩ : syracuseStep 2276171 = 3414257) B3414257
theorem B2276225 : Blo 1008601 2276225 := bstep (se 2 (by rfl) ⟨853584, by rfl⟩ : syracuseStep 2276225 = 1707169) B1707169
theorem B1620875 : Blo 1008601 1620875 := bstep (se 1 (by rfl) ⟨1215656, by rfl⟩ : syracuseStep 1620875 = 2431313) B2431313
theorem B5749805 : Blo 1008601 5749805 := bstep (se 3 (by rfl) ⟨1078088, by rfl⟩ : syracuseStep 5749805 = 2156177) B2156177
theorem B2047027 : Blo 1008601 2047027 := bstep (se 1 (by rfl) ⟨1535270, by rfl⟩ : syracuseStep 2047027 = 3070541) B3070541
theorem B2276441 : Blo 1008601 2276441 := bstep (se 2 (by rfl) ⟨853665, by rfl⟩ : syracuseStep 2276441 = 1707331) B1707331
theorem B7683173 : Blo 1008601 7683173 := bstep (se 4 (by rfl) ⟨720297, by rfl⟩ : syracuseStep 7683173 = 1440595) B1440595
theorem B6077591 : Blo 1008601 6077591 := bstep (se 1 (by rfl) ⟨4558193, by rfl⟩ : syracuseStep 6077591 = 9116387) B9116387
theorem B3456179 : Blo 1008601 3456179 := bstep (se 1 (by rfl) ⟨2592134, by rfl⟩ : syracuseStep 3456179 = 5184269) B5184269
theorem B2276531 : Blo 1008601 2276531 := bstep (se 1 (by rfl) ⟨1707398, by rfl⟩ : syracuseStep 2276531 = 3414797) B3414797
theorem B2276567 : Blo 1008601 2276567 := bstep (se 1 (by rfl) ⟨1707425, by rfl⟩ : syracuseStep 2276567 = 3414851) B3414851
theorem B70139141 : Blo 1008601 70139141 := bstep (se 4 (by rfl) ⟨6575544, by rfl⟩ : syracuseStep 70139141 = 13151089) B13151089
theorem B2309399 : Blo 1008601 2309399 := bstep (se 1 (by rfl) ⟨1732049, by rfl⟩ : syracuseStep 2309399 = 3464099) B3464099
theorem B2276747 : Blo 1008601 2276747 := bstep (se 1 (by rfl) ⟨1707560, by rfl⟩ : syracuseStep 2276747 = 3415121) B3415121
theorem B2276801 : Blo 1008601 2276801 := bstep (se 2 (by rfl) ⟨853800, by rfl⟩ : syracuseStep 2276801 = 1707601) B1707601
theorem B7683659 : Blo 1008601 7683659 := bstep (se 1 (by rfl) ⟨5762744, by rfl⟩ : syracuseStep 7683659 = 11525489) B11525489
theorem B2277017 : Blo 1008601 2277017 := bstep (se 2 (by rfl) ⟨853881, by rfl⟩ : syracuseStep 2277017 = 1707763) B1707763
theorem B1621657 : Blo 1008601 1621657 := bstep (se 2 (by rfl) ⟨608121, by rfl⟩ : syracuseStep 1621657 = 1216243) B1216243
theorem B1621721 : Blo 1008601 1621721 := bstep (se 2 (by rfl) ⟨608145, by rfl⟩ : syracuseStep 1621721 = 1216291) B1216291
theorem B2277107 : Blo 1008601 2277107 := bstep (se 1 (by rfl) ⟨1707830, by rfl⟩ : syracuseStep 2277107 = 3415661) B3415661
theorem B8208145 : Blo 1008601 8208145 := bstep (se 2 (by rfl) ⟨3078054, by rfl⟩ : syracuseStep 8208145 = 6156109) B6156109
theorem B2277143 : Blo 1008601 2277143 := bstep (se 1 (by rfl) ⟨1707857, by rfl⟩ : syracuseStep 2277143 = 3415715) B3415715
theorem B1916723 : Blo 1008601 1916723 := bstep (se 1 (by rfl) ⟨1437542, by rfl⟩ : syracuseStep 1916723 = 2875085) B2875085
theorem B1621849 : Blo 1008601 1621849 := bstep (se 2 (by rfl) ⟨608193, by rfl⟩ : syracuseStep 1621849 = 1216387) B1216387
theorem B1818497 : Blo 1008601 1818497 := bstep (se 2 (by rfl) ⟨681936, by rfl⟩ : syracuseStep 1818497 = 1363873) B1363873
theorem B41533361 : Blo 1008601 41533361 := bstep (se 2 (by rfl) ⟨15575010, by rfl⟩ : syracuseStep 41533361 = 31150021) B31150021
theorem B1916875 : Blo 1008601 1916875 := bstep (se 1 (by rfl) ⟨1437656, by rfl⟩ : syracuseStep 1916875 = 2875313) B2875313
theorem B2277323 : Blo 1008601 2277323 := bstep (se 1 (by rfl) ⟨1707992, by rfl⟩ : syracuseStep 2277323 = 3415985) B3415985
theorem B2277377 : Blo 1008601 2277377 := bstep (se 2 (by rfl) ⟨854016, by rfl⟩ : syracuseStep 2277377 = 1708033) B1708033
theorem B1818713 : Blo 1008601 1818713 := bstep (se 2 (by rfl) ⟨682017, by rfl⟩ : syracuseStep 1818713 = 1364035) B1364035
theorem B2277593 : Blo 1008601 2277593 := bstep (se 2 (by rfl) ⟨854097, by rfl⟩ : syracuseStep 2277593 = 1708195) B1708195
theorem B1917209 : Blo 1008601 1917209 := bstep (se 2 (by rfl) ⟨718953, by rfl⟩ : syracuseStep 1917209 = 1437907) B1437907
theorem B2277683 : Blo 1008601 2277683 := bstep (se 1 (by rfl) ⟨1708262, by rfl⟩ : syracuseStep 2277683 = 3416525) B3416525
theorem B2277719 : Blo 1008601 2277719 := bstep (se 1 (by rfl) ⟨1708289, by rfl⟩ : syracuseStep 2277719 = 3416579) B3416579
theorem B3686849 : Blo 1008601 3686849 := bstep (se 2 (by rfl) ⟨1382568, by rfl⟩ : syracuseStep 3686849 = 2765137) B2765137
theorem B4309469 : Blo 1008601 4309469 := bstep (se 3 (by rfl) ⟨808025, by rfl⟩ : syracuseStep 4309469 = 1616051) B1616051
theorem B2277899 : Blo 1008601 2277899 := bstep (se 1 (by rfl) ⟨1708424, by rfl⟩ : syracuseStep 2277899 = 3416849) B3416849
theorem B3457559 : Blo 1008601 3457559 := bstep (se 1 (by rfl) ⟨2593169, by rfl⟩ : syracuseStep 3457559 = 5186339) B5186339
theorem B2277953 : Blo 1008601 2277953 := bstep (se 2 (by rfl) ⟨854232, by rfl⟩ : syracuseStep 2277953 = 1708465) B1708465
theorem B2048665 : Blo 1008601 2048665 := bstep (se 2 (by rfl) ⟨768249, by rfl⟩ : syracuseStep 2048665 = 1536499) B1536499
theorem B2278169 : Blo 1008601 2278169 := bstep (se 2 (by rfl) ⟨854313, by rfl⟩ : syracuseStep 2278169 = 1708627) B1708627
theorem B8209187 : Blo 1008601 8209187 := bstep (se 1 (by rfl) ⟨6156890, by rfl⟩ : syracuseStep 8209187 = 12313781) B12313781
theorem B2278259 : Blo 1008601 2278259 := bstep (se 1 (by rfl) ⟨1708694, by rfl⟩ : syracuseStep 2278259 = 3417389) B3417389
theorem B1917847 : Blo 1008601 1917847 := bstep (se 1 (by rfl) ⟨1438385, by rfl⟩ : syracuseStep 1917847 = 2876771) B2876771
theorem B2278295 : Blo 1008601 2278295 := bstep (se 1 (by rfl) ⟨1708721, by rfl⟩ : syracuseStep 2278295 = 3417443) B3417443
theorem B4310167 : Blo 1008601 4310167 := bstep (se 1 (by rfl) ⟨3232625, by rfl⟩ : syracuseStep 4310167 = 6465251) B6465251
theorem B1295947 : Blo 1008601 1295947 := bstep (se 1 (by rfl) ⟨971960, by rfl⟩ : syracuseStep 1295947 = 1943921) B1943921
theorem B1918667 : Blo 1008601 1918667 := bstep (se 1 (by rfl) ⟨1439000, by rfl⟩ : syracuseStep 1918667 = 2878001) B2878001
theorem B1918721 : Blo 1008601 1918721 := bstep (se 2 (by rfl) ⟨719520, by rfl⟩ : syracuseStep 1918721 = 1439041) B1439041
theorem B5916433 : Blo 1008601 5916433 := bstep (se 2 (by rfl) ⟨2218662, by rfl⟩ : syracuseStep 5916433 = 4437325) B4437325
theorem B3459037 : Blo 1008601 3459037 := bstep (se 3 (by rfl) ⟨648569, by rfl⟩ : syracuseStep 3459037 = 1297139) B1297139
theorem B1820659 : Blo 1008601 1820659 := bstep (se 1 (by rfl) ⟨1365494, by rfl⟩ : syracuseStep 1820659 = 2730989) B2730989
theorem B1296523 : Blo 1008601 1296523 := bstep (se 1 (by rfl) ⟨972392, by rfl⟩ : syracuseStep 1296523 = 1944785) B1944785
theorem B7293361 : Blo 1008601 7293361 := bstep (se 2 (by rfl) ⟨2735010, by rfl⟩ : syracuseStep 7293361 = 5470021) B5470021
theorem B4311569 : Blo 1008601 4311569 := bstep (se 2 (by rfl) ⟨1616838, by rfl⟩ : syracuseStep 4311569 = 3233677) B3233677
theorem B3689011 : Blo 1008601 3689011 := bstep (se 1 (by rfl) ⟨2766758, by rfl⟩ : syracuseStep 3689011 = 5533517) B5533517
theorem B1919639 : Blo 1008601 1919639 := bstep (se 1 (by rfl) ⟨1439729, by rfl⟩ : syracuseStep 1919639 = 2879459) B2879459
theorem B9227159 : Blo 1008601 9227159 := bstep (se 1 (by rfl) ⟨6920369, by rfl⟩ : syracuseStep 9227159 = 13840739) B13840739
theorem B1920179 : Blo 1008601 1920179 := bstep (se 1 (by rfl) ⟨1440134, by rfl⟩ : syracuseStep 1920179 = 2880269) B2880269
theorem B1363159 : Blo 1008601 1363159 := bstep (se 1 (by rfl) ⟨1022369, by rfl⟩ : syracuseStep 1363159 = 2044739) B2044739
theorem B7294283 : Blo 1008601 7294283 := bstep (se 1 (by rfl) ⟨5470712, by rfl⟩ : syracuseStep 7294283 = 10941425) B10941425
theorem B10800485 : Blo 1008601 10800485 := bstep (se 4 (by rfl) ⟨1012545, by rfl⟩ : syracuseStep 10800485 = 2025091) B2025091
theorem B22171153 : Blo 1008601 22171153 := bstep (se 2 (by rfl) ⟨8314182, by rfl⟩ : syracuseStep 22171153 = 16628365) B16628365
theorem B8638103 : Blo 1008601 8638103 := bstep (se 1 (by rfl) ⟨6478577, by rfl⟩ : syracuseStep 8638103 = 12957155) B12957155
theorem B1920665 : Blo 1008601 1920665 := bstep (se 2 (by rfl) ⟨720249, by rfl⟩ : syracuseStep 1920665 = 1440499) B1440499
theorem B3067595 : Blo 1008601 3067595 := bstep (se 1 (by rfl) ⟨2300696, by rfl⟩ : syracuseStep 3067595 = 4601393) B4601393
theorem B1134679 : Blo 1008601 1134679 := bstep (se 1 (by rfl) ⟨851009, by rfl⟩ : syracuseStep 1134679 = 1702019) B1702019
theorem B3461213 : Blo 1008601 3461213 := bstep (se 3 (by rfl) ⟨648977, by rfl⟩ : syracuseStep 3461213 = 1297955) B1297955
theorem B5460119 : Blo 1008601 5460119 := bstep (se 1 (by rfl) ⟨4095089, by rfl⟩ : syracuseStep 5460119 = 8190179) B8190179
theorem B1134859 : Blo 1008601 1134859 := bstep (se 1 (by rfl) ⟨851144, by rfl⟩ : syracuseStep 1134859 = 1702289) B1702289
theorem B1134967 : Blo 1008601 1134967 := bstep (se 1 (by rfl) ⟨851225, by rfl⟩ : syracuseStep 1134967 = 1702451) B1702451
theorem B1298903 : Blo 1008601 1298903 := bstep (se 1 (by rfl) ⟨974177, by rfl⟩ : syracuseStep 1298903 = 1948355) B1948355
theorem B1135147 : Blo 1008601 1135147 := bstep (se 1 (by rfl) ⟨851360, by rfl⟩ : syracuseStep 1135147 = 1702721) B1702721
theorem B3232345 : Blo 1008601 3232345 := bstep (se 2 (by rfl) ⟨1212129, by rfl⟩ : syracuseStep 3232345 = 2424259) B2424259
theorem B1135255 : Blo 1008601 1135255 := bstep (se 1 (by rfl) ⟨851441, by rfl⟩ : syracuseStep 1135255 = 1702883) B1702883
theorem B7689005 : Blo 1008601 7689005 := bstep (se 3 (by rfl) ⟨1441688, by rfl⟩ : syracuseStep 7689005 = 2883377) B2883377
theorem B1135435 : Blo 1008601 1135435 := bstep (se 1 (by rfl) ⟨851576, by rfl⟩ : syracuseStep 1135435 = 1703153) B1703153
theorem B3068761 : Blo 1008601 3068761 := bstep (se 2 (by rfl) ⟨1150785, by rfl⟩ : syracuseStep 3068761 = 2301571) B2301571
theorem B1135543 : Blo 1008601 1135543 := bstep (se 1 (by rfl) ⟨851657, by rfl⟩ : syracuseStep 1135543 = 1703315) B1703315
theorem B2774081 : Blo 1008601 2774081 := bstep (se 2 (by rfl) ⟨1040280, by rfl⟩ : syracuseStep 2774081 = 2080561) B2080561
theorem B1922123 : Blo 1008601 1922123 := bstep (se 1 (by rfl) ⟨1441592, by rfl⟩ : syracuseStep 1922123 = 2883185) B2883185
theorem B1135723 : Blo 1008601 1135723 := bstep (se 1 (by rfl) ⟨851792, by rfl⟩ : syracuseStep 1135723 = 1703585) B1703585
theorem B17290421 : Blo 1008601 17290421 := bstep (se 5 (by rfl) ⟨810488, by rfl⟩ : syracuseStep 17290421 = 1620977) B1620977
theorem B2872523 : Blo 1008601 2872523 := bstep (se 1 (by rfl) ⟨2154392, by rfl⟩ : syracuseStep 2872523 = 4308785) B4308785
theorem B1135831 : Blo 1008601 1135831 := bstep (se 1 (by rfl) ⟨851873, by rfl⟩ : syracuseStep 1135831 = 1703747) B1703747
theorem B1922305 : Blo 1008601 1922305 := bstep (se 2 (by rfl) ⟨720864, by rfl⟩ : syracuseStep 1922305 = 1441729) B1441729
theorem B1136011 : Blo 1008601 1136011 := bstep (se 1 (by rfl) ⟨852008, by rfl⟩ : syracuseStep 1136011 = 1704017) B1704017
theorem B4314541 : Blo 1008601 4314541 := bstep (se 3 (by rfl) ⟨808976, by rfl⟩ : syracuseStep 4314541 = 1617953) B1617953
theorem B1136119 : Blo 1008601 1136119 := bstep (se 1 (by rfl) ⟨852089, by rfl⟩ : syracuseStep 1136119 = 1704179) B1704179
theorem B8640017 : Blo 1008601 8640017 := bstep (se 2 (by rfl) ⟨3240006, by rfl⟩ : syracuseStep 8640017 = 6480013) B6480013
theorem B2872921 : Blo 1008601 2872921 := bstep (se 2 (by rfl) ⟨1077345, by rfl⟩ : syracuseStep 2872921 = 2154691) B2154691
theorem B1136299 : Blo 1008601 1136299 := bstep (se 1 (by rfl) ⟨852224, by rfl⟩ : syracuseStep 1136299 = 1704449) B1704449
theorem B6477529 : Blo 1008601 6477529 := bstep (se 2 (by rfl) ⟨2429073, by rfl⟩ : syracuseStep 6477529 = 4858147) B4858147
theorem B4314883 : Blo 1008601 4314883 := bstep (se 1 (by rfl) ⟨3236162, by rfl⟩ : syracuseStep 4314883 = 6472325) B6472325
theorem B1136407 : Blo 1008601 1136407 := bstep (se 1 (by rfl) ⟨852305, by rfl⟩ : syracuseStep 1136407 = 1704611) B1704611
theorem B1136587 : Blo 1008601 1136587 := bstep (se 1 (by rfl) ⟨852440, by rfl⟩ : syracuseStep 1136587 = 1704881) B1704881
theorem B1136695 : Blo 1008601 1136695 := bstep (se 1 (by rfl) ⟨852521, by rfl⟩ : syracuseStep 1136695 = 1705043) B1705043
theorem B1136875 : Blo 1008601 1136875 := bstep (se 1 (by rfl) ⟨852656, by rfl⟩ : syracuseStep 1136875 = 1705313) B1705313
theorem B3234113 : Blo 1008601 3234113 := bstep (se 2 (by rfl) ⟨1212792, by rfl⟩ : syracuseStep 3234113 = 2425585) B2425585
theorem B1136983 : Blo 1008601 1136983 := bstep (se 1 (by rfl) ⟨852737, by rfl⟩ : syracuseStep 1136983 = 1705475) B1705475
theorem B5757277 : Blo 1008601 5757277 := bstep (se 3 (by rfl) ⟨1079489, by rfl⟩ : syracuseStep 5757277 = 2158979) B2158979
theorem B49174901 : Blo 1008601 49174901 := bstep (se 5 (by rfl) ⟨2305073, by rfl⟩ : syracuseStep 49174901 = 4610147) B4610147
theorem B1137163 : Blo 1008601 1137163 := bstep (se 1 (by rfl) ⟨852872, by rfl⟩ : syracuseStep 1137163 = 1705745) B1705745
theorem B1137271 : Blo 1008601 1137271 := bstep (se 1 (by rfl) ⟨852953, by rfl⟩ : syracuseStep 1137271 = 1705907) B1705907
theorem B4315841 : Blo 1008601 4315841 := bstep (se 2 (by rfl) ⟨1618440, by rfl⟩ : syracuseStep 4315841 = 3236881) B3236881
theorem B1137451 : Blo 1008601 1137451 := bstep (se 1 (by rfl) ⟨853088, by rfl⟩ : syracuseStep 1137451 = 1706177) B1706177
theorem B2874163 : Blo 1008601 2874163 := bstep (se 1 (by rfl) ⟨2155622, by rfl⟩ : syracuseStep 2874163 = 4311245) B4311245
theorem B1137559 : Blo 1008601 1137559 := bstep (se 1 (by rfl) ⟨853169, by rfl⟩ : syracuseStep 1137559 = 1706339) B1706339
theorem B3071027 : Blo 1008601 3071027 := bstep (se 1 (by rfl) ⟨2303270, by rfl⟩ : syracuseStep 3071027 = 4606541) B4606541
theorem B1137739 : Blo 1008601 1137739 := bstep (se 1 (by rfl) ⟨853304, by rfl⟩ : syracuseStep 1137739 = 1706609) B1706609
theorem B8313949 : Blo 1008601 8313949 := bstep (se 3 (by rfl) ⟨1558865, by rfl⟩ : syracuseStep 8313949 = 3117731) B3117731
theorem B1137847 : Blo 1008601 1137847 := bstep (se 1 (by rfl) ⟨853385, by rfl⟩ : syracuseStep 1137847 = 1706771) B1706771
theorem B2186585 : Blo 1008601 2186585 := bstep (se 2 (by rfl) ⟨819969, by rfl⟩ : syracuseStep 2186585 = 1639939) B1639939
theorem B1138027 : Blo 1008601 1138027 := bstep (se 1 (by rfl) ⟨853520, by rfl⟩ : syracuseStep 1138027 = 1707041) B1707041
theorem B4152755 : Blo 1008601 4152755 := bstep (se 1 (by rfl) ⟨3114566, by rfl⟩ : syracuseStep 4152755 = 6229133) B6229133
theorem B1138135 : Blo 1008601 1138135 := bstep (se 1 (by rfl) ⟨853601, by rfl⟩ : syracuseStep 1138135 = 1707203) B1707203
theorem B3235393 : Blo 1008601 3235393 := bstep (se 2 (by rfl) ⟨1213272, by rfl⟩ : syracuseStep 3235393 = 2426545) B2426545
theorem B1138315 : Blo 1008601 1138315 := bstep (se 1 (by rfl) ⟨853736, by rfl⟩ : syracuseStep 1138315 = 1707473) B1707473
theorem B1138423 : Blo 1008601 1138423 := bstep (se 1 (by rfl) ⟨853817, by rfl⟩ : syracuseStep 1138423 = 1707635) B1707635
theorem B1138603 : Blo 1008601 1138603 := bstep (se 1 (by rfl) ⟨853952, by rfl⟩ : syracuseStep 1138603 = 1707905) B1707905
theorem B1138711 : Blo 1008601 1138711 := bstep (se 1 (by rfl) ⟨854033, by rfl⟩ : syracuseStep 1138711 = 1708067) B1708067
theorem B7004225 : Blo 1008601 7004225 := bstep (se 2 (by rfl) ⟨2626584, by rfl⟩ : syracuseStep 7004225 = 5253169) B5253169
theorem B1728587 : Blo 1008601 1728587 := bstep (se 1 (by rfl) ⟨1296440, by rfl⟩ : syracuseStep 1728587 = 2592881) B2592881
theorem B4317259 : Blo 1008601 4317259 := bstep (se 1 (by rfl) ⟨3237944, by rfl⟩ : syracuseStep 4317259 = 6475889) B6475889
theorem B2187415 : Blo 1008601 2187415 := bstep (se 1 (by rfl) ⟨1640561, by rfl⟩ : syracuseStep 2187415 = 3281123) B3281123
theorem B1138891 : Blo 1008601 1138891 := bstep (se 1 (by rfl) ⟨854168, by rfl⟩ : syracuseStep 1138891 = 1708337) B1708337
theorem B1138999 : Blo 1008601 1138999 := bstep (se 1 (by rfl) ⟨854249, by rfl⟩ : syracuseStep 1138999 = 1708499) B1708499
theorem B4317533 : Blo 1008601 4317533 := bstep (se 3 (by rfl) ⟨809537, by rfl⟩ : syracuseStep 4317533 = 1619075) B1619075
theorem B18407897 : Blo 1008601 18407897 := bstep (se 2 (by rfl) ⟨6902961, by rfl⟩ : syracuseStep 18407897 = 13805923) B13805923
theorem B1728985 : Blo 1008601 1728985 := bstep (se 2 (by rfl) ⟨648369, by rfl⟩ : syracuseStep 1728985 = 1296739) B1296739
theorem B2155187 : Blo 1008601 2155187 := bstep (se 1 (by rfl) ⟨1616390, by rfl⟩ : syracuseStep 2155187 = 3232781) B3232781
theorem B3236573 : Blo 1008601 3236573 := bstep (se 3 (by rfl) ⟨606857, by rfl⟩ : syracuseStep 3236573 = 1213715) B1213715
theorem B59007797 : Blo 1008601 59007797 := bstep (se 5 (by rfl) ⟨2765990, by rfl⟩ : syracuseStep 59007797 = 5531981) B5531981
theorem B3072971 : Blo 1008601 3072971 := bstep (se 1 (by rfl) ⟨2304728, by rfl⟩ : syracuseStep 3072971 = 4609457) B4609457
theorem B1008619 : Blo 1008601 1008619 := bstep (se 1 (by rfl) ⟨756464, by rfl⟩ : syracuseStep 1008619 = 1512929) B1512929
theorem B1008631 : Blo 1008601 1008631 := bstep (se 1 (by rfl) ⟨756473, by rfl⟩ : syracuseStep 1008631 = 1512947) B1512947
theorem B1008651 : Blo 1008601 1008651 := bstep (se 1 (by rfl) ⟨756488, by rfl⟩ : syracuseStep 1008651 = 1512977) B1512977
theorem B16376849 : Blo 1008601 16376849 := bstep (se 2 (by rfl) ⟨6141318, by rfl⟩ : syracuseStep 16376849 = 12282637) B12282637
theorem B1008663 : Blo 1008601 1008663 := bstep (se 1 (by rfl) ⟨756497, by rfl⟩ : syracuseStep 1008663 = 1512995) B1512995
theorem B1008683 : Blo 1008601 1008683 := bstep (se 1 (by rfl) ⟨756512, by rfl⟩ : syracuseStep 1008683 = 1513025) B1513025
theorem B1008695 : Blo 1008601 1008695 := bstep (se 1 (by rfl) ⟨756521, by rfl⟩ : syracuseStep 1008695 = 1513043) B1513043
theorem B1008715 : Blo 1008601 1008715 := bstep (se 1 (by rfl) ⟨756536, by rfl⟩ : syracuseStep 1008715 = 1513073) B1513073
theorem B1008727 : Blo 1008601 1008727 := bstep (se 1 (by rfl) ⟨756545, by rfl⟩ : syracuseStep 1008727 = 1513091) B1513091
theorem B9725021 : Blo 1008601 9725021 := bstep (se 3 (by rfl) ⟨1823441, by rfl⟩ : syracuseStep 9725021 = 3646883) B3646883
theorem B1008747 : Blo 1008601 1008747 := bstep (se 1 (by rfl) ⟨756560, by rfl⟩ : syracuseStep 1008747 = 1513121) B1513121
theorem B1008759 : Blo 1008601 1008759 := bstep (se 1 (by rfl) ⟨756569, by rfl⟩ : syracuseStep 1008759 = 1513139) B1513139
theorem B1008779 : Blo 1008601 1008779 := bstep (se 1 (by rfl) ⟨756584, by rfl⟩ : syracuseStep 1008779 = 1513169) B1513169
theorem B1008791 : Blo 1008601 1008791 := bstep (se 1 (by rfl) ⟨756593, by rfl⟩ : syracuseStep 1008791 = 1513187) B1513187
theorem B1008811 : Blo 1008601 1008811 := bstep (se 1 (by rfl) ⟨756608, by rfl⟩ : syracuseStep 1008811 = 1513217) B1513217
theorem B4678829 : Blo 1008601 4678829 := bstep (se 3 (by rfl) ⟨877280, by rfl⟩ : syracuseStep 4678829 = 1754561) B1754561
theorem B1008823 : Blo 1008601 1008823 := bstep (se 1 (by rfl) ⟨756617, by rfl⟩ : syracuseStep 1008823 = 1513235) B1513235
theorem B1008843 : Blo 1008601 1008843 := bstep (se 1 (by rfl) ⟨756632, by rfl⟩ : syracuseStep 1008843 = 1513265) B1513265
theorem B1008855 : Blo 1008601 1008855 := bstep (se 1 (by rfl) ⟨756641, by rfl⟩ : syracuseStep 1008855 = 1513283) B1513283
theorem B1008875 : Blo 1008601 1008875 := bstep (se 1 (by rfl) ⟨756656, by rfl⟩ : syracuseStep 1008875 = 1513313) B1513313
theorem B1008887 : Blo 1008601 1008887 := bstep (se 1 (by rfl) ⟨756665, by rfl⟩ : syracuseStep 1008887 = 1513331) B1513331
theorem B1008907 : Blo 1008601 1008907 := bstep (se 1 (by rfl) ⟨756680, by rfl⟩ : syracuseStep 1008907 = 1513361) B1513361
theorem B7660817 : Blo 1008601 7660817 := bstep (se 2 (by rfl) ⟨2872806, by rfl⟩ : syracuseStep 7660817 = 5745613) B5745613
theorem B1008919 : Blo 1008601 1008919 := bstep (se 1 (by rfl) ⟨756689, by rfl⟩ : syracuseStep 1008919 = 1513379) B1513379
theorem B1008939 : Blo 1008601 1008939 := bstep (se 1 (by rfl) ⟨756704, by rfl⟩ : syracuseStep 1008939 = 1513409) B1513409
theorem B1008951 : Blo 1008601 1008951 := bstep (se 1 (by rfl) ⟨756713, by rfl⟩ : syracuseStep 1008951 = 1513427) B1513427
theorem B1008971 : Blo 1008601 1008971 := bstep (se 1 (by rfl) ⟨756728, by rfl⟩ : syracuseStep 1008971 = 1513457) B1513457
theorem B1008983 : Blo 1008601 1008983 := bstep (se 1 (by rfl) ⟨756737, by rfl⟩ : syracuseStep 1008983 = 1513475) B1513475
theorem B1009003 : Blo 1008601 1009003 := bstep (se 1 (by rfl) ⟨756752, by rfl⟩ : syracuseStep 1009003 = 1513505) B1513505
theorem B1009015 : Blo 1008601 1009015 := bstep (se 1 (by rfl) ⟨756761, by rfl⟩ : syracuseStep 1009015 = 1513523) B1513523
theorem B1009035 : Blo 1008601 1009035 := bstep (se 1 (by rfl) ⟨756776, by rfl⟩ : syracuseStep 1009035 = 1513553) B1513553
theorem B1009047 : Blo 1008601 1009047 := bstep (se 1 (by rfl) ⟨756785, by rfl⟩ : syracuseStep 1009047 = 1513571) B1513571
theorem B1009067 : Blo 1008601 1009067 := bstep (se 1 (by rfl) ⟨756800, by rfl⟩ : syracuseStep 1009067 = 1513601) B1513601
theorem B1009079 : Blo 1008601 1009079 := bstep (se 1 (by rfl) ⟨756809, by rfl⟩ : syracuseStep 1009079 = 1513619) B1513619
theorem B1009099 : Blo 1008601 1009099 := bstep (se 1 (by rfl) ⟨756824, by rfl⟩ : syracuseStep 1009099 = 1513649) B1513649
theorem B1009111 : Blo 1008601 1009111 := bstep (se 1 (by rfl) ⟨756833, by rfl⟩ : syracuseStep 1009111 = 1513667) B1513667
theorem B1009131 : Blo 1008601 1009131 := bstep (se 1 (by rfl) ⟨756848, by rfl⟩ : syracuseStep 1009131 = 1513697) B1513697
theorem B1009143 : Blo 1008601 1009143 := bstep (se 1 (by rfl) ⟨756857, by rfl⟩ : syracuseStep 1009143 = 1513715) B1513715
theorem B2156033 : Blo 1008601 2156033 := bstep (se 2 (by rfl) ⟨808512, by rfl⟩ : syracuseStep 2156033 = 1617025) B1617025
theorem B1009163 : Blo 1008601 1009163 := bstep (se 1 (by rfl) ⟨756872, by rfl⟩ : syracuseStep 1009163 = 1513745) B1513745
theorem B1009175 : Blo 1008601 1009175 := bstep (se 1 (by rfl) ⟨756881, by rfl⟩ : syracuseStep 1009175 = 1513763) B1513763
theorem B7792163 : Blo 1008601 7792163 := bstep (se 1 (by rfl) ⟨5844122, by rfl⟩ : syracuseStep 7792163 = 11688245) B11688245
theorem B1009195 : Blo 1008601 1009195 := bstep (se 1 (by rfl) ⟨756896, by rfl⟩ : syracuseStep 1009195 = 1513793) B1513793
theorem B1009207 : Blo 1008601 1009207 := bstep (se 1 (by rfl) ⟨756905, by rfl⟩ : syracuseStep 1009207 = 1513811) B1513811
theorem B1009227 : Blo 1008601 1009227 := bstep (se 1 (by rfl) ⟨756920, by rfl⟩ : syracuseStep 1009227 = 1513841) B1513841
theorem B1009239 : Blo 1008601 1009239 := bstep (se 1 (by rfl) ⟨756929, by rfl⟩ : syracuseStep 1009239 = 1513859) B1513859
theorem B1009259 : Blo 1008601 1009259 := bstep (se 1 (by rfl) ⟨756944, by rfl⟩ : syracuseStep 1009259 = 1513889) B1513889
theorem B1009271 : Blo 1008601 1009271 := bstep (se 1 (by rfl) ⟨756953, by rfl⟩ : syracuseStep 1009271 = 1513907) B1513907
theorem B1009291 : Blo 1008601 1009291 := bstep (se 1 (by rfl) ⟨756968, by rfl⟩ : syracuseStep 1009291 = 1513937) B1513937
theorem B1009303 : Blo 1008601 1009303 := bstep (se 1 (by rfl) ⟨756977, by rfl⟩ : syracuseStep 1009303 = 1513955) B1513955
theorem B2877079 : Blo 1008601 2877079 := bstep (se 1 (by rfl) ⟨2157809, by rfl⟩ : syracuseStep 2877079 = 4315619) B4315619
theorem B1009323 : Blo 1008601 1009323 := bstep (se 1 (by rfl) ⟨756992, by rfl⟩ : syracuseStep 1009323 = 1513985) B1513985
theorem B1009335 : Blo 1008601 1009335 := bstep (se 1 (by rfl) ⟨757001, by rfl⟩ : syracuseStep 1009335 = 1514003) B1514003
theorem B1009355 : Blo 1008601 1009355 := bstep (se 1 (by rfl) ⟨757016, by rfl⟩ : syracuseStep 1009355 = 1514033) B1514033
theorem B1009367 : Blo 1008601 1009367 := bstep (se 1 (by rfl) ⟨757025, by rfl⟩ : syracuseStep 1009367 = 1514051) B1514051
theorem B1009387 : Blo 1008601 1009387 := bstep (se 1 (by rfl) ⟨757040, by rfl⟩ : syracuseStep 1009387 = 1514081) B1514081
theorem B1009399 : Blo 1008601 1009399 := bstep (se 1 (by rfl) ⟨757049, by rfl⟩ : syracuseStep 1009399 = 1514099) B1514099
theorem B1009419 : Blo 1008601 1009419 := bstep (se 1 (by rfl) ⟨757064, by rfl⟩ : syracuseStep 1009419 = 1514129) B1514129
theorem B1009431 : Blo 1008601 1009431 := bstep (se 1 (by rfl) ⟨757073, by rfl⟩ : syracuseStep 1009431 = 1514147) B1514147
theorem B1009451 : Blo 1008601 1009451 := bstep (se 1 (by rfl) ⟨757088, by rfl⟩ : syracuseStep 1009451 = 1514177) B1514177
theorem B1009463 : Blo 1008601 1009463 := bstep (se 1 (by rfl) ⟨757097, by rfl⟩ : syracuseStep 1009463 = 1514195) B1514195
theorem B1009483 : Blo 1008601 1009483 := bstep (se 1 (by rfl) ⟨757112, by rfl⟩ : syracuseStep 1009483 = 1514225) B1514225
theorem B1009495 : Blo 1008601 1009495 := bstep (se 1 (by rfl) ⟨757121, by rfl⟩ : syracuseStep 1009495 = 1514243) B1514243
theorem B2156375 : Blo 1008601 2156375 := bstep (se 1 (by rfl) ⟨1617281, by rfl⟩ : syracuseStep 2156375 = 3234563) B3234563
theorem B1009515 : Blo 1008601 1009515 := bstep (se 1 (by rfl) ⟨757136, by rfl⟩ : syracuseStep 1009515 = 1514273) B1514273
theorem B1009527 : Blo 1008601 1009527 := bstep (se 1 (by rfl) ⟨757145, by rfl⟩ : syracuseStep 1009527 = 1514291) B1514291
theorem B1009547 : Blo 1008601 1009547 := bstep (se 1 (by rfl) ⟨757160, by rfl⟩ : syracuseStep 1009547 = 1514321) B1514321
theorem B1009559 : Blo 1008601 1009559 := bstep (se 1 (by rfl) ⟨757169, by rfl⟩ : syracuseStep 1009559 = 1514339) B1514339
theorem B1009579 : Blo 1008601 1009579 := bstep (se 1 (by rfl) ⟨757184, by rfl⟩ : syracuseStep 1009579 = 1514369) B1514369
theorem B1009591 : Blo 1008601 1009591 := bstep (se 1 (by rfl) ⟨757193, by rfl⟩ : syracuseStep 1009591 = 1514387) B1514387
theorem B1009611 : Blo 1008601 1009611 := bstep (se 1 (by rfl) ⟨757208, by rfl⟩ : syracuseStep 1009611 = 1514417) B1514417
theorem B1009623 : Blo 1008601 1009623 := bstep (se 1 (by rfl) ⟨757217, by rfl⟩ : syracuseStep 1009623 = 1514435) B1514435
theorem B1009643 : Blo 1008601 1009643 := bstep (se 1 (by rfl) ⟨757232, by rfl⟩ : syracuseStep 1009643 = 1514465) B1514465
theorem B1009655 : Blo 1008601 1009655 := bstep (se 1 (by rfl) ⟨757241, by rfl⟩ : syracuseStep 1009655 = 1514483) B1514483
theorem B1009675 : Blo 1008601 1009675 := bstep (se 1 (by rfl) ⟨757256, by rfl⟩ : syracuseStep 1009675 = 1514513) B1514513
theorem B1009687 : Blo 1008601 1009687 := bstep (se 1 (by rfl) ⟨757265, by rfl⟩ : syracuseStep 1009687 = 1514531) B1514531
theorem B1009707 : Blo 1008601 1009707 := bstep (se 1 (by rfl) ⟨757280, by rfl⟩ : syracuseStep 1009707 = 1514561) B1514561
theorem B1009719 : Blo 1008601 1009719 := bstep (se 1 (by rfl) ⟨757289, by rfl⟩ : syracuseStep 1009719 = 1514579) B1514579
theorem B1009739 : Blo 1008601 1009739 := bstep (se 1 (by rfl) ⟨757304, by rfl⟩ : syracuseStep 1009739 = 1514609) B1514609
theorem B1009751 : Blo 1008601 1009751 := bstep (se 1 (by rfl) ⟨757313, by rfl⟩ : syracuseStep 1009751 = 1514627) B1514627
theorem B1009771 : Blo 1008601 1009771 := bstep (se 1 (by rfl) ⟨757328, by rfl⟩ : syracuseStep 1009771 = 1514657) B1514657
theorem B1009783 : Blo 1008601 1009783 := bstep (se 1 (by rfl) ⟨757337, by rfl⟩ : syracuseStep 1009783 = 1514675) B1514675
theorem B1009803 : Blo 1008601 1009803 := bstep (se 1 (by rfl) ⟨757352, by rfl⟩ : syracuseStep 1009803 = 1514705) B1514705
theorem B3500183 : Blo 1008601 3500183 := bstep (se 1 (by rfl) ⟨2625137, by rfl⟩ : syracuseStep 3500183 = 5250275) B5250275
theorem B1009815 : Blo 1008601 1009815 := bstep (se 1 (by rfl) ⟨757361, by rfl⟩ : syracuseStep 1009815 = 1514723) B1514723
theorem B1009835 : Blo 1008601 1009835 := bstep (se 1 (by rfl) ⟨757376, by rfl⟩ : syracuseStep 1009835 = 1514753) B1514753
theorem B1009847 : Blo 1008601 1009847 := bstep (se 1 (by rfl) ⟨757385, by rfl⟩ : syracuseStep 1009847 = 1514771) B1514771
theorem B1009867 : Blo 1008601 1009867 := bstep (se 1 (by rfl) ⟨757400, by rfl⟩ : syracuseStep 1009867 = 1514801) B1514801
theorem B1009879 : Blo 1008601 1009879 := bstep (se 1 (by rfl) ⟨757409, by rfl⟩ : syracuseStep 1009879 = 1514819) B1514819
theorem B1009899 : Blo 1008601 1009899 := bstep (se 1 (by rfl) ⟨757424, by rfl⟩ : syracuseStep 1009899 = 1514849) B1514849
theorem B1009911 : Blo 1008601 1009911 := bstep (se 1 (by rfl) ⟨757433, by rfl⟩ : syracuseStep 1009911 = 1514867) B1514867
theorem B1009931 : Blo 1008601 1009931 := bstep (se 1 (by rfl) ⟨757448, by rfl⟩ : syracuseStep 1009931 = 1514897) B1514897
theorem B1009943 : Blo 1008601 1009943 := bstep (se 1 (by rfl) ⟨757457, by rfl⟩ : syracuseStep 1009943 = 1514915) B1514915
theorem B1009963 : Blo 1008601 1009963 := bstep (se 1 (by rfl) ⟨757472, by rfl⟩ : syracuseStep 1009963 = 1514945) B1514945
theorem B11659565 : Blo 1008601 11659565 := bstep (se 3 (by rfl) ⟨2186168, by rfl⟩ : syracuseStep 11659565 = 4372337) B4372337
theorem B1009975 : Blo 1008601 1009975 := bstep (se 1 (by rfl) ⟨757481, by rfl⟩ : syracuseStep 1009975 = 1514963) B1514963
theorem B1534283 : Blo 1008601 1534283 := bstep (se 1 (by rfl) ⟨1150712, by rfl⟩ : syracuseStep 1534283 = 2301425) B2301425
theorem B1009995 : Blo 1008601 1009995 := bstep (se 1 (by rfl) ⟨757496, by rfl⟩ : syracuseStep 1009995 = 1514993) B1514993
theorem B1010007 : Blo 1008601 1010007 := bstep (se 1 (by rfl) ⟨757505, by rfl⟩ : syracuseStep 1010007 = 1515011) B1515011
theorem B1010027 : Blo 1008601 1010027 := bstep (se 1 (by rfl) ⟨757520, by rfl⟩ : syracuseStep 1010027 = 1515041) B1515041
theorem B1010039 : Blo 1008601 1010039 := bstep (se 1 (by rfl) ⟨757529, by rfl⟩ : syracuseStep 1010039 = 1515059) B1515059
theorem B1010059 : Blo 1008601 1010059 := bstep (se 1 (by rfl) ⟨757544, by rfl⟩ : syracuseStep 1010059 = 1515089) B1515089
theorem B1010071 : Blo 1008601 1010071 := bstep (se 1 (by rfl) ⟨757553, by rfl⟩ : syracuseStep 1010071 = 1515107) B1515107
theorem B1010091 : Blo 1008601 1010091 := bstep (se 1 (by rfl) ⟨757568, by rfl⟩ : syracuseStep 1010091 = 1515137) B1515137
theorem B1010103 : Blo 1008601 1010103 := bstep (se 1 (by rfl) ⟨757577, by rfl⟩ : syracuseStep 1010103 = 1515155) B1515155
theorem B1010123 : Blo 1008601 1010123 := bstep (se 1 (by rfl) ⟨757592, by rfl⟩ : syracuseStep 1010123 = 1515185) B1515185
theorem B1010135 : Blo 1008601 1010135 := bstep (se 1 (by rfl) ⟨757601, by rfl⟩ : syracuseStep 1010135 = 1515203) B1515203
theorem B1010155 : Blo 1008601 1010155 := bstep (se 1 (by rfl) ⟨757616, by rfl⟩ : syracuseStep 1010155 = 1515233) B1515233
theorem B1010167 : Blo 1008601 1010167 := bstep (se 1 (by rfl) ⟨757625, by rfl⟩ : syracuseStep 1010167 = 1515251) B1515251
theorem B1010187 : Blo 1008601 1010187 := bstep (se 1 (by rfl) ⟨757640, by rfl⟩ : syracuseStep 1010187 = 1515281) B1515281
theorem B1010199 : Blo 1008601 1010199 := bstep (se 1 (by rfl) ⟨757649, by rfl⟩ : syracuseStep 1010199 = 1515299) B1515299
theorem B1010219 : Blo 1008601 1010219 := bstep (se 1 (by rfl) ⟨757664, by rfl⟩ : syracuseStep 1010219 = 1515329) B1515329
theorem B1010231 : Blo 1008601 1010231 := bstep (se 1 (by rfl) ⟨757673, by rfl⟩ : syracuseStep 1010231 = 1515347) B1515347
theorem B1010251 : Blo 1008601 1010251 := bstep (se 1 (by rfl) ⟨757688, by rfl⟩ : syracuseStep 1010251 = 1515377) B1515377
theorem B1010263 : Blo 1008601 1010263 := bstep (se 1 (by rfl) ⟨757697, by rfl⟩ : syracuseStep 1010263 = 1515395) B1515395
theorem B1010283 : Blo 1008601 1010283 := bstep (se 1 (by rfl) ⟨757712, by rfl⟩ : syracuseStep 1010283 = 1515425) B1515425
theorem B1010295 : Blo 1008601 1010295 := bstep (se 1 (by rfl) ⟨757721, by rfl⟩ : syracuseStep 1010295 = 1515443) B1515443
theorem B1010315 : Blo 1008601 1010315 := bstep (se 1 (by rfl) ⟨757736, by rfl⟩ : syracuseStep 1010315 = 1515473) B1515473
theorem B1010327 : Blo 1008601 1010327 := bstep (se 1 (by rfl) ⟨757745, by rfl⟩ : syracuseStep 1010327 = 1515491) B1515491
theorem B1010347 : Blo 1008601 1010347 := bstep (se 1 (by rfl) ⟨757760, by rfl⟩ : syracuseStep 1010347 = 1515521) B1515521
theorem B1010359 : Blo 1008601 1010359 := bstep (se 1 (by rfl) ⟨757769, by rfl⟩ : syracuseStep 1010359 = 1515539) B1515539
theorem B1010379 : Blo 1008601 1010379 := bstep (se 1 (by rfl) ⟨757784, by rfl⟩ : syracuseStep 1010379 = 1515569) B1515569
theorem B1010391 : Blo 1008601 1010391 := bstep (se 1 (by rfl) ⟨757793, by rfl⟩ : syracuseStep 1010391 = 1515587) B1515587
theorem B1010411 : Blo 1008601 1010411 := bstep (se 1 (by rfl) ⟨757808, by rfl⟩ : syracuseStep 1010411 = 1515617) B1515617
theorem B1010423 : Blo 1008601 1010423 := bstep (se 1 (by rfl) ⟨757817, by rfl⟩ : syracuseStep 1010423 = 1515635) B1515635
theorem B1010443 : Blo 1008601 1010443 := bstep (se 1 (by rfl) ⟨757832, by rfl⟩ : syracuseStep 1010443 = 1515665) B1515665
theorem B1010455 : Blo 1008601 1010455 := bstep (se 1 (by rfl) ⟨757841, by rfl⟩ : syracuseStep 1010455 = 1515683) B1515683
theorem B1010475 : Blo 1008601 1010475 := bstep (se 1 (by rfl) ⟨757856, by rfl⟩ : syracuseStep 1010475 = 1515713) B1515713
theorem B1010487 : Blo 1008601 1010487 := bstep (se 1 (by rfl) ⟨757865, by rfl⟩ : syracuseStep 1010487 = 1515731) B1515731
theorem B1010507 : Blo 1008601 1010507 := bstep (se 1 (by rfl) ⟨757880, by rfl⟩ : syracuseStep 1010507 = 1515761) B1515761
theorem B1010519 : Blo 1008601 1010519 := bstep (se 1 (by rfl) ⟨757889, by rfl⟩ : syracuseStep 1010519 = 1515779) B1515779
theorem B1010539 : Blo 1008601 1010539 := bstep (se 1 (by rfl) ⟨757904, by rfl⟩ : syracuseStep 1010539 = 1515809) B1515809
theorem B1010551 : Blo 1008601 1010551 := bstep (se 1 (by rfl) ⟨757913, by rfl⟩ : syracuseStep 1010551 = 1515827) B1515827
theorem B5106563 : Blo 1008601 5106563 := bstep (se 1 (by rfl) ⟨3829922, by rfl⟩ : syracuseStep 5106563 = 7659845) B7659845
theorem B1010571 : Blo 1008601 1010571 := bstep (se 1 (by rfl) ⟨757928, by rfl⟩ : syracuseStep 1010571 = 1515857) B1515857
theorem B4320145 : Blo 1008601 4320145 := bstep (se 2 (by rfl) ⟨1620054, by rfl⟩ : syracuseStep 4320145 = 3240109) B3240109
theorem B1010583 : Blo 1008601 1010583 := bstep (se 1 (by rfl) ⟨757937, by rfl⟩ : syracuseStep 1010583 = 1515875) B1515875
theorem B1010603 : Blo 1008601 1010603 := bstep (se 1 (by rfl) ⟨757952, by rfl⟩ : syracuseStep 1010603 = 1515905) B1515905
theorem B1010615 : Blo 1008601 1010615 := bstep (se 1 (by rfl) ⟨757961, by rfl⟩ : syracuseStep 1010615 = 1515923) B1515923
theorem B1010635 : Blo 1008601 1010635 := bstep (se 1 (by rfl) ⟨757976, by rfl⟩ : syracuseStep 1010635 = 1515953) B1515953
theorem B2878411 : Blo 1008601 2878411 := bstep (se 1 (by rfl) ⟨2158808, by rfl⟩ : syracuseStep 2878411 = 4317617) B4317617
theorem B1010647 : Blo 1008601 1010647 := bstep (se 1 (by rfl) ⟨757985, by rfl⟩ : syracuseStep 1010647 = 1515971) B1515971
theorem B1010667 : Blo 1008601 1010667 := bstep (se 1 (by rfl) ⟨758000, by rfl⟩ : syracuseStep 1010667 = 1516001) B1516001
theorem B1010679 : Blo 1008601 1010679 := bstep (se 1 (by rfl) ⟨758009, by rfl⟩ : syracuseStep 1010679 = 1516019) B1516019
theorem B1010699 : Blo 1008601 1010699 := bstep (se 1 (by rfl) ⟨758024, by rfl⟩ : syracuseStep 1010699 = 1516049) B1516049
theorem B1010711 : Blo 1008601 1010711 := bstep (se 1 (by rfl) ⟨758033, by rfl⟩ : syracuseStep 1010711 = 1516067) B1516067
theorem B1010731 : Blo 1008601 1010731 := bstep (se 1 (by rfl) ⟨758048, by rfl⟩ : syracuseStep 1010731 = 1516097) B1516097
theorem B3992627 : Blo 1008601 3992627 := bstep (se 1 (by rfl) ⟨2994470, by rfl⟩ : syracuseStep 3992627 = 5988941) B5988941
theorem B1010743 : Blo 1008601 1010743 := bstep (se 1 (by rfl) ⟨758057, by rfl⟩ : syracuseStep 1010743 = 1516115) B1516115
theorem B3075137 : Blo 1008601 3075137 := bstep (se 2 (by rfl) ⟨1153176, by rfl⟩ : syracuseStep 3075137 = 2306353) B2306353
theorem B1010763 : Blo 1008601 1010763 := bstep (se 1 (by rfl) ⟨758072, by rfl⟩ : syracuseStep 1010763 = 1516145) B1516145
theorem B1010775 : Blo 1008601 1010775 := bstep (se 1 (by rfl) ⟨758081, by rfl⟩ : syracuseStep 1010775 = 1516163) B1516163
theorem B1010795 : Blo 1008601 1010795 := bstep (se 1 (by rfl) ⟨758096, by rfl⟩ : syracuseStep 1010795 = 1516193) B1516193
theorem B1010807 : Blo 1008601 1010807 := bstep (se 1 (by rfl) ⟨758105, by rfl⟩ : syracuseStep 1010807 = 1516211) B1516211
theorem B1010827 : Blo 1008601 1010827 := bstep (se 1 (by rfl) ⟨758120, by rfl⟩ : syracuseStep 1010827 = 1516241) B1516241
theorem B1010839 : Blo 1008601 1010839 := bstep (se 1 (by rfl) ⟨758129, by rfl⟩ : syracuseStep 1010839 = 1516259) B1516259
theorem B1436825 : Blo 1008601 1436825 := bstep (se 2 (by rfl) ⟨538809, by rfl⟩ : syracuseStep 1436825 = 1077619) B1077619
theorem B1010859 : Blo 1008601 1010859 := bstep (se 1 (by rfl) ⟨758144, by rfl⟩ : syracuseStep 1010859 = 1516289) B1516289
theorem B1010871 : Blo 1008601 1010871 := bstep (se 1 (by rfl) ⟨758153, by rfl⟩ : syracuseStep 1010871 = 1516307) B1516307
theorem B1010891 : Blo 1008601 1010891 := bstep (se 1 (by rfl) ⟨758168, by rfl⟩ : syracuseStep 1010891 = 1516337) B1516337
theorem B1010903 : Blo 1008601 1010903 := bstep (se 1 (by rfl) ⟨758177, by rfl⟩ : syracuseStep 1010903 = 1516355) B1516355
theorem B2878685 : Blo 1008601 2878685 := bstep (se 3 (by rfl) ⟨539753, by rfl⟩ : syracuseStep 2878685 = 1079507) B1079507
theorem B1010923 : Blo 1008601 1010923 := bstep (se 1 (by rfl) ⟨758192, by rfl⟩ : syracuseStep 1010923 = 1516385) B1516385
theorem B1010935 : Blo 1008601 1010935 := bstep (se 1 (by rfl) ⟨758201, by rfl⟩ : syracuseStep 1010935 = 1516403) B1516403
theorem B2157835 : Blo 1008601 2157835 := bstep (se 1 (by rfl) ⟨1618376, by rfl⟩ : syracuseStep 2157835 = 3236753) B3236753
theorem B1010955 : Blo 1008601 1010955 := bstep (se 1 (by rfl) ⟨758216, by rfl⟩ : syracuseStep 1010955 = 1516433) B1516433
theorem B1010967 : Blo 1008601 1010967 := bstep (se 1 (by rfl) ⟨758225, by rfl⟩ : syracuseStep 1010967 = 1516451) B1516451
theorem B1535257 : Blo 1008601 1535257 := bstep (se 2 (by rfl) ⟨575721, by rfl⟩ : syracuseStep 1535257 = 1151443) B1151443
theorem B1010987 : Blo 1008601 1010987 := bstep (se 1 (by rfl) ⟨758240, by rfl⟩ : syracuseStep 1010987 = 1516481) B1516481
theorem B1010999 : Blo 1008601 1010999 := bstep (se 1 (by rfl) ⟨758249, by rfl⟩ : syracuseStep 1010999 = 1516499) B1516499
theorem B1011019 : Blo 1008601 1011019 := bstep (se 1 (by rfl) ⟨758264, by rfl⟩ : syracuseStep 1011019 = 1516529) B1516529
theorem B1011031 : Blo 1008601 1011031 := bstep (se 1 (by rfl) ⟨758273, by rfl⟩ : syracuseStep 1011031 = 1516547) B1516547
theorem B5467493 : Blo 1008601 5467493 := bstep (se 4 (by rfl) ⟨512577, by rfl⟩ : syracuseStep 5467493 = 1025155) B1025155
theorem B1011051 : Blo 1008601 1011051 := bstep (se 1 (by rfl) ⟨758288, by rfl⟩ : syracuseStep 1011051 = 1516577) B1516577
theorem B1011063 : Blo 1008601 1011063 := bstep (se 1 (by rfl) ⟨758297, by rfl⟩ : syracuseStep 1011063 = 1516595) B1516595
theorem B1011083 : Blo 1008601 1011083 := bstep (se 1 (by rfl) ⟨758312, by rfl⟩ : syracuseStep 1011083 = 1516625) B1516625
theorem B1011095 : Blo 1008601 1011095 := bstep (se 1 (by rfl) ⟨758321, by rfl⟩ : syracuseStep 1011095 = 1516643) B1516643
theorem B1011115 : Blo 1008601 1011115 := bstep (se 1 (by rfl) ⟨758336, by rfl⟩ : syracuseStep 1011115 = 1516673) B1516673
theorem B1011127 : Blo 1008601 1011127 := bstep (se 1 (by rfl) ⟨758345, by rfl⟩ : syracuseStep 1011127 = 1516691) B1516691
theorem B1011147 : Blo 1008601 1011147 := bstep (se 1 (by rfl) ⟨758360, by rfl⟩ : syracuseStep 1011147 = 1516721) B1516721
theorem B1011159 : Blo 1008601 1011159 := bstep (se 1 (by rfl) ⟨758369, by rfl⟩ : syracuseStep 1011159 = 1516739) B1516739
theorem B1011179 : Blo 1008601 1011179 := bstep (se 1 (by rfl) ⟨758384, by rfl⟩ : syracuseStep 1011179 = 1516769) B1516769
theorem B1011191 : Blo 1008601 1011191 := bstep (se 1 (by rfl) ⟨758393, by rfl⟩ : syracuseStep 1011191 = 1516787) B1516787
theorem B2158091 : Blo 1008601 2158091 := bstep (se 1 (by rfl) ⟨1618568, by rfl⟩ : syracuseStep 2158091 = 3237137) B3237137
theorem B1011211 : Blo 1008601 1011211 := bstep (se 1 (by rfl) ⟨758408, by rfl⟩ : syracuseStep 1011211 = 1516817) B1516817
theorem B1011223 : Blo 1008601 1011223 := bstep (se 1 (by rfl) ⟨758417, by rfl⟩ : syracuseStep 1011223 = 1516835) B1516835
theorem B1011243 : Blo 1008601 1011243 := bstep (se 1 (by rfl) ⟨758432, by rfl⟩ : syracuseStep 1011243 = 1516865) B1516865
theorem B2879027 : Blo 1008601 2879027 := bstep (se 1 (by rfl) ⟨2159270, by rfl⟩ : syracuseStep 2879027 = 4318541) B4318541
theorem B1011255 : Blo 1008601 1011255 := bstep (se 1 (by rfl) ⟨758441, by rfl⟩ : syracuseStep 1011255 = 1516883) B1516883
theorem B1011275 : Blo 1008601 1011275 := bstep (se 1 (by rfl) ⟨758456, by rfl⟩ : syracuseStep 1011275 = 1516913) B1516913
theorem B1011287 : Blo 1008601 1011287 := bstep (se 1 (by rfl) ⟨758465, by rfl⟩ : syracuseStep 1011287 = 1516931) B1516931
theorem B1011307 : Blo 1008601 1011307 := bstep (se 1 (by rfl) ⟨758480, by rfl⟩ : syracuseStep 1011307 = 1516961) B1516961
theorem B1011319 : Blo 1008601 1011319 := bstep (se 1 (by rfl) ⟨758489, by rfl⟩ : syracuseStep 1011319 = 1516979) B1516979
theorem B1011339 : Blo 1008601 1011339 := bstep (se 1 (by rfl) ⟨758504, by rfl⟩ : syracuseStep 1011339 = 1517009) B1517009
theorem B3894929 : Blo 1008601 3894929 := bstep (se 2 (by rfl) ⟨1460598, by rfl⟩ : syracuseStep 3894929 = 2921197) B2921197
theorem B1011351 : Blo 1008601 1011351 := bstep (se 1 (by rfl) ⟨758513, by rfl⟩ : syracuseStep 1011351 = 1517027) B1517027
theorem B1011371 : Blo 1008601 1011371 := bstep (se 1 (by rfl) ⟨758528, by rfl⟩ : syracuseStep 1011371 = 1517057) B1517057
theorem B16412341 : Blo 1008601 16412341 := bstep (se 5 (by rfl) ⟨769328, by rfl⟩ : syracuseStep 16412341 = 1538657) B1538657
theorem B1011383 : Blo 1008601 1011383 := bstep (se 1 (by rfl) ⟨758537, by rfl⟩ : syracuseStep 1011383 = 1517075) B1517075
theorem B1011403 : Blo 1008601 1011403 := bstep (se 1 (by rfl) ⟨758552, by rfl⟩ : syracuseStep 1011403 = 1517105) B1517105
theorem B1011415 : Blo 1008601 1011415 := bstep (se 1 (by rfl) ⟨758561, by rfl⟩ : syracuseStep 1011415 = 1517123) B1517123
theorem B1011435 : Blo 1008601 1011435 := bstep (se 1 (by rfl) ⟨758576, by rfl⟩ : syracuseStep 1011435 = 1517153) B1517153
theorem B1011447 : Blo 1008601 1011447 := bstep (se 1 (by rfl) ⟨758585, by rfl⟩ : syracuseStep 1011447 = 1517171) B1517171
theorem B1011467 : Blo 1008601 1011467 := bstep (se 1 (by rfl) ⟨758600, by rfl⟩ : syracuseStep 1011467 = 1517201) B1517201
theorem B1437463 : Blo 1008601 1437463 := bstep (se 1 (by rfl) ⟨1078097, by rfl⟩ : syracuseStep 1437463 = 2156195) B2156195
theorem B1011479 : Blo 1008601 1011479 := bstep (se 1 (by rfl) ⟨758609, by rfl⟩ : syracuseStep 1011479 = 1517219) B1517219
theorem B1011499 : Blo 1008601 1011499 := bstep (se 1 (by rfl) ⟨758624, by rfl⟩ : syracuseStep 1011499 = 1517249) B1517249
theorem B1011511 : Blo 1008601 1011511 := bstep (se 1 (by rfl) ⟨758633, by rfl⟩ : syracuseStep 1011511 = 1517267) B1517267
theorem B1011531 : Blo 1008601 1011531 := bstep (se 1 (by rfl) ⟨758648, by rfl⟩ : syracuseStep 1011531 = 1517297) B1517297
theorem B1011543 : Blo 1008601 1011543 := bstep (se 1 (by rfl) ⟨758657, by rfl⟩ : syracuseStep 1011543 = 1517315) B1517315
theorem B1011563 : Blo 1008601 1011563 := bstep (se 1 (by rfl) ⟨758672, by rfl⟩ : syracuseStep 1011563 = 1517345) B1517345
theorem B1011575 : Blo 1008601 1011575 := bstep (se 1 (by rfl) ⟨758681, by rfl⟩ : syracuseStep 1011575 = 1517363) B1517363
theorem B1011595 : Blo 1008601 1011595 := bstep (se 1 (by rfl) ⟨758696, by rfl⟩ : syracuseStep 1011595 = 1517393) B1517393
theorem B1011607 : Blo 1008601 1011607 := bstep (se 1 (by rfl) ⟨758705, by rfl⟩ : syracuseStep 1011607 = 1517411) B1517411
theorem B1011627 : Blo 1008601 1011627 := bstep (se 1 (by rfl) ⟨758720, by rfl⟩ : syracuseStep 1011627 = 1517441) B1517441
theorem B1077175 : Blo 1008601 1077175 := bstep (se 1 (by rfl) ⟨807881, by rfl⟩ : syracuseStep 1077175 = 1615763) B1615763
theorem B1011639 : Blo 1008601 1011639 := bstep (se 1 (by rfl) ⟨758729, by rfl⟩ : syracuseStep 1011639 = 1517459) B1517459
theorem B1011659 : Blo 1008601 1011659 := bstep (se 1 (by rfl) ⟨758744, by rfl⟩ : syracuseStep 1011659 = 1517489) B1517489
theorem B1011671 : Blo 1008601 1011671 := bstep (se 1 (by rfl) ⟨758753, by rfl⟩ : syracuseStep 1011671 = 1517507) B1517507
theorem B1011691 : Blo 1008601 1011691 := bstep (se 1 (by rfl) ⟨758768, by rfl⟩ : syracuseStep 1011691 = 1517537) B1517537
theorem B1011703 : Blo 1008601 1011703 := bstep (se 1 (by rfl) ⟨758777, by rfl⟩ : syracuseStep 1011703 = 1517555) B1517555
theorem B1011723 : Blo 1008601 1011723 := bstep (se 1 (by rfl) ⟨758792, by rfl⟩ : syracuseStep 1011723 = 1517585) B1517585
theorem B1011735 : Blo 1008601 1011735 := bstep (se 1 (by rfl) ⟨758801, by rfl⟩ : syracuseStep 1011735 = 1517603) B1517603
theorem B1011755 : Blo 1008601 1011755 := bstep (se 1 (by rfl) ⟨758816, by rfl⟩ : syracuseStep 1011755 = 1517633) B1517633
theorem B1011767 : Blo 1008601 1011767 := bstep (se 1 (by rfl) ⟨758825, by rfl⟩ : syracuseStep 1011767 = 1517651) B1517651
theorem B1011787 : Blo 1008601 1011787 := bstep (se 1 (by rfl) ⟨758840, by rfl⟩ : syracuseStep 1011787 = 1517681) B1517681
theorem B1011799 : Blo 1008601 1011799 := bstep (se 1 (by rfl) ⟨758849, by rfl⟩ : syracuseStep 1011799 = 1517699) B1517699
theorem B1011819 : Blo 1008601 1011819 := bstep (se 1 (by rfl) ⟨758864, by rfl⟩ : syracuseStep 1011819 = 1517729) B1517729
theorem B1011831 : Blo 1008601 1011831 := bstep (se 1 (by rfl) ⟨758873, by rfl⟩ : syracuseStep 1011831 = 1517747) B1517747
theorem B1011851 : Blo 1008601 1011851 := bstep (se 1 (by rfl) ⟨758888, by rfl⟩ : syracuseStep 1011851 = 1517777) B1517777
theorem B1011863 : Blo 1008601 1011863 := bstep (se 1 (by rfl) ⟨758897, by rfl⟩ : syracuseStep 1011863 = 1517795) B1517795
theorem B1011883 : Blo 1008601 1011883 := bstep (se 1 (by rfl) ⟨758912, by rfl⟩ : syracuseStep 1011883 = 1517825) B1517825
theorem B1011895 : Blo 1008601 1011895 := bstep (se 1 (by rfl) ⟨758921, by rfl⟩ : syracuseStep 1011895 = 1517843) B1517843
theorem B1011915 : Blo 1008601 1011915 := bstep (se 1 (by rfl) ⟨758936, by rfl⟩ : syracuseStep 1011915 = 1517873) B1517873
theorem B1011927 : Blo 1008601 1011927 := bstep (se 1 (by rfl) ⟨758945, by rfl⟩ : syracuseStep 1011927 = 1517891) B1517891
theorem B1011947 : Blo 1008601 1011947 := bstep (se 1 (by rfl) ⟨758960, by rfl⟩ : syracuseStep 1011947 = 1517921) B1517921
theorem B1011959 : Blo 1008601 1011959 := bstep (se 1 (by rfl) ⟨758969, by rfl⟩ : syracuseStep 1011959 = 1517939) B1517939
theorem B1011979 : Blo 1008601 1011979 := bstep (se 1 (by rfl) ⟨758984, by rfl⟩ : syracuseStep 1011979 = 1517969) B1517969
theorem B1011991 : Blo 1008601 1011991 := bstep (se 1 (by rfl) ⟨758993, by rfl⟩ : syracuseStep 1011991 = 1517987) B1517987
theorem B1012011 : Blo 1008601 1012011 := bstep (se 1 (by rfl) ⟨759008, by rfl⟩ : syracuseStep 1012011 = 1518017) B1518017
theorem B1012023 : Blo 1008601 1012023 := bstep (se 1 (by rfl) ⟨759017, by rfl⟩ : syracuseStep 1012023 = 1518035) B1518035
theorem B1012043 : Blo 1008601 1012043 := bstep (se 1 (by rfl) ⟨759032, by rfl⟩ : syracuseStep 1012043 = 1518065) B1518065
theorem B1012055 : Blo 1008601 1012055 := bstep (se 1 (by rfl) ⟨759041, by rfl⟩ : syracuseStep 1012055 = 1518083) B1518083
theorem B3830105 : Blo 1008601 3830105 := bstep (se 2 (by rfl) ⟨1436289, by rfl⟩ : syracuseStep 3830105 = 2872579) B2872579
theorem B1012075 : Blo 1008601 1012075 := bstep (se 1 (by rfl) ⟨759056, by rfl⟩ : syracuseStep 1012075 = 1518113) B1518113
theorem B1012087 : Blo 1008601 1012087 := bstep (se 1 (by rfl) ⟨759065, by rfl⟩ : syracuseStep 1012087 = 1518131) B1518131
theorem B1012107 : Blo 1008601 1012107 := bstep (se 1 (by rfl) ⟨759080, by rfl⟩ : syracuseStep 1012107 = 1518161) B1518161
theorem B1012119 : Blo 1008601 1012119 := bstep (se 1 (by rfl) ⟨759089, by rfl⟩ : syracuseStep 1012119 = 1518179) B1518179
theorem B1012139 : Blo 1008601 1012139 := bstep (se 1 (by rfl) ⟨759104, by rfl⟩ : syracuseStep 1012139 = 1518209) B1518209
theorem B1012151 : Blo 1008601 1012151 := bstep (se 1 (by rfl) ⟨759113, by rfl⟩ : syracuseStep 1012151 = 1518227) B1518227
theorem B1012171 : Blo 1008601 1012171 := bstep (se 1 (by rfl) ⟨759128, by rfl⟩ : syracuseStep 1012171 = 1518257) B1518257
theorem B1012183 : Blo 1008601 1012183 := bstep (se 1 (by rfl) ⟨759137, by rfl⟩ : syracuseStep 1012183 = 1518275) B1518275
theorem B2159065 : Blo 1008601 2159065 := bstep (se 2 (by rfl) ⟨809649, by rfl⟩ : syracuseStep 2159065 = 1619299) B1619299
theorem B1012203 : Blo 1008601 1012203 := bstep (se 1 (by rfl) ⟨759152, by rfl⟩ : syracuseStep 1012203 = 1518305) B1518305
theorem B1012215 : Blo 1008601 1012215 := bstep (se 1 (by rfl) ⟨759161, by rfl⟩ : syracuseStep 1012215 = 1518323) B1518323
theorem B1012235 : Blo 1008601 1012235 := bstep (se 1 (by rfl) ⟨759176, by rfl⟩ : syracuseStep 1012235 = 1518353) B1518353
theorem B1012247 : Blo 1008601 1012247 := bstep (se 1 (by rfl) ⟨759185, by rfl⟩ : syracuseStep 1012247 = 1518371) B1518371
theorem B1012267 : Blo 1008601 1012267 := bstep (se 1 (by rfl) ⟨759200, by rfl⟩ : syracuseStep 1012267 = 1518401) B1518401
theorem B1012279 : Blo 1008601 1012279 := bstep (se 1 (by rfl) ⟨759209, by rfl⟩ : syracuseStep 1012279 = 1518419) B1518419
theorem B1438283 : Blo 1008601 1438283 := bstep (se 1 (by rfl) ⟨1078712, by rfl⟩ : syracuseStep 1438283 = 2157425) B2157425
theorem B1012299 : Blo 1008601 1012299 := bstep (se 1 (by rfl) ⟨759224, by rfl⟩ : syracuseStep 1012299 = 1518449) B1518449
theorem B1012311 : Blo 1008601 1012311 := bstep (se 1 (by rfl) ⟨759233, by rfl⟩ : syracuseStep 1012311 = 1518467) B1518467
theorem B1012331 : Blo 1008601 1012331 := bstep (se 1 (by rfl) ⟨759248, by rfl⟩ : syracuseStep 1012331 = 1518497) B1518497
theorem B2159219 : Blo 1008601 2159219 := bstep (se 1 (by rfl) ⟨1619414, by rfl⟩ : syracuseStep 2159219 = 3238829) B3238829
theorem B1012343 : Blo 1008601 1012343 := bstep (se 1 (by rfl) ⟨759257, by rfl⟩ : syracuseStep 1012343 = 1518515) B1518515
theorem B1012363 : Blo 1008601 1012363 := bstep (se 1 (by rfl) ⟨759272, by rfl⟩ : syracuseStep 1012363 = 1518545) B1518545
theorem B1012375 : Blo 1008601 1012375 := bstep (se 1 (by rfl) ⟨759281, by rfl⟩ : syracuseStep 1012375 = 1518563) B1518563
theorem B1012395 : Blo 1008601 1012395 := bstep (se 1 (by rfl) ⟨759296, by rfl⟩ : syracuseStep 1012395 = 1518593) B1518593
theorem B1012407 : Blo 1008601 1012407 := bstep (se 1 (by rfl) ⟨759305, by rfl⟩ : syracuseStep 1012407 = 1518611) B1518611
theorem B1012427 : Blo 1008601 1012427 := bstep (se 1 (by rfl) ⟨759320, by rfl⟩ : syracuseStep 1012427 = 1518641) B1518641
theorem B1012439 : Blo 1008601 1012439 := bstep (se 1 (by rfl) ⟨759329, by rfl⟩ : syracuseStep 1012439 = 1518659) B1518659
theorem B3076829 : Blo 1008601 3076829 := bstep (se 3 (by rfl) ⟨576905, by rfl⟩ : syracuseStep 3076829 = 1153811) B1153811
theorem B1077995 : Blo 1008601 1077995 := bstep (se 1 (by rfl) ⟨808496, by rfl⟩ : syracuseStep 1077995 = 1616993) B1616993
theorem B1012459 : Blo 1008601 1012459 := bstep (se 1 (by rfl) ⟨759344, by rfl⟩ : syracuseStep 1012459 = 1518689) B1518689
theorem B1012471 : Blo 1008601 1012471 := bstep (se 1 (by rfl) ⟨759353, by rfl⟩ : syracuseStep 1012471 = 1518707) B1518707
theorem B1012491 : Blo 1008601 1012491 := bstep (se 1 (by rfl) ⟨759368, by rfl⟩ : syracuseStep 1012491 = 1518737) B1518737
theorem B1012503 : Blo 1008601 1012503 := bstep (se 1 (by rfl) ⟨759377, by rfl⟩ : syracuseStep 1012503 = 1518755) B1518755
theorem B1012523 : Blo 1008601 1012523 := bstep (se 1 (by rfl) ⟨759392, by rfl⟩ : syracuseStep 1012523 = 1518785) B1518785
theorem B1012535 : Blo 1008601 1012535 := bstep (se 1 (by rfl) ⟨759401, by rfl⟩ : syracuseStep 1012535 = 1518803) B1518803
theorem B1012555 : Blo 1008601 1012555 := bstep (se 1 (by rfl) ⟨759416, by rfl⟩ : syracuseStep 1012555 = 1518833) B1518833
theorem B1012567 : Blo 1008601 1012567 := bstep (se 1 (by rfl) ⟨759425, by rfl⟩ : syracuseStep 1012567 = 1518851) B1518851
theorem B1012587 : Blo 1008601 1012587 := bstep (se 1 (by rfl) ⟨759440, by rfl⟩ : syracuseStep 1012587 = 1518881) B1518881
theorem B1012599 : Blo 1008601 1012599 := bstep (se 1 (by rfl) ⟨759449, by rfl⟩ : syracuseStep 1012599 = 1518899) B1518899
theorem B7664705 : Blo 1008601 7664705 := bstep (se 2 (by rfl) ⟨2874264, by rfl⟩ : syracuseStep 7664705 = 5748529) B5748529
theorem B6911041 : Blo 1008601 6911041 := bstep (se 2 (by rfl) ⟨2591640, by rfl⟩ : syracuseStep 6911041 = 5183281) B5183281
theorem B2159731 : Blo 1008601 2159731 := bstep (se 1 (by rfl) ⟨1619798, by rfl⟩ : syracuseStep 2159731 = 3239597) B3239597
theorem B3405131 : Blo 1008601 3405131 := bstep (se 1 (by rfl) ⟨2553848, by rfl⟩ : syracuseStep 3405131 = 5107697) B5107697
theorem B3241367 : Blo 1008601 3241367 := bstep (se 1 (by rfl) ⟨2431025, by rfl⟩ : syracuseStep 3241367 = 4862051) B4862051
theorem B9729553 : Blo 1008601 9729553 := bstep (se 2 (by rfl) ⟨3648582, by rfl⟩ : syracuseStep 9729553 = 7297165) B7297165
theorem B2881099 : Blo 1008601 2881099 := bstep (se 1 (by rfl) ⟨2160824, by rfl⟩ : syracuseStep 2881099 = 4321649) B4321649
theorem B3405401 : Blo 1008601 3405401 := bstep (se 2 (by rfl) ⟨1277025, by rfl⟩ : syracuseStep 3405401 = 2554051) B2554051
theorem B17233559 : Blo 1008601 17233559 := bstep (se 1 (by rfl) ⟨12925169, by rfl⟩ : syracuseStep 17233559 = 25850339) B25850339
theorem B2160407 : Blo 1008601 2160407 := bstep (se 1 (by rfl) ⟨1620305, by rfl⟩ : syracuseStep 2160407 = 3240611) B3240611
theorem B2160449 : Blo 1008601 2160449 := bstep (se 2 (by rfl) ⟨810168, by rfl⟩ : syracuseStep 2160449 = 1620337) B1620337
theorem B1079191 : Blo 1008601 1079191 := bstep (se 1 (by rfl) ⟨809393, by rfl⟩ : syracuseStep 1079191 = 1618787) B1618787
theorem B3831731 : Blo 1008601 3831731 := bstep (se 1 (by rfl) ⟨2873798, by rfl⟩ : syracuseStep 3831731 = 5747597) B5747597
theorem B3831745 : Blo 1008601 3831745 := bstep (se 2 (by rfl) ⟨1436904, by rfl⟩ : syracuseStep 3831745 = 2873809) B2873809
theorem B4323289 : Blo 1008601 4323289 := bstep (se 2 (by rfl) ⟨1621233, by rfl⟩ : syracuseStep 4323289 = 3242467) B3242467
theorem B2881601 : Blo 1008601 2881601 := bstep (se 2 (by rfl) ⟨1080600, by rfl⟩ : syracuseStep 2881601 = 2161201) B2161201
theorem B1702039 : Blo 1008601 1702039 := bstep (se 1 (by rfl) ⟨1276529, by rfl⟩ : syracuseStep 1702039 = 2553059) B2553059
theorem B3406103 : Blo 1008601 3406103 := bstep (se 1 (by rfl) ⟨2554577, by rfl⟩ : syracuseStep 3406103 = 5109155) B5109155
theorem B2554163 : Blo 1008601 2554163 := bstep (se 1 (by rfl) ⟨1915622, by rfl⟩ : syracuseStep 2554163 = 3831245) B3831245
theorem B2881943 : Blo 1008601 2881943 := bstep (se 1 (by rfl) ⟨2161457, by rfl⟩ : syracuseStep 2881943 = 4322915) B4322915
theorem B5110289 : Blo 1008601 5110289 := bstep (se 2 (by rfl) ⟨1916358, by rfl⟩ : syracuseStep 5110289 = 3832717) B3832717
theorem B4323905 : Blo 1008601 4323905 := bstep (se 2 (by rfl) ⟨1621464, by rfl⟩ : syracuseStep 4323905 = 3242929) B3242929
theorem B1276555 : Blo 1008601 1276555 := bstep (se 1 (by rfl) ⟨957416, by rfl⟩ : syracuseStep 1276555 = 1914833) B1914833
theorem B5110451 : Blo 1008601 5110451 := bstep (se 1 (by rfl) ⟨3832838, by rfl⟩ : syracuseStep 5110451 = 7665677) B7665677
theorem B1080011 : Blo 1008601 1080011 := bstep (se 1 (by rfl) ⟨810008, by rfl⟩ : syracuseStep 1080011 = 1620017) B1620017
theorem B3242699 : Blo 1008601 3242699 := bstep (se 1 (by rfl) ⟨2432024, by rfl⟩ : syracuseStep 3242699 = 4864049) B4864049
theorem B1702667 : Blo 1008601 1702667 := bstep (se 1 (by rfl) ⟨1277000, by rfl⟩ : syracuseStep 1702667 = 2554001) B2554001
theorem B3406643 : Blo 1008601 3406643 := bstep (se 1 (by rfl) ⟨2554982, by rfl⟩ : syracuseStep 3406643 = 5109965) B5109965
theorem B2554699 : Blo 1008601 2554699 := bstep (se 1 (by rfl) ⟨1916024, by rfl⟩ : syracuseStep 2554699 = 3832049) B3832049
theorem B1080139 : Blo 1008601 1080139 := bstep (se 1 (by rfl) ⟨810104, by rfl⟩ : syracuseStep 1080139 = 1620209) B1620209
theorem B1702795 : Blo 1008601 1702795 := bstep (se 1 (by rfl) ⟨1277096, by rfl⟩ : syracuseStep 1702795 = 2554193) B2554193
theorem B1276823 : Blo 1008601 1276823 := bstep (se 1 (by rfl) ⟨957617, by rfl⟩ : syracuseStep 1276823 = 1915235) B1915235
theorem B2554841 : Blo 1008601 2554841 := bstep (se 2 (by rfl) ⟨958065, by rfl⟩ : syracuseStep 2554841 = 1916131) B1916131
theorem B7666649 : Blo 1008601 7666649 := bstep (se 2 (by rfl) ⟨2874993, by rfl⟩ : syracuseStep 7666649 = 5749987) B5749987
theorem B1702937 : Blo 1008601 1702937 := bstep (se 2 (by rfl) ⟨638601, by rfl⟩ : syracuseStep 1702937 = 1277203) B1277203
theorem B3406913 : Blo 1008601 3406913 := bstep (se 2 (by rfl) ⟨1277592, by rfl⟩ : syracuseStep 3406913 = 2555185) B2555185
theorem B1703065 : Blo 1008601 1703065 := bstep (se 2 (by rfl) ⟨638649, by rfl⟩ : syracuseStep 1703065 = 1277299) B1277299
theorem B3636503 : Blo 1008601 3636503 := bstep (se 1 (by rfl) ⟨2727377, by rfl⟩ : syracuseStep 3636503 = 5454755) B5454755
theorem B3243287 : Blo 1008601 3243287 := bstep (se 1 (by rfl) ⟨2432465, by rfl⟩ : syracuseStep 3243287 = 4864931) B4864931
theorem B5766551 : Blo 1008601 5766551 := bstep (se 1 (by rfl) ⟨4324913, by rfl⟩ : syracuseStep 5766551 = 8649827) B8649827
theorem B1211927 : Blo 1008601 1211927 := bstep (se 1 (by rfl) ⟨908945, by rfl⟩ : syracuseStep 1211927 = 1817891) B1817891
theorem B1277527 : Blo 1008601 1277527 := bstep (se 1 (by rfl) ⟨958145, by rfl⟩ : syracuseStep 1277527 = 1916291) B1916291
theorem B3407453 : Blo 1008601 3407453 := bstep (se 3 (by rfl) ⟨638897, by rfl⟩ : syracuseStep 3407453 = 1277795) B1277795
theorem B5471837 : Blo 1008601 5471837 := bstep (se 3 (by rfl) ⟨1025969, by rfl⟩ : syracuseStep 5471837 = 2051939) B2051939
theorem B1703639 : Blo 1008601 1703639 := bstep (se 1 (by rfl) ⟨1277729, by rfl⟩ : syracuseStep 1703639 = 2555459) B2555459
theorem B2555671 : Blo 1008601 2555671 := bstep (se 1 (by rfl) ⟨1916753, by rfl⟩ : syracuseStep 2555671 = 3833507) B3833507
theorem B3243827 : Blo 1008601 3243827 := bstep (se 1 (by rfl) ⟨2432870, by rfl⟩ : syracuseStep 3243827 = 4865741) B4865741
theorem B3833675 : Blo 1008601 3833675 := bstep (se 1 (by rfl) ⟨2875256, by rfl⟩ : syracuseStep 3833675 = 5750513) B5750513
theorem B1703767 : Blo 1008601 1703767 := bstep (se 1 (by rfl) ⟨1277825, by rfl⟩ : syracuseStep 1703767 = 2555651) B2555651
theorem B3833689 : Blo 1008601 3833689 := bstep (se 2 (by rfl) ⟨1437633, by rfl⟩ : syracuseStep 3833689 = 2875267) B2875267
theorem B1704071 : Blo 1008601 1704071 := bstep (se 1 (by rfl) ⟨1278053, by rfl⟩ : syracuseStep 1704071 = 2556107) B2556107
theorem B2916553 : Blo 1008601 2916553 := bstep (se 2 (by rfl) ⟨1093707, by rfl⟩ : syracuseStep 2916553 = 2187415) B2187415
theorem B4849901 : Blo 1008601 4849901 := bstep (se 3 (by rfl) ⟨909356, by rfl⟩ : syracuseStep 4849901 = 1818713) B1818713
theorem B2457899 : Blo 1008601 2457899 := bstep (se 1 (by rfl) ⟨1843424, by rfl⟩ : syracuseStep 2457899 = 3686849) B3686849
theorem B3408263 : Blo 1008601 3408263 := bstep (se 1 (by rfl) ⟨2556197, by rfl⟩ : syracuseStep 3408263 = 5112395) B5112395
theorem B2458009 : Blo 1008601 2458009 := bstep (se 2 (by rfl) ⟨921753, by rfl⟩ : syracuseStep 2458009 = 1843507) B1843507
theorem B2556431 : Blo 1008601 2556431 := bstep (se 1 (by rfl) ⟨1917323, by rfl⟩ : syracuseStep 2556431 = 3834647) B3834647
theorem B5472791 : Blo 1008601 5472791 := bstep (se 1 (by rfl) ⟨4104593, by rfl⟩ : syracuseStep 5472791 = 8209187) B8209187
theorem B5112557 : Blo 1008601 5112557 := bstep (se 3 (by rfl) ⟨958604, by rfl⟩ : syracuseStep 5112557 = 1917209) B1917209
theorem B3408641 : Blo 1008601 3408641 := bstep (se 2 (by rfl) ⟨1278240, by rfl⟩ : syracuseStep 3408641 = 2556481) B2556481
theorem B1704719 : Blo 1008601 1704719 := bstep (se 1 (by rfl) ⟨1278539, by rfl⟩ : syracuseStep 1704719 = 2557079) B2557079
theorem B5833619 : Blo 1008601 5833619 := bstep (se 1 (by rfl) ⟨4375214, by rfl⟩ : syracuseStep 5833619 = 8750429) B8750429
theorem B1279147 : Blo 1008601 1279147 := bstep (se 1 (by rfl) ⟨959360, by rfl⟩ : syracuseStep 1279147 = 1918721) B1918721
theorem B8619209 : Blo 1008601 8619209 := bstep (se 2 (by rfl) ⟨3232203, by rfl⟩ : syracuseStep 8619209 = 6464407) B6464407
theorem B2557129 : Blo 1008601 2557129 := bstep (se 2 (by rfl) ⟨958923, by rfl⟩ : syracuseStep 2557129 = 1917847) B1917847
theorem B6325541 : Blo 1008601 6325541 := bstep (se 4 (by rfl) ⟨593019, by rfl⟩ : syracuseStep 6325541 = 1186039) B1186039
theorem B1705259 : Blo 1008601 1705259 := bstep (se 1 (by rfl) ⟨1278944, by rfl⟩ : syracuseStep 1705259 = 2557889) B2557889
theorem B2557271 : Blo 1008601 2557271 := bstep (se 1 (by rfl) ⟨1917953, by rfl⟩ : syracuseStep 2557271 = 3835907) B3835907
theorem B5113367 : Blo 1008601 5113367 := bstep (se 1 (by rfl) ⟨3835025, by rfl⟩ : syracuseStep 5113367 = 7670051) B7670051
theorem B3835421 : Blo 1008601 3835421 := bstep (se 3 (by rfl) ⟨719141, by rfl⟩ : syracuseStep 3835421 = 1438283) B1438283
theorem B3409451 : Blo 1008601 3409451 := bstep (se 1 (by rfl) ⟨2557088, by rfl⟩ : syracuseStep 3409451 = 5114177) B5114177
theorem B1705657 : Blo 1008601 1705657 := bstep (se 2 (by rfl) ⟨639621, by rfl⟩ : syracuseStep 1705657 = 1279243) B1279243
theorem B1280119 : Blo 1008601 1280119 := bstep (se 1 (by rfl) ⟨960089, by rfl⟩ : syracuseStep 1280119 = 1920179) B1920179
theorem B3836105 : Blo 1008601 3836105 := bstep (se 2 (by rfl) ⟨1438539, by rfl⟩ : syracuseStep 3836105 = 2877079) B2877079
theorem B1706359 : Blo 1008601 1706359 := bstep (se 1 (by rfl) ⟨1279769, by rfl⟩ : syracuseStep 1706359 = 2559539) B2559539
theorem B1280443 : Blo 1008601 1280443 := bstep (se 1 (by rfl) ⟨960332, by rfl⟩ : syracuseStep 1280443 = 1920665) B1920665
theorem B1706555 : Blo 1008601 1706555 := bstep (se 1 (by rfl) ⟨1279916, by rfl⟩ : syracuseStep 1706555 = 2559833) B2559833
theorem B2427545 : Blo 1008601 2427545 := bstep (se 2 (by rfl) ⟨910329, by rfl⟩ : syracuseStep 2427545 = 1820659) B1820659
theorem B3640079 : Blo 1008601 3640079 := bstep (se 1 (by rfl) ⟨2730059, by rfl⟩ : syracuseStep 3640079 = 5460119) B5460119
theorem B3410747 : Blo 1008601 3410747 := bstep (se 1 (by rfl) ⟨2558060, by rfl⟩ : syracuseStep 3410747 = 5116121) B5116121
theorem B1641275 : Blo 1008601 1641275 := bstep (se 1 (by rfl) ⟨1230956, by rfl⟩ : syracuseStep 1641275 = 2461913) B2461913
theorem B33164147 : Blo 1008601 33164147 := bstep (se 1 (by rfl) ⟨24873110, by rfl⟩ : syracuseStep 33164147 = 49746221) B49746221
theorem B1706953 : Blo 1008601 1706953 := bstep (se 2 (by rfl) ⟨640107, by rfl⟩ : syracuseStep 1706953 = 1280215) B1280215
theorem B12946493 : Blo 1008601 12946493 := bstep (se 3 (by rfl) ⟨2427467, by rfl⟩ : syracuseStep 12946493 = 4854935) B4854935
theorem B3411233 : Blo 1008601 3411233 := bstep (se 2 (by rfl) ⟨1279212, by rfl⟩ : syracuseStep 3411233 = 2558425) B2558425
theorem B2559347 : Blo 1008601 2559347 := bstep (se 1 (by rfl) ⟨1919510, by rfl⟩ : syracuseStep 2559347 = 3839021) B3839021
theorem B1281415 : Blo 1008601 1281415 := bstep (se 1 (by rfl) ⟨961061, by rfl⟩ : syracuseStep 1281415 = 1922123) B1922123
theorem B4918681 : Blo 1008601 4918681 := bstep (se 2 (by rfl) ⟨1844505, by rfl⟩ : syracuseStep 4918681 = 3689011) B3689011
theorem B1707655 : Blo 1008601 1707655 := bstep (se 1 (by rfl) ⟨1280741, by rfl⟩ : syracuseStep 1707655 = 2561483) B2561483
theorem B3411827 : Blo 1008601 3411827 := bstep (se 1 (by rfl) ⟨2558870, by rfl⟩ : syracuseStep 3411827 = 5117741) B5117741
theorem B2559863 : Blo 1008601 2559863 := bstep (se 1 (by rfl) ⟨1919897, by rfl⟩ : syracuseStep 2559863 = 3839795) B3839795
theorem B3837881 : Blo 1008601 3837881 := bstep (se 2 (by rfl) ⟨1439205, by rfl⟩ : syracuseStep 3837881 = 2878411) B2878411
theorem B1708303 : Blo 1008601 1708303 := bstep (se 1 (by rfl) ⟨1281227, by rfl⟩ : syracuseStep 1708303 = 2562455) B2562455
theorem B8622521 : Blo 1008601 8622521 := bstep (se 2 (by rfl) ⟨3233445, by rfl⟩ : syracuseStep 8622521 = 6466891) B6466891
theorem B5116445 : Blo 1008601 5116445 := bstep (se 3 (by rfl) ⟨959333, by rfl⟩ : syracuseStep 5116445 = 1918667) B1918667
theorem B29561537 : Blo 1008601 29561537 := bstep (se 2 (by rfl) ⟨11085576, by rfl⟩ : syracuseStep 29561537 = 22171153) B22171153
theorem B10523429 : Blo 1008601 10523429 := bstep (se 4 (by rfl) ⟨986571, by rfl⟩ : syracuseStep 10523429 = 1973143) B1973143
theorem B2560855 : Blo 1008601 2560855 := bstep (se 1 (by rfl) ⟨1920641, by rfl⟩ : syracuseStep 2560855 = 3841283) B3841283
theorem B4920323 : Blo 1008601 4920323 := bstep (se 1 (by rfl) ⟨3690242, by rfl⟩ : syracuseStep 4920323 = 7380485) B7380485
theorem B5116931 : Blo 1008601 5116931 := bstep (se 1 (by rfl) ⟨3837698, by rfl⟩ : syracuseStep 5116931 = 7675397) B7675397
theorem B2561159 : Blo 1008601 2561159 := bstep (se 1 (by rfl) ⟨1920869, by rfl⟩ : syracuseStep 2561159 = 3841739) B3841739
theorem B2561291 : Blo 1008601 2561291 := bstep (se 1 (by rfl) ⟨1920968, by rfl⟩ : syracuseStep 2561291 = 3841937) B3841937
theorem B1512905 : Blo 1008601 1512905 := bstep (se 2 (by rfl) ⟨567339, by rfl⟩ : syracuseStep 1512905 = 1134679) B1134679
theorem B4855243 : Blo 1008601 4855243 := bstep (se 1 (by rfl) ⟨3641432, by rfl⟩ : syracuseStep 4855243 = 7282865) B7282865
theorem B1513019 : Blo 1008601 1513019 := bstep (se 1 (by rfl) ⟨1134764, by rfl⟩ : syracuseStep 1513019 = 2269529) B2269529
theorem B1513079 : Blo 1008601 1513079 := bstep (se 1 (by rfl) ⟨1134809, by rfl⟩ : syracuseStep 1513079 = 2269619) B2269619
theorem B1513103 : Blo 1008601 1513103 := bstep (se 1 (by rfl) ⟨1134827, by rfl⟩ : syracuseStep 1513103 = 2269655) B2269655
theorem B1513145 : Blo 1008601 1513145 := bstep (se 2 (by rfl) ⟨567429, by rfl⟩ : syracuseStep 1513145 = 1134859) B1134859
theorem B1513223 : Blo 1008601 1513223 := bstep (se 1 (by rfl) ⟨1134917, by rfl⟩ : syracuseStep 1513223 = 2269835) B2269835
theorem B2561807 : Blo 1008601 2561807 := bstep (se 1 (by rfl) ⟨1921355, by rfl⟩ : syracuseStep 2561807 = 3842711) B3842711
theorem B1513259 : Blo 1008601 1513259 := bstep (se 1 (by rfl) ⟨1134944, by rfl⟩ : syracuseStep 1513259 = 2269889) B2269889
theorem B1513289 : Blo 1008601 1513289 := bstep (se 2 (by rfl) ⟨567483, by rfl⟩ : syracuseStep 1513289 = 1134967) B1134967
theorem B2561939 : Blo 1008601 2561939 := bstep (se 1 (by rfl) ⟨1921454, by rfl⟩ : syracuseStep 2561939 = 3842909) B3842909
theorem B1513403 : Blo 1008601 1513403 := bstep (se 1 (by rfl) ⟨1135052, by rfl⟩ : syracuseStep 1513403 = 2270105) B2270105
theorem B1513463 : Blo 1008601 1513463 := bstep (se 1 (by rfl) ⟨1135097, by rfl⟩ : syracuseStep 1513463 = 2270195) B2270195
theorem B10917899 : Blo 1008601 10917899 := bstep (se 1 (by rfl) ⟨8188424, by rfl⟩ : syracuseStep 10917899 = 16376849) B16376849
theorem B1513487 : Blo 1008601 1513487 := bstep (se 1 (by rfl) ⟨1135115, by rfl⟩ : syracuseStep 1513487 = 2270231) B2270231
theorem B1513529 : Blo 1008601 1513529 := bstep (se 2 (by rfl) ⟨567573, by rfl⟩ : syracuseStep 1513529 = 1135147) B1135147
theorem B3119219 : Blo 1008601 3119219 := bstep (se 1 (by rfl) ⟨2339414, by rfl⟩ : syracuseStep 3119219 = 4678829) B4678829
theorem B1513607 : Blo 1008601 1513607 := bstep (se 1 (by rfl) ⟨1135205, by rfl⟩ : syracuseStep 1513607 = 2270411) B2270411
theorem B1513643 : Blo 1008601 1513643 := bstep (se 1 (by rfl) ⟨1135232, by rfl⟩ : syracuseStep 1513643 = 2270465) B2270465
theorem B1513673 : Blo 1008601 1513673 := bstep (se 2 (by rfl) ⟨567627, by rfl⟩ : syracuseStep 1513673 = 1135255) B1135255
theorem B1513787 : Blo 1008601 1513787 := bstep (se 1 (by rfl) ⟨1135340, by rfl⟩ : syracuseStep 1513787 = 2270681) B2270681
theorem B1513847 : Blo 1008601 1513847 := bstep (se 1 (by rfl) ⟨1135385, by rfl⟩ : syracuseStep 1513847 = 2270771) B2270771
theorem B1513871 : Blo 1008601 1513871 := bstep (se 1 (by rfl) ⟨1135403, by rfl⟩ : syracuseStep 1513871 = 2270807) B2270807
theorem B3414419 : Blo 1008601 3414419 := bstep (se 1 (by rfl) ⟨2560814, by rfl⟩ : syracuseStep 3414419 = 5121629) B5121629
theorem B1513913 : Blo 1008601 1513913 := bstep (se 2 (by rfl) ⟨567717, by rfl⟩ : syracuseStep 1513913 = 1135435) B1135435
theorem B1513991 : Blo 1008601 1513991 := bstep (se 1 (by rfl) ⟨1135493, by rfl⟩ : syracuseStep 1513991 = 2270987) B2270987
theorem B1514027 : Blo 1008601 1514027 := bstep (se 1 (by rfl) ⟨1135520, by rfl⟩ : syracuseStep 1514027 = 2271041) B2271041
theorem B9706027 : Blo 1008601 9706027 := bstep (se 1 (by rfl) ⟨7279520, by rfl⟩ : syracuseStep 9706027 = 14559041) B14559041
theorem B1514057 : Blo 1008601 1514057 := bstep (se 2 (by rfl) ⟨567771, by rfl⟩ : syracuseStep 1514057 = 1135543) B1135543
theorem B5118551 : Blo 1008601 5118551 := bstep (se 1 (by rfl) ⟨3838913, by rfl⟩ : syracuseStep 5118551 = 7677827) B7677827
theorem B1514171 : Blo 1008601 1514171 := bstep (se 1 (by rfl) ⟨1135628, by rfl⟩ : syracuseStep 1514171 = 2271257) B2271257
theorem B1514231 : Blo 1008601 1514231 := bstep (se 1 (by rfl) ⟨1135673, by rfl⟩ : syracuseStep 1514231 = 2271347) B2271347
theorem B9214721 : Blo 1008601 9214721 := bstep (se 2 (by rfl) ⟨3455520, by rfl⟩ : syracuseStep 9214721 = 6911041) B6911041
theorem B2333455 : Blo 1008601 2333455 := bstep (se 1 (by rfl) ⟨1750091, by rfl⟩ : syracuseStep 2333455 = 3500183) B3500183
theorem B1514255 : Blo 1008601 1514255 := bstep (se 1 (by rfl) ⟨1135691, by rfl⟩ : syracuseStep 1514255 = 2271383) B2271383
theorem B1514297 : Blo 1008601 1514297 := bstep (se 2 (by rfl) ⟨567861, by rfl⟩ : syracuseStep 1514297 = 1135723) B1135723
theorem B7773043 : Blo 1008601 7773043 := bstep (se 1 (by rfl) ⟨5829782, by rfl⟩ : syracuseStep 7773043 = 11659565) B11659565
theorem B1514375 : Blo 1008601 1514375 := bstep (se 1 (by rfl) ⟨1135781, by rfl⟩ : syracuseStep 1514375 = 2271563) B2271563
theorem B1514411 : Blo 1008601 1514411 := bstep (se 1 (by rfl) ⟨1135808, by rfl⟩ : syracuseStep 1514411 = 2271617) B2271617
theorem B1514441 : Blo 1008601 1514441 := bstep (se 2 (by rfl) ⟨567915, by rfl⟩ : syracuseStep 1514441 = 1135831) B1135831
theorem B2563073 : Blo 1008601 2563073 := bstep (se 2 (by rfl) ⟨961152, by rfl⟩ : syracuseStep 2563073 = 1922305) B1922305
theorem B1514555 : Blo 1008601 1514555 := bstep (se 1 (by rfl) ⟨1135916, by rfl⟩ : syracuseStep 1514555 = 2271833) B2271833
theorem B5119037 : Blo 1008601 5119037 := bstep (se 3 (by rfl) ⟨959819, by rfl⟩ : syracuseStep 5119037 = 1919639) B1919639
theorem B1514615 : Blo 1008601 1514615 := bstep (se 1 (by rfl) ⟨1135961, by rfl⟩ : syracuseStep 1514615 = 2271923) B2271923
theorem B1514639 : Blo 1008601 1514639 := bstep (se 1 (by rfl) ⟨1135979, by rfl⟩ : syracuseStep 1514639 = 2271959) B2271959
theorem B1514681 : Blo 1008601 1514681 := bstep (se 2 (by rfl) ⟨568005, by rfl⟩ : syracuseStep 1514681 = 1136011) B1136011
theorem B1514759 : Blo 1008601 1514759 := bstep (se 1 (by rfl) ⟨1136069, by rfl⟩ : syracuseStep 1514759 = 2272139) B2272139
theorem B1514795 : Blo 1008601 1514795 := bstep (se 1 (by rfl) ⟨1136096, by rfl⟩ : syracuseStep 1514795 = 2272193) B2272193
theorem B1514825 : Blo 1008601 1514825 := bstep (se 2 (by rfl) ⟨568059, by rfl⟩ : syracuseStep 1514825 = 1136119) B1136119
theorem B2661751 : Blo 1008601 2661751 := bstep (se 1 (by rfl) ⟨1996313, by rfl⟩ : syracuseStep 2661751 = 3992627) B3992627
theorem B3841465 : Blo 1008601 3841465 := bstep (se 2 (by rfl) ⟨1440549, by rfl⟩ : syracuseStep 3841465 = 2881099) B2881099
theorem B1514939 : Blo 1008601 1514939 := bstep (se 1 (by rfl) ⟨1136204, by rfl⟩ : syracuseStep 1514939 = 2272409) B2272409
theorem B1514999 : Blo 1008601 1514999 := bstep (se 1 (by rfl) ⟨1136249, by rfl⟩ : syracuseStep 1514999 = 2272499) B2272499
theorem B1515023 : Blo 1008601 1515023 := bstep (se 1 (by rfl) ⟨1136267, by rfl⟩ : syracuseStep 1515023 = 2272535) B2272535
theorem B1515065 : Blo 1008601 1515065 := bstep (se 2 (by rfl) ⟨568149, by rfl⟩ : syracuseStep 1515065 = 1136299) B1136299
theorem B3644995 : Blo 1008601 3644995 := bstep (se 1 (by rfl) ⟨2733746, by rfl⟩ : syracuseStep 3644995 = 5467493) B5467493
theorem B1515143 : Blo 1008601 1515143 := bstep (se 1 (by rfl) ⟨1136357, by rfl⟩ : syracuseStep 1515143 = 2272715) B2272715
theorem B1515179 : Blo 1008601 1515179 := bstep (se 1 (by rfl) ⟨1136384, by rfl⟩ : syracuseStep 1515179 = 2272769) B2272769
theorem B1515209 : Blo 1008601 1515209 := bstep (se 2 (by rfl) ⟨568203, by rfl⟩ : syracuseStep 1515209 = 1136407) B1136407
theorem B2596619 : Blo 1008601 2596619 := bstep (se 1 (by rfl) ⟨1947464, by rfl⟩ : syracuseStep 2596619 = 3894929) B3894929
theorem B3415823 : Blo 1008601 3415823 := bstep (se 1 (by rfl) ⟨2561867, by rfl⟩ : syracuseStep 3415823 = 5123735) B5123735
theorem B84156205 : Blo 1008601 84156205 := bstep (se 3 (by rfl) ⟨15779288, by rfl⟩ : syracuseStep 84156205 = 31558577) B31558577
theorem B1515323 : Blo 1008601 1515323 := bstep (se 1 (by rfl) ⟨1136492, by rfl⟩ : syracuseStep 1515323 = 2272985) B2272985
theorem B1515383 : Blo 1008601 1515383 := bstep (se 1 (by rfl) ⟨1136537, by rfl⟩ : syracuseStep 1515383 = 2273075) B2273075
theorem B1515407 : Blo 1008601 1515407 := bstep (se 1 (by rfl) ⟨1136555, by rfl⟩ : syracuseStep 1515407 = 2273111) B2273111
theorem B1515449 : Blo 1008601 1515449 := bstep (se 2 (by rfl) ⟨568293, by rfl⟩ : syracuseStep 1515449 = 1136587) B1136587
theorem B1515527 : Blo 1008601 1515527 := bstep (se 1 (by rfl) ⟨1136645, by rfl⟩ : syracuseStep 1515527 = 2273291) B2273291
theorem B3416093 : Blo 1008601 3416093 := bstep (se 3 (by rfl) ⟨640517, by rfl⟩ : syracuseStep 3416093 = 1281035) B1281035
theorem B1515563 : Blo 1008601 1515563 := bstep (se 1 (by rfl) ⟨1136672, by rfl⟩ : syracuseStep 1515563 = 2273345) B2273345
theorem B1515593 : Blo 1008601 1515593 := bstep (se 2 (by rfl) ⟨568347, by rfl⟩ : syracuseStep 1515593 = 1136695) B1136695
theorem B1515707 : Blo 1008601 1515707 := bstep (se 1 (by rfl) ⟨1136780, by rfl⟩ : syracuseStep 1515707 = 2273561) B2273561
theorem B2269385 : Blo 1008601 2269385 := bstep (se 2 (by rfl) ⟨851019, by rfl⟩ : syracuseStep 2269385 = 1702039) B1702039
theorem B1515767 : Blo 1008601 1515767 := bstep (se 1 (by rfl) ⟨1136825, by rfl⟩ : syracuseStep 1515767 = 2273651) B2273651
theorem B1515791 : Blo 1008601 1515791 := bstep (se 1 (by rfl) ⟨1136843, by rfl⟩ : syracuseStep 1515791 = 2273687) B2273687
theorem B1515833 : Blo 1008601 1515833 := bstep (se 2 (by rfl) ⟨568437, by rfl⟩ : syracuseStep 1515833 = 1136875) B1136875
theorem B1515911 : Blo 1008601 1515911 := bstep (se 1 (by rfl) ⟨1136933, by rfl⟩ : syracuseStep 1515911 = 2273867) B2273867
theorem B1515947 : Blo 1008601 1515947 := bstep (se 1 (by rfl) ⟨1136960, by rfl⟩ : syracuseStep 1515947 = 2273921) B2273921
theorem B1515977 : Blo 1008601 1515977 := bstep (se 2 (by rfl) ⟨568491, by rfl⟩ : syracuseStep 1515977 = 1136983) B1136983
theorem B7676369 : Blo 1008601 7676369 := bstep (se 2 (by rfl) ⟨2878638, by rfl⟩ : syracuseStep 7676369 = 5757277) B5757277
theorem B2957867 : Blo 1008601 2957867 := bstep (se 1 (by rfl) ⟨2218400, by rfl⟩ : syracuseStep 2957867 = 4436801) B4436801
theorem B1516091 : Blo 1008601 1516091 := bstep (se 1 (by rfl) ⟨1137068, by rfl⟩ : syracuseStep 1516091 = 2274137) B2274137
theorem B1516151 : Blo 1008601 1516151 := bstep (se 1 (by rfl) ⟨1137113, by rfl⟩ : syracuseStep 1516151 = 2274227) B2274227
theorem B1516175 : Blo 1008601 1516175 := bstep (se 1 (by rfl) ⟨1137131, by rfl⟩ : syracuseStep 1516175 = 2274263) B2274263
theorem B1516217 : Blo 1008601 1516217 := bstep (se 2 (by rfl) ⟨568581, by rfl⟩ : syracuseStep 1516217 = 1137163) B1137163
theorem B1516295 : Blo 1008601 1516295 := bstep (se 1 (by rfl) ⟨1137221, by rfl⟩ : syracuseStep 1516295 = 2274443) B2274443
theorem B1516331 : Blo 1008601 1516331 := bstep (se 1 (by rfl) ⟨1137248, by rfl⟩ : syracuseStep 1516331 = 2274497) B2274497
theorem B5120819 : Blo 1008601 5120819 := bstep (se 1 (by rfl) ⟨3840614, by rfl⟩ : syracuseStep 5120819 = 7681229) B7681229
theorem B1516361 : Blo 1008601 1516361 := bstep (se 2 (by rfl) ⟨568635, by rfl⟩ : syracuseStep 1516361 = 1137271) B1137271
theorem B3285875 : Blo 1008601 3285875 := bstep (se 1 (by rfl) ⟨2464406, by rfl⟩ : syracuseStep 3285875 = 4928813) B4928813
theorem B2270087 : Blo 1008601 2270087 := bstep (se 1 (by rfl) ⟨1702565, by rfl⟩ : syracuseStep 2270087 = 3405131) B3405131
theorem B1516475 : Blo 1008601 1516475 := bstep (se 1 (by rfl) ⟨1137356, by rfl⟩ : syracuseStep 1516475 = 2274713) B2274713
theorem B1516535 : Blo 1008601 1516535 := bstep (se 1 (by rfl) ⟨1137401, by rfl⟩ : syracuseStep 1516535 = 2274803) B2274803
theorem B1516559 : Blo 1008601 1516559 := bstep (se 1 (by rfl) ⟨1137419, by rfl⟩ : syracuseStep 1516559 = 2274839) B2274839
theorem B1516601 : Blo 1008601 1516601 := bstep (se 2 (by rfl) ⟨568725, by rfl⟩ : syracuseStep 1516601 = 1137451) B1137451
theorem B2270267 : Blo 1008601 2270267 := bstep (se 1 (by rfl) ⟨1702700, by rfl⟩ : syracuseStep 2270267 = 3405401) B3405401
theorem B5121143 : Blo 1008601 5121143 := bstep (se 1 (by rfl) ⟨3840857, by rfl⟩ : syracuseStep 5121143 = 7681715) B7681715
theorem B1516679 : Blo 1008601 1516679 := bstep (se 1 (by rfl) ⟨1137509, by rfl⟩ : syracuseStep 1516679 = 2275019) B2275019
theorem B1516715 : Blo 1008601 1516715 := bstep (se 1 (by rfl) ⟨1137536, by rfl⟩ : syracuseStep 1516715 = 2275073) B2275073
theorem B2270393 : Blo 1008601 2270393 := bstep (se 2 (by rfl) ⟨851397, by rfl⟩ : syracuseStep 2270393 = 1702795) B1702795
theorem B1516745 : Blo 1008601 1516745 := bstep (se 2 (by rfl) ⟨568779, by rfl⟩ : syracuseStep 1516745 = 1137559) B1137559
theorem B1516859 : Blo 1008601 1516859 := bstep (se 1 (by rfl) ⟨1137644, by rfl⟩ : syracuseStep 1516859 = 2275289) B2275289
theorem B1516919 : Blo 1008601 1516919 := bstep (se 1 (by rfl) ⟨1137689, by rfl⟩ : syracuseStep 1516919 = 2275379) B2275379
theorem B1516943 : Blo 1008601 1516943 := bstep (se 1 (by rfl) ⟨1137707, by rfl⟩ : syracuseStep 1516943 = 2275415) B2275415
theorem B2729369 : Blo 1008601 2729369 := bstep (se 2 (by rfl) ⟨1023513, by rfl⟩ : syracuseStep 2729369 = 2047027) B2047027
theorem B3417497 : Blo 1008601 3417497 := bstep (se 2 (by rfl) ⟨1281561, by rfl⟩ : syracuseStep 3417497 = 2563123) B2563123
theorem B1516985 : Blo 1008601 1516985 := bstep (se 2 (by rfl) ⟨568869, by rfl⟩ : syracuseStep 1516985 = 1137739) B1137739
theorem B11085265 : Blo 1008601 11085265 := bstep (se 2 (by rfl) ⟨4156974, by rfl⟩ : syracuseStep 11085265 = 8313949) B8313949
theorem B1517063 : Blo 1008601 1517063 := bstep (se 1 (by rfl) ⟨1137797, by rfl⟩ : syracuseStep 1517063 = 2275595) B2275595
theorem B2270735 : Blo 1008601 2270735 := bstep (se 1 (by rfl) ⟨1703051, by rfl⟩ : syracuseStep 2270735 = 3406103) B3406103
theorem B2270753 : Blo 1008601 2270753 := bstep (se 2 (by rfl) ⟨851532, by rfl⟩ : syracuseStep 2270753 = 1703065) B1703065
theorem B1517099 : Blo 1008601 1517099 := bstep (se 1 (by rfl) ⟨1137824, by rfl⟩ : syracuseStep 1517099 = 2275649) B2275649
theorem B1517129 : Blo 1008601 1517129 := bstep (se 2 (by rfl) ⟨568923, by rfl⟩ : syracuseStep 1517129 = 1137847) B1137847
theorem B1517243 : Blo 1008601 1517243 := bstep (se 1 (by rfl) ⟨1137932, by rfl⟩ : syracuseStep 1517243 = 2275865) B2275865
theorem B1517303 : Blo 1008601 1517303 := bstep (se 1 (by rfl) ⟨1137977, by rfl⟩ : syracuseStep 1517303 = 2275955) B2275955
theorem B1517327 : Blo 1008601 1517327 := bstep (se 1 (by rfl) ⟨1137995, by rfl⟩ : syracuseStep 1517327 = 2275991) B2275991
theorem B1517369 : Blo 1008601 1517369 := bstep (se 2 (by rfl) ⟨569013, by rfl⟩ : syracuseStep 1517369 = 1138027) B1138027
theorem B2271095 : Blo 1008601 2271095 := bstep (se 1 (by rfl) ⟨1703321, by rfl⟩ : syracuseStep 2271095 = 3406643) B3406643
theorem B1517447 : Blo 1008601 1517447 := bstep (se 1 (by rfl) ⟨1138085, by rfl⟩ : syracuseStep 1517447 = 2276171) B2276171
theorem B1517483 : Blo 1008601 1517483 := bstep (se 1 (by rfl) ⟨1138112, by rfl⟩ : syracuseStep 1517483 = 2276225) B2276225
theorem B1517513 : Blo 1008601 1517513 := bstep (se 2 (by rfl) ⟨569067, by rfl⟩ : syracuseStep 1517513 = 1138135) B1138135
theorem B2271275 : Blo 1008601 2271275 := bstep (se 1 (by rfl) ⟨1703456, by rfl⟩ : syracuseStep 2271275 = 3406913) B3406913
theorem B1517627 : Blo 1008601 1517627 := bstep (se 1 (by rfl) ⟨1138220, by rfl⟩ : syracuseStep 1517627 = 2276441) B2276441
theorem B5122115 : Blo 1008601 5122115 := bstep (se 1 (by rfl) ⟨3841586, by rfl⟩ : syracuseStep 5122115 = 7683173) B7683173
theorem B2304119 : Blo 1008601 2304119 := bstep (se 1 (by rfl) ⟨1728089, by rfl⟩ : syracuseStep 2304119 = 3456179) B3456179
theorem B1517687 : Blo 1008601 1517687 := bstep (se 1 (by rfl) ⟨1138265, by rfl⟩ : syracuseStep 1517687 = 2276531) B2276531
theorem B1517711 : Blo 1008601 1517711 := bstep (se 1 (by rfl) ⟨1138283, by rfl⟩ : syracuseStep 1517711 = 2276567) B2276567
theorem B1517753 : Blo 1008601 1517753 := bstep (se 2 (by rfl) ⟨569157, by rfl⟩ : syracuseStep 1517753 = 1138315) B1138315
theorem B1517831 : Blo 1008601 1517831 := bstep (se 1 (by rfl) ⟨1138373, by rfl⟩ : syracuseStep 1517831 = 2276747) B2276747
theorem B3844367 : Blo 1008601 3844367 := bstep (se 1 (by rfl) ⟨2883275, by rfl⟩ : syracuseStep 3844367 = 5766551) B5766551
theorem B1517867 : Blo 1008601 1517867 := bstep (se 1 (by rfl) ⟨1138400, by rfl⟩ : syracuseStep 1517867 = 2276801) B2276801
theorem B1517897 : Blo 1008601 1517897 := bstep (se 2 (by rfl) ⟨569211, by rfl⟩ : syracuseStep 1517897 = 1138423) B1138423
theorem B5122439 : Blo 1008601 5122439 := bstep (se 1 (by rfl) ⟨3841829, by rfl⟩ : syracuseStep 5122439 = 7683659) B7683659
theorem B2271635 : Blo 1008601 2271635 := bstep (se 1 (by rfl) ⟨1703726, by rfl⟩ : syracuseStep 2271635 = 3407453) B3407453
theorem B3647891 : Blo 1008601 3647891 := bstep (se 1 (by rfl) ⟨2735918, by rfl⟩ : syracuseStep 3647891 = 5471837) B5471837
theorem B1518011 : Blo 1008601 1518011 := bstep (se 1 (by rfl) ⟨1138508, by rfl⟩ : syracuseStep 1518011 = 2277017) B2277017
theorem B2271689 : Blo 1008601 2271689 := bstep (se 2 (by rfl) ⟨851883, by rfl⟩ : syracuseStep 2271689 = 1703767) B1703767
theorem B1518071 : Blo 1008601 1518071 := bstep (se 1 (by rfl) ⟨1138553, by rfl⟩ : syracuseStep 1518071 = 2277107) B2277107
theorem B1518095 : Blo 1008601 1518095 := bstep (se 1 (by rfl) ⟨1138571, by rfl⟩ : syracuseStep 1518095 = 2277143) B2277143
theorem B1518137 : Blo 1008601 1518137 := bstep (se 2 (by rfl) ⟨569301, by rfl⟩ : syracuseStep 1518137 = 1138603) B1138603
theorem B1518215 : Blo 1008601 1518215 := bstep (se 1 (by rfl) ⟨1138661, by rfl⟩ : syracuseStep 1518215 = 2277323) B2277323
theorem B1518251 : Blo 1008601 1518251 := bstep (se 1 (by rfl) ⟨1138688, by rfl⟩ : syracuseStep 1518251 = 2277377) B2277377
theorem B1518281 : Blo 1008601 1518281 := bstep (se 2 (by rfl) ⟨569355, by rfl⟩ : syracuseStep 1518281 = 1138711) B1138711
theorem B1518395 : Blo 1008601 1518395 := bstep (se 1 (by rfl) ⟨1138796, by rfl⟩ : syracuseStep 1518395 = 2277593) B2277593
theorem B1518455 : Blo 1008601 1518455 := bstep (se 1 (by rfl) ⟨1138841, by rfl⟩ : syracuseStep 1518455 = 2277683) B2277683
theorem B1518479 : Blo 1008601 1518479 := bstep (se 1 (by rfl) ⟨1138859, by rfl⟩ : syracuseStep 1518479 = 2277719) B2277719
theorem B1846201 : Blo 1008601 1846201 := bstep (se 2 (by rfl) ⟨692325, by rfl⟩ : syracuseStep 1846201 = 1384651) B1384651
theorem B1518521 : Blo 1008601 1518521 := bstep (se 2 (by rfl) ⟨569445, by rfl⟩ : syracuseStep 1518521 = 1138891) B1138891
theorem B1518599 : Blo 1008601 1518599 := bstep (se 1 (by rfl) ⟨1138949, by rfl⟩ : syracuseStep 1518599 = 2277899) B2277899
theorem B2305039 : Blo 1008601 2305039 := bstep (se 1 (by rfl) ⟨1728779, by rfl⟩ : syracuseStep 2305039 = 3457559) B3457559
theorem B1518635 : Blo 1008601 1518635 := bstep (se 1 (by rfl) ⟨1138976, by rfl⟩ : syracuseStep 1518635 = 2277953) B2277953
theorem B1518665 : Blo 1008601 1518665 := bstep (se 2 (by rfl) ⟨569499, by rfl⟩ : syracuseStep 1518665 = 1138999) B1138999
theorem B2272391 : Blo 1008601 2272391 := bstep (se 1 (by rfl) ⟨1704293, by rfl⟩ : syracuseStep 2272391 = 3408587) B3408587
theorem B1518779 : Blo 1008601 1518779 := bstep (se 1 (by rfl) ⟨1139084, by rfl⟩ : syracuseStep 1518779 = 2278169) B2278169
theorem B1518839 : Blo 1008601 1518839 := bstep (se 1 (by rfl) ⟨1139129, by rfl⟩ : syracuseStep 1518839 = 2278259) B2278259
theorem B1518863 : Blo 1008601 1518863 := bstep (se 1 (by rfl) ⟨1139147, by rfl⟩ : syracuseStep 1518863 = 2278295) B2278295
theorem B2305313 : Blo 1008601 2305313 := bstep (se 2 (by rfl) ⟨864492, by rfl⟩ : syracuseStep 2305313 = 1728985) B1728985
theorem B2272571 : Blo 1008601 2272571 := bstep (se 1 (by rfl) ⟨1704428, by rfl⟩ : syracuseStep 2272571 = 3408857) B3408857
theorem B2272697 : Blo 1008601 2272697 := bstep (se 2 (by rfl) ⟨852261, by rfl⟩ : syracuseStep 2272697 = 1704523) B1704523
theorem B2731553 : Blo 1008601 2731553 := bstep (se 2 (by rfl) ⟨1024332, by rfl⟩ : syracuseStep 2731553 = 2048665) B2048665
theorem B2273039 : Blo 1008601 2273039 := bstep (se 1 (by rfl) ⟨1704779, by rfl⟩ : syracuseStep 2273039 = 3409559) B3409559
theorem B2273057 : Blo 1008601 2273057 := bstep (se 2 (by rfl) ⟨852396, by rfl⟩ : syracuseStep 2273057 = 1704793) B1704793
theorem B504868949 : Blo 1008601 504868949 := bstep (se 8 (by rfl) ⟨2958216, by rfl⟩ : syracuseStep 504868949 = 5916433) B5916433
theorem B2273399 : Blo 1008601 2273399 := bstep (se 1 (by rfl) ⟨1705049, by rfl⟩ : syracuseStep 2273399 = 3410099) B3410099
theorem B5746889 : Blo 1008601 5746889 := bstep (se 2 (by rfl) ⟨2155083, by rfl⟩ : syracuseStep 5746889 = 4310167) B4310167
theorem B2273579 : Blo 1008601 2273579 := bstep (se 1 (by rfl) ⟨1705184, by rfl⟩ : syracuseStep 2273579 = 3410369) B3410369
theorem B2273939 : Blo 1008601 2273939 := bstep (se 1 (by rfl) ⟨1705454, by rfl⟩ : syracuseStep 2273939 = 3410909) B3410909
theorem B1618633 : Blo 1008601 1618633 := bstep (se 2 (by rfl) ⟨606987, by rfl⟩ : syracuseStep 1618633 = 1213975) B1213975
theorem B2273993 : Blo 1008601 2273993 := bstep (se 2 (by rfl) ⟨852747, by rfl⟩ : syracuseStep 2273993 = 1705495) B1705495
theorem B4862855 : Blo 1008601 4862855 := bstep (se 1 (by rfl) ⟨3647141, by rfl⟩ : syracuseStep 4862855 = 7294283) B7294283
theorem B2045063 : Blo 1008601 2045063 := bstep (se 1 (by rfl) ⟨1533797, by rfl⟩ : syracuseStep 2045063 = 3067595) B3067595
theorem B2733323 : Blo 1008601 2733323 := bstep (se 1 (by rfl) ⟨2049992, by rfl⟩ : syracuseStep 2733323 = 4099985) B4099985
theorem B6141199 : Blo 1008601 6141199 := bstep (se 1 (by rfl) ⟨4605899, by rfl⟩ : syracuseStep 6141199 = 9211799) B9211799
theorem B2274695 : Blo 1008601 2274695 := bstep (se 1 (by rfl) ⟨1706021, by rfl⟩ : syracuseStep 2274695 = 3412043) B3412043
theorem B11515283 : Blo 1008601 11515283 := bstep (se 1 (by rfl) ⟨8636462, by rfl⟩ : syracuseStep 11515283 = 17272925) B17272925
theorem B2307475 : Blo 1008601 2307475 := bstep (se 1 (by rfl) ⟨1730606, by rfl⟩ : syracuseStep 2307475 = 3461213) B3461213
theorem B2274875 : Blo 1008601 2274875 := bstep (se 1 (by rfl) ⟨1706156, by rfl⟩ : syracuseStep 2274875 = 3412313) B3412313
theorem B2275001 : Blo 1008601 2275001 := bstep (se 2 (by rfl) ⟨853125, by rfl⟩ : syracuseStep 2275001 = 1706251) B1706251
theorem B4994797 : Blo 1008601 4994797 := bstep (se 3 (by rfl) ⟨936524, by rfl⟩ : syracuseStep 4994797 = 1873049) B1873049
theorem B5126003 : Blo 1008601 5126003 := bstep (se 1 (by rfl) ⟨3844502, by rfl⟩ : syracuseStep 5126003 = 7689005) B7689005
theorem B8632331 : Blo 1008601 8632331 := bstep (se 1 (by rfl) ⟨6474248, by rfl⟩ : syracuseStep 8632331 = 12948497) B12948497
theorem B2275343 : Blo 1008601 2275343 := bstep (se 1 (by rfl) ⟨1706507, by rfl⟩ : syracuseStep 2275343 = 3413015) B3413015
theorem B2275361 : Blo 1008601 2275361 := bstep (se 2 (by rfl) ⟨853260, by rfl⟩ : syracuseStep 2275361 = 1706521) B1706521
theorem B1849387 : Blo 1008601 1849387 := bstep (se 1 (by rfl) ⟨1387040, by rfl⟩ : syracuseStep 1849387 = 2774081) B2774081
theorem B3323965 : Blo 1008601 3323965 := bstep (se 3 (by rfl) ⟨623243, by rfl⟩ : syracuseStep 3323965 = 1246487) B1246487
theorem B5748803 : Blo 1008601 5748803 := bstep (se 1 (by rfl) ⟨4311602, by rfl⟩ : syracuseStep 5748803 = 8623205) B8623205
theorem B1915015 : Blo 1008601 1915015 := bstep (se 1 (by rfl) ⟨1436261, by rfl⟩ : syracuseStep 1915015 = 2872523) B2872523
theorem B2275703 : Blo 1008601 2275703 := bstep (se 1 (by rfl) ⟨1706777, by rfl⟩ : syracuseStep 2275703 = 3413555) B3413555
theorem B2275883 : Blo 1008601 2275883 := bstep (se 1 (by rfl) ⟨1706912, by rfl⟩ : syracuseStep 2275883 = 3413825) B3413825
theorem B2276243 : Blo 1008601 2276243 := bstep (se 1 (by rfl) ⟨1707182, by rfl⟩ : syracuseStep 2276243 = 3414365) B3414365
theorem B32783267 : Blo 1008601 32783267 := bstep (se 1 (by rfl) ⟨24587450, by rfl⟩ : syracuseStep 32783267 = 49174901) B49174901
theorem B2276297 : Blo 1008601 2276297 := bstep (se 2 (by rfl) ⟨853611, by rfl⟩ : syracuseStep 2276297 = 1707223) B1707223
theorem B1457353 : Blo 1008601 1457353 := bstep (se 2 (by rfl) ⟨546507, by rfl⟩ : syracuseStep 1457353 = 1093015) B1093015
theorem B2047351 : Blo 1008601 2047351 := bstep (se 1 (by rfl) ⟨1535513, by rfl⟩ : syracuseStep 2047351 = 3071027) B3071027
theorem B1621433 : Blo 1008601 1621433 := bstep (se 2 (by rfl) ⟨608037, by rfl⟩ : syracuseStep 1621433 = 1216075) B1216075
theorem B6471197 : Blo 1008601 6471197 := bstep (se 3 (by rfl) ⟨1213349, by rfl⟩ : syracuseStep 6471197 = 2426699) B2426699
theorem B1457723 : Blo 1008601 1457723 := bstep (se 1 (by rfl) ⟨1093292, by rfl⟩ : syracuseStep 1457723 = 2186585) B2186585
theorem B2768503 : Blo 1008601 2768503 := bstep (se 1 (by rfl) ⟨2076377, by rfl⟩ : syracuseStep 2768503 = 4152755) B4152755
theorem B2276999 : Blo 1008601 2276999 := bstep (se 1 (by rfl) ⟨1707749, by rfl⟩ : syracuseStep 2276999 = 3415499) B3415499
theorem B1916617 : Blo 1008601 1916617 := bstep (se 2 (by rfl) ⟨718731, by rfl⟩ : syracuseStep 1916617 = 1437463) B1437463
theorem B2277179 : Blo 1008601 2277179 := bstep (se 1 (by rfl) ⟨1707884, by rfl⟩ : syracuseStep 2277179 = 3415769) B3415769
theorem B2277305 : Blo 1008601 2277305 := bstep (se 2 (by rfl) ⟨853989, by rfl⟩ : syracuseStep 2277305 = 1707979) B1707979
theorem B4669483 : Blo 1008601 4669483 := bstep (se 1 (by rfl) ⟨3502112, by rfl⟩ : syracuseStep 4669483 = 7004225) B7004225
theorem B1294471 : Blo 1008601 1294471 := bstep (se 1 (by rfl) ⟨970853, by rfl⟩ : syracuseStep 1294471 = 1941707) B1941707
theorem B12927221 : Blo 1008601 12927221 := bstep (se 5 (by rfl) ⟨605963, by rfl⟩ : syracuseStep 12927221 = 1211927) B1211927
theorem B2277647 : Blo 1008601 2277647 := bstep (se 1 (by rfl) ⟨1708235, by rfl⟩ : syracuseStep 2277647 = 3416471) B3416471
theorem B2277665 : Blo 1008601 2277665 := bstep (se 2 (by rfl) ⟨854124, by rfl⟩ : syracuseStep 2277665 = 1708249) B1708249
theorem B12271931 : Blo 1008601 12271931 := bstep (se 1 (by rfl) ⟨9203948, by rfl⟩ : syracuseStep 12271931 = 18407897) B18407897
theorem B39338531 : Blo 1008601 39338531 := bstep (se 1 (by rfl) ⟨29503898, by rfl⟩ : syracuseStep 39338531 = 59007797) B59007797
theorem B2278007 : Blo 1008601 2278007 := bstep (se 1 (by rfl) ⟨1708505, by rfl⟩ : syracuseStep 2278007 = 3417011) B3417011
theorem B2048647 : Blo 1008601 2048647 := bstep (se 1 (by rfl) ⟨1536485, by rfl⟩ : syracuseStep 2048647 = 3072971) B3072971
theorem B4309793 : Blo 1008601 4309793 := bstep (se 2 (by rfl) ⟨1616172, by rfl⟩ : syracuseStep 4309793 = 3232345) B3232345
theorem B2278187 : Blo 1008601 2278187 := bstep (se 1 (by rfl) ⟨1708640, by rfl⟩ : syracuseStep 2278187 = 3417281) B3417281
theorem B5194775 : Blo 1008601 5194775 := bstep (se 1 (by rfl) ⟨3896081, by rfl⟩ : syracuseStep 5194775 = 7792163) B7792163
theorem B3687713 : Blo 1008601 3687713 := bstep (se 2 (by rfl) ⟨1382892, by rfl⟩ : syracuseStep 3687713 = 2765785) B2765785
theorem B8767043 : Blo 1008601 8767043 := bstep (se 1 (by rfl) ⟨6575282, by rfl⟩ : syracuseStep 8767043 = 13150565) B13150565
theorem B5752721 : Blo 1008601 5752721 := bstep (se 2 (by rfl) ⟨2157270, by rfl⟩ : syracuseStep 5752721 = 4314541) B4314541
theorem B2050091 : Blo 1008601 2050091 := bstep (se 1 (by rfl) ⟨1537568, by rfl⟩ : syracuseStep 2050091 = 3075137) B3075137
theorem B1919123 : Blo 1008601 1919123 := bstep (se 1 (by rfl) ⟨1439342, by rfl⟩ : syracuseStep 1919123 = 2878685) B2878685
theorem B6473965 : Blo 1008601 6473965 := bstep (se 3 (by rfl) ⟨1213868, by rfl⟩ : syracuseStep 6473965 = 2427737) B2427737
theorem B8636705 : Blo 1008601 8636705 := bstep (se 2 (by rfl) ⟨3238764, by rfl⟩ : syracuseStep 8636705 = 6477529) B6477529
theorem B5753177 : Blo 1008601 5753177 := bstep (se 2 (by rfl) ⟨2157441, by rfl⟩ : syracuseStep 5753177 = 4314883) B4314883
theorem B1919351 : Blo 1008601 1919351 := bstep (se 1 (by rfl) ⟨1439513, by rfl⟩ : syracuseStep 1919351 = 2879027) B2879027
theorem B1297015 : Blo 1008601 1297015 := bstep (se 1 (by rfl) ⟨972761, by rfl⟩ : syracuseStep 1297015 = 1945523) B1945523
theorem B9226871 : Blo 1008601 9226871 := bstep (se 1 (by rfl) ⟨6920153, by rfl⟩ : syracuseStep 9226871 = 13840307) B13840307
theorem B1821575 : Blo 1008601 1821575 := bstep (se 1 (by rfl) ⟨1366181, by rfl⟩ : syracuseStep 1821575 = 2732363) B2732363
theorem B17255429 : Blo 1008601 17255429 := bstep (se 4 (by rfl) ⟨1617696, by rfl⟩ : syracuseStep 17255429 = 3235393) B3235393
theorem B2051219 : Blo 1008601 2051219 := bstep (se 1 (by rfl) ⟨1538414, by rfl⟩ : syracuseStep 2051219 = 3076829) B3076829
theorem B1822267 : Blo 1008601 1822267 := bstep (se 1 (by rfl) ⟨1366700, by rfl⟩ : syracuseStep 1822267 = 2733401) B2733401
theorem B11489039 : Blo 1008601 11489039 := bstep (se 1 (by rfl) ⟨8616779, by rfl⟩ : syracuseStep 11489039 = 17233559) B17233559
theorem B8179471 : Blo 1008601 8179471 := bstep (se 1 (by rfl) ⟨6134603, by rfl⟩ : syracuseStep 8179471 = 12269207) B12269207
theorem B3460897 : Blo 1008601 3460897 := bstep (se 2 (by rfl) ⟨1297836, by rfl⟩ : syracuseStep 3460897 = 2595673) B2595673
theorem B1921067 : Blo 1008601 1921067 := bstep (se 1 (by rfl) ⟨1440800, by rfl⟩ : syracuseStep 1921067 = 2881601) B2881601
theorem B1298575 : Blo 1008601 1298575 := bstep (se 1 (by rfl) ⟨973931, by rfl⟩ : syracuseStep 1298575 = 1947863) B1947863
theorem B1921295 : Blo 1008601 1921295 := bstep (se 1 (by rfl) ⟨1440971, by rfl⟩ : syracuseStep 1921295 = 2881943) B2881943
theorem B1135111 : Blo 1008601 1135111 := bstep (se 1 (by rfl) ⟨851333, by rfl⟩ : syracuseStep 1135111 = 1702667) B1702667
theorem B1135291 : Blo 1008601 1135291 := bstep (se 1 (by rfl) ⟨851468, by rfl⟩ : syracuseStep 1135291 = 1702937) B1702937
theorem B4051727 : Blo 1008601 4051727 := bstep (se 1 (by rfl) ⟨3038795, by rfl⟩ : syracuseStep 4051727 = 6077591) B6077591
theorem B1135759 : Blo 1008601 1135759 := bstep (se 1 (by rfl) ⟨851819, by rfl⟩ : syracuseStep 1135759 = 1703639) B1703639
theorem B5756345 : Blo 1008601 5756345 := bstep (se 2 (by rfl) ⟨2158629, by rfl⟩ : syracuseStep 5756345 = 4317259) B4317259
theorem B4609565 : Blo 1008601 4609565 := bstep (se 3 (by rfl) ⟨864293, by rfl⟩ : syracuseStep 4609565 = 1728587) B1728587
theorem B1136263 : Blo 1008601 1136263 := bstep (se 1 (by rfl) ⟨852197, by rfl⟩ : syracuseStep 1136263 = 1704395) B1704395
theorem B2872979 : Blo 1008601 2872979 := bstep (se 1 (by rfl) ⟨2154734, by rfl⟩ : syracuseStep 2872979 = 4309469) B4309469
theorem B1136443 : Blo 1008601 1136443 := bstep (se 1 (by rfl) ⟨852332, by rfl⟩ : syracuseStep 1136443 = 1704665) B1704665
theorem B1136911 : Blo 1008601 1136911 := bstep (se 1 (by rfl) ⟨852683, by rfl⟩ : syracuseStep 1136911 = 1705367) B1705367
theorem B3234163 : Blo 1008601 3234163 := bstep (se 1 (by rfl) ⟨2425622, by rfl⟩ : syracuseStep 3234163 = 4851245) B4851245
theorem B3463741 : Blo 1008601 3463741 := bstep (se 3 (by rfl) ⟨649451, by rfl⟩ : syracuseStep 3463741 = 1298903) B1298903
theorem B1137415 : Blo 1008601 1137415 := bstep (se 1 (by rfl) ⟨853061, by rfl⟩ : syracuseStep 1137415 = 1706123) B1706123
theorem B1137595 : Blo 1008601 1137595 := bstep (se 1 (by rfl) ⟨853196, by rfl⟩ : syracuseStep 1137595 = 1706393) B1706393
theorem B2874379 : Blo 1008601 2874379 := bstep (se 1 (by rfl) ⟨2155784, by rfl⟩ : syracuseStep 2874379 = 4311569) B4311569
theorem B6151439 : Blo 1008601 6151439 := bstep (se 1 (by rfl) ⟨4613579, by rfl⟩ : syracuseStep 6151439 = 9227159) B9227159
theorem B2874653 : Blo 1008601 2874653 := bstep (se 3 (by rfl) ⟨538997, by rfl⟩ : syracuseStep 2874653 = 1077995) B1077995
theorem B1138063 : Blo 1008601 1138063 := bstep (se 1 (by rfl) ⟨853547, by rfl⟩ : syracuseStep 1138063 = 1707095) B1707095
theorem B7200323 : Blo 1008601 7200323 := bstep (se 1 (by rfl) ⟨5400242, by rfl⟩ : syracuseStep 7200323 = 10800485) B10800485
theorem B5758735 : Blo 1008601 5758735 := bstep (se 1 (by rfl) ⟨4319051, by rfl⟩ : syracuseStep 5758735 = 8638103) B8638103
theorem B1138567 : Blo 1008601 1138567 := bstep (se 1 (by rfl) ⟨853925, by rfl⟩ : syracuseStep 1138567 = 1707851) B1707851
theorem B4612049 : Blo 1008601 4612049 := bstep (se 2 (by rfl) ⟨1729518, by rfl⟩ : syracuseStep 4612049 = 3459037) B3459037
theorem B3694621 : Blo 1008601 3694621 := bstep (se 3 (by rfl) ⟨692741, by rfl⟩ : syracuseStep 3694621 = 1385483) B1385483
theorem B2154529 : Blo 1008601 2154529 := bstep (se 2 (by rfl) ⟨807948, by rfl⟩ : syracuseStep 2154529 = 1615897) B1615897
theorem B1138747 : Blo 1008601 1138747 := bstep (se 1 (by rfl) ⟨854060, by rfl⟩ : syracuseStep 1138747 = 1708121) B1708121
theorem B1728697 : Blo 1008601 1728697 := bstep (se 2 (by rfl) ⟨648261, by rfl⟩ : syracuseStep 1728697 = 1296523) B1296523
theorem B65462741 : Blo 1008601 65462741 := bstep (se 7 (by rfl) ⟨767141, by rfl⟩ : syracuseStep 65462741 = 1534283) B1534283
theorem B9724481 : Blo 1008601 9724481 := bstep (se 2 (by rfl) ⟨3646680, by rfl⟩ : syracuseStep 9724481 = 7293361) B7293361
theorem B11526947 : Blo 1008601 11526947 := bstep (se 1 (by rfl) ⟨8645210, by rfl⟩ : syracuseStep 11526947 = 17290421) B17290421
theorem B1008647 : Blo 1008601 1008647 := bstep (se 1 (by rfl) ⟨756485, by rfl⟩ : syracuseStep 1008647 = 1512971) B1512971
theorem B5760011 : Blo 1008601 5760011 := bstep (se 1 (by rfl) ⟨4320008, by rfl⟩ : syracuseStep 5760011 = 8640017) B8640017
theorem B1008655 : Blo 1008601 1008655 := bstep (se 1 (by rfl) ⟨756491, by rfl⟩ : syracuseStep 1008655 = 1512983) B1512983
theorem B1008699 : Blo 1008601 1008699 := bstep (se 1 (by rfl) ⟨756524, by rfl⟩ : syracuseStep 1008699 = 1513049) B1513049
theorem B1008775 : Blo 1008601 1008775 := bstep (se 1 (by rfl) ⟨756581, by rfl⟩ : syracuseStep 1008775 = 1513163) B1513163
theorem B1008783 : Blo 1008601 1008783 := bstep (se 1 (by rfl) ⟨756587, by rfl⟩ : syracuseStep 1008783 = 1513175) B1513175
theorem B1008827 : Blo 1008601 1008827 := bstep (se 1 (by rfl) ⟨756620, by rfl⟩ : syracuseStep 1008827 = 1513241) B1513241
theorem B5760193 : Blo 1008601 5760193 := bstep (se 2 (by rfl) ⟨2160072, by rfl⟩ : syracuseStep 5760193 = 4320145) B4320145
theorem B1008903 : Blo 1008601 1008903 := bstep (se 1 (by rfl) ⟨756677, by rfl⟩ : syracuseStep 1008903 = 1513355) B1513355
theorem B1008911 : Blo 1008601 1008911 := bstep (se 1 (by rfl) ⟨756683, by rfl⟩ : syracuseStep 1008911 = 1513367) B1513367
theorem B1008955 : Blo 1008601 1008955 := bstep (se 1 (by rfl) ⟨756716, by rfl⟩ : syracuseStep 1008955 = 1513433) B1513433
theorem B1009031 : Blo 1008601 1009031 := bstep (se 1 (by rfl) ⟨756773, by rfl⟩ : syracuseStep 1009031 = 1513547) B1513547
theorem B1009039 : Blo 1008601 1009039 := bstep (se 1 (by rfl) ⟨756779, by rfl⟩ : syracuseStep 1009039 = 1513559) B1513559
theorem B1009083 : Blo 1008601 1009083 := bstep (se 1 (by rfl) ⟨756812, by rfl⟩ : syracuseStep 1009083 = 1513625) B1513625
theorem B1009159 : Blo 1008601 1009159 := bstep (se 1 (by rfl) ⟨756869, by rfl⟩ : syracuseStep 1009159 = 1513739) B1513739
theorem B1009167 : Blo 1008601 1009167 := bstep (se 1 (by rfl) ⟨756875, by rfl⟩ : syracuseStep 1009167 = 1513751) B1513751
theorem B2156075 : Blo 1008601 2156075 := bstep (se 1 (by rfl) ⟨1617056, by rfl⟩ : syracuseStep 2156075 = 3234113) B3234113
theorem B1009211 : Blo 1008601 1009211 := bstep (se 1 (by rfl) ⟨756908, by rfl⟩ : syracuseStep 1009211 = 1513817) B1513817
theorem B1009287 : Blo 1008601 1009287 := bstep (se 1 (by rfl) ⟨756965, by rfl⟩ : syracuseStep 1009287 = 1513931) B1513931
theorem B1009295 : Blo 1008601 1009295 := bstep (se 1 (by rfl) ⟨756971, by rfl⟩ : syracuseStep 1009295 = 1513943) B1513943
theorem B2877113 : Blo 1008601 2877113 := bstep (se 2 (by rfl) ⟨1078917, by rfl⟩ : syracuseStep 2877113 = 2157835) B2157835
theorem B1009339 : Blo 1008601 1009339 := bstep (se 1 (by rfl) ⟨757004, by rfl⟩ : syracuseStep 1009339 = 1514009) B1514009
theorem B1009415 : Blo 1008601 1009415 := bstep (se 1 (by rfl) ⟨757061, by rfl⟩ : syracuseStep 1009415 = 1514123) B1514123
theorem B1009423 : Blo 1008601 1009423 := bstep (se 1 (by rfl) ⟨757067, by rfl⟩ : syracuseStep 1009423 = 1514135) B1514135
theorem B2877227 : Blo 1008601 2877227 := bstep (se 1 (by rfl) ⟨2157920, by rfl⟩ : syracuseStep 2877227 = 4315841) B4315841
theorem B1009467 : Blo 1008601 1009467 := bstep (se 1 (by rfl) ⟨757100, by rfl⟩ : syracuseStep 1009467 = 1514201) B1514201
theorem B1009543 : Blo 1008601 1009543 := bstep (se 1 (by rfl) ⟨757157, by rfl⟩ : syracuseStep 1009543 = 1514315) B1514315
theorem B1009551 : Blo 1008601 1009551 := bstep (se 1 (by rfl) ⟨757163, by rfl⟩ : syracuseStep 1009551 = 1514327) B1514327
theorem B3073945 : Blo 1008601 3073945 := bstep (se 2 (by rfl) ⟨1152729, by rfl⟩ : syracuseStep 3073945 = 2305459) B2305459
theorem B1009595 : Blo 1008601 1009595 := bstep (se 1 (by rfl) ⟨757196, by rfl⟩ : syracuseStep 1009595 = 1514393) B1514393
theorem B1009671 : Blo 1008601 1009671 := bstep (se 1 (by rfl) ⟨757253, by rfl⟩ : syracuseStep 1009671 = 1514507) B1514507
theorem B1533967 : Blo 1008601 1533967 := bstep (se 1 (by rfl) ⟨1150475, by rfl⟩ : syracuseStep 1533967 = 2300951) B2300951
theorem B1009679 : Blo 1008601 1009679 := bstep (se 1 (by rfl) ⟨757259, by rfl⟩ : syracuseStep 1009679 = 1514519) B1514519
theorem B1009723 : Blo 1008601 1009723 := bstep (se 1 (by rfl) ⟨757292, by rfl⟩ : syracuseStep 1009723 = 1514585) B1514585
theorem B1009799 : Blo 1008601 1009799 := bstep (se 1 (by rfl) ⟨757349, by rfl⟩ : syracuseStep 1009799 = 1514699) B1514699
theorem B1009807 : Blo 1008601 1009807 := bstep (se 1 (by rfl) ⟨757355, by rfl⟩ : syracuseStep 1009807 = 1514711) B1514711
theorem B3074201 : Blo 1008601 3074201 := bstep (se 2 (by rfl) ⟨1152825, by rfl⟩ : syracuseStep 3074201 = 2305651) B2305651
theorem B1009851 : Blo 1008601 1009851 := bstep (se 1 (by rfl) ⟨757388, by rfl⟩ : syracuseStep 1009851 = 1514777) B1514777
theorem B21883121 : Blo 1008601 21883121 := bstep (se 2 (by rfl) ⟨8206170, by rfl⟩ : syracuseStep 21883121 = 16412341) B16412341
theorem B1009927 : Blo 1008601 1009927 := bstep (se 1 (by rfl) ⟨757445, by rfl⟩ : syracuseStep 1009927 = 1514891) B1514891
theorem B1009935 : Blo 1008601 1009935 := bstep (se 1 (by rfl) ⟨757451, by rfl⟩ : syracuseStep 1009935 = 1514903) B1514903
theorem B1009979 : Blo 1008601 1009979 := bstep (se 1 (by rfl) ⟨757484, by rfl⟩ : syracuseStep 1009979 = 1514969) B1514969
theorem B1010055 : Blo 1008601 1010055 := bstep (se 1 (by rfl) ⟨757541, by rfl⟩ : syracuseStep 1010055 = 1515083) B1515083
theorem B1010063 : Blo 1008601 1010063 := bstep (se 1 (by rfl) ⟨757547, by rfl⟩ : syracuseStep 1010063 = 1515095) B1515095
theorem B1010107 : Blo 1008601 1010107 := bstep (se 1 (by rfl) ⟨757580, by rfl⟩ : syracuseStep 1010107 = 1515161) B1515161
theorem B1010183 : Blo 1008601 1010183 := bstep (se 1 (by rfl) ⟨757637, by rfl⟩ : syracuseStep 1010183 = 1515275) B1515275
theorem B1010191 : Blo 1008601 1010191 := bstep (se 1 (by rfl) ⟨757643, by rfl⟩ : syracuseStep 1010191 = 1515287) B1515287
theorem B1010235 : Blo 1008601 1010235 := bstep (se 1 (by rfl) ⟨757676, by rfl⟩ : syracuseStep 1010235 = 1515353) B1515353
theorem B1436233 : Blo 1008601 1436233 := bstep (se 2 (by rfl) ⟨538587, by rfl⟩ : syracuseStep 1436233 = 1077175) B1077175
theorem B1010311 : Blo 1008601 1010311 := bstep (se 1 (by rfl) ⟨757733, by rfl⟩ : syracuseStep 1010311 = 1515467) B1515467
theorem B1010319 : Blo 1008601 1010319 := bstep (se 1 (by rfl) ⟨757739, by rfl⟩ : syracuseStep 1010319 = 1515479) B1515479
theorem B1010363 : Blo 1008601 1010363 := bstep (se 1 (by rfl) ⟨757772, by rfl⟩ : syracuseStep 1010363 = 1515545) B1515545
theorem B1010439 : Blo 1008601 1010439 := bstep (se 1 (by rfl) ⟨757829, by rfl⟩ : syracuseStep 1010439 = 1515659) B1515659
theorem B1010447 : Blo 1008601 1010447 := bstep (se 1 (by rfl) ⟨757835, by rfl⟩ : syracuseStep 1010447 = 1515671) B1515671
theorem B1010491 : Blo 1008601 1010491 := bstep (se 1 (by rfl) ⟨757868, by rfl⟩ : syracuseStep 1010491 = 1515737) B1515737
theorem B1010567 : Blo 1008601 1010567 := bstep (se 1 (by rfl) ⟨757925, by rfl⟩ : syracuseStep 1010567 = 1515851) B1515851
theorem B1010575 : Blo 1008601 1010575 := bstep (se 1 (by rfl) ⟨757931, by rfl⟩ : syracuseStep 1010575 = 1515863) B1515863
theorem B2878355 : Blo 1008601 2878355 := bstep (se 1 (by rfl) ⟨2158766, by rfl⟩ : syracuseStep 2878355 = 4317533) B4317533
theorem B1010619 : Blo 1008601 1010619 := bstep (se 1 (by rfl) ⟨757964, by rfl⟩ : syracuseStep 1010619 = 1515929) B1515929
theorem B1010695 : Blo 1008601 1010695 := bstep (se 1 (by rfl) ⟨758021, by rfl⟩ : syracuseStep 1010695 = 1516043) B1516043
theorem B1010703 : Blo 1008601 1010703 := bstep (se 1 (by rfl) ⟨758027, by rfl⟩ : syracuseStep 1010703 = 1516055) B1516055
theorem B1010747 : Blo 1008601 1010747 := bstep (se 1 (by rfl) ⟨758060, by rfl⟩ : syracuseStep 1010747 = 1516121) B1516121
theorem B4320317 : Blo 1008601 4320317 := bstep (se 3 (by rfl) ⟨810059, by rfl⟩ : syracuseStep 4320317 = 1620119) B1620119
theorem B1436791 : Blo 1008601 1436791 := bstep (se 1 (by rfl) ⟨1077593, by rfl⟩ : syracuseStep 1436791 = 2155187) B2155187
theorem B1010823 : Blo 1008601 1010823 := bstep (se 1 (by rfl) ⟨758117, by rfl⟩ : syracuseStep 1010823 = 1516235) B1516235
theorem B1010831 : Blo 1008601 1010831 := bstep (se 1 (by rfl) ⟨758123, by rfl⟩ : syracuseStep 1010831 = 1516247) B1516247
theorem B2157715 : Blo 1008601 2157715 := bstep (se 1 (by rfl) ⟨1618286, by rfl⟩ : syracuseStep 2157715 = 3236573) B3236573
theorem B1010875 : Blo 1008601 1010875 := bstep (se 1 (by rfl) ⟨758156, by rfl⟩ : syracuseStep 1010875 = 1516313) B1516313
theorem B1010951 : Blo 1008601 1010951 := bstep (se 1 (by rfl) ⟨758213, by rfl⟩ : syracuseStep 1010951 = 1516427) B1516427
theorem B1010959 : Blo 1008601 1010959 := bstep (se 1 (by rfl) ⟨758219, by rfl⟩ : syracuseStep 1010959 = 1516439) B1516439
theorem B2878753 : Blo 1008601 2878753 := bstep (se 2 (by rfl) ⟨1079532, by rfl⟩ : syracuseStep 2878753 = 2159065) B2159065
theorem B1011003 : Blo 1008601 1011003 := bstep (se 1 (by rfl) ⟨758252, by rfl⟩ : syracuseStep 1011003 = 1516505) B1516505
theorem B1011079 : Blo 1008601 1011079 := bstep (se 1 (by rfl) ⟨758309, by rfl⟩ : syracuseStep 1011079 = 1516619) B1516619
theorem B1011087 : Blo 1008601 1011087 := bstep (se 1 (by rfl) ⟨758315, by rfl⟩ : syracuseStep 1011087 = 1516631) B1516631
theorem B6483347 : Blo 1008601 6483347 := bstep (se 1 (by rfl) ⟨4862510, by rfl⟩ : syracuseStep 6483347 = 9725021) B9725021
theorem B1011131 : Blo 1008601 1011131 := bstep (se 1 (by rfl) ⟨758348, by rfl⟩ : syracuseStep 1011131 = 1516697) B1516697
theorem B1011207 : Blo 1008601 1011207 := bstep (se 1 (by rfl) ⟨758405, by rfl⟩ : syracuseStep 1011207 = 1516811) B1516811
theorem B5107211 : Blo 1008601 5107211 := bstep (se 1 (by rfl) ⟨3830408, by rfl⟩ : syracuseStep 5107211 = 7660817) B7660817
theorem B1011215 : Blo 1008601 1011215 := bstep (se 1 (by rfl) ⟨758411, by rfl⟩ : syracuseStep 1011215 = 1516823) B1516823
theorem B1011259 : Blo 1008601 1011259 := bstep (se 1 (by rfl) ⟨758444, by rfl⟩ : syracuseStep 1011259 = 1516889) B1516889
theorem B110587477 : Blo 1008601 110587477 := bstep (se 8 (by rfl) ⟨647973, by rfl⟩ : syracuseStep 110587477 = 1295947) B1295947
theorem B1011335 : Blo 1008601 1011335 := bstep (se 1 (by rfl) ⟨758501, by rfl⟩ : syracuseStep 1011335 = 1517003) B1517003
theorem B1011343 : Blo 1008601 1011343 := bstep (se 1 (by rfl) ⟨758507, by rfl⟩ : syracuseStep 1011343 = 1517015) B1517015
theorem B1437355 : Blo 1008601 1437355 := bstep (se 1 (by rfl) ⟨1078016, by rfl⟩ : syracuseStep 1437355 = 2156033) B2156033
theorem B5107373 : Blo 1008601 5107373 := bstep (se 3 (by rfl) ⟨957632, by rfl⟩ : syracuseStep 5107373 = 1915265) B1915265
theorem B1011387 : Blo 1008601 1011387 := bstep (se 1 (by rfl) ⟨758540, by rfl⟩ : syracuseStep 1011387 = 1517081) B1517081
theorem B6156013 : Blo 1008601 6156013 := bstep (se 3 (by rfl) ⟨1154252, by rfl⟩ : syracuseStep 6156013 = 2308505) B2308505
theorem B1011463 : Blo 1008601 1011463 := bstep (se 1 (by rfl) ⟨758597, by rfl⟩ : syracuseStep 1011463 = 1517195) B1517195
theorem B1011471 : Blo 1008601 1011471 := bstep (se 1 (by rfl) ⟨758603, by rfl⟩ : syracuseStep 1011471 = 1517207) B1517207
theorem B4091681 : Blo 1008601 4091681 := bstep (se 2 (by rfl) ⟨1534380, by rfl⟩ : syracuseStep 4091681 = 3068761) B3068761
theorem B7270181 : Blo 1008601 7270181 := bstep (se 4 (by rfl) ⟨681579, by rfl⟩ : syracuseStep 7270181 = 1363159) B1363159
theorem B1011515 : Blo 1008601 1011515 := bstep (se 1 (by rfl) ⟨758636, by rfl⟩ : syracuseStep 1011515 = 1517273) B1517273
theorem B3829619 : Blo 1008601 3829619 := bstep (se 1 (by rfl) ⟨2872214, by rfl⟩ : syracuseStep 3829619 = 5744429) B5744429
theorem B1011591 : Blo 1008601 1011591 := bstep (se 1 (by rfl) ⟨758693, by rfl⟩ : syracuseStep 1011591 = 1517387) B1517387
theorem B1437583 : Blo 1008601 1437583 := bstep (se 1 (by rfl) ⟨1078187, by rfl⟩ : syracuseStep 1437583 = 2156375) B2156375
theorem B1011599 : Blo 1008601 1011599 := bstep (se 1 (by rfl) ⟨758699, by rfl⟩ : syracuseStep 1011599 = 1517399) B1517399
theorem B12283811 : Blo 1008601 12283811 := bstep (se 1 (by rfl) ⟨9212858, by rfl⟩ : syracuseStep 12283811 = 18425717) B18425717
theorem B1011643 : Blo 1008601 1011643 := bstep (se 1 (by rfl) ⟨758732, by rfl⟩ : syracuseStep 1011643 = 1517465) B1517465
theorem B1011719 : Blo 1008601 1011719 := bstep (se 1 (by rfl) ⟨758789, by rfl⟩ : syracuseStep 1011719 = 1517579) B1517579
theorem B1011727 : Blo 1008601 1011727 := bstep (se 1 (by rfl) ⟨758795, by rfl⟩ : syracuseStep 1011727 = 1517591) B1517591
theorem B1011771 : Blo 1008601 1011771 := bstep (se 1 (by rfl) ⟨758828, by rfl⟩ : syracuseStep 1011771 = 1517657) B1517657
theorem B4616279 : Blo 1008601 4616279 := bstep (se 1 (by rfl) ⟨3462209, by rfl⟩ : syracuseStep 4616279 = 6924419) B6924419
theorem B2912375 : Blo 1008601 2912375 := bstep (se 1 (by rfl) ⟨2184281, by rfl⟩ : syracuseStep 2912375 = 4368563) B4368563
theorem B8188037 : Blo 1008601 8188037 := bstep (se 4 (by rfl) ⟨767628, by rfl⟩ : syracuseStep 8188037 = 1535257) B1535257
theorem B1011847 : Blo 1008601 1011847 := bstep (se 1 (by rfl) ⟨758885, by rfl⟩ : syracuseStep 1011847 = 1517771) B1517771
theorem B1011855 : Blo 1008601 1011855 := bstep (se 1 (by rfl) ⟨758891, by rfl⟩ : syracuseStep 1011855 = 1517783) B1517783
theorem B2879641 : Blo 1008601 2879641 := bstep (se 2 (by rfl) ⟨1079865, by rfl⟩ : syracuseStep 2879641 = 2159731) B2159731
theorem B1011899 : Blo 1008601 1011899 := bstep (se 1 (by rfl) ⟨758924, by rfl⟩ : syracuseStep 1011899 = 1517849) B1517849
theorem B1011975 : Blo 1008601 1011975 := bstep (se 1 (by rfl) ⟨758981, by rfl⟩ : syracuseStep 1011975 = 1517963) B1517963
theorem B1011983 : Blo 1008601 1011983 := bstep (se 1 (by rfl) ⟨758987, by rfl⟩ : syracuseStep 1011983 = 1517975) B1517975
theorem B3830075 : Blo 1008601 3830075 := bstep (se 1 (by rfl) ⟨2872556, by rfl⟩ : syracuseStep 3830075 = 5745113) B5745113
theorem B11497787 : Blo 1008601 11497787 := bstep (se 1 (by rfl) ⟨8623340, by rfl⟩ : syracuseStep 11497787 = 17246681) B17246681
theorem B1012027 : Blo 1008601 1012027 := bstep (se 1 (by rfl) ⟨759020, by rfl⟩ : syracuseStep 1012027 = 1518041) B1518041
theorem B1012103 : Blo 1008601 1012103 := bstep (se 1 (by rfl) ⟨759077, by rfl⟩ : syracuseStep 1012103 = 1518155) B1518155
theorem B1012111 : Blo 1008601 1012111 := bstep (se 1 (by rfl) ⟨759083, by rfl⟩ : syracuseStep 1012111 = 1518167) B1518167
theorem B1012155 : Blo 1008601 1012155 := bstep (se 1 (by rfl) ⟨759116, by rfl⟩ : syracuseStep 1012155 = 1518233) B1518233
theorem B1012231 : Blo 1008601 1012231 := bstep (se 1 (by rfl) ⟨759173, by rfl⟩ : syracuseStep 1012231 = 1518347) B1518347
theorem B1012239 : Blo 1008601 1012239 := bstep (se 1 (by rfl) ⟨759179, by rfl⟩ : syracuseStep 1012239 = 1518359) B1518359
theorem B2880029 : Blo 1008601 2880029 := bstep (se 3 (by rfl) ⟨540005, by rfl⟩ : syracuseStep 2880029 = 1080011) B1080011
theorem B1012283 : Blo 1008601 1012283 := bstep (se 1 (by rfl) ⟨759212, by rfl⟩ : syracuseStep 1012283 = 1518425) B1518425
theorem B3404375 : Blo 1008601 3404375 := bstep (se 1 (by rfl) ⟨2553281, by rfl⟩ : syracuseStep 3404375 = 5106563) B5106563
theorem B1012359 : Blo 1008601 1012359 := bstep (se 1 (by rfl) ⟨759269, by rfl⟩ : syracuseStep 1012359 = 1518539) B1518539
theorem B1012367 : Blo 1008601 1012367 := bstep (se 1 (by rfl) ⟨759275, by rfl⟩ : syracuseStep 1012367 = 1518551) B1518551
theorem B1012411 : Blo 1008601 1012411 := bstep (se 1 (by rfl) ⟨759308, by rfl⟩ : syracuseStep 1012411 = 1518617) B1518617
theorem B12972737 : Blo 1008601 12972737 := bstep (se 2 (by rfl) ⟨4864776, by rfl⟩ : syracuseStep 12972737 = 9729553) B9729553
theorem B1012487 : Blo 1008601 1012487 := bstep (se 1 (by rfl) ⟨759365, by rfl⟩ : syracuseStep 1012487 = 1518731) B1518731
theorem B1012495 : Blo 1008601 1012495 := bstep (se 1 (by rfl) ⟨759371, by rfl⟩ : syracuseStep 1012495 = 1518743) B1518743
theorem B3830561 : Blo 1008601 3830561 := bstep (se 2 (by rfl) ⟨1436460, by rfl⟩ : syracuseStep 3830561 = 2872921) B2872921
theorem B1012539 : Blo 1008601 1012539 := bstep (se 1 (by rfl) ⟨759404, by rfl⟩ : syracuseStep 1012539 = 1518809) B1518809
theorem B2159561 : Blo 1008601 2159561 := bstep (se 2 (by rfl) ⟨809835, by rfl⟩ : syracuseStep 2159561 = 1619671) B1619671
theorem B1438727 : Blo 1008601 1438727 := bstep (se 1 (by rfl) ⟨1079045, by rfl⟩ : syracuseStep 1438727 = 2158091) B2158091
theorem B3404861 : Blo 1008601 3404861 := bstep (se 3 (by rfl) ⟨638411, by rfl⟩ : syracuseStep 3404861 = 1276823) B1276823
theorem B1438921 : Blo 1008601 1438921 := bstep (se 2 (by rfl) ⟨539595, by rfl⟩ : syracuseStep 1438921 = 1079191) B1079191
theorem B5108993 : Blo 1008601 5108993 := bstep (se 2 (by rfl) ⟨1915872, by rfl⟩ : syracuseStep 5108993 = 3831745) B3831745
theorem B5764385 : Blo 1008601 5764385 := bstep (se 2 (by rfl) ⟨2161644, by rfl⟩ : syracuseStep 5764385 = 4323289) B4323289
theorem B2553241 : Blo 1008601 2553241 := bstep (se 2 (by rfl) ⟨957465, by rfl⟩ : syracuseStep 2553241 = 1914931) B1914931
theorem B2553403 : Blo 1008601 2553403 := bstep (se 1 (by rfl) ⟨1915052, by rfl⟩ : syracuseStep 2553403 = 3830105) B3830105
theorem B2553545 : Blo 1008601 2553545 := bstep (se 2 (by rfl) ⟨957579, by rfl⟩ : syracuseStep 2553545 = 1915159) B1915159
theorem B3831533 : Blo 1008601 3831533 := bstep (se 3 (by rfl) ⟨718412, by rfl⟩ : syracuseStep 3831533 = 1436825) B1436825
theorem B1439479 : Blo 1008601 1439479 := bstep (se 1 (by rfl) ⟨1079609, by rfl⟩ : syracuseStep 1439479 = 2159219) B2159219
theorem B9729827 : Blo 1008601 9729827 := bstep (se 1 (by rfl) ⟨7297370, by rfl⟩ : syracuseStep 9729827 = 14594741) B14594741
theorem B2160569 : Blo 1008601 2160569 := bstep (se 2 (by rfl) ⟨810213, by rfl⟩ : syracuseStep 2160569 = 1620427) B1620427
theorem B2553889 : Blo 1008601 2553889 := bstep (se 2 (by rfl) ⟨957708, by rfl⟩ : syracuseStep 2553889 = 1915417) B1915417
theorem B5109803 : Blo 1008601 5109803 := bstep (se 1 (by rfl) ⟨3832352, by rfl⟩ : syracuseStep 5109803 = 7664705) B7664705
theorem B3242045 : Blo 1008601 3242045 := bstep (se 3 (by rfl) ⟨607883, by rfl⟩ : syracuseStep 3242045 = 1215767) B1215767
theorem B8648765 : Blo 1008601 8648765 := bstep (se 3 (by rfl) ⟨1621643, by rfl⟩ : syracuseStep 8648765 = 3243287) B3243287
theorem B1702073 : Blo 1008601 1702073 := bstep (se 2 (by rfl) ⟨638277, by rfl⟩ : syracuseStep 1702073 = 1276555) B1276555
theorem B12613877 : Blo 1008601 12613877 := bstep (se 5 (by rfl) ⟨591275, by rfl⟩ : syracuseStep 12613877 = 1182551) B1182551
theorem B2160911 : Blo 1008601 2160911 := bstep (se 1 (by rfl) ⟨1620683, by rfl⟩ : syracuseStep 2160911 = 3241367) B3241367
theorem B24574225 : Blo 1008601 24574225 := bstep (se 2 (by rfl) ⟨9215334, by rfl⟩ : syracuseStep 24574225 = 18430669) B18430669
theorem B1538347 : Blo 1008601 1538347 := bstep (se 1 (by rfl) ⟨1153760, by rfl⟩ : syracuseStep 1538347 = 2307521) B2307521
theorem B3832217 : Blo 1008601 3832217 := bstep (se 2 (by rfl) ⟨1437081, by rfl⟩ : syracuseStep 3832217 = 2874163) B2874163
theorem B3406265 : Blo 1008601 3406265 := bstep (se 2 (by rfl) ⟨1277349, by rfl⟩ : syracuseStep 3406265 = 2554699) B2554699
theorem B1440185 : Blo 1008601 1440185 := bstep (se 2 (by rfl) ⟨540069, by rfl⟩ : syracuseStep 1440185 = 1080139) B1080139
theorem B1440271 : Blo 1008601 1440271 := bstep (se 1 (by rfl) ⟨1080203, by rfl⟩ : syracuseStep 1440271 = 2160407) B2160407
theorem B1440299 : Blo 1008601 1440299 := bstep (se 1 (by rfl) ⟨1080224, by rfl⟩ : syracuseStep 1440299 = 2160449) B2160449
theorem B2554487 : Blo 1008601 2554487 := bstep (se 1 (by rfl) ⟨1915865, by rfl⟩ : syracuseStep 2554487 = 3831731) B3831731
theorem B1079951 : Blo 1008601 1079951 := bstep (se 1 (by rfl) ⟨809963, by rfl⟩ : syracuseStep 1079951 = 1619927) B1619927
theorem B12286721 : Blo 1008601 12286721 := bstep (se 2 (by rfl) ⟨4607520, by rfl⟩ : syracuseStep 12286721 = 9215041) B9215041
theorem B1702775 : Blo 1008601 1702775 := bstep (se 1 (by rfl) ⟨1277081, by rfl⟩ : syracuseStep 1702775 = 2554163) B2554163
theorem B3406859 : Blo 1008601 3406859 := bstep (se 1 (by rfl) ⟨2555144, by rfl⟩ : syracuseStep 3406859 = 5110289) B5110289
theorem B2882603 : Blo 1008601 2882603 := bstep (se 1 (by rfl) ⟨2161952, by rfl⟩ : syracuseStep 2882603 = 4323905) B4323905
theorem B10910807 : Blo 1008601 10910807 := bstep (se 1 (by rfl) ⟨8183105, by rfl⟩ : syracuseStep 10910807 = 16366211) B16366211
theorem B3406967 : Blo 1008601 3406967 := bstep (se 1 (by rfl) ⟨2555225, by rfl⟩ : syracuseStep 3406967 = 5110451) B5110451
theorem B2161799 : Blo 1008601 2161799 := bstep (se 1 (by rfl) ⟨1621349, by rfl⟩ : syracuseStep 2161799 = 3242699) B3242699
theorem B4324589 : Blo 1008601 4324589 := bstep (se 3 (by rfl) ⟨810860, by rfl⟩ : syracuseStep 4324589 = 1621721) B1621721
theorem B1080583 : Blo 1008601 1080583 := bstep (se 1 (by rfl) ⟨810437, by rfl⟩ : syracuseStep 1080583 = 1620875) B1620875
theorem B1703227 : Blo 1008601 1703227 := bstep (se 1 (by rfl) ⟨1277420, by rfl⟩ : syracuseStep 1703227 = 2554841) B2554841
theorem B5111099 : Blo 1008601 5111099 := bstep (se 1 (by rfl) ⟨3833324, by rfl⟩ : syracuseStep 5111099 = 7666649) B7666649
theorem B3833203 : Blo 1008601 3833203 := bstep (se 1 (by rfl) ⟨2874902, by rfl⟩ : syracuseStep 3833203 = 5749805) B5749805
theorem B1703369 : Blo 1008601 1703369 := bstep (se 2 (by rfl) ⟨638763, by rfl⟩ : syracuseStep 1703369 = 1277527) B1277527
theorem B5111261 : Blo 1008601 5111261 := bstep (se 3 (by rfl) ⟨958361, by rfl⟩ : syracuseStep 5111261 = 1916723) B1916723
theorem B46759427 : Blo 1008601 46759427 := bstep (se 1 (by rfl) ⟨35069570, by rfl⟩ : syracuseStep 46759427 = 70139141) B70139141
theorem B2424335 : Blo 1008601 2424335 := bstep (se 1 (by rfl) ⟨1818251, by rfl⟩ : syracuseStep 2424335 = 3636503) B3636503
theorem B1539599 : Blo 1008601 1539599 := bstep (se 1 (by rfl) ⟨1154699, by rfl⟩ : syracuseStep 1539599 = 2309399) B2309399
theorem B2162209 : Blo 1008601 2162209 := bstep (se 2 (by rfl) ⟨810828, by rfl⟩ : syracuseStep 2162209 = 1621657) B1621657
theorem B10944193 : Blo 1008601 10944193 := bstep (se 2 (by rfl) ⟨4104072, by rfl⟩ : syracuseStep 10944193 = 8208145) B8208145
theorem B3407561 : Blo 1008601 3407561 := bstep (se 2 (by rfl) ⟨1277835, by rfl⟩ : syracuseStep 3407561 = 2555671) B2555671
theorem B5111585 : Blo 1008601 5111585 := bstep (se 2 (by rfl) ⟨1916844, by rfl⟩ : syracuseStep 5111585 = 3833689) B3833689
theorem B2162465 : Blo 1008601 2162465 := bstep (se 2 (by rfl) ⟨810924, by rfl⟩ : syracuseStep 2162465 = 1621849) B1621849
theorem B2162551 : Blo 1008601 2162551 := bstep (se 1 (by rfl) ⟨1621913, by rfl⟩ : syracuseStep 2162551 = 3243827) B3243827
theorem B2555783 : Blo 1008601 2555783 := bstep (se 1 (by rfl) ⟨1916837, by rfl⟩ : syracuseStep 2555783 = 3833675) B3833675
theorem B1212331 : Blo 1008601 1212331 := bstep (se 1 (by rfl) ⟨909248, by rfl⟩ : syracuseStep 1212331 = 1818497) B1818497
theorem B2555833 : Blo 1008601 2555833 := bstep (se 2 (by rfl) ⟨958437, by rfl⟩ : syracuseStep 2555833 = 1916875) B1916875
theorem B27688907 : Blo 1008601 27688907 := bstep (se 1 (by rfl) ⟨20766680, by rfl⟩ : syracuseStep 27688907 = 41533361) B41533361
theorem B6225977 : Blo 1008601 6225977 := bstep (se 2 (by rfl) ⟨2334741, by rfl⟩ : syracuseStep 6225977 = 4669483) B4669483
theorem B8618147 : Blo 1008601 8618147 := bstep (se 1 (by rfl) ⟨6463610, by rfl⟩ : syracuseStep 8618147 = 12927221) B12927221
theorem B1638599 : Blo 1008601 1638599 := bstep (se 1 (by rfl) ⟨1228949, by rfl⟩ : syracuseStep 1638599 = 2457899) B2457899
theorem B1704287 : Blo 1008601 1704287 := bstep (se 1 (by rfl) ⟨1278215, by rfl⟩ : syracuseStep 1704287 = 2556431) B2556431
theorem B3408371 : Blo 1008601 3408371 := bstep (se 1 (by rfl) ⟨2556278, by rfl⟩ : syracuseStep 3408371 = 5112557) B5112557
theorem B3277345 : Blo 1008601 3277345 := bstep (se 2 (by rfl) ⟨1229004, by rfl⟩ : syracuseStep 3277345 = 2458009) B2458009
theorem B2458475 : Blo 1008601 2458475 := bstep (se 1 (by rfl) ⟨1843856, by rfl⟩ : syracuseStep 2458475 = 3687713) B3687713
theorem B1704847 : Blo 1008601 1704847 := bstep (se 1 (by rfl) ⟨1278635, by rfl⟩ : syracuseStep 1704847 = 2557271) B2557271
theorem B3408911 : Blo 1008601 3408911 := bstep (se 1 (by rfl) ⟨2556683, by rfl⟩ : syracuseStep 3408911 = 5113367) B5113367
theorem B2556947 : Blo 1008601 2556947 := bstep (se 1 (by rfl) ⟨1917710, by rfl⟩ : syracuseStep 2556947 = 3835421) B3835421
theorem B3835147 : Blo 1008601 3835147 := bstep (se 1 (by rfl) ⟨2876360, by rfl⟩ : syracuseStep 3835147 = 5752721) B5752721
theorem B1279415 : Blo 1008601 1279415 := bstep (se 1 (by rfl) ⟨959561, by rfl⟩ : syracuseStep 1279415 = 1919123) B1919123
theorem B2557403 : Blo 1008601 2557403 := bstep (se 1 (by rfl) ⟨1918052, by rfl⟩ : syracuseStep 2557403 = 3836105) B3836105
theorem B1705529 : Blo 1008601 1705529 := bstep (se 2 (by rfl) ⟨639573, by rfl⟩ : syracuseStep 1705529 = 1279147) B1279147
theorem B3835451 : Blo 1008601 3835451 := bstep (se 1 (by rfl) ⟨2876588, by rfl⟩ : syracuseStep 3835451 = 5753177) B5753177
theorem B1279567 : Blo 1008601 1279567 := bstep (se 1 (by rfl) ⟨959675, by rfl⟩ : syracuseStep 1279567 = 1919351) B1919351
theorem B3409505 : Blo 1008601 3409505 := bstep (se 2 (by rfl) ⟨1278564, by rfl⟩ : syracuseStep 3409505 = 2557129) B2557129
theorem B11503619 : Blo 1008601 11503619 := bstep (se 1 (by rfl) ⟨8627714, by rfl⟩ : syracuseStep 11503619 = 17255429) B17255429
theorem B1706231 : Blo 1008601 1706231 := bstep (se 1 (by rfl) ⟨1279673, by rfl⟩ : syracuseStep 1706231 = 2559347) B2559347
theorem B4098593 : Blo 1008601 4098593 := bstep (se 2 (by rfl) ⟨1536972, by rfl⟩ : syracuseStep 4098593 = 3073945) B3073945
theorem B1706575 : Blo 1008601 1706575 := bstep (se 1 (by rfl) ⟨1279931, by rfl⟩ : syracuseStep 1706575 = 2559863) B2559863
theorem B2558587 : Blo 1008601 2558587 := bstep (se 1 (by rfl) ⟨1918940, by rfl⟩ : syracuseStep 2558587 = 3837881) B3837881
theorem B3836605 : Blo 1008601 3836605 := bstep (se 3 (by rfl) ⟨719363, by rfl⟩ : syracuseStep 3836605 = 1438727) B1438727
theorem B1280711 : Blo 1008601 1280711 := bstep (se 1 (by rfl) ⟨960533, by rfl⟩ : syracuseStep 1280711 = 1921067) B1921067
theorem B1706825 : Blo 1008601 1706825 := bstep (se 2 (by rfl) ⟨640059, by rfl⟩ : syracuseStep 1706825 = 1280119) B1280119
theorem B1280863 : Blo 1008601 1280863 := bstep (se 1 (by rfl) ⟨960647, by rfl⟩ : syracuseStep 1280863 = 1921295) B1921295
theorem B3410963 : Blo 1008601 3410963 := bstep (se 1 (by rfl) ⟨2558222, by rfl⟩ : syracuseStep 3410963 = 5116445) B5116445
theorem B7015619 : Blo 1008601 7015619 := bstep (se 1 (by rfl) ⟨5261714, by rfl⟩ : syracuseStep 7015619 = 10523429) B10523429
theorem B1707257 : Blo 1008601 1707257 := bstep (se 2 (by rfl) ⟨640221, by rfl⟩ : syracuseStep 1707257 = 1280443) B1280443
theorem B6917413 : Blo 1008601 6917413 := bstep (se 4 (by rfl) ⟨648507, by rfl⟩ : syracuseStep 6917413 = 1297015) B1297015
theorem B3411287 : Blo 1008601 3411287 := bstep (se 1 (by rfl) ⟨2558465, by rfl⟩ : syracuseStep 3411287 = 5116931) B5116931
theorem B1707439 : Blo 1008601 1707439 := bstep (se 1 (by rfl) ⟨1280579, by rfl⟩ : syracuseStep 1707439 = 2561159) B2561159
theorem B1707527 : Blo 1008601 1707527 := bstep (se 1 (by rfl) ⟨1280645, by rfl⟩ : syracuseStep 1707527 = 2561291) B2561291
theorem B3837563 : Blo 1008601 3837563 := bstep (se 1 (by rfl) ⟨2878172, by rfl⟩ : syracuseStep 3837563 = 5756345) B5756345
theorem B1707871 : Blo 1008601 1707871 := bstep (se 1 (by rfl) ⟨1280903, by rfl⟩ : syracuseStep 1707871 = 2561807) B2561807
theorem B2461601 : Blo 1008601 2461601 := bstep (se 2 (by rfl) ⟨923100, by rfl⟩ : syracuseStep 2461601 = 1846201) B1846201
theorem B1707959 : Blo 1008601 1707959 := bstep (se 1 (by rfl) ⟨1280969, by rfl⟩ : syracuseStep 1707959 = 2561939) B2561939
theorem B7278599 : Blo 1008601 7278599 := bstep (se 1 (by rfl) ⟨5458949, by rfl⟩ : syracuseStep 7278599 = 10917899) B10917899
theorem B3838337 : Blo 1008601 3838337 := bstep (se 2 (by rfl) ⟨1439376, by rfl⟩ : syracuseStep 3838337 = 2878753) B2878753
theorem B3412367 : Blo 1008601 3412367 := bstep (se 1 (by rfl) ⟨2559275, by rfl⟩ : syracuseStep 3412367 = 5118551) B5118551
theorem B1708553 : Blo 1008601 1708553 := bstep (se 2 (by rfl) ⟨640707, by rfl⟩ : syracuseStep 1708553 = 1281415) B1281415
theorem B6558241 : Blo 1008601 6558241 := bstep (se 2 (by rfl) ⟨2459340, by rfl⟩ : syracuseStep 6558241 = 4918681) B4918681
theorem B1708715 : Blo 1008601 1708715 := bstep (se 1 (by rfl) ⟨1281536, by rfl⟩ : syracuseStep 1708715 = 2563073) B2563073
theorem B3412691 : Blo 1008601 3412691 := bstep (se 1 (by rfl) ⟨2559518, by rfl⟩ : syracuseStep 3412691 = 5119037) B5119037
theorem B2429689 : Blo 1008601 2429689 := bstep (se 2 (by rfl) ⟨911133, by rfl⟩ : syracuseStep 2429689 = 1822267) B1822267
theorem B4100959 : Blo 1008601 4100959 := bstep (se 1 (by rfl) ⟨3075719, by rfl⟩ : syracuseStep 4100959 = 6151439) B6151439
theorem B1512923 : Blo 1008601 1512923 := bstep (se 1 (by rfl) ⟨1134692, by rfl⟩ : syracuseStep 1512923 = 2269385) B2269385
theorem B16422389 : Blo 1008601 16422389 := bstep (se 5 (by rfl) ⟨769799, by rfl⟩ : syracuseStep 16422389 = 1539599) B1539599
theorem B3839521 : Blo 1008601 3839521 := bstep (se 2 (by rfl) ⟨1439820, by rfl⟩ : syracuseStep 3839521 = 2879641) B2879641
theorem B5117579 : Blo 1008601 5117579 := bstep (se 1 (by rfl) ⟨3838184, by rfl⟩ : syracuseStep 5117579 = 7676369) B7676369
theorem B1971911 : Blo 1008601 1971911 := bstep (se 1 (by rfl) ⟨1478933, by rfl⟩ : syracuseStep 1971911 = 2957867) B2957867
theorem B3413879 : Blo 1008601 3413879 := bstep (se 1 (by rfl) ⟨2560409, by rfl⟩ : syracuseStep 3413879 = 5120819) B5120819
theorem B1513391 : Blo 1008601 1513391 := bstep (se 1 (by rfl) ⟨1135043, by rfl⟩ : syracuseStep 1513391 = 2270087) B2270087
theorem B3840007 : Blo 1008601 3840007 := bstep (se 1 (by rfl) ⟨2880005, by rfl⟩ : syracuseStep 3840007 = 5760011) B5760011
theorem B1513481 : Blo 1008601 1513481 := bstep (se 2 (by rfl) ⟨567555, by rfl⟩ : syracuseStep 1513481 = 1135111) B1135111
theorem B1513511 : Blo 1008601 1513511 := bstep (se 1 (by rfl) ⟨1135133, by rfl⟩ : syracuseStep 1513511 = 2270267) B2270267
theorem B3414095 : Blo 1008601 3414095 := bstep (se 1 (by rfl) ⟨2560571, by rfl⟩ : syracuseStep 3414095 = 5121143) B5121143
theorem B1513595 : Blo 1008601 1513595 := bstep (se 1 (by rfl) ⟨1135196, by rfl⟩ : syracuseStep 1513595 = 2270393) B2270393
theorem B1513721 : Blo 1008601 1513721 := bstep (se 2 (by rfl) ⟨567645, by rfl⟩ : syracuseStep 1513721 = 1135291) B1135291
theorem B1513823 : Blo 1008601 1513823 := bstep (se 1 (by rfl) ⟨1135367, by rfl⟩ : syracuseStep 1513823 = 2270735) B2270735
theorem B1513835 : Blo 1008601 1513835 := bstep (se 1 (by rfl) ⟨1135376, by rfl⟩ : syracuseStep 1513835 = 2270753) B2270753
theorem B3414473 : Blo 1008601 3414473 := bstep (se 2 (by rfl) ⟨1280427, by rfl⟩ : syracuseStep 3414473 = 2560855) B2560855
theorem B3840493 : Blo 1008601 3840493 := bstep (se 3 (by rfl) ⟨720092, by rfl⟩ : syracuseStep 3840493 = 1440185) B1440185
theorem B1514063 : Blo 1008601 1514063 := bstep (se 1 (by rfl) ⟨1135547, by rfl⟩ : syracuseStep 1514063 = 2271095) B2271095
theorem B1514183 : Blo 1008601 1514183 := bstep (se 1 (by rfl) ⟨1135637, by rfl⟩ : syracuseStep 1514183 = 2271275) B2271275
theorem B3414743 : Blo 1008601 3414743 := bstep (se 1 (by rfl) ⟨2561057, by rfl⟩ : syracuseStep 3414743 = 5122115) B5122115
theorem B3840797 : Blo 1008601 3840797 := bstep (se 3 (by rfl) ⟨720149, by rfl⟩ : syracuseStep 3840797 = 1440299) B1440299
theorem B14588747 : Blo 1008601 14588747 := bstep (se 1 (by rfl) ⟨10941560, by rfl⟩ : syracuseStep 14588747 = 21883121) B21883121
theorem B2562911 : Blo 1008601 2562911 := bstep (se 1 (by rfl) ⟨1922183, by rfl⟩ : syracuseStep 2562911 = 3844367) B3844367
theorem B1514345 : Blo 1008601 1514345 := bstep (se 2 (by rfl) ⟨567879, by rfl⟩ : syracuseStep 1514345 = 1135759) B1135759
theorem B3414959 : Blo 1008601 3414959 := bstep (se 1 (by rfl) ⟨2561219, by rfl⟩ : syracuseStep 3414959 = 5122439) B5122439
theorem B1514423 : Blo 1008601 1514423 := bstep (se 1 (by rfl) ⟨1135817, by rfl⟩ : syracuseStep 1514423 = 2271635) B2271635
theorem B2431927 : Blo 1008601 2431927 := bstep (se 1 (by rfl) ⟨1823945, by rfl⟩ : syracuseStep 2431927 = 3647891) B3647891
theorem B1514459 : Blo 1008601 1514459 := bstep (se 1 (by rfl) ⟨1135844, by rfl⟩ : syracuseStep 1514459 = 2271689) B2271689
theorem B14196005 : Blo 1008601 14196005 := bstep (se 4 (by rfl) ⟨1330875, by rfl⟩ : syracuseStep 14196005 = 2661751) B2661751
theorem B9706877 : Blo 1008601 9706877 := bstep (se 3 (by rfl) ⟨1820039, by rfl⟩ : syracuseStep 9706877 = 3640079) B3640079
theorem B1514927 : Blo 1008601 1514927 := bstep (se 1 (by rfl) ⟨1136195, by rfl⟩ : syracuseStep 1514927 = 2272391) B2272391
theorem B1515017 : Blo 1008601 1515017 := bstep (se 2 (by rfl) ⟨568131, by rfl⟩ : syracuseStep 1515017 = 1136263) B1136263
theorem B1515047 : Blo 1008601 1515047 := bstep (se 1 (by rfl) ⟨1136285, by rfl⟩ : syracuseStep 1515047 = 2272571) B2272571
theorem B1515131 : Blo 1008601 1515131 := bstep (se 1 (by rfl) ⟨1136348, by rfl⟩ : syracuseStep 1515131 = 2272697) B2272697
theorem B6659729 : Blo 1008601 6659729 := bstep (se 2 (by rfl) ⟨2497398, by rfl⟩ : syracuseStep 6659729 = 4994797) B4994797
theorem B4857533 : Blo 1008601 4857533 := bstep (se 3 (by rfl) ⟨910787, by rfl⟩ : syracuseStep 4857533 = 1821575) B1821575
theorem B1515257 : Blo 1008601 1515257 := bstep (se 2 (by rfl) ⟨568221, by rfl⟩ : syracuseStep 1515257 = 1136443) B1136443
theorem B59121413 : Blo 1008601 59121413 := bstep (se 4 (by rfl) ⟨5542632, by rfl⟩ : syracuseStep 59121413 = 11085265) B11085265
theorem B1515359 : Blo 1008601 1515359 := bstep (se 1 (by rfl) ⟨1136519, by rfl⟩ : syracuseStep 1515359 = 2273039) B2273039
theorem B1515371 : Blo 1008601 1515371 := bstep (se 1 (by rfl) ⟨1136528, by rfl⟩ : syracuseStep 1515371 = 2273057) B2273057
theorem B2465849 : Blo 1008601 2465849 := bstep (se 2 (by rfl) ⟨924693, by rfl⟩ : syracuseStep 2465849 = 1849387) B1849387
theorem B1941583 : Blo 1008601 1941583 := bstep (se 1 (by rfl) ⟨1456187, by rfl⟩ : syracuseStep 1941583 = 2912375) B2912375
theorem B1515599 : Blo 1008601 1515599 := bstep (se 1 (by rfl) ⟨1136699, by rfl⟩ : syracuseStep 1515599 = 2273399) B2273399
theorem B4431953 : Blo 1008601 4431953 := bstep (se 2 (by rfl) ⟨1661982, by rfl⟩ : syracuseStep 4431953 = 3323965) B3323965
theorem B1515719 : Blo 1008601 1515719 := bstep (se 1 (by rfl) ⟨1136789, by rfl⟩ : syracuseStep 1515719 = 2273579) B2273579
theorem B1515881 : Blo 1008601 1515881 := bstep (se 2 (by rfl) ⟨568455, by rfl⟩ : syracuseStep 1515881 = 1136911) B1136911
theorem B2269583 : Blo 1008601 2269583 := bstep (se 1 (by rfl) ⟨1702187, by rfl⟩ : syracuseStep 2269583 = 3404375) B3404375
theorem B1515959 : Blo 1008601 1515959 := bstep (se 1 (by rfl) ⟨1136969, by rfl⟩ : syracuseStep 1515959 = 2273939) B2273939
theorem B1515995 : Blo 1008601 1515995 := bstep (se 1 (by rfl) ⟨1136996, by rfl⟩ : syracuseStep 1515995 = 2273993) B2273993
theorem B2269907 : Blo 1008601 2269907 := bstep (se 1 (by rfl) ⟨1702430, by rfl⟩ : syracuseStep 2269907 = 3404861) B3404861
theorem B3842923 : Blo 1008601 3842923 := bstep (se 1 (by rfl) ⟨2882192, by rfl⟩ : syracuseStep 3842923 = 5764385) B5764385
theorem B1516463 : Blo 1008601 1516463 := bstep (se 1 (by rfl) ⟨1137347, by rfl⟩ : syracuseStep 1516463 = 2274695) B2274695
theorem B7676855 : Blo 1008601 7676855 := bstep (se 1 (by rfl) ⟨5757641, by rfl⟩ : syracuseStep 7676855 = 11515283) B11515283
theorem B1516553 : Blo 1008601 1516553 := bstep (se 2 (by rfl) ⟨568707, by rfl⟩ : syracuseStep 1516553 = 1137415) B1137415
theorem B1516583 : Blo 1008601 1516583 := bstep (se 1 (by rfl) ⟨1137437, by rfl⟩ : syracuseStep 1516583 = 2274875) B2274875
theorem B1516667 : Blo 1008601 1516667 := bstep (se 1 (by rfl) ⟨1137500, by rfl⟩ : syracuseStep 1516667 = 2275001) B2275001
theorem B10364057 : Blo 1008601 10364057 := bstep (se 2 (by rfl) ⟨3886521, by rfl⟩ : syracuseStep 10364057 = 7773043) B7773043
theorem B3417335 : Blo 1008601 3417335 := bstep (se 1 (by rfl) ⟨2563001, by rfl⟩ : syracuseStep 3417335 = 5126003) B5126003
theorem B1516793 : Blo 1008601 1516793 := bstep (se 2 (by rfl) ⟨568797, by rfl⟩ : syracuseStep 1516793 = 1137595) B1137595
theorem B1516895 : Blo 1008601 1516895 := bstep (se 1 (by rfl) ⟨1137671, by rfl⟩ : syracuseStep 1516895 = 2275343) B2275343
theorem B1516907 : Blo 1008601 1516907 := bstep (se 1 (by rfl) ⟨1137680, by rfl⟩ : syracuseStep 1516907 = 2275361) B2275361
theorem B6464893 : Blo 1008601 6464893 := bstep (se 3 (by rfl) ⟨1212167, by rfl⟩ : syracuseStep 6464893 = 2424335) B2424335
theorem B1517135 : Blo 1008601 1517135 := bstep (se 1 (by rfl) ⟨1137851, by rfl⟩ : syracuseStep 1517135 = 2275703) B2275703
theorem B1943137 : Blo 1008601 1943137 := bstep (se 2 (by rfl) ⟨728676, by rfl⟩ : syracuseStep 1943137 = 1457353) B1457353
theorem B2270843 : Blo 1008601 2270843 := bstep (se 1 (by rfl) ⟨1703132, by rfl⟩ : syracuseStep 2270843 = 3406265) B3406265
theorem B1517255 : Blo 1008601 1517255 := bstep (se 1 (by rfl) ⟨1137941, by rfl⟩ : syracuseStep 1517255 = 2275883) B2275883
theorem B2270969 : Blo 1008601 2270969 := bstep (se 2 (by rfl) ⟨851613, by rfl⟩ : syracuseStep 2270969 = 1703227) B1703227
theorem B2729801 : Blo 1008601 2729801 := bstep (se 2 (by rfl) ⟨1023675, by rfl⟩ : syracuseStep 2729801 = 2047351) B2047351
theorem B1517417 : Blo 1008601 1517417 := bstep (se 2 (by rfl) ⟨569031, by rfl⟩ : syracuseStep 1517417 = 1138063) B1138063
theorem B5121953 : Blo 1008601 5121953 := bstep (se 2 (by rfl) ⟨1920732, by rfl⟩ : syracuseStep 5121953 = 3841465) B3841465
theorem B1517495 : Blo 1008601 1517495 := bstep (se 1 (by rfl) ⟨1138121, by rfl⟩ : syracuseStep 1517495 = 2276243) B2276243
theorem B1517531 : Blo 1008601 1517531 := bstep (se 1 (by rfl) ⟨1138148, by rfl⟩ : syracuseStep 1517531 = 2276297) B2276297
theorem B2271239 : Blo 1008601 2271239 := bstep (se 1 (by rfl) ⟨1703429, by rfl⟩ : syracuseStep 2271239 = 3406859) B3406859
theorem B2271311 : Blo 1008601 2271311 := bstep (se 1 (by rfl) ⟨1703483, by rfl⟩ : syracuseStep 2271311 = 3406967) B3406967
theorem B4859993 : Blo 1008601 4859993 := bstep (se 2 (by rfl) ⟨1822497, by rfl⟩ : syracuseStep 4859993 = 3644995) B3644995
theorem B14592257 : Blo 1008601 14592257 := bstep (se 2 (by rfl) ⟨5472096, by rfl⟩ : syracuseStep 14592257 = 10944193) B10944193
theorem B31172951 : Blo 1008601 31172951 := bstep (se 1 (by rfl) ⟨23379713, by rfl⟩ : syracuseStep 31172951 = 46759427) B46759427
theorem B7678313 : Blo 1008601 7678313 := bstep (se 2 (by rfl) ⟨2879367, by rfl⟩ : syracuseStep 7678313 = 5758735) B5758735
theorem B112208273 : Blo 1008601 112208273 := bstep (se 2 (by rfl) ⟨42078102, by rfl⟩ : syracuseStep 112208273 = 84156205) B84156205
theorem B1517999 : Blo 1008601 1517999 := bstep (se 1 (by rfl) ⟨1138499, by rfl⟩ : syracuseStep 1517999 = 2276999) B2276999
theorem B2271707 : Blo 1008601 2271707 := bstep (se 1 (by rfl) ⟨1703780, by rfl⟩ : syracuseStep 2271707 = 3407561) B3407561
theorem B1518089 : Blo 1008601 1518089 := bstep (se 2 (by rfl) ⟨569283, by rfl⟩ : syracuseStep 1518089 = 1138567) B1138567
theorem B1518119 : Blo 1008601 1518119 := bstep (se 1 (by rfl) ⟨1138589, by rfl⟩ : syracuseStep 1518119 = 2277179) B2277179
theorem B1616441 : Blo 1008601 1616441 := bstep (se 2 (by rfl) ⟨606165, by rfl⟩ : syracuseStep 1616441 = 1212331) B1212331
theorem B1518203 : Blo 1008601 1518203 := bstep (se 1 (by rfl) ⟨1138652, by rfl⟩ : syracuseStep 1518203 = 2277305) B2277305
theorem B18459271 : Blo 1008601 18459271 := bstep (se 1 (by rfl) ⟨13844453, by rfl⟩ : syracuseStep 18459271 = 27688907) B27688907
theorem B4926161 : Blo 1008601 4926161 := bstep (se 2 (by rfl) ⟨1847310, by rfl⟩ : syracuseStep 4926161 = 3694621) B3694621
theorem B1518329 : Blo 1008601 1518329 := bstep (se 2 (by rfl) ⟨569373, by rfl⟩ : syracuseStep 1518329 = 1138747) B1138747
theorem B1518431 : Blo 1008601 1518431 := bstep (se 1 (by rfl) ⟨1138823, by rfl⟩ : syracuseStep 1518431 = 2277647) B2277647
theorem B1518443 : Blo 1008601 1518443 := bstep (se 1 (by rfl) ⟨1138832, by rfl⟩ : syracuseStep 1518443 = 2277665) B2277665
theorem B2304929 : Blo 1008601 2304929 := bstep (se 2 (by rfl) ⟨864348, by rfl⟩ : syracuseStep 2304929 = 1728697) B1728697
theorem B2272175 : Blo 1008601 2272175 := bstep (se 1 (by rfl) ⟨1704131, by rfl⟩ : syracuseStep 2272175 = 3408263) B3408263
theorem B3648527 : Blo 1008601 3648527 := bstep (se 1 (by rfl) ⟨2736395, by rfl⟩ : syracuseStep 3648527 = 5472791) B5472791
theorem B26225687 : Blo 1008601 26225687 := bstep (se 1 (by rfl) ⟨19669265, by rfl⟩ : syracuseStep 26225687 = 39338531) B39338531
theorem B1518671 : Blo 1008601 1518671 := bstep (se 1 (by rfl) ⟨1139003, by rfl⟩ : syracuseStep 1518671 = 2278007) B2278007
theorem B2272427 : Blo 1008601 2272427 := bstep (se 1 (by rfl) ⟨1704320, by rfl⟩ : syracuseStep 2272427 = 3408641) B3408641
theorem B1518791 : Blo 1008601 1518791 := bstep (se 1 (by rfl) ⟨1139093, by rfl⟩ : syracuseStep 1518791 = 2278187) B2278187
theorem B6925733 : Blo 1008601 6925733 := bstep (se 4 (by rfl) ⟨649287, by rfl⟩ : syracuseStep 6925733 = 1298575) B1298575
theorem B5746139 : Blo 1008601 5746139 := bstep (se 1 (by rfl) ⟨4309604, by rfl⟩ : syracuseStep 5746139 = 8619209) B8619209
theorem B2731529 : Blo 1008601 2731529 := bstep (se 2 (by rfl) ⟨1024323, by rfl⟩ : syracuseStep 2731529 = 2048647) B2048647
theorem B2272967 : Blo 1008601 2272967 := bstep (se 1 (by rfl) ⟨1704725, by rfl⟩ : syracuseStep 2272967 = 3409451) B3409451
theorem B5844695 : Blo 1008601 5844695 := bstep (se 1 (by rfl) ⟨4383521, by rfl⟩ : syracuseStep 5844695 = 8767043) B8767043
theorem B7680257 : Blo 1008601 7680257 := bstep (se 2 (by rfl) ⟨2880096, by rfl⟩ : syracuseStep 7680257 = 5760193) B5760193
theorem B1618363 : Blo 1008601 1618363 := bstep (se 1 (by rfl) ⟨1213772, by rfl⟩ : syracuseStep 1618363 = 2427545) B2427545
theorem B2273831 : Blo 1008601 2273831 := bstep (se 1 (by rfl) ⟨1705373, by rfl⟩ : syracuseStep 2273831 = 3410747) B3410747
theorem B1094183 : Blo 1008601 1094183 := bstep (se 1 (by rfl) ⟨820637, by rfl⟩ : syracuseStep 1094183 = 1641275) B1641275
theorem B8630995 : Blo 1008601 8630995 := bstep (se 1 (by rfl) ⟨6473246, by rfl⟩ : syracuseStep 8630995 = 12946493) B12946493
theorem B2274155 : Blo 1008601 2274155 := bstep (se 1 (by rfl) ⟨1705616, by rfl⟩ : syracuseStep 2274155 = 3411233) B3411233
theorem B2274209 : Blo 1008601 2274209 := bstep (se 2 (by rfl) ⟨852828, by rfl⟩ : syracuseStep 2274209 = 1705657) B1705657
theorem B2274551 : Blo 1008601 2274551 := bstep (se 1 (by rfl) ⟨1705913, by rfl⟩ : syracuseStep 2274551 = 3411827) B3411827
theorem B13120861 : Blo 1008601 13120861 := bstep (se 3 (by rfl) ⟨2460161, by rfl⟩ : syracuseStep 13120861 = 4920323) B4920323
theorem B5748347 : Blo 1008601 5748347 := bstep (se 1 (by rfl) ⟨4311260, by rfl⟩ : syracuseStep 5748347 = 8622521) B8622521
theorem B8631953 : Blo 1008601 8631953 := bstep (se 2 (by rfl) ⟨3236982, by rfl⟩ : syracuseStep 8631953 = 6473965) B6473965
theorem B2275145 : Blo 1008601 2275145 := bstep (se 2 (by rfl) ⟨853179, by rfl⟩ : syracuseStep 2275145 = 1706359) B1706359
theorem B2701151 : Blo 1008601 2701151 := bstep (se 1 (by rfl) ⟨2025863, by rfl⟩ : syracuseStep 2701151 = 4051727) B4051727
theorem B7288861 : Blo 1008601 7288861 := bstep (se 3 (by rfl) ⟨1366661, by rfl⟩ : syracuseStep 7288861 = 2733323) B2733323
theorem B1914977 : Blo 1008601 1914977 := bstep (se 2 (by rfl) ⟨718116, by rfl⟩ : syracuseStep 1914977 = 1436233) B1436233
theorem B1915319 : Blo 1008601 1915319 := bstep (se 1 (by rfl) ⟨1436489, by rfl⟩ : syracuseStep 1915319 = 2872979) B2872979
theorem B2275937 : Blo 1008601 2275937 := bstep (se 2 (by rfl) ⟨853476, by rfl⟩ : syracuseStep 2275937 = 1706953) B1706953
theorem B2079479 : Blo 1008601 2079479 := bstep (se 1 (by rfl) ⟨1559609, by rfl⟩ : syracuseStep 2079479 = 3119219) B3119219
theorem B1915721 : Blo 1008601 1915721 := bstep (se 2 (by rfl) ⟨718395, by rfl⟩ : syracuseStep 1915721 = 1436791) B1436791
theorem B2276279 : Blo 1008601 2276279 := bstep (se 1 (by rfl) ⟨1707209, by rfl⟩ : syracuseStep 2276279 = 3414419) B3414419
theorem B6143147 : Blo 1008601 6143147 := bstep (se 1 (by rfl) ⟨4607360, by rfl⟩ : syracuseStep 6143147 = 9214721) B9214721
theorem B2276873 : Blo 1008601 2276873 := bstep (se 2 (by rfl) ⟨853827, by rfl⟩ : syracuseStep 2276873 = 1707655) B1707655
theorem B1916435 : Blo 1008601 1916435 := bstep (se 1 (by rfl) ⟨1437326, by rfl⟩ : syracuseStep 1916435 = 2874653) B2874653
theorem B1916473 : Blo 1008601 1916473 := bstep (se 2 (by rfl) ⟨718677, by rfl⟩ : syracuseStep 1916473 = 1437355) B1437355
theorem B8208017 : Blo 1008601 8208017 := bstep (se 2 (by rfl) ⟨3078006, by rfl⟩ : syracuseStep 8208017 = 6156013) B6156013
theorem B4800215 : Blo 1008601 4800215 := bstep (se 1 (by rfl) ⟨3600161, by rfl⟩ : syracuseStep 4800215 = 7200323) B7200323
theorem B2277215 : Blo 1008601 2277215 := bstep (se 1 (by rfl) ⟨1707911, by rfl⟩ : syracuseStep 2277215 = 3415823) B3415823
theorem B1916777 : Blo 1008601 1916777 := bstep (se 2 (by rfl) ⟨718791, by rfl⟩ : syracuseStep 1916777 = 1437583) B1437583
theorem B2277395 : Blo 1008601 2277395 := bstep (se 1 (by rfl) ⟨1708046, by rfl⟩ : syracuseStep 2277395 = 3416093) B3416093
theorem B2277737 : Blo 1008601 2277737 := bstep (se 2 (by rfl) ⟨854151, by rfl⟩ : syracuseStep 2277737 = 1708303) B1708303
theorem B7684631 : Blo 1008601 7684631 := bstep (se 1 (by rfl) ⟨5763473, by rfl⟩ : syracuseStep 7684631 = 11526947) B11526947
theorem B1819579 : Blo 1008601 1819579 := bstep (se 1 (by rfl) ⟨1364684, by rfl⟩ : syracuseStep 1819579 = 2729369) B2729369
theorem B2278331 : Blo 1008601 2278331 := bstep (se 1 (by rfl) ⟨1708748, by rfl⟩ : syracuseStep 2278331 = 3417497) B3417497
theorem B1918075 : Blo 1008601 1918075 := bstep (se 1 (by rfl) ⟨1438556, by rfl⟩ : syracuseStep 1918075 = 2877113) B2877113
theorem B1918151 : Blo 1008601 1918151 := bstep (se 1 (by rfl) ⟨1438613, by rfl⟩ : syracuseStep 1918151 = 2877227) B2877227
theorem B2049467 : Blo 1008601 2049467 := bstep (se 1 (by rfl) ⟨1537100, by rfl⟩ : syracuseStep 2049467 = 3074201) B3074201
theorem B1918561 : Blo 1008601 1918561 := bstep (se 2 (by rfl) ⟨719460, by rfl⟩ : syracuseStep 1918561 = 1438921) B1438921
theorem B1918903 : Blo 1008601 1918903 := bstep (se 1 (by rfl) ⟨1439177, by rfl⟩ : syracuseStep 1918903 = 2878355) B2878355
theorem B6473657 : Blo 1008601 6473657 := bstep (se 2 (by rfl) ⟨2427621, by rfl⟩ : syracuseStep 6473657 = 4855243) B4855243
theorem B1919305 : Blo 1008601 1919305 := bstep (se 2 (by rfl) ⟨719739, by rfl⟩ : syracuseStep 1919305 = 1439479) B1439479
theorem B1821035 : Blo 1008601 1821035 := bstep (se 1 (by rfl) ⟨1365776, by rfl⟩ : syracuseStep 1821035 = 2731553) B2731553
theorem B336579299 : Blo 1008601 336579299 := bstep (se 1 (by rfl) ⟨252434474, by rfl⟩ : syracuseStep 336579299 = 504868949) B504868949
theorem B5458691 : Blo 1008601 5458691 := bstep (se 1 (by rfl) ⟨4094018, by rfl⟩ : syracuseStep 5458691 = 8188037) B8188037
theorem B1920019 : Blo 1008601 1920019 := bstep (se 1 (by rfl) ⟨1440014, by rfl⟩ : syracuseStep 1920019 = 2880029) B2880029
theorem B2051129 : Blo 1008601 2051129 := bstep (se 2 (by rfl) ⟨769173, by rfl⟩ : syracuseStep 2051129 = 1538347) B1538347
theorem B4312217 : Blo 1008601 4312217 := bstep (se 2 (by rfl) ⟨1617081, by rfl⟩ : syracuseStep 4312217 = 3234163) B3234163
theorem B1920361 : Blo 1008601 1920361 := bstep (se 2 (by rfl) ⟨720135, by rfl⟩ : syracuseStep 1920361 = 1440271) B1440271
theorem B1363375 : Blo 1008601 1363375 := bstep (se 1 (by rfl) ⟨1022531, by rfl⟩ : syracuseStep 1363375 = 2045063) B2045063
theorem B5754887 : Blo 1008601 5754887 := bstep (se 1 (by rfl) ⟨4316165, by rfl⟩ : syracuseStep 5754887 = 8632331) B8632331
theorem B1134715 : Blo 1008601 1134715 := bstep (se 1 (by rfl) ⟨851036, by rfl⟩ : syracuseStep 1134715 = 1702073) B1702073
theorem B3887261 : Blo 1008601 3887261 := bstep (se 3 (by rfl) ⟨728861, by rfl⟩ : syracuseStep 3887261 = 1457723) B1457723
theorem B8409251 : Blo 1008601 8409251 := bstep (se 1 (by rfl) ⟨6306938, by rfl⟩ : syracuseStep 8409251 = 12613877) B12613877
theorem B1135183 : Blo 1008601 1135183 := bstep (se 1 (by rfl) ⟨851387, by rfl⟩ : syracuseStep 1135183 = 1702775) B1702775
theorem B1921735 : Blo 1008601 1921735 := bstep (se 1 (by rfl) ⟨1441301, by rfl⟩ : syracuseStep 1921735 = 2882603) B2882603
theorem B3691337 : Blo 1008601 3691337 := bstep (se 2 (by rfl) ⟨1384251, by rfl⟩ : syracuseStep 3691337 = 2768503) B2768503
theorem B1135579 : Blo 1008601 1135579 := bstep (se 1 (by rfl) ⟨851684, by rfl⟩ : syracuseStep 1135579 = 1703369) B1703369
theorem B4314131 : Blo 1008601 4314131 := bstep (se 1 (by rfl) ⟨3235598, by rfl⟩ : syracuseStep 4314131 = 6471197) B6471197
theorem B2872705 : Blo 1008601 2872705 := bstep (se 2 (by rfl) ⟨1077264, by rfl⟩ : syracuseStep 2872705 = 2154529) B2154529
theorem B8181157 : Blo 1008601 8181157 := bstep (se 4 (by rfl) ⟨766983, by rfl⟩ : syracuseStep 8181157 = 1533967) B1533967
theorem B1136047 : Blo 1008601 1136047 := bstep (se 1 (by rfl) ⟨852035, by rfl⟩ : syracuseStep 1136047 = 1704071) B1704071
theorem B3233267 : Blo 1008601 3233267 := bstep (se 1 (by rfl) ⟨2424950, by rfl⟩ : syracuseStep 3233267 = 4849901) B4849901
theorem B1725961 : Blo 1008601 1725961 := bstep (se 2 (by rfl) ⟨647235, by rfl⟩ : syracuseStep 1725961 = 1294471) B1294471
theorem B8181287 : Blo 1008601 8181287 := bstep (se 1 (by rfl) ⟨6135965, by rfl⟩ : syracuseStep 8181287 = 12271931) B12271931
theorem B3888737 : Blo 1008601 3888737 := bstep (se 2 (by rfl) ⟨1458276, by rfl⟩ : syracuseStep 3888737 = 2916553) B2916553
theorem B1136479 : Blo 1008601 1136479 := bstep (se 1 (by rfl) ⟨852359, by rfl⟩ : syracuseStep 1136479 = 1704719) B1704719
theorem B2873195 : Blo 1008601 2873195 := bstep (se 1 (by rfl) ⟨2154896, by rfl⟩ : syracuseStep 2873195 = 4309793) B4309793
theorem B3889079 : Blo 1008601 3889079 := bstep (se 1 (by rfl) ⟨2916809, by rfl⟩ : syracuseStep 3889079 = 5833619) B5833619
theorem B3463183 : Blo 1008601 3463183 := bstep (se 1 (by rfl) ⟨2597387, by rfl⟩ : syracuseStep 3463183 = 5194775) B5194775
theorem B4217027 : Blo 1008601 4217027 := bstep (se 1 (by rfl) ⟨3162770, by rfl⟩ : syracuseStep 4217027 = 6325541) B6325541
theorem B1136839 : Blo 1008601 1136839 := bstep (se 1 (by rfl) ⟨852629, by rfl⟩ : syracuseStep 1136839 = 1705259) B1705259
theorem B1366727 : Blo 1008601 1366727 := bstep (se 1 (by rfl) ⟨1025045, by rfl⟩ : syracuseStep 1366727 = 2050091) B2050091
theorem B5757803 : Blo 1008601 5757803 := bstep (se 1 (by rfl) ⟨4318352, by rfl⟩ : syracuseStep 5757803 = 8636705) B8636705
theorem B1137703 : Blo 1008601 1137703 := bstep (se 1 (by rfl) ⟨853277, by rfl⟩ : syracuseStep 1137703 = 1706555) B1706555
theorem B6151247 : Blo 1008601 6151247 := bstep (se 1 (by rfl) ⟨4613435, by rfl⟩ : syracuseStep 6151247 = 9226871) B9226871
theorem B78830765 : Blo 1008601 78830765 := bstep (se 3 (by rfl) ⟨14780768, by rfl⟩ : syracuseStep 78830765 = 29561537) B29561537
theorem B22109431 : Blo 1008601 22109431 := bstep (se 1 (by rfl) ⟨16582073, by rfl⟩ : syracuseStep 22109431 = 33164147) B33164147
theorem B1367479 : Blo 1008601 1367479 := bstep (se 1 (by rfl) ⟨1025609, by rfl⟩ : syracuseStep 1367479 = 2051219) B2051219
theorem B12967613 : Blo 1008601 12967613 := bstep (se 3 (by rfl) ⟨2431427, by rfl⟩ : syracuseStep 12967613 = 4862855) B4862855
theorem B7659359 : Blo 1008601 7659359 := bstep (se 1 (by rfl) ⟨5744519, by rfl⟩ : syracuseStep 7659359 = 11489039) B11489039
theorem B18473285 : Blo 1008601 18473285 := bstep (se 4 (by rfl) ⟨1731870, by rfl⟩ : syracuseStep 18473285 = 3463741) B3463741
theorem B1008603 : Blo 1008601 1008603 := bstep (se 1 (by rfl) ⟨756452, by rfl⟩ : syracuseStep 1008603 = 1512905) B1512905
theorem B3073043 : Blo 1008601 3073043 := bstep (se 1 (by rfl) ⟨2304782, by rfl⟩ : syracuseStep 3073043 = 4609565) B4609565
theorem B1008679 : Blo 1008601 1008679 := bstep (se 1 (by rfl) ⟨756509, by rfl⟩ : syracuseStep 1008679 = 1513019) B1513019
theorem B1008719 : Blo 1008601 1008719 := bstep (se 1 (by rfl) ⟨756539, by rfl⟩ : syracuseStep 1008719 = 1513079) B1513079
theorem B1008735 : Blo 1008601 1008735 := bstep (se 1 (by rfl) ⟨756551, by rfl⟩ : syracuseStep 1008735 = 1513103) B1513103
theorem B1008763 : Blo 1008601 1008763 := bstep (se 1 (by rfl) ⟨756572, by rfl⟩ : syracuseStep 1008763 = 1513145) B1513145
theorem B1008815 : Blo 1008601 1008815 := bstep (se 1 (by rfl) ⟨756611, by rfl⟩ : syracuseStep 1008815 = 1513223) B1513223
theorem B1008839 : Blo 1008601 1008839 := bstep (se 1 (by rfl) ⟨756629, by rfl⟩ : syracuseStep 1008839 = 1513259) B1513259
theorem B1008859 : Blo 1008601 1008859 := bstep (se 1 (by rfl) ⟨756644, by rfl⟩ : syracuseStep 1008859 = 1513289) B1513289
theorem B1008935 : Blo 1008601 1008935 := bstep (se 1 (by rfl) ⟨756701, by rfl⟩ : syracuseStep 1008935 = 1513403) B1513403
theorem B1008975 : Blo 1008601 1008975 := bstep (se 1 (by rfl) ⟨756731, by rfl⟩ : syracuseStep 1008975 = 1513463) B1513463
theorem B1008991 : Blo 1008601 1008991 := bstep (se 1 (by rfl) ⟨756743, by rfl⟩ : syracuseStep 1008991 = 1513487) B1513487
theorem B3073385 : Blo 1008601 3073385 := bstep (se 2 (by rfl) ⟨1152519, by rfl⟩ : syracuseStep 3073385 = 2305039) B2305039
theorem B1009019 : Blo 1008601 1009019 := bstep (se 1 (by rfl) ⟨756764, by rfl⟩ : syracuseStep 1009019 = 1513529) B1513529
theorem B12445093 : Blo 1008601 12445093 := bstep (se 4 (by rfl) ⟨1166727, by rfl⟩ : syracuseStep 12445093 = 2333455) B2333455
theorem B1009071 : Blo 1008601 1009071 := bstep (se 1 (by rfl) ⟨756803, by rfl⟩ : syracuseStep 1009071 = 1513607) B1513607
theorem B1009095 : Blo 1008601 1009095 := bstep (se 1 (by rfl) ⟨756821, by rfl⟩ : syracuseStep 1009095 = 1513643) B1513643
theorem B1009115 : Blo 1008601 1009115 := bstep (se 1 (by rfl) ⟨756836, by rfl⟩ : syracuseStep 1009115 = 1513673) B1513673
theorem B2876953 : Blo 1008601 2876953 := bstep (se 2 (by rfl) ⟨1078857, by rfl⟩ : syracuseStep 2876953 = 2157715) B2157715
theorem B1009191 : Blo 1008601 1009191 := bstep (se 1 (by rfl) ⟨756893, by rfl⟩ : syracuseStep 1009191 = 1513787) B1513787
theorem B1009231 : Blo 1008601 1009231 := bstep (se 1 (by rfl) ⟨756923, by rfl⟩ : syracuseStep 1009231 = 1513847) B1513847
theorem B1009247 : Blo 1008601 1009247 := bstep (se 1 (by rfl) ⟨756935, by rfl⟩ : syracuseStep 1009247 = 1513871) B1513871
theorem B1009275 : Blo 1008601 1009275 := bstep (se 1 (by rfl) ⟨756956, by rfl⟩ : syracuseStep 1009275 = 1513913) B1513913
theorem B1009327 : Blo 1008601 1009327 := bstep (se 1 (by rfl) ⟨756995, by rfl⟩ : syracuseStep 1009327 = 1513991) B1513991
theorem B1009351 : Blo 1008601 1009351 := bstep (se 1 (by rfl) ⟨757013, by rfl⟩ : syracuseStep 1009351 = 1514027) B1514027
theorem B1009371 : Blo 1008601 1009371 := bstep (se 1 (by rfl) ⟨757028, by rfl⟩ : syracuseStep 1009371 = 1514057) B1514057
theorem B1009447 : Blo 1008601 1009447 := bstep (se 1 (by rfl) ⟨757085, by rfl⟩ : syracuseStep 1009447 = 1514171) B1514171
theorem B1009487 : Blo 1008601 1009487 := bstep (se 1 (by rfl) ⟨757115, by rfl⟩ : syracuseStep 1009487 = 1514231) B1514231
theorem B1009503 : Blo 1008601 1009503 := bstep (se 1 (by rfl) ⟨757127, by rfl⟩ : syracuseStep 1009503 = 1514255) B1514255
theorem B1009531 : Blo 1008601 1009531 := bstep (se 1 (by rfl) ⟨757148, by rfl⟩ : syracuseStep 1009531 = 1514297) B1514297
theorem B1009583 : Blo 1008601 1009583 := bstep (se 1 (by rfl) ⟨757187, by rfl⟩ : syracuseStep 1009583 = 1514375) B1514375
theorem B1009607 : Blo 1008601 1009607 := bstep (se 1 (by rfl) ⟨757205, by rfl⟩ : syracuseStep 1009607 = 1514411) B1514411
theorem B1009627 : Blo 1008601 1009627 := bstep (se 1 (by rfl) ⟨757220, by rfl⟩ : syracuseStep 1009627 = 1514441) B1514441
theorem B1009703 : Blo 1008601 1009703 := bstep (se 1 (by rfl) ⟨757277, by rfl⟩ : syracuseStep 1009703 = 1514555) B1514555
theorem B1009743 : Blo 1008601 1009743 := bstep (se 1 (by rfl) ⟨757307, by rfl⟩ : syracuseStep 1009743 = 1514615) B1514615
theorem B1009759 : Blo 1008601 1009759 := bstep (se 1 (by rfl) ⟨757319, by rfl⟩ : syracuseStep 1009759 = 1514639) B1514639
theorem B147449969 : Blo 1008601 147449969 := bstep (se 2 (by rfl) ⟨55293738, by rfl⟩ : syracuseStep 147449969 = 110587477) B110587477
theorem B1009787 : Blo 1008601 1009787 := bstep (se 1 (by rfl) ⟨757340, by rfl⟩ : syracuseStep 1009787 = 1514681) B1514681
theorem B1009839 : Blo 1008601 1009839 := bstep (se 1 (by rfl) ⟨757379, by rfl⟩ : syracuseStep 1009839 = 1514759) B1514759
theorem B1009863 : Blo 1008601 1009863 := bstep (se 1 (by rfl) ⟨757397, by rfl⟩ : syracuseStep 1009863 = 1514795) B1514795
theorem B1009883 : Blo 1008601 1009883 := bstep (se 1 (by rfl) ⟨757412, by rfl⟩ : syracuseStep 1009883 = 1514825) B1514825
theorem B1009959 : Blo 1008601 1009959 := bstep (se 1 (by rfl) ⟨757469, by rfl⟩ : syracuseStep 1009959 = 1514939) B1514939
theorem B1009999 : Blo 1008601 1009999 := bstep (se 1 (by rfl) ⟨757499, by rfl⟩ : syracuseStep 1009999 = 1514999) B1514999
theorem B1010015 : Blo 1008601 1010015 := bstep (se 1 (by rfl) ⟨757511, by rfl⟩ : syracuseStep 1010015 = 1515023) B1515023
theorem B10905961 : Blo 1008601 10905961 := bstep (se 2 (by rfl) ⟨4089735, by rfl⟩ : syracuseStep 10905961 = 8179471) B8179471
theorem B1010043 : Blo 1008601 1010043 := bstep (se 1 (by rfl) ⟨757532, by rfl⟩ : syracuseStep 1010043 = 1515065) B1515065
theorem B4614529 : Blo 1008601 4614529 := bstep (se 2 (by rfl) ⟨1730448, by rfl⟩ : syracuseStep 4614529 = 3460897) B3460897
theorem B1010095 : Blo 1008601 1010095 := bstep (se 1 (by rfl) ⟨757571, by rfl⟩ : syracuseStep 1010095 = 1515143) B1515143
theorem B1010119 : Blo 1008601 1010119 := bstep (se 1 (by rfl) ⟨757589, by rfl⟩ : syracuseStep 1010119 = 1515179) B1515179
theorem B1010139 : Blo 1008601 1010139 := bstep (se 1 (by rfl) ⟨757604, by rfl⟩ : syracuseStep 1010139 = 1515209) B1515209
theorem B1731079 : Blo 1008601 1731079 := bstep (se 1 (by rfl) ⟨1298309, by rfl⟩ : syracuseStep 1731079 = 2596619) B2596619
theorem B1010215 : Blo 1008601 1010215 := bstep (se 1 (by rfl) ⟨757661, by rfl⟩ : syracuseStep 1010215 = 1515323) B1515323
theorem B1010255 : Blo 1008601 1010255 := bstep (se 1 (by rfl) ⟨757691, by rfl⟩ : syracuseStep 1010255 = 1515383) B1515383
theorem B1010271 : Blo 1008601 1010271 := bstep (se 1 (by rfl) ⟨757703, by rfl⟩ : syracuseStep 1010271 = 1515407) B1515407
theorem B1010299 : Blo 1008601 1010299 := bstep (se 1 (by rfl) ⟨757724, by rfl⟩ : syracuseStep 1010299 = 1515449) B1515449
theorem B3074699 : Blo 1008601 3074699 := bstep (se 1 (by rfl) ⟨2306024, by rfl⟩ : syracuseStep 3074699 = 4612049) B4612049
theorem B1010351 : Blo 1008601 1010351 := bstep (se 1 (by rfl) ⟨757763, by rfl⟩ : syracuseStep 1010351 = 1515527) B1515527
theorem B1010375 : Blo 1008601 1010375 := bstep (se 1 (by rfl) ⟨757781, by rfl⟩ : syracuseStep 1010375 = 1515563) B1515563
theorem B1010395 : Blo 1008601 1010395 := bstep (se 1 (by rfl) ⟨757796, by rfl⟩ : syracuseStep 1010395 = 1515593) B1515593
theorem B1010471 : Blo 1008601 1010471 := bstep (se 1 (by rfl) ⟨757853, by rfl⟩ : syracuseStep 1010471 = 1515707) B1515707
theorem B8645453 : Blo 1008601 8645453 := bstep (se 3 (by rfl) ⟨1621022, by rfl⟩ : syracuseStep 8645453 = 3242045) B3242045
theorem B1010511 : Blo 1008601 1010511 := bstep (se 1 (by rfl) ⟨757883, by rfl⟩ : syracuseStep 1010511 = 1515767) B1515767
theorem B1010527 : Blo 1008601 1010527 := bstep (se 1 (by rfl) ⟨757895, by rfl⟩ : syracuseStep 1010527 = 1515791) B1515791
theorem B1010555 : Blo 1008601 1010555 := bstep (se 1 (by rfl) ⟨757916, by rfl⟩ : syracuseStep 1010555 = 1515833) B1515833
theorem B1010607 : Blo 1008601 1010607 := bstep (se 1 (by rfl) ⟨757955, by rfl⟩ : syracuseStep 1010607 = 1515911) B1515911
theorem B1010631 : Blo 1008601 1010631 := bstep (se 1 (by rfl) ⟨757973, by rfl⟩ : syracuseStep 1010631 = 1515947) B1515947
theorem B1010651 : Blo 1008601 1010651 := bstep (se 1 (by rfl) ⟨757988, by rfl⟩ : syracuseStep 1010651 = 1515977) B1515977
theorem B43641827 : Blo 1008601 43641827 := bstep (se 1 (by rfl) ⟨32731370, by rfl⟩ : syracuseStep 43641827 = 65462741) B65462741
theorem B1010727 : Blo 1008601 1010727 := bstep (se 1 (by rfl) ⟨758045, by rfl⟩ : syracuseStep 1010727 = 1516091) B1516091
theorem B6482987 : Blo 1008601 6482987 := bstep (se 1 (by rfl) ⟨4862240, by rfl⟩ : syracuseStep 6482987 = 9724481) B9724481
theorem B1010767 : Blo 1008601 1010767 := bstep (se 1 (by rfl) ⟨758075, by rfl⟩ : syracuseStep 1010767 = 1516151) B1516151
theorem B1010783 : Blo 1008601 1010783 := bstep (se 1 (by rfl) ⟨758087, by rfl⟩ : syracuseStep 1010783 = 1516175) B1516175
theorem B1010811 : Blo 1008601 1010811 := bstep (se 1 (by rfl) ⟨758108, by rfl⟩ : syracuseStep 1010811 = 1516217) B1516217
theorem B1010863 : Blo 1008601 1010863 := bstep (se 1 (by rfl) ⟨758147, by rfl⟩ : syracuseStep 1010863 = 1516295) B1516295
theorem B1010887 : Blo 1008601 1010887 := bstep (se 1 (by rfl) ⟨758165, by rfl⟩ : syracuseStep 1010887 = 1516331) B1516331
theorem B1010907 : Blo 1008601 1010907 := bstep (se 1 (by rfl) ⟨758180, by rfl⟩ : syracuseStep 1010907 = 1516361) B1516361
theorem B2190583 : Blo 1008601 2190583 := bstep (se 1 (by rfl) ⟨1642937, by rfl⟩ : syracuseStep 2190583 = 3285875) B3285875
theorem B1010983 : Blo 1008601 1010983 := bstep (se 1 (by rfl) ⟨758237, by rfl⟩ : syracuseStep 1010983 = 1516475) B1516475
theorem B1011023 : Blo 1008601 1011023 := bstep (se 1 (by rfl) ⟨758267, by rfl⟩ : syracuseStep 1011023 = 1516535) B1516535
theorem B1011039 : Blo 1008601 1011039 := bstep (se 1 (by rfl) ⟨758279, by rfl⟩ : syracuseStep 1011039 = 1516559) B1516559
theorem B1011067 : Blo 1008601 1011067 := bstep (se 1 (by rfl) ⟨758300, by rfl⟩ : syracuseStep 1011067 = 1516601) B1516601
theorem B1011119 : Blo 1008601 1011119 := bstep (se 1 (by rfl) ⟨758339, by rfl⟩ : syracuseStep 1011119 = 1516679) B1516679
theorem B1011143 : Blo 1008601 1011143 := bstep (se 1 (by rfl) ⟨758357, by rfl⟩ : syracuseStep 1011143 = 1516715) B1516715
theorem B1011163 : Blo 1008601 1011163 := bstep (se 1 (by rfl) ⟨758372, by rfl⟩ : syracuseStep 1011163 = 1516745) B1516745
theorem B1011239 : Blo 1008601 1011239 := bstep (se 1 (by rfl) ⟨758429, by rfl⟩ : syracuseStep 1011239 = 1516859) B1516859
theorem B1011279 : Blo 1008601 1011279 := bstep (se 1 (by rfl) ⟨758459, by rfl⟩ : syracuseStep 1011279 = 1516919) B1516919
theorem B1011295 : Blo 1008601 1011295 := bstep (se 1 (by rfl) ⟨758471, by rfl⟩ : syracuseStep 1011295 = 1516943) B1516943
theorem B2158177 : Blo 1008601 2158177 := bstep (se 2 (by rfl) ⟨809316, by rfl⟩ : syracuseStep 2158177 = 1618633) B1618633
theorem B1011323 : Blo 1008601 1011323 := bstep (se 1 (by rfl) ⟨758492, by rfl⟩ : syracuseStep 1011323 = 1516985) B1516985
theorem B1011375 : Blo 1008601 1011375 := bstep (se 1 (by rfl) ⟨758531, by rfl⟩ : syracuseStep 1011375 = 1517063) B1517063
theorem B1437383 : Blo 1008601 1437383 := bstep (se 1 (by rfl) ⟨1078037, by rfl⟩ : syracuseStep 1437383 = 2156075) B2156075
theorem B1011399 : Blo 1008601 1011399 := bstep (se 1 (by rfl) ⟨758549, by rfl⟩ : syracuseStep 1011399 = 1517099) B1517099
theorem B1011419 : Blo 1008601 1011419 := bstep (se 1 (by rfl) ⟨758564, by rfl⟩ : syracuseStep 1011419 = 1517129) B1517129
theorem B1011495 : Blo 1008601 1011495 := bstep (se 1 (by rfl) ⟨758621, by rfl⟩ : syracuseStep 1011495 = 1517243) B1517243
theorem B1011535 : Blo 1008601 1011535 := bstep (se 1 (by rfl) ⟨758651, by rfl⟩ : syracuseStep 1011535 = 1517303) B1517303
theorem B1011551 : Blo 1008601 1011551 := bstep (se 1 (by rfl) ⟨758663, by rfl⟩ : syracuseStep 1011551 = 1517327) B1517327
theorem B1011579 : Blo 1008601 1011579 := bstep (se 1 (by rfl) ⟨758684, by rfl⟩ : syracuseStep 1011579 = 1517369) B1517369
theorem B1011631 : Blo 1008601 1011631 := bstep (se 1 (by rfl) ⟨758723, by rfl⟩ : syracuseStep 1011631 = 1517447) B1517447
theorem B1011655 : Blo 1008601 1011655 := bstep (se 1 (by rfl) ⟨758741, by rfl⟩ : syracuseStep 1011655 = 1517483) B1517483
theorem B1011675 : Blo 1008601 1011675 := bstep (se 1 (by rfl) ⟨758756, by rfl⟩ : syracuseStep 1011675 = 1517513) B1517513
theorem B5763109 : Blo 1008601 5763109 := bstep (se 4 (by rfl) ⟨540291, by rfl⟩ : syracuseStep 5763109 = 1080583) B1080583
theorem B1011751 : Blo 1008601 1011751 := bstep (se 1 (by rfl) ⟨758813, by rfl⟩ : syracuseStep 1011751 = 1517627) B1517627
theorem B1536079 : Blo 1008601 1536079 := bstep (se 1 (by rfl) ⟨1152059, by rfl⟩ : syracuseStep 1536079 = 2304119) B2304119
theorem B1011791 : Blo 1008601 1011791 := bstep (se 1 (by rfl) ⟨758843, by rfl⟩ : syracuseStep 1011791 = 1517687) B1517687
theorem B1011807 : Blo 1008601 1011807 := bstep (se 1 (by rfl) ⟨758855, by rfl⟩ : syracuseStep 1011807 = 1517711) B1517711
theorem B1011835 : Blo 1008601 1011835 := bstep (se 1 (by rfl) ⟨758876, by rfl⟩ : syracuseStep 1011835 = 1517753) B1517753
theorem B1011887 : Blo 1008601 1011887 := bstep (se 1 (by rfl) ⟨758915, by rfl⟩ : syracuseStep 1011887 = 1517831) B1517831
theorem B1011911 : Blo 1008601 1011911 := bstep (se 1 (by rfl) ⟨758933, by rfl⟩ : syracuseStep 1011911 = 1517867) B1517867
theorem B1011931 : Blo 1008601 1011931 := bstep (se 1 (by rfl) ⟨758948, by rfl⟩ : syracuseStep 1011931 = 1517897) B1517897
theorem B1012007 : Blo 1008601 1012007 := bstep (se 1 (by rfl) ⟨759005, by rfl⟩ : syracuseStep 1012007 = 1518011) B1518011
theorem B1012047 : Blo 1008601 1012047 := bstep (se 1 (by rfl) ⟨759035, by rfl⟩ : syracuseStep 1012047 = 1518071) B1518071
theorem B1012063 : Blo 1008601 1012063 := bstep (se 1 (by rfl) ⟨759047, by rfl⟩ : syracuseStep 1012063 = 1518095) B1518095
theorem B8188265 : Blo 1008601 8188265 := bstep (se 2 (by rfl) ⟨3070599, by rfl⟩ : syracuseStep 8188265 = 6141199) B6141199
theorem B1012091 : Blo 1008601 1012091 := bstep (se 1 (by rfl) ⟨759068, by rfl⟩ : syracuseStep 1012091 = 1518137) B1518137
theorem B2879869 : Blo 1008601 2879869 := bstep (se 3 (by rfl) ⟨539975, by rfl⟩ : syracuseStep 2879869 = 1079951) B1079951
theorem B1012143 : Blo 1008601 1012143 := bstep (se 1 (by rfl) ⟨759107, by rfl⟩ : syracuseStep 1012143 = 1518215) B1518215
theorem B1012167 : Blo 1008601 1012167 := bstep (se 1 (by rfl) ⟨759125, by rfl⟩ : syracuseStep 1012167 = 1518251) B1518251
theorem B1012187 : Blo 1008601 1012187 := bstep (se 1 (by rfl) ⟨759140, by rfl⟩ : syracuseStep 1012187 = 1518281) B1518281
theorem B3076633 : Blo 1008601 3076633 := bstep (se 2 (by rfl) ⟨1153737, by rfl⟩ : syracuseStep 3076633 = 2307475) B2307475
theorem B3404321 : Blo 1008601 3404321 := bstep (se 2 (by rfl) ⟨1276620, by rfl⟩ : syracuseStep 3404321 = 2553241) B2553241
theorem B1012263 : Blo 1008601 1012263 := bstep (se 1 (by rfl) ⟨759197, by rfl⟩ : syracuseStep 1012263 = 1518395) B1518395
theorem B1012303 : Blo 1008601 1012303 := bstep (se 1 (by rfl) ⟨759227, by rfl⟩ : syracuseStep 1012303 = 1518455) B1518455
theorem B1012319 : Blo 1008601 1012319 := bstep (se 1 (by rfl) ⟨759239, by rfl⟩ : syracuseStep 1012319 = 1518479) B1518479
theorem B1012347 : Blo 1008601 1012347 := bstep (se 1 (by rfl) ⟨759260, by rfl⟩ : syracuseStep 1012347 = 1518521) B1518521
theorem B1012399 : Blo 1008601 1012399 := bstep (se 1 (by rfl) ⟨759299, by rfl⟩ : syracuseStep 1012399 = 1518599) B1518599
theorem B1012423 : Blo 1008601 1012423 := bstep (se 1 (by rfl) ⟨759317, by rfl⟩ : syracuseStep 1012423 = 1518635) B1518635
theorem B2880211 : Blo 1008601 2880211 := bstep (se 1 (by rfl) ⟨2160158, by rfl⟩ : syracuseStep 2880211 = 4320317) B4320317
theorem B1012443 : Blo 1008601 1012443 := bstep (se 1 (by rfl) ⟨759332, by rfl⟩ : syracuseStep 1012443 = 1518665) B1518665
theorem B3404537 : Blo 1008601 3404537 := bstep (se 2 (by rfl) ⟨1276701, by rfl⟩ : syracuseStep 3404537 = 2553403) B2553403
theorem B1012519 : Blo 1008601 1012519 := bstep (se 1 (by rfl) ⟨759389, by rfl⟩ : syracuseStep 1012519 = 1518779) B1518779
theorem B1012559 : Blo 1008601 1012559 := bstep (se 1 (by rfl) ⟨759419, by rfl⟩ : syracuseStep 1012559 = 1518839) B1518839
theorem B1012575 : Blo 1008601 1012575 := bstep (se 1 (by rfl) ⟨759431, by rfl⟩ : syracuseStep 1012575 = 1518863) B1518863
theorem B1536875 : Blo 1008601 1536875 := bstep (se 1 (by rfl) ⟨1152656, by rfl⟩ : syracuseStep 1536875 = 2305313) B2305313
theorem B4322231 : Blo 1008601 4322231 := bstep (se 1 (by rfl) ⟨3241673, by rfl⟩ : syracuseStep 4322231 = 6483347) B6483347
theorem B3404807 : Blo 1008601 3404807 := bstep (se 1 (by rfl) ⟨2553605, by rfl⟩ : syracuseStep 3404807 = 5107211) B5107211
theorem B3404915 : Blo 1008601 3404915 := bstep (se 1 (by rfl) ⟨2553686, by rfl⟩ : syracuseStep 3404915 = 5107373) B5107373
theorem B4846787 : Blo 1008601 4846787 := bstep (se 1 (by rfl) ⟨3635090, by rfl⟩ : syracuseStep 4846787 = 7270181) B7270181
theorem B2553079 : Blo 1008601 2553079 := bstep (se 1 (by rfl) ⟨1914809, by rfl⟩ : syracuseStep 2553079 = 3829619) B3829619
theorem B8189207 : Blo 1008601 8189207 := bstep (se 1 (by rfl) ⟨6141905, by rfl⟩ : syracuseStep 8189207 = 12283811) B12283811
theorem B3405185 : Blo 1008601 3405185 := bstep (se 2 (by rfl) ⟨1276944, by rfl⟩ : syracuseStep 3405185 = 2553889) B2553889
theorem B3077519 : Blo 1008601 3077519 := bstep (se 1 (by rfl) ⟨2308139, by rfl⟩ : syracuseStep 3077519 = 4616279) B4616279
theorem B3831259 : Blo 1008601 3831259 := bstep (se 1 (by rfl) ⟨2873444, by rfl⟩ : syracuseStep 3831259 = 5746889) B5746889
theorem B2553353 : Blo 1008601 2553353 := bstep (se 2 (by rfl) ⟨957507, by rfl⟩ : syracuseStep 2553353 = 1915015) B1915015
theorem B2553383 : Blo 1008601 2553383 := bstep (se 1 (by rfl) ⟨1915037, by rfl⟩ : syracuseStep 2553383 = 3830075) B3830075
theorem B7665191 : Blo 1008601 7665191 := bstep (se 1 (by rfl) ⟨5748893, by rfl⟩ : syracuseStep 7665191 = 11497787) B11497787
theorem B32765633 : Blo 1008601 32765633 := bstep (se 2 (by rfl) ⟨12287112, by rfl⟩ : syracuseStep 32765633 = 24574225) B24574225
theorem B8648491 : Blo 1008601 8648491 := bstep (se 1 (by rfl) ⟨6486368, by rfl⟩ : syracuseStep 8648491 = 12972737) B12972737
theorem B2553707 : Blo 1008601 2553707 := bstep (se 1 (by rfl) ⟨1915280, by rfl⟩ : syracuseStep 2553707 = 3830561) B3830561
theorem B1439707 : Blo 1008601 1439707 := bstep (se 1 (by rfl) ⟨1079780, by rfl⟩ : syracuseStep 1439707 = 2159561) B2159561
theorem B12941369 : Blo 1008601 12941369 := bstep (se 2 (by rfl) ⟨4853013, by rfl⟩ : syracuseStep 12941369 = 9706027) B9706027
theorem B3405995 : Blo 1008601 3405995 := bstep (se 1 (by rfl) ⟨2554496, by rfl⟩ : syracuseStep 3405995 = 5108993) B5108993
theorem B1702363 : Blo 1008601 1702363 := bstep (se 1 (by rfl) ⟨1276772, by rfl⟩ : syracuseStep 1702363 = 2553545) B2553545
theorem B2554355 : Blo 1008601 2554355 := bstep (se 1 (by rfl) ⟨1915766, by rfl⟩ : syracuseStep 2554355 = 3831533) B3831533
theorem B6486551 : Blo 1008601 6486551 := bstep (se 1 (by rfl) ⟨4864913, by rfl⟩ : syracuseStep 6486551 = 9729827) B9729827
theorem B1440379 : Blo 1008601 1440379 := bstep (se 1 (by rfl) ⟨1080284, by rfl⟩ : syracuseStep 1440379 = 2160569) B2160569
theorem B3832505 : Blo 1008601 3832505 := bstep (se 2 (by rfl) ⟨1437189, by rfl⟩ : syracuseStep 3832505 = 2874379) B2874379
theorem B3406535 : Blo 1008601 3406535 := bstep (se 1 (by rfl) ⟨2554901, by rfl⟩ : syracuseStep 3406535 = 5109803) B5109803
theorem B5765843 : Blo 1008601 5765843 := bstep (se 1 (by rfl) ⟨4324382, by rfl⟩ : syracuseStep 5765843 = 8648765) B8648765
theorem B3832535 : Blo 1008601 3832535 := bstep (se 1 (by rfl) ⟨2874401, by rfl⟩ : syracuseStep 3832535 = 5748803) B5748803
theorem B1440607 : Blo 1008601 1440607 := bstep (se 1 (by rfl) ⟨1080455, by rfl⟩ : syracuseStep 1440607 = 2160911) B2160911
theorem B2554811 : Blo 1008601 2554811 := bstep (se 1 (by rfl) ⟨1916108, by rfl⟩ : syracuseStep 2554811 = 3832217) B3832217
theorem B1702991 : Blo 1008601 1702991 := bstep (se 1 (by rfl) ⟨1277243, by rfl⟩ : syracuseStep 1702991 = 2554487) B2554487
theorem B5110937 : Blo 1008601 5110937 := bstep (se 2 (by rfl) ⟨1916601, by rfl⟩ : syracuseStep 5110937 = 3833203) B3833203
theorem B8191147 : Blo 1008601 8191147 := bstep (se 1 (by rfl) ⟨6143360, by rfl⟩ : syracuseStep 8191147 = 12286721) B12286721
theorem B21855511 : Blo 1008601 21855511 := bstep (se 1 (by rfl) ⟨16391633, by rfl⟩ : syracuseStep 21855511 = 32783267) B32783267
theorem B2882945 : Blo 1008601 2882945 := bstep (se 2 (by rfl) ⟨1081104, by rfl⟩ : syracuseStep 2882945 = 2162209) B2162209
theorem B7273871 : Blo 1008601 7273871 := bstep (se 1 (by rfl) ⟨5455403, by rfl⟩ : syracuseStep 7273871 = 10910807) B10910807
theorem B10911149 : Blo 1008601 10911149 := bstep (se 3 (by rfl) ⟨2045840, by rfl⟩ : syracuseStep 10911149 = 4091681) B4091681
theorem B1441199 : Blo 1008601 1441199 := bstep (se 1 (by rfl) ⟨1080899, by rfl⟩ : syracuseStep 1441199 = 2161799) B2161799
theorem B2883059 : Blo 1008601 2883059 := bstep (se 1 (by rfl) ⟨2162294, by rfl⟩ : syracuseStep 2883059 = 4324589) B4324589
theorem B3407399 : Blo 1008601 3407399 := bstep (se 1 (by rfl) ⟨2555549, by rfl⟩ : syracuseStep 3407399 = 5111099) B5111099
theorem B2555489 : Blo 1008601 2555489 := bstep (se 2 (by rfl) ⟨958308, by rfl⟩ : syracuseStep 2555489 = 1916617) B1916617
theorem B1080955 : Blo 1008601 1080955 := bstep (se 1 (by rfl) ⟨810716, by rfl⟩ : syracuseStep 1080955 = 1621433) B1621433
theorem B3407507 : Blo 1008601 3407507 := bstep (se 1 (by rfl) ⟨2555630, by rfl⟩ : syracuseStep 3407507 = 5111261) B5111261
theorem B2883401 : Blo 1008601 2883401 := bstep (se 2 (by rfl) ⟨1081275, by rfl⟩ : syracuseStep 2883401 = 2162551) B2162551
theorem B3407723 : Blo 1008601 3407723 := bstep (se 1 (by rfl) ⟨2555792, by rfl⟩ : syracuseStep 3407723 = 5111585) B5111585
theorem B1441643 : Blo 1008601 1441643 := bstep (se 1 (by rfl) ⟨1081232, by rfl⟩ : syracuseStep 1441643 = 2162465) B2162465
theorem B3407777 : Blo 1008601 3407777 := bstep (se 2 (by rfl) ⟨1277916, by rfl⟩ : syracuseStep 3407777 = 2555833) B2555833
theorem B1703855 : Blo 1008601 1703855 := bstep (se 1 (by rfl) ⟨1277891, by rfl⟩ : syracuseStep 1703855 = 2555783) B2555783
theorem B2588777 : Blo 1008601 2588777 := bstep (se 2 (by rfl) ⟨970791, by rfl⟩ : syracuseStep 2588777 = 1941583) B1941583
theorem B1638983 : Blo 1008601 1638983 := bstep (se 1 (by rfl) ⟨1229237, by rfl⟩ : syracuseStep 1638983 = 2458475) B2458475
theorem B1704631 : Blo 1008601 1704631 := bstep (se 1 (by rfl) ⟨1278473, by rfl⟩ : syracuseStep 1704631 = 2556947) B2556947
theorem B1278767 : Blo 1008601 1278767 := bstep (se 1 (by rfl) ⟨959075, by rfl⟩ : syracuseStep 1278767 = 1918151) B1918151
theorem B1704935 : Blo 1008601 1704935 := bstep (se 1 (by rfl) ⟨1278701, by rfl⟩ : syracuseStep 1704935 = 2557403) B2557403
theorem B2556967 : Blo 1008601 2556967 := bstep (se 1 (by rfl) ⟨1917725, by rfl⟩ : syracuseStep 2556967 = 3835451) B3835451
theorem B2426105 : Blo 1008601 2426105 := bstep (se 2 (by rfl) ⟨909789, by rfl⟩ : syracuseStep 2426105 = 1819579) B1819579
theorem B7669079 : Blo 1008601 7669079 := bstep (se 1 (by rfl) ⟨5751809, by rfl⟩ : syracuseStep 7669079 = 11503619) B11503619
theorem B2557433 : Blo 1008601 2557433 := bstep (se 2 (by rfl) ⟨959037, by rfl⟩ : syracuseStep 2557433 = 1918075) B1918075
theorem B1214023 : Blo 1008601 1214023 := bstep (se 1 (by rfl) ⟨910517, by rfl⟩ : syracuseStep 1214023 = 1821035) B1821035
theorem B5113529 : Blo 1008601 5113529 := bstep (se 2 (by rfl) ⟨1917573, by rfl⟩ : syracuseStep 5113529 = 3835147) B3835147
theorem B8619857 : Blo 1008601 8619857 := bstep (se 2 (by rfl) ⟨3232446, by rfl⟩ : syracuseStep 8619857 = 6464893) B6464893
theorem B3639127 : Blo 1008601 3639127 := bstep (se 1 (by rfl) ⟨2729345, by rfl⟩ : syracuseStep 3639127 = 5458691) B5458691
theorem B3835937 : Blo 1008601 3835937 := bstep (se 2 (by rfl) ⟨1438476, by rfl⟩ : syracuseStep 3835937 = 2876953) B2876953
theorem B1706089 : Blo 1008601 1706089 := bstep (se 2 (by rfl) ⟨639783, by rfl⟩ : syracuseStep 1706089 = 1279567) B1279567
theorem B2590849 : Blo 1008601 2590849 := bstep (se 2 (by rfl) ⟨971568, by rfl⟩ : syracuseStep 2590849 = 1943137) B1943137
theorem B2558081 : Blo 1008601 2558081 := bstep (se 2 (by rfl) ⟨959280, by rfl⟩ : syracuseStep 2558081 = 1918561) B1918561
theorem B2558375 : Blo 1008601 2558375 := bstep (se 1 (by rfl) ⟨1918781, by rfl⟩ : syracuseStep 2558375 = 3837563) B3837563
theorem B2558537 : Blo 1008601 2558537 := bstep (se 2 (by rfl) ⟨959451, by rfl⟩ : syracuseStep 2558537 = 1918903) B1918903
theorem B1641067 : Blo 1008601 1641067 := bstep (se 1 (by rfl) ⟨1230800, by rfl⟩ : syracuseStep 1641067 = 2461601) B2461601
theorem B4852399 : Blo 1008601 4852399 := bstep (se 1 (by rfl) ⟨3639299, by rfl⟩ : syracuseStep 4852399 = 7278599) B7278599
theorem B3836591 : Blo 1008601 3836591 := bstep (se 1 (by rfl) ⟨2877443, by rfl⟩ : syracuseStep 3836591 = 5754887) B5754887
theorem B2591507 : Blo 1008601 2591507 := bstep (se 1 (by rfl) ⟨1943630, by rfl⟩ : syracuseStep 2591507 = 3887261) B3887261
theorem B5606167 : Blo 1008601 5606167 := bstep (se 1 (by rfl) ⟨4204625, by rfl⟩ : syracuseStep 5606167 = 8409251) B8409251
theorem B2558891 : Blo 1008601 2558891 := bstep (se 1 (by rfl) ⟨1919168, by rfl⟩ : syracuseStep 2558891 = 3838337) B3838337
theorem B2559073 : Blo 1008601 2559073 := bstep (se 2 (by rfl) ⟨959652, by rfl⟩ : syracuseStep 2559073 = 1919305) B1919305
theorem B3411449 : Blo 1008601 3411449 := bstep (se 2 (by rfl) ⟨1279293, by rfl⟩ : syracuseStep 3411449 = 2558587) B2558587
theorem B5115473 : Blo 1008601 5115473 := bstep (se 2 (by rfl) ⟨1918302, by rfl⟩ : syracuseStep 5115473 = 3836605) B3836605
theorem B10948259 : Blo 1008601 10948259 := bstep (se 1 (by rfl) ⟨8211194, by rfl⟩ : syracuseStep 10948259 = 16422389) B16422389
theorem B2592491 : Blo 1008601 2592491 := bstep (se 1 (by rfl) ⟨1944368, by rfl⟩ : syracuseStep 2592491 = 3888737) B3888737
theorem B3411719 : Blo 1008601 3411719 := bstep (se 1 (by rfl) ⟨2558789, by rfl⟩ : syracuseStep 3411719 = 5117579) B5117579
theorem B1707817 : Blo 1008601 1707817 := bstep (se 2 (by rfl) ⟨640431, by rfl⟩ : syracuseStep 1707817 = 1280863) B1280863
theorem B3411773 : Blo 1008601 3411773 := bstep (se 3 (by rfl) ⟨639707, by rfl⟩ : syracuseStep 3411773 = 1279415) B1279415
theorem B2592719 : Blo 1008601 2592719 := bstep (se 1 (by rfl) ⟨1944539, by rfl⟩ : syracuseStep 2592719 = 3889079) B3889079
theorem B2560025 : Blo 1008601 2560025 := bstep (se 2 (by rfl) ⟨960009, by rfl⟩ : syracuseStep 2560025 = 1920019) B1920019
theorem B2560481 : Blo 1008601 2560481 := bstep (se 2 (by rfl) ⟨960180, by rfl⟩ : syracuseStep 2560481 = 1920361) B1920361
theorem B2560531 : Blo 1008601 2560531 := bstep (se 1 (by rfl) ⟨1920398, by rfl⟩ : syracuseStep 2560531 = 3840797) B3840797
theorem B1708607 : Blo 1008601 1708607 := bstep (se 1 (by rfl) ⟨1281455, by rfl⟩ : syracuseStep 1708607 = 2562911) B2562911
theorem B3838535 : Blo 1008601 3838535 := bstep (se 1 (by rfl) ⟨2878901, by rfl⟩ : syracuseStep 3838535 = 5757803) B5757803
theorem B4100831 : Blo 1008601 4100831 := bstep (se 1 (by rfl) ⟨3075623, by rfl⟩ : syracuseStep 4100831 = 6151247) B6151247
theorem B1643899 : Blo 1008601 1643899 := bstep (se 1 (by rfl) ⟨1232924, by rfl⟩ : syracuseStep 1643899 = 2465849) B2465849
theorem B1512953 : Blo 1008601 1512953 := bstep (se 2 (by rfl) ⟨567357, by rfl⟩ : syracuseStep 1512953 = 1134715) B1134715
theorem B1513055 : Blo 1008601 1513055 := bstep (se 1 (by rfl) ⟨1134791, by rfl⟩ : syracuseStep 1513055 = 2269583) B2269583
theorem B11671285 : Blo 1008601 11671285 := bstep (se 5 (by rfl) ⟨547091, by rfl⟩ : syracuseStep 11671285 = 1094183) B1094183
theorem B1513271 : Blo 1008601 1513271 := bstep (se 1 (by rfl) ⟨1134953, by rfl⟩ : syracuseStep 1513271 = 2269907) B2269907
theorem B3839825 : Blo 1008601 3839825 := bstep (se 2 (by rfl) ⟨1439934, by rfl⟩ : syracuseStep 3839825 = 2879869) B2879869
theorem B11245405 : Blo 1008601 11245405 := bstep (se 3 (by rfl) ⟨2108513, by rfl⟩ : syracuseStep 11245405 = 4217027) B4217027
theorem B5117903 : Blo 1008601 5117903 := bstep (se 1 (by rfl) ⟨3838427, by rfl⟩ : syracuseStep 5117903 = 7676855) B7676855
theorem B4102177 : Blo 1008601 4102177 := bstep (se 2 (by rfl) ⟨1538316, by rfl⟩ : syracuseStep 4102177 = 3076633) B3076633
theorem B1513577 : Blo 1008601 1513577 := bstep (se 2 (by rfl) ⟨567591, by rfl⟩ : syracuseStep 1513577 = 1135183) B1135183
theorem B2562313 : Blo 1008601 2562313 := bstep (se 2 (by rfl) ⟨960867, by rfl⟩ : syracuseStep 2562313 = 1921735) B1921735
theorem B11507993 : Blo 1008601 11507993 := bstep (se 2 (by rfl) ⟨4315497, by rfl⟩ : syracuseStep 11507993 = 8630995) B8630995
theorem B3840281 : Blo 1008601 3840281 := bstep (se 2 (by rfl) ⟨1440105, by rfl⟩ : syracuseStep 3840281 = 2880211) B2880211
theorem B1513895 : Blo 1008601 1513895 := bstep (se 1 (by rfl) ⟨1135421, by rfl⟩ : syracuseStep 1513895 = 2270843) B2270843
theorem B1513979 : Blo 1008601 1513979 := bstep (se 1 (by rfl) ⟨1135484, by rfl⟩ : syracuseStep 1513979 = 2270969) B2270969
theorem B3414635 : Blo 1008601 3414635 := bstep (se 1 (by rfl) ⟨2560976, by rfl⟩ : syracuseStep 3414635 = 5121953) B5121953
theorem B1514105 : Blo 1008601 1514105 := bstep (se 2 (by rfl) ⟨567789, by rfl⟩ : syracuseStep 1514105 = 1135579) B1135579
theorem B1514159 : Blo 1008601 1514159 := bstep (se 1 (by rfl) ⟨1135619, by rfl⟩ : syracuseStep 1514159 = 2271239) B2271239
theorem B1514207 : Blo 1008601 1514207 := bstep (se 1 (by rfl) ⟨1135655, by rfl⟩ : syracuseStep 1514207 = 2271311) B2271311
theorem B20781967 : Blo 1008601 20781967 := bstep (se 1 (by rfl) ⟨15586475, by rfl⟩ : syracuseStep 20781967 = 31172951) B31172951
theorem B5118875 : Blo 1008601 5118875 := bstep (se 1 (by rfl) ⟨3839156, by rfl⟩ : syracuseStep 5118875 = 7678313) B7678313
theorem B1514471 : Blo 1008601 1514471 := bstep (se 1 (by rfl) ⟨1135853, by rfl⟩ : syracuseStep 1514471 = 2271707) B2271707
theorem B3284107 : Blo 1008601 3284107 := bstep (se 1 (by rfl) ⟨2463080, by rfl⟩ : syracuseStep 3284107 = 4926161) B4926161
theorem B3644605 : Blo 1008601 3644605 := bstep (se 3 (by rfl) ⟨683363, by rfl⟩ : syracuseStep 3644605 = 1366727) B1366727
theorem B3415229 : Blo 1008601 3415229 := bstep (se 3 (by rfl) ⟨640355, by rfl⟩ : syracuseStep 3415229 = 1280711) B1280711
theorem B1514729 : Blo 1008601 1514729 := bstep (se 2 (by rfl) ⟨568023, by rfl⟩ : syracuseStep 1514729 = 1136047) B1136047
theorem B1514783 : Blo 1008601 1514783 := bstep (se 1 (by rfl) ⟨1136087, by rfl⟩ : syracuseStep 1514783 = 2272175) B2272175
theorem B2432351 : Blo 1008601 2432351 := bstep (se 1 (by rfl) ⟨1824263, by rfl⟩ : syracuseStep 2432351 = 3648527) B3648527
theorem B2301281 : Blo 1008601 2301281 := bstep (se 2 (by rfl) ⟨862980, by rfl⟩ : syracuseStep 2301281 = 1725961) B1725961
theorem B5119361 : Blo 1008601 5119361 := bstep (se 2 (by rfl) ⟨1919760, by rfl⟩ : syracuseStep 5119361 = 3839521) B3839521
theorem B1514951 : Blo 1008601 1514951 := bstep (se 1 (by rfl) ⟨1136213, by rfl⟩ : syracuseStep 1514951 = 2272427) B2272427
theorem B1515305 : Blo 1008601 1515305 := bstep (se 2 (by rfl) ⟨568239, by rfl⟩ : syracuseStep 1515305 = 1136479) B1136479
theorem B1515311 : Blo 1008601 1515311 := bstep (se 1 (by rfl) ⟨1136483, by rfl⟩ : syracuseStep 1515311 = 2272967) B2272967
theorem B5120009 : Blo 1008601 5120009 := bstep (se 2 (by rfl) ⟨1920003, by rfl⟩ : syracuseStep 5120009 = 3840007) B3840007
theorem B5120171 : Blo 1008601 5120171 := bstep (se 1 (by rfl) ⟨3840128, by rfl⟩ : syracuseStep 5120171 = 7680257) B7680257
theorem B1515785 : Blo 1008601 1515785 := bstep (se 2 (by rfl) ⟨568419, by rfl⟩ : syracuseStep 1515785 = 1136839) B1136839
theorem B2269547 : Blo 1008601 2269547 := bstep (se 1 (by rfl) ⟨1702160, by rfl⟩ : syracuseStep 2269547 = 3404321) B3404321
theorem B1515887 : Blo 1008601 1515887 := bstep (se 1 (by rfl) ⟨1136915, by rfl⟩ : syracuseStep 1515887 = 2273831) B2273831
theorem B2269691 : Blo 1008601 2269691 := bstep (se 1 (by rfl) ⟨1702268, by rfl⟩ : syracuseStep 2269691 = 3404537) B3404537
theorem B1516103 : Blo 1008601 1516103 := bstep (se 1 (by rfl) ⟨1137077, by rfl⟩ : syracuseStep 1516103 = 2274155) B2274155
theorem B1024583 : Blo 1008601 1024583 := bstep (se 1 (by rfl) ⟨768437, by rfl⟩ : syracuseStep 1024583 = 1536875) B1536875
theorem B1516139 : Blo 1008601 1516139 := bstep (se 1 (by rfl) ⟨1137104, by rfl⟩ : syracuseStep 1516139 = 2274209) B2274209
theorem B2269817 : Blo 1008601 2269817 := bstep (se 2 (by rfl) ⟨851181, by rfl⟩ : syracuseStep 2269817 = 1702363) B1702363
theorem B5120657 : Blo 1008601 5120657 := bstep (se 2 (by rfl) ⟨1920246, by rfl⟩ : syracuseStep 5120657 = 3840493) B3840493
theorem B2269871 : Blo 1008601 2269871 := bstep (se 1 (by rfl) ⟨1702403, by rfl⟩ : syracuseStep 2269871 = 3404807) B3404807
theorem B2269943 : Blo 1008601 2269943 := bstep (se 1 (by rfl) ⟨1702457, by rfl⟩ : syracuseStep 2269943 = 3404915) B3404915
theorem B1516367 : Blo 1008601 1516367 := bstep (se 1 (by rfl) ⟨1137275, by rfl⟩ : syracuseStep 1516367 = 2274551) B2274551
theorem B2270123 : Blo 1008601 2270123 := bstep (se 1 (by rfl) ⟨1702592, by rfl⟩ : syracuseStep 2270123 = 3405185) B3405185
theorem B3843197 : Blo 1008601 3843197 := bstep (se 3 (by rfl) ⟨720599, by rfl⟩ : syracuseStep 3843197 = 1441199) B1441199
theorem B1516763 : Blo 1008601 1516763 := bstep (se 1 (by rfl) ⟨1137572, by rfl⟩ : syracuseStep 1516763 = 2275145) B2275145
theorem B7284077 : Blo 1008601 7284077 := bstep (se 3 (by rfl) ⟨1365764, by rfl⟩ : syracuseStep 7284077 = 2731529) B2731529
theorem B8627579 : Blo 1008601 8627579 := bstep (se 1 (by rfl) ⟨6470684, by rfl⟩ : syracuseStep 8627579 = 12941369) B12941369
theorem B1516937 : Blo 1008601 1516937 := bstep (se 2 (by rfl) ⟨568851, by rfl⟩ : syracuseStep 1516937 = 1137703) B1137703
theorem B2270663 : Blo 1008601 2270663 := bstep (se 1 (by rfl) ⟨1702997, by rfl⟩ : syracuseStep 2270663 = 3405995) B3405995
theorem B10921529 : Blo 1008601 10921529 := bstep (se 2 (by rfl) ⟨4095573, by rfl⟩ : syracuseStep 10921529 = 8191147) B8191147
theorem B29140681 : Blo 1008601 29140681 := bstep (se 2 (by rfl) ⟨10927755, by rfl⟩ : syracuseStep 29140681 = 21855511) B21855511
theorem B1517291 : Blo 1008601 1517291 := bstep (se 1 (by rfl) ⟨1137968, by rfl⟩ : syracuseStep 1517291 = 2275937) B2275937
theorem B2271023 : Blo 1008601 2271023 := bstep (se 1 (by rfl) ⟨1703267, by rfl⟩ : syracuseStep 2271023 = 3406535) B3406535
theorem B3843895 : Blo 1008601 3843895 := bstep (se 1 (by rfl) ⟨2882921, by rfl⟩ : syracuseStep 3843895 = 5765843) B5765843
theorem B1386319 : Blo 1008601 1386319 := bstep (se 1 (by rfl) ⟨1039739, by rfl⟩ : syracuseStep 1386319 = 2079479) B2079479
theorem B1517519 : Blo 1008601 1517519 := bstep (se 1 (by rfl) ⟨1138139, by rfl⟩ : syracuseStep 1517519 = 2276279) B2276279
theorem B3844381 : Blo 1008601 3844381 := bstep (se 3 (by rfl) ⟨720821, by rfl⟩ : syracuseStep 3844381 = 1441643) B1441643
theorem B1517915 : Blo 1008601 1517915 := bstep (se 1 (by rfl) ⟨1138436, by rfl⟩ : syracuseStep 1517915 = 2276873) B2276873
theorem B2271599 : Blo 1008601 2271599 := bstep (se 1 (by rfl) ⟨1703699, by rfl⟩ : syracuseStep 2271599 = 3407399) B3407399
theorem B2271671 : Blo 1008601 2271671 := bstep (se 1 (by rfl) ⟨1703753, by rfl⟩ : syracuseStep 2271671 = 3407507) B3407507
theorem B1518143 : Blo 1008601 1518143 := bstep (se 1 (by rfl) ⟨1138607, by rfl⟩ : syracuseStep 1518143 = 2277215) B2277215
theorem B2271815 : Blo 1008601 2271815 := bstep (se 1 (by rfl) ⟨1703861, by rfl⟩ : syracuseStep 2271815 = 3407723) B3407723
theorem B2271851 : Blo 1008601 2271851 := bstep (se 1 (by rfl) ⟨1703888, by rfl⟩ : syracuseStep 2271851 = 3407777) B3407777
theorem B1518263 : Blo 1008601 1518263 := bstep (se 1 (by rfl) ⟨1138697, by rfl⟩ : syracuseStep 1518263 = 2277395) B2277395
theorem B5745431 : Blo 1008601 5745431 := bstep (se 1 (by rfl) ⟨4309073, by rfl⟩ : syracuseStep 5745431 = 8618147) B8618147
theorem B1518491 : Blo 1008601 1518491 := bstep (se 1 (by rfl) ⟨1138868, by rfl⟩ : syracuseStep 1518491 = 2277737) B2277737
theorem B2272247 : Blo 1008601 2272247 := bstep (se 1 (by rfl) ⟨1704185, by rfl⟩ : syracuseStep 2272247 = 3408371) B3408371
theorem B5123087 : Blo 1008601 5123087 := bstep (se 1 (by rfl) ⟨3842315, by rfl⟩ : syracuseStep 5123087 = 7684631) B7684631
theorem B1518887 : Blo 1008601 1518887 := bstep (se 1 (by rfl) ⟨1139165, by rfl⟩ : syracuseStep 1518887 = 2278331) B2278331
theorem B2272607 : Blo 1008601 2272607 := bstep (se 1 (by rfl) ⟨1704455, by rfl⟩ : syracuseStep 2272607 = 3408911) B3408911
theorem B4369793 : Blo 1008601 4369793 := bstep (se 2 (by rfl) ⟨1638672, by rfl⟩ : syracuseStep 4369793 = 3277345) B3277345
theorem B49262093 : Blo 1008601 49262093 := bstep (se 3 (by rfl) ⟨9236642, by rfl⟩ : syracuseStep 49262093 = 18473285) B18473285
theorem B2273003 : Blo 1008601 2273003 := bstep (se 1 (by rfl) ⟨1704752, by rfl⟩ : syracuseStep 2273003 = 3409505) B3409505
theorem B5123897 : Blo 1008601 5123897 := bstep (se 2 (by rfl) ⟨1921461, by rfl⟩ : syracuseStep 5123897 = 3842923) B3842923
theorem B2273129 : Blo 1008601 2273129 := bstep (se 2 (by rfl) ⟨852423, by rfl⟩ : syracuseStep 2273129 = 1704847) B1704847
theorem B2732395 : Blo 1008601 2732395 := bstep (se 1 (by rfl) ⟨2049296, by rfl⟩ : syracuseStep 2732395 = 4098593) B4098593
theorem B16593457 : Blo 1008601 16593457 := bstep (se 2 (by rfl) ⟨6222546, by rfl⟩ : syracuseStep 16593457 = 12445093) B12445093
theorem B2273975 : Blo 1008601 2273975 := bstep (se 1 (by rfl) ⟨1705481, by rfl⟩ : syracuseStep 2273975 = 3410963) B3410963
theorem B17478389 : Blo 1008601 17478389 := bstep (se 5 (by rfl) ⟨819299, by rfl⟩ : syracuseStep 17478389 = 1638599) B1638599
theorem B9843565 : Blo 1008601 9843565 := bstep (se 3 (by rfl) ⟨1845668, by rfl⟩ : syracuseStep 9843565 = 3691337) B3691337
theorem B2274191 : Blo 1008601 2274191 := bstep (se 1 (by rfl) ⟨1705643, by rfl⟩ : syracuseStep 2274191 = 3411287) B3411287
theorem B8631269 : Blo 1008601 8631269 := bstep (se 4 (by rfl) ⟨809181, by rfl⟩ : syracuseStep 8631269 = 1618363) B1618363
theorem B2274911 : Blo 1008601 2274911 := bstep (se 1 (by rfl) ⟨1706183, by rfl⟩ : syracuseStep 2274911 = 3412367) B3412367
theorem B2275127 : Blo 1008601 2275127 := bstep (se 1 (by rfl) ⟨1706345, by rfl⟩ : syracuseStep 2275127 = 3412691) B3412691
theorem B2308105 : Blo 1008601 2308105 := bstep (se 2 (by rfl) ⟨865539, by rfl⟩ : syracuseStep 2308105 = 1731079) B1731079
theorem B98449445 : Blo 1008601 98449445 := bstep (se 4 (by rfl) ⟨9229635, by rfl⟩ : syracuseStep 98449445 = 18459271) B18459271
theorem B2275433 : Blo 1008601 2275433 := bstep (se 2 (by rfl) ⟨853287, by rfl⟩ : syracuseStep 2275433 = 1706575) B1706575
theorem B5454191 : Blo 1008601 5454191 := bstep (se 1 (by rfl) ⟨4090643, by rfl⟩ : syracuseStep 5454191 = 8181287) B8181287
theorem B1915463 : Blo 1008601 1915463 := bstep (se 1 (by rfl) ⟨1436597, by rfl⟩ : syracuseStep 1915463 = 2873195) B2873195
theorem B2275919 : Blo 1008601 2275919 := bstep (se 1 (by rfl) ⟨1706939, by rfl⟩ : syracuseStep 2275919 = 3413879) B3413879
theorem B2276063 : Blo 1008601 2276063 := bstep (se 1 (by rfl) ⟨1707047, by rfl⟩ : syracuseStep 2276063 = 3414095) B3414095
theorem B2276315 : Blo 1008601 2276315 := bstep (se 1 (by rfl) ⟨1707236, by rfl⟩ : syracuseStep 2276315 = 3414473) B3414473
theorem B9223217 : Blo 1008601 9223217 := bstep (se 2 (by rfl) ⟨3458706, by rfl⟩ : syracuseStep 9223217 = 6917413) B6917413
theorem B2276495 : Blo 1008601 2276495 := bstep (se 1 (by rfl) ⟨1707371, by rfl⟩ : syracuseStep 2276495 = 3414743) B3414743
theorem B5258429 : Blo 1008601 5258429 := bstep (se 3 (by rfl) ⟨985955, by rfl⟩ : syracuseStep 5258429 = 1971911) B1971911
theorem B1817833 : Blo 1008601 1817833 := bstep (se 2 (by rfl) ⟨681687, by rfl⟩ : syracuseStep 1817833 = 1363375) B1363375
theorem B2276585 : Blo 1008601 2276585 := bstep (se 2 (by rfl) ⟨853719, by rfl⟩ : syracuseStep 2276585 = 1707439) B1707439
theorem B2276639 : Blo 1008601 2276639 := bstep (se 1 (by rfl) ⟨1707479, by rfl⟩ : syracuseStep 2276639 = 3414959) B3414959
theorem B6471251 : Blo 1008601 6471251 := bstep (se 1 (by rfl) ⟨4853438, by rfl⟩ : syracuseStep 6471251 = 9706877) B9706877
theorem B4439819 : Blo 1008601 4439819 := bstep (se 1 (by rfl) ⟨3329864, by rfl⟩ : syracuseStep 4439819 = 6659729) B6659729
theorem B2277161 : Blo 1008601 2277161 := bstep (se 2 (by rfl) ⟨853935, by rfl⟩ : syracuseStep 2277161 = 1707871) B1707871
theorem B7684145 : Blo 1008601 7684145 := bstep (se 2 (by rfl) ⟨2881554, by rfl⟩ : syracuseStep 7684145 = 5763109) B5763109
theorem B2048105 : Blo 1008601 2048105 := bstep (se 2 (by rfl) ⟨768039, by rfl⟩ : syracuseStep 2048105 = 1536079) B1536079
theorem B2048695 : Blo 1008601 2048695 := bstep (se 1 (by rfl) ⟨1536521, by rfl⟩ : syracuseStep 2048695 = 3073043) B3073043
theorem B2278223 : Blo 1008601 2278223 := bstep (se 1 (by rfl) ⟨1708667, by rfl⟩ : syracuseStep 2278223 = 3417335) B3417335
theorem B2048923 : Blo 1008601 2048923 := bstep (se 1 (by rfl) ⟨1536692, by rfl⟩ : syracuseStep 2048923 = 3073385) B3073385
theorem B1819867 : Blo 1008601 1819867 := bstep (se 1 (by rfl) ⟨1364900, by rfl⟩ : syracuseStep 1819867 = 2729801) B2729801
theorem B11683109 : Blo 1008601 11683109 := bstep (se 4 (by rfl) ⟨1095291, by rfl⟩ : syracuseStep 11683109 = 2190583) B2190583
theorem B4310509 : Blo 1008601 4310509 := bstep (se 3 (by rfl) ⟨808220, by rfl⟩ : syracuseStep 4310509 = 1616441) B1616441
theorem B2049799 : Blo 1008601 2049799 := bstep (se 1 (by rfl) ⟨1537349, by rfl⟩ : syracuseStep 2049799 = 3074699) B3074699
theorem B17483791 : Blo 1008601 17483791 := bstep (se 1 (by rfl) ⟨13112843, by rfl⟩ : syracuseStep 17483791 = 26225687) B26225687
theorem B1919609 : Blo 1008601 1919609 := bstep (se 2 (by rfl) ⟨719853, by rfl⟩ : syracuseStep 1919609 = 1439707) B1439707
theorem B9718481 : Blo 1008601 9718481 := bstep (se 2 (by rfl) ⟨3644430, by rfl⟩ : syracuseStep 9718481 = 7288861) B7288861
theorem B5458843 : Blo 1008601 5458843 := bstep (se 1 (by rfl) ⟨4094132, by rfl⟩ : syracuseStep 5458843 = 8188265) B8188265
theorem B3231191 : Blo 1008601 3231191 := bstep (se 1 (by rfl) ⟨2423393, by rfl⟩ : syracuseStep 3231191 = 4846787) B4846787
theorem B1920505 : Blo 1008601 1920505 := bstep (se 2 (by rfl) ⟨720189, by rfl⟩ : syracuseStep 1920505 = 1440379) B1440379
theorem B5459471 : Blo 1008601 5459471 := bstep (se 1 (by rfl) ⟨4094603, by rfl⟩ : syracuseStep 5459471 = 8189207) B8189207
theorem B5754635 : Blo 1008601 5754635 := bstep (se 1 (by rfl) ⟨4315976, by rfl⟩ : syracuseStep 5754635 = 8631953) B8631953
theorem B1920809 : Blo 1008601 1920809 := bstep (se 2 (by rfl) ⟨720303, by rfl⟩ : syracuseStep 1920809 = 1440607) B1440607
theorem B21843755 : Blo 1008601 21843755 := bstep (se 1 (by rfl) ⟨16382816, by rfl⟩ : syracuseStep 21843755 = 32765633) B32765633
theorem B29479241 : Blo 1008601 29479241 := bstep (se 2 (by rfl) ⟨11054715, by rfl⟩ : syracuseStep 29479241 = 22109431) B22109431
theorem B15585853 : Blo 1008601 15585853 := bstep (se 3 (by rfl) ⟨2922347, by rfl⟩ : syracuseStep 15585853 = 5844695) B5844695
theorem B1823305 : Blo 1008601 1823305 := bstep (se 2 (by rfl) ⟨683739, by rfl⟩ : syracuseStep 1823305 = 1367479) B1367479
theorem B1135327 : Blo 1008601 1135327 := bstep (se 1 (by rfl) ⟨851495, by rfl⟩ : syracuseStep 1135327 = 1702991) B1702991
theorem B1921963 : Blo 1008601 1921963 := bstep (se 1 (by rfl) ⟨1441472, by rfl⟩ : syracuseStep 1921963 = 2882945) B2882945
theorem B1922039 : Blo 1008601 1922039 := bstep (se 1 (by rfl) ⟨1441529, by rfl⟩ : syracuseStep 1922039 = 2883059) B2883059
theorem B3200143 : Blo 1008601 3200143 := bstep (se 1 (by rfl) ⟨2400107, by rfl⟩ : syracuseStep 3200143 = 4800215) B4800215
theorem B1922267 : Blo 1008601 1922267 := bstep (se 1 (by rfl) ⟨1441700, by rfl⟩ : syracuseStep 1922267 = 2883401) B2883401
theorem B1135903 : Blo 1008601 1135903 := bstep (se 1 (by rfl) ⟨851927, by rfl⟩ : syracuseStep 1135903 = 1703855) B1703855
theorem B4150651 : Blo 1008601 4150651 := bstep (se 1 (by rfl) ⟨3112988, by rfl⟩ : syracuseStep 4150651 = 6225977) B6225977
theorem B11818541 : Blo 1008601 11818541 := bstep (se 3 (by rfl) ⟨2215976, by rfl⟩ : syracuseStep 11818541 = 4431953) B4431953
theorem B1136191 : Blo 1008601 1136191 := bstep (se 1 (by rfl) ⟨852143, by rfl⟩ : syracuseStep 1136191 = 1704287) B1704287
theorem B1137019 : Blo 1008601 1137019 := bstep (se 1 (by rfl) ⟨852764, by rfl⟩ : syracuseStep 1137019 = 1705529) B1705529
theorem B4315771 : Blo 1008601 4315771 := bstep (se 1 (by rfl) ⟨3236828, by rfl⟩ : syracuseStep 4315771 = 6473657) B6473657
theorem B1137487 : Blo 1008601 1137487 := bstep (se 1 (by rfl) ⟨853115, by rfl⟩ : syracuseStep 1137487 = 1706231) B1706231
theorem B224386199 : Blo 1008601 224386199 := bstep (se 1 (by rfl) ⟨168289649, by rfl⟩ : syracuseStep 224386199 = 336579299) B336579299
theorem B1137883 : Blo 1008601 1137883 := bstep (se 1 (by rfl) ⟨853412, by rfl⟩ : syracuseStep 1137883 = 1706825) B1706825
theorem B1138171 : Blo 1008601 1138171 := bstep (se 1 (by rfl) ⟨853628, by rfl⟩ : syracuseStep 1138171 = 1707257) B1707257
theorem B1138351 : Blo 1008601 1138351 := bstep (se 1 (by rfl) ⟨853763, by rfl⟩ : syracuseStep 1138351 = 1707527) B1707527
theorem B1138639 : Blo 1008601 1138639 := bstep (se 1 (by rfl) ⟨853979, by rfl⟩ : syracuseStep 1138639 = 1707959) B1707959
theorem B1139035 : Blo 1008601 1139035 := bstep (se 1 (by rfl) ⟨854276, by rfl⟩ : syracuseStep 1139035 = 1708553) B1708553
theorem B1139143 : Blo 1008601 1139143 := bstep (se 1 (by rfl) ⟨854357, by rfl⟩ : syracuseStep 1139143 = 1708715) B1708715
theorem B14541281 : Blo 1008601 14541281 := bstep (se 2 (by rfl) ⟨5452980, by rfl⟩ : syracuseStep 14541281 = 10905961) B10905961
theorem B6152705 : Blo 1008601 6152705 := bstep (se 2 (by rfl) ⟨2307264, by rfl⟩ : syracuseStep 6152705 = 4614529) B4614529
theorem B2876087 : Blo 1008601 2876087 := bstep (se 1 (by rfl) ⟨2157065, by rfl⟩ : syracuseStep 2876087 = 4314131) B4314131
theorem B1008615 : Blo 1008601 1008615 := bstep (se 1 (by rfl) ⟨756461, by rfl⟩ : syracuseStep 1008615 = 1512923) B1512923
theorem B2155511 : Blo 1008601 2155511 := bstep (se 1 (by rfl) ⟨1616633, by rfl⟩ : syracuseStep 2155511 = 3233267) B3233267
theorem B5465245 : Blo 1008601 5465245 := bstep (se 3 (by rfl) ⟨1024733, by rfl⟩ : syracuseStep 5465245 = 2049467) B2049467
theorem B1008927 : Blo 1008601 1008927 := bstep (se 1 (by rfl) ⟨756695, by rfl⟩ : syracuseStep 1008927 = 1513391) B1513391
theorem B1008987 : Blo 1008601 1008987 := bstep (se 1 (by rfl) ⟨756740, by rfl⟩ : syracuseStep 1008987 = 1513481) B1513481
theorem B1009007 : Blo 1008601 1009007 := bstep (se 1 (by rfl) ⟨756755, by rfl⟩ : syracuseStep 1009007 = 1513511) B1513511
theorem B1009063 : Blo 1008601 1009063 := bstep (se 1 (by rfl) ⟨756797, by rfl⟩ : syracuseStep 1009063 = 1513595) B1513595
theorem B32826869 : Blo 1008601 32826869 := bstep (se 5 (by rfl) ⟨1538759, by rfl⟩ : syracuseStep 32826869 = 3077519) B3077519
theorem B1009147 : Blo 1008601 1009147 := bstep (se 1 (by rfl) ⟨756860, by rfl⟩ : syracuseStep 1009147 = 1513721) B1513721
theorem B1009215 : Blo 1008601 1009215 := bstep (se 1 (by rfl) ⟨756911, by rfl⟩ : syracuseStep 1009215 = 1513823) B1513823
theorem B1009223 : Blo 1008601 1009223 := bstep (se 1 (by rfl) ⟨756917, by rfl⟩ : syracuseStep 1009223 = 1513835) B1513835
theorem B1009375 : Blo 1008601 1009375 := bstep (se 1 (by rfl) ⟨757031, by rfl⟩ : syracuseStep 1009375 = 1514063) B1514063
theorem B1009455 : Blo 1008601 1009455 := bstep (se 1 (by rfl) ⟨757091, by rfl⟩ : syracuseStep 1009455 = 1514183) B1514183
theorem B9725831 : Blo 1008601 9725831 := bstep (se 1 (by rfl) ⟨7294373, by rfl⟩ : syracuseStep 9725831 = 14588747) B14588747
theorem B1009563 : Blo 1008601 1009563 := bstep (se 1 (by rfl) ⟨757172, by rfl⟩ : syracuseStep 1009563 = 1514345) B1514345
theorem B1009615 : Blo 1008601 1009615 := bstep (se 1 (by rfl) ⟨757211, by rfl⟩ : syracuseStep 1009615 = 1514423) B1514423
theorem B1009639 : Blo 1008601 1009639 := bstep (se 1 (by rfl) ⟨757229, by rfl⟩ : syracuseStep 1009639 = 1514459) B1514459
theorem B52553843 : Blo 1008601 52553843 := bstep (se 1 (by rfl) ⟨39415382, by rfl⟩ : syracuseStep 52553843 = 78830765) B78830765
theorem B2877569 : Blo 1008601 2877569 := bstep (se 2 (by rfl) ⟨1079088, by rfl⟩ : syracuseStep 2877569 = 2158177) B2158177
theorem B9464003 : Blo 1008601 9464003 := bstep (se 1 (by rfl) ⟨7098002, by rfl⟩ : syracuseStep 9464003 = 14196005) B14196005
theorem B1009951 : Blo 1008601 1009951 := bstep (se 1 (by rfl) ⟨757463, by rfl⟩ : syracuseStep 1009951 = 1514927) B1514927
theorem B12970277 : Blo 1008601 12970277 := bstep (se 4 (by rfl) ⟨1215963, by rfl⟩ : syracuseStep 12970277 = 2431927) B2431927
theorem B1010011 : Blo 1008601 1010011 := bstep (se 1 (by rfl) ⟨757508, by rfl⟩ : syracuseStep 1010011 = 1515017) B1515017
theorem B1010031 : Blo 1008601 1010031 := bstep (se 1 (by rfl) ⟨757523, by rfl⟩ : syracuseStep 1010031 = 1515047) B1515047
theorem B1010087 : Blo 1008601 1010087 := bstep (se 1 (by rfl) ⟨757565, by rfl⟩ : syracuseStep 1010087 = 1515131) B1515131
theorem B3238355 : Blo 1008601 3238355 := bstep (se 1 (by rfl) ⟨2428766, by rfl⟩ : syracuseStep 3238355 = 4857533) B4857533
theorem B8645075 : Blo 1008601 8645075 := bstep (se 1 (by rfl) ⟨6483806, by rfl⟩ : syracuseStep 8645075 = 12967613) B12967613
theorem B1010171 : Blo 1008601 1010171 := bstep (se 1 (by rfl) ⟨757628, by rfl⟩ : syracuseStep 1010171 = 1515257) B1515257
theorem B39414275 : Blo 1008601 39414275 := bstep (se 1 (by rfl) ⟨29560706, by rfl⟩ : syracuseStep 39414275 = 59121413) B59121413
theorem B5106239 : Blo 1008601 5106239 := bstep (se 1 (by rfl) ⟨3829679, by rfl⟩ : syracuseStep 5106239 = 7659359) B7659359
theorem B1010239 : Blo 1008601 1010239 := bstep (se 1 (by rfl) ⟨757679, by rfl⟩ : syracuseStep 1010239 = 1515359) B1515359
theorem B1010247 : Blo 1008601 1010247 := bstep (se 1 (by rfl) ⟨757685, by rfl⟩ : syracuseStep 1010247 = 1515371) B1515371
theorem B1010399 : Blo 1008601 1010399 := bstep (se 1 (by rfl) ⟨757799, by rfl⟩ : syracuseStep 1010399 = 1515599) B1515599
theorem B1010479 : Blo 1008601 1010479 := bstep (se 1 (by rfl) ⟨757859, by rfl⟩ : syracuseStep 1010479 = 1515719) B1515719
theorem B1010587 : Blo 1008601 1010587 := bstep (se 1 (by rfl) ⟨757940, by rfl⟩ : syracuseStep 1010587 = 1515881) B1515881
theorem B1010639 : Blo 1008601 1010639 := bstep (se 1 (by rfl) ⟨757979, by rfl⟩ : syracuseStep 1010639 = 1515959) B1515959
theorem B1010663 : Blo 1008601 1010663 := bstep (se 1 (by rfl) ⟨757997, by rfl⟩ : syracuseStep 1010663 = 1515995) B1515995
theorem B1010975 : Blo 1008601 1010975 := bstep (se 1 (by rfl) ⟨758231, by rfl⟩ : syracuseStep 1010975 = 1516463) B1516463
theorem B1011035 : Blo 1008601 1011035 := bstep (se 1 (by rfl) ⟨758276, by rfl⟩ : syracuseStep 1011035 = 1516553) B1516553
theorem B1011055 : Blo 1008601 1011055 := bstep (se 1 (by rfl) ⟨758291, by rfl⟩ : syracuseStep 1011055 = 1516583) B1516583
theorem B8744321 : Blo 1008601 8744321 := bstep (se 2 (by rfl) ⟨3279120, by rfl⟩ : syracuseStep 8744321 = 6558241) B6558241
theorem B1011111 : Blo 1008601 1011111 := bstep (se 1 (by rfl) ⟨758333, by rfl⟩ : syracuseStep 1011111 = 1516667) B1516667
theorem B6909371 : Blo 1008601 6909371 := bstep (se 1 (by rfl) ⟨5182028, by rfl⟩ : syracuseStep 6909371 = 10364057) B10364057
theorem B1011195 : Blo 1008601 1011195 := bstep (se 1 (by rfl) ⟨758396, by rfl⟩ : syracuseStep 1011195 = 1516793) B1516793
theorem B1011263 : Blo 1008601 1011263 := bstep (se 1 (by rfl) ⟨758447, by rfl⟩ : syracuseStep 1011263 = 1516895) B1516895
theorem B1011271 : Blo 1008601 1011271 := bstep (se 1 (by rfl) ⟨758453, by rfl⟩ : syracuseStep 1011271 = 1516907) B1516907
theorem B3239585 : Blo 1008601 3239585 := bstep (se 2 (by rfl) ⟨1214844, by rfl⟩ : syracuseStep 3239585 = 2429689) B2429689
theorem B1011423 : Blo 1008601 1011423 := bstep (se 1 (by rfl) ⟨758567, by rfl⟩ : syracuseStep 1011423 = 1517135) B1517135
theorem B5467945 : Blo 1008601 5467945 := bstep (se 2 (by rfl) ⟨2050479, by rfl⟩ : syracuseStep 5467945 = 4100959) B4100959
theorem B1011503 : Blo 1008601 1011503 := bstep (se 1 (by rfl) ⟨758627, by rfl⟩ : syracuseStep 1011503 = 1517255) B1517255
theorem B1011611 : Blo 1008601 1011611 := bstep (se 1 (by rfl) ⟨758708, by rfl⟩ : syracuseStep 1011611 = 1517417) B1517417
theorem B1011663 : Blo 1008601 1011663 := bstep (se 1 (by rfl) ⟨758747, by rfl⟩ : syracuseStep 1011663 = 1517495) B1517495
theorem B1011687 : Blo 1008601 1011687 := bstep (se 1 (by rfl) ⟨758765, by rfl⟩ : syracuseStep 1011687 = 1517531) B1517531
theorem B3239995 : Blo 1008601 3239995 := bstep (se 1 (by rfl) ⟨2429996, by rfl⟩ : syracuseStep 3239995 = 4859993) B4859993
theorem B98299979 : Blo 1008601 98299979 := bstep (se 1 (by rfl) ⟨73724984, by rfl⟩ : syracuseStep 98299979 = 147449969) B147449969
theorem B9728171 : Blo 1008601 9728171 := bstep (se 1 (by rfl) ⟨7296128, by rfl⟩ : syracuseStep 9728171 = 14592257) B14592257
theorem B74805515 : Blo 1008601 74805515 := bstep (se 1 (by rfl) ⟨56104136, by rfl⟩ : syracuseStep 74805515 = 112208273) B112208273
theorem B1011999 : Blo 1008601 1011999 := bstep (se 1 (by rfl) ⟨758999, by rfl⟩ : syracuseStep 1011999 = 1517999) B1517999
theorem B3404105 : Blo 1008601 3404105 := bstep (se 2 (by rfl) ⟨1276539, by rfl⟩ : syracuseStep 3404105 = 2553079) B2553079
theorem B1012059 : Blo 1008601 1012059 := bstep (se 1 (by rfl) ⟨759044, by rfl⟩ : syracuseStep 1012059 = 1518089) B1518089
theorem B1012079 : Blo 1008601 1012079 := bstep (se 1 (by rfl) ⟨759059, by rfl⟩ : syracuseStep 1012079 = 1518119) B1518119
theorem B1012135 : Blo 1008601 1012135 := bstep (se 1 (by rfl) ⟨759101, by rfl⟩ : syracuseStep 1012135 = 1518203) B1518203
theorem B17494481 : Blo 1008601 17494481 := bstep (se 2 (by rfl) ⟨6560430, by rfl⟩ : syracuseStep 17494481 = 13120861) B13120861
theorem B1012219 : Blo 1008601 1012219 := bstep (se 1 (by rfl) ⟨759164, by rfl⟩ : syracuseStep 1012219 = 1518329) B1518329
theorem B3830273 : Blo 1008601 3830273 := bstep (se 2 (by rfl) ⟨1436352, by rfl⟩ : syracuseStep 3830273 = 2872705) B2872705
theorem B10908209 : Blo 1008601 10908209 := bstep (se 2 (by rfl) ⟨4090578, by rfl⟩ : syracuseStep 10908209 = 8181157) B8181157
theorem B5763635 : Blo 1008601 5763635 := bstep (se 1 (by rfl) ⟨4322726, by rfl⟩ : syracuseStep 5763635 = 8645453) B8645453
theorem B1012287 : Blo 1008601 1012287 := bstep (se 1 (by rfl) ⟨759215, by rfl⟩ : syracuseStep 1012287 = 1518431) B1518431
theorem B1012295 : Blo 1008601 1012295 := bstep (se 1 (by rfl) ⟨759221, by rfl⟩ : syracuseStep 1012295 = 1518443) B1518443
theorem B1536619 : Blo 1008601 1536619 := bstep (se 1 (by rfl) ⟨1152464, by rfl⟩ : syracuseStep 1536619 = 2304929) B2304929
theorem B5108345 : Blo 1008601 5108345 := bstep (se 2 (by rfl) ⟨1915629, by rfl⟩ : syracuseStep 5108345 = 3831259) B3831259
theorem B29094551 : Blo 1008601 29094551 := bstep (se 1 (by rfl) ⟨21820913, by rfl⟩ : syracuseStep 29094551 = 43641827) B43641827
theorem B4321991 : Blo 1008601 4321991 := bstep (se 1 (by rfl) ⟨3241493, by rfl⟩ : syracuseStep 4321991 = 6482987) B6482987
theorem B1012447 : Blo 1008601 1012447 := bstep (se 1 (by rfl) ⟨759335, by rfl⟩ : syracuseStep 1012447 = 1518671) B1518671
theorem B1012527 : Blo 1008601 1012527 := bstep (se 1 (by rfl) ⟨759395, by rfl⟩ : syracuseStep 1012527 = 1518791) B1518791
theorem B4617155 : Blo 1008601 4617155 := bstep (se 1 (by rfl) ⟨3462866, by rfl⟩ : syracuseStep 4617155 = 6925733) B6925733
theorem B3830759 : Blo 1008601 3830759 := bstep (se 1 (by rfl) ⟨2873069, by rfl⟩ : syracuseStep 3830759 = 5746139) B5746139
theorem B11531321 : Blo 1008601 11531321 := bstep (se 2 (by rfl) ⟨4324245, by rfl⟩ : syracuseStep 11531321 = 8648491) B8648491
theorem B4617577 : Blo 1008601 4617577 := bstep (se 2 (by rfl) ⟨1731591, by rfl⟩ : syracuseStep 4617577 = 3463183) B3463183
theorem B5469677 : Blo 1008601 5469677 := bstep (se 3 (by rfl) ⟨1025564, by rfl⟩ : syracuseStep 5469677 = 2051129) B2051129
theorem B11499245 : Blo 1008601 11499245 := bstep (se 3 (by rfl) ⟨2156108, by rfl⟩ : syracuseStep 11499245 = 4312217) B4312217
theorem B18708317 : Blo 1008601 18708317 := bstep (se 3 (by rfl) ⟨3507809, by rfl⟩ : syracuseStep 18708317 = 7015619) B7015619
theorem B2881487 : Blo 1008601 2881487 := bstep (se 1 (by rfl) ⟨2161115, by rfl⟩ : syracuseStep 2881487 = 4322231) B4322231
theorem B5765093 : Blo 1008601 5765093 := bstep (se 4 (by rfl) ⟨540477, by rfl⟩ : syracuseStep 5765093 = 1080955) B1080955
theorem B1702235 : Blo 1008601 1702235 := bstep (se 1 (by rfl) ⟨1276676, by rfl⟩ : syracuseStep 1702235 = 2553353) B2553353
theorem B1702255 : Blo 1008601 1702255 := bstep (se 1 (by rfl) ⟨1276691, by rfl⟩ : syracuseStep 1702255 = 2553383) B2553383
theorem B5110127 : Blo 1008601 5110127 := bstep (se 1 (by rfl) ⟨3832595, by rfl⟩ : syracuseStep 5110127 = 7665191) B7665191
theorem B3832231 : Blo 1008601 3832231 := bstep (se 1 (by rfl) ⟨2874173, by rfl⟩ : syracuseStep 3832231 = 5748347) B5748347
theorem B1800767 : Blo 1008601 1800767 := bstep (se 1 (by rfl) ⟨1350575, by rfl⟩ : syracuseStep 1800767 = 2701151) B2701151
theorem B1702471 : Blo 1008601 1702471 := bstep (se 1 (by rfl) ⟨1276853, by rfl⟩ : syracuseStep 1702471 = 2553707) B2553707
theorem B1276651 : Blo 1008601 1276651 := bstep (se 1 (by rfl) ⟨957488, by rfl⟩ : syracuseStep 1276651 = 1914977) B1914977
theorem B1276879 : Blo 1008601 1276879 := bstep (se 1 (by rfl) ⟨957659, by rfl⟩ : syracuseStep 1276879 = 1915319) B1915319
theorem B1702903 : Blo 1008601 1702903 := bstep (se 1 (by rfl) ⟨1277177, by rfl⟩ : syracuseStep 1702903 = 2554355) B2554355
theorem B4324367 : Blo 1008601 4324367 := bstep (se 1 (by rfl) ⟨3243275, by rfl⟩ : syracuseStep 4324367 = 6486551) B6486551
theorem B2555003 : Blo 1008601 2555003 := bstep (se 1 (by rfl) ⟨1916252, by rfl⟩ : syracuseStep 2555003 = 3832505) B3832505
theorem B2555023 : Blo 1008601 2555023 := bstep (se 1 (by rfl) ⟨1916267, by rfl⟩ : syracuseStep 2555023 = 3832535) B3832535
theorem B3833021 : Blo 1008601 3833021 := bstep (se 3 (by rfl) ⟨718691, by rfl⟩ : syracuseStep 3833021 = 1437383) B1437383
theorem B1277147 : Blo 1008601 1277147 := bstep (se 1 (by rfl) ⟨957860, by rfl⟩ : syracuseStep 1277147 = 1915721) B1915721
theorem B1703207 : Blo 1008601 1703207 := bstep (se 1 (by rfl) ⟨1277405, by rfl⟩ : syracuseStep 1703207 = 2554811) B2554811
theorem B2555297 : Blo 1008601 2555297 := bstep (se 2 (by rfl) ⟨958236, by rfl⟩ : syracuseStep 2555297 = 1916473) B1916473
theorem B3407291 : Blo 1008601 3407291 := bstep (se 1 (by rfl) ⟨2555468, by rfl⟩ : syracuseStep 3407291 = 5110937) B5110937
theorem B4095431 : Blo 1008601 4095431 := bstep (se 1 (by rfl) ⟨3071573, by rfl⟩ : syracuseStep 4095431 = 6143147) B6143147
theorem B4849247 : Blo 1008601 4849247 := bstep (se 1 (by rfl) ⟨3636935, by rfl⟩ : syracuseStep 4849247 = 7273871) B7273871
theorem B7274099 : Blo 1008601 7274099 := bstep (se 1 (by rfl) ⟨5455574, by rfl⟩ : syracuseStep 7274099 = 10911149) B10911149
theorem B1277623 : Blo 1008601 1277623 := bstep (se 1 (by rfl) ⟨958217, by rfl⟩ : syracuseStep 1277623 = 1916435) B1916435
theorem B1703659 : Blo 1008601 1703659 := bstep (se 1 (by rfl) ⟨1277744, by rfl⟩ : syracuseStep 1703659 = 2555489) B2555489
theorem B5472011 : Blo 1008601 5472011 := bstep (se 1 (by rfl) ⟨4104008, by rfl⟩ : syracuseStep 5472011 = 8208017) B8208017
theorem B1277851 : Blo 1008601 1277851 := bstep (se 1 (by rfl) ⟨958388, by rfl⟩ : syracuseStep 1277851 = 1916777) B1916777
theorem B5112719 : Blo 1008601 5112719 := bstep (se 1 (by rfl) ⟨3834539, by rfl⟩ : syracuseStep 5112719 = 7669079) B7669079
theorem B1704955 : Blo 1008601 1704955 := bstep (se 1 (by rfl) ⟨1278716, by rfl⟩ : syracuseStep 1704955 = 2557433) B2557433
theorem B3409019 : Blo 1008601 3409019 := bstep (se 1 (by rfl) ⟨2556764, by rfl⟩ : syracuseStep 3409019 = 5113529) B5113529
theorem B2557291 : Blo 1008601 2557291 := bstep (se 1 (by rfl) ⟨1917968, by rfl⟩ : syracuseStep 2557291 = 3835937) B3835937
theorem B3409289 : Blo 1008601 3409289 := bstep (se 2 (by rfl) ⟨1278483, by rfl⟩ : syracuseStep 3409289 = 2556967) B2556967
theorem B1705387 : Blo 1008601 1705387 := bstep (se 1 (by rfl) ⟨1279040, by rfl⟩ : syracuseStep 1705387 = 2558081) B2558081
theorem B1705583 : Blo 1008601 1705583 := bstep (se 1 (by rfl) ⟨1279187, by rfl⟩ : syracuseStep 1705583 = 2558375) B2558375
theorem B2426489 : Blo 1008601 2426489 := bstep (se 2 (by rfl) ⟨909933, by rfl⟩ : syracuseStep 2426489 = 1819867) B1819867
theorem B1705691 : Blo 1008601 1705691 := bstep (se 1 (by rfl) ⟨1279268, by rfl⟩ : syracuseStep 1705691 = 2558537) B2558537
theorem B1279739 : Blo 1008601 1279739 := bstep (se 1 (by rfl) ⟨959804, by rfl⟩ : syracuseStep 1279739 = 1919609) B1919609
theorem B2557727 : Blo 1008601 2557727 := bstep (se 1 (by rfl) ⟨1918295, by rfl⟩ : syracuseStep 2557727 = 3836591) B3836591
theorem B7669565 : Blo 1008601 7669565 := bstep (se 3 (by rfl) ⟨1438043, by rfl⟩ : syracuseStep 7669565 = 2876087) B2876087
theorem B1705927 : Blo 1008601 1705927 := bstep (se 1 (by rfl) ⟨1279445, by rfl⟩ : syracuseStep 1705927 = 2558891) B2558891
theorem B3410045 : Blo 1008601 3410045 := bstep (se 3 (by rfl) ⟨639383, by rfl⟩ : syracuseStep 3410045 = 1278767) B1278767
theorem B3639647 : Blo 1008601 3639647 := bstep (se 1 (by rfl) ⟨2729735, by rfl⟩ : syracuseStep 3639647 = 5459471) B5459471
theorem B3410315 : Blo 1008601 3410315 := bstep (se 1 (by rfl) ⟨2557736, by rfl⟩ : syracuseStep 3410315 = 5115473) B5115473
theorem B4852169 : Blo 1008601 4852169 := bstep (se 2 (by rfl) ⟨1819563, by rfl⟩ : syracuseStep 4852169 = 3639127) B3639127
theorem B3836423 : Blo 1008601 3836423 := bstep (se 1 (by rfl) ⟨2877317, by rfl⟩ : syracuseStep 3836423 = 5754635) B5754635
theorem B1280539 : Blo 1008601 1280539 := bstep (se 1 (by rfl) ⟨960404, by rfl⟩ : syracuseStep 1280539 = 1920809) B1920809
theorem B1706683 : Blo 1008601 1706683 := bstep (se 1 (by rfl) ⟨1280012, by rfl⟩ : syracuseStep 1706683 = 2560025) B2560025
theorem B70060949 : Blo 1008601 70060949 := bstep (se 6 (by rfl) ⟨1642053, by rfl⟩ : syracuseStep 70060949 = 3284107) B3284107
theorem B1706987 : Blo 1008601 1706987 := bstep (se 1 (by rfl) ⟨1280240, by rfl⟩ : syracuseStep 1706987 = 2560481) B2560481
theorem B2559023 : Blo 1008601 2559023 := bstep (se 1 (by rfl) ⟨1919267, by rfl⟩ : syracuseStep 2559023 = 3838535) B3838535
theorem B8752357 : Blo 1008601 8752357 := bstep (se 4 (by rfl) ⟨820533, by rfl⟩ : syracuseStep 8752357 = 1641067) B1641067
theorem B1281359 : Blo 1008601 1281359 := bstep (se 1 (by rfl) ⟨961019, by rfl⟩ : syracuseStep 1281359 = 1922039) B1922039
theorem B1281511 : Blo 1008601 1281511 := bstep (se 1 (by rfl) ⟨961133, by rfl⟩ : syracuseStep 1281511 = 1922267) B1922267
theorem B7474889 : Blo 1008601 7474889 := bstep (se 2 (by rfl) ⟨2803083, by rfl⟩ : syracuseStep 7474889 = 5606167) B5606167
theorem B7278457 : Blo 1008601 7278457 := bstep (se 2 (by rfl) ⟨2729421, by rfl⟩ : syracuseStep 7278457 = 5458843) B5458843
theorem B2559883 : Blo 1008601 2559883 := bstep (se 1 (by rfl) ⟨1919912, by rfl⟩ : syracuseStep 2559883 = 3839825) B3839825
theorem B3411935 : Blo 1008601 3411935 := bstep (se 1 (by rfl) ⟨2558951, by rfl⟩ : syracuseStep 3411935 = 5117903) B5117903
theorem B3412097 : Blo 1008601 3412097 := bstep (se 2 (by rfl) ⟨1279536, by rfl⟩ : syracuseStep 3412097 = 2559073) B2559073
theorem B7671995 : Blo 1008601 7671995 := bstep (se 1 (by rfl) ⟨5753996, by rfl⟩ : syracuseStep 7671995 = 11507993) B11507993
theorem B2560187 : Blo 1008601 2560187 := bstep (se 1 (by rfl) ⟨1920140, by rfl⟩ : syracuseStep 2560187 = 3840281) B3840281
theorem B3412583 : Blo 1008601 3412583 := bstep (se 1 (by rfl) ⟨2559437, by rfl⟩ : syracuseStep 3412583 = 5118875) B5118875
theorem B2560673 : Blo 1008601 2560673 := bstep (se 2 (by rfl) ⟨960252, by rfl⟩ : syracuseStep 2560673 = 1920505) B1920505
theorem B149590799 : Blo 1008601 149590799 := bstep (se 1 (by rfl) ⟨112193099, by rfl⟩ : syracuseStep 149590799 = 224386199) B224386199
theorem B3412907 : Blo 1008601 3412907 := bstep (se 1 (by rfl) ⟨2559680, by rfl⟩ : syracuseStep 3412907 = 5119361) B5119361
theorem B3413339 : Blo 1008601 3413339 := bstep (se 1 (by rfl) ⟨2560004, by rfl⟩ : syracuseStep 3413339 = 5120009) B5120009
theorem B3413447 : Blo 1008601 3413447 := bstep (se 1 (by rfl) ⟨2560085, by rfl⟩ : syracuseStep 3413447 = 5120171) B5120171
theorem B1513031 : Blo 1008601 1513031 := bstep (se 1 (by rfl) ⟨1134773, by rfl⟩ : syracuseStep 1513031 = 2269547) B2269547
theorem B1513127 : Blo 1008601 1513127 := bstep (se 1 (by rfl) ⟨1134845, by rfl⟩ : syracuseStep 1513127 = 2269691) B2269691
theorem B4101803 : Blo 1008601 4101803 := bstep (se 1 (by rfl) ⟨3076352, by rfl⟩ : syracuseStep 4101803 = 6152705) B6152705
theorem B1513211 : Blo 1008601 1513211 := bstep (se 1 (by rfl) ⟨1134908, by rfl⟩ : syracuseStep 1513211 = 2269817) B2269817
theorem B3413771 : Blo 1008601 3413771 := bstep (se 1 (by rfl) ⟨2560328, by rfl⟩ : syracuseStep 3413771 = 5120657) B5120657
theorem B1513247 : Blo 1008601 1513247 := bstep (se 1 (by rfl) ⟨1134935, by rfl⟩ : syracuseStep 1513247 = 2269871) B2269871
theorem B3643193 : Blo 1008601 3643193 := bstep (se 2 (by rfl) ⟨1366197, by rfl⟩ : syracuseStep 3643193 = 2732395) B2732395
theorem B1513295 : Blo 1008601 1513295 := bstep (se 1 (by rfl) ⟨1134971, by rfl⟩ : syracuseStep 1513295 = 2269943) B2269943
theorem B1513415 : Blo 1008601 1513415 := bstep (se 1 (by rfl) ⟨1135061, by rfl⟩ : syracuseStep 1513415 = 2270123) B2270123
theorem B3414041 : Blo 1008601 3414041 := bstep (se 2 (by rfl) ⟨1280265, by rfl⟩ : syracuseStep 3414041 = 2560531) B2560531
theorem B22124609 : Blo 1008601 22124609 := bstep (se 2 (by rfl) ⟨8296728, by rfl⟩ : syracuseStep 22124609 = 16593457) B16593457
theorem B20781137 : Blo 1008601 20781137 := bstep (se 2 (by rfl) ⟨7792926, by rfl⟩ : syracuseStep 20781137 = 15585853) B15585853
theorem B2562131 : Blo 1008601 2562131 := bstep (se 1 (by rfl) ⟨1921598, by rfl⟩ : syracuseStep 2562131 = 3843197) B3843197
theorem B2431073 : Blo 1008601 2431073 := bstep (se 2 (by rfl) ⟨911652, by rfl⟩ : syracuseStep 2431073 = 1823305) B1823305
theorem B4856051 : Blo 1008601 4856051 := bstep (se 1 (by rfl) ⟨3642038, by rfl⟩ : syracuseStep 4856051 = 7284077) B7284077
theorem B1513769 : Blo 1008601 1513769 := bstep (se 2 (by rfl) ⟨567663, by rfl⟩ : syracuseStep 1513769 = 1135327) B1135327
theorem B1513775 : Blo 1008601 1513775 := bstep (se 1 (by rfl) ⟨1135331, by rfl⟩ : syracuseStep 1513775 = 2270663) B2270663
theorem B7281019 : Blo 1008601 7281019 := bstep (se 1 (by rfl) ⟨5460764, by rfl⟩ : syracuseStep 7281019 = 10921529) B10921529
theorem B1514015 : Blo 1008601 1514015 := bstep (se 1 (by rfl) ⟨1135511, by rfl⟩ : syracuseStep 1514015 = 2271023) B2271023
theorem B2562617 : Blo 1008601 2562617 := bstep (se 2 (by rfl) ⟨960981, by rfl⟩ : syracuseStep 2562617 = 1921963) B1921963
theorem B35035895 : Blo 1008601 35035895 := bstep (se 1 (by rfl) ⟨26276921, by rfl⟩ : syracuseStep 35035895 = 52553843) B52553843
theorem B4266857 : Blo 1008601 4266857 := bstep (se 2 (by rfl) ⟨1600071, by rfl⟩ : syracuseStep 4266857 = 3200143) B3200143
theorem B1514399 : Blo 1008601 1514399 := bstep (se 1 (by rfl) ⟨1135799, by rfl⟩ : syracuseStep 1514399 = 2271599) B2271599
theorem B1514447 : Blo 1008601 1514447 := bstep (se 1 (by rfl) ⟨1135835, by rfl⟩ : syracuseStep 1514447 = 2271671) B2271671
theorem B1514537 : Blo 1008601 1514537 := bstep (se 2 (by rfl) ⟨567951, by rfl⟩ : syracuseStep 1514537 = 1135903) B1135903
theorem B1514543 : Blo 1008601 1514543 := bstep (se 1 (by rfl) ⟨1135907, by rfl⟩ : syracuseStep 1514543 = 2271815) B2271815
theorem B1514567 : Blo 1008601 1514567 := bstep (se 1 (by rfl) ⟨1135925, by rfl⟩ : syracuseStep 1514567 = 2271851) B2271851
theorem B1514831 : Blo 1008601 1514831 := bstep (se 1 (by rfl) ⟨1136123, by rfl⟩ : syracuseStep 1514831 = 2272247) B2272247
theorem B3415391 : Blo 1008601 3415391 := bstep (se 1 (by rfl) ⟨2561543, by rfl⟩ : syracuseStep 3415391 = 5123087) B5123087
theorem B1514921 : Blo 1008601 1514921 := bstep (se 2 (by rfl) ⟨568095, by rfl⟩ : syracuseStep 1514921 = 1136191) B1136191
theorem B1515071 : Blo 1008601 1515071 := bstep (se 1 (by rfl) ⟨1136303, by rfl⟩ : syracuseStep 1515071 = 2272607) B2272607
theorem B32841395 : Blo 1008601 32841395 := bstep (se 1 (by rfl) ⟨24631046, by rfl⟩ : syracuseStep 32841395 = 49262093) B49262093
theorem B1515335 : Blo 1008601 1515335 := bstep (se 1 (by rfl) ⟨1136501, by rfl⟩ : syracuseStep 1515335 = 2273003) B2273003
theorem B3415931 : Blo 1008601 3415931 := bstep (se 1 (by rfl) ⟨2561948, by rfl⟩ : syracuseStep 3415931 = 5123897) B5123897
theorem B1515419 : Blo 1008601 1515419 := bstep (se 1 (by rfl) ⟨1136564, by rfl⟩ : syracuseStep 1515419 = 2273129) B2273129
theorem B2269403 : Blo 1008601 2269403 := bstep (se 1 (by rfl) ⟨1702052, by rfl⟩ : syracuseStep 2269403 = 3404105) B3404105
theorem B3416417 : Blo 1008601 3416417 := bstep (se 2 (by rfl) ⟨1281156, by rfl⟩ : syracuseStep 3416417 = 2562313) B2562313
theorem B3842423 : Blo 1008601 3842423 := bstep (se 1 (by rfl) ⟨2881817, by rfl⟩ : syracuseStep 3842423 = 5763635) B5763635
theorem B1515983 : Blo 1008601 1515983 := bstep (se 1 (by rfl) ⟨1136987, by rfl⟩ : syracuseStep 1515983 = 2273975) B2273975
theorem B2269673 : Blo 1008601 2269673 := bstep (se 2 (by rfl) ⟨851127, by rfl⟩ : syracuseStep 2269673 = 1702255) B1702255
theorem B1516025 : Blo 1008601 1516025 := bstep (se 2 (by rfl) ⟨568509, by rfl⟩ : syracuseStep 1516025 = 1137019) B1137019
theorem B1516127 : Blo 1008601 1516127 := bstep (se 1 (by rfl) ⟨1137095, by rfl⟩ : syracuseStep 1516127 = 2274191) B2274191
theorem B2269961 : Blo 1008601 2269961 := bstep (se 2 (by rfl) ⟨851235, by rfl⟩ : syracuseStep 2269961 = 1702471) B1702471
theorem B3646451 : Blo 1008601 3646451 := bstep (se 1 (by rfl) ⟨2734838, by rfl⟩ : syracuseStep 3646451 = 5469677) B5469677
theorem B1516607 : Blo 1008601 1516607 := bstep (se 1 (by rfl) ⟨1137455, by rfl⟩ : syracuseStep 1516607 = 2274911) B2274911
theorem B1516649 : Blo 1008601 1516649 := bstep (se 2 (by rfl) ⟨568743, by rfl⟩ : syracuseStep 1516649 = 1137487) B1137487
theorem B1516751 : Blo 1008601 1516751 := bstep (se 1 (by rfl) ⟨1137563, by rfl⟩ : syracuseStep 1516751 = 2275127) B2275127
theorem B3843395 : Blo 1008601 3843395 := bstep (se 1 (by rfl) ⟨2882546, by rfl⟩ : syracuseStep 3843395 = 5765093) B5765093
theorem B2270537 : Blo 1008601 2270537 := bstep (se 2 (by rfl) ⟨851451, by rfl⟩ : syracuseStep 2270537 = 1702903) B1702903
theorem B1516955 : Blo 1008601 1516955 := bstep (se 1 (by rfl) ⟨1137716, by rfl⟩ : syracuseStep 1516955 = 2275433) B2275433
theorem B4859473 : Blo 1008601 4859473 := bstep (se 2 (by rfl) ⟨1822302, by rfl⟩ : syracuseStep 4859473 = 3644605) B3644605
theorem B1517177 : Blo 1008601 1517177 := bstep (se 2 (by rfl) ⟨568941, by rfl⟩ : syracuseStep 1517177 = 1137883) B1137883
theorem B1517279 : Blo 1008601 1517279 := bstep (se 1 (by rfl) ⟨1137959, by rfl⟩ : syracuseStep 1517279 = 2275919) B2275919
theorem B1517375 : Blo 1008601 1517375 := bstep (se 1 (by rfl) ⟨1138031, by rfl⟩ : syracuseStep 1517375 = 2276063) B2276063
theorem B1517543 : Blo 1008601 1517543 := bstep (se 1 (by rfl) ⟨1138157, by rfl⟩ : syracuseStep 1517543 = 2276315) B2276315
theorem B1517561 : Blo 1008601 1517561 := bstep (se 2 (by rfl) ⟨569085, by rfl⟩ : syracuseStep 1517561 = 1138171) B1138171
theorem B11839517 : Blo 1008601 11839517 := bstep (se 3 (by rfl) ⟨2219909, by rfl⟩ : syracuseStep 11839517 = 4439819) B4439819
theorem B1517663 : Blo 1008601 1517663 := bstep (se 1 (by rfl) ⟨1138247, by rfl⟩ : syracuseStep 1517663 = 2276495) B2276495
theorem B1517723 : Blo 1008601 1517723 := bstep (se 1 (by rfl) ⟨1138292, by rfl⟩ : syracuseStep 1517723 = 2276585) B2276585
theorem B1517759 : Blo 1008601 1517759 := bstep (se 1 (by rfl) ⟨1138319, by rfl⟩ : syracuseStep 1517759 = 2276639) B2276639
theorem B1517801 : Blo 1008601 1517801 := bstep (se 2 (by rfl) ⟨569175, by rfl⟩ : syracuseStep 1517801 = 1138351) B1138351
theorem B2271527 : Blo 1008601 2271527 := bstep (se 1 (by rfl) ⟨1703645, by rfl⟩ : syracuseStep 2271527 = 3407291) B3407291
theorem B2730287 : Blo 1008601 2730287 := bstep (se 1 (by rfl) ⟨2047715, by rfl⟩ : syracuseStep 2730287 = 4095431) B4095431
theorem B2271545 : Blo 1008601 2271545 := bstep (se 2 (by rfl) ⟨851829, by rfl⟩ : syracuseStep 2271545 = 1703659) B1703659
theorem B3648007 : Blo 1008601 3648007 := bstep (se 1 (by rfl) ⟨2736005, by rfl⟩ : syracuseStep 3648007 = 5472011) B5472011
theorem B1518107 : Blo 1008601 1518107 := bstep (se 1 (by rfl) ⟨1138580, by rfl⟩ : syracuseStep 1518107 = 2277161) B2277161
theorem B1518185 : Blo 1008601 1518185 := bstep (se 2 (by rfl) ⟨569319, by rfl⟩ : syracuseStep 1518185 = 1138639) B1138639
theorem B5122763 : Blo 1008601 5122763 := bstep (se 1 (by rfl) ⟨3842072, by rfl⟩ : syracuseStep 5122763 = 7684145) B7684145
theorem B1092655 : Blo 1008601 1092655 := bstep (se 1 (by rfl) ⟨819491, by rfl⟩ : syracuseStep 1092655 = 1638983) B1638983
theorem B1518713 : Blo 1008601 1518713 := bstep (se 2 (by rfl) ⟨569517, by rfl⟩ : syracuseStep 1518713 = 1139035) B1139035
theorem B1518815 : Blo 1008601 1518815 := bstep (se 1 (by rfl) ⟨1139111, by rfl⟩ : syracuseStep 1518815 = 2278223) B2278223
theorem B1518857 : Blo 1008601 1518857 := bstep (se 2 (by rfl) ⟨569571, by rfl⟩ : syracuseStep 1518857 = 1139143) B1139143
theorem B1617403 : Blo 1008601 1617403 := bstep (se 1 (by rfl) ⟨1213052, by rfl⟩ : syracuseStep 1617403 = 2426105) B2426105
theorem B2272841 : Blo 1008601 2272841 := bstep (se 2 (by rfl) ⟨852315, by rfl⟩ : syracuseStep 2272841 = 1704631) B1704631
theorem B2731897 : Blo 1008601 2731897 := bstep (se 2 (by rfl) ⟨1024461, by rfl⟩ : syracuseStep 2731897 = 2048923) B2048923
theorem B5746571 : Blo 1008601 5746571 := bstep (se 1 (by rfl) ⟨4309928, by rfl⟩ : syracuseStep 5746571 = 8619857) B8619857
theorem B2732221 : Blo 1008601 2732221 := bstep (se 3 (by rfl) ⟨512291, by rfl⟩ : syracuseStep 2732221 = 1024583) B1024583
theorem B7286993 : Blo 1008601 7286993 := bstep (se 2 (by rfl) ⟨2732622, by rfl⟩ : syracuseStep 7286993 = 5465245) B5465245
theorem B46609037 : Blo 1008601 46609037 := bstep (se 3 (by rfl) ⟨8739194, by rfl⟩ : syracuseStep 46609037 = 17478389) B17478389
theorem B5747345 : Blo 1008601 5747345 := bstep (se 2 (by rfl) ⟨2155254, by rfl⟩ : syracuseStep 5747345 = 4310509) B4310509
theorem B1618697 : Blo 1008601 1618697 := bstep (se 2 (by rfl) ⟨607011, by rfl⟩ : syracuseStep 1618697 = 1214023) B1214023
theorem B2274299 : Blo 1008601 2274299 := bstep (se 1 (by rfl) ⟨1705724, by rfl⟩ : syracuseStep 2274299 = 3411449) B3411449
theorem B2733065 : Blo 1008601 2733065 := bstep (se 2 (by rfl) ⟨1024899, by rfl⟩ : syracuseStep 2733065 = 2049799) B2049799
theorem B5125193 : Blo 1008601 5125193 := bstep (se 2 (by rfl) ⟨1921947, by rfl⟩ : syracuseStep 5125193 = 3843895) B3843895
theorem B1848425 : Blo 1008601 1848425 := bstep (se 2 (by rfl) ⟨693159, by rfl⟩ : syracuseStep 1848425 = 1386319) B1386319
theorem B2274479 : Blo 1008601 2274479 := bstep (se 1 (by rfl) ⟨1705859, by rfl⟩ : syracuseStep 2274479 = 3411719) B3411719
theorem B14562503 : Blo 1008601 14562503 := bstep (se 1 (by rfl) ⟨10921877, by rfl⟩ : syracuseStep 14562503 = 21843755) B21843755
theorem B2274515 : Blo 1008601 2274515 := bstep (se 1 (by rfl) ⟨1705886, by rfl⟩ : syracuseStep 2274515 = 3411773) B3411773
theorem B5748029 : Blo 1008601 5748029 := bstep (se 3 (by rfl) ⟨1077755, by rfl⟩ : syracuseStep 5748029 = 2155511) B2155511
theorem B23311721 : Blo 1008601 23311721 := bstep (se 2 (by rfl) ⟨8741895, by rfl⟩ : syracuseStep 23311721 = 17483791) B17483791
theorem B2274785 : Blo 1008601 2274785 := bstep (se 2 (by rfl) ⟨853044, by rfl⟩ : syracuseStep 2274785 = 1706089) B1706089
theorem B5125841 : Blo 1008601 5125841 := bstep (se 2 (by rfl) ⟨1922190, by rfl⟩ : syracuseStep 5125841 = 3844381) B3844381
theorem B2733887 : Blo 1008601 2733887 := bstep (se 1 (by rfl) ⟨2050415, by rfl⟩ : syracuseStep 2733887 = 4100831) B4100831
theorem B6469865 : Blo 1008601 6469865 := bstep (se 2 (by rfl) ⟨2426199, by rfl⟩ : syracuseStep 6469865 = 4852399) B4852399
theorem B10926373 : Blo 1008601 10926373 := bstep (se 4 (by rfl) ⟨1024347, by rfl⟩ : syracuseStep 10926373 = 2048695) B2048695
theorem B7879027 : Blo 1008601 7879027 := bstep (se 1 (by rfl) ⟨5909270, by rfl⟩ : syracuseStep 7879027 = 11818541) B11818541
theorem B2276423 : Blo 1008601 2276423 := bstep (se 1 (by rfl) ⟨1707317, by rfl⟩ : syracuseStep 2276423 = 3414635) B3414635
theorem B2276819 : Blo 1008601 2276819 := bstep (se 1 (by rfl) ⟨1707614, by rfl⟩ : syracuseStep 2276819 = 3415229) B3415229
theorem B1621567 : Blo 1008601 1621567 := bstep (se 1 (by rfl) ⟨1216175, by rfl⟩ : syracuseStep 1621567 = 2432351) B2432351
theorem B7290593 : Blo 1008601 7290593 := bstep (se 2 (by rfl) ⟨2733972, by rfl⟩ : syracuseStep 7290593 = 5467945) B5467945
theorem B2277089 : Blo 1008601 2277089 := bstep (se 2 (by rfl) ⟨853908, by rfl⟩ : syracuseStep 2277089 = 1707817) B1707817
theorem B2048825 : Blo 1008601 2048825 := bstep (se 2 (by rfl) ⟨768309, by rfl⟩ : syracuseStep 2048825 = 1536619) B1536619
theorem B5751719 : Blo 1008601 5751719 := bstep (se 1 (by rfl) ⟨4313789, by rfl⟩ : syracuseStep 5751719 = 8627579) B8627579
theorem B13124753 : Blo 1008601 13124753 := bstep (se 2 (by rfl) ⟨4921782, by rfl⟩ : syracuseStep 13124753 = 9843565) B9843565
theorem B1918379 : Blo 1008601 1918379 := bstep (se 1 (by rfl) ⟨1438784, by rfl⟩ : syracuseStep 1918379 = 2877569) B2877569
theorem B6309335 : Blo 1008601 6309335 := bstep (se 1 (by rfl) ⟨4732001, by rfl⟩ : syracuseStep 6309335 = 9464003) B9464003
theorem B24627077 : Blo 1008601 24627077 := bstep (se 4 (by rfl) ⟨2308788, by rfl⟩ : syracuseStep 24627077 = 4617577) B4617577
theorem B4606247 : Blo 1008601 4606247 := bstep (se 1 (by rfl) ⟨3454685, by rfl⟩ : syracuseStep 4606247 = 6909371) B6909371
theorem B14993873 : Blo 1008601 14993873 := bstep (se 2 (by rfl) ⟨5622702, by rfl⟩ : syracuseStep 14993873 = 11245405) B11245405
theorem B5754179 : Blo 1008601 5754179 := bstep (se 1 (by rfl) ⟨4315634, by rfl⟩ : syracuseStep 5754179 = 8631269) B8631269
theorem B7687547 : Blo 1008601 7687547 := bstep (se 1 (by rfl) ⟨5765660, by rfl⟩ : syracuseStep 7687547 = 11531321) B11531321
theorem B5754361 : Blo 1008601 5754361 := bstep (se 2 (by rfl) ⟨2157885, by rfl⟩ : syracuseStep 5754361 = 4315771) B4315771
theorem B11652781 : Blo 1008601 11652781 := bstep (se 3 (by rfl) ⟨2184896, by rfl⟩ : syracuseStep 11652781 = 4369793) B4369793
theorem B23318189 : Blo 1008601 23318189 := bstep (se 3 (by rfl) ⟨4372160, by rfl⟩ : syracuseStep 23318189 = 8744321) B8744321
theorem B27709289 : Blo 1008601 27709289 := bstep (se 2 (by rfl) ⟨10390983, by rfl⟩ : syracuseStep 27709289 = 20781967) B20781967
theorem B12472211 : Blo 1008601 12472211 := bstep (se 1 (by rfl) ⟨9354158, by rfl⟩ : syracuseStep 12472211 = 18708317) B18708317
theorem B1920991 : Blo 1008601 1920991 := bstep (se 1 (by rfl) ⟨1440743, by rfl⟩ : syracuseStep 1920991 = 2881487) B2881487
theorem B1134823 : Blo 1008601 1134823 := bstep (se 1 (by rfl) ⟨851117, by rfl⟩ : syracuseStep 1134823 = 1702235) B1702235
theorem B1200511 : Blo 1008601 1200511 := bstep (se 1 (by rfl) ⟨900383, by rfl⟩ : syracuseStep 1200511 = 1800767) B1800767
theorem B6148811 : Blo 1008601 6148811 := bstep (se 1 (by rfl) ⟨4611608, by rfl⟩ : syracuseStep 6148811 = 9223217) B9223217
theorem B1135471 : Blo 1008601 1135471 := bstep (se 1 (by rfl) ⟨851603, by rfl⟩ : syracuseStep 1135471 = 1703207) B1703207
theorem B4314167 : Blo 1008601 4314167 := bstep (se 1 (by rfl) ⟨3235625, by rfl⟩ : syracuseStep 4314167 = 6471251) B6471251
theorem B3232831 : Blo 1008601 3232831 := bstep (se 1 (by rfl) ⟨2424623, by rfl⟩ : syracuseStep 3232831 = 4849247) B4849247
theorem B12309893 : Blo 1008601 12309893 := bstep (se 4 (by rfl) ⟨1154052, by rfl⟩ : syracuseStep 12309893 = 2308105) B2308105
theorem B1725851 : Blo 1008601 1725851 := bstep (se 1 (by rfl) ⟨1294388, by rfl⟩ : syracuseStep 1725851 = 2588777) B2588777
theorem B5461613 : Blo 1008601 5461613 := bstep (se 3 (by rfl) ⟨1024052, by rfl⟩ : syracuseStep 5461613 = 2048105) B2048105
theorem B1136623 : Blo 1008601 1136623 := bstep (se 1 (by rfl) ⟨852467, by rfl⟩ : syracuseStep 1136623 = 1704935) B1704935
theorem B13817861 : Blo 1008601 13817861 := bstep (se 4 (by rfl) ⟨1295424, by rfl⟩ : syracuseStep 13817861 = 2590849) B2590849
theorem B7788739 : Blo 1008601 7788739 := bstep (se 1 (by rfl) ⟨5841554, by rfl⟩ : syracuseStep 7788739 = 11683109) B11683109
theorem B29088557 : Blo 1008601 29088557 := bstep (se 3 (by rfl) ⟨5454104, by rfl⟩ : syracuseStep 29088557 = 10908209) B10908209
theorem B1727671 : Blo 1008601 1727671 := bstep (se 1 (by rfl) ⟨1295753, by rfl⟩ : syracuseStep 1727671 = 2591507) B2591507
theorem B38854241 : Blo 1008601 38854241 := bstep (se 2 (by rfl) ⟨14570340, by rfl⟩ : syracuseStep 38854241 = 29140681) B29140681
theorem B2154127 : Blo 1008601 2154127 := bstep (se 1 (by rfl) ⟨1615595, by rfl⟩ : syracuseStep 2154127 = 3231191) B3231191
theorem B7298839 : Blo 1008601 7298839 := bstep (se 1 (by rfl) ⟨5474129, by rfl⟩ : syracuseStep 7298839 = 10948259) B10948259
theorem B1728479 : Blo 1008601 1728479 := bstep (se 1 (by rfl) ⟨1296359, by rfl⟩ : syracuseStep 1728479 = 2592719) B2592719
theorem B19652827 : Blo 1008601 19652827 := bstep (se 1 (by rfl) ⟨14739620, by rfl⟩ : syracuseStep 19652827 = 29479241) B29479241
theorem B1139071 : Blo 1008601 1139071 := bstep (se 1 (by rfl) ⟨854303, by rfl⟩ : syracuseStep 1139071 = 1708607) B1708607
theorem B1008635 : Blo 1008601 1008635 := bstep (se 1 (by rfl) ⟨756476, by rfl⟩ : syracuseStep 1008635 = 1512953) B1512953
theorem B1008703 : Blo 1008601 1008703 := bstep (se 1 (by rfl) ⟨756527, by rfl⟩ : syracuseStep 1008703 = 1513055) B1513055
theorem B1008847 : Blo 1008601 1008847 := bstep (se 1 (by rfl) ⟨756635, by rfl⟩ : syracuseStep 1008847 = 1513271) B1513271
theorem B1009051 : Blo 1008601 1009051 := bstep (se 1 (by rfl) ⟨756788, by rfl⟩ : syracuseStep 1009051 = 1513577) B1513577
theorem B1009263 : Blo 1008601 1009263 := bstep (se 1 (by rfl) ⟨756947, by rfl⟩ : syracuseStep 1009263 = 1513895) B1513895
theorem B1009319 : Blo 1008601 1009319 := bstep (se 1 (by rfl) ⟨756989, by rfl⟩ : syracuseStep 1009319 = 1513979) B1513979
theorem B1009403 : Blo 1008601 1009403 := bstep (se 1 (by rfl) ⟨757052, by rfl⟩ : syracuseStep 1009403 = 1514105) B1514105
theorem B1009439 : Blo 1008601 1009439 := bstep (se 1 (by rfl) ⟨757079, by rfl⟩ : syracuseStep 1009439 = 1514159) B1514159
theorem B1009471 : Blo 1008601 1009471 := bstep (se 1 (by rfl) ⟨757103, by rfl⟩ : syracuseStep 1009471 = 1514207) B1514207
theorem B1009647 : Blo 1008601 1009647 := bstep (se 1 (by rfl) ⟨757235, by rfl⟩ : syracuseStep 1009647 = 1514471) B1514471
theorem B1009819 : Blo 1008601 1009819 := bstep (se 1 (by rfl) ⟨757364, by rfl⟩ : syracuseStep 1009819 = 1514729) B1514729
theorem B1009855 : Blo 1008601 1009855 := bstep (se 1 (by rfl) ⟨757391, by rfl⟩ : syracuseStep 1009855 = 1514783) B1514783
theorem B1534187 : Blo 1008601 1534187 := bstep (se 1 (by rfl) ⟨1150640, by rfl⟩ : syracuseStep 1534187 = 2301281) B2301281
theorem B1009967 : Blo 1008601 1009967 := bstep (se 1 (by rfl) ⟨757475, by rfl⟩ : syracuseStep 1009967 = 1514951) B1514951
theorem B1010203 : Blo 1008601 1010203 := bstep (se 1 (by rfl) ⟨757652, by rfl⟩ : syracuseStep 1010203 = 1515305) B1515305
theorem B1010207 : Blo 1008601 1010207 := bstep (se 1 (by rfl) ⟨757655, by rfl⟩ : syracuseStep 1010207 = 1515311) B1515311
theorem B4319993 : Blo 1008601 4319993 := bstep (se 2 (by rfl) ⟨1619997, by rfl⟩ : syracuseStep 4319993 = 3239995) B3239995
theorem B1010523 : Blo 1008601 1010523 := bstep (se 1 (by rfl) ⟨757892, by rfl⟩ : syracuseStep 1010523 = 1515785) B1515785
theorem B1010591 : Blo 1008601 1010591 := bstep (se 1 (by rfl) ⟨757943, by rfl⟩ : syracuseStep 1010591 = 1515887) B1515887
theorem B9694187 : Blo 1008601 9694187 := bstep (se 1 (by rfl) ⟨7270640, by rfl⟩ : syracuseStep 9694187 = 14541281) B14541281
theorem B1010735 : Blo 1008601 1010735 := bstep (se 1 (by rfl) ⟨758051, by rfl⟩ : syracuseStep 1010735 = 1516103) B1516103
theorem B1010759 : Blo 1008601 1010759 := bstep (se 1 (by rfl) ⟨758069, by rfl⟩ : syracuseStep 1010759 = 1516139) B1516139
theorem B1010911 : Blo 1008601 1010911 := bstep (se 1 (by rfl) ⟨758183, by rfl⟩ : syracuseStep 1010911 = 1516367) B1516367
theorem B1011175 : Blo 1008601 1011175 := bstep (se 1 (by rfl) ⟨758381, by rfl⟩ : syracuseStep 1011175 = 1516763) B1516763
theorem B1011291 : Blo 1008601 1011291 := bstep (se 1 (by rfl) ⟨758468, by rfl⟩ : syracuseStep 1011291 = 1516937) B1516937
theorem B21884579 : Blo 1008601 21884579 := bstep (se 1 (by rfl) ⟨16413434, by rfl⟩ : syracuseStep 21884579 = 32826869) B32826869
theorem B1011527 : Blo 1008601 1011527 := bstep (se 1 (by rfl) ⟨758645, by rfl⟩ : syracuseStep 1011527 = 1517291) B1517291
theorem B6483887 : Blo 1008601 6483887 := bstep (se 1 (by rfl) ⟨4862915, by rfl⟩ : syracuseStep 6483887 = 9725831) B9725831
theorem B1011679 : Blo 1008601 1011679 := bstep (se 1 (by rfl) ⟨758759, by rfl⟩ : syracuseStep 1011679 = 1517519) B1517519
theorem B8646851 : Blo 1008601 8646851 := bstep (se 1 (by rfl) ⟨6485138, by rfl⟩ : syracuseStep 8646851 = 12970277) B12970277
theorem B1011943 : Blo 1008601 1011943 := bstep (se 1 (by rfl) ⟨758957, by rfl⟩ : syracuseStep 1011943 = 1517915) B1517915
theorem B2158903 : Blo 1008601 2158903 := bstep (se 1 (by rfl) ⟨1619177, by rfl⟩ : syracuseStep 2158903 = 3238355) B3238355
theorem B5763383 : Blo 1008601 5763383 := bstep (se 1 (by rfl) ⟨4322537, by rfl⟩ : syracuseStep 5763383 = 8645075) B8645075
theorem B26276183 : Blo 1008601 26276183 := bstep (se 1 (by rfl) ⟨19707137, by rfl⟩ : syracuseStep 26276183 = 39414275) B39414275
theorem B3404159 : Blo 1008601 3404159 := bstep (se 1 (by rfl) ⟨2553119, by rfl⟩ : syracuseStep 3404159 = 5106239) B5106239
theorem B1012095 : Blo 1008601 1012095 := bstep (se 1 (by rfl) ⟨759071, by rfl⟩ : syracuseStep 1012095 = 1518143) B1518143
theorem B1012175 : Blo 1008601 1012175 := bstep (se 1 (by rfl) ⟨759131, by rfl⟩ : syracuseStep 1012175 = 1518263) B1518263
theorem B5534201 : Blo 1008601 5534201 := bstep (se 2 (by rfl) ⟨2075325, by rfl⟩ : syracuseStep 5534201 = 4150651) B4150651
theorem B2191865 : Blo 1008601 2191865 := bstep (se 2 (by rfl) ⟨821949, by rfl⟩ : syracuseStep 2191865 = 1643899) B1643899
theorem B3830287 : Blo 1008601 3830287 := bstep (se 1 (by rfl) ⟨2872715, by rfl⟩ : syracuseStep 3830287 = 5745431) B5745431
theorem B25915949 : Blo 1008601 25915949 := bstep (se 3 (by rfl) ⟨4859240, by rfl⟩ : syracuseStep 25915949 = 9718481) B9718481
theorem B1012327 : Blo 1008601 1012327 := bstep (se 1 (by rfl) ⟨759245, by rfl⟩ : syracuseStep 1012327 = 1518491) B1518491
theorem B1012591 : Blo 1008601 1012591 := bstep (se 1 (by rfl) ⟨759443, by rfl⟩ : syracuseStep 1012591 = 1518887) B1518887
theorem B15561713 : Blo 1008601 15561713 := bstep (se 2 (by rfl) ⟨5835642, by rfl⟩ : syracuseStep 15561713 = 11671285) B11671285
theorem B2159723 : Blo 1008601 2159723 := bstep (se 1 (by rfl) ⟨1619792, by rfl⟩ : syracuseStep 2159723 = 3239585) B3239585
theorem B5469569 : Blo 1008601 5469569 := bstep (se 2 (by rfl) ⟨2051088, by rfl⟩ : syracuseStep 5469569 = 4102177) B4102177
theorem B65533319 : Blo 1008601 65533319 := bstep (se 1 (by rfl) ⟨49149989, by rfl⟩ : syracuseStep 65533319 = 98299979) B98299979
theorem B6485447 : Blo 1008601 6485447 := bstep (se 1 (by rfl) ⟨4864085, by rfl⟩ : syracuseStep 6485447 = 9728171) B9728171
theorem B49870343 : Blo 1008601 49870343 := bstep (se 1 (by rfl) ⟨37402757, by rfl⟩ : syracuseStep 49870343 = 74805515) B74805515
theorem B11662987 : Blo 1008601 11662987 := bstep (se 1 (by rfl) ⟨8747240, by rfl⟩ : syracuseStep 11662987 = 17494481) B17494481
theorem B2553515 : Blo 1008601 2553515 := bstep (se 1 (by rfl) ⟨1915136, by rfl⟩ : syracuseStep 2553515 = 3830273) B3830273
theorem B3405563 : Blo 1008601 3405563 := bstep (se 1 (by rfl) ⟨2554172, by rfl⟩ : syracuseStep 3405563 = 5108345) B5108345
theorem B19396367 : Blo 1008601 19396367 := bstep (se 1 (by rfl) ⟨14547275, by rfl⟩ : syracuseStep 19396367 = 29094551) B29094551
theorem B2881327 : Blo 1008601 2881327 := bstep (se 1 (by rfl) ⟨2160995, by rfl⟩ : syracuseStep 2881327 = 4321991) B4321991
theorem B5109641 : Blo 1008601 5109641 := bstep (se 2 (by rfl) ⟨1916115, by rfl⟩ : syracuseStep 5109641 = 3832231) B3832231
theorem B3405725 : Blo 1008601 3405725 := bstep (se 3 (by rfl) ⟨638573, by rfl⟩ : syracuseStep 3405725 = 1277147) B1277147
theorem B3078103 : Blo 1008601 3078103 := bstep (se 1 (by rfl) ⟨2308577, by rfl⟩ : syracuseStep 3078103 = 4617155) B4617155
theorem B2553839 : Blo 1008601 2553839 := bstep (se 1 (by rfl) ⟨1915379, by rfl⟩ : syracuseStep 2553839 = 3830759) B3830759
theorem B1702201 : Blo 1008601 1702201 := bstep (se 2 (by rfl) ⟨638325, by rfl⟩ : syracuseStep 1702201 = 1276651) B1276651
theorem B7666163 : Blo 1008601 7666163 := bstep (se 1 (by rfl) ⟨5749622, by rfl⟩ : syracuseStep 7666163 = 11499245) B11499245
theorem B1702505 : Blo 1008601 1702505 := bstep (se 2 (by rfl) ⟨638439, by rfl⟩ : syracuseStep 1702505 = 1276879) B1276879
theorem B65632963 : Blo 1008601 65632963 := bstep (se 1 (by rfl) ⟨49224722, by rfl⟩ : syracuseStep 65632963 = 98449445) B98449445
theorem B3406697 : Blo 1008601 3406697 := bstep (se 2 (by rfl) ⟨1277511, by rfl⟩ : syracuseStep 3406697 = 2555023) B2555023
theorem B3636127 : Blo 1008601 3636127 := bstep (se 1 (by rfl) ⟨2727095, by rfl⟩ : syracuseStep 3636127 = 5454191) B5454191
theorem B3406751 : Blo 1008601 3406751 := bstep (se 1 (by rfl) ⟨2555063, by rfl⟩ : syracuseStep 3406751 = 5110127) B5110127
theorem B2423777 : Blo 1008601 2423777 := bstep (se 2 (by rfl) ⟨908916, by rfl⟩ : syracuseStep 2423777 = 1817833) B1817833
theorem B1276975 : Blo 1008601 1276975 := bstep (se 1 (by rfl) ⟨957731, by rfl⟩ : syracuseStep 1276975 = 1915463) B1915463
theorem B6913309 : Blo 1008601 6913309 := bstep (se 3 (by rfl) ⟨1296245, by rfl⟩ : syracuseStep 6913309 = 2592491) B2592491
theorem B2882911 : Blo 1008601 2882911 := bstep (se 1 (by rfl) ⟨2162183, by rfl⟩ : syracuseStep 2882911 = 4324367) B4324367
theorem B1703335 : Blo 1008601 1703335 := bstep (se 1 (by rfl) ⟨1277501, by rfl⟩ : syracuseStep 1703335 = 2555003) B2555003
theorem B2555347 : Blo 1008601 2555347 := bstep (se 1 (by rfl) ⟨1916510, by rfl⟩ : syracuseStep 2555347 = 3833021) B3833021
theorem B3505619 : Blo 1008601 3505619 := bstep (se 1 (by rfl) ⟨2629214, by rfl⟩ : syracuseStep 3505619 = 5258429) B5258429
theorem B1703497 : Blo 1008601 1703497 := bstep (se 2 (by rfl) ⟨638811, by rfl⟩ : syracuseStep 1703497 = 1277623) B1277623
theorem B1703531 : Blo 1008601 1703531 := bstep (se 1 (by rfl) ⟨1277648, by rfl⟩ : syracuseStep 1703531 = 2555297) B2555297
theorem B4849399 : Blo 1008601 4849399 := bstep (se 1 (by rfl) ⟨3637049, by rfl⟩ : syracuseStep 4849399 = 7274099) B7274099
theorem B1703801 : Blo 1008601 1703801 := bstep (se 2 (by rfl) ⟨638925, by rfl⟩ : syracuseStep 1703801 = 1277851) B1277851
theorem B3408479 : Blo 1008601 3408479 := bstep (se 1 (by rfl) ⟨2556359, by rfl⟩ : syracuseStep 3408479 = 5112719) B5112719
theorem B3834479 : Blo 1008601 3834479 := bstep (se 1 (by rfl) ⟨2875859, by rfl⟩ : syracuseStep 3834479 = 5751719) B5751719
theorem B8749835 : Blo 1008601 8749835 := bstep (se 1 (by rfl) ⟨6562376, by rfl⟩ : syracuseStep 8749835 = 13124753) B13124753
theorem B1278919 : Blo 1008601 1278919 := bstep (se 1 (by rfl) ⟨959189, by rfl⟩ : syracuseStep 1278919 = 1918379) B1918379
theorem B1705151 : Blo 1008601 1705151 := bstep (se 1 (by rfl) ⟨1278863, by rfl⟩ : syracuseStep 1705151 = 2557727) B2557727
theorem B5113043 : Blo 1008601 5113043 := bstep (se 1 (by rfl) ⟨3834782, by rfl⟩ : syracuseStep 5113043 = 7669565) B7669565
theorem B16418051 : Blo 1008601 16418051 := bstep (se 1 (by rfl) ⟨12313538, by rfl⟩ : syracuseStep 16418051 = 24627077) B24627077
theorem B2426431 : Blo 1008601 2426431 := bstep (se 1 (by rfl) ⟨1819823, by rfl⟩ : syracuseStep 2426431 = 3639647) B3639647
theorem B9995915 : Blo 1008601 9995915 := bstep (se 1 (by rfl) ⟨7496936, by rfl⟩ : syracuseStep 9995915 = 14993873) B14993873
theorem B2557615 : Blo 1008601 2557615 := bstep (se 1 (by rfl) ⟨1918211, by rfl⟩ : syracuseStep 2557615 = 3836423) B3836423
theorem B3409721 : Blo 1008601 3409721 := bstep (se 2 (by rfl) ⟨1278645, by rfl⟩ : syracuseStep 3409721 = 2557291) B2557291
theorem B1706015 : Blo 1008601 1706015 := bstep (se 1 (by rfl) ⟨1279511, by rfl⟩ : syracuseStep 1706015 = 2559023) B2559023
theorem B3836119 : Blo 1008601 3836119 := bstep (se 1 (by rfl) ⟨2877089, by rfl⟩ : syracuseStep 3836119 = 5754179) B5754179
theorem B5114663 : Blo 1008601 5114663 := bstep (se 1 (by rfl) ⟨3835997, by rfl⟩ : syracuseStep 5114663 = 7671995) B7671995
theorem B1706791 : Blo 1008601 1706791 := bstep (se 1 (by rfl) ⟨1280093, by rfl⟩ : syracuseStep 1706791 = 2560187) B2560187
theorem B1707115 : Blo 1008601 1707115 := bstep (se 1 (by rfl) ⟨1280336, by rfl⟩ : syracuseStep 1707115 = 2560673) B2560673
theorem B1707385 : Blo 1008601 1707385 := bstep (se 2 (by rfl) ⟨640269, by rfl⟩ : syracuseStep 1707385 = 1280539) B1280539
theorem B1150567 : Blo 1008601 1150567 := bstep (se 1 (by rfl) ⟨862925, by rfl⟩ : syracuseStep 1150567 = 1725851) B1725851
theorem B3641075 : Blo 1008601 3641075 := bstep (se 1 (by rfl) ⟨2730806, by rfl⟩ : syracuseStep 3641075 = 5461613) B5461613
theorem B2428795 : Blo 1008601 2428795 := bstep (se 1 (by rfl) ⟨1821596, by rfl⟩ : syracuseStep 2428795 = 3643193) B3643193
theorem B9211907 : Blo 1008601 9211907 := bstep (se 1 (by rfl) ⟨6908930, by rfl⟩ : syracuseStep 9211907 = 13817861) B13817861
theorem B14749739 : Blo 1008601 14749739 := bstep (se 1 (by rfl) ⟨11062304, by rfl⟩ : syracuseStep 14749739 = 22124609) B22124609
theorem B1708087 : Blo 1008601 1708087 := bstep (se 1 (by rfl) ⟨1281065, by rfl⟩ : syracuseStep 1708087 = 2562131) B2562131
theorem B1708411 : Blo 1008601 1708411 := bstep (se 1 (by rfl) ⟨1281308, by rfl⟩ : syracuseStep 1708411 = 2562617) B2562617
theorem B1708681 : Blo 1008601 1708681 := bstep (se 2 (by rfl) ⟨640755, by rfl⟩ : syracuseStep 1708681 = 1281511) B1281511
theorem B3412637 : Blo 1008601 3412637 := bstep (se 3 (by rfl) ⟨639869, by rfl⟩ : syracuseStep 3412637 = 1279739) B1279739
theorem B7672481 : Blo 1008601 7672481 := bstep (se 2 (by rfl) ⟨2877180, by rfl⟩ : syracuseStep 7672481 = 5754361) B5754361
theorem B15537041 : Blo 1008601 15537041 := bstep (se 2 (by rfl) ⟨5826390, by rfl⟩ : syracuseStep 15537041 = 11652781) B11652781
theorem B21894263 : Blo 1008601 21894263 := bstep (se 1 (by rfl) ⟨16420697, by rfl⟩ : syracuseStep 21894263 = 32841395) B32841395
theorem B9704609 : Blo 1008601 9704609 := bstep (se 2 (by rfl) ⟨3639228, by rfl⟩ : syracuseStep 9704609 = 7278457) B7278457
theorem B3642529 : Blo 1008601 3642529 := bstep (se 2 (by rfl) ⟨1365948, by rfl⟩ : syracuseStep 3642529 = 2731897) B2731897
theorem B3413177 : Blo 1008601 3413177 := bstep (se 2 (by rfl) ⟨1279941, by rfl⟩ : syracuseStep 3413177 = 2559883) B2559883
theorem B2561321 : Blo 1008601 2561321 := bstep (se 2 (by rfl) ⟨960495, by rfl⟩ : syracuseStep 2561321 = 1920991) B1920991
theorem B1152319 : Blo 1008601 1152319 := bstep (se 1 (by rfl) ⟨864239, by rfl⟩ : syracuseStep 1152319 = 1728479) B1728479
theorem B1512935 : Blo 1008601 1512935 := bstep (se 1 (by rfl) ⟨1134701, by rfl⟩ : syracuseStep 1512935 = 2269403) B2269403
theorem B2561615 : Blo 1008601 2561615 := bstep (se 1 (by rfl) ⟨1921211, by rfl⟩ : syracuseStep 2561615 = 3842423) B3842423
theorem B1513097 : Blo 1008601 1513097 := bstep (se 2 (by rfl) ⟨567411, by rfl⟩ : syracuseStep 1513097 = 1134823) B1134823
theorem B1513115 : Blo 1008601 1513115 := bstep (se 1 (by rfl) ⟨1134836, by rfl⟩ : syracuseStep 1513115 = 2269673) B2269673
theorem B1513307 : Blo 1008601 1513307 := bstep (se 1 (by rfl) ⟨1134980, by rfl⟩ : syracuseStep 1513307 = 2269961) B2269961
theorem B12949469 : Blo 1008601 12949469 := bstep (se 3 (by rfl) ⟨2428025, by rfl⟩ : syracuseStep 12949469 = 4856051) B4856051
theorem B2430967 : Blo 1008601 2430967 := bstep (se 1 (by rfl) ⟨1823225, by rfl⟩ : syracuseStep 2430967 = 3646451) B3646451
theorem B7280765 : Blo 1008601 7280765 := bstep (se 3 (by rfl) ⟨1365143, by rfl⟩ : syracuseStep 7280765 = 2730287) B2730287
theorem B2562263 : Blo 1008601 2562263 := bstep (se 1 (by rfl) ⟨1921697, by rfl⟩ : syracuseStep 2562263 = 3843395) B3843395
theorem B1513691 : Blo 1008601 1513691 := bstep (se 1 (by rfl) ⟨1135268, by rfl⟩ : syracuseStep 1513691 = 2270537) B2270537
theorem B1513961 : Blo 1008601 1513961 := bstep (se 2 (by rfl) ⟨567735, by rfl⟩ : syracuseStep 1513961 = 1135471) B1135471
theorem B1022791 : Blo 1008601 1022791 := bstep (se 1 (by rfl) ⟨767093, by rfl⟩ : syracuseStep 1022791 = 1534187) B1534187
theorem B1514351 : Blo 1008601 1514351 := bstep (se 1 (by rfl) ⟨1135763, by rfl⟩ : syracuseStep 1514351 = 2271527) B2271527
theorem B1514363 : Blo 1008601 1514363 := bstep (se 1 (by rfl) ⟨1135772, by rfl⟩ : syracuseStep 1514363 = 2271545) B2271545
theorem B3415175 : Blo 1008601 3415175 := bstep (se 1 (by rfl) ⟨2561381, by rfl⟩ : syracuseStep 3415175 = 5122763) B5122763
theorem B6462791 : Blo 1008601 6462791 := bstep (se 1 (by rfl) ⟨4847093, by rfl⟩ : syracuseStep 6462791 = 9694187) B9694187
theorem B1515227 : Blo 1008601 1515227 := bstep (se 1 (by rfl) ⟨1136420, by rfl⟩ : syracuseStep 1515227 = 2272841) B2272841
theorem B3841769 : Blo 1008601 3841769 := bstep (se 2 (by rfl) ⟨1440663, by rfl⟩ : syracuseStep 3841769 = 2881327) B2881327
theorem B14589719 : Blo 1008601 14589719 := bstep (se 1 (by rfl) ⟨10942289, by rfl⟩ : syracuseStep 14589719 = 21884579) B21884579
theorem B6463405 : Blo 1008601 6463405 := bstep (se 3 (by rfl) ⟨1211888, by rfl⟩ : syracuseStep 6463405 = 2423777) B2423777
theorem B4104137 : Blo 1008601 4104137 := bstep (se 2 (by rfl) ⟨1539051, by rfl⟩ : syracuseStep 4104137 = 3078103) B3078103
theorem B1515497 : Blo 1008601 1515497 := bstep (se 2 (by rfl) ⟨568311, by rfl⟩ : syracuseStep 1515497 = 1136623) B1136623
theorem B4857995 : Blo 1008601 4857995 := bstep (se 1 (by rfl) ⟨3643496, by rfl⟩ : syracuseStep 4857995 = 7286993) B7286993
theorem B3842255 : Blo 1008601 3842255 := bstep (se 1 (by rfl) ⟨2881691, by rfl⟩ : syracuseStep 3842255 = 5763383) B5763383
theorem B2269439 : Blo 1008601 2269439 := bstep (se 1 (by rfl) ⟨1702079, by rfl⟩ : syracuseStep 2269439 = 3404159) B3404159
theorem B17277299 : Blo 1008601 17277299 := bstep (se 1 (by rfl) ⟨12957974, by rfl⟩ : syracuseStep 17277299 = 25915949) B25915949
theorem B2269601 : Blo 1008601 2269601 := bstep (se 2 (by rfl) ⟨851100, by rfl⟩ : syracuseStep 2269601 = 1702201) B1702201
theorem B31072691 : Blo 1008601 31072691 := bstep (se 1 (by rfl) ⟨23304518, by rfl⟩ : syracuseStep 31072691 = 46609037) B46609037
theorem B9708025 : Blo 1008601 9708025 := bstep (se 2 (by rfl) ⟨3640509, by rfl⟩ : syracuseStep 9708025 = 7281019) B7281019
theorem B1516199 : Blo 1008601 1516199 := bstep (se 1 (by rfl) ⟨1137149, by rfl⟩ : syracuseStep 1516199 = 2274299) B2274299
theorem B3416795 : Blo 1008601 3416795 := bstep (se 1 (by rfl) ⟨2562596, by rfl⟩ : syracuseStep 3416795 = 5125193) B5125193
theorem B1516319 : Blo 1008601 1516319 := bstep (se 1 (by rfl) ⟨1137239, by rfl⟩ : syracuseStep 1516319 = 2274479) B2274479
theorem B9708335 : Blo 1008601 9708335 := bstep (se 1 (by rfl) ⟨7281251, by rfl⟩ : syracuseStep 9708335 = 14562503) B14562503
theorem B1516343 : Blo 1008601 1516343 := bstep (se 1 (by rfl) ⟨1137257, by rfl⟩ : syracuseStep 1516343 = 2274515) B2274515
theorem B3416957 : Blo 1008601 3416957 := bstep (se 3 (by rfl) ⟨640679, by rfl⟩ : syracuseStep 3416957 = 1281359) B1281359
theorem B15541147 : Blo 1008601 15541147 := bstep (se 1 (by rfl) ⟨11655860, by rfl⟩ : syracuseStep 15541147 = 23311721) B23311721
theorem B3646379 : Blo 1008601 3646379 := bstep (se 1 (by rfl) ⟨2734784, by rfl⟩ : syracuseStep 3646379 = 5469569) B5469569
theorem B43688879 : Blo 1008601 43688879 := bstep (se 1 (by rfl) ⟨32766659, by rfl⟩ : syracuseStep 43688879 = 65533319) B65533319
theorem B1516523 : Blo 1008601 1516523 := bstep (se 1 (by rfl) ⟨1137392, by rfl⟩ : syracuseStep 1516523 = 2274785) B2274785
theorem B3417227 : Blo 1008601 3417227 := bstep (se 1 (by rfl) ⟨2562920, by rfl⟩ : syracuseStep 3417227 = 5125841) B5125841
theorem B2270375 : Blo 1008601 2270375 := bstep (se 1 (by rfl) ⟨1702781, by rfl⟩ : syracuseStep 2270375 = 3405563) B3405563
theorem B9348317 : Blo 1008601 9348317 := bstep (se 3 (by rfl) ⟨1752809, by rfl⟩ : syracuseStep 9348317 = 3505619) B3505619
theorem B2270483 : Blo 1008601 2270483 := bstep (se 1 (by rfl) ⟨1702862, by rfl⟩ : syracuseStep 2270483 = 3405725) B3405725
theorem B25863461 : Blo 1008601 25863461 := bstep (se 4 (by rfl) ⟨2424699, by rfl⟩ : syracuseStep 25863461 = 4849399) B4849399
theorem B2303561 : Blo 1008601 2303561 := bstep (se 2 (by rfl) ⟨863835, by rfl⟩ : syracuseStep 2303561 = 1727671) B1727671
theorem B9217745 : Blo 1008601 9217745 := bstep (se 2 (by rfl) ⟨3456654, by rfl⟩ : syracuseStep 9217745 = 6913309) B6913309
theorem B3843881 : Blo 1008601 3843881 := bstep (se 2 (by rfl) ⟨1441455, by rfl⟩ : syracuseStep 3843881 = 2882911) B2882911
theorem B19933037 : Blo 1008601 19933037 := bstep (se 3 (by rfl) ⟨3737444, by rfl⟩ : syracuseStep 19933037 = 7474889) B7474889
theorem B2271113 : Blo 1008601 2271113 := bstep (se 2 (by rfl) ⟨851667, by rfl⟩ : syracuseStep 2271113 = 1703335) B1703335
theorem B2271131 : Blo 1008601 2271131 := bstep (se 1 (by rfl) ⟨1703348, by rfl⟩ : syracuseStep 2271131 = 3406697) B3406697
theorem B2271167 : Blo 1008601 2271167 := bstep (se 1 (by rfl) ⟨1703375, by rfl⟩ : syracuseStep 2271167 = 3406751) B3406751
theorem B1517615 : Blo 1008601 1517615 := bstep (se 1 (by rfl) ⟨1138211, by rfl⟩ : syracuseStep 1517615 = 2276423) B2276423
theorem B2271329 : Blo 1008601 2271329 := bstep (se 2 (by rfl) ⟨851748, by rfl⟩ : syracuseStep 2271329 = 1703497) B1703497
theorem B1517879 : Blo 1008601 1517879 := bstep (se 1 (by rfl) ⟨1138409, by rfl⟩ : syracuseStep 1517879 = 2276819) B2276819
theorem B4860395 : Blo 1008601 4860395 := bstep (se 1 (by rfl) ⟨3645296, by rfl⟩ : syracuseStep 4860395 = 7290593) B7290593
theorem B1518059 : Blo 1008601 1518059 := bstep (se 1 (by rfl) ⟨1138544, by rfl⟩ : syracuseStep 1518059 = 2277089) B2277089
theorem B1518761 : Blo 1008601 1518761 := bstep (se 2 (by rfl) ⟨569535, by rfl⟩ : syracuseStep 1518761 = 1139071) B1139071
theorem B2272679 : Blo 1008601 2272679 := bstep (se 1 (by rfl) ⟨1704509, by rfl⟩ : syracuseStep 2272679 = 3409019) B3409019
theorem B2272859 : Blo 1008601 2272859 := bstep (se 1 (by rfl) ⟨1704644, by rfl⟩ : syracuseStep 2272859 = 3409289) B3409289
theorem B1617659 : Blo 1008601 1617659 := bstep (se 1 (by rfl) ⟨1213244, by rfl⟩ : syracuseStep 1617659 = 2426489) B2426489
theorem B14757869 : Blo 1008601 14757869 := bstep (se 3 (by rfl) ⟨2767100, by rfl⟩ : syracuseStep 14757869 = 5534201) B5534201
theorem B5844973 : Blo 1008601 5844973 := bstep (se 3 (by rfl) ⟨1095932, by rfl⟩ : syracuseStep 5844973 = 2191865) B2191865
theorem B2273273 : Blo 1008601 2273273 := bstep (se 2 (by rfl) ⟨852477, by rfl⟩ : syracuseStep 2273273 = 1704955) B1704955
theorem B2273363 : Blo 1008601 2273363 := bstep (se 1 (by rfl) ⟨1705022, by rfl⟩ : syracuseStep 2273363 = 3410045) B3410045
theorem B2273543 : Blo 1008601 2273543 := bstep (se 1 (by rfl) ⟨1705157, by rfl⟩ : syracuseStep 2273543 = 3410315) B3410315
theorem B16396829 : Blo 1008601 16396829 := bstep (se 3 (by rfl) ⟨3074405, by rfl⟩ : syracuseStep 16396829 = 6148811) B6148811
theorem B2273849 : Blo 1008601 2273849 := bstep (se 2 (by rfl) ⟨852693, by rfl⟩ : syracuseStep 2273849 = 1705387) B1705387
theorem B46707299 : Blo 1008601 46707299 := bstep (se 1 (by rfl) ⟨35030474, by rfl⟩ : syracuseStep 46707299 = 70060949) B70060949
theorem B6402725 : Blo 1008601 6402725 := bstep (se 4 (by rfl) ⟨600255, by rfl⟩ : syracuseStep 6402725 = 1200511) B1200511
theorem B5125031 : Blo 1008601 5125031 := bstep (se 1 (by rfl) ⟨3843773, by rfl⟩ : syracuseStep 5125031 = 7687547) B7687547
theorem B15545459 : Blo 1008601 15545459 := bstep (se 1 (by rfl) ⟨11659094, by rfl⟩ : syracuseStep 15545459 = 23318189) B23318189
theorem B2274569 : Blo 1008601 2274569 := bstep (se 2 (by rfl) ⟨852963, by rfl⟩ : syracuseStep 2274569 = 1705927) B1705927
theorem B2274623 : Blo 1008601 2274623 := bstep (se 1 (by rfl) ⟨1705967, by rfl⟩ : syracuseStep 2274623 = 3411935) B3411935
theorem B2274731 : Blo 1008601 2274731 := bstep (se 1 (by rfl) ⟨1706048, by rfl⟩ : syracuseStep 2274731 = 3412097) B3412097
theorem B4929133 : Blo 1008601 4929133 := bstep (se 3 (by rfl) ⟨924212, by rfl⟩ : syracuseStep 4929133 = 1848425) B1848425
theorem B2275055 : Blo 1008601 2275055 := bstep (se 1 (by rfl) ⟨1706291, by rfl⟩ : syracuseStep 2275055 = 3412583) B3412583
theorem B99727199 : Blo 1008601 99727199 := bstep (se 1 (by rfl) ⟨74795399, by rfl⟩ : syracuseStep 99727199 = 149590799) B149590799
theorem B2275271 : Blo 1008601 2275271 := bstep (se 1 (by rfl) ⟨1706453, by rfl⟩ : syracuseStep 2275271 = 3412907) B3412907
theorem B4864009 : Blo 1008601 4864009 := bstep (se 2 (by rfl) ⟨1824003, by rfl⟩ : syracuseStep 4864009 = 3648007) B3648007
theorem B2275559 : Blo 1008601 2275559 := bstep (se 1 (by rfl) ⟨1706669, by rfl⟩ : syracuseStep 2275559 = 3413339) B3413339
theorem B2275577 : Blo 1008601 2275577 := bstep (se 2 (by rfl) ⟨853341, by rfl⟩ : syracuseStep 2275577 = 1706683) B1706683
theorem B8206595 : Blo 1008601 8206595 := bstep (se 1 (by rfl) ⟨6154946, by rfl⟩ : syracuseStep 8206595 = 12309893) B12309893
theorem B2275631 : Blo 1008601 2275631 := bstep (se 1 (by rfl) ⟨1706723, by rfl⟩ : syracuseStep 2275631 = 3413447) B3413447
theorem B2734535 : Blo 1008601 2734535 := bstep (se 1 (by rfl) ⟨2050901, by rfl⟩ : syracuseStep 2734535 = 4101803) B4101803
theorem B2275847 : Blo 1008601 2275847 := bstep (se 1 (by rfl) ⟨1706885, by rfl⟩ : syracuseStep 2275847 = 3413771) B3413771
theorem B16824893 : Blo 1008601 16824893 := bstep (se 3 (by rfl) ⟨3154667, by rfl⟩ : syracuseStep 16824893 = 6309335) B6309335
theorem B2276027 : Blo 1008601 2276027 := bstep (se 1 (by rfl) ⟨1707020, by rfl⟩ : syracuseStep 2276027 = 3414041) B3414041
theorem B2276927 : Blo 1008601 2276927 := bstep (se 1 (by rfl) ⟨1707695, by rfl⟩ : syracuseStep 2276927 = 3415391) B3415391
theorem B25902827 : Blo 1008601 25902827 := bstep (se 1 (by rfl) ⟨19427120, by rfl⟩ : syracuseStep 25902827 = 38854241) B38854241
theorem B2277287 : Blo 1008601 2277287 := bstep (se 1 (by rfl) ⟨1707965, by rfl⟩ : syracuseStep 2277287 = 3415931) B3415931
theorem B2277611 : Blo 1008601 2277611 := bstep (se 1 (by rfl) ⟨1708208, by rfl⟩ : syracuseStep 2277611 = 3416417) B3416417
theorem B46679237 : Blo 1008601 46679237 := bstep (se 4 (by rfl) ⟨4376178, by rfl⟩ : syracuseStep 46679237 = 8752357) B8752357
theorem B4310441 : Blo 1008601 4310441 := bstep (se 2 (by rfl) ⟨1616415, by rfl⟩ : syracuseStep 4310441 = 3232831) B3232831
theorem B15550649 : Blo 1008601 15550649 := bstep (se 2 (by rfl) ⟨5831493, by rfl⟩ : syracuseStep 15550649 = 11662987) B11662987
theorem B17517455 : Blo 1008601 17517455 := bstep (se 1 (by rfl) ⟨13138091, by rfl⟩ : syracuseStep 17517455 = 26276183) B26276183
theorem B14568497 : Blo 1008601 14568497 := bstep (se 2 (by rfl) ⟨5463186, by rfl⟩ : syracuseStep 14568497 = 10926373) B10926373
theorem B10505369 : Blo 1008601 10505369 := bstep (se 2 (by rfl) ⟨3939513, by rfl⟩ : syracuseStep 10505369 = 7879027) B7879027
theorem B10374475 : Blo 1008601 10374475 := bstep (se 1 (by rfl) ⟨7780856, by rfl⟩ : syracuseStep 10374475 = 15561713) B15561713
theorem B1822043 : Blo 1008601 1822043 := bstep (se 1 (by rfl) ⟨1366532, by rfl⟩ : syracuseStep 1822043 = 2733065) B2733065
theorem B87510617 : Blo 1008601 87510617 := bstep (se 2 (by rfl) ⟨32816481, by rfl⟩ : syracuseStep 87510617 = 65632963) B65632963
theorem B33246895 : Blo 1008601 33246895 := bstep (se 1 (by rfl) ⟨24935171, by rfl⟩ : syracuseStep 33246895 = 49870343) B49870343
theorem B12930911 : Blo 1008601 12930911 := bstep (se 1 (by rfl) ⟨9698183, by rfl⟩ : syracuseStep 12930911 = 19396367) B19396367
theorem B1822591 : Blo 1008601 1822591 := bstep (se 1 (by rfl) ⟨1366943, by rfl⟩ : syracuseStep 1822591 = 2733887) B2733887
theorem B4313243 : Blo 1008601 4313243 := bstep (se 1 (by rfl) ⟨3234932, by rfl⟩ : syracuseStep 4313243 = 6469865) B6469865
theorem B1135003 : Blo 1008601 1135003 := bstep (se 1 (by rfl) ⟨851252, by rfl⟩ : syracuseStep 1135003 = 1702505) B1702505
theorem B2872169 : Blo 1008601 2872169 := bstep (se 2 (by rfl) ⟨1077063, by rfl⟩ : syracuseStep 2872169 = 2154127) B2154127
theorem B1135687 : Blo 1008601 1135687 := bstep (se 1 (by rfl) ⟨851765, by rfl⟩ : syracuseStep 1135687 = 1703531) B1703531
theorem B1135867 : Blo 1008601 1135867 := bstep (se 1 (by rfl) ⟨851900, by rfl⟩ : syracuseStep 1135867 = 1703801) B1703801
theorem B26203769 : Blo 1008601 26203769 := bstep (se 2 (by rfl) ⟨9826413, by rfl⟩ : syracuseStep 26203769 = 19652827) B19652827
theorem B14571845 : Blo 1008601 14571845 := bstep (se 4 (by rfl) ⟨1366110, by rfl⟩ : syracuseStep 14571845 = 2732221) B2732221
theorem B1137055 : Blo 1008601 1137055 := bstep (se 1 (by rfl) ⟨852791, by rfl⟩ : syracuseStep 1137055 = 1705583) B1705583
theorem B1137127 : Blo 1008601 1137127 := bstep (se 1 (by rfl) ⟨852845, by rfl⟩ : syracuseStep 1137127 = 1705691) B1705691
theorem B3070831 : Blo 1008601 3070831 := bstep (se 1 (by rfl) ⟨2303123, by rfl⟩ : syracuseStep 3070831 = 4606247) B4606247
theorem B3234779 : Blo 1008601 3234779 := bstep (se 1 (by rfl) ⟨2426084, by rfl⟩ : syracuseStep 3234779 = 4852169) B4852169
theorem B1137991 : Blo 1008601 1137991 := bstep (se 1 (by rfl) ⟨853493, by rfl⟩ : syracuseStep 1137991 = 1706987) B1706987
theorem B6479297 : Blo 1008601 6479297 := bstep (se 2 (by rfl) ⟨2429736, by rfl⟩ : syracuseStep 6479297 = 4859473) B4859473
theorem B5463533 : Blo 1008601 5463533 := bstep (se 3 (by rfl) ⟨1024412, by rfl⟩ : syracuseStep 5463533 = 2048825) B2048825
theorem B18472859 : Blo 1008601 18472859 := bstep (se 1 (by rfl) ⟨13854644, by rfl⟩ : syracuseStep 18472859 = 27709289) B27709289
theorem B8314807 : Blo 1008601 8314807 := bstep (se 1 (by rfl) ⟨6236105, by rfl⟩ : syracuseStep 8314807 = 12472211) B12472211
theorem B5759261 : Blo 1008601 5759261 := bstep (se 3 (by rfl) ⟨1079861, by rfl⟩ : syracuseStep 5759261 = 2159723) B2159723
theorem B2876111 : Blo 1008601 2876111 := bstep (se 1 (by rfl) ⟨2157083, by rfl⟩ : syracuseStep 2876111 = 4314167) B4314167
theorem B1008687 : Blo 1008601 1008687 := bstep (se 1 (by rfl) ⟨756515, by rfl⟩ : syracuseStep 1008687 = 1513031) B1513031
theorem B1008751 : Blo 1008601 1008751 := bstep (se 1 (by rfl) ⟨756563, by rfl⟩ : syracuseStep 1008751 = 1513127) B1513127
theorem B1008807 : Blo 1008601 1008807 := bstep (se 1 (by rfl) ⟨756605, by rfl⟩ : syracuseStep 1008807 = 1513211) B1513211
theorem B1008831 : Blo 1008601 1008831 := bstep (se 1 (by rfl) ⟨756623, by rfl⟩ : syracuseStep 1008831 = 1513247) B1513247
theorem B1008863 : Blo 1008601 1008863 := bstep (se 1 (by rfl) ⟨756647, by rfl⟩ : syracuseStep 1008863 = 1513295) B1513295
theorem B1008943 : Blo 1008601 1008943 := bstep (se 1 (by rfl) ⟨756707, by rfl⟩ : syracuseStep 1008943 = 1513415) B1513415
theorem B13854091 : Blo 1008601 13854091 := bstep (se 1 (by rfl) ⟨10390568, by rfl⟩ : syracuseStep 13854091 = 20781137) B20781137
theorem B1009179 : Blo 1008601 1009179 := bstep (se 1 (by rfl) ⟨756884, by rfl⟩ : syracuseStep 1009179 = 1513769) B1513769
theorem B1009183 : Blo 1008601 1009183 := bstep (se 1 (by rfl) ⟨756887, by rfl⟩ : syracuseStep 1009183 = 1513775) B1513775
theorem B1009343 : Blo 1008601 1009343 := bstep (se 1 (by rfl) ⟨757007, by rfl⟩ : syracuseStep 1009343 = 1514015) B1514015
theorem B23357263 : Blo 1008601 23357263 := bstep (se 1 (by rfl) ⟨17517947, by rfl⟩ : syracuseStep 23357263 = 35035895) B35035895
theorem B19392371 : Blo 1008601 19392371 := bstep (se 1 (by rfl) ⟨14544278, by rfl⟩ : syracuseStep 19392371 = 29088557) B29088557
theorem B2844571 : Blo 1008601 2844571 := bstep (se 1 (by rfl) ⟨2133428, by rfl⟩ : syracuseStep 2844571 = 4266857) B4266857
theorem B1009599 : Blo 1008601 1009599 := bstep (se 1 (by rfl) ⟨757199, by rfl⟩ : syracuseStep 1009599 = 1514399) B1514399
theorem B1009631 : Blo 1008601 1009631 := bstep (se 1 (by rfl) ⟨757223, by rfl⟩ : syracuseStep 1009631 = 1514447) B1514447
theorem B2156537 : Blo 1008601 2156537 := bstep (se 2 (by rfl) ⟨808701, by rfl⟩ : syracuseStep 2156537 = 1617403) B1617403
theorem B1009691 : Blo 1008601 1009691 := bstep (se 1 (by rfl) ⟨757268, by rfl⟩ : syracuseStep 1009691 = 1514537) B1514537
theorem B1009695 : Blo 1008601 1009695 := bstep (se 1 (by rfl) ⟨757271, by rfl⟩ : syracuseStep 1009695 = 1514543) B1514543
theorem B1009711 : Blo 1008601 1009711 := bstep (se 1 (by rfl) ⟨757283, by rfl⟩ : syracuseStep 1009711 = 1514567) B1514567
theorem B1009887 : Blo 1008601 1009887 := bstep (se 1 (by rfl) ⟨757415, by rfl⟩ : syracuseStep 1009887 = 1514831) B1514831
theorem B1009947 : Blo 1008601 1009947 := bstep (se 1 (by rfl) ⟨757460, by rfl⟩ : syracuseStep 1009947 = 1514921) B1514921
theorem B1010047 : Blo 1008601 1010047 := bstep (se 1 (by rfl) ⟨757535, by rfl⟩ : syracuseStep 1010047 = 1515071) B1515071
theorem B1010223 : Blo 1008601 1010223 := bstep (se 1 (by rfl) ⟨757667, by rfl⟩ : syracuseStep 1010223 = 1515335) B1515335
theorem B1010279 : Blo 1008601 1010279 := bstep (se 1 (by rfl) ⟨757709, by rfl⟩ : syracuseStep 1010279 = 1515419) B1515419
theorem B5827493 : Blo 1008601 5827493 := bstep (se 4 (by rfl) ⟨546327, by rfl⟩ : syracuseStep 5827493 = 1092655) B1092655
theorem B6482861 : Blo 1008601 6482861 := bstep (se 3 (by rfl) ⟨1215536, by rfl⟩ : syracuseStep 6482861 = 2431073) B2431073
theorem B1010655 : Blo 1008601 1010655 := bstep (se 1 (by rfl) ⟨757991, by rfl⟩ : syracuseStep 1010655 = 1515983) B1515983
theorem B1010683 : Blo 1008601 1010683 := bstep (se 1 (by rfl) ⟨758012, by rfl⟩ : syracuseStep 1010683 = 1516025) B1516025
theorem B1010751 : Blo 1008601 1010751 := bstep (se 1 (by rfl) ⟨758063, by rfl⟩ : syracuseStep 1010751 = 1516127) B1516127
theorem B2878537 : Blo 1008601 2878537 := bstep (se 2 (by rfl) ⟨1079451, by rfl⟩ : syracuseStep 2878537 = 2158903) B2158903
theorem B5107049 : Blo 1008601 5107049 := bstep (se 2 (by rfl) ⟨1915143, by rfl⟩ : syracuseStep 5107049 = 3830287) B3830287
theorem B1011071 : Blo 1008601 1011071 := bstep (se 1 (by rfl) ⟨758303, by rfl⟩ : syracuseStep 1011071 = 1516607) B1516607
theorem B1011099 : Blo 1008601 1011099 := bstep (se 1 (by rfl) ⟨758324, by rfl⟩ : syracuseStep 1011099 = 1516649) B1516649
theorem B1011167 : Blo 1008601 1011167 := bstep (se 1 (by rfl) ⟨758375, by rfl⟩ : syracuseStep 1011167 = 1516751) B1516751
theorem B1011303 : Blo 1008601 1011303 := bstep (se 1 (by rfl) ⟨758477, by rfl⟩ : syracuseStep 1011303 = 1516955) B1516955
theorem B1011451 : Blo 1008601 1011451 := bstep (se 1 (by rfl) ⟨758588, by rfl⟩ : syracuseStep 1011451 = 1517177) B1517177
theorem B1011519 : Blo 1008601 1011519 := bstep (se 1 (by rfl) ⟨758639, by rfl⟩ : syracuseStep 1011519 = 1517279) B1517279
theorem B1011583 : Blo 1008601 1011583 := bstep (se 1 (by rfl) ⟨758687, by rfl⟩ : syracuseStep 1011583 = 1517375) B1517375
theorem B1011695 : Blo 1008601 1011695 := bstep (se 1 (by rfl) ⟨758771, by rfl⟩ : syracuseStep 1011695 = 1517543) B1517543
theorem B1011707 : Blo 1008601 1011707 := bstep (se 1 (by rfl) ⟨758780, by rfl⟩ : syracuseStep 1011707 = 1517561) B1517561
theorem B7893011 : Blo 1008601 7893011 := bstep (se 1 (by rfl) ⟨5919758, by rfl⟩ : syracuseStep 7893011 = 11839517) B11839517
theorem B1011775 : Blo 1008601 1011775 := bstep (se 1 (by rfl) ⟨758831, by rfl⟩ : syracuseStep 1011775 = 1517663) B1517663
theorem B1011815 : Blo 1008601 1011815 := bstep (se 1 (by rfl) ⟨758861, by rfl⟩ : syracuseStep 1011815 = 1517723) B1517723
theorem B1011839 : Blo 1008601 1011839 := bstep (se 1 (by rfl) ⟨758879, by rfl⟩ : syracuseStep 1011839 = 1517759) B1517759
theorem B1011867 : Blo 1008601 1011867 := bstep (se 1 (by rfl) ⟨758900, by rfl⟩ : syracuseStep 1011867 = 1517801) B1517801
theorem B1012071 : Blo 1008601 1012071 := bstep (se 1 (by rfl) ⟨759053, by rfl⟩ : syracuseStep 1012071 = 1518107) B1518107
theorem B1012123 : Blo 1008601 1012123 := bstep (se 1 (by rfl) ⟨759092, by rfl⟩ : syracuseStep 1012123 = 1518185) B1518185
theorem B2879995 : Blo 1008601 2879995 := bstep (se 1 (by rfl) ⟨2159996, by rfl⟩ : syracuseStep 2879995 = 4319993) B4319993
theorem B1012475 : Blo 1008601 1012475 := bstep (se 1 (by rfl) ⟨759356, by rfl⟩ : syracuseStep 1012475 = 1518713) B1518713
theorem B1012543 : Blo 1008601 1012543 := bstep (se 1 (by rfl) ⟨759407, by rfl⟩ : syracuseStep 1012543 = 1518815) B1518815
theorem B1012571 : Blo 1008601 1012571 := bstep (se 1 (by rfl) ⟨759428, by rfl⟩ : syracuseStep 1012571 = 1518857) B1518857
theorem B3831047 : Blo 1008601 3831047 := bstep (se 1 (by rfl) ⟨2873285, by rfl⟩ : syracuseStep 3831047 = 5746571) B5746571
theorem B4322591 : Blo 1008601 4322591 := bstep (se 1 (by rfl) ⟨3241943, by rfl⟩ : syracuseStep 4322591 = 6483887) B6483887
theorem B5764567 : Blo 1008601 5764567 := bstep (se 1 (by rfl) ⟨4323425, by rfl⟩ : syracuseStep 5764567 = 8646851) B8646851
theorem B10384985 : Blo 1008601 10384985 := bstep (se 2 (by rfl) ⟨3894369, by rfl⟩ : syracuseStep 10384985 = 7788739) B7788739
theorem B3831563 : Blo 1008601 3831563 := bstep (se 1 (by rfl) ⟨2873672, by rfl⟩ : syracuseStep 3831563 = 5747345) B5747345
theorem B1079131 : Blo 1008601 1079131 := bstep (se 1 (by rfl) ⟨809348, by rfl⟩ : syracuseStep 1079131 = 1618697) B1618697
theorem B3832019 : Blo 1008601 3832019 := bstep (se 1 (by rfl) ⟨2874014, by rfl⟩ : syracuseStep 3832019 = 5748029) B5748029
theorem B4323631 : Blo 1008601 4323631 := bstep (se 1 (by rfl) ⟨3242723, by rfl⟩ : syracuseStep 4323631 = 6485447) B6485447
theorem B1702343 : Blo 1008601 1702343 := bstep (se 1 (by rfl) ⟨1276757, by rfl⟩ : syracuseStep 1702343 = 2553515) B2553515
theorem B4848169 : Blo 1008601 4848169 := bstep (se 2 (by rfl) ⟨1818063, by rfl⟩ : syracuseStep 4848169 = 3636127) B3636127
theorem B3406427 : Blo 1008601 3406427 := bstep (se 1 (by rfl) ⟨2554820, by rfl⟩ : syracuseStep 3406427 = 5109641) B5109641
theorem B1702559 : Blo 1008601 1702559 := bstep (se 1 (by rfl) ⟨1276919, by rfl⟩ : syracuseStep 1702559 = 2553839) B2553839
theorem B1702633 : Blo 1008601 1702633 := bstep (se 2 (by rfl) ⟨638487, by rfl⟩ : syracuseStep 1702633 = 1276975) B1276975
theorem B5110775 : Blo 1008601 5110775 := bstep (se 1 (by rfl) ⟨3833081, by rfl⟩ : syracuseStep 5110775 = 7666163) B7666163
theorem B3407129 : Blo 1008601 3407129 := bstep (se 2 (by rfl) ⟨1277673, by rfl⟩ : syracuseStep 3407129 = 2555347) B2555347
theorem B2162089 : Blo 1008601 2162089 := bstep (se 2 (by rfl) ⟨810783, by rfl⟩ : syracuseStep 2162089 = 1621567) B1621567
theorem B9731785 : Blo 1008601 9731785 := bstep (se 2 (by rfl) ⟨3649419, by rfl⟩ : syracuseStep 9731785 = 7298839) B7298839
theorem B2556319 : Blo 1008601 2556319 := bstep (se 1 (by rfl) ⟨1917239, by rfl⟩ : syracuseStep 2556319 = 3834479) B3834479
theorem B5833223 : Blo 1008601 5833223 := bstep (se 1 (by rfl) ⟨4374917, by rfl⟩ : syracuseStep 5833223 = 8749835) B8749835
theorem B12944033 : Blo 1008601 12944033 := bstep (se 2 (by rfl) ⟨4854012, by rfl⟩ : syracuseStep 12944033 = 9708025) B9708025
theorem B3408695 : Blo 1008601 3408695 := bstep (se 1 (by rfl) ⟨2556521, by rfl⟩ : syracuseStep 3408695 = 5113043) B5113043
theorem B10945367 : Blo 1008601 10945367 := bstep (se 1 (by rfl) ⟨8209025, by rfl⟩ : syracuseStep 10945367 = 16418051) B16418051
theorem B1705225 : Blo 1008601 1705225 := bstep (se 2 (by rfl) ⟨639459, by rfl⟩ : syracuseStep 1705225 = 1278919) B1278919
theorem B3409775 : Blo 1008601 3409775 := bstep (se 1 (by rfl) ⟨2557331, by rfl⟩ : syracuseStep 3409775 = 5114663) B5114663
theorem B1214695 : Blo 1008601 1214695 := bstep (se 1 (by rfl) ⟨911021, by rfl⟩ : syracuseStep 1214695 = 1822043) B1822043
theorem B3410153 : Blo 1008601 3410153 := bstep (se 2 (by rfl) ⟨1278807, by rfl⟩ : syracuseStep 3410153 = 2557615) B2557615
theorem B2427383 : Blo 1008601 2427383 := bstep (se 1 (by rfl) ⟨1820537, by rfl⟩ : syracuseStep 2427383 = 3641075) B3641075
theorem B8620607 : Blo 1008601 8620607 := bstep (se 1 (by rfl) ⟨6465455, by rfl⟩ : syracuseStep 8620607 = 12930911) B12930911
theorem B9833159 : Blo 1008601 9833159 := bstep (se 1 (by rfl) ⟨7374869, by rfl⟩ : syracuseStep 9833159 = 14749739) B14749739
theorem B5114825 : Blo 1008601 5114825 := bstep (se 2 (by rfl) ⟨1918059, by rfl⟩ : syracuseStep 5114825 = 3836119) B3836119
theorem B5114987 : Blo 1008601 5114987 := bstep (se 1 (by rfl) ⟨3836240, by rfl⟩ : syracuseStep 5114987 = 7672481) B7672481
theorem B10358027 : Blo 1008601 10358027 := bstep (se 1 (by rfl) ⟨7768520, by rfl⟩ : syracuseStep 10358027 = 15537041) B15537041
theorem B1707547 : Blo 1008601 1707547 := bstep (se 1 (by rfl) ⟨1280660, by rfl⟩ : syracuseStep 1707547 = 2561321) B2561321
theorem B1707743 : Blo 1008601 1707743 := bstep (se 1 (by rfl) ⟨1280807, by rfl⟩ : syracuseStep 1707743 = 2561615) B2561615
theorem B17469179 : Blo 1008601 17469179 := bstep (se 1 (by rfl) ⟨13101884, by rfl⟩ : syracuseStep 17469179 = 26203769) B26203769
theorem B4853843 : Blo 1008601 4853843 := bstep (se 1 (by rfl) ⟨3640382, by rfl⟩ : syracuseStep 4853843 = 7280765) B7280765
theorem B3838049 : Blo 1008601 3838049 := bstep (se 2 (by rfl) ⟨1439268, by rfl⟩ : syracuseStep 3838049 = 2878537) B2878537
theorem B1708175 : Blo 1008601 1708175 := bstep (se 1 (by rfl) ⟨1281131, by rfl⟩ : syracuseStep 1708175 = 2562263) B2562263
theorem B13832633 : Blo 1008601 13832633 := bstep (se 2 (by rfl) ⟨5187237, by rfl⟩ : syracuseStep 13832633 = 10374475) B10374475
theorem B3642355 : Blo 1008601 3642355 := bstep (se 1 (by rfl) ⟨2731766, by rfl⟩ : syracuseStep 3642355 = 5463533) B5463533
theorem B2561179 : Blo 1008601 2561179 := bstep (se 1 (by rfl) ⟨1920884, by rfl⟩ : syracuseStep 2561179 = 3841769) B3841769
theorem B2561503 : Blo 1008601 2561503 := bstep (se 1 (by rfl) ⟨1921127, by rfl⟩ : syracuseStep 2561503 = 3842255) B3842255
theorem B1512959 : Blo 1008601 1512959 := bstep (se 1 (by rfl) ⟨1134719, by rfl⟩ : syracuseStep 1512959 = 2269439) B2269439
theorem B3839507 : Blo 1008601 3839507 := bstep (se 1 (by rfl) ⟨2879630, by rfl⟩ : syracuseStep 3839507 = 5759261) B5759261
theorem B1513067 : Blo 1008601 1513067 := bstep (se 1 (by rfl) ⟨1134800, by rfl⟩ : syracuseStep 1513067 = 2269601) B2269601
theorem B1513337 : Blo 1008601 1513337 := bstep (se 2 (by rfl) ⟨567501, by rfl⟩ : syracuseStep 1513337 = 1135003) B1135003
theorem B2430919 : Blo 1008601 2430919 := bstep (se 1 (by rfl) ⟨1823189, by rfl⟩ : syracuseStep 2430919 = 3646379) B3646379
theorem B3839993 : Blo 1008601 3839993 := bstep (se 2 (by rfl) ⟨1439997, by rfl⟩ : syracuseStep 3839993 = 2879995) B2879995
theorem B1513583 : Blo 1008601 1513583 := bstep (se 1 (by rfl) ⟨1135187, by rfl⟩ : syracuseStep 1513583 = 2270375) B2270375
theorem B6232211 : Blo 1008601 6232211 := bstep (se 1 (by rfl) ⟨4674158, by rfl⟩ : syracuseStep 6232211 = 9348317) B9348317
theorem B1513655 : Blo 1008601 1513655 := bstep (se 1 (by rfl) ⟨1135241, by rfl⟩ : syracuseStep 1513655 = 2270483) B2270483
theorem B17242307 : Blo 1008601 17242307 := bstep (se 1 (by rfl) ⟨12931730, by rfl⟩ : syracuseStep 17242307 = 25863461) B25863461
theorem B2562587 : Blo 1008601 2562587 := bstep (se 1 (by rfl) ⟨1921940, by rfl⟩ : syracuseStep 2562587 = 3843881) B3843881
theorem B1514075 : Blo 1008601 1514075 := bstep (se 1 (by rfl) ⟨1135556, by rfl⟩ : syracuseStep 1514075 = 2271113) B2271113
theorem B1514087 : Blo 1008601 1514087 := bstep (se 1 (by rfl) ⟨1135565, by rfl⟩ : syracuseStep 1514087 = 2271131) B2271131
theorem B1514111 : Blo 1008601 1514111 := bstep (se 1 (by rfl) ⟨1135583, by rfl⟩ : syracuseStep 1514111 = 2271167) B2271167
theorem B1514219 : Blo 1008601 1514219 := bstep (se 1 (by rfl) ⟨1135664, by rfl⟩ : syracuseStep 1514219 = 2271329) B2271329
theorem B1514249 : Blo 1008601 1514249 := bstep (se 2 (by rfl) ⟨567843, by rfl⟩ : syracuseStep 1514249 = 1135687) B1135687
theorem B44866381 : Blo 1008601 44866381 := bstep (se 3 (by rfl) ⟨8412446, by rfl⟩ : syracuseStep 44866381 = 16824893) B16824893
theorem B4856705 : Blo 1008601 4856705 := bstep (se 2 (by rfl) ⟨1821264, by rfl⟩ : syracuseStep 4856705 = 3642529) B3642529
theorem B1514489 : Blo 1008601 1514489 := bstep (se 2 (by rfl) ⟨567933, by rfl⟩ : syracuseStep 1514489 = 1135867) B1135867
theorem B1515119 : Blo 1008601 1515119 := bstep (se 1 (by rfl) ⟨1136339, by rfl⟩ : syracuseStep 1515119 = 2272679) B2272679
theorem B1515239 : Blo 1008601 1515239 := bstep (se 1 (by rfl) ⟨1136429, by rfl⟩ : syracuseStep 1515239 = 2272859) B2272859
theorem B9838579 : Blo 1008601 9838579 := bstep (se 1 (by rfl) ⟨7378934, by rfl⟩ : syracuseStep 9838579 = 14757869) B14757869
theorem B1515515 : Blo 1008601 1515515 := bstep (se 1 (by rfl) ⟨1136636, by rfl⟩ : syracuseStep 1515515 = 2273273) B2273273
theorem B1515575 : Blo 1008601 1515575 := bstep (se 1 (by rfl) ⟨1136681, by rfl⟩ : syracuseStep 1515575 = 2273363) B2273363
theorem B1515695 : Blo 1008601 1515695 := bstep (se 1 (by rfl) ⟨1136771, by rfl⟩ : syracuseStep 1515695 = 2273543) B2273543
theorem B1515899 : Blo 1008601 1515899 := bstep (se 1 (by rfl) ⟨1136924, by rfl⟩ : syracuseStep 1515899 = 2273849) B2273849
theorem B31138199 : Blo 1008601 31138199 := bstep (se 1 (by rfl) ⟨23353649, by rfl⟩ : syracuseStep 31138199 = 46707299) B46707299
theorem B4268483 : Blo 1008601 4268483 := bstep (se 1 (by rfl) ⟨3201362, by rfl⟩ : syracuseStep 4268483 = 6402725) B6402725
theorem B6136357 : Blo 1008601 6136357 := bstep (se 4 (by rfl) ⟨575283, by rfl⟩ : syracuseStep 6136357 = 1150567) B1150567
theorem B1516073 : Blo 1008601 1516073 := bstep (se 2 (by rfl) ⟨568527, by rfl⟩ : syracuseStep 1516073 = 1137055) B1137055
theorem B3416687 : Blo 1008601 3416687 := bstep (se 1 (by rfl) ⟨2562515, by rfl⟩ : syracuseStep 3416687 = 5125031) B5125031
theorem B1516169 : Blo 1008601 1516169 := bstep (se 2 (by rfl) ⟨568563, by rfl⟩ : syracuseStep 1516169 = 1137127) B1137127
theorem B6464225 : Blo 1008601 6464225 := bstep (se 2 (by rfl) ⟨2424084, by rfl⟩ : syracuseStep 6464225 = 4848169) B4848169
theorem B10363639 : Blo 1008601 10363639 := bstep (se 1 (by rfl) ⟨7772729, by rfl⟩ : syracuseStep 10363639 = 15545459) B15545459
theorem B1516379 : Blo 1008601 1516379 := bstep (se 1 (by rfl) ⟨1137284, by rfl⟩ : syracuseStep 1516379 = 2274569) B2274569
theorem B1516415 : Blo 1008601 1516415 := bstep (se 1 (by rfl) ⟨1137311, by rfl⟩ : syracuseStep 1516415 = 2274623) B2274623
theorem B1516487 : Blo 1008601 1516487 := bstep (se 1 (by rfl) ⟨1137365, by rfl⟩ : syracuseStep 1516487 = 2274731) B2274731
theorem B2270177 : Blo 1008601 2270177 := bstep (se 2 (by rfl) ⟨851316, by rfl⟩ : syracuseStep 2270177 = 1702633) B1702633
theorem B6923323 : Blo 1008601 6923323 := bstep (se 1 (by rfl) ⟨5192492, by rfl⟩ : syracuseStep 6923323 = 10384985) B10384985
theorem B1516703 : Blo 1008601 1516703 := bstep (se 1 (by rfl) ⟨1137527, by rfl⟩ : syracuseStep 1516703 = 2275055) B2275055
theorem B1516847 : Blo 1008601 1516847 := bstep (se 1 (by rfl) ⟨1137635, by rfl⟩ : syracuseStep 1516847 = 2275271) B2275271
theorem B1517039 : Blo 1008601 1517039 := bstep (se 1 (by rfl) ⟨1137779, by rfl⟩ : syracuseStep 1517039 = 2275559) B2275559
theorem B1517051 : Blo 1008601 1517051 := bstep (se 1 (by rfl) ⟨1137788, by rfl⟩ : syracuseStep 1517051 = 2275577) B2275577
theorem B1517087 : Blo 1008601 1517087 := bstep (se 1 (by rfl) ⟨1137815, by rfl⟩ : syracuseStep 1517087 = 2275631) B2275631
theorem B1517231 : Blo 1008601 1517231 := bstep (se 1 (by rfl) ⟨1137923, by rfl⟩ : syracuseStep 1517231 = 2275847) B2275847
theorem B2270951 : Blo 1008601 2270951 := bstep (se 1 (by rfl) ⟨1703213, by rfl⟩ : syracuseStep 2270951 = 3406427) B3406427
theorem B1517321 : Blo 1008601 1517321 := bstep (se 2 (by rfl) ⟨568995, by rfl⟩ : syracuseStep 1517321 = 1137991) B1137991
theorem B1517351 : Blo 1008601 1517351 := bstep (se 1 (by rfl) ⟨1138013, by rfl⟩ : syracuseStep 1517351 = 2276027) B2276027
theorem B2271419 : Blo 1008601 2271419 := bstep (se 1 (by rfl) ⟨1703564, by rfl⟩ : syracuseStep 2271419 = 3407129) B3407129
theorem B1517951 : Blo 1008601 1517951 := bstep (se 1 (by rfl) ⟨1138463, by rfl⟩ : syracuseStep 1517951 = 2276927) B2276927
theorem B11086409 : Blo 1008601 11086409 := bstep (se 2 (by rfl) ⟨4157403, by rfl⟩ : syracuseStep 11086409 = 8314807) B8314807
theorem B1518191 : Blo 1008601 1518191 := bstep (se 1 (by rfl) ⟨1138643, by rfl⟩ : syracuseStep 1518191 = 2277287) B2277287
theorem B21048029 : Blo 1008601 21048029 := bstep (se 3 (by rfl) ⟨3946505, by rfl⟩ : syracuseStep 21048029 = 7893011) B7893011
theorem B1518407 : Blo 1008601 1518407 := bstep (se 1 (by rfl) ⟨1138805, by rfl⟩ : syracuseStep 1518407 = 2277611) B2277611
theorem B2272319 : Blo 1008601 2272319 := bstep (se 1 (by rfl) ⟨1704239, by rfl⟩ : syracuseStep 2272319 = 3408479) B3408479
theorem B6663943 : Blo 1008601 6663943 := bstep (se 1 (by rfl) ⟨4997957, by rfl⟩ : syracuseStep 6663943 = 9995915) B9995915
theorem B20721529 : Blo 1008601 20721529 := bstep (se 2 (by rfl) ⟨7770573, by rfl⟩ : syracuseStep 20721529 = 15541147) B15541147
theorem B2273147 : Blo 1008601 2273147 := bstep (se 1 (by rfl) ⟨1704860, by rfl⟩ : syracuseStep 2273147 = 3409721) B3409721
theorem B10367099 : Blo 1008601 10367099 := bstep (se 1 (by rfl) ⟨7775324, by rfl⟩ : syracuseStep 10367099 = 15550649) B15550649
theorem B11678303 : Blo 1008601 11678303 := bstep (se 1 (by rfl) ⟨8758727, by rfl⟩ : syracuseStep 11678303 = 17517455) B17517455
theorem B9712331 : Blo 1008601 9712331 := bstep (se 1 (by rfl) ⟨7284248, by rfl⟩ : syracuseStep 9712331 = 14568497) B14568497
theorem B58340411 : Blo 1008601 58340411 := bstep (se 1 (by rfl) ⟨43755308, by rfl⟩ : syracuseStep 58340411 = 87510617) B87510617
theorem B31143017 : Blo 1008601 31143017 := bstep (se 2 (by rfl) ⟨11678631, by rfl⟩ : syracuseStep 31143017 = 23357263) B23357263
theorem B6141271 : Blo 1008601 6141271 := bstep (se 1 (by rfl) ⟨4605953, by rfl⟩ : syracuseStep 6141271 = 9211907) B9211907
theorem B2275091 : Blo 1008601 2275091 := bstep (se 1 (by rfl) ⟨1706318, by rfl⟩ : syracuseStep 2275091 = 3412637) B3412637
theorem B1914779 : Blo 1008601 1914779 := bstep (se 1 (by rfl) ⟨1436084, by rfl⟩ : syracuseStep 1914779 = 2872169) B2872169
theorem B14596175 : Blo 1008601 14596175 := bstep (se 1 (by rfl) ⟨10947131, by rfl⟩ : syracuseStep 14596175 = 21894263) B21894263
theorem B6469739 : Blo 1008601 6469739 := bstep (se 1 (by rfl) ⟨4852304, by rfl⟩ : syracuseStep 6469739 = 9704609) B9704609
theorem B2275451 : Blo 1008601 2275451 := bstep (se 1 (by rfl) ⟨1706588, by rfl⟩ : syracuseStep 2275451 = 3413177) B3413177
theorem B2275721 : Blo 1008601 2275721 := bstep (se 2 (by rfl) ⟨853395, by rfl⟩ : syracuseStep 2275721 = 1706791) B1706791
theorem B8632979 : Blo 1008601 8632979 := bstep (se 1 (by rfl) ⟨6474734, by rfl⟩ : syracuseStep 8632979 = 12949469) B12949469
theorem B2276153 : Blo 1008601 2276153 := bstep (se 2 (by rfl) ⟨853557, by rfl⟩ : syracuseStep 2276153 = 1707115) B1707115
theorem B9714563 : Blo 1008601 9714563 := bstep (se 1 (by rfl) ⟨7285922, by rfl⟩ : syracuseStep 9714563 = 14571845) B14571845
theorem B2276513 : Blo 1008601 2276513 := bstep (se 2 (by rfl) ⟨853692, by rfl⟩ : syracuseStep 2276513 = 1707385) B1707385
theorem B2276783 : Blo 1008601 2276783 := bstep (se 1 (by rfl) ⟨1707587, by rfl⟩ : syracuseStep 2276783 = 3415175) B3415175
theorem B4308527 : Blo 1008601 4308527 := bstep (se 1 (by rfl) ⟨3231395, by rfl⟩ : syracuseStep 4308527 = 6462791) B6462791
theorem B2736091 : Blo 1008601 2736091 := bstep (se 1 (by rfl) ⟨2052068, by rfl⟩ : syracuseStep 2736091 = 4104137) B4104137
theorem B2277449 : Blo 1008601 2277449 := bstep (se 2 (by rfl) ⟨854043, by rfl⟩ : syracuseStep 2277449 = 1708087) B1708087
theorem B11518199 : Blo 1008601 11518199 := bstep (se 1 (by rfl) ⟨8638649, by rfl⟩ : syracuseStep 11518199 = 17277299) B17277299
theorem B1917407 : Blo 1008601 1917407 := bstep (se 1 (by rfl) ⟨1438055, by rfl⟩ : syracuseStep 1917407 = 2876111) B2876111
theorem B2277863 : Blo 1008601 2277863 := bstep (se 1 (by rfl) ⟨1708397, by rfl⟩ : syracuseStep 2277863 = 3416795) B3416795
theorem B2277881 : Blo 1008601 2277881 := bstep (se 2 (by rfl) ⟨854205, by rfl⟩ : syracuseStep 2277881 = 1708411) B1708411
theorem B6472223 : Blo 1008601 6472223 := bstep (se 1 (by rfl) ⟨4854167, by rfl⟩ : syracuseStep 6472223 = 9708335) B9708335
theorem B2277971 : Blo 1008601 2277971 := bstep (se 1 (by rfl) ⟨1708478, by rfl⟩ : syracuseStep 2277971 = 3416957) B3416957
theorem B2278151 : Blo 1008601 2278151 := bstep (se 1 (by rfl) ⟨1708613, by rfl⟩ : syracuseStep 2278151 = 3417227) B3417227
theorem B2278241 : Blo 1008601 2278241 := bstep (se 2 (by rfl) ⟨854340, by rfl⟩ : syracuseStep 2278241 = 1708681) B1708681
theorem B6145163 : Blo 1008601 6145163 := bstep (se 1 (by rfl) ⟨4608872, by rfl⟩ : syracuseStep 6145163 = 9217745) B9217745
theorem B13288691 : Blo 1008601 13288691 := bstep (se 1 (by rfl) ⟨9966518, by rfl⟩ : syracuseStep 13288691 = 19933037) B19933037
theorem B12928247 : Blo 1008601 12928247 := bstep (se 1 (by rfl) ⟨9696185, by rfl⟩ : syracuseStep 12928247 = 19392371) B19392371
theorem B3884995 : Blo 1008601 3884995 := bstep (se 1 (by rfl) ⟨2913746, by rfl⟩ : syracuseStep 3884995 = 5827493) B5827493
theorem B7686089 : Blo 1008601 7686089 := bstep (se 2 (by rfl) ⟨2882283, by rfl⟩ : syracuseStep 7686089 = 5764567) B5764567
theorem B6572177 : Blo 1008601 6572177 := bstep (se 2 (by rfl) ⟨2464566, by rfl⟩ : syracuseStep 6572177 = 4929133) B4929133
theorem B10931219 : Blo 1008601 10931219 := bstep (se 1 (by rfl) ⟨8198414, by rfl⟩ : syracuseStep 10931219 = 16396829) B16396829
theorem B1363721 : Blo 1008601 1363721 := bstep (se 2 (by rfl) ⟨511395, by rfl⟩ : syracuseStep 1363721 = 1022791) B1022791
theorem B1134895 : Blo 1008601 1134895 := bstep (se 1 (by rfl) ⟨851171, by rfl⟩ : syracuseStep 1134895 = 1702343) B1702343
theorem B1823023 : Blo 1008601 1823023 := bstep (se 1 (by rfl) ⟨1367267, by rfl⟩ : syracuseStep 1823023 = 2734535) B2734535
theorem B1135039 : Blo 1008601 1135039 := bstep (se 1 (by rfl) ⟨851279, by rfl⟩ : syracuseStep 1135039 = 1702559) B1702559
theorem B9720485 : Blo 1008601 9720485 := bstep (se 4 (by rfl) ⟨911295, by rfl⟩ : syracuseStep 9720485 = 1822591) B1822591
theorem B1136767 : Blo 1008601 1136767 := bstep (se 1 (by rfl) ⟨852575, by rfl⟩ : syracuseStep 1136767 = 1705151) B1705151
theorem B31119491 : Blo 1008601 31119491 := bstep (se 1 (by rfl) ⟨23339618, by rfl⟩ : syracuseStep 31119491 = 46679237) B46679237
theorem B2873627 : Blo 1008601 2873627 := bstep (se 1 (by rfl) ⟨2155220, by rfl⟩ : syracuseStep 2873627 = 4310441) B4310441
theorem B82860509 : Blo 1008601 82860509 := bstep (se 3 (by rfl) ⟨15536345, by rfl⟩ : syracuseStep 82860509 = 31072691) B31072691
theorem B1137343 : Blo 1008601 1137343 := bstep (se 1 (by rfl) ⟨853007, by rfl⟩ : syracuseStep 1137343 = 1706015) B1706015
theorem B18472121 : Blo 1008601 18472121 := bstep (se 2 (by rfl) ⟨6927045, by rfl⟩ : syracuseStep 18472121 = 13854091) B13854091
theorem B3235241 : Blo 1008601 3235241 := bstep (se 2 (by rfl) ⟨1213215, by rfl⟩ : syracuseStep 3235241 = 2426431) B2426431
theorem B7003579 : Blo 1008601 7003579 := bstep (se 1 (by rfl) ⟨5252684, by rfl⟩ : syracuseStep 7003579 = 10505369) B10505369
theorem B3792761 : Blo 1008601 3792761 := bstep (se 2 (by rfl) ⟨1422285, by rfl⟩ : syracuseStep 3792761 = 2844571) B2844571
theorem B2875495 : Blo 1008601 2875495 := bstep (se 1 (by rfl) ⟨2156621, by rfl⟩ : syracuseStep 2875495 = 4313243) B4313243
theorem B1008623 : Blo 1008601 1008623 := bstep (se 1 (by rfl) ⟨756467, by rfl⟩ : syracuseStep 1008623 = 1512935) B1512935
theorem B1008731 : Blo 1008601 1008731 := bstep (se 1 (by rfl) ⟨756548, by rfl⟩ : syracuseStep 1008731 = 1513097) B1513097
theorem B1008743 : Blo 1008601 1008743 := bstep (se 1 (by rfl) ⟨756557, by rfl⟩ : syracuseStep 1008743 = 1513115) B1513115
theorem B1008871 : Blo 1008601 1008871 := bstep (se 1 (by rfl) ⟨756653, by rfl⟩ : syracuseStep 1008871 = 1513307) B1513307
theorem B1009127 : Blo 1008601 1009127 := bstep (se 1 (by rfl) ⟨756845, by rfl⟩ : syracuseStep 1009127 = 1513691) B1513691
theorem B1009307 : Blo 1008601 1009307 := bstep (se 1 (by rfl) ⟨756980, by rfl⟩ : syracuseStep 1009307 = 1513961) B1513961
theorem B1009567 : Blo 1008601 1009567 := bstep (se 1 (by rfl) ⟨757175, by rfl⟩ : syracuseStep 1009567 = 1514351) B1514351
theorem B1009575 : Blo 1008601 1009575 := bstep (se 1 (by rfl) ⟨757181, by rfl⟩ : syracuseStep 1009575 = 1514363) B1514363
theorem B2156519 : Blo 1008601 2156519 := bstep (se 1 (by rfl) ⟨1617389, by rfl⟩ : syracuseStep 2156519 = 3234779) B3234779
theorem B44329193 : Blo 1008601 44329193 := bstep (se 2 (by rfl) ⟨16623447, by rfl⟩ : syracuseStep 44329193 = 33246895) B33246895
theorem B4319531 : Blo 1008601 4319531 := bstep (se 1 (by rfl) ⟨3239648, by rfl⟩ : syracuseStep 4319531 = 6479297) B6479297
theorem B1010151 : Blo 1008601 1010151 := bstep (se 1 (by rfl) ⟨757613, by rfl⟩ : syracuseStep 1010151 = 1515227) B1515227
theorem B3238393 : Blo 1008601 3238393 := bstep (se 2 (by rfl) ⟨1214397, by rfl⟩ : syracuseStep 3238393 = 2428795) B2428795
theorem B9726479 : Blo 1008601 9726479 := bstep (se 1 (by rfl) ⟨7294859, by rfl⟩ : syracuseStep 9726479 = 14589719) B14589719
theorem B12315239 : Blo 1008601 12315239 := bstep (se 1 (by rfl) ⟨9236429, by rfl⟩ : syracuseStep 12315239 = 18472859) B18472859
theorem B7793297 : Blo 1008601 7793297 := bstep (se 2 (by rfl) ⟨2922486, by rfl⟩ : syracuseStep 7793297 = 5844973) B5844973
theorem B1010331 : Blo 1008601 1010331 := bstep (se 1 (by rfl) ⟨757748, by rfl⟩ : syracuseStep 1010331 = 1515497) B1515497
theorem B3238663 : Blo 1008601 3238663 := bstep (se 1 (by rfl) ⟨2428997, by rfl⟩ : syracuseStep 3238663 = 4857995) B4857995
theorem B1010799 : Blo 1008601 1010799 := bstep (se 1 (by rfl) ⟨758099, by rfl⟩ : syracuseStep 1010799 = 1516199) B1516199
theorem B1010879 : Blo 1008601 1010879 := bstep (se 1 (by rfl) ⟨758159, by rfl⟩ : syracuseStep 1010879 = 1516319) B1516319
theorem B1010895 : Blo 1008601 1010895 := bstep (se 1 (by rfl) ⟨758171, by rfl⟩ : syracuseStep 1010895 = 1516343) B1516343
theorem B29125919 : Blo 1008601 29125919 := bstep (se 1 (by rfl) ⟨21844439, by rfl⟩ : syracuseStep 29125919 = 43688879) B43688879
theorem B1011015 : Blo 1008601 1011015 := bstep (se 1 (by rfl) ⟨758261, by rfl⟩ : syracuseStep 1011015 = 1516523) B1516523
theorem B1535707 : Blo 1008601 1535707 := bstep (se 1 (by rfl) ⟨1151780, by rfl⟩ : syracuseStep 1535707 = 2303561) B2303561
theorem B1437691 : Blo 1008601 1437691 := bstep (se 1 (by rfl) ⟨1078268, by rfl⟩ : syracuseStep 1437691 = 2156537) B2156537
theorem B1011743 : Blo 1008601 1011743 := bstep (se 1 (by rfl) ⟨758807, by rfl⟩ : syracuseStep 1011743 = 1517615) B1517615
theorem B1011919 : Blo 1008601 1011919 := bstep (se 1 (by rfl) ⟨758939, by rfl⟩ : syracuseStep 1011919 = 1517879) B1517879
theorem B3240263 : Blo 1008601 3240263 := bstep (se 1 (by rfl) ⟨2430197, by rfl⟩ : syracuseStep 3240263 = 4860395) B4860395
theorem B1012039 : Blo 1008601 1012039 := bstep (se 1 (by rfl) ⟨759029, by rfl⟩ : syracuseStep 1012039 = 1518059) B1518059
theorem B1536425 : Blo 1008601 1536425 := bstep (se 2 (by rfl) ⟨576159, by rfl⟩ : syracuseStep 1536425 = 1152319) B1152319
theorem B4321907 : Blo 1008601 4321907 := bstep (se 1 (by rfl) ⟨3241430, by rfl⟩ : syracuseStep 4321907 = 6482861) B6482861
theorem B1012507 : Blo 1008601 1012507 := bstep (se 1 (by rfl) ⟨759380, by rfl⟩ : syracuseStep 1012507 = 1518761) B1518761
theorem B3404699 : Blo 1008601 3404699 := bstep (se 1 (by rfl) ⟨2553524, by rfl⟩ : syracuseStep 3404699 = 5107049) B5107049
theorem B1438841 : Blo 1008601 1438841 := bstep (se 2 (by rfl) ⟨539565, by rfl⟩ : syracuseStep 1438841 = 1079131) B1079131
theorem B1078439 : Blo 1008601 1078439 := bstep (se 1 (by rfl) ⟨808829, by rfl⟩ : syracuseStep 1078439 = 1617659) B1617659
theorem B3241289 : Blo 1008601 3241289 := bstep (se 2 (by rfl) ⟨1215483, by rfl⟩ : syracuseStep 3241289 = 2430967) B2430967
theorem B6485345 : Blo 1008601 6485345 := bstep (se 2 (by rfl) ⟨2432004, by rfl⟩ : syracuseStep 6485345 = 4864009) B4864009
theorem B5764841 : Blo 1008601 5764841 := bstep (se 2 (by rfl) ⟨2161815, by rfl⟩ : syracuseStep 5764841 = 4323631) B4323631
theorem B2554031 : Blo 1008601 2554031 := bstep (se 1 (by rfl) ⟨1915523, by rfl⟩ : syracuseStep 2554031 = 3831047) B3831047
theorem B2881727 : Blo 1008601 2881727 := bstep (se 1 (by rfl) ⟨2161295, by rfl⟩ : syracuseStep 2881727 = 4322591) B4322591
theorem B4094441 : Blo 1008601 4094441 := bstep (se 2 (by rfl) ⟨1535415, by rfl⟩ : syracuseStep 4094441 = 3070831) B3070831
theorem B2554375 : Blo 1008601 2554375 := bstep (se 1 (by rfl) ⟨1915781, by rfl⟩ : syracuseStep 2554375 = 3831563) B3831563
theorem B66484799 : Blo 1008601 66484799 := bstep (se 1 (by rfl) ⟨49863599, by rfl⟩ : syracuseStep 66484799 = 99727199) B99727199
theorem B2554679 : Blo 1008601 2554679 := bstep (se 1 (by rfl) ⟨1916009, by rfl⟩ : syracuseStep 2554679 = 3832019) B3832019
theorem B5471063 : Blo 1008601 5471063 := bstep (se 1 (by rfl) ⟨4103297, by rfl⟩ : syracuseStep 5471063 = 8206595) B8206595
theorem B2882785 : Blo 1008601 2882785 := bstep (se 2 (by rfl) ⟨1081044, by rfl⟩ : syracuseStep 2882785 = 2162089) B2162089
theorem B3407183 : Blo 1008601 3407183 := bstep (se 1 (by rfl) ⟨2555387, by rfl⟩ : syracuseStep 3407183 = 5110775) B5110775
theorem B12975713 : Blo 1008601 12975713 := bstep (se 2 (by rfl) ⟨4865892, by rfl⟩ : syracuseStep 12975713 = 9731785) B9731785
theorem B17268551 : Blo 1008601 17268551 := bstep (se 1 (by rfl) ⟨12951413, by rfl⟩ : syracuseStep 17268551 = 25902827) B25902827
theorem B8617873 : Blo 1008601 8617873 := bstep (se 2 (by rfl) ⟨3231702, by rfl⟩ : syracuseStep 8617873 = 6463405) B6463405
theorem B3833993 : Blo 1008601 3833993 := bstep (se 2 (by rfl) ⟨1437747, by rfl⟩ : syracuseStep 3833993 = 2875495) B2875495
theorem B1278271 : Blo 1008601 1278271 := bstep (se 1 (by rfl) ⟨958703, by rfl⟩ : syracuseStep 1278271 = 1917407) B1917407
theorem B3408425 : Blo 1008601 3408425 := bstep (se 2 (by rfl) ⟨1278159, by rfl⟩ : syracuseStep 3408425 = 2556319) B2556319
theorem B4096775 : Blo 1008601 4096775 := bstep (se 1 (by rfl) ⟨3072581, by rfl⟩ : syracuseStep 4096775 = 6145163) B6145163
theorem B8618831 : Blo 1008601 8618831 := bstep (se 1 (by rfl) ⟨6464123, by rfl⟩ : syracuseStep 8618831 = 12928247) B12928247
theorem B6555439 : Blo 1008601 6555439 := bstep (se 1 (by rfl) ⟨4916579, by rfl⟩ : syracuseStep 6555439 = 9833159) B9833159
theorem B17237933 : Blo 1008601 17237933 := bstep (se 3 (by rfl) ⟨3232112, by rfl⟩ : syracuseStep 17237933 = 6464225) B6464225
theorem B3409883 : Blo 1008601 3409883 := bstep (se 1 (by rfl) ⟨2557412, by rfl⟩ : syracuseStep 3409883 = 5114825) B5114825
theorem B3409991 : Blo 1008601 3409991 := bstep (se 1 (by rfl) ⟨2557493, by rfl⟩ : syracuseStep 3409991 = 5114987) B5114987
theorem B5179993 : Blo 1008601 5179993 := bstep (se 2 (by rfl) ⟨1942497, by rfl⟩ : syracuseStep 5179993 = 3884995) B3884995
theorem B2558699 : Blo 1008601 2558699 := bstep (se 1 (by rfl) ⟨1919024, by rfl⟩ : syracuseStep 2558699 = 3838049) B3838049
theorem B3836909 : Blo 1008601 3836909 := bstep (se 3 (by rfl) ⟨719420, by rfl⟩ : syracuseStep 3836909 = 1438841) B1438841
theorem B2559671 : Blo 1008601 2559671 := bstep (se 1 (by rfl) ⟨1919753, by rfl⟩ : syracuseStep 2559671 = 3839507) B3839507
theorem B2559995 : Blo 1008601 2559995 := bstep (se 1 (by rfl) ⟨1919996, by rfl⟩ : syracuseStep 2559995 = 3839993) B3839993
theorem B20746327 : Blo 1008601 20746327 := bstep (se 1 (by rfl) ⟨15559745, by rfl⟩ : syracuseStep 20746327 = 31119491) B31119491
theorem B1708391 : Blo 1008601 1708391 := bstep (se 1 (by rfl) ⟨1281293, by rfl⟩ : syracuseStep 1708391 = 2562587) B2562587
theorem B8885257 : Blo 1008601 8885257 := bstep (se 2 (by rfl) ⟨3331971, by rfl⟩ : syracuseStep 8885257 = 6663943) B6663943
theorem B27628705 : Blo 1008601 27628705 := bstep (se 2 (by rfl) ⟨10360764, by rfl⟩ : syracuseStep 27628705 = 20721529) B20721529
theorem B2528507 : Blo 1008601 2528507 := bstep (se 1 (by rfl) ⟨1896380, by rfl⟩ : syracuseStep 2528507 = 3792761) B3792761
theorem B1513193 : Blo 1008601 1513193 := bstep (se 2 (by rfl) ⟨567447, by rfl⟩ : syracuseStep 1513193 = 1134895) B1134895
theorem B2430697 : Blo 1008601 2430697 := bstep (se 2 (by rfl) ⟨911511, by rfl⟩ : syracuseStep 2430697 = 1823023) B1823023
theorem B1513385 : Blo 1008601 1513385 := bstep (se 2 (by rfl) ⟨567519, by rfl⟩ : syracuseStep 1513385 = 1135039) B1135039
theorem B1513451 : Blo 1008601 1513451 := bstep (se 1 (by rfl) ⟨1135088, by rfl⟩ : syracuseStep 1513451 = 2270177) B2270177
theorem B1513967 : Blo 1008601 1513967 := bstep (se 1 (by rfl) ⟨1135475, by rfl⟩ : syracuseStep 1513967 = 2270951) B2270951
theorem B4856473 : Blo 1008601 4856473 := bstep (se 2 (by rfl) ⟨1821177, by rfl⟩ : syracuseStep 4856473 = 3642355) B3642355
theorem B1514279 : Blo 1008601 1514279 := bstep (se 1 (by rfl) ⟨1135709, by rfl⟩ : syracuseStep 1514279 = 2271419) B2271419
theorem B3414905 : Blo 1008601 3414905 := bstep (se 2 (by rfl) ⟨1280589, by rfl⟩ : syracuseStep 3414905 = 2561179) B2561179
theorem B14032019 : Blo 1008601 14032019 := bstep (se 1 (by rfl) ⟨10524014, by rfl⟩ : syracuseStep 14032019 = 21048029) B21048029
theorem B3415337 : Blo 1008601 3415337 := bstep (se 2 (by rfl) ⟨1280751, by rfl⟩ : syracuseStep 3415337 = 2561503) B2561503
theorem B1514879 : Blo 1008601 1514879 := bstep (se 1 (by rfl) ⟨1136159, by rfl⟩ : syracuseStep 1514879 = 2272319) B2272319
theorem B1515431 : Blo 1008601 1515431 := bstep (se 1 (by rfl) ⟨1136573, by rfl⟩ : syracuseStep 1515431 = 2273147) B2273147
theorem B1515689 : Blo 1008601 1515689 := bstep (se 2 (by rfl) ⟨568383, by rfl⟩ : syracuseStep 1515689 = 1136767) B1136767
theorem B1024283 : Blo 1008601 1024283 := bstep (se 1 (by rfl) ⟨768212, by rfl⟩ : syracuseStep 1024283 = 1536425) B1536425
theorem B2269799 : Blo 1008601 2269799 := bstep (se 1 (by rfl) ⟨1702349, by rfl⟩ : syracuseStep 2269799 = 3404699) B3404699
theorem B1516457 : Blo 1008601 1516457 := bstep (se 2 (by rfl) ⟨568671, by rfl⟩ : syracuseStep 1516457 = 1137343) B1137343
theorem B3843227 : Blo 1008601 3843227 := bstep (se 1 (by rfl) ⟨2882420, by rfl⟩ : syracuseStep 3843227 = 5764841) B5764841
theorem B1516727 : Blo 1008601 1516727 := bstep (se 1 (by rfl) ⟨1137545, by rfl⟩ : syracuseStep 1516727 = 2275091) B2275091
theorem B1516967 : Blo 1008601 1516967 := bstep (se 1 (by rfl) ⟨1137725, by rfl⟩ : syracuseStep 1516967 = 2275451) B2275451
theorem B1517147 : Blo 1008601 1517147 := bstep (se 1 (by rfl) ⟨1137860, by rfl⟩ : syracuseStep 1517147 = 2275721) B2275721
theorem B3843713 : Blo 1008601 3843713 := bstep (se 2 (by rfl) ⟨1441392, by rfl⟩ : syracuseStep 3843713 = 2882785) B2882785
theorem B2729627 : Blo 1008601 2729627 := bstep (se 1 (by rfl) ⟨2047220, by rfl⟩ : syracuseStep 2729627 = 4094441) B4094441
theorem B1517435 : Blo 1008601 1517435 := bstep (se 1 (by rfl) ⟨1138076, by rfl⟩ : syracuseStep 1517435 = 2276153) B2276153
theorem B3647375 : Blo 1008601 3647375 := bstep (se 1 (by rfl) ⟨2735531, by rfl⟩ : syracuseStep 3647375 = 5471063) B5471063
theorem B1517675 : Blo 1008601 1517675 := bstep (se 1 (by rfl) ⟨1138256, by rfl⟩ : syracuseStep 1517675 = 2276513) B2276513
theorem B2271455 : Blo 1008601 2271455 := bstep (se 1 (by rfl) ⟨1703591, by rfl⟩ : syracuseStep 2271455 = 3407183) B3407183
theorem B1517855 : Blo 1008601 1517855 := bstep (se 1 (by rfl) ⟨1138391, by rfl⟩ : syracuseStep 1517855 = 2276783) B2276783
theorem B11512367 : Blo 1008601 11512367 := bstep (se 1 (by rfl) ⟨8634275, by rfl⟩ : syracuseStep 11512367 = 17268551) B17268551
theorem B3648121 : Blo 1008601 3648121 := bstep (se 2 (by rfl) ⟨1368045, by rfl⟩ : syracuseStep 3648121 = 2736091) B2736091
theorem B13118105 : Blo 1008601 13118105 := bstep (se 2 (by rfl) ⟨4919289, by rfl⟩ : syracuseStep 13118105 = 9838579) B9838579
theorem B1518299 : Blo 1008601 1518299 := bstep (se 1 (by rfl) ⟨1138724, by rfl⟩ : syracuseStep 1518299 = 2277449) B2277449
theorem B7678799 : Blo 1008601 7678799 := bstep (se 1 (by rfl) ⟨5759099, by rfl⟩ : syracuseStep 7678799 = 11518199) B11518199
theorem B1518575 : Blo 1008601 1518575 := bstep (se 1 (by rfl) ⟨1138931, by rfl⟩ : syracuseStep 1518575 = 2277863) B2277863
theorem B1518587 : Blo 1008601 1518587 := bstep (se 1 (by rfl) ⟨1138940, by rfl⟩ : syracuseStep 1518587 = 2277881) B2277881
theorem B1518647 : Blo 1008601 1518647 := bstep (se 1 (by rfl) ⟨1138985, by rfl⟩ : syracuseStep 1518647 = 2277971) B2277971
theorem B8629355 : Blo 1008601 8629355 := bstep (se 1 (by rfl) ⟨6472016, by rfl⟩ : syracuseStep 8629355 = 12944033) B12944033
theorem B1518767 : Blo 1008601 1518767 := bstep (se 1 (by rfl) ⟨1139075, by rfl⟩ : syracuseStep 1518767 = 2278151) B2278151
theorem B2272463 : Blo 1008601 2272463 := bstep (se 1 (by rfl) ⟨1704347, by rfl⟩ : syracuseStep 2272463 = 3408695) B3408695
theorem B1518827 : Blo 1008601 1518827 := bstep (se 1 (by rfl) ⟨1139120, by rfl⟩ : syracuseStep 1518827 = 2278241) B2278241
theorem B8859127 : Blo 1008601 8859127 := bstep (se 1 (by rfl) ⟨6644345, by rfl⟩ : syracuseStep 8859127 = 13288691) B13288691
theorem B2273183 : Blo 1008601 2273183 := bstep (se 1 (by rfl) ⟨1704887, by rfl⟩ : syracuseStep 2273183 = 3409775) B3409775
theorem B5124059 : Blo 1008601 5124059 := bstep (se 1 (by rfl) ⟨3843044, by rfl⟩ : syracuseStep 5124059 = 7686089) B7686089
theorem B2273435 : Blo 1008601 2273435 := bstep (se 1 (by rfl) ⟨1705076, by rfl⟩ : syracuseStep 2273435 = 3410153) B3410153
theorem B31142141 : Blo 1008601 31142141 := bstep (se 3 (by rfl) ⟨5839151, by rfl⟩ : syracuseStep 31142141 = 11678303) B11678303
theorem B1618255 : Blo 1008601 1618255 := bstep (se 1 (by rfl) ⟨1213691, by rfl⟩ : syracuseStep 1618255 = 2427383) B2427383
theorem B2273633 : Blo 1008601 2273633 := bstep (se 2 (by rfl) ⟨852612, by rfl⟩ : syracuseStep 2273633 = 1705225) B1705225
theorem B5747071 : Blo 1008601 5747071 := bstep (se 1 (by rfl) ⟨4310303, by rfl⟩ : syracuseStep 5747071 = 8620607) B8620607
theorem B7287479 : Blo 1008601 7287479 := bstep (se 1 (by rfl) ⟨5465609, by rfl⟩ : syracuseStep 7287479 = 10931219) B10931219
theorem B11646119 : Blo 1008601 11646119 := bstep (se 1 (by rfl) ⟨8734589, by rfl⟩ : syracuseStep 11646119 = 17469179) B17469179
theorem B1915751 : Blo 1008601 1915751 := bstep (se 1 (by rfl) ⟨1436813, by rfl⟩ : syracuseStep 1915751 = 2873627) B2873627
theorem B2276729 : Blo 1008601 2276729 := bstep (se 2 (by rfl) ⟨853773, by rfl⟩ : syracuseStep 2276729 = 1707547) B1707547
theorem B2047609 : Blo 1008601 2047609 := bstep (se 2 (by rfl) ⟨767853, by rfl⟩ : syracuseStep 2047609 = 1535707) B1535707
theorem B1916921 : Blo 1008601 1916921 := bstep (se 2 (by rfl) ⟨718845, by rfl⟩ : syracuseStep 1916921 = 1437691) B1437691
theorem B20758799 : Blo 1008601 20758799 := bstep (se 1 (by rfl) ⟨15569099, by rfl⟩ : syracuseStep 20758799 = 31138199) B31138199
theorem B2277791 : Blo 1008601 2277791 := bstep (se 1 (by rfl) ⟨1708343, by rfl⟩ : syracuseStep 2277791 = 3416687) B3416687
theorem B7390939 : Blo 1008601 7390939 := bstep (se 1 (by rfl) ⟨5543204, by rfl⟩ : syracuseStep 7390939 = 11086409) B11086409
theorem B8210159 : Blo 1008601 8210159 := bstep (se 1 (by rfl) ⟨6157619, by rfl⟩ : syracuseStep 8210159 = 12315239) B12315239
theorem B5195531 : Blo 1008601 5195531 := bstep (se 1 (by rfl) ⟨3896648, by rfl⟩ : syracuseStep 5195531 = 7793297) B7793297
theorem B19417279 : Blo 1008601 19417279 := bstep (se 1 (by rfl) ⟨14562959, by rfl⟩ : syracuseStep 19417279 = 29125919) B29125919
theorem B6474887 : Blo 1008601 6474887 := bstep (se 1 (by rfl) ⟨4856165, by rfl⟩ : syracuseStep 6474887 = 9712331) B9712331
theorem B20762011 : Blo 1008601 20762011 := bstep (se 1 (by rfl) ⟨15571508, by rfl⟩ : syracuseStep 20762011 = 31143017) B31143017
theorem B59821841 : Blo 1008601 59821841 := bstep (se 2 (by rfl) ⟨22433190, by rfl⟩ : syracuseStep 59821841 = 44866381) B44866381
theorem B4313159 : Blo 1008601 4313159 := bstep (se 1 (by rfl) ⟨3234869, by rfl⟩ : syracuseStep 4313159 = 6469739) B6469739
theorem B1921151 : Blo 1008601 1921151 := bstep (se 1 (by rfl) ⟨1440863, by rfl⟩ : syracuseStep 1921151 = 2881727) B2881727
theorem B44323199 : Blo 1008601 44323199 := bstep (se 1 (by rfl) ⟨33242399, by rfl⟩ : syracuseStep 44323199 = 66484799) B66484799
theorem B5755319 : Blo 1008601 5755319 := bstep (se 1 (by rfl) ⟨4316489, by rfl⟩ : syracuseStep 5755319 = 8632979) B8632979
theorem B6476375 : Blo 1008601 6476375 := bstep (se 1 (by rfl) ⟨4857281, by rfl⟩ : syracuseStep 6476375 = 9714563) B9714563
theorem B2872351 : Blo 1008601 2872351 := bstep (se 1 (by rfl) ⟨2154263, by rfl⟩ : syracuseStep 2872351 = 4308527) B4308527
theorem B11490497 : Blo 1008601 11490497 := bstep (se 2 (by rfl) ⟨4308936, by rfl⟩ : syracuseStep 11490497 = 8617873) B8617873
theorem B3888815 : Blo 1008601 3888815 := bstep (se 1 (by rfl) ⟨2916611, by rfl⟩ : syracuseStep 3888815 = 5833223) B5833223
theorem B4314815 : Blo 1008601 4314815 := bstep (se 1 (by rfl) ⟨3236111, by rfl⟩ : syracuseStep 4314815 = 6472223) B6472223
theorem B7296911 : Blo 1008601 7296911 := bstep (se 1 (by rfl) ⟨5472683, by rfl⟩ : syracuseStep 7296911 = 10945367) B10945367
theorem B8181809 : Blo 1008601 8181809 := bstep (se 2 (by rfl) ⟨3068178, by rfl⟩ : syracuseStep 8181809 = 6136357) B6136357
theorem B8640701 : Blo 1008601 8640701 := bstep (se 3 (by rfl) ⟨1620131, by rfl⟩ : syracuseStep 8640701 = 3240263) B3240263
theorem B13818185 : Blo 1008601 13818185 := bstep (se 2 (by rfl) ⟨5181819, by rfl⟩ : syracuseStep 13818185 = 10363639) B10363639
theorem B36887021 : Blo 1008601 36887021 := bstep (se 3 (by rfl) ⟨6916316, by rfl⟩ : syracuseStep 36887021 = 13832633) B13832633
theorem B6478373 : Blo 1008601 6478373 := bstep (se 4 (by rfl) ⟨607347, by rfl⟩ : syracuseStep 6478373 = 1214695) B1214695
theorem B9231097 : Blo 1008601 9231097 := bstep (se 2 (by rfl) ⟨3461661, by rfl⟩ : syracuseStep 9231097 = 6923323) B6923323
theorem B4381451 : Blo 1008601 4381451 := bstep (se 1 (by rfl) ⟨3286088, by rfl⟩ : syracuseStep 4381451 = 6572177) B6572177
theorem B6905351 : Blo 1008601 6905351 := bstep (se 1 (by rfl) ⟨5179013, by rfl⟩ : syracuseStep 6905351 = 10358027) B10358027
theorem B1138495 : Blo 1008601 1138495 := bstep (se 1 (by rfl) ⟨853871, by rfl⟩ : syracuseStep 1138495 = 1707743) B1707743
theorem B3235895 : Blo 1008601 3235895 := bstep (se 1 (by rfl) ⟨2426921, by rfl⟩ : syracuseStep 3235895 = 4853843) B4853843
theorem B1138783 : Blo 1008601 1138783 := bstep (se 1 (by rfl) ⟨854087, by rfl⟩ : syracuseStep 1138783 = 1708175) B1708175
theorem B2875837 : Blo 1008601 2875837 := bstep (se 3 (by rfl) ⟨539219, by rfl⟩ : syracuseStep 2875837 = 1078439) B1078439
theorem B6480323 : Blo 1008601 6480323 := bstep (se 1 (by rfl) ⟨4860242, by rfl⟩ : syracuseStep 6480323 = 9720485) B9720485
theorem B4317857 : Blo 1008601 4317857 := bstep (se 2 (by rfl) ⟨1619196, by rfl⟩ : syracuseStep 4317857 = 3238393) B3238393
theorem B1008639 : Blo 1008601 1008639 := bstep (se 1 (by rfl) ⟨756479, by rfl⟩ : syracuseStep 1008639 = 1512959) B1512959
theorem B4318217 : Blo 1008601 4318217 := bstep (se 2 (by rfl) ⟨1619331, by rfl⟩ : syracuseStep 4318217 = 3238663) B3238663
theorem B1008711 : Blo 1008601 1008711 := bstep (se 1 (by rfl) ⟨756533, by rfl⟩ : syracuseStep 1008711 = 1513067) B1513067
theorem B1008891 : Blo 1008601 1008891 := bstep (se 1 (by rfl) ⟨756668, by rfl⟩ : syracuseStep 1008891 = 1513337) B1513337
theorem B1009055 : Blo 1008601 1009055 := bstep (se 1 (by rfl) ⟨756791, by rfl⟩ : syracuseStep 1009055 = 1513583) B1513583
theorem B4154807 : Blo 1008601 4154807 := bstep (se 1 (by rfl) ⟨3116105, by rfl⟩ : syracuseStep 4154807 = 6232211) B6232211
theorem B1009103 : Blo 1008601 1009103 := bstep (se 1 (by rfl) ⟨756827, by rfl⟩ : syracuseStep 1009103 = 1513655) B1513655
theorem B11494871 : Blo 1008601 11494871 := bstep (se 1 (by rfl) ⟨8621153, by rfl⟩ : syracuseStep 11494871 = 17242307) B17242307
theorem B55240339 : Blo 1008601 55240339 := bstep (se 1 (by rfl) ⟨41430254, by rfl⟩ : syracuseStep 55240339 = 82860509) B82860509
theorem B1009383 : Blo 1008601 1009383 := bstep (se 1 (by rfl) ⟨757037, by rfl⟩ : syracuseStep 1009383 = 1514075) B1514075
theorem B1009391 : Blo 1008601 1009391 := bstep (se 1 (by rfl) ⟨757043, by rfl⟩ : syracuseStep 1009391 = 1514087) B1514087
theorem B1009407 : Blo 1008601 1009407 := bstep (se 1 (by rfl) ⟨757055, by rfl⟩ : syracuseStep 1009407 = 1514111) B1514111
theorem B1009479 : Blo 1008601 1009479 := bstep (se 1 (by rfl) ⟨757109, by rfl⟩ : syracuseStep 1009479 = 1514219) B1514219
theorem B1009499 : Blo 1008601 1009499 := bstep (se 1 (by rfl) ⟨757124, by rfl⟩ : syracuseStep 1009499 = 1514249) B1514249
theorem B3237803 : Blo 1008601 3237803 := bstep (se 1 (by rfl) ⟨2428352, by rfl⟩ : syracuseStep 3237803 = 4856705) B4856705
theorem B1009659 : Blo 1008601 1009659 := bstep (se 1 (by rfl) ⟨757244, by rfl⟩ : syracuseStep 1009659 = 1514489) B1514489
theorem B12314747 : Blo 1008601 12314747 := bstep (se 1 (by rfl) ⟨9236060, by rfl⟩ : syracuseStep 12314747 = 18472121) B18472121
theorem B2156827 : Blo 1008601 2156827 := bstep (se 1 (by rfl) ⟨1617620, by rfl⟩ : syracuseStep 2156827 = 3235241) B3235241
theorem B5106077 : Blo 1008601 5106077 := bstep (se 3 (by rfl) ⟨957389, by rfl⟩ : syracuseStep 5106077 = 1914779) B1914779
theorem B1010079 : Blo 1008601 1010079 := bstep (se 1 (by rfl) ⟨757559, by rfl⟩ : syracuseStep 1010079 = 1515119) B1515119
theorem B1010159 : Blo 1008601 1010159 := bstep (se 1 (by rfl) ⟨757619, by rfl⟩ : syracuseStep 1010159 = 1515239) B1515239
theorem B1010343 : Blo 1008601 1010343 := bstep (se 1 (by rfl) ⟨757757, by rfl⟩ : syracuseStep 1010343 = 1515515) B1515515
theorem B1010383 : Blo 1008601 1010383 := bstep (se 1 (by rfl) ⟨757787, by rfl⟩ : syracuseStep 1010383 = 1515575) B1515575
theorem B1010463 : Blo 1008601 1010463 := bstep (se 1 (by rfl) ⟨757847, by rfl⟩ : syracuseStep 1010463 = 1515695) B1515695
theorem B1010599 : Blo 1008601 1010599 := bstep (se 1 (by rfl) ⟨757949, by rfl⟩ : syracuseStep 1010599 = 1515899) B1515899
theorem B2845655 : Blo 1008601 2845655 := bstep (se 1 (by rfl) ⟨2134241, by rfl⟩ : syracuseStep 2845655 = 4268483) B4268483
theorem B1010715 : Blo 1008601 1010715 := bstep (se 1 (by rfl) ⟨758036, by rfl⟩ : syracuseStep 1010715 = 1516073) B1516073
theorem B1010779 : Blo 1008601 1010779 := bstep (se 1 (by rfl) ⟨758084, by rfl⟩ : syracuseStep 1010779 = 1516169) B1516169
theorem B1010919 : Blo 1008601 1010919 := bstep (se 1 (by rfl) ⟨758189, by rfl⟩ : syracuseStep 1010919 = 1516379) B1516379
theorem B1010943 : Blo 1008601 1010943 := bstep (se 1 (by rfl) ⟨758207, by rfl⟩ : syracuseStep 1010943 = 1516415) B1516415
theorem B1010991 : Blo 1008601 1010991 := bstep (se 1 (by rfl) ⟨758243, by rfl⟩ : syracuseStep 1010991 = 1516487) B1516487
theorem B1011135 : Blo 1008601 1011135 := bstep (se 1 (by rfl) ⟨758351, by rfl⟩ : syracuseStep 1011135 = 1516703) B1516703
theorem B1011231 : Blo 1008601 1011231 := bstep (se 1 (by rfl) ⟨758423, by rfl⟩ : syracuseStep 1011231 = 1516847) B1516847
theorem B1011359 : Blo 1008601 1011359 := bstep (se 1 (by rfl) ⟨758519, by rfl⟩ : syracuseStep 1011359 = 1517039) B1517039
theorem B1011367 : Blo 1008601 1011367 := bstep (se 1 (by rfl) ⟨758525, by rfl⟩ : syracuseStep 1011367 = 1517051) B1517051
theorem B1011391 : Blo 1008601 1011391 := bstep (se 1 (by rfl) ⟨758543, by rfl⟩ : syracuseStep 1011391 = 1517087) B1517087
theorem B1011487 : Blo 1008601 1011487 := bstep (se 1 (by rfl) ⟨758615, by rfl⟩ : syracuseStep 1011487 = 1517231) B1517231
theorem B1011547 : Blo 1008601 1011547 := bstep (se 1 (by rfl) ⟨758660, by rfl⟩ : syracuseStep 1011547 = 1517321) B1517321
theorem B1011567 : Blo 1008601 1011567 := bstep (se 1 (by rfl) ⟨758675, by rfl⟩ : syracuseStep 1011567 = 1517351) B1517351
theorem B1437679 : Blo 1008601 1437679 := bstep (se 1 (by rfl) ⟨1078259, by rfl⟩ : syracuseStep 1437679 = 2156519) B2156519
theorem B29552795 : Blo 1008601 29552795 := bstep (se 1 (by rfl) ⟨22164596, by rfl⟩ : syracuseStep 29552795 = 44329193) B44329193
theorem B2879687 : Blo 1008601 2879687 := bstep (se 1 (by rfl) ⟨2159765, by rfl⟩ : syracuseStep 2879687 = 4319531) B4319531
theorem B1011967 : Blo 1008601 1011967 := bstep (se 1 (by rfl) ⟨758975, by rfl⟩ : syracuseStep 1011967 = 1517951) B1517951
theorem B6484319 : Blo 1008601 6484319 := bstep (se 1 (by rfl) ⟨4863239, by rfl⟩ : syracuseStep 6484319 = 9726479) B9726479
theorem B1012127 : Blo 1008601 1012127 := bstep (se 1 (by rfl) ⟨759095, by rfl⟩ : syracuseStep 1012127 = 1518191) B1518191
theorem B8188361 : Blo 1008601 8188361 := bstep (se 2 (by rfl) ⟨3070635, by rfl⟩ : syracuseStep 8188361 = 6141271) B6141271
theorem B1012271 : Blo 1008601 1012271 := bstep (se 1 (by rfl) ⟨759203, by rfl⟩ : syracuseStep 1012271 = 1518407) B1518407
theorem B3241225 : Blo 1008601 3241225 := bstep (se 2 (by rfl) ⟨1215459, by rfl⟩ : syracuseStep 3241225 = 2430919) B2430919
theorem B6911399 : Blo 1008601 6911399 := bstep (se 1 (by rfl) ⟨5183549, by rfl⟩ : syracuseStep 6911399 = 10367099) B10367099
theorem B2881271 : Blo 1008601 2881271 := bstep (se 1 (by rfl) ⟨2160953, by rfl⟩ : syracuseStep 2881271 = 4321907) B4321907
theorem B3405833 : Blo 1008601 3405833 := bstep (se 2 (by rfl) ⟨1277187, by rfl⟩ : syracuseStep 3405833 = 2554375) B2554375
theorem B38893607 : Blo 1008601 38893607 := bstep (se 1 (by rfl) ⟨29170205, by rfl⟩ : syracuseStep 38893607 = 58340411) B58340411
theorem B2160859 : Blo 1008601 2160859 := bstep (se 1 (by rfl) ⟨1620644, by rfl⟩ : syracuseStep 2160859 = 3241289) B3241289
theorem B4323563 : Blo 1008601 4323563 := bstep (se 1 (by rfl) ⟨3242672, by rfl⟩ : syracuseStep 4323563 = 6485345) B6485345
theorem B9730783 : Blo 1008601 9730783 := bstep (se 1 (by rfl) ⟨7298087, by rfl⟩ : syracuseStep 9730783 = 14596175) B14596175
theorem B1702687 : Blo 1008601 1702687 := bstep (se 1 (by rfl) ⟨1277015, by rfl⟩ : syracuseStep 1702687 = 2554031) B2554031
theorem B1703119 : Blo 1008601 1703119 := bstep (se 1 (by rfl) ⟨1277339, by rfl⟩ : syracuseStep 1703119 = 2554679) B2554679
theorem B9338105 : Blo 1008601 9338105 := bstep (se 2 (by rfl) ⟨3501789, by rfl⟩ : syracuseStep 9338105 = 7003579) B7003579
theorem B3636589 : Blo 1008601 3636589 := bstep (se 3 (by rfl) ⟨681860, by rfl⟩ : syracuseStep 3636589 = 1363721) B1363721
theorem B8650475 : Blo 1008601 8650475 := bstep (se 1 (by rfl) ⟨6487856, by rfl⟩ : syracuseStep 8650475 = 12975713) B12975713
theorem B2555995 : Blo 1008601 2555995 := bstep (se 1 (by rfl) ⟨1916996, by rfl⟩ : syracuseStep 2555995 = 3833993) B3833993
theorem B1704361 : Blo 1008601 1704361 := bstep (se 2 (by rfl) ⟨639135, by rfl⟩ : syracuseStep 1704361 = 1278271) B1278271
theorem B3834449 : Blo 1008601 3834449 := bstep (se 2 (by rfl) ⟨1437918, by rfl⟩ : syracuseStep 3834449 = 2875837) B2875837
theorem B5473439 : Blo 1008601 5473439 := bstep (se 1 (by rfl) ⟨4105079, by rfl⟩ : syracuseStep 5473439 = 8210159) B8210159
theorem B1705799 : Blo 1008601 1705799 := bstep (se 1 (by rfl) ⟨1279349, by rfl⟩ : syracuseStep 1705799 = 2558699) B2558699
theorem B2557939 : Blo 1008601 2557939 := bstep (se 1 (by rfl) ⟨1918454, by rfl⟩ : syracuseStep 2557939 = 3836909) B3836909
theorem B1706447 : Blo 1008601 1706447 := bstep (se 1 (by rfl) ⟨1279835, by rfl⟩ : syracuseStep 1706447 = 2559671) B2559671
theorem B39881227 : Blo 1008601 39881227 := bstep (se 1 (by rfl) ⟨29910920, by rfl⟩ : syracuseStep 39881227 = 59821841) B59821841
theorem B1706663 : Blo 1008601 1706663 := bstep (se 1 (by rfl) ⟨1279997, by rfl⟩ : syracuseStep 1706663 = 2559995) B2559995
theorem B1280767 : Blo 1008601 1280767 := bstep (se 1 (by rfl) ⟨960575, by rfl⟩ : syracuseStep 1280767 = 1921151) B1921151
theorem B25889705 : Blo 1008601 25889705 := bstep (se 2 (by rfl) ⟨9708639, by rfl⟩ : syracuseStep 25889705 = 19417279) B19417279
theorem B3836879 : Blo 1008601 3836879 := bstep (se 1 (by rfl) ⟨2877659, by rfl⟩ : syracuseStep 3836879 = 5755319) B5755319
theorem B27626629 : Blo 1008601 27626629 := bstep (se 4 (by rfl) ⟨2589996, by rfl⟩ : syracuseStep 27626629 = 5179993) B5179993
theorem B9212123 : Blo 1008601 9212123 := bstep (se 1 (by rfl) ⟨6909092, by rfl⟩ : syracuseStep 9212123 = 13818185) B13818185
theorem B2920967 : Blo 1008601 2920967 := bstep (se 1 (by rfl) ⟨2190725, by rfl⟩ : syracuseStep 2920967 = 4381451) B4381451
theorem B47388037 : Blo 1008601 47388037 := bstep (se 4 (by rfl) ⟨4442628, by rfl⟩ : syracuseStep 47388037 = 8885257) B8885257
theorem B27661769 : Blo 1008601 27661769 := bstep (se 2 (by rfl) ⟨10373163, by rfl⟩ : syracuseStep 27661769 = 20746327) B20746327
theorem B1513199 : Blo 1008601 1513199 := bstep (se 1 (by rfl) ⟨1134899, by rfl⟩ : syracuseStep 1513199 = 2269799) B2269799
theorem B2562151 : Blo 1008601 2562151 := bstep (se 1 (by rfl) ⟨1921613, by rfl⟩ : syracuseStep 2562151 = 3843227) B3843227
theorem B2562475 : Blo 1008601 2562475 := bstep (se 1 (by rfl) ⟨1921856, by rfl⟩ : syracuseStep 2562475 = 3843713) B3843713
theorem B2431583 : Blo 1008601 2431583 := bstep (se 1 (by rfl) ⟨1823687, by rfl⟩ : syracuseStep 2431583 = 3647375) B3647375
theorem B1514303 : Blo 1008601 1514303 := bstep (se 1 (by rfl) ⟨1135727, by rfl⟩ : syracuseStep 1514303 = 2271455) B2271455
theorem B36838273 : Blo 1008601 36838273 := bstep (se 2 (by rfl) ⟨13814352, by rfl⟩ : syracuseStep 36838273 = 27628705) B27628705
theorem B7674911 : Blo 1008601 7674911 := bstep (se 1 (by rfl) ⟨5756183, by rfl⟩ : syracuseStep 7674911 = 11512367) B11512367
theorem B5119199 : Blo 1008601 5119199 := bstep (se 1 (by rfl) ⟨3839399, by rfl⟩ : syracuseStep 5119199 = 7678799) B7678799
theorem B1514975 : Blo 1008601 1514975 := bstep (se 1 (by rfl) ⟨1136231, by rfl⟩ : syracuseStep 1514975 = 2272463) B2272463
theorem B1515455 : Blo 1008601 1515455 := bstep (se 1 (by rfl) ⟨1136591, by rfl⟩ : syracuseStep 1515455 = 2273183) B2273183
theorem B3416039 : Blo 1008601 3416039 := bstep (se 1 (by rfl) ⟨2562029, by rfl⟩ : syracuseStep 3416039 = 5124059) B5124059
theorem B1515623 : Blo 1008601 1515623 := bstep (se 1 (by rfl) ⟨1136717, by rfl⟩ : syracuseStep 1515623 = 2273435) B2273435
theorem B19701863 : Blo 1008601 19701863 := bstep (se 1 (by rfl) ⟨14776397, by rfl⟩ : syracuseStep 19701863 = 29552795) B29552795
theorem B1515755 : Blo 1008601 1515755 := bstep (se 1 (by rfl) ⟨1136816, by rfl⟩ : syracuseStep 1515755 = 2273633) B2273633
theorem B4858319 : Blo 1008601 4858319 := bstep (se 1 (by rfl) ⟨3643739, by rfl⟩ : syracuseStep 4858319 = 7287479) B7287479
theorem B10920581 : Blo 1008601 10920581 := bstep (se 4 (by rfl) ⟨1023804, by rfl⟩ : syracuseStep 10920581 = 2047609) B2047609
theorem B2270249 : Blo 1008601 2270249 := bstep (se 2 (by rfl) ⟨851343, by rfl⟩ : syracuseStep 2270249 = 1702687) B1702687
theorem B2270555 : Blo 1008601 2270555 := bstep (se 1 (by rfl) ⟨1702916, by rfl⟩ : syracuseStep 2270555 = 3405833) B3405833
theorem B25929071 : Blo 1008601 25929071 := bstep (se 1 (by rfl) ⟨19446803, by rfl⟩ : syracuseStep 25929071 = 38893607) B38893607
theorem B2270825 : Blo 1008601 2270825 := bstep (se 2 (by rfl) ⟨851559, by rfl⟩ : syracuseStep 2270825 = 1703119) B1703119
theorem B1517819 : Blo 1008601 1517819 := bstep (se 1 (by rfl) ⟨1138364, by rfl⟩ : syracuseStep 1517819 = 2276729) B2276729
theorem B1517993 : Blo 1008601 1517993 := bstep (se 2 (by rfl) ⟨569247, by rfl⟩ : syracuseStep 1517993 = 1138495) B1138495
theorem B1518377 : Blo 1008601 1518377 := bstep (se 2 (by rfl) ⟨569391, by rfl⟩ : syracuseStep 1518377 = 1138783) B1138783
theorem B1518527 : Blo 1008601 1518527 := bstep (se 1 (by rfl) ⟨1138895, by rfl⟩ : syracuseStep 1518527 = 2277791) B2277791
theorem B2272283 : Blo 1008601 2272283 := bstep (se 1 (by rfl) ⟨1704212, by rfl⟩ : syracuseStep 2272283 = 3408425) B3408425
theorem B5745887 : Blo 1008601 5745887 := bstep (se 1 (by rfl) ⟨4309415, by rfl⟩ : syracuseStep 5745887 = 8618831) B8618831
theorem B55356797 : Blo 1008601 55356797 := bstep (se 3 (by rfl) ⟨10379399, by rfl⟩ : syracuseStep 55356797 = 20758799) B20758799
theorem B2731421 : Blo 1008601 2731421 := bstep (se 3 (by rfl) ⟨512141, by rfl⟩ : syracuseStep 2731421 = 1024283) B1024283
theorem B2273255 : Blo 1008601 2273255 := bstep (se 1 (by rfl) ⟨1704941, by rfl⟩ : syracuseStep 2273255 = 3409883) B3409883
theorem B2273327 : Blo 1008601 2273327 := bstep (se 1 (by rfl) ⟨1704995, by rfl⟩ : syracuseStep 2273327 = 3409991) B3409991
theorem B10924733 : Blo 1008601 10924733 := bstep (se 3 (by rfl) ⟨2048387, by rfl⟩ : syracuseStep 10924733 = 4096775) B4096775
theorem B4864607 : Blo 1008601 4864607 := bstep (se 1 (by rfl) ⟨3648455, by rfl⟩ : syracuseStep 4864607 = 7296911) B7296911
theorem B5454539 : Blo 1008601 5454539 := bstep (se 1 (by rfl) ⟨4090904, by rfl⟩ : syracuseStep 5454539 = 8181809) B8181809
theorem B24591347 : Blo 1008601 24591347 := bstep (se 1 (by rfl) ⟨18443510, by rfl⟩ : syracuseStep 24591347 = 36887021) B36887021
theorem B2276603 : Blo 1008601 2276603 := bstep (se 1 (by rfl) ⟨1707452, by rfl⟩ : syracuseStep 2276603 = 3414905) B3414905
theorem B11812169 : Blo 1008601 11812169 := bstep (se 2 (by rfl) ⟨4429563, by rfl⟩ : syracuseStep 11812169 = 8859127) B8859127
theorem B9354679 : Blo 1008601 9354679 := bstep (se 1 (by rfl) ⟨7016009, by rfl⟩ : syracuseStep 9354679 = 14032019) B14032019
theorem B2276891 : Blo 1008601 2276891 := bstep (se 1 (by rfl) ⟨1707668, by rfl⟩ : syracuseStep 2276891 = 3415337) B3415337
theorem B4603567 : Blo 1008601 4603567 := bstep (se 1 (by rfl) ⟨3452675, by rfl⟩ : syracuseStep 4603567 = 6905351) B6905351
theorem B2769871 : Blo 1008601 2769871 := bstep (se 1 (by rfl) ⟨2077403, by rfl⟩ : syracuseStep 2769871 = 4154807) B4154807
theorem B1819751 : Blo 1008601 1819751 := bstep (se 1 (by rfl) ⟨1364813, by rfl⟩ : syracuseStep 1819751 = 2729627) B2729627
theorem B8209831 : Blo 1008601 8209831 := bstep (se 1 (by rfl) ⟨6157373, by rfl⟩ : syracuseStep 8209831 = 12314747) B12314747
theorem B5752903 : Blo 1008601 5752903 := bstep (se 1 (by rfl) ⟨4314677, by rfl⟩ : syracuseStep 5752903 = 8629355) B8629355
theorem B1919791 : Blo 1008601 1919791 := bstep (se 1 (by rfl) ⟨1439843, by rfl⟩ : syracuseStep 1919791 = 2879687) B2879687
theorem B20761427 : Blo 1008601 20761427 := bstep (se 1 (by rfl) ⟨15571070, by rfl⟩ : syracuseStep 20761427 = 31142141) B31142141
theorem B5458907 : Blo 1008601 5458907 := bstep (se 1 (by rfl) ⟨4094180, by rfl⟩ : syracuseStep 5458907 = 8188361) B8188361
theorem B6475297 : Blo 1008601 6475297 := bstep (se 2 (by rfl) ⟨2428236, by rfl⟩ : syracuseStep 6475297 = 4856473) B4856473
theorem B4607599 : Blo 1008601 4607599 := bstep (se 1 (by rfl) ⟨3455699, by rfl⟩ : syracuseStep 4607599 = 6911399) B6911399
theorem B12308129 : Blo 1008601 12308129 := bstep (se 2 (by rfl) ⟨4615548, by rfl⟩ : syracuseStep 12308129 = 9231097) B9231097
theorem B1920847 : Blo 1008601 1920847 := bstep (se 1 (by rfl) ⟨1440635, by rfl⟩ : syracuseStep 1920847 = 2881271) B2881271
theorem B3463687 : Blo 1008601 3463687 := bstep (se 1 (by rfl) ⟨2597765, by rfl⟩ : syracuseStep 3463687 = 5195531) B5195531
theorem B11491955 : Blo 1008601 11491955 := bstep (se 1 (by rfl) ⟨8618966, by rfl⟩ : syracuseStep 11491955 = 17237933) B17237933
theorem B4316591 : Blo 1008601 4316591 := bstep (se 1 (by rfl) ⟨3237443, by rfl⟩ : syracuseStep 4316591 = 6474887) B6474887
theorem B73653785 : Blo 1008601 73653785 := bstep (se 2 (by rfl) ⟨27620169, by rfl⟩ : syracuseStep 73653785 = 55240339) B55240339
theorem B9854585 : Blo 1008601 9854585 := bstep (se 2 (by rfl) ⟨3695469, by rfl⟩ : syracuseStep 9854585 = 7390939) B7390939
theorem B8740585 : Blo 1008601 8740585 := bstep (se 2 (by rfl) ⟨3277719, by rfl⟩ : syracuseStep 8740585 = 6555439) B6555439
theorem B2875439 : Blo 1008601 2875439 := bstep (se 1 (by rfl) ⟨2156579, by rfl⟩ : syracuseStep 2875439 = 4313159) B4313159
theorem B1138927 : Blo 1008601 1138927 := bstep (se 1 (by rfl) ⟨854195, by rfl⟩ : syracuseStep 1138927 = 1708391) B1708391
theorem B29548799 : Blo 1008601 29548799 := bstep (se 1 (by rfl) ⟨22161599, by rfl⟩ : syracuseStep 29548799 = 44323199) B44323199
theorem B2875769 : Blo 1008601 2875769 := bstep (se 2 (by rfl) ⟨1078413, by rfl⟩ : syracuseStep 2875769 = 2156827) B2156827
theorem B4317583 : Blo 1008601 4317583 := bstep (se 1 (by rfl) ⟨3238187, by rfl⟩ : syracuseStep 4317583 = 6476375) B6476375
theorem B31056317 : Blo 1008601 31056317 := bstep (se 3 (by rfl) ⟨5823059, by rfl⟩ : syracuseStep 31056317 = 11646119) B11646119
theorem B19456645 : Blo 1008601 19456645 := bstep (se 4 (by rfl) ⟨1824060, by rfl⟩ : syracuseStep 19456645 = 3648121) B3648121
theorem B6742685 : Blo 1008601 6742685 := bstep (se 3 (by rfl) ⟨1264253, by rfl⟩ : syracuseStep 6742685 = 2528507) B2528507
theorem B7660331 : Blo 1008601 7660331 := bstep (se 1 (by rfl) ⟨5745248, by rfl⟩ : syracuseStep 7660331 = 11490497) B11490497
theorem B2876543 : Blo 1008601 2876543 := bstep (se 1 (by rfl) ⟨2157407, by rfl⟩ : syracuseStep 2876543 = 4314815) B4314815
theorem B1008795 : Blo 1008601 1008795 := bstep (se 1 (by rfl) ⟨756596, by rfl⟩ : syracuseStep 1008795 = 1513193) B1513193
theorem B1008923 : Blo 1008601 1008923 := bstep (se 1 (by rfl) ⟨756692, by rfl⟩ : syracuseStep 1008923 = 1513385) B1513385
theorem B1008967 : Blo 1008601 1008967 := bstep (se 1 (by rfl) ⟨756725, by rfl⟩ : syracuseStep 1008967 = 1513451) B1513451
theorem B5760467 : Blo 1008601 5760467 := bstep (se 1 (by rfl) ⟨4320350, by rfl⟩ : syracuseStep 5760467 = 8640701) B8640701
theorem B1009311 : Blo 1008601 1009311 := bstep (se 1 (by rfl) ⟨756983, by rfl⟩ : syracuseStep 1009311 = 1513967) B1513967
theorem B4318915 : Blo 1008601 4318915 := bstep (se 1 (by rfl) ⟨3239186, by rfl⟩ : syracuseStep 4318915 = 6478373) B6478373
theorem B1009519 : Blo 1008601 1009519 := bstep (se 1 (by rfl) ⟨757139, by rfl⟩ : syracuseStep 1009519 = 1514279) B1514279
theorem B27682681 : Blo 1008601 27682681 := bstep (se 2 (by rfl) ⟨10381005, by rfl⟩ : syracuseStep 27682681 = 20762011) B20762011
theorem B1009919 : Blo 1008601 1009919 := bstep (se 1 (by rfl) ⟨757439, by rfl⟩ : syracuseStep 1009919 = 1514879) B1514879
theorem B1010287 : Blo 1008601 1010287 := bstep (se 1 (by rfl) ⟨757715, by rfl⟩ : syracuseStep 1010287 = 1515431) B1515431
theorem B2157263 : Blo 1008601 2157263 := bstep (se 1 (by rfl) ⟨1617947, by rfl⟩ : syracuseStep 2157263 = 3235895) B3235895
theorem B1010459 : Blo 1008601 1010459 := bstep (se 1 (by rfl) ⟨757844, by rfl⟩ : syracuseStep 1010459 = 1515689) B1515689
theorem B4320215 : Blo 1008601 4320215 := bstep (se 1 (by rfl) ⟨3240161, by rfl⟩ : syracuseStep 4320215 = 6480323) B6480323
theorem B2157673 : Blo 1008601 2157673 := bstep (se 2 (by rfl) ⟨809127, by rfl⟩ : syracuseStep 2157673 = 1618255) B1618255
theorem B2878571 : Blo 1008601 2878571 := bstep (se 1 (by rfl) ⟨2158928, by rfl⟩ : syracuseStep 2878571 = 4317857) B4317857
theorem B7662761 : Blo 1008601 7662761 := bstep (se 2 (by rfl) ⟨2873535, by rfl⟩ : syracuseStep 7662761 = 5747071) B5747071
theorem B1010971 : Blo 1008601 1010971 := bstep (se 1 (by rfl) ⟨758228, by rfl⟩ : syracuseStep 1010971 = 1516457) B1516457
theorem B2878811 : Blo 1008601 2878811 := bstep (se 1 (by rfl) ⟨2159108, by rfl⟩ : syracuseStep 2878811 = 4318217) B4318217
theorem B1011151 : Blo 1008601 1011151 := bstep (se 1 (by rfl) ⟨758363, by rfl⟩ : syracuseStep 1011151 = 1516727) B1516727
theorem B1011311 : Blo 1008601 1011311 := bstep (se 1 (by rfl) ⟨758483, by rfl⟩ : syracuseStep 1011311 = 1516967) B1516967
theorem B7663247 : Blo 1008601 7663247 := bstep (se 1 (by rfl) ⟨5747435, by rfl⟩ : syracuseStep 7663247 = 11494871) B11494871
theorem B1011431 : Blo 1008601 1011431 := bstep (se 1 (by rfl) ⟨758573, by rfl⟩ : syracuseStep 1011431 = 1517147) B1517147
theorem B1011623 : Blo 1008601 1011623 := bstep (se 1 (by rfl) ⟨758717, by rfl⟩ : syracuseStep 1011623 = 1517435) B1517435
theorem B2158535 : Blo 1008601 2158535 := bstep (se 1 (by rfl) ⟨1618901, by rfl⟩ : syracuseStep 2158535 = 3237803) B3237803
theorem B3829801 : Blo 1008601 3829801 := bstep (se 2 (by rfl) ⟨1436175, by rfl⟩ : syracuseStep 3829801 = 2872351) B2872351
theorem B1011783 : Blo 1008601 1011783 := bstep (se 1 (by rfl) ⟨758837, by rfl⟩ : syracuseStep 1011783 = 1517675) B1517675
theorem B1011903 : Blo 1008601 1011903 := bstep (se 1 (by rfl) ⟨758927, by rfl⟩ : syracuseStep 1011903 = 1517855) B1517855
theorem B3404051 : Blo 1008601 3404051 := bstep (se 1 (by rfl) ⟨2553038, by rfl⟩ : syracuseStep 3404051 = 5106077) B5106077
theorem B4321633 : Blo 1008601 4321633 := bstep (se 2 (by rfl) ⟨1620612, by rfl⟩ : syracuseStep 4321633 = 3241225) B3241225
theorem B8745403 : Blo 1008601 8745403 := bstep (se 1 (by rfl) ⟨6559052, by rfl⟩ : syracuseStep 8745403 = 13118105) B13118105
theorem B1012199 : Blo 1008601 1012199 := bstep (se 1 (by rfl) ⟨759149, by rfl⟩ : syracuseStep 1012199 = 1518299) B1518299
theorem B41480693 : Blo 1008601 41480693 := bstep (se 5 (by rfl) ⟨1944407, by rfl⟩ : syracuseStep 41480693 = 3888815) B3888815
theorem B1897103 : Blo 1008601 1897103 := bstep (se 1 (by rfl) ⟨1422827, by rfl⟩ : syracuseStep 1897103 = 2845655) B2845655
theorem B1012383 : Blo 1008601 1012383 := bstep (se 1 (by rfl) ⟨759287, by rfl⟩ : syracuseStep 1012383 = 1518575) B1518575
theorem B1012391 : Blo 1008601 1012391 := bstep (se 1 (by rfl) ⟨759293, by rfl⟩ : syracuseStep 1012391 = 1518587) B1518587
theorem B1012431 : Blo 1008601 1012431 := bstep (se 1 (by rfl) ⟨759323, by rfl⟩ : syracuseStep 1012431 = 1518647) B1518647
theorem B1012511 : Blo 1008601 1012511 := bstep (se 1 (by rfl) ⟨759383, by rfl⟩ : syracuseStep 1012511 = 1518767) B1518767
theorem B1012551 : Blo 1008601 1012551 := bstep (se 1 (by rfl) ⟨759413, by rfl⟩ : syracuseStep 1012551 = 1518827) B1518827
theorem B5108669 : Blo 1008601 5108669 := bstep (se 3 (by rfl) ⟨957875, by rfl⟩ : syracuseStep 5108669 = 1915751) B1915751
theorem B3240929 : Blo 1008601 3240929 := bstep (se 2 (by rfl) ⟨1215348, by rfl⟩ : syracuseStep 3240929 = 2430697) B2430697
theorem B4322879 : Blo 1008601 4322879 := bstep (se 1 (by rfl) ⟨3242159, by rfl⟩ : syracuseStep 4322879 = 6484319) B6484319
theorem B2881145 : Blo 1008601 2881145 := bstep (se 2 (by rfl) ⟨1080429, by rfl⟩ : syracuseStep 2881145 = 2160859) B2160859
theorem B12974377 : Blo 1008601 12974377 := bstep (se 2 (by rfl) ⟨4865391, by rfl⟩ : syracuseStep 12974377 = 9730783) B9730783
theorem B2882375 : Blo 1008601 2882375 := bstep (se 1 (by rfl) ⟨2161781, by rfl⟩ : syracuseStep 2882375 = 4323563) B4323563
theorem B4848785 : Blo 1008601 4848785 := bstep (se 2 (by rfl) ⟨1818294, by rfl⟩ : syracuseStep 4848785 = 3636589) B3636589
theorem B6225403 : Blo 1008601 6225403 := bstep (se 1 (by rfl) ⟨4669052, by rfl⟩ : syracuseStep 6225403 = 9338105) B9338105
theorem B5766983 : Blo 1008601 5766983 := bstep (se 1 (by rfl) ⟨4325237, by rfl⟩ : syracuseStep 5766983 = 8650475) B8650475
theorem B7667621 : Blo 1008601 7667621 := bstep (se 4 (by rfl) ⟨718839, by rfl⟩ : syracuseStep 7667621 = 1437679) B1437679
theorem B1277947 : Blo 1008601 1277947 := bstep (se 1 (by rfl) ⟨958460, by rfl⟩ : syracuseStep 1277947 = 1916921) B1916921
theorem B3407993 : Blo 1008601 3407993 := bstep (se 2 (by rfl) ⟨1277997, by rfl⟩ : syracuseStep 3407993 = 2555995) B2555995
theorem B2556299 : Blo 1008601 2556299 := bstep (se 1 (by rfl) ⟨1917224, by rfl⟩ : syracuseStep 2556299 = 3834449) B3834449
theorem B10946441 : Blo 1008601 10946441 := bstep (se 2 (by rfl) ⟨4104915, by rfl⟩ : syracuseStep 10946441 = 8209831) B8209831
theorem B2557919 : Blo 1008601 2557919 := bstep (se 1 (by rfl) ⟨1918439, by rfl⟩ : syracuseStep 2557919 = 3836879) B3836879
theorem B3639271 : Blo 1008601 3639271 := bstep (se 1 (by rfl) ⟨2729453, by rfl⟩ : syracuseStep 3639271 = 5458907) B5458907
theorem B3410585 : Blo 1008601 3410585 := bstep (se 2 (by rfl) ⟨1278969, by rfl⟩ : syracuseStep 3410585 = 2557939) B2557939
theorem B7670537 : Blo 1008601 7670537 := bstep (se 2 (by rfl) ⟨2876451, by rfl⟩ : syracuseStep 7670537 = 5752903) B5752903
theorem B4852669 : Blo 1008601 4852669 := bstep (se 3 (by rfl) ⟨909875, by rfl⟩ : syracuseStep 4852669 = 1819751) B1819751
theorem B1707689 : Blo 1008601 1707689 := bstep (se 2 (by rfl) ⟨640383, by rfl⟩ : syracuseStep 1707689 = 1280767) B1280767
theorem B2559721 : Blo 1008601 2559721 := bstep (se 2 (by rfl) ⟨959895, by rfl⟩ : syracuseStep 2559721 = 1919791) B1919791
theorem B36835505 : Blo 1008601 36835505 := bstep (se 2 (by rfl) ⟨13813314, by rfl⟩ : syracuseStep 36835505 = 27626629) B27626629
theorem B5116607 : Blo 1008601 5116607 := bstep (se 1 (by rfl) ⟨3837455, by rfl⟩ : syracuseStep 5116607 = 7674911) B7674911
theorem B3412799 : Blo 1008601 3412799 := bstep (se 1 (by rfl) ⟨2559599, by rfl⟩ : syracuseStep 3412799 = 5119199) B5119199
theorem B2561129 : Blo 1008601 2561129 := bstep (se 2 (by rfl) ⟨960423, by rfl⟩ : syracuseStep 2561129 = 1920847) B1920847
theorem B19699199 : Blo 1008601 19699199 := bstep (se 1 (by rfl) ⟨14774399, by rfl⟩ : syracuseStep 19699199 = 29548799) B29548799
theorem B7280387 : Blo 1008601 7280387 := bstep (se 1 (by rfl) ⟨5460290, by rfl⟩ : syracuseStep 7280387 = 10920581) B10920581
theorem B4495123 : Blo 1008601 4495123 := bstep (se 1 (by rfl) ⟨3371342, by rfl⟩ : syracuseStep 4495123 = 6742685) B6742685
theorem B1513499 : Blo 1008601 1513499 := bstep (se 1 (by rfl) ⟨1135124, by rfl⟩ : syracuseStep 1513499 = 2270249) B2270249
theorem B1513703 : Blo 1008601 1513703 := bstep (se 1 (by rfl) ⟨1135277, by rfl⟩ : syracuseStep 1513703 = 2270555) B2270555
theorem B3840311 : Blo 1008601 3840311 := bstep (se 1 (by rfl) ⟨2880233, by rfl⟩ : syracuseStep 3840311 = 5760467) B5760467
theorem B1513883 : Blo 1008601 1513883 := bstep (se 1 (by rfl) ⟨1135412, by rfl⟩ : syracuseStep 1513883 = 2270825) B2270825
theorem B63184049 : Blo 1008601 63184049 := bstep (se 2 (by rfl) ⟨23694018, by rfl⟩ : syracuseStep 63184049 = 47388037) B47388037
theorem B1514855 : Blo 1008601 1514855 := bstep (se 1 (by rfl) ⟨1136141, by rfl⟩ : syracuseStep 1514855 = 2272283) B2272283
theorem B1515503 : Blo 1008601 1515503 := bstep (se 1 (by rfl) ⟨1136627, by rfl⟩ : syracuseStep 1515503 = 2273255) B2273255
theorem B1515551 : Blo 1008601 1515551 := bstep (se 1 (by rfl) ⟨1136663, by rfl⟩ : syracuseStep 1515551 = 2273327) B2273327
theorem B3416201 : Blo 1008601 3416201 := bstep (se 2 (by rfl) ⟨1281075, by rfl⟩ : syracuseStep 3416201 = 2562151) B2562151
theorem B2269367 : Blo 1008601 2269367 := bstep (se 1 (by rfl) ⟨1702025, by rfl⟩ : syracuseStep 2269367 = 3404051) B3404051
theorem B7283155 : Blo 1008601 7283155 := bstep (se 1 (by rfl) ⟨5462366, by rfl⟩ : syracuseStep 7283155 = 10924733) B10924733
theorem B3416633 : Blo 1008601 3416633 := bstep (se 2 (by rfl) ⟨1281237, by rfl⟩ : syracuseStep 3416633 = 2562475) B2562475
theorem B7283789 : Blo 1008601 7283789 := bstep (se 3 (by rfl) ⟨1365710, by rfl⟩ : syracuseStep 7283789 = 2731421) B2731421
theorem B11510909 : Blo 1008601 11510909 := bstep (se 3 (by rfl) ⟨2158295, by rfl⟩ : syracuseStep 11510909 = 4316591) B4316591
theorem B16394231 : Blo 1008601 16394231 := bstep (se 1 (by rfl) ⟨12295673, by rfl⟩ : syracuseStep 16394231 = 24591347) B24591347
theorem B8300537 : Blo 1008601 8300537 := bstep (se 2 (by rfl) ⟨3112701, by rfl⟩ : syracuseStep 8300537 = 6225403) B6225403
theorem B1517735 : Blo 1008601 1517735 := bstep (se 1 (by rfl) ⟨1138301, by rfl⟩ : syracuseStep 1517735 = 2276603) B2276603
theorem B7874779 : Blo 1008601 7874779 := bstep (se 1 (by rfl) ⟨5906084, by rfl⟩ : syracuseStep 7874779 = 11812169) B11812169
theorem B6138089 : Blo 1008601 6138089 := bstep (se 2 (by rfl) ⟨2301783, by rfl⟩ : syracuseStep 6138089 = 4603567) B4603567
theorem B1517927 : Blo 1008601 1517927 := bstep (se 1 (by rfl) ⟨1138445, by rfl⟩ : syracuseStep 1517927 = 2276891) B2276891
theorem B3844655 : Blo 1008601 3844655 := bstep (se 1 (by rfl) ⟨2883491, by rfl⟩ : syracuseStep 3844655 = 5766983) B5766983
theorem B1518569 : Blo 1008601 1518569 := bstep (se 2 (by rfl) ⟨569463, by rfl⟩ : syracuseStep 1518569 = 1138927) B1138927
theorem B2272481 : Blo 1008601 2272481 := bstep (se 2 (by rfl) ⟨852180, by rfl⟩ : syracuseStep 2272481 = 1704361) B1704361
theorem B3648959 : Blo 1008601 3648959 := bstep (se 1 (by rfl) ⟨2736719, by rfl⟩ : syracuseStep 3648959 = 5473439) B5473439
theorem B5058941 : Blo 1008601 5058941 := bstep (se 3 (by rfl) ⟨948551, by rfl⟩ : syracuseStep 5058941 = 1897103) B1897103
theorem B13840951 : Blo 1008601 13840951 := bstep (se 1 (by rfl) ⟨10380713, by rfl⟩ : syracuseStep 13840951 = 20761427) B20761427
theorem B8205419 : Blo 1008601 8205419 := bstep (se 1 (by rfl) ⟨6154064, by rfl⟩ : syracuseStep 8205419 = 12308129) B12308129
theorem B36910241 : Blo 1008601 36910241 := bstep (se 2 (by rfl) ⟨13841340, by rfl⟩ : syracuseStep 36910241 = 27682681) B27682681
theorem B6141415 : Blo 1008601 6141415 := bstep (se 1 (by rfl) ⟨4606061, by rfl⟩ : syracuseStep 6141415 = 9212123) B9212123
theorem B1947311 : Blo 1008601 1947311 := bstep (se 1 (by rfl) ⟨1460483, by rfl⟩ : syracuseStep 1947311 = 2920967) B2920967
theorem B1621055 : Blo 1008601 1621055 := bstep (se 1 (by rfl) ⟨1215791, by rfl⟩ : syracuseStep 1621055 = 2431583) B2431583
theorem B8633729 : Blo 1008601 8633729 := bstep (se 2 (by rfl) ⟨3237648, by rfl⟩ : syracuseStep 8633729 = 6475297) B6475297
theorem B6143465 : Blo 1008601 6143465 := bstep (se 2 (by rfl) ⟨2303799, by rfl⟩ : syracuseStep 6143465 = 4607599) B4607599
theorem B49102523 : Blo 1008601 49102523 := bstep (se 1 (by rfl) ⟨36826892, by rfl⟩ : syracuseStep 49102523 = 73653785) B73653785
theorem B6569723 : Blo 1008601 6569723 := bstep (se 1 (by rfl) ⟨4927292, by rfl⟩ : syracuseStep 6569723 = 9854585) B9854585
theorem B2277359 : Blo 1008601 2277359 := bstep (se 1 (by rfl) ⟨1708019, by rfl⟩ : syracuseStep 2277359 = 3416039) B3416039
theorem B1916959 : Blo 1008601 1916959 := bstep (se 1 (by rfl) ⟨1437719, by rfl⟩ : syracuseStep 1916959 = 2875439) B2875439
theorem B1917179 : Blo 1008601 1917179 := bstep (se 1 (by rfl) ⟨1437884, by rfl⟩ : syracuseStep 1917179 = 2875769) B2875769
theorem B1917695 : Blo 1008601 1917695 := bstep (se 1 (by rfl) ⟨1438271, by rfl⟩ : syracuseStep 1917695 = 2876543) B2876543
theorem B17286047 : Blo 1008601 17286047 := bstep (se 1 (by rfl) ⟨12964535, by rfl⟩ : syracuseStep 17286047 = 25929071) B25929071
theorem B1919047 : Blo 1008601 1919047 := bstep (se 1 (by rfl) ⟨1439285, by rfl⟩ : syracuseStep 1919047 = 2878571) B2878571
theorem B1919207 : Blo 1008601 1919207 := bstep (se 1 (by rfl) ⟨1439405, by rfl⟩ : syracuseStep 1919207 = 2878811) B2878811
theorem B49891621 : Blo 1008601 49891621 := bstep (se 4 (by rfl) ⟨4677339, by rfl⟩ : syracuseStep 49891621 = 9354679) B9354679
theorem B1920763 : Blo 1008601 1920763 := bstep (se 1 (by rfl) ⟨1440572, by rfl⟩ : syracuseStep 1920763 = 2881145) B2881145
theorem B1921583 : Blo 1008601 1921583 := bstep (se 1 (by rfl) ⟨1441187, by rfl⟩ : syracuseStep 1921583 = 2882375) B2882375
theorem B3232523 : Blo 1008601 3232523 := bstep (se 1 (by rfl) ⟨2424392, by rfl⟩ : syracuseStep 3232523 = 4848785) B4848785
theorem B11654113 : Blo 1008601 11654113 := bstep (se 2 (by rfl) ⟨4370292, by rfl⟩ : syracuseStep 11654113 = 8740585) B8740585
theorem B5756093 : Blo 1008601 5756093 := bstep (se 3 (by rfl) ⟨1079267, by rfl⟩ : syracuseStep 5756093 = 2158535) B2158535
theorem B5756777 : Blo 1008601 5756777 := bstep (se 2 (by rfl) ⟨2158791, by rfl⟩ : syracuseStep 5756777 = 4317583) B4317583
theorem B25942193 : Blo 1008601 25942193 := bstep (se 2 (by rfl) ⟨9728322, by rfl⟩ : syracuseStep 25942193 = 19456645) B19456645
theorem B1137199 : Blo 1008601 1137199 := bstep (se 1 (by rfl) ⟨852899, by rfl⟩ : syracuseStep 1137199 = 1705799) B1705799
theorem B3693161 : Blo 1008601 3693161 := bstep (se 2 (by rfl) ⟨1384935, by rfl⟩ : syracuseStep 3693161 = 2769871) B2769871
theorem B1137631 : Blo 1008601 1137631 := bstep (se 1 (by rfl) ⟨853223, by rfl⟩ : syracuseStep 1137631 = 1706447) B1706447
theorem B1137775 : Blo 1008601 1137775 := bstep (se 1 (by rfl) ⟨853331, by rfl⟩ : syracuseStep 1137775 = 1706663) B1706663
theorem B17259803 : Blo 1008601 17259803 := bstep (se 1 (by rfl) ⟨12944852, by rfl⟩ : syracuseStep 17259803 = 25889705) B25889705
theorem B5758553 : Blo 1008601 5758553 := bstep (se 2 (by rfl) ⟨2159457, by rfl⟩ : syracuseStep 5758553 = 4318915) B4318915
theorem B8642477 : Blo 1008601 8642477 := bstep (se 3 (by rfl) ⟨1620464, by rfl⟩ : syracuseStep 8642477 = 3240929) B3240929
theorem B18472997 : Blo 1008601 18472997 := bstep (se 4 (by rfl) ⟨1731843, by rfl⟩ : syracuseStep 18472997 = 3463687) B3463687
theorem B53174969 : Blo 1008601 53174969 := bstep (se 2 (by rfl) ⟨19940613, by rfl⟩ : syracuseStep 53174969 = 39881227) B39881227
theorem B18441179 : Blo 1008601 18441179 := bstep (se 1 (by rfl) ⟨13830884, by rfl⟩ : syracuseStep 18441179 = 27661769) B27661769
theorem B1008799 : Blo 1008601 1008799 := bstep (se 1 (by rfl) ⟨756599, by rfl⟩ : syracuseStep 1008799 = 1513199) B1513199
theorem B2876897 : Blo 1008601 2876897 := bstep (se 2 (by rfl) ⟨1078836, by rfl⟩ : syracuseStep 2876897 = 2157673) B2157673
theorem B7661303 : Blo 1008601 7661303 := bstep (se 1 (by rfl) ⟨5745977, by rfl⟩ : syracuseStep 7661303 = 11491955) B11491955
theorem B1009535 : Blo 1008601 1009535 := bstep (se 1 (by rfl) ⟨757151, by rfl⟩ : syracuseStep 1009535 = 1514303) B1514303
theorem B1009983 : Blo 1008601 1009983 := bstep (se 1 (by rfl) ⟨757487, by rfl⟩ : syracuseStep 1009983 = 1514975) B1514975
theorem B1010303 : Blo 1008601 1010303 := bstep (se 1 (by rfl) ⟨757727, by rfl⟩ : syracuseStep 1010303 = 1515455) B1515455
theorem B5106401 : Blo 1008601 5106401 := bstep (se 2 (by rfl) ⟨1914900, by rfl⟩ : syracuseStep 5106401 = 3829801) B3829801
theorem B1010415 : Blo 1008601 1010415 := bstep (se 1 (by rfl) ⟨757811, by rfl⟩ : syracuseStep 1010415 = 1515623) B1515623
theorem B13134575 : Blo 1008601 13134575 := bstep (se 1 (by rfl) ⟨9850931, by rfl⟩ : syracuseStep 13134575 = 19701863) B19701863
theorem B1010503 : Blo 1008601 1010503 := bstep (se 1 (by rfl) ⟨757877, by rfl⟩ : syracuseStep 1010503 = 1515755) B1515755
theorem B20704211 : Blo 1008601 20704211 := bstep (se 1 (by rfl) ⟨15528158, by rfl⟩ : syracuseStep 20704211 = 31056317) B31056317
theorem B3238879 : Blo 1008601 3238879 := bstep (se 1 (by rfl) ⟨2429159, by rfl⟩ : syracuseStep 3238879 = 4858319) B4858319
theorem B5762177 : Blo 1008601 5762177 := bstep (se 2 (by rfl) ⟨2160816, by rfl⟩ : syracuseStep 5762177 = 4321633) B4321633
theorem B5106887 : Blo 1008601 5106887 := bstep (se 1 (by rfl) ⟨3830165, by rfl⟩ : syracuseStep 5106887 = 7660331) B7660331
theorem B11660537 : Blo 1008601 11660537 := bstep (se 2 (by rfl) ⟨4372701, by rfl⟩ : syracuseStep 11660537 = 8745403) B8745403
theorem B1011879 : Blo 1008601 1011879 := bstep (se 1 (by rfl) ⟨758909, by rfl⟩ : syracuseStep 1011879 = 1517819) B1517819
theorem B1011995 : Blo 1008601 1011995 := bstep (se 1 (by rfl) ⟨758996, by rfl⟩ : syracuseStep 1011995 = 1517993) B1517993
theorem B1438175 : Blo 1008601 1438175 := bstep (se 1 (by rfl) ⟨1078631, by rfl⟩ : syracuseStep 1438175 = 2157263) B2157263
theorem B1012251 : Blo 1008601 1012251 := bstep (se 1 (by rfl) ⟨759188, by rfl⟩ : syracuseStep 1012251 = 1518377) B1518377
theorem B1012351 : Blo 1008601 1012351 := bstep (se 1 (by rfl) ⟨759263, by rfl⟩ : syracuseStep 1012351 = 1518527) B1518527
theorem B2880143 : Blo 1008601 2880143 := bstep (se 1 (by rfl) ⟨2160107, by rfl⟩ : syracuseStep 2880143 = 4320215) B4320215
theorem B5108507 : Blo 1008601 5108507 := bstep (se 1 (by rfl) ⟨3831380, by rfl⟩ : syracuseStep 5108507 = 7662761) B7662761
theorem B3830591 : Blo 1008601 3830591 := bstep (se 1 (by rfl) ⟨2872943, by rfl⟩ : syracuseStep 3830591 = 5745887) B5745887
theorem B5108831 : Blo 1008601 5108831 := bstep (se 1 (by rfl) ⟨3831623, by rfl⟩ : syracuseStep 5108831 = 7663247) B7663247
theorem B27653795 : Blo 1008601 27653795 := bstep (se 1 (by rfl) ⟨20740346, by rfl⟩ : syracuseStep 27653795 = 41480693) B41480693
theorem B17299169 : Blo 1008601 17299169 := bstep (se 2 (by rfl) ⟨6487188, by rfl⟩ : syracuseStep 17299169 = 12974377) B12974377
theorem B3405779 : Blo 1008601 3405779 := bstep (se 1 (by rfl) ⟨2554334, by rfl⟩ : syracuseStep 3405779 = 5108669) B5108669
theorem B147618125 : Blo 1008601 147618125 := bstep (se 3 (by rfl) ⟨27678398, by rfl⟩ : syracuseStep 147618125 = 55356797) B55356797
theorem B2881919 : Blo 1008601 2881919 := bstep (se 1 (by rfl) ⟨2161439, by rfl⟩ : syracuseStep 2881919 = 4322879) B4322879
theorem B49117697 : Blo 1008601 49117697 := bstep (se 2 (by rfl) ⟨18419136, by rfl⟩ : syracuseStep 49117697 = 36838273) B36838273
theorem B3243071 : Blo 1008601 3243071 := bstep (se 1 (by rfl) ⟨2432303, by rfl⟩ : syracuseStep 3243071 = 4864607) B4864607
theorem B3636359 : Blo 1008601 3636359 := bstep (se 1 (by rfl) ⟨2727269, by rfl⟩ : syracuseStep 3636359 = 5454539) B5454539
theorem B5111747 : Blo 1008601 5111747 := bstep (se 1 (by rfl) ⟨3833810, by rfl⟩ : syracuseStep 5111747 = 7667621) B7667621
theorem B1703929 : Blo 1008601 1703929 := bstep (se 2 (by rfl) ⟨638973, by rfl⟩ : syracuseStep 1703929 = 1277947) B1277947
theorem B2555945 : Blo 1008601 2555945 := bstep (se 2 (by rfl) ⟨958479, by rfl⟩ : syracuseStep 2555945 = 1916959) B1916959
theorem B1278119 : Blo 1008601 1278119 := bstep (se 1 (by rfl) ⟨958589, by rfl⟩ : syracuseStep 1278119 = 1917179) B1917179
theorem B1704199 : Blo 1008601 1704199 := bstep (se 1 (by rfl) ⟨1278149, by rfl⟩ : syracuseStep 1704199 = 2556299) B2556299
theorem B3835133 : Blo 1008601 3835133 := bstep (se 3 (by rfl) ⟨719087, by rfl⟩ : syracuseStep 3835133 = 1438175) B1438175
theorem B1705279 : Blo 1008601 1705279 := bstep (se 1 (by rfl) ⟨1278959, by rfl⟩ : syracuseStep 1705279 = 2557919) B2557919
theorem B1279471 : Blo 1008601 1279471 := bstep (se 1 (by rfl) ⟨959603, by rfl⟩ : syracuseStep 1279471 = 1919207) B1919207
theorem B5113691 : Blo 1008601 5113691 := bstep (se 1 (by rfl) ⟨3835268, by rfl⟩ : syracuseStep 5113691 = 7670537) B7670537
theorem B5113853 : Blo 1008601 5113853 := bstep (se 3 (by rfl) ⟨958847, by rfl⟩ : syracuseStep 5113853 = 1917695) B1917695
theorem B4852361 : Blo 1008601 4852361 := bstep (se 2 (by rfl) ⟨1819635, by rfl⟩ : syracuseStep 4852361 = 3639271) B3639271
theorem B2558729 : Blo 1008601 2558729 := bstep (se 2 (by rfl) ⟨959523, by rfl⟩ : syracuseStep 2558729 = 1919047) B1919047
theorem B66522161 : Blo 1008601 66522161 := bstep (se 2 (by rfl) ⟨24945810, by rfl⟩ : syracuseStep 66522161 = 49891621) B49891621
theorem B3411071 : Blo 1008601 3411071 := bstep (se 1 (by rfl) ⟨2558303, by rfl⟩ : syracuseStep 3411071 = 5116607) B5116607
theorem B1707419 : Blo 1008601 1707419 := bstep (se 1 (by rfl) ⟨1280564, by rfl⟩ : syracuseStep 1707419 = 2561129) B2561129
theorem B3837395 : Blo 1008601 3837395 := bstep (se 1 (by rfl) ⟨2878046, by rfl⟩ : syracuseStep 3837395 = 5756093) B5756093
theorem B4853591 : Blo 1008601 4853591 := bstep (se 1 (by rfl) ⟨3640193, by rfl⟩ : syracuseStep 4853591 = 7280387) B7280387
theorem B3837851 : Blo 1008601 3837851 := bstep (se 1 (by rfl) ⟨2878388, by rfl⟩ : syracuseStep 3837851 = 5756777) B5756777
theorem B2560207 : Blo 1008601 2560207 := bstep (se 1 (by rfl) ⟨1920155, by rfl⟩ : syracuseStep 2560207 = 3840311) B3840311
theorem B2462107 : Blo 1008601 2462107 := bstep (se 1 (by rfl) ⟨1846580, by rfl⟩ : syracuseStep 2462107 = 3693161) B3693161
theorem B11506535 : Blo 1008601 11506535 := bstep (se 1 (by rfl) ⟨8629901, by rfl⟩ : syracuseStep 11506535 = 17259803) B17259803
theorem B3412961 : Blo 1008601 3412961 := bstep (se 2 (by rfl) ⟨1279860, by rfl⟩ : syracuseStep 3412961 = 2559721) B2559721
theorem B2561017 : Blo 1008601 2561017 := bstep (se 2 (by rfl) ⟨960381, by rfl⟩ : syracuseStep 2561017 = 1920763) B1920763
theorem B3839035 : Blo 1008601 3839035 := bstep (se 1 (by rfl) ⟨2879276, by rfl⟩ : syracuseStep 3839035 = 5758553) B5758553
theorem B1512911 : Blo 1008601 1512911 := bstep (se 1 (by rfl) ⟨1134683, by rfl⟩ : syracuseStep 1512911 = 2269367) B2269367
theorem B12294119 : Blo 1008601 12294119 := bstep (se 1 (by rfl) ⟨9220589, by rfl⟩ : syracuseStep 12294119 = 18441179) B18441179
theorem B4855859 : Blo 1008601 4855859 := bstep (se 1 (by rfl) ⟨3641894, by rfl⟩ : syracuseStep 4855859 = 7283789) B7283789
theorem B18454601 : Blo 1008601 18454601 := bstep (se 2 (by rfl) ⟨6920475, by rfl⟩ : syracuseStep 18454601 = 13840951) B13840951
theorem B7673939 : Blo 1008601 7673939 := bstep (se 1 (by rfl) ⟨5755454, by rfl⟩ : syracuseStep 7673939 = 11510909) B11510909
theorem B15538817 : Blo 1008601 15538817 := bstep (se 2 (by rfl) ⟨5827056, by rfl⟩ : syracuseStep 15538817 = 11654113) B11654113
theorem B2563103 : Blo 1008601 2563103 := bstep (se 1 (by rfl) ⟨1922327, by rfl⟩ : syracuseStep 2563103 = 3844655) B3844655
theorem B8756383 : Blo 1008601 8756383 := bstep (se 1 (by rfl) ⟨6567287, by rfl⟩ : syracuseStep 8756383 = 13134575) B13134575
theorem B13802807 : Blo 1008601 13802807 := bstep (se 1 (by rfl) ⟨10352105, by rfl⟩ : syracuseStep 13802807 = 20704211) B20704211
theorem B3841451 : Blo 1008601 3841451 := bstep (se 1 (by rfl) ⟨2881088, by rfl⟩ : syracuseStep 3841451 = 5762177) B5762177
theorem B1514987 : Blo 1008601 1514987 := bstep (se 1 (by rfl) ⟨1136240, by rfl⟩ : syracuseStep 1514987 = 2272481) B2272481
theorem B2432639 : Blo 1008601 2432639 := bstep (se 1 (by rfl) ⟨1824479, by rfl⟩ : syracuseStep 2432639 = 3648959) B3648959
theorem B1516265 : Blo 1008601 1516265 := bstep (se 2 (by rfl) ⟨568599, by rfl⟩ : syracuseStep 1516265 = 1137199) B1137199
theorem B1516841 : Blo 1008601 1516841 := bstep (se 2 (by rfl) ⟨568815, by rfl⟩ : syracuseStep 1516841 = 1137631) B1137631
theorem B2270519 : Blo 1008601 2270519 := bstep (se 1 (by rfl) ⟨1702889, by rfl⟩ : syracuseStep 2270519 = 3405779) B3405779
theorem B1517033 : Blo 1008601 1517033 := bstep (se 2 (by rfl) ⟨568887, by rfl⟩ : syracuseStep 1517033 = 1137775) B1137775
theorem B98412083 : Blo 1008601 98412083 := bstep (se 1 (by rfl) ⟨73809062, by rfl⟩ : syracuseStep 98412083 = 147618125) B147618125
theorem B32745131 : Blo 1008601 32745131 := bstep (se 1 (by rfl) ⟨24558848, by rfl⟩ : syracuseStep 32745131 = 49117697) B49117697
theorem B1518239 : Blo 1008601 1518239 := bstep (se 1 (by rfl) ⟨1138679, by rfl⟩ : syracuseStep 1518239 = 2277359) B2277359
theorem B2271905 : Blo 1008601 2271905 := bstep (se 2 (by rfl) ⟨851964, by rfl⟩ : syracuseStep 2271905 = 1703929) B1703929
theorem B2271995 : Blo 1008601 2271995 := bstep (se 1 (by rfl) ⟨1703996, by rfl⟩ : syracuseStep 2271995 = 3407993) B3407993
theorem B9710873 : Blo 1008601 9710873 := bstep (se 2 (by rfl) ⟨3641577, by rfl⟩ : syracuseStep 9710873 = 7283155) B7283155
theorem B5124221 : Blo 1008601 5124221 := bstep (se 3 (by rfl) ⟨960791, by rfl⟩ : syracuseStep 5124221 = 1921583) B1921583
theorem B2273723 : Blo 1008601 2273723 := bstep (se 1 (by rfl) ⟨1705292, by rfl⟩ : syracuseStep 2273723 = 3410585) B3410585
theorem B24557003 : Blo 1008601 24557003 := bstep (se 1 (by rfl) ⟨18417752, by rfl⟩ : syracuseStep 24557003 = 36835505) B36835505
theorem B10499705 : Blo 1008601 10499705 := bstep (se 2 (by rfl) ⟨3937389, by rfl⟩ : syracuseStep 10499705 = 7874779) B7874779
theorem B2275199 : Blo 1008601 2275199 := bstep (se 1 (by rfl) ⟨1706399, by rfl⟩ : syracuseStep 2275199 = 3412799) B3412799
theorem B6470225 : Blo 1008601 6470225 := bstep (se 2 (by rfl) ⟨2426334, by rfl⟩ : syracuseStep 6470225 = 4852669) B4852669
theorem B42122699 : Blo 1008601 42122699 := bstep (se 1 (by rfl) ⟨31592024, by rfl⟩ : syracuseStep 42122699 = 63184049) B63184049
theorem B2277467 : Blo 1008601 2277467 := bstep (se 1 (by rfl) ⟨1708100, by rfl⟩ : syracuseStep 2277467 = 3416201) B3416201
theorem B2277755 : Blo 1008601 2277755 := bstep (se 1 (by rfl) ⟨1708316, by rfl⟩ : syracuseStep 2277755 = 3416633) B3416633
theorem B1917931 : Blo 1008601 1917931 := bstep (se 1 (by rfl) ⟨1438448, by rfl⟩ : syracuseStep 1917931 = 2876897) B2876897
theorem B7685117 : Blo 1008601 7685117 := bstep (se 3 (by rfl) ⟨1440959, by rfl⟩ : syracuseStep 7685117 = 2881919) B2881919
theorem B10929487 : Blo 1008601 10929487 := bstep (se 1 (by rfl) ⟨8197115, by rfl⟩ : syracuseStep 10929487 = 16394231) B16394231
theorem B1920095 : Blo 1008601 1920095 := bstep (se 1 (by rfl) ⟨1440071, by rfl⟩ : syracuseStep 1920095 = 2880143) B2880143
theorem B18435863 : Blo 1008601 18435863 := bstep (se 1 (by rfl) ⟨13826897, by rfl⟩ : syracuseStep 18435863 = 27653795) B27653795
theorem B1298207 : Blo 1008601 1298207 := bstep (se 1 (by rfl) ⟨973655, by rfl⟩ : syracuseStep 1298207 = 1947311) B1947311
theorem B5755819 : Blo 1008601 5755819 := bstep (se 1 (by rfl) ⟨4316864, by rfl⟩ : syracuseStep 5755819 = 8633729) B8633729
theorem B4379815 : Blo 1008601 4379815 := bstep (se 1 (by rfl) ⟨3284861, by rfl⟩ : syracuseStep 4379815 = 6569723) B6569723
theorem B11524031 : Blo 1008601 11524031 := bstep (se 1 (by rfl) ⟨8643023, by rfl⟩ : syracuseStep 11524031 = 17286047) B17286047
theorem B13490509 : Blo 1008601 13490509 := bstep (se 3 (by rfl) ⟨2529470, by rfl⟩ : syracuseStep 13490509 = 5058941) B5058941
theorem B7297627 : Blo 1008601 7297627 := bstep (se 1 (by rfl) ⟨5473220, by rfl⟩ : syracuseStep 7297627 = 10946441) B10946441
theorem B1138459 : Blo 1008601 1138459 := bstep (se 1 (by rfl) ⟨853844, by rfl⟩ : syracuseStep 1138459 = 1707689) B1707689
theorem B21881117 : Blo 1008601 21881117 := bstep (se 3 (by rfl) ⟨4102709, by rfl⟩ : syracuseStep 21881117 = 8205419) B8205419
theorem B2155015 : Blo 1008601 2155015 := bstep (se 1 (by rfl) ⟨1616261, by rfl⟩ : syracuseStep 2155015 = 3232523) B3232523
theorem B13132799 : Blo 1008601 13132799 := bstep (se 1 (by rfl) ⟨9849599, by rfl⟩ : syracuseStep 13132799 = 19699199) B19699199
theorem B4318505 : Blo 1008601 4318505 := bstep (se 2 (by rfl) ⟨1619439, by rfl⟩ : syracuseStep 4318505 = 3238879) B3238879
theorem B1008999 : Blo 1008601 1008999 := bstep (se 1 (by rfl) ⟨756749, by rfl⟩ : syracuseStep 1008999 = 1513499) B1513499
theorem B17294795 : Blo 1008601 17294795 := bstep (se 1 (by rfl) ⟨12971096, by rfl⟩ : syracuseStep 17294795 = 25942193) B25942193
theorem B1009135 : Blo 1008601 1009135 := bstep (se 1 (by rfl) ⟨756851, by rfl⟩ : syracuseStep 1009135 = 1513703) B1513703
theorem B1009255 : Blo 1008601 1009255 := bstep (se 1 (by rfl) ⟨756941, by rfl⟩ : syracuseStep 1009255 = 1513883) B1513883
theorem B1009903 : Blo 1008601 1009903 := bstep (se 1 (by rfl) ⟨757427, by rfl⟩ : syracuseStep 1009903 = 1514855) B1514855
theorem B5761651 : Blo 1008601 5761651 := bstep (se 1 (by rfl) ⟨4321238, by rfl⟩ : syracuseStep 5761651 = 8642477) B8642477
theorem B1010335 : Blo 1008601 1010335 := bstep (se 1 (by rfl) ⟨757751, by rfl⟩ : syracuseStep 1010335 = 1515503) B1515503
theorem B1010367 : Blo 1008601 1010367 := bstep (se 1 (by rfl) ⟨757775, by rfl⟩ : syracuseStep 1010367 = 1515551) B1515551
theorem B12315331 : Blo 1008601 12315331 := bstep (se 1 (by rfl) ⟨9236498, by rfl⟩ : syracuseStep 12315331 = 18472997) B18472997
theorem B35449979 : Blo 1008601 35449979 := bstep (se 1 (by rfl) ⟨26587484, by rfl⟩ : syracuseStep 35449979 = 53174969) B53174969
theorem B5107535 : Blo 1008601 5107535 := bstep (se 1 (by rfl) ⟨3830651, by rfl⟩ : syracuseStep 5107535 = 7661303) B7661303
theorem B5533691 : Blo 1008601 5533691 := bstep (se 1 (by rfl) ⟨4150268, by rfl⟩ : syracuseStep 5533691 = 8300537) B8300537
theorem B1011823 : Blo 1008601 1011823 := bstep (se 1 (by rfl) ⟨758867, by rfl⟩ : syracuseStep 1011823 = 1517735) B1517735
theorem B4092059 : Blo 1008601 4092059 := bstep (se 1 (by rfl) ⟨3069044, by rfl⟩ : syracuseStep 4092059 = 6138089) B6138089
theorem B1011951 : Blo 1008601 1011951 := bstep (se 1 (by rfl) ⟨758963, by rfl⟩ : syracuseStep 1011951 = 1517927) B1517927
theorem B3404267 : Blo 1008601 3404267 := bstep (se 1 (by rfl) ⟨2553200, by rfl⟩ : syracuseStep 3404267 = 5106401) B5106401
theorem B8188553 : Blo 1008601 8188553 := bstep (se 2 (by rfl) ⟨3070707, by rfl⟩ : syracuseStep 8188553 = 6141415) B6141415
theorem B1012379 : Blo 1008601 1012379 := bstep (se 1 (by rfl) ⟨759284, by rfl⟩ : syracuseStep 1012379 = 1518569) B1518569
theorem B3404591 : Blo 1008601 3404591 := bstep (se 1 (by rfl) ⟨2553443, by rfl⟩ : syracuseStep 3404591 = 5106887) B5106887
theorem B5993497 : Blo 1008601 5993497 := bstep (se 2 (by rfl) ⟨2247561, by rfl⟩ : syracuseStep 5993497 = 4495123) B4495123
theorem B3405671 : Blo 1008601 3405671 := bstep (se 1 (by rfl) ⟨2554253, by rfl⟩ : syracuseStep 3405671 = 5108507) B5108507
theorem B2553727 : Blo 1008601 2553727 := bstep (se 1 (by rfl) ⟨1915295, by rfl⟩ : syracuseStep 2553727 = 3830591) B3830591
theorem B31094765 : Blo 1008601 31094765 := bstep (se 3 (by rfl) ⟨5830268, by rfl⟩ : syracuseStep 31094765 = 11660537) B11660537
theorem B3405887 : Blo 1008601 3405887 := bstep (se 1 (by rfl) ⟨2554415, by rfl⟩ : syracuseStep 3405887 = 5108831) B5108831
theorem B24606827 : Blo 1008601 24606827 := bstep (se 1 (by rfl) ⟨18455120, by rfl⟩ : syracuseStep 24606827 = 36910241) B36910241
theorem B11532779 : Blo 1008601 11532779 := bstep (se 1 (by rfl) ⟨8649584, by rfl⟩ : syracuseStep 11532779 = 17299169) B17299169
theorem B1080703 : Blo 1008601 1080703 := bstep (se 1 (by rfl) ⟨810527, by rfl⟩ : syracuseStep 1080703 = 1621055) B1621055
theorem B2162047 : Blo 1008601 2162047 := bstep (se 1 (by rfl) ⟨1621535, by rfl⟩ : syracuseStep 2162047 = 3243071) B3243071
theorem B2424239 : Blo 1008601 2424239 := bstep (se 1 (by rfl) ⟨1818179, by rfl⟩ : syracuseStep 2424239 = 3636359) B3636359
theorem B4095643 : Blo 1008601 4095643 := bstep (se 1 (by rfl) ⟨3071732, by rfl⟩ : syracuseStep 4095643 = 6143465) B6143465
theorem B32735015 : Blo 1008601 32735015 := bstep (se 1 (by rfl) ⟨24551261, by rfl⟩ : syracuseStep 32735015 = 49102523) B49102523
theorem B3407831 : Blo 1008601 3407831 := bstep (se 1 (by rfl) ⟨2555873, by rfl⟩ : syracuseStep 3407831 = 5111747) B5111747
theorem B1703963 : Blo 1008601 1703963 := bstep (se 1 (by rfl) ⟨1277972, by rfl⟩ : syracuseStep 1703963 = 2555945) B2555945
theorem B3408317 : Blo 1008601 3408317 := bstep (se 3 (by rfl) ⟨639059, by rfl⟩ : syracuseStep 3408317 = 1278119) B1278119
theorem B2556755 : Blo 1008601 2556755 := bstep (se 1 (by rfl) ⟨1917566, by rfl⟩ : syracuseStep 2556755 = 3835133) B3835133
theorem B3409127 : Blo 1008601 3409127 := bstep (se 1 (by rfl) ⟨2556845, by rfl⟩ : syracuseStep 3409127 = 5113691) B5113691
theorem B2557241 : Blo 1008601 2557241 := bstep (se 2 (by rfl) ⟨958965, by rfl⟩ : syracuseStep 2557241 = 1917931) B1917931
theorem B3409235 : Blo 1008601 3409235 := bstep (se 1 (by rfl) ⟨2556926, by rfl⟩ : syracuseStep 3409235 = 5113853) B5113853
theorem B1705819 : Blo 1008601 1705819 := bstep (se 1 (by rfl) ⟨1279364, by rfl⟩ : syracuseStep 1705819 = 2558729) B2558729
theorem B1705961 : Blo 1008601 1705961 := bstep (se 2 (by rfl) ⟨639735, by rfl⟩ : syracuseStep 1705961 = 1279471) B1279471
theorem B1280063 : Blo 1008601 1280063 := bstep (se 1 (by rfl) ⟨960047, by rfl⟩ : syracuseStep 1280063 = 1920095) B1920095
theorem B2558263 : Blo 1008601 2558263 := bstep (se 1 (by rfl) ⟨1918697, by rfl⟩ : syracuseStep 2558263 = 3837395) B3837395
theorem B12290575 : Blo 1008601 12290575 := bstep (se 1 (by rfl) ⟨9217931, by rfl⟩ : syracuseStep 12290575 = 18435863) B18435863
theorem B2558567 : Blo 1008601 2558567 := bstep (se 1 (by rfl) ⟨1918925, by rfl⟩ : syracuseStep 2558567 = 3837851) B3837851
theorem B7671023 : Blo 1008601 7671023 := bstep (se 1 (by rfl) ⟨5753267, by rfl⟩ : syracuseStep 7671023 = 11506535) B11506535
theorem B16420441 : Blo 1008601 16420441 := bstep (se 2 (by rfl) ⟨6157665, by rfl⟩ : syracuseStep 16420441 = 12315331) B12315331
theorem B8196079 : Blo 1008601 8196079 := bstep (se 1 (by rfl) ⟨6147059, by rfl⟩ : syracuseStep 8196079 = 12294119) B12294119
theorem B5115959 : Blo 1008601 5115959 := bstep (se 1 (by rfl) ⟨3836969, by rfl⟩ : syracuseStep 5115959 = 7673939) B7673939
theorem B10359211 : Blo 1008601 10359211 := bstep (se 1 (by rfl) ⟨7769408, by rfl⟩ : syracuseStep 10359211 = 15538817) B15538817
theorem B1708735 : Blo 1008601 1708735 := bstep (se 1 (by rfl) ⟨1281551, by rfl⟩ : syracuseStep 1708735 = 2563103) B2563103
theorem B2560967 : Blo 1008601 2560967 := bstep (se 1 (by rfl) ⟨1920725, by rfl⟩ : syracuseStep 2560967 = 3841451) B3841451
theorem B14587411 : Blo 1008601 14587411 := bstep (se 1 (by rfl) ⟨10940558, by rfl⟩ : syracuseStep 14587411 = 21881117) B21881117
theorem B3413609 : Blo 1008601 3413609 := bstep (se 2 (by rfl) ⟨1280103, by rfl⟩ : syracuseStep 3413609 = 2560207) B2560207
theorem B3282809 : Blo 1008601 3282809 := bstep (se 2 (by rfl) ⟨1231053, by rfl⟩ : syracuseStep 3282809 = 2462107) B2462107
theorem B8755199 : Blo 1008601 8755199 := bstep (se 1 (by rfl) ⟨6566399, by rfl⟩ : syracuseStep 8755199 = 13132799) B13132799
theorem B1513679 : Blo 1008601 1513679 := bstep (se 1 (by rfl) ⟨1135259, by rfl⟩ : syracuseStep 1513679 = 2270519) B2270519
theorem B65608055 : Blo 1008601 65608055 := bstep (se 1 (by rfl) ⟨49206041, by rfl⟩ : syracuseStep 65608055 = 98412083) B98412083
theorem B21830087 : Blo 1008601 21830087 := bstep (se 1 (by rfl) ⟨16372565, by rfl⟩ : syracuseStep 21830087 = 32745131) B32745131
theorem B7674425 : Blo 1008601 7674425 := bstep (se 2 (by rfl) ⟨2877909, by rfl⟩ : syracuseStep 7674425 = 5755819) B5755819
theorem B3414689 : Blo 1008601 3414689 := bstep (se 2 (by rfl) ⟨1280508, by rfl⟩ : syracuseStep 3414689 = 2561017) B2561017
theorem B5118713 : Blo 1008601 5118713 := bstep (se 2 (by rfl) ⟨1919517, by rfl⟩ : syracuseStep 5118713 = 3839035) B3839035
theorem B1514603 : Blo 1008601 1514603 := bstep (se 1 (by rfl) ⟨1135952, by rfl⟩ : syracuseStep 1514603 = 2271905) B2271905
theorem B1514663 : Blo 1008601 1514663 := bstep (se 1 (by rfl) ⟨1135997, by rfl⟩ : syracuseStep 1514663 = 2271995) B2271995
theorem B3416147 : Blo 1008601 3416147 := bstep (se 1 (by rfl) ⟨2562110, by rfl⟩ : syracuseStep 3416147 = 5124221) B5124221
theorem B2728039 : Blo 1008601 2728039 := bstep (se 1 (by rfl) ⟨2046029, by rfl⟩ : syracuseStep 2728039 = 4092059) B4092059
theorem B1515815 : Blo 1008601 1515815 := bstep (se 1 (by rfl) ⟨1136861, by rfl⟩ : syracuseStep 1515815 = 2273723) B2273723
theorem B2269511 : Blo 1008601 2269511 := bstep (se 1 (by rfl) ⟨1702133, by rfl⟩ : syracuseStep 2269511 = 3404267) B3404267
theorem B2269727 : Blo 1008601 2269727 := bstep (se 1 (by rfl) ⟨1702295, by rfl⟩ : syracuseStep 2269727 = 3404591) B3404591
theorem B2270447 : Blo 1008601 2270447 := bstep (se 1 (by rfl) ⟨1702835, by rfl⟩ : syracuseStep 2270447 = 3405671) B3405671
theorem B1516799 : Blo 1008601 1516799 := bstep (se 1 (by rfl) ⟨1137599, by rfl⟩ : syracuseStep 1516799 = 2275199) B2275199
theorem B2270591 : Blo 1008601 2270591 := bstep (se 1 (by rfl) ⟨1702943, by rfl⟩ : syracuseStep 2270591 = 3405887) B3405887
theorem B11675177 : Blo 1008601 11675177 := bstep (se 2 (by rfl) ⟨4378191, by rfl⟩ : syracuseStep 11675177 = 8756383) B8756383
theorem B1616159 : Blo 1008601 1616159 := bstep (se 1 (by rfl) ⟨1212119, by rfl⟩ : syracuseStep 1616159 = 2424239) B2424239
theorem B1517945 : Blo 1008601 1517945 := bstep (se 2 (by rfl) ⟨569229, by rfl⟩ : syracuseStep 1517945 = 1138459) B1138459
theorem B2271887 : Blo 1008601 2271887 := bstep (se 1 (by rfl) ⟨1703915, by rfl⟩ : syracuseStep 2271887 = 3407831) B3407831
theorem B14756509 : Blo 1008601 14756509 := bstep (se 3 (by rfl) ⟨2766845, by rfl⟩ : syracuseStep 14756509 = 5533691) B5533691
theorem B1518311 : Blo 1008601 1518311 := bstep (se 1 (by rfl) ⟨1138733, by rfl⟩ : syracuseStep 1518311 = 2277467) B2277467
theorem B1518503 : Blo 1008601 1518503 := bstep (se 1 (by rfl) ⟨1138877, by rfl⟩ : syracuseStep 1518503 = 2277755) B2277755
theorem B2272265 : Blo 1008601 2272265 := bstep (se 2 (by rfl) ⟨852099, by rfl⟩ : syracuseStep 2272265 = 1704199) B1704199
theorem B5123411 : Blo 1008601 5123411 := bstep (se 1 (by rfl) ⟨3842558, by rfl⟩ : syracuseStep 5123411 = 7685117) B7685117
theorem B2273705 : Blo 1008601 2273705 := bstep (se 2 (by rfl) ⟨852639, by rfl⟩ : syracuseStep 2273705 = 1705279) B1705279
theorem B44348107 : Blo 1008601 44348107 := bstep (se 1 (by rfl) ⟨33261080, by rfl⟩ : syracuseStep 44348107 = 66522161) B66522161
theorem B2274047 : Blo 1008601 2274047 := bstep (se 1 (by rfl) ⟨1705535, by rfl⟩ : syracuseStep 2274047 = 3411071) B3411071
theorem B2275307 : Blo 1008601 2275307 := bstep (se 1 (by rfl) ⟨1706480, by rfl⟩ : syracuseStep 2275307 = 3412961) B3412961
theorem B7682201 : Blo 1008601 7682201 := bstep (se 2 (by rfl) ⟨2880825, by rfl⟩ : syracuseStep 7682201 = 5761651) B5761651
theorem B7682687 : Blo 1008601 7682687 := bstep (se 1 (by rfl) ⟨5762015, by rfl⟩ : syracuseStep 7682687 = 11524031) B11524031
theorem B31965317 : Blo 1008601 31965317 := bstep (se 4 (by rfl) ⟨2996748, by rfl⟩ : syracuseStep 31965317 = 5993497) B5993497
theorem B6473915 : Blo 1008601 6473915 := bstep (se 1 (by rfl) ⟨4855436, by rfl⟩ : syracuseStep 6473915 = 9710873) B9710873
theorem B5459035 : Blo 1008601 5459035 := bstep (se 1 (by rfl) ⟨4094276, by rfl⟩ : syracuseStep 5459035 = 8188553) B8188553
theorem B16371335 : Blo 1008601 16371335 := bstep (se 1 (by rfl) ⟨12278501, by rfl⟩ : syracuseStep 16371335 = 24557003) B24557003
theorem B6999803 : Blo 1008601 6999803 := bstep (se 1 (by rfl) ⟨5249852, by rfl⟩ : syracuseStep 6999803 = 10499705) B10499705
theorem B20729843 : Blo 1008601 20729843 := bstep (se 1 (by rfl) ⟨15547382, by rfl⟩ : syracuseStep 20729843 = 31094765) B31094765
theorem B16404551 : Blo 1008601 16404551 := bstep (se 1 (by rfl) ⟨12303413, by rfl⟩ : syracuseStep 16404551 = 24606827) B24606827
theorem B7688519 : Blo 1008601 7688519 := bstep (se 1 (by rfl) ⟨5766389, by rfl⟩ : syracuseStep 7688519 = 11532779) B11532779
theorem B4313483 : Blo 1008601 4313483 := bstep (se 1 (by rfl) ⟨3235112, by rfl⟩ : syracuseStep 4313483 = 6470225) B6470225
theorem B3461885 : Blo 1008601 3461885 := bstep (se 3 (by rfl) ⟨649103, by rfl⟩ : syracuseStep 3461885 = 1298207) B1298207
theorem B5460857 : Blo 1008601 5460857 := bstep (se 2 (by rfl) ⟨2047821, by rfl⟩ : syracuseStep 5460857 = 4095643) B4095643
theorem B3234907 : Blo 1008601 3234907 := bstep (se 1 (by rfl) ⟨2426180, by rfl⟩ : syracuseStep 3234907 = 4852361) B4852361
theorem B14572649 : Blo 1008601 14572649 := bstep (se 2 (by rfl) ⟨5464743, by rfl⟩ : syracuseStep 14572649 = 10929487) B10929487
theorem B1138279 : Blo 1008601 1138279 := bstep (se 1 (by rfl) ⟨853709, by rfl⟩ : syracuseStep 1138279 = 1707419) B1707419
theorem B3235727 : Blo 1008601 3235727 := bstep (se 1 (by rfl) ⟨2426795, by rfl⟩ : syracuseStep 3235727 = 4853591) B4853591
theorem B11493413 : Blo 1008601 11493413 := bstep (se 4 (by rfl) ⟨1077507, by rfl⟩ : syracuseStep 11493413 = 2155015) B2155015
theorem B1008607 : Blo 1008601 1008607 := bstep (se 1 (by rfl) ⟨756455, by rfl⟩ : syracuseStep 1008607 = 1512911) B1512911
theorem B3237239 : Blo 1008601 3237239 := bstep (se 1 (by rfl) ⟨2427929, by rfl⟩ : syracuseStep 3237239 = 4855859) B4855859
theorem B9201871 : Blo 1008601 9201871 := bstep (se 1 (by rfl) ⟨6901403, by rfl⟩ : syracuseStep 9201871 = 13802807) B13802807
theorem B1009991 : Blo 1008601 1009991 := bstep (se 1 (by rfl) ⟨757493, by rfl⟩ : syracuseStep 1009991 = 1514987) B1514987
theorem B49212269 : Blo 1008601 49212269 := bstep (se 3 (by rfl) ⟨9227300, by rfl⟩ : syracuseStep 49212269 = 18454601) B18454601
theorem B1010843 : Blo 1008601 1010843 := bstep (se 1 (by rfl) ⟨758132, by rfl⟩ : syracuseStep 1010843 = 1516265) B1516265
theorem B2879003 : Blo 1008601 2879003 := bstep (se 1 (by rfl) ⟨2159252, by rfl⟩ : syracuseStep 2879003 = 4318505) B4318505
theorem B1011227 : Blo 1008601 1011227 := bstep (se 1 (by rfl) ⟨758420, by rfl⟩ : syracuseStep 1011227 = 1516841) B1516841
theorem B23359013 : Blo 1008601 23359013 := bstep (se 4 (by rfl) ⟨2189907, by rfl⟩ : syracuseStep 23359013 = 4379815) B4379815
theorem B11529863 : Blo 1008601 11529863 := bstep (se 1 (by rfl) ⟨8647397, by rfl⟩ : syracuseStep 11529863 = 17294795) B17294795
theorem B1011355 : Blo 1008601 1011355 := bstep (se 1 (by rfl) ⟨758516, by rfl⟩ : syracuseStep 1011355 = 1517033) B1517033
theorem B1012159 : Blo 1008601 1012159 := bstep (se 1 (by rfl) ⟨759119, by rfl⟩ : syracuseStep 1012159 = 1518239) B1518239
theorem B3404969 : Blo 1008601 3404969 := bstep (se 2 (by rfl) ⟨1276863, by rfl⟩ : syracuseStep 3404969 = 2553727) B2553727
theorem B3405023 : Blo 1008601 3405023 := bstep (se 1 (by rfl) ⟨2553767, by rfl⟩ : syracuseStep 3405023 = 5107535) B5107535
theorem B94533277 : Blo 1008601 94533277 := bstep (se 3 (by rfl) ⟨17724989, by rfl⟩ : syracuseStep 94533277 = 35449979) B35449979
theorem B17987345 : Blo 1008601 17987345 := bstep (se 2 (by rfl) ⟨6745254, by rfl⟩ : syracuseStep 17987345 = 13490509) B13490509
theorem B9730169 : Blo 1008601 9730169 := bstep (se 2 (by rfl) ⟨3648813, by rfl⟩ : syracuseStep 9730169 = 7297627) B7297627
theorem B6487037 : Blo 1008601 6487037 := bstep (se 3 (by rfl) ⟨1216319, by rfl⟩ : syracuseStep 6487037 = 2432639) B2432639
theorem B1440937 : Blo 1008601 1440937 := bstep (se 2 (by rfl) ⟨540351, by rfl⟩ : syracuseStep 1440937 = 1080703) B1080703
theorem B2882729 : Blo 1008601 2882729 := bstep (se 2 (by rfl) ⟨1081023, by rfl⟩ : syracuseStep 2882729 = 2162047) B2162047
theorem B28081799 : Blo 1008601 28081799 := bstep (se 1 (by rfl) ⟨21061349, by rfl⟩ : syracuseStep 28081799 = 42122699) B42122699
theorem B21823343 : Blo 1008601 21823343 := bstep (se 1 (by rfl) ⟨16367507, by rfl⟩ : syracuseStep 21823343 = 32735015) B32735015
theorem B3637385 : Blo 1008601 3637385 := bstep (se 2 (by rfl) ⟨1364019, by rfl⟩ : syracuseStep 3637385 = 2728039) B2728039
theorem B1704503 : Blo 1008601 1704503 := bstep (se 1 (by rfl) ⟨1278377, by rfl⟩ : syracuseStep 1704503 = 2556755) B2556755
theorem B1704827 : Blo 1008601 1704827 := bstep (se 1 (by rfl) ⟨1278620, by rfl⟩ : syracuseStep 1704827 = 2557241) B2557241
theorem B1705711 : Blo 1008601 1705711 := bstep (se 1 (by rfl) ⟨1279283, by rfl⟩ : syracuseStep 1705711 = 2558567) B2558567
theorem B5114015 : Blo 1008601 5114015 := bstep (se 1 (by rfl) ⟨3835511, by rfl⟩ : syracuseStep 5114015 = 7671023) B7671023
theorem B3410639 : Blo 1008601 3410639 := bstep (se 1 (by rfl) ⟨2557979, by rfl⟩ : syracuseStep 3410639 = 5115959) B5115959
theorem B3411017 : Blo 1008601 3411017 := bstep (se 2 (by rfl) ⟨1279131, by rfl⟩ : syracuseStep 3411017 = 2558263) B2558263
theorem B3640571 : Blo 1008601 3640571 := bstep (se 1 (by rfl) ⟨2730428, by rfl⟩ : syracuseStep 3640571 = 5460857) B5460857
theorem B1707311 : Blo 1008601 1707311 := bstep (se 1 (by rfl) ⟨1280483, by rfl⟩ : syracuseStep 1707311 = 2560967) B2560967
theorem B16387433 : Blo 1008601 16387433 := bstep (se 2 (by rfl) ⟨6145287, by rfl⟩ : syracuseStep 16387433 = 12290575) B12290575
theorem B5836799 : Blo 1008601 5836799 := bstep (se 1 (by rfl) ⟨4377599, by rfl⟩ : syracuseStep 5836799 = 8755199) B8755199
theorem B7278713 : Blo 1008601 7278713 := bstep (se 2 (by rfl) ⟨2729517, by rfl⟩ : syracuseStep 7278713 = 5459035) B5459035
theorem B14553391 : Blo 1008601 14553391 := bstep (se 1 (by rfl) ⟨10915043, by rfl⟩ : syracuseStep 14553391 = 21830087) B21830087
theorem B5116283 : Blo 1008601 5116283 := bstep (se 1 (by rfl) ⟨3837212, by rfl⟩ : syracuseStep 5116283 = 7674425) B7674425
theorem B3412475 : Blo 1008601 3412475 := bstep (se 1 (by rfl) ⟨2559356, by rfl⟩ : syracuseStep 3412475 = 5118713) B5118713
theorem B21893921 : Blo 1008601 21893921 := bstep (se 2 (by rfl) ⟨8210220, by rfl⟩ : syracuseStep 21893921 = 16420441) B16420441
theorem B8754157 : Blo 1008601 8754157 := bstep (se 3 (by rfl) ⟨1641404, by rfl⟩ : syracuseStep 8754157 = 3282809) B3282809
theorem B3413501 : Blo 1008601 3413501 := bstep (se 3 (by rfl) ⟨640031, by rfl⟩ : syracuseStep 3413501 = 1280063) B1280063
theorem B1513007 : Blo 1008601 1513007 := bstep (se 1 (by rfl) ⟨1134755, by rfl⟩ : syracuseStep 1513007 = 2269511) B2269511
theorem B1513151 : Blo 1008601 1513151 := bstep (se 1 (by rfl) ⟨1134863, by rfl⟩ : syracuseStep 1513151 = 2269727) B2269727
theorem B1513631 : Blo 1008601 1513631 := bstep (se 1 (by rfl) ⟨1135223, by rfl⟩ : syracuseStep 1513631 = 2270447) B2270447
theorem B1513727 : Blo 1008601 1513727 := bstep (se 1 (by rfl) ⟨1135295, by rfl⟩ : syracuseStep 1513727 = 2270591) B2270591
theorem B1514591 : Blo 1008601 1514591 := bstep (se 1 (by rfl) ⟨1135943, by rfl⟩ : syracuseStep 1514591 = 2271887) B2271887
theorem B32808179 : Blo 1008601 32808179 := bstep (se 1 (by rfl) ⟨24606134, by rfl⟩ : syracuseStep 32808179 = 49212269) B49212269
theorem B1514843 : Blo 1008601 1514843 := bstep (se 1 (by rfl) ⟨1136132, by rfl⟩ : syracuseStep 1514843 = 2272265) B2272265
theorem B3415607 : Blo 1008601 3415607 := bstep (se 1 (by rfl) ⟨2561705, by rfl⟩ : syracuseStep 3415607 = 5123411) B5123411
theorem B15572675 : Blo 1008601 15572675 := bstep (se 1 (by rfl) ⟨11679506, by rfl⟩ : syracuseStep 15572675 = 23359013) B23359013
theorem B1515803 : Blo 1008601 1515803 := bstep (se 1 (by rfl) ⟨1136852, by rfl⟩ : syracuseStep 1515803 = 2273705) B2273705
theorem B1516031 : Blo 1008601 1516031 := bstep (se 1 (by rfl) ⟨1137023, by rfl⟩ : syracuseStep 1516031 = 2274047) B2274047
theorem B2269979 : Blo 1008601 2269979 := bstep (se 1 (by rfl) ⟨1702484, by rfl⟩ : syracuseStep 2269979 = 3404969) B3404969
theorem B2270015 : Blo 1008601 2270015 := bstep (se 1 (by rfl) ⟨1702511, by rfl⟩ : syracuseStep 2270015 = 3405023) B3405023
theorem B1516871 : Blo 1008601 1516871 := bstep (se 1 (by rfl) ⟨1137653, by rfl⟩ : syracuseStep 1516871 = 2275307) B2275307
theorem B7677341 : Blo 1008601 7677341 := bstep (se 3 (by rfl) ⟨1439501, by rfl⟩ : syracuseStep 7677341 = 2879003) B2879003
theorem B5121467 : Blo 1008601 5121467 := bstep (se 1 (by rfl) ⟨3841100, by rfl⟩ : syracuseStep 5121467 = 7682201) B7682201
theorem B43656893 : Blo 1008601 43656893 := bstep (se 3 (by rfl) ⟨8185667, by rfl⟩ : syracuseStep 43656893 = 16371335) B16371335
theorem B5121791 : Blo 1008601 5121791 := bstep (se 1 (by rfl) ⟨3841343, by rfl⟩ : syracuseStep 5121791 = 7682687) B7682687
theorem B1517705 : Blo 1008601 1517705 := bstep (se 2 (by rfl) ⟨569139, by rfl⟩ : syracuseStep 1517705 = 1138279) B1138279
theorem B8628605 : Blo 1008601 8628605 := bstep (se 3 (by rfl) ⟨1617863, by rfl⟩ : syracuseStep 8628605 = 3235727) B3235727
theorem B18721199 : Blo 1008601 18721199 := bstep (se 1 (by rfl) ⟨14040899, by rfl⟩ : syracuseStep 18721199 = 28081799) B28081799
theorem B2272211 : Blo 1008601 2272211 := bstep (se 1 (by rfl) ⟨1704158, by rfl⟩ : syracuseStep 2272211 = 3408317) B3408317
theorem B2272751 : Blo 1008601 2272751 := bstep (se 1 (by rfl) ⟨1704563, by rfl⟩ : syracuseStep 2272751 = 3409127) B3409127
theorem B2272823 : Blo 1008601 2272823 := bstep (se 1 (by rfl) ⟨1704617, by rfl⟩ : syracuseStep 2272823 = 3409235) B3409235
theorem B340963381 : Blo 1008601 340963381 := bstep (se 5 (by rfl) ⟨15982658, by rfl⟩ : syracuseStep 340963381 = 31965317) B31965317
theorem B2274425 : Blo 1008601 2274425 := bstep (se 2 (by rfl) ⟨852909, by rfl⟩ : syracuseStep 2274425 = 1705819) B1705819
theorem B4666535 : Blo 1008601 4666535 := bstep (se 1 (by rfl) ⟨3499901, by rfl⟩ : syracuseStep 4666535 = 6999803) B6999803
theorem B5125679 : Blo 1008601 5125679 := bstep (se 1 (by rfl) ⟨3844259, by rfl⟩ : syracuseStep 5125679 = 7688519) B7688519
theorem B12269161 : Blo 1008601 12269161 := bstep (se 2 (by rfl) ⟨4600935, by rfl⟩ : syracuseStep 12269161 = 9201871) B9201871
theorem B2307923 : Blo 1008601 2307923 := bstep (se 1 (by rfl) ⟨1730942, by rfl⟩ : syracuseStep 2307923 = 3461885) B3461885
theorem B19675345 : Blo 1008601 19675345 := bstep (se 2 (by rfl) ⟨7378254, by rfl⟩ : syracuseStep 19675345 = 14756509) B14756509
theorem B2275739 : Blo 1008601 2275739 := bstep (se 1 (by rfl) ⟨1706804, by rfl⟩ : syracuseStep 2275739 = 3413609) B3413609
theorem B2276459 : Blo 1008601 2276459 := bstep (se 1 (by rfl) ⟨1707344, by rfl⟩ : syracuseStep 2276459 = 3414689) B3414689
theorem B9715099 : Blo 1008601 9715099 := bstep (se 1 (by rfl) ⟨7286324, by rfl⟩ : syracuseStep 9715099 = 14572649) B14572649
theorem B10928105 : Blo 1008601 10928105 := bstep (se 2 (by rfl) ⟨4098039, by rfl⟩ : syracuseStep 10928105 = 8196079) B8196079
theorem B2277431 : Blo 1008601 2277431 := bstep (se 1 (by rfl) ⟨1708073, by rfl⟩ : syracuseStep 2277431 = 3416147) B3416147
theorem B13812281 : Blo 1008601 13812281 := bstep (se 2 (by rfl) ⟨5179605, by rfl⟩ : syracuseStep 13812281 = 10359211) B10359211
theorem B4309757 : Blo 1008601 4309757 := bstep (se 3 (by rfl) ⟨808079, by rfl⟩ : syracuseStep 4309757 = 1616159) B1616159
theorem B2278313 : Blo 1008601 2278313 := bstep (se 2 (by rfl) ⟨854367, by rfl⟩ : syracuseStep 2278313 = 1708735) B1708735
theorem B59130809 : Blo 1008601 59130809 := bstep (se 2 (by rfl) ⟨22174053, by rfl⟩ : syracuseStep 59130809 = 44348107) B44348107
theorem B7783451 : Blo 1008601 7783451 := bstep (se 1 (by rfl) ⟨5837588, by rfl⟩ : syracuseStep 7783451 = 11675177) B11675177
theorem B19449881 : Blo 1008601 19449881 := bstep (se 2 (by rfl) ⟨7293705, by rfl⟩ : syracuseStep 19449881 = 14587411) B14587411
theorem B126044369 : Blo 1008601 126044369 := bstep (se 2 (by rfl) ⟨47266638, by rfl⟩ : syracuseStep 126044369 = 94533277) B94533277
theorem B7686575 : Blo 1008601 7686575 := bstep (se 1 (by rfl) ⟨5764931, by rfl⟩ : syracuseStep 7686575 = 11529863) B11529863
theorem B4313209 : Blo 1008601 4313209 := bstep (se 2 (by rfl) ⟨1617453, by rfl⟩ : syracuseStep 4313209 = 3234907) B3234907
theorem B1921249 : Blo 1008601 1921249 := bstep (se 2 (by rfl) ⟨720468, by rfl⟩ : syracuseStep 1921249 = 1440937) B1440937
theorem B1921819 : Blo 1008601 1921819 := bstep (se 1 (by rfl) ⟨1441364, by rfl⟩ : syracuseStep 1921819 = 2882729) B2882729
theorem B1135975 : Blo 1008601 1135975 := bstep (se 1 (by rfl) ⟨851981, by rfl⟩ : syracuseStep 1135975 = 1703963) B1703963
theorem B1137307 : Blo 1008601 1137307 := bstep (se 1 (by rfl) ⟨852980, by rfl⟩ : syracuseStep 1137307 = 1705961) B1705961
theorem B4315943 : Blo 1008601 4315943 := bstep (se 1 (by rfl) ⟨3236957, by rfl⟩ : syracuseStep 4315943 = 6473915) B6473915
theorem B13819895 : Blo 1008601 13819895 := bstep (se 1 (by rfl) ⟨10364921, by rfl⟩ : syracuseStep 13819895 = 20729843) B20729843
theorem B10936367 : Blo 1008601 10936367 := bstep (se 1 (by rfl) ⟨8202275, by rfl⟩ : syracuseStep 10936367 = 16404551) B16404551
theorem B2875655 : Blo 1008601 2875655 := bstep (se 1 (by rfl) ⟨2156741, by rfl⟩ : syracuseStep 2875655 = 4313483) B4313483
theorem B1009119 : Blo 1008601 1009119 := bstep (se 1 (by rfl) ⟨756839, by rfl⟩ : syracuseStep 1009119 = 1513679) B1513679
theorem B43738703 : Blo 1008601 43738703 := bstep (se 1 (by rfl) ⟨32804027, by rfl⟩ : syracuseStep 43738703 = 65608055) B65608055
theorem B1009735 : Blo 1008601 1009735 := bstep (se 1 (by rfl) ⟨757301, by rfl⟩ : syracuseStep 1009735 = 1514603) B1514603
theorem B1009775 : Blo 1008601 1009775 := bstep (se 1 (by rfl) ⟨757331, by rfl⟩ : syracuseStep 1009775 = 1514663) B1514663
theorem B7662275 : Blo 1008601 7662275 := bstep (se 1 (by rfl) ⟨5746706, by rfl⟩ : syracuseStep 7662275 = 11493413) B11493413
theorem B1010543 : Blo 1008601 1010543 := bstep (se 1 (by rfl) ⟨757907, by rfl⟩ : syracuseStep 1010543 = 1515815) B1515815
theorem B1011199 : Blo 1008601 1011199 := bstep (se 1 (by rfl) ⟨758399, by rfl⟩ : syracuseStep 1011199 = 1516799) B1516799
theorem B2158159 : Blo 1008601 2158159 := bstep (se 1 (by rfl) ⟨1618619, by rfl⟩ : syracuseStep 2158159 = 3237239) B3237239
theorem B1011963 : Blo 1008601 1011963 := bstep (se 1 (by rfl) ⟨758972, by rfl⟩ : syracuseStep 1011963 = 1517945) B1517945
theorem B1012207 : Blo 1008601 1012207 := bstep (se 1 (by rfl) ⟨759155, by rfl⟩ : syracuseStep 1012207 = 1518311) B1518311
theorem B1012335 : Blo 1008601 1012335 := bstep (se 1 (by rfl) ⟨759251, by rfl⟩ : syracuseStep 1012335 = 1518503) B1518503
theorem B11991563 : Blo 1008601 11991563 := bstep (se 1 (by rfl) ⟨8993672, by rfl⟩ : syracuseStep 11991563 = 17987345) B17987345
theorem B6486779 : Blo 1008601 6486779 := bstep (se 1 (by rfl) ⟨4865084, by rfl⟩ : syracuseStep 6486779 = 9730169) B9730169
theorem B4324691 : Blo 1008601 4324691 := bstep (se 1 (by rfl) ⟨3243518, by rfl⟩ : syracuseStep 4324691 = 6487037) B6487037
theorem B14548895 : Blo 1008601 14548895 := bstep (se 1 (by rfl) ⟨10911671, by rfl⟩ : syracuseStep 14548895 = 21823343) B21823343
theorem B2424923 : Blo 1008601 2424923 := bstep (se 1 (by rfl) ⟨1818692, by rfl⟩ : syracuseStep 2424923 = 3637385) B3637385
theorem B9208187 : Blo 1008601 9208187 := bstep (se 1 (by rfl) ⟨6906140, by rfl⟩ : syracuseStep 9208187 = 13812281) B13812281
theorem B39420539 : Blo 1008601 39420539 := bstep (se 1 (by rfl) ⟨29565404, by rfl⟩ : syracuseStep 39420539 = 59130809) B59130809
theorem B3409343 : Blo 1008601 3409343 := bstep (se 1 (by rfl) ⟨2557007, by rfl⟩ : syracuseStep 3409343 = 5114015) B5114015
theorem B49776373 : Blo 1008601 49776373 := bstep (se 5 (by rfl) ⟨2333267, by rfl⟩ : syracuseStep 49776373 = 4666535) B4666535
theorem B2427047 : Blo 1008601 2427047 := bstep (se 1 (by rfl) ⟨1820285, by rfl⟩ : syracuseStep 2427047 = 3640571) B3640571
theorem B4852475 : Blo 1008601 4852475 := bstep (se 1 (by rfl) ⟨3639356, by rfl⟩ : syracuseStep 4852475 = 7278713) B7278713
theorem B3410855 : Blo 1008601 3410855 := bstep (se 1 (by rfl) ⟨2558141, by rfl⟩ : syracuseStep 3410855 = 5116283) B5116283
theorem B9213263 : Blo 1008601 9213263 := bstep (se 1 (by rfl) ⟨6909947, by rfl⟩ : syracuseStep 9213263 = 13819895) B13819895
theorem B2561665 : Blo 1008601 2561665 := bstep (se 2 (by rfl) ⟨960624, by rfl⟩ : syracuseStep 2561665 = 1921249) B1921249
theorem B19404521 : Blo 1008601 19404521 := bstep (se 2 (by rfl) ⟨7276695, by rfl⟩ : syracuseStep 19404521 = 14553391) B14553391
theorem B1513319 : Blo 1008601 1513319 := bstep (se 1 (by rfl) ⟨1134989, by rfl⟩ : syracuseStep 1513319 = 2269979) B2269979
theorem B1513343 : Blo 1008601 1513343 := bstep (se 1 (by rfl) ⟨1135007, by rfl⟩ : syracuseStep 1513343 = 2270015) B2270015
theorem B5118227 : Blo 1008601 5118227 := bstep (se 1 (by rfl) ⟨3838670, by rfl⟩ : syracuseStep 5118227 = 7677341) B7677341
theorem B3414311 : Blo 1008601 3414311 := bstep (se 1 (by rfl) ⟨2560733, by rfl⟩ : syracuseStep 3414311 = 5121467) B5121467
theorem B2562425 : Blo 1008601 2562425 := bstep (se 2 (by rfl) ⟨960909, by rfl⟩ : syracuseStep 2562425 = 1921819) B1921819
theorem B29104595 : Blo 1008601 29104595 := bstep (se 1 (by rfl) ⟨21828446, by rfl⟩ : syracuseStep 29104595 = 43656893) B43656893
theorem B3414527 : Blo 1008601 3414527 := bstep (se 1 (by rfl) ⟨2560895, by rfl⟩ : syracuseStep 3414527 = 5121791) B5121791
theorem B11672209 : Blo 1008601 11672209 := bstep (se 2 (by rfl) ⟨4377078, by rfl⟩ : syracuseStep 11672209 = 8754157) B8754157
theorem B1514633 : Blo 1008601 1514633 := bstep (se 2 (by rfl) ⟨567987, by rfl⟩ : syracuseStep 1514633 = 1135975) B1135975
theorem B1514807 : Blo 1008601 1514807 := bstep (se 1 (by rfl) ⟨1136105, by rfl⟩ : syracuseStep 1514807 = 2272211) B2272211
theorem B16358881 : Blo 1008601 16358881 := bstep (se 2 (by rfl) ⟨6134580, by rfl⟩ : syracuseStep 16358881 = 12269161) B12269161
theorem B1515167 : Blo 1008601 1515167 := bstep (se 1 (by rfl) ⟨1136375, by rfl⟩ : syracuseStep 1515167 = 2272751) B2272751
theorem B1515215 : Blo 1008601 1515215 := bstep (se 1 (by rfl) ⟨1136411, by rfl⟩ : syracuseStep 1515215 = 2272823) B2272823
theorem B1516283 : Blo 1008601 1516283 := bstep (se 1 (by rfl) ⟨1137212, by rfl⟩ : syracuseStep 1516283 = 2274425) B2274425
theorem B1516409 : Blo 1008601 1516409 := bstep (se 2 (by rfl) ⟨568653, by rfl⟩ : syracuseStep 1516409 = 1137307) B1137307
theorem B3417119 : Blo 1008601 3417119 := bstep (se 1 (by rfl) ⟨2562839, by rfl⟩ : syracuseStep 3417119 = 5125679) B5125679
theorem B1517159 : Blo 1008601 1517159 := bstep (se 1 (by rfl) ⟨1137869, by rfl⟩ : syracuseStep 1517159 = 2275739) B2275739
theorem B41527133 : Blo 1008601 41527133 := bstep (se 3 (by rfl) ⟨7786337, by rfl⟩ : syracuseStep 41527133 = 15572675) B15572675
theorem B12953465 : Blo 1008601 12953465 := bstep (se 2 (by rfl) ⟨4857549, by rfl⟩ : syracuseStep 12953465 = 9715099) B9715099
theorem B1517639 : Blo 1008601 1517639 := bstep (se 1 (by rfl) ⟨1138229, by rfl⟩ : syracuseStep 1517639 = 2276459) B2276459
theorem B7285403 : Blo 1008601 7285403 := bstep (se 1 (by rfl) ⟨5464052, by rfl⟩ : syracuseStep 7285403 = 10928105) B10928105
theorem B1518287 : Blo 1008601 1518287 := bstep (se 1 (by rfl) ⟨1138715, by rfl⟩ : syracuseStep 1518287 = 2277431) B2277431
theorem B1518875 : Blo 1008601 1518875 := bstep (se 1 (by rfl) ⟨1139156, by rfl⟩ : syracuseStep 1518875 = 2278313) B2278313
theorem B5188967 : Blo 1008601 5188967 := bstep (se 1 (by rfl) ⟨3891725, by rfl⟩ : syracuseStep 5188967 = 7783451) B7783451
theorem B84029579 : Blo 1008601 84029579 := bstep (se 1 (by rfl) ⟨63022184, by rfl⟩ : syracuseStep 84029579 = 126044369) B126044369
theorem B5124383 : Blo 1008601 5124383 := bstep (se 1 (by rfl) ⟨3843287, by rfl⟩ : syracuseStep 5124383 = 7686575) B7686575
theorem B2273759 : Blo 1008601 2273759 := bstep (se 1 (by rfl) ⟨1705319, by rfl⟩ : syracuseStep 2273759 = 3410639) B3410639
theorem B2274011 : Blo 1008601 2274011 := bstep (se 1 (by rfl) ⟨1705508, by rfl⟩ : syracuseStep 2274011 = 3411017) B3411017
theorem B10924955 : Blo 1008601 10924955 := bstep (se 1 (by rfl) ⟨8193716, by rfl⟩ : syracuseStep 10924955 = 16387433) B16387433
theorem B2274281 : Blo 1008601 2274281 := bstep (se 2 (by rfl) ⟨852855, by rfl⟩ : syracuseStep 2274281 = 1705711) B1705711
theorem B2274983 : Blo 1008601 2274983 := bstep (se 1 (by rfl) ⟨1706237, by rfl⟩ : syracuseStep 2274983 = 3412475) B3412475
theorem B14595947 : Blo 1008601 14595947 := bstep (se 1 (by rfl) ⟨10946960, by rfl⟩ : syracuseStep 14595947 = 21893921) B21893921
theorem B2275667 : Blo 1008601 2275667 := bstep (se 1 (by rfl) ⟨1706750, by rfl⟩ : syracuseStep 2275667 = 3413501) B3413501
theorem B21872119 : Blo 1008601 21872119 := bstep (se 1 (by rfl) ⟨16404089, by rfl⟩ : syracuseStep 21872119 = 32808179) B32808179
theorem B2277071 : Blo 1008601 2277071 := bstep (se 1 (by rfl) ⟨1707803, by rfl⟩ : syracuseStep 2277071 = 3415607) B3415607
theorem B7290911 : Blo 1008601 7290911 := bstep (se 1 (by rfl) ⟨5468183, by rfl⟩ : syracuseStep 7290911 = 10936367) B10936367
theorem B5750945 : Blo 1008601 5750945 := bstep (se 2 (by rfl) ⟨2156604, by rfl⟩ : syracuseStep 5750945 = 4313209) B4313209
theorem B1917103 : Blo 1008601 1917103 := bstep (se 1 (by rfl) ⟨1437827, by rfl⟩ : syracuseStep 1917103 = 2875655) B2875655
theorem B5752403 : Blo 1008601 5752403 := bstep (se 1 (by rfl) ⟨4314302, by rfl⟩ : syracuseStep 5752403 = 8628605) B8628605
theorem B26233793 : Blo 1008601 26233793 := bstep (se 2 (by rfl) ⟨9837672, by rfl⟩ : syracuseStep 26233793 = 19675345) B19675345
theorem B1136335 : Blo 1008601 1136335 := bstep (se 1 (by rfl) ⟨852251, by rfl⟩ : syracuseStep 1136335 = 1704503) B1704503
theorem B2873171 : Blo 1008601 2873171 := bstep (se 1 (by rfl) ⟨2154878, by rfl⟩ : syracuseStep 2873171 = 4309757) B4309757
theorem B1136551 : Blo 1008601 1136551 := bstep (se 1 (by rfl) ⟨852413, by rfl⟩ : syracuseStep 1136551 = 1704827) B1704827
theorem B12966587 : Blo 1008601 12966587 := bstep (se 1 (by rfl) ⟨9724940, by rfl⟩ : syracuseStep 12966587 = 19449881) B19449881
theorem B1138207 : Blo 1008601 1138207 := bstep (se 1 (by rfl) ⟨853655, by rfl⟩ : syracuseStep 1138207 = 1707311) B1707311
theorem B3891199 : Blo 1008601 3891199 := bstep (se 1 (by rfl) ⟨2918399, by rfl⟩ : syracuseStep 3891199 = 5836799) B5836799
theorem B1008671 : Blo 1008601 1008671 := bstep (se 1 (by rfl) ⟨756503, by rfl⟩ : syracuseStep 1008671 = 1513007) B1513007
theorem B1008767 : Blo 1008601 1008767 := bstep (se 1 (by rfl) ⟨756575, by rfl⟩ : syracuseStep 1008767 = 1513151) B1513151
theorem B1009087 : Blo 1008601 1009087 := bstep (se 1 (by rfl) ⟨756815, by rfl⟩ : syracuseStep 1009087 = 1513631) B1513631
theorem B1009151 : Blo 1008601 1009151 := bstep (se 1 (by rfl) ⟨756863, by rfl⟩ : syracuseStep 1009151 = 1513727) B1513727
theorem B2877295 : Blo 1008601 2877295 := bstep (se 1 (by rfl) ⟨2157971, by rfl⟩ : syracuseStep 2877295 = 4315943) B4315943
theorem B1009727 : Blo 1008601 1009727 := bstep (se 1 (by rfl) ⟨757295, by rfl⟩ : syracuseStep 1009727 = 1514591) B1514591
theorem B2877545 : Blo 1008601 2877545 := bstep (se 2 (by rfl) ⟨1079079, by rfl⟩ : syracuseStep 2877545 = 2158159) B2158159
theorem B1009895 : Blo 1008601 1009895 := bstep (se 1 (by rfl) ⟨757421, by rfl⟩ : syracuseStep 1009895 = 1514843) B1514843
theorem B454617841 : Blo 1008601 454617841 := bstep (se 2 (by rfl) ⟨170481690, by rfl⟩ : syracuseStep 454617841 = 340963381) B340963381
theorem B1010535 : Blo 1008601 1010535 := bstep (se 1 (by rfl) ⟨757901, by rfl⟩ : syracuseStep 1010535 = 1515803) B1515803
theorem B1010687 : Blo 1008601 1010687 := bstep (se 1 (by rfl) ⟨758015, by rfl⟩ : syracuseStep 1010687 = 1516031) B1516031
theorem B1011247 : Blo 1008601 1011247 := bstep (se 1 (by rfl) ⟨758435, by rfl⟩ : syracuseStep 1011247 = 1516871) B1516871
theorem B29159135 : Blo 1008601 29159135 := bstep (se 1 (by rfl) ⟨21869351, by rfl⟩ : syracuseStep 29159135 = 43738703) B43738703
theorem B1011803 : Blo 1008601 1011803 := bstep (se 1 (by rfl) ⟨758852, by rfl⟩ : syracuseStep 1011803 = 1517705) B1517705
theorem B12480799 : Blo 1008601 12480799 := bstep (se 1 (by rfl) ⟨9360599, by rfl⟩ : syracuseStep 12480799 = 18721199) B18721199
theorem B5108183 : Blo 1008601 5108183 := bstep (se 1 (by rfl) ⟨3831137, by rfl⟩ : syracuseStep 5108183 = 7662275) B7662275
theorem B1538615 : Blo 1008601 1538615 := bstep (se 1 (by rfl) ⟨1153961, by rfl⟩ : syracuseStep 1538615 = 2307923) B2307923
theorem B7994375 : Blo 1008601 7994375 := bstep (se 1 (by rfl) ⟨5995781, by rfl⟩ : syracuseStep 7994375 = 11991563) B11991563
theorem B4324519 : Blo 1008601 4324519 := bstep (se 1 (by rfl) ⟨3243389, by rfl⟩ : syracuseStep 4324519 = 6486779) B6486779
theorem B2883127 : Blo 1008601 2883127 := bstep (se 1 (by rfl) ⟨2162345, by rfl⟩ : syracuseStep 2883127 = 4324691) B4324691
theorem B9699263 : Blo 1008601 9699263 := bstep (se 1 (by rfl) ⟨7274447, by rfl⟩ : syracuseStep 9699263 = 14548895) B14548895
theorem B3833963 : Blo 1008601 3833963 := bstep (se 1 (by rfl) ⟨2875472, by rfl⟩ : syracuseStep 3833963 = 5750945) B5750945
theorem B2556137 : Blo 1008601 2556137 := bstep (se 2 (by rfl) ⟨958551, by rfl⟩ : syracuseStep 2556137 = 1917103) B1917103
theorem B26280359 : Blo 1008601 26280359 := bstep (se 1 (by rfl) ⟨19710269, by rfl⟩ : syracuseStep 26280359 = 39420539) B39420539
theorem B3834935 : Blo 1008601 3834935 := bstep (se 1 (by rfl) ⟨2876201, by rfl⟩ : syracuseStep 3834935 = 5752403) B5752403
theorem B3836393 : Blo 1008601 3836393 := bstep (se 2 (by rfl) ⟨1438647, by rfl⟩ : syracuseStep 3836393 = 2877295) B2877295
theorem B3412151 : Blo 1008601 3412151 := bstep (se 1 (by rfl) ⟨2559113, by rfl⟩ : syracuseStep 3412151 = 5118227) B5118227
theorem B1708283 : Blo 1008601 1708283 := bstep (se 1 (by rfl) ⟨1281212, by rfl⟩ : syracuseStep 1708283 = 2562425) B2562425
theorem B19403063 : Blo 1008601 19403063 := bstep (se 1 (by rfl) ⟨14552297, by rfl⟩ : syracuseStep 19403063 = 29104595) B29104595
theorem B7673453 : Blo 1008601 7673453 := bstep (se 3 (by rfl) ⟨1438772, by rfl⟩ : syracuseStep 7673453 = 2877545) B2877545
theorem B4102973 : Blo 1008601 4102973 := bstep (se 3 (by rfl) ⟨769307, by rfl⟩ : syracuseStep 4102973 = 1538615) B1538615
theorem B4856935 : Blo 1008601 4856935 := bstep (se 1 (by rfl) ⟨3642701, by rfl⟩ : syracuseStep 4856935 = 7285403) B7285403
theorem B3415553 : Blo 1008601 3415553 := bstep (se 2 (by rfl) ⟨1280832, by rfl⟩ : syracuseStep 3415553 = 2561665) B2561665
theorem B1515113 : Blo 1008601 1515113 := bstep (se 2 (by rfl) ⟨568167, by rfl⟩ : syracuseStep 1515113 = 1136335) B1136335
theorem B19439423 : Blo 1008601 19439423 := bstep (se 1 (by rfl) ⟨14579567, by rfl⟩ : syracuseStep 19439423 = 29159135) B29159135
theorem B1515401 : Blo 1008601 1515401 := bstep (se 2 (by rfl) ⟨568275, by rfl⟩ : syracuseStep 1515401 = 1136551) B1136551
theorem B3416255 : Blo 1008601 3416255 := bstep (se 1 (by rfl) ⟨2562191, by rfl⟩ : syracuseStep 3416255 = 5124383) B5124383
theorem B1515839 : Blo 1008601 1515839 := bstep (se 1 (by rfl) ⟨1136879, by rfl⟩ : syracuseStep 1515839 = 2273759) B2273759
theorem B1516007 : Blo 1008601 1516007 := bstep (se 1 (by rfl) ⟨1137005, by rfl⟩ : syracuseStep 1516007 = 2274011) B2274011
theorem B7283303 : Blo 1008601 7283303 := bstep (se 1 (by rfl) ⟨5462477, by rfl⟩ : syracuseStep 7283303 = 10924955) B10924955
theorem B1516187 : Blo 1008601 1516187 := bstep (se 1 (by rfl) ⟨1137140, by rfl⟩ : syracuseStep 1516187 = 2274281) B2274281
theorem B1516655 : Blo 1008601 1516655 := bstep (se 1 (by rfl) ⟨1137491, by rfl⟩ : syracuseStep 1516655 = 2274983) B2274983
theorem B1517111 : Blo 1008601 1517111 := bstep (se 1 (by rfl) ⟨1137833, by rfl⟩ : syracuseStep 1517111 = 2275667) B2275667
theorem B1517609 : Blo 1008601 1517609 := bstep (se 2 (by rfl) ⟨569103, by rfl⟩ : syracuseStep 1517609 = 1138207) B1138207
theorem B3844169 : Blo 1008601 3844169 := bstep (se 2 (by rfl) ⟨1441563, by rfl⟩ : syracuseStep 3844169 = 2883127) B2883127
theorem B1518047 : Blo 1008601 1518047 := bstep (se 1 (by rfl) ⟨1138535, by rfl⟩ : syracuseStep 1518047 = 2277071) B2277071
theorem B6466175 : Blo 1008601 6466175 := bstep (se 1 (by rfl) ⟨4849631, by rfl⟩ : syracuseStep 6466175 = 9699263) B9699263
theorem B5188265 : Blo 1008601 5188265 := bstep (se 2 (by rfl) ⟨1945599, by rfl⟩ : syracuseStep 5188265 = 3891199) B3891199
theorem B1616615 : Blo 1008601 1616615 := bstep (se 1 (by rfl) ⟨1212461, by rfl⟩ : syracuseStep 1616615 = 2424923) B2424923
theorem B19442429 : Blo 1008601 19442429 := bstep (se 3 (by rfl) ⟨3645455, by rfl⟩ : syracuseStep 19442429 = 7290911) B7290911
theorem B6138791 : Blo 1008601 6138791 := bstep (se 1 (by rfl) ⟨4604093, by rfl⟩ : syracuseStep 6138791 = 9208187) B9208187
theorem B2272895 : Blo 1008601 2272895 := bstep (se 1 (by rfl) ⟨1704671, by rfl⟩ : syracuseStep 2272895 = 3409343) B3409343
theorem B1618031 : Blo 1008601 1618031 := bstep (se 1 (by rfl) ⟨1213523, by rfl⟩ : syracuseStep 1618031 = 2427047) B2427047
theorem B2273903 : Blo 1008601 2273903 := bstep (se 1 (by rfl) ⟨1705427, by rfl⟩ : syracuseStep 2273903 = 3410855) B3410855
theorem B66368497 : Blo 1008601 66368497 := bstep (se 2 (by rfl) ⟨24888186, by rfl⟩ : syracuseStep 66368497 = 49776373) B49776373
theorem B6142175 : Blo 1008601 6142175 := bstep (se 1 (by rfl) ⟨4606631, by rfl⟩ : syracuseStep 6142175 = 9213263) B9213263
theorem B606157121 : Blo 1008601 606157121 := bstep (se 2 (by rfl) ⟨227308920, by rfl⟩ : syracuseStep 606157121 = 454617841) B454617841
theorem B2276207 : Blo 1008601 2276207 := bstep (se 1 (by rfl) ⟨1707155, by rfl⟩ : syracuseStep 2276207 = 3414311) B3414311
theorem B2276351 : Blo 1008601 2276351 := bstep (se 1 (by rfl) ⟨1707263, by rfl⟩ : syracuseStep 2276351 = 3414527) B3414527
theorem B2278079 : Blo 1008601 2278079 := bstep (se 1 (by rfl) ⟨1708559, by rfl⟩ : syracuseStep 2278079 = 3417119) B3417119
theorem B8635643 : Blo 1008601 8635643 := bstep (se 1 (by rfl) ⟨6476732, by rfl⟩ : syracuseStep 8635643 = 12953465) B12953465
theorem B3459311 : Blo 1008601 3459311 := bstep (se 1 (by rfl) ⟨2594483, by rfl⟩ : syracuseStep 3459311 = 5188967) B5188967
theorem B56019719 : Blo 1008601 56019719 := bstep (se 1 (by rfl) ⟨42014789, by rfl⟩ : syracuseStep 56019719 = 84029579) B84029579
theorem B21811841 : Blo 1008601 21811841 := bstep (se 2 (by rfl) ⟨8179440, by rfl⟩ : syracuseStep 21811841 = 16358881) B16358881
theorem B5329583 : Blo 1008601 5329583 := bstep (se 1 (by rfl) ⟨3997187, by rfl⟩ : syracuseStep 5329583 = 7994375) B7994375
theorem B3234983 : Blo 1008601 3234983 := bstep (se 1 (by rfl) ⟨2426237, by rfl⟩ : syracuseStep 3234983 = 4852475) B4852475
theorem B17489195 : Blo 1008601 17489195 := bstep (se 1 (by rfl) ⟨13116896, by rfl⟩ : syracuseStep 17489195 = 26233793) B26233793
theorem B12936347 : Blo 1008601 12936347 := bstep (se 1 (by rfl) ⟨9702260, by rfl⟩ : syracuseStep 12936347 = 19404521) B19404521
theorem B1008879 : Blo 1008601 1008879 := bstep (se 1 (by rfl) ⟨756659, by rfl⟩ : syracuseStep 1008879 = 1513319) B1513319
theorem B1008895 : Blo 1008601 1008895 := bstep (se 1 (by rfl) ⟨756671, by rfl⟩ : syracuseStep 1008895 = 1513343) B1513343
theorem B8644391 : Blo 1008601 8644391 := bstep (se 1 (by rfl) ⟨6483293, by rfl⟩ : syracuseStep 8644391 = 12966587) B12966587
theorem B1009755 : Blo 1008601 1009755 := bstep (se 1 (by rfl) ⟨757316, by rfl⟩ : syracuseStep 1009755 = 1514633) B1514633
theorem B1009871 : Blo 1008601 1009871 := bstep (se 1 (by rfl) ⟨757403, by rfl⟩ : syracuseStep 1009871 = 1514807) B1514807
theorem B7661789 : Blo 1008601 7661789 := bstep (se 3 (by rfl) ⟨1436585, by rfl⟩ : syracuseStep 7661789 = 2873171) B2873171
theorem B1010111 : Blo 1008601 1010111 := bstep (se 1 (by rfl) ⟨757583, by rfl⟩ : syracuseStep 1010111 = 1515167) B1515167
theorem B1010143 : Blo 1008601 1010143 := bstep (se 1 (by rfl) ⟨757607, by rfl⟩ : syracuseStep 1010143 = 1515215) B1515215
theorem B16641065 : Blo 1008601 16641065 := bstep (se 2 (by rfl) ⟨6240399, by rfl⟩ : syracuseStep 16641065 = 12480799) B12480799
theorem B1010855 : Blo 1008601 1010855 := bstep (se 1 (by rfl) ⟨758141, by rfl⟩ : syracuseStep 1010855 = 1516283) B1516283
theorem B1010939 : Blo 1008601 1010939 := bstep (se 1 (by rfl) ⟨758204, by rfl⟩ : syracuseStep 1010939 = 1516409) B1516409
theorem B1011439 : Blo 1008601 1011439 := bstep (se 1 (by rfl) ⟨758579, by rfl⟩ : syracuseStep 1011439 = 1517159) B1517159
theorem B27684755 : Blo 1008601 27684755 := bstep (se 1 (by rfl) ⟨20763566, by rfl⟩ : syracuseStep 27684755 = 41527133) B41527133
theorem B1011759 : Blo 1008601 1011759 := bstep (se 1 (by rfl) ⟨758819, by rfl⟩ : syracuseStep 1011759 = 1517639) B1517639
theorem B1012191 : Blo 1008601 1012191 := bstep (se 1 (by rfl) ⟨759143, by rfl⟩ : syracuseStep 1012191 = 1518287) B1518287
theorem B1012583 : Blo 1008601 1012583 := bstep (se 1 (by rfl) ⟨759437, by rfl⟩ : syracuseStep 1012583 = 1518875) B1518875
theorem B3405455 : Blo 1008601 3405455 := bstep (se 1 (by rfl) ⟨2554091, by rfl⟩ : syracuseStep 3405455 = 5108183) B5108183
theorem B15562945 : Blo 1008601 15562945 := bstep (se 2 (by rfl) ⟨5836104, by rfl⟩ : syracuseStep 15562945 = 11672209) B11672209
theorem B9730631 : Blo 1008601 9730631 := bstep (se 1 (by rfl) ⟨7297973, by rfl⟩ : syracuseStep 9730631 = 14595947) B14595947
theorem B5766025 : Blo 1008601 5766025 := bstep (se 2 (by rfl) ⟨2162259, by rfl⟩ : syracuseStep 5766025 = 4324519) B4324519
theorem B29162825 : Blo 1008601 29162825 := bstep (se 2 (by rfl) ⟨10936059, by rfl⟩ : syracuseStep 29162825 = 21872119) B21872119
theorem B2555975 : Blo 1008601 2555975 := bstep (se 1 (by rfl) ⟨1916981, by rfl⟩ : syracuseStep 2555975 = 3833963) B3833963
theorem B1704091 : Blo 1008601 1704091 := bstep (se 1 (by rfl) ⟨1278068, by rfl⟩ : syracuseStep 1704091 = 2556137) B2556137
theorem B2556623 : Blo 1008601 2556623 := bstep (se 1 (by rfl) ⟨1917467, by rfl⟩ : syracuseStep 2556623 = 3834935) B3834935
theorem B2557595 : Blo 1008601 2557595 := bstep (se 1 (by rfl) ⟨1918196, by rfl⟩ : syracuseStep 2557595 = 3836393) B3836393
theorem B5115635 : Blo 1008601 5115635 := bstep (se 1 (by rfl) ⟨3836726, by rfl⟩ : syracuseStep 5115635 = 7673453) B7673453
theorem B4855535 : Blo 1008601 4855535 := bstep (se 1 (by rfl) ⟨3641651, by rfl⟩ : syracuseStep 4855535 = 7283303) B7283303
theorem B8624231 : Blo 1008601 8624231 := bstep (se 1 (by rfl) ⟨6468173, by rfl⟩ : syracuseStep 8624231 = 12936347) B12936347
theorem B2562779 : Blo 1008601 2562779 := bstep (se 1 (by rfl) ⟨1922084, by rfl⟩ : syracuseStep 2562779 = 3844169) B3844169
theorem B1515263 : Blo 1008601 1515263 := bstep (se 1 (by rfl) ⟨1136447, by rfl⟩ : syracuseStep 1515263 = 2272895) B2272895
theorem B18456503 : Blo 1008601 18456503 := bstep (se 1 (by rfl) ⟨13842377, by rfl⟩ : syracuseStep 18456503 = 27684755) B27684755
theorem B44376173 : Blo 1008601 44376173 := bstep (se 3 (by rfl) ⟨8320532, by rfl⟩ : syracuseStep 44376173 = 16641065) B16641065
theorem B20750593 : Blo 1008601 20750593 := bstep (se 2 (by rfl) ⟨7781472, by rfl⟩ : syracuseStep 20750593 = 15562945) B15562945
theorem B1515935 : Blo 1008601 1515935 := bstep (se 1 (by rfl) ⟨1136951, by rfl⟩ : syracuseStep 1515935 = 2273903) B2273903
theorem B8626621 : Blo 1008601 8626621 := bstep (se 3 (by rfl) ⟨1617491, by rfl⟩ : syracuseStep 8626621 = 3234983) B3234983
theorem B2270303 : Blo 1008601 2270303 := bstep (se 1 (by rfl) ⟨1702727, by rfl⟩ : syracuseStep 2270303 = 3405455) B3405455
theorem B404104747 : Blo 1008601 404104747 := bstep (se 1 (by rfl) ⟨303078560, by rfl⟩ : syracuseStep 404104747 = 606157121) B606157121
theorem B1517471 : Blo 1008601 1517471 := bstep (se 1 (by rfl) ⟨1138103, by rfl⟩ : syracuseStep 1517471 = 2276207) B2276207
theorem B1517567 : Blo 1008601 1517567 := bstep (se 1 (by rfl) ⟨1138175, by rfl⟩ : syracuseStep 1517567 = 2276351) B2276351
theorem B19441883 : Blo 1008601 19441883 := bstep (se 1 (by rfl) ⟨14581412, by rfl⟩ : syracuseStep 19441883 = 29162825) B29162825
theorem B1518719 : Blo 1008601 1518719 := bstep (se 1 (by rfl) ⟨1139039, by rfl⟩ : syracuseStep 1518719 = 2278079) B2278079
theorem B2306207 : Blo 1008601 2306207 := bstep (se 1 (by rfl) ⟨1729655, by rfl⟩ : syracuseStep 2306207 = 3459311) B3459311
theorem B2274767 : Blo 1008601 2274767 := bstep (se 1 (by rfl) ⟨1706075, by rfl⟩ : syracuseStep 2274767 = 3412151) B3412151
theorem B3553055 : Blo 1008601 3553055 := bstep (se 1 (by rfl) ⟨2664791, by rfl⟩ : syracuseStep 3553055 = 5329583) B5329583
theorem B2735315 : Blo 1008601 2735315 := bstep (se 1 (by rfl) ⟨2051486, by rfl⟩ : syracuseStep 2735315 = 4102973) B4102973
theorem B2277035 : Blo 1008601 2277035 := bstep (se 1 (by rfl) ⟨1707776, by rfl⟩ : syracuseStep 2277035 = 3415553) B3415553
theorem B12959615 : Blo 1008601 12959615 := bstep (se 1 (by rfl) ⟨9719711, by rfl⟩ : syracuseStep 12959615 = 19439423) B19439423
theorem B2277503 : Blo 1008601 2277503 := bstep (se 1 (by rfl) ⟨1708127, by rfl⟩ : syracuseStep 2277503 = 3416255) B3416255
theorem B88491329 : Blo 1008601 88491329 := bstep (se 2 (by rfl) ⟨33184248, by rfl⟩ : syracuseStep 88491329 = 66368497) B66368497
theorem B4310783 : Blo 1008601 4310783 := bstep (se 1 (by rfl) ⟨3233087, by rfl⟩ : syracuseStep 4310783 = 6466175) B6466175
theorem B3458843 : Blo 1008601 3458843 := bstep (se 1 (by rfl) ⟨2594132, by rfl⟩ : syracuseStep 3458843 = 5188265) B5188265
theorem B12961619 : Blo 1008601 12961619 := bstep (se 1 (by rfl) ⟨9721214, by rfl⟩ : syracuseStep 12961619 = 19442429) B19442429
theorem B7688033 : Blo 1008601 7688033 := bstep (se 2 (by rfl) ⟨2883012, by rfl⟩ : syracuseStep 7688033 = 5766025) B5766025
theorem B6475913 : Blo 1008601 6475913 := bstep (se 2 (by rfl) ⟨2428467, by rfl⟩ : syracuseStep 6475913 = 4856935) B4856935
theorem B17520239 : Blo 1008601 17520239 := bstep (se 1 (by rfl) ⟨13140179, by rfl⟩ : syracuseStep 17520239 = 26280359) B26280359
theorem B5757095 : Blo 1008601 5757095 := bstep (se 1 (by rfl) ⟨4317821, by rfl⟩ : syracuseStep 5757095 = 8635643) B8635643
theorem B1138855 : Blo 1008601 1138855 := bstep (se 1 (by rfl) ⟨854141, by rfl⟩ : syracuseStep 1138855 = 1708283) B1708283
theorem B12935375 : Blo 1008601 12935375 := bstep (se 1 (by rfl) ⟨9701531, by rfl⟩ : syracuseStep 12935375 = 19403063) B19403063
theorem B14541227 : Blo 1008601 14541227 := bstep (se 1 (by rfl) ⟨10905920, by rfl⟩ : syracuseStep 14541227 = 21811841) B21811841
theorem B11659463 : Blo 1008601 11659463 := bstep (se 1 (by rfl) ⟨8744597, by rfl⟩ : syracuseStep 11659463 = 17489195) B17489195
theorem B1010075 : Blo 1008601 1010075 := bstep (se 1 (by rfl) ⟨757556, by rfl⟩ : syracuseStep 1010075 = 1515113) B1515113
theorem B1010267 : Blo 1008601 1010267 := bstep (se 1 (by rfl) ⟨757700, by rfl⟩ : syracuseStep 1010267 = 1515401) B1515401
theorem B1010559 : Blo 1008601 1010559 := bstep (se 1 (by rfl) ⟨757919, by rfl⟩ : syracuseStep 1010559 = 1515839) B1515839
theorem B1010671 : Blo 1008601 1010671 := bstep (se 1 (by rfl) ⟨758003, by rfl⟩ : syracuseStep 1010671 = 1516007) B1516007
theorem B1010791 : Blo 1008601 1010791 := bstep (se 1 (by rfl) ⟨758093, by rfl⟩ : syracuseStep 1010791 = 1516187) B1516187
theorem B1011103 : Blo 1008601 1011103 := bstep (se 1 (by rfl) ⟨758327, by rfl⟩ : syracuseStep 1011103 = 1516655) B1516655
theorem B1011407 : Blo 1008601 1011407 := bstep (se 1 (by rfl) ⟨758555, by rfl⟩ : syracuseStep 1011407 = 1517111) B1517111
theorem B5762927 : Blo 1008601 5762927 := bstep (se 1 (by rfl) ⟨4322195, by rfl⟩ : syracuseStep 5762927 = 8644391) B8644391
theorem B1011739 : Blo 1008601 1011739 := bstep (se 1 (by rfl) ⟨758804, by rfl⟩ : syracuseStep 1011739 = 1517609) B1517609
theorem B5107859 : Blo 1008601 5107859 := bstep (se 1 (by rfl) ⟨3830894, by rfl⟩ : syracuseStep 5107859 = 7661789) B7661789
theorem B1012031 : Blo 1008601 1012031 := bstep (se 1 (by rfl) ⟨759023, by rfl⟩ : syracuseStep 1012031 = 1518047) B1518047
theorem B1077743 : Blo 1008601 1077743 := bstep (se 1 (by rfl) ⟨808307, by rfl⟩ : syracuseStep 1077743 = 1616615) B1616615
theorem B4092527 : Blo 1008601 4092527 := bstep (se 1 (by rfl) ⟨3069395, by rfl⟩ : syracuseStep 4092527 = 6138791) B6138791
theorem B149385917 : Blo 1008601 149385917 := bstep (se 3 (by rfl) ⟨28009859, by rfl⟩ : syracuseStep 149385917 = 56019719) B56019719
theorem B1078687 : Blo 1008601 1078687 := bstep (se 1 (by rfl) ⟨809015, by rfl⟩ : syracuseStep 1078687 = 1618031) B1618031
theorem B4094783 : Blo 1008601 4094783 := bstep (se 1 (by rfl) ⟨3071087, by rfl⟩ : syracuseStep 4094783 = 6142175) B6142175
theorem B6487087 : Blo 1008601 6487087 := bstep (se 1 (by rfl) ⟨4865315, by rfl⟩ : syracuseStep 6487087 = 9730631) B9730631
theorem B1703983 : Blo 1008601 1703983 := bstep (se 1 (by rfl) ⟨1277987, by rfl⟩ : syracuseStep 1703983 = 2555975) B2555975
theorem B1704415 : Blo 1008601 1704415 := bstep (se 1 (by rfl) ⟨1278311, by rfl⟩ : syracuseStep 1704415 = 2556623) B2556623
theorem B11502161 : Blo 1008601 11502161 := bstep (se 2 (by rfl) ⟨4313310, by rfl⟩ : syracuseStep 11502161 = 8626621) B8626621
theorem B1705063 : Blo 1008601 1705063 := bstep (se 1 (by rfl) ⟨1278797, by rfl⟩ : syracuseStep 1705063 = 2557595) B2557595
theorem B398362445 : Blo 1008601 398362445 := bstep (se 3 (by rfl) ⟨74692958, by rfl⟩ : syracuseStep 398362445 = 149385917) B149385917
theorem B538806329 : Blo 1008601 538806329 := bstep (se 2 (by rfl) ⟨202052373, by rfl⟩ : syracuseStep 538806329 = 404104747) B404104747
theorem B3410423 : Blo 1008601 3410423 := bstep (se 1 (by rfl) ⟨2557817, by rfl⟩ : syracuseStep 3410423 = 5115635) B5115635
theorem B3838063 : Blo 1008601 3838063 := bstep (se 1 (by rfl) ⟨2878547, by rfl⟩ : syracuseStep 3838063 = 5757095) B5757095
theorem B1708519 : Blo 1008601 1708519 := bstep (se 1 (by rfl) ⟨1281389, by rfl⟩ : syracuseStep 1708519 = 2562779) B2562779
theorem B8623583 : Blo 1008601 8623583 := bstep (se 1 (by rfl) ⟨6467687, by rfl⟩ : syracuseStep 8623583 = 12935375) B12935375
theorem B1513535 : Blo 1008601 1513535 := bstep (se 1 (by rfl) ⟨1135151, by rfl⟩ : syracuseStep 1513535 = 2270303) B2270303
theorem B7772975 : Blo 1008601 7772975 := bstep (se 1 (by rfl) ⟨5829731, by rfl⟩ : syracuseStep 7772975 = 11659463) B11659463
theorem B3841951 : Blo 1008601 3841951 := bstep (se 1 (by rfl) ⟨2881463, by rfl⟩ : syracuseStep 3841951 = 5762927) B5762927
theorem B2728351 : Blo 1008601 2728351 := bstep (se 1 (by rfl) ⟨2046263, by rfl⟩ : syracuseStep 2728351 = 4092527) B4092527
theorem B1516511 : Blo 1008601 1516511 := bstep (se 1 (by rfl) ⟨1137383, by rfl⟩ : syracuseStep 1516511 = 2274767) B2274767
theorem B2368703 : Blo 1008601 2368703 := bstep (se 1 (by rfl) ⟨1776527, by rfl⟩ : syracuseStep 2368703 = 3553055) B3553055
theorem B2729855 : Blo 1008601 2729855 := bstep (se 1 (by rfl) ⟨2047391, by rfl⟩ : syracuseStep 2729855 = 4094783) B4094783
theorem B1518023 : Blo 1008601 1518023 := bstep (se 1 (by rfl) ⟨1138517, by rfl⟩ : syracuseStep 1518023 = 2277035) B2277035
theorem B1518335 : Blo 1008601 1518335 := bstep (se 1 (by rfl) ⟨1138751, by rfl⟩ : syracuseStep 1518335 = 2277503) B2277503
theorem B2272121 : Blo 1008601 2272121 := bstep (se 2 (by rfl) ⟨852045, by rfl⟩ : syracuseStep 2272121 = 1704091) B1704091
theorem B1518473 : Blo 1008601 1518473 := bstep (se 2 (by rfl) ⟨569427, by rfl⟩ : syracuseStep 1518473 = 1138855) B1138855
theorem B27667457 : Blo 1008601 27667457 := bstep (se 2 (by rfl) ⟨10375296, by rfl⟩ : syracuseStep 27667457 = 20750593) B20750593
theorem B58994219 : Blo 1008601 58994219 := bstep (se 1 (by rfl) ⟨44245664, by rfl⟩ : syracuseStep 58994219 = 88491329) B88491329
theorem B5125355 : Blo 1008601 5125355 := bstep (se 1 (by rfl) ⟨3844016, by rfl⟩ : syracuseStep 5125355 = 7688033) B7688033
theorem B11680159 : Blo 1008601 11680159 := bstep (se 1 (by rfl) ⟨8760119, by rfl⟩ : syracuseStep 11680159 = 17520239) B17520239
theorem B5749487 : Blo 1008601 5749487 := bstep (se 1 (by rfl) ⟨4312115, by rfl⟩ : syracuseStep 5749487 = 8624231) B8624231
theorem B12961255 : Blo 1008601 12961255 := bstep (se 1 (by rfl) ⟨9720941, by rfl⟩ : syracuseStep 12961255 = 19441883) B19441883
theorem B1823543 : Blo 1008601 1823543 := bstep (se 1 (by rfl) ⟨1367657, by rfl⟩ : syracuseStep 1823543 = 2735315) B2735315
theorem B8639743 : Blo 1008601 8639743 := bstep (se 1 (by rfl) ⟨6479807, by rfl⟩ : syracuseStep 8639743 = 12959615) B12959615
theorem B2873855 : Blo 1008601 2873855 := bstep (se 1 (by rfl) ⟨2155391, by rfl⟩ : syracuseStep 2873855 = 4310783) B4310783
theorem B8641079 : Blo 1008601 8641079 := bstep (se 1 (by rfl) ⟨6480809, by rfl⟩ : syracuseStep 8641079 = 12961619) B12961619
theorem B2873981 : Blo 1008601 2873981 := bstep (se 3 (by rfl) ⟨538871, by rfl⟩ : syracuseStep 2873981 = 1077743) B1077743
theorem B4317275 : Blo 1008601 4317275 := bstep (se 1 (by rfl) ⟨3237956, by rfl⟩ : syracuseStep 4317275 = 6475913) B6475913
theorem B3237023 : Blo 1008601 3237023 := bstep (se 1 (by rfl) ⟨2427767, by rfl⟩ : syracuseStep 3237023 = 4855535) B4855535
theorem B1010175 : Blo 1008601 1010175 := bstep (se 1 (by rfl) ⟨757631, by rfl⟩ : syracuseStep 1010175 = 1515263) B1515263
theorem B29584115 : Blo 1008601 29584115 := bstep (se 1 (by rfl) ⟨22188086, by rfl⟩ : syracuseStep 29584115 = 44376173) B44376173
theorem B1010623 : Blo 1008601 1010623 := bstep (se 1 (by rfl) ⟨757967, by rfl⟩ : syracuseStep 1010623 = 1515935) B1515935
theorem B9694151 : Blo 1008601 9694151 := bstep (se 1 (by rfl) ⟨7270613, by rfl⟩ : syracuseStep 9694151 = 14541227) B14541227
theorem B1011647 : Blo 1008601 1011647 := bstep (se 1 (by rfl) ⟨758735, by rfl⟩ : syracuseStep 1011647 = 1517471) B1517471
theorem B1011711 : Blo 1008601 1011711 := bstep (se 1 (by rfl) ⟨758783, by rfl⟩ : syracuseStep 1011711 = 1517567) B1517567
theorem B1438249 : Blo 1008601 1438249 := bstep (se 2 (by rfl) ⟨539343, by rfl⟩ : syracuseStep 1438249 = 1078687) B1078687
theorem B1012479 : Blo 1008601 1012479 := bstep (se 1 (by rfl) ⟨759359, by rfl⟩ : syracuseStep 1012479 = 1518719) B1518719
theorem B3405239 : Blo 1008601 3405239 := bstep (se 1 (by rfl) ⟨2553929, by rfl⟩ : syracuseStep 3405239 = 5107859) B5107859
theorem B1537471 : Blo 1008601 1537471 := bstep (se 1 (by rfl) ⟨1153103, by rfl⟩ : syracuseStep 1537471 = 2306207) B2306207
theorem B36894325 : Blo 1008601 36894325 := bstep (se 5 (by rfl) ⟨1729421, by rfl⟩ : syracuseStep 36894325 = 3458843) B3458843
theorem B8649449 : Blo 1008601 8649449 := bstep (se 2 (by rfl) ⟨3243543, by rfl⟩ : syracuseStep 8649449 = 6487087) B6487087
theorem B49217341 : Blo 1008601 49217341 := bstep (se 3 (by rfl) ⟨9228251, by rfl⟩ : syracuseStep 49217341 = 18456503) B18456503
theorem B7668107 : Blo 1008601 7668107 := bstep (se 1 (by rfl) ⟨5751080, by rfl⟩ : syracuseStep 7668107 = 11502161) B11502161
theorem B3637801 : Blo 1008601 3637801 := bstep (se 2 (by rfl) ⟨1364175, by rfl⟩ : syracuseStep 3637801 = 2728351) B2728351
theorem B359204219 : Blo 1008601 359204219 := bstep (se 1 (by rfl) ⟨269403164, by rfl⟩ : syracuseStep 359204219 = 538806329) B538806329
theorem B1215695 : Blo 1008601 1215695 := bstep (se 1 (by rfl) ⟨911771, by rfl⟩ : syracuseStep 1215695 = 1823543) B1823543
theorem B5181983 : Blo 1008601 5181983 := bstep (se 1 (by rfl) ⟨3886487, by rfl⟩ : syracuseStep 5181983 = 7772975) B7772975
theorem B5117417 : Blo 1008601 5117417 := bstep (se 2 (by rfl) ⟨1919031, by rfl⟩ : syracuseStep 5117417 = 3838063) B3838063
theorem B1514747 : Blo 1008601 1514747 := bstep (se 1 (by rfl) ⟨1136060, by rfl⟩ : syracuseStep 1514747 = 2272121) B2272121
theorem B6462767 : Blo 1008601 6462767 := bstep (se 1 (by rfl) ⟨4847075, by rfl⟩ : syracuseStep 6462767 = 9694151) B9694151
theorem B49192433 : Blo 1008601 49192433 := bstep (se 2 (by rfl) ⟨18447162, by rfl⟩ : syracuseStep 49192433 = 36894325) B36894325
theorem B39329479 : Blo 1008601 39329479 := bstep (se 1 (by rfl) ⟨29497109, by rfl⟩ : syracuseStep 39329479 = 58994219) B58994219
theorem B15573545 : Blo 1008601 15573545 := bstep (se 2 (by rfl) ⟨5840079, by rfl⟩ : syracuseStep 15573545 = 11680159) B11680159
theorem B3416903 : Blo 1008601 3416903 := bstep (se 1 (by rfl) ⟨2562677, by rfl⟩ : syracuseStep 3416903 = 5125355) B5125355
theorem B2270159 : Blo 1008601 2270159 := bstep (se 1 (by rfl) ⟨1702619, by rfl⟩ : syracuseStep 2270159 = 3405239) B3405239
theorem B5122601 : Blo 1008601 5122601 := bstep (se 2 (by rfl) ⟨1920975, by rfl⟩ : syracuseStep 5122601 = 3841951) B3841951
theorem B2271977 : Blo 1008601 2271977 := bstep (se 2 (by rfl) ⟨851991, by rfl⟩ : syracuseStep 2271977 = 1703983) B1703983
theorem B2272553 : Blo 1008601 2272553 := bstep (se 2 (by rfl) ⟨852207, by rfl⟩ : syracuseStep 2272553 = 1704415) B1704415
theorem B2273417 : Blo 1008601 2273417 := bstep (se 2 (by rfl) ⟨852531, by rfl⟩ : syracuseStep 2273417 = 1705063) B1705063
theorem B2273615 : Blo 1008601 2273615 := bstep (se 1 (by rfl) ⟨1705211, by rfl⟩ : syracuseStep 2273615 = 3410423) B3410423
theorem B17281673 : Blo 1008601 17281673 := bstep (se 2 (by rfl) ⟨6480627, by rfl⟩ : syracuseStep 17281673 = 12961255) B12961255
theorem B5749055 : Blo 1008601 5749055 := bstep (se 1 (by rfl) ⟨4311791, by rfl⟩ : syracuseStep 5749055 = 8623583) B8623583
theorem B1915903 : Blo 1008601 1915903 := bstep (se 1 (by rfl) ⟨1436927, by rfl⟩ : syracuseStep 1915903 = 2873855) B2873855
theorem B1915987 : Blo 1008601 1915987 := bstep (se 1 (by rfl) ⟨1436990, by rfl⟩ : syracuseStep 1915987 = 2873981) B2873981
theorem B2278025 : Blo 1008601 2278025 := bstep (se 2 (by rfl) ⟨854259, by rfl⟩ : syracuseStep 2278025 = 1708519) B1708519
theorem B1917665 : Blo 1008601 1917665 := bstep (se 2 (by rfl) ⟨719124, by rfl⟩ : syracuseStep 1917665 = 1438249) B1438249
theorem B1819903 : Blo 1008601 1819903 := bstep (se 1 (by rfl) ⟨1364927, by rfl⟩ : syracuseStep 1819903 = 2729855) B2729855
theorem B11519657 : Blo 1008601 11519657 := bstep (se 2 (by rfl) ⟨4319871, by rfl⟩ : syracuseStep 11519657 = 8639743) B8639743
theorem B2049961 : Blo 1008601 2049961 := bstep (se 2 (by rfl) ⟨768735, by rfl⟩ : syracuseStep 2049961 = 1537471) B1537471
theorem B65623121 : Blo 1008601 65623121 := bstep (se 2 (by rfl) ⟨24608670, by rfl⟩ : syracuseStep 65623121 = 49217341) B49217341
theorem B265574963 : Blo 1008601 265574963 := bstep (se 1 (by rfl) ⟨199181222, by rfl⟩ : syracuseStep 265574963 = 398362445) B398362445
theorem B6316541 : Blo 1008601 6316541 := bstep (se 3 (by rfl) ⟨1184351, by rfl⟩ : syracuseStep 6316541 = 2368703) B2368703
theorem B1009023 : Blo 1008601 1009023 := bstep (se 1 (by rfl) ⟨756767, by rfl⟩ : syracuseStep 1009023 = 1513535) B1513535
theorem B5760719 : Blo 1008601 5760719 := bstep (se 1 (by rfl) ⟨4320539, by rfl⟩ : syracuseStep 5760719 = 8641079) B8641079
theorem B2878183 : Blo 1008601 2878183 := bstep (se 1 (by rfl) ⟨2158637, by rfl⟩ : syracuseStep 2878183 = 4317275) B4317275
theorem B1011007 : Blo 1008601 1011007 := bstep (se 1 (by rfl) ⟨758255, by rfl⟩ : syracuseStep 1011007 = 1516511) B1516511
theorem B2158015 : Blo 1008601 2158015 := bstep (se 1 (by rfl) ⟨1618511, by rfl⟩ : syracuseStep 2158015 = 3237023) B3237023
theorem B1012015 : Blo 1008601 1012015 := bstep (se 1 (by rfl) ⟨759011, by rfl⟩ : syracuseStep 1012015 = 1518023) B1518023
theorem B19722743 : Blo 1008601 19722743 := bstep (se 1 (by rfl) ⟨14792057, by rfl⟩ : syracuseStep 19722743 = 29584115) B29584115
theorem B1012223 : Blo 1008601 1012223 := bstep (se 1 (by rfl) ⟨759167, by rfl⟩ : syracuseStep 1012223 = 1518335) B1518335
theorem B1012315 : Blo 1008601 1012315 := bstep (se 1 (by rfl) ⟨759236, by rfl⟩ : syracuseStep 1012315 = 1518473) B1518473
theorem B18444971 : Blo 1008601 18444971 := bstep (se 1 (by rfl) ⟨13833728, by rfl⟩ : syracuseStep 18444971 = 27667457) B27667457
theorem B5766299 : Blo 1008601 5766299 := bstep (se 1 (by rfl) ⟨4324724, by rfl⟩ : syracuseStep 5766299 = 8649449) B8649449
theorem B3832991 : Blo 1008601 3832991 := bstep (se 1 (by rfl) ⟨2874743, by rfl⟩ : syracuseStep 3832991 = 5749487) B5749487
theorem B5112071 : Blo 1008601 5112071 := bstep (se 1 (by rfl) ⟨3834053, by rfl⟩ : syracuseStep 5112071 = 7668107) B7668107
theorem B1278443 : Blo 1008601 1278443 := bstep (se 1 (by rfl) ⟨958832, by rfl⟩ : syracuseStep 1278443 = 1917665) B1917665
theorem B4850401 : Blo 1008601 4850401 := bstep (se 2 (by rfl) ⟨1818900, by rfl⟩ : syracuseStep 4850401 = 3637801) B3637801
theorem B239469479 : Blo 1008601 239469479 := bstep (se 1 (by rfl) ⟨179602109, by rfl⟩ : syracuseStep 239469479 = 359204219) B359204219
theorem B2426537 : Blo 1008601 2426537 := bstep (se 2 (by rfl) ⟨909951, by rfl⟩ : syracuseStep 2426537 = 1819903) B1819903
theorem B43748747 : Blo 1008601 43748747 := bstep (se 1 (by rfl) ⟨32811560, by rfl⟩ : syracuseStep 43748747 = 65623121) B65623121
theorem B3837577 : Blo 1008601 3837577 := bstep (se 2 (by rfl) ⟨1439091, by rfl⟩ : syracuseStep 3837577 = 2878183) B2878183
theorem B3411611 : Blo 1008601 3411611 := bstep (se 1 (by rfl) ⟨2558708, by rfl⟩ : syracuseStep 3411611 = 5117417) B5117417
theorem B177049975 : Blo 1008601 177049975 := bstep (se 1 (by rfl) ⟨132787481, by rfl⟩ : syracuseStep 177049975 = 265574963) B265574963
theorem B1513439 : Blo 1008601 1513439 := bstep (se 1 (by rfl) ⟨1135079, by rfl⟩ : syracuseStep 1513439 = 2270159) B2270159
theorem B3840479 : Blo 1008601 3840479 := bstep (se 1 (by rfl) ⟨2880359, by rfl⟩ : syracuseStep 3840479 = 5760719) B5760719
theorem B3415067 : Blo 1008601 3415067 := bstep (se 1 (by rfl) ⟨2561300, by rfl⟩ : syracuseStep 3415067 = 5122601) B5122601
theorem B1514651 : Blo 1008601 1514651 := bstep (se 1 (by rfl) ⟨1135988, by rfl⟩ : syracuseStep 1514651 = 2271977) B2271977
theorem B1515035 : Blo 1008601 1515035 := bstep (se 1 (by rfl) ⟨1136276, by rfl⟩ : syracuseStep 1515035 = 2272553) B2272553
theorem B1515611 : Blo 1008601 1515611 := bstep (se 1 (by rfl) ⟨1136708, by rfl⟩ : syracuseStep 1515611 = 2273417) B2273417
theorem B1515743 : Blo 1008601 1515743 := bstep (se 1 (by rfl) ⟨1136807, by rfl⟩ : syracuseStep 1515743 = 2273615) B2273615
theorem B13148495 : Blo 1008601 13148495 := bstep (se 1 (by rfl) ⟨9861371, by rfl⟩ : syracuseStep 13148495 = 19722743) B19722743
theorem B12296647 : Blo 1008601 12296647 := bstep (se 1 (by rfl) ⟨9222485, by rfl⟩ : syracuseStep 12296647 = 18444971) B18444971
theorem B209757221 : Blo 1008601 209757221 := bstep (se 4 (by rfl) ⟨19664739, by rfl⟩ : syracuseStep 209757221 = 39329479) B39329479
theorem B3844199 : Blo 1008601 3844199 := bstep (se 1 (by rfl) ⟨2883149, by rfl⟩ : syracuseStep 3844199 = 5766299) B5766299
theorem B1518683 : Blo 1008601 1518683 := bstep (se 1 (by rfl) ⟨1139012, by rfl⟩ : syracuseStep 1518683 = 2278025) B2278025
theorem B7679771 : Blo 1008601 7679771 := bstep (se 1 (by rfl) ⟨5759828, by rfl⟩ : syracuseStep 7679771 = 11519657) B11519657
theorem B2733281 : Blo 1008601 2733281 := bstep (se 2 (by rfl) ⟨1024980, by rfl⟩ : syracuseStep 2733281 = 2049961) B2049961
theorem B3454655 : Blo 1008601 3454655 := bstep (se 1 (by rfl) ⟨2590991, by rfl⟩ : syracuseStep 3454655 = 5181983) B5181983
theorem B4308511 : Blo 1008601 4308511 := bstep (se 1 (by rfl) ⟨3231383, by rfl⟩ : syracuseStep 4308511 = 6462767) B6462767
theorem B4211027 : Blo 1008601 4211027 := bstep (se 1 (by rfl) ⟨3158270, by rfl⟩ : syracuseStep 4211027 = 6316541) B6316541
theorem B2277935 : Blo 1008601 2277935 := bstep (se 1 (by rfl) ⟨1708451, by rfl⟩ : syracuseStep 2277935 = 3416903) B3416903
theorem B11521115 : Blo 1008601 11521115 := bstep (se 1 (by rfl) ⟨8640836, by rfl⟩ : syracuseStep 11521115 = 17281673) B17281673
theorem B2877353 : Blo 1008601 2877353 := bstep (se 2 (by rfl) ⟨1079007, by rfl⟩ : syracuseStep 2877353 = 2158015) B2158015
theorem B1009831 : Blo 1008601 1009831 := bstep (se 1 (by rfl) ⟨757373, by rfl⟩ : syracuseStep 1009831 = 1514747) B1514747
theorem B32794955 : Blo 1008601 32794955 := bstep (se 1 (by rfl) ⟨24596216, by rfl⟩ : syracuseStep 32794955 = 49192433) B49192433
theorem B10382363 : Blo 1008601 10382363 := bstep (se 1 (by rfl) ⟨7786772, by rfl⟩ : syracuseStep 10382363 = 15573545) B15573545
theorem B3241853 : Blo 1008601 3241853 := bstep (se 3 (by rfl) ⟨607847, by rfl⟩ : syracuseStep 3241853 = 1215695) B1215695
theorem B2554537 : Blo 1008601 2554537 := bstep (se 2 (by rfl) ⟨957951, by rfl⟩ : syracuseStep 2554537 = 1915903) B1915903
theorem B2554649 : Blo 1008601 2554649 := bstep (se 2 (by rfl) ⟨957993, by rfl⟩ : syracuseStep 2554649 = 1915987) B1915987
theorem B3832703 : Blo 1008601 3832703 := bstep (se 1 (by rfl) ⟨2874527, by rfl⟩ : syracuseStep 3832703 = 5749055) B5749055
theorem B2555327 : Blo 1008601 2555327 := bstep (se 1 (by rfl) ⟨1916495, by rfl⟩ : syracuseStep 2555327 = 3832991) B3832991
theorem B3408047 : Blo 1008601 3408047 := bstep (se 1 (by rfl) ⟨2556035, by rfl⟩ : syracuseStep 3408047 = 5112071) B5112071
theorem B159646319 : Blo 1008601 159646319 := bstep (se 1 (by rfl) ⟨119734739, by rfl⟩ : syracuseStep 159646319 = 239469479) B239469479
theorem B3409181 : Blo 1008601 3409181 := bstep (se 3 (by rfl) ⟨639221, by rfl⟩ : syracuseStep 3409181 = 1278443) B1278443
theorem B29165831 : Blo 1008601 29165831 := bstep (se 1 (by rfl) ⟨21874373, by rfl⟩ : syracuseStep 29165831 = 43748747) B43748747
theorem B2560319 : Blo 1008601 2560319 := bstep (se 1 (by rfl) ⟨1920239, by rfl⟩ : syracuseStep 2560319 = 3840479) B3840479
theorem B5116769 : Blo 1008601 5116769 := bstep (se 2 (by rfl) ⟨1918788, by rfl⟩ : syracuseStep 5116769 = 3837577) B3837577
theorem B236066633 : Blo 1008601 236066633 := bstep (se 2 (by rfl) ⟨88524987, by rfl⟩ : syracuseStep 236066633 = 177049975) B177049975
theorem B2562799 : Blo 1008601 2562799 := bstep (se 1 (by rfl) ⟨1922099, by rfl⟩ : syracuseStep 2562799 = 3844199) B3844199
theorem B21863303 : Blo 1008601 21863303 := bstep (se 1 (by rfl) ⟨16397477, by rfl⟩ : syracuseStep 21863303 = 32794955) B32794955
theorem B6921575 : Blo 1008601 6921575 := bstep (se 1 (by rfl) ⟨5191181, by rfl⟩ : syracuseStep 6921575 = 10382363) B10382363
theorem B5119847 : Blo 1008601 5119847 := bstep (se 1 (by rfl) ⟨3839885, by rfl⟩ : syracuseStep 5119847 = 7679771) B7679771
theorem B5744681 : Blo 1008601 5744681 := bstep (se 2 (by rfl) ⟨2154255, by rfl⟩ : syracuseStep 5744681 = 4308511) B4308511
theorem B1518623 : Blo 1008601 1518623 := bstep (se 1 (by rfl) ⟨1138967, by rfl⟩ : syracuseStep 1518623 = 2277935) B2277935
theorem B16395529 : Blo 1008601 16395529 := bstep (se 2 (by rfl) ⟨6148323, by rfl⟩ : syracuseStep 16395529 = 12296647) B12296647
theorem B6467201 : Blo 1008601 6467201 := bstep (se 2 (by rfl) ⟨2425200, by rfl⟩ : syracuseStep 6467201 = 4850401) B4850401
theorem B7680743 : Blo 1008601 7680743 := bstep (se 1 (by rfl) ⟨5760557, by rfl⟩ : syracuseStep 7680743 = 11521115) B11521115
theorem B2274407 : Blo 1008601 2274407 := bstep (se 1 (by rfl) ⟨1705805, by rfl⟩ : syracuseStep 2274407 = 3411611) B3411611
theorem B6470765 : Blo 1008601 6470765 := bstep (se 3 (by rfl) ⟨1213268, by rfl⟩ : syracuseStep 6470765 = 2426537) B2426537
theorem B2276711 : Blo 1008601 2276711 := bstep (se 1 (by rfl) ⟨1707533, by rfl⟩ : syracuseStep 2276711 = 3415067) B3415067
theorem B8765663 : Blo 1008601 8765663 := bstep (se 1 (by rfl) ⟨6574247, by rfl⟩ : syracuseStep 8765663 = 13148495) B13148495
theorem B139838147 : Blo 1008601 139838147 := bstep (se 1 (by rfl) ⟨104878610, by rfl⟩ : syracuseStep 139838147 = 209757221) B209757221
theorem B1918235 : Blo 1008601 1918235 := bstep (se 1 (by rfl) ⟨1438676, by rfl⟩ : syracuseStep 1918235 = 2877353) B2877353
theorem B36849653 : Blo 1008601 36849653 := bstep (se 5 (by rfl) ⟨1727327, by rfl⟩ : syracuseStep 36849653 = 3454655) B3454655
theorem B1822187 : Blo 1008601 1822187 := bstep (se 1 (by rfl) ⟨1366640, by rfl⟩ : syracuseStep 1822187 = 2733281) B2733281
theorem B2807351 : Blo 1008601 2807351 := bstep (se 1 (by rfl) ⟨2105513, by rfl⟩ : syracuseStep 2807351 = 4211027) B4211027
theorem B1008959 : Blo 1008601 1008959 := bstep (se 1 (by rfl) ⟨756719, by rfl⟩ : syracuseStep 1008959 = 1513439) B1513439
theorem B1009767 : Blo 1008601 1009767 := bstep (se 1 (by rfl) ⟨757325, by rfl⟩ : syracuseStep 1009767 = 1514651) B1514651
theorem B1010023 : Blo 1008601 1010023 := bstep (se 1 (by rfl) ⟨757517, by rfl⟩ : syracuseStep 1010023 = 1515035) B1515035
theorem B1010407 : Blo 1008601 1010407 := bstep (se 1 (by rfl) ⟨757805, by rfl⟩ : syracuseStep 1010407 = 1515611) B1515611
theorem B1010495 : Blo 1008601 1010495 := bstep (se 1 (by rfl) ⟨757871, by rfl⟩ : syracuseStep 1010495 = 1515743) B1515743
theorem B1012455 : Blo 1008601 1012455 := bstep (se 1 (by rfl) ⟨759341, by rfl⟩ : syracuseStep 1012455 = 1518683) B1518683
theorem B3406049 : Blo 1008601 3406049 := bstep (se 2 (by rfl) ⟨1277268, by rfl⟩ : syracuseStep 3406049 = 2554537) B2554537
theorem B2161235 : Blo 1008601 2161235 := bstep (se 1 (by rfl) ⟨1620926, by rfl⟩ : syracuseStep 2161235 = 3241853) B3241853
theorem B1703099 : Blo 1008601 1703099 := bstep (se 1 (by rfl) ⟨1277324, by rfl⟩ : syracuseStep 1703099 = 2554649) B2554649
theorem B2555135 : Blo 1008601 2555135 := bstep (se 1 (by rfl) ⟨1916351, by rfl⟩ : syracuseStep 2555135 = 3832703) B3832703
theorem B1703551 : Blo 1008601 1703551 := bstep (se 1 (by rfl) ⟨1277663, by rfl⟩ : syracuseStep 1703551 = 2555327) B2555327
theorem B106430879 : Blo 1008601 106430879 := bstep (se 1 (by rfl) ⟨79823159, by rfl⟩ : syracuseStep 106430879 = 159646319) B159646319
theorem B93225431 : Blo 1008601 93225431 := bstep (se 1 (by rfl) ⟨69919073, by rfl⟩ : syracuseStep 93225431 = 139838147) B139838147
theorem B1278823 : Blo 1008601 1278823 := bstep (se 1 (by rfl) ⟨959117, by rfl⟩ : syracuseStep 1278823 = 1918235) B1918235
theorem B1706879 : Blo 1008601 1706879 := bstep (se 1 (by rfl) ⟨1280159, by rfl⟩ : syracuseStep 1706879 = 2560319) B2560319
theorem B3411179 : Blo 1008601 3411179 := bstep (se 1 (by rfl) ⟨2558384, by rfl⟩ : syracuseStep 3411179 = 5116769) B5116769
theorem B1871567 : Blo 1008601 1871567 := bstep (se 1 (by rfl) ⟨1403675, by rfl⟩ : syracuseStep 1871567 = 2807351) B2807351
theorem B21860705 : Blo 1008601 21860705 := bstep (se 2 (by rfl) ⟨8197764, by rfl⟩ : syracuseStep 21860705 = 16395529) B16395529
theorem B3413231 : Blo 1008601 3413231 := bstep (se 1 (by rfl) ⟨2559923, by rfl⟩ : syracuseStep 3413231 = 5119847) B5119847
theorem B5120495 : Blo 1008601 5120495 := bstep (se 1 (by rfl) ⟨3840371, by rfl⟩ : syracuseStep 5120495 = 7680743) B7680743
theorem B1516271 : Blo 1008601 1516271 := bstep (se 1 (by rfl) ⟨1137203, by rfl⟩ : syracuseStep 1516271 = 2274407) B2274407
theorem B3417065 : Blo 1008601 3417065 := bstep (se 2 (by rfl) ⟨1281399, by rfl⟩ : syracuseStep 3417065 = 2562799) B2562799
theorem B4859165 : Blo 1008601 4859165 := bstep (se 3 (by rfl) ⟨911093, by rfl⟩ : syracuseStep 4859165 = 1822187) B1822187
theorem B2270699 : Blo 1008601 2270699 := bstep (se 1 (by rfl) ⟨1703024, by rfl⟩ : syracuseStep 2270699 = 3406049) B3406049
theorem B2271401 : Blo 1008601 2271401 := bstep (se 2 (by rfl) ⟨851775, by rfl⟩ : syracuseStep 2271401 = 1703551) B1703551
theorem B1517807 : Blo 1008601 1517807 := bstep (se 1 (by rfl) ⟨1138355, by rfl⟩ : syracuseStep 1517807 = 2276711) B2276711
theorem B2272031 : Blo 1008601 2272031 := bstep (se 1 (by rfl) ⟨1704023, by rfl⟩ : syracuseStep 2272031 = 3408047) B3408047
theorem B23375101 : Blo 1008601 23375101 := bstep (se 3 (by rfl) ⟨4382831, by rfl⟩ : syracuseStep 23375101 = 8765663) B8765663
theorem B2272787 : Blo 1008601 2272787 := bstep (se 1 (by rfl) ⟨1704590, by rfl⟩ : syracuseStep 2272787 = 3409181) B3409181
theorem B19443887 : Blo 1008601 19443887 := bstep (se 1 (by rfl) ⟨14582915, by rfl⟩ : syracuseStep 19443887 = 29165831) B29165831
theorem B4311467 : Blo 1008601 4311467 := bstep (se 1 (by rfl) ⟨3233600, by rfl⟩ : syracuseStep 4311467 = 6467201) B6467201
theorem B4313843 : Blo 1008601 4313843 := bstep (se 1 (by rfl) ⟨3235382, by rfl⟩ : syracuseStep 4313843 = 6470765) B6470765
theorem B1135399 : Blo 1008601 1135399 := bstep (se 1 (by rfl) ⟨851549, by rfl⟩ : syracuseStep 1135399 = 1703099) B1703099
theorem B24566435 : Blo 1008601 24566435 := bstep (se 1 (by rfl) ⟨18424826, by rfl⟩ : syracuseStep 24566435 = 36849653) B36849653
theorem B157377755 : Blo 1008601 157377755 := bstep (se 1 (by rfl) ⟨118033316, by rfl⟩ : syracuseStep 157377755 = 236066633) B236066633
theorem B14575535 : Blo 1008601 14575535 := bstep (se 1 (by rfl) ⟨10931651, by rfl⟩ : syracuseStep 14575535 = 21863303) B21863303
theorem B4614383 : Blo 1008601 4614383 := bstep (se 1 (by rfl) ⟨3460787, by rfl⟩ : syracuseStep 4614383 = 6921575) B6921575
theorem B3829787 : Blo 1008601 3829787 := bstep (se 1 (by rfl) ⟨2872340, by rfl⟩ : syracuseStep 3829787 = 5744681) B5744681
theorem B1012415 : Blo 1008601 1012415 := bstep (se 1 (by rfl) ⟨759311, by rfl⟩ : syracuseStep 1012415 = 1518623) B1518623
theorem B1440823 : Blo 1008601 1440823 := bstep (se 1 (by rfl) ⟨1080617, by rfl⟩ : syracuseStep 1440823 = 2161235) B2161235
theorem B1703423 : Blo 1008601 1703423 := bstep (se 1 (by rfl) ⟨1277567, by rfl⟩ : syracuseStep 1703423 = 2555135) B2555135
theorem B1705097 : Blo 1008601 1705097 := bstep (se 2 (by rfl) ⟨639411, by rfl⟩ : syracuseStep 1705097 = 1278823) B1278823
theorem B31166801 : Blo 1008601 31166801 := bstep (se 2 (by rfl) ⟨11687550, by rfl⟩ : syracuseStep 31166801 = 23375101) B23375101
theorem B3413663 : Blo 1008601 3413663 := bstep (se 1 (by rfl) ⟨2560247, by rfl⟩ : syracuseStep 3413663 = 5120495) B5120495
theorem B1513799 : Blo 1008601 1513799 := bstep (se 1 (by rfl) ⟨1135349, by rfl⟩ : syracuseStep 1513799 = 2270699) B2270699
theorem B1513865 : Blo 1008601 1513865 := bstep (se 2 (by rfl) ⟨567699, by rfl⟩ : syracuseStep 1513865 = 1135399) B1135399
theorem B1514267 : Blo 1008601 1514267 := bstep (se 1 (by rfl) ⟨1135700, by rfl⟩ : syracuseStep 1514267 = 2271401) B2271401
theorem B1514687 : Blo 1008601 1514687 := bstep (se 1 (by rfl) ⟨1136015, by rfl⟩ : syracuseStep 1514687 = 2272031) B2272031
theorem B19963381 : Blo 1008601 19963381 := bstep (se 5 (by rfl) ⟨935783, by rfl⟩ : syracuseStep 19963381 = 1871567) B1871567
theorem B1515191 : Blo 1008601 1515191 := bstep (se 1 (by rfl) ⟨1136393, by rfl⟩ : syracuseStep 1515191 = 2272787) B2272787
theorem B283815677 : Blo 1008601 283815677 := bstep (se 3 (by rfl) ⟨53215439, by rfl⟩ : syracuseStep 283815677 = 106430879) B106430879
theorem B2274119 : Blo 1008601 2274119 := bstep (se 1 (by rfl) ⟨1705589, by rfl⟩ : syracuseStep 2274119 = 3411179) B3411179
theorem B2275487 : Blo 1008601 2275487 := bstep (se 1 (by rfl) ⟨1706615, by rfl⟩ : syracuseStep 2275487 = 3413231) B3413231
theorem B2278043 : Blo 1008601 2278043 := bstep (se 1 (by rfl) ⟨1708532, by rfl⟩ : syracuseStep 2278043 = 3417065) B3417065
theorem B9717023 : Blo 1008601 9717023 := bstep (se 1 (by rfl) ⟨7287767, by rfl⟩ : syracuseStep 9717023 = 14575535) B14575535
theorem B12962591 : Blo 1008601 12962591 := bstep (se 1 (by rfl) ⟨9721943, by rfl⟩ : syracuseStep 12962591 = 19443887) B19443887
theorem B1921097 : Blo 1008601 1921097 := bstep (se 2 (by rfl) ⟨720411, by rfl⟩ : syracuseStep 1921097 = 1440823) B1440823
theorem B1135615 : Blo 1008601 1135615 := bstep (se 1 (by rfl) ⟨851711, by rfl⟩ : syracuseStep 1135615 = 1703423) B1703423
theorem B62150287 : Blo 1008601 62150287 := bstep (se 1 (by rfl) ⟨46612715, by rfl⟩ : syracuseStep 62150287 = 93225431) B93225431
theorem B2874311 : Blo 1008601 2874311 := bstep (se 1 (by rfl) ⟨2155733, by rfl⟩ : syracuseStep 2874311 = 4311467) B4311467
theorem B1137919 : Blo 1008601 1137919 := bstep (se 1 (by rfl) ⟨853439, by rfl⟩ : syracuseStep 1137919 = 1706879) B1706879
theorem B14573803 : Blo 1008601 14573803 := bstep (se 1 (by rfl) ⟨10930352, by rfl⟩ : syracuseStep 14573803 = 21860705) B21860705
theorem B2875895 : Blo 1008601 2875895 := bstep (se 1 (by rfl) ⟨2156921, by rfl⟩ : syracuseStep 2875895 = 4313843) B4313843
theorem B16377623 : Blo 1008601 16377623 := bstep (se 1 (by rfl) ⟨12283217, by rfl⟩ : syracuseStep 16377623 = 24566435) B24566435
theorem B1010847 : Blo 1008601 1010847 := bstep (se 1 (by rfl) ⟨758135, by rfl⟩ : syracuseStep 1010847 = 1516271) B1516271
theorem B104918503 : Blo 1008601 104918503 := bstep (se 1 (by rfl) ⟨78688877, by rfl⟩ : syracuseStep 104918503 = 157377755) B157377755
theorem B3239443 : Blo 1008601 3239443 := bstep (se 1 (by rfl) ⟨2429582, by rfl⟩ : syracuseStep 3239443 = 4859165) B4859165
theorem B3076255 : Blo 1008601 3076255 := bstep (se 1 (by rfl) ⟨2307191, by rfl⟩ : syracuseStep 3076255 = 4614383) B4614383
theorem B1011871 : Blo 1008601 1011871 := bstep (se 1 (by rfl) ⟨758903, by rfl⟩ : syracuseStep 1011871 = 1517807) B1517807
theorem B2553191 : Blo 1008601 2553191 := bstep (se 1 (by rfl) ⟨1914893, by rfl⟩ : syracuseStep 2553191 = 3829787) B3829787
theorem B19431737 : Blo 1008601 19431737 := bstep (se 2 (by rfl) ⟨7286901, by rfl⟩ : syracuseStep 19431737 = 14573803) B14573803
theorem B20777867 : Blo 1008601 20777867 := bstep (se 1 (by rfl) ⟨15583400, by rfl⟩ : syracuseStep 20777867 = 31166801) B31166801
theorem B139891337 : Blo 1008601 139891337 := bstep (se 2 (by rfl) ⟨52459251, by rfl⟩ : syracuseStep 139891337 = 104918503) B104918503
theorem B4101673 : Blo 1008601 4101673 := bstep (se 2 (by rfl) ⟨1538127, by rfl⟩ : syracuseStep 4101673 = 3076255) B3076255
theorem B10918415 : Blo 1008601 10918415 := bstep (se 1 (by rfl) ⟨8188811, by rfl⟩ : syracuseStep 10918415 = 16377623) B16377623
theorem B1514153 : Blo 1008601 1514153 := bstep (se 2 (by rfl) ⟨567807, by rfl⟩ : syracuseStep 1514153 = 1135615) B1135615
theorem B189210451 : Blo 1008601 189210451 := bstep (se 1 (by rfl) ⟨141907838, by rfl⟩ : syracuseStep 189210451 = 283815677) B283815677
theorem B1516079 : Blo 1008601 1516079 := bstep (se 1 (by rfl) ⟨1137059, by rfl⟩ : syracuseStep 1516079 = 2274119) B2274119
theorem B1516991 : Blo 1008601 1516991 := bstep (se 1 (by rfl) ⟨1137743, by rfl⟩ : syracuseStep 1516991 = 2275487) B2275487
theorem B1517225 : Blo 1008601 1517225 := bstep (se 2 (by rfl) ⟨568959, by rfl⟩ : syracuseStep 1517225 = 1137919) B1137919
theorem B26617841 : Blo 1008601 26617841 := bstep (se 2 (by rfl) ⟨9981690, by rfl⟩ : syracuseStep 26617841 = 19963381) B19963381
theorem B5122925 : Blo 1008601 5122925 := bstep (se 3 (by rfl) ⟨960548, by rfl⟩ : syracuseStep 5122925 = 1921097) B1921097
theorem B1518695 : Blo 1008601 1518695 := bstep (se 1 (by rfl) ⟨1139021, by rfl⟩ : syracuseStep 1518695 = 2278043) B2278043
theorem B2275775 : Blo 1008601 2275775 := bstep (se 1 (by rfl) ⟨1706831, by rfl⟩ : syracuseStep 2275775 = 3413663) B3413663
theorem B1916207 : Blo 1008601 1916207 := bstep (se 1 (by rfl) ⟨1437155, by rfl⟩ : syracuseStep 1916207 = 2874311) B2874311
theorem B1917263 : Blo 1008601 1917263 := bstep (se 1 (by rfl) ⟨1437947, by rfl⟩ : syracuseStep 1917263 = 2875895) B2875895
theorem B1136731 : Blo 1008601 1136731 := bstep (se 1 (by rfl) ⟨852548, by rfl⟩ : syracuseStep 1136731 = 1705097) B1705097
theorem B6478015 : Blo 1008601 6478015 := bstep (se 1 (by rfl) ⟨4858511, by rfl⟩ : syracuseStep 6478015 = 9717023) B9717023
theorem B8641727 : Blo 1008601 8641727 := bstep (se 1 (by rfl) ⟨6481295, by rfl⟩ : syracuseStep 8641727 = 12962591) B12962591
theorem B1009199 : Blo 1008601 1009199 := bstep (se 1 (by rfl) ⟨756899, by rfl⟩ : syracuseStep 1009199 = 1513799) B1513799
theorem B1009243 : Blo 1008601 1009243 := bstep (se 1 (by rfl) ⟨756932, by rfl⟩ : syracuseStep 1009243 = 1513865) B1513865
theorem B1009511 : Blo 1008601 1009511 := bstep (se 1 (by rfl) ⟨757133, by rfl⟩ : syracuseStep 1009511 = 1514267) B1514267
theorem B4319257 : Blo 1008601 4319257 := bstep (se 2 (by rfl) ⟨1619721, by rfl⟩ : syracuseStep 4319257 = 3239443) B3239443
theorem B1009791 : Blo 1008601 1009791 := bstep (se 1 (by rfl) ⟨757343, by rfl⟩ : syracuseStep 1009791 = 1514687) B1514687
theorem B1010127 : Blo 1008601 1010127 := bstep (se 1 (by rfl) ⟨757595, by rfl⟩ : syracuseStep 1010127 = 1515191) B1515191
theorem B82867049 : Blo 1008601 82867049 := bstep (se 2 (by rfl) ⟨31075143, by rfl⟩ : syracuseStep 82867049 = 62150287) B62150287
theorem B1702127 : Blo 1008601 1702127 := bstep (se 1 (by rfl) ⟨1276595, by rfl⟩ : syracuseStep 1702127 = 2553191) B2553191
theorem B1278175 : Blo 1008601 1278175 := bstep (se 1 (by rfl) ⟨958631, by rfl⟩ : syracuseStep 1278175 = 1917263) B1917263
theorem B93260891 : Blo 1008601 93260891 := bstep (se 1 (by rfl) ⟨69945668, by rfl⟩ : syracuseStep 93260891 = 139891337) B139891337
theorem B3415283 : Blo 1008601 3415283 := bstep (se 1 (by rfl) ⟨2561462, by rfl⟩ : syracuseStep 3415283 = 5122925) B5122925
theorem B1515641 : Blo 1008601 1515641 := bstep (se 2 (by rfl) ⟨568365, by rfl⟩ : syracuseStep 1515641 = 1136731) B1136731
theorem B1517183 : Blo 1008601 1517183 := bstep (se 1 (by rfl) ⟨1137887, by rfl⟩ : syracuseStep 1517183 = 2275775) B2275775
theorem B12954491 : Blo 1008601 12954491 := bstep (se 1 (by rfl) ⟨9715868, by rfl⟩ : syracuseStep 12954491 = 19431737) B19431737
theorem B17745227 : Blo 1008601 17745227 := bstep (se 1 (by rfl) ⟨13308920, by rfl⟩ : syracuseStep 17745227 = 26617841) B26617841
theorem B29115773 : Blo 1008601 29115773 := bstep (se 3 (by rfl) ⟨5459207, by rfl⟩ : syracuseStep 29115773 = 10918415) B10918415
theorem B8637353 : Blo 1008601 8637353 := bstep (se 2 (by rfl) ⟨3239007, by rfl⟩ : syracuseStep 8637353 = 6478015) B6478015
theorem B1134751 : Blo 1008601 1134751 := bstep (se 1 (by rfl) ⟨851063, by rfl⟩ : syracuseStep 1134751 = 1702127) B1702127
theorem B13851911 : Blo 1008601 13851911 := bstep (se 1 (by rfl) ⟨10388933, by rfl⟩ : syracuseStep 13851911 = 20777867) B20777867
theorem B5759009 : Blo 1008601 5759009 := bstep (se 2 (by rfl) ⟨2159628, by rfl⟩ : syracuseStep 5759009 = 4319257) B4319257
theorem B1009435 : Blo 1008601 1009435 := bstep (se 1 (by rfl) ⟨757076, by rfl⟩ : syracuseStep 1009435 = 1514153) B1514153
theorem B5761151 : Blo 1008601 5761151 := bstep (se 1 (by rfl) ⟨4320863, by rfl⟩ : syracuseStep 5761151 = 8641727) B8641727
theorem B1010719 : Blo 1008601 1010719 := bstep (se 1 (by rfl) ⟨758039, by rfl⟩ : syracuseStep 1010719 = 1516079) B1516079
theorem B1011327 : Blo 1008601 1011327 := bstep (se 1 (by rfl) ⟨758495, by rfl⟩ : syracuseStep 1011327 = 1516991) B1516991
theorem B1011483 : Blo 1008601 1011483 := bstep (se 1 (by rfl) ⟨758612, by rfl⟩ : syracuseStep 1011483 = 1517225) B1517225
theorem B5468897 : Blo 1008601 5468897 := bstep (se 2 (by rfl) ⟨2050836, by rfl⟩ : syracuseStep 5468897 = 4101673) B4101673
theorem B1012463 : Blo 1008601 1012463 := bstep (se 1 (by rfl) ⟨759347, by rfl⟩ : syracuseStep 1012463 = 1518695) B1518695
theorem B55244699 : Blo 1008601 55244699 := bstep (se 1 (by rfl) ⟨41433524, by rfl⟩ : syracuseStep 55244699 = 82867049) B82867049
theorem B1277471 : Blo 1008601 1277471 := bstep (se 1 (by rfl) ⟨958103, by rfl⟩ : syracuseStep 1277471 = 1916207) B1916207
theorem B252280601 : Blo 1008601 252280601 := bstep (se 2 (by rfl) ⟨94605225, by rfl⟩ : syracuseStep 252280601 = 189210451) B189210451
theorem B1704233 : Blo 1008601 1704233 := bstep (se 2 (by rfl) ⟨639087, by rfl⟩ : syracuseStep 1704233 = 1278175) B1278175
theorem B11830151 : Blo 1008601 11830151 := bstep (se 1 (by rfl) ⟨8872613, by rfl⟩ : syracuseStep 11830151 = 17745227) B17745227
theorem B3839339 : Blo 1008601 3839339 := bstep (se 1 (by rfl) ⟨2879504, by rfl⟩ : syracuseStep 3839339 = 5759009) B5759009
theorem B1513001 : Blo 1008601 1513001 := bstep (se 2 (by rfl) ⟨567375, by rfl⟩ : syracuseStep 1513001 = 1134751) B1134751
theorem B3840767 : Blo 1008601 3840767 := bstep (se 1 (by rfl) ⟨2880575, by rfl⟩ : syracuseStep 3840767 = 5761151) B5761151
theorem B3645931 : Blo 1008601 3645931 := bstep (se 1 (by rfl) ⟨2734448, by rfl⟩ : syracuseStep 3645931 = 5468897) B5468897
theorem B19410515 : Blo 1008601 19410515 := bstep (se 1 (by rfl) ⟨14557886, by rfl⟩ : syracuseStep 19410515 = 29115773) B29115773
theorem B62173927 : Blo 1008601 62173927 := bstep (se 1 (by rfl) ⟨46630445, by rfl⟩ : syracuseStep 62173927 = 93260891) B93260891
theorem B2276855 : Blo 1008601 2276855 := bstep (se 1 (by rfl) ⟨1707641, by rfl⟩ : syracuseStep 2276855 = 3415283) B3415283
theorem B8636327 : Blo 1008601 8636327 := bstep (se 1 (by rfl) ⟨6477245, by rfl⟩ : syracuseStep 8636327 = 12954491) B12954491
theorem B168187067 : Blo 1008601 168187067 := bstep (se 1 (by rfl) ⟨126140300, by rfl⟩ : syracuseStep 168187067 = 252280601) B252280601
theorem B5758235 : Blo 1008601 5758235 := bstep (se 1 (by rfl) ⟨4318676, by rfl⟩ : syracuseStep 5758235 = 8637353) B8637353
theorem B9234607 : Blo 1008601 9234607 := bstep (se 1 (by rfl) ⟨6925955, by rfl⟩ : syracuseStep 9234607 = 13851911) B13851911
theorem B1010427 : Blo 1008601 1010427 := bstep (se 1 (by rfl) ⟨757820, by rfl⟩ : syracuseStep 1010427 = 1515641) B1515641
theorem B1011455 : Blo 1008601 1011455 := bstep (se 1 (by rfl) ⟨758591, by rfl⟩ : syracuseStep 1011455 = 1517183) B1517183
theorem B36829799 : Blo 1008601 36829799 := bstep (se 1 (by rfl) ⟨27622349, by rfl⟩ : syracuseStep 36829799 = 55244699) B55244699
theorem B3406589 : Blo 1008601 3406589 := bstep (se 3 (by rfl) ⟨638735, by rfl⟩ : syracuseStep 3406589 = 1277471) B1277471
theorem B2559559 : Blo 1008601 2559559 := bstep (se 1 (by rfl) ⟨1919669, by rfl⟩ : syracuseStep 2559559 = 3839339) B3839339
theorem B2560511 : Blo 1008601 2560511 := bstep (se 1 (by rfl) ⟨1920383, by rfl⟩ : syracuseStep 2560511 = 3840767) B3840767
theorem B3838823 : Blo 1008601 3838823 := bstep (se 1 (by rfl) ⟨2879117, by rfl⟩ : syracuseStep 3838823 = 5758235) B5758235
theorem B24553199 : Blo 1008601 24553199 := bstep (se 1 (by rfl) ⟨18414899, by rfl⟩ : syracuseStep 24553199 = 36829799) B36829799
theorem B2271059 : Blo 1008601 2271059 := bstep (se 1 (by rfl) ⟨1703294, by rfl⟩ : syracuseStep 2271059 = 3406589) B3406589
theorem B1517903 : Blo 1008601 1517903 := bstep (se 1 (by rfl) ⟨1138427, by rfl⟩ : syracuseStep 1517903 = 2276855) B2276855
theorem B4861241 : Blo 1008601 4861241 := bstep (se 2 (by rfl) ⟨1822965, by rfl⟩ : syracuseStep 4861241 = 3645931) B3645931
theorem B1136155 : Blo 1008601 1136155 := bstep (se 1 (by rfl) ⟨852116, by rfl⟩ : syracuseStep 1136155 = 1704233) B1704233
theorem B7886767 : Blo 1008601 7886767 := bstep (se 1 (by rfl) ⟨5915075, by rfl⟩ : syracuseStep 7886767 = 11830151) B11830151
theorem B5757551 : Blo 1008601 5757551 := bstep (se 1 (by rfl) ⟨4318163, by rfl⟩ : syracuseStep 5757551 = 8636327) B8636327
theorem B12312809 : Blo 1008601 12312809 := bstep (se 2 (by rfl) ⟨4617303, by rfl⟩ : syracuseStep 12312809 = 9234607) B9234607
theorem B112124711 : Blo 1008601 112124711 := bstep (se 1 (by rfl) ⟨84093533, by rfl⟩ : syracuseStep 112124711 = 168187067) B168187067
theorem B1008667 : Blo 1008601 1008667 := bstep (se 1 (by rfl) ⟨756500, by rfl⟩ : syracuseStep 1008667 = 1513001) B1513001
theorem B82898569 : Blo 1008601 82898569 := bstep (se 2 (by rfl) ⟨31086963, by rfl⟩ : syracuseStep 82898569 = 62173927) B62173927
theorem B12940343 : Blo 1008601 12940343 := bstep (se 1 (by rfl) ⟨9705257, by rfl⟩ : syracuseStep 12940343 = 19410515) B19410515
theorem B1707007 : Blo 1008601 1707007 := bstep (se 1 (by rfl) ⟨1280255, by rfl⟩ : syracuseStep 1707007 = 2560511) B2560511
theorem B2559215 : Blo 1008601 2559215 := bstep (se 1 (by rfl) ⟨1919411, by rfl⟩ : syracuseStep 2559215 = 3838823) B3838823
theorem B3838367 : Blo 1008601 3838367 := bstep (se 1 (by rfl) ⟨2878775, by rfl⟩ : syracuseStep 3838367 = 5757551) B5757551
theorem B3412745 : Blo 1008601 3412745 := bstep (se 2 (by rfl) ⟨1279779, by rfl⟩ : syracuseStep 3412745 = 2559559) B2559559
theorem B110531425 : Blo 1008601 110531425 := bstep (se 2 (by rfl) ⟨41449284, by rfl⟩ : syracuseStep 110531425 = 82898569) B82898569
theorem B74749807 : Blo 1008601 74749807 := bstep (se 1 (by rfl) ⟨56062355, by rfl⟩ : syracuseStep 74749807 = 112124711) B112124711
theorem B1514039 : Blo 1008601 1514039 := bstep (se 1 (by rfl) ⟨1135529, by rfl⟩ : syracuseStep 1514039 = 2271059) B2271059
theorem B1514873 : Blo 1008601 1514873 := bstep (se 2 (by rfl) ⟨568077, by rfl⟩ : syracuseStep 1514873 = 1136155) B1136155
theorem B8626895 : Blo 1008601 8626895 := bstep (se 1 (by rfl) ⟨6470171, by rfl⟩ : syracuseStep 8626895 = 12940343) B12940343
theorem B8208539 : Blo 1008601 8208539 := bstep (se 1 (by rfl) ⟨6156404, by rfl⟩ : syracuseStep 8208539 = 12312809) B12312809
theorem B16368799 : Blo 1008601 16368799 := bstep (se 1 (by rfl) ⟨12276599, by rfl⟩ : syracuseStep 16368799 = 24553199) B24553199
theorem B1011935 : Blo 1008601 1011935 := bstep (se 1 (by rfl) ⟨758951, by rfl⟩ : syracuseStep 1011935 = 1517903) B1517903
theorem B3240827 : Blo 1008601 3240827 := bstep (se 1 (by rfl) ⟨2430620, by rfl⟩ : syracuseStep 3240827 = 4861241) B4861241
theorem B10515689 : Blo 1008601 10515689 := bstep (se 2 (by rfl) ⟨3943383, by rfl⟩ : syracuseStep 10515689 = 7886767) B7886767
theorem B5472359 : Blo 1008601 5472359 := bstep (se 1 (by rfl) ⟨4104269, by rfl⟩ : syracuseStep 5472359 = 8208539) B8208539
theorem B21825065 : Blo 1008601 21825065 := bstep (se 2 (by rfl) ⟨8184399, by rfl⟩ : syracuseStep 21825065 = 16368799) B16368799
theorem B1706143 : Blo 1008601 1706143 := bstep (se 1 (by rfl) ⟨1279607, by rfl⟩ : syracuseStep 1706143 = 2559215) B2559215
theorem B2558911 : Blo 1008601 2558911 := bstep (se 1 (by rfl) ⟨1919183, by rfl⟩ : syracuseStep 2558911 = 3838367) B3838367
theorem B2275163 : Blo 1008601 2275163 := bstep (se 1 (by rfl) ⟨1706372, by rfl⟩ : syracuseStep 2275163 = 3412745) B3412745
theorem B2276009 : Blo 1008601 2276009 := bstep (se 2 (by rfl) ⟨853503, by rfl⟩ : syracuseStep 2276009 = 1707007) B1707007
theorem B5751263 : Blo 1008601 5751263 := bstep (se 1 (by rfl) ⟨4313447, by rfl⟩ : syracuseStep 5751263 = 8626895) B8626895
theorem B147375233 : Blo 1008601 147375233 := bstep (se 2 (by rfl) ⟨55265712, by rfl⟩ : syracuseStep 147375233 = 110531425) B110531425
theorem B99666409 : Blo 1008601 99666409 := bstep (se 2 (by rfl) ⟨37374903, by rfl⟩ : syracuseStep 99666409 = 74749807) B74749807
theorem B1009359 : Blo 1008601 1009359 := bstep (se 1 (by rfl) ⟨757019, by rfl⟩ : syracuseStep 1009359 = 1514039) B1514039
theorem B1009915 : Blo 1008601 1009915 := bstep (se 1 (by rfl) ⟨757436, by rfl⟩ : syracuseStep 1009915 = 1514873) B1514873
theorem B2160551 : Blo 1008601 2160551 := bstep (se 1 (by rfl) ⟨1620413, by rfl⟩ : syracuseStep 2160551 = 3240827) B3240827
theorem B7010459 : Blo 1008601 7010459 := bstep (se 1 (by rfl) ⟨5257844, by rfl⟩ : syracuseStep 7010459 = 10515689) B10515689
theorem B3834175 : Blo 1008601 3834175 := bstep (se 1 (by rfl) ⟨2875631, by rfl⟩ : syracuseStep 3834175 = 5751263) B5751263
theorem B14550043 : Blo 1008601 14550043 := bstep (se 1 (by rfl) ⟨10912532, by rfl⟩ : syracuseStep 14550043 = 21825065) B21825065
theorem B3411881 : Blo 1008601 3411881 := bstep (se 2 (by rfl) ⟨1279455, by rfl⟩ : syracuseStep 3411881 = 2558911) B2558911
theorem B1516775 : Blo 1008601 1516775 := bstep (se 1 (by rfl) ⟨1137581, by rfl⟩ : syracuseStep 1516775 = 2275163) B2275163
theorem B1517339 : Blo 1008601 1517339 := bstep (se 1 (by rfl) ⟨1138004, by rfl⟩ : syracuseStep 1517339 = 2276009) B2276009
theorem B3648239 : Blo 1008601 3648239 := bstep (se 1 (by rfl) ⟨2736179, by rfl⟩ : syracuseStep 3648239 = 5472359) B5472359
theorem B98250155 : Blo 1008601 98250155 := bstep (se 1 (by rfl) ⟨73687616, by rfl⟩ : syracuseStep 98250155 = 147375233) B147375233
theorem B2274857 : Blo 1008601 2274857 := bstep (se 2 (by rfl) ⟨853071, by rfl⟩ : syracuseStep 2274857 = 1706143) B1706143
theorem B132888545 : Blo 1008601 132888545 := bstep (se 2 (by rfl) ⟨49833204, by rfl⟩ : syracuseStep 132888545 = 99666409) B99666409
theorem B4673639 : Blo 1008601 4673639 := bstep (se 1 (by rfl) ⟨3505229, by rfl⟩ : syracuseStep 4673639 = 7010459) B7010459
theorem B5761469 : Blo 1008601 5761469 := bstep (se 3 (by rfl) ⟨1080275, by rfl⟩ : syracuseStep 5761469 = 2160551) B2160551
theorem B5112233 : Blo 1008601 5112233 := bstep (se 2 (by rfl) ⟨1917087, by rfl⟩ : syracuseStep 5112233 = 3834175) B3834175
theorem B19400057 : Blo 1008601 19400057 := bstep (se 2 (by rfl) ⟨7275021, by rfl⟩ : syracuseStep 19400057 = 14550043) B14550043
theorem B3115759 : Blo 1008601 3115759 := bstep (se 1 (by rfl) ⟨2336819, by rfl⟩ : syracuseStep 3115759 = 4673639) B4673639
theorem B3840979 : Blo 1008601 3840979 := bstep (se 1 (by rfl) ⟨2880734, by rfl⟩ : syracuseStep 3840979 = 5761469) B5761469
theorem B2432159 : Blo 1008601 2432159 := bstep (se 1 (by rfl) ⟨1824119, by rfl⟩ : syracuseStep 2432159 = 3648239) B3648239
theorem B1516571 : Blo 1008601 1516571 := bstep (se 1 (by rfl) ⟨1137428, by rfl⟩ : syracuseStep 1516571 = 2274857) B2274857
theorem B2274587 : Blo 1008601 2274587 := bstep (se 1 (by rfl) ⟨1705940, by rfl⟩ : syracuseStep 2274587 = 3411881) B3411881
theorem B88592363 : Blo 1008601 88592363 := bstep (se 1 (by rfl) ⟨66444272, by rfl⟩ : syracuseStep 88592363 = 132888545) B132888545
theorem B1011183 : Blo 1008601 1011183 := bstep (se 1 (by rfl) ⟨758387, by rfl⟩ : syracuseStep 1011183 = 1516775) B1516775
theorem B1011559 : Blo 1008601 1011559 := bstep (se 1 (by rfl) ⟨758669, by rfl⟩ : syracuseStep 1011559 = 1517339) B1517339
theorem B65500103 : Blo 1008601 65500103 := bstep (se 1 (by rfl) ⟨49125077, by rfl⟩ : syracuseStep 65500103 = 98250155) B98250155
theorem B3408155 : Blo 1008601 3408155 := bstep (se 1 (by rfl) ⟨2556116, by rfl⟩ : syracuseStep 3408155 = 5112233) B5112233
theorem B1516391 : Blo 1008601 1516391 := bstep (se 1 (by rfl) ⟨1137293, by rfl⟩ : syracuseStep 1516391 = 2274587) B2274587
theorem B5121305 : Blo 1008601 5121305 := bstep (se 2 (by rfl) ⟨1920489, by rfl⟩ : syracuseStep 5121305 = 3840979) B3840979
theorem B59061575 : Blo 1008601 59061575 := bstep (se 1 (by rfl) ⟨44296181, by rfl⟩ : syracuseStep 59061575 = 88592363) B88592363
theorem B1621439 : Blo 1008601 1621439 := bstep (se 1 (by rfl) ⟨1216079, by rfl⟩ : syracuseStep 1621439 = 2432159) B2432159
theorem B43666735 : Blo 1008601 43666735 := bstep (se 1 (by rfl) ⟨32750051, by rfl⟩ : syracuseStep 43666735 = 65500103) B65500103
theorem B12933371 : Blo 1008601 12933371 := bstep (se 1 (by rfl) ⟨9700028, by rfl⟩ : syracuseStep 12933371 = 19400057) B19400057
theorem B4154345 : Blo 1008601 4154345 := bstep (se 2 (by rfl) ⟨1557879, by rfl⟩ : syracuseStep 4154345 = 3115759) B3115759
theorem B1011047 : Blo 1008601 1011047 := bstep (se 1 (by rfl) ⟨758285, by rfl⟩ : syracuseStep 1011047 = 1516571) B1516571
theorem B8622247 : Blo 1008601 8622247 := bstep (se 1 (by rfl) ⟨6466685, by rfl⟩ : syracuseStep 8622247 = 12933371) B12933371
theorem B3414203 : Blo 1008601 3414203 := bstep (se 1 (by rfl) ⟨2560652, by rfl⟩ : syracuseStep 3414203 = 5121305) B5121305
theorem B2272103 : Blo 1008601 2272103 := bstep (se 1 (by rfl) ⟨1704077, by rfl⟩ : syracuseStep 2272103 = 3408155) B3408155
theorem B2769563 : Blo 1008601 2769563 := bstep (se 1 (by rfl) ⟨2077172, by rfl⟩ : syracuseStep 2769563 = 4154345) B4154345
theorem B39374383 : Blo 1008601 39374383 := bstep (se 1 (by rfl) ⟨29530787, by rfl⟩ : syracuseStep 39374383 = 59061575) B59061575
theorem B58222313 : Blo 1008601 58222313 := bstep (se 2 (by rfl) ⟨21833367, by rfl⟩ : syracuseStep 58222313 = 43666735) B43666735
theorem B1010927 : Blo 1008601 1010927 := bstep (se 1 (by rfl) ⟨758195, by rfl⟩ : syracuseStep 1010927 = 1516391) B1516391
theorem B1080959 : Blo 1008601 1080959 := bstep (se 1 (by rfl) ⟨810719, by rfl⟩ : syracuseStep 1080959 = 1621439) B1621439
theorem B52499177 : Blo 1008601 52499177 := bstep (se 2 (by rfl) ⟨19687191, by rfl⟩ : syracuseStep 52499177 = 39374383) B39374383
theorem B1514735 : Blo 1008601 1514735 := bstep (se 1 (by rfl) ⟨1136051, by rfl⟩ : syracuseStep 1514735 = 2272103) B2272103
theorem B7385501 : Blo 1008601 7385501 := bstep (se 3 (by rfl) ⟨1384781, by rfl⟩ : syracuseStep 7385501 = 2769563) B2769563
theorem B2276135 : Blo 1008601 2276135 := bstep (se 1 (by rfl) ⟨1707101, by rfl⟩ : syracuseStep 2276135 = 3414203) B3414203
theorem B38814875 : Blo 1008601 38814875 := bstep (se 1 (by rfl) ⟨29111156, by rfl⟩ : syracuseStep 38814875 = 58222313) B58222313
theorem B11496329 : Blo 1008601 11496329 := bstep (se 2 (by rfl) ⟨4311123, by rfl⟩ : syracuseStep 11496329 = 8622247) B8622247
theorem B2882557 : Blo 1008601 2882557 := bstep (se 3 (by rfl) ⟨540479, by rfl⟩ : syracuseStep 2882557 = 1080959) B1080959
theorem B34999451 : Blo 1008601 34999451 := bstep (se 1 (by rfl) ⟨26249588, by rfl⟩ : syracuseStep 34999451 = 52499177) B52499177
theorem B4923667 : Blo 1008601 4923667 := bstep (se 1 (by rfl) ⟨3692750, by rfl⟩ : syracuseStep 4923667 = 7385501) B7385501
theorem B3843409 : Blo 1008601 3843409 := bstep (se 2 (by rfl) ⟨1441278, by rfl⟩ : syracuseStep 3843409 = 2882557) B2882557
theorem B1517423 : Blo 1008601 1517423 := bstep (se 1 (by rfl) ⟨1138067, by rfl⟩ : syracuseStep 1517423 = 2276135) B2276135
theorem B25876583 : Blo 1008601 25876583 := bstep (se 1 (by rfl) ⟨19407437, by rfl⟩ : syracuseStep 25876583 = 38814875) B38814875
theorem B1009823 : Blo 1008601 1009823 := bstep (se 1 (by rfl) ⟨757367, by rfl⟩ : syracuseStep 1009823 = 1514735) B1514735
theorem B7664219 : Blo 1008601 7664219 := bstep (se 1 (by rfl) ⟨5748164, by rfl⟩ : syracuseStep 7664219 = 11496329) B11496329
theorem B23332967 : Blo 1008601 23332967 := bstep (se 1 (by rfl) ⟨17499725, by rfl⟩ : syracuseStep 23332967 = 34999451) B34999451
theorem B26259557 : Blo 1008601 26259557 := bstep (se 4 (by rfl) ⟨2461833, by rfl⟩ : syracuseStep 26259557 = 4923667) B4923667
theorem B5124545 : Blo 1008601 5124545 := bstep (se 2 (by rfl) ⟨1921704, by rfl⟩ : syracuseStep 5124545 = 3843409) B3843409
theorem B17251055 : Blo 1008601 17251055 := bstep (se 1 (by rfl) ⟨12938291, by rfl⟩ : syracuseStep 17251055 = 25876583) B25876583
theorem B1011615 : Blo 1008601 1011615 := bstep (se 1 (by rfl) ⟨758711, by rfl⟩ : syracuseStep 1011615 = 1517423) B1517423
theorem B5109479 : Blo 1008601 5109479 := bstep (se 1 (by rfl) ⟨3832109, by rfl⟩ : syracuseStep 5109479 = 7664219) B7664219
theorem B70025485 : Blo 1008601 70025485 := bstep (se 3 (by rfl) ⟨13129778, by rfl⟩ : syracuseStep 70025485 = 26259557) B26259557
theorem B3416363 : Blo 1008601 3416363 := bstep (se 1 (by rfl) ⟨2562272, by rfl⟩ : syracuseStep 3416363 = 5124545) B5124545
theorem B15555311 : Blo 1008601 15555311 := bstep (se 1 (by rfl) ⟨11666483, by rfl⟩ : syracuseStep 15555311 = 23332967) B23332967
theorem B3406319 : Blo 1008601 3406319 := bstep (se 1 (by rfl) ⟨2554739, by rfl⟩ : syracuseStep 3406319 = 5109479) B5109479
theorem B11500703 : Blo 1008601 11500703 := bstep (se 1 (by rfl) ⟨8625527, by rfl⟩ : syracuseStep 11500703 = 17251055) B17251055
theorem B2270879 : Blo 1008601 2270879 := bstep (se 1 (by rfl) ⟨1703159, by rfl⟩ : syracuseStep 2270879 = 3406319) B3406319
theorem B93367313 : Blo 1008601 93367313 := bstep (se 2 (by rfl) ⟨35012742, by rfl⟩ : syracuseStep 93367313 = 70025485) B70025485
theorem B10370207 : Blo 1008601 10370207 := bstep (se 1 (by rfl) ⟨7777655, by rfl⟩ : syracuseStep 10370207 = 15555311) B15555311
theorem B2277575 : Blo 1008601 2277575 := bstep (se 1 (by rfl) ⟨1708181, by rfl⟩ : syracuseStep 2277575 = 3416363) B3416363
theorem B7667135 : Blo 1008601 7667135 := bstep (se 1 (by rfl) ⟨5750351, by rfl⟩ : syracuseStep 7667135 = 11500703) B11500703
theorem B1513919 : Blo 1008601 1513919 := bstep (se 1 (by rfl) ⟨1135439, by rfl⟩ : syracuseStep 1513919 = 2270879) B2270879
theorem B1518383 : Blo 1008601 1518383 := bstep (se 1 (by rfl) ⟨1138787, by rfl⟩ : syracuseStep 1518383 = 2277575) B2277575
theorem B62244875 : Blo 1008601 62244875 := bstep (se 1 (by rfl) ⟨46683656, by rfl⟩ : syracuseStep 62244875 = 93367313) B93367313
theorem B27653885 : Blo 1008601 27653885 := bstep (se 3 (by rfl) ⟨5185103, by rfl⟩ : syracuseStep 27653885 = 10370207) B10370207
theorem B5111423 : Blo 1008601 5111423 := bstep (se 1 (by rfl) ⟨3833567, by rfl⟩ : syracuseStep 5111423 = 7667135) B7667135
theorem B41496583 : Blo 1008601 41496583 := bstep (se 1 (by rfl) ⟨31122437, by rfl⟩ : syracuseStep 41496583 = 62244875) B62244875
theorem B18435923 : Blo 1008601 18435923 := bstep (se 1 (by rfl) ⟨13826942, by rfl⟩ : syracuseStep 18435923 = 27653885) B27653885
theorem B1009279 : Blo 1008601 1009279 := bstep (se 1 (by rfl) ⟨756959, by rfl⟩ : syracuseStep 1009279 = 1513919) B1513919
theorem B1012255 : Blo 1008601 1012255 := bstep (se 1 (by rfl) ⟨759191, by rfl⟩ : syracuseStep 1012255 = 1518383) B1518383
theorem B3407615 : Blo 1008601 3407615 := bstep (se 1 (by rfl) ⟨2555711, by rfl⟩ : syracuseStep 3407615 = 5111423) B5111423
theorem B12290615 : Blo 1008601 12290615 := bstep (se 1 (by rfl) ⟨9217961, by rfl⟩ : syracuseStep 12290615 = 18435923) B18435923
theorem B2271743 : Blo 1008601 2271743 := bstep (se 1 (by rfl) ⟨1703807, by rfl⟩ : syracuseStep 2271743 = 3407615) B3407615
theorem B55328777 : Blo 1008601 55328777 := bstep (se 2 (by rfl) ⟨20748291, by rfl⟩ : syracuseStep 55328777 = 41496583) B41496583
theorem B8193743 : Blo 1008601 8193743 := bstep (se 1 (by rfl) ⟨6145307, by rfl⟩ : syracuseStep 8193743 = 12290615) B12290615
theorem B1514495 : Blo 1008601 1514495 := bstep (se 1 (by rfl) ⟨1135871, by rfl⟩ : syracuseStep 1514495 = 2271743) B2271743
theorem B36885851 : Blo 1008601 36885851 := bstep (se 1 (by rfl) ⟨27664388, by rfl⟩ : syracuseStep 36885851 = 55328777) B55328777
theorem B24590567 : Blo 1008601 24590567 := bstep (se 1 (by rfl) ⟨18442925, by rfl⟩ : syracuseStep 24590567 = 36885851) B36885851
theorem B5462495 : Blo 1008601 5462495 := bstep (se 1 (by rfl) ⟨4096871, by rfl⟩ : syracuseStep 5462495 = 8193743) B8193743
theorem B1009663 : Blo 1008601 1009663 := bstep (se 1 (by rfl) ⟨757247, by rfl⟩ : syracuseStep 1009663 = 1514495) B1514495
theorem B3641663 : Blo 1008601 3641663 := bstep (se 1 (by rfl) ⟨2731247, by rfl⟩ : syracuseStep 3641663 = 5462495) B5462495
theorem B16393711 : Blo 1008601 16393711 := bstep (se 1 (by rfl) ⟨12295283, by rfl⟩ : syracuseStep 16393711 = 24590567) B24590567
theorem B21858281 : Blo 1008601 21858281 := bstep (se 2 (by rfl) ⟨8196855, by rfl⟩ : syracuseStep 21858281 = 16393711) B16393711
theorem B2427775 : Blo 1008601 2427775 := bstep (se 1 (by rfl) ⟨1820831, by rfl⟩ : syracuseStep 2427775 = 3641663) B3641663
theorem B12948133 : Blo 1008601 12948133 := bstep (se 4 (by rfl) ⟨1213887, by rfl⟩ : syracuseStep 12948133 = 2427775) B2427775
theorem B14572187 : Blo 1008601 14572187 := bstep (se 1 (by rfl) ⟨10929140, by rfl⟩ : syracuseStep 14572187 = 21858281) B21858281
theorem B9714791 : Blo 1008601 9714791 := bstep (se 1 (by rfl) ⟨7286093, by rfl⟩ : syracuseStep 9714791 = 14572187) B14572187
theorem B17264177 : Blo 1008601 17264177 := bstep (se 2 (by rfl) ⟨6474066, by rfl⟩ : syracuseStep 17264177 = 12948133) B12948133
theorem B11509451 : Blo 1008601 11509451 := bstep (se 1 (by rfl) ⟨8632088, by rfl⟩ : syracuseStep 11509451 = 17264177) B17264177
theorem B6476527 : Blo 1008601 6476527 := bstep (se 1 (by rfl) ⟨4857395, by rfl⟩ : syracuseStep 6476527 = 9714791) B9714791
theorem B7672967 : Blo 1008601 7672967 := bstep (se 1 (by rfl) ⟨5754725, by rfl⟩ : syracuseStep 7672967 = 11509451) B11509451
theorem B8635369 : Blo 1008601 8635369 := bstep (se 2 (by rfl) ⟨3238263, by rfl⟩ : syracuseStep 8635369 = 6476527) B6476527
theorem B5115311 : Blo 1008601 5115311 := bstep (se 1 (by rfl) ⟨3836483, by rfl⟩ : syracuseStep 5115311 = 7672967) B7672967
theorem B11513825 : Blo 1008601 11513825 := bstep (se 2 (by rfl) ⟨4317684, by rfl⟩ : syracuseStep 11513825 = 8635369) B8635369
theorem B3410207 : Blo 1008601 3410207 := bstep (se 1 (by rfl) ⟨2557655, by rfl⟩ : syracuseStep 3410207 = 5115311) B5115311
theorem B7675883 : Blo 1008601 7675883 := bstep (se 1 (by rfl) ⟨5756912, by rfl⟩ : syracuseStep 7675883 = 11513825) B11513825
theorem B5117255 : Blo 1008601 5117255 := bstep (se 1 (by rfl) ⟨3837941, by rfl⟩ : syracuseStep 5117255 = 7675883) B7675883
theorem B2273471 : Blo 1008601 2273471 := bstep (se 1 (by rfl) ⟨1705103, by rfl⟩ : syracuseStep 2273471 = 3410207) B3410207
theorem B3411503 : Blo 1008601 3411503 := bstep (se 1 (by rfl) ⟨2558627, by rfl⟩ : syracuseStep 3411503 = 5117255) B5117255
theorem B1515647 : Blo 1008601 1515647 := bstep (se 1 (by rfl) ⟨1136735, by rfl⟩ : syracuseStep 1515647 = 2273471) B2273471
theorem B2274335 : Blo 1008601 2274335 := bstep (se 1 (by rfl) ⟨1705751, by rfl⟩ : syracuseStep 2274335 = 3411503) B3411503
theorem B1010431 : Blo 1008601 1010431 := bstep (se 1 (by rfl) ⟨757823, by rfl⟩ : syracuseStep 1010431 = 1515647) B1515647
theorem B1516223 : Blo 1008601 1516223 := bstep (se 1 (by rfl) ⟨1137167, by rfl⟩ : syracuseStep 1516223 = 2274335) B2274335
theorem B1010815 : Blo 1008601 1010815 := bstep (se 1 (by rfl) ⟨758111, by rfl⟩ : syracuseStep 1010815 = 1516223) B1516223

theorem C0 (j : ℕ) (h1 : 252150 ≤ j) (h2 : j ≤ 252849) : Blo 1008601 (4 * j + 3) := by
  interval_cases j
  · exact B1008603
  · exact B1008607
  · exact B1008611
  · exact B1008615
  · exact B1008619
  · exact B1008623
  · exact B1008627
  · exact B1008631
  · exact B1008635
  · exact B1008639
  · exact B1008643
  · exact B1008647
  · exact B1008651
  · exact B1008655
  · exact B1008659
  · exact B1008663
  · exact B1008667
  · exact B1008671
  · exact B1008675
  · exact B1008679
  · exact B1008683
  · exact B1008687
  · exact B1008691
  · exact B1008695
  · exact B1008699
  · exact B1008703
  · exact B1008707
  · exact B1008711
  · exact B1008715
  · exact B1008719
  · exact B1008723
  · exact B1008727
  · exact B1008731
  · exact B1008735
  · exact B1008739
  · exact B1008743
  · exact B1008747
  · exact B1008751
  · exact B1008755
  · exact B1008759
  · exact B1008763
  · exact B1008767
  · exact B1008771
  · exact B1008775
  · exact B1008779
  · exact B1008783
  · exact B1008787
  · exact B1008791
  · exact B1008795
  · exact B1008799
  · exact B1008803
  · exact B1008807
  · exact B1008811
  · exact B1008815
  · exact B1008819
  · exact B1008823
  · exact B1008827
  · exact B1008831
  · exact B1008835
  · exact B1008839
  · exact B1008843
  · exact B1008847
  · exact B1008851
  · exact B1008855
  · exact B1008859
  · exact B1008863
  · exact B1008867
  · exact B1008871
  · exact B1008875
  · exact B1008879
  · exact B1008883
  · exact B1008887
  · exact B1008891
  · exact B1008895
  · exact B1008899
  · exact B1008903
  · exact B1008907
  · exact B1008911
  · exact B1008915
  · exact B1008919
  · exact B1008923
  · exact B1008927
  · exact B1008931
  · exact B1008935
  · exact B1008939
  · exact B1008943
  · exact B1008947
  · exact B1008951
  · exact B1008955
  · exact B1008959
  · exact B1008963
  · exact B1008967
  · exact B1008971
  · exact B1008975
  · exact B1008979
  · exact B1008983
  · exact B1008987
  · exact B1008991
  · exact B1008995
  · exact B1008999
  · exact B1009003
  · exact B1009007
  · exact B1009011
  · exact B1009015
  · exact B1009019
  · exact B1009023
  · exact B1009027
  · exact B1009031
  · exact B1009035
  · exact B1009039
  · exact B1009043
  · exact B1009047
  · exact B1009051
  · exact B1009055
  · exact B1009059
  · exact B1009063
  · exact B1009067
  · exact B1009071
  · exact B1009075
  · exact B1009079
  · exact B1009083
  · exact B1009087
  · exact B1009091
  · exact B1009095
  · exact B1009099
  · exact B1009103
  · exact B1009107
  · exact B1009111
  · exact B1009115
  · exact B1009119
  · exact B1009123
  · exact B1009127
  · exact B1009131
  · exact B1009135
  · exact B1009139
  · exact B1009143
  · exact B1009147
  · exact B1009151
  · exact B1009155
  · exact B1009159
  · exact B1009163
  · exact B1009167
  · exact B1009171
  · exact B1009175
  · exact B1009179
  · exact B1009183
  · exact B1009187
  · exact B1009191
  · exact B1009195
  · exact B1009199
  · exact B1009203
  · exact B1009207
  · exact B1009211
  · exact B1009215
  · exact B1009219
  · exact B1009223
  · exact B1009227
  · exact B1009231
  · exact B1009235
  · exact B1009239
  · exact B1009243
  · exact B1009247
  · exact B1009251
  · exact B1009255
  · exact B1009259
  · exact B1009263
  · exact B1009267
  · exact B1009271
  · exact B1009275
  · exact B1009279
  · exact B1009283
  · exact B1009287
  · exact B1009291
  · exact B1009295
  · exact B1009299
  · exact B1009303
  · exact B1009307
  · exact B1009311
  · exact B1009315
  · exact B1009319
  · exact B1009323
  · exact B1009327
  · exact B1009331
  · exact B1009335
  · exact B1009339
  · exact B1009343
  · exact B1009347
  · exact B1009351
  · exact B1009355
  · exact B1009359
  · exact B1009363
  · exact B1009367
  · exact B1009371
  · exact B1009375
  · exact B1009379
  · exact B1009383
  · exact B1009387
  · exact B1009391
  · exact B1009395
  · exact B1009399
  · exact B1009403
  · exact B1009407
  · exact B1009411
  · exact B1009415
  · exact B1009419
  · exact B1009423
  · exact B1009427
  · exact B1009431
  · exact B1009435
  · exact B1009439
  · exact B1009443
  · exact B1009447
  · exact B1009451
  · exact B1009455
  · exact B1009459
  · exact B1009463
  · exact B1009467
  · exact B1009471
  · exact B1009475
  · exact B1009479
  · exact B1009483
  · exact B1009487
  · exact B1009491
  · exact B1009495
  · exact B1009499
  · exact B1009503
  · exact B1009507
  · exact B1009511
  · exact B1009515
  · exact B1009519
  · exact B1009523
  · exact B1009527
  · exact B1009531
  · exact B1009535
  · exact B1009539
  · exact B1009543
  · exact B1009547
  · exact B1009551
  · exact B1009555
  · exact B1009559
  · exact B1009563
  · exact B1009567
  · exact B1009571
  · exact B1009575
  · exact B1009579
  · exact B1009583
  · exact B1009587
  · exact B1009591
  · exact B1009595
  · exact B1009599
  · exact B1009603
  · exact B1009607
  · exact B1009611
  · exact B1009615
  · exact B1009619
  · exact B1009623
  · exact B1009627
  · exact B1009631
  · exact B1009635
  · exact B1009639
  · exact B1009643
  · exact B1009647
  · exact B1009651
  · exact B1009655
  · exact B1009659
  · exact B1009663
  · exact B1009667
  · exact B1009671
  · exact B1009675
  · exact B1009679
  · exact B1009683
  · exact B1009687
  · exact B1009691
  · exact B1009695
  · exact B1009699
  · exact B1009703
  · exact B1009707
  · exact B1009711
  · exact B1009715
  · exact B1009719
  · exact B1009723
  · exact B1009727
  · exact B1009731
  · exact B1009735
  · exact B1009739
  · exact B1009743
  · exact B1009747
  · exact B1009751
  · exact B1009755
  · exact B1009759
  · exact B1009763
  · exact B1009767
  · exact B1009771
  · exact B1009775
  · exact B1009779
  · exact B1009783
  · exact B1009787
  · exact B1009791
  · exact B1009795
  · exact B1009799
  · exact B1009803
  · exact B1009807
  · exact B1009811
  · exact B1009815
  · exact B1009819
  · exact B1009823
  · exact B1009827
  · exact B1009831
  · exact B1009835
  · exact B1009839
  · exact B1009843
  · exact B1009847
  · exact B1009851
  · exact B1009855
  · exact B1009859
  · exact B1009863
  · exact B1009867
  · exact B1009871
  · exact B1009875
  · exact B1009879
  · exact B1009883
  · exact B1009887
  · exact B1009891
  · exact B1009895
  · exact B1009899
  · exact B1009903
  · exact B1009907
  · exact B1009911
  · exact B1009915
  · exact B1009919
  · exact B1009923
  · exact B1009927
  · exact B1009931
  · exact B1009935
  · exact B1009939
  · exact B1009943
  · exact B1009947
  · exact B1009951
  · exact B1009955
  · exact B1009959
  · exact B1009963
  · exact B1009967
  · exact B1009971
  · exact B1009975
  · exact B1009979
  · exact B1009983
  · exact B1009987
  · exact B1009991
  · exact B1009995
  · exact B1009999
  · exact B1010003
  · exact B1010007
  · exact B1010011
  · exact B1010015
  · exact B1010019
  · exact B1010023
  · exact B1010027
  · exact B1010031
  · exact B1010035
  · exact B1010039
  · exact B1010043
  · exact B1010047
  · exact B1010051
  · exact B1010055
  · exact B1010059
  · exact B1010063
  · exact B1010067
  · exact B1010071
  · exact B1010075
  · exact B1010079
  · exact B1010083
  · exact B1010087
  · exact B1010091
  · exact B1010095
  · exact B1010099
  · exact B1010103
  · exact B1010107
  · exact B1010111
  · exact B1010115
  · exact B1010119
  · exact B1010123
  · exact B1010127
  · exact B1010131
  · exact B1010135
  · exact B1010139
  · exact B1010143
  · exact B1010147
  · exact B1010151
  · exact B1010155
  · exact B1010159
  · exact B1010163
  · exact B1010167
  · exact B1010171
  · exact B1010175
  · exact B1010179
  · exact B1010183
  · exact B1010187
  · exact B1010191
  · exact B1010195
  · exact B1010199
  · exact B1010203
  · exact B1010207
  · exact B1010211
  · exact B1010215
  · exact B1010219
  · exact B1010223
  · exact B1010227
  · exact B1010231
  · exact B1010235
  · exact B1010239
  · exact B1010243
  · exact B1010247
  · exact B1010251
  · exact B1010255
  · exact B1010259
  · exact B1010263
  · exact B1010267
  · exact B1010271
  · exact B1010275
  · exact B1010279
  · exact B1010283
  · exact B1010287
  · exact B1010291
  · exact B1010295
  · exact B1010299
  · exact B1010303
  · exact B1010307
  · exact B1010311
  · exact B1010315
  · exact B1010319
  · exact B1010323
  · exact B1010327
  · exact B1010331
  · exact B1010335
  · exact B1010339
  · exact B1010343
  · exact B1010347
  · exact B1010351
  · exact B1010355
  · exact B1010359
  · exact B1010363
  · exact B1010367
  · exact B1010371
  · exact B1010375
  · exact B1010379
  · exact B1010383
  · exact B1010387
  · exact B1010391
  · exact B1010395
  · exact B1010399
  · exact B1010403
  · exact B1010407
  · exact B1010411
  · exact B1010415
  · exact B1010419
  · exact B1010423
  · exact B1010427
  · exact B1010431
  · exact B1010435
  · exact B1010439
  · exact B1010443
  · exact B1010447
  · exact B1010451
  · exact B1010455
  · exact B1010459
  · exact B1010463
  · exact B1010467
  · exact B1010471
  · exact B1010475
  · exact B1010479
  · exact B1010483
  · exact B1010487
  · exact B1010491
  · exact B1010495
  · exact B1010499
  · exact B1010503
  · exact B1010507
  · exact B1010511
  · exact B1010515
  · exact B1010519
  · exact B1010523
  · exact B1010527
  · exact B1010531
  · exact B1010535
  · exact B1010539
  · exact B1010543
  · exact B1010547
  · exact B1010551
  · exact B1010555
  · exact B1010559
  · exact B1010563
  · exact B1010567
  · exact B1010571
  · exact B1010575
  · exact B1010579
  · exact B1010583
  · exact B1010587
  · exact B1010591
  · exact B1010595
  · exact B1010599
  · exact B1010603
  · exact B1010607
  · exact B1010611
  · exact B1010615
  · exact B1010619
  · exact B1010623
  · exact B1010627
  · exact B1010631
  · exact B1010635
  · exact B1010639
  · exact B1010643
  · exact B1010647
  · exact B1010651
  · exact B1010655
  · exact B1010659
  · exact B1010663
  · exact B1010667
  · exact B1010671
  · exact B1010675
  · exact B1010679
  · exact B1010683
  · exact B1010687
  · exact B1010691
  · exact B1010695
  · exact B1010699
  · exact B1010703
  · exact B1010707
  · exact B1010711
  · exact B1010715
  · exact B1010719
  · exact B1010723
  · exact B1010727
  · exact B1010731
  · exact B1010735
  · exact B1010739
  · exact B1010743
  · exact B1010747
  · exact B1010751
  · exact B1010755
  · exact B1010759
  · exact B1010763
  · exact B1010767
  · exact B1010771
  · exact B1010775
  · exact B1010779
  · exact B1010783
  · exact B1010787
  · exact B1010791
  · exact B1010795
  · exact B1010799
  · exact B1010803
  · exact B1010807
  · exact B1010811
  · exact B1010815
  · exact B1010819
  · exact B1010823
  · exact B1010827
  · exact B1010831
  · exact B1010835
  · exact B1010839
  · exact B1010843
  · exact B1010847
  · exact B1010851
  · exact B1010855
  · exact B1010859
  · exact B1010863
  · exact B1010867
  · exact B1010871
  · exact B1010875
  · exact B1010879
  · exact B1010883
  · exact B1010887
  · exact B1010891
  · exact B1010895
  · exact B1010899
  · exact B1010903
  · exact B1010907
  · exact B1010911
  · exact B1010915
  · exact B1010919
  · exact B1010923
  · exact B1010927
  · exact B1010931
  · exact B1010935
  · exact B1010939
  · exact B1010943
  · exact B1010947
  · exact B1010951
  · exact B1010955
  · exact B1010959
  · exact B1010963
  · exact B1010967
  · exact B1010971
  · exact B1010975
  · exact B1010979
  · exact B1010983
  · exact B1010987
  · exact B1010991
  · exact B1010995
  · exact B1010999
  · exact B1011003
  · exact B1011007
  · exact B1011011
  · exact B1011015
  · exact B1011019
  · exact B1011023
  · exact B1011027
  · exact B1011031
  · exact B1011035
  · exact B1011039
  · exact B1011043
  · exact B1011047
  · exact B1011051
  · exact B1011055
  · exact B1011059
  · exact B1011063
  · exact B1011067
  · exact B1011071
  · exact B1011075
  · exact B1011079
  · exact B1011083
  · exact B1011087
  · exact B1011091
  · exact B1011095
  · exact B1011099
  · exact B1011103
  · exact B1011107
  · exact B1011111
  · exact B1011115
  · exact B1011119
  · exact B1011123
  · exact B1011127
  · exact B1011131
  · exact B1011135
  · exact B1011139
  · exact B1011143
  · exact B1011147
  · exact B1011151
  · exact B1011155
  · exact B1011159
  · exact B1011163
  · exact B1011167
  · exact B1011171
  · exact B1011175
  · exact B1011179
  · exact B1011183
  · exact B1011187
  · exact B1011191
  · exact B1011195
  · exact B1011199
  · exact B1011203
  · exact B1011207
  · exact B1011211
  · exact B1011215
  · exact B1011219
  · exact B1011223
  · exact B1011227
  · exact B1011231
  · exact B1011235
  · exact B1011239
  · exact B1011243
  · exact B1011247
  · exact B1011251
  · exact B1011255
  · exact B1011259
  · exact B1011263
  · exact B1011267
  · exact B1011271
  · exact B1011275
  · exact B1011279
  · exact B1011283
  · exact B1011287
  · exact B1011291
  · exact B1011295
  · exact B1011299
  · exact B1011303
  · exact B1011307
  · exact B1011311
  · exact B1011315
  · exact B1011319
  · exact B1011323
  · exact B1011327
  · exact B1011331
  · exact B1011335
  · exact B1011339
  · exact B1011343
  · exact B1011347
  · exact B1011351
  · exact B1011355
  · exact B1011359
  · exact B1011363
  · exact B1011367
  · exact B1011371
  · exact B1011375
  · exact B1011379
  · exact B1011383
  · exact B1011387
  · exact B1011391
  · exact B1011395
  · exact B1011399

theorem C1 (j : ℕ) (h1 : 252850 ≤ j) (h2 : j ≤ 253149) : Blo 1008601 (4 * j + 3) := by
  interval_cases j
  · exact B1011403
  · exact B1011407
  · exact B1011411
  · exact B1011415
  · exact B1011419
  · exact B1011423
  · exact B1011427
  · exact B1011431
  · exact B1011435
  · exact B1011439
  · exact B1011443
  · exact B1011447
  · exact B1011451
  · exact B1011455
  · exact B1011459
  · exact B1011463
  · exact B1011467
  · exact B1011471
  · exact B1011475
  · exact B1011479
  · exact B1011483
  · exact B1011487
  · exact B1011491
  · exact B1011495
  · exact B1011499
  · exact B1011503
  · exact B1011507
  · exact B1011511
  · exact B1011515
  · exact B1011519
  · exact B1011523
  · exact B1011527
  · exact B1011531
  · exact B1011535
  · exact B1011539
  · exact B1011543
  · exact B1011547
  · exact B1011551
  · exact B1011555
  · exact B1011559
  · exact B1011563
  · exact B1011567
  · exact B1011571
  · exact B1011575
  · exact B1011579
  · exact B1011583
  · exact B1011587
  · exact B1011591
  · exact B1011595
  · exact B1011599
  · exact B1011603
  · exact B1011607
  · exact B1011611
  · exact B1011615
  · exact B1011619
  · exact B1011623
  · exact B1011627
  · exact B1011631
  · exact B1011635
  · exact B1011639
  · exact B1011643
  · exact B1011647
  · exact B1011651
  · exact B1011655
  · exact B1011659
  · exact B1011663
  · exact B1011667
  · exact B1011671
  · exact B1011675
  · exact B1011679
  · exact B1011683
  · exact B1011687
  · exact B1011691
  · exact B1011695
  · exact B1011699
  · exact B1011703
  · exact B1011707
  · exact B1011711
  · exact B1011715
  · exact B1011719
  · exact B1011723
  · exact B1011727
  · exact B1011731
  · exact B1011735
  · exact B1011739
  · exact B1011743
  · exact B1011747
  · exact B1011751
  · exact B1011755
  · exact B1011759
  · exact B1011763
  · exact B1011767
  · exact B1011771
  · exact B1011775
  · exact B1011779
  · exact B1011783
  · exact B1011787
  · exact B1011791
  · exact B1011795
  · exact B1011799
  · exact B1011803
  · exact B1011807
  · exact B1011811
  · exact B1011815
  · exact B1011819
  · exact B1011823
  · exact B1011827
  · exact B1011831
  · exact B1011835
  · exact B1011839
  · exact B1011843
  · exact B1011847
  · exact B1011851
  · exact B1011855
  · exact B1011859
  · exact B1011863
  · exact B1011867
  · exact B1011871
  · exact B1011875
  · exact B1011879
  · exact B1011883
  · exact B1011887
  · exact B1011891
  · exact B1011895
  · exact B1011899
  · exact B1011903
  · exact B1011907
  · exact B1011911
  · exact B1011915
  · exact B1011919
  · exact B1011923
  · exact B1011927
  · exact B1011931
  · exact B1011935
  · exact B1011939
  · exact B1011943
  · exact B1011947
  · exact B1011951
  · exact B1011955
  · exact B1011959
  · exact B1011963
  · exact B1011967
  · exact B1011971
  · exact B1011975
  · exact B1011979
  · exact B1011983
  · exact B1011987
  · exact B1011991
  · exact B1011995
  · exact B1011999
  · exact B1012003
  · exact B1012007
  · exact B1012011
  · exact B1012015
  · exact B1012019
  · exact B1012023
  · exact B1012027
  · exact B1012031
  · exact B1012035
  · exact B1012039
  · exact B1012043
  · exact B1012047
  · exact B1012051
  · exact B1012055
  · exact B1012059
  · exact B1012063
  · exact B1012067
  · exact B1012071
  · exact B1012075
  · exact B1012079
  · exact B1012083
  · exact B1012087
  · exact B1012091
  · exact B1012095
  · exact B1012099
  · exact B1012103
  · exact B1012107
  · exact B1012111
  · exact B1012115
  · exact B1012119
  · exact B1012123
  · exact B1012127
  · exact B1012131
  · exact B1012135
  · exact B1012139
  · exact B1012143
  · exact B1012147
  · exact B1012151
  · exact B1012155
  · exact B1012159
  · exact B1012163
  · exact B1012167
  · exact B1012171
  · exact B1012175
  · exact B1012179
  · exact B1012183
  · exact B1012187
  · exact B1012191
  · exact B1012195
  · exact B1012199
  · exact B1012203
  · exact B1012207
  · exact B1012211
  · exact B1012215
  · exact B1012219
  · exact B1012223
  · exact B1012227
  · exact B1012231
  · exact B1012235
  · exact B1012239
  · exact B1012243
  · exact B1012247
  · exact B1012251
  · exact B1012255
  · exact B1012259
  · exact B1012263
  · exact B1012267
  · exact B1012271
  · exact B1012275
  · exact B1012279
  · exact B1012283
  · exact B1012287
  · exact B1012291
  · exact B1012295
  · exact B1012299
  · exact B1012303
  · exact B1012307
  · exact B1012311
  · exact B1012315
  · exact B1012319
  · exact B1012323
  · exact B1012327
  · exact B1012331
  · exact B1012335
  · exact B1012339
  · exact B1012343
  · exact B1012347
  · exact B1012351
  · exact B1012355
  · exact B1012359
  · exact B1012363
  · exact B1012367
  · exact B1012371
  · exact B1012375
  · exact B1012379
  · exact B1012383
  · exact B1012387
  · exact B1012391
  · exact B1012395
  · exact B1012399
  · exact B1012403
  · exact B1012407
  · exact B1012411
  · exact B1012415
  · exact B1012419
  · exact B1012423
  · exact B1012427
  · exact B1012431
  · exact B1012435
  · exact B1012439
  · exact B1012443
  · exact B1012447
  · exact B1012451
  · exact B1012455
  · exact B1012459
  · exact B1012463
  · exact B1012467
  · exact B1012471
  · exact B1012475
  · exact B1012479
  · exact B1012483
  · exact B1012487
  · exact B1012491
  · exact B1012495
  · exact B1012499
  · exact B1012503
  · exact B1012507
  · exact B1012511
  · exact B1012515
  · exact B1012519
  · exact B1012523
  · exact B1012527
  · exact B1012531
  · exact B1012535
  · exact B1012539
  · exact B1012543
  · exact B1012547
  · exact B1012551
  · exact B1012555
  · exact B1012559
  · exact B1012563
  · exact B1012567
  · exact B1012571
  · exact B1012575
  · exact B1012579
  · exact B1012583
  · exact B1012587
  · exact B1012591
  · exact B1012595
  · exact B1012599

theorem solution (m : ℕ) (hlo : 1008601 ≤ m) (hhi : m ≤ 1012601) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 252150 ≤ j := by omega
    have hj2 : j ≤ 253149 := by omega
    have hb : Blo 1008601 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 252850 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
