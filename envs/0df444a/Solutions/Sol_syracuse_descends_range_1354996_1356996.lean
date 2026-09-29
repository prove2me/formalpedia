-- Prove2me | solution 1 for syracuse_descends_range_1354996_1356996
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:52.965147+00:00
-- url     : https://prove2.me/submissions/53b9178e-6681-49b2-8180-62f66828053f

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


theorem B7725077 : Blo 1354996 7725077 := bbase (se 6 (by rfl) ⟨181056, by rfl⟩ : syracuseStep 7725077 = 362113) (by norm_num)
theorem B4341845 : Blo 1354996 4341845 := bbase (se 8 (by rfl) ⟨25440, by rfl⟩ : syracuseStep 4341845 = 50881) (by norm_num)
theorem B3432557 : Blo 1354996 3432557 := bbase (se 3 (by rfl) ⟨643604, by rfl⟩ : syracuseStep 3432557 = 1287209) (by norm_num)
theorem B2171141 : Blo 1354996 2171141 := bbase (se 4 (by rfl) ⟨203544, by rfl⟩ : syracuseStep 2171141 = 407089) (by norm_num)
theorem B2572573 : Blo 1354996 2572573 := bbase (se 3 (by rfl) ⟨482357, by rfl⟩ : syracuseStep 2572573 = 964715) (by norm_num)
theorem B5144917 : Blo 1354996 5144917 := bbase (se 10 (by rfl) ⟨7536, by rfl⟩ : syracuseStep 5144917 = 15073) (by norm_num)
theorem B4579685 : Blo 1354996 4579685 := bbase (se 4 (by rfl) ⟨429345, by rfl⟩ : syracuseStep 4579685 = 858691) (by norm_num)
theorem B2572717 : Blo 1354996 2572717 := bbase (se 3 (by rfl) ⟨482384, by rfl⟩ : syracuseStep 2572717 = 964769) (by norm_num)
theorem B2171333 : Blo 1354996 2171333 := bbase (se 4 (by rfl) ⟨203562, by rfl⟩ : syracuseStep 2171333 = 407125) (by norm_num)
theorem B3432901 : Blo 1354996 3432901 := bbase (se 4 (by rfl) ⟨321834, by rfl⟩ : syracuseStep 3432901 = 643669) (by norm_num)
theorem B6865397 : Blo 1354996 6865397 := bbase (se 5 (by rfl) ⟨321815, by rfl⟩ : syracuseStep 6865397 = 643631) (by norm_num)
theorem B3433013 : Blo 1354996 3433013 := bbase (se 5 (by rfl) ⟨160922, by rfl⟩ : syracuseStep 3433013 = 321845) (by norm_num)
theorem B2171461 : Blo 1354996 2171461 := bbase (se 4 (by rfl) ⟨203574, by rfl⟩ : syracuseStep 2171461 = 407149) (by norm_num)
theorem B2572877 : Blo 1354996 2572877 := bbase (se 3 (by rfl) ⟨482414, by rfl⟩ : syracuseStep 2572877 = 964829) (by norm_num)
theorem B4342357 : Blo 1354996 4342357 := bbase (se 8 (by rfl) ⟨25443, by rfl⟩ : syracuseStep 4342357 = 50887) (by norm_num)
theorem B1466993 : Blo 1354996 1466993 := bbase (se 2 (by rfl) ⟨550122, by rfl⟩ : syracuseStep 1466993 = 1100245) (by norm_num)
theorem B5145221 : Blo 1354996 5145221 := bbase (se 4 (by rfl) ⟨482364, by rfl⟩ : syracuseStep 5145221 = 964729) (by norm_num)
theorem B1524397 : Blo 1354996 1524397 := bbase (se 3 (by rfl) ⟨285824, by rfl⟩ : syracuseStep 1524397 = 571649) (by norm_num)
theorem B1524433 : Blo 1354996 1524433 := bbase (se 2 (by rfl) ⟨571662, by rfl⟩ : syracuseStep 1524433 = 1143325) (by norm_num)
theorem B6513365 : Blo 1354996 6513365 := bbase (se 7 (by rfl) ⟨76328, by rfl⟩ : syracuseStep 6513365 = 152657) (by norm_num)
theorem B2573021 : Blo 1354996 2573021 := bbase (se 3 (by rfl) ⟨482441, by rfl⟩ : syracuseStep 2573021 = 964883) (by norm_num)
theorem B1524469 : Blo 1354996 1524469 := bbase (se 5 (by rfl) ⟨71459, by rfl⟩ : syracuseStep 1524469 = 142919) (by norm_num)
theorem B3433205 : Blo 1354996 3433205 := bbase (se 5 (by rfl) ⟨160931, by rfl⟩ : syracuseStep 3433205 = 321863) (by norm_num)
theorem B1524505 : Blo 1354996 1524505 := bbase (se 2 (by rfl) ⟨571689, by rfl⟩ : syracuseStep 1524505 = 1143379) (by norm_num)
theorem B1524541 : Blo 1354996 1524541 := bbase (se 3 (by rfl) ⟨285851, by rfl⟩ : syracuseStep 1524541 = 571703) (by norm_num)
theorem B1524577 : Blo 1354996 1524577 := bbase (se 2 (by rfl) ⟨571716, by rfl⟩ : syracuseStep 1524577 = 1143433) (by norm_num)
theorem B1467253 : Blo 1354996 1467253 := bbase (se 5 (by rfl) ⟨68777, by rfl⟩ : syracuseStep 1467253 = 137555) (by norm_num)
theorem B2032517 : Blo 1354996 2032517 := bbase (se 4 (by rfl) ⟨190548, by rfl⟩ : syracuseStep 2032517 = 381097) (by norm_num)
theorem B1524613 : Blo 1354996 1524613 := bbase (se 4 (by rfl) ⟨142932, by rfl⟩ : syracuseStep 1524613 = 285865) (by norm_num)
theorem B2032541 : Blo 1354996 2032541 := bbase (se 3 (by rfl) ⟨381101, by rfl⟩ : syracuseStep 2032541 = 762203) (by norm_num)
theorem B1524649 : Blo 1354996 1524649 := bbase (se 2 (by rfl) ⟨571743, by rfl⟩ : syracuseStep 1524649 = 1143487) (by norm_num)
theorem B2032565 : Blo 1354996 2032565 := bbase (se 5 (by rfl) ⟨95276, by rfl⟩ : syracuseStep 2032565 = 190553) (by norm_num)
theorem B2032589 : Blo 1354996 2032589 := bbase (se 3 (by rfl) ⟨381110, by rfl⟩ : syracuseStep 2032589 = 762221) (by norm_num)
theorem B1524685 : Blo 1354996 1524685 := bbase (se 3 (by rfl) ⟨285878, by rfl⟩ : syracuseStep 1524685 = 571757) (by norm_num)
theorem B2032613 : Blo 1354996 2032613 := bbase (se 4 (by rfl) ⟨190557, by rfl⟩ : syracuseStep 2032613 = 381115) (by norm_num)
theorem B1524721 : Blo 1354996 1524721 := bbase (se 2 (by rfl) ⟨571770, by rfl⟩ : syracuseStep 1524721 = 1143541) (by norm_num)
theorem B2032637 : Blo 1354996 2032637 := bbase (se 3 (by rfl) ⟨381119, by rfl⟩ : syracuseStep 2032637 = 762239) (by norm_num)
theorem B2286589 : Blo 1354996 2286589 := bbase (se 3 (by rfl) ⟨428735, by rfl⟩ : syracuseStep 2286589 = 857471) (by norm_num)
theorem B2573309 : Blo 1354996 2573309 := bbase (se 3 (by rfl) ⟨482495, by rfl⟩ : syracuseStep 2573309 = 964991) (by norm_num)
theorem B2032661 : Blo 1354996 2032661 := bbase (se 6 (by rfl) ⟨47640, by rfl⟩ : syracuseStep 2032661 = 95281) (by norm_num)
theorem B1524757 : Blo 1354996 1524757 := bbase (se 6 (by rfl) ⟨35736, by rfl⟩ : syracuseStep 1524757 = 71473) (by norm_num)
theorem B2032685 : Blo 1354996 2032685 := bbase (se 3 (by rfl) ⟨381128, by rfl⟩ : syracuseStep 2032685 = 762257) (by norm_num)
theorem B1524793 : Blo 1354996 1524793 := bbase (se 2 (by rfl) ⟨571797, by rfl⟩ : syracuseStep 1524793 = 1143595) (by norm_num)
theorem B2032709 : Blo 1354996 2032709 := bbase (se 4 (by rfl) ⟨190566, by rfl⟩ : syracuseStep 2032709 = 381133) (by norm_num)
theorem B2442317 : Blo 1354996 2442317 := bbase (se 3 (by rfl) ⟨457934, by rfl⟩ : syracuseStep 2442317 = 915869) (by norm_num)
theorem B3433549 : Blo 1354996 3433549 := bbase (se 3 (by rfl) ⟨643790, by rfl⟩ : syracuseStep 3433549 = 1287581) (by norm_num)
theorem B2286677 : Blo 1354996 2286677 := bbase (se 8 (by rfl) ⟨13398, by rfl⟩ : syracuseStep 2286677 = 26797) (by norm_num)
theorem B2319445 : Blo 1354996 2319445 := bbase (se 8 (by rfl) ⟨13590, by rfl⟩ : syracuseStep 2319445 = 27181) (by norm_num)
theorem B2032733 : Blo 1354996 2032733 := bbase (se 3 (by rfl) ⟨381137, by rfl⟩ : syracuseStep 2032733 = 762275) (by norm_num)
theorem B1524829 : Blo 1354996 1524829 := bbase (se 3 (by rfl) ⟨285905, by rfl⟩ : syracuseStep 1524829 = 571811) (by norm_num)
theorem B2032757 : Blo 1354996 2032757 := bbase (se 5 (by rfl) ⟨95285, by rfl⟩ : syracuseStep 2032757 = 190571) (by norm_num)
theorem B1524865 : Blo 1354996 1524865 := bbase (se 2 (by rfl) ⟨571824, by rfl⟩ : syracuseStep 1524865 = 1143649) (by norm_num)
theorem B3859589 : Blo 1354996 3859589 := bbase (se 4 (by rfl) ⟨361836, by rfl⟩ : syracuseStep 3859589 = 723673) (by norm_num)
theorem B2032781 : Blo 1354996 2032781 := bbase (se 3 (by rfl) ⟨381146, by rfl⟩ : syracuseStep 2032781 = 762293) (by norm_num)
theorem B2573461 : Blo 1354996 2573461 := bbase (se 6 (by rfl) ⟨60315, by rfl⟩ : syracuseStep 2573461 = 120631) (by norm_num)
theorem B2032805 : Blo 1354996 2032805 := bbase (se 4 (by rfl) ⟨190575, by rfl⟩ : syracuseStep 2032805 = 381151) (by norm_num)
theorem B1524901 : Blo 1354996 1524901 := bbase (se 4 (by rfl) ⟨142959, by rfl⟩ : syracuseStep 1524901 = 285919) (by norm_num)
theorem B2032829 : Blo 1354996 2032829 := bbase (se 3 (by rfl) ⟨381155, by rfl⟩ : syracuseStep 2032829 = 762311) (by norm_num)
theorem B3433661 : Blo 1354996 3433661 := bbase (se 3 (by rfl) ⟨643811, by rfl⟩ : syracuseStep 3433661 = 1287623) (by norm_num)
theorem B2172101 : Blo 1354996 2172101 := bbase (se 4 (by rfl) ⟨203634, by rfl⟩ : syracuseStep 2172101 = 407269) (by norm_num)
theorem B1524937 : Blo 1354996 1524937 := bbase (se 2 (by rfl) ⟨571851, by rfl⟩ : syracuseStep 1524937 = 1143703) (by norm_num)
theorem B2286805 : Blo 1354996 2286805 := bbase (se 7 (by rfl) ⟨26798, by rfl⟩ : syracuseStep 2286805 = 53597) (by norm_num)
theorem B2032853 : Blo 1354996 2032853 := bbase (se 7 (by rfl) ⟨23822, by rfl⟩ : syracuseStep 2032853 = 47645) (by norm_num)
theorem B2032877 : Blo 1354996 2032877 := bbase (se 3 (by rfl) ⟨381164, by rfl⟩ : syracuseStep 2032877 = 762329) (by norm_num)
theorem B1524973 : Blo 1354996 1524973 := bbase (se 3 (by rfl) ⟨285932, by rfl⟩ : syracuseStep 1524973 = 571865) (by norm_num)
theorem B2032901 : Blo 1354996 2032901 := bbase (se 4 (by rfl) ⟨190584, by rfl⟩ : syracuseStep 2032901 = 381169) (by norm_num)
theorem B1525009 : Blo 1354996 1525009 := bbase (se 2 (by rfl) ⟨571878, by rfl⟩ : syracuseStep 1525009 = 1143757) (by norm_num)
theorem B2032925 : Blo 1354996 2032925 := bbase (se 3 (by rfl) ⟨381173, by rfl⟩ : syracuseStep 2032925 = 762347) (by norm_num)
theorem B3048749 : Blo 1354996 3048749 := bbase (se 3 (by rfl) ⟨571640, by rfl⟩ : syracuseStep 3048749 = 1143281) (by norm_num)
theorem B2286893 : Blo 1354996 2286893 := bbase (se 3 (by rfl) ⟨428792, by rfl⟩ : syracuseStep 2286893 = 857585) (by norm_num)
theorem B2032949 : Blo 1354996 2032949 := bbase (se 5 (by rfl) ⟨95294, by rfl⟩ : syracuseStep 2032949 = 190589) (by norm_num)
theorem B1525045 : Blo 1354996 1525045 := bbase (se 5 (by rfl) ⟨71486, by rfl⟩ : syracuseStep 1525045 = 142973) (by norm_num)
theorem B2032973 : Blo 1354996 2032973 := bbase (se 3 (by rfl) ⟨381182, by rfl⟩ : syracuseStep 2032973 = 762365) (by norm_num)
theorem B1525081 : Blo 1354996 1525081 := bbase (se 2 (by rfl) ⟨571905, by rfl⟩ : syracuseStep 1525081 = 1143811) (by norm_num)
theorem B2032997 : Blo 1354996 2032997 := bbase (se 4 (by rfl) ⟨190593, by rfl⟩ : syracuseStep 2032997 = 381187) (by norm_num)
theorem B3048821 : Blo 1354996 3048821 := bbase (se 5 (by rfl) ⟨142913, by rfl⟩ : syracuseStep 3048821 = 285827) (by norm_num)
theorem B2033021 : Blo 1354996 2033021 := bbase (se 3 (by rfl) ⟨381191, by rfl⟩ : syracuseStep 2033021 = 762383) (by norm_num)
theorem B1525117 : Blo 1354996 1525117 := bbase (se 3 (by rfl) ⟨285959, by rfl⟩ : syracuseStep 1525117 = 571919) (by norm_num)
theorem B3433853 : Blo 1354996 3433853 := bbase (se 3 (by rfl) ⟨643847, by rfl⟩ : syracuseStep 3433853 = 1287695) (by norm_num)
theorem B2033045 : Blo 1354996 2033045 := bbase (se 6 (by rfl) ⟨47649, by rfl⟩ : syracuseStep 2033045 = 95299) (by norm_num)
theorem B1525153 : Blo 1354996 1525153 := bbase (se 2 (by rfl) ⟨571932, by rfl⟩ : syracuseStep 1525153 = 1143865) (by norm_num)
theorem B2287021 : Blo 1354996 2287021 := bbase (se 3 (by rfl) ⟨428816, by rfl⟩ : syracuseStep 2287021 = 857633) (by norm_num)
theorem B2033069 : Blo 1354996 2033069 := bbase (se 3 (by rfl) ⟨381200, by rfl⟩ : syracuseStep 2033069 = 762401) (by norm_num)
theorem B12371381 : Blo 1354996 12371381 := bbase (se 5 (by rfl) ⟨579908, by rfl⟩ : syracuseStep 12371381 = 1159817) (by norm_num)
theorem B3048893 : Blo 1354996 3048893 := bbase (se 3 (by rfl) ⟨571667, by rfl⟩ : syracuseStep 3048893 = 1143335) (by norm_num)
theorem B2033093 : Blo 1354996 2033093 := bbase (se 4 (by rfl) ⟨190602, by rfl⟩ : syracuseStep 2033093 = 381205) (by norm_num)
theorem B1525189 : Blo 1354996 1525189 := bbase (se 4 (by rfl) ⟨142986, by rfl⟩ : syracuseStep 1525189 = 285973) (by norm_num)
theorem B2573765 : Blo 1354996 2573765 := bbase (se 4 (by rfl) ⟨241290, by rfl⟩ : syracuseStep 2573765 = 482581) (by norm_num)
theorem B37094869 : Blo 1354996 37094869 := bbase (se 7 (by rfl) ⟨434705, by rfl⟩ : syracuseStep 37094869 = 869411) (by norm_num)
theorem B2033117 : Blo 1354996 2033117 := bbase (se 3 (by rfl) ⟨381209, by rfl⟩ : syracuseStep 2033117 = 762419) (by norm_num)
theorem B1525225 : Blo 1354996 1525225 := bbase (se 2 (by rfl) ⟨571959, by rfl⟩ : syracuseStep 1525225 = 1143919) (by norm_num)
theorem B2033141 : Blo 1354996 2033141 := bbase (se 5 (by rfl) ⟨95303, by rfl⟩ : syracuseStep 2033141 = 190607) (by norm_num)
theorem B3048965 : Blo 1354996 3048965 := bbase (se 4 (by rfl) ⟨285840, by rfl⟩ : syracuseStep 3048965 = 571681) (by norm_num)
theorem B2287109 : Blo 1354996 2287109 := bbase (se 4 (by rfl) ⟨214416, by rfl⟩ : syracuseStep 2287109 = 428833) (by norm_num)
theorem B2033165 : Blo 1354996 2033165 := bbase (se 3 (by rfl) ⟨381218, by rfl⟩ : syracuseStep 2033165 = 762437) (by norm_num)
theorem B1525261 : Blo 1354996 1525261 := bbase (se 3 (by rfl) ⟨285986, by rfl⟩ : syracuseStep 1525261 = 571973) (by norm_num)
theorem B2033189 : Blo 1354996 2033189 := bbase (se 4 (by rfl) ⟨190611, by rfl⟩ : syracuseStep 2033189 = 381223) (by norm_num)
theorem B1525297 : Blo 1354996 1525297 := bbase (se 2 (by rfl) ⟨571986, by rfl⟩ : syracuseStep 1525297 = 1143973) (by norm_num)
theorem B2033213 : Blo 1354996 2033213 := bbase (se 3 (by rfl) ⟨381227, by rfl⟩ : syracuseStep 2033213 = 762455) (by norm_num)
theorem B3049037 : Blo 1354996 3049037 := bbase (se 3 (by rfl) ⟨571694, by rfl⟩ : syracuseStep 3049037 = 1143389) (by norm_num)
theorem B2475605 : Blo 1354996 2475605 := bbase (se 8 (by rfl) ⟨14505, by rfl⟩ : syracuseStep 2475605 = 29011) (by norm_num)
theorem B2033237 : Blo 1354996 2033237 := bbase (se 8 (by rfl) ⟨11913, by rfl⟩ : syracuseStep 2033237 = 23827) (by norm_num)
theorem B1525333 : Blo 1354996 1525333 := bbase (se 8 (by rfl) ⟨8937, by rfl⟩ : syracuseStep 1525333 = 17875) (by norm_num)
theorem B2033261 : Blo 1354996 2033261 := bbase (se 3 (by rfl) ⟨381236, by rfl⟩ : syracuseStep 2033261 = 762473) (by norm_num)
theorem B1525369 : Blo 1354996 1525369 := bbase (se 2 (by rfl) ⟨572013, by rfl⟩ : syracuseStep 1525369 = 1144027) (by norm_num)
theorem B2287237 : Blo 1354996 2287237 := bbase (se 4 (by rfl) ⟨214428, by rfl⟩ : syracuseStep 2287237 = 428857) (by norm_num)
theorem B2033285 : Blo 1354996 2033285 := bbase (se 4 (by rfl) ⟨190620, by rfl⟩ : syracuseStep 2033285 = 381241) (by norm_num)
theorem B2172557 : Blo 1354996 2172557 := bbase (se 3 (by rfl) ⟨407354, by rfl⟩ : syracuseStep 2172557 = 814709) (by norm_num)
theorem B3049109 : Blo 1354996 3049109 := bbase (se 6 (by rfl) ⟨71463, by rfl⟩ : syracuseStep 3049109 = 142927) (by norm_num)
theorem B2033309 : Blo 1354996 2033309 := bbase (se 3 (by rfl) ⟨381245, by rfl⟩ : syracuseStep 2033309 = 762491) (by norm_num)
theorem B1525405 : Blo 1354996 1525405 := bbase (se 3 (by rfl) ⟨286013, by rfl⟩ : syracuseStep 1525405 = 572027) (by norm_num)
theorem B2033333 : Blo 1354996 2033333 := bbase (se 5 (by rfl) ⟨95312, by rfl⟩ : syracuseStep 2033333 = 190625) (by norm_num)
theorem B1525441 : Blo 1354996 1525441 := bbase (se 2 (by rfl) ⟨572040, by rfl⟩ : syracuseStep 1525441 = 1144081) (by norm_num)
theorem B2033357 : Blo 1354996 2033357 := bbase (se 3 (by rfl) ⟨381254, by rfl⟩ : syracuseStep 2033357 = 762509) (by norm_num)
theorem B3434197 : Blo 1354996 3434197 := bbase (se 7 (by rfl) ⟨40244, by rfl⟩ : syracuseStep 3434197 = 80489) (by norm_num)
theorem B3049181 : Blo 1354996 3049181 := bbase (se 3 (by rfl) ⟨571721, by rfl⟩ : syracuseStep 3049181 = 1143443) (by norm_num)
theorem B2287325 : Blo 1354996 2287325 := bbase (se 3 (by rfl) ⟨428873, by rfl⟩ : syracuseStep 2287325 = 857747) (by norm_num)
theorem B2033381 : Blo 1354996 2033381 := bbase (se 4 (by rfl) ⟨190629, by rfl⟩ : syracuseStep 2033381 = 381259) (by norm_num)
theorem B1525477 : Blo 1354996 1525477 := bbase (se 4 (by rfl) ⟨143013, by rfl⟩ : syracuseStep 1525477 = 286027) (by norm_num)
theorem B9660149 : Blo 1354996 9660149 := bbase (se 5 (by rfl) ⟨452819, by rfl⟩ : syracuseStep 9660149 = 905639) (by norm_num)
theorem B2033405 : Blo 1354996 2033405 := bbase (se 3 (by rfl) ⟨381263, by rfl⟩ : syracuseStep 2033405 = 762527) (by norm_num)
theorem B4884229 : Blo 1354996 4884229 := bbase (se 4 (by rfl) ⟨457896, by rfl⟩ : syracuseStep 4884229 = 915793) (by norm_num)
theorem B6866693 : Blo 1354996 6866693 := bbase (se 4 (by rfl) ⟨643752, by rfl⟩ : syracuseStep 6866693 = 1287505) (by norm_num)
theorem B1525513 : Blo 1354996 1525513 := bbase (se 2 (by rfl) ⟨572067, by rfl⟩ : syracuseStep 1525513 = 1144135) (by norm_num)
theorem B2033429 : Blo 1354996 2033429 := bbase (se 6 (by rfl) ⟨47658, by rfl⟩ : syracuseStep 2033429 = 95317) (by norm_num)
theorem B3049253 : Blo 1354996 3049253 := bbase (se 4 (by rfl) ⟨285867, by rfl⟩ : syracuseStep 3049253 = 571735) (by norm_num)
theorem B3860261 : Blo 1354996 3860261 := bbase (se 4 (by rfl) ⟨361899, by rfl⟩ : syracuseStep 3860261 = 723799) (by norm_num)
theorem B2033453 : Blo 1354996 2033453 := bbase (se 3 (by rfl) ⟨381272, by rfl⟩ : syracuseStep 2033453 = 762545) (by norm_num)
theorem B1525549 : Blo 1354996 1525549 := bbase (se 3 (by rfl) ⟨286040, by rfl⟩ : syracuseStep 1525549 = 572081) (by norm_num)
theorem B2033477 : Blo 1354996 2033477 := bbase (se 4 (by rfl) ⟨190638, by rfl⟩ : syracuseStep 2033477 = 381277) (by norm_num)
theorem B3434309 : Blo 1354996 3434309 := bbase (se 4 (by rfl) ⟨321966, by rfl⟩ : syracuseStep 3434309 = 643933) (by norm_num)
theorem B1525585 : Blo 1354996 1525585 := bbase (se 2 (by rfl) ⟨572094, by rfl⟩ : syracuseStep 1525585 = 1144189) (by norm_num)
theorem B2287453 : Blo 1354996 2287453 := bbase (se 3 (by rfl) ⟨428897, by rfl⟩ : syracuseStep 2287453 = 857795) (by norm_num)
theorem B2033501 : Blo 1354996 2033501 := bbase (se 3 (by rfl) ⟨381281, by rfl⟩ : syracuseStep 2033501 = 762563) (by norm_num)
theorem B3049325 : Blo 1354996 3049325 := bbase (se 3 (by rfl) ⟨571748, by rfl⟩ : syracuseStep 3049325 = 1143497) (by norm_num)
theorem B2172781 : Blo 1354996 2172781 := bbase (se 3 (by rfl) ⟨407396, by rfl⟩ : syracuseStep 2172781 = 814793) (by norm_num)
theorem B2033525 : Blo 1354996 2033525 := bbase (se 5 (by rfl) ⟨95321, by rfl⟩ : syracuseStep 2033525 = 190643) (by norm_num)
theorem B1525621 : Blo 1354996 1525621 := bbase (se 5 (by rfl) ⟨71513, by rfl⟩ : syracuseStep 1525621 = 143027) (by norm_num)
theorem B2033549 : Blo 1354996 2033549 := bbase (se 3 (by rfl) ⟨381290, by rfl⟩ : syracuseStep 2033549 = 762581) (by norm_num)
theorem B11585429 : Blo 1354996 11585429 := bbase (se 6 (by rfl) ⟨271533, by rfl⟩ : syracuseStep 11585429 = 543067) (by norm_num)
theorem B1525657 : Blo 1354996 1525657 := bbase (se 2 (by rfl) ⟨572121, by rfl⟩ : syracuseStep 1525657 = 1144243) (by norm_num)
theorem B2033573 : Blo 1354996 2033573 := bbase (se 4 (by rfl) ⟨190647, by rfl⟩ : syracuseStep 2033573 = 381295) (by norm_num)
theorem B2172845 : Blo 1354996 2172845 := bbase (se 3 (by rfl) ⟨407408, by rfl⟩ : syracuseStep 2172845 = 814817) (by norm_num)
theorem B3049397 : Blo 1354996 3049397 := bbase (se 5 (by rfl) ⟨142940, by rfl⟩ : syracuseStep 3049397 = 285881) (by norm_num)
theorem B2287541 : Blo 1354996 2287541 := bbase (se 5 (by rfl) ⟨107228, by rfl⟩ : syracuseStep 2287541 = 214457) (by norm_num)
theorem B6514613 : Blo 1354996 6514613 := bbase (se 5 (by rfl) ⟨305372, by rfl⟩ : syracuseStep 6514613 = 610745) (by norm_num)
theorem B3090365 : Blo 1354996 3090365 := bbase (se 3 (by rfl) ⟨579443, by rfl⟩ : syracuseStep 3090365 = 1158887) (by norm_num)
theorem B2033597 : Blo 1354996 2033597 := bbase (se 3 (by rfl) ⟨381299, by rfl⟩ : syracuseStep 2033597 = 762599) (by norm_num)
theorem B1525693 : Blo 1354996 1525693 := bbase (se 3 (by rfl) ⟨286067, by rfl⟩ : syracuseStep 1525693 = 572135) (by norm_num)
theorem B2033621 : Blo 1354996 2033621 := bbase (se 7 (by rfl) ⟨23831, by rfl⟩ : syracuseStep 2033621 = 47663) (by norm_num)
theorem B7325653 : Blo 1354996 7325653 := bbase (se 7 (by rfl) ⟨85847, by rfl⟩ : syracuseStep 7325653 = 171695) (by norm_num)
theorem B1525729 : Blo 1354996 1525729 := bbase (se 2 (by rfl) ⟨572148, by rfl⟩ : syracuseStep 1525729 = 1144297) (by norm_num)
theorem B2033645 : Blo 1354996 2033645 := bbase (se 3 (by rfl) ⟨381308, by rfl⟩ : syracuseStep 2033645 = 762617) (by norm_num)
theorem B3049469 : Blo 1354996 3049469 := bbase (se 3 (by rfl) ⟨571775, by rfl⟩ : syracuseStep 3049469 = 1143551) (by norm_num)
theorem B2033669 : Blo 1354996 2033669 := bbase (se 4 (by rfl) ⟨190656, by rfl⟩ : syracuseStep 2033669 = 381313) (by norm_num)
theorem B1525765 : Blo 1354996 1525765 := bbase (se 4 (by rfl) ⟨143040, by rfl⟩ : syracuseStep 1525765 = 286081) (by norm_num)
theorem B3434501 : Blo 1354996 3434501 := bbase (se 4 (by rfl) ⟨321984, by rfl⟩ : syracuseStep 3434501 = 643969) (by norm_num)
theorem B4573205 : Blo 1354996 4573205 := bbase (se 6 (by rfl) ⟨107184, by rfl⟩ : syracuseStep 4573205 = 214369) (by norm_num)
theorem B2033693 : Blo 1354996 2033693 := bbase (se 3 (by rfl) ⟨381317, by rfl⟩ : syracuseStep 2033693 = 762635) (by norm_num)
theorem B1525801 : Blo 1354996 1525801 := bbase (se 2 (by rfl) ⟨572175, by rfl⟩ : syracuseStep 1525801 = 1144351) (by norm_num)
theorem B2172973 : Blo 1354996 2172973 := bbase (se 3 (by rfl) ⟨407432, by rfl⟩ : syracuseStep 2172973 = 814865) (by norm_num)
theorem B2287669 : Blo 1354996 2287669 := bbase (se 5 (by rfl) ⟨107234, by rfl⟩ : syracuseStep 2287669 = 214469) (by norm_num)
theorem B2033717 : Blo 1354996 2033717 := bbase (se 5 (by rfl) ⟨95330, by rfl⟩ : syracuseStep 2033717 = 190661) (by norm_num)
theorem B3049541 : Blo 1354996 3049541 := bbase (se 4 (by rfl) ⟨285894, by rfl⟩ : syracuseStep 3049541 = 571789) (by norm_num)
theorem B2033741 : Blo 1354996 2033741 := bbase (se 3 (by rfl) ⟨381326, by rfl⟩ : syracuseStep 2033741 = 762653) (by norm_num)
theorem B1525837 : Blo 1354996 1525837 := bbase (se 3 (by rfl) ⟨286094, by rfl⟩ : syracuseStep 1525837 = 572189) (by norm_num)
theorem B2033765 : Blo 1354996 2033765 := bbase (se 4 (by rfl) ⟨190665, by rfl⟩ : syracuseStep 2033765 = 381331) (by norm_num)
theorem B1525873 : Blo 1354996 1525873 := bbase (se 2 (by rfl) ⟨572202, by rfl⟩ : syracuseStep 1525873 = 1144405) (by norm_num)
theorem B2033789 : Blo 1354996 2033789 := bbase (se 3 (by rfl) ⟨381335, by rfl⟩ : syracuseStep 2033789 = 762671) (by norm_num)
theorem B3049613 : Blo 1354996 3049613 := bbase (se 3 (by rfl) ⟨571802, by rfl⟩ : syracuseStep 3049613 = 1143605) (by norm_num)
theorem B2287757 : Blo 1354996 2287757 := bbase (se 3 (by rfl) ⟨428954, by rfl⟩ : syracuseStep 2287757 = 857909) (by norm_num)
theorem B2320525 : Blo 1354996 2320525 := bbase (se 3 (by rfl) ⟨435098, by rfl⟩ : syracuseStep 2320525 = 870197) (by norm_num)
theorem B2033813 : Blo 1354996 2033813 := bbase (se 6 (by rfl) ⟨47667, by rfl⟩ : syracuseStep 2033813 = 95335) (by norm_num)
theorem B1525909 : Blo 1354996 1525909 := bbase (se 6 (by rfl) ⟨35763, by rfl⟩ : syracuseStep 1525909 = 71527) (by norm_num)
theorem B7055509 : Blo 1354996 7055509 := bbase (se 6 (by rfl) ⟨165363, by rfl⟩ : syracuseStep 7055509 = 330727) (by norm_num)
theorem B2033837 : Blo 1354996 2033837 := bbase (se 3 (by rfl) ⟨381344, by rfl⟩ : syracuseStep 2033837 = 762689) (by norm_num)
theorem B2574517 : Blo 1354996 2574517 := bbase (se 5 (by rfl) ⟨120680, by rfl⟩ : syracuseStep 2574517 = 241361) (by norm_num)
theorem B1525945 : Blo 1354996 1525945 := bbase (se 2 (by rfl) ⟨572229, by rfl⟩ : syracuseStep 1525945 = 1144459) (by norm_num)
theorem B2033861 : Blo 1354996 2033861 := bbase (se 4 (by rfl) ⟨190674, by rfl⟩ : syracuseStep 2033861 = 381349) (by norm_num)
theorem B3049685 : Blo 1354996 3049685 := bbase (se 7 (by rfl) ⟨35738, by rfl⟩ : syracuseStep 3049685 = 71477) (by norm_num)
theorem B3860693 : Blo 1354996 3860693 := bbase (se 7 (by rfl) ⟨45242, by rfl⟩ : syracuseStep 3860693 = 90485) (by norm_num)
theorem B2033885 : Blo 1354996 2033885 := bbase (se 3 (by rfl) ⟨381353, by rfl⟩ : syracuseStep 2033885 = 762707) (by norm_num)
theorem B1525981 : Blo 1354996 1525981 := bbase (se 3 (by rfl) ⟨286121, by rfl⟩ : syracuseStep 1525981 = 572243) (by norm_num)
theorem B2033909 : Blo 1354996 2033909 := bbase (se 5 (by rfl) ⟨95339, by rfl⟩ : syracuseStep 2033909 = 190679) (by norm_num)
theorem B1526017 : Blo 1354996 1526017 := bbase (se 2 (by rfl) ⟨572256, by rfl⟩ : syracuseStep 1526017 = 1144513) (by norm_num)
theorem B2287885 : Blo 1354996 2287885 := bbase (se 3 (by rfl) ⟨428978, by rfl⟩ : syracuseStep 2287885 = 857957) (by norm_num)
theorem B2033933 : Blo 1354996 2033933 := bbase (se 3 (by rfl) ⟨381362, by rfl⟩ : syracuseStep 2033933 = 762725) (by norm_num)
theorem B3049757 : Blo 1354996 3049757 := bbase (se 3 (by rfl) ⟨571829, by rfl⟩ : syracuseStep 3049757 = 1143659) (by norm_num)
theorem B2033957 : Blo 1354996 2033957 := bbase (se 4 (by rfl) ⟨190683, by rfl⟩ : syracuseStep 2033957 = 381367) (by norm_num)
theorem B4344101 : Blo 1354996 4344101 := bbase (se 4 (by rfl) ⟨407259, by rfl⟩ : syracuseStep 4344101 = 814519) (by norm_num)
theorem B1526053 : Blo 1354996 1526053 := bbase (se 4 (by rfl) ⟨143067, by rfl⟩ : syracuseStep 1526053 = 286135) (by norm_num)
theorem B2033981 : Blo 1354996 2033981 := bbase (se 3 (by rfl) ⟨381371, by rfl⟩ : syracuseStep 2033981 = 762743) (by norm_num)
theorem B2574661 : Blo 1354996 2574661 := bbase (se 4 (by rfl) ⟨241374, by rfl⟩ : syracuseStep 2574661 = 482749) (by norm_num)
theorem B1526089 : Blo 1354996 1526089 := bbase (se 2 (by rfl) ⟨572283, by rfl⟩ : syracuseStep 1526089 = 1144567) (by norm_num)
theorem B2034005 : Blo 1354996 2034005 := bbase (se 10 (by rfl) ⟨2979, by rfl⟩ : syracuseStep 2034005 = 5959) (by norm_num)
theorem B3434845 : Blo 1354996 3434845 := bbase (se 3 (by rfl) ⟨644033, by rfl⟩ : syracuseStep 3434845 = 1288067) (by norm_num)
theorem B3049829 : Blo 1354996 3049829 := bbase (se 4 (by rfl) ⟨285921, by rfl⟩ : syracuseStep 3049829 = 571843) (by norm_num)
theorem B2287973 : Blo 1354996 2287973 := bbase (se 4 (by rfl) ⟨214497, by rfl⟩ : syracuseStep 2287973 = 428995) (by norm_num)
theorem B2034029 : Blo 1354996 2034029 := bbase (se 3 (by rfl) ⟨381380, by rfl⟩ : syracuseStep 2034029 = 762761) (by norm_num)
theorem B1526125 : Blo 1354996 1526125 := bbase (se 3 (by rfl) ⟨286148, by rfl⟩ : syracuseStep 1526125 = 572297) (by norm_num)
theorem B2034053 : Blo 1354996 2034053 := bbase (se 4 (by rfl) ⟨190692, by rfl⟩ : syracuseStep 2034053 = 381385) (by norm_num)
theorem B2894221 : Blo 1354996 2894221 := bbase (se 3 (by rfl) ⟨542666, by rfl⟩ : syracuseStep 2894221 = 1085333) (by norm_num)
theorem B1526161 : Blo 1354996 1526161 := bbase (se 2 (by rfl) ⟨572310, by rfl⟩ : syracuseStep 1526161 = 1144621) (by norm_num)
theorem B10299797 : Blo 1354996 10299797 := bbase (se 6 (by rfl) ⟨241401, by rfl⟩ : syracuseStep 10299797 = 482803) (by norm_num)
theorem B2034077 : Blo 1354996 2034077 := bbase (se 3 (by rfl) ⟨381389, by rfl⟩ : syracuseStep 2034077 = 762779) (by norm_num)
theorem B3049901 : Blo 1354996 3049901 := bbase (se 3 (by rfl) ⟨571856, by rfl⟩ : syracuseStep 3049901 = 1143713) (by norm_num)
theorem B2034101 : Blo 1354996 2034101 := bbase (se 5 (by rfl) ⟨95348, by rfl⟩ : syracuseStep 2034101 = 190697) (by norm_num)
theorem B1526197 : Blo 1354996 1526197 := bbase (se 5 (by rfl) ⟨71540, by rfl⟩ : syracuseStep 1526197 = 143081) (by norm_num)
theorem B4573637 : Blo 1354996 4573637 := bbase (se 4 (by rfl) ⟨428778, by rfl⟩ : syracuseStep 4573637 = 857557) (by norm_num)
theorem B2034125 : Blo 1354996 2034125 := bbase (se 3 (by rfl) ⟨381398, by rfl⟩ : syracuseStep 2034125 = 762797) (by norm_num)
theorem B2935253 : Blo 1354996 2935253 := bbase (se 7 (by rfl) ⟨34397, by rfl⟩ : syracuseStep 2935253 = 68795) (by norm_num)
theorem B1526233 : Blo 1354996 1526233 := bbase (se 2 (by rfl) ⟨572337, by rfl⟩ : syracuseStep 1526233 = 1144675) (by norm_num)
theorem B2288101 : Blo 1354996 2288101 := bbase (se 4 (by rfl) ⟨214509, by rfl⟩ : syracuseStep 2288101 = 429019) (by norm_num)
theorem B4344293 : Blo 1354996 4344293 := bbase (se 4 (by rfl) ⟨407277, by rfl⟩ : syracuseStep 4344293 = 814555) (by norm_num)
theorem B2034149 : Blo 1354996 2034149 := bbase (se 4 (by rfl) ⟨190701, by rfl⟩ : syracuseStep 2034149 = 381403) (by norm_num)
theorem B2574821 : Blo 1354996 2574821 := bbase (se 4 (by rfl) ⟨241389, by rfl⟩ : syracuseStep 2574821 = 482779) (by norm_num)
theorem B3049973 : Blo 1354996 3049973 := bbase (se 5 (by rfl) ⟨142967, by rfl⟩ : syracuseStep 3049973 = 285935) (by norm_num)
theorem B2034173 : Blo 1354996 2034173 := bbase (se 3 (by rfl) ⟨381407, by rfl⟩ : syracuseStep 2034173 = 762815) (by norm_num)
theorem B1526269 : Blo 1354996 1526269 := bbase (se 3 (by rfl) ⟨286175, by rfl⟩ : syracuseStep 1526269 = 572351) (by norm_num)
theorem B2034197 : Blo 1354996 2034197 := bbase (se 6 (by rfl) ⟨47676, by rfl⟩ : syracuseStep 2034197 = 95353) (by norm_num)
theorem B1526305 : Blo 1354996 1526305 := bbase (se 2 (by rfl) ⟨572364, by rfl⟩ : syracuseStep 1526305 = 1144729) (by norm_num)
theorem B2034221 : Blo 1354996 2034221 := bbase (se 3 (by rfl) ⟨381416, by rfl⟩ : syracuseStep 2034221 = 762833) (by norm_num)
theorem B3050045 : Blo 1354996 3050045 := bbase (se 3 (by rfl) ⟨571883, by rfl⟩ : syracuseStep 3050045 = 1143767) (by norm_num)
theorem B2288189 : Blo 1354996 2288189 := bbase (se 3 (by rfl) ⟨429035, by rfl⟩ : syracuseStep 2288189 = 858071) (by norm_num)
theorem B4639301 : Blo 1354996 4639301 := bbase (se 4 (by rfl) ⟨434934, by rfl⟩ : syracuseStep 4639301 = 869869) (by norm_num)
theorem B2034245 : Blo 1354996 2034245 := bbase (se 4 (by rfl) ⟨190710, by rfl⟩ : syracuseStep 2034245 = 381421) (by norm_num)
theorem B1526341 : Blo 1354996 1526341 := bbase (se 4 (by rfl) ⟨143094, by rfl⟩ : syracuseStep 1526341 = 286189) (by norm_num)
theorem B2034269 : Blo 1354996 2034269 := bbase (se 3 (by rfl) ⟨381425, by rfl⟩ : syracuseStep 2034269 = 762851) (by norm_num)
theorem B1526377 : Blo 1354996 1526377 := bbase (se 2 (by rfl) ⟨572391, by rfl⟩ : syracuseStep 1526377 = 1144783) (by norm_num)
theorem B2034293 : Blo 1354996 2034293 := bbase (se 5 (by rfl) ⟨95357, by rfl⟩ : syracuseStep 2034293 = 190715) (by norm_num)
theorem B2574965 : Blo 1354996 2574965 := bbase (se 5 (by rfl) ⟨120701, by rfl⟩ : syracuseStep 2574965 = 241403) (by norm_num)
theorem B3050117 : Blo 1354996 3050117 := bbase (se 4 (by rfl) ⟨285948, by rfl⟩ : syracuseStep 3050117 = 571897) (by norm_num)
theorem B2034317 : Blo 1354996 2034317 := bbase (se 3 (by rfl) ⟨381434, by rfl⟩ : syracuseStep 2034317 = 762869) (by norm_num)
theorem B1526413 : Blo 1354996 1526413 := bbase (se 3 (by rfl) ⟨286202, by rfl⟩ : syracuseStep 1526413 = 572405) (by norm_num)
theorem B2034341 : Blo 1354996 2034341 := bbase (se 4 (by rfl) ⟨190719, by rfl⟩ : syracuseStep 2034341 = 381439) (by norm_num)
theorem B1526449 : Blo 1354996 1526449 := bbase (se 2 (by rfl) ⟨572418, by rfl⟩ : syracuseStep 1526449 = 1144837) (by norm_num)
theorem B2288317 : Blo 1354996 2288317 := bbase (se 3 (by rfl) ⟨429059, by rfl⟩ : syracuseStep 2288317 = 858119) (by norm_num)
theorem B2034365 : Blo 1354996 2034365 := bbase (se 3 (by rfl) ⟨381443, by rfl⟩ : syracuseStep 2034365 = 762887) (by norm_num)
theorem B5147333 : Blo 1354996 5147333 := bbase (se 4 (by rfl) ⟨482562, by rfl⟩ : syracuseStep 5147333 = 965125) (by norm_num)
theorem B3050189 : Blo 1354996 3050189 := bbase (se 3 (by rfl) ⟨571910, by rfl⟩ : syracuseStep 3050189 = 1143821) (by norm_num)
theorem B2034389 : Blo 1354996 2034389 := bbase (se 7 (by rfl) ⟨23840, by rfl⟩ : syracuseStep 2034389 = 47681) (by norm_num)
theorem B1526485 : Blo 1354996 1526485 := bbase (se 7 (by rfl) ⟨17888, by rfl⟩ : syracuseStep 1526485 = 35777) (by norm_num)
theorem B3304165 : Blo 1354996 3304165 := bbase (se 4 (by rfl) ⟨309765, by rfl⟩ : syracuseStep 3304165 = 619531) (by norm_num)
theorem B2034413 : Blo 1354996 2034413 := bbase (se 3 (by rfl) ⟨381452, by rfl⟩ : syracuseStep 2034413 = 762905) (by norm_num)
theorem B1526521 : Blo 1354996 1526521 := bbase (se 2 (by rfl) ⟨572445, by rfl⟩ : syracuseStep 1526521 = 1144891) (by norm_num)
theorem B2034437 : Blo 1354996 2034437 := bbase (se 4 (by rfl) ⟨190728, by rfl⟩ : syracuseStep 2034437 = 381457) (by norm_num)
theorem B3050261 : Blo 1354996 3050261 := bbase (se 6 (by rfl) ⟨71490, by rfl⟩ : syracuseStep 3050261 = 142981) (by norm_num)
theorem B2288405 : Blo 1354996 2288405 := bbase (se 6 (by rfl) ⟨53634, by rfl⟩ : syracuseStep 2288405 = 107269) (by norm_num)
theorem B2034461 : Blo 1354996 2034461 := bbase (se 3 (by rfl) ⟨381461, by rfl⟩ : syracuseStep 2034461 = 762923) (by norm_num)
theorem B1526557 : Blo 1354996 1526557 := bbase (se 3 (by rfl) ⟨286229, by rfl⟩ : syracuseStep 1526557 = 572459) (by norm_num)
theorem B10292021 : Blo 1354996 10292021 := bbase (se 5 (by rfl) ⟨482438, by rfl⟩ : syracuseStep 10292021 = 964877) (by norm_num)
theorem B2034485 : Blo 1354996 2034485 := bbase (se 5 (by rfl) ⟨95366, by rfl⟩ : syracuseStep 2034485 = 190733) (by norm_num)
theorem B1526593 : Blo 1354996 1526593 := bbase (se 2 (by rfl) ⟨572472, by rfl⟩ : syracuseStep 1526593 = 1144945) (by norm_num)
theorem B2034509 : Blo 1354996 2034509 := bbase (se 3 (by rfl) ⟨381470, by rfl⟩ : syracuseStep 2034509 = 762941) (by norm_num)
theorem B1715033 : Blo 1354996 1715033 := bbase (se 2 (by rfl) ⟨643137, by rfl⟩ : syracuseStep 1715033 = 1286275) (by norm_num)
theorem B3050333 : Blo 1354996 3050333 := bbase (se 3 (by rfl) ⟨571937, by rfl⟩ : syracuseStep 3050333 = 1143875) (by norm_num)
theorem B2034533 : Blo 1354996 2034533 := bbase (se 4 (by rfl) ⟨190737, by rfl⟩ : syracuseStep 2034533 = 381475) (by norm_num)
theorem B4574069 : Blo 1354996 4574069 := bbase (se 5 (by rfl) ⟨214409, by rfl⟩ : syracuseStep 4574069 = 428819) (by norm_num)
theorem B2894717 : Blo 1354996 2894717 := bbase (se 3 (by rfl) ⟨542759, by rfl⟩ : syracuseStep 2894717 = 1085519) (by norm_num)
theorem B2034557 : Blo 1354996 2034557 := bbase (se 3 (by rfl) ⟨381479, by rfl⟩ : syracuseStep 2034557 = 762959) (by norm_num)
theorem B1715089 : Blo 1354996 1715089 := bbase (se 2 (by rfl) ⟨643158, by rfl⟩ : syracuseStep 1715089 = 1286317) (by norm_num)
theorem B2288533 : Blo 1354996 2288533 := bbase (se 6 (by rfl) ⟨53637, by rfl⟩ : syracuseStep 2288533 = 107275) (by norm_num)
theorem B2034581 : Blo 1354996 2034581 := bbase (se 6 (by rfl) ⟨47685, by rfl⟩ : syracuseStep 2034581 = 95371) (by norm_num)
theorem B2575253 : Blo 1354996 2575253 := bbase (se 6 (by rfl) ⟨60357, by rfl⟩ : syracuseStep 2575253 = 120715) (by norm_num)
theorem B3050405 : Blo 1354996 3050405 := bbase (se 4 (by rfl) ⟨285975, by rfl⟩ : syracuseStep 3050405 = 571951) (by norm_num)
theorem B2034605 : Blo 1354996 2034605 := bbase (se 3 (by rfl) ⟨381488, by rfl⟩ : syracuseStep 2034605 = 762977) (by norm_num)
theorem B3861445 : Blo 1354996 3861445 := bbase (se 4 (by rfl) ⟨362010, by rfl⟩ : syracuseStep 3861445 = 724021) (by norm_num)
theorem B2034629 : Blo 1354996 2034629 := bbase (se 4 (by rfl) ⟨190746, by rfl⟩ : syracuseStep 2034629 = 381493) (by norm_num)
theorem B2034653 : Blo 1354996 2034653 := bbase (se 3 (by rfl) ⟨381497, by rfl⟩ : syracuseStep 2034653 = 762995) (by norm_num)
theorem B5147621 : Blo 1354996 5147621 := bbase (se 4 (by rfl) ⟨482589, by rfl⟩ : syracuseStep 5147621 = 965179) (by norm_num)
theorem B3050477 : Blo 1354996 3050477 := bbase (se 3 (by rfl) ⟨571964, by rfl⟩ : syracuseStep 3050477 = 1143929) (by norm_num)
theorem B2288621 : Blo 1354996 2288621 := bbase (se 3 (by rfl) ⟨429116, by rfl⟩ : syracuseStep 2288621 = 858233) (by norm_num)
theorem B1715185 : Blo 1354996 1715185 := bbase (se 2 (by rfl) ⟨643194, by rfl⟩ : syracuseStep 1715185 = 1286389) (by norm_num)
theorem B2034677 : Blo 1354996 2034677 := bbase (se 5 (by rfl) ⟨95375, by rfl⟩ : syracuseStep 2034677 = 190751) (by norm_num)
theorem B2034701 : Blo 1354996 2034701 := bbase (se 3 (by rfl) ⟨381506, by rfl⟩ : syracuseStep 2034701 = 763013) (by norm_num)
theorem B6867989 : Blo 1354996 6867989 := bbase (se 6 (by rfl) ⟨160968, by rfl⟩ : syracuseStep 6867989 = 321937) (by norm_num)
theorem B2034725 : Blo 1354996 2034725 := bbase (se 4 (by rfl) ⟨190755, by rfl⟩ : syracuseStep 2034725 = 381511) (by norm_num)
theorem B2575405 : Blo 1354996 2575405 := bbase (se 3 (by rfl) ⟨482888, by rfl⟩ : syracuseStep 2575405 = 965777) (by norm_num)
theorem B3050549 : Blo 1354996 3050549 := bbase (se 5 (by rfl) ⟨142994, by rfl⟩ : syracuseStep 3050549 = 285989) (by norm_num)
theorem B2034749 : Blo 1354996 2034749 := bbase (se 3 (by rfl) ⟨381515, by rfl⟩ : syracuseStep 2034749 = 763031) (by norm_num)
theorem B2747477 : Blo 1354996 2747477 := bbase (se 8 (by rfl) ⟨16098, by rfl⟩ : syracuseStep 2747477 = 32197) (by norm_num)
theorem B2034773 : Blo 1354996 2034773 := bbase (se 8 (by rfl) ⟨11922, by rfl⟩ : syracuseStep 2034773 = 23845) (by norm_num)
theorem B2288749 : Blo 1354996 2288749 := bbase (se 3 (by rfl) ⟨429140, by rfl⟩ : syracuseStep 2288749 = 858281) (by norm_num)
theorem B2034797 : Blo 1354996 2034797 := bbase (se 3 (by rfl) ⟨381524, by rfl⟩ : syracuseStep 2034797 = 763049) (by norm_num)
theorem B3050621 : Blo 1354996 3050621 := bbase (se 3 (by rfl) ⟨571991, by rfl⟩ : syracuseStep 3050621 = 1143983) (by norm_num)
theorem B2034821 : Blo 1354996 2034821 := bbase (se 4 (by rfl) ⟨190764, by rfl⟩ : syracuseStep 2034821 = 381529) (by norm_num)
theorem B1715357 : Blo 1354996 1715357 := bbase (se 3 (by rfl) ⟨321629, by rfl⟩ : syracuseStep 1715357 = 643259) (by norm_num)
theorem B2034845 : Blo 1354996 2034845 := bbase (se 3 (by rfl) ⟨381533, by rfl⟩ : syracuseStep 2034845 = 763067) (by norm_num)
theorem B2034869 : Blo 1354996 2034869 := bbase (se 5 (by rfl) ⟨95384, by rfl⟩ : syracuseStep 2034869 = 190769) (by norm_num)
theorem B2935997 : Blo 1354996 2935997 := bbase (se 3 (by rfl) ⟨550499, by rfl⟩ : syracuseStep 2935997 = 1100999) (by norm_num)
theorem B3050693 : Blo 1354996 3050693 := bbase (se 4 (by rfl) ⟨286002, by rfl⟩ : syracuseStep 3050693 = 572005) (by norm_num)
theorem B2288837 : Blo 1354996 2288837 := bbase (se 4 (by rfl) ⟨214578, by rfl⟩ : syracuseStep 2288837 = 429157) (by norm_num)
theorem B2034893 : Blo 1354996 2034893 := bbase (se 3 (by rfl) ⟨381542, by rfl⟩ : syracuseStep 2034893 = 763085) (by norm_num)
theorem B1715413 : Blo 1354996 1715413 := bbase (se 7 (by rfl) ⟨20102, by rfl⟩ : syracuseStep 1715413 = 40205) (by norm_num)
theorem B4885717 : Blo 1354996 4885717 := bbase (se 7 (by rfl) ⟨57254, by rfl⟩ : syracuseStep 4885717 = 114509) (by norm_num)
theorem B2034917 : Blo 1354996 2034917 := bbase (se 4 (by rfl) ⟨190773, by rfl⟩ : syracuseStep 2034917 = 381547) (by norm_num)
theorem B2034941 : Blo 1354996 2034941 := bbase (se 3 (by rfl) ⟨381551, by rfl⟩ : syracuseStep 2034941 = 763103) (by norm_num)
theorem B3050765 : Blo 1354996 3050765 := bbase (se 3 (by rfl) ⟨572018, by rfl⟩ : syracuseStep 3050765 = 1144037) (by norm_num)
theorem B2034965 : Blo 1354996 2034965 := bbase (se 6 (by rfl) ⟨47694, by rfl⟩ : syracuseStep 2034965 = 95389) (by norm_num)
theorem B4574501 : Blo 1354996 4574501 := bbase (se 4 (by rfl) ⟨428859, by rfl⟩ : syracuseStep 4574501 = 857719) (by norm_num)
theorem B2034989 : Blo 1354996 2034989 := bbase (se 3 (by rfl) ⟨381560, by rfl⟩ : syracuseStep 2034989 = 763121) (by norm_num)
theorem B1715509 : Blo 1354996 1715509 := bbase (se 5 (by rfl) ⟨80414, by rfl⟩ : syracuseStep 1715509 = 160829) (by norm_num)
theorem B2288965 : Blo 1354996 2288965 := bbase (se 4 (by rfl) ⟨214590, by rfl⟩ : syracuseStep 2288965 = 429181) (by norm_num)
theorem B2035013 : Blo 1354996 2035013 := bbase (se 4 (by rfl) ⟨190782, by rfl⟩ : syracuseStep 2035013 = 381565) (by norm_num)
theorem B3050837 : Blo 1354996 3050837 := bbase (se 11 (by rfl) ⟨2234, by rfl⟩ : syracuseStep 3050837 = 4469) (by norm_num)
theorem B2035037 : Blo 1354996 2035037 := bbase (se 3 (by rfl) ⟨381569, by rfl⟩ : syracuseStep 2035037 = 763139) (by norm_num)
theorem B2575709 : Blo 1354996 2575709 := bbase (se 3 (by rfl) ⟨482945, by rfl⟩ : syracuseStep 2575709 = 965891) (by norm_num)
theorem B2035061 : Blo 1354996 2035061 := bbase (se 5 (by rfl) ⟨95393, by rfl⟩ : syracuseStep 2035061 = 190787) (by norm_num)
theorem B2035085 : Blo 1354996 2035085 := bbase (se 3 (by rfl) ⟨381578, by rfl⟩ : syracuseStep 2035085 = 763157) (by norm_num)
theorem B3050909 : Blo 1354996 3050909 := bbase (se 3 (by rfl) ⟨572045, by rfl⟩ : syracuseStep 3050909 = 1144091) (by norm_num)
theorem B2289053 : Blo 1354996 2289053 := bbase (se 3 (by rfl) ⟨429197, by rfl⟩ : syracuseStep 2289053 = 858395) (by norm_num)
theorem B2035109 : Blo 1354996 2035109 := bbase (se 4 (by rfl) ⟨190791, by rfl⟩ : syracuseStep 2035109 = 381583) (by norm_num)
theorem B6860213 : Blo 1354996 6860213 := bbase (se 5 (by rfl) ⟨321572, by rfl⟩ : syracuseStep 6860213 = 643145) (by norm_num)
theorem B2035133 : Blo 1354996 2035133 := bbase (se 3 (by rfl) ⟨381587, by rfl⟩ : syracuseStep 2035133 = 763175) (by norm_num)
theorem B2035157 : Blo 1354996 2035157 := bbase (se 7 (by rfl) ⟨23849, by rfl⟩ : syracuseStep 2035157 = 47699) (by norm_num)
theorem B1715681 : Blo 1354996 1715681 := bbase (se 2 (by rfl) ⟨643380, by rfl⟩ : syracuseStep 1715681 = 1286761) (by norm_num)
theorem B3050981 : Blo 1354996 3050981 := bbase (se 4 (by rfl) ⟨286029, by rfl⟩ : syracuseStep 3050981 = 572059) (by norm_num)
theorem B2035181 : Blo 1354996 2035181 := bbase (se 3 (by rfl) ⟨381596, by rfl⟩ : syracuseStep 2035181 = 763193) (by norm_num)
theorem B2035205 : Blo 1354996 2035205 := bbase (se 4 (by rfl) ⟨190800, by rfl⟩ : syracuseStep 2035205 = 381601) (by norm_num)
theorem B1715737 : Blo 1354996 1715737 := bbase (se 2 (by rfl) ⟨643401, by rfl⟩ : syracuseStep 1715737 = 1286803) (by norm_num)
theorem B2289181 : Blo 1354996 2289181 := bbase (se 3 (by rfl) ⟨429221, by rfl⟩ : syracuseStep 2289181 = 858443) (by norm_num)
theorem B2035229 : Blo 1354996 2035229 := bbase (se 3 (by rfl) ⟨381605, by rfl⟩ : syracuseStep 2035229 = 763211) (by norm_num)
theorem B3051053 : Blo 1354996 3051053 := bbase (se 3 (by rfl) ⟨572072, by rfl⟩ : syracuseStep 3051053 = 1144145) (by norm_num)
theorem B2035253 : Blo 1354996 2035253 := bbase (se 5 (by rfl) ⟨95402, by rfl⟩ : syracuseStep 2035253 = 190805) (by norm_num)
theorem B2747981 : Blo 1354996 2747981 := bbase (se 3 (by rfl) ⟨515246, by rfl⟩ : syracuseStep 2747981 = 1030493) (by norm_num)
theorem B2035277 : Blo 1354996 2035277 := bbase (se 3 (by rfl) ⟨381614, by rfl⟩ : syracuseStep 2035277 = 763229) (by norm_num)
theorem B2936405 : Blo 1354996 2936405 := bbase (se 8 (by rfl) ⟨17205, by rfl⟩ : syracuseStep 2936405 = 34411) (by norm_num)
theorem B2035301 : Blo 1354996 2035301 := bbase (se 4 (by rfl) ⟨190809, by rfl⟩ : syracuseStep 2035301 = 381619) (by norm_num)
theorem B3051125 : Blo 1354996 3051125 := bbase (se 5 (by rfl) ⟨143021, by rfl⟩ : syracuseStep 3051125 = 286043) (by norm_num)
theorem B1412725 : Blo 1354996 1412725 := bbase (se 5 (by rfl) ⟨66221, by rfl⟩ : syracuseStep 1412725 = 132443) (by norm_num)
theorem B2289269 : Blo 1354996 2289269 := bbase (se 5 (by rfl) ⟨107309, by rfl⟩ : syracuseStep 2289269 = 214619) (by norm_num)
theorem B1715833 : Blo 1354996 1715833 := bbase (se 2 (by rfl) ⟨643437, by rfl⟩ : syracuseStep 1715833 = 1286875) (by norm_num)
theorem B2035325 : Blo 1354996 2035325 := bbase (se 3 (by rfl) ⟨381623, by rfl⟩ : syracuseStep 2035325 = 763247) (by norm_num)
theorem B2444941 : Blo 1354996 2444941 := bbase (se 3 (by rfl) ⟨458426, by rfl⟩ : syracuseStep 2444941 = 916853) (by norm_num)
theorem B2035349 : Blo 1354996 2035349 := bbase (se 6 (by rfl) ⟨47703, by rfl⟩ : syracuseStep 2035349 = 95407) (by norm_num)
theorem B2608805 : Blo 1354996 2608805 := bbase (se 4 (by rfl) ⟨244575, by rfl⟩ : syracuseStep 2608805 = 489151) (by norm_num)
theorem B2035373 : Blo 1354996 2035373 := bbase (se 3 (by rfl) ⟨381632, by rfl⟩ : syracuseStep 2035373 = 763265) (by norm_num)
theorem B3051197 : Blo 1354996 3051197 := bbase (se 3 (by rfl) ⟨572099, by rfl⟩ : syracuseStep 3051197 = 1144199) (by norm_num)
theorem B2035397 : Blo 1354996 2035397 := bbase (se 4 (by rfl) ⟨190818, by rfl⟩ : syracuseStep 2035397 = 381637) (by norm_num)
theorem B1412813 : Blo 1354996 1412813 := bbase (se 3 (by rfl) ⟨264902, by rfl⟩ : syracuseStep 1412813 = 529805) (by norm_num)
theorem B4574933 : Blo 1354996 4574933 := bbase (se 7 (by rfl) ⟨53612, by rfl⟩ : syracuseStep 4574933 = 107225) (by norm_num)
theorem B2895581 : Blo 1354996 2895581 := bbase (se 3 (by rfl) ⟨542921, by rfl⟩ : syracuseStep 2895581 = 1085843) (by norm_num)
theorem B2035421 : Blo 1354996 2035421 := bbase (se 3 (by rfl) ⟨381641, by rfl⟩ : syracuseStep 2035421 = 763283) (by norm_num)
theorem B2289397 : Blo 1354996 2289397 := bbase (se 5 (by rfl) ⟨107315, by rfl⟩ : syracuseStep 2289397 = 214631) (by norm_num)
theorem B2035445 : Blo 1354996 2035445 := bbase (se 5 (by rfl) ⟨95411, by rfl⟩ : syracuseStep 2035445 = 190823) (by norm_num)
theorem B3051269 : Blo 1354996 3051269 := bbase (se 4 (by rfl) ⟨286056, by rfl⟩ : syracuseStep 3051269 = 572113) (by norm_num)
theorem B2035469 : Blo 1354996 2035469 := bbase (se 3 (by rfl) ⟨381650, by rfl⟩ : syracuseStep 2035469 = 763301) (by norm_num)
theorem B1716005 : Blo 1354996 1716005 := bbase (se 4 (by rfl) ⟨160875, by rfl⟩ : syracuseStep 1716005 = 321751) (by norm_num)
theorem B2035493 : Blo 1354996 2035493 := bbase (se 4 (by rfl) ⟨190827, by rfl⟩ : syracuseStep 2035493 = 381655) (by norm_num)
theorem B3051341 : Blo 1354996 3051341 := bbase (se 3 (by rfl) ⟨572126, by rfl⟩ : syracuseStep 3051341 = 1144253) (by norm_num)
theorem B2289485 : Blo 1354996 2289485 := bbase (se 3 (by rfl) ⟨429278, by rfl⟩ : syracuseStep 2289485 = 858557) (by norm_num)
theorem B1740629 : Blo 1354996 1740629 := bbase (se 9 (by rfl) ⟨5099, by rfl⟩ : syracuseStep 1740629 = 10199) (by norm_num)
theorem B1716061 : Blo 1354996 1716061 := bbase (se 3 (by rfl) ⟨321761, by rfl⟩ : syracuseStep 1716061 = 643523) (by norm_num)
theorem B2895725 : Blo 1354996 2895725 := bbase (se 3 (by rfl) ⟨542948, by rfl⟩ : syracuseStep 2895725 = 1085897) (by norm_num)
theorem B3051413 : Blo 1354996 3051413 := bbase (se 6 (by rfl) ⟨71517, by rfl⟩ : syracuseStep 3051413 = 143035) (by norm_num)
theorem B1716157 : Blo 1354996 1716157 := bbase (se 3 (by rfl) ⟨321779, by rfl⟩ : syracuseStep 1716157 = 643559) (by norm_num)
theorem B2289613 : Blo 1354996 2289613 := bbase (se 3 (by rfl) ⟨429302, by rfl⟩ : syracuseStep 2289613 = 858605) (by norm_num)
theorem B3051485 : Blo 1354996 3051485 := bbase (se 3 (by rfl) ⟨572153, by rfl⟩ : syracuseStep 3051485 = 1144307) (by norm_num)
theorem B2609189 : Blo 1354996 2609189 := bbase (se 4 (by rfl) ⟨244611, by rfl⟩ : syracuseStep 2609189 = 489223) (by norm_num)
theorem B3051557 : Blo 1354996 3051557 := bbase (se 4 (by rfl) ⟨286083, by rfl⟩ : syracuseStep 3051557 = 572167) (by norm_num)
theorem B2289701 : Blo 1354996 2289701 := bbase (se 4 (by rfl) ⟨214659, by rfl⟩ : syracuseStep 2289701 = 429319) (by norm_num)
theorem B1716329 : Blo 1354996 1716329 := bbase (se 2 (by rfl) ⟨643623, by rfl⟩ : syracuseStep 1716329 = 1287247) (by norm_num)
theorem B3051629 : Blo 1354996 3051629 := bbase (se 3 (by rfl) ⟨572180, by rfl⟩ : syracuseStep 3051629 = 1144361) (by norm_num)
theorem B4575365 : Blo 1354996 4575365 := bbase (se 4 (by rfl) ⟨428940, by rfl⟩ : syracuseStep 4575365 = 857881) (by norm_num)
theorem B5148805 : Blo 1354996 5148805 := bbase (se 4 (by rfl) ⟨482700, by rfl⟩ : syracuseStep 5148805 = 965401) (by norm_num)
theorem B2232461 : Blo 1354996 2232461 := bbase (se 3 (by rfl) ⟨418586, by rfl⟩ : syracuseStep 2232461 = 837173) (by norm_num)
theorem B1716385 : Blo 1354996 1716385 := bbase (se 2 (by rfl) ⟨643644, by rfl⟩ : syracuseStep 1716385 = 1287289) (by norm_num)
theorem B2289829 : Blo 1354996 2289829 := bbase (se 4 (by rfl) ⟨214671, by rfl⟩ : syracuseStep 2289829 = 429343) (by norm_num)
theorem B3051701 : Blo 1354996 3051701 := bbase (se 5 (by rfl) ⟨143048, by rfl⟩ : syracuseStep 3051701 = 286097) (by norm_num)
theorem B2748613 : Blo 1354996 2748613 := bbase (se 4 (by rfl) ⟨257682, by rfl⟩ : syracuseStep 2748613 = 515365) (by norm_num)
theorem B3051773 : Blo 1354996 3051773 := bbase (se 3 (by rfl) ⟨572207, by rfl⟩ : syracuseStep 3051773 = 1144415) (by norm_num)
theorem B2289917 : Blo 1354996 2289917 := bbase (se 3 (by rfl) ⟨429359, by rfl⟩ : syracuseStep 2289917 = 858719) (by norm_num)
theorem B1716481 : Blo 1354996 1716481 := bbase (se 2 (by rfl) ⟨643680, by rfl⟩ : syracuseStep 1716481 = 1287361) (by norm_num)
theorem B4403461 : Blo 1354996 4403461 := bbase (se 4 (by rfl) ⟨412824, by rfl⟩ : syracuseStep 4403461 = 825649) (by norm_num)
theorem B6869285 : Blo 1354996 6869285 := bbase (se 4 (by rfl) ⟨643995, by rfl⟩ : syracuseStep 6869285 = 1287991) (by norm_num)
theorem B3051845 : Blo 1354996 3051845 := bbase (se 4 (by rfl) ⟨286110, by rfl⟩ : syracuseStep 3051845 = 572221) (by norm_num)
theorem B3051917 : Blo 1354996 3051917 := bbase (se 3 (by rfl) ⟨572234, by rfl⟩ : syracuseStep 3051917 = 1144469) (by norm_num)
theorem B13914517 : Blo 1354996 13914517 := bbase (se 6 (by rfl) ⟨326121, by rfl⟩ : syracuseStep 13914517 = 652243) (by norm_num)
theorem B1929629 : Blo 1354996 1929629 := bbase (se 3 (by rfl) ⟨361805, by rfl⟩ : syracuseStep 1929629 = 723611) (by norm_num)
theorem B1716653 : Blo 1354996 1716653 := bbase (se 3 (by rfl) ⟨321872, by rfl⟩ : syracuseStep 1716653 = 643745) (by norm_num)
theorem B5149109 : Blo 1354996 5149109 := bbase (se 5 (by rfl) ⟨241364, by rfl⟩ : syracuseStep 5149109 = 482729) (by norm_num)
theorem B3477973 : Blo 1354996 3477973 := bbase (se 7 (by rfl) ⟨40757, by rfl⟩ : syracuseStep 3477973 = 81515) (by norm_num)
theorem B3051989 : Blo 1354996 3051989 := bbase (se 7 (by rfl) ⟨35765, by rfl⟩ : syracuseStep 3051989 = 71531) (by norm_num)
theorem B1716709 : Blo 1354996 1716709 := bbase (se 4 (by rfl) ⟨160941, by rfl⟩ : syracuseStep 1716709 = 321883) (by norm_num)
theorem B2200069 : Blo 1354996 2200069 := bbase (se 4 (by rfl) ⟨206256, by rfl⟩ : syracuseStep 2200069 = 412513) (by norm_num)
theorem B9777685 : Blo 1354996 9777685 := bbase (se 6 (by rfl) ⟨229164, by rfl⟩ : syracuseStep 9777685 = 458329) (by norm_num)
theorem B3052061 : Blo 1354996 3052061 := bbase (se 3 (by rfl) ⟨572261, by rfl⟩ : syracuseStep 3052061 = 1144523) (by norm_num)
theorem B4575797 : Blo 1354996 4575797 := bbase (se 5 (by rfl) ⟨214490, by rfl⟩ : syracuseStep 4575797 = 428981) (by norm_num)
theorem B1716805 : Blo 1354996 1716805 := bbase (se 4 (by rfl) ⟨160950, by rfl⟩ : syracuseStep 1716805 = 321901) (by norm_num)
theorem B2896469 : Blo 1354996 2896469 := bbase (se 8 (by rfl) ⟨16971, by rfl⟩ : syracuseStep 2896469 = 33943) (by norm_num)
theorem B3052133 : Blo 1354996 3052133 := bbase (se 4 (by rfl) ⟨286137, by rfl⟩ : syracuseStep 3052133 = 572275) (by norm_num)
theorem B6517381 : Blo 1354996 6517381 := bbase (se 4 (by rfl) ⟨611004, by rfl⟩ : syracuseStep 6517381 = 1222009) (by norm_num)
theorem B3052205 : Blo 1354996 3052205 := bbase (se 3 (by rfl) ⟨572288, by rfl⟩ : syracuseStep 3052205 = 1144577) (by norm_num)
theorem B5501621 : Blo 1354996 5501621 := bbase (se 5 (by rfl) ⟨257888, by rfl⟩ : syracuseStep 5501621 = 515777) (by norm_num)
theorem B6861509 : Blo 1354996 6861509 := bbase (se 4 (by rfl) ⟨643266, by rfl⟩ : syracuseStep 6861509 = 1286533) (by norm_num)
theorem B1716977 : Blo 1354996 1716977 := bbase (se 2 (by rfl) ⟨643866, by rfl⟩ : syracuseStep 1716977 = 1287733) (by norm_num)
theorem B3052277 : Blo 1354996 3052277 := bbase (se 5 (by rfl) ⟨143075, by rfl⟩ : syracuseStep 3052277 = 286151) (by norm_num)
theorem B1717033 : Blo 1354996 1717033 := bbase (se 2 (by rfl) ⟨643887, by rfl⟩ : syracuseStep 1717033 = 1287775) (by norm_num)
theorem B3052349 : Blo 1354996 3052349 := bbase (se 3 (by rfl) ⟨572315, by rfl⟩ : syracuseStep 3052349 = 1144631) (by norm_num)
theorem B5501765 : Blo 1354996 5501765 := bbase (se 4 (by rfl) ⟨515790, by rfl⟩ : syracuseStep 5501765 = 1031581) (by norm_num)
theorem B3052421 : Blo 1354996 3052421 := bbase (se 4 (by rfl) ⟨286164, by rfl⟩ : syracuseStep 3052421 = 572329) (by norm_num)
theorem B1717129 : Blo 1354996 1717129 := bbase (se 2 (by rfl) ⟨643923, by rfl⟩ : syracuseStep 1717129 = 1287847) (by norm_num)
theorem B3052493 : Blo 1354996 3052493 := bbase (se 3 (by rfl) ⟨572342, by rfl⟩ : syracuseStep 3052493 = 1144685) (by norm_num)
theorem B4576229 : Blo 1354996 4576229 := bbase (se 4 (by rfl) ⟨429021, by rfl⟩ : syracuseStep 4576229 = 858043) (by norm_num)
theorem B3052565 : Blo 1354996 3052565 := bbase (se 6 (by rfl) ⟨71544, by rfl⟩ : syracuseStep 3052565 = 143089) (by norm_num)
theorem B1717301 : Blo 1354996 1717301 := bbase (se 5 (by rfl) ⟨80498, by rfl⟩ : syracuseStep 1717301 = 160997) (by norm_num)
theorem B1545301 : Blo 1354996 1545301 := bbase (se 8 (by rfl) ⟨9054, by rfl⟩ : syracuseStep 1545301 = 18109) (by norm_num)
theorem B3052637 : Blo 1354996 3052637 := bbase (se 3 (by rfl) ⟨572369, by rfl⟩ : syracuseStep 3052637 = 1144739) (by norm_num)
theorem B1717357 : Blo 1354996 1717357 := bbase (se 3 (by rfl) ⟨322004, by rfl⟩ : syracuseStep 1717357 = 644009) (by norm_num)
theorem B3052709 : Blo 1354996 3052709 := bbase (se 4 (by rfl) ⟨286191, by rfl⟩ : syracuseStep 3052709 = 572383) (by norm_num)
theorem B5788853 : Blo 1354996 5788853 := bbase (se 5 (by rfl) ⟨271352, by rfl⟩ : syracuseStep 5788853 = 542705) (by norm_num)
theorem B1545421 : Blo 1354996 1545421 := bbase (se 3 (by rfl) ⟨289766, by rfl⟩ : syracuseStep 1545421 = 579533) (by norm_num)
theorem B1447141 : Blo 1354996 1447141 := bbase (se 4 (by rfl) ⟨135669, by rfl⟩ : syracuseStep 1447141 = 271339) (by norm_num)
theorem B3052781 : Blo 1354996 3052781 := bbase (se 3 (by rfl) ⟨572396, by rfl⟩ : syracuseStep 3052781 = 1144793) (by norm_num)
theorem B3257605 : Blo 1354996 3257605 := bbase (se 4 (by rfl) ⟨305400, by rfl⟩ : syracuseStep 3257605 = 610801) (by norm_num)
theorem B3257653 : Blo 1354996 3257653 := bbase (se 5 (by rfl) ⟨152702, by rfl⟩ : syracuseStep 3257653 = 305405) (by norm_num)
theorem B3052853 : Blo 1354996 3052853 := bbase (se 5 (by rfl) ⟨143102, by rfl⟩ : syracuseStep 3052853 = 286205) (by norm_num)
theorem B2897221 : Blo 1354996 2897221 := bbase (se 4 (by rfl) ⟨271614, by rfl⟩ : syracuseStep 2897221 = 543229) (by norm_num)
theorem B32986453 : Blo 1354996 32986453 := bbase (se 17 (by rfl) ⟨377, by rfl⟩ : syracuseStep 32986453 = 755) (by norm_num)
theorem B2512229 : Blo 1354996 2512229 := bbase (se 4 (by rfl) ⟨235521, by rfl⟩ : syracuseStep 2512229 = 471043) (by norm_num)
theorem B3052925 : Blo 1354996 3052925 := bbase (se 3 (by rfl) ⟨572423, by rfl⟩ : syracuseStep 3052925 = 1144847) (by norm_num)
theorem B4576661 : Blo 1354996 4576661 := bbase (se 6 (by rfl) ⟨107265, by rfl⟩ : syracuseStep 4576661 = 214531) (by norm_num)
theorem B3052997 : Blo 1354996 3052997 := bbase (se 4 (by rfl) ⟨286218, by rfl⟩ : syracuseStep 3052997 = 572437) (by norm_num)
theorem B15447509 : Blo 1354996 15447509 := bbase (se 7 (by rfl) ⟨181025, by rfl⟩ : syracuseStep 15447509 = 362051) (by norm_num)
theorem B2897365 : Blo 1354996 2897365 := bbase (se 7 (by rfl) ⟨33953, by rfl⟩ : syracuseStep 2897365 = 67907) (by norm_num)
theorem B3053069 : Blo 1354996 3053069 := bbase (se 3 (by rfl) ⟨572450, by rfl⟩ : syracuseStep 3053069 = 1144901) (by norm_num)
theorem B1488413 : Blo 1354996 1488413 := bbase (se 3 (by rfl) ⟨279077, by rfl⟩ : syracuseStep 1488413 = 558155) (by norm_num)
theorem B4126277 : Blo 1354996 4126277 := bbase (se 4 (by rfl) ⟨386838, by rfl⟩ : syracuseStep 4126277 = 773677) (by norm_num)
theorem B3429965 : Blo 1354996 3429965 := bbase (se 3 (by rfl) ⟨643118, by rfl⟩ : syracuseStep 3429965 = 1286237) (by norm_num)
theorem B3479125 : Blo 1354996 3479125 := bbase (se 8 (by rfl) ⟨20385, by rfl⟩ : syracuseStep 3479125 = 40771) (by norm_num)
theorem B3053141 : Blo 1354996 3053141 := bbase (se 8 (by rfl) ⟨17889, by rfl⟩ : syracuseStep 3053141 = 35779) (by norm_num)
theorem B1447517 : Blo 1354996 1447517 := bbase (se 3 (by rfl) ⟨271409, by rfl⟩ : syracuseStep 1447517 = 542819) (by norm_num)
theorem B3053213 : Blo 1354996 3053213 := bbase (se 3 (by rfl) ⟨572477, by rfl⟩ : syracuseStep 3053213 = 1144955) (by norm_num)
theorem B1447589 : Blo 1354996 1447589 := bbase (se 4 (by rfl) ⟨135711, by rfl⟩ : syracuseStep 1447589 = 271423) (by norm_num)
theorem B1373869 : Blo 1354996 1373869 := bbase (se 3 (by rfl) ⟨257600, by rfl⟩ : syracuseStep 1373869 = 515201) (by norm_num)
theorem B4126421 : Blo 1354996 4126421 := bbase (se 7 (by rfl) ⟨48356, by rfl⟩ : syracuseStep 4126421 = 96713) (by norm_num)
theorem B1373917 : Blo 1354996 1373917 := bbase (se 3 (by rfl) ⟨257609, by rfl⟩ : syracuseStep 1373917 = 515219) (by norm_num)
theorem B1545985 : Blo 1354996 1545985 := bbase (se 2 (by rfl) ⟨579744, by rfl⟩ : syracuseStep 1545985 = 1159489) (by norm_num)
theorem B4888325 : Blo 1354996 4888325 := bbase (se 4 (by rfl) ⟨458280, by rfl⟩ : syracuseStep 4888325 = 916561) (by norm_num)
theorem B1627933 : Blo 1354996 1627933 := bbase (se 3 (by rfl) ⟨305237, by rfl⟩ : syracuseStep 1627933 = 610475) (by norm_num)
theorem B1931053 : Blo 1354996 1931053 := bbase (se 3 (by rfl) ⟨362072, by rfl⟩ : syracuseStep 1931053 = 724145) (by norm_num)
theorem B4577093 : Blo 1354996 4577093 := bbase (se 4 (by rfl) ⟨429102, by rfl⟩ : syracuseStep 4577093 = 858205) (by norm_num)
theorem B2897741 : Blo 1354996 2897741 := bbase (se 3 (by rfl) ⟨543326, by rfl⟩ : syracuseStep 2897741 = 1086653) (by norm_num)
theorem B2062165 : Blo 1354996 2062165 := bbase (se 9 (by rfl) ⟨6041, by rfl⟩ : syracuseStep 2062165 = 12083) (by norm_num)
theorem B1447777 : Blo 1354996 1447777 := bbase (se 2 (by rfl) ⟨542916, by rfl⟩ : syracuseStep 1447777 = 1085833) (by norm_num)
theorem B2062189 : Blo 1354996 2062189 := bbase (se 3 (by rfl) ⟨386660, by rfl⟩ : syracuseStep 2062189 = 773321) (by norm_num)
theorem B3258269 : Blo 1354996 3258269 := bbase (se 3 (by rfl) ⟨610925, by rfl⟩ : syracuseStep 3258269 = 1221851) (by norm_num)
theorem B3430309 : Blo 1354996 3430309 := bbase (se 4 (by rfl) ⟨321591, by rfl⟩ : syracuseStep 3430309 = 643183) (by norm_num)
theorem B6862805 : Blo 1354996 6862805 := bbase (se 7 (by rfl) ⟨80423, by rfl⟩ : syracuseStep 6862805 = 160847) (by norm_num)
theorem B3094517 : Blo 1354996 3094517 := bbase (se 5 (by rfl) ⟨145055, by rfl⟩ : syracuseStep 3094517 = 290111) (by norm_num)
theorem B3430421 : Blo 1354996 3430421 := bbase (se 6 (by rfl) ⟨80400, by rfl⟩ : syracuseStep 3430421 = 160801) (by norm_num)
theorem B1447961 : Blo 1354996 1447961 := bbase (se 2 (by rfl) ⟨542985, by rfl⟩ : syracuseStep 1447961 = 1085971) (by norm_num)
theorem B2898109 : Blo 1354996 2898109 := bbase (se 3 (by rfl) ⟨543395, by rfl⟩ : syracuseStep 2898109 = 1086791) (by norm_num)
theorem B3430613 : Blo 1354996 3430613 := bbase (se 7 (by rfl) ⟨40202, by rfl⟩ : syracuseStep 3430613 = 80405) (by norm_num)
theorem B3258613 : Blo 1354996 3258613 := bbase (se 5 (by rfl) ⟨152747, by rfl⟩ : syracuseStep 3258613 = 305495) (by norm_num)
theorem B4577525 : Blo 1354996 4577525 := bbase (se 5 (by rfl) ⟨214571, by rfl⟩ : syracuseStep 4577525 = 429143) (by norm_num)
theorem B1374517 : Blo 1354996 1374517 := bbase (se 5 (by rfl) ⟨64430, by rfl⟩ : syracuseStep 1374517 = 128861) (by norm_num)
theorem B13031765 : Blo 1354996 13031765 := bbase (se 10 (by rfl) ⟨19089, by rfl⟩ : syracuseStep 13031765 = 38179) (by norm_num)
theorem B1931645 : Blo 1354996 1931645 := bbase (se 3 (by rfl) ⟨362183, by rfl⟩ : syracuseStep 1931645 = 724367) (by norm_num)
theorem B10041781 : Blo 1354996 10041781 := bbase (se 5 (by rfl) ⟨470708, by rfl⟩ : syracuseStep 10041781 = 941417) (by norm_num)
theorem B1931725 : Blo 1354996 1931725 := bbase (se 3 (by rfl) ⟨362198, by rfl⟩ : syracuseStep 1931725 = 724397) (by norm_num)
theorem B3258845 : Blo 1354996 3258845 := bbase (se 3 (by rfl) ⟨611033, by rfl⟩ : syracuseStep 3258845 = 1222067) (by norm_num)
theorem B5151221 : Blo 1354996 5151221 := bbase (se 5 (by rfl) ⟨241463, by rfl⟩ : syracuseStep 5151221 = 482927) (by norm_num)
theorem B2751013 : Blo 1354996 2751013 := bbase (se 4 (by rfl) ⟨257907, by rfl⟩ : syracuseStep 2751013 = 515815) (by norm_num)
theorem B3430957 : Blo 1354996 3430957 := bbase (se 3 (by rfl) ⟨643304, by rfl⟩ : syracuseStep 3430957 = 1286609) (by norm_num)
theorem B1374769 : Blo 1354996 1374769 := bbase (se 2 (by rfl) ⟨515538, by rfl⟩ : syracuseStep 1374769 = 1031077) (by norm_num)
theorem B1931845 : Blo 1354996 1931845 := bbase (se 4 (by rfl) ⟨181110, by rfl⟩ : syracuseStep 1931845 = 362221) (by norm_num)
theorem B3431069 : Blo 1354996 3431069 := bbase (se 3 (by rfl) ⟨643325, by rfl⟩ : syracuseStep 3431069 = 1286651) (by norm_num)
theorem B3259037 : Blo 1354996 3259037 := bbase (se 3 (by rfl) ⟨611069, by rfl⟩ : syracuseStep 3259037 = 1222139) (by norm_num)
theorem B4577957 : Blo 1354996 4577957 := bbase (se 4 (by rfl) ⟨429183, by rfl⟩ : syracuseStep 4577957 = 858367) (by norm_num)
theorem B1931941 : Blo 1354996 1931941 := bbase (se 4 (by rfl) ⟨181119, by rfl⟩ : syracuseStep 1931941 = 362239) (by norm_num)
theorem B10992341 : Blo 1354996 10992341 := bbase (se 7 (by rfl) ⟨128816, by rfl⟩ : syracuseStep 10992341 = 257633) (by norm_num)
theorem B1448713 : Blo 1354996 1448713 := bbase (se 2 (by rfl) ⟨543267, by rfl⟩ : syracuseStep 1448713 = 1086535) (by norm_num)
theorem B5151509 : Blo 1354996 5151509 := bbase (se 6 (by rfl) ⟨120738, by rfl⟩ : syracuseStep 5151509 = 241477) (by norm_num)
theorem B1448785 : Blo 1354996 1448785 := bbase (se 2 (by rfl) ⟨543294, by rfl⟩ : syracuseStep 1448785 = 1086589) (by norm_num)
theorem B3431261 : Blo 1354996 3431261 := bbase (se 3 (by rfl) ⟨643361, by rfl⟩ : syracuseStep 3431261 = 1286723) (by norm_num)
theorem B5790629 : Blo 1354996 5790629 := bbase (se 4 (by rfl) ⟨542871, by rfl⟩ : syracuseStep 5790629 = 1085743) (by norm_num)
theorem B3259325 : Blo 1354996 3259325 := bbase (se 3 (by rfl) ⟨611123, by rfl⟩ : syracuseStep 3259325 = 1222247) (by norm_num)
theorem B1448965 : Blo 1354996 1448965 := bbase (se 4 (by rfl) ⟨135840, by rfl⟩ : syracuseStep 1448965 = 271681) (by norm_num)
theorem B4578389 : Blo 1354996 4578389 := bbase (se 8 (by rfl) ⟨26826, by rfl⟩ : syracuseStep 4578389 = 53653) (by norm_num)
theorem B4889765 : Blo 1354996 4889765 := bbase (se 4 (by rfl) ⟨458415, by rfl⟩ : syracuseStep 4889765 = 916831) (by norm_num)
theorem B3431605 : Blo 1354996 3431605 := bbase (se 5 (by rfl) ⟨160856, by rfl⟩ : syracuseStep 3431605 = 321713) (by norm_num)
theorem B6864101 : Blo 1354996 6864101 := bbase (se 4 (by rfl) ⟨643509, by rfl⟩ : syracuseStep 6864101 = 1287019) (by norm_num)
theorem B3431717 : Blo 1354996 3431717 := bbase (se 4 (by rfl) ⟨321723, by rfl⟩ : syracuseStep 3431717 = 643447) (by norm_num)
theorem B3480869 : Blo 1354996 3480869 := bbase (se 4 (by rfl) ⟨326331, by rfl⟩ : syracuseStep 3480869 = 652663) (by norm_num)
theorem B4341077 : Blo 1354996 4341077 := bbase (se 11 (by rfl) ⟨3179, by rfl⟩ : syracuseStep 4341077 = 6359) (by norm_num)
theorem B8682869 : Blo 1354996 8682869 := bbase (se 5 (by rfl) ⟨407009, by rfl⟩ : syracuseStep 8682869 = 814019) (by norm_num)
theorem B3431909 : Blo 1354996 3431909 := bbase (se 4 (by rfl) ⟨321741, by rfl⟩ : syracuseStep 3431909 = 643483) (by norm_num)
theorem B4578821 : Blo 1354996 4578821 := bbase (se 4 (by rfl) ⟨429264, by rfl⟩ : syracuseStep 4578821 = 858529) (by norm_num)
theorem B1629725 : Blo 1354996 1629725 := bbase (se 3 (by rfl) ⟨305573, by rfl⟩ : syracuseStep 1629725 = 611147) (by norm_num)
theorem B6602485 : Blo 1354996 6602485 := bbase (se 5 (by rfl) ⟨309491, by rfl⟩ : syracuseStep 6602485 = 618983) (by norm_num)
theorem B3432253 : Blo 1354996 3432253 := bbase (se 3 (by rfl) ⟨643547, by rfl⟩ : syracuseStep 3432253 = 1287095) (by norm_num)
theorem B1630057 : Blo 1354996 1630057 := bbase (se 2 (by rfl) ⟨611271, by rfl⟩ : syracuseStep 1630057 = 1222543) (by norm_num)
theorem B5791621 : Blo 1354996 5791621 := bbase (se 4 (by rfl) ⟨542964, by rfl⟩ : syracuseStep 5791621 = 1085929) (by norm_num)
theorem B3432365 : Blo 1354996 3432365 := bbase (se 3 (by rfl) ⟨643568, by rfl⟩ : syracuseStep 3432365 = 1287137) (by norm_num)
theorem B4579253 : Blo 1354996 4579253 := bbase (se 5 (by rfl) ⟨214652, by rfl⟩ : syracuseStep 4579253 = 429305) (by norm_num)
theorem B3481525 : Blo 1354996 3481525 := bbase (se 5 (by rfl) ⟨163196, by rfl⟩ : syracuseStep 3481525 = 326393) (by norm_num)
theorem B37085141 : Blo 1354996 37085141 := bbase (se 7 (by rfl) ⟨434591, by rfl⟩ : syracuseStep 37085141 = 869183) (by norm_num)
theorem B11583445 : Blo 1354996 11583445 := bbase (se 7 (by rfl) ⟨135743, by rfl⟩ : syracuseStep 11583445 = 271487) (by norm_num)
theorem B1630201 : Blo 1354996 1630201 := bbase (se 2 (by rfl) ⟨611325, by rfl⟩ : syracuseStep 1630201 = 1222651) (by norm_num)
theorem B4579469 : Blo 1354996 4579469 := bstep (se 3 (by rfl) ⟨858650, by rfl⟩ : syracuseStep 4579469 = 1717301) B1717301
theorem B6865073 : Blo 1354996 6865073 := bstep (se 2 (by rfl) ⟨2574402, by rfl⟩ : syracuseStep 6865073 = 5148805) B5148805
theorem B4579523 : Blo 1354996 4579523 := bstep (se 1 (by rfl) ⟨3434642, by rfl⟩ : syracuseStep 4579523 = 6869285) B6869285
theorem B6512845 : Blo 1354996 6512845 := bstep (se 3 (by rfl) ⟨1221158, by rfl⟩ : syracuseStep 6512845 = 2442317) B2442317
theorem B3432689 : Blo 1354996 3432689 := bstep (se 2 (by rfl) ⟨1287258, by rfl⟩ : syracuseStep 3432689 = 2574517) B2574517
theorem B3432739 : Blo 1354996 3432739 := bstep (se 1 (by rfl) ⟨2574554, by rfl⟩ : syracuseStep 3432739 = 5149109) B5149109
theorem B17383733 : Blo 1354996 17383733 := bstep (se 5 (by rfl) ⟨814862, by rfl⟩ : syracuseStep 17383733 = 1629725) B1629725
theorem B3432881 : Blo 1354996 3432881 := bstep (se 2 (by rfl) ⟨1287330, by rfl⟩ : syracuseStep 3432881 = 2574661) B2574661
theorem B4579793 : Blo 1354996 4579793 := bstep (se 2 (by rfl) ⟨1717422, by rfl⟩ : syracuseStep 4579793 = 3434845) B3434845
theorem B4342243 : Blo 1354996 4342243 := bstep (se 1 (by rfl) ⟨3256682, by rfl⟩ : syracuseStep 4342243 = 6513365) B6513365
theorem B4637297 : Blo 1354996 4637297 := bstep (se 2 (by rfl) ⟨1738986, by rfl⟩ : syracuseStep 4637297 = 3477973) B3477973
theorem B2933425 : Blo 1354996 2933425 := bstep (se 2 (by rfl) ⟨1100034, by rfl⟩ : syracuseStep 2933425 = 2200069) B2200069
theorem B1524451 : Blo 1354996 1524451 := bstep (se 1 (by rfl) ⟨1143338, by rfl⟩ : syracuseStep 1524451 = 2286677) B2286677
theorem B2573059 : Blo 1354996 2573059 := bstep (se 1 (by rfl) ⟨1929794, by rfl⟩ : syracuseStep 2573059 = 3859589) B3859589
theorem B3859235 : Blo 1354996 3859235 := bstep (se 1 (by rfl) ⟨2894426, by rfl⟩ : syracuseStep 3859235 = 5788853) B5788853
theorem B1524595 : Blo 1354996 1524595 := bstep (se 1 (by rfl) ⟨1143446, by rfl⟩ : syracuseStep 1524595 = 2286893) B2286893
theorem B2032499 : Blo 1354996 2032499 := bstep (se 1 (by rfl) ⟨1524374, by rfl⟩ : syracuseStep 2032499 = 3048749) B3048749
theorem B2032529 : Blo 1354996 2032529 := bstep (se 2 (by rfl) ⟨762198, by rfl⟩ : syracuseStep 2032529 = 1524397) B1524397
theorem B2032547 : Blo 1354996 2032547 := bstep (se 1 (by rfl) ⟨1524410, by rfl⟩ : syracuseStep 2032547 = 3048821) B3048821
theorem B2032577 : Blo 1354996 2032577 := bstep (se 2 (by rfl) ⟨762216, by rfl⟩ : syracuseStep 2032577 = 1524433) B1524433
theorem B2032595 : Blo 1354996 2032595 := bstep (se 1 (by rfl) ⟨1524446, by rfl⟩ : syracuseStep 2032595 = 3048893) B3048893
theorem B10298339 : Blo 1354996 10298339 := bstep (se 1 (by rfl) ⟨7723754, by rfl⟩ : syracuseStep 10298339 = 15447509) B15447509
theorem B2032625 : Blo 1354996 2032625 := bstep (se 2 (by rfl) ⟨762234, by rfl⟩ : syracuseStep 2032625 = 1524469) B1524469
theorem B2032643 : Blo 1354996 2032643 := bstep (se 1 (by rfl) ⟨1524482, by rfl⟩ : syracuseStep 2032643 = 3048965) B3048965
theorem B1524739 : Blo 1354996 1524739 := bstep (se 1 (by rfl) ⟨1143554, by rfl⟩ : syracuseStep 1524739 = 2287109) B2287109
theorem B2032673 : Blo 1354996 2032673 := bstep (se 2 (by rfl) ⟨762252, by rfl⟩ : syracuseStep 2032673 = 1524505) B1524505
theorem B2286643 : Blo 1354996 2286643 := bstep (se 1 (by rfl) ⟨1714982, by rfl⟩ : syracuseStep 2286643 = 3429965) B3429965
theorem B2032691 : Blo 1354996 2032691 := bstep (se 1 (by rfl) ⟨1524518, by rfl⟩ : syracuseStep 2032691 = 3049037) B3049037
theorem B5145677 : Blo 1354996 5145677 := bstep (se 3 (by rfl) ⟨964814, by rfl⟩ : syracuseStep 5145677 = 1929629) B1929629
theorem B2032721 : Blo 1354996 2032721 := bstep (se 2 (by rfl) ⟨762270, by rfl⟩ : syracuseStep 2032721 = 1524541) B1524541
theorem B2032739 : Blo 1354996 2032739 := bstep (se 1 (by rfl) ⟨1524554, by rfl⟩ : syracuseStep 2032739 = 3049109) B3049109
theorem B2032769 : Blo 1354996 2032769 := bstep (se 2 (by rfl) ⟨762288, by rfl⟩ : syracuseStep 2032769 = 1524577) B1524577
theorem B2032787 : Blo 1354996 2032787 := bstep (se 1 (by rfl) ⟨1524590, by rfl⟩ : syracuseStep 2032787 = 3049181) B3049181
theorem B1524883 : Blo 1354996 1524883 := bstep (se 1 (by rfl) ⟨1143662, by rfl⟩ : syracuseStep 1524883 = 2287325) B2287325
theorem B6440099 : Blo 1354996 6440099 := bstep (se 1 (by rfl) ⟨4830074, by rfl⟩ : syracuseStep 6440099 = 9660149) B9660149
theorem B2032817 : Blo 1354996 2032817 := bstep (se 2 (by rfl) ⟨762306, by rfl⟩ : syracuseStep 2032817 = 1524613) B1524613
theorem B2286785 : Blo 1354996 2286785 := bstep (se 2 (by rfl) ⟨857544, by rfl⟩ : syracuseStep 2286785 = 1715089) B1715089
theorem B2032835 : Blo 1354996 2032835 := bstep (se 1 (by rfl) ⟨1524626, by rfl⟩ : syracuseStep 2032835 = 3049253) B3049253
theorem B2573507 : Blo 1354996 2573507 := bstep (se 1 (by rfl) ⟨1930130, by rfl⟩ : syracuseStep 2573507 = 3860261) B3860261
theorem B2032865 : Blo 1354996 2032865 := bstep (se 2 (by rfl) ⟨762324, by rfl⟩ : syracuseStep 2032865 = 1524649) B1524649
theorem B2032883 : Blo 1354996 2032883 := bstep (se 1 (by rfl) ⟨1524662, by rfl⟩ : syracuseStep 2032883 = 3049325) B3049325
theorem B11584781 : Blo 1354996 11584781 := bstep (se 3 (by rfl) ⟨2172146, by rfl⟩ : syracuseStep 11584781 = 4344293) B4344293
theorem B2032913 : Blo 1354996 2032913 := bstep (se 2 (by rfl) ⟨762342, by rfl⟩ : syracuseStep 2032913 = 1524685) B1524685
theorem B2172179 : Blo 1354996 2172179 := bstep (se 1 (by rfl) ⟨1629134, by rfl⟩ : syracuseStep 2172179 = 3258269) B3258269
theorem B2032931 : Blo 1354996 2032931 := bstep (se 1 (by rfl) ⟨1524698, by rfl⟩ : syracuseStep 2032931 = 3049397) B3049397
theorem B1525027 : Blo 1354996 1525027 := bstep (se 1 (by rfl) ⟨1143770, by rfl⟩ : syracuseStep 1525027 = 2287541) B2287541
theorem B4343075 : Blo 1354996 4343075 := bstep (se 1 (by rfl) ⟨3257306, by rfl⟩ : syracuseStep 4343075 = 6514613) B6514613
theorem B2286913 : Blo 1354996 2286913 := bstep (se 2 (by rfl) ⟨857592, by rfl⟩ : syracuseStep 2286913 = 1715185) B1715185
theorem B2032961 : Blo 1354996 2032961 := bstep (se 2 (by rfl) ⟨762360, by rfl⟩ : syracuseStep 2032961 = 1524721) B1524721
theorem B3048785 : Blo 1354996 3048785 := bstep (se 2 (by rfl) ⟨1143294, by rfl⟩ : syracuseStep 3048785 = 2286589) B2286589
theorem B2032979 : Blo 1354996 2032979 := bstep (se 1 (by rfl) ⟨1524734, by rfl⟩ : syracuseStep 2032979 = 3049469) B3049469
theorem B3048803 : Blo 1354996 3048803 := bstep (se 1 (by rfl) ⟨2286602, by rfl⟩ : syracuseStep 3048803 = 4573205) B4573205
theorem B2286947 : Blo 1354996 2286947 := bstep (se 1 (by rfl) ⟨1715210, by rfl⟩ : syracuseStep 2286947 = 3430421) B3430421
theorem B2033009 : Blo 1354996 2033009 := bstep (se 2 (by rfl) ⟨762378, by rfl⟩ : syracuseStep 2033009 = 1524757) B1524757
theorem B2033027 : Blo 1354996 2033027 := bstep (se 1 (by rfl) ⟨1524770, by rfl⟩ : syracuseStep 2033027 = 3049541) B3049541
theorem B3433873 : Blo 1354996 3433873 := bstep (se 2 (by rfl) ⟨1287702, by rfl⟩ : syracuseStep 3433873 = 2575405) B2575405
theorem B2033057 : Blo 1354996 2033057 := bstep (se 2 (by rfl) ⟨762396, by rfl⟩ : syracuseStep 2033057 = 1524793) B1524793
theorem B2033075 : Blo 1354996 2033075 := bstep (se 1 (by rfl) ⟨1524806, by rfl⟩ : syracuseStep 2033075 = 3049613) B3049613
theorem B1525171 : Blo 1354996 1525171 := bstep (se 1 (by rfl) ⟨1143878, by rfl⟩ : syracuseStep 1525171 = 2287757) B2287757
theorem B2033105 : Blo 1354996 2033105 := bstep (se 2 (by rfl) ⟨762414, by rfl⟩ : syracuseStep 2033105 = 1524829) B1524829
theorem B2287075 : Blo 1354996 2287075 := bstep (se 1 (by rfl) ⟨1715306, by rfl⟩ : syracuseStep 2287075 = 3430613) B3430613
theorem B2033123 : Blo 1354996 2033123 := bstep (se 1 (by rfl) ⟨1524842, by rfl⟩ : syracuseStep 2033123 = 3049685) B3049685
theorem B2573795 : Blo 1354996 2573795 := bstep (se 1 (by rfl) ⟨1930346, by rfl⟩ : syracuseStep 2573795 = 3860693) B3860693
theorem B2033153 : Blo 1354996 2033153 := bstep (se 2 (by rfl) ⟨762432, by rfl⟩ : syracuseStep 2033153 = 1524865) B1524865
theorem B2033171 : Blo 1354996 2033171 := bstep (se 1 (by rfl) ⟨1524878, by rfl⟩ : syracuseStep 2033171 = 3049757) B3049757
theorem B2033201 : Blo 1354996 2033201 := bstep (se 2 (by rfl) ⟨762450, by rfl⟩ : syracuseStep 2033201 = 1524901) B1524901
theorem B2033219 : Blo 1354996 2033219 := bstep (se 1 (by rfl) ⟨1524914, by rfl⟩ : syracuseStep 2033219 = 3049829) B3049829
theorem B1525315 : Blo 1354996 1525315 := bstep (se 1 (by rfl) ⟨1143986, by rfl⟩ : syracuseStep 1525315 = 2287973) B2287973
theorem B3860045 : Blo 1354996 3860045 := bstep (se 3 (by rfl) ⟨723758, by rfl⟩ : syracuseStep 3860045 = 1447517) B1447517
theorem B2033249 : Blo 1354996 2033249 := bstep (se 2 (by rfl) ⟨762468, by rfl⟩ : syracuseStep 2033249 = 1524937) B1524937
theorem B6866531 : Blo 1354996 6866531 := bstep (se 1 (by rfl) ⟨5149898, by rfl⟩ : syracuseStep 6866531 = 10299797) B10299797
theorem B3049073 : Blo 1354996 3049073 := bstep (se 2 (by rfl) ⟨1143402, by rfl⟩ : syracuseStep 3049073 = 2286805) B2286805
theorem B2287217 : Blo 1354996 2287217 := bstep (se 2 (by rfl) ⟨857706, by rfl⟩ : syracuseStep 2287217 = 1715413) B1715413
theorem B2033267 : Blo 1354996 2033267 := bstep (se 1 (by rfl) ⟨1524950, by rfl⟩ : syracuseStep 2033267 = 3049901) B3049901
theorem B6514289 : Blo 1354996 6514289 := bstep (se 2 (by rfl) ⟨2442858, by rfl⟩ : syracuseStep 6514289 = 4885717) B4885717
theorem B3049091 : Blo 1354996 3049091 := bstep (se 1 (by rfl) ⟨2286818, by rfl⟩ : syracuseStep 3049091 = 4573637) B4573637
theorem B2033297 : Blo 1354996 2033297 := bstep (se 2 (by rfl) ⟨762486, by rfl⟩ : syracuseStep 2033297 = 1524973) B1524973
theorem B2172563 : Blo 1354996 2172563 := bstep (se 1 (by rfl) ⟨1629422, by rfl⟩ : syracuseStep 2172563 = 3258845) B3258845
theorem B2033315 : Blo 1354996 2033315 := bstep (se 1 (by rfl) ⟨1524986, by rfl⟩ : syracuseStep 2033315 = 3049973) B3049973
theorem B3434147 : Blo 1354996 3434147 := bstep (se 1 (by rfl) ⟨2575610, by rfl⟩ : syracuseStep 3434147 = 5151221) B5151221
theorem B4343473 : Blo 1354996 4343473 := bstep (se 2 (by rfl) ⟨1628802, by rfl⟩ : syracuseStep 4343473 = 3257605) B3257605
theorem B2033345 : Blo 1354996 2033345 := bstep (se 2 (by rfl) ⟨762504, by rfl⟩ : syracuseStep 2033345 = 1525009) B1525009
theorem B2033363 : Blo 1354996 2033363 := bstep (se 1 (by rfl) ⟨1525022, by rfl⟩ : syracuseStep 2033363 = 3050045) B3050045
theorem B1525459 : Blo 1354996 1525459 := bstep (se 1 (by rfl) ⟨1144094, by rfl⟩ : syracuseStep 1525459 = 2288189) B2288189
theorem B4343537 : Blo 1354996 4343537 := bstep (se 2 (by rfl) ⟨1628826, by rfl⟩ : syracuseStep 4343537 = 3257653) B3257653
theorem B2287345 : Blo 1354996 2287345 := bstep (se 2 (by rfl) ⟨857754, by rfl⟩ : syracuseStep 2287345 = 1715509) B1715509
theorem B2033393 : Blo 1354996 2033393 := bstep (se 2 (by rfl) ⟨762522, by rfl⟩ : syracuseStep 2033393 = 1525045) B1525045
theorem B2033411 : Blo 1354996 2033411 := bstep (se 1 (by rfl) ⟨1525058, by rfl⟩ : syracuseStep 2033411 = 3050117) B3050117
theorem B7726853 : Blo 1354996 7726853 := bstep (se 4 (by rfl) ⟨724392, by rfl⟩ : syracuseStep 7726853 = 1448785) B1448785
theorem B3860237 : Blo 1354996 3860237 := bstep (se 3 (by rfl) ⟨723794, by rfl⟩ : syracuseStep 3860237 = 1447589) B1447589
theorem B6956813 : Blo 1354996 6956813 := bstep (se 3 (by rfl) ⟨1304402, by rfl⟩ : syracuseStep 6956813 = 2608805) B2608805
theorem B2287379 : Blo 1354996 2287379 := bstep (se 1 (by rfl) ⟨1715534, by rfl⟩ : syracuseStep 2287379 = 3431069) B3431069
theorem B2172691 : Blo 1354996 2172691 := bstep (se 1 (by rfl) ⟨1629518, by rfl⟩ : syracuseStep 2172691 = 3259037) B3259037
theorem B2033441 : Blo 1354996 2033441 := bstep (se 2 (by rfl) ⟨762540, by rfl⟩ : syracuseStep 2033441 = 1525081) B1525081
theorem B2033459 : Blo 1354996 2033459 := bstep (se 1 (by rfl) ⟨1525094, by rfl⟩ : syracuseStep 2033459 = 3050189) B3050189
theorem B2033489 : Blo 1354996 2033489 := bstep (se 2 (by rfl) ⟨762558, by rfl⟩ : syracuseStep 2033489 = 1525117) B1525117
theorem B2033507 : Blo 1354996 2033507 := bstep (se 1 (by rfl) ⟨1525130, by rfl⟩ : syracuseStep 2033507 = 3050261) B3050261
theorem B1525603 : Blo 1354996 1525603 := bstep (se 1 (by rfl) ⟨1144202, by rfl⟩ : syracuseStep 1525603 = 2288405) B2288405
theorem B3434339 : Blo 1354996 3434339 := bstep (se 1 (by rfl) ⟨2575754, by rfl⟩ : syracuseStep 3434339 = 5151509) B5151509
theorem B2033537 : Blo 1354996 2033537 := bstep (se 2 (by rfl) ⟨762576, by rfl⟩ : syracuseStep 2033537 = 1525153) B1525153
theorem B11003789 : Blo 1354996 11003789 := bstep (se 3 (by rfl) ⟨2063210, by rfl⟩ : syracuseStep 11003789 = 4126421) B4126421
theorem B3049361 : Blo 1354996 3049361 := bstep (se 2 (by rfl) ⟨1143510, by rfl⟩ : syracuseStep 3049361 = 2287021) B2287021
theorem B2287507 : Blo 1354996 2287507 := bstep (se 1 (by rfl) ⟨1715630, by rfl⟩ : syracuseStep 2287507 = 3431261) B3431261
theorem B2033555 : Blo 1354996 2033555 := bstep (se 1 (by rfl) ⟨1525166, by rfl⟩ : syracuseStep 2033555 = 3050333) B3050333
theorem B3049379 : Blo 1354996 3049379 := bstep (se 1 (by rfl) ⟨2287034, by rfl⟩ : syracuseStep 3049379 = 4574069) B4574069
theorem B2033585 : Blo 1354996 2033585 := bstep (se 2 (by rfl) ⟨762594, by rfl⟩ : syracuseStep 2033585 = 1525189) B1525189
theorem B2033603 : Blo 1354996 2033603 := bstep (se 1 (by rfl) ⟨1525202, by rfl⟩ : syracuseStep 2033603 = 3050405) B3050405
theorem B2033633 : Blo 1354996 2033633 := bstep (se 2 (by rfl) ⟨762612, by rfl⟩ : syracuseStep 2033633 = 1525225) B1525225
theorem B2033651 : Blo 1354996 2033651 := bstep (se 1 (by rfl) ⟨1525238, by rfl⟩ : syracuseStep 2033651 = 3050477) B3050477
theorem B1525747 : Blo 1354996 1525747 := bstep (se 1 (by rfl) ⟨1144310, by rfl⟩ : syracuseStep 1525747 = 2288621) B2288621
theorem B2033681 : Blo 1354996 2033681 := bstep (se 2 (by rfl) ⟨762630, by rfl⟩ : syracuseStep 2033681 = 1525261) B1525261
theorem B2287649 : Blo 1354996 2287649 := bstep (se 2 (by rfl) ⟨857868, by rfl⟩ : syracuseStep 2287649 = 1715737) B1715737
theorem B2033699 : Blo 1354996 2033699 := bstep (se 1 (by rfl) ⟨1525274, by rfl⟩ : syracuseStep 2033699 = 3050549) B3050549
theorem B23169077 : Blo 1354996 23169077 := bstep (se 5 (by rfl) ⟨1086050, by rfl⟩ : syracuseStep 23169077 = 2172101) B2172101
theorem B2033729 : Blo 1354996 2033729 := bstep (se 2 (by rfl) ⟨762648, by rfl⟩ : syracuseStep 2033729 = 1525297) B1525297
theorem B15435845 : Blo 1354996 15435845 := bstep (se 4 (by rfl) ⟨1447110, by rfl⟩ : syracuseStep 15435845 = 2894221) B2894221
theorem B2033747 : Blo 1354996 2033747 := bstep (se 1 (by rfl) ⟨1525310, by rfl⟩ : syracuseStep 2033747 = 3050621) B3050621
theorem B2033777 : Blo 1354996 2033777 := bstep (se 2 (by rfl) ⟨762666, by rfl⟩ : syracuseStep 2033777 = 1525333) B1525333
theorem B4638833 : Blo 1354996 4638833 := bstep (se 2 (by rfl) ⟨1739562, by rfl⟩ : syracuseStep 4638833 = 3479125) B3479125
theorem B2033795 : Blo 1354996 2033795 := bstep (se 1 (by rfl) ⟨1525346, by rfl⟩ : syracuseStep 2033795 = 3050693) B3050693
theorem B1525891 : Blo 1354996 1525891 := bstep (se 1 (by rfl) ⟨1144418, by rfl⟩ : syracuseStep 1525891 = 2288837) B2288837
theorem B2287777 : Blo 1354996 2287777 := bstep (se 2 (by rfl) ⟨857916, by rfl⟩ : syracuseStep 2287777 = 1715833) B1715833
theorem B2033825 : Blo 1354996 2033825 := bstep (se 2 (by rfl) ⟨762684, by rfl⟩ : syracuseStep 2033825 = 1525369) B1525369
theorem B3049649 : Blo 1354996 3049649 := bstep (se 2 (by rfl) ⟨1143618, by rfl⟩ : syracuseStep 3049649 = 2287237) B2287237
theorem B2033843 : Blo 1354996 2033843 := bstep (se 1 (by rfl) ⟨1525382, by rfl⟩ : syracuseStep 2033843 = 3050765) B3050765
theorem B3049667 : Blo 1354996 3049667 := bstep (se 1 (by rfl) ⟨2287250, by rfl⟩ : syracuseStep 3049667 = 4574501) B4574501
theorem B2287811 : Blo 1354996 2287811 := bstep (se 1 (by rfl) ⟨1715858, by rfl⟩ : syracuseStep 2287811 = 3431717) B3431717
theorem B2320579 : Blo 1354996 2320579 := bstep (se 1 (by rfl) ⟨1740434, by rfl⟩ : syracuseStep 2320579 = 3480869) B3480869
theorem B7727309 : Blo 1354996 7727309 := bstep (se 3 (by rfl) ⟨1448870, by rfl⟩ : syracuseStep 7727309 = 2897741) B2897741
theorem B2033873 : Blo 1354996 2033873 := bstep (se 2 (by rfl) ⟨762702, by rfl⟩ : syracuseStep 2033873 = 1525405) B1525405
theorem B2894051 : Blo 1354996 2894051 := bstep (se 1 (by rfl) ⟨2170538, by rfl⟩ : syracuseStep 2894051 = 4341077) B4341077
theorem B2033891 : Blo 1354996 2033891 := bstep (se 1 (by rfl) ⟨1525418, by rfl⟩ : syracuseStep 2033891 = 3050837) B3050837
theorem B4573421 : Blo 1354996 4573421 := bstep (se 3 (by rfl) ⟨857516, by rfl⟩ : syracuseStep 4573421 = 1715033) B1715033
theorem B2033921 : Blo 1354996 2033921 := bstep (se 2 (by rfl) ⟨762720, by rfl⟩ : syracuseStep 2033921 = 1525441) B1525441
theorem B2033939 : Blo 1354996 2033939 := bstep (se 1 (by rfl) ⟨1525454, by rfl⟩ : syracuseStep 2033939 = 3050909) B3050909
theorem B1526035 : Blo 1354996 1526035 := bstep (se 1 (by rfl) ⟨1144526, by rfl⟩ : syracuseStep 1526035 = 2289053) B2289053
theorem B4573475 : Blo 1354996 4573475 := bstep (se 1 (by rfl) ⟨3430106, by rfl⟩ : syracuseStep 4573475 = 6860213) B6860213
theorem B2033969 : Blo 1354996 2033969 := bstep (se 2 (by rfl) ⟨762738, by rfl⟩ : syracuseStep 2033969 = 1525477) B1525477
theorem B2287939 : Blo 1354996 2287939 := bstep (se 1 (by rfl) ⟨1715954, by rfl⟩ : syracuseStep 2287939 = 3431909) B3431909
theorem B2033987 : Blo 1354996 2033987 := bstep (se 1 (by rfl) ⟨1525490, by rfl⟩ : syracuseStep 2033987 = 3050981) B3050981
theorem B7719245 : Blo 1354996 7719245 := bstep (se 3 (by rfl) ⟨1447358, by rfl⟩ : syracuseStep 7719245 = 2894717) B2894717
theorem B2034017 : Blo 1354996 2034017 := bstep (se 2 (by rfl) ⟨762756, by rfl⟩ : syracuseStep 2034017 = 1525513) B1525513
theorem B2034035 : Blo 1354996 2034035 := bstep (se 1 (by rfl) ⟨1525526, by rfl⟩ : syracuseStep 2034035 = 3051053) B3051053
theorem B6867341 : Blo 1354996 6867341 := bstep (se 3 (by rfl) ⟨1287626, by rfl⟩ : syracuseStep 6867341 = 2575253) B2575253
theorem B2034065 : Blo 1354996 2034065 := bstep (se 2 (by rfl) ⟨762774, by rfl⟩ : syracuseStep 2034065 = 1525549) B1525549
theorem B2574737 : Blo 1354996 2574737 := bstep (se 2 (by rfl) ⟨965526, by rfl⟩ : syracuseStep 2574737 = 1931053) B1931053
theorem B2034083 : Blo 1354996 2034083 := bstep (se 1 (by rfl) ⟨1525562, by rfl⟩ : syracuseStep 2034083 = 3051125) B3051125
theorem B1526179 : Blo 1354996 1526179 := bstep (se 1 (by rfl) ⟨1144634, by rfl⟩ : syracuseStep 1526179 = 2289269) B2289269
theorem B2034113 : Blo 1354996 2034113 := bstep (se 2 (by rfl) ⟨762792, by rfl⟩ : syracuseStep 2034113 = 1525585) B1525585
theorem B5794253 : Blo 1354996 5794253 := bstep (se 3 (by rfl) ⟨1086422, by rfl⟩ : syracuseStep 5794253 = 2172845) B2172845
theorem B3049937 : Blo 1354996 3049937 := bstep (se 2 (by rfl) ⟨1143726, by rfl⟩ : syracuseStep 3049937 = 2287453) B2287453
theorem B2288081 : Blo 1354996 2288081 := bstep (se 2 (by rfl) ⟨858030, by rfl⟩ : syracuseStep 2288081 = 1716061) B1716061
theorem B2034131 : Blo 1354996 2034131 := bstep (se 1 (by rfl) ⟨1525598, by rfl⟩ : syracuseStep 2034131 = 3051197) B3051197
theorem B2173409 : Blo 1354996 2173409 := bstep (se 2 (by rfl) ⟨815028, by rfl⟩ : syracuseStep 2173409 = 1630057) B1630057
theorem B3049955 : Blo 1354996 3049955 := bstep (se 1 (by rfl) ⟨2287466, by rfl⟩ : syracuseStep 3049955 = 4574933) B4574933
theorem B2034161 : Blo 1354996 2034161 := bstep (se 2 (by rfl) ⟨762810, by rfl⟩ : syracuseStep 2034161 = 1525621) B1525621
theorem B2034179 : Blo 1354996 2034179 := bstep (se 1 (by rfl) ⟨1525634, by rfl⟩ : syracuseStep 2034179 = 3051269) B3051269
theorem B2034209 : Blo 1354996 2034209 := bstep (se 2 (by rfl) ⟨762828, by rfl⟩ : syracuseStep 2034209 = 1525657) B1525657
theorem B4573745 : Blo 1354996 4573745 := bstep (se 2 (by rfl) ⟨1715154, by rfl⟩ : syracuseStep 4573745 = 3430309) B3430309
theorem B2034227 : Blo 1354996 2034227 := bstep (se 1 (by rfl) ⟨1525670, by rfl⟩ : syracuseStep 2034227 = 3051341) B3051341
theorem B1526323 : Blo 1354996 1526323 := bstep (se 1 (by rfl) ⟨1144742, by rfl⟩ : syracuseStep 1526323 = 2289485) B2289485
theorem B2288209 : Blo 1354996 2288209 := bstep (se 2 (by rfl) ⟨858078, by rfl⟩ : syracuseStep 2288209 = 1716157) B1716157
theorem B2034257 : Blo 1354996 2034257 := bstep (se 2 (by rfl) ⟨762846, by rfl⟩ : syracuseStep 2034257 = 1525693) B1525693
theorem B2034275 : Blo 1354996 2034275 := bstep (se 1 (by rfl) ⟨1525706, by rfl⟩ : syracuseStep 2034275 = 3051413) B3051413
theorem B9767537 : Blo 1354996 9767537 := bstep (se 2 (by rfl) ⟨3662826, by rfl⟩ : syracuseStep 9767537 = 7325653) B7325653
theorem B15444593 : Blo 1354996 15444593 := bstep (se 2 (by rfl) ⟨5791722, by rfl⟩ : syracuseStep 15444593 = 11583445) B11583445
theorem B2288243 : Blo 1354996 2288243 := bstep (se 1 (by rfl) ⟨1716182, by rfl⟩ : syracuseStep 2288243 = 3432365) B3432365
theorem B2034305 : Blo 1354996 2034305 := bstep (se 2 (by rfl) ⟨762864, by rfl⟩ : syracuseStep 2034305 = 1525729) B1525729
theorem B2034323 : Blo 1354996 2034323 := bstep (se 1 (by rfl) ⟨1525742, by rfl⟩ : syracuseStep 2034323 = 3051485) B3051485
theorem B2173601 : Blo 1354996 2173601 := bstep (se 2 (by rfl) ⟨815100, by rfl⟩ : syracuseStep 2173601 = 1630201) B1630201
theorem B2034353 : Blo 1354996 2034353 := bstep (se 2 (by rfl) ⟨762882, by rfl⟩ : syracuseStep 2034353 = 1525765) B1525765
theorem B1739459 : Blo 1354996 1739459 := bstep (se 1 (by rfl) ⟨1304594, by rfl⟩ : syracuseStep 1739459 = 2609189) B2609189
theorem B2034371 : Blo 1354996 2034371 := bstep (se 1 (by rfl) ⟨1525778, by rfl⟩ : syracuseStep 2034371 = 3051557) B3051557
theorem B1526467 : Blo 1354996 1526467 := bstep (se 1 (by rfl) ⟨1144850, by rfl⟩ : syracuseStep 1526467 = 2289701) B2289701
theorem B2034401 : Blo 1354996 2034401 := bstep (se 2 (by rfl) ⟨762900, by rfl⟩ : syracuseStep 2034401 = 1525801) B1525801
theorem B2894563 : Blo 1354996 2894563 := bstep (se 1 (by rfl) ⟨2170922, by rfl⟩ : syracuseStep 2894563 = 4341845) B4341845
theorem B3861229 : Blo 1354996 3861229 := bstep (se 3 (by rfl) ⟨723980, by rfl⟩ : syracuseStep 3861229 = 1447961) B1447961
theorem B3050225 : Blo 1354996 3050225 := bstep (se 2 (by rfl) ⟨1143834, by rfl⟩ : syracuseStep 3050225 = 2287669) B2287669
theorem B2288371 : Blo 1354996 2288371 := bstep (se 1 (by rfl) ⟨1716278, by rfl⟩ : syracuseStep 2288371 = 3432557) B3432557
theorem B2034419 : Blo 1354996 2034419 := bstep (se 1 (by rfl) ⟨1525814, by rfl⟩ : syracuseStep 2034419 = 3051629) B3051629
theorem B3050243 : Blo 1354996 3050243 := bstep (se 1 (by rfl) ⟨2287682, by rfl⟩ : syracuseStep 3050243 = 4575365) B4575365
theorem B2034449 : Blo 1354996 2034449 := bstep (se 2 (by rfl) ⟨762918, by rfl⟩ : syracuseStep 2034449 = 1525837) B1525837
theorem B93940501 : Blo 1354996 93940501 := bstep (se 6 (by rfl) ⟨2201730, by rfl⟩ : syracuseStep 93940501 = 4403461) B4403461
theorem B2034467 : Blo 1354996 2034467 := bstep (se 1 (by rfl) ⟨1525850, by rfl⟩ : syracuseStep 2034467 = 3051701) B3051701
theorem B2034497 : Blo 1354996 2034497 := bstep (se 2 (by rfl) ⟨762936, by rfl⟩ : syracuseStep 2034497 = 1525873) B1525873
theorem B2034515 : Blo 1354996 2034515 := bstep (se 1 (by rfl) ⟨1525886, by rfl⟩ : syracuseStep 2034515 = 3051773) B3051773
theorem B1526611 : Blo 1354996 1526611 := bstep (se 1 (by rfl) ⟨1144958, by rfl⟩ : syracuseStep 1526611 = 2289917) B2289917
theorem B2034545 : Blo 1354996 2034545 := bstep (se 2 (by rfl) ⟨762954, by rfl⟩ : syracuseStep 2034545 = 1525909) B1525909
theorem B9407345 : Blo 1354996 9407345 := bstep (se 2 (by rfl) ⟨3527754, by rfl⟩ : syracuseStep 9407345 = 7055509) B7055509
theorem B2288513 : Blo 1354996 2288513 := bstep (se 2 (by rfl) ⟨858192, by rfl⟩ : syracuseStep 2288513 = 1716385) B1716385
theorem B2034563 : Blo 1354996 2034563 := bstep (se 1 (by rfl) ⟨1525922, by rfl⟩ : syracuseStep 2034563 = 3051845) B3051845
theorem B7326605 : Blo 1354996 7326605 := bstep (se 3 (by rfl) ⟨1373738, by rfl⟩ : syracuseStep 7326605 = 2747477) B2747477
theorem B2034593 : Blo 1354996 2034593 := bstep (se 2 (by rfl) ⟨762972, by rfl⟩ : syracuseStep 2034593 = 1525945) B1525945
theorem B3664817 : Blo 1354996 3664817 := bstep (se 2 (by rfl) ⟨1374306, by rfl⟩ : syracuseStep 3664817 = 2748613) B2748613
theorem B2034611 : Blo 1354996 2034611 := bstep (se 1 (by rfl) ⟨1525958, by rfl⟩ : syracuseStep 2034611 = 3051917) B3051917
theorem B2034641 : Blo 1354996 2034641 := bstep (se 2 (by rfl) ⟨762990, by rfl⟩ : syracuseStep 2034641 = 1525981) B1525981
theorem B2034659 : Blo 1354996 2034659 := bstep (se 1 (by rfl) ⟨1525994, by rfl⟩ : syracuseStep 2034659 = 3051989) B3051989
theorem B2288641 : Blo 1354996 2288641 := bstep (se 2 (by rfl) ⟨858240, by rfl⟩ : syracuseStep 2288641 = 1716481) B1716481
theorem B2034689 : Blo 1354996 2034689 := bstep (se 2 (by rfl) ⟨763008, by rfl⟩ : syracuseStep 2034689 = 1526017) B1526017
theorem B3050513 : Blo 1354996 3050513 := bstep (se 2 (by rfl) ⟨1143942, by rfl⟩ : syracuseStep 3050513 = 2287885) B2287885
theorem B2034707 : Blo 1354996 2034707 := bstep (se 1 (by rfl) ⟨1526030, by rfl⟩ : syracuseStep 2034707 = 3052061) B3052061
theorem B3050531 : Blo 1354996 3050531 := bstep (se 1 (by rfl) ⟨2287898, by rfl⟩ : syracuseStep 3050531 = 4575797) B4575797
theorem B2288675 : Blo 1354996 2288675 := bstep (se 1 (by rfl) ⟨1716506, by rfl⟩ : syracuseStep 2288675 = 3433013) B3433013
theorem B2034737 : Blo 1354996 2034737 := bstep (se 2 (by rfl) ⟨763026, by rfl⟩ : syracuseStep 2034737 = 1526053) B1526053
theorem B1715251 : Blo 1354996 1715251 := bstep (se 1 (by rfl) ⟨1286438, by rfl⟩ : syracuseStep 1715251 = 2572877) B2572877
theorem B2034755 : Blo 1354996 2034755 := bstep (se 1 (by rfl) ⟨1526066, by rfl⟩ : syracuseStep 2034755 = 3052133) B3052133
theorem B4574285 : Blo 1354996 4574285 := bstep (se 3 (by rfl) ⟨857678, by rfl⟩ : syracuseStep 4574285 = 1715357) B1715357
theorem B2034785 : Blo 1354996 2034785 := bstep (se 2 (by rfl) ⟨763044, by rfl⟩ : syracuseStep 2034785 = 1526089) B1526089
theorem B6859889 : Blo 1354996 6859889 := bstep (se 2 (by rfl) ⟨2572458, by rfl⟩ : syracuseStep 6859889 = 5144917) B5144917
theorem B2034803 : Blo 1354996 2034803 := bstep (se 1 (by rfl) ⟨1526102, by rfl⟩ : syracuseStep 2034803 = 3052205) B3052205
theorem B4574339 : Blo 1354996 4574339 := bstep (se 1 (by rfl) ⟨3430754, by rfl⟩ : syracuseStep 4574339 = 6861509) B6861509
theorem B2034833 : Blo 1354996 2034833 := bstep (se 2 (by rfl) ⟨763062, by rfl⟩ : syracuseStep 2034833 = 1526125) B1526125
theorem B1715347 : Blo 1354996 1715347 := bstep (se 1 (by rfl) ⟨1286510, by rfl⟩ : syracuseStep 1715347 = 2573021) B2573021
theorem B2288803 : Blo 1354996 2288803 := bstep (se 1 (by rfl) ⟨1716602, by rfl⟩ : syracuseStep 2288803 = 3433205) B3433205
theorem B2034851 : Blo 1354996 2034851 := bstep (se 1 (by rfl) ⟨1526138, by rfl⟩ : syracuseStep 2034851 = 3052277) B3052277
theorem B2034881 : Blo 1354996 2034881 := bstep (se 2 (by rfl) ⟨763080, by rfl⟩ : syracuseStep 2034881 = 1526161) B1526161
theorem B2034899 : Blo 1354996 2034899 := bstep (se 1 (by rfl) ⟨1526174, by rfl⟩ : syracuseStep 2034899 = 3052349) B3052349
theorem B13389041 : Blo 1354996 13389041 := bstep (se 2 (by rfl) ⟨5020890, by rfl⟩ : syracuseStep 13389041 = 10041781) B10041781
theorem B2034929 : Blo 1354996 2034929 := bstep (se 2 (by rfl) ⟨763098, by rfl⟩ : syracuseStep 2034929 = 1526197) B1526197
theorem B1355011 : Blo 1354996 1355011 := bstep (se 1 (by rfl) ⟨1016258, by rfl⟩ : syracuseStep 1355011 = 2032517) B2032517
theorem B2034947 : Blo 1354996 2034947 := bstep (se 1 (by rfl) ⟨1526210, by rfl⟩ : syracuseStep 2034947 = 3052421) B3052421
theorem B2575633 : Blo 1354996 2575633 := bstep (se 2 (by rfl) ⟨965862, by rfl⟩ : syracuseStep 2575633 = 1931725) B1931725
theorem B1355027 : Blo 1354996 1355027 := bstep (se 1 (by rfl) ⟨1016270, by rfl⟩ : syracuseStep 1355027 = 2032541) B2032541
theorem B2034977 : Blo 1354996 2034977 := bstep (se 2 (by rfl) ⟨763116, by rfl⟩ : syracuseStep 2034977 = 1526233) B1526233
theorem B1355043 : Blo 1354996 1355043 := bstep (se 1 (by rfl) ⟨1016282, by rfl⟩ : syracuseStep 1355043 = 2032565) B2032565
theorem B3050801 : Blo 1354996 3050801 := bstep (se 2 (by rfl) ⟨1144050, by rfl⟩ : syracuseStep 3050801 = 2288101) B2288101
theorem B2288945 : Blo 1354996 2288945 := bstep (se 2 (by rfl) ⟨858354, by rfl⟩ : syracuseStep 2288945 = 1716709) B1716709
theorem B1355059 : Blo 1354996 1355059 := bstep (se 1 (by rfl) ⟨1016294, by rfl⟩ : syracuseStep 1355059 = 2032589) B2032589
theorem B2034995 : Blo 1354996 2034995 := bstep (se 1 (by rfl) ⟨1526246, by rfl⟩ : syracuseStep 2034995 = 3052493) B3052493
theorem B1355075 : Blo 1354996 1355075 := bstep (se 1 (by rfl) ⟨1016306, by rfl⟩ : syracuseStep 1355075 = 2032613) B2032613
theorem B3050819 : Blo 1354996 3050819 := bstep (se 1 (by rfl) ⟨2288114, by rfl⟩ : syracuseStep 3050819 = 4576229) B4576229
theorem B2035025 : Blo 1354996 2035025 := bstep (se 2 (by rfl) ⟨763134, by rfl⟩ : syracuseStep 2035025 = 1526269) B1526269
theorem B1355091 : Blo 1354996 1355091 := bstep (se 1 (by rfl) ⟨1016318, by rfl⟩ : syracuseStep 1355091 = 2032637) B2032637
theorem B1355107 : Blo 1354996 1355107 := bstep (se 1 (by rfl) ⟨1016330, by rfl⟩ : syracuseStep 1355107 = 2032661) B2032661
theorem B2035043 : Blo 1354996 2035043 := bstep (se 1 (by rfl) ⟨1526282, by rfl⟩ : syracuseStep 2035043 = 3052565) B3052565
theorem B13036913 : Blo 1354996 13036913 := bstep (se 2 (by rfl) ⟨4888842, by rfl⟩ : syracuseStep 13036913 = 9777685) B9777685
theorem B1355123 : Blo 1354996 1355123 := bstep (se 1 (by rfl) ⟨1016342, by rfl⟩ : syracuseStep 1355123 = 2032685) B2032685
theorem B2035073 : Blo 1354996 2035073 := bstep (se 2 (by rfl) ⟨763152, by rfl⟩ : syracuseStep 2035073 = 1526305) B1526305
theorem B1355139 : Blo 1354996 1355139 := bstep (se 1 (by rfl) ⟨1016354, by rfl⟩ : syracuseStep 1355139 = 2032709) B2032709
theorem B4574609 : Blo 1354996 4574609 := bstep (se 2 (by rfl) ⟨1715478, by rfl⟩ : syracuseStep 4574609 = 3430957) B3430957
theorem B1355155 : Blo 1354996 1355155 := bstep (se 1 (by rfl) ⟨1016366, by rfl⟩ : syracuseStep 1355155 = 2032733) B2032733
theorem B2035091 : Blo 1354996 2035091 := bstep (se 1 (by rfl) ⟨1526318, by rfl⟩ : syracuseStep 2035091 = 3052637) B3052637
theorem B1355171 : Blo 1354996 1355171 := bstep (se 1 (by rfl) ⟨1016378, by rfl⟩ : syracuseStep 1355171 = 2032757) B2032757
theorem B2895281 : Blo 1354996 2895281 := bstep (se 2 (by rfl) ⟨1085730, by rfl⟩ : syracuseStep 2895281 = 2171461) B2171461
theorem B2289073 : Blo 1354996 2289073 := bstep (se 2 (by rfl) ⟨858402, by rfl⟩ : syracuseStep 2289073 = 1716805) B1716805
theorem B1355187 : Blo 1354996 1355187 := bstep (se 1 (by rfl) ⟨1016390, by rfl⟩ : syracuseStep 1355187 = 2032781) B2032781
theorem B2035121 : Blo 1354996 2035121 := bstep (se 2 (by rfl) ⟨763170, by rfl⟩ : syracuseStep 2035121 = 1526341) B1526341
theorem B2575793 : Blo 1354996 2575793 := bstep (se 2 (by rfl) ⟨965922, by rfl⟩ : syracuseStep 2575793 = 1931845) B1931845
theorem B1355203 : Blo 1354996 1355203 := bstep (se 1 (by rfl) ⟨1016402, by rfl⟩ : syracuseStep 1355203 = 2032805) B2032805
theorem B2035139 : Blo 1354996 2035139 := bstep (se 1 (by rfl) ⟨1526354, by rfl⟩ : syracuseStep 2035139 = 3052709) B3052709
theorem B1355219 : Blo 1354996 1355219 := bstep (se 1 (by rfl) ⟨1016414, by rfl⟩ : syracuseStep 1355219 = 2032829) B2032829
theorem B2289107 : Blo 1354996 2289107 := bstep (se 1 (by rfl) ⟨1716830, by rfl⟩ : syracuseStep 2289107 = 3433661) B3433661
theorem B2035169 : Blo 1354996 2035169 := bstep (se 2 (by rfl) ⟨763188, by rfl⟩ : syracuseStep 2035169 = 1526377) B1526377
theorem B1355235 : Blo 1354996 1355235 := bstep (se 1 (by rfl) ⟨1016426, by rfl⟩ : syracuseStep 1355235 = 2032853) B2032853
theorem B1355251 : Blo 1354996 1355251 := bstep (se 1 (by rfl) ⟨1016438, by rfl⟩ : syracuseStep 1355251 = 2032877) B2032877
theorem B2035187 : Blo 1354996 2035187 := bstep (se 1 (by rfl) ⟨1526390, by rfl⟩ : syracuseStep 2035187 = 3052781) B3052781
theorem B1355267 : Blo 1354996 1355267 := bstep (se 1 (by rfl) ⟨1016450, by rfl⟩ : syracuseStep 1355267 = 2032901) B2032901
theorem B2035217 : Blo 1354996 2035217 := bstep (se 2 (by rfl) ⟨763206, by rfl⟩ : syracuseStep 2035217 = 1526413) B1526413
theorem B1355283 : Blo 1354996 1355283 := bstep (se 1 (by rfl) ⟨1016462, by rfl⟩ : syracuseStep 1355283 = 2032925) B2032925
theorem B1355299 : Blo 1354996 1355299 := bstep (se 1 (by rfl) ⟨1016474, by rfl⟩ : syracuseStep 1355299 = 2032949) B2032949
theorem B2035235 : Blo 1354996 2035235 := bstep (se 1 (by rfl) ⟨1526426, by rfl⟩ : syracuseStep 2035235 = 3052853) B3052853
theorem B1355315 : Blo 1354996 1355315 := bstep (se 1 (by rfl) ⟨1016486, by rfl⟩ : syracuseStep 1355315 = 2032973) B2032973
theorem B2035265 : Blo 1354996 2035265 := bstep (se 2 (by rfl) ⟨763224, by rfl⟩ : syracuseStep 2035265 = 1526449) B1526449
theorem B1355331 : Blo 1354996 1355331 := bstep (se 1 (by rfl) ⟨1016498, by rfl⟩ : syracuseStep 1355331 = 2032997) B2032997
theorem B3051089 : Blo 1354996 3051089 := bstep (se 2 (by rfl) ⟨1144158, by rfl⟩ : syracuseStep 3051089 = 2288317) B2288317
theorem B1355347 : Blo 1354996 1355347 := bstep (se 1 (by rfl) ⟨1016510, by rfl⟩ : syracuseStep 1355347 = 2033021) B2033021
theorem B2289235 : Blo 1354996 2289235 := bstep (se 1 (by rfl) ⟨1716926, by rfl⟩ : syracuseStep 2289235 = 3433853) B3433853
theorem B2035283 : Blo 1354996 2035283 := bstep (se 1 (by rfl) ⟨1526462, by rfl⟩ : syracuseStep 2035283 = 3052925) B3052925
theorem B1355363 : Blo 1354996 1355363 := bstep (se 1 (by rfl) ⟨1016522, by rfl⟩ : syracuseStep 1355363 = 2033045) B2033045
theorem B3051107 : Blo 1354996 3051107 := bstep (se 1 (by rfl) ⟨2288330, by rfl⟩ : syracuseStep 3051107 = 4576661) B4576661
theorem B2035313 : Blo 1354996 2035313 := bstep (se 2 (by rfl) ⟨763242, by rfl⟩ : syracuseStep 2035313 = 1526485) B1526485
theorem B1355379 : Blo 1354996 1355379 := bstep (se 1 (by rfl) ⟨1016534, by rfl⟩ : syracuseStep 1355379 = 2033069) B2033069
theorem B1355395 : Blo 1354996 1355395 := bstep (se 1 (by rfl) ⟨1016546, by rfl⟩ : syracuseStep 1355395 = 2033093) B2033093
theorem B1715843 : Blo 1354996 1715843 := bstep (se 1 (by rfl) ⟨1286882, by rfl⟩ : syracuseStep 1715843 = 2573765) B2573765
theorem B2035331 : Blo 1354996 2035331 := bstep (se 1 (by rfl) ⟨1526498, by rfl⟩ : syracuseStep 2035331 = 3052997) B3052997
theorem B1355411 : Blo 1354996 1355411 := bstep (se 1 (by rfl) ⟨1016558, by rfl⟩ : syracuseStep 1355411 = 2033117) B2033117
theorem B2035361 : Blo 1354996 2035361 := bstep (se 2 (by rfl) ⟨763260, by rfl⟩ : syracuseStep 2035361 = 1526521) B1526521
theorem B1355427 : Blo 1354996 1355427 := bstep (se 1 (by rfl) ⟨1016570, by rfl⟩ : syracuseStep 1355427 = 2033141) B2033141
theorem B1355443 : Blo 1354996 1355443 := bstep (se 1 (by rfl) ⟨1016582, by rfl⟩ : syracuseStep 1355443 = 2033165) B2033165
theorem B2035379 : Blo 1354996 2035379 := bstep (se 1 (by rfl) ⟨1526534, by rfl⟩ : syracuseStep 2035379 = 3053069) B3053069
theorem B1355459 : Blo 1354996 1355459 := bstep (se 1 (by rfl) ⟨1016594, by rfl⟩ : syracuseStep 1355459 = 2033189) B2033189
theorem B2035409 : Blo 1354996 2035409 := bstep (se 2 (by rfl) ⟨763278, by rfl⟩ : syracuseStep 2035409 = 1526557) B1526557
theorem B1355475 : Blo 1354996 1355475 := bstep (se 1 (by rfl) ⟨1016606, by rfl⟩ : syracuseStep 1355475 = 2033213) B2033213
theorem B2289377 : Blo 1354996 2289377 := bstep (se 2 (by rfl) ⟨858516, by rfl⟩ : syracuseStep 2289377 = 1717033) B1717033
theorem B1650403 : Blo 1354996 1650403 := bstep (se 1 (by rfl) ⟨1237802, by rfl⟩ : syracuseStep 1650403 = 2475605) B2475605
theorem B1355491 : Blo 1354996 1355491 := bstep (se 1 (by rfl) ⟨1016618, by rfl⟩ : syracuseStep 1355491 = 2033237) B2033237
theorem B2035427 : Blo 1354996 2035427 := bstep (se 1 (by rfl) ⟨1526570, by rfl⟩ : syracuseStep 2035427 = 3053141) B3053141
theorem B1355507 : Blo 1354996 1355507 := bstep (se 1 (by rfl) ⟨1016630, by rfl⟩ : syracuseStep 1355507 = 2033261) B2033261
theorem B1355523 : Blo 1354996 1355523 := bstep (se 1 (by rfl) ⟨1016642, by rfl⟩ : syracuseStep 1355523 = 2033285) B2033285
theorem B2035457 : Blo 1354996 2035457 := bstep (se 2 (by rfl) ⟨763296, by rfl⟩ : syracuseStep 2035457 = 1526593) B1526593
theorem B1355539 : Blo 1354996 1355539 := bstep (se 1 (by rfl) ⟨1016654, by rfl⟩ : syracuseStep 1355539 = 2033309) B2033309
theorem B2035475 : Blo 1354996 2035475 := bstep (se 1 (by rfl) ⟨1526606, by rfl⟩ : syracuseStep 2035475 = 3053213) B3053213
theorem B1355555 : Blo 1354996 1355555 := bstep (se 1 (by rfl) ⟨1016666, by rfl⟩ : syracuseStep 1355555 = 2033333) B2033333
theorem B1355571 : Blo 1354996 1355571 := bstep (se 1 (by rfl) ⟨1016678, by rfl⟩ : syracuseStep 1355571 = 2033357) B2033357
theorem B1355587 : Blo 1354996 1355587 := bstep (se 1 (by rfl) ⟨1016690, by rfl⟩ : syracuseStep 1355587 = 2033381) B2033381
theorem B1355603 : Blo 1354996 1355603 := bstep (se 1 (by rfl) ⟨1016702, by rfl⟩ : syracuseStep 1355603 = 2033405) B2033405
theorem B2289505 : Blo 1354996 2289505 := bstep (se 2 (by rfl) ⟨858564, by rfl⟩ : syracuseStep 2289505 = 1717129) B1717129
theorem B1355619 : Blo 1354996 1355619 := bstep (se 1 (by rfl) ⟨1016714, by rfl⟩ : syracuseStep 1355619 = 2033429) B2033429
theorem B3051377 : Blo 1354996 3051377 := bstep (se 2 (by rfl) ⟨1144266, by rfl⟩ : syracuseStep 3051377 = 2288533) B2288533
theorem B1355635 : Blo 1354996 1355635 := bstep (se 1 (by rfl) ⟨1016726, by rfl⟩ : syracuseStep 1355635 = 2033453) B2033453
theorem B1355651 : Blo 1354996 1355651 := bstep (se 1 (by rfl) ⟨1016738, by rfl⟩ : syracuseStep 1355651 = 2033477) B2033477
theorem B3051395 : Blo 1354996 3051395 := bstep (se 1 (by rfl) ⟨2288546, by rfl⟩ : syracuseStep 3051395 = 4577093) B4577093
theorem B2289539 : Blo 1354996 2289539 := bstep (se 1 (by rfl) ⟨1717154, by rfl⟩ : syracuseStep 2289539 = 3434309) B3434309
theorem B1355667 : Blo 1354996 1355667 := bstep (se 1 (by rfl) ⟨1016750, by rfl⟩ : syracuseStep 1355667 = 2033501) B2033501
theorem B1355683 : Blo 1354996 1355683 := bstep (se 1 (by rfl) ⟨1016762, by rfl⟩ : syracuseStep 1355683 = 2033525) B2033525
theorem B4575149 : Blo 1354996 4575149 := bstep (se 3 (by rfl) ⟨857840, by rfl⟩ : syracuseStep 4575149 = 1715681) B1715681
theorem B5148593 : Blo 1354996 5148593 := bstep (se 2 (by rfl) ⟨1930722, by rfl⟩ : syracuseStep 5148593 = 3861445) B3861445
theorem B1355699 : Blo 1354996 1355699 := bstep (se 1 (by rfl) ⟨1016774, by rfl⟩ : syracuseStep 1355699 = 2033549) B2033549
theorem B1355715 : Blo 1354996 1355715 := bstep (se 1 (by rfl) ⟨1016786, by rfl⟩ : syracuseStep 1355715 = 2033573) B2033573
theorem B17379269 : Blo 1354996 17379269 := bstep (se 4 (by rfl) ⟨1629306, by rfl⟩ : syracuseStep 17379269 = 3258613) B3258613
theorem B2060243 : Blo 1354996 2060243 := bstep (se 1 (by rfl) ⟨1545182, by rfl⟩ : syracuseStep 2060243 = 3090365) B3090365
theorem B1355731 : Blo 1354996 1355731 := bstep (se 1 (by rfl) ⟨1016798, by rfl⟩ : syracuseStep 1355731 = 2033597) B2033597
theorem B4575203 : Blo 1354996 4575203 := bstep (se 1 (by rfl) ⟨3431402, by rfl⟩ : syracuseStep 4575203 = 6862805) B6862805
theorem B1355747 : Blo 1354996 1355747 := bstep (se 1 (by rfl) ⟨1016810, by rfl⟩ : syracuseStep 1355747 = 2033621) B2033621
theorem B1355763 : Blo 1354996 1355763 := bstep (se 1 (by rfl) ⟨1016822, by rfl⟩ : syracuseStep 1355763 = 2033645) B2033645
theorem B1355779 : Blo 1354996 1355779 := bstep (se 1 (by rfl) ⟨1016834, by rfl⟩ : syracuseStep 1355779 = 2033669) B2033669
theorem B2289667 : Blo 1354996 2289667 := bstep (se 1 (by rfl) ⟨1717250, by rfl⟩ : syracuseStep 2289667 = 3434501) B3434501
theorem B8245253 : Blo 1354996 8245253 := bstep (se 4 (by rfl) ⟨772992, by rfl⟩ : syracuseStep 8245253 = 1545985) B1545985
theorem B1355795 : Blo 1354996 1355795 := bstep (se 1 (by rfl) ⟨1016846, by rfl⟩ : syracuseStep 1355795 = 2033693) B2033693
theorem B1355811 : Blo 1354996 1355811 := bstep (se 1 (by rfl) ⟨1016858, by rfl⟩ : syracuseStep 1355811 = 2033717) B2033717
theorem B1355827 : Blo 1354996 1355827 := bstep (se 1 (by rfl) ⟨1016870, by rfl⟩ : syracuseStep 1355827 = 2033741) B2033741
theorem B1355843 : Blo 1354996 1355843 := bstep (se 1 (by rfl) ⟨1016882, by rfl⟩ : syracuseStep 1355843 = 2033765) B2033765
theorem B3969101 : Blo 1354996 3969101 := bstep (se 3 (by rfl) ⟨744206, by rfl⟩ : syracuseStep 3969101 = 1488413) B1488413
theorem B1355859 : Blo 1354996 1355859 := bstep (se 1 (by rfl) ⟨1016894, by rfl⟩ : syracuseStep 1355859 = 2033789) B2033789
theorem B1355875 : Blo 1354996 1355875 := bstep (se 1 (by rfl) ⟨1016906, by rfl⟩ : syracuseStep 1355875 = 2033813) B2033813
theorem B2060401 : Blo 1354996 2060401 := bstep (se 2 (by rfl) ⟨772650, by rfl⟩ : syracuseStep 2060401 = 1545301) B1545301
theorem B3092593 : Blo 1354996 3092593 := bstep (se 2 (by rfl) ⟨1159722, by rfl⟩ : syracuseStep 3092593 = 2319445) B2319445
theorem B1355891 : Blo 1354996 1355891 := bstep (se 1 (by rfl) ⟨1016918, by rfl⟩ : syracuseStep 1355891 = 2033837) B2033837
theorem B1355907 : Blo 1354996 1355907 := bstep (se 1 (by rfl) ⟨1016930, by rfl⟩ : syracuseStep 1355907 = 2033861) B2033861
theorem B3051665 : Blo 1354996 3051665 := bstep (se 2 (by rfl) ⟨1144374, by rfl⟩ : syracuseStep 3051665 = 2288749) B2288749
theorem B2289809 : Blo 1354996 2289809 := bstep (se 2 (by rfl) ⟨858678, by rfl⟩ : syracuseStep 2289809 = 1717357) B1717357
theorem B1355923 : Blo 1354996 1355923 := bstep (se 1 (by rfl) ⟨1016942, by rfl⟩ : syracuseStep 1355923 = 2033885) B2033885
theorem B1355939 : Blo 1354996 1355939 := bstep (se 1 (by rfl) ⟨1016954, by rfl⟩ : syracuseStep 1355939 = 2033909) B2033909
theorem B3051683 : Blo 1354996 3051683 := bstep (se 1 (by rfl) ⟨2288762, by rfl⟩ : syracuseStep 3051683 = 4577525) B4577525
theorem B1355955 : Blo 1354996 1355955 := bstep (se 1 (by rfl) ⟨1016966, by rfl⟩ : syracuseStep 1355955 = 2033933) B2033933
theorem B1355971 : Blo 1354996 1355971 := bstep (se 1 (by rfl) ⟨1016978, by rfl⟩ : syracuseStep 1355971 = 2033957) B2033957
theorem B2896067 : Blo 1354996 2896067 := bstep (se 1 (by rfl) ⟨2172050, by rfl⟩ : syracuseStep 2896067 = 4344101) B4344101
theorem B1355987 : Blo 1354996 1355987 := bstep (se 1 (by rfl) ⟨1016990, by rfl⟩ : syracuseStep 1355987 = 2033981) B2033981
theorem B8687843 : Blo 1354996 8687843 := bstep (se 1 (by rfl) ⟨6515882, by rfl⟩ : syracuseStep 8687843 = 13031765) B13031765
theorem B1356003 : Blo 1354996 1356003 := bstep (se 1 (by rfl) ⟨1017002, by rfl⟩ : syracuseStep 1356003 = 2034005) B2034005
theorem B4575473 : Blo 1354996 4575473 := bstep (se 2 (by rfl) ⟨1715802, by rfl⟩ : syracuseStep 4575473 = 3431605) B3431605
theorem B1356019 : Blo 1354996 1356019 := bstep (se 1 (by rfl) ⟨1017014, by rfl⟩ : syracuseStep 1356019 = 2034029) B2034029
theorem B1356035 : Blo 1354996 1356035 := bstep (se 1 (by rfl) ⟨1017026, by rfl⟩ : syracuseStep 1356035 = 2034053) B2034053
theorem B2060561 : Blo 1354996 2060561 := bstep (se 2 (by rfl) ⟨772710, by rfl⟩ : syracuseStep 2060561 = 1545421) B1545421
theorem B1356051 : Blo 1354996 1356051 := bstep (se 1 (by rfl) ⟨1017038, by rfl⟩ : syracuseStep 1356051 = 2034077) B2034077
theorem B1356067 : Blo 1354996 1356067 := bstep (se 1 (by rfl) ⟨1017050, by rfl⟩ : syracuseStep 1356067 = 2034101) B2034101
theorem B3911981 : Blo 1354996 3911981 := bstep (se 3 (by rfl) ⟨733496, by rfl⟩ : syracuseStep 3911981 = 1466993) B1466993
theorem B1929521 : Blo 1354996 1929521 := bstep (se 2 (by rfl) ⟨723570, by rfl⟩ : syracuseStep 1929521 = 1447141) B1447141
theorem B1356083 : Blo 1354996 1356083 := bstep (se 1 (by rfl) ⟨1017062, by rfl⟩ : syracuseStep 1356083 = 2034125) B2034125
theorem B1356099 : Blo 1354996 1356099 := bstep (se 1 (by rfl) ⟨1017074, by rfl⟩ : syracuseStep 1356099 = 2034149) B2034149
theorem B1716547 : Blo 1354996 1716547 := bstep (se 1 (by rfl) ⟨1287410, by rfl⟩ : syracuseStep 1716547 = 2574821) B2574821
theorem B1356115 : Blo 1354996 1356115 := bstep (se 1 (by rfl) ⟨1017086, by rfl⟩ : syracuseStep 1356115 = 2034173) B2034173
theorem B1356131 : Blo 1354996 1356131 := bstep (se 1 (by rfl) ⟨1017098, by rfl⟩ : syracuseStep 1356131 = 2034197) B2034197
theorem B1356147 : Blo 1354996 1356147 := bstep (se 1 (by rfl) ⟨1017110, by rfl⟩ : syracuseStep 1356147 = 2034221) B2034221
theorem B3092867 : Blo 1354996 3092867 := bstep (se 1 (by rfl) ⟨2319650, by rfl⟩ : syracuseStep 3092867 = 4639301) B4639301
theorem B1356163 : Blo 1354996 1356163 := bstep (se 1 (by rfl) ⟨1017122, by rfl⟩ : syracuseStep 1356163 = 2034245) B2034245
theorem B1356179 : Blo 1354996 1356179 := bstep (se 1 (by rfl) ⟨1017134, by rfl⟩ : syracuseStep 1356179 = 2034269) B2034269
theorem B1356195 : Blo 1354996 1356195 := bstep (se 1 (by rfl) ⟨1017146, by rfl⟩ : syracuseStep 1356195 = 2034293) B2034293
theorem B1716643 : Blo 1354996 1716643 := bstep (se 1 (by rfl) ⟨1287482, by rfl⟩ : syracuseStep 1716643 = 2574965) B2574965
theorem B3051953 : Blo 1354996 3051953 := bstep (se 2 (by rfl) ⟨1144482, by rfl⟩ : syracuseStep 3051953 = 2288965) B2288965
theorem B3862961 : Blo 1354996 3862961 := bstep (se 2 (by rfl) ⟨1448610, by rfl⟩ : syracuseStep 3862961 = 2897221) B2897221
theorem B1356211 : Blo 1354996 1356211 := bstep (se 1 (by rfl) ⟨1017158, by rfl⟩ : syracuseStep 1356211 = 2034317) B2034317
theorem B1356227 : Blo 1354996 1356227 := bstep (se 1 (by rfl) ⟨1017170, by rfl⟩ : syracuseStep 1356227 = 2034341) B2034341
theorem B3051971 : Blo 1354996 3051971 := bstep (se 1 (by rfl) ⟨2288978, by rfl⟩ : syracuseStep 3051971 = 4577957) B4577957
theorem B1356243 : Blo 1354996 1356243 := bstep (se 1 (by rfl) ⟨1017182, by rfl⟩ : syracuseStep 1356243 = 2034365) B2034365
theorem B7328227 : Blo 1354996 7328227 := bstep (se 1 (by rfl) ⟨5496170, by rfl⟩ : syracuseStep 7328227 = 10992341) B10992341
theorem B1356259 : Blo 1354996 1356259 := bstep (se 1 (by rfl) ⟨1017194, by rfl⟩ : syracuseStep 1356259 = 2034389) B2034389
theorem B1356275 : Blo 1354996 1356275 := bstep (se 1 (by rfl) ⟨1017206, by rfl⟩ : syracuseStep 1356275 = 2034413) B2034413
theorem B1356291 : Blo 1354996 1356291 := bstep (se 1 (by rfl) ⟨1017218, by rfl⟩ : syracuseStep 1356291 = 2034437) B2034437
theorem B7721477 : Blo 1354996 7721477 := bstep (se 4 (by rfl) ⟨723888, by rfl⟩ : syracuseStep 7721477 = 1447777) B1447777
theorem B1356307 : Blo 1354996 1356307 := bstep (se 1 (by rfl) ⟨1017230, by rfl⟩ : syracuseStep 1356307 = 2034461) B2034461
theorem B6861347 : Blo 1354996 6861347 := bstep (se 1 (by rfl) ⟨5146010, by rfl⟩ : syracuseStep 6861347 = 10292021) B10292021
theorem B1356323 : Blo 1354996 1356323 := bstep (se 1 (by rfl) ⟨1017242, by rfl⟩ : syracuseStep 1356323 = 2034485) B2034485
theorem B1356339 : Blo 1354996 1356339 := bstep (se 1 (by rfl) ⟨1017254, by rfl⟩ : syracuseStep 1356339 = 2034509) B2034509
theorem B1356355 : Blo 1354996 1356355 := bstep (se 1 (by rfl) ⟨1017266, by rfl⟩ : syracuseStep 1356355 = 2034533) B2034533
theorem B1356371 : Blo 1354996 1356371 := bstep (se 1 (by rfl) ⟨1017278, by rfl⟩ : syracuseStep 1356371 = 2034557) B2034557
theorem B1356387 : Blo 1354996 1356387 := bstep (se 1 (by rfl) ⟨1017290, by rfl⟩ : syracuseStep 1356387 = 2034581) B2034581
theorem B49459825 : Blo 1354996 49459825 := bstep (se 2 (by rfl) ⟨18547434, by rfl⟩ : syracuseStep 49459825 = 37094869) B37094869
theorem B3863153 : Blo 1354996 3863153 := bstep (se 2 (by rfl) ⟨1448682, by rfl⟩ : syracuseStep 3863153 = 2897365) B2897365
theorem B1356403 : Blo 1354996 1356403 := bstep (se 1 (by rfl) ⟨1017302, by rfl⟩ : syracuseStep 1356403 = 2034605) B2034605
theorem B1356419 : Blo 1354996 1356419 := bstep (se 1 (by rfl) ⟨1017314, by rfl⟩ : syracuseStep 1356419 = 2034629) B2034629
theorem B1356435 : Blo 1354996 1356435 := bstep (se 1 (by rfl) ⟨1017326, by rfl⟩ : syracuseStep 1356435 = 2034653) B2034653
theorem B1356451 : Blo 1354996 1356451 := bstep (se 1 (by rfl) ⟨1017338, by rfl⟩ : syracuseStep 1356451 = 2034677) B2034677
theorem B1356467 : Blo 1354996 1356467 := bstep (se 1 (by rfl) ⟨1017350, by rfl⟩ : syracuseStep 1356467 = 2034701) B2034701
theorem B1356483 : Blo 1354996 1356483 := bstep (se 1 (by rfl) ⟨1017362, by rfl⟩ : syracuseStep 1356483 = 2034725) B2034725
theorem B3052241 : Blo 1354996 3052241 := bstep (se 2 (by rfl) ⟨1144590, by rfl⟩ : syracuseStep 3052241 = 2289181) B2289181
theorem B1356499 : Blo 1354996 1356499 := bstep (se 1 (by rfl) ⟨1017374, by rfl⟩ : syracuseStep 1356499 = 2034749) B2034749
theorem B1356515 : Blo 1354996 1356515 := bstep (se 1 (by rfl) ⟨1017386, by rfl⟩ : syracuseStep 1356515 = 2034773) B2034773
theorem B3052259 : Blo 1354996 3052259 := bstep (se 1 (by rfl) ⟨2289194, by rfl⟩ : syracuseStep 3052259 = 4578389) B4578389
theorem B1356531 : Blo 1354996 1356531 := bstep (se 1 (by rfl) ⟨1017398, by rfl⟩ : syracuseStep 1356531 = 2034797) B2034797
theorem B1356547 : Blo 1354996 1356547 := bstep (se 1 (by rfl) ⟨1017410, by rfl⟩ : syracuseStep 1356547 = 2034821) B2034821
theorem B4576013 : Blo 1354996 4576013 := bstep (se 3 (by rfl) ⟨858002, by rfl⟩ : syracuseStep 4576013 = 1716005) B1716005
theorem B1356563 : Blo 1354996 1356563 := bstep (se 1 (by rfl) ⟨1017422, by rfl⟩ : syracuseStep 1356563 = 2034845) B2034845
theorem B1356579 : Blo 1354996 1356579 := bstep (se 1 (by rfl) ⟨1017434, by rfl⟩ : syracuseStep 1356579 = 2034869) B2034869
theorem B1356595 : Blo 1354996 1356595 := bstep (se 1 (by rfl) ⟨1017446, by rfl⟩ : syracuseStep 1356595 = 2034893) B2034893
theorem B4576067 : Blo 1354996 4576067 := bstep (se 1 (by rfl) ⟨3432050, by rfl⟩ : syracuseStep 4576067 = 6864101) B6864101
theorem B1356611 : Blo 1354996 1356611 := bstep (se 1 (by rfl) ⟨1017458, by rfl⟩ : syracuseStep 1356611 = 2034917) B2034917
theorem B1356627 : Blo 1354996 1356627 := bstep (se 1 (by rfl) ⟨1017470, by rfl⟩ : syracuseStep 1356627 = 2034941) B2034941
theorem B1356643 : Blo 1354996 1356643 := bstep (se 1 (by rfl) ⟨1017482, by rfl⟩ : syracuseStep 1356643 = 2034965) B2034965
theorem B1356659 : Blo 1354996 1356659 := bstep (se 1 (by rfl) ⟨1017494, by rfl⟩ : syracuseStep 1356659 = 2034989) B2034989
theorem B1356675 : Blo 1354996 1356675 := bstep (se 1 (by rfl) ⟨1017506, by rfl⟩ : syracuseStep 1356675 = 2035013) B2035013
theorem B4641677 : Blo 1354996 4641677 := bstep (se 3 (by rfl) ⟨870314, by rfl⟩ : syracuseStep 4641677 = 1740629) B1740629
theorem B1831825 : Blo 1354996 1831825 := bstep (se 2 (by rfl) ⟨686934, by rfl⟩ : syracuseStep 1831825 = 1373869) B1373869
theorem B1356691 : Blo 1354996 1356691 := bstep (se 1 (by rfl) ⟨1017518, by rfl⟩ : syracuseStep 1356691 = 2035037) B2035037
theorem B1717139 : Blo 1354996 1717139 := bstep (se 1 (by rfl) ⟨1287854, by rfl⟩ : syracuseStep 1717139 = 2575709) B2575709
theorem B5788579 : Blo 1354996 5788579 := bstep (se 1 (by rfl) ⟨4341434, by rfl⟩ : syracuseStep 5788579 = 8682869) B8682869
theorem B1356707 : Blo 1354996 1356707 := bstep (se 1 (by rfl) ⟨1017530, by rfl⟩ : syracuseStep 1356707 = 2035061) B2035061
theorem B1356723 : Blo 1354996 1356723 := bstep (se 1 (by rfl) ⟨1017542, by rfl⟩ : syracuseStep 1356723 = 2035085) B2035085
theorem B1356739 : Blo 1354996 1356739 := bstep (se 1 (by rfl) ⟨1017554, by rfl⟩ : syracuseStep 1356739 = 2035109) B2035109
theorem B1831889 : Blo 1354996 1831889 := bstep (se 2 (by rfl) ⟨686958, by rfl⟩ : syracuseStep 1831889 = 1373917) B1373917
theorem B1356755 : Blo 1354996 1356755 := bstep (se 1 (by rfl) ⟨1017566, by rfl⟩ : syracuseStep 1356755 = 2035133) B2035133
theorem B1356771 : Blo 1354996 1356771 := bstep (se 1 (by rfl) ⟨1017578, by rfl⟩ : syracuseStep 1356771 = 2035157) B2035157
theorem B8803313 : Blo 1354996 8803313 := bstep (se 2 (by rfl) ⟨3301242, by rfl⟩ : syracuseStep 8803313 = 6602485) B6602485
theorem B3052529 : Blo 1354996 3052529 := bstep (se 2 (by rfl) ⟨1144698, by rfl⟩ : syracuseStep 3052529 = 2289397) B2289397
theorem B1356787 : Blo 1354996 1356787 := bstep (se 1 (by rfl) ⟨1017590, by rfl⟩ : syracuseStep 1356787 = 2035181) B2035181
theorem B3052547 : Blo 1354996 3052547 := bstep (se 1 (by rfl) ⟨2289410, by rfl⟩ : syracuseStep 3052547 = 4578821) B4578821
theorem B1356803 : Blo 1354996 1356803 := bstep (se 1 (by rfl) ⟨1017602, by rfl⟩ : syracuseStep 1356803 = 2035205) B2035205
theorem B1356819 : Blo 1354996 1356819 := bstep (se 1 (by rfl) ⟨1017614, by rfl⟩ : syracuseStep 1356819 = 2035229) B2035229
theorem B1356835 : Blo 1354996 1356835 := bstep (se 1 (by rfl) ⟨1017626, by rfl⟩ : syracuseStep 1356835 = 2035253) B2035253
theorem B1831987 : Blo 1354996 1831987 := bstep (se 1 (by rfl) ⟨1373990, by rfl⟩ : syracuseStep 1831987 = 2747981) B2747981
theorem B1356851 : Blo 1354996 1356851 := bstep (se 1 (by rfl) ⟨1017638, by rfl⟩ : syracuseStep 1356851 = 2035277) B2035277
theorem B1356867 : Blo 1354996 1356867 := bstep (se 1 (by rfl) ⟨1017650, by rfl⟩ : syracuseStep 1356867 = 2035301) B2035301
theorem B4576337 : Blo 1354996 4576337 := bstep (se 2 (by rfl) ⟨1716126, by rfl⟩ : syracuseStep 4576337 = 3432253) B3432253
theorem B1356883 : Blo 1354996 1356883 := bstep (se 1 (by rfl) ⟨1017662, by rfl⟩ : syracuseStep 1356883 = 2035325) B2035325
theorem B1356899 : Blo 1354996 1356899 := bstep (se 1 (by rfl) ⟨1017674, by rfl⟩ : syracuseStep 1356899 = 2035349) B2035349
theorem B2749553 : Blo 1354996 2749553 := bstep (se 2 (by rfl) ⟨1031082, by rfl⟩ : syracuseStep 2749553 = 2062165) B2062165
theorem B1356915 : Blo 1354996 1356915 := bstep (se 1 (by rfl) ⟨1017686, by rfl⟩ : syracuseStep 1356915 = 2035373) B2035373
theorem B1356931 : Blo 1354996 1356931 := bstep (se 1 (by rfl) ⟨1017698, by rfl⟩ : syracuseStep 1356931 = 2035397) B2035397
theorem B2749585 : Blo 1354996 2749585 := bstep (se 2 (by rfl) ⟨1031094, by rfl⟩ : syracuseStep 2749585 = 2062189) B2062189
theorem B2897041 : Blo 1354996 2897041 := bstep (se 2 (by rfl) ⟨1086390, by rfl⟩ : syracuseStep 2897041 = 2172781) B2172781
theorem B1930387 : Blo 1354996 1930387 := bstep (se 1 (by rfl) ⟨1447790, by rfl⟩ : syracuseStep 1930387 = 2895581) B2895581
theorem B1356947 : Blo 1354996 1356947 := bstep (se 1 (by rfl) ⟨1017710, by rfl⟩ : syracuseStep 1356947 = 2035421) B2035421
theorem B1356963 : Blo 1354996 1356963 := bstep (se 1 (by rfl) ⟨1017722, by rfl⟩ : syracuseStep 1356963 = 2035445) B2035445
theorem B7722161 : Blo 1354996 7722161 := bstep (se 2 (by rfl) ⟨2895810, by rfl⟩ : syracuseStep 7722161 = 5791621) B5791621
theorem B1356979 : Blo 1354996 1356979 := bstep (se 1 (by rfl) ⟨1017734, by rfl⟩ : syracuseStep 1356979 = 2035469) B2035469
theorem B1356995 : Blo 1354996 1356995 := bstep (se 1 (by rfl) ⟨1017746, by rfl⟩ : syracuseStep 1356995 = 2035493) B2035493
theorem B4642033 : Blo 1354996 4642033 := bstep (se 2 (by rfl) ⟨1740762, by rfl⟩ : syracuseStep 4642033 = 3481525) B3481525
theorem B1930483 : Blo 1354996 1930483 := bstep (se 1 (by rfl) ⟨1447862, by rfl⟩ : syracuseStep 1930483 = 2895725) B2895725
theorem B3052817 : Blo 1354996 3052817 := bstep (se 2 (by rfl) ⟨1144806, by rfl⟩ : syracuseStep 3052817 = 2289613) B2289613
theorem B3052835 : Blo 1354996 3052835 := bstep (se 1 (by rfl) ⟨2289626, by rfl⟩ : syracuseStep 3052835 = 4579253) B4579253
theorem B6862157 : Blo 1354996 6862157 := bstep (se 3 (by rfl) ⟨1286654, by rfl⟩ : syracuseStep 6862157 = 2573309) B2573309
theorem B5150051 : Blo 1354996 5150051 := bstep (se 1 (by rfl) ⟨3862538, by rfl⟩ : syracuseStep 5150051 = 7725077) B7725077
theorem B2897297 : Blo 1354996 2897297 := bstep (se 2 (by rfl) ⟨1086486, by rfl⟩ : syracuseStep 2897297 = 2172973) B2172973
theorem B1447427 : Blo 1354996 1447427 := bstep (se 1 (by rfl) ⟨1085570, by rfl⟩ : syracuseStep 1447427 = 2171141) B2171141
theorem B3094033 : Blo 1354996 3094033 := bstep (se 2 (by rfl) ⟨1160262, by rfl⟩ : syracuseStep 3094033 = 2320525) B2320525
theorem B3053105 : Blo 1354996 3053105 := bstep (se 2 (by rfl) ⟨1144914, by rfl⟩ : syracuseStep 3053105 = 2289829) B2289829
theorem B3053123 : Blo 1354996 3053123 := bstep (se 1 (by rfl) ⟨2289842, by rfl⟩ : syracuseStep 3053123 = 4579685) B4579685
theorem B3864145 : Blo 1354996 3864145 := bstep (se 2 (by rfl) ⟨1449054, by rfl⟩ : syracuseStep 3864145 = 2898109) B2898109
theorem B4576877 : Blo 1354996 4576877 := bstep (se 3 (by rfl) ⟨858164, by rfl⟩ : syracuseStep 4576877 = 1716329) B1716329
theorem B1447555 : Blo 1354996 1447555 := bstep (se 1 (by rfl) ⟨1085666, by rfl⟩ : syracuseStep 1447555 = 2171333) B2171333
theorem B4576931 : Blo 1354996 4576931 := bstep (se 1 (by rfl) ⟨3432698, by rfl⟩ : syracuseStep 4576931 = 6865397) B6865397
theorem B5953229 : Blo 1354996 5953229 := bstep (se 3 (by rfl) ⟨1116230, by rfl⟩ : syracuseStep 5953229 = 2232461) B2232461
theorem B3430097 : Blo 1354996 3430097 := bstep (se 2 (by rfl) ⟨1286286, by rfl⟩ : syracuseStep 3430097 = 2572573) B2572573
theorem B1930979 : Blo 1354996 1930979 := bstep (se 1 (by rfl) ⟨1448234, by rfl⟩ : syracuseStep 1930979 = 2896469) B2896469
theorem B1832689 : Blo 1354996 1832689 := bstep (se 2 (by rfl) ⟨687258, by rfl⟩ : syracuseStep 1832689 = 1374517) B1374517
theorem B3430147 : Blo 1354996 3430147 := bstep (se 1 (by rfl) ⟨2572610, by rfl⟩ : syracuseStep 3430147 = 5145221) B5145221
theorem B13039373 : Blo 1354996 13039373 := bstep (se 3 (by rfl) ⟨2444882, by rfl⟩ : syracuseStep 13039373 = 4889765) B4889765
theorem B18552689 : Blo 1354996 18552689 := bstep (se 2 (by rfl) ⟨6957258, by rfl⟩ : syracuseStep 18552689 = 13914517) B13914517
theorem B3667843 : Blo 1354996 3667843 := bstep (se 1 (by rfl) ⟨2750882, by rfl⟩ : syracuseStep 3667843 = 5501765) B5501765
theorem B3430289 : Blo 1354996 3430289 := bstep (se 2 (by rfl) ⟨1286358, by rfl⟩ : syracuseStep 3430289 = 2572717) B2572717
theorem B4577201 : Blo 1354996 4577201 := bstep (se 2 (by rfl) ⟨1716450, by rfl⟩ : syracuseStep 4577201 = 3432901) B3432901
theorem B3668017 : Blo 1354996 3668017 := bstep (se 2 (by rfl) ⟨1375506, by rfl⟩ : syracuseStep 3668017 = 2751013) B2751013
theorem B1833025 : Blo 1354996 1833025 := bstep (se 2 (by rfl) ⟨687384, by rfl⟩ : syracuseStep 1833025 = 1374769) B1374769
theorem B5789809 : Blo 1354996 5789809 := bstep (se 2 (by rfl) ⟨2171178, by rfl⟩ : syracuseStep 5789809 = 4342357) B4342357
theorem B8689841 : Blo 1354996 8689841 := bstep (se 2 (by rfl) ⟨3258690, by rfl⟩ : syracuseStep 8689841 = 6517381) B6517381
theorem B10303685 : Blo 1354996 10303685 := bstep (se 4 (by rfl) ⟨965970, by rfl⟩ : syracuseStep 10303685 = 1931941) B1931941
theorem B6699277 : Blo 1354996 6699277 := bstep (se 3 (by rfl) ⟨1256114, by rfl⟩ : syracuseStep 6699277 = 2512229) B2512229
theorem B8247587 : Blo 1354996 8247587 := bstep (se 1 (by rfl) ⟨6185690, by rfl⟩ : syracuseStep 8247587 = 12371381) B12371381
theorem B4405553 : Blo 1354996 4405553 := bstep (se 2 (by rfl) ⟨1652082, by rfl⟩ : syracuseStep 4405553 = 3304165) B3304165
theorem B5151053 : Blo 1354996 5151053 := bstep (se 3 (by rfl) ⟨965822, by rfl⟩ : syracuseStep 5151053 = 1931645) B1931645
theorem B1931617 : Blo 1354996 1931617 := bstep (se 2 (by rfl) ⟨724356, by rfl⟩ : syracuseStep 1931617 = 1448713) B1448713
theorem B2750851 : Blo 1354996 2750851 := bstep (se 1 (by rfl) ⟨2063138, by rfl⟩ : syracuseStep 2750851 = 4126277) B4126277
theorem B1448371 : Blo 1354996 1448371 := bstep (se 1 (by rfl) ⟨1086278, by rfl⟩ : syracuseStep 1448371 = 2172557) B2172557
theorem B4577741 : Blo 1354996 4577741 := bstep (se 3 (by rfl) ⟨858326, by rfl⟩ : syracuseStep 4577741 = 1716653) B1716653
theorem B1956337 : Blo 1354996 1956337 := bstep (se 2 (by rfl) ⟨733626, by rfl⟩ : syracuseStep 1956337 = 1467253) B1467253
theorem B3258883 : Blo 1354996 3258883 := bstep (se 1 (by rfl) ⟨2444162, by rfl⟩ : syracuseStep 3258883 = 4888325) B4888325
theorem B4577795 : Blo 1354996 4577795 := bstep (se 1 (by rfl) ⟨3433346, by rfl⟩ : syracuseStep 4577795 = 6866693) B6866693
theorem B7723619 : Blo 1354996 7723619 := bstep (se 1 (by rfl) ⟨5792714, by rfl⟩ : syracuseStep 7723619 = 11585429) B11585429
theorem B2063011 : Blo 1354996 2063011 := bstep (se 1 (by rfl) ⟨1547258, by rfl⟩ : syracuseStep 2063011 = 3094517) B3094517
theorem B1931953 : Blo 1354996 1931953 := bstep (se 2 (by rfl) ⟨724482, by rfl⟩ : syracuseStep 1931953 = 1448965) B1448965
theorem B26049221 : Blo 1354996 26049221 := bstep (se 4 (by rfl) ⟨2442114, by rfl⟩ : syracuseStep 26049221 = 4884229) B4884229
theorem B4578065 : Blo 1354996 4578065 := bstep (se 2 (by rfl) ⟨1716774, by rfl⟩ : syracuseStep 4578065 = 3433549) B3433549
theorem B3431281 : Blo 1354996 3431281 := bstep (se 2 (by rfl) ⟨1286730, by rfl⟩ : syracuseStep 3431281 = 2573461) B2573461
theorem B1956835 : Blo 1354996 1956835 := bstep (se 1 (by rfl) ⟨1467626, by rfl⟩ : syracuseStep 1956835 = 2935253) B2935253
theorem B43981937 : Blo 1354996 43981937 := bstep (se 2 (by rfl) ⟨16493226, by rfl⟩ : syracuseStep 43981937 = 32986453) B32986453
theorem B3431555 : Blo 1354996 3431555 := bstep (se 1 (by rfl) ⟨2573666, by rfl⟩ : syracuseStep 3431555 = 5147333) B5147333
theorem B14670989 : Blo 1354996 14670989 := bstep (se 3 (by rfl) ⟨2750810, by rfl⟩ : syracuseStep 14670989 = 5501621) B5501621
theorem B3767501 : Blo 1354996 3767501 := bstep (se 3 (by rfl) ⟨706406, by rfl⟩ : syracuseStep 3767501 = 1412813) B1412813
theorem B4578605 : Blo 1354996 4578605 := bstep (se 3 (by rfl) ⟨858488, by rfl⟩ : syracuseStep 4578605 = 1716977) B1716977
theorem B3431747 : Blo 1354996 3431747 := bstep (se 1 (by rfl) ⟨2573810, by rfl⟩ : syracuseStep 3431747 = 5147621) B5147621
theorem B4578659 : Blo 1354996 4578659 := bstep (se 1 (by rfl) ⟨3433994, by rfl⟩ : syracuseStep 4578659 = 6867989) B6867989
theorem B1957331 : Blo 1354996 1957331 := bstep (se 1 (by rfl) ⟨1467998, by rfl⟩ : syracuseStep 1957331 = 2935997) B2935997
theorem B1883633 : Blo 1354996 1883633 := bstep (se 2 (by rfl) ⟨706362, by rfl⟩ : syracuseStep 1883633 = 1412725) B1412725
theorem B3259921 : Blo 1354996 3259921 := bstep (se 2 (by rfl) ⟨1222470, by rfl⟩ : syracuseStep 3259921 = 2444941) B2444941
theorem B4578929 : Blo 1354996 4578929 := bstep (se 2 (by rfl) ⟨1717098, by rfl⟩ : syracuseStep 4578929 = 3434197) B3434197
theorem B2170577 : Blo 1354996 2170577 := bstep (se 2 (by rfl) ⟨813966, by rfl⟩ : syracuseStep 2170577 = 1627933) B1627933
theorem B1957603 : Blo 1354996 1957603 := bstep (se 1 (by rfl) ⟨1468202, by rfl⟩ : syracuseStep 1957603 = 2936405) B2936405
theorem B15441677 : Blo 1354996 15441677 := bstep (se 3 (by rfl) ⟨2895314, by rfl⟩ : syracuseStep 15441677 = 5790629) B5790629
theorem B8691533 : Blo 1354996 8691533 := bstep (se 3 (by rfl) ⟨1629662, by rfl⟩ : syracuseStep 8691533 = 3259325) B3259325
theorem B24723427 : Blo 1354996 24723427 := bstep (se 1 (by rfl) ⟨18542570, by rfl⟩ : syracuseStep 24723427 = 37085141) B37085141
theorem B5496835 : Blo 1354996 5496835 := bstep (se 1 (by rfl) ⟨4122626, by rfl⟩ : syracuseStep 5496835 = 8245253) B8245253
theorem B4890689 : Blo 1354996 4890689 := bstep (se 2 (by rfl) ⟨1834008, by rfl⟩ : syracuseStep 4890689 = 3668017) B3668017
theorem B5791895 : Blo 1354996 5791895 := bstep (se 1 (by rfl) ⟨4343921, by rfl⟩ : syracuseStep 5791895 = 8687843) B8687843
theorem B10584269 : Blo 1354996 10584269 := bstep (se 3 (by rfl) ⟨1984550, by rfl⟩ : syracuseStep 10584269 = 3969101) B3969101
theorem B8683793 : Blo 1354996 8683793 := bstep (se 2 (by rfl) ⟨3256422, by rfl⟩ : syracuseStep 8683793 = 6512845) B6512845
theorem B2572823 : Blo 1354996 2572823 := bstep (se 1 (by rfl) ⟨1929617, by rfl⟩ : syracuseStep 2572823 = 3859235) B3859235
theorem B6865559 : Blo 1354996 6865559 := bstep (se 1 (by rfl) ⟨5149169, by rfl⟩ : syracuseStep 6865559 = 10298339) B10298339
theorem B1524523 : Blo 1354996 1524523 := bstep (se 1 (by rfl) ⟨1143392, by rfl⟩ : syracuseStep 1524523 = 2286785) B2286785
theorem B5145389 : Blo 1354996 5145389 := bstep (se 3 (by rfl) ⟨964760, by rfl⟩ : syracuseStep 5145389 = 1929521) B1929521
theorem B65946433 : Blo 1354996 65946433 := bstep (se 2 (by rfl) ⟨24729912, by rfl⟩ : syracuseStep 65946433 = 49459825) B49459825
theorem B2032523 : Blo 1354996 2032523 := bstep (se 1 (by rfl) ⟨1524392, by rfl⟩ : syracuseStep 2032523 = 3048785) B3048785
theorem B2032535 : Blo 1354996 2032535 := bstep (se 1 (by rfl) ⟨1524401, by rfl⟩ : syracuseStep 2032535 = 3048803) B3048803
theorem B1524631 : Blo 1354996 1524631 := bstep (se 1 (by rfl) ⟨1143473, by rfl⟩ : syracuseStep 1524631 = 2286947) B2286947
theorem B3433367 : Blo 1354996 3433367 := bstep (se 1 (by rfl) ⟨2575025, by rfl⟩ : syracuseStep 3433367 = 5150051) B5150051
theorem B2032601 : Blo 1354996 2032601 := bstep (se 2 (by rfl) ⟨762225, by rfl⟩ : syracuseStep 2032601 = 1524451) B1524451
theorem B3859417 : Blo 1354996 3859417 := bstep (se 2 (by rfl) ⟨1447281, by rfl⟩ : syracuseStep 3859417 = 2894563) B2894563
theorem B2573363 : Blo 1354996 2573363 := bstep (se 1 (by rfl) ⟨1930022, by rfl⟩ : syracuseStep 2573363 = 3860045) B3860045
theorem B2032715 : Blo 1354996 2032715 := bstep (se 1 (by rfl) ⟨1524536, by rfl⟩ : syracuseStep 2032715 = 3049073) B3049073
theorem B1524811 : Blo 1354996 1524811 := bstep (se 1 (by rfl) ⟨1143608, by rfl⟩ : syracuseStep 1524811 = 2287217) B2287217
theorem B4342859 : Blo 1354996 4342859 := bstep (se 1 (by rfl) ⟨3257144, by rfl⟩ : syracuseStep 4342859 = 6514289) B6514289
theorem B2032727 : Blo 1354996 2032727 := bstep (se 1 (by rfl) ⟨1524545, by rfl⟩ : syracuseStep 2032727 = 3049091) B3049091
theorem B2286731 : Blo 1354996 2286731 := bstep (se 1 (by rfl) ⟨1715048, by rfl⟩ : syracuseStep 2286731 = 3430097) B3430097
theorem B2032793 : Blo 1354996 2032793 := bstep (se 2 (by rfl) ⟨762297, by rfl⟩ : syracuseStep 2032793 = 1524595) B1524595
theorem B8692915 : Blo 1354996 8692915 := bstep (se 1 (by rfl) ⟨6519686, by rfl⟩ : syracuseStep 8692915 = 13039373) B13039373
theorem B100345013 : Blo 1354996 100345013 := bstep (se 5 (by rfl) ⟨4703672, by rfl⟩ : syracuseStep 100345013 = 9407345) B9407345
theorem B1524919 : Blo 1354996 1524919 := bstep (se 1 (by rfl) ⟨1143689, by rfl⟩ : syracuseStep 1524919 = 2287379) B2287379
theorem B2442433 : Blo 1354996 2442433 := bstep (se 2 (by rfl) ⟨915912, by rfl⟩ : syracuseStep 2442433 = 1831825) B1831825
theorem B7718105 : Blo 1354996 7718105 := bstep (se 2 (by rfl) ⟨2894289, by rfl⟩ : syracuseStep 7718105 = 5788579) B5788579
theorem B5219549 : Blo 1354996 5219549 := bstep (se 3 (by rfl) ⟨978665, by rfl⟩ : syracuseStep 5219549 = 1957331) B1957331
theorem B9774341 : Blo 1354996 9774341 := bstep (se 4 (by rfl) ⟨916344, by rfl⟩ : syracuseStep 9774341 = 1832689) B1832689
theorem B2286859 : Blo 1354996 2286859 := bstep (se 1 (by rfl) ⟨1715144, by rfl⟩ : syracuseStep 2286859 = 3430289) B3430289
theorem B2032907 : Blo 1354996 2032907 := bstep (se 1 (by rfl) ⟨1524680, by rfl⟩ : syracuseStep 2032907 = 3049361) B3049361
theorem B2032919 : Blo 1354996 2032919 := bstep (se 1 (by rfl) ⟨1524689, by rfl⟩ : syracuseStep 2032919 = 3049379) B3049379
theorem B2032985 : Blo 1354996 2032985 := bstep (se 2 (by rfl) ⟨762369, by rfl⟩ : syracuseStep 2032985 = 1524739) B1524739
theorem B3859805 : Blo 1354996 3859805 := bstep (se 3 (by rfl) ⟨723713, by rfl⟩ : syracuseStep 3859805 = 1447427) B1447427
theorem B1525099 : Blo 1354996 1525099 := bstep (se 1 (by rfl) ⟨1143824, by rfl⟩ : syracuseStep 1525099 = 2287649) B2287649
theorem B10290563 : Blo 1354996 10290563 := bstep (se 1 (by rfl) ⟨7717922, by rfl⟩ : syracuseStep 10290563 = 15435845) B15435845
theorem B3048857 : Blo 1354996 3048857 := bstep (se 2 (by rfl) ⟨1143321, by rfl⟩ : syracuseStep 3048857 = 2286643) B2286643
theorem B2287001 : Blo 1354996 2287001 := bstep (se 2 (by rfl) ⟨857625, by rfl⟩ : syracuseStep 2287001 = 1715251) B1715251
theorem B2442649 : Blo 1354996 2442649 := bstep (se 2 (by rfl) ⟨915993, by rfl⟩ : syracuseStep 2442649 = 1831987) B1831987
theorem B2033099 : Blo 1354996 2033099 := bstep (se 1 (by rfl) ⟨1524824, by rfl⟩ : syracuseStep 2033099 = 3049649) B3049649
theorem B5793227 : Blo 1354996 5793227 := bstep (se 1 (by rfl) ⟨4344920, by rfl⟩ : syracuseStep 5793227 = 8689841) B8689841
theorem B2033111 : Blo 1354996 2033111 := bstep (se 1 (by rfl) ⟨1524833, by rfl⟩ : syracuseStep 2033111 = 3049667) B3049667
theorem B1525207 : Blo 1354996 1525207 := bstep (se 1 (by rfl) ⟨1143905, by rfl⟩ : syracuseStep 1525207 = 2287811) B2287811
theorem B3048947 : Blo 1354996 3048947 := bstep (se 1 (by rfl) ⟨2286710, by rfl⟩ : syracuseStep 3048947 = 4573421) B4573421
theorem B3048983 : Blo 1354996 3048983 := bstep (se 1 (by rfl) ⟨2286737, by rfl⟩ : syracuseStep 3048983 = 4573475) B4573475
theorem B2287129 : Blo 1354996 2287129 := bstep (se 2 (by rfl) ⟨857673, by rfl⟩ : syracuseStep 2287129 = 1715347) B1715347
theorem B2033177 : Blo 1354996 2033177 := bstep (se 2 (by rfl) ⟨762441, by rfl⟩ : syracuseStep 2033177 = 1524883) B1524883
theorem B2573849 : Blo 1354996 2573849 := bstep (se 2 (by rfl) ⟨965193, by rfl⟩ : syracuseStep 2573849 = 1930387) B1930387
theorem B5146163 : Blo 1354996 5146163 := bstep (se 1 (by rfl) ⟨3859622, by rfl⟩ : syracuseStep 5146163 = 7719245) B7719245
theorem B3434035 : Blo 1354996 3434035 := bstep (se 1 (by rfl) ⟨2575526, by rfl⟩ : syracuseStep 3434035 = 5151053) B5151053
theorem B2033291 : Blo 1354996 2033291 := bstep (se 1 (by rfl) ⟨1524968, by rfl⟩ : syracuseStep 2033291 = 3049937) B3049937
theorem B1525387 : Blo 1354996 1525387 := bstep (se 1 (by rfl) ⟨1144040, by rfl⟩ : syracuseStep 1525387 = 2288081) B2288081
theorem B2033303 : Blo 1354996 2033303 := bstep (se 1 (by rfl) ⟨1524977, by rfl⟩ : syracuseStep 2033303 = 3049955) B3049955
theorem B3434177 : Blo 1354996 3434177 := bstep (se 2 (by rfl) ⟨1287816, by rfl⟩ : syracuseStep 3434177 = 2575633) B2575633
theorem B3049163 : Blo 1354996 3049163 := bstep (se 1 (by rfl) ⟨2286872, by rfl⟩ : syracuseStep 3049163 = 4573745) B4573745
theorem B2033369 : Blo 1354996 2033369 := bstep (se 2 (by rfl) ⟨762513, by rfl⟩ : syracuseStep 2033369 = 1525027) B1525027
theorem B1525495 : Blo 1354996 1525495 := bstep (se 1 (by rfl) ⟨1144121, by rfl⟩ : syracuseStep 1525495 = 2288243) B2288243
theorem B3049217 : Blo 1354996 3049217 := bstep (se 2 (by rfl) ⟨1143456, by rfl⟩ : syracuseStep 3049217 = 2286913) B2286913
theorem B2033483 : Blo 1354996 2033483 := bstep (se 1 (by rfl) ⟨1525112, by rfl⟩ : syracuseStep 2033483 = 3050225) B3050225
theorem B2033495 : Blo 1354996 2033495 := bstep (se 1 (by rfl) ⟨1525121, by rfl⟩ : syracuseStep 2033495 = 3050243) B3050243
theorem B4638557 : Blo 1354996 4638557 := bstep (se 3 (by rfl) ⟨869729, by rfl⟩ : syracuseStep 4638557 = 1739459) B1739459
theorem B2033561 : Blo 1354996 2033561 := bstep (se 2 (by rfl) ⟨762585, by rfl⟩ : syracuseStep 2033561 = 1525171) B1525171
theorem B1525675 : Blo 1354996 1525675 := bstep (se 1 (by rfl) ⟨1144256, by rfl⟩ : syracuseStep 1525675 = 2288513) B2288513
theorem B4884403 : Blo 1354996 4884403 := bstep (se 1 (by rfl) ⟨3663302, by rfl⟩ : syracuseStep 4884403 = 7326605) B7326605
theorem B2443211 : Blo 1354996 2443211 := bstep (se 1 (by rfl) ⟨1832408, by rfl⟩ : syracuseStep 2443211 = 3664817) B3664817
theorem B3049433 : Blo 1354996 3049433 := bstep (se 2 (by rfl) ⟨1143537, by rfl⟩ : syracuseStep 3049433 = 2287075) B2287075
theorem B2033675 : Blo 1354996 2033675 := bstep (se 1 (by rfl) ⟨1525256, by rfl⟩ : syracuseStep 2033675 = 3050513) B3050513
theorem B2033687 : Blo 1354996 2033687 := bstep (se 1 (by rfl) ⟨1525265, by rfl⟩ : syracuseStep 2033687 = 3050531) B3050531
theorem B1525783 : Blo 1354996 1525783 := bstep (se 1 (by rfl) ⟨1144337, by rfl⟩ : syracuseStep 1525783 = 2288675) B2288675
theorem B3049523 : Blo 1354996 3049523 := bstep (se 1 (by rfl) ⟨2287142, by rfl⟩ : syracuseStep 3049523 = 4574285) B4574285
theorem B4573259 : Blo 1354996 4573259 := bstep (se 1 (by rfl) ⟨3429944, by rfl⟩ : syracuseStep 4573259 = 6859889) B6859889
theorem B29321291 : Blo 1354996 29321291 := bstep (se 1 (by rfl) ⟨21990968, by rfl⟩ : syracuseStep 29321291 = 43981937) B43981937
theorem B3049559 : Blo 1354996 3049559 := bstep (se 1 (by rfl) ⟨2287169, by rfl⟩ : syracuseStep 3049559 = 4574339) B4574339
theorem B2287703 : Blo 1354996 2287703 := bstep (se 1 (by rfl) ⟨1715777, by rfl⟩ : syracuseStep 2287703 = 3431555) B3431555
theorem B2033753 : Blo 1354996 2033753 := bstep (se 2 (by rfl) ⟨762657, by rfl⟩ : syracuseStep 2033753 = 1525315) B1525315
theorem B2033867 : Blo 1354996 2033867 := bstep (se 1 (by rfl) ⟨1525400, by rfl⟩ : syracuseStep 2033867 = 3050801) B3050801
theorem B1525963 : Blo 1354996 1525963 := bstep (se 1 (by rfl) ⟨1144472, by rfl⟩ : syracuseStep 1525963 = 2288945) B2288945
theorem B2287831 : Blo 1354996 2287831 := bstep (se 1 (by rfl) ⟨1715873, by rfl⟩ : syracuseStep 2287831 = 3431747) B3431747
theorem B2033879 : Blo 1354996 2033879 := bstep (se 1 (by rfl) ⟨1525409, by rfl⟩ : syracuseStep 2033879 = 3050819) B3050819
theorem B3049739 : Blo 1354996 3049739 := bstep (se 1 (by rfl) ⟨2287304, by rfl⟩ : syracuseStep 3049739 = 4574609) B4574609
theorem B2033945 : Blo 1354996 2033945 := bstep (se 2 (by rfl) ⟨762729, by rfl⟩ : syracuseStep 2033945 = 1525459) B1525459
theorem B1526071 : Blo 1354996 1526071 := bstep (se 1 (by rfl) ⟨1144553, by rfl⟩ : syracuseStep 1526071 = 2289107) B2289107
theorem B3049793 : Blo 1354996 3049793 := bstep (se 2 (by rfl) ⟨1143672, by rfl⟩ : syracuseStep 3049793 = 2287345) B2287345
theorem B4573529 : Blo 1354996 4573529 := bstep (se 2 (by rfl) ⟨1715073, by rfl⟩ : syracuseStep 4573529 = 3430147) B3430147
theorem B2034059 : Blo 1354996 2034059 := bstep (se 1 (by rfl) ⟨1525544, by rfl⟩ : syracuseStep 2034059 = 3051089) B3051089
theorem B2034071 : Blo 1354996 2034071 := bstep (se 1 (by rfl) ⟨1525553, by rfl⟩ : syracuseStep 2034071 = 3051107) B3051107
theorem B2034137 : Blo 1354996 2034137 := bstep (se 2 (by rfl) ⟨762801, by rfl⟩ : syracuseStep 2034137 = 1525603) B1525603
theorem B1526251 : Blo 1354996 1526251 := bstep (se 1 (by rfl) ⟨1144688, by rfl⟩ : syracuseStep 1526251 = 2289377) B2289377
theorem B3050009 : Blo 1354996 3050009 := bstep (se 2 (by rfl) ⟨1143753, by rfl⟩ : syracuseStep 3050009 = 2287507) B2287507
theorem B4885037 : Blo 1354996 4885037 := bstep (se 3 (by rfl) ⟨915944, by rfl⟩ : syracuseStep 4885037 = 1831889) B1831889
theorem B5794355 : Blo 1354996 5794355 := bstep (se 1 (by rfl) ⟨4345766, by rfl⟩ : syracuseStep 5794355 = 8691533) B8691533
theorem B2034251 : Blo 1354996 2034251 := bstep (se 1 (by rfl) ⟨1525688, by rfl⟩ : syracuseStep 2034251 = 3051377) B3051377
theorem B2034263 : Blo 1354996 2034263 := bstep (se 1 (by rfl) ⟨1525697, by rfl⟩ : syracuseStep 2034263 = 3051395) B3051395
theorem B1526359 : Blo 1354996 1526359 := bstep (se 1 (by rfl) ⟨1144769, by rfl⟩ : syracuseStep 1526359 = 2289539) B2289539
theorem B3050099 : Blo 1354996 3050099 := bstep (se 1 (by rfl) ⟨2287574, by rfl⟩ : syracuseStep 3050099 = 4575149) B4575149
theorem B11586179 : Blo 1354996 11586179 := bstep (se 1 (by rfl) ⟨8689634, by rfl⟩ : syracuseStep 11586179 = 17379269) B17379269
theorem B3050135 : Blo 1354996 3050135 := bstep (se 1 (by rfl) ⟨2287601, by rfl⟩ : syracuseStep 3050135 = 4575203) B4575203
theorem B2034329 : Blo 1354996 2034329 := bstep (se 2 (by rfl) ⟨762873, by rfl⟩ : syracuseStep 2034329 = 1525747) B1525747
theorem B2444033 : Blo 1354996 2444033 := bstep (se 2 (by rfl) ⟨916512, by rfl⟩ : syracuseStep 2444033 = 1833025) B1833025
theorem B2034443 : Blo 1354996 2034443 := bstep (se 1 (by rfl) ⟨1525832, by rfl⟩ : syracuseStep 2034443 = 3051665) B3051665
theorem B1526539 : Blo 1354996 1526539 := bstep (se 1 (by rfl) ⟨1144904, by rfl⟩ : syracuseStep 1526539 = 2289809) B2289809
theorem B2034455 : Blo 1354996 2034455 := bstep (se 1 (by rfl) ⟨1525841, by rfl⟩ : syracuseStep 2034455 = 3051683) B3051683
theorem B2747201 : Blo 1354996 2747201 := bstep (se 2 (by rfl) ⟨1030200, by rfl⟩ : syracuseStep 2747201 = 2060401) B2060401
theorem B7719745 : Blo 1354996 7719745 := bstep (se 2 (by rfl) ⟨2894904, by rfl⟩ : syracuseStep 7719745 = 5789809) B5789809
theorem B4123457 : Blo 1354996 4123457 := bstep (se 2 (by rfl) ⟨1546296, by rfl⟩ : syracuseStep 4123457 = 3092593) B3092593
theorem B3050315 : Blo 1354996 3050315 := bstep (se 1 (by rfl) ⟨2287736, by rfl⟩ : syracuseStep 3050315 = 4575473) B4575473
theorem B2288459 : Blo 1354996 2288459 := bstep (se 1 (by rfl) ⟨1716344, by rfl⟩ : syracuseStep 2288459 = 3432689) B3432689
theorem B2034521 : Blo 1354996 2034521 := bstep (se 2 (by rfl) ⟨762945, by rfl⟩ : syracuseStep 2034521 = 1525891) B1525891
theorem B3050369 : Blo 1354996 3050369 := bstep (se 2 (by rfl) ⟨1143888, by rfl⟩ : syracuseStep 3050369 = 2287777) B2287777
theorem B2288587 : Blo 1354996 2288587 := bstep (se 1 (by rfl) ⟨1716440, by rfl⟩ : syracuseStep 2288587 = 3432881) B3432881
theorem B2034635 : Blo 1354996 2034635 := bstep (se 1 (by rfl) ⟨1525976, by rfl⟩ : syracuseStep 2034635 = 3051953) B3051953
theorem B2575307 : Blo 1354996 2575307 := bstep (se 1 (by rfl) ⟨1931480, by rfl⟩ : syracuseStep 2575307 = 3862961) B3862961
theorem B2034647 : Blo 1354996 2034647 := bstep (se 1 (by rfl) ⟨1525985, by rfl⟩ : syracuseStep 2034647 = 3051971) B3051971
theorem B5147651 : Blo 1354996 5147651 := bstep (se 1 (by rfl) ⟨3860738, by rfl⟩ : syracuseStep 5147651 = 7721477) B7721477
theorem B8932369 : Blo 1354996 8932369 := bstep (se 2 (by rfl) ⟨3349638, by rfl⟩ : syracuseStep 8932369 = 6699277) B6699277
theorem B4574231 : Blo 1354996 4574231 := bstep (se 1 (by rfl) ⟨3430673, by rfl⟩ : syracuseStep 4574231 = 6861347) B6861347
theorem B2034713 : Blo 1354996 2034713 := bstep (se 2 (by rfl) ⟨763017, by rfl⟩ : syracuseStep 2034713 = 1526035) B1526035
theorem B3050585 : Blo 1354996 3050585 := bstep (se 2 (by rfl) ⟨1143969, by rfl⟩ : syracuseStep 3050585 = 2287939) B2287939
theorem B2288729 : Blo 1354996 2288729 := bstep (se 2 (by rfl) ⟨858273, by rfl⟩ : syracuseStep 2288729 = 1716547) B1716547
theorem B2575489 : Blo 1354996 2575489 := bstep (se 2 (by rfl) ⟨965808, by rfl⟩ : syracuseStep 2575489 = 1931617) B1931617
theorem B2034827 : Blo 1354996 2034827 := bstep (se 1 (by rfl) ⟨1526120, by rfl⟩ : syracuseStep 2034827 = 3052241) B3052241
theorem B2034839 : Blo 1354996 2034839 := bstep (se 1 (by rfl) ⟨1526129, by rfl⟩ : syracuseStep 2034839 = 3052259) B3052259
theorem B3050675 : Blo 1354996 3050675 := bstep (se 1 (by rfl) ⟨2288006, by rfl⟩ : syracuseStep 3050675 = 4576013) B4576013
theorem B3050711 : Blo 1354996 3050711 := bstep (se 1 (by rfl) ⟨2288033, by rfl⟩ : syracuseStep 3050711 = 4576067) B4576067
theorem B2288857 : Blo 1354996 2288857 := bstep (se 2 (by rfl) ⟨858321, by rfl⟩ : syracuseStep 2288857 = 1716643) B1716643
theorem B2034905 : Blo 1354996 2034905 := bstep (se 2 (by rfl) ⟨763089, by rfl⟩ : syracuseStep 2034905 = 1526179) B1526179
theorem B1354999 : Blo 1354996 1354999 := bstep (se 1 (by rfl) ⟨1016249, by rfl⟩ : syracuseStep 1354999 = 2032499) B2032499
theorem B1355019 : Blo 1354996 1355019 := bstep (se 1 (by rfl) ⟨1016264, by rfl⟩ : syracuseStep 1355019 = 2032529) B2032529
theorem B1355031 : Blo 1354996 1355031 := bstep (se 1 (by rfl) ⟨1016273, by rfl⟩ : syracuseStep 1355031 = 2032547) B2032547
theorem B1355051 : Blo 1354996 1355051 := bstep (se 1 (by rfl) ⟨1016288, by rfl⟩ : syracuseStep 1355051 = 2032577) B2032577
theorem B1355063 : Blo 1354996 1355063 := bstep (se 1 (by rfl) ⟨1016297, by rfl⟩ : syracuseStep 1355063 = 2032595) B2032595
theorem B1355083 : Blo 1354996 1355083 := bstep (se 1 (by rfl) ⟨1016312, by rfl⟩ : syracuseStep 1355083 = 2032625) B2032625
theorem B5868875 : Blo 1354996 5868875 := bstep (se 1 (by rfl) ⟨4401656, by rfl⟩ : syracuseStep 5868875 = 8803313) B8803313
theorem B2035019 : Blo 1354996 2035019 := bstep (se 1 (by rfl) ⟨1526264, by rfl⟩ : syracuseStep 2035019 = 3052529) B3052529
theorem B1355095 : Blo 1354996 1355095 := bstep (se 1 (by rfl) ⟨1016321, by rfl⟩ : syracuseStep 1355095 = 2032643) B2032643
theorem B2035031 : Blo 1354996 2035031 := bstep (se 1 (by rfl) ⟨1526273, by rfl⟩ : syracuseStep 2035031 = 3052547) B3052547
theorem B4345177 : Blo 1354996 4345177 := bstep (se 2 (by rfl) ⟨1629441, by rfl⟩ : syracuseStep 4345177 = 3258883) B3258883
theorem B1355115 : Blo 1354996 1355115 := bstep (se 1 (by rfl) ⟨1016336, by rfl⟩ : syracuseStep 1355115 = 2032673) B2032673
theorem B1355127 : Blo 1354996 1355127 := bstep (se 1 (by rfl) ⟨1016345, by rfl⟩ : syracuseStep 1355127 = 2032691) B2032691
theorem B1355147 : Blo 1354996 1355147 := bstep (se 1 (by rfl) ⟨1016360, by rfl⟩ : syracuseStep 1355147 = 2032721) B2032721
theorem B3050891 : Blo 1354996 3050891 := bstep (se 1 (by rfl) ⟨2288168, by rfl⟩ : syracuseStep 3050891 = 4576337) B4576337
theorem B1355159 : Blo 1354996 1355159 := bstep (se 1 (by rfl) ⟨1016369, by rfl⟩ : syracuseStep 1355159 = 2032739) B2032739
theorem B2035097 : Blo 1354996 2035097 := bstep (se 2 (by rfl) ⟨763161, by rfl⟩ : syracuseStep 2035097 = 1526323) B1526323
theorem B1355179 : Blo 1354996 1355179 := bstep (se 1 (by rfl) ⟨1016384, by rfl⟩ : syracuseStep 1355179 = 2032769) B2032769
theorem B1355191 : Blo 1354996 1355191 := bstep (se 1 (by rfl) ⟨1016393, by rfl⟩ : syracuseStep 1355191 = 2032787) B2032787
theorem B3050945 : Blo 1354996 3050945 := bstep (se 2 (by rfl) ⟨1144104, by rfl⟩ : syracuseStep 3050945 = 2288209) B2288209
theorem B1355211 : Blo 1354996 1355211 := bstep (se 1 (by rfl) ⟨1016408, by rfl⟩ : syracuseStep 1355211 = 2032817) B2032817
theorem B5148107 : Blo 1354996 5148107 := bstep (se 1 (by rfl) ⟨3861080, by rfl⟩ : syracuseStep 5148107 = 7722161) B7722161
theorem B10431949 : Blo 1354996 10431949 := bstep (se 3 (by rfl) ⟨1955990, by rfl⟩ : syracuseStep 10431949 = 3911981) B3911981
theorem B1355223 : Blo 1354996 1355223 := bstep (se 1 (by rfl) ⟨1016417, by rfl⟩ : syracuseStep 1355223 = 2032835) B2032835
theorem B1715671 : Blo 1354996 1715671 := bstep (se 1 (by rfl) ⟨1286753, by rfl⟩ : syracuseStep 1715671 = 2573507) B2573507
theorem B1355243 : Blo 1354996 1355243 := bstep (se 1 (by rfl) ⟨1016432, by rfl⟩ : syracuseStep 1355243 = 2032865) B2032865
theorem B1355255 : Blo 1354996 1355255 := bstep (se 1 (by rfl) ⟨1016441, by rfl⟩ : syracuseStep 1355255 = 2032883) B2032883
theorem B1355275 : Blo 1354996 1355275 := bstep (se 1 (by rfl) ⟨1016456, by rfl⟩ : syracuseStep 1355275 = 2032913) B2032913
theorem B2035211 : Blo 1354996 2035211 := bstep (se 1 (by rfl) ⟨1526408, by rfl⟩ : syracuseStep 2035211 = 3052817) B3052817
theorem B1355287 : Blo 1354996 1355287 := bstep (se 1 (by rfl) ⟨1016465, by rfl⟩ : syracuseStep 1355287 = 2032931) B2032931
theorem B2895383 : Blo 1354996 2895383 := bstep (se 1 (by rfl) ⟨2171537, by rfl⟩ : syracuseStep 2895383 = 4343075) B4343075
theorem B2035223 : Blo 1354996 2035223 := bstep (se 1 (by rfl) ⟨1526417, by rfl⟩ : syracuseStep 2035223 = 3052835) B3052835
theorem B1355307 : Blo 1354996 1355307 := bstep (se 1 (by rfl) ⟨1016480, by rfl⟩ : syracuseStep 1355307 = 2032961) B2032961
theorem B4574771 : Blo 1354996 4574771 := bstep (se 1 (by rfl) ⟨3431078, by rfl⟩ : syracuseStep 4574771 = 6862157) B6862157
theorem B1355319 : Blo 1354996 1355319 := bstep (se 1 (by rfl) ⟨1016489, by rfl⟩ : syracuseStep 1355319 = 2032979) B2032979
theorem B2575937 : Blo 1354996 2575937 := bstep (se 2 (by rfl) ⟨965976, by rfl⟩ : syracuseStep 2575937 = 1931953) B1931953
theorem B1355339 : Blo 1354996 1355339 := bstep (se 1 (by rfl) ⟨1016504, by rfl⟩ : syracuseStep 1355339 = 2033009) B2033009
theorem B1355351 : Blo 1354996 1355351 := bstep (se 1 (by rfl) ⟨1016513, by rfl⟩ : syracuseStep 1355351 = 2033027) B2033027
theorem B2035289 : Blo 1354996 2035289 := bstep (se 2 (by rfl) ⟨763233, by rfl⟩ : syracuseStep 2035289 = 1526467) B1526467
theorem B1355371 : Blo 1354996 1355371 := bstep (se 1 (by rfl) ⟨1016528, by rfl⟩ : syracuseStep 1355371 = 2033057) B2033057
theorem B1355383 : Blo 1354996 1355383 := bstep (se 1 (by rfl) ⟨1016537, by rfl⟩ : syracuseStep 1355383 = 2033075) B2033075
theorem B1355403 : Blo 1354996 1355403 := bstep (se 1 (by rfl) ⟨1016552, by rfl⟩ : syracuseStep 1355403 = 2033105) B2033105
theorem B5148305 : Blo 1354996 5148305 := bstep (se 2 (by rfl) ⟨1930614, by rfl⟩ : syracuseStep 5148305 = 3861229) B3861229
theorem B1355415 : Blo 1354996 1355415 := bstep (se 1 (by rfl) ⟨1016561, by rfl⟩ : syracuseStep 1355415 = 2033123) B2033123
theorem B3051161 : Blo 1354996 3051161 := bstep (se 2 (by rfl) ⟨1144185, by rfl⟩ : syracuseStep 3051161 = 2288371) B2288371
theorem B1355435 : Blo 1354996 1355435 := bstep (se 1 (by rfl) ⟨1016576, by rfl⟩ : syracuseStep 1355435 = 2033153) B2033153
theorem B1355447 : Blo 1354996 1355447 := bstep (se 1 (by rfl) ⟨1016585, by rfl⟩ : syracuseStep 1355447 = 2033171) B2033171
theorem B1355467 : Blo 1354996 1355467 := bstep (se 1 (by rfl) ⟨1016600, by rfl⟩ : syracuseStep 1355467 = 2033201) B2033201
theorem B2035403 : Blo 1354996 2035403 := bstep (se 1 (by rfl) ⟨1526552, by rfl⟩ : syracuseStep 2035403 = 3053105) B3053105
theorem B1355479 : Blo 1354996 1355479 := bstep (se 1 (by rfl) ⟨1016609, by rfl⟩ : syracuseStep 1355479 = 2033219) B2033219
theorem B2035415 : Blo 1354996 2035415 := bstep (se 1 (by rfl) ⟨1526561, by rfl⟩ : syracuseStep 2035415 = 3053123) B3053123
theorem B1355499 : Blo 1354996 1355499 := bstep (se 1 (by rfl) ⟨1016624, by rfl⟩ : syracuseStep 1355499 = 2033249) B2033249
theorem B3051251 : Blo 1354996 3051251 := bstep (se 1 (by rfl) ⟨2288438, by rfl⟩ : syracuseStep 3051251 = 4576877) B4576877
theorem B1355511 : Blo 1354996 1355511 := bstep (se 1 (by rfl) ⟨1016633, by rfl⟩ : syracuseStep 1355511 = 2033267) B2033267
theorem B1355531 : Blo 1354996 1355531 := bstep (se 1 (by rfl) ⟨1016648, by rfl⟩ : syracuseStep 1355531 = 2033297) B2033297
theorem B1355543 : Blo 1354996 1355543 := bstep (se 1 (by rfl) ⟨1016657, by rfl⟩ : syracuseStep 1355543 = 2033315) B2033315
theorem B3051287 : Blo 1354996 3051287 := bstep (se 1 (by rfl) ⟨2288465, by rfl⟩ : syracuseStep 3051287 = 4576931) B4576931
theorem B2289431 : Blo 1354996 2289431 := bstep (se 1 (by rfl) ⟨1717073, by rfl⟩ : syracuseStep 2289431 = 3434147) B3434147
theorem B2035481 : Blo 1354996 2035481 := bstep (se 2 (by rfl) ⟨763305, by rfl⟩ : syracuseStep 2035481 = 1526611) B1526611
theorem B1355563 : Blo 1354996 1355563 := bstep (se 1 (by rfl) ⟨1016672, by rfl⟩ : syracuseStep 1355563 = 2033345) B2033345
theorem B3968819 : Blo 1354996 3968819 := bstep (se 1 (by rfl) ⟨2976614, by rfl⟩ : syracuseStep 3968819 = 5953229) B5953229
theorem B1355575 : Blo 1354996 1355575 := bstep (se 1 (by rfl) ⟨1016681, by rfl⟩ : syracuseStep 1355575 = 2033363) B2033363
theorem B4575041 : Blo 1354996 4575041 := bstep (se 2 (by rfl) ⟨1715640, by rfl⟩ : syracuseStep 4575041 = 3431281) B3431281
theorem B1355595 : Blo 1354996 1355595 := bstep (se 1 (by rfl) ⟨1016696, by rfl⟩ : syracuseStep 1355595 = 2033393) B2033393
theorem B2895691 : Blo 1354996 2895691 := bstep (se 1 (by rfl) ⟨2171768, by rfl⟩ : syracuseStep 2895691 = 4343537) B4343537
theorem B1355607 : Blo 1354996 1355607 := bstep (se 1 (by rfl) ⟨1016705, by rfl⟩ : syracuseStep 1355607 = 2033411) B2033411
theorem B1355627 : Blo 1354996 1355627 := bstep (se 1 (by rfl) ⟨1016720, by rfl⟩ : syracuseStep 1355627 = 2033441) B2033441
theorem B1355639 : Blo 1354996 1355639 := bstep (se 1 (by rfl) ⟨1016729, by rfl⟩ : syracuseStep 1355639 = 2033459) B2033459
theorem B1355659 : Blo 1354996 1355659 := bstep (se 1 (by rfl) ⟨1016744, by rfl⟩ : syracuseStep 1355659 = 2033489) B2033489
theorem B1355671 : Blo 1354996 1355671 := bstep (se 1 (by rfl) ⟨1016753, by rfl⟩ : syracuseStep 1355671 = 2033507) B2033507
theorem B2289559 : Blo 1354996 2289559 := bstep (se 1 (by rfl) ⟨1717169, by rfl⟩ : syracuseStep 2289559 = 3434339) B3434339
theorem B1355691 : Blo 1354996 1355691 := bstep (se 1 (by rfl) ⟨1016768, by rfl⟩ : syracuseStep 1355691 = 2033537) B2033537
theorem B7335859 : Blo 1354996 7335859 := bstep (se 1 (by rfl) ⟨5501894, by rfl⟩ : syracuseStep 7335859 = 11003789) B11003789
theorem B1355703 : Blo 1354996 1355703 := bstep (se 1 (by rfl) ⟨1016777, by rfl⟩ : syracuseStep 1355703 = 2033555) B2033555
theorem B1355723 : Blo 1354996 1355723 := bstep (se 1 (by rfl) ⟨1016792, by rfl⟩ : syracuseStep 1355723 = 2033585) B2033585
theorem B3051467 : Blo 1354996 3051467 := bstep (se 1 (by rfl) ⟨2288600, by rfl⟩ : syracuseStep 3051467 = 4577201) B4577201
theorem B1355735 : Blo 1354996 1355735 := bstep (se 1 (by rfl) ⟨1016801, by rfl⟩ : syracuseStep 1355735 = 2033603) B2033603
theorem B2609113 : Blo 1354996 2609113 := bstep (se 2 (by rfl) ⟨978417, by rfl⟩ : syracuseStep 2609113 = 1956835) B1956835
theorem B1355755 : Blo 1354996 1355755 := bstep (se 1 (by rfl) ⟨1016816, by rfl⟩ : syracuseStep 1355755 = 2033633) B2033633
theorem B1355767 : Blo 1354996 1355767 := bstep (se 1 (by rfl) ⟨1016825, by rfl⟩ : syracuseStep 1355767 = 2033651) B2033651
theorem B3051521 : Blo 1354996 3051521 := bstep (se 2 (by rfl) ⟨1144320, by rfl⟩ : syracuseStep 3051521 = 2288641) B2288641
theorem B1355787 : Blo 1354996 1355787 := bstep (se 1 (by rfl) ⟨1016840, by rfl⟩ : syracuseStep 1355787 = 2033681) B2033681
theorem B1355799 : Blo 1354996 1355799 := bstep (se 1 (by rfl) ⟨1016849, by rfl⟩ : syracuseStep 1355799 = 2033699) B2033699
theorem B15446051 : Blo 1354996 15446051 := bstep (se 1 (by rfl) ⟨11584538, by rfl⟩ : syracuseStep 15446051 = 23169077) B23169077
theorem B1355819 : Blo 1354996 1355819 := bstep (se 1 (by rfl) ⟨1016864, by rfl⟩ : syracuseStep 1355819 = 2033729) B2033729
theorem B1355831 : Blo 1354996 1355831 := bstep (se 1 (by rfl) ⟨1016873, by rfl⟩ : syracuseStep 1355831 = 2033747) B2033747
theorem B1355851 : Blo 1354996 1355851 := bstep (se 1 (by rfl) ⟨1016888, by rfl⟩ : syracuseStep 1355851 = 2033777) B2033777
theorem B3092555 : Blo 1354996 3092555 := bstep (se 1 (by rfl) ⟨2319416, by rfl⟩ : syracuseStep 3092555 = 4638833) B4638833
theorem B1355863 : Blo 1354996 1355863 := bstep (se 1 (by rfl) ⟨1016897, by rfl⟩ : syracuseStep 1355863 = 2033795) B2033795
theorem B1355883 : Blo 1354996 1355883 := bstep (se 1 (by rfl) ⟨1016912, by rfl⟩ : syracuseStep 1355883 = 2033825) B2033825
theorem B1355895 : Blo 1354996 1355895 := bstep (se 1 (by rfl) ⟨1016921, by rfl⟩ : syracuseStep 1355895 = 2033843) B2033843
theorem B6869123 : Blo 1354996 6869123 := bstep (se 1 (by rfl) ⟨5151842, by rfl⟩ : syracuseStep 6869123 = 10303685) B10303685
theorem B1355915 : Blo 1354996 1355915 := bstep (se 1 (by rfl) ⟨1016936, by rfl⟩ : syracuseStep 1355915 = 2033873) B2033873
theorem B1929367 : Blo 1354996 1929367 := bstep (se 1 (by rfl) ⟨1447025, by rfl⟩ : syracuseStep 1929367 = 2894051) B2894051
theorem B1355927 : Blo 1354996 1355927 := bstep (se 1 (by rfl) ⟨1016945, by rfl⟩ : syracuseStep 1355927 = 2033891) B2033891
theorem B1355947 : Blo 1354996 1355947 := bstep (se 1 (by rfl) ⟨1016960, by rfl⟩ : syracuseStep 1355947 = 2033921) B2033921
theorem B1355959 : Blo 1354996 1355959 := bstep (se 1 (by rfl) ⟨1016969, by rfl⟩ : syracuseStep 1355959 = 2033939) B2033939
theorem B3666113 : Blo 1354996 3666113 := bstep (se 2 (by rfl) ⟨1374792, by rfl⟩ : syracuseStep 3666113 = 2749585) B2749585
theorem B3862721 : Blo 1354996 3862721 := bstep (se 2 (by rfl) ⟨1448520, by rfl⟩ : syracuseStep 3862721 = 2897041) B2897041
theorem B1355979 : Blo 1354996 1355979 := bstep (se 1 (by rfl) ⟨1016984, by rfl⟩ : syracuseStep 1355979 = 2033969) B2033969
theorem B2937035 : Blo 1354996 2937035 := bstep (se 1 (by rfl) ⟨2202776, by rfl⟩ : syracuseStep 2937035 = 4405553) B4405553
theorem B1355991 : Blo 1354996 1355991 := bstep (se 1 (by rfl) ⟨1016993, by rfl⟩ : syracuseStep 1355991 = 2033987) B2033987
theorem B3051737 : Blo 1354996 3051737 := bstep (se 2 (by rfl) ⟨1144401, by rfl⟩ : syracuseStep 3051737 = 2288803) B2288803
theorem B1356011 : Blo 1354996 1356011 := bstep (se 1 (by rfl) ⟨1017008, by rfl⟩ : syracuseStep 1356011 = 2034017) B2034017
theorem B1356023 : Blo 1354996 1356023 := bstep (se 1 (by rfl) ⟨1017017, by rfl⟩ : syracuseStep 1356023 = 2034035) B2034035
theorem B1356043 : Blo 1354996 1356043 := bstep (se 1 (by rfl) ⟨1017032, by rfl⟩ : syracuseStep 1356043 = 2034065) B2034065
theorem B1716491 : Blo 1354996 1716491 := bstep (se 1 (by rfl) ⟨1287368, by rfl⟩ : syracuseStep 1716491 = 2574737) B2574737
theorem B1356055 : Blo 1354996 1356055 := bstep (se 1 (by rfl) ⟨1017041, by rfl⟩ : syracuseStep 1356055 = 2034083) B2034083
theorem B1356075 : Blo 1354996 1356075 := bstep (se 1 (by rfl) ⟨1017056, by rfl⟩ : syracuseStep 1356075 = 2034113) B2034113
theorem B12366125 : Blo 1354996 12366125 := bstep (se 3 (by rfl) ⟨2318648, by rfl⟩ : syracuseStep 12366125 = 4637297) B4637297
theorem B10301741 : Blo 1354996 10301741 := bstep (se 3 (by rfl) ⟨1931576, by rfl⟩ : syracuseStep 10301741 = 3863153) B3863153
theorem B3051827 : Blo 1354996 3051827 := bstep (se 1 (by rfl) ⟨2288870, by rfl⟩ : syracuseStep 3051827 = 4577741) B4577741
theorem B3862835 : Blo 1354996 3862835 := bstep (se 1 (by rfl) ⟨2897126, by rfl⟩ : syracuseStep 3862835 = 5794253) B5794253
theorem B1356087 : Blo 1354996 1356087 := bstep (se 1 (by rfl) ⟨1017065, by rfl⟩ : syracuseStep 1356087 = 2034131) B2034131
theorem B6189377 : Blo 1354996 6189377 := bstep (se 2 (by rfl) ⟨2321016, by rfl⟩ : syracuseStep 6189377 = 4642033) B4642033
theorem B1356107 : Blo 1354996 1356107 := bstep (se 1 (by rfl) ⟨1017080, by rfl⟩ : syracuseStep 1356107 = 2034161) B2034161
theorem B1356119 : Blo 1354996 1356119 := bstep (se 1 (by rfl) ⟨1017089, by rfl⟩ : syracuseStep 1356119 = 2034179) B2034179
theorem B3051863 : Blo 1354996 3051863 := bstep (se 1 (by rfl) ⟨2288897, by rfl⟩ : syracuseStep 3051863 = 4577795) B4577795
theorem B4575581 : Blo 1354996 4575581 := bstep (se 3 (by rfl) ⟨857921, by rfl⟩ : syracuseStep 4575581 = 1715843) B1715843
theorem B1356139 : Blo 1354996 1356139 := bstep (se 1 (by rfl) ⟨1017104, by rfl⟩ : syracuseStep 1356139 = 2034209) B2034209
theorem B68694389 : Blo 1354996 68694389 := bstep (se 5 (by rfl) ⟨3220049, by rfl⟩ : syracuseStep 68694389 = 6440099) B6440099
theorem B1356151 : Blo 1354996 1356151 := bstep (se 1 (by rfl) ⟨1017113, by rfl⟩ : syracuseStep 1356151 = 2034227) B2034227
theorem B1356171 : Blo 1354996 1356171 := bstep (se 1 (by rfl) ⟨1017128, by rfl⟩ : syracuseStep 1356171 = 2034257) B2034257
theorem B5149079 : Blo 1354996 5149079 := bstep (se 1 (by rfl) ⟨3861809, by rfl⟩ : syracuseStep 5149079 = 7723619) B7723619
theorem B1356183 : Blo 1354996 1356183 := bstep (se 1 (by rfl) ⟨1017137, by rfl⟩ : syracuseStep 1356183 = 2034275) B2034275
theorem B1356203 : Blo 1354996 1356203 := bstep (se 1 (by rfl) ⟨1017152, by rfl⟩ : syracuseStep 1356203 = 2034305) B2034305
theorem B5796269 : Blo 1354996 5796269 := bstep (se 3 (by rfl) ⟨1086800, by rfl⟩ : syracuseStep 5796269 = 2173601) B2173601
theorem B1356215 : Blo 1354996 1356215 := bstep (se 1 (by rfl) ⟨1017161, by rfl⟩ : syracuseStep 1356215 = 2034323) B2034323
theorem B1356235 : Blo 1354996 1356235 := bstep (se 1 (by rfl) ⟨1017176, by rfl⟩ : syracuseStep 1356235 = 2034353) B2034353
theorem B1356247 : Blo 1354996 1356247 := bstep (se 1 (by rfl) ⟨1017185, by rfl⟩ : syracuseStep 1356247 = 2034371) B2034371
theorem B1356267 : Blo 1354996 1356267 := bstep (se 1 (by rfl) ⟨1017200, by rfl⟩ : syracuseStep 1356267 = 2034401) B2034401
theorem B1356279 : Blo 1354996 1356279 := bstep (se 1 (by rfl) ⟨1017209, by rfl⟩ : syracuseStep 1356279 = 2034419) B2034419
theorem B1356299 : Blo 1354996 1356299 := bstep (se 1 (by rfl) ⟨1017224, by rfl⟩ : syracuseStep 1356299 = 2034449) B2034449
theorem B3052043 : Blo 1354996 3052043 := bstep (se 1 (by rfl) ⟨2289032, by rfl⟩ : syracuseStep 3052043 = 4578065) B4578065
theorem B1356311 : Blo 1354996 1356311 := bstep (se 1 (by rfl) ⟨1017233, by rfl⟩ : syracuseStep 1356311 = 2034467) B2034467
theorem B1356331 : Blo 1354996 1356331 := bstep (se 1 (by rfl) ⟨1017248, by rfl⟩ : syracuseStep 1356331 = 2034497) B2034497
theorem B5788205 : Blo 1354996 5788205 := bstep (se 3 (by rfl) ⟨1085288, by rfl⟩ : syracuseStep 5788205 = 2170577) B2170577
theorem B1356343 : Blo 1354996 1356343 := bstep (se 1 (by rfl) ⟨1017257, by rfl⟩ : syracuseStep 1356343 = 2034515) B2034515
theorem B3052097 : Blo 1354996 3052097 := bstep (se 2 (by rfl) ⟨1144536, by rfl⟩ : syracuseStep 3052097 = 2289073) B2289073
theorem B1356363 : Blo 1354996 1356363 := bstep (se 1 (by rfl) ⟨1017272, by rfl⟩ : syracuseStep 1356363 = 2034545) B2034545
theorem B1356375 : Blo 1354996 1356375 := bstep (se 1 (by rfl) ⟨1017281, by rfl⟩ : syracuseStep 1356375 = 2034563) B2034563
theorem B5149277 : Blo 1354996 5149277 := bstep (se 3 (by rfl) ⟨965489, by rfl⟩ : syracuseStep 5149277 = 1930979) B1930979
theorem B1356395 : Blo 1354996 1356395 := bstep (se 1 (by rfl) ⟨1017296, by rfl⟩ : syracuseStep 1356395 = 2034593) B2034593
theorem B1356407 : Blo 1354996 1356407 := bstep (se 1 (by rfl) ⟨1017305, by rfl⟩ : syracuseStep 1356407 = 2034611) B2034611
theorem B1356427 : Blo 1354996 1356427 := bstep (se 1 (by rfl) ⟨1017320, by rfl⟩ : syracuseStep 1356427 = 2034641) B2034641
theorem B1356439 : Blo 1354996 1356439 := bstep (se 1 (by rfl) ⟨1017329, by rfl⟩ : syracuseStep 1356439 = 2034659) B2034659
theorem B1356459 : Blo 1354996 1356459 := bstep (se 1 (by rfl) ⟨1017344, by rfl⟩ : syracuseStep 1356459 = 2034689) B2034689
theorem B1356471 : Blo 1354996 1356471 := bstep (se 1 (by rfl) ⟨1017353, by rfl⟩ : syracuseStep 1356471 = 2034707) B2034707
theorem B4125377 : Blo 1354996 4125377 := bstep (se 2 (by rfl) ⟨1547016, by rfl⟩ : syracuseStep 4125377 = 3094033) B3094033
theorem B4346561 : Blo 1354996 4346561 := bstep (se 2 (by rfl) ⟨1629960, by rfl⟩ : syracuseStep 4346561 = 3259921) B3259921
theorem B1356491 : Blo 1354996 1356491 := bstep (se 1 (by rfl) ⟨1017368, by rfl⟩ : syracuseStep 1356491 = 2034737) B2034737
theorem B10293965 : Blo 1354996 10293965 := bstep (se 3 (by rfl) ⟨1930118, by rfl⟩ : syracuseStep 10293965 = 3860237) B3860237
theorem B18551501 : Blo 1354996 18551501 := bstep (se 3 (by rfl) ⟨3478406, by rfl⟩ : syracuseStep 18551501 = 6956813) B6956813
theorem B1356503 : Blo 1354996 1356503 := bstep (se 1 (by rfl) ⟨1017377, by rfl⟩ : syracuseStep 1356503 = 2034755) B2034755
theorem B1356523 : Blo 1354996 1356523 := bstep (se 1 (by rfl) ⟨1017392, by rfl⟩ : syracuseStep 1356523 = 2034785) B2034785
theorem B1356535 : Blo 1354996 1356535 := bstep (se 1 (by rfl) ⟨1017401, by rfl⟩ : syracuseStep 1356535 = 2034803) B2034803
theorem B1356555 : Blo 1354996 1356555 := bstep (se 1 (by rfl) ⟨1017416, by rfl⟩ : syracuseStep 1356555 = 2034833) B2034833
theorem B1356567 : Blo 1354996 1356567 := bstep (se 1 (by rfl) ⟨1017425, by rfl⟩ : syracuseStep 1356567 = 2034851) B2034851
theorem B3052313 : Blo 1354996 3052313 := bstep (se 2 (by rfl) ⟨1144617, by rfl⟩ : syracuseStep 3052313 = 2289235) B2289235
theorem B1356587 : Blo 1354996 1356587 := bstep (se 1 (by rfl) ⟨1017440, by rfl⟩ : syracuseStep 1356587 = 2034881) B2034881
theorem B2511667 : Blo 1354996 2511667 := bstep (se 1 (by rfl) ⟨1883750, by rfl⟩ : syracuseStep 2511667 = 3767501) B3767501
theorem B1356599 : Blo 1354996 1356599 := bstep (se 1 (by rfl) ⟨1017449, by rfl⟩ : syracuseStep 1356599 = 2034899) B2034899
theorem B8926027 : Blo 1354996 8926027 := bstep (se 1 (by rfl) ⟨6694520, by rfl⟩ : syracuseStep 8926027 = 13389041) B13389041
theorem B1356619 : Blo 1354996 1356619 := bstep (se 1 (by rfl) ⟨1017464, by rfl⟩ : syracuseStep 1356619 = 2034929) B2034929
theorem B1356631 : Blo 1354996 1356631 := bstep (se 1 (by rfl) ⟨1017473, by rfl⟩ : syracuseStep 1356631 = 2034947) B2034947
theorem B1930073 : Blo 1354996 1930073 := bstep (se 2 (by rfl) ⟨723777, by rfl⟩ : syracuseStep 1930073 = 1447555) B1447555
theorem B1356651 : Blo 1354996 1356651 := bstep (se 1 (by rfl) ⟨1017488, by rfl⟩ : syracuseStep 1356651 = 2034977) B2034977
theorem B3052403 : Blo 1354996 3052403 := bstep (se 1 (by rfl) ⟨2289302, by rfl⟩ : syracuseStep 3052403 = 4578605) B4578605
theorem B1356663 : Blo 1354996 1356663 := bstep (se 1 (by rfl) ⟨1017497, by rfl⟩ : syracuseStep 1356663 = 2034995) B2034995
theorem B1356683 : Blo 1354996 1356683 := bstep (se 1 (by rfl) ⟨1017512, by rfl⟩ : syracuseStep 1356683 = 2035025) B2035025
theorem B3052439 : Blo 1354996 3052439 := bstep (se 1 (by rfl) ⟨2289329, by rfl⟩ : syracuseStep 3052439 = 4578659) B4578659
theorem B1356695 : Blo 1354996 1356695 := bstep (se 1 (by rfl) ⟨1017521, by rfl⟩ : syracuseStep 1356695 = 2035043) B2035043
theorem B1356715 : Blo 1354996 1356715 := bstep (se 1 (by rfl) ⟨1017536, by rfl⟩ : syracuseStep 1356715 = 2035073) B2035073
theorem B1356727 : Blo 1354996 1356727 := bstep (se 1 (by rfl) ⟨1017545, by rfl⟩ : syracuseStep 1356727 = 2035091) B2035091
theorem B1930187 : Blo 1354996 1930187 := bstep (se 1 (by rfl) ⟨1447640, by rfl⟩ : syracuseStep 1930187 = 2895281) B2895281
theorem B1356747 : Blo 1354996 1356747 := bstep (se 1 (by rfl) ⟨1017560, by rfl⟩ : syracuseStep 1356747 = 2035121) B2035121
theorem B1717195 : Blo 1354996 1717195 := bstep (se 1 (by rfl) ⟨1287896, by rfl⟩ : syracuseStep 1717195 = 2575793) B2575793
theorem B1356759 : Blo 1354996 1356759 := bstep (se 1 (by rfl) ⟨1017569, by rfl⟩ : syracuseStep 1356759 = 2035139) B2035139
theorem B2200537 : Blo 1354996 2200537 := bstep (se 2 (by rfl) ⟨825201, by rfl⟩ : syracuseStep 2200537 = 1650403) B1650403
theorem B2610137 : Blo 1354996 2610137 := bstep (se 2 (by rfl) ⟨978801, by rfl⟩ : syracuseStep 2610137 = 1957603) B1957603
theorem B1356779 : Blo 1354996 1356779 := bstep (se 1 (by rfl) ⟨1017584, by rfl⟩ : syracuseStep 1356779 = 2035169) B2035169
theorem B1356791 : Blo 1354996 1356791 := bstep (se 1 (by rfl) ⟨1017593, by rfl⟩ : syracuseStep 1356791 = 2035187) B2035187
theorem B1356811 : Blo 1354996 1356811 := bstep (se 1 (by rfl) ⟨1017608, by rfl⟩ : syracuseStep 1356811 = 2035217) B2035217
theorem B41735189 : Blo 1354996 41735189 := bstep (se 6 (by rfl) ⟨978168, by rfl⟩ : syracuseStep 41735189 = 1956337) B1956337
theorem B1356823 : Blo 1354996 1356823 := bstep (se 1 (by rfl) ⟨1017617, by rfl⟩ : syracuseStep 1356823 = 2035235) B2035235
theorem B2896921 : Blo 1354996 2896921 := bstep (se 2 (by rfl) ⟨1086345, by rfl⟩ : syracuseStep 2896921 = 2172691) B2172691
theorem B1356843 : Blo 1354996 1356843 := bstep (se 1 (by rfl) ⟨1017632, by rfl⟩ : syracuseStep 1356843 = 2035265) B2035265
theorem B1356855 : Blo 1354996 1356855 := bstep (se 1 (by rfl) ⟨1017641, by rfl⟩ : syracuseStep 1356855 = 2035283) B2035283
theorem B3052619 : Blo 1354996 3052619 := bstep (se 1 (by rfl) ⟨2289464, by rfl⟩ : syracuseStep 3052619 = 4578929) B4578929
theorem B1356875 : Blo 1354996 1356875 := bstep (se 1 (by rfl) ⟨1017656, by rfl⟩ : syracuseStep 1356875 = 2035313) B2035313
theorem B1356887 : Blo 1354996 1356887 := bstep (se 1 (by rfl) ⟨1017665, by rfl⟩ : syracuseStep 1356887 = 2035331) B2035331
theorem B1356907 : Blo 1354996 1356907 := bstep (se 1 (by rfl) ⟨1017680, by rfl⟩ : syracuseStep 1356907 = 2035361) B2035361
theorem B1356919 : Blo 1354996 1356919 := bstep (se 1 (by rfl) ⟨1017689, by rfl⟩ : syracuseStep 1356919 = 2035379) B2035379
theorem B3052673 : Blo 1354996 3052673 := bstep (se 2 (by rfl) ⟨1144752, by rfl⟩ : syracuseStep 3052673 = 2289505) B2289505
theorem B1356939 : Blo 1354996 1356939 := bstep (se 1 (by rfl) ⟨1017704, by rfl⟩ : syracuseStep 1356939 = 2035409) B2035409
theorem B1356951 : Blo 1354996 1356951 := bstep (se 1 (by rfl) ⟨1017713, by rfl⟩ : syracuseStep 1356951 = 2035427) B2035427
theorem B1356971 : Blo 1354996 1356971 := bstep (se 1 (by rfl) ⟨1017728, by rfl⟩ : syracuseStep 1356971 = 2035457) B2035457
theorem B10294451 : Blo 1354996 10294451 := bstep (se 1 (by rfl) ⟨7720838, by rfl⟩ : syracuseStep 10294451 = 15441677) B15441677
theorem B20092085 : Blo 1354996 20092085 := bstep (se 5 (by rfl) ⟨941816, by rfl⟩ : syracuseStep 20092085 = 1883633) B1883633
theorem B1356983 : Blo 1354996 1356983 := bstep (se 1 (by rfl) ⟨1017737, by rfl⟩ : syracuseStep 1356983 = 2035475) B2035475
theorem B1373495 : Blo 1354996 1373495 := bstep (se 1 (by rfl) ⟨1030121, by rfl⟩ : syracuseStep 1373495 = 2060243) B2060243
theorem B3052889 : Blo 1354996 3052889 := bstep (se 2 (by rfl) ⟨1144833, by rfl⟩ : syracuseStep 3052889 = 2289667) B2289667
theorem B3052979 : Blo 1354996 3052979 := bstep (se 1 (by rfl) ⟨2289734, by rfl⟩ : syracuseStep 3052979 = 4579469) B4579469
theorem B4576715 : Blo 1354996 4576715 := bstep (se 1 (by rfl) ⟨3432536, by rfl⟩ : syracuseStep 4576715 = 6865073) B6865073
theorem B1930711 : Blo 1354996 1930711 := bstep (se 1 (by rfl) ⟨1448033, by rfl⟩ : syracuseStep 1930711 = 2896067) B2896067
theorem B3053015 : Blo 1354996 3053015 := bstep (se 1 (by rfl) ⟨2289761, by rfl⟩ : syracuseStep 3053015 = 4579523) B4579523
theorem B1373707 : Blo 1354996 1373707 := bstep (se 1 (by rfl) ⟨1030280, by rfl⟩ : syracuseStep 1373707 = 2060561) B2060561
theorem B11589155 : Blo 1354996 11589155 := bstep (se 1 (by rfl) ⟨8691866, by rfl⟩ : syracuseStep 11589155 = 17383733) B17383733
theorem B2061911 : Blo 1354996 2061911 := bstep (se 1 (by rfl) ⟨1546433, by rfl⟩ : syracuseStep 2061911 = 3092867) B3092867
theorem B3094105 : Blo 1354996 3094105 := bstep (se 2 (by rfl) ⟨1160289, by rfl⟩ : syracuseStep 3094105 = 2320579) B2320579
theorem B3053195 : Blo 1354996 3053195 := bstep (se 1 (by rfl) ⟨2289896, by rfl⟩ : syracuseStep 3053195 = 4579793) B4579793
theorem B4576985 : Blo 1354996 4576985 := bstep (se 2 (by rfl) ⟨1716369, by rfl⟩ : syracuseStep 4576985 = 3432739) B3432739
theorem B3667801 : Blo 1354996 3667801 := bstep (se 2 (by rfl) ⟨1375425, by rfl⟩ : syracuseStep 3667801 = 2750851) B2750851
theorem B3094451 : Blo 1354996 3094451 := bstep (se 1 (by rfl) ⟨2320838, by rfl⟩ : syracuseStep 3094451 = 4641677) B4641677
theorem B5789657 : Blo 1354996 5789657 := bstep (se 2 (by rfl) ⟨2171121, by rfl⟩ : syracuseStep 5789657 = 4342243) B4342243
theorem B9770969 : Blo 1354996 9770969 := bstep (se 2 (by rfl) ⟨3664113, by rfl⟩ : syracuseStep 9770969 = 7328227) B7328227
theorem B3430451 : Blo 1354996 3430451 := bstep (se 1 (by rfl) ⟨2572838, by rfl⟩ : syracuseStep 3430451 = 5145677) B5145677
theorem B1833035 : Blo 1354996 1833035 := bstep (se 1 (by rfl) ⟨1374776, by rfl⟩ : syracuseStep 1833035 = 2749553) B2749553
theorem B21993565 : Blo 1354996 21993565 := bstep (se 3 (by rfl) ⟨4123793, by rfl⟩ : syracuseStep 21993565 = 8247587) B8247587
theorem B7723187 : Blo 1354996 7723187 := bstep (se 1 (by rfl) ⟨5792390, by rfl⟩ : syracuseStep 7723187 = 11584781) B11584781
theorem B1448119 : Blo 1354996 1448119 := bstep (se 1 (by rfl) ⟨1086089, by rfl⟩ : syracuseStep 1448119 = 2172179) B2172179
theorem B2750681 : Blo 1354996 2750681 := bstep (se 2 (by rfl) ⟨1031505, by rfl⟩ : syracuseStep 2750681 = 2063011) B2063011
theorem B15644933 : Blo 1354996 15644933 := bstep (se 4 (by rfl) ⟨1466712, by rfl⟩ : syracuseStep 15644933 = 2933425) B2933425
theorem B1931531 : Blo 1354996 1931531 := bstep (se 1 (by rfl) ⟨1448648, by rfl⟩ : syracuseStep 1931531 = 2897297) B2897297
theorem B3430745 : Blo 1354996 3430745 := bstep (se 2 (by rfl) ⟨1286529, by rfl⟩ : syracuseStep 3430745 = 2573059) B2573059
theorem B125254001 : Blo 1354996 125254001 := bstep (se 2 (by rfl) ⟨46970250, by rfl⟩ : syracuseStep 125254001 = 93940501) B93940501
theorem B4577687 : Blo 1354996 4577687 := bstep (se 1 (by rfl) ⟨3433265, by rfl⟩ : syracuseStep 4577687 = 6866531) B6866531
theorem B1448375 : Blo 1354996 1448375 := bstep (se 1 (by rfl) ⟨1086281, by rfl⟩ : syracuseStep 1448375 = 2172563) B2172563
theorem B5151235 : Blo 1354996 5151235 := bstep (se 1 (by rfl) ⟨3863426, by rfl⟩ : syracuseStep 5151235 = 7726853) B7726853
theorem B12368459 : Blo 1354996 12368459 := bstep (se 1 (by rfl) ⟨9276344, by rfl⟩ : syracuseStep 12368459 = 18552689) B18552689
theorem B6863453 : Blo 1354996 6863453 := bstep (se 3 (by rfl) ⟨1286897, by rfl⟩ : syracuseStep 6863453 = 2573795) B2573795
theorem B10295909 : Blo 1354996 10295909 := bstep (se 4 (by rfl) ⟨965241, by rfl⟩ : syracuseStep 10295909 = 1930483) B1930483
theorem B5151539 : Blo 1354996 5151539 := bstep (se 1 (by rfl) ⟨3863654, by rfl⟩ : syracuseStep 5151539 = 7727309) B7727309
theorem B4578227 : Blo 1354996 4578227 := bstep (se 1 (by rfl) ⟨3433670, by rfl⟩ : syracuseStep 4578227 = 6867341) B6867341
theorem B1448939 : Blo 1354996 1448939 := bstep (se 1 (by rfl) ⟨1086704, by rfl⟩ : syracuseStep 1448939 = 2173409) B2173409
theorem B6511691 : Blo 1354996 6511691 := bstep (se 1 (by rfl) ⟨4883768, by rfl⟩ : syracuseStep 6511691 = 9767537) B9767537
theorem B10296395 : Blo 1354996 10296395 := bstep (se 1 (by rfl) ⟨7722296, by rfl⟩ : syracuseStep 10296395 = 15444593) B15444593
theorem B17366147 : Blo 1354996 17366147 := bstep (se 1 (by rfl) ⟨13024610, by rfl⟩ : syracuseStep 17366147 = 26049221) B26049221
theorem B4578497 : Blo 1354996 4578497 := bstep (se 2 (by rfl) ⟨1716936, by rfl⟩ : syracuseStep 4578497 = 3433873) B3433873
theorem B9780659 : Blo 1354996 9780659 := bstep (se 1 (by rfl) ⟨7335494, by rfl⟩ : syracuseStep 9780659 = 14670989) B14670989
theorem B5152193 : Blo 1354996 5152193 := bstep (se 2 (by rfl) ⟨1932072, by rfl⟩ : syracuseStep 5152193 = 3864145) B3864145
theorem B5791297 : Blo 1354996 5791297 := bstep (se 2 (by rfl) ⟨2171736, by rfl⟩ : syracuseStep 5791297 = 4343473) B4343473
theorem B8691275 : Blo 1354996 8691275 := bstep (se 1 (by rfl) ⟨6518456, by rfl⟩ : syracuseStep 8691275 = 13036913) B13036913
theorem B7724645 : Blo 1354996 7724645 := bstep (se 4 (by rfl) ⟨724185, by rfl⟩ : syracuseStep 7724645 = 1448371) B1448371
theorem B4579037 : Blo 1354996 4579037 := bstep (se 3 (by rfl) ⟨858569, by rfl⟩ : syracuseStep 4579037 = 1717139) B1717139
theorem B4890457 : Blo 1354996 4890457 := bstep (se 2 (by rfl) ⟨1833921, by rfl⟩ : syracuseStep 4890457 = 3667843) B3667843
theorem B3432395 : Blo 1354996 3432395 := bstep (se 1 (by rfl) ⟨2574296, by rfl⟩ : syracuseStep 3432395 = 5148593) B5148593
theorem B32964569 : Blo 1354996 32964569 := bstep (se 2 (by rfl) ⟨12361713, by rfl⟩ : syracuseStep 32964569 = 24723427) B24723427
theorem B10297367 : Blo 1354996 10297367 := bstep (se 1 (by rfl) ⟨7723025, by rfl⟩ : syracuseStep 10297367 = 15446051) B15446051
theorem B3260459 : Blo 1354996 3260459 := bstep (se 1 (by rfl) ⟨2445344, by rfl⟩ : syracuseStep 3260459 = 4890689) B4890689
theorem B4579415 : Blo 1354996 4579415 := bstep (se 1 (by rfl) ⟨3434561, by rfl⟩ : syracuseStep 4579415 = 6869123) B6869123
theorem B1958023 : Blo 1354996 1958023 := bstep (se 1 (by rfl) ⟨1468517, by rfl⟩ : syracuseStep 1958023 = 2937035) B2937035
theorem B2572489 : Blo 1354996 2572489 := bstep (se 2 (by rfl) ⟨964683, by rfl⟩ : syracuseStep 2572489 = 1929367) B1929367
theorem B3432719 : Blo 1354996 3432719 := bstep (se 1 (by rfl) ⟨2574539, by rfl⟩ : syracuseStep 3432719 = 5149079) B5149079
theorem B3858803 : Blo 1354996 3858803 := bstep (se 1 (by rfl) ⟨2894102, by rfl⟩ : syracuseStep 3858803 = 5788205) B5788205
theorem B3432851 : Blo 1354996 3432851 := bstep (se 1 (by rfl) ⟨2574638, by rfl⟩ : syracuseStep 3432851 = 5149277) B5149277
theorem B29303477 : Blo 1354996 29303477 := bstep (se 5 (by rfl) ⟨1373600, by rfl⟩ : syracuseStep 29303477 = 2747201) B2747201
theorem B1524487 : Blo 1354996 1524487 := bstep (se 1 (by rfl) ⟨1143365, by rfl⟩ : syracuseStep 1524487 = 2286731) B2286731
theorem B66896675 : Blo 1354996 66896675 := bstep (se 1 (by rfl) ⟨50172506, by rfl⟩ : syracuseStep 66896675 = 100345013) B100345013
theorem B13394723 : Blo 1354996 13394723 := bstep (se 1 (by rfl) ⟨10046042, by rfl⟩ : syracuseStep 13394723 = 20092085) B20092085
theorem B5145403 : Blo 1354996 5145403 := bstep (se 1 (by rfl) ⟨3859052, by rfl⟩ : syracuseStep 5145403 = 7718105) B7718105
theorem B3662653 : Blo 1354996 3662653 := bstep (se 3 (by rfl) ⟨686747, by rfl⟩ : syracuseStep 3662653 = 1373495) B1373495
theorem B2573203 : Blo 1354996 2573203 := bstep (se 1 (by rfl) ⟨1929902, by rfl⟩ : syracuseStep 2573203 = 3859805) B3859805
theorem B2032571 : Blo 1354996 2032571 := bstep (se 1 (by rfl) ⟨1524428, by rfl⟩ : syracuseStep 2032571 = 3048857) B3048857
theorem B1524667 : Blo 1354996 1524667 := bstep (se 1 (by rfl) ⟨1143500, by rfl⟩ : syracuseStep 1524667 = 2287001) B2287001
theorem B2032631 : Blo 1354996 2032631 := bstep (se 1 (by rfl) ⟨1524473, by rfl⟩ : syracuseStep 2032631 = 3048947) B3048947
theorem B2032655 : Blo 1354996 2032655 := bstep (se 1 (by rfl) ⟨1524491, by rfl⟩ : syracuseStep 2032655 = 3048983) B3048983
theorem B7726103 : Blo 1354996 7726103 := bstep (se 1 (by rfl) ⟨5794577, by rfl⟩ : syracuseStep 7726103 = 11589155) B11589155
theorem B2032697 : Blo 1354996 2032697 := bstep (se 2 (by rfl) ⟨762261, by rfl⟩ : syracuseStep 2032697 = 1524523) B1524523
theorem B2032775 : Blo 1354996 2032775 := bstep (se 1 (by rfl) ⟨1524581, by rfl⟩ : syracuseStep 2032775 = 3049163) B3049163
theorem B2032811 : Blo 1354996 2032811 := bstep (se 1 (by rfl) ⟨1524608, by rfl⟩ : syracuseStep 2032811 = 3049217) B3049217
theorem B2032841 : Blo 1354996 2032841 := bstep (se 2 (by rfl) ⟨762315, by rfl⟩ : syracuseStep 2032841 = 1524631) B1524631
theorem B2934049 : Blo 1354996 2934049 := bstep (se 2 (by rfl) ⟨1100268, by rfl⟩ : syracuseStep 2934049 = 2200537) B2200537
theorem B5145889 : Blo 1354996 5145889 := bstep (se 2 (by rfl) ⟨1929708, by rfl⟩ : syracuseStep 5145889 = 3859417) B3859417
theorem B2032955 : Blo 1354996 2032955 := bstep (se 1 (by rfl) ⟨1524716, by rfl⟩ : syracuseStep 2032955 = 3049433) B3049433
theorem B3859771 : Blo 1354996 3859771 := bstep (se 1 (by rfl) ⟨2894828, by rfl⟩ : syracuseStep 3859771 = 5789657) B5789657
theorem B2286967 : Blo 1354996 2286967 := bstep (se 1 (by rfl) ⟨1715225, by rfl⟩ : syracuseStep 2286967 = 3430451) B3430451
theorem B2033015 : Blo 1354996 2033015 := bstep (se 1 (by rfl) ⟨1524761, by rfl⟩ : syracuseStep 2033015 = 3049523) B3049523
theorem B3048839 : Blo 1354996 3048839 := bstep (se 1 (by rfl) ⟨2286629, by rfl⟩ : syracuseStep 3048839 = 4573259) B4573259
theorem B19547527 : Blo 1354996 19547527 := bstep (se 1 (by rfl) ⟨14660645, by rfl⟩ : syracuseStep 19547527 = 29321291) B29321291
theorem B2033039 : Blo 1354996 2033039 := bstep (se 1 (by rfl) ⟨1524779, by rfl⟩ : syracuseStep 2033039 = 3049559) B3049559
theorem B1525135 : Blo 1354996 1525135 := bstep (se 1 (by rfl) ⟨1143851, by rfl⟩ : syracuseStep 1525135 = 2287703) B2287703
theorem B2033081 : Blo 1354996 2033081 := bstep (se 2 (by rfl) ⟨762405, by rfl⟩ : syracuseStep 2033081 = 1524811) B1524811
theorem B10429955 : Blo 1354996 10429955 := bstep (se 1 (by rfl) ⟨7822466, by rfl⟩ : syracuseStep 10429955 = 15644933) B15644933
theorem B3433985 : Blo 1354996 3433985 := bstep (se 2 (by rfl) ⟨1287744, by rfl⟩ : syracuseStep 3433985 = 2575489) B2575489
theorem B2033159 : Blo 1354996 2033159 := bstep (se 1 (by rfl) ⟨1524869, by rfl⟩ : syracuseStep 2033159 = 3049739) B3049739
theorem B32982557 : Blo 1354996 32982557 := bstep (se 3 (by rfl) ⟨6184229, by rfl⟩ : syracuseStep 32982557 = 12368459) B12368459
theorem B2033195 : Blo 1354996 2033195 := bstep (se 1 (by rfl) ⟨1524896, by rfl⟩ : syracuseStep 2033195 = 3049793) B3049793
theorem B3049019 : Blo 1354996 3049019 := bstep (se 1 (by rfl) ⟨2286764, by rfl⟩ : syracuseStep 3049019 = 4573529) B4573529
theorem B2287163 : Blo 1354996 2287163 := bstep (se 1 (by rfl) ⟨1715372, by rfl⟩ : syracuseStep 2287163 = 3430745) B3430745
theorem B2033225 : Blo 1354996 2033225 := bstep (se 2 (by rfl) ⟨762459, by rfl⟩ : syracuseStep 2033225 = 1524919) B1524919
theorem B83502667 : Blo 1354996 83502667 := bstep (se 1 (by rfl) ⟨62627000, by rfl⟩ : syracuseStep 83502667 = 125254001) B125254001
theorem B13395557 : Blo 1354996 13395557 := bstep (se 4 (by rfl) ⟨1255833, by rfl⟩ : syracuseStep 13395557 = 2511667) B2511667
theorem B3049145 : Blo 1354996 3049145 := bstep (se 2 (by rfl) ⟨1143429, by rfl⟩ : syracuseStep 3049145 = 2286859) B2286859
theorem B2033339 : Blo 1354996 2033339 := bstep (se 1 (by rfl) ⟨1525004, by rfl⟩ : syracuseStep 2033339 = 3050009) B3050009
theorem B47605477 : Blo 1354996 47605477 := bstep (se 4 (by rfl) ⟨4463013, by rfl⟩ : syracuseStep 47605477 = 8926027) B8926027
theorem B2033399 : Blo 1354996 2033399 := bstep (se 1 (by rfl) ⟨1525049, by rfl⟩ : syracuseStep 2033399 = 3050099) B3050099
theorem B2033423 : Blo 1354996 2033423 := bstep (se 1 (by rfl) ⟨1525067, by rfl⟩ : syracuseStep 2033423 = 3050135) B3050135
theorem B5793569 : Blo 1354996 5793569 := bstep (se 2 (by rfl) ⟨2172588, by rfl⟩ : syracuseStep 5793569 = 4345177) B4345177
theorem B2033465 : Blo 1354996 2033465 := bstep (se 2 (by rfl) ⟨762549, by rfl⟩ : syracuseStep 2033465 = 1525099) B1525099
theorem B3434359 : Blo 1354996 3434359 := bstep (se 1 (by rfl) ⟨2575769, by rfl⟩ : syracuseStep 3434359 = 5151539) B5151539
theorem B2033543 : Blo 1354996 2033543 := bstep (se 1 (by rfl) ⟨1525157, by rfl⟩ : syracuseStep 2033543 = 3050315) B3050315
theorem B1525639 : Blo 1354996 1525639 := bstep (se 1 (by rfl) ⟨1144229, by rfl⟩ : syracuseStep 1525639 = 2288459) B2288459
theorem B2033579 : Blo 1354996 2033579 := bstep (se 1 (by rfl) ⟨1525184, by rfl⟩ : syracuseStep 2033579 = 3050369) B3050369
theorem B2287561 : Blo 1354996 2287561 := bstep (se 2 (by rfl) ⟨857835, by rfl⟩ : syracuseStep 2287561 = 1715671) B1715671
theorem B2033609 : Blo 1354996 2033609 := bstep (se 2 (by rfl) ⟨762603, by rfl⟩ : syracuseStep 2033609 = 1525207) B1525207
theorem B2574281 : Blo 1354996 2574281 := bstep (se 2 (by rfl) ⟨965355, by rfl⟩ : syracuseStep 2574281 = 1930711) B1930711
theorem B3049487 : Blo 1354996 3049487 := bstep (se 1 (by rfl) ⟨2287115, by rfl⟩ : syracuseStep 3049487 = 4574231) B4574231
theorem B3049505 : Blo 1354996 3049505 := bstep (se 2 (by rfl) ⟨1143564, by rfl⟩ : syracuseStep 3049505 = 2287129) B2287129
theorem B2033723 : Blo 1354996 2033723 := bstep (se 1 (by rfl) ⟨1525292, by rfl⟩ : syracuseStep 2033723 = 3050585) B3050585
theorem B1525819 : Blo 1354996 1525819 := bstep (se 1 (by rfl) ⟨1144364, by rfl⟩ : syracuseStep 1525819 = 2288729) B2288729
theorem B11577431 : Blo 1354996 11577431 := bstep (se 1 (by rfl) ⟨8683073, by rfl⟩ : syracuseStep 11577431 = 17366147) B17366147
theorem B2033783 : Blo 1354996 2033783 := bstep (se 1 (by rfl) ⟨1525337, by rfl⟩ : syracuseStep 2033783 = 3050675) B3050675
theorem B2033807 : Blo 1354996 2033807 := bstep (se 1 (by rfl) ⟨1525355, by rfl⟩ : syracuseStep 2033807 = 3050711) B3050711
theorem B2033849 : Blo 1354996 2033849 := bstep (se 2 (by rfl) ⟨762693, by rfl⟩ : syracuseStep 2033849 = 1525387) B1525387
theorem B5146861 : Blo 1354996 5146861 := bstep (se 3 (by rfl) ⟨965036, by rfl⟩ : syracuseStep 5146861 = 1930073) B1930073
theorem B2033927 : Blo 1354996 2033927 := bstep (se 1 (by rfl) ⟨1525445, by rfl⟩ : syracuseStep 2033927 = 3050891) B3050891
theorem B2033963 : Blo 1354996 2033963 := bstep (se 1 (by rfl) ⟨1525472, by rfl⟩ : syracuseStep 2033963 = 3050945) B3050945
theorem B3434795 : Blo 1354996 3434795 := bstep (se 1 (by rfl) ⟨2576096, by rfl⟩ : syracuseStep 3434795 = 5152193) B5152193
theorem B2033993 : Blo 1354996 2033993 := bstep (se 2 (by rfl) ⟨762747, by rfl⟩ : syracuseStep 2033993 = 1525495) B1525495
theorem B3049847 : Blo 1354996 3049847 := bstep (se 1 (by rfl) ⟨2287385, by rfl⟩ : syracuseStep 3049847 = 4574771) B4574771
theorem B5794183 : Blo 1354996 5794183 := bstep (se 1 (by rfl) ⟨4345637, by rfl⟩ : syracuseStep 5794183 = 8691275) B8691275
theorem B3860921 : Blo 1354996 3860921 := bstep (se 2 (by rfl) ⟨1447845, by rfl⟩ : syracuseStep 3860921 = 2895691) B2895691
theorem B2034107 : Blo 1354996 2034107 := bstep (se 1 (by rfl) ⟨1525580, by rfl⟩ : syracuseStep 2034107 = 3051161) B3051161
theorem B2034167 : Blo 1354996 2034167 := bstep (se 1 (by rfl) ⟨1525625, by rfl⟩ : syracuseStep 2034167 = 3051251) B3051251
theorem B2034191 : Blo 1354996 2034191 := bstep (se 1 (by rfl) ⟨1525643, by rfl⟩ : syracuseStep 2034191 = 3051287) B3051287
theorem B1526287 : Blo 1354996 1526287 := bstep (se 1 (by rfl) ⟨1144715, by rfl⟩ : syracuseStep 1526287 = 2289431) B2289431
theorem B5147165 : Blo 1354996 5147165 := bstep (se 3 (by rfl) ⟨965093, by rfl⟩ : syracuseStep 5147165 = 1930187) B1930187
theorem B3050027 : Blo 1354996 3050027 := bstep (se 1 (by rfl) ⟨2287520, by rfl⟩ : syracuseStep 3050027 = 4575041) B4575041
theorem B2034233 : Blo 1354996 2034233 := bstep (se 2 (by rfl) ⟨762837, by rfl⟩ : syracuseStep 2034233 = 1525675) B1525675
theorem B2288263 : Blo 1354996 2288263 := bstep (se 1 (by rfl) ⟨1716197, by rfl⟩ : syracuseStep 2288263 = 3432395) B3432395
theorem B2034311 : Blo 1354996 2034311 := bstep (se 1 (by rfl) ⟨1525733, by rfl⟩ : syracuseStep 2034311 = 3051467) B3051467
theorem B2034347 : Blo 1354996 2034347 := bstep (se 1 (by rfl) ⟨1525760, by rfl⟩ : syracuseStep 2034347 = 3051521) B3051521
theorem B2034377 : Blo 1354996 2034377 := bstep (se 2 (by rfl) ⟨762891, by rfl⟩ : syracuseStep 2034377 = 1525783) B1525783
theorem B3861263 : Blo 1354996 3861263 := bstep (se 1 (by rfl) ⟨2895947, by rfl⟩ : syracuseStep 3861263 = 5791895) B5791895
theorem B2444075 : Blo 1354996 2444075 := bstep (se 1 (by rfl) ⟨1833056, by rfl⟩ : syracuseStep 2444075 = 3666113) B3666113
theorem B2575147 : Blo 1354996 2575147 := bstep (se 1 (by rfl) ⟨1931360, by rfl⟩ : syracuseStep 2575147 = 3862721) B3862721
theorem B7056179 : Blo 1354996 7056179 := bstep (se 1 (by rfl) ⟨5292134, by rfl⟩ : syracuseStep 7056179 = 10584269) B10584269
theorem B2034491 : Blo 1354996 2034491 := bstep (se 1 (by rfl) ⟨1525868, by rfl⟩ : syracuseStep 2034491 = 3051737) B3051737
theorem B8244083 : Blo 1354996 8244083 := bstep (se 1 (by rfl) ⟨6183062, by rfl⟩ : syracuseStep 8244083 = 12366125) B12366125
theorem B6867827 : Blo 1354996 6867827 := bstep (se 1 (by rfl) ⟨5150870, by rfl⟩ : syracuseStep 6867827 = 10301741) B10301741
theorem B2034551 : Blo 1354996 2034551 := bstep (se 1 (by rfl) ⟨1525913, by rfl⟩ : syracuseStep 2034551 = 3051827) B3051827
theorem B2575223 : Blo 1354996 2575223 := bstep (se 1 (by rfl) ⟨1931417, by rfl⟩ : syracuseStep 2575223 = 3862835) B3862835
theorem B2034575 : Blo 1354996 2034575 := bstep (se 1 (by rfl) ⟨1525931, by rfl⟩ : syracuseStep 2034575 = 3051863) B3051863
theorem B3050387 : Blo 1354996 3050387 := bstep (se 1 (by rfl) ⟨2287790, by rfl⟩ : syracuseStep 3050387 = 4575581) B4575581
theorem B45796259 : Blo 1354996 45796259 := bstep (se 1 (by rfl) ⟨34347194, by rfl⟩ : syracuseStep 45796259 = 68694389) B68694389
theorem B2034617 : Blo 1354996 2034617 := bstep (se 2 (by rfl) ⟨762981, by rfl⟩ : syracuseStep 2034617 = 1525963) B1525963
theorem B3050441 : Blo 1354996 3050441 := bstep (se 2 (by rfl) ⟨1143915, by rfl⟩ : syracuseStep 3050441 = 2287831) B2287831
theorem B2034695 : Blo 1354996 2034695 := bstep (se 1 (by rfl) ⟨1526021, by rfl⟩ : syracuseStep 2034695 = 3052043) B3052043
theorem B2034731 : Blo 1354996 2034731 := bstep (se 1 (by rfl) ⟨1526048, by rfl⟩ : syracuseStep 2034731 = 3052097) B3052097
theorem B2034761 : Blo 1354996 2034761 := bstep (se 2 (by rfl) ⟨763035, by rfl⟩ : syracuseStep 2034761 = 1526071) B1526071
theorem B2034875 : Blo 1354996 2034875 := bstep (se 1 (by rfl) ⟨1526156, by rfl⟩ : syracuseStep 2034875 = 3052313) B3052313
theorem B2034935 : Blo 1354996 2034935 := bstep (se 1 (by rfl) ⟨1526201, by rfl⟩ : syracuseStep 2034935 = 3052403) B3052403
theorem B1355015 : Blo 1354996 1355015 := bstep (se 1 (by rfl) ⟨1016261, by rfl⟩ : syracuseStep 1355015 = 2032523) B2032523
theorem B1355023 : Blo 1354996 1355023 := bstep (se 1 (by rfl) ⟨1016267, by rfl⟩ : syracuseStep 1355023 = 2032535) B2032535
theorem B2288911 : Blo 1354996 2288911 := bstep (se 1 (by rfl) ⟨1716683, by rfl⟩ : syracuseStep 2288911 = 3433367) B3433367
theorem B2034959 : Blo 1354996 2034959 := bstep (se 1 (by rfl) ⟨1526219, by rfl⟩ : syracuseStep 2034959 = 3052439) B3052439
theorem B2035001 : Blo 1354996 2035001 := bstep (se 2 (by rfl) ⟨763125, by rfl⟩ : syracuseStep 2035001 = 1526251) B1526251
theorem B1355067 : Blo 1354996 1355067 := bstep (se 1 (by rfl) ⟨1016300, by rfl⟩ : syracuseStep 1355067 = 2032601) B2032601
theorem B1740091 : Blo 1354996 1740091 := bstep (se 1 (by rfl) ⟨1305068, by rfl⟩ : syracuseStep 1740091 = 2610137) B2610137
theorem B6868313 : Blo 1354996 6868313 := bstep (se 2 (by rfl) ⟨2575617, by rfl⟩ : syracuseStep 6868313 = 5151235) B5151235
theorem B27823459 : Blo 1354996 27823459 := bstep (se 1 (by rfl) ⟨20867594, by rfl⟩ : syracuseStep 27823459 = 41735189) B41735189
theorem B1715575 : Blo 1354996 1715575 := bstep (se 1 (by rfl) ⟨1286681, by rfl⟩ : syracuseStep 1715575 = 2573363) B2573363
theorem B1355143 : Blo 1354996 1355143 := bstep (se 1 (by rfl) ⟨1016357, by rfl⟩ : syracuseStep 1355143 = 2032715) B2032715
theorem B2895239 : Blo 1354996 2895239 := bstep (se 1 (by rfl) ⟨2171429, by rfl⟩ : syracuseStep 2895239 = 4342859) B4342859
theorem B2035079 : Blo 1354996 2035079 := bstep (se 1 (by rfl) ⟨1526309, by rfl⟩ : syracuseStep 2035079 = 3052619) B3052619
theorem B1355151 : Blo 1354996 1355151 := bstep (se 1 (by rfl) ⟨1016363, by rfl⟩ : syracuseStep 1355151 = 2032727) B2032727
theorem B2035115 : Blo 1354996 2035115 := bstep (se 1 (by rfl) ⟨1526336, by rfl⟩ : syracuseStep 2035115 = 3052673) B3052673
theorem B1355195 : Blo 1354996 1355195 := bstep (se 1 (by rfl) ⟨1016396, by rfl⟩ : syracuseStep 1355195 = 2032793) B2032793
theorem B2035145 : Blo 1354996 2035145 := bstep (se 2 (by rfl) ⟨763179, by rfl⟩ : syracuseStep 2035145 = 1526359) B1526359
theorem B6516227 : Blo 1354996 6516227 := bstep (se 1 (by rfl) ⟨4887170, by rfl⟩ : syracuseStep 6516227 = 9774341) B9774341
theorem B1355271 : Blo 1354996 1355271 := bstep (se 1 (by rfl) ⟨1016453, by rfl⟩ : syracuseStep 1355271 = 2032907) B2032907
theorem B1355279 : Blo 1354996 1355279 := bstep (se 1 (by rfl) ⟨1016459, by rfl⟩ : syracuseStep 1355279 = 2032919) B2032919
theorem B15650333 : Blo 1354996 15650333 := bstep (se 3 (by rfl) ⟨2934437, by rfl⟩ : syracuseStep 15650333 = 5868875) B5868875
theorem B1355323 : Blo 1354996 1355323 := bstep (se 1 (by rfl) ⟨1016492, by rfl⟩ : syracuseStep 1355323 = 2032985) B2032985
theorem B2035259 : Blo 1354996 2035259 := bstep (se 1 (by rfl) ⟨1526444, by rfl⟩ : syracuseStep 2035259 = 3052889) B3052889
theorem B6860375 : Blo 1354996 6860375 := bstep (se 1 (by rfl) ⟨5145281, by rfl⟩ : syracuseStep 6860375 = 10290563) B10290563
theorem B2035319 : Blo 1354996 2035319 := bstep (se 1 (by rfl) ⟨1526489, by rfl⟩ : syracuseStep 2035319 = 3052979) B3052979
theorem B1355399 : Blo 1354996 1355399 := bstep (se 1 (by rfl) ⟨1016549, by rfl⟩ : syracuseStep 1355399 = 2033099) B2033099
theorem B3051143 : Blo 1354996 3051143 := bstep (se 1 (by rfl) ⟨2288357, by rfl⟩ : syracuseStep 3051143 = 4576715) B4576715
theorem B3862151 : Blo 1354996 3862151 := bstep (se 1 (by rfl) ⟨2896613, by rfl⟩ : syracuseStep 3862151 = 5793227) B5793227
theorem B1355407 : Blo 1354996 1355407 := bstep (se 1 (by rfl) ⟨1016555, by rfl⟩ : syracuseStep 1355407 = 2033111) B2033111
theorem B2035343 : Blo 1354996 2035343 := bstep (se 1 (by rfl) ⟨1526507, by rfl⟩ : syracuseStep 2035343 = 3053015) B3053015
theorem B2035385 : Blo 1354996 2035385 := bstep (se 2 (by rfl) ⟨763269, by rfl⟩ : syracuseStep 2035385 = 1526539) B1526539
theorem B1355451 : Blo 1354996 1355451 := bstep (se 1 (by rfl) ⟨1016588, by rfl⟩ : syracuseStep 1355451 = 2033177) B2033177
theorem B1715899 : Blo 1354996 1715899 := bstep (se 1 (by rfl) ⟨1286924, by rfl⟩ : syracuseStep 1715899 = 2573849) B2573849
theorem B87928577 : Blo 1354996 87928577 := bstep (se 2 (by rfl) ⟨32973216, by rfl⟩ : syracuseStep 87928577 = 65946433) B65946433
theorem B10292993 : Blo 1354996 10292993 := bstep (se 2 (by rfl) ⟨3859872, by rfl⟩ : syracuseStep 10292993 = 7719745) B7719745
theorem B1355527 : Blo 1354996 1355527 := bstep (se 1 (by rfl) ⟨1016645, by rfl⟩ : syracuseStep 1355527 = 2033291) B2033291
theorem B2035463 : Blo 1354996 2035463 := bstep (se 1 (by rfl) ⟨1526597, by rfl⟩ : syracuseStep 2035463 = 3053195) B3053195
theorem B1355535 : Blo 1354996 1355535 := bstep (se 1 (by rfl) ⟨1016651, by rfl⟩ : syracuseStep 1355535 = 2033303) B2033303
theorem B2289451 : Blo 1354996 2289451 := bstep (se 1 (by rfl) ⟨1717088, by rfl⟩ : syracuseStep 2289451 = 3434177) B3434177
theorem B1355579 : Blo 1354996 1355579 := bstep (se 1 (by rfl) ⟨1016684, by rfl⟩ : syracuseStep 1355579 = 2033369) B2033369
theorem B3051323 : Blo 1354996 3051323 := bstep (se 1 (by rfl) ⟨2288492, by rfl⟩ : syracuseStep 3051323 = 4576985) B4576985
theorem B3862333 : Blo 1354996 3862333 := bstep (se 3 (by rfl) ⟨724187, by rfl⟩ : syracuseStep 3862333 = 1448375) B1448375
theorem B1355655 : Blo 1354996 1355655 := bstep (se 1 (by rfl) ⟨1016741, by rfl⟩ : syracuseStep 1355655 = 2033483) B2033483
theorem B1355663 : Blo 1354996 1355663 := bstep (se 1 (by rfl) ⟨1016747, by rfl⟩ : syracuseStep 1355663 = 2033495) B2033495
theorem B3051449 : Blo 1354996 3051449 := bstep (se 2 (by rfl) ⟨1144293, by rfl⟩ : syracuseStep 3051449 = 2288587) B2288587
theorem B2289593 : Blo 1354996 2289593 := bstep (se 2 (by rfl) ⟨858597, by rfl⟩ : syracuseStep 2289593 = 1717195) B1717195
theorem B1355707 : Blo 1354996 1355707 := bstep (se 1 (by rfl) ⟨1016780, by rfl⟩ : syracuseStep 1355707 = 2033561) B2033561
theorem B1355783 : Blo 1354996 1355783 := bstep (se 1 (by rfl) ⟨1016837, by rfl⟩ : syracuseStep 1355783 = 2033675) B2033675
theorem B1355791 : Blo 1354996 1355791 := bstep (se 1 (by rfl) ⟨1016843, by rfl⟩ : syracuseStep 1355791 = 2033687) B2033687
theorem B3862561 : Blo 1354996 3862561 := bstep (se 2 (by rfl) ⟨1448460, by rfl⟩ : syracuseStep 3862561 = 2896921) B2896921
theorem B1355835 : Blo 1354996 1355835 := bstep (se 1 (by rfl) ⟨1016876, by rfl⟩ : syracuseStep 1355835 = 2033753) B2033753
theorem B6860861 : Blo 1354996 6860861 := bstep (se 3 (by rfl) ⟨1286411, by rfl⟩ : syracuseStep 6860861 = 2572823) B2572823
theorem B7721021 : Blo 1354996 7721021 := bstep (se 3 (by rfl) ⟨1447691, by rfl⟩ : syracuseStep 7721021 = 2895383) B2895383
theorem B5148791 : Blo 1354996 5148791 := bstep (se 1 (by rfl) ⟨3861593, by rfl⟩ : syracuseStep 5148791 = 7723187) B7723187
theorem B1355911 : Blo 1354996 1355911 := bstep (se 1 (by rfl) ⟨1016933, by rfl⟩ : syracuseStep 1355911 = 2033867) B2033867
theorem B1355919 : Blo 1354996 1355919 := bstep (se 1 (by rfl) ⟨1016939, by rfl⟩ : syracuseStep 1355919 = 2033879) B2033879
theorem B1355963 : Blo 1354996 1355963 := bstep (se 1 (by rfl) ⟨1016972, by rfl⟩ : syracuseStep 1355963 = 2033945) B2033945
theorem B3256577 : Blo 1354996 3256577 := bstep (se 2 (by rfl) ⟨1221216, by rfl⟩ : syracuseStep 3256577 = 2442433) B2442433
theorem B1356039 : Blo 1354996 1356039 := bstep (se 1 (by rfl) ⟨1017029, by rfl⟩ : syracuseStep 1356039 = 2034059) B2034059
theorem B1356047 : Blo 1354996 1356047 := bstep (se 1 (by rfl) ⟨1017035, by rfl⟩ : syracuseStep 1356047 = 2034071) B2034071
theorem B3051791 : Blo 1354996 3051791 := bstep (se 1 (by rfl) ⟨2288843, by rfl⟩ : syracuseStep 3051791 = 4577687) B4577687
theorem B3051809 : Blo 1354996 3051809 := bstep (se 2 (by rfl) ⟨1144428, by rfl⟩ : syracuseStep 3051809 = 2288857) B2288857
theorem B1356091 : Blo 1354996 1356091 := bstep (se 1 (by rfl) ⟨1017068, by rfl⟩ : syracuseStep 1356091 = 2034137) B2034137
theorem B3256691 : Blo 1354996 3256691 := bstep (se 1 (by rfl) ⟨2442518, by rfl⟩ : syracuseStep 3256691 = 4885037) B4885037
theorem B3862903 : Blo 1354996 3862903 := bstep (se 1 (by rfl) ⟨2897177, by rfl⟩ : syracuseStep 3862903 = 5794355) B5794355
theorem B1356167 : Blo 1354996 1356167 := bstep (se 1 (by rfl) ⟨1017125, by rfl⟩ : syracuseStep 1356167 = 2034251) B2034251
theorem B1356175 : Blo 1354996 1356175 := bstep (se 1 (by rfl) ⟨1017131, by rfl⟩ : syracuseStep 1356175 = 2034263) B2034263
theorem B4575635 : Blo 1354996 4575635 := bstep (se 1 (by rfl) ⟨3431726, by rfl⟩ : syracuseStep 4575635 = 6863453) B6863453
theorem B1356219 : Blo 1354996 1356219 := bstep (se 1 (by rfl) ⟨1017164, by rfl⟩ : syracuseStep 1356219 = 2034329) B2034329
theorem B1356295 : Blo 1354996 1356295 := bstep (se 1 (by rfl) ⟨1017221, by rfl⟩ : syracuseStep 1356295 = 2034443) B2034443
theorem B1356303 : Blo 1354996 1356303 := bstep (se 1 (by rfl) ⟨1017227, by rfl⟩ : syracuseStep 1356303 = 2034455) B2034455
theorem B3256865 : Blo 1354996 3256865 := bstep (se 2 (by rfl) ⟨1221324, by rfl⟩ : syracuseStep 3256865 = 2442649) B2442649
theorem B2748971 : Blo 1354996 2748971 := bstep (se 1 (by rfl) ⟨2061728, by rfl⟩ : syracuseStep 2748971 = 4123457) B4123457
theorem B1356347 : Blo 1354996 1356347 := bstep (se 1 (by rfl) ⟨1017260, by rfl⟩ : syracuseStep 1356347 = 2034521) B2034521
theorem B3052151 : Blo 1354996 3052151 := bstep (se 1 (by rfl) ⟨2289113, by rfl⟩ : syracuseStep 3052151 = 4578227) B4578227
theorem B1356423 : Blo 1354996 1356423 := bstep (se 1 (by rfl) ⟨1017317, by rfl⟩ : syracuseStep 1356423 = 2034635) B2034635
theorem B1716871 : Blo 1354996 1716871 := bstep (se 1 (by rfl) ⟨1287653, by rfl⟩ : syracuseStep 1716871 = 2575307) B2575307
theorem B1356431 : Blo 1354996 1356431 := bstep (se 1 (by rfl) ⟨1017323, by rfl⟩ : syracuseStep 1356431 = 2034647) B2034647
theorem B6517421 : Blo 1354996 6517421 := bstep (se 3 (by rfl) ⟨1222016, by rfl⟩ : syracuseStep 6517421 = 2444033) B2444033
theorem B1831609 : Blo 1354996 1831609 := bstep (se 2 (by rfl) ⟨686853, by rfl⟩ : syracuseStep 1831609 = 1373707) B1373707
theorem B1356475 : Blo 1354996 1356475 := bstep (se 1 (by rfl) ⟨1017356, by rfl⟩ : syracuseStep 1356475 = 2034713) B2034713
theorem B7721729 : Blo 1354996 7721729 := bstep (se 2 (by rfl) ⟨2895648, by rfl⟩ : syracuseStep 7721729 = 5791297) B5791297
theorem B1356551 : Blo 1354996 1356551 := bstep (se 1 (by rfl) ⟨1017413, by rfl⟩ : syracuseStep 1356551 = 2034827) B2034827
theorem B1356559 : Blo 1354996 1356559 := bstep (se 1 (by rfl) ⟨1017419, by rfl⟩ : syracuseStep 1356559 = 2034839) B2034839
theorem B4125473 : Blo 1354996 4125473 := bstep (se 2 (by rfl) ⟨1547052, by rfl⟩ : syracuseStep 4125473 = 3094105) B3094105
theorem B3052331 : Blo 1354996 3052331 := bstep (se 1 (by rfl) ⟨2289248, by rfl⟩ : syracuseStep 3052331 = 4578497) B4578497
theorem B1356603 : Blo 1354996 1356603 := bstep (se 1 (by rfl) ⟨1017452, by rfl⟩ : syracuseStep 1356603 = 2034905) B2034905
theorem B1356679 : Blo 1354996 1356679 := bstep (se 1 (by rfl) ⟨1017509, by rfl⟩ : syracuseStep 1356679 = 2035019) B2035019
theorem B1356687 : Blo 1354996 1356687 := bstep (se 1 (by rfl) ⟨1017515, by rfl⟩ : syracuseStep 1356687 = 2035031) B2035031
theorem B1356731 : Blo 1354996 1356731 := bstep (se 1 (by rfl) ⟨1017548, by rfl⟩ : syracuseStep 1356731 = 2035097) B2035097
theorem B1356807 : Blo 1354996 1356807 := bstep (se 1 (by rfl) ⟨1017605, by rfl⟩ : syracuseStep 1356807 = 2035211) B2035211
theorem B1356815 : Blo 1354996 1356815 := bstep (se 1 (by rfl) ⟨1017611, by rfl⟩ : syracuseStep 1356815 = 2035223) B2035223
theorem B1717291 : Blo 1354996 1717291 := bstep (se 1 (by rfl) ⟨1287968, by rfl⟩ : syracuseStep 1717291 = 2575937) B2575937
theorem B1356859 : Blo 1354996 1356859 := bstep (se 1 (by rfl) ⟨1017644, by rfl⟩ : syracuseStep 1356859 = 2035289) B2035289
theorem B5149763 : Blo 1354996 5149763 := bstep (se 1 (by rfl) ⟨3862322, by rfl⟩ : syracuseStep 5149763 = 7724645) B7724645
theorem B1356935 : Blo 1354996 1356935 := bstep (se 1 (by rfl) ⟨1017701, by rfl⟩ : syracuseStep 1356935 = 2035403) B2035403
theorem B1356943 : Blo 1354996 1356943 := bstep (se 1 (by rfl) ⟨1017707, by rfl⟩ : syracuseStep 1356943 = 2035415) B2035415
theorem B3052691 : Blo 1354996 3052691 := bstep (se 1 (by rfl) ⟨2289518, by rfl⟩ : syracuseStep 3052691 = 4579037) B4579037
theorem B1356987 : Blo 1354996 1356987 := bstep (se 1 (by rfl) ⟨1017740, by rfl⟩ : syracuseStep 1356987 = 2035481) B2035481
theorem B3052745 : Blo 1354996 3052745 := bstep (se 2 (by rfl) ⟨1144779, by rfl⟩ : syracuseStep 3052745 = 2289559) B2289559
theorem B26055917 : Blo 1354996 26055917 := bstep (se 3 (by rfl) ⟨4885484, by rfl⟩ : syracuseStep 26055917 = 9770969) B9770969
theorem B3863837 : Blo 1354996 3863837 := bstep (se 3 (by rfl) ⟨724469, by rfl⟩ : syracuseStep 3863837 = 1448939) B1448939
theorem B3478817 : Blo 1354996 3478817 := bstep (se 2 (by rfl) ⟨1304556, by rfl⟩ : syracuseStep 3478817 = 2609113) B2609113
theorem B21976379 : Blo 1354996 21976379 := bstep (se 1 (by rfl) ⟨16482284, by rfl⟩ : syracuseStep 21976379 = 32964569) B32964569
theorem B7329113 : Blo 1354996 7329113 := bstep (se 2 (by rfl) ⟨2748417, by rfl⟩ : syracuseStep 7329113 = 5496835) B5496835
theorem B2061703 : Blo 1354996 2061703 := bstep (se 1 (by rfl) ⟨1546277, by rfl⟩ : syracuseStep 2061703 = 3092555) B3092555
theorem B29324753 : Blo 1354996 29324753 := bstep (se 2 (by rfl) ⟨10996782, by rfl⟩ : syracuseStep 29324753 = 21993565) B21993565
theorem B5789195 : Blo 1354996 5789195 := bstep (se 1 (by rfl) ⟨4341896, by rfl⟩ : syracuseStep 5789195 = 8683793) B8683793
theorem B1930825 : Blo 1354996 1930825 := bstep (se 2 (by rfl) ⟨724059, by rfl⟩ : syracuseStep 1930825 = 1448119) B1448119
theorem B3864179 : Blo 1354996 3864179 := bstep (se 1 (by rfl) ⟨2898134, by rfl⟩ : syracuseStep 3864179 = 5796269) B5796269
theorem B4577039 : Blo 1354996 4577039 := bstep (se 1 (by rfl) ⟨3432779, by rfl⟩ : syracuseStep 4577039 = 6865559) B6865559
theorem B2897707 : Blo 1354996 2897707 := bstep (se 1 (by rfl) ⟨2173280, by rfl⟩ : syracuseStep 2897707 = 4346561) B4346561
theorem B6862643 : Blo 1354996 6862643 := bstep (se 1 (by rfl) ⟨5146982, by rfl⟩ : syracuseStep 6862643 = 10293965) B10293965
theorem B12367667 : Blo 1354996 12367667 := bstep (se 1 (by rfl) ⟨9275750, by rfl⟩ : syracuseStep 12367667 = 18551501) B18551501
theorem B3430259 : Blo 1354996 3430259 := bstep (se 1 (by rfl) ⟨2572694, by rfl⟩ : syracuseStep 3430259 = 5145389) B5145389
theorem B4577309 : Blo 1354996 4577309 := bstep (se 3 (by rfl) ⟨858245, by rfl⟩ : syracuseStep 4577309 = 1716491) B1716491
theorem B5150749 : Blo 1354996 5150749 := bstep (se 3 (by rfl) ⟨965765, by rfl⟩ : syracuseStep 5150749 = 1931531) B1931531
theorem B19552373 : Blo 1354996 19552373 := bstep (se 5 (by rfl) ⟨916517, by rfl⟩ : syracuseStep 19552373 = 1833035) B1833035
theorem B6862967 : Blo 1354996 6862967 := bstep (se 1 (by rfl) ⟨5147225, by rfl⟩ : syracuseStep 6862967 = 10294451) B10294451
theorem B3479699 : Blo 1354996 3479699 := bstep (se 1 (by rfl) ⟨2609774, by rfl⟩ : syracuseStep 3479699 = 5219549) B5219549
theorem B16505005 : Blo 1354996 16505005 := bstep (se 3 (by rfl) ⟨3094688, by rfl⟩ : syracuseStep 16505005 = 6189377) B6189377
theorem B3430775 : Blo 1354996 3430775 := bstep (se 1 (by rfl) ⟨2573081, by rfl⟩ : syracuseStep 3430775 = 5146163) B5146163
theorem B1374607 : Blo 1354996 1374607 := bstep (se 1 (by rfl) ⟨1030955, by rfl⟩ : syracuseStep 1374607 = 2061911) B2061911
theorem B2062967 : Blo 1354996 2062967 := bstep (se 1 (by rfl) ⟨1547225, by rfl⟩ : syracuseStep 2062967 = 3094451) B3094451
theorem B1628807 : Blo 1354996 1628807 := bstep (se 1 (by rfl) ⟨1221605, by rfl⟩ : syracuseStep 1628807 = 2443211) B2443211
theorem B11909825 : Blo 1354996 11909825 := bstep (se 2 (by rfl) ⟨4466184, by rfl⟩ : syracuseStep 11909825 = 8932369) B8932369
theorem B1833787 : Blo 1354996 1833787 := bstep (se 1 (by rfl) ⟨1375340, by rfl⟩ : syracuseStep 1833787 = 2750681) B2750681
theorem B11590553 : Blo 1354996 11590553 := bstep (se 2 (by rfl) ⟨4346457, by rfl⟩ : syracuseStep 11590553 = 8692915) B8692915
theorem B6863939 : Blo 1354996 6863939 := bstep (se 1 (by rfl) ⟨5147954, by rfl⟩ : syracuseStep 6863939 = 10295909) B10295909
theorem B7724119 : Blo 1354996 7724119 := bstep (se 1 (by rfl) ⟨5793089, by rfl⟩ : syracuseStep 7724119 = 11586179) B11586179
theorem B11001005 : Blo 1354996 11001005 := bstep (se 3 (by rfl) ⟨2062688, by rfl⟩ : syracuseStep 11001005 = 4125377) B4125377
theorem B13909265 : Blo 1354996 13909265 := bstep (se 2 (by rfl) ⟨5215974, by rfl⟩ : syracuseStep 13909265 = 10431949) B10431949
theorem B3431767 : Blo 1354996 3431767 := bstep (se 1 (by rfl) ⟨2573825, by rfl⟩ : syracuseStep 3431767 = 5147651) B5147651
theorem B4341127 : Blo 1354996 4341127 := bstep (se 1 (by rfl) ⟨3255845, by rfl⟩ : syracuseStep 4341127 = 6511691) B6511691
theorem B6864263 : Blo 1354996 6864263 := bstep (se 1 (by rfl) ⟨5148197, by rfl⟩ : syracuseStep 6864263 = 10296395) B10296395
theorem B4578713 : Blo 1354996 4578713 := bstep (se 2 (by rfl) ⟨1717017, by rfl⟩ : syracuseStep 4578713 = 3434035) B3434035
theorem B12369485 : Blo 1354996 12369485 := bstep (se 3 (by rfl) ⟨2319278, by rfl⟩ : syracuseStep 12369485 = 4638557) B4638557
theorem B6520439 : Blo 1354996 6520439 := bstep (se 1 (by rfl) ⟨4890329, by rfl⟩ : syracuseStep 6520439 = 9780659) B9780659
theorem B3432071 : Blo 1354996 3432071 := bstep (se 1 (by rfl) ⟨2574053, by rfl⟩ : syracuseStep 3432071 = 5148107) B5148107
theorem B3432203 : Blo 1354996 3432203 := bstep (se 1 (by rfl) ⟨2574152, by rfl⟩ : syracuseStep 3432203 = 5148305) B5148305
theorem B4890401 : Blo 1354996 4890401 := bstep (se 2 (by rfl) ⟨1833900, by rfl⟩ : syracuseStep 4890401 = 3667801) B3667801
theorem B6520609 : Blo 1354996 6520609 := bstep (se 2 (by rfl) ⟨2445228, by rfl⟩ : syracuseStep 6520609 = 4890457) B4890457
theorem B2645879 : Blo 1354996 2645879 := bstep (se 1 (by rfl) ⟨1984409, by rfl⟩ : syracuseStep 2645879 = 3968819) B3968819
theorem B6512537 : Blo 1354996 6512537 := bstep (se 2 (by rfl) ⟨2442201, by rfl⟩ : syracuseStep 6512537 = 4884403) B4884403
theorem B9781145 : Blo 1354996 9781145 := bstep (se 2 (by rfl) ⟨3667929, by rfl⟩ : syracuseStep 9781145 = 7335859) B7335859
theorem B6864911 : Blo 1354996 6864911 := bstep (se 1 (by rfl) ⟨5148683, by rfl⟩ : syracuseStep 6864911 = 10297367) B10297367
theorem B3432527 : Blo 1354996 3432527 := bstep (se 1 (by rfl) ⟨2574395, by rfl⟩ : syracuseStep 3432527 = 5148791) B5148791
theorem B2171051 : Blo 1354996 2171051 := bstep (se 1 (by rfl) ⟨1628288, by rfl⟩ : syracuseStep 2171051 = 3256577) B3256577
theorem B2572535 : Blo 1354996 2572535 := bstep (se 1 (by rfl) ⟨1929401, by rfl⟩ : syracuseStep 2572535 = 3858803) B3858803
theorem B2171243 : Blo 1354996 2171243 := bstep (se 1 (by rfl) ⟨1628432, by rfl⟩ : syracuseStep 2171243 = 3256865) B3256865
theorem B7725577 : Blo 1354996 7725577 := bstep (se 2 (by rfl) ⟨2897091, by rfl⟩ : syracuseStep 7725577 = 5794183) B5794183
theorem B44597783 : Blo 1354996 44597783 := bstep (se 1 (by rfl) ⟨33448337, by rfl⟩ : syracuseStep 44597783 = 66896675) B66896675
theorem B3433175 : Blo 1354996 3433175 := bstep (se 1 (by rfl) ⟨2574881, by rfl⟩ : syracuseStep 3433175 = 5149763) B5149763
theorem B2319211 : Blo 1354996 2319211 := bstep (se 1 (by rfl) ⟨1739408, by rfl⟩ : syracuseStep 2319211 = 3478817) B3478817
theorem B2442145 : Blo 1354996 2442145 := bstep (se 2 (by rfl) ⟨915804, by rfl⟩ : syracuseStep 2442145 = 1831609) B1831609
theorem B2032559 : Blo 1354996 2032559 := bstep (se 1 (by rfl) ⟨1524419, by rfl⟩ : syracuseStep 2032559 = 3048839) B3048839
theorem B8684509 : Blo 1354996 8684509 := bstep (se 3 (by rfl) ⟨1628345, by rfl⟩ : syracuseStep 8684509 = 3256691) B3256691
theorem B3859463 : Blo 1354996 3859463 := bstep (se 1 (by rfl) ⟨2894597, by rfl⟩ : syracuseStep 3859463 = 5789195) B5789195
theorem B2032649 : Blo 1354996 2032649 := bstep (se 2 (by rfl) ⟨762243, by rfl⟩ : syracuseStep 2032649 = 1524487) B1524487
theorem B2032679 : Blo 1354996 2032679 := bstep (se 1 (by rfl) ⟨1524509, by rfl⟩ : syracuseStep 2032679 = 3049019) B3049019
theorem B1524775 : Blo 1354996 1524775 := bstep (se 1 (by rfl) ⟨1143581, by rfl⟩ : syracuseStep 1524775 = 2287163) B2287163
theorem B3433529 : Blo 1354996 3433529 := bstep (se 2 (by rfl) ⟨1287573, by rfl⟩ : syracuseStep 3433529 = 2575147) B2575147
theorem B8930371 : Blo 1354996 8930371 := bstep (se 1 (by rfl) ⟨6697778, by rfl⟩ : syracuseStep 8930371 = 13395557) B13395557
theorem B4883537 : Blo 1354996 4883537 := bstep (se 2 (by rfl) ⟨1831326, by rfl⟩ : syracuseStep 4883537 = 3662653) B3662653
theorem B2032763 : Blo 1354996 2032763 := bstep (se 1 (by rfl) ⟨1524572, by rfl⟩ : syracuseStep 2032763 = 3049145) B3049145
theorem B2286839 : Blo 1354996 2286839 := bstep (se 1 (by rfl) ⟨1715129, by rfl⟩ : syracuseStep 2286839 = 3430259) B3430259
theorem B2032889 : Blo 1354996 2032889 := bstep (se 2 (by rfl) ⟨762333, by rfl⟩ : syracuseStep 2032889 = 1524667) B1524667
theorem B17376605 : Blo 1354996 17376605 := bstep (se 3 (by rfl) ⟨3258113, by rfl⟩ : syracuseStep 17376605 = 6516227) B6516227
theorem B2032991 : Blo 1354996 2032991 := bstep (se 1 (by rfl) ⟨1524743, by rfl⟩ : syracuseStep 2032991 = 3049487) B3049487
theorem B2033003 : Blo 1354996 2033003 := bstep (se 1 (by rfl) ⟨1524752, by rfl⟩ : syracuseStep 2033003 = 3049505) B3049505
theorem B7718287 : Blo 1354996 7718287 := bstep (se 1 (by rfl) ⟨5788715, by rfl⟩ : syracuseStep 7718287 = 11577431) B11577431
theorem B13034915 : Blo 1354996 13034915 := bstep (se 1 (by rfl) ⟨9776186, by rfl⟩ : syracuseStep 13034915 = 19552373) B19552373
theorem B10298825 : Blo 1354996 10298825 := bstep (se 2 (by rfl) ⟨3862059, by rfl⟩ : syracuseStep 10298825 = 7724119) B7724119
theorem B2287183 : Blo 1354996 2287183 := bstep (se 1 (by rfl) ⟨1715387, by rfl⟩ : syracuseStep 2287183 = 3430775) B3430775
theorem B2033231 : Blo 1354996 2033231 := bstep (se 1 (by rfl) ⟨1524923, by rfl⟩ : syracuseStep 2033231 = 3049847) B3049847
theorem B2573947 : Blo 1354996 2573947 := bstep (se 1 (by rfl) ⟨1930460, by rfl⟩ : syracuseStep 2573947 = 3860921) B3860921
theorem B4343485 : Blo 1354996 4343485 := bstep (se 3 (by rfl) ⟨814403, by rfl⟩ : syracuseStep 4343485 = 1628807) B1628807
theorem B2033351 : Blo 1354996 2033351 := bstep (se 1 (by rfl) ⟨1525013, by rfl⟩ : syracuseStep 2033351 = 3050027) B3050027
theorem B5146361 : Blo 1354996 5146361 := bstep (se 2 (by rfl) ⟨1929885, by rfl⟩ : syracuseStep 5146361 = 3859771) B3859771
theorem B2320121 : Blo 1354996 2320121 := bstep (se 2 (by rfl) ⟨870045, by rfl⟩ : syracuseStep 2320121 = 1740091) B1740091
theorem B7939883 : Blo 1354996 7939883 := bstep (se 1 (by rfl) ⟨5954912, by rfl⟩ : syracuseStep 7939883 = 11909825) B11909825
theorem B3049289 : Blo 1354996 3049289 := bstep (se 2 (by rfl) ⟨1143483, by rfl⟩ : syracuseStep 3049289 = 2286967) B2286967
theorem B2287433 : Blo 1354996 2287433 := bstep (se 2 (by rfl) ⟨857787, by rfl⟩ : syracuseStep 2287433 = 1715575) B1715575
theorem B2574175 : Blo 1354996 2574175 := bstep (se 1 (by rfl) ⟨1930631, by rfl⟩ : syracuseStep 2574175 = 3861263) B3861263
theorem B2033513 : Blo 1354996 2033513 := bstep (se 2 (by rfl) ⟨762567, by rfl⟩ : syracuseStep 2033513 = 1525135) B1525135
theorem B4704119 : Blo 1354996 4704119 := bstep (se 1 (by rfl) ⟨3528089, by rfl⟩ : syracuseStep 4704119 = 7056179) B7056179
theorem B2033591 : Blo 1354996 2033591 := bstep (se 1 (by rfl) ⟨1525193, by rfl⟩ : syracuseStep 2033591 = 3050387) B3050387
theorem B7727035 : Blo 1354996 7727035 := bstep (se 1 (by rfl) ⟨5795276, by rfl⟩ : syracuseStep 7727035 = 11590553) B11590553
theorem B2033627 : Blo 1354996 2033627 := bstep (se 1 (by rfl) ⟨1525220, by rfl⟩ : syracuseStep 2033627 = 3050441) B3050441
theorem B10995749 : Blo 1354996 10995749 := bstep (se 4 (by rfl) ⟨1030851, by rfl⟩ : syracuseStep 10995749 = 2061703) B2061703
theorem B35719261 : Blo 1354996 35719261 := bstep (se 3 (by rfl) ⟨6697361, by rfl⟩ : syracuseStep 35719261 = 13394723) B13394723
theorem B2574433 : Blo 1354996 2574433 := bstep (se 2 (by rfl) ⟨965412, by rfl⟩ : syracuseStep 2574433 = 1930825) B1930825
theorem B7334003 : Blo 1354996 7334003 := bstep (se 1 (by rfl) ⟨5500502, by rfl⟩ : syracuseStep 7334003 = 11001005) B11001005
theorem B2287865 : Blo 1354996 2287865 := bstep (se 2 (by rfl) ⟨857949, by rfl⟩ : syracuseStep 2287865 = 1715899) B1715899
theorem B63473969 : Blo 1354996 63473969 := bstep (se 2 (by rfl) ⟨23802738, by rfl⟩ : syracuseStep 63473969 = 47605477) B47605477
theorem B7055677 : Blo 1354996 7055677 := bstep (se 3 (by rfl) ⟨1322939, by rfl⟩ : syracuseStep 7055677 = 2645879) B2645879
theorem B8694145 : Blo 1354996 8694145 := bstep (se 2 (by rfl) ⟨3260304, by rfl⟩ : syracuseStep 8694145 = 6520609) B6520609
theorem B4573583 : Blo 1354996 4573583 := bstep (se 1 (by rfl) ⟨3430187, by rfl⟩ : syracuseStep 4573583 = 6860375) B6860375
theorem B2288047 : Blo 1354996 2288047 := bstep (se 1 (by rfl) ⟨1716035, by rfl⟩ : syracuseStep 2288047 = 3432071) B3432071
theorem B2034095 : Blo 1354996 2034095 := bstep (se 1 (by rfl) ⟨1525571, by rfl⟩ : syracuseStep 2034095 = 3051143) B3051143
theorem B2574767 : Blo 1354996 2574767 := bstep (se 1 (by rfl) ⟨1931075, by rfl⟩ : syracuseStep 2574767 = 3862151) B3862151
theorem B2288135 : Blo 1354996 2288135 := bstep (se 1 (by rfl) ⟨1716101, by rfl⟩ : syracuseStep 2288135 = 3432203) B3432203
theorem B2034185 : Blo 1354996 2034185 := bstep (se 2 (by rfl) ⟨762819, by rfl⟩ : syracuseStep 2034185 = 1525639) B1525639
theorem B2034215 : Blo 1354996 2034215 := bstep (se 1 (by rfl) ⟨1525661, by rfl⟩ : syracuseStep 2034215 = 3051323) B3051323
theorem B3050081 : Blo 1354996 3050081 := bstep (se 2 (by rfl) ⟨1143780, by rfl⟩ : syracuseStep 3050081 = 2287561) B2287561
theorem B2034299 : Blo 1354996 2034299 := bstep (se 1 (by rfl) ⟨1525724, by rfl⟩ : syracuseStep 2034299 = 3051449) B3051449
theorem B1526395 : Blo 1354996 1526395 := bstep (se 1 (by rfl) ⟨1144796, by rfl⟩ : syracuseStep 1526395 = 2289593) B2289593
theorem B2173639 : Blo 1354996 2173639 := bstep (se 1 (by rfl) ⟨1630229, by rfl⟩ : syracuseStep 2173639 = 3260459) B3260459
theorem B6867665 : Blo 1354996 6867665 := bstep (se 2 (by rfl) ⟨2575374, by rfl⟩ : syracuseStep 6867665 = 5150749) B5150749
theorem B4573907 : Blo 1354996 4573907 := bstep (se 1 (by rfl) ⟨3430430, by rfl⟩ : syracuseStep 4573907 = 6860861) B6860861
theorem B5147347 : Blo 1354996 5147347 := bstep (se 1 (by rfl) ⟨3860510, by rfl⟩ : syracuseStep 5147347 = 7721021) B7721021
theorem B2034425 : Blo 1354996 2034425 := bstep (se 2 (by rfl) ⟨762909, by rfl⟩ : syracuseStep 2034425 = 1525819) B1525819
theorem B2288479 : Blo 1354996 2288479 := bstep (se 1 (by rfl) ⟨1716359, by rfl⟩ : syracuseStep 2288479 = 3432719) B3432719
theorem B2034527 : Blo 1354996 2034527 := bstep (se 1 (by rfl) ⟨1525895, by rfl⟩ : syracuseStep 2034527 = 3051791) B3051791
theorem B2034539 : Blo 1354996 2034539 := bstep (se 1 (by rfl) ⟨1525904, by rfl⟩ : syracuseStep 2034539 = 3051809) B3051809
theorem B22006673 : Blo 1354996 22006673 := bstep (se 2 (by rfl) ⟨8252502, by rfl⟩ : syracuseStep 22006673 = 16505005) B16505005
theorem B3050423 : Blo 1354996 3050423 := bstep (se 1 (by rfl) ⟨2287817, by rfl⟩ : syracuseStep 3050423 = 4575635) B4575635
theorem B2288567 : Blo 1354996 2288567 := bstep (se 1 (by rfl) ⟨1716425, by rfl⟩ : syracuseStep 2288567 = 3432851) B3432851
theorem B2034767 : Blo 1354996 2034767 := bstep (se 1 (by rfl) ⟨1526075, by rfl⟩ : syracuseStep 2034767 = 3052151) B3052151
theorem B4344947 : Blo 1354996 4344947 := bstep (se 1 (by rfl) ⟨3258710, by rfl⟩ : syracuseStep 4344947 = 6517421) B6517421
theorem B26070133 : Blo 1354996 26070133 := bstep (se 5 (by rfl) ⟨1222037, by rfl⟩ : syracuseStep 26070133 = 2444075) B2444075
theorem B5147819 : Blo 1354996 5147819 := bstep (se 1 (by rfl) ⟨3860864, by rfl⟩ : syracuseStep 5147819 = 7721729) B7721729
theorem B2034887 : Blo 1354996 2034887 := bstep (se 1 (by rfl) ⟨1526165, by rfl⟩ : syracuseStep 2034887 = 3052331) B3052331
theorem B1355047 : Blo 1354996 1355047 := bstep (se 1 (by rfl) ⟨1016285, by rfl⟩ : syracuseStep 1355047 = 2032571) B2032571
theorem B1355087 : Blo 1354996 1355087 := bstep (se 1 (by rfl) ⟨1016315, by rfl⟩ : syracuseStep 1355087 = 2032631) B2032631
theorem B1355103 : Blo 1354996 1355103 := bstep (se 1 (by rfl) ⟨1016327, by rfl⟩ : syracuseStep 1355103 = 2032655) B2032655
theorem B2035049 : Blo 1354996 2035049 := bstep (se 2 (by rfl) ⟨763143, by rfl⟩ : syracuseStep 2035049 = 1526287) B1526287
theorem B1355131 : Blo 1354996 1355131 := bstep (se 1 (by rfl) ⟨1016348, by rfl⟩ : syracuseStep 1355131 = 2032697) B2032697
theorem B1355183 : Blo 1354996 1355183 := bstep (se 1 (by rfl) ⟨1016387, by rfl⟩ : syracuseStep 1355183 = 2032775) B2032775
theorem B2035127 : Blo 1354996 2035127 := bstep (se 1 (by rfl) ⟨1526345, by rfl⟩ : syracuseStep 2035127 = 3052691) B3052691
theorem B1355207 : Blo 1354996 1355207 := bstep (se 1 (by rfl) ⟨1016405, by rfl⟩ : syracuseStep 1355207 = 2032811) B2032811
theorem B1355227 : Blo 1354996 1355227 := bstep (se 1 (by rfl) ⟨1016420, by rfl⟩ : syracuseStep 1355227 = 2032841) B2032841
theorem B2035163 : Blo 1354996 2035163 := bstep (se 1 (by rfl) ⟨1526372, by rfl⟩ : syracuseStep 2035163 = 3052745) B3052745
theorem B17370611 : Blo 1354996 17370611 := bstep (se 1 (by rfl) ⟨13027958, by rfl⟩ : syracuseStep 17370611 = 26055917) B26055917
theorem B3051017 : Blo 1354996 3051017 := bstep (se 2 (by rfl) ⟨1144131, by rfl⟩ : syracuseStep 3051017 = 2288263) B2288263
theorem B2289161 : Blo 1354996 2289161 := bstep (se 2 (by rfl) ⟨858435, by rfl⟩ : syracuseStep 2289161 = 1716871) B1716871
theorem B2575891 : Blo 1354996 2575891 := bstep (se 1 (by rfl) ⟨1931918, by rfl⟩ : syracuseStep 2575891 = 3863837) B3863837
theorem B14650919 : Blo 1354996 14650919 := bstep (se 1 (by rfl) ⟨10988189, by rfl⟩ : syracuseStep 14650919 = 21976379) B21976379
theorem B1355303 : Blo 1354996 1355303 := bstep (se 1 (by rfl) ⟨1016477, by rfl⟩ : syracuseStep 1355303 = 2032955) B2032955
theorem B4886075 : Blo 1354996 4886075 := bstep (se 1 (by rfl) ⟨3664556, by rfl⟩ : syracuseStep 4886075 = 7329113) B7329113
theorem B1355343 : Blo 1354996 1355343 := bstep (se 1 (by rfl) ⟨1016507, by rfl⟩ : syracuseStep 1355343 = 2033015) B2033015
theorem B1355359 : Blo 1354996 1355359 := bstep (se 1 (by rfl) ⟨1016519, by rfl⟩ : syracuseStep 1355359 = 2033039) B2033039
theorem B1355387 : Blo 1354996 1355387 := bstep (se 1 (by rfl) ⟨1016540, by rfl⟩ : syracuseStep 1355387 = 2033081) B2033081
theorem B19549835 : Blo 1354996 19549835 := bstep (se 1 (by rfl) ⟨14662376, by rfl⟩ : syracuseStep 19549835 = 29324753) B29324753
theorem B2289323 : Blo 1354996 2289323 := bstep (se 1 (by rfl) ⟨1716992, by rfl⟩ : syracuseStep 2289323 = 3433985) B3433985
theorem B1355439 : Blo 1354996 1355439 := bstep (se 1 (by rfl) ⟨1016579, by rfl⟩ : syracuseStep 1355439 = 2033159) B2033159
theorem B1355463 : Blo 1354996 1355463 := bstep (se 1 (by rfl) ⟨1016597, by rfl⟩ : syracuseStep 1355463 = 2033195) B2033195
theorem B1355483 : Blo 1354996 1355483 := bstep (se 1 (by rfl) ⟨1016612, by rfl⟩ : syracuseStep 1355483 = 2033225) B2033225
theorem B2576119 : Blo 1354996 2576119 := bstep (se 1 (by rfl) ⟨1932089, by rfl⟩ : syracuseStep 2576119 = 3864179) B3864179
theorem B6860537 : Blo 1354996 6860537 := bstep (se 2 (by rfl) ⟨2572701, by rfl⟩ : syracuseStep 6860537 = 5145403) B5145403
theorem B2445049 : Blo 1354996 2445049 := bstep (se 2 (by rfl) ⟨916893, by rfl⟩ : syracuseStep 2445049 = 1833787) B1833787
theorem B1355559 : Blo 1354996 1355559 := bstep (se 1 (by rfl) ⟨1016669, by rfl⟩ : syracuseStep 1355559 = 2033339) B2033339
theorem B1355599 : Blo 1354996 1355599 := bstep (se 1 (by rfl) ⟨1016699, by rfl⟩ : syracuseStep 1355599 = 2033399) B2033399
theorem B1355615 : Blo 1354996 1355615 := bstep (se 1 (by rfl) ⟨1016711, by rfl⟩ : syracuseStep 1355615 = 2033423) B2033423
theorem B3051359 : Blo 1354996 3051359 := bstep (se 1 (by rfl) ⟨2288519, by rfl⟩ : syracuseStep 3051359 = 4577039) B4577039
theorem B3862379 : Blo 1354996 3862379 := bstep (se 1 (by rfl) ⟨2896784, by rfl⟩ : syracuseStep 3862379 = 5793569) B5793569
theorem B4575095 : Blo 1354996 4575095 := bstep (se 1 (by rfl) ⟨3431321, by rfl⟩ : syracuseStep 4575095 = 6862643) B6862643
theorem B8245111 : Blo 1354996 8245111 := bstep (se 1 (by rfl) ⟨6183833, by rfl⟩ : syracuseStep 8245111 = 12367667) B12367667
theorem B1355643 : Blo 1354996 1355643 := bstep (se 1 (by rfl) ⟨1016732, by rfl⟩ : syracuseStep 1355643 = 2033465) B2033465
theorem B1355695 : Blo 1354996 1355695 := bstep (se 1 (by rfl) ⟨1016771, by rfl⟩ : syracuseStep 1355695 = 2033543) B2033543
theorem B1355719 : Blo 1354996 1355719 := bstep (se 1 (by rfl) ⟨1016789, by rfl⟩ : syracuseStep 1355719 = 2033579) B2033579
theorem B1355739 : Blo 1354996 1355739 := bstep (se 1 (by rfl) ⟨1016804, by rfl⟩ : syracuseStep 1355739 = 2033609) B2033609
theorem B3051539 : Blo 1354996 3051539 := bstep (se 1 (by rfl) ⟨2288654, by rfl⟩ : syracuseStep 3051539 = 4577309) B4577309
theorem B1355815 : Blo 1354996 1355815 := bstep (se 1 (by rfl) ⟨1016861, by rfl⟩ : syracuseStep 1355815 = 2033723) B2033723
theorem B2289721 : Blo 1354996 2289721 := bstep (se 2 (by rfl) ⟨858645, by rfl⟩ : syracuseStep 2289721 = 1717291) B1717291
theorem B87953485 : Blo 1354996 87953485 := bstep (se 3 (by rfl) ⟨16491278, by rfl⟩ : syracuseStep 87953485 = 32982557) B32982557
theorem B4575311 : Blo 1354996 4575311 := bstep (se 1 (by rfl) ⟨3431483, by rfl⟩ : syracuseStep 4575311 = 6862967) B6862967
theorem B1355855 : Blo 1354996 1355855 := bstep (se 1 (by rfl) ⟨1016891, by rfl⟩ : syracuseStep 1355855 = 2033783) B2033783
theorem B1355871 : Blo 1354996 1355871 := bstep (se 1 (by rfl) ⟨1016903, by rfl⟩ : syracuseStep 1355871 = 2033807) B2033807
theorem B1355899 : Blo 1354996 1355899 := bstep (se 1 (by rfl) ⟨1016924, by rfl⟩ : syracuseStep 1355899 = 2033849) B2033849
theorem B1355951 : Blo 1354996 1355951 := bstep (se 1 (by rfl) ⟨1016963, by rfl⟩ : syracuseStep 1355951 = 2033927) B2033927
theorem B1355975 : Blo 1354996 1355975 := bstep (se 1 (by rfl) ⟨1016981, by rfl⟩ : syracuseStep 1355975 = 2033963) B2033963
theorem B2289863 : Blo 1354996 2289863 := bstep (se 1 (by rfl) ⟨1717397, by rfl⟩ : syracuseStep 2289863 = 3434795) B3434795
theorem B1355995 : Blo 1354996 1355995 := bstep (se 1 (by rfl) ⟨1016996, by rfl⟩ : syracuseStep 1355995 = 2033993) B2033993
theorem B1356071 : Blo 1354996 1356071 := bstep (se 1 (by rfl) ⟨1017053, by rfl⟩ : syracuseStep 1356071 = 2034107) B2034107
theorem B5501245 : Blo 1354996 5501245 := bstep (se 3 (by rfl) ⟨1031483, by rfl⟩ : syracuseStep 5501245 = 2062967) B2062967
theorem B1356111 : Blo 1354996 1356111 := bstep (se 1 (by rfl) ⟨1017083, by rfl⟩ : syracuseStep 1356111 = 2034167) B2034167
theorem B1356127 : Blo 1354996 1356127 := bstep (se 1 (by rfl) ⟨1017095, by rfl⟩ : syracuseStep 1356127 = 2034191) B2034191
theorem B3051881 : Blo 1354996 3051881 := bstep (se 2 (by rfl) ⟨1144455, by rfl⟩ : syracuseStep 3051881 = 2288911) B2288911
theorem B1356155 : Blo 1354996 1356155 := bstep (se 1 (by rfl) ⟨1017116, by rfl⟩ : syracuseStep 1356155 = 2034233) B2034233
theorem B3912065 : Blo 1354996 3912065 := bstep (se 2 (by rfl) ⟨1467024, by rfl⟩ : syracuseStep 3912065 = 2934049) B2934049
theorem B6861185 : Blo 1354996 6861185 := bstep (se 2 (by rfl) ⟨2572944, by rfl⟩ : syracuseStep 6861185 = 5145889) B5145889
theorem B1356207 : Blo 1354996 1356207 := bstep (se 1 (by rfl) ⟨1017155, by rfl⟩ : syracuseStep 1356207 = 2034311) B2034311
theorem B1356231 : Blo 1354996 1356231 := bstep (se 1 (by rfl) ⟨1017173, by rfl⟩ : syracuseStep 1356231 = 2034347) B2034347
theorem B4575689 : Blo 1354996 4575689 := bstep (se 2 (by rfl) ⟨1715883, by rfl⟩ : syracuseStep 4575689 = 3431767) B3431767
theorem B37097945 : Blo 1354996 37097945 := bstep (se 2 (by rfl) ⟨13911729, by rfl⟩ : syracuseStep 37097945 = 27823459) B27823459
theorem B1356251 : Blo 1354996 1356251 := bstep (se 1 (by rfl) ⟨1017188, by rfl⟩ : syracuseStep 1356251 = 2034377) B2034377
theorem B5788169 : Blo 1354996 5788169 := bstep (se 2 (by rfl) ⟨2170563, by rfl⟩ : syracuseStep 5788169 = 4341127) B4341127
theorem B26063369 : Blo 1354996 26063369 := bstep (se 2 (by rfl) ⟨9773763, by rfl⟩ : syracuseStep 26063369 = 19547527) B19547527
theorem B1356327 : Blo 1354996 1356327 := bstep (se 1 (by rfl) ⟨1017245, by rfl⟩ : syracuseStep 1356327 = 2034491) B2034491
theorem B1356367 : Blo 1354996 1356367 := bstep (se 1 (by rfl) ⟨1017275, by rfl⟩ : syracuseStep 1356367 = 2034551) B2034551
theorem B1716815 : Blo 1354996 1716815 := bstep (se 1 (by rfl) ⟨1287611, by rfl⟩ : syracuseStep 1716815 = 2575223) B2575223
theorem B1356383 : Blo 1354996 1356383 := bstep (se 1 (by rfl) ⟨1017287, by rfl⟩ : syracuseStep 1356383 = 2034575) B2034575
theorem B1356411 : Blo 1354996 1356411 := bstep (se 1 (by rfl) ⟨1017308, by rfl⟩ : syracuseStep 1356411 = 2034617) B2034617
theorem B1356463 : Blo 1354996 1356463 := bstep (se 1 (by rfl) ⟨1017347, by rfl⟩ : syracuseStep 1356463 = 2034695) B2034695
theorem B1356487 : Blo 1354996 1356487 := bstep (se 1 (by rfl) ⟨1017365, by rfl⟩ : syracuseStep 1356487 = 2034731) B2034731
theorem B4575959 : Blo 1354996 4575959 := bstep (se 1 (by rfl) ⟨3431969, by rfl⟩ : syracuseStep 4575959 = 6863939) B6863939
theorem B1356507 : Blo 1354996 1356507 := bstep (se 1 (by rfl) ⟨1017380, by rfl⟩ : syracuseStep 1356507 = 2034761) B2034761
theorem B1356583 : Blo 1354996 1356583 := bstep (se 1 (by rfl) ⟨1017437, by rfl⟩ : syracuseStep 1356583 = 2034875) B2034875
theorem B1356623 : Blo 1354996 1356623 := bstep (se 1 (by rfl) ⟨1017467, by rfl⟩ : syracuseStep 1356623 = 2034935) B2034935
theorem B1356639 : Blo 1354996 1356639 := bstep (se 1 (by rfl) ⟨1017479, by rfl⟩ : syracuseStep 1356639 = 2034959) B2034959
theorem B1356667 : Blo 1354996 1356667 := bstep (se 1 (by rfl) ⟨1017500, by rfl⟩ : syracuseStep 1356667 = 2035001) B2035001
theorem B1930159 : Blo 1354996 1930159 := bstep (se 1 (by rfl) ⟨1447619, by rfl⟩ : syracuseStep 1930159 = 2895239) B2895239
theorem B4576175 : Blo 1354996 4576175 := bstep (se 1 (by rfl) ⟨3432131, by rfl⟩ : syracuseStep 4576175 = 6864263) B6864263
theorem B1356719 : Blo 1354996 1356719 := bstep (se 1 (by rfl) ⟨1017539, by rfl⟩ : syracuseStep 1356719 = 2035079) B2035079
theorem B3052475 : Blo 1354996 3052475 := bstep (se 1 (by rfl) ⟨2289356, by rfl⟩ : syracuseStep 3052475 = 4578713) B4578713
theorem B1356743 : Blo 1354996 1356743 := bstep (se 1 (by rfl) ⟨1017557, by rfl⟩ : syracuseStep 1356743 = 2035115) B2035115
theorem B1356763 : Blo 1354996 1356763 := bstep (se 1 (by rfl) ⟨1017572, by rfl⟩ : syracuseStep 1356763 = 2035145) B2035145
theorem B10433555 : Blo 1354996 10433555 := bstep (se 1 (by rfl) ⟨7825166, by rfl⟩ : syracuseStep 10433555 = 15650333) B15650333
theorem B1356839 : Blo 1354996 1356839 := bstep (se 1 (by rfl) ⟨1017629, by rfl⟩ : syracuseStep 1356839 = 2035259) B2035259
theorem B8246323 : Blo 1354996 8246323 := bstep (se 1 (by rfl) ⟨6184742, by rfl⟩ : syracuseStep 8246323 = 12369485) B12369485
theorem B3052601 : Blo 1354996 3052601 := bstep (se 2 (by rfl) ⟨1144725, by rfl⟩ : syracuseStep 3052601 = 2289451) B2289451
theorem B3863609 : Blo 1354996 3863609 := bstep (se 2 (by rfl) ⟨1448853, by rfl⟩ : syracuseStep 3863609 = 2897707) B2897707
theorem B1356879 : Blo 1354996 1356879 := bstep (se 1 (by rfl) ⟨1017659, by rfl⟩ : syracuseStep 1356879 = 2035319) B2035319
theorem B4346959 : Blo 1354996 4346959 := bstep (se 1 (by rfl) ⟨3260219, by rfl⟩ : syracuseStep 4346959 = 6520439) B6520439
theorem B5149777 : Blo 1354996 5149777 := bstep (se 2 (by rfl) ⟨1931166, by rfl⟩ : syracuseStep 5149777 = 3862333) B3862333
theorem B1356895 : Blo 1354996 1356895 := bstep (se 1 (by rfl) ⟨1017671, by rfl⟩ : syracuseStep 1356895 = 2035343) B2035343
theorem B1356923 : Blo 1354996 1356923 := bstep (se 1 (by rfl) ⟨1017692, by rfl⟩ : syracuseStep 1356923 = 2035385) B2035385
theorem B58619051 : Blo 1354996 58619051 := bstep (se 1 (by rfl) ⟨43964288, by rfl⟩ : syracuseStep 58619051 = 87928577) B87928577
theorem B6861995 : Blo 1354996 6861995 := bstep (se 1 (by rfl) ⟨5146496, by rfl⟩ : syracuseStep 6861995 = 10292993) B10292993
theorem B1356975 : Blo 1354996 1356975 := bstep (se 1 (by rfl) ⟨1017731, by rfl⟩ : syracuseStep 1356975 = 2035463) B2035463
theorem B5150081 : Blo 1354996 5150081 := bstep (se 2 (by rfl) ⟨1931280, by rfl⟩ : syracuseStep 5150081 = 3862561) B3862561
theorem B3052943 : Blo 1354996 3052943 := bstep (se 1 (by rfl) ⟨2289707, by rfl⟩ : syracuseStep 3052943 = 4579415) B4579415
theorem B3429985 : Blo 1354996 3429985 := bstep (se 2 (by rfl) ⟨1286244, by rfl⟩ : syracuseStep 3429985 = 2572489) B2572489
theorem B6862481 : Blo 1354996 6862481 := bstep (se 2 (by rfl) ⟨2573430, by rfl⟩ : syracuseStep 6862481 = 5146861) B5146861
theorem B1832647 : Blo 1354996 1832647 := bstep (se 1 (by rfl) ⟨1374485, by rfl⟩ : syracuseStep 1832647 = 2748971) B2748971
theorem B9279197 : Blo 1354996 9279197 := bstep (se 3 (by rfl) ⟨1739849, by rfl⟩ : syracuseStep 9279197 = 3479699) B3479699
theorem B19535651 : Blo 1354996 19535651 := bstep (se 1 (by rfl) ⟨14651738, by rfl⟩ : syracuseStep 19535651 = 29303477) B29303477
theorem B5150537 : Blo 1354996 5150537 := bstep (se 2 (by rfl) ⟨1931451, by rfl⟩ : syracuseStep 5150537 = 3862903) B3862903
theorem B1832809 : Blo 1354996 1832809 := bstep (se 2 (by rfl) ⟨687303, by rfl⟩ : syracuseStep 1832809 = 1374607) B1374607
theorem B2750315 : Blo 1354996 2750315 := bstep (se 1 (by rfl) ⟨2062736, by rfl⟩ : syracuseStep 2750315 = 4125473) B4125473
theorem B5150735 : Blo 1354996 5150735 := bstep (se 1 (by rfl) ⟨3863051, by rfl⟩ : syracuseStep 5150735 = 7726103) B7726103
theorem B10442789 : Blo 1354996 10442789 := bstep (se 4 (by rfl) ⟨979011, by rfl⟩ : syracuseStep 10442789 = 1958023) B1958023
theorem B6953303 : Blo 1354996 6953303 := bstep (se 1 (by rfl) ⟨5214977, by rfl⟩ : syracuseStep 6953303 = 10429955) B10429955
theorem B3430937 : Blo 1354996 3430937 := bstep (se 2 (by rfl) ⟨1286601, by rfl⟩ : syracuseStep 3430937 = 2573203) B2573203
theorem B3431443 : Blo 1354996 3431443 := bstep (se 1 (by rfl) ⟨2573582, by rfl⟩ : syracuseStep 3431443 = 5147165) B5147165
theorem B5496055 : Blo 1354996 5496055 := bstep (se 1 (by rfl) ⟨4122041, by rfl⟩ : syracuseStep 5496055 = 8244083) B8244083
theorem B4578551 : Blo 1354996 4578551 := bstep (se 1 (by rfl) ⟨3433913, by rfl⟩ : syracuseStep 4578551 = 6867827) B6867827
theorem B30530839 : Blo 1354996 30530839 := bstep (se 1 (by rfl) ⟨22898129, by rfl⟩ : syracuseStep 30530839 = 45796259) B45796259
theorem B111336889 : Blo 1354996 111336889 := bstep (se 2 (by rfl) ⟨41751333, by rfl⟩ : syracuseStep 111336889 = 83502667) B83502667
theorem B9272843 : Blo 1354996 9272843 := bstep (se 1 (by rfl) ⟨6954632, by rfl⟩ : syracuseStep 9272843 = 13909265) B13909265
theorem B4578875 : Blo 1354996 4578875 := bstep (se 1 (by rfl) ⟨3434156, by rfl⟩ : syracuseStep 4578875 = 6868313) B6868313
theorem B4579145 : Blo 1354996 4579145 := bstep (se 2 (by rfl) ⟨1717179, by rfl⟩ : syracuseStep 4579145 = 3434359) B3434359
theorem B3260267 : Blo 1354996 3260267 := bstep (se 1 (by rfl) ⟨2445200, by rfl⟩ : syracuseStep 3260267 = 4890401) B4890401
theorem B6864749 : Blo 1354996 6864749 := bstep (se 3 (by rfl) ⟨1287140, by rfl⟩ : syracuseStep 6864749 = 2574281) B2574281
theorem B4341691 : Blo 1354996 4341691 := bstep (se 1 (by rfl) ⟨3256268, by rfl⟩ : syracuseStep 4341691 = 6512537) B6512537
theorem B6520763 : Blo 1354996 6520763 := bstep (se 1 (by rfl) ⟨4890572, by rfl⟩ : syracuseStep 6520763 = 9781145) B9781145
theorem B3432577 : Blo 1354996 3432577 := bstep (se 2 (by rfl) ⟨1287216, by rfl⟩ : syracuseStep 3432577 = 2574433) B2574433
theorem B24731963 : Blo 1354996 24731963 := bstep (se 1 (by rfl) ⟨18548972, by rfl⟩ : syracuseStep 24731963 = 37097945) B37097945
theorem B3858779 : Blo 1354996 3858779 := bstep (se 1 (by rfl) ⟨2894084, by rfl⟩ : syracuseStep 3858779 = 5788169) B5788169
theorem B17375579 : Blo 1354996 17375579 := bstep (se 1 (by rfl) ⟨13031684, by rfl⟩ : syracuseStep 17375579 = 26063369) B26063369
theorem B11592193 : Blo 1354996 11592193 := bstep (se 2 (by rfl) ⟨4347072, by rfl⟩ : syracuseStep 11592193 = 8694145) B8694145
theorem B2572975 : Blo 1354996 2572975 := bstep (se 1 (by rfl) ⟨1929731, by rfl⟩ : syracuseStep 2572975 = 3859463) B3859463
theorem B6955703 : Blo 1354996 6955703 := bstep (se 1 (by rfl) ⟨5216777, by rfl⟩ : syracuseStep 6955703 = 10433555) B10433555
theorem B1524559 : Blo 1354996 1524559 := bstep (se 1 (by rfl) ⟨1143419, by rfl⟩ : syracuseStep 1524559 = 2286839) B2286839
theorem B11584403 : Blo 1354996 11584403 := bstep (se 1 (by rfl) ⟨8688302, by rfl⟩ : syracuseStep 11584403 = 17376605) B17376605
theorem B3433387 : Blo 1354996 3433387 := bstep (se 1 (by rfl) ⟨2575040, by rfl⟩ : syracuseStep 3433387 = 5150081) B5150081
theorem B6865883 : Blo 1354996 6865883 := bstep (se 1 (by rfl) ⟨5149412, by rfl⟩ : syracuseStep 6865883 = 10298825) B10298825
theorem B6866045 : Blo 1354996 6866045 := bstep (se 3 (by rfl) ⟨1287383, by rfl⟩ : syracuseStep 6866045 = 2574767) B2574767
theorem B6186131 : Blo 1354996 6186131 := bstep (se 1 (by rfl) ⟨4639598, by rfl⟩ : syracuseStep 6186131 = 9279197) B9279197
theorem B2032859 : Blo 1354996 2032859 := bstep (se 1 (by rfl) ⟨1524644, by rfl⟩ : syracuseStep 2032859 = 3049289) B3049289
theorem B1524955 : Blo 1354996 1524955 := bstep (se 1 (by rfl) ⟨1143716, by rfl⟩ : syracuseStep 1524955 = 2287433) B2287433
theorem B3433691 : Blo 1354996 3433691 := bstep (se 1 (by rfl) ⟨2575268, by rfl⟩ : syracuseStep 3433691 = 5150537) B5150537
theorem B2573545 : Blo 1354996 2573545 := bstep (se 2 (by rfl) ⟨965079, by rfl⟩ : syracuseStep 2573545 = 1930159) B1930159
theorem B29312293 : Blo 1354996 29312293 := bstep (se 4 (by rfl) ⟨2748027, by rfl⟩ : syracuseStep 29312293 = 5496055) B5496055
theorem B3433823 : Blo 1354996 3433823 := bstep (se 1 (by rfl) ⟨2575367, by rfl⟩ : syracuseStep 3433823 = 5150735) B5150735
theorem B2033033 : Blo 1354996 2033033 := bstep (se 2 (by rfl) ⟨762387, by rfl⟩ : syracuseStep 2033033 = 1524775) B1524775
theorem B10995097 : Blo 1354996 10995097 := bstep (se 2 (by rfl) ⟨4123161, by rfl⟩ : syracuseStep 10995097 = 8246323) B8246323
theorem B6866369 : Blo 1354996 6866369 := bstep (se 2 (by rfl) ⟨2574888, by rfl⟩ : syracuseStep 6866369 = 5149777) B5149777
theorem B34760177 : Blo 1354996 34760177 := bstep (se 2 (by rfl) ⟨13035066, by rfl⟩ : syracuseStep 34760177 = 26070133) B26070133
theorem B1525243 : Blo 1354996 1525243 := bstep (se 1 (by rfl) ⟨1143932, by rfl⟩ : syracuseStep 1525243 = 2287865) B2287865
theorem B3049055 : Blo 1354996 3049055 := bstep (se 1 (by rfl) ⟨2286791, by rfl⟩ : syracuseStep 3049055 = 4573583) B4573583
theorem B1525423 : Blo 1354996 1525423 := bstep (se 1 (by rfl) ⟨1144067, by rfl⟩ : syracuseStep 1525423 = 2288135) B2288135
theorem B2287291 : Blo 1354996 2287291 := bstep (se 1 (by rfl) ⟨1715468, by rfl⟩ : syracuseStep 2287291 = 3430937) B3430937
theorem B40707785 : Blo 1354996 40707785 := bstep (se 2 (by rfl) ⟨15265419, by rfl⟩ : syracuseStep 40707785 = 30530839) B30530839
theorem B2033387 : Blo 1354996 2033387 := bstep (se 1 (by rfl) ⟨1525040, by rfl⟩ : syracuseStep 2033387 = 3050081) B3050081
theorem B3049271 : Blo 1354996 3049271 := bstep (se 1 (by rfl) ⟨2286953, by rfl⟩ : syracuseStep 3049271 = 4573907) B4573907
theorem B10291049 : Blo 1354996 10291049 := bstep (se 2 (by rfl) ⟨3859143, by rfl⟩ : syracuseStep 10291049 = 7718287) B7718287
theorem B148449185 : Blo 1354996 148449185 := bstep (se 2 (by rfl) ⟨55668444, by rfl⟩ : syracuseStep 148449185 = 111336889) B111336889
theorem B2033615 : Blo 1354996 2033615 := bstep (se 1 (by rfl) ⟨1525211, by rfl⟩ : syracuseStep 2033615 = 3050423) B3050423
theorem B1525711 : Blo 1354996 1525711 := bstep (se 1 (by rfl) ⟨1144283, by rfl⟩ : syracuseStep 1525711 = 2288567) B2288567
theorem B6186989 : Blo 1354996 6186989 := bstep (se 3 (by rfl) ⟨1160060, by rfl⟩ : syracuseStep 6186989 = 2320121) B2320121
theorem B3434521 : Blo 1354996 3434521 := bstep (se 2 (by rfl) ⟨1287945, by rfl⟩ : syracuseStep 3434521 = 2575891) B2575891
theorem B3049577 : Blo 1354996 3049577 := bstep (se 2 (by rfl) ⟨1143591, by rfl⟩ : syracuseStep 3049577 = 2287183) B2287183
theorem B4573313 : Blo 1354996 4573313 := bstep (se 2 (by rfl) ⟨1714992, by rfl⟩ : syracuseStep 4573313 = 3429985) B3429985
theorem B2443529 : Blo 1354996 2443529 := bstep (se 2 (by rfl) ⟨916323, by rfl⟩ : syracuseStep 2443529 = 1832647) B1832647
theorem B7334173 : Blo 1354996 7334173 := bstep (se 3 (by rfl) ⟨1375157, by rfl⟩ : syracuseStep 7334173 = 2750315) B2750315
theorem B3434825 : Blo 1354996 3434825 := bstep (se 2 (by rfl) ⟨1288059, by rfl⟩ : syracuseStep 3434825 = 2576119) B2576119
theorem B2034011 : Blo 1354996 2034011 := bstep (se 1 (by rfl) ⟨1525508, by rfl⟩ : syracuseStep 2034011 = 3051017) B3051017
theorem B1526107 : Blo 1354996 1526107 := bstep (se 1 (by rfl) ⟨1144580, by rfl⟩ : syracuseStep 1526107 = 2289161) B2289161
theorem B9767279 : Blo 1354996 9767279 := bstep (se 1 (by rfl) ⟨7325459, by rfl⟩ : syracuseStep 9767279 = 14650919) B14650919
theorem B1526215 : Blo 1354996 1526215 := bstep (se 1 (by rfl) ⟨1144661, by rfl⟩ : syracuseStep 1526215 = 2289323) B2289323
theorem B2443745 : Blo 1354996 2443745 := bstep (se 2 (by rfl) ⟨916404, by rfl⟩ : syracuseStep 2443745 = 1832809) B1832809
theorem B4573691 : Blo 1354996 4573691 := bstep (se 1 (by rfl) ⟨3430268, by rfl⟩ : syracuseStep 4573691 = 6860537) B6860537
theorem B2034239 : Blo 1354996 2034239 := bstep (se 1 (by rfl) ⟨1525679, by rfl⟩ : syracuseStep 2034239 = 3051359) B3051359
theorem B2574919 : Blo 1354996 2574919 := bstep (se 1 (by rfl) ⟨1931189, by rfl⟩ : syracuseStep 2574919 = 3862379) B3862379
theorem B2173511 : Blo 1354996 2173511 := bstep (se 1 (by rfl) ⟨1630133, by rfl⟩ : syracuseStep 2173511 = 3260267) B3260267
theorem B3050063 : Blo 1354996 3050063 := bstep (se 1 (by rfl) ⟨2287547, by rfl⟩ : syracuseStep 3050063 = 4575095) B4575095
theorem B2034359 : Blo 1354996 2034359 := bstep (se 1 (by rfl) ⟨1525769, by rfl⟩ : syracuseStep 2034359 = 3051539) B3051539
theorem B3050207 : Blo 1354996 3050207 := bstep (se 1 (by rfl) ⟨2287655, by rfl⟩ : syracuseStep 3050207 = 4575311) B4575311
theorem B2288351 : Blo 1354996 2288351 := bstep (se 1 (by rfl) ⟨1716263, by rfl⟩ : syracuseStep 2288351 = 3432527) B3432527
theorem B117271313 : Blo 1354996 117271313 := bstep (se 2 (by rfl) ⟨43976742, by rfl⟩ : syracuseStep 117271313 = 87953485) B87953485
theorem B1526575 : Blo 1354996 1526575 := bstep (se 1 (by rfl) ⟨1144931, by rfl⟩ : syracuseStep 1526575 = 2289863) B2289863
theorem B1715023 : Blo 1354996 1715023 := bstep (se 1 (by rfl) ⟨1286267, by rfl⟩ : syracuseStep 1715023 = 2572535) B2572535
theorem B2034587 : Blo 1354996 2034587 := bstep (se 1 (by rfl) ⟨1525940, by rfl⟩ : syracuseStep 2034587 = 3051881) B3051881
theorem B2608043 : Blo 1354996 2608043 := bstep (se 1 (by rfl) ⟨1956032, by rfl⟩ : syracuseStep 2608043 = 3912065) B3912065
theorem B4574123 : Blo 1354996 4574123 := bstep (se 1 (by rfl) ⟨3430592, by rfl⟩ : syracuseStep 4574123 = 6861185) B6861185
theorem B3050459 : Blo 1354996 3050459 := bstep (se 1 (by rfl) ⟨2287844, by rfl⟩ : syracuseStep 3050459 = 4575689) B4575689
theorem B29731855 : Blo 1354996 29731855 := bstep (se 1 (by rfl) ⟨22298891, by rfl⟩ : syracuseStep 29731855 = 44597783) B44597783
theorem B9407569 : Blo 1354996 9407569 := bstep (se 2 (by rfl) ⟨3527838, by rfl⟩ : syracuseStep 9407569 = 7055677) B7055677
theorem B7334993 : Blo 1354996 7334993 := bstep (se 2 (by rfl) ⟨2750622, by rfl⟩ : syracuseStep 7334993 = 5501245) B5501245
theorem B3050639 : Blo 1354996 3050639 := bstep (se 1 (by rfl) ⟨2287979, by rfl⟩ : syracuseStep 3050639 = 4575959) B4575959
theorem B2288783 : Blo 1354996 2288783 := bstep (se 1 (by rfl) ⟨1716587, by rfl⟩ : syracuseStep 2288783 = 3433175) B3433175
theorem B3050729 : Blo 1354996 3050729 := bstep (se 2 (by rfl) ⟨1144023, by rfl⟩ : syracuseStep 3050729 = 2288047) B2288047
theorem B1355039 : Blo 1354996 1355039 := bstep (se 1 (by rfl) ⟨1016279, by rfl⟩ : syracuseStep 1355039 = 2032559) B2032559
theorem B3050783 : Blo 1354996 3050783 := bstep (se 1 (by rfl) ⟨2288087, by rfl⟩ : syracuseStep 3050783 = 4576175) B4576175
theorem B2034983 : Blo 1354996 2034983 := bstep (se 1 (by rfl) ⟨1526237, by rfl⟩ : syracuseStep 2034983 = 3052475) B3052475
theorem B1355099 : Blo 1354996 1355099 := bstep (se 1 (by rfl) ⟨1016324, by rfl⟩ : syracuseStep 1355099 = 2032649) B2032649
theorem B10300769 : Blo 1354996 10300769 := bstep (se 2 (by rfl) ⟨3862788, by rfl⟩ : syracuseStep 10300769 = 7725577) B7725577
theorem B1355119 : Blo 1354996 1355119 := bstep (se 1 (by rfl) ⟨1016339, by rfl⟩ : syracuseStep 1355119 = 2032679) B2032679
theorem B2289019 : Blo 1354996 2289019 := bstep (se 1 (by rfl) ⟨1716764, by rfl⟩ : syracuseStep 2289019 = 3433529) B3433529
theorem B2035067 : Blo 1354996 2035067 := bstep (se 1 (by rfl) ⟨1526300, by rfl⟩ : syracuseStep 2035067 = 3052601) B3052601
theorem B2575739 : Blo 1354996 2575739 := bstep (se 1 (by rfl) ⟨1931804, by rfl⟩ : syracuseStep 2575739 = 3863609) B3863609
theorem B1355175 : Blo 1354996 1355175 := bstep (se 1 (by rfl) ⟨1016381, by rfl⟩ : syracuseStep 1355175 = 2032763) B2032763
theorem B39079367 : Blo 1354996 39079367 := bstep (se 1 (by rfl) ⟨29309525, by rfl⟩ : syracuseStep 39079367 = 58619051) B58619051
theorem B4574663 : Blo 1354996 4574663 := bstep (se 1 (by rfl) ⟨3430997, by rfl⟩ : syracuseStep 4574663 = 6861995) B6861995
theorem B1355259 : Blo 1354996 1355259 := bstep (se 1 (by rfl) ⟨1016444, by rfl⟩ : syracuseStep 1355259 = 2032889) B2032889
theorem B2035193 : Blo 1354996 2035193 := bstep (se 2 (by rfl) ⟨763197, by rfl⟩ : syracuseStep 2035193 = 1526395) B1526395
theorem B1355327 : Blo 1354996 1355327 := bstep (se 1 (by rfl) ⟨1016495, by rfl⟩ : syracuseStep 1355327 = 2032991) B2032991
theorem B1355335 : Blo 1354996 1355335 := bstep (se 1 (by rfl) ⟨1016501, by rfl⟩ : syracuseStep 1355335 = 2033003) B2033003
theorem B2035295 : Blo 1354996 2035295 := bstep (se 1 (by rfl) ⟨1526471, by rfl⟩ : syracuseStep 2035295 = 3052943) B3052943
theorem B1355487 : Blo 1354996 1355487 := bstep (se 1 (by rfl) ⟨1016615, by rfl⟩ : syracuseStep 1355487 = 2033231) B2033231
theorem B4574987 : Blo 1354996 4574987 := bstep (se 1 (by rfl) ⟨3431240, by rfl⟩ : syracuseStep 4574987 = 6862481) B6862481
theorem B3051305 : Blo 1354996 3051305 := bstep (se 2 (by rfl) ⟨1144239, by rfl⟩ : syracuseStep 3051305 = 2288479) B2288479
theorem B1355567 : Blo 1354996 1355567 := bstep (se 1 (by rfl) ⟨1016675, by rfl⟩ : syracuseStep 1355567 = 2033351) B2033351
theorem B3256193 : Blo 1354996 3256193 := bstep (se 2 (by rfl) ⟨1221072, by rfl⟩ : syracuseStep 3256193 = 2442145) B2442145
theorem B1355675 : Blo 1354996 1355675 := bstep (se 1 (by rfl) ⟨1016756, by rfl⟩ : syracuseStep 1355675 = 2033513) B2033513
theorem B1355727 : Blo 1354996 1355727 := bstep (se 1 (by rfl) ⟨1016795, by rfl⟩ : syracuseStep 1355727 = 2033591) B2033591
theorem B11579345 : Blo 1354996 11579345 := bstep (se 2 (by rfl) ⟨4342254, by rfl⟩ : syracuseStep 11579345 = 8684509) B8684509
theorem B1355751 : Blo 1354996 1355751 := bstep (se 1 (by rfl) ⟨1016813, by rfl⟩ : syracuseStep 1355751 = 2033627) B2033627
theorem B4575257 : Blo 1354996 4575257 := bstep (se 2 (by rfl) ⟨1715721, by rfl⟩ : syracuseStep 4575257 = 3431443) B3431443
theorem B11907161 : Blo 1354996 11907161 := bstep (se 2 (by rfl) ⟨4465185, by rfl⟩ : syracuseStep 11907161 = 8930371) B8930371
theorem B5795945 : Blo 1354996 5795945 := bstep (se 2 (by rfl) ⟨2173479, by rfl⟩ : syracuseStep 5795945 = 4346959) B4346959
theorem B42315979 : Blo 1354996 42315979 := bstep (se 1 (by rfl) ⟨31736984, by rfl⟩ : syracuseStep 42315979 = 63473969) B63473969
theorem B1356063 : Blo 1354996 1356063 := bstep (se 1 (by rfl) ⟨1017047, by rfl⟩ : syracuseStep 1356063 = 2034095) B2034095
theorem B1356123 : Blo 1354996 1356123 := bstep (se 1 (by rfl) ⟨1017092, by rfl⟩ : syracuseStep 1356123 = 2034185) B2034185
theorem B1356143 : Blo 1354996 1356143 := bstep (se 1 (by rfl) ⟨1017107, by rfl⟩ : syracuseStep 1356143 = 2034215) B2034215
theorem B1356199 : Blo 1354996 1356199 := bstep (se 1 (by rfl) ⟨1017149, by rfl⟩ : syracuseStep 1356199 = 2034299) B2034299
theorem B1356283 : Blo 1354996 1356283 := bstep (se 1 (by rfl) ⟨1017212, by rfl⟩ : syracuseStep 1356283 = 2034425) B2034425
theorem B1356351 : Blo 1354996 1356351 := bstep (se 1 (by rfl) ⟨1017263, by rfl⟩ : syracuseStep 1356351 = 2034527) B2034527
theorem B1356359 : Blo 1354996 1356359 := bstep (se 1 (by rfl) ⟨1017269, by rfl⟩ : syracuseStep 1356359 = 2034539) B2034539
theorem B1356511 : Blo 1354996 1356511 := bstep (se 1 (by rfl) ⟨1017383, by rfl⟩ : syracuseStep 1356511 = 2034767) B2034767
theorem B2896631 : Blo 1354996 2896631 := bstep (se 1 (by rfl) ⟨2172473, by rfl⟩ : syracuseStep 2896631 = 4344947) B4344947
theorem B21173021 : Blo 1354996 21173021 := bstep (se 3 (by rfl) ⟨3969941, by rfl⟩ : syracuseStep 21173021 = 7939883) B7939883
theorem B1356591 : Blo 1354996 1356591 := bstep (se 1 (by rfl) ⟨1017443, by rfl⟩ : syracuseStep 1356591 = 2034887) B2034887
theorem B3052367 : Blo 1354996 3052367 := bstep (se 1 (by rfl) ⟨2289275, by rfl⟩ : syracuseStep 3052367 = 4578551) B4578551
theorem B1356699 : Blo 1354996 1356699 := bstep (se 1 (by rfl) ⟨1017524, by rfl⟩ : syracuseStep 1356699 = 2035049) B2035049
theorem B1356751 : Blo 1354996 1356751 := bstep (se 1 (by rfl) ⟨1017563, by rfl⟩ : syracuseStep 1356751 = 2035127) B2035127
theorem B1356775 : Blo 1354996 1356775 := bstep (se 1 (by rfl) ⟨1017581, by rfl⟩ : syracuseStep 1356775 = 2035163) B2035163
theorem B11580407 : Blo 1354996 11580407 := bstep (se 1 (by rfl) ⟨8685305, by rfl⟩ : syracuseStep 11580407 = 17370611) B17370611
theorem B6181895 : Blo 1354996 6181895 := bstep (se 1 (by rfl) ⟨4636421, by rfl⟩ : syracuseStep 6181895 = 9272843) B9272843
theorem B3257383 : Blo 1354996 3257383 := bstep (se 1 (by rfl) ⟨2443037, by rfl⟩ : syracuseStep 3257383 = 4886075) B4886075
theorem B3052583 : Blo 1354996 3052583 := bstep (se 1 (by rfl) ⟨2289437, by rfl⟩ : syracuseStep 3052583 = 4578875) B4578875
theorem B17388701 : Blo 1354996 17388701 := bstep (se 3 (by rfl) ⟨3260381, by rfl⟩ : syracuseStep 17388701 = 6520763) B6520763
theorem B3052763 : Blo 1354996 3052763 := bstep (se 1 (by rfl) ⟨2289572, by rfl⟩ : syracuseStep 3052763 = 4579145) B4579145
theorem B4576499 : Blo 1354996 4576499 := bstep (se 1 (by rfl) ⟨3432374, by rfl⟩ : syracuseStep 4576499 = 6864749) B6864749
theorem B5788921 : Blo 1354996 5788921 := bstep (se 2 (by rfl) ⟨2170845, by rfl⟩ : syracuseStep 5788921 = 4341691) B4341691
theorem B10302713 : Blo 1354996 10302713 := bstep (se 2 (by rfl) ⟨3863517, by rfl⟩ : syracuseStep 10302713 = 7727035) B7727035
theorem B4576607 : Blo 1354996 4576607 := bstep (se 1 (by rfl) ⟨3432455, by rfl⟩ : syracuseStep 4576607 = 6864911) B6864911
theorem B3052961 : Blo 1354996 3052961 := bstep (se 2 (by rfl) ⟨1144860, by rfl⟩ : syracuseStep 3052961 = 2289721) B2289721
theorem B1447367 : Blo 1354996 1447367 := bstep (se 1 (by rfl) ⟨1085525, by rfl⟩ : syracuseStep 1447367 = 2171051) B2171051
theorem B13022765 : Blo 1354996 13022765 := bstep (se 3 (by rfl) ⟨2441768, by rfl⟩ : syracuseStep 13022765 = 4883537) B4883537
theorem B190502725 : Blo 1354996 190502725 := bstep (se 4 (by rfl) ⟨17859630, by rfl⟩ : syracuseStep 190502725 = 35719261) B35719261
theorem B2898185 : Blo 1354996 2898185 := bstep (se 2 (by rfl) ⟨1086819, by rfl⟩ : syracuseStep 2898185 = 2173639) B2173639
theorem B8689943 : Blo 1354996 8689943 := bstep (se 1 (by rfl) ⟨6517457, by rfl⟩ : syracuseStep 8689943 = 13034915) B13034915
theorem B6863129 : Blo 1354996 6863129 := bstep (se 2 (by rfl) ⟨2573673, by rfl⟩ : syracuseStep 6863129 = 5147347) B5147347
theorem B5789981 : Blo 1354996 5789981 := bstep (se 3 (by rfl) ⟨1085621, by rfl⟩ : syracuseStep 5789981 = 2171243) B2171243
theorem B3430907 : Blo 1354996 3430907 := bstep (se 1 (by rfl) ⟨2573180, by rfl⟩ : syracuseStep 3430907 = 5146361) B5146361
theorem B13023767 : Blo 1354996 13023767 := bstep (se 1 (by rfl) ⟨9767825, by rfl⟩ : syracuseStep 13023767 = 19535651) B19535651
theorem B3136079 : Blo 1354996 3136079 := bstep (se 1 (by rfl) ⟨2352059, by rfl⟩ : syracuseStep 3136079 = 4704119) B4704119
theorem B13040261 : Blo 1354996 13040261 := bstep (se 4 (by rfl) ⟨1222524, by rfl⟩ : syracuseStep 13040261 = 2445049) B2445049
theorem B7330499 : Blo 1354996 7330499 := bstep (se 1 (by rfl) ⟨5497874, by rfl⟩ : syracuseStep 7330499 = 10995749) B10995749
theorem B6961859 : Blo 1354996 6961859 := bstep (se 1 (by rfl) ⟨5221394, by rfl⟩ : syracuseStep 6961859 = 10442789) B10442789
theorem B4889335 : Blo 1354996 4889335 := bstep (se 1 (by rfl) ⟨3667001, by rfl⟩ : syracuseStep 4889335 = 7334003) B7334003
theorem B4578173 : Blo 1354996 4578173 := bstep (se 3 (by rfl) ⟨858407, by rfl⟩ : syracuseStep 4578173 = 1716815) B1716815
theorem B4635535 : Blo 1354996 4635535 := bstep (se 1 (by rfl) ⟨3476651, by rfl⟩ : syracuseStep 4635535 = 6953303) B6953303
theorem B4578443 : Blo 1354996 4578443 := bstep (se 1 (by rfl) ⟨3433832, by rfl⟩ : syracuseStep 4578443 = 6867665) B6867665
theorem B12369125 : Blo 1354996 12369125 := bstep (se 4 (by rfl) ⟨1159605, by rfl⟩ : syracuseStep 12369125 = 2319211) B2319211
theorem B14671115 : Blo 1354996 14671115 := bstep (se 1 (by rfl) ⟨11003336, by rfl⟩ : syracuseStep 14671115 = 22006673) B22006673
theorem B3431879 : Blo 1354996 3431879 := bstep (se 1 (by rfl) ⟨2573909, by rfl⟩ : syracuseStep 3431879 = 5147819) B5147819
theorem B3431929 : Blo 1354996 3431929 := bstep (se 2 (by rfl) ⟨1286973, by rfl⟩ : syracuseStep 3431929 = 2573947) B2573947
theorem B5791313 : Blo 1354996 5791313 := bstep (se 2 (by rfl) ⟨2171742, by rfl⟩ : syracuseStep 5791313 = 4343485) B4343485
theorem B13033223 : Blo 1354996 13033223 := bstep (se 1 (by rfl) ⟨9774917, by rfl⟩ : syracuseStep 13033223 = 19549835) B19549835
theorem B3432233 : Blo 1354996 3432233 := bstep (se 2 (by rfl) ⟨1287087, by rfl⟩ : syracuseStep 3432233 = 2574175) B2574175
theorem B10993481 : Blo 1354996 10993481 := bstep (se 2 (by rfl) ⟨4122555, by rfl⟩ : syracuseStep 10993481 = 8245111) B8245111
theorem B4579361 : Blo 1354996 4579361 := bstep (se 2 (by rfl) ⟨1717260, by rfl⟩ : syracuseStep 4579361 = 3434521) B3434521
theorem B7938107 : Blo 1354996 7938107 := bstep (se 1 (by rfl) ⟨5953580, by rfl⟩ : syracuseStep 7938107 = 11907161) B11907161
theorem B11583719 : Blo 1354996 11583719 := bstep (se 1 (by rfl) ⟨8687789, by rfl⟩ : syracuseStep 11583719 = 17375579) B17375579
theorem B4637135 : Blo 1354996 4637135 := bstep (se 1 (by rfl) ⟨3477851, by rfl⟩ : syracuseStep 4637135 = 6955703) B6955703
theorem B14115347 : Blo 1354996 14115347 := bstep (se 1 (by rfl) ⟨10586510, by rfl⟩ : syracuseStep 14115347 = 21173021) B21173021
theorem B4121263 : Blo 1354996 4121263 := bstep (se 1 (by rfl) ⟨3090947, by rfl⟩ : syracuseStep 4121263 = 6181895) B6181895
theorem B3433225 : Blo 1354996 3433225 := bstep (se 2 (by rfl) ⟨1287459, by rfl⟩ : syracuseStep 3433225 = 2574919) B2574919
theorem B11592467 : Blo 1354996 11592467 := bstep (se 1 (by rfl) ⟨8694350, by rfl⟩ : syracuseStep 11592467 = 17388701) B17388701
theorem B10290077 : Blo 1354996 10290077 := bstep (se 3 (by rfl) ⟨1929389, by rfl⟩ : syracuseStep 10290077 = 3858779) B3858779
theorem B2032703 : Blo 1354996 2032703 := bstep (se 1 (by rfl) ⟨1524527, by rfl⟩ : syracuseStep 2032703 = 3049055) B3049055
theorem B2286697 : Blo 1354996 2286697 := bstep (se 2 (by rfl) ⟨857511, by rfl⟩ : syracuseStep 2286697 = 1715023) B1715023
theorem B2032745 : Blo 1354996 2032745 := bstep (se 2 (by rfl) ⟨762279, by rfl⟩ : syracuseStep 2032745 = 1524559) B1524559
theorem B3859645 : Blo 1354996 3859645 := bstep (se 3 (by rfl) ⟨723683, by rfl⟩ : syracuseStep 3859645 = 1447367) B1447367
theorem B2032847 : Blo 1354996 2032847 := bstep (se 1 (by rfl) ⟨1524635, by rfl⟩ : syracuseStep 2032847 = 3049271) B3049271
theorem B39642473 : Blo 1354996 39642473 := bstep (se 2 (by rfl) ⟨14865927, by rfl⟩ : syracuseStep 39642473 = 29731855) B29731855
theorem B4343177 : Blo 1354996 4343177 := bstep (se 2 (by rfl) ⟨1628691, by rfl⟩ : syracuseStep 4343177 = 3257383) B3257383
theorem B2033051 : Blo 1354996 2033051 := bstep (se 1 (by rfl) ⟨1524788, by rfl⟩ : syracuseStep 2033051 = 3049577) B3049577
theorem B3048875 : Blo 1354996 3048875 := bstep (se 1 (by rfl) ⟨2286656, by rfl⟩ : syracuseStep 3048875 = 4573313) B4573313
theorem B12543425 : Blo 1354996 12543425 := bstep (se 2 (by rfl) ⟨4703784, by rfl⟩ : syracuseStep 12543425 = 9407569) B9407569
theorem B5793295 : Blo 1354996 5793295 := bstep (se 1 (by rfl) ⟨4344971, by rfl⟩ : syracuseStep 5793295 = 8689943) B8689943
theorem B3859987 : Blo 1354996 3859987 := bstep (se 1 (by rfl) ⟨2894990, by rfl⟩ : syracuseStep 3859987 = 5789981) B5789981
theorem B2033273 : Blo 1354996 2033273 := bstep (se 2 (by rfl) ⟨762477, by rfl⟩ : syracuseStep 2033273 = 1524955) B1524955
theorem B7718561 : Blo 1354996 7718561 := bstep (se 2 (by rfl) ⟨2894460, by rfl⟩ : syracuseStep 7718561 = 5788921) B5788921
theorem B3049127 : Blo 1354996 3049127 := bstep (se 1 (by rfl) ⟨2286845, by rfl⟩ : syracuseStep 3049127 = 4573691) B4573691
theorem B2287271 : Blo 1354996 2287271 := bstep (se 1 (by rfl) ⟨1715453, by rfl⟩ : syracuseStep 2287271 = 3430907) B3430907
theorem B2033375 : Blo 1354996 2033375 := bstep (se 1 (by rfl) ⟨1525031, by rfl⟩ : syracuseStep 2033375 = 3050063) B3050063
theorem B2090719 : Blo 1354996 2090719 := bstep (se 1 (by rfl) ⟨1568039, by rfl⟩ : syracuseStep 2090719 = 3136079) B3136079
theorem B8693507 : Blo 1354996 8693507 := bstep (se 1 (by rfl) ⟨6520130, by rfl⟩ : syracuseStep 8693507 = 13040261) B13040261
theorem B2033471 : Blo 1354996 2033471 := bstep (se 1 (by rfl) ⟨1525103, by rfl⟩ : syracuseStep 2033471 = 3050207) B3050207
theorem B1525567 : Blo 1354996 1525567 := bstep (se 1 (by rfl) ⟨1144175, by rfl⟩ : syracuseStep 1525567 = 2288351) B2288351
theorem B108554093 : Blo 1354996 108554093 := bstep (se 3 (by rfl) ⟨20353892, by rfl⟩ : syracuseStep 108554093 = 40707785) B40707785
theorem B3049415 : Blo 1354996 3049415 := bstep (se 1 (by rfl) ⟨2287061, by rfl⟩ : syracuseStep 3049415 = 4574123) B4574123
theorem B2033639 : Blo 1354996 2033639 := bstep (se 1 (by rfl) ⟨1525229, by rfl⟩ : syracuseStep 2033639 = 3050459) B3050459
theorem B2033657 : Blo 1354996 2033657 := bstep (se 2 (by rfl) ⟨762621, by rfl⟩ : syracuseStep 2033657 = 1525243) B1525243
theorem B2033759 : Blo 1354996 2033759 := bstep (se 1 (by rfl) ⟨1525319, by rfl⟩ : syracuseStep 2033759 = 3050639) B3050639
theorem B1525855 : Blo 1354996 1525855 := bstep (se 1 (by rfl) ⟨1144391, by rfl⟩ : syracuseStep 1525855 = 2288783) B2288783
theorem B2033819 : Blo 1354996 2033819 := bstep (se 1 (by rfl) ⟨1525364, by rfl⟩ : syracuseStep 2033819 = 3050729) B3050729
theorem B2033855 : Blo 1354996 2033855 := bstep (se 1 (by rfl) ⟨1525391, by rfl⟩ : syracuseStep 2033855 = 3050783) B3050783
theorem B2033897 : Blo 1354996 2033897 := bstep (se 2 (by rfl) ⟨762711, by rfl⟩ : syracuseStep 2033897 = 1525423) B1525423
theorem B6867179 : Blo 1354996 6867179 := bstep (se 1 (by rfl) ⟨5150384, by rfl⟩ : syracuseStep 6867179 = 10300769) B10300769
theorem B3049721 : Blo 1354996 3049721 := bstep (se 2 (by rfl) ⟨1143645, by rfl⟩ : syracuseStep 3049721 = 2287291) B2287291
theorem B26052911 : Blo 1354996 26052911 := bstep (se 1 (by rfl) ⟨19539683, by rfl⟩ : syracuseStep 26052911 = 39079367) B39079367
theorem B3049775 : Blo 1354996 3049775 := bstep (se 1 (by rfl) ⟨2287331, by rfl⟩ : syracuseStep 3049775 = 4574663) B4574663
theorem B2287919 : Blo 1354996 2287919 := bstep (se 1 (by rfl) ⟨1715939, by rfl⟩ : syracuseStep 2287919 = 3431879) B3431879
theorem B3860875 : Blo 1354996 3860875 := bstep (se 1 (by rfl) ⟨2895656, by rfl⟩ : syracuseStep 3860875 = 5791313) B5791313
theorem B254003633 : Blo 1354996 254003633 := bstep (se 2 (by rfl) ⟨95251362, by rfl⟩ : syracuseStep 254003633 = 190502725) B190502725
theorem B3049991 : Blo 1354996 3049991 := bstep (se 1 (by rfl) ⟨2287493, by rfl⟩ : syracuseStep 3049991 = 4574987) B4574987
theorem B2288155 : Blo 1354996 2288155 := bstep (se 1 (by rfl) ⟨1716116, by rfl⟩ : syracuseStep 2288155 = 3432233) B3432233
theorem B2034203 : Blo 1354996 2034203 := bstep (se 1 (by rfl) ⟨1525652, by rfl⟩ : syracuseStep 2034203 = 3051305) B3051305
theorem B2034281 : Blo 1354996 2034281 := bstep (se 2 (by rfl) ⟨762855, by rfl⟩ : syracuseStep 2034281 = 1525711) B1525711
theorem B7719563 : Blo 1354996 7719563 := bstep (se 1 (by rfl) ⟨5789672, by rfl⟩ : syracuseStep 7719563 = 11579345) B11579345
theorem B3050171 : Blo 1354996 3050171 := bstep (se 1 (by rfl) ⟨2287628, by rfl⟩ : syracuseStep 3050171 = 4575257) B4575257
theorem B56421305 : Blo 1354996 56421305 := bstep (se 2 (by rfl) ⟨21157989, by rfl⟩ : syracuseStep 56421305 = 42315979) B42315979
theorem B2034809 : Blo 1354996 2034809 := bstep (se 2 (by rfl) ⟨763053, by rfl⟩ : syracuseStep 2034809 = 1526107) B1526107
theorem B2034911 : Blo 1354996 2034911 := bstep (se 1 (by rfl) ⟨1526183, by rfl⟩ : syracuseStep 2034911 = 3052367) B3052367
theorem B2034953 : Blo 1354996 2034953 := bstep (se 2 (by rfl) ⟨763107, by rfl⟩ : syracuseStep 2034953 = 1526215) B1526215
theorem B32984333 : Blo 1354996 32984333 := bstep (se 3 (by rfl) ⟨6184562, by rfl⟩ : syracuseStep 32984333 = 12369125) B12369125
theorem B7720271 : Blo 1354996 7720271 := bstep (se 1 (by rfl) ⟨5790203, by rfl⟩ : syracuseStep 7720271 = 11580407) B11580407
theorem B7728493 : Blo 1354996 7728493 := bstep (se 3 (by rfl) ⟨1449092, by rfl⟩ : syracuseStep 7728493 = 2898185) B2898185
theorem B2035055 : Blo 1354996 2035055 := bstep (se 1 (by rfl) ⟨1526291, by rfl⟩ : syracuseStep 2035055 = 3052583) B3052583
theorem B4124087 : Blo 1354996 4124087 := bstep (se 1 (by rfl) ⟨3093065, by rfl⟩ : syracuseStep 4124087 = 6186131) B6186131
theorem B1355239 : Blo 1354996 1355239 := bstep (se 1 (by rfl) ⟨1016429, by rfl⟩ : syracuseStep 1355239 = 2032859) B2032859
theorem B2289127 : Blo 1354996 2289127 := bstep (se 1 (by rfl) ⟨1716845, by rfl⟩ : syracuseStep 2289127 = 3433691) B3433691
theorem B2035175 : Blo 1354996 2035175 := bstep (se 1 (by rfl) ⟨1526381, by rfl⟩ : syracuseStep 2035175 = 3052763) B3052763
theorem B3050999 : Blo 1354996 3050999 := bstep (se 1 (by rfl) ⟨2288249, by rfl⟩ : syracuseStep 3050999 = 4576499) B4576499
theorem B6868475 : Blo 1354996 6868475 := bstep (se 1 (by rfl) ⟨5151356, by rfl⟩ : syracuseStep 6868475 = 10302713) B10302713
theorem B3051071 : Blo 1354996 3051071 := bstep (se 1 (by rfl) ⟨2288303, by rfl⟩ : syracuseStep 3051071 = 4576607) B4576607
theorem B2289215 : Blo 1354996 2289215 := bstep (se 1 (by rfl) ⟨1716911, by rfl⟩ : syracuseStep 2289215 = 3433823) B3433823
theorem B1355355 : Blo 1354996 1355355 := bstep (se 1 (by rfl) ⟨1016516, by rfl⟩ : syracuseStep 1355355 = 2033033) B2033033
theorem B2035307 : Blo 1354996 2035307 := bstep (se 1 (by rfl) ⟨1526480, by rfl⟩ : syracuseStep 2035307 = 3052961) B3052961
theorem B6868637 : Blo 1354996 6868637 := bstep (se 3 (by rfl) ⟨1287869, by rfl⟩ : syracuseStep 6868637 = 2575739) B2575739
theorem B2035433 : Blo 1354996 2035433 := bstep (se 2 (by rfl) ⟨763287, by rfl⟩ : syracuseStep 2035433 = 1526575) B1526575
theorem B1355591 : Blo 1354996 1355591 := bstep (se 1 (by rfl) ⟨1016693, by rfl⟩ : syracuseStep 1355591 = 2033387) B2033387
theorem B6180713 : Blo 1354996 6180713 := bstep (se 2 (by rfl) ⟨2317767, by rfl⟩ : syracuseStep 6180713 = 4635535) B4635535
theorem B6860699 : Blo 1354996 6860699 := bstep (se 1 (by rfl) ⟨5145524, by rfl⟩ : syracuseStep 6860699 = 10291049) B10291049
theorem B1355743 : Blo 1354996 1355743 := bstep (se 1 (by rfl) ⟨1016807, by rfl⟩ : syracuseStep 1355743 = 2033615) B2033615
theorem B4575419 : Blo 1354996 4575419 := bstep (se 1 (by rfl) ⟨3431564, by rfl⟩ : syracuseStep 4575419 = 6863129) B6863129
theorem B5796029 : Blo 1354996 5796029 := bstep (se 3 (by rfl) ⟨1086755, by rfl⟩ : syracuseStep 5796029 = 2173511) B2173511
theorem B2289883 : Blo 1354996 2289883 := bstep (se 1 (by rfl) ⟨1717412, by rfl⟩ : syracuseStep 2289883 = 3434825) B3434825
theorem B1356007 : Blo 1354996 1356007 := bstep (se 1 (by rfl) ⟨1017005, by rfl⟩ : syracuseStep 1356007 = 2034011) B2034011
theorem B1356159 : Blo 1354996 1356159 := bstep (se 1 (by rfl) ⟨1017119, by rfl⟩ : syracuseStep 1356159 = 2034239) B2034239
theorem B1356239 : Blo 1354996 1356239 := bstep (se 1 (by rfl) ⟨1017179, by rfl⟩ : syracuseStep 1356239 = 2034359) B2034359
theorem B4886999 : Blo 1354996 4886999 := bstep (se 1 (by rfl) ⟨3665249, by rfl⟩ : syracuseStep 4886999 = 7330499) B7330499
theorem B4641239 : Blo 1354996 4641239 := bstep (se 1 (by rfl) ⟨3480929, by rfl⟩ : syracuseStep 4641239 = 6961859) B6961859
theorem B3052025 : Blo 1354996 3052025 := bstep (se 2 (by rfl) ⟨1144509, by rfl⟩ : syracuseStep 3052025 = 2289019) B2289019
theorem B78180875 : Blo 1354996 78180875 := bstep (se 1 (by rfl) ⟨58635656, by rfl⟩ : syracuseStep 78180875 = 117271313) B117271313
theorem B14660129 : Blo 1354996 14660129 := bstep (se 2 (by rfl) ⟨5497548, by rfl⟩ : syracuseStep 14660129 = 10995097) B10995097
theorem B3052115 : Blo 1354996 3052115 := bstep (se 1 (by rfl) ⟨2289086, by rfl⟩ : syracuseStep 3052115 = 4578173) B4578173
theorem B1356391 : Blo 1354996 1356391 := bstep (se 1 (by rfl) ⟨1017293, by rfl⟩ : syracuseStep 1356391 = 2034587) B2034587
theorem B4575905 : Blo 1354996 4575905 := bstep (se 2 (by rfl) ⟨1715964, by rfl⟩ : syracuseStep 4575905 = 3431929) B3431929
theorem B3052295 : Blo 1354996 3052295 := bstep (se 1 (by rfl) ⟨2289221, by rfl⟩ : syracuseStep 3052295 = 4578443) B4578443
theorem B1356655 : Blo 1354996 1356655 := bstep (se 1 (by rfl) ⟨1017491, by rfl⟩ : syracuseStep 1356655 = 2034983) B2034983
theorem B1356711 : Blo 1354996 1356711 := bstep (se 1 (by rfl) ⟨1017533, by rfl⟩ : syracuseStep 1356711 = 2035067) B2035067
theorem B1356795 : Blo 1354996 1356795 := bstep (se 1 (by rfl) ⟨1017596, by rfl⟩ : syracuseStep 1356795 = 2035193) B2035193
theorem B1356863 : Blo 1354996 1356863 := bstep (se 1 (by rfl) ⟨1017647, by rfl⟩ : syracuseStep 1356863 = 2035295) B2035295
theorem B8688815 : Blo 1354996 8688815 := bstep (se 1 (by rfl) ⟨6516611, by rfl⟩ : syracuseStep 8688815 = 13033223) B13033223
theorem B7328987 : Blo 1354996 7328987 := bstep (se 1 (by rfl) ⟨5496740, by rfl⟩ : syracuseStep 7328987 = 10993481) B10993481
theorem B3863963 : Blo 1354996 3863963 := bstep (se 1 (by rfl) ⟨2897972, by rfl⟩ : syracuseStep 3863963 = 5795945) B5795945
theorem B4576769 : Blo 1354996 4576769 := bstep (se 2 (by rfl) ⟨1716288, by rfl⟩ : syracuseStep 4576769 = 3432577) B3432577
theorem B16487975 : Blo 1354996 16487975 := bstep (se 1 (by rfl) ⟨12365981, by rfl⟩ : syracuseStep 16487975 = 24731963) B24731963
theorem B19559981 : Blo 1354996 19559981 := bstep (se 3 (by rfl) ⟨3667496, by rfl⟩ : syracuseStep 19559981 = 7334993) B7334993
theorem B9778897 : Blo 1354996 9778897 := bstep (se 2 (by rfl) ⟨3667086, by rfl⟩ : syracuseStep 9778897 = 7334173) B7334173
theorem B1931087 : Blo 1354996 1931087 := bstep (se 1 (by rfl) ⟨1448315, by rfl⟩ : syracuseStep 1931087 = 2896631) B2896631
theorem B7722935 : Blo 1354996 7722935 := bstep (se 1 (by rfl) ⟨5792201, by rfl⟩ : syracuseStep 7722935 = 11584403) B11584403
theorem B4577255 : Blo 1354996 4577255 := bstep (se 1 (by rfl) ⟨3432941, by rfl⟩ : syracuseStep 4577255 = 6865883) B6865883
theorem B15456257 : Blo 1354996 15456257 := bstep (se 2 (by rfl) ⟨5796096, by rfl⟩ : syracuseStep 15456257 = 11592193) B11592193
theorem B4577363 : Blo 1354996 4577363 := bstep (se 1 (by rfl) ⟨3433022, by rfl⟩ : syracuseStep 4577363 = 6866045) B6866045
theorem B3430633 : Blo 1354996 3430633 := bstep (se 2 (by rfl) ⟨1286487, by rfl⟩ : syracuseStep 3430633 = 2572975) B2572975
theorem B4577579 : Blo 1354996 4577579 := bstep (se 1 (by rfl) ⟨3433184, by rfl⟩ : syracuseStep 4577579 = 6866369) B6866369
theorem B6519113 : Blo 1354996 6519113 := bstep (se 2 (by rfl) ⟨2444667, by rfl⟩ : syracuseStep 6519113 = 4889335) B4889335
theorem B23173451 : Blo 1354996 23173451 := bstep (se 1 (by rfl) ⟨17380088, by rfl⟩ : syracuseStep 23173451 = 34760177) B34760177
theorem B8681843 : Blo 1354996 8681843 := bstep (se 1 (by rfl) ⟨6511382, by rfl⟩ : syracuseStep 8681843 = 13022765) B13022765
theorem B4577849 : Blo 1354996 4577849 := bstep (se 2 (by rfl) ⟨1716693, by rfl⟩ : syracuseStep 4577849 = 3433387) B3433387
theorem B98966123 : Blo 1354996 98966123 := bstep (se 1 (by rfl) ⟨74224592, by rfl⟩ : syracuseStep 98966123 = 148449185) B148449185
theorem B1629019 : Blo 1354996 1629019 := bstep (se 1 (by rfl) ⟨1221764, by rfl⟩ : syracuseStep 1629019 = 2443529) B2443529
theorem B6511519 : Blo 1354996 6511519 := bstep (se 1 (by rfl) ⟨4883639, by rfl⟩ : syracuseStep 6511519 = 9767279) B9767279
theorem B3431393 : Blo 1354996 3431393 := bstep (se 2 (by rfl) ⟨1286772, by rfl⟩ : syracuseStep 3431393 = 2573545) B2573545
theorem B1629163 : Blo 1354996 1629163 := bstep (se 1 (by rfl) ⟨1221872, by rfl⟩ : syracuseStep 1629163 = 2443745) B2443745
theorem B8682511 : Blo 1354996 8682511 := bstep (se 1 (by rfl) ⟨6511883, by rfl⟩ : syracuseStep 8682511 = 13023767) B13023767
theorem B39083057 : Blo 1354996 39083057 := bstep (se 2 (by rfl) ⟨14656146, by rfl⟩ : syracuseStep 39083057 = 29312293) B29312293
theorem B9780743 : Blo 1354996 9780743 := bstep (se 1 (by rfl) ⟨7335557, by rfl⟩ : syracuseStep 9780743 = 14671115) B14671115
theorem B6954781 : Blo 1354996 6954781 := bstep (se 3 (by rfl) ⟨1304021, by rfl⟩ : syracuseStep 6954781 = 2608043) B2608043
theorem B2170795 : Blo 1354996 2170795 := bstep (se 1 (by rfl) ⟨1628096, by rfl⟩ : syracuseStep 2170795 = 3256193) B3256193
theorem B16498637 : Blo 1354996 16498637 := bstep (se 3 (by rfl) ⟨3093494, by rfl⟩ : syracuseStep 16498637 = 6186989) B6186989
theorem B5292071 : Blo 1354996 5292071 := bstep (se 1 (by rfl) ⟨3969053, by rfl⟩ : syracuseStep 5292071 = 7938107) B7938107
theorem B9773419 : Blo 1354996 9773419 := bstep (se 1 (by rfl) ⟨7330064, by rfl⟩ : syracuseStep 9773419 = 14660129) B14660129
theorem B5792543 : Blo 1354996 5792543 := bstep (se 1 (by rfl) ⟨4344407, by rfl⟩ : syracuseStep 5792543 = 8688815) B8688815
theorem B21980069 : Blo 1354996 21980069 := bstep (se 4 (by rfl) ⟨2060631, by rfl⟩ : syracuseStep 21980069 = 4121263) B4121263
theorem B2032583 : Blo 1354996 2032583 := bstep (se 1 (by rfl) ⟨1524437, by rfl⟩ : syracuseStep 2032583 = 3048875) B3048875
theorem B23151581 : Blo 1354996 23151581 := bstep (se 3 (by rfl) ⟨4340921, by rfl⟩ : syracuseStep 23151581 = 8681843) B8681843
theorem B5145707 : Blo 1354996 5145707 := bstep (se 1 (by rfl) ⟨3859280, by rfl⟩ : syracuseStep 5145707 = 7718561) B7718561
theorem B2032751 : Blo 1354996 2032751 := bstep (se 1 (by rfl) ⟨1524563, by rfl⟩ : syracuseStep 2032751 = 3049127) B3049127
theorem B1524847 : Blo 1354996 1524847 := bstep (se 1 (by rfl) ⟨1143635, by rfl⟩ : syracuseStep 1524847 = 2287271) B2287271
theorem B2172025 : Blo 1354996 2172025 := bstep (se 2 (by rfl) ⟨814509, by rfl⟩ : syracuseStep 2172025 = 1629019) B1629019
theorem B72369395 : Blo 1354996 72369395 := bstep (se 1 (by rfl) ⟨54277046, by rfl⟩ : syracuseStep 72369395 = 108554093) B108554093
theorem B2032943 : Blo 1354996 2032943 := bstep (se 1 (by rfl) ⟨1524707, by rfl⟩ : syracuseStep 2032943 = 3049415) B3049415
theorem B11576681 : Blo 1354996 11576681 := bstep (se 2 (by rfl) ⟨4341255, by rfl⟩ : syracuseStep 11576681 = 8682511) B8682511
theorem B52159949 : Blo 1354996 52159949 := bstep (se 3 (by rfl) ⟨9779990, by rfl⟩ : syracuseStep 52159949 = 19559981) B19559981
theorem B3048929 : Blo 1354996 3048929 := bstep (se 2 (by rfl) ⟨1143348, by rfl⟩ : syracuseStep 3048929 = 2286697) B2286697
theorem B2033147 : Blo 1354996 2033147 := bstep (se 1 (by rfl) ⟨1524860, by rfl⟩ : syracuseStep 2033147 = 3049721) B3049721
theorem B17368607 : Blo 1354996 17368607 := bstep (se 1 (by rfl) ⟨13026455, by rfl⟩ : syracuseStep 17368607 = 26052911) B26052911
theorem B2033183 : Blo 1354996 2033183 := bstep (se 1 (by rfl) ⟨1524887, by rfl⟩ : syracuseStep 2033183 = 3049775) B3049775
theorem B1525279 : Blo 1354996 1525279 := bstep (se 1 (by rfl) ⟨1143959, by rfl⟩ : syracuseStep 1525279 = 2287919) B2287919
theorem B5146193 : Blo 1354996 5146193 := bstep (se 2 (by rfl) ⟨1929822, by rfl⟩ : syracuseStep 5146193 = 3859645) B3859645
theorem B2033327 : Blo 1354996 2033327 := bstep (se 1 (by rfl) ⟨1524995, by rfl⟩ : syracuseStep 2033327 = 3049991) B3049991
theorem B5146375 : Blo 1354996 5146375 := bstep (se 1 (by rfl) ⟨3859781, by rfl⟩ : syracuseStep 5146375 = 7719563) B7719563
theorem B2033447 : Blo 1354996 2033447 := bstep (se 1 (by rfl) ⟨1525085, by rfl⟩ : syracuseStep 2033447 = 3050171) B3050171
theorem B2287595 : Blo 1354996 2287595 := bstep (se 1 (by rfl) ⟨1715696, by rfl⟩ : syracuseStep 2287595 = 3431393) B3431393
theorem B5146649 : Blo 1354996 5146649 := bstep (se 2 (by rfl) ⟨1929993, by rfl⟩ : syracuseStep 5146649 = 3859987) B3859987
theorem B21989555 : Blo 1354996 21989555 := bstep (se 1 (by rfl) ⟨16492166, by rfl⟩ : syracuseStep 21989555 = 32984333) B32984333
theorem B5146847 : Blo 1354996 5146847 := bstep (se 1 (by rfl) ⟨3860135, by rfl⟩ : syracuseStep 5146847 = 7720271) B7720271
theorem B2787625 : Blo 1354996 2787625 := bstep (se 2 (by rfl) ⟨1045359, by rfl⟩ : syracuseStep 2787625 = 2090719) B2090719
theorem B2033999 : Blo 1354996 2033999 := bstep (se 1 (by rfl) ⟨1525499, by rfl⟩ : syracuseStep 2033999 = 3050999) B3050999
theorem B2034047 : Blo 1354996 2034047 := bstep (se 1 (by rfl) ⟨1525535, by rfl⟩ : syracuseStep 2034047 = 3051071) B3051071
theorem B1526143 : Blo 1354996 1526143 := bstep (se 1 (by rfl) ⟨1144607, by rfl⟩ : syracuseStep 1526143 = 2289215) B2289215
theorem B2034089 : Blo 1354996 2034089 := bstep (se 2 (by rfl) ⟨762783, by rfl⟩ : syracuseStep 2034089 = 1525567) B1525567
theorem B2894393 : Blo 1354996 2894393 := bstep (se 2 (by rfl) ⟨1085397, by rfl⟩ : syracuseStep 2894393 = 2170795) B2170795
theorem B4573799 : Blo 1354996 4573799 := bstep (se 1 (by rfl) ⟨3430349, by rfl⟩ : syracuseStep 4573799 = 6860699) B6860699
theorem B3050279 : Blo 1354996 3050279 := bstep (se 1 (by rfl) ⟨2287709, by rfl⟩ : syracuseStep 3050279 = 4575419) B4575419
theorem B2034473 : Blo 1354996 2034473 := bstep (se 2 (by rfl) ⟨762927, by rfl⟩ : syracuseStep 2034473 = 1525855) B1525855
theorem B4574177 : Blo 1354996 4574177 := bstep (se 2 (by rfl) ⟨1715316, by rfl⟩ : syracuseStep 4574177 = 3430633) B3430633
theorem B2034683 : Blo 1354996 2034683 := bstep (se 1 (by rfl) ⟨1526012, by rfl⟩ : syracuseStep 2034683 = 3052025) B3052025
theorem B52120583 : Blo 1354996 52120583 := bstep (se 1 (by rfl) ⟨39090437, by rfl⟩ : syracuseStep 52120583 = 78180875) B78180875
theorem B2034743 : Blo 1354996 2034743 := bstep (se 1 (by rfl) ⟨1526057, by rfl⟩ : syracuseStep 2034743 = 3052115) B3052115
theorem B3050603 : Blo 1354996 3050603 := bstep (se 1 (by rfl) ⟨2287952, by rfl⟩ : syracuseStep 3050603 = 4575905) B4575905
theorem B2034863 : Blo 1354996 2034863 := bstep (se 1 (by rfl) ⟨1526147, by rfl⟩ : syracuseStep 2034863 = 3052295) B3052295
theorem B7728311 : Blo 1354996 7728311 := bstep (se 1 (by rfl) ⟨5796233, by rfl⟩ : syracuseStep 7728311 = 11592467) B11592467
theorem B5147833 : Blo 1354996 5147833 := bstep (se 2 (by rfl) ⟨1930437, by rfl⟩ : syracuseStep 5147833 = 3860875) B3860875
theorem B6860051 : Blo 1354996 6860051 := bstep (se 1 (by rfl) ⟨5145038, by rfl⟩ : syracuseStep 6860051 = 10290077) B10290077
theorem B3050873 : Blo 1354996 3050873 := bstep (se 2 (by rfl) ⟨1144077, by rfl⟩ : syracuseStep 3050873 = 2288155) B2288155
theorem B1355135 : Blo 1354996 1355135 := bstep (se 1 (by rfl) ⟨1016351, by rfl⟩ : syracuseStep 1355135 = 2032703) B2032703
theorem B1355163 : Blo 1354996 1355163 := bstep (se 1 (by rfl) ⟨1016372, by rfl⟩ : syracuseStep 1355163 = 2032745) B2032745
theorem B1355231 : Blo 1354996 1355231 := bstep (se 1 (by rfl) ⟨1016423, by rfl⟩ : syracuseStep 1355231 = 2032847) B2032847
theorem B4885991 : Blo 1354996 4885991 := bstep (se 1 (by rfl) ⟨3664493, by rfl⟩ : syracuseStep 4885991 = 7328987) B7328987
theorem B1355367 : Blo 1354996 1355367 := bstep (se 1 (by rfl) ⟨1016525, by rfl⟩ : syracuseStep 1355367 = 2033051) B2033051
theorem B2575975 : Blo 1354996 2575975 := bstep (se 1 (by rfl) ⟨1931981, by rfl⟩ : syracuseStep 2575975 = 3863963) B3863963
theorem B105713261 : Blo 1354996 105713261 := bstep (se 3 (by rfl) ⟨19821236, by rfl⟩ : syracuseStep 105713261 = 39642473) B39642473
theorem B3051179 : Blo 1354996 3051179 := bstep (se 1 (by rfl) ⟨2288384, by rfl⟩ : syracuseStep 3051179 = 4576769) B4576769
theorem B1355515 : Blo 1354996 1355515 := bstep (se 1 (by rfl) ⟨1016636, by rfl⟩ : syracuseStep 1355515 = 2033273) B2033273
theorem B1355583 : Blo 1354996 1355583 := bstep (se 1 (by rfl) ⟨1016687, by rfl⟩ : syracuseStep 1355583 = 2033375) B2033375
theorem B5795671 : Blo 1354996 5795671 := bstep (se 1 (by rfl) ⟨4346753, by rfl⟩ : syracuseStep 5795671 = 8693507) B8693507
theorem B12365693 : Blo 1354996 12365693 := bstep (se 3 (by rfl) ⟨2318567, by rfl⟩ : syracuseStep 12365693 = 4637135) B4637135
theorem B1355647 : Blo 1354996 1355647 := bstep (se 1 (by rfl) ⟨1016735, by rfl⟩ : syracuseStep 1355647 = 2033471) B2033471
theorem B5148623 : Blo 1354996 5148623 := bstep (se 1 (by rfl) ⟨3861467, by rfl⟩ : syracuseStep 5148623 = 7722935) B7722935
theorem B1355759 : Blo 1354996 1355759 := bstep (se 1 (by rfl) ⟨1016819, by rfl⟩ : syracuseStep 1355759 = 2033639) B2033639
theorem B3051503 : Blo 1354996 3051503 := bstep (se 1 (by rfl) ⟨2288627, by rfl⟩ : syracuseStep 3051503 = 4577255) B4577255
theorem B1355771 : Blo 1354996 1355771 := bstep (se 1 (by rfl) ⟨1016828, by rfl⟩ : syracuseStep 1355771 = 2033657) B2033657
theorem B3051575 : Blo 1354996 3051575 := bstep (se 1 (by rfl) ⟨2288681, by rfl⟩ : syracuseStep 3051575 = 4577363) B4577363
theorem B1355839 : Blo 1354996 1355839 := bstep (se 1 (by rfl) ⟨1016879, by rfl⟩ : syracuseStep 1355839 = 2033759) B2033759
theorem B1355879 : Blo 1354996 1355879 := bstep (se 1 (by rfl) ⟨1016909, by rfl⟩ : syracuseStep 1355879 = 2033819) B2033819
theorem B1355903 : Blo 1354996 1355903 := bstep (se 1 (by rfl) ⟨1016927, by rfl⟩ : syracuseStep 1355903 = 2033855) B2033855
theorem B1355931 : Blo 1354996 1355931 := bstep (se 1 (by rfl) ⟨1016948, by rfl⟩ : syracuseStep 1355931 = 2033897) B2033897
theorem B3051719 : Blo 1354996 3051719 := bstep (se 1 (by rfl) ⟨2288789, by rfl⟩ : syracuseStep 3051719 = 4577579) B4577579
theorem B4346075 : Blo 1354996 4346075 := bstep (se 1 (by rfl) ⟨3259556, by rfl⟩ : syracuseStep 4346075 = 6519113) B6519113
theorem B1356135 : Blo 1354996 1356135 := bstep (se 1 (by rfl) ⟨1017101, by rfl⟩ : syracuseStep 1356135 = 2034203) B2034203
theorem B3051899 : Blo 1354996 3051899 := bstep (se 1 (by rfl) ⟨2288924, by rfl⟩ : syracuseStep 3051899 = 4577849) B4577849
theorem B1356187 : Blo 1354996 1356187 := bstep (se 1 (by rfl) ⟨1017140, by rfl⟩ : syracuseStep 1356187 = 2034281) B2034281
theorem B37614203 : Blo 1354996 37614203 := bstep (se 1 (by rfl) ⟨28210652, by rfl⟩ : syracuseStep 37614203 = 56421305) B56421305
theorem B3052169 : Blo 1354996 3052169 := bstep (se 2 (by rfl) ⟨1144563, by rfl⟩ : syracuseStep 3052169 = 2289127) B2289127
theorem B26055371 : Blo 1354996 26055371 := bstep (se 1 (by rfl) ⟨19541528, by rfl⟩ : syracuseStep 26055371 = 39083057) B39083057
theorem B1356539 : Blo 1354996 1356539 := bstep (se 1 (by rfl) ⟨1017404, by rfl⟩ : syracuseStep 1356539 = 2034809) B2034809
theorem B1356607 : Blo 1354996 1356607 := bstep (se 1 (by rfl) ⟨1017455, by rfl⟩ : syracuseStep 1356607 = 2034911) B2034911
theorem B1356635 : Blo 1354996 1356635 := bstep (se 1 (by rfl) ⟨1017476, by rfl⟩ : syracuseStep 1356635 = 2034953) B2034953
theorem B5149565 : Blo 1354996 5149565 := bstep (se 3 (by rfl) ⟨965543, by rfl⟩ : syracuseStep 5149565 = 1931087) B1931087
theorem B1356703 : Blo 1354996 1356703 := bstep (se 1 (by rfl) ⟨1017527, by rfl⟩ : syracuseStep 1356703 = 2035055) B2035055
theorem B13038529 : Blo 1354996 13038529 := bstep (se 2 (by rfl) ⟨4889448, by rfl⟩ : syracuseStep 13038529 = 9778897) B9778897
theorem B2749391 : Blo 1354996 2749391 := bstep (se 1 (by rfl) ⟨2062043, by rfl⟩ : syracuseStep 2749391 = 4124087) B4124087
theorem B1356783 : Blo 1354996 1356783 := bstep (se 1 (by rfl) ⟨1017587, by rfl⟩ : syracuseStep 1356783 = 2035175) B2035175
theorem B1356871 : Blo 1354996 1356871 := bstep (se 1 (by rfl) ⟨1017653, by rfl⟩ : syracuseStep 1356871 = 2035307) B2035307
theorem B1356955 : Blo 1354996 1356955 := bstep (se 1 (by rfl) ⟨1017716, by rfl⟩ : syracuseStep 1356955 = 2035433) B2035433
theorem B8688869 : Blo 1354996 8688869 := bstep (se 4 (by rfl) ⟨814581, by rfl⟩ : syracuseStep 8688869 = 1629163) B1629163
theorem B10999091 : Blo 1354996 10999091 := bstep (se 1 (by rfl) ⟨8249318, by rfl⟩ : syracuseStep 10999091 = 16498637) B16498637
theorem B3052907 : Blo 1354996 3052907 := bstep (se 1 (by rfl) ⟨2289680, by rfl⟩ : syracuseStep 3052907 = 4579361) B4579361
theorem B3864019 : Blo 1354996 3864019 := bstep (se 1 (by rfl) ⟨2898014, by rfl⟩ : syracuseStep 3864019 = 5796029) B5796029
theorem B7722479 : Blo 1354996 7722479 := bstep (se 1 (by rfl) ⟨5791859, by rfl⟩ : syracuseStep 7722479 = 11583719) B11583719
theorem B3053177 : Blo 1354996 3053177 := bstep (se 2 (by rfl) ⟨1144941, by rfl⟩ : syracuseStep 3053177 = 2289883) B2289883
theorem B3257999 : Blo 1354996 3257999 := bstep (se 1 (by rfl) ⟨2443499, by rfl⟩ : syracuseStep 3257999 = 4886999) B4886999
theorem B9410231 : Blo 1354996 9410231 := bstep (se 1 (by rfl) ⟨7057673, by rfl⟩ : syracuseStep 9410231 = 14115347) B14115347
theorem B8362283 : Blo 1354996 8362283 := bstep (se 1 (by rfl) ⟨6271712, by rfl⟩ : syracuseStep 8362283 = 12543425) B12543425
theorem B4577633 : Blo 1354996 4577633 := bstep (se 2 (by rfl) ⟨1716612, by rfl⟩ : syracuseStep 4577633 = 3433225) B3433225
theorem B11581805 : Blo 1354996 11581805 := bstep (se 3 (by rfl) ⟨2171588, by rfl⟩ : syracuseStep 11581805 = 4343177) B4343177
theorem B10991983 : Blo 1354996 10991983 := bstep (se 1 (by rfl) ⟨8243987, by rfl⟩ : syracuseStep 10991983 = 16487975) B16487975
theorem B8682025 : Blo 1354996 8682025 := bstep (se 2 (by rfl) ⟨3255759, by rfl⟩ : syracuseStep 8682025 = 6511519) B6511519
theorem B12376637 : Blo 1354996 12376637 := bstep (se 3 (by rfl) ⟨2320619, by rfl⟩ : syracuseStep 12376637 = 4641239) B4641239
theorem B10304171 : Blo 1354996 10304171 := bstep (se 1 (by rfl) ⟨7728128, by rfl⟩ : syracuseStep 10304171 = 15456257) B15456257
theorem B4578119 : Blo 1354996 4578119 := bstep (se 1 (by rfl) ⟨3433589, by rfl⟩ : syracuseStep 4578119 = 6867179) B6867179
theorem B15448967 : Blo 1354996 15448967 := bstep (se 1 (by rfl) ⟨11586725, by rfl⟩ : syracuseStep 15448967 = 23173451) B23173451
theorem B169335755 : Blo 1354996 169335755 := bstep (se 1 (by rfl) ⟨127001816, by rfl⟩ : syracuseStep 169335755 = 254003633) B254003633
theorem B65977415 : Blo 1354996 65977415 := bstep (se 1 (by rfl) ⟨49483061, by rfl⟩ : syracuseStep 65977415 = 98966123) B98966123
theorem B10304657 : Blo 1354996 10304657 := bstep (se 2 (by rfl) ⟨3864246, by rfl⟩ : syracuseStep 10304657 = 7728493) B7728493
theorem B7724393 : Blo 1354996 7724393 := bstep (se 2 (by rfl) ⟨2896647, by rfl⟩ : syracuseStep 7724393 = 5793295) B5793295
theorem B4578983 : Blo 1354996 4578983 := bstep (se 1 (by rfl) ⟨3434237, by rfl⟩ : syracuseStep 4578983 = 6868475) B6868475
theorem B6520495 : Blo 1354996 6520495 := bstep (se 1 (by rfl) ⟨4890371, by rfl⟩ : syracuseStep 6520495 = 9780743) B9780743
theorem B9273041 : Blo 1354996 9273041 := bstep (se 2 (by rfl) ⟨3477390, by rfl⟩ : syracuseStep 9273041 = 6954781) B6954781
theorem B4579091 : Blo 1354996 4579091 := bstep (se 1 (by rfl) ⟨3434318, by rfl⟩ : syracuseStep 4579091 = 6868637) B6868637
theorem B4120475 : Blo 1354996 4120475 := bstep (se 1 (by rfl) ⟨3090356, by rfl⟩ : syracuseStep 4120475 = 6180713) B6180713
theorem B25076135 : Blo 1354996 25076135 := bstep (se 1 (by rfl) ⟨18807101, by rfl⟩ : syracuseStep 25076135 = 37614203) B37614203
theorem B14655977 : Blo 1354996 14655977 := bstep (se 2 (by rfl) ⟨5495991, by rfl⟩ : syracuseStep 14655977 = 10991983) B10991983
theorem B3433043 : Blo 1354996 3433043 := bstep (se 1 (by rfl) ⟨2574782, by rfl⟩ : syracuseStep 3433043 = 5149565) B5149565
theorem B15434387 : Blo 1354996 15434387 := bstep (se 1 (by rfl) ⟨11575790, by rfl⟩ : syracuseStep 15434387 = 23151581) B23151581
theorem B11576033 : Blo 1354996 11576033 := bstep (se 2 (by rfl) ⟨4341012, by rfl⟩ : syracuseStep 11576033 = 8682025) B8682025
theorem B5792579 : Blo 1354996 5792579 := bstep (se 1 (by rfl) ⟨4344434, by rfl⟩ : syracuseStep 5792579 = 8688869) B8688869
theorem B7332727 : Blo 1354996 7332727 := bstep (se 1 (by rfl) ⟨5499545, by rfl⟩ : syracuseStep 7332727 = 10999091) B10999091
theorem B7717787 : Blo 1354996 7717787 := bstep (se 1 (by rfl) ⟨5788340, by rfl⟩ : syracuseStep 7717787 = 11576681) B11576681
theorem B2032619 : Blo 1354996 2032619 := bstep (se 1 (by rfl) ⟨1524464, by rfl⟩ : syracuseStep 2032619 = 3048929) B3048929
theorem B2171999 : Blo 1354996 2171999 := bstep (se 1 (by rfl) ⟨1628999, by rfl⟩ : syracuseStep 2171999 = 3257999) B3257999
theorem B17384705 : Blo 1354996 17384705 := bstep (se 2 (by rfl) ⟨6519264, by rfl⟩ : syracuseStep 17384705 = 13038529) B13038529
theorem B1525063 : Blo 1354996 1525063 := bstep (se 1 (by rfl) ⟨1143797, by rfl⟩ : syracuseStep 1525063 = 2287595) B2287595
theorem B2033129 : Blo 1354996 2033129 := bstep (se 2 (by rfl) ⟨762423, by rfl⟩ : syracuseStep 2033129 = 1524847) B1524847
theorem B8251091 : Blo 1354996 8251091 := bstep (se 1 (by rfl) ⟨6188318, by rfl⟩ : syracuseStep 8251091 = 12376637) B12376637
theorem B3049199 : Blo 1354996 3049199 := bstep (se 1 (by rfl) ⟨2286899, by rfl⟩ : syracuseStep 3049199 = 4573799) B4573799
theorem B2033519 : Blo 1354996 2033519 := bstep (se 1 (by rfl) ⟨1525139, by rfl⟩ : syracuseStep 2033519 = 3050279) B3050279
theorem B10299311 : Blo 1354996 10299311 := bstep (se 1 (by rfl) ⟨7724483, by rfl⟩ : syracuseStep 10299311 = 15448967) B15448967
theorem B3049451 : Blo 1354996 3049451 := bstep (se 1 (by rfl) ⟨2287088, by rfl⟩ : syracuseStep 3049451 = 4574177) B4574177
theorem B2033705 : Blo 1354996 2033705 := bstep (se 2 (by rfl) ⟨762639, by rfl⟩ : syracuseStep 2033705 = 1525279) B1525279
theorem B43984943 : Blo 1354996 43984943 := bstep (se 1 (by rfl) ⟨32988707, by rfl⟩ : syracuseStep 43984943 = 65977415) B65977415
theorem B2033735 : Blo 1354996 2033735 := bstep (se 1 (by rfl) ⟨1525301, by rfl⟩ : syracuseStep 2033735 = 3050603) B3050603
theorem B3434633 : Blo 1354996 3434633 := bstep (se 2 (by rfl) ⟨1287987, by rfl⟩ : syracuseStep 3434633 = 2575975) B2575975
theorem B4573367 : Blo 1354996 4573367 := bstep (se 1 (by rfl) ⟨3430025, by rfl⟩ : syracuseStep 4573367 = 6860051) B6860051
theorem B8693993 : Blo 1354996 8693993 := bstep (se 2 (by rfl) ⟨3260247, by rfl⟩ : syracuseStep 8693993 = 6520495) B6520495
theorem B2033915 : Blo 1354996 2033915 := bstep (se 1 (by rfl) ⟨1525436, by rfl⟩ : syracuseStep 2033915 = 3050873) B3050873
theorem B10987933 : Blo 1354996 10987933 := bstep (se 3 (by rfl) ⟨2060237, by rfl⟩ : syracuseStep 10987933 = 4120475) B4120475
theorem B2034119 : Blo 1354996 2034119 := bstep (se 1 (by rfl) ⟨1525589, by rfl⟩ : syracuseStep 2034119 = 3051179) B3051179
theorem B7727561 : Blo 1354996 7727561 := bstep (se 2 (by rfl) ⟨2897835, by rfl⟩ : syracuseStep 7727561 = 5795671) B5795671
theorem B8243795 : Blo 1354996 8243795 := bstep (se 1 (by rfl) ⟨6182846, by rfl⟩ : syracuseStep 8243795 = 12365693) B12365693
theorem B2034335 : Blo 1354996 2034335 := bstep (se 1 (by rfl) ⟨1525751, by rfl⟩ : syracuseStep 2034335 = 3051503) B3051503
theorem B2034383 : Blo 1354996 2034383 := bstep (se 1 (by rfl) ⟨1525787, by rfl⟩ : syracuseStep 2034383 = 3051575) B3051575
theorem B2034479 : Blo 1354996 2034479 := bstep (se 1 (by rfl) ⟨1525859, by rfl⟩ : syracuseStep 2034479 = 3051719) B3051719
theorem B2034599 : Blo 1354996 2034599 := bstep (se 1 (by rfl) ⟨1525949, by rfl⟩ : syracuseStep 2034599 = 3051899) B3051899
theorem B2034779 : Blo 1354996 2034779 := bstep (se 1 (by rfl) ⟨1526084, by rfl⟩ : syracuseStep 2034779 = 3052169) B3052169
theorem B89197685 : Blo 1354996 89197685 := bstep (se 5 (by rfl) ⟨4181141, by rfl⟩ : syracuseStep 89197685 = 8362283) B8362283
theorem B17370247 : Blo 1354996 17370247 := bstep (se 1 (by rfl) ⟨13027685, by rfl⟩ : syracuseStep 17370247 = 26055371) B26055371
theorem B2034857 : Blo 1354996 2034857 := bstep (se 2 (by rfl) ⟨763071, by rfl⟩ : syracuseStep 2034857 = 1526143) B1526143
theorem B3861695 : Blo 1354996 3861695 := bstep (se 1 (by rfl) ⟨2896271, by rfl⟩ : syracuseStep 3861695 = 5792543) B5792543
theorem B1355055 : Blo 1354996 1355055 := bstep (se 1 (by rfl) ⟨1016291, by rfl⟩ : syracuseStep 1355055 = 2032583) B2032583
theorem B1355167 : Blo 1354996 1355167 := bstep (se 1 (by rfl) ⟨1016375, by rfl⟩ : syracuseStep 1355167 = 2032751) B2032751
theorem B48246263 : Blo 1354996 48246263 := bstep (se 1 (by rfl) ⟨36184697, by rfl⟩ : syracuseStep 48246263 = 72369395) B72369395
theorem B1355295 : Blo 1354996 1355295 := bstep (se 1 (by rfl) ⟨1016471, by rfl⟩ : syracuseStep 1355295 = 2032943) B2032943
theorem B2035271 : Blo 1354996 2035271 := bstep (se 1 (by rfl) ⟨1526453, by rfl⟩ : syracuseStep 2035271 = 3052907) B3052907
theorem B5148319 : Blo 1354996 5148319 := bstep (se 1 (by rfl) ⟨3861239, by rfl⟩ : syracuseStep 5148319 = 7722479) B7722479
theorem B1355431 : Blo 1354996 1355431 := bstep (se 1 (by rfl) ⟨1016573, by rfl⟩ : syracuseStep 1355431 = 2033147) B2033147
theorem B11579071 : Blo 1354996 11579071 := bstep (se 1 (by rfl) ⟨8684303, by rfl⟩ : syracuseStep 11579071 = 17368607) B17368607
theorem B1355455 : Blo 1354996 1355455 := bstep (se 1 (by rfl) ⟨1016591, by rfl⟩ : syracuseStep 1355455 = 2033183) B2033183
theorem B2035451 : Blo 1354996 2035451 := bstep (se 1 (by rfl) ⟨1526588, by rfl⟩ : syracuseStep 2035451 = 3053177) B3053177
theorem B1355551 : Blo 1354996 1355551 := bstep (se 1 (by rfl) ⟨1016663, by rfl⟩ : syracuseStep 1355551 = 2033327) B2033327
theorem B1355631 : Blo 1354996 1355631 := bstep (se 1 (by rfl) ⟨1016723, by rfl⟩ : syracuseStep 1355631 = 2033447) B2033447
theorem B14659703 : Blo 1354996 14659703 := bstep (se 1 (by rfl) ⟨10994777, by rfl⟩ : syracuseStep 14659703 = 21989555) B21989555
theorem B2896033 : Blo 1354996 2896033 := bstep (se 2 (by rfl) ⟨1086012, by rfl⟩ : syracuseStep 2896033 = 2172025) B2172025
theorem B1355999 : Blo 1354996 1355999 := bstep (se 1 (by rfl) ⟨1016999, by rfl⟩ : syracuseStep 1355999 = 2033999) B2033999
theorem B3051755 : Blo 1354996 3051755 := bstep (se 1 (by rfl) ⟨2288816, by rfl⟩ : syracuseStep 3051755 = 4577633) B4577633
theorem B7721203 : Blo 1354996 7721203 := bstep (se 1 (by rfl) ⟨5790902, by rfl⟩ : syracuseStep 7721203 = 11581805) B11581805
theorem B1356031 : Blo 1354996 1356031 := bstep (se 1 (by rfl) ⟨1017023, by rfl⟩ : syracuseStep 1356031 = 2034047) B2034047
theorem B1356059 : Blo 1354996 1356059 := bstep (se 1 (by rfl) ⟨1017044, by rfl⟩ : syracuseStep 1356059 = 2034089) B2034089
theorem B1929595 : Blo 1354996 1929595 := bstep (se 1 (by rfl) ⟨1447196, by rfl⟩ : syracuseStep 1929595 = 2894393) B2894393
theorem B6869447 : Blo 1354996 6869447 := bstep (se 1 (by rfl) ⟨5152085, by rfl⟩ : syracuseStep 6869447 = 10304171) B10304171
theorem B1356315 : Blo 1354996 1356315 := bstep (se 1 (by rfl) ⟨1017236, by rfl⟩ : syracuseStep 1356315 = 2034473) B2034473
theorem B3052079 : Blo 1354996 3052079 := bstep (se 1 (by rfl) ⟨2289059, by rfl⟩ : syracuseStep 3052079 = 4578119) B4578119
theorem B112890503 : Blo 1354996 112890503 := bstep (se 1 (by rfl) ⟨84667877, by rfl⟩ : syracuseStep 112890503 = 169335755) B169335755
theorem B1356455 : Blo 1354996 1356455 := bstep (se 1 (by rfl) ⟨1017341, by rfl⟩ : syracuseStep 1356455 = 2034683) B2034683
theorem B34747055 : Blo 1354996 34747055 := bstep (se 1 (by rfl) ⟨26060291, by rfl⟩ : syracuseStep 34747055 = 52120583) B52120583
theorem B1356495 : Blo 1354996 1356495 := bstep (se 1 (by rfl) ⟨1017371, by rfl⟩ : syracuseStep 1356495 = 2034743) B2034743
theorem B6869771 : Blo 1354996 6869771 := bstep (se 1 (by rfl) ⟨5152328, by rfl⟩ : syracuseStep 6869771 = 10304657) B10304657
theorem B1356575 : Blo 1354996 1356575 := bstep (se 1 (by rfl) ⟨1017431, by rfl⟩ : syracuseStep 1356575 = 2034863) B2034863
theorem B5149595 : Blo 1354996 5149595 := bstep (se 1 (by rfl) ⟨3862196, by rfl⟩ : syracuseStep 5149595 = 7724393) B7724393
theorem B3257327 : Blo 1354996 3257327 := bstep (se 1 (by rfl) ⟨2442995, by rfl⟩ : syracuseStep 3257327 = 4885991) B4885991
theorem B6861833 : Blo 1354996 6861833 := bstep (se 2 (by rfl) ⟨2573187, by rfl⟩ : syracuseStep 6861833 = 5146375) B5146375
theorem B3052655 : Blo 1354996 3052655 := bstep (se 1 (by rfl) ⟨2289491, by rfl⟩ : syracuseStep 3052655 = 4578983) B4578983
theorem B6182027 : Blo 1354996 6182027 := bstep (se 1 (by rfl) ⟨4636520, by rfl⟩ : syracuseStep 6182027 = 9273041) B9273041
theorem B3052727 : Blo 1354996 3052727 := bstep (se 1 (by rfl) ⟨2289545, by rfl⟩ : syracuseStep 3052727 = 4579091) B4579091
theorem B3528047 : Blo 1354996 3528047 := bstep (se 1 (by rfl) ⟨2646035, by rfl⟩ : syracuseStep 3528047 = 5292071) B5292071
theorem B2897383 : Blo 1354996 2897383 := bstep (se 1 (by rfl) ⟨2173037, by rfl⟩ : syracuseStep 2897383 = 4346075) B4346075
theorem B13031225 : Blo 1354996 13031225 := bstep (se 2 (by rfl) ⟨4886709, by rfl⟩ : syracuseStep 13031225 = 9773419) B9773419
theorem B14653379 : Blo 1354996 14653379 := bstep (se 1 (by rfl) ⟨10990034, by rfl⟩ : syracuseStep 14653379 = 21980069) B21980069
theorem B1832927 : Blo 1354996 1832927 := bstep (se 1 (by rfl) ⟨1374695, by rfl⟩ : syracuseStep 1832927 = 2749391) B2749391
theorem B3430471 : Blo 1354996 3430471 := bstep (se 1 (by rfl) ⟨2572853, by rfl⟩ : syracuseStep 3430471 = 5145707) B5145707
theorem B34773299 : Blo 1354996 34773299 := bstep (se 1 (by rfl) ⟨26079974, by rfl⟩ : syracuseStep 34773299 = 52159949) B52159949
theorem B3430795 : Blo 1354996 3430795 := bstep (se 1 (by rfl) ⟨2573096, by rfl⟩ : syracuseStep 3430795 = 5146193) B5146193
theorem B6273487 : Blo 1354996 6273487 := bstep (se 1 (by rfl) ⟨4705115, by rfl⟩ : syracuseStep 6273487 = 9410231) B9410231
theorem B3431099 : Blo 1354996 3431099 := bstep (se 1 (by rfl) ⟨2573324, by rfl⟩ : syracuseStep 3431099 = 5146649) B5146649
theorem B3431231 : Blo 1354996 3431231 := bstep (se 1 (by rfl) ⟨2573423, by rfl⟩ : syracuseStep 3431231 = 5146847) B5146847
theorem B14867333 : Blo 1354996 14867333 := bstep (se 4 (by rfl) ⟨1393812, by rfl⟩ : syracuseStep 14867333 = 2787625) B2787625
theorem B6863777 : Blo 1354996 6863777 := bstep (se 2 (by rfl) ⟨2573916, by rfl⟩ : syracuseStep 6863777 = 5147833) B5147833
theorem B5152025 : Blo 1354996 5152025 := bstep (se 2 (by rfl) ⟨1932009, by rfl⟩ : syracuseStep 5152025 = 3864019) B3864019
theorem B5152207 : Blo 1354996 5152207 := bstep (se 1 (by rfl) ⟨3864155, by rfl⟩ : syracuseStep 5152207 = 7728311) B7728311
theorem B70475507 : Blo 1354996 70475507 := bstep (se 1 (by rfl) ⟨52856630, by rfl⟩ : syracuseStep 70475507 = 105713261) B105713261
theorem B3432415 : Blo 1354996 3432415 := bstep (se 1 (by rfl) ⟨2574311, by rfl⟩ : syracuseStep 3432415 = 5148623) B5148623
theorem B9773135 : Blo 1354996 9773135 := bstep (se 1 (by rfl) ⟨7329851, by rfl⟩ : syracuseStep 9773135 = 14659703) B14659703
theorem B4579631 : Blo 1354996 4579631 := bstep (se 1 (by rfl) ⟨3434723, by rfl⟩ : syracuseStep 4579631 = 6869447) B6869447
theorem B75260335 : Blo 1354996 75260335 := bstep (se 1 (by rfl) ⟨56445251, by rfl⟩ : syracuseStep 75260335 = 112890503) B112890503
theorem B10289591 : Blo 1354996 10289591 := bstep (se 1 (by rfl) ⟨7717193, by rfl⟩ : syracuseStep 10289591 = 15434387) B15434387
theorem B7717355 : Blo 1354996 7717355 := bstep (se 1 (by rfl) ⟨5788016, by rfl⟩ : syracuseStep 7717355 = 11576033) B11576033
theorem B2572793 : Blo 1354996 2572793 := bstep (se 2 (by rfl) ⟨964797, by rfl⟩ : syracuseStep 2572793 = 1929595) B1929595
theorem B10297853 : Blo 1354996 10297853 := bstep (se 3 (by rfl) ⟨1930847, by rfl⟩ : syracuseStep 10297853 = 3861695) B3861695
theorem B4579847 : Blo 1354996 4579847 := bstep (se 1 (by rfl) ⟨3434885, by rfl⟩ : syracuseStep 4579847 = 6869771) B6869771
theorem B5145191 : Blo 1354996 5145191 := bstep (se 1 (by rfl) ⟨3858893, by rfl⟩ : syracuseStep 5145191 = 7717787) B7717787
theorem B3433063 : Blo 1354996 3433063 := bstep (se 1 (by rfl) ⟨2574797, by rfl⟩ : syracuseStep 3433063 = 5149595) B5149595
theorem B2171551 : Blo 1354996 2171551 := bstep (se 1 (by rfl) ⟨1628663, by rfl⟩ : syracuseStep 2171551 = 3257327) B3257327
theorem B4121351 : Blo 1354996 4121351 := bstep (se 1 (by rfl) ⟨3091013, by rfl⟩ : syracuseStep 4121351 = 6182027) B6182027
theorem B2032799 : Blo 1354996 2032799 := bstep (se 1 (by rfl) ⟨1524599, by rfl⟩ : syracuseStep 2032799 = 3049199) B3049199
theorem B6866207 : Blo 1354996 6866207 := bstep (se 1 (by rfl) ⟨5149655, by rfl⟩ : syracuseStep 6866207 = 10299311) B10299311
theorem B2032967 : Blo 1354996 2032967 := bstep (se 1 (by rfl) ⟨1524725, by rfl⟩ : syracuseStep 2032967 = 3049451) B3049451
theorem B3048911 : Blo 1354996 3048911 := bstep (se 1 (by rfl) ⟨2286683, by rfl⟩ : syracuseStep 3048911 = 4573367) B4573367
theorem B23160329 : Blo 1354996 23160329 := bstep (se 2 (by rfl) ⟨8685123, by rfl⟩ : syracuseStep 23160329 = 17370247) B17370247
theorem B2033417 : Blo 1354996 2033417 := bstep (se 2 (by rfl) ⟨762531, by rfl⟩ : syracuseStep 2033417 = 1525063) B1525063
theorem B2287399 : Blo 1354996 2287399 := bstep (se 1 (by rfl) ⟨1715549, by rfl⟩ : syracuseStep 2287399 = 3431099) B3431099
theorem B2287487 : Blo 1354996 2287487 := bstep (se 1 (by rfl) ⟨1715615, by rfl⟩ : syracuseStep 2287487 = 3431231) B3431231
theorem B3434683 : Blo 1354996 3434683 := bstep (se 1 (by rfl) ⟨2576012, by rfl⟩ : syracuseStep 3434683 = 5152025) B5152025
theorem B32164175 : Blo 1354996 32164175 := bstep (se 1 (by rfl) ⟨24123131, by rfl⟩ : syracuseStep 32164175 = 48246263) B48246263
theorem B33458597 : Blo 1354996 33458597 := bstep (se 4 (by rfl) ⟨3136743, by rfl⟩ : syracuseStep 33458597 = 6273487) B6273487
theorem B46983671 : Blo 1354996 46983671 := bstep (se 1 (by rfl) ⟨35237753, by rfl⟩ : syracuseStep 46983671 = 70475507) B70475507
theorem B4573961 : Blo 1354996 4573961 := bstep (se 2 (by rfl) ⟨1715235, by rfl⟩ : syracuseStep 4573961 = 3430471) B3430471
theorem B2034503 : Blo 1354996 2034503 := bstep (se 1 (by rfl) ⟨1525877, by rfl⟩ : syracuseStep 2034503 = 3051755) B3051755
theorem B3861377 : Blo 1354996 3861377 := bstep (se 2 (by rfl) ⟨1448016, by rfl⟩ : syracuseStep 3861377 = 2896033) B2896033
theorem B2034719 : Blo 1354996 2034719 := bstep (se 1 (by rfl) ⟨1526039, by rfl⟩ : syracuseStep 2034719 = 3052079) B3052079
theorem B2288695 : Blo 1354996 2288695 := bstep (se 1 (by rfl) ⟨1716521, by rfl⟩ : syracuseStep 2288695 = 3433043) B3433043
theorem B4574393 : Blo 1354996 4574393 := bstep (se 2 (by rfl) ⟨1715397, by rfl⟩ : syracuseStep 4574393 = 3430795) B3430795
theorem B14650577 : Blo 1354996 14650577 := bstep (se 2 (by rfl) ⟨5493966, by rfl⟩ : syracuseStep 14650577 = 10987933) B10987933
theorem B3861719 : Blo 1354996 3861719 := bstep (se 1 (by rfl) ⟨2896289, by rfl⟩ : syracuseStep 3861719 = 5792579) B5792579
theorem B1355079 : Blo 1354996 1355079 := bstep (se 1 (by rfl) ⟨1016309, by rfl⟩ : syracuseStep 1355079 = 2032619) B2032619
theorem B4574555 : Blo 1354996 4574555 := bstep (se 1 (by rfl) ⟨3430916, by rfl⟩ : syracuseStep 4574555 = 6861833) B6861833
theorem B2035103 : Blo 1354996 2035103 := bstep (se 1 (by rfl) ⟨1526327, by rfl⟩ : syracuseStep 2035103 = 3052655) B3052655
theorem B2035151 : Blo 1354996 2035151 := bstep (se 1 (by rfl) ⟨1526363, by rfl⟩ : syracuseStep 2035151 = 3052727) B3052727
theorem B9408125 : Blo 1354996 9408125 := bstep (se 3 (by rfl) ⟨1764023, by rfl⟩ : syracuseStep 9408125 = 3528047) B3528047
theorem B1355419 : Blo 1354996 1355419 := bstep (se 1 (by rfl) ⟨1016564, by rfl⟩ : syracuseStep 1355419 = 2033129) B2033129
theorem B5500727 : Blo 1354996 5500727 := bstep (se 1 (by rfl) ⟨4125545, by rfl⟩ : syracuseStep 5500727 = 8251091) B8251091
theorem B9776969 : Blo 1354996 9776969 := bstep (se 2 (by rfl) ⟨3666363, by rfl⟩ : syracuseStep 9776969 = 7332727) B7332727
theorem B8687483 : Blo 1354996 8687483 := bstep (se 1 (by rfl) ⟨6515612, by rfl⟩ : syracuseStep 8687483 = 13031225) B13031225
theorem B1355679 : Blo 1354996 1355679 := bstep (se 1 (by rfl) ⟨1016759, by rfl⟩ : syracuseStep 1355679 = 2033519) B2033519
theorem B9768919 : Blo 1354996 9768919 := bstep (se 1 (by rfl) ⟨7326689, by rfl⟩ : syracuseStep 9768919 = 14653379) B14653379
theorem B1355803 : Blo 1354996 1355803 := bstep (se 1 (by rfl) ⟨1016852, by rfl⟩ : syracuseStep 1355803 = 2033705) B2033705
theorem B29323295 : Blo 1354996 29323295 := bstep (se 1 (by rfl) ⟨21992471, by rfl⟩ : syracuseStep 29323295 = 43984943) B43984943
theorem B1355823 : Blo 1354996 1355823 := bstep (se 1 (by rfl) ⟨1016867, by rfl⟩ : syracuseStep 1355823 = 2033735) B2033735
theorem B2289755 : Blo 1354996 2289755 := bstep (se 1 (by rfl) ⟨1717316, by rfl⟩ : syracuseStep 2289755 = 3434633) B3434633
theorem B5795995 : Blo 1354996 5795995 := bstep (se 1 (by rfl) ⟨4346996, by rfl⟩ : syracuseStep 5795995 = 8693993) B8693993
theorem B1355943 : Blo 1354996 1355943 := bstep (se 1 (by rfl) ⟨1016957, by rfl⟩ : syracuseStep 1355943 = 2033915) B2033915
theorem B1356079 : Blo 1354996 1356079 := bstep (se 1 (by rfl) ⟨1017059, by rfl⟩ : syracuseStep 1356079 = 2034119) B2034119
theorem B1356223 : Blo 1354996 1356223 := bstep (se 1 (by rfl) ⟨1017167, by rfl⟩ : syracuseStep 1356223 = 2034335) B2034335
theorem B1356255 : Blo 1354996 1356255 := bstep (se 1 (by rfl) ⟨1017191, by rfl⟩ : syracuseStep 1356255 = 2034383) B2034383
theorem B1356319 : Blo 1354996 1356319 := bstep (se 1 (by rfl) ⟨1017239, by rfl⟩ : syracuseStep 1356319 = 2034479) B2034479
theorem B6869609 : Blo 1354996 6869609 := bstep (se 2 (by rfl) ⟨2576103, by rfl⟩ : syracuseStep 6869609 = 5152207) B5152207
theorem B4575851 : Blo 1354996 4575851 := bstep (se 1 (by rfl) ⟨3431888, by rfl⟩ : syracuseStep 4575851 = 6863777) B6863777
theorem B1356399 : Blo 1354996 1356399 := bstep (se 1 (by rfl) ⟨1017299, by rfl⟩ : syracuseStep 1356399 = 2034599) B2034599
theorem B3863177 : Blo 1354996 3863177 := bstep (se 2 (by rfl) ⟨1448691, by rfl⟩ : syracuseStep 3863177 = 2897383) B2897383
theorem B1356519 : Blo 1354996 1356519 := bstep (se 1 (by rfl) ⟨1017389, by rfl⟩ : syracuseStep 1356519 = 2034779) B2034779
theorem B1356571 : Blo 1354996 1356571 := bstep (se 1 (by rfl) ⟨1017428, by rfl⟩ : syracuseStep 1356571 = 2034857) B2034857
theorem B15438761 : Blo 1354996 15438761 := bstep (se 2 (by rfl) ⟨5789535, by rfl⟩ : syracuseStep 15438761 = 11579071) B11579071
theorem B1356847 : Blo 1354996 1356847 := bstep (se 1 (by rfl) ⟨1017635, by rfl⟩ : syracuseStep 1356847 = 2035271) B2035271
theorem B1356967 : Blo 1354996 1356967 := bstep (se 1 (by rfl) ⟨1017725, by rfl⟩ : syracuseStep 1356967 = 2035451) B2035451
theorem B4887805 : Blo 1354996 4887805 := bstep (se 3 (by rfl) ⟨916463, by rfl⟩ : syracuseStep 4887805 = 1832927) B1832927
theorem B4576553 : Blo 1354996 4576553 := bstep (se 2 (by rfl) ⟨1716207, by rfl⟩ : syracuseStep 4576553 = 3432415) B3432415
theorem B16717423 : Blo 1354996 16717423 := bstep (se 1 (by rfl) ⟨12538067, by rfl⟩ : syracuseStep 16717423 = 25076135) B25076135
theorem B10294937 : Blo 1354996 10294937 := bstep (se 2 (by rfl) ⟨3860601, by rfl⟩ : syracuseStep 10294937 = 7721203) B7721203
theorem B9770651 : Blo 1354996 9770651 := bstep (se 1 (by rfl) ⟨7327988, by rfl⟩ : syracuseStep 9770651 = 14655977) B14655977
theorem B23164703 : Blo 1354996 23164703 := bstep (se 1 (by rfl) ⟨17373527, by rfl⟩ : syracuseStep 23164703 = 34747055) B34747055
theorem B1447999 : Blo 1354996 1447999 := bstep (se 1 (by rfl) ⟨1085999, by rfl⟩ : syracuseStep 1447999 = 2171999) B2171999
theorem B11589803 : Blo 1354996 11589803 := bstep (se 1 (by rfl) ⟨8692352, by rfl⟩ : syracuseStep 11589803 = 17384705) B17384705
theorem B23182199 : Blo 1354996 23182199 := bstep (se 1 (by rfl) ⟨17386649, by rfl⟩ : syracuseStep 23182199 = 34773299) B34773299
theorem B5151707 : Blo 1354996 5151707 := bstep (se 1 (by rfl) ⟨3863780, by rfl⟩ : syracuseStep 5151707 = 7727561) B7727561
theorem B5495863 : Blo 1354996 5495863 := bstep (se 1 (by rfl) ⟨4121897, by rfl⟩ : syracuseStep 5495863 = 8243795) B8243795
theorem B9911555 : Blo 1354996 9911555 := bstep (se 1 (by rfl) ⟨7433666, by rfl⟩ : syracuseStep 9911555 = 14867333) B14867333
theorem B59465123 : Blo 1354996 59465123 := bstep (se 1 (by rfl) ⟨44598842, by rfl⟩ : syracuseStep 59465123 = 89197685) B89197685
theorem B6864425 : Blo 1354996 6864425 := bstep (se 2 (by rfl) ⟨2574159, by rfl⟩ : syracuseStep 6864425 = 5148319) B5148319
theorem B4579577 : Blo 1354996 4579577 := bstep (se 2 (by rfl) ⟨1717341, by rfl⟩ : syracuseStep 4579577 = 3434683) B3434683
theorem B5144903 : Blo 1354996 5144903 := bstep (se 1 (by rfl) ⟨3858677, by rfl⟩ : syracuseStep 5144903 = 7717355) B7717355
theorem B6865235 : Blo 1354996 6865235 := bstep (se 1 (by rfl) ⟨5148926, by rfl⟩ : syracuseStep 6865235 = 10297853) B10297853
theorem B4579739 : Blo 1354996 4579739 := bstep (se 1 (by rfl) ⟨3434804, by rfl⟩ : syracuseStep 4579739 = 6869609) B6869609
theorem B85771133 : Blo 1354996 85771133 := bstep (se 3 (by rfl) ⟨16082087, by rfl⟩ : syracuseStep 85771133 = 32164175) B32164175
theorem B2032607 : Blo 1354996 2032607 := bstep (se 1 (by rfl) ⟨1524455, by rfl⟩ : syracuseStep 2032607 = 3048911) B3048911
theorem B6513767 : Blo 1354996 6513767 := bstep (se 1 (by rfl) ⟨4885325, by rfl⟩ : syracuseStep 6513767 = 9770651) B9770651
theorem B15443135 : Blo 1354996 15443135 := bstep (se 1 (by rfl) ⟨11582351, by rfl⟩ : syracuseStep 15443135 = 23164703) B23164703
theorem B1524991 : Blo 1354996 1524991 := bstep (se 1 (by rfl) ⟨1143743, by rfl⟩ : syracuseStep 1524991 = 2287487) B2287487
theorem B7726535 : Blo 1354996 7726535 := bstep (se 1 (by rfl) ⟨5794901, by rfl⟩ : syracuseStep 7726535 = 11589803) B11589803
theorem B3049307 : Blo 1354996 3049307 := bstep (se 1 (by rfl) ⟨2286980, by rfl⟩ : syracuseStep 3049307 = 4573961) B4573961
theorem B2574251 : Blo 1354996 2574251 := bstep (se 1 (by rfl) ⟨1930688, by rfl⟩ : syracuseStep 2574251 = 3861377) B3861377
theorem B3434471 : Blo 1354996 3434471 := bstep (se 1 (by rfl) ⟨2575853, by rfl⟩ : syracuseStep 3434471 = 5151707) B5151707
theorem B3049595 : Blo 1354996 3049595 := bstep (se 1 (by rfl) ⟨2287196, by rfl⟩ : syracuseStep 3049595 = 4574393) B4574393
theorem B9767051 : Blo 1354996 9767051 := bstep (se 1 (by rfl) ⟨7325288, by rfl⟩ : syracuseStep 9767051 = 14650577) B14650577
theorem B2574479 : Blo 1354996 2574479 := bstep (se 1 (by rfl) ⟨1930859, by rfl⟩ : syracuseStep 2574479 = 3861719) B3861719
theorem B3049703 : Blo 1354996 3049703 := bstep (se 1 (by rfl) ⟨2287277, by rfl⟩ : syracuseStep 3049703 = 4574555) B4574555
theorem B39643415 : Blo 1354996 39643415 := bstep (se 1 (by rfl) ⟨29732561, by rfl⟩ : syracuseStep 39643415 = 59465123) B59465123
theorem B3049865 : Blo 1354996 3049865 := bstep (se 2 (by rfl) ⟨1143699, by rfl⟩ : syracuseStep 3049865 = 2287399) B2287399
theorem B19548863 : Blo 1354996 19548863 := bstep (se 1 (by rfl) ⟨14661647, by rfl⟩ : syracuseStep 19548863 = 29323295) B29323295
theorem B6515423 : Blo 1354996 6515423 := bstep (se 1 (by rfl) ⟨4886567, by rfl⟩ : syracuseStep 6515423 = 9773135) B9773135
theorem B1526503 : Blo 1354996 1526503 := bstep (se 1 (by rfl) ⟨1144877, by rfl⟩ : syracuseStep 1526503 = 2289755) B2289755
theorem B7727993 : Blo 1354996 7727993 := bstep (se 2 (by rfl) ⟨2897997, by rfl⟩ : syracuseStep 7727993 = 5795995) B5795995
theorem B6859727 : Blo 1354996 6859727 := bstep (se 1 (by rfl) ⟨5144795, by rfl⟩ : syracuseStep 6859727 = 10289591) B10289591
theorem B1715195 : Blo 1354996 1715195 := bstep (se 1 (by rfl) ⟨1286396, by rfl⟩ : syracuseStep 1715195 = 2572793) B2572793
theorem B3050567 : Blo 1354996 3050567 := bstep (se 1 (by rfl) ⟨2287925, by rfl⟩ : syracuseStep 3050567 = 4575851) B4575851
theorem B2575451 : Blo 1354996 2575451 := bstep (se 1 (by rfl) ⟨1931588, by rfl⟩ : syracuseStep 2575451 = 3863177) B3863177
theorem B2747567 : Blo 1354996 2747567 := bstep (se 1 (by rfl) ⟨2060675, by rfl⟩ : syracuseStep 2747567 = 4121351) B4121351
theorem B100347113 : Blo 1354996 100347113 := bstep (se 2 (by rfl) ⟨37630167, by rfl⟩ : syracuseStep 100347113 = 75260335) B75260335
theorem B10292507 : Blo 1354996 10292507 := bstep (se 1 (by rfl) ⟨7719380, by rfl⟩ : syracuseStep 10292507 = 15438761) B15438761
theorem B1355199 : Blo 1354996 1355199 := bstep (se 1 (by rfl) ⟨1016399, by rfl⟩ : syracuseStep 1355199 = 2032799) B2032799
theorem B3051035 : Blo 1354996 3051035 := bstep (se 1 (by rfl) ⟨2288276, by rfl⟩ : syracuseStep 3051035 = 4576553) B4576553
theorem B2895401 : Blo 1354996 2895401 := bstep (se 2 (by rfl) ⟨1085775, by rfl⟩ : syracuseStep 2895401 = 2171551) B2171551
theorem B1355311 : Blo 1354996 1355311 := bstep (se 1 (by rfl) ⟨1016483, by rfl⟩ : syracuseStep 1355311 = 2032967) B2032967
theorem B1355611 : Blo 1354996 1355611 := bstep (se 1 (by rfl) ⟨1016708, by rfl⟩ : syracuseStep 1355611 = 2033417) B2033417
theorem B7327817 : Blo 1354996 7327817 := bstep (se 2 (by rfl) ⟨2747931, by rfl⟩ : syracuseStep 7327817 = 5495863) B5495863
theorem B3051593 : Blo 1354996 3051593 := bstep (se 2 (by rfl) ⟨1144347, by rfl⟩ : syracuseStep 3051593 = 2288695) B2288695
theorem B31322447 : Blo 1354996 31322447 := bstep (se 1 (by rfl) ⟨23491835, by rfl⟩ : syracuseStep 31322447 = 46983671) B46983671
theorem B6517073 : Blo 1354996 6517073 := bstep (se 2 (by rfl) ⟨2443902, by rfl⟩ : syracuseStep 6517073 = 4887805) B4887805
theorem B1356335 : Blo 1354996 1356335 := bstep (se 1 (by rfl) ⟨1017251, by rfl⟩ : syracuseStep 1356335 = 2034503) B2034503
theorem B15454799 : Blo 1354996 15454799 := bstep (se 1 (by rfl) ⟨11591099, by rfl⟩ : syracuseStep 15454799 = 23182199) B23182199
theorem B1356479 : Blo 1354996 1356479 := bstep (se 1 (by rfl) ⟨1017359, by rfl⟩ : syracuseStep 1356479 = 2034719) B2034719
theorem B6607703 : Blo 1354996 6607703 := bstep (se 1 (by rfl) ⟨4955777, by rfl⟩ : syracuseStep 6607703 = 9911555) B9911555
theorem B1356735 : Blo 1354996 1356735 := bstep (se 1 (by rfl) ⟨1017551, by rfl⟩ : syracuseStep 1356735 = 2035103) B2035103
theorem B1356767 : Blo 1354996 1356767 := bstep (se 1 (by rfl) ⟨1017575, by rfl⟩ : syracuseStep 1356767 = 2035151) B2035151
theorem B4576283 : Blo 1354996 4576283 := bstep (se 1 (by rfl) ⟨3432212, by rfl⟩ : syracuseStep 4576283 = 6864425) B6864425
theorem B6272083 : Blo 1354996 6272083 := bstep (se 1 (by rfl) ⟨4704062, by rfl⟩ : syracuseStep 6272083 = 9408125) B9408125
theorem B3667151 : Blo 1354996 3667151 := bstep (se 1 (by rfl) ⟨2750363, by rfl⟩ : syracuseStep 3667151 = 5500727) B5500727
theorem B6517979 : Blo 1354996 6517979 := bstep (se 1 (by rfl) ⟨4888484, by rfl⟩ : syracuseStep 6517979 = 9776969) B9776969
theorem B3053087 : Blo 1354996 3053087 := bstep (se 1 (by rfl) ⟨2289815, by rfl⟩ : syracuseStep 3053087 = 4579631) B4579631
theorem B7722661 : Blo 1354996 7722661 := bstep (se 4 (by rfl) ⟨723999, by rfl⟩ : syracuseStep 7722661 = 1447999) B1447999
theorem B3053231 : Blo 1354996 3053231 := bstep (se 1 (by rfl) ⟨2289923, by rfl⟩ : syracuseStep 3053231 = 4579847) B4579847
theorem B3430127 : Blo 1354996 3430127 := bstep (se 1 (by rfl) ⟨2572595, by rfl⟩ : syracuseStep 3430127 = 5145191) B5145191
theorem B4577417 : Blo 1354996 4577417 := bstep (se 2 (by rfl) ⟨1716531, by rfl⟩ : syracuseStep 4577417 = 3433063) B3433063
theorem B4577471 : Blo 1354996 4577471 := bstep (se 1 (by rfl) ⟨3433103, by rfl⟩ : syracuseStep 4577471 = 6866207) B6866207
theorem B15440219 : Blo 1354996 15440219 := bstep (se 1 (by rfl) ⟨11580164, by rfl⟩ : syracuseStep 15440219 = 23160329) B23160329
theorem B6863291 : Blo 1354996 6863291 := bstep (se 1 (by rfl) ⟨5147468, by rfl⟩ : syracuseStep 6863291 = 10294937) B10294937
theorem B22305731 : Blo 1354996 22305731 := bstep (se 1 (by rfl) ⟨16729298, by rfl⟩ : syracuseStep 22305731 = 33458597) B33458597
theorem B22289897 : Blo 1354996 22289897 := bstep (se 2 (by rfl) ⟨8358711, by rfl⟩ : syracuseStep 22289897 = 16717423) B16717423
theorem B5791655 : Blo 1354996 5791655 := bstep (se 1 (by rfl) ⟨4343741, by rfl⟩ : syracuseStep 5791655 = 8687483) B8687483
theorem B13025225 : Blo 1354996 13025225 := bstep (se 2 (by rfl) ⟨4884459, by rfl⟩ : syracuseStep 13025225 = 9768919) B9768919
theorem B20881631 : Blo 1354996 20881631 := bstep (se 1 (by rfl) ⟨15661223, by rfl⟩ : syracuseStep 20881631 = 31322447) B31322447
theorem B57180755 : Blo 1354996 57180755 := bstep (se 1 (by rfl) ⟨42885566, by rfl⟩ : syracuseStep 57180755 = 85771133) B85771133
theorem B4342511 : Blo 1354996 4342511 := bstep (se 1 (by rfl) ⟨3256883, by rfl⟩ : syracuseStep 4342511 = 6513767) B6513767
theorem B2286751 : Blo 1354996 2286751 := bstep (se 1 (by rfl) ⟨1715063, by rfl⟩ : syracuseStep 2286751 = 3430127) B3430127
theorem B2032871 : Blo 1354996 2032871 := bstep (se 1 (by rfl) ⟨1524653, by rfl⟩ : syracuseStep 2032871 = 3049307) B3049307
theorem B2033063 : Blo 1354996 2033063 := bstep (se 1 (by rfl) ⟨1524797, by rfl⟩ : syracuseStep 2033063 = 3049595) B3049595
theorem B2033135 : Blo 1354996 2033135 := bstep (se 1 (by rfl) ⟨1524851, by rfl⟩ : syracuseStep 2033135 = 3049703) B3049703
theorem B26428943 : Blo 1354996 26428943 := bstep (se 1 (by rfl) ⟨19821707, by rfl⟩ : syracuseStep 26428943 = 39643415) B39643415
theorem B2033243 : Blo 1354996 2033243 := bstep (se 1 (by rfl) ⟨1524932, by rfl⟩ : syracuseStep 2033243 = 3049865) B3049865
theorem B2033321 : Blo 1354996 2033321 := bstep (se 2 (by rfl) ⟨762495, by rfl⟩ : syracuseStep 2033321 = 1524991) B1524991
theorem B4343615 : Blo 1354996 4343615 := bstep (se 1 (by rfl) ⟨3257711, by rfl⟩ : syracuseStep 4343615 = 6515423) B6515423
theorem B4573151 : Blo 1354996 4573151 := bstep (se 1 (by rfl) ⟨3429863, by rfl⟩ : syracuseStep 4573151 = 6859727) B6859727
theorem B2033711 : Blo 1354996 2033711 := bstep (se 1 (by rfl) ⟨1525283, by rfl⟩ : syracuseStep 2033711 = 3050567) B3050567
theorem B66898075 : Blo 1354996 66898075 := bstep (se 1 (by rfl) ⟨50173556, by rfl⟩ : syracuseStep 66898075 = 100347113) B100347113
theorem B2034023 : Blo 1354996 2034023 := bstep (se 1 (by rfl) ⟨1525517, by rfl⟩ : syracuseStep 2034023 = 3051035) B3051035
theorem B3861103 : Blo 1354996 3861103 := bstep (se 1 (by rfl) ⟨2895827, by rfl⟩ : syracuseStep 3861103 = 5791655) B5791655
theorem B4573853 : Blo 1354996 4573853 := bstep (se 3 (by rfl) ⟨857597, by rfl⟩ : syracuseStep 4573853 = 1715195) B1715195
theorem B4885211 : Blo 1354996 4885211 := bstep (se 1 (by rfl) ⟨3663908, by rfl⟩ : syracuseStep 4885211 = 7327817) B7327817
theorem B2034395 : Blo 1354996 2034395 := bstep (se 1 (by rfl) ⟨1525796, by rfl⟩ : syracuseStep 2034395 = 3051593) B3051593
theorem B4344715 : Blo 1354996 4344715 := bstep (se 1 (by rfl) ⟨3258536, by rfl⟩ : syracuseStep 4344715 = 6517073) B6517073
theorem B7326845 : Blo 1354996 7326845 := bstep (se 3 (by rfl) ⟨1373783, by rfl⟩ : syracuseStep 7326845 = 2747567) B2747567
theorem B1355071 : Blo 1354996 1355071 := bstep (se 1 (by rfl) ⟨1016303, by rfl⟩ : syracuseStep 1355071 = 2032607) B2032607
theorem B3050855 : Blo 1354996 3050855 := bstep (se 1 (by rfl) ⟨2288141, by rfl⟩ : syracuseStep 3050855 = 4576283) B4576283
theorem B4345319 : Blo 1354996 4345319 := bstep (se 1 (by rfl) ⟨3258989, by rfl⟩ : syracuseStep 4345319 = 6517979) B6517979
theorem B2035337 : Blo 1354996 2035337 := bstep (se 2 (by rfl) ⟨763251, by rfl⟩ : syracuseStep 2035337 = 1526503) B1526503
theorem B2035391 : Blo 1354996 2035391 := bstep (se 1 (by rfl) ⟨1526543, by rfl⟩ : syracuseStep 2035391 = 3053087) B3053087
theorem B2035487 : Blo 1354996 2035487 := bstep (se 1 (by rfl) ⟨1526615, by rfl⟩ : syracuseStep 2035487 = 3053231) B3053231
theorem B1716167 : Blo 1354996 1716167 := bstep (se 1 (by rfl) ⟨1287125, by rfl⟩ : syracuseStep 1716167 = 2574251) B2574251
theorem B2289647 : Blo 1354996 2289647 := bstep (se 1 (by rfl) ⟨1717235, by rfl⟩ : syracuseStep 2289647 = 3434471) B3434471
theorem B3051611 : Blo 1354996 3051611 := bstep (se 1 (by rfl) ⟨2288708, by rfl⟩ : syracuseStep 3051611 = 4577417) B4577417
theorem B1716319 : Blo 1354996 1716319 := bstep (se 1 (by rfl) ⟨1287239, by rfl⟩ : syracuseStep 1716319 = 2574479) B2574479
theorem B3051647 : Blo 1354996 3051647 := bstep (se 1 (by rfl) ⟨2288735, by rfl⟩ : syracuseStep 3051647 = 4577471) B4577471
theorem B10293479 : Blo 1354996 10293479 := bstep (se 1 (by rfl) ⟨7720109, by rfl⟩ : syracuseStep 10293479 = 15440219) B15440219
theorem B4575527 : Blo 1354996 4575527 := bstep (se 1 (by rfl) ⟨3431645, by rfl⟩ : syracuseStep 4575527 = 6863291) B6863291
theorem B1716967 : Blo 1354996 1716967 := bstep (se 1 (by rfl) ⟨1287725, by rfl⟩ : syracuseStep 1716967 = 2575451) B2575451
theorem B6861671 : Blo 1354996 6861671 := bstep (se 1 (by rfl) ⟨5146253, by rfl⟩ : syracuseStep 6861671 = 10292507) B10292507
theorem B1930267 : Blo 1354996 1930267 := bstep (se 1 (by rfl) ⟨1447700, by rfl⟩ : syracuseStep 1930267 = 2895401) B2895401
theorem B3053051 : Blo 1354996 3053051 := bstep (se 1 (by rfl) ⟨2289788, by rfl⟩ : syracuseStep 3053051 = 4579577) B4579577
theorem B3429935 : Blo 1354996 3429935 := bstep (se 1 (by rfl) ⟨2572451, by rfl⟩ : syracuseStep 3429935 = 5144903) B5144903
theorem B4576823 : Blo 1354996 4576823 := bstep (se 1 (by rfl) ⟨3432617, by rfl⟩ : syracuseStep 4576823 = 6865235) B6865235
theorem B3053159 : Blo 1354996 3053159 := bstep (se 1 (by rfl) ⟨2289869, by rfl⟩ : syracuseStep 3053159 = 4579739) B4579739
theorem B10303199 : Blo 1354996 10303199 := bstep (se 1 (by rfl) ⟨7727399, by rfl⟩ : syracuseStep 10303199 = 15454799) B15454799
theorem B9779069 : Blo 1354996 9779069 := bstep (se 3 (by rfl) ⟨1833575, by rfl⟩ : syracuseStep 9779069 = 3667151) B3667151
theorem B10295423 : Blo 1354996 10295423 := bstep (se 1 (by rfl) ⟨7721567, by rfl⟩ : syracuseStep 10295423 = 15443135) B15443135
theorem B5151023 : Blo 1354996 5151023 := bstep (se 1 (by rfl) ⟨3863267, by rfl⟩ : syracuseStep 5151023 = 7726535) B7726535
theorem B6511367 : Blo 1354996 6511367 := bstep (se 1 (by rfl) ⟨4883525, by rfl⟩ : syracuseStep 6511367 = 9767051) B9767051
theorem B8362777 : Blo 1354996 8362777 := bstep (se 2 (by rfl) ⟨3136041, by rfl⟩ : syracuseStep 8362777 = 6272083) B6272083
theorem B13032575 : Blo 1354996 13032575 := bstep (se 1 (by rfl) ⟨9774431, by rfl⟩ : syracuseStep 13032575 = 19548863) B19548863
theorem B5151995 : Blo 1354996 5151995 := bstep (se 1 (by rfl) ⟨3863996, by rfl⟩ : syracuseStep 5151995 = 7727993) B7727993
theorem B237927797 : Blo 1354996 237927797 := bstep (se 5 (by rfl) ⟨11152865, by rfl⟩ : syracuseStep 237927797 = 22305731) B22305731
theorem B10296881 : Blo 1354996 10296881 := bstep (se 2 (by rfl) ⟨3861330, by rfl⟩ : syracuseStep 10296881 = 7722661) B7722661
theorem B17620541 : Blo 1354996 17620541 := bstep (se 3 (by rfl) ⟨3303851, by rfl⟩ : syracuseStep 17620541 = 6607703) B6607703
theorem B14859931 : Blo 1354996 14859931 := bstep (se 1 (by rfl) ⟨11144948, by rfl⟩ : syracuseStep 14859931 = 22289897) B22289897
theorem B34733933 : Blo 1354996 34733933 := bstep (se 3 (by rfl) ⟨6512612, by rfl⟩ : syracuseStep 34733933 = 13025225) B13025225
theorem B2286623 : Blo 1354996 2286623 := bstep (se 1 (by rfl) ⟨1714967, by rfl⟩ : syracuseStep 2286623 = 3429935) B3429935
theorem B11150369 : Blo 1354996 11150369 := bstep (se 2 (by rfl) ⟨4181388, by rfl⟩ : syracuseStep 11150369 = 8362777) B8362777
theorem B5792953 : Blo 1354996 5792953 := bstep (se 2 (by rfl) ⟨2172357, by rfl⟩ : syracuseStep 5792953 = 4344715) B4344715
theorem B3048767 : Blo 1354996 3048767 := bstep (se 1 (by rfl) ⟨2286575, by rfl⟩ : syracuseStep 3048767 = 4573151) B4573151
theorem B2573689 : Blo 1354996 2573689 := bstep (se 2 (by rfl) ⟨965133, by rfl⟩ : syracuseStep 2573689 = 1930267) B1930267
theorem B3434015 : Blo 1354996 3434015 := bstep (se 1 (by rfl) ⟨2575511, by rfl⟩ : syracuseStep 3434015 = 5151023) B5151023
theorem B3049001 : Blo 1354996 3049001 := bstep (se 2 (by rfl) ⟨1143375, by rfl⟩ : syracuseStep 3049001 = 2286751) B2286751
theorem B3049235 : Blo 1354996 3049235 := bstep (se 1 (by rfl) ⟨2286926, by rfl⟩ : syracuseStep 3049235 = 4573853) B4573853
theorem B13027229 : Blo 1354996 13027229 := bstep (se 3 (by rfl) ⟨2442605, by rfl⟩ : syracuseStep 13027229 = 4885211) B4885211
theorem B4884563 : Blo 1354996 4884563 := bstep (se 1 (by rfl) ⟨3663422, by rfl⟩ : syracuseStep 4884563 = 7326845) B7326845
theorem B3434663 : Blo 1354996 3434663 := bstep (se 1 (by rfl) ⟨2575997, by rfl⟩ : syracuseStep 3434663 = 5151995) B5151995
theorem B2033903 : Blo 1354996 2033903 := bstep (se 1 (by rfl) ⟨1525427, by rfl⟩ : syracuseStep 2033903 = 3050855) B3050855
theorem B1526431 : Blo 1354996 1526431 := bstep (se 1 (by rfl) ⟨1144823, by rfl⟩ : syracuseStep 1526431 = 2289647) B2289647
theorem B2034407 : Blo 1354996 2034407 := bstep (se 1 (by rfl) ⟨1525805, by rfl⟩ : syracuseStep 2034407 = 3051611) B3051611
theorem B2034431 : Blo 1354996 2034431 := bstep (se 1 (by rfl) ⟨1525823, by rfl⟩ : syracuseStep 2034431 = 3051647) B3051647
theorem B2288425 : Blo 1354996 2288425 := bstep (se 2 (by rfl) ⟨858159, by rfl⟩ : syracuseStep 2288425 = 1716319) B1716319
theorem B13921087 : Blo 1354996 13921087 := bstep (se 1 (by rfl) ⟨10440815, by rfl⟩ : syracuseStep 13921087 = 20881631) B20881631
theorem B3050351 : Blo 1354996 3050351 := bstep (se 1 (by rfl) ⟨2287763, by rfl⟩ : syracuseStep 3050351 = 4575527) B4575527
theorem B89197433 : Blo 1354996 89197433 := bstep (se 2 (by rfl) ⟨33449037, by rfl⟩ : syracuseStep 89197433 = 66898075) B66898075
theorem B38120503 : Blo 1354996 38120503 := bstep (se 1 (by rfl) ⟨28590377, by rfl⟩ : syracuseStep 38120503 = 57180755) B57180755
theorem B4574447 : Blo 1354996 4574447 := bstep (se 1 (by rfl) ⟨3430835, by rfl⟩ : syracuseStep 4574447 = 6861671) B6861671
theorem B5148137 : Blo 1354996 5148137 := bstep (se 2 (by rfl) ⟨1930551, by rfl⟩ : syracuseStep 5148137 = 3861103) B3861103
theorem B1355247 : Blo 1354996 1355247 := bstep (se 1 (by rfl) ⟨1016435, by rfl⟩ : syracuseStep 1355247 = 2032871) B2032871
theorem B1355375 : Blo 1354996 1355375 := bstep (se 1 (by rfl) ⟨1016531, by rfl⟩ : syracuseStep 1355375 = 2033063) B2033063
theorem B2289289 : Blo 1354996 2289289 := bstep (se 2 (by rfl) ⟨858483, by rfl⟩ : syracuseStep 2289289 = 1716967) B1716967
theorem B1355423 : Blo 1354996 1355423 := bstep (se 1 (by rfl) ⟨1016567, by rfl⟩ : syracuseStep 1355423 = 2033135) B2033135
theorem B2035367 : Blo 1354996 2035367 := bstep (se 1 (by rfl) ⟨1526525, by rfl⟩ : syracuseStep 2035367 = 3053051) B3053051
theorem B3051215 : Blo 1354996 3051215 := bstep (se 1 (by rfl) ⟨2288411, by rfl⟩ : syracuseStep 3051215 = 4576823) B4576823
theorem B1355495 : Blo 1354996 1355495 := bstep (se 1 (by rfl) ⟨1016621, by rfl⟩ : syracuseStep 1355495 = 2033243) B2033243
theorem B2035439 : Blo 1354996 2035439 := bstep (se 1 (by rfl) ⟨1526579, by rfl⟩ : syracuseStep 2035439 = 3053159) B3053159
theorem B1355547 : Blo 1354996 1355547 := bstep (se 1 (by rfl) ⟨1016660, by rfl⟩ : syracuseStep 1355547 = 2033321) B2033321
theorem B6868799 : Blo 1354996 6868799 := bstep (se 1 (by rfl) ⟨5151599, by rfl⟩ : syracuseStep 6868799 = 10303199) B10303199
theorem B2895743 : Blo 1354996 2895743 := bstep (se 1 (by rfl) ⟨2171807, by rfl⟩ : syracuseStep 2895743 = 4343615) B4343615
theorem B1355807 : Blo 1354996 1355807 := bstep (se 1 (by rfl) ⟨1016855, by rfl⟩ : syracuseStep 1355807 = 2033711) B2033711
theorem B1356015 : Blo 1354996 1356015 := bstep (se 1 (by rfl) ⟨1017011, by rfl⟩ : syracuseStep 1356015 = 2034023) B2034023
theorem B1356263 : Blo 1354996 1356263 := bstep (se 1 (by rfl) ⟨1017197, by rfl⟩ : syracuseStep 1356263 = 2034395) B2034395
theorem B11580029 : Blo 1354996 11580029 := bstep (se 3 (by rfl) ⟨2171255, by rfl⟩ : syracuseStep 11580029 = 4342511) B4342511
theorem B8688383 : Blo 1354996 8688383 := bstep (se 1 (by rfl) ⟨6516287, by rfl⟩ : syracuseStep 8688383 = 13032575) B13032575
theorem B19813241 : Blo 1354996 19813241 := bstep (se 2 (by rfl) ⟨7429965, by rfl⟩ : syracuseStep 19813241 = 14859931) B14859931
theorem B158618531 : Blo 1354996 158618531 := bstep (se 1 (by rfl) ⟨118963898, by rfl⟩ : syracuseStep 158618531 = 237927797) B237927797
theorem B2896879 : Blo 1354996 2896879 := bstep (se 1 (by rfl) ⟨2172659, by rfl⟩ : syracuseStep 2896879 = 4345319) B4345319
theorem B1356891 : Blo 1354996 1356891 := bstep (se 1 (by rfl) ⟨1017668, by rfl⟩ : syracuseStep 1356891 = 2035337) B2035337
theorem B1356927 : Blo 1354996 1356927 := bstep (se 1 (by rfl) ⟨1017695, by rfl⟩ : syracuseStep 1356927 = 2035391) B2035391
theorem B4576445 : Blo 1354996 4576445 := bstep (se 3 (by rfl) ⟨858083, by rfl⟩ : syracuseStep 4576445 = 1716167) B1716167
theorem B1356991 : Blo 1354996 1356991 := bstep (se 1 (by rfl) ⟨1017743, by rfl⟩ : syracuseStep 1356991 = 2035487) B2035487
theorem B23155955 : Blo 1354996 23155955 := bstep (se 1 (by rfl) ⟨17366966, by rfl⟩ : syracuseStep 23155955 = 34733933) B34733933
theorem B6862319 : Blo 1354996 6862319 := bstep (se 1 (by rfl) ⟨5146739, by rfl⟩ : syracuseStep 6862319 = 10293479) B10293479
theorem B17619295 : Blo 1354996 17619295 := bstep (se 1 (by rfl) ⟨13214471, by rfl⟩ : syracuseStep 17619295 = 26428943) B26428943
theorem B6519379 : Blo 1354996 6519379 := bstep (se 1 (by rfl) ⟨4889534, by rfl⟩ : syracuseStep 6519379 = 9779069) B9779069
theorem B6863615 : Blo 1354996 6863615 := bstep (se 1 (by rfl) ⟨5147711, by rfl⟩ : syracuseStep 6863615 = 10295423) B10295423
theorem B4340911 : Blo 1354996 4340911 := bstep (se 1 (by rfl) ⟨3255683, by rfl⟩ : syracuseStep 4340911 = 6511367) B6511367
theorem B6864587 : Blo 1354996 6864587 := bstep (se 1 (by rfl) ⟨5148440, by rfl⟩ : syracuseStep 6864587 = 10296881) B10296881
theorem B11747027 : Blo 1354996 11747027 := bstep (se 1 (by rfl) ⟨8810270, by rfl⟩ : syracuseStep 11747027 = 17620541) B17620541
theorem B5792255 : Blo 1354996 5792255 := bstep (se 1 (by rfl) ⟨4344191, by rfl⟩ : syracuseStep 5792255 = 8688383) B8688383
theorem B1524415 : Blo 1354996 1524415 := bstep (se 1 (by rfl) ⟨1143311, by rfl⟩ : syracuseStep 1524415 = 2286623) B2286623
theorem B8692505 : Blo 1354996 8692505 := bstep (se 2 (by rfl) ⟨3259689, by rfl⟩ : syracuseStep 8692505 = 6519379) B6519379
theorem B2032511 : Blo 1354996 2032511 := bstep (se 1 (by rfl) ⟨1524383, by rfl⟩ : syracuseStep 2032511 = 3048767) B3048767
theorem B2032667 : Blo 1354996 2032667 := bstep (se 1 (by rfl) ⟨1524500, by rfl⟩ : syracuseStep 2032667 = 3049001) B3049001
theorem B2032823 : Blo 1354996 2032823 := bstep (se 1 (by rfl) ⟨1524617, by rfl⟩ : syracuseStep 2032823 = 3049235) B3049235
theorem B8684819 : Blo 1354996 8684819 := bstep (se 1 (by rfl) ⟨6513614, by rfl⟩ : syracuseStep 8684819 = 13027229) B13027229
theorem B2033567 : Blo 1354996 2033567 := bstep (se 1 (by rfl) ⟨1525175, by rfl⟩ : syracuseStep 2033567 = 3050351) B3050351
theorem B3049631 : Blo 1354996 3049631 := bstep (se 1 (by rfl) ⟨2287223, by rfl⟩ : syracuseStep 3049631 = 4574447) B4574447
theorem B2034143 : Blo 1354996 2034143 := bstep (se 1 (by rfl) ⟨1525607, by rfl⟩ : syracuseStep 2034143 = 3051215) B3051215
theorem B7720019 : Blo 1354996 7720019 := bstep (se 1 (by rfl) ⟨5790014, by rfl⟩ : syracuseStep 7720019 = 11580029) B11580029
theorem B13208827 : Blo 1354996 13208827 := bstep (se 1 (by rfl) ⟨9906620, by rfl⟩ : syracuseStep 13208827 = 19813241) B19813241
theorem B7433579 : Blo 1354996 7433579 := bstep (se 1 (by rfl) ⟨5575184, by rfl⟩ : syracuseStep 7433579 = 11150369) B11150369
theorem B3050963 : Blo 1354996 3050963 := bstep (se 1 (by rfl) ⟨2288222, by rfl⟩ : syracuseStep 3050963 = 4576445) B4576445
theorem B15437303 : Blo 1354996 15437303 := bstep (se 1 (by rfl) ⟨11577977, by rfl⟩ : syracuseStep 15437303 = 23155955) B23155955
theorem B2035241 : Blo 1354996 2035241 := bstep (se 2 (by rfl) ⟨763215, by rfl⟩ : syracuseStep 2035241 = 1526431) B1526431
theorem B4574879 : Blo 1354996 4574879 := bstep (se 1 (by rfl) ⟨3431159, by rfl⟩ : syracuseStep 4574879 = 6862319) B6862319
theorem B2289343 : Blo 1354996 2289343 := bstep (se 1 (by rfl) ⟨1717007, by rfl⟩ : syracuseStep 2289343 = 3434015) B3434015
theorem B3051233 : Blo 1354996 3051233 := bstep (se 2 (by rfl) ⟨1144212, by rfl⟩ : syracuseStep 3051233 = 2288425) B2288425
theorem B3862505 : Blo 1354996 3862505 := bstep (se 2 (by rfl) ⟨1448439, by rfl⟩ : syracuseStep 3862505 = 2896879) B2896879
theorem B3256375 : Blo 1354996 3256375 := bstep (se 1 (by rfl) ⟨2442281, by rfl⟩ : syracuseStep 3256375 = 4884563) B4884563
theorem B50827337 : Blo 1354996 50827337 := bstep (se 2 (by rfl) ⟨19060251, by rfl⟩ : syracuseStep 50827337 = 38120503) B38120503
theorem B2289775 : Blo 1354996 2289775 := bstep (se 1 (by rfl) ⟨1717331, by rfl⟩ : syracuseStep 2289775 = 3434663) B3434663
theorem B1355935 : Blo 1354996 1355935 := bstep (se 1 (by rfl) ⟨1016951, by rfl⟩ : syracuseStep 1355935 = 2033903) B2033903
theorem B5787881 : Blo 1354996 5787881 := bstep (se 2 (by rfl) ⟨2170455, by rfl⟩ : syracuseStep 5787881 = 4340911) B4340911
theorem B1356271 : Blo 1354996 1356271 := bstep (se 1 (by rfl) ⟨1017203, by rfl⟩ : syracuseStep 1356271 = 2034407) B2034407
theorem B4575743 : Blo 1354996 4575743 := bstep (se 1 (by rfl) ⟨3431807, by rfl⟩ : syracuseStep 4575743 = 6863615) B6863615
theorem B1356287 : Blo 1354996 1356287 := bstep (se 1 (by rfl) ⟨1017215, by rfl⟩ : syracuseStep 1356287 = 2034431) B2034431
theorem B3052385 : Blo 1354996 3052385 := bstep (se 2 (by rfl) ⟨1144644, by rfl⟩ : syracuseStep 3052385 = 2289289) B2289289
theorem B422982749 : Blo 1354996 422982749 := bstep (se 3 (by rfl) ⟨79309265, by rfl⟩ : syracuseStep 422982749 = 158618531) B158618531
theorem B1356911 : Blo 1354996 1356911 := bstep (se 1 (by rfl) ⟨1017683, by rfl⟩ : syracuseStep 1356911 = 2035367) B2035367
theorem B4576391 : Blo 1354996 4576391 := bstep (se 1 (by rfl) ⟨3432293, by rfl⟩ : syracuseStep 4576391 = 6864587) B6864587
theorem B1356959 : Blo 1354996 1356959 := bstep (se 1 (by rfl) ⟨1017719, by rfl⟩ : syracuseStep 1356959 = 2035439) B2035439
theorem B1930495 : Blo 1354996 1930495 := bstep (se 1 (by rfl) ⟨1447871, by rfl⟩ : syracuseStep 1930495 = 2895743) B2895743
theorem B23492393 : Blo 1354996 23492393 := bstep (se 2 (by rfl) ⟨8809647, by rfl⟩ : syracuseStep 23492393 = 17619295) B17619295
theorem B18561449 : Blo 1354996 18561449 := bstep (se 2 (by rfl) ⟨6960543, by rfl⟩ : syracuseStep 18561449 = 13921087) B13921087
theorem B7723937 : Blo 1354996 7723937 := bstep (se 2 (by rfl) ⟨2896476, by rfl⟩ : syracuseStep 7723937 = 5792953) B5792953
theorem B3431585 : Blo 1354996 3431585 := bstep (se 2 (by rfl) ⟨1286844, by rfl⟩ : syracuseStep 3431585 = 2573689) B2573689
theorem B59464955 : Blo 1354996 59464955 := bstep (se 1 (by rfl) ⟨44598716, by rfl⟩ : syracuseStep 59464955 = 89197433) B89197433
theorem B3432091 : Blo 1354996 3432091 := bstep (se 1 (by rfl) ⟨2574068, by rfl⟩ : syracuseStep 3432091 = 5148137) B5148137
theorem B7831351 : Blo 1354996 7831351 := bstep (se 1 (by rfl) ⟨5873513, by rfl⟩ : syracuseStep 7831351 = 11747027) B11747027
theorem B4579199 : Blo 1354996 4579199 := bstep (se 1 (by rfl) ⟨3434399, by rfl⟩ : syracuseStep 4579199 = 6868799) B6868799
theorem B4341833 : Blo 1354996 4341833 := bstep (se 2 (by rfl) ⟨1628187, by rfl⟩ : syracuseStep 4341833 = 3256375) B3256375
theorem B3858587 : Blo 1354996 3858587 := bstep (se 1 (by rfl) ⟨2893940, by rfl⟩ : syracuseStep 3858587 = 5787881) B5787881
theorem B2032553 : Blo 1354996 2032553 := bstep (se 2 (by rfl) ⟨762207, by rfl⟩ : syracuseStep 2032553 = 1524415) B1524415
theorem B2033087 : Blo 1354996 2033087 := bstep (se 1 (by rfl) ⟨1524815, by rfl⟩ : syracuseStep 2033087 = 3049631) B3049631
theorem B2573993 : Blo 1354996 2573993 := bstep (se 2 (by rfl) ⟨965247, by rfl⟩ : syracuseStep 2573993 = 1930495) B1930495
theorem B5146679 : Blo 1354996 5146679 := bstep (se 1 (by rfl) ⟨3860009, by rfl⟩ : syracuseStep 5146679 = 7720019) B7720019
theorem B2287723 : Blo 1354996 2287723 := bstep (se 1 (by rfl) ⟨1715792, by rfl⟩ : syracuseStep 2287723 = 3431585) B3431585
theorem B39643303 : Blo 1354996 39643303 := bstep (se 1 (by rfl) ⟨29732477, by rfl⟩ : syracuseStep 39643303 = 59464955) B59464955
theorem B2033975 : Blo 1354996 2033975 := bstep (se 1 (by rfl) ⟨1525481, by rfl⟩ : syracuseStep 2033975 = 3050963) B3050963
theorem B10291535 : Blo 1354996 10291535 := bstep (se 1 (by rfl) ⟨7718651, by rfl⟩ : syracuseStep 10291535 = 15437303) B15437303
theorem B3049919 : Blo 1354996 3049919 := bstep (se 1 (by rfl) ⟨2287439, by rfl⟩ : syracuseStep 3049919 = 4574879) B4574879
theorem B2034155 : Blo 1354996 2034155 := bstep (se 1 (by rfl) ⟨1525616, by rfl⟩ : syracuseStep 2034155 = 3051233) B3051233
theorem B2575003 : Blo 1354996 2575003 := bstep (se 1 (by rfl) ⟨1931252, by rfl⟩ : syracuseStep 2575003 = 3862505) B3862505
theorem B33884891 : Blo 1354996 33884891 := bstep (se 1 (by rfl) ⟨25413668, by rfl⟩ : syracuseStep 33884891 = 50827337) B50827337
theorem B3050495 : Blo 1354996 3050495 := bstep (se 1 (by rfl) ⟨2287871, by rfl⟩ : syracuseStep 3050495 = 4575743) B4575743
theorem B3861503 : Blo 1354996 3861503 := bstep (se 1 (by rfl) ⟨2896127, by rfl⟩ : syracuseStep 3861503 = 5792255) B5792255
theorem B5795003 : Blo 1354996 5795003 := bstep (se 1 (by rfl) ⟨4346252, by rfl⟩ : syracuseStep 5795003 = 8692505) B8692505
theorem B2034923 : Blo 1354996 2034923 := bstep (se 1 (by rfl) ⟨1526192, by rfl⟩ : syracuseStep 2034923 = 3052385) B3052385
theorem B1355007 : Blo 1354996 1355007 := bstep (se 1 (by rfl) ⟨1016255, by rfl⟩ : syracuseStep 1355007 = 2032511) B2032511
theorem B1355111 : Blo 1354996 1355111 := bstep (se 1 (by rfl) ⟨1016333, by rfl⟩ : syracuseStep 1355111 = 2032667) B2032667
theorem B281988499 : Blo 1354996 281988499 := bstep (se 1 (by rfl) ⟨211491374, by rfl⟩ : syracuseStep 281988499 = 422982749) B422982749
theorem B3050927 : Blo 1354996 3050927 := bstep (se 1 (by rfl) ⟨2288195, by rfl⟩ : syracuseStep 3050927 = 4576391) B4576391
theorem B1355215 : Blo 1354996 1355215 := bstep (se 1 (by rfl) ⟨1016411, by rfl⟩ : syracuseStep 1355215 = 2032823) B2032823
theorem B1355711 : Blo 1354996 1355711 := bstep (se 1 (by rfl) ⟨1016783, by rfl⟩ : syracuseStep 1355711 = 2033567) B2033567
theorem B12374299 : Blo 1354996 12374299 := bstep (se 1 (by rfl) ⟨9280724, by rfl⟩ : syracuseStep 12374299 = 18561449) B18561449
theorem B1356095 : Blo 1354996 1356095 := bstep (se 1 (by rfl) ⟨1017071, by rfl⟩ : syracuseStep 1356095 = 2034143) B2034143
theorem B5149291 : Blo 1354996 5149291 := bstep (se 1 (by rfl) ⟨3861968, by rfl⟩ : syracuseStep 5149291 = 7723937) B7723937
theorem B4576121 : Blo 1354996 4576121 := bstep (se 2 (by rfl) ⟨1716045, by rfl⟩ : syracuseStep 4576121 = 3432091) B3432091
theorem B3052457 : Blo 1354996 3052457 := bstep (se 2 (by rfl) ⟨1144671, by rfl⟩ : syracuseStep 3052457 = 2289343) B2289343
theorem B1356827 : Blo 1354996 1356827 := bstep (se 1 (by rfl) ⟨1017620, by rfl⟩ : syracuseStep 1356827 = 2035241) B2035241
theorem B10441801 : Blo 1354996 10441801 := bstep (se 2 (by rfl) ⟨3915675, by rfl⟩ : syracuseStep 10441801 = 7831351) B7831351
theorem B3052799 : Blo 1354996 3052799 := bstep (se 1 (by rfl) ⟨2289599, by rfl⟩ : syracuseStep 3052799 = 4579199) B4579199
theorem B3053033 : Blo 1354996 3053033 := bstep (se 2 (by rfl) ⟨1144887, by rfl⟩ : syracuseStep 3053033 = 2289775) B2289775
theorem B5789879 : Blo 1354996 5789879 := bstep (se 1 (by rfl) ⟨4342409, by rfl⟩ : syracuseStep 5789879 = 8684819) B8684819
theorem B19822877 : Blo 1354996 19822877 := bstep (se 3 (by rfl) ⟨3716789, by rfl⟩ : syracuseStep 19822877 = 7433579) B7433579
theorem B15661595 : Blo 1354996 15661595 := bstep (se 1 (by rfl) ⟨11746196, by rfl⟩ : syracuseStep 15661595 = 23492393) B23492393
theorem B17611769 : Blo 1354996 17611769 := bstep (se 2 (by rfl) ⟨6604413, by rfl⟩ : syracuseStep 17611769 = 13208827) B13208827
theorem B2572391 : Blo 1354996 2572391 := bstep (se 1 (by rfl) ⟨1929293, by rfl⟩ : syracuseStep 2572391 = 3858587) B3858587
theorem B16499065 : Blo 1354996 16499065 := bstep (se 2 (by rfl) ⟨6187149, by rfl⟩ : syracuseStep 16499065 = 12374299) B12374299
theorem B6865721 : Blo 1354996 6865721 := bstep (se 2 (by rfl) ⟨2574645, by rfl⟩ : syracuseStep 6865721 = 5149291) B5149291
theorem B3433337 : Blo 1354996 3433337 := bstep (se 2 (by rfl) ⟨1287501, by rfl⟩ : syracuseStep 3433337 = 2575003) B2575003
theorem B3859919 : Blo 1354996 3859919 := bstep (se 1 (by rfl) ⟨2894939, by rfl⟩ : syracuseStep 3859919 = 5789879) B5789879
theorem B13215251 : Blo 1354996 13215251 := bstep (se 1 (by rfl) ⟨9911438, by rfl⟩ : syracuseStep 13215251 = 19822877) B19822877
theorem B2033279 : Blo 1354996 2033279 := bstep (se 1 (by rfl) ⟨1524959, by rfl⟩ : syracuseStep 2033279 = 3049919) B3049919
theorem B2033663 : Blo 1354996 2033663 := bstep (se 1 (by rfl) ⟨1525247, by rfl⟩ : syracuseStep 2033663 = 3050495) B3050495
theorem B2574335 : Blo 1354996 2574335 := bstep (se 1 (by rfl) ⟨1930751, by rfl⟩ : syracuseStep 2574335 = 3861503) B3861503
theorem B2033951 : Blo 1354996 2033951 := bstep (se 1 (by rfl) ⟨1525463, by rfl⟩ : syracuseStep 2033951 = 3050927) B3050927
theorem B2894555 : Blo 1354996 2894555 := bstep (se 1 (by rfl) ⟨2170916, by rfl⟩ : syracuseStep 2894555 = 4341833) B4341833
theorem B3050297 : Blo 1354996 3050297 := bstep (se 2 (by rfl) ⟨1143861, by rfl⟩ : syracuseStep 3050297 = 2287723) B2287723
theorem B52857737 : Blo 1354996 52857737 := bstep (se 2 (by rfl) ⟨19821651, by rfl⟩ : syracuseStep 52857737 = 39643303) B39643303
theorem B15453341 : Blo 1354996 15453341 := bstep (se 3 (by rfl) ⟨2897501, by rfl⟩ : syracuseStep 15453341 = 5795003) B5795003
theorem B3050747 : Blo 1354996 3050747 := bstep (se 1 (by rfl) ⟨2288060, by rfl⟩ : syracuseStep 3050747 = 4576121) B4576121
theorem B1355035 : Blo 1354996 1355035 := bstep (se 1 (by rfl) ⟨1016276, by rfl⟩ : syracuseStep 1355035 = 2032553) B2032553
theorem B2034971 : Blo 1354996 2034971 := bstep (se 1 (by rfl) ⟨1526228, by rfl⟩ : syracuseStep 2034971 = 3052457) B3052457
theorem B2035199 : Blo 1354996 2035199 := bstep (se 1 (by rfl) ⟨1526399, by rfl⟩ : syracuseStep 2035199 = 3052799) B3052799
theorem B1355391 : Blo 1354996 1355391 := bstep (se 1 (by rfl) ⟨1016543, by rfl⟩ : syracuseStep 1355391 = 2033087) B2033087
theorem B2035355 : Blo 1354996 2035355 := bstep (se 1 (by rfl) ⟨1526516, by rfl⟩ : syracuseStep 2035355 = 3053033) B3053033
theorem B1715995 : Blo 1354996 1715995 := bstep (se 1 (by rfl) ⟨1286996, by rfl⟩ : syracuseStep 1715995 = 2573993) B2573993
theorem B13922401 : Blo 1354996 13922401 := bstep (se 2 (by rfl) ⟨5220900, by rfl⟩ : syracuseStep 13922401 = 10441801) B10441801
theorem B1355983 : Blo 1354996 1355983 := bstep (se 1 (by rfl) ⟨1016987, by rfl⟩ : syracuseStep 1355983 = 2033975) B2033975
theorem B6861023 : Blo 1354996 6861023 := bstep (se 1 (by rfl) ⟨5145767, by rfl⟩ : syracuseStep 6861023 = 10291535) B10291535
theorem B1356103 : Blo 1354996 1356103 := bstep (se 1 (by rfl) ⟨1017077, by rfl⟩ : syracuseStep 1356103 = 2034155) B2034155
theorem B10441063 : Blo 1354996 10441063 := bstep (se 1 (by rfl) ⟨7830797, by rfl⟩ : syracuseStep 10441063 = 15661595) B15661595
theorem B22589927 : Blo 1354996 22589927 := bstep (se 1 (by rfl) ⟨16942445, by rfl⟩ : syracuseStep 22589927 = 33884891) B33884891
theorem B375984665 : Blo 1354996 375984665 := bstep (se 2 (by rfl) ⟨140994249, by rfl⟩ : syracuseStep 375984665 = 281988499) B281988499
theorem B1356615 : Blo 1354996 1356615 := bstep (se 1 (by rfl) ⟨1017461, by rfl⟩ : syracuseStep 1356615 = 2034923) B2034923
theorem B3431119 : Blo 1354996 3431119 := bstep (se 1 (by rfl) ⟨2573339, by rfl⟩ : syracuseStep 3431119 = 5146679) B5146679
theorem B46964717 : Blo 1354996 46964717 := bstep (se 3 (by rfl) ⟨8805884, by rfl⟩ : syracuseStep 46964717 = 17611769) B17611769
theorem B18563201 : Blo 1354996 18563201 := bstep (se 2 (by rfl) ⟨6961200, by rfl⟩ : syracuseStep 18563201 = 13922401) B13922401
theorem B2573279 : Blo 1354996 2573279 := bstep (se 1 (by rfl) ⟨1929959, by rfl⟩ : syracuseStep 2573279 = 3859919) B3859919
theorem B2033531 : Blo 1354996 2033531 := bstep (se 1 (by rfl) ⟨1525148, by rfl⟩ : syracuseStep 2033531 = 3050297) B3050297
theorem B7718813 : Blo 1354996 7718813 := bstep (se 3 (by rfl) ⟨1447277, by rfl⟩ : syracuseStep 7718813 = 2894555) B2894555
theorem B2033831 : Blo 1354996 2033831 := bstep (se 1 (by rfl) ⟨1525373, by rfl⟩ : syracuseStep 2033831 = 3050747) B3050747
theorem B2287993 : Blo 1354996 2287993 := bstep (se 2 (by rfl) ⟨857997, by rfl⟩ : syracuseStep 2287993 = 1715995) B1715995
theorem B1714927 : Blo 1354996 1714927 := bstep (se 1 (by rfl) ⟨1286195, by rfl⟩ : syracuseStep 1714927 = 2572391) B2572391
theorem B4574015 : Blo 1354996 4574015 := bstep (se 1 (by rfl) ⟨3430511, by rfl⟩ : syracuseStep 4574015 = 6861023) B6861023
theorem B15059951 : Blo 1354996 15059951 := bstep (se 1 (by rfl) ⟨11294963, by rfl⟩ : syracuseStep 15059951 = 22589927) B22589927
theorem B13921417 : Blo 1354996 13921417 := bstep (se 2 (by rfl) ⟨5220531, by rfl⟩ : syracuseStep 13921417 = 10441063) B10441063
theorem B21998753 : Blo 1354996 21998753 := bstep (se 2 (by rfl) ⟨8249532, by rfl⟩ : syracuseStep 21998753 = 16499065) B16499065
theorem B2288891 : Blo 1354996 2288891 := bstep (se 1 (by rfl) ⟨1716668, by rfl⟩ : syracuseStep 2288891 = 3433337) B3433337
theorem B4574825 : Blo 1354996 4574825 := bstep (se 2 (by rfl) ⟨1715559, by rfl⟩ : syracuseStep 4574825 = 3431119) B3431119
theorem B8810167 : Blo 1354996 8810167 := bstep (se 1 (by rfl) ⟨6607625, by rfl⟩ : syracuseStep 8810167 = 13215251) B13215251
theorem B1355519 : Blo 1354996 1355519 := bstep (se 1 (by rfl) ⟨1016639, by rfl⟩ : syracuseStep 1355519 = 2033279) B2033279
theorem B1355775 : Blo 1354996 1355775 := bstep (se 1 (by rfl) ⟨1016831, by rfl⟩ : syracuseStep 1355775 = 2033663) B2033663
theorem B1716223 : Blo 1354996 1716223 := bstep (se 1 (by rfl) ⟨1287167, by rfl⟩ : syracuseStep 1716223 = 2574335) B2574335
theorem B1355967 : Blo 1354996 1355967 := bstep (se 1 (by rfl) ⟨1016975, by rfl⟩ : syracuseStep 1355967 = 2033951) B2033951
theorem B35238491 : Blo 1354996 35238491 := bstep (se 1 (by rfl) ⟨26428868, by rfl⟩ : syracuseStep 35238491 = 52857737) B52857737
theorem B10302227 : Blo 1354996 10302227 := bstep (se 1 (by rfl) ⟨7726670, by rfl⟩ : syracuseStep 10302227 = 15453341) B15453341
theorem B1356647 : Blo 1354996 1356647 := bstep (se 1 (by rfl) ⟨1017485, by rfl⟩ : syracuseStep 1356647 = 2034971) B2034971
theorem B1356799 : Blo 1354996 1356799 := bstep (se 1 (by rfl) ⟨1017599, by rfl⟩ : syracuseStep 1356799 = 2035199) B2035199
theorem B1356903 : Blo 1354996 1356903 := bstep (se 1 (by rfl) ⟨1017677, by rfl⟩ : syracuseStep 1356903 = 2035355) B2035355
theorem B250656443 : Blo 1354996 250656443 := bstep (se 1 (by rfl) ⟨187992332, by rfl⟩ : syracuseStep 250656443 = 375984665) B375984665
theorem B4577147 : Blo 1354996 4577147 := bstep (se 1 (by rfl) ⟨3432860, by rfl⟩ : syracuseStep 4577147 = 6865721) B6865721
theorem B31309811 : Blo 1354996 31309811 := bstep (se 1 (by rfl) ⟨23482358, by rfl⟩ : syracuseStep 31309811 = 46964717) B46964717
theorem B2286569 : Blo 1354996 2286569 := bstep (se 2 (by rfl) ⟨857463, by rfl⟩ : syracuseStep 2286569 = 1714927) B1714927
theorem B5145875 : Blo 1354996 5145875 := bstep (se 1 (by rfl) ⟨3859406, by rfl⟩ : syracuseStep 5145875 = 7718813) B7718813
theorem B3049343 : Blo 1354996 3049343 := bstep (se 1 (by rfl) ⟨2287007, by rfl⟩ : syracuseStep 3049343 = 4574015) B4574015
theorem B14665835 : Blo 1354996 14665835 := bstep (se 1 (by rfl) ⟨10999376, by rfl⟩ : syracuseStep 14665835 = 21998753) B21998753
theorem B1525927 : Blo 1354996 1525927 := bstep (se 1 (by rfl) ⟨1144445, by rfl⟩ : syracuseStep 1525927 = 2288891) B2288891
theorem B3049883 : Blo 1354996 3049883 := bstep (se 1 (by rfl) ⟨2287412, by rfl⟩ : syracuseStep 3049883 = 4574825) B4574825
theorem B2288297 : Blo 1354996 2288297 := bstep (se 2 (by rfl) ⟨858111, by rfl⟩ : syracuseStep 2288297 = 1716223) B1716223
theorem B3050657 : Blo 1354996 3050657 := bstep (se 2 (by rfl) ⟨1143996, by rfl⟩ : syracuseStep 3050657 = 2287993) B2287993
theorem B6868151 : Blo 1354996 6868151 := bstep (se 1 (by rfl) ⟨5151113, by rfl⟩ : syracuseStep 6868151 = 10302227) B10302227
theorem B1715519 : Blo 1354996 1715519 := bstep (se 1 (by rfl) ⟨1286639, by rfl⟩ : syracuseStep 1715519 = 2573279) B2573279
theorem B167104295 : Blo 1354996 167104295 := bstep (se 1 (by rfl) ⟨125328221, by rfl⟩ : syracuseStep 167104295 = 250656443) B250656443
theorem B1355687 : Blo 1354996 1355687 := bstep (se 1 (by rfl) ⟨1016765, by rfl⟩ : syracuseStep 1355687 = 2033531) B2033531
theorem B3051431 : Blo 1354996 3051431 := bstep (se 1 (by rfl) ⟨2288573, by rfl⟩ : syracuseStep 3051431 = 4577147) B4577147
theorem B1355887 : Blo 1354996 1355887 := bstep (se 1 (by rfl) ⟨1016915, by rfl⟩ : syracuseStep 1355887 = 2033831) B2033831
theorem B10039967 : Blo 1354996 10039967 := bstep (se 1 (by rfl) ⟨7529975, by rfl⟩ : syracuseStep 10039967 = 15059951) B15059951
theorem B12375467 : Blo 1354996 12375467 := bstep (se 1 (by rfl) ⟨9281600, by rfl⟩ : syracuseStep 12375467 = 18563201) B18563201
theorem B23492327 : Blo 1354996 23492327 := bstep (se 1 (by rfl) ⟨17619245, by rfl⟩ : syracuseStep 23492327 = 35238491) B35238491
theorem B18561889 : Blo 1354996 18561889 := bstep (se 2 (by rfl) ⟨6960708, by rfl⟩ : syracuseStep 18561889 = 13921417) B13921417
theorem B11746889 : Blo 1354996 11746889 := bstep (se 2 (by rfl) ⟨4405083, by rfl⟩ : syracuseStep 11746889 = 8810167) B8810167
theorem B20873207 : Blo 1354996 20873207 := bstep (se 1 (by rfl) ⟨15654905, by rfl⟩ : syracuseStep 20873207 = 31309811) B31309811
theorem B6693311 : Blo 1354996 6693311 := bstep (se 1 (by rfl) ⟨5019983, by rfl⟩ : syracuseStep 6693311 = 10039967) B10039967
theorem B1524379 : Blo 1354996 1524379 := bstep (se 1 (by rfl) ⟨1143284, by rfl⟩ : syracuseStep 1524379 = 2286569) B2286569
theorem B8250311 : Blo 1354996 8250311 := bstep (se 1 (by rfl) ⟨6187733, by rfl⟩ : syracuseStep 8250311 = 12375467) B12375467
theorem B24749185 : Blo 1354996 24749185 := bstep (se 2 (by rfl) ⟨9280944, by rfl⟩ : syracuseStep 24749185 = 18561889) B18561889
theorem B2032895 : Blo 1354996 2032895 := bstep (se 1 (by rfl) ⟨1524671, by rfl⟩ : syracuseStep 2032895 = 3049343) B3049343
theorem B2033255 : Blo 1354996 2033255 := bstep (se 1 (by rfl) ⟨1524941, by rfl⟩ : syracuseStep 2033255 = 3049883) B3049883
theorem B1525531 : Blo 1354996 1525531 := bstep (se 1 (by rfl) ⟨1144148, by rfl⟩ : syracuseStep 1525531 = 2288297) B2288297
theorem B62646205 : Blo 1354996 62646205 := bstep (se 3 (by rfl) ⟨11746163, by rfl⟩ : syracuseStep 62646205 = 23492327) B23492327
theorem B2033771 : Blo 1354996 2033771 := bstep (se 1 (by rfl) ⟨1525328, by rfl⟩ : syracuseStep 2033771 = 3050657) B3050657
theorem B2034287 : Blo 1354996 2034287 := bstep (se 1 (by rfl) ⟨1525715, by rfl⟩ : syracuseStep 2034287 = 3051431) B3051431
theorem B2034569 : Blo 1354996 2034569 := bstep (se 2 (by rfl) ⟨762963, by rfl⟩ : syracuseStep 2034569 = 1525927) B1525927
theorem B4574717 : Blo 1354996 4574717 := bstep (se 3 (by rfl) ⟨857759, by rfl⟩ : syracuseStep 4574717 = 1715519) B1715519
theorem B9777223 : Blo 1354996 9777223 := bstep (se 1 (by rfl) ⟨7332917, by rfl⟩ : syracuseStep 9777223 = 14665835) B14665835
theorem B13915471 : Blo 1354996 13915471 := bstep (se 1 (by rfl) ⟨10436603, by rfl⟩ : syracuseStep 13915471 = 20873207) B20873207
theorem B3430583 : Blo 1354996 3430583 := bstep (se 1 (by rfl) ⟨2572937, by rfl⟩ : syracuseStep 3430583 = 5145875) B5145875
theorem B4578767 : Blo 1354996 4578767 := bstep (se 1 (by rfl) ⟨3434075, by rfl⟩ : syracuseStep 4578767 = 6868151) B6868151
theorem B7831259 : Blo 1354996 7831259 := bstep (se 1 (by rfl) ⟨5873444, by rfl⟩ : syracuseStep 7831259 = 11746889) B11746889
theorem B111402863 : Blo 1354996 111402863 := bstep (se 1 (by rfl) ⟨83552147, by rfl⟩ : syracuseStep 111402863 = 167104295) B167104295
theorem B2032505 : Blo 1354996 2032505 := bstep (se 2 (by rfl) ⟨762189, by rfl⟩ : syracuseStep 2032505 = 1524379) B1524379
theorem B2287055 : Blo 1354996 2287055 := bstep (se 1 (by rfl) ⟨1715291, by rfl⟩ : syracuseStep 2287055 = 3430583) B3430583
theorem B32998913 : Blo 1354996 32998913 := bstep (se 2 (by rfl) ⟨12374592, by rfl⟩ : syracuseStep 32998913 = 24749185) B24749185
theorem B3049811 : Blo 1354996 3049811 := bstep (se 1 (by rfl) ⟨2287358, by rfl⟩ : syracuseStep 3049811 = 4574717) B4574717
theorem B2034041 : Blo 1354996 2034041 := bstep (se 2 (by rfl) ⟨762765, by rfl⟩ : syracuseStep 2034041 = 1525531) B1525531
theorem B5220839 : Blo 1354996 5220839 := bstep (se 1 (by rfl) ⟨3915629, by rfl⟩ : syracuseStep 5220839 = 7831259) B7831259
theorem B83528273 : Blo 1354996 83528273 := bstep (se 2 (by rfl) ⟨31323102, by rfl⟩ : syracuseStep 83528273 = 62646205) B62646205
theorem B13036297 : Blo 1354996 13036297 := bstep (se 2 (by rfl) ⟨4888611, by rfl⟩ : syracuseStep 13036297 = 9777223) B9777223
theorem B5500207 : Blo 1354996 5500207 := bstep (se 1 (by rfl) ⟨4125155, by rfl⟩ : syracuseStep 5500207 = 8250311) B8250311
theorem B1355263 : Blo 1354996 1355263 := bstep (se 1 (by rfl) ⟨1016447, by rfl⟩ : syracuseStep 1355263 = 2032895) B2032895
theorem B1355503 : Blo 1354996 1355503 := bstep (se 1 (by rfl) ⟨1016627, by rfl⟩ : syracuseStep 1355503 = 2033255) B2033255
theorem B1355847 : Blo 1354996 1355847 := bstep (se 1 (by rfl) ⟨1016885, by rfl⟩ : syracuseStep 1355847 = 2033771) B2033771
theorem B1356191 : Blo 1354996 1356191 := bstep (se 1 (by rfl) ⟨1017143, by rfl⟩ : syracuseStep 1356191 = 2034287) B2034287
theorem B1356379 : Blo 1354996 1356379 := bstep (se 1 (by rfl) ⟨1017284, by rfl⟩ : syracuseStep 1356379 = 2034569) B2034569
theorem B3052511 : Blo 1354996 3052511 := bstep (se 1 (by rfl) ⟨2289383, by rfl⟩ : syracuseStep 3052511 = 4578767) B4578767
theorem B17848829 : Blo 1354996 17848829 := bstep (se 3 (by rfl) ⟨3346655, by rfl⟩ : syracuseStep 17848829 = 6693311) B6693311
theorem B18553961 : Blo 1354996 18553961 := bstep (se 2 (by rfl) ⟨6957735, by rfl⟩ : syracuseStep 18553961 = 13915471) B13915471
theorem B74268575 : Blo 1354996 74268575 := bstep (se 1 (by rfl) ⟨55701431, by rfl⟩ : syracuseStep 74268575 = 111402863) B111402863
theorem B1524703 : Blo 1354996 1524703 := bstep (se 1 (by rfl) ⟨1143527, by rfl⟩ : syracuseStep 1524703 = 2287055) B2287055
theorem B47596877 : Blo 1354996 47596877 := bstep (se 3 (by rfl) ⟨8924414, by rfl⟩ : syracuseStep 47596877 = 17848829) B17848829
theorem B2033207 : Blo 1354996 2033207 := bstep (se 1 (by rfl) ⟨1524905, by rfl⟩ : syracuseStep 2033207 = 3049811) B3049811
theorem B1355003 : Blo 1354996 1355003 := bstep (se 1 (by rfl) ⟨1016252, by rfl⟩ : syracuseStep 1355003 = 2032505) B2032505
theorem B2035007 : Blo 1354996 2035007 := bstep (se 1 (by rfl) ⟨1526255, by rfl⟩ : syracuseStep 2035007 = 3052511) B3052511
theorem B21999275 : Blo 1354996 21999275 := bstep (se 1 (by rfl) ⟨16499456, by rfl⟩ : syracuseStep 21999275 = 32998913) B32998913
theorem B13922237 : Blo 1354996 13922237 := bstep (se 3 (by rfl) ⟨2610419, by rfl⟩ : syracuseStep 13922237 = 5220839) B5220839
theorem B1356027 : Blo 1354996 1356027 := bstep (se 1 (by rfl) ⟨1017020, by rfl⟩ : syracuseStep 1356027 = 2034041) B2034041
theorem B55685515 : Blo 1354996 55685515 := bstep (se 1 (by rfl) ⟨41764136, by rfl⟩ : syracuseStep 55685515 = 83528273) B83528273
theorem B17381729 : Blo 1354996 17381729 := bstep (se 2 (by rfl) ⟨6518148, by rfl⟩ : syracuseStep 17381729 = 13036297) B13036297
theorem B29334437 : Blo 1354996 29334437 := bstep (se 4 (by rfl) ⟨2750103, by rfl⟩ : syracuseStep 29334437 = 5500207) B5500207
theorem B12369307 : Blo 1354996 12369307 := bstep (se 1 (by rfl) ⟨9276980, by rfl⟩ : syracuseStep 12369307 = 18553961) B18553961
theorem B49512383 : Blo 1354996 49512383 := bstep (se 1 (by rfl) ⟨37134287, by rfl⟩ : syracuseStep 49512383 = 74268575) B74268575
theorem B507700021 : Blo 1354996 507700021 := bstep (se 5 (by rfl) ⟨23798438, by rfl⟩ : syracuseStep 507700021 = 47596877) B47596877
theorem B2032937 : Blo 1354996 2032937 := bstep (se 2 (by rfl) ⟨762351, by rfl⟩ : syracuseStep 2032937 = 1524703) B1524703
theorem B16492409 : Blo 1354996 16492409 := bstep (se 2 (by rfl) ⟨6184653, by rfl⟩ : syracuseStep 16492409 = 12369307) B12369307
theorem B19556291 : Blo 1354996 19556291 := bstep (se 1 (by rfl) ⟨14667218, by rfl⟩ : syracuseStep 19556291 = 29334437) B29334437
theorem B14666183 : Blo 1354996 14666183 := bstep (se 1 (by rfl) ⟨10999637, by rfl⟩ : syracuseStep 14666183 = 21999275) B21999275
theorem B33008255 : Blo 1354996 33008255 := bstep (se 1 (by rfl) ⟨24756191, by rfl⟩ : syracuseStep 33008255 = 49512383) B49512383
theorem B74247353 : Blo 1354996 74247353 := bstep (se 2 (by rfl) ⟨27842757, by rfl⟩ : syracuseStep 74247353 = 55685515) B55685515
theorem B1355471 : Blo 1354996 1355471 := bstep (se 1 (by rfl) ⟨1016603, by rfl⟩ : syracuseStep 1355471 = 2033207) B2033207
theorem B11587819 : Blo 1354996 11587819 := bstep (se 1 (by rfl) ⟨8690864, by rfl⟩ : syracuseStep 11587819 = 17381729) B17381729
theorem B1356671 : Blo 1354996 1356671 := bstep (se 1 (by rfl) ⟨1017503, by rfl⟩ : syracuseStep 1356671 = 2035007) B2035007
theorem B37125965 : Blo 1354996 37125965 := bstep (se 3 (by rfl) ⟨6961118, by rfl⟩ : syracuseStep 37125965 = 13922237) B13922237
theorem B15450425 : Blo 1354996 15450425 := bstep (se 2 (by rfl) ⟨5793909, by rfl⟩ : syracuseStep 15450425 = 11587819) B11587819
theorem B10994939 : Blo 1354996 10994939 := bstep (se 1 (by rfl) ⟨8246204, by rfl⟩ : syracuseStep 10994939 = 16492409) B16492409
theorem B22005503 : Blo 1354996 22005503 := bstep (se 1 (by rfl) ⟨16504127, by rfl⟩ : syracuseStep 22005503 = 33008255) B33008255
theorem B49498235 : Blo 1354996 49498235 := bstep (se 1 (by rfl) ⟨37123676, by rfl⟩ : syracuseStep 49498235 = 74247353) B74247353
theorem B99002573 : Blo 1354996 99002573 := bstep (se 3 (by rfl) ⟨18562982, by rfl⟩ : syracuseStep 99002573 = 37125965) B37125965
theorem B1355291 : Blo 1354996 1355291 := bstep (se 1 (by rfl) ⟨1016468, by rfl⟩ : syracuseStep 1355291 = 2032937) B2032937
theorem B676933361 : Blo 1354996 676933361 := bstep (se 2 (by rfl) ⟨253850010, by rfl⟩ : syracuseStep 676933361 = 507700021) B507700021
theorem B13037527 : Blo 1354996 13037527 := bstep (se 1 (by rfl) ⟨9778145, by rfl⟩ : syracuseStep 13037527 = 19556291) B19556291
theorem B9777455 : Blo 1354996 9777455 := bstep (se 1 (by rfl) ⟨7333091, by rfl⟩ : syracuseStep 9777455 = 14666183) B14666183
theorem B32998823 : Blo 1354996 32998823 := bstep (se 1 (by rfl) ⟨24749117, by rfl⟩ : syracuseStep 32998823 = 49498235) B49498235
theorem B10300283 : Blo 1354996 10300283 := bstep (se 1 (by rfl) ⟨7725212, by rfl⟩ : syracuseStep 10300283 = 15450425) B15450425
theorem B6518303 : Blo 1354996 6518303 := bstep (se 1 (by rfl) ⟨4888727, by rfl⟩ : syracuseStep 6518303 = 9777455) B9777455
theorem B7329959 : Blo 1354996 7329959 := bstep (se 1 (by rfl) ⟨5497469, by rfl⟩ : syracuseStep 7329959 = 10994939) B10994939
theorem B14670335 : Blo 1354996 14670335 := bstep (se 1 (by rfl) ⟨11002751, by rfl⟩ : syracuseStep 14670335 = 22005503) B22005503
theorem B66001715 : Blo 1354996 66001715 := bstep (se 1 (by rfl) ⟨49501286, by rfl⟩ : syracuseStep 66001715 = 99002573) B99002573
theorem B451288907 : Blo 1354996 451288907 := bstep (se 1 (by rfl) ⟨338466680, by rfl⟩ : syracuseStep 451288907 = 676933361) B676933361
theorem B17383369 : Blo 1354996 17383369 := bstep (se 2 (by rfl) ⟨6518763, by rfl⟩ : syracuseStep 17383369 = 13037527) B13037527
theorem B44001143 : Blo 1354996 44001143 := bstep (se 1 (by rfl) ⟨33000857, by rfl⟩ : syracuseStep 44001143 = 66001715) B66001715
theorem B6866855 : Blo 1354996 6866855 := bstep (se 1 (by rfl) ⟨5150141, by rfl⟩ : syracuseStep 6866855 = 10300283) B10300283
theorem B23177825 : Blo 1354996 23177825 := bstep (se 2 (by rfl) ⟨8691684, by rfl⟩ : syracuseStep 23177825 = 17383369) B17383369
theorem B21999215 : Blo 1354996 21999215 := bstep (se 1 (by rfl) ⟨16499411, by rfl⟩ : syracuseStep 21999215 = 32998823) B32998823
theorem B4345535 : Blo 1354996 4345535 := bstep (se 1 (by rfl) ⟨3259151, by rfl⟩ : syracuseStep 4345535 = 6518303) B6518303
theorem B4886639 : Blo 1354996 4886639 := bstep (se 1 (by rfl) ⟨3664979, by rfl⟩ : syracuseStep 4886639 = 7329959) B7329959
theorem B9780223 : Blo 1354996 9780223 := bstep (se 1 (by rfl) ⟨7335167, by rfl⟩ : syracuseStep 9780223 = 14670335) B14670335
theorem B300859271 : Blo 1354996 300859271 := bstep (se 1 (by rfl) ⟨225644453, by rfl⟩ : syracuseStep 300859271 = 451288907) B451288907
theorem B15451883 : Blo 1354996 15451883 := bstep (se 1 (by rfl) ⟨11588912, by rfl⟩ : syracuseStep 15451883 = 23177825) B23177825
theorem B14666143 : Blo 1354996 14666143 := bstep (se 1 (by rfl) ⟨10999607, by rfl⟩ : syracuseStep 14666143 = 21999215) B21999215
theorem B11588093 : Blo 1354996 11588093 := bstep (se 3 (by rfl) ⟨2172767, by rfl⟩ : syracuseStep 11588093 = 4345535) B4345535
theorem B3257759 : Blo 1354996 3257759 := bstep (se 1 (by rfl) ⟨2443319, by rfl⟩ : syracuseStep 3257759 = 4886639) B4886639
theorem B29334095 : Blo 1354996 29334095 := bstep (se 1 (by rfl) ⟨22000571, by rfl⟩ : syracuseStep 29334095 = 44001143) B44001143
theorem B4577903 : Blo 1354996 4577903 := bstep (se 1 (by rfl) ⟨3433427, by rfl⟩ : syracuseStep 4577903 = 6866855) B6866855
theorem B13040297 : Blo 1354996 13040297 := bstep (se 2 (by rfl) ⟨4890111, by rfl⟩ : syracuseStep 13040297 = 9780223) B9780223
theorem B200572847 : Blo 1354996 200572847 := bstep (se 1 (by rfl) ⟨150429635, by rfl⟩ : syracuseStep 200572847 = 300859271) B300859271
theorem B7725395 : Blo 1354996 7725395 := bstep (se 1 (by rfl) ⟨5794046, by rfl⟩ : syracuseStep 7725395 = 11588093) B11588093
theorem B19554857 : Blo 1354996 19554857 := bstep (se 2 (by rfl) ⟨7333071, by rfl⟩ : syracuseStep 19554857 = 14666143) B14666143
theorem B19556063 : Blo 1354996 19556063 := bstep (se 1 (by rfl) ⟨14667047, by rfl⟩ : syracuseStep 19556063 = 29334095) B29334095
theorem B8693531 : Blo 1354996 8693531 := bstep (se 1 (by rfl) ⟨6520148, by rfl⟩ : syracuseStep 8693531 = 13040297) B13040297
theorem B8687357 : Blo 1354996 8687357 := bstep (se 3 (by rfl) ⟨1628879, by rfl⟩ : syracuseStep 8687357 = 3257759) B3257759
theorem B10301255 : Blo 1354996 10301255 := bstep (se 1 (by rfl) ⟨7725941, by rfl⟩ : syracuseStep 10301255 = 15451883) B15451883
theorem B3051935 : Blo 1354996 3051935 := bstep (se 1 (by rfl) ⟨2288951, by rfl⟩ : syracuseStep 3051935 = 4577903) B4577903
theorem B133715231 : Blo 1354996 133715231 := bstep (se 1 (by rfl) ⟨100286423, by rfl⟩ : syracuseStep 133715231 = 200572847) B200572847
theorem B6867503 : Blo 1354996 6867503 := bstep (se 1 (by rfl) ⟨5150627, by rfl⟩ : syracuseStep 6867503 = 10301255) B10301255
theorem B2034623 : Blo 1354996 2034623 := bstep (se 1 (by rfl) ⟨1525967, by rfl⟩ : syracuseStep 2034623 = 3051935) B3051935
theorem B13036571 : Blo 1354996 13036571 := bstep (se 1 (by rfl) ⟨9777428, by rfl⟩ : syracuseStep 13036571 = 19554857) B19554857
theorem B13037375 : Blo 1354996 13037375 := bstep (se 1 (by rfl) ⟨9778031, by rfl⟩ : syracuseStep 13037375 = 19556063) B19556063
theorem B5795687 : Blo 1354996 5795687 := bstep (se 1 (by rfl) ⟨4346765, by rfl⟩ : syracuseStep 5795687 = 8693531) B8693531
theorem B5150263 : Blo 1354996 5150263 := bstep (se 1 (by rfl) ⟨3862697, by rfl⟩ : syracuseStep 5150263 = 7725395) B7725395
theorem B89143487 : Blo 1354996 89143487 := bstep (se 1 (by rfl) ⟨66857615, by rfl⟩ : syracuseStep 89143487 = 133715231) B133715231
theorem B5791571 : Blo 1354996 5791571 := bstep (se 1 (by rfl) ⟨4343678, by rfl⟩ : syracuseStep 5791571 = 8687357) B8687357
theorem B6867017 : Blo 1354996 6867017 := bstep (se 2 (by rfl) ⟨2575131, by rfl⟩ : syracuseStep 6867017 = 5150263) B5150263
theorem B3861047 : Blo 1354996 3861047 := bstep (se 1 (by rfl) ⟨2895785, by rfl⟩ : syracuseStep 3861047 = 5791571) B5791571
theorem B59428991 : Blo 1354996 59428991 := bstep (se 1 (by rfl) ⟨44571743, by rfl⟩ : syracuseStep 59428991 = 89143487) B89143487
theorem B1356415 : Blo 1354996 1356415 := bstep (se 1 (by rfl) ⟨1017311, by rfl⟩ : syracuseStep 1356415 = 2034623) B2034623
theorem B3863791 : Blo 1354996 3863791 := bstep (se 1 (by rfl) ⟨2897843, by rfl⟩ : syracuseStep 3863791 = 5795687) B5795687
theorem B4578335 : Blo 1354996 4578335 := bstep (se 1 (by rfl) ⟨3433751, by rfl⟩ : syracuseStep 4578335 = 6867503) B6867503
theorem B8691047 : Blo 1354996 8691047 := bstep (se 1 (by rfl) ⟨6518285, by rfl⟩ : syracuseStep 8691047 = 13036571) B13036571
theorem B8691583 : Blo 1354996 8691583 := bstep (se 1 (by rfl) ⟨6518687, by rfl⟩ : syracuseStep 8691583 = 13037375) B13037375
theorem B2574031 : Blo 1354996 2574031 := bstep (se 1 (by rfl) ⟨1930523, by rfl⟩ : syracuseStep 2574031 = 3861047) B3861047
theorem B5794031 : Blo 1354996 5794031 := bstep (se 1 (by rfl) ⟨4345523, by rfl⟩ : syracuseStep 5794031 = 8691047) B8691047
theorem B158477309 : Blo 1354996 158477309 := bstep (se 3 (by rfl) ⟨29714495, by rfl⟩ : syracuseStep 158477309 = 59428991) B59428991
theorem B3052223 : Blo 1354996 3052223 := bstep (se 1 (by rfl) ⟨2289167, by rfl⟩ : syracuseStep 3052223 = 4578335) B4578335
theorem B11588777 : Blo 1354996 11588777 := bstep (se 2 (by rfl) ⟨4345791, by rfl⟩ : syracuseStep 11588777 = 8691583) B8691583
theorem B4578011 : Blo 1354996 4578011 := bstep (se 1 (by rfl) ⟨3433508, by rfl⟩ : syracuseStep 4578011 = 6867017) B6867017
theorem B5151721 : Blo 1354996 5151721 := bstep (se 2 (by rfl) ⟨1931895, by rfl⟩ : syracuseStep 5151721 = 3863791) B3863791
theorem B7725851 : Blo 1354996 7725851 := bstep (se 1 (by rfl) ⟨5794388, by rfl⟩ : syracuseStep 7725851 = 11588777) B11588777
theorem B2034815 : Blo 1354996 2034815 := bstep (se 1 (by rfl) ⟨1526111, by rfl⟩ : syracuseStep 2034815 = 3052223) B3052223
theorem B6868961 : Blo 1354996 6868961 := bstep (se 2 (by rfl) ⟨2575860, by rfl⟩ : syracuseStep 6868961 = 5151721) B5151721
theorem B3862687 : Blo 1354996 3862687 := bstep (se 1 (by rfl) ⟨2897015, by rfl⟩ : syracuseStep 3862687 = 5794031) B5794031
theorem B3052007 : Blo 1354996 3052007 := bstep (se 1 (by rfl) ⟨2289005, by rfl⟩ : syracuseStep 3052007 = 4578011) B4578011
theorem B105651539 : Blo 1354996 105651539 := bstep (se 1 (by rfl) ⟨79238654, by rfl⟩ : syracuseStep 105651539 = 158477309) B158477309
theorem B3432041 : Blo 1354996 3432041 := bstep (se 2 (by rfl) ⟨1287015, by rfl⟩ : syracuseStep 3432041 = 2574031) B2574031
theorem B2288027 : Blo 1354996 2288027 := bstep (se 1 (by rfl) ⟨1716020, by rfl⟩ : syracuseStep 2288027 = 3432041) B3432041
theorem B2034671 : Blo 1354996 2034671 := bstep (se 1 (by rfl) ⟨1526003, by rfl⟩ : syracuseStep 2034671 = 3052007) B3052007
theorem B1356543 : Blo 1354996 1356543 := bstep (se 1 (by rfl) ⟨1017407, by rfl⟩ : syracuseStep 1356543 = 2034815) B2034815
theorem B5150249 : Blo 1354996 5150249 := bstep (se 2 (by rfl) ⟨1931343, by rfl⟩ : syracuseStep 5150249 = 3862687) B3862687
theorem B5150567 : Blo 1354996 5150567 := bstep (se 1 (by rfl) ⟨3862925, by rfl⟩ : syracuseStep 5150567 = 7725851) B7725851
theorem B70434359 : Blo 1354996 70434359 := bstep (se 1 (by rfl) ⟨52825769, by rfl⟩ : syracuseStep 70434359 = 105651539) B105651539
theorem B4579307 : Blo 1354996 4579307 := bstep (se 1 (by rfl) ⟨3434480, by rfl⟩ : syracuseStep 4579307 = 6868961) B6868961
theorem B3433499 : Blo 1354996 3433499 := bstep (se 1 (by rfl) ⟨2575124, by rfl⟩ : syracuseStep 3433499 = 5150249) B5150249
theorem B3433711 : Blo 1354996 3433711 := bstep (se 1 (by rfl) ⟨2575283, by rfl⟩ : syracuseStep 3433711 = 5150567) B5150567
theorem B1525351 : Blo 1354996 1525351 := bstep (se 1 (by rfl) ⟨1144013, by rfl⟩ : syracuseStep 1525351 = 2288027) B2288027
theorem B1356447 : Blo 1354996 1356447 := bstep (se 1 (by rfl) ⟨1017335, by rfl⟩ : syracuseStep 1356447 = 2034671) B2034671
theorem B3052871 : Blo 1354996 3052871 := bstep (se 1 (by rfl) ⟨2289653, by rfl⟩ : syracuseStep 3052871 = 4579307) B4579307
theorem B46956239 : Blo 1354996 46956239 := bstep (se 1 (by rfl) ⟨35217179, by rfl⟩ : syracuseStep 46956239 = 70434359) B70434359
theorem B2033801 : Blo 1354996 2033801 := bstep (se 2 (by rfl) ⟨762675, by rfl⟩ : syracuseStep 2033801 = 1525351) B1525351
theorem B31304159 : Blo 1354996 31304159 := bstep (se 1 (by rfl) ⟨23478119, by rfl⟩ : syracuseStep 31304159 = 46956239) B46956239
theorem B2288999 : Blo 1354996 2288999 := bstep (se 1 (by rfl) ⟨1716749, by rfl⟩ : syracuseStep 2288999 = 3433499) B3433499
theorem B2035247 : Blo 1354996 2035247 := bstep (se 1 (by rfl) ⟨1526435, by rfl⟩ : syracuseStep 2035247 = 3052871) B3052871
theorem B4578281 : Blo 1354996 4578281 := bstep (se 2 (by rfl) ⟨1716855, by rfl⟩ : syracuseStep 4578281 = 3433711) B3433711
theorem B1525999 : Blo 1354996 1525999 := bstep (se 1 (by rfl) ⟨1144499, by rfl⟩ : syracuseStep 1525999 = 2288999) B2288999
theorem B1355867 : Blo 1354996 1355867 := bstep (se 1 (by rfl) ⟨1016900, by rfl⟩ : syracuseStep 1355867 = 2033801) B2033801
theorem B20869439 : Blo 1354996 20869439 := bstep (se 1 (by rfl) ⟨15652079, by rfl⟩ : syracuseStep 20869439 = 31304159) B31304159
theorem B3052187 : Blo 1354996 3052187 := bstep (se 1 (by rfl) ⟨2289140, by rfl⟩ : syracuseStep 3052187 = 4578281) B4578281
theorem B1356831 : Blo 1354996 1356831 := bstep (se 1 (by rfl) ⟨1017623, by rfl⟩ : syracuseStep 1356831 = 2035247) B2035247
theorem B2034665 : Blo 1354996 2034665 := bstep (se 2 (by rfl) ⟨762999, by rfl⟩ : syracuseStep 2034665 = 1525999) B1525999
theorem B2034791 : Blo 1354996 2034791 := bstep (se 1 (by rfl) ⟨1526093, by rfl⟩ : syracuseStep 2034791 = 3052187) B3052187
theorem B222607349 : Blo 1354996 222607349 := bstep (se 5 (by rfl) ⟨10434719, by rfl⟩ : syracuseStep 222607349 = 20869439) B20869439
theorem B1356443 : Blo 1354996 1356443 := bstep (se 1 (by rfl) ⟨1017332, by rfl⟩ : syracuseStep 1356443 = 2034665) B2034665
theorem B1356527 : Blo 1354996 1356527 := bstep (se 1 (by rfl) ⟨1017395, by rfl⟩ : syracuseStep 1356527 = 2034791) B2034791
theorem B148404899 : Blo 1354996 148404899 := bstep (se 1 (by rfl) ⟨111303674, by rfl⟩ : syracuseStep 148404899 = 222607349) B222607349
theorem B98936599 : Blo 1354996 98936599 := bstep (se 1 (by rfl) ⟨74202449, by rfl⟩ : syracuseStep 98936599 = 148404899) B148404899
theorem B131915465 : Blo 1354996 131915465 := bstep (se 2 (by rfl) ⟨49468299, by rfl⟩ : syracuseStep 131915465 = 98936599) B98936599
theorem B87943643 : Blo 1354996 87943643 := bstep (se 1 (by rfl) ⟨65957732, by rfl⟩ : syracuseStep 87943643 = 131915465) B131915465
theorem B58629095 : Blo 1354996 58629095 := bstep (se 1 (by rfl) ⟨43971821, by rfl⟩ : syracuseStep 58629095 = 87943643) B87943643
theorem B39086063 : Blo 1354996 39086063 := bstep (se 1 (by rfl) ⟨29314547, by rfl⟩ : syracuseStep 39086063 = 58629095) B58629095
theorem B26057375 : Blo 1354996 26057375 := bstep (se 1 (by rfl) ⟨19543031, by rfl⟩ : syracuseStep 26057375 = 39086063) B39086063
theorem B17371583 : Blo 1354996 17371583 := bstep (se 1 (by rfl) ⟨13028687, by rfl⟩ : syracuseStep 17371583 = 26057375) B26057375
theorem B11581055 : Blo 1354996 11581055 := bstep (se 1 (by rfl) ⟨8685791, by rfl⟩ : syracuseStep 11581055 = 17371583) B17371583
theorem B7720703 : Blo 1354996 7720703 := bstep (se 1 (by rfl) ⟨5790527, by rfl⟩ : syracuseStep 7720703 = 11581055) B11581055
theorem B5147135 : Blo 1354996 5147135 := bstep (se 1 (by rfl) ⟨3860351, by rfl⟩ : syracuseStep 5147135 = 7720703) B7720703
theorem B3431423 : Blo 1354996 3431423 := bstep (se 1 (by rfl) ⟨2573567, by rfl⟩ : syracuseStep 3431423 = 5147135) B5147135
theorem B2287615 : Blo 1354996 2287615 := bstep (se 1 (by rfl) ⟨1715711, by rfl⟩ : syracuseStep 2287615 = 3431423) B3431423
theorem B3050153 : Blo 1354996 3050153 := bstep (se 2 (by rfl) ⟨1143807, by rfl⟩ : syracuseStep 3050153 = 2287615) B2287615
theorem B2033435 : Blo 1354996 2033435 := bstep (se 1 (by rfl) ⟨1525076, by rfl⟩ : syracuseStep 2033435 = 3050153) B3050153
theorem B1355623 : Blo 1354996 1355623 := bstep (se 1 (by rfl) ⟨1016717, by rfl⟩ : syracuseStep 1355623 = 2033435) B2033435

theorem C0 (j : ℕ) (h1 : 338749 ≤ j) (h2 : j ≤ 339248) : Blo 1354996 (4 * j + 3) := by
  interval_cases j
  · exact B1354999
  · exact B1355003
  · exact B1355007
  · exact B1355011
  · exact B1355015
  · exact B1355019
  · exact B1355023
  · exact B1355027
  · exact B1355031
  · exact B1355035
  · exact B1355039
  · exact B1355043
  · exact B1355047
  · exact B1355051
  · exact B1355055
  · exact B1355059
  · exact B1355063
  · exact B1355067
  · exact B1355071
  · exact B1355075
  · exact B1355079
  · exact B1355083
  · exact B1355087
  · exact B1355091
  · exact B1355095
  · exact B1355099
  · exact B1355103
  · exact B1355107
  · exact B1355111
  · exact B1355115
  · exact B1355119
  · exact B1355123
  · exact B1355127
  · exact B1355131
  · exact B1355135
  · exact B1355139
  · exact B1355143
  · exact B1355147
  · exact B1355151
  · exact B1355155
  · exact B1355159
  · exact B1355163
  · exact B1355167
  · exact B1355171
  · exact B1355175
  · exact B1355179
  · exact B1355183
  · exact B1355187
  · exact B1355191
  · exact B1355195
  · exact B1355199
  · exact B1355203
  · exact B1355207
  · exact B1355211
  · exact B1355215
  · exact B1355219
  · exact B1355223
  · exact B1355227
  · exact B1355231
  · exact B1355235
  · exact B1355239
  · exact B1355243
  · exact B1355247
  · exact B1355251
  · exact B1355255
  · exact B1355259
  · exact B1355263
  · exact B1355267
  · exact B1355271
  · exact B1355275
  · exact B1355279
  · exact B1355283
  · exact B1355287
  · exact B1355291
  · exact B1355295
  · exact B1355299
  · exact B1355303
  · exact B1355307
  · exact B1355311
  · exact B1355315
  · exact B1355319
  · exact B1355323
  · exact B1355327
  · exact B1355331
  · exact B1355335
  · exact B1355339
  · exact B1355343
  · exact B1355347
  · exact B1355351
  · exact B1355355
  · exact B1355359
  · exact B1355363
  · exact B1355367
  · exact B1355371
  · exact B1355375
  · exact B1355379
  · exact B1355383
  · exact B1355387
  · exact B1355391
  · exact B1355395
  · exact B1355399
  · exact B1355403
  · exact B1355407
  · exact B1355411
  · exact B1355415
  · exact B1355419
  · exact B1355423
  · exact B1355427
  · exact B1355431
  · exact B1355435
  · exact B1355439
  · exact B1355443
  · exact B1355447
  · exact B1355451
  · exact B1355455
  · exact B1355459
  · exact B1355463
  · exact B1355467
  · exact B1355471
  · exact B1355475
  · exact B1355479
  · exact B1355483
  · exact B1355487
  · exact B1355491
  · exact B1355495
  · exact B1355499
  · exact B1355503
  · exact B1355507
  · exact B1355511
  · exact B1355515
  · exact B1355519
  · exact B1355523
  · exact B1355527
  · exact B1355531
  · exact B1355535
  · exact B1355539
  · exact B1355543
  · exact B1355547
  · exact B1355551
  · exact B1355555
  · exact B1355559
  · exact B1355563
  · exact B1355567
  · exact B1355571
  · exact B1355575
  · exact B1355579
  · exact B1355583
  · exact B1355587
  · exact B1355591
  · exact B1355595
  · exact B1355599
  · exact B1355603
  · exact B1355607
  · exact B1355611
  · exact B1355615
  · exact B1355619
  · exact B1355623
  · exact B1355627
  · exact B1355631
  · exact B1355635
  · exact B1355639
  · exact B1355643
  · exact B1355647
  · exact B1355651
  · exact B1355655
  · exact B1355659
  · exact B1355663
  · exact B1355667
  · exact B1355671
  · exact B1355675
  · exact B1355679
  · exact B1355683
  · exact B1355687
  · exact B1355691
  · exact B1355695
  · exact B1355699
  · exact B1355703
  · exact B1355707
  · exact B1355711
  · exact B1355715
  · exact B1355719
  · exact B1355723
  · exact B1355727
  · exact B1355731
  · exact B1355735
  · exact B1355739
  · exact B1355743
  · exact B1355747
  · exact B1355751
  · exact B1355755
  · exact B1355759
  · exact B1355763
  · exact B1355767
  · exact B1355771
  · exact B1355775
  · exact B1355779
  · exact B1355783
  · exact B1355787
  · exact B1355791
  · exact B1355795
  · exact B1355799
  · exact B1355803
  · exact B1355807
  · exact B1355811
  · exact B1355815
  · exact B1355819
  · exact B1355823
  · exact B1355827
  · exact B1355831
  · exact B1355835
  · exact B1355839
  · exact B1355843
  · exact B1355847
  · exact B1355851
  · exact B1355855
  · exact B1355859
  · exact B1355863
  · exact B1355867
  · exact B1355871
  · exact B1355875
  · exact B1355879
  · exact B1355883
  · exact B1355887
  · exact B1355891
  · exact B1355895
  · exact B1355899
  · exact B1355903
  · exact B1355907
  · exact B1355911
  · exact B1355915
  · exact B1355919
  · exact B1355923
  · exact B1355927
  · exact B1355931
  · exact B1355935
  · exact B1355939
  · exact B1355943
  · exact B1355947
  · exact B1355951
  · exact B1355955
  · exact B1355959
  · exact B1355963
  · exact B1355967
  · exact B1355971
  · exact B1355975
  · exact B1355979
  · exact B1355983
  · exact B1355987
  · exact B1355991
  · exact B1355995
  · exact B1355999
  · exact B1356003
  · exact B1356007
  · exact B1356011
  · exact B1356015
  · exact B1356019
  · exact B1356023
  · exact B1356027
  · exact B1356031
  · exact B1356035
  · exact B1356039
  · exact B1356043
  · exact B1356047
  · exact B1356051
  · exact B1356055
  · exact B1356059
  · exact B1356063
  · exact B1356067
  · exact B1356071
  · exact B1356075
  · exact B1356079
  · exact B1356083
  · exact B1356087
  · exact B1356091
  · exact B1356095
  · exact B1356099
  · exact B1356103
  · exact B1356107
  · exact B1356111
  · exact B1356115
  · exact B1356119
  · exact B1356123
  · exact B1356127
  · exact B1356131
  · exact B1356135
  · exact B1356139
  · exact B1356143
  · exact B1356147
  · exact B1356151
  · exact B1356155
  · exact B1356159
  · exact B1356163
  · exact B1356167
  · exact B1356171
  · exact B1356175
  · exact B1356179
  · exact B1356183
  · exact B1356187
  · exact B1356191
  · exact B1356195
  · exact B1356199
  · exact B1356203
  · exact B1356207
  · exact B1356211
  · exact B1356215
  · exact B1356219
  · exact B1356223
  · exact B1356227
  · exact B1356231
  · exact B1356235
  · exact B1356239
  · exact B1356243
  · exact B1356247
  · exact B1356251
  · exact B1356255
  · exact B1356259
  · exact B1356263
  · exact B1356267
  · exact B1356271
  · exact B1356275
  · exact B1356279
  · exact B1356283
  · exact B1356287
  · exact B1356291
  · exact B1356295
  · exact B1356299
  · exact B1356303
  · exact B1356307
  · exact B1356311
  · exact B1356315
  · exact B1356319
  · exact B1356323
  · exact B1356327
  · exact B1356331
  · exact B1356335
  · exact B1356339
  · exact B1356343
  · exact B1356347
  · exact B1356351
  · exact B1356355
  · exact B1356359
  · exact B1356363
  · exact B1356367
  · exact B1356371
  · exact B1356375
  · exact B1356379
  · exact B1356383
  · exact B1356387
  · exact B1356391
  · exact B1356395
  · exact B1356399
  · exact B1356403
  · exact B1356407
  · exact B1356411
  · exact B1356415
  · exact B1356419
  · exact B1356423
  · exact B1356427
  · exact B1356431
  · exact B1356435
  · exact B1356439
  · exact B1356443
  · exact B1356447
  · exact B1356451
  · exact B1356455
  · exact B1356459
  · exact B1356463
  · exact B1356467
  · exact B1356471
  · exact B1356475
  · exact B1356479
  · exact B1356483
  · exact B1356487
  · exact B1356491
  · exact B1356495
  · exact B1356499
  · exact B1356503
  · exact B1356507
  · exact B1356511
  · exact B1356515
  · exact B1356519
  · exact B1356523
  · exact B1356527
  · exact B1356531
  · exact B1356535
  · exact B1356539
  · exact B1356543
  · exact B1356547
  · exact B1356551
  · exact B1356555
  · exact B1356559
  · exact B1356563
  · exact B1356567
  · exact B1356571
  · exact B1356575
  · exact B1356579
  · exact B1356583
  · exact B1356587
  · exact B1356591
  · exact B1356595
  · exact B1356599
  · exact B1356603
  · exact B1356607
  · exact B1356611
  · exact B1356615
  · exact B1356619
  · exact B1356623
  · exact B1356627
  · exact B1356631
  · exact B1356635
  · exact B1356639
  · exact B1356643
  · exact B1356647
  · exact B1356651
  · exact B1356655
  · exact B1356659
  · exact B1356663
  · exact B1356667
  · exact B1356671
  · exact B1356675
  · exact B1356679
  · exact B1356683
  · exact B1356687
  · exact B1356691
  · exact B1356695
  · exact B1356699
  · exact B1356703
  · exact B1356707
  · exact B1356711
  · exact B1356715
  · exact B1356719
  · exact B1356723
  · exact B1356727
  · exact B1356731
  · exact B1356735
  · exact B1356739
  · exact B1356743
  · exact B1356747
  · exact B1356751
  · exact B1356755
  · exact B1356759
  · exact B1356763
  · exact B1356767
  · exact B1356771
  · exact B1356775
  · exact B1356779
  · exact B1356783
  · exact B1356787
  · exact B1356791
  · exact B1356795
  · exact B1356799
  · exact B1356803
  · exact B1356807
  · exact B1356811
  · exact B1356815
  · exact B1356819
  · exact B1356823
  · exact B1356827
  · exact B1356831
  · exact B1356835
  · exact B1356839
  · exact B1356843
  · exact B1356847
  · exact B1356851
  · exact B1356855
  · exact B1356859
  · exact B1356863
  · exact B1356867
  · exact B1356871
  · exact B1356875
  · exact B1356879
  · exact B1356883
  · exact B1356887
  · exact B1356891
  · exact B1356895
  · exact B1356899
  · exact B1356903
  · exact B1356907
  · exact B1356911
  · exact B1356915
  · exact B1356919
  · exact B1356923
  · exact B1356927
  · exact B1356931
  · exact B1356935
  · exact B1356939
  · exact B1356943
  · exact B1356947
  · exact B1356951
  · exact B1356955
  · exact B1356959
  · exact B1356963
  · exact B1356967
  · exact B1356971
  · exact B1356975
  · exact B1356979
  · exact B1356983
  · exact B1356987
  · exact B1356991
  · exact B1356995

theorem solution (m : ℕ) (hlo : 1354996 ≤ m) (hhi : m ≤ 1356996) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 338749 ≤ j := by omega
    have hj2 : j ≤ 339248 := by omega
    have hb : Blo 1354996 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
