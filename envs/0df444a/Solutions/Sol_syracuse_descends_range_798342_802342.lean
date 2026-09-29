-- Prove2me | solution 1 for syracuse_descends_range_798342_802342
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:37.215162+00:00
-- url     : https://prove2.me/submissions/81374701-708b-4959-9b22-716e9a0e1718

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


theorem B1802285 : Blo 798342 1802285 := bbase (se 3 (by rfl) ⟨337928, by rfl⟩ : syracuseStep 1802285 = 675857) (by norm_num)
theorem B1802357 : Blo 798342 1802357 := bbase (se 5 (by rfl) ⟨84485, by rfl⟩ : syracuseStep 1802357 = 168971) (by norm_num)
theorem B1802429 : Blo 798342 1802429 := bbase (se 3 (by rfl) ⟨337955, by rfl⟩ : syracuseStep 1802429 = 675911) (by norm_num)
theorem B1736893 : Blo 798342 1736893 := bbase (se 3 (by rfl) ⟨325667, by rfl⟩ : syracuseStep 1736893 = 651335) (by norm_num)
theorem B1736957 : Blo 798342 1736957 := bbase (se 3 (by rfl) ⟨325679, by rfl⟩ : syracuseStep 1736957 = 651359) (by norm_num)
theorem B1802501 : Blo 798342 1802501 := bbase (se 4 (by rfl) ⟨168984, by rfl⟩ : syracuseStep 1802501 = 337969) (by norm_num)
theorem B1802573 : Blo 798342 1802573 := bbase (se 3 (by rfl) ⟨337982, by rfl⟩ : syracuseStep 1802573 = 675965) (by norm_num)
theorem B1802645 : Blo 798342 1802645 := bbase (se 6 (by rfl) ⟨42249, by rfl⟩ : syracuseStep 1802645 = 84499) (by norm_num)
theorem B1999325 : Blo 798342 1999325 := bbase (se 3 (by rfl) ⟨374873, by rfl⟩ : syracuseStep 1999325 = 749747) (by norm_num)
theorem B1802717 : Blo 798342 1802717 := bbase (se 3 (by rfl) ⟨338009, by rfl⟩ : syracuseStep 1802717 = 676019) (by norm_num)
theorem B1802789 : Blo 798342 1802789 := bbase (se 4 (by rfl) ⟨169011, by rfl⟩ : syracuseStep 1802789 = 338023) (by norm_num)
theorem B1802861 : Blo 798342 1802861 := bbase (se 3 (by rfl) ⟨338036, by rfl⟩ : syracuseStep 1802861 = 676073) (by norm_num)
theorem B852653 : Blo 798342 852653 := bbase (se 3 (by rfl) ⟨159872, by rfl⟩ : syracuseStep 852653 = 319745) (by norm_num)
theorem B1802933 : Blo 798342 1802933 := bbase (se 5 (by rfl) ⟨84512, by rfl⟩ : syracuseStep 1802933 = 169025) (by norm_num)
theorem B852725 : Blo 798342 852725 := bbase (se 5 (by rfl) ⟨39971, by rfl⟩ : syracuseStep 852725 = 79943) (by norm_num)
theorem B1803005 : Blo 798342 1803005 := bbase (se 3 (by rfl) ⟨338063, by rfl⟩ : syracuseStep 1803005 = 676127) (by norm_num)
theorem B2196229 : Blo 798342 2196229 := bbase (se 4 (by rfl) ⟨205896, by rfl⟩ : syracuseStep 2196229 = 411793) (by norm_num)
theorem B1803077 : Blo 798342 1803077 := bbase (se 4 (by rfl) ⟨169038, by rfl⟩ : syracuseStep 1803077 = 338077) (by norm_num)
theorem B1540949 : Blo 798342 1540949 := bbase (se 9 (by rfl) ⟨4514, by rfl⟩ : syracuseStep 1540949 = 9029) (by norm_num)
theorem B1278845 : Blo 798342 1278845 := bbase (se 3 (by rfl) ⟨239783, by rfl⟩ : syracuseStep 1278845 = 479567) (by norm_num)
theorem B1803149 : Blo 798342 1803149 := bbase (se 3 (by rfl) ⟨338090, by rfl⟩ : syracuseStep 1803149 = 676181) (by norm_num)
theorem B852913 : Blo 798342 852913 := bbase (se 2 (by rfl) ⟨319842, by rfl⟩ : syracuseStep 852913 = 639685) (by norm_num)
theorem B11535317 : Blo 798342 11535317 := bbase (se 7 (by rfl) ⟨135179, by rfl⟩ : syracuseStep 11535317 = 270359) (by norm_num)
theorem B1803221 : Blo 798342 1803221 := bbase (se 7 (by rfl) ⟨21131, by rfl⟩ : syracuseStep 1803221 = 42263) (by norm_num)
theorem B1803293 : Blo 798342 1803293 := bbase (se 3 (by rfl) ⟨338117, by rfl⟩ : syracuseStep 1803293 = 676235) (by norm_num)
theorem B1279037 : Blo 798342 1279037 := bbase (se 3 (by rfl) ⟨239819, by rfl⟩ : syracuseStep 1279037 = 479639) (by norm_num)
theorem B1541197 : Blo 798342 1541197 := bbase (se 3 (by rfl) ⟨288974, by rfl⟩ : syracuseStep 1541197 = 577949) (by norm_num)
theorem B1803365 : Blo 798342 1803365 := bbase (se 4 (by rfl) ⟨169065, by rfl⟩ : syracuseStep 1803365 = 338131) (by norm_num)
theorem B853097 : Blo 798342 853097 := bbase (se 2 (by rfl) ⟨319911, by rfl⟩ : syracuseStep 853097 = 639823) (by norm_num)
theorem B6915221 : Blo 798342 6915221 := bbase (se 6 (by rfl) ⟨162075, by rfl⟩ : syracuseStep 6915221 = 324151) (by norm_num)
theorem B1803437 : Blo 798342 1803437 := bbase (se 3 (by rfl) ⟨338144, by rfl⟩ : syracuseStep 1803437 = 676289) (by norm_num)
theorem B1279165 : Blo 798342 1279165 := bbase (se 3 (by rfl) ⟨239843, by rfl⟩ : syracuseStep 1279165 = 479687) (by norm_num)
theorem B1443005 : Blo 798342 1443005 := bbase (se 3 (by rfl) ⟨270563, by rfl⟩ : syracuseStep 1443005 = 541127) (by norm_num)
theorem B1803509 : Blo 798342 1803509 := bbase (se 5 (by rfl) ⟨84539, by rfl⟩ : syracuseStep 1803509 = 169079) (by norm_num)
theorem B1803581 : Blo 798342 1803581 := bbase (se 3 (by rfl) ⟨338171, by rfl⟩ : syracuseStep 1803581 = 676343) (by norm_num)
theorem B1803653 : Blo 798342 1803653 := bbase (se 4 (by rfl) ⟨169092, by rfl⟩ : syracuseStep 1803653 = 338185) (by norm_num)
theorem B1803725 : Blo 798342 1803725 := bbase (se 3 (by rfl) ⟨338198, by rfl⟩ : syracuseStep 1803725 = 676397) (by norm_num)
theorem B1803797 : Blo 798342 1803797 := bbase (se 6 (by rfl) ⟨42276, by rfl⟩ : syracuseStep 1803797 = 84553) (by norm_num)
theorem B12977749 : Blo 798342 12977749 := bbase (se 8 (by rfl) ⟨76041, by rfl⟩ : syracuseStep 12977749 = 152083) (by norm_num)
theorem B1803869 : Blo 798342 1803869 := bbase (se 3 (by rfl) ⟨338225, by rfl⟩ : syracuseStep 1803869 = 676451) (by norm_num)
theorem B1803941 : Blo 798342 1803941 := bbase (se 4 (by rfl) ⟨169119, by rfl⟩ : syracuseStep 1803941 = 338239) (by norm_num)
theorem B15599317 : Blo 798342 15599317 := bbase (se 7 (by rfl) ⟨182804, by rfl⟩ : syracuseStep 15599317 = 365609) (by norm_num)
theorem B1804013 : Blo 798342 1804013 := bbase (se 3 (by rfl) ⟨338252, by rfl⟩ : syracuseStep 1804013 = 676505) (by norm_num)
theorem B1804085 : Blo 798342 1804085 := bbase (se 5 (by rfl) ⟨84566, by rfl⟩ : syracuseStep 1804085 = 169133) (by norm_num)
theorem B1279805 : Blo 798342 1279805 := bbase (se 3 (by rfl) ⟨239963, by rfl⟩ : syracuseStep 1279805 = 479927) (by norm_num)
theorem B2557765 : Blo 798342 2557765 := bbase (se 4 (by rfl) ⟨239790, by rfl⟩ : syracuseStep 2557765 = 479581) (by norm_num)
theorem B853849 : Blo 798342 853849 := bbase (se 2 (by rfl) ⟨320193, by rfl⟩ : syracuseStep 853849 = 640387) (by norm_num)
theorem B1705853 : Blo 798342 1705853 := bbase (se 3 (by rfl) ⟨319847, by rfl⟩ : syracuseStep 1705853 = 639695) (by norm_num)
theorem B1804157 : Blo 798342 1804157 := bbase (se 3 (by rfl) ⟨338279, by rfl⟩ : syracuseStep 1804157 = 676559) (by norm_num)
theorem B821125 : Blo 798342 821125 := bbase (se 4 (by rfl) ⟨76980, by rfl⟩ : syracuseStep 821125 = 153961) (by norm_num)
theorem B853921 : Blo 798342 853921 := bbase (se 2 (by rfl) ⟨320220, by rfl⟩ : syracuseStep 853921 = 640441) (by norm_num)
theorem B1804229 : Blo 798342 1804229 := bbase (se 4 (by rfl) ⟨169146, by rfl⟩ : syracuseStep 1804229 = 338293) (by norm_num)
theorem B1705997 : Blo 798342 1705997 := bbase (se 3 (by rfl) ⟨319874, by rfl⟩ : syracuseStep 1705997 = 639749) (by norm_num)
theorem B1804301 : Blo 798342 1804301 := bbase (se 3 (by rfl) ⟨338306, by rfl⟩ : syracuseStep 1804301 = 676613) (by norm_num)
theorem B854101 : Blo 798342 854101 := bbase (se 8 (by rfl) ⟨5004, by rfl⟩ : syracuseStep 854101 = 10009) (by norm_num)
theorem B1804373 : Blo 798342 1804373 := bbase (se 8 (by rfl) ⟨10572, by rfl⟩ : syracuseStep 1804373 = 21145) (by norm_num)
theorem B1804445 : Blo 798342 1804445 := bbase (se 3 (by rfl) ⟨338333, by rfl⟩ : syracuseStep 1804445 = 676667) (by norm_num)
theorem B1804517 : Blo 798342 1804517 := bbase (se 4 (by rfl) ⟨169173, by rfl⟩ : syracuseStep 1804517 = 338347) (by norm_num)
theorem B1280261 : Blo 798342 1280261 := bbase (se 4 (by rfl) ⟨120024, by rfl⟩ : syracuseStep 1280261 = 240049) (by norm_num)
theorem B1804589 : Blo 798342 1804589 := bbase (se 3 (by rfl) ⟨338360, by rfl⟩ : syracuseStep 1804589 = 676721) (by norm_num)
theorem B1804661 : Blo 798342 1804661 := bbase (se 5 (by rfl) ⟨84593, by rfl⟩ : syracuseStep 1804661 = 169187) (by norm_num)
theorem B1804733 : Blo 798342 1804733 := bbase (se 3 (by rfl) ⟨338387, by rfl⟩ : syracuseStep 1804733 = 676775) (by norm_num)
theorem B1280485 : Blo 798342 1280485 := bbase (se 4 (by rfl) ⟨120045, by rfl⟩ : syracuseStep 1280485 = 240091) (by norm_num)
theorem B1804805 : Blo 798342 1804805 := bbase (se 4 (by rfl) ⟨169200, by rfl⟩ : syracuseStep 1804805 = 338401) (by norm_num)
theorem B854545 : Blo 798342 854545 := bbase (se 2 (by rfl) ⟨320454, by rfl⟩ : syracuseStep 854545 = 640909) (by norm_num)
theorem B1280549 : Blo 798342 1280549 := bbase (se 4 (by rfl) ⟨120051, by rfl⟩ : syracuseStep 1280549 = 240103) (by norm_num)
theorem B2165285 : Blo 798342 2165285 := bbase (se 4 (by rfl) ⟨202995, by rfl⟩ : syracuseStep 2165285 = 405991) (by norm_num)
theorem B1804877 : Blo 798342 1804877 := bbase (se 3 (by rfl) ⟨338414, by rfl⟩ : syracuseStep 1804877 = 676829) (by norm_num)
theorem B7309909 : Blo 798342 7309909 := bbase (se 8 (by rfl) ⟨42831, by rfl⟩ : syracuseStep 7309909 = 85663) (by norm_num)
theorem B2165381 : Blo 798342 2165381 := bbase (se 4 (by rfl) ⟨203004, by rfl⟩ : syracuseStep 2165381 = 406009) (by norm_num)
theorem B854669 : Blo 798342 854669 := bbase (se 3 (by rfl) ⟨160250, by rfl⟩ : syracuseStep 854669 = 320501) (by norm_num)
theorem B1804949 : Blo 798342 1804949 := bbase (se 6 (by rfl) ⟨42303, by rfl⟩ : syracuseStep 1804949 = 84607) (by norm_num)
theorem B1280677 : Blo 798342 1280677 := bbase (se 4 (by rfl) ⟨120063, by rfl⟩ : syracuseStep 1280677 = 240127) (by norm_num)
theorem B1215157 : Blo 798342 1215157 := bbase (se 5 (by rfl) ⟨56960, by rfl⟩ : syracuseStep 1215157 = 113921) (by norm_num)
theorem B1805021 : Blo 798342 1805021 := bbase (se 3 (by rfl) ⟨338441, by rfl⟩ : syracuseStep 1805021 = 676883) (by norm_num)
theorem B1706741 : Blo 798342 1706741 := bbase (se 5 (by rfl) ⟨80003, by rfl⟩ : syracuseStep 1706741 = 160007) (by norm_num)
theorem B1805093 : Blo 798342 1805093 := bbase (se 4 (by rfl) ⟨169227, by rfl⟩ : syracuseStep 1805093 = 338455) (by norm_num)
theorem B1805165 : Blo 798342 1805165 := bbase (se 3 (by rfl) ⟨338468, by rfl⟩ : syracuseStep 1805165 = 676937) (by norm_num)
theorem B854921 : Blo 798342 854921 := bbase (se 2 (by rfl) ⟨320595, by rfl⟩ : syracuseStep 854921 = 641191) (by norm_num)
theorem B1805237 : Blo 798342 1805237 := bbase (se 5 (by rfl) ⟨84620, by rfl⟩ : syracuseStep 1805237 = 169241) (by norm_num)
theorem B3411173 : Blo 798342 3411173 := bbase (se 4 (by rfl) ⟨319797, by rfl⟩ : syracuseStep 3411173 = 639595) (by norm_num)
theorem B855365 : Blo 798342 855365 := bbase (se 4 (by rfl) ⟨80190, by rfl⟩ : syracuseStep 855365 = 160381) (by norm_num)
theorem B1707493 : Blo 798342 1707493 := bbase (se 4 (by rfl) ⟨160077, by rfl⟩ : syracuseStep 1707493 = 320155) (by norm_num)
theorem B2559509 : Blo 798342 2559509 := bbase (se 6 (by rfl) ⟨59988, by rfl⟩ : syracuseStep 2559509 = 119977) (by norm_num)
theorem B855613 : Blo 798342 855613 := bbase (se 3 (by rfl) ⟨160427, by rfl⟩ : syracuseStep 855613 = 320855) (by norm_num)
theorem B3247685 : Blo 798342 3247685 := bbase (se 4 (by rfl) ⟨304470, by rfl⟩ : syracuseStep 3247685 = 608941) (by norm_num)
theorem B1707637 : Blo 798342 1707637 := bbase (se 5 (by rfl) ⟨80045, by rfl⟩ : syracuseStep 1707637 = 160091) (by norm_num)
theorem B1347205 : Blo 798342 1347205 := bbase (se 4 (by rfl) ⟨126300, by rfl⟩ : syracuseStep 1347205 = 252601) (by norm_num)
theorem B2559701 : Blo 798342 2559701 := bbase (se 7 (by rfl) ⟨29996, by rfl⟩ : syracuseStep 2559701 = 59993) (by norm_num)
theorem B24678101 : Blo 798342 24678101 := bbase (se 7 (by rfl) ⟨289196, by rfl⟩ : syracuseStep 24678101 = 578393) (by norm_num)
theorem B1347293 : Blo 798342 1347293 := bbase (se 3 (by rfl) ⟨252617, by rfl⟩ : syracuseStep 1347293 = 505235) (by norm_num)
theorem B1347421 : Blo 798342 1347421 := bbase (se 3 (by rfl) ⟨252641, by rfl⟩ : syracuseStep 1347421 = 505283) (by norm_num)
theorem B1281901 : Blo 798342 1281901 := bbase (se 3 (by rfl) ⟨240356, by rfl⟩ : syracuseStep 1281901 = 480713) (by norm_num)
theorem B1347509 : Blo 798342 1347509 := bbase (se 5 (by rfl) ⟨63164, by rfl⟩ : syracuseStep 1347509 = 126329) (by norm_num)
theorem B1708013 : Blo 798342 1708013 := bbase (se 3 (by rfl) ⟨320252, by rfl⟩ : syracuseStep 1708013 = 640505) (by norm_num)
theorem B856057 : Blo 798342 856057 := bbase (se 2 (by rfl) ⟨321021, by rfl⟩ : syracuseStep 856057 = 642043) (by norm_num)
theorem B1347637 : Blo 798342 1347637 := bbase (se 5 (by rfl) ⟨63170, by rfl⟩ : syracuseStep 1347637 = 126341) (by norm_num)
theorem B856117 : Blo 798342 856117 := bbase (se 5 (by rfl) ⟨40130, by rfl⟩ : syracuseStep 856117 = 80261) (by norm_num)
theorem B1347725 : Blo 798342 1347725 := bbase (se 3 (by rfl) ⟨252698, by rfl⟩ : syracuseStep 1347725 = 505397) (by norm_num)
theorem B3412165 : Blo 798342 3412165 := bbase (se 4 (by rfl) ⟨319890, by rfl⟩ : syracuseStep 3412165 = 639781) (by norm_num)
theorem B1347853 : Blo 798342 1347853 := bbase (se 3 (by rfl) ⟨252722, by rfl⟩ : syracuseStep 1347853 = 505445) (by norm_num)
theorem B1708381 : Blo 798342 1708381 := bbase (se 3 (by rfl) ⟨320321, by rfl⟩ : syracuseStep 1708381 = 640643) (by norm_num)
theorem B1347941 : Blo 798342 1347941 := bbase (se 4 (by rfl) ⟨126369, by rfl⟩ : syracuseStep 1347941 = 252739) (by norm_num)
theorem B856433 : Blo 798342 856433 := bbase (se 2 (by rfl) ⟨321162, by rfl⟩ : syracuseStep 856433 = 642325) (by norm_num)
theorem B4690325 : Blo 798342 4690325 := bbase (se 6 (by rfl) ⟨109929, by rfl⟩ : syracuseStep 4690325 = 219859) (by norm_num)
theorem B2429365 : Blo 798342 2429365 := bbase (se 5 (by rfl) ⟨113876, by rfl⟩ : syracuseStep 2429365 = 227753) (by norm_num)
theorem B1348069 : Blo 798342 1348069 := bbase (se 4 (by rfl) ⟨126381, by rfl⟩ : syracuseStep 1348069 = 252763) (by norm_num)
theorem B1282573 : Blo 798342 1282573 := bbase (se 3 (by rfl) ⟨240482, by rfl⟩ : syracuseStep 1282573 = 480965) (by norm_num)
theorem B1348157 : Blo 798342 1348157 := bbase (se 3 (by rfl) ⟨252779, by rfl⟩ : syracuseStep 1348157 = 505559) (by norm_num)
theorem B1348285 : Blo 798342 1348285 := bbase (se 3 (by rfl) ⟨252803, by rfl⟩ : syracuseStep 1348285 = 505607) (by norm_num)
theorem B1348373 : Blo 798342 1348373 := bbase (se 6 (by rfl) ⟨31602, by rfl⟩ : syracuseStep 1348373 = 63205) (by norm_num)
theorem B1348501 : Blo 798342 1348501 := bbase (se 6 (by rfl) ⟨31605, by rfl⟩ : syracuseStep 1348501 = 63211) (by norm_num)
theorem B1348589 : Blo 798342 1348589 := bbase (se 3 (by rfl) ⟨252860, by rfl⟩ : syracuseStep 1348589 = 505721) (by norm_num)
theorem B1348717 : Blo 798342 1348717 := bbase (se 3 (by rfl) ⟨252884, by rfl⟩ : syracuseStep 1348717 = 505769) (by norm_num)
theorem B1348805 : Blo 798342 1348805 := bbase (se 4 (by rfl) ⟨126450, by rfl⟩ : syracuseStep 1348805 = 252901) (by norm_num)
theorem B922897 : Blo 798342 922897 := bbase (se 2 (by rfl) ⟨346086, by rfl⟩ : syracuseStep 922897 = 692173) (by norm_num)
theorem B1348933 : Blo 798342 1348933 := bbase (se 4 (by rfl) ⟨126462, by rfl⟩ : syracuseStep 1348933 = 252925) (by norm_num)
theorem B2168149 : Blo 798342 2168149 := bbase (se 14 (by rfl) ⟨198, by rfl⟩ : syracuseStep 2168149 = 397) (by norm_num)
theorem B1349021 : Blo 798342 1349021 := bbase (se 3 (by rfl) ⟨252941, by rfl⟩ : syracuseStep 1349021 = 505883) (by norm_num)
theorem B1283573 : Blo 798342 1283573 := bbase (se 5 (by rfl) ⟨60167, by rfl⟩ : syracuseStep 1283573 = 120335) (by norm_num)
theorem B1349149 : Blo 798342 1349149 := bbase (se 3 (by rfl) ⟨252965, by rfl⟩ : syracuseStep 1349149 = 505931) (by norm_num)
theorem B1218125 : Blo 798342 1218125 := bbase (se 3 (by rfl) ⟨228398, by rfl⟩ : syracuseStep 1218125 = 456797) (by norm_num)
theorem B1349237 : Blo 798342 1349237 := bbase (se 5 (by rfl) ⟨63245, by rfl⟩ : syracuseStep 1349237 = 126491) (by norm_num)
theorem B4560533 : Blo 798342 4560533 := bbase (se 6 (by rfl) ⟨106887, by rfl⟩ : syracuseStep 4560533 = 213775) (by norm_num)
theorem B1218221 : Blo 798342 1218221 := bbase (se 3 (by rfl) ⟨228416, by rfl⟩ : syracuseStep 1218221 = 456833) (by norm_num)
theorem B1349365 : Blo 798342 1349365 := bbase (se 5 (by rfl) ⟨63251, by rfl⟩ : syracuseStep 1349365 = 126503) (by norm_num)
theorem B1709885 : Blo 798342 1709885 := bbase (se 3 (by rfl) ⟨320603, by rfl⟩ : syracuseStep 1709885 = 641207) (by norm_num)
theorem B1349453 : Blo 798342 1349453 := bbase (se 3 (by rfl) ⟨253022, by rfl⟩ : syracuseStep 1349453 = 506045) (by norm_num)
theorem B1349581 : Blo 798342 1349581 := bbase (se 3 (by rfl) ⟨253046, by rfl⟩ : syracuseStep 1349581 = 506093) (by norm_num)
theorem B1710029 : Blo 798342 1710029 := bbase (se 3 (by rfl) ⟨320630, by rfl⟩ : syracuseStep 1710029 = 641261) (by norm_num)
theorem B2889701 : Blo 798342 2889701 := bbase (se 4 (by rfl) ⟨270909, by rfl⟩ : syracuseStep 2889701 = 541819) (by norm_num)
theorem B1349669 : Blo 798342 1349669 := bbase (se 4 (by rfl) ⟨126531, by rfl⟩ : syracuseStep 1349669 = 253063) (by norm_num)
theorem B2922533 : Blo 798342 2922533 := bbase (se 4 (by rfl) ⟨273987, by rfl⟩ : syracuseStep 2922533 = 547975) (by norm_num)
theorem B1349797 : Blo 798342 1349797 := bbase (se 4 (by rfl) ⟨126543, by rfl⟩ : syracuseStep 1349797 = 253087) (by norm_num)
theorem B1349885 : Blo 798342 1349885 := bbase (se 3 (by rfl) ⟨253103, by rfl⟩ : syracuseStep 1349885 = 506207) (by norm_num)
theorem B1710389 : Blo 798342 1710389 := bbase (se 5 (by rfl) ⟨80174, by rfl⟩ : syracuseStep 1710389 = 160349) (by norm_num)
theorem B1350013 : Blo 798342 1350013 := bbase (se 3 (by rfl) ⟨253127, by rfl⟩ : syracuseStep 1350013 = 506255) (by norm_num)
theorem B1350101 : Blo 798342 1350101 := bbase (se 7 (by rfl) ⟨15821, by rfl⟩ : syracuseStep 1350101 = 31643) (by norm_num)
theorem B7707125 : Blo 798342 7707125 := bbase (se 5 (by rfl) ⟨361271, by rfl⟩ : syracuseStep 7707125 = 722543) (by norm_num)
theorem B3840533 : Blo 798342 3840533 := bbase (se 6 (by rfl) ⟨90012, by rfl⟩ : syracuseStep 3840533 = 180025) (by norm_num)
theorem B1219141 : Blo 798342 1219141 := bbase (se 4 (by rfl) ⟨114294, by rfl⟩ : syracuseStep 1219141 = 228589) (by norm_num)
theorem B1350229 : Blo 798342 1350229 := bbase (se 8 (by rfl) ⟨7911, by rfl⟩ : syracuseStep 1350229 = 15823) (by norm_num)
theorem B1317541 : Blo 798342 1317541 := bbase (se 4 (by rfl) ⟨123519, by rfl⟩ : syracuseStep 1317541 = 247039) (by norm_num)
theorem B1350317 : Blo 798342 1350317 := bbase (se 3 (by rfl) ⟨253184, by rfl⟩ : syracuseStep 1350317 = 506369) (by norm_num)
theorem B1350445 : Blo 798342 1350445 := bbase (se 3 (by rfl) ⟨253208, by rfl⟩ : syracuseStep 1350445 = 506417) (by norm_num)
theorem B1645357 : Blo 798342 1645357 := bbase (se 3 (by rfl) ⟨308504, by rfl⟩ : syracuseStep 1645357 = 617009) (by norm_num)
theorem B4561717 : Blo 798342 4561717 := bbase (se 5 (by rfl) ⟨213830, by rfl⟩ : syracuseStep 4561717 = 427661) (by norm_num)
theorem B3119957 : Blo 798342 3119957 := bbase (se 9 (by rfl) ⟨9140, by rfl⟩ : syracuseStep 3119957 = 18281) (by norm_num)
theorem B1350533 : Blo 798342 1350533 := bbase (se 4 (by rfl) ⟨126612, by rfl⟩ : syracuseStep 1350533 = 253225) (by norm_num)
theorem B1285085 : Blo 798342 1285085 := bbase (se 3 (by rfl) ⟨240953, by rfl⟩ : syracuseStep 1285085 = 481907) (by norm_num)
theorem B1350661 : Blo 798342 1350661 := bbase (se 4 (by rfl) ⟨126624, by rfl⟩ : syracuseStep 1350661 = 253249) (by norm_num)
theorem B1219645 : Blo 798342 1219645 := bbase (se 3 (by rfl) ⟨228683, by rfl⟩ : syracuseStep 1219645 = 457367) (by norm_num)
theorem B1350749 : Blo 798342 1350749 := bbase (se 3 (by rfl) ⟨253265, by rfl⟩ : syracuseStep 1350749 = 506531) (by norm_num)
theorem B1711277 : Blo 798342 1711277 := bbase (se 3 (by rfl) ⟨320864, by rfl⟩ : syracuseStep 1711277 = 641729) (by norm_num)
theorem B1350877 : Blo 798342 1350877 := bbase (se 3 (by rfl) ⟨253289, by rfl⟩ : syracuseStep 1350877 = 506579) (by norm_num)
theorem B2563301 : Blo 798342 2563301 := bbase (se 4 (by rfl) ⟨240309, by rfl⟩ : syracuseStep 2563301 = 480619) (by norm_num)
theorem B2694437 : Blo 798342 2694437 := bbase (se 4 (by rfl) ⟨252603, by rfl⟩ : syracuseStep 2694437 = 505207) (by norm_num)
theorem B1350965 : Blo 798342 1350965 := bbase (se 5 (by rfl) ⟨63326, by rfl⟩ : syracuseStep 1350965 = 126653) (by norm_num)
theorem B1219925 : Blo 798342 1219925 := bbase (se 11 (by rfl) ⟨893, by rfl⟩ : syracuseStep 1219925 = 1787) (by norm_num)
theorem B6069653 : Blo 798342 6069653 := bbase (se 6 (by rfl) ⟨142257, by rfl⟩ : syracuseStep 6069653 = 284515) (by norm_num)
theorem B1711525 : Blo 798342 1711525 := bbase (se 4 (by rfl) ⟨160455, by rfl⟩ : syracuseStep 1711525 = 320911) (by norm_num)
theorem B1351093 : Blo 798342 1351093 := bbase (se 5 (by rfl) ⟨63332, by rfl⟩ : syracuseStep 1351093 = 126665) (by norm_num)
theorem B1351181 : Blo 798342 1351181 := bbase (se 3 (by rfl) ⟨253346, by rfl⟩ : syracuseStep 1351181 = 506693) (by norm_num)
theorem B1351309 : Blo 798342 1351309 := bbase (se 3 (by rfl) ⟨253370, by rfl⟩ : syracuseStep 1351309 = 506741) (by norm_num)
theorem B2694869 : Blo 798342 2694869 := bbase (se 7 (by rfl) ⟨31580, by rfl⟩ : syracuseStep 2694869 = 63161) (by norm_num)
theorem B1351397 : Blo 798342 1351397 := bbase (se 4 (by rfl) ⟨126693, by rfl⟩ : syracuseStep 1351397 = 253387) (by norm_num)
theorem B2629397 : Blo 798342 2629397 := bbase (se 6 (by rfl) ⟨61626, by rfl⟩ : syracuseStep 2629397 = 123253) (by norm_num)
theorem B1351525 : Blo 798342 1351525 := bbase (se 4 (by rfl) ⟨126705, by rfl⟩ : syracuseStep 1351525 = 253411) (by norm_num)
theorem B1712029 : Blo 798342 1712029 := bbase (se 3 (by rfl) ⟨321005, by rfl⟩ : syracuseStep 1712029 = 642011) (by norm_num)
theorem B1351613 : Blo 798342 1351613 := bbase (se 3 (by rfl) ⟨253427, by rfl⟩ : syracuseStep 1351613 = 506855) (by norm_num)
theorem B14622677 : Blo 798342 14622677 := bbase (se 7 (by rfl) ⟨171359, by rfl⟩ : syracuseStep 14622677 = 342719) (by norm_num)
theorem B11706389 : Blo 798342 11706389 := bbase (se 6 (by rfl) ⟨274368, by rfl⟩ : syracuseStep 11706389 = 548737) (by norm_num)
theorem B1351741 : Blo 798342 1351741 := bbase (se 3 (by rfl) ⟨253451, by rfl⟩ : syracuseStep 1351741 = 506903) (by norm_num)
theorem B2695301 : Blo 798342 2695301 := bbase (se 4 (by rfl) ⟨252684, by rfl⟩ : syracuseStep 2695301 = 505369) (by norm_num)
theorem B1351829 : Blo 798342 1351829 := bbase (se 6 (by rfl) ⟨31683, by rfl⟩ : syracuseStep 1351829 = 63367) (by norm_num)
theorem B6496469 : Blo 798342 6496469 := bbase (se 7 (by rfl) ⟨76130, by rfl⟩ : syracuseStep 6496469 = 152261) (by norm_num)
theorem B1515773 : Blo 798342 1515773 := bbase (se 3 (by rfl) ⟨284207, by rfl⟩ : syracuseStep 1515773 = 568415) (by norm_num)
theorem B1351957 : Blo 798342 1351957 := bbase (se 6 (by rfl) ⟨31686, by rfl⟩ : syracuseStep 1351957 = 63373) (by norm_num)
theorem B1352045 : Blo 798342 1352045 := bbase (se 3 (by rfl) ⟨253508, by rfl⟩ : syracuseStep 1352045 = 507017) (by norm_num)
theorem B1515925 : Blo 798342 1515925 := bbase (se 6 (by rfl) ⟨35529, by rfl⟩ : syracuseStep 1515925 = 71059) (by norm_num)
theorem B1352173 : Blo 798342 1352173 := bbase (se 3 (by rfl) ⟨253532, by rfl⟩ : syracuseStep 1352173 = 507065) (by norm_num)
theorem B2695733 : Blo 798342 2695733 := bbase (se 5 (by rfl) ⟨126362, by rfl⟩ : syracuseStep 2695733 = 252725) (by norm_num)
theorem B1352261 : Blo 798342 1352261 := bbase (se 4 (by rfl) ⟨126774, by rfl⟩ : syracuseStep 1352261 = 253549) (by norm_num)
theorem B6824533 : Blo 798342 6824533 := bbase (se 8 (by rfl) ⟨39987, by rfl⟩ : syracuseStep 6824533 = 79975) (by norm_num)
theorem B1516229 : Blo 798342 1516229 := bbase (se 4 (by rfl) ⟨142146, by rfl⟩ : syracuseStep 1516229 = 284293) (by norm_num)
theorem B1352389 : Blo 798342 1352389 := bbase (se 4 (by rfl) ⟨126786, by rfl⟩ : syracuseStep 1352389 = 253573) (by norm_num)
theorem B4563701 : Blo 798342 4563701 := bbase (se 5 (by rfl) ⟨213923, by rfl⟩ : syracuseStep 4563701 = 427847) (by norm_num)
theorem B1712917 : Blo 798342 1712917 := bbase (se 6 (by rfl) ⟨40146, by rfl⟩ : syracuseStep 1712917 = 80293) (by norm_num)
theorem B1352477 : Blo 798342 1352477 := bbase (se 3 (by rfl) ⟨253589, by rfl⟩ : syracuseStep 1352477 = 507179) (by norm_num)
theorem B1352605 : Blo 798342 1352605 := bbase (se 3 (by rfl) ⟨253613, by rfl⟩ : syracuseStep 1352605 = 507227) (by norm_num)
theorem B2696165 : Blo 798342 2696165 := bbase (se 4 (by rfl) ⟨252765, by rfl⟩ : syracuseStep 2696165 = 505531) (by norm_num)
theorem B1352693 : Blo 798342 1352693 := bbase (se 5 (by rfl) ⟨63407, by rfl⟩ : syracuseStep 1352693 = 126815) (by norm_num)
theorem B3417173 : Blo 798342 3417173 := bbase (se 8 (by rfl) ⟨20022, by rfl⟩ : syracuseStep 3417173 = 40045) (by norm_num)
theorem B959585 : Blo 798342 959585 := bbase (se 2 (by rfl) ⟨359844, by rfl⟩ : syracuseStep 959585 = 719689) (by norm_num)
theorem B1352821 : Blo 798342 1352821 := bbase (se 5 (by rfl) ⟨63413, by rfl⟩ : syracuseStep 1352821 = 126827) (by norm_num)
theorem B4334741 : Blo 798342 4334741 := bbase (se 6 (by rfl) ⟨101595, by rfl⟩ : syracuseStep 4334741 = 203191) (by norm_num)
theorem B3515557 : Blo 798342 3515557 := bbase (se 4 (by rfl) ⟨329583, by rfl⟩ : syracuseStep 3515557 = 659167) (by norm_num)
theorem B1352909 : Blo 798342 1352909 := bbase (se 3 (by rfl) ⟨253670, by rfl⟩ : syracuseStep 1352909 = 507341) (by norm_num)
theorem B3646709 : Blo 798342 3646709 := bbase (se 5 (by rfl) ⟨170939, by rfl⟩ : syracuseStep 3646709 = 341879) (by norm_num)
theorem B1713413 : Blo 798342 1713413 := bbase (se 4 (by rfl) ⟨160632, by rfl⟩ : syracuseStep 1713413 = 321265) (by norm_num)
theorem B1025309 : Blo 798342 1025309 := bbase (se 3 (by rfl) ⟨192245, by rfl⟩ : syracuseStep 1025309 = 384491) (by norm_num)
theorem B959797 : Blo 798342 959797 := bbase (se 5 (by rfl) ⟨44990, by rfl⟩ : syracuseStep 959797 = 89981) (by norm_num)
theorem B1353037 : Blo 798342 1353037 := bbase (se 3 (by rfl) ⟨253694, by rfl⟩ : syracuseStep 1353037 = 507389) (by norm_num)
theorem B3417461 : Blo 798342 3417461 := bbase (se 5 (by rfl) ⟨160193, by rfl⟩ : syracuseStep 3417461 = 320387) (by norm_num)
theorem B2696597 : Blo 798342 2696597 := bbase (se 6 (by rfl) ⟨63201, by rfl⟩ : syracuseStep 2696597 = 126403) (by norm_num)
theorem B1353125 : Blo 798342 1353125 := bbase (se 4 (by rfl) ⟨126855, by rfl⟩ : syracuseStep 1353125 = 253711) (by norm_num)
theorem B1516981 : Blo 798342 1516981 := bbase (se 5 (by rfl) ⟨71108, by rfl⟩ : syracuseStep 1516981 = 142217) (by norm_num)
theorem B2565557 : Blo 798342 2565557 := bbase (se 5 (by rfl) ⟨120260, by rfl⟩ : syracuseStep 2565557 = 240521) (by norm_num)
theorem B959941 : Blo 798342 959941 := bbase (se 4 (by rfl) ⟨89994, by rfl⟩ : syracuseStep 959941 = 179989) (by norm_num)
theorem B1353253 : Blo 798342 1353253 := bbase (se 4 (by rfl) ⟨126867, by rfl⟩ : syracuseStep 1353253 = 253735) (by norm_num)
theorem B2565685 : Blo 798342 2565685 := bbase (se 5 (by rfl) ⟨120266, by rfl⟩ : syracuseStep 2565685 = 240533) (by norm_num)
theorem B1517125 : Blo 798342 1517125 := bbase (se 4 (by rfl) ⟨142230, by rfl⟩ : syracuseStep 1517125 = 284461) (by norm_num)
theorem B1353341 : Blo 798342 1353341 := bbase (se 3 (by rfl) ⟨253751, by rfl⟩ : syracuseStep 1353341 = 507503) (by norm_num)
theorem B1517285 : Blo 798342 1517285 := bbase (se 4 (by rfl) ⟨142245, by rfl⟩ : syracuseStep 1517285 = 284491) (by norm_num)
theorem B1353469 : Blo 798342 1353469 := bbase (se 3 (by rfl) ⟨253775, by rfl⟩ : syracuseStep 1353469 = 507551) (by norm_num)
theorem B2697029 : Blo 798342 2697029 := bbase (se 4 (by rfl) ⟨252846, by rfl⟩ : syracuseStep 2697029 = 505693) (by norm_num)
theorem B1353557 : Blo 798342 1353557 := bbase (se 9 (by rfl) ⟨3965, by rfl⟩ : syracuseStep 1353557 = 7931) (by norm_num)
theorem B1517429 : Blo 798342 1517429 := bbase (se 5 (by rfl) ⟨71129, by rfl⟩ : syracuseStep 1517429 = 142259) (by norm_num)
theorem B1353685 : Blo 798342 1353685 := bbase (se 7 (by rfl) ⟨15863, by rfl⟩ : syracuseStep 1353685 = 31727) (by norm_num)
theorem B1353773 : Blo 798342 1353773 := bbase (se 3 (by rfl) ⟨253832, by rfl⟩ : syracuseStep 1353773 = 507665) (by norm_num)
theorem B3418213 : Blo 798342 3418213 := bbase (se 4 (by rfl) ⟨320457, by rfl⟩ : syracuseStep 3418213 = 640915) (by norm_num)
theorem B1517717 : Blo 798342 1517717 := bbase (se 6 (by rfl) ⟨35571, by rfl⟩ : syracuseStep 1517717 = 71143) (by norm_num)
theorem B1353901 : Blo 798342 1353901 := bbase (se 3 (by rfl) ⟨253856, by rfl⟩ : syracuseStep 1353901 = 507713) (by norm_num)
theorem B2697461 : Blo 798342 2697461 := bbase (se 5 (by rfl) ⟨126443, by rfl⟩ : syracuseStep 2697461 = 252887) (by norm_num)
theorem B1517869 : Blo 798342 1517869 := bbase (se 3 (by rfl) ⟨284600, by rfl⟩ : syracuseStep 1517869 = 569201) (by norm_num)
theorem B6826517 : Blo 798342 6826517 := bbase (se 6 (by rfl) ⟨159996, by rfl⟩ : syracuseStep 6826517 = 319993) (by norm_num)
theorem B2599445 : Blo 798342 2599445 := bbase (se 6 (by rfl) ⟨60924, by rfl⟩ : syracuseStep 2599445 = 121849) (by norm_num)
theorem B4106821 : Blo 798342 4106821 := bbase (se 4 (by rfl) ⟨385014, by rfl⟩ : syracuseStep 4106821 = 770029) (by norm_num)
theorem B4336213 : Blo 798342 4336213 := bbase (se 8 (by rfl) ⟨25407, by rfl⟩ : syracuseStep 4336213 = 50815) (by norm_num)
theorem B1518173 : Blo 798342 1518173 := bbase (se 3 (by rfl) ⟨284657, by rfl⟩ : syracuseStep 1518173 = 569315) (by norm_num)
theorem B2697893 : Blo 798342 2697893 := bbase (se 4 (by rfl) ⟨252927, by rfl⟩ : syracuseStep 2697893 = 505855) (by norm_num)
theorem B3844837 : Blo 798342 3844837 := bbase (se 4 (by rfl) ⟨360453, by rfl⟩ : syracuseStep 3844837 = 720907) (by norm_num)
theorem B3418949 : Blo 798342 3418949 := bbase (se 4 (by rfl) ⟨320526, by rfl⟩ : syracuseStep 3418949 = 641053) (by norm_num)
theorem B4565909 : Blo 798342 4565909 := bbase (se 6 (by rfl) ⟨107013, by rfl⟩ : syracuseStep 4565909 = 214027) (by norm_num)
theorem B961517 : Blo 798342 961517 := bbase (se 3 (by rfl) ⟨180284, by rfl⟩ : syracuseStep 961517 = 360569) (by norm_num)
theorem B2698325 : Blo 798342 2698325 := bbase (se 8 (by rfl) ⟨15810, by rfl⟩ : syracuseStep 2698325 = 31621) (by norm_num)
theorem B1846493 : Blo 798342 1846493 := bbase (se 3 (by rfl) ⟨346217, by rfl⟩ : syracuseStep 1846493 = 692435) (by norm_num)
theorem B961853 : Blo 798342 961853 := bbase (se 3 (by rfl) ⟨180347, by rfl⟩ : syracuseStep 961853 = 360695) (by norm_num)
theorem B1518925 : Blo 798342 1518925 := bbase (se 3 (by rfl) ⟨284798, by rfl⟩ : syracuseStep 1518925 = 569597) (by norm_num)
theorem B961969 : Blo 798342 961969 := bbase (se 2 (by rfl) ⟨360738, by rfl⟩ : syracuseStep 961969 = 721477) (by norm_num)
theorem B1519069 : Blo 798342 1519069 := bbase (se 3 (by rfl) ⟨284825, by rfl⟩ : syracuseStep 1519069 = 569651) (by norm_num)
theorem B962041 : Blo 798342 962041 := bbase (se 2 (by rfl) ⟨360765, by rfl⟩ : syracuseStep 962041 = 721531) (by norm_num)
theorem B2698757 : Blo 798342 2698757 := bbase (se 4 (by rfl) ⟨253008, by rfl⟩ : syracuseStep 2698757 = 506017) (by norm_num)
theorem B962065 : Blo 798342 962065 := bbase (se 2 (by rfl) ⟨360774, by rfl⟩ : syracuseStep 962065 = 721549) (by norm_num)
theorem B1519229 : Blo 798342 1519229 := bbase (se 3 (by rfl) ⟨284855, by rfl⟩ : syracuseStep 1519229 = 569711) (by norm_num)
theorem B962209 : Blo 798342 962209 := bbase (se 2 (by rfl) ⟨360828, by rfl⟩ : syracuseStep 962209 = 721657) (by norm_num)
theorem B1519373 : Blo 798342 1519373 := bbase (se 3 (by rfl) ⟨284882, by rfl⟩ : syracuseStep 1519373 = 569765) (by norm_num)
theorem B1945397 : Blo 798342 1945397 := bbase (se 5 (by rfl) ⟨91190, by rfl⟩ : syracuseStep 1945397 = 182381) (by norm_num)
theorem B2699189 : Blo 798342 2699189 := bbase (se 5 (by rfl) ⟨126524, by rfl⟩ : syracuseStep 2699189 = 253049) (by norm_num)
theorem B4042709 : Blo 798342 4042709 := bbase (se 7 (by rfl) ⟨47375, by rfl⟩ : syracuseStep 4042709 = 94751) (by norm_num)
theorem B1028101 : Blo 798342 1028101 := bbase (se 4 (by rfl) ⟨96384, by rfl⟩ : syracuseStep 1028101 = 192769) (by norm_num)
theorem B1519661 : Blo 798342 1519661 := bbase (se 3 (by rfl) ⟨284936, by rfl⟩ : syracuseStep 1519661 = 569873) (by norm_num)
theorem B18493525 : Blo 798342 18493525 := bbase (se 8 (by rfl) ⟨108360, by rfl⟩ : syracuseStep 18493525 = 216721) (by norm_num)
theorem B4108421 : Blo 798342 4108421 := bbase (se 4 (by rfl) ⟨385164, by rfl⟩ : syracuseStep 4108421 = 770329) (by norm_num)
theorem B1519813 : Blo 798342 1519813 := bbase (se 4 (by rfl) ⟨142482, by rfl⟩ : syracuseStep 1519813 = 284965) (by norm_num)
theorem B2699621 : Blo 798342 2699621 := bbase (se 4 (by rfl) ⟨253089, by rfl⟩ : syracuseStep 2699621 = 506179) (by norm_num)
theorem B2568581 : Blo 798342 2568581 := bbase (se 4 (by rfl) ⟨240804, by rfl⟩ : syracuseStep 2568581 = 481609) (by norm_num)
theorem B864689 : Blo 798342 864689 := bbase (se 2 (by rfl) ⟨324258, by rfl⟩ : syracuseStep 864689 = 648517) (by norm_num)
theorem B7287221 : Blo 798342 7287221 := bbase (se 5 (by rfl) ⟨341588, by rfl⟩ : syracuseStep 7287221 = 683177) (by norm_num)
theorem B1520117 : Blo 798342 1520117 := bbase (se 5 (by rfl) ⟨71255, by rfl⟩ : syracuseStep 1520117 = 142511) (by norm_num)
theorem B3650069 : Blo 798342 3650069 := bbase (se 6 (by rfl) ⟨85548, by rfl⟩ : syracuseStep 3650069 = 171097) (by norm_num)
theorem B864841 : Blo 798342 864841 := bbase (se 2 (by rfl) ⟨324315, by rfl⟩ : syracuseStep 864841 = 648631) (by norm_num)
theorem B2273957 : Blo 798342 2273957 := bbase (se 4 (by rfl) ⟨213183, by rfl⟩ : syracuseStep 2273957 = 426367) (by norm_num)
theorem B2700053 : Blo 798342 2700053 := bbase (se 6 (by rfl) ⟨63282, by rfl⟩ : syracuseStep 2700053 = 126565) (by norm_num)
theorem B1094437 : Blo 798342 1094437 := bbase (se 4 (by rfl) ⟨102603, by rfl⟩ : syracuseStep 1094437 = 205207) (by norm_num)
theorem B963425 : Blo 798342 963425 := bbase (se 2 (by rfl) ⟨361284, by rfl⟩ : syracuseStep 963425 = 722569) (by norm_num)
theorem B2274389 : Blo 798342 2274389 := bbase (se 8 (by rfl) ⟨13326, by rfl⟩ : syracuseStep 2274389 = 26653) (by norm_num)
theorem B898141 : Blo 798342 898141 := bbase (se 3 (by rfl) ⟨168401, by rfl⟩ : syracuseStep 898141 = 336803) (by norm_num)
theorem B898177 : Blo 798342 898177 := bbase (se 2 (by rfl) ⟨336816, by rfl⟩ : syracuseStep 898177 = 673633) (by norm_num)
theorem B963733 : Blo 798342 963733 := bbase (se 6 (by rfl) ⟨22587, by rfl⟩ : syracuseStep 963733 = 45175) (by norm_num)
theorem B898213 : Blo 798342 898213 := bbase (se 4 (by rfl) ⟨84207, by rfl⟩ : syracuseStep 898213 = 168415) (by norm_num)
theorem B2700485 : Blo 798342 2700485 := bbase (se 4 (by rfl) ⟨253170, by rfl⟩ : syracuseStep 2700485 = 506341) (by norm_num)
theorem B898249 : Blo 798342 898249 := bbase (se 2 (by rfl) ⟨336843, by rfl⟩ : syracuseStep 898249 = 673687) (by norm_num)
theorem B4044005 : Blo 798342 4044005 := bbase (se 4 (by rfl) ⟨379125, by rfl⟩ : syracuseStep 4044005 = 758251) (by norm_num)
theorem B1520869 : Blo 798342 1520869 := bbase (se 4 (by rfl) ⟨142581, by rfl⟩ : syracuseStep 1520869 = 285163) (by norm_num)
theorem B898285 : Blo 798342 898285 := bbase (se 3 (by rfl) ⟨168428, by rfl⟩ : syracuseStep 898285 = 336857) (by norm_num)
theorem B963833 : Blo 798342 963833 := bbase (se 2 (by rfl) ⟨361437, by rfl⟩ : syracuseStep 963833 = 722875) (by norm_num)
theorem B898321 : Blo 798342 898321 := bbase (se 2 (by rfl) ⟨336870, by rfl⟩ : syracuseStep 898321 = 673741) (by norm_num)
theorem B898357 : Blo 798342 898357 := bbase (se 5 (by rfl) ⟨42110, by rfl⟩ : syracuseStep 898357 = 84221) (by norm_num)
theorem B898393 : Blo 798342 898393 := bbase (se 2 (by rfl) ⟨336897, by rfl⟩ : syracuseStep 898393 = 673795) (by norm_num)
theorem B1619293 : Blo 798342 1619293 := bbase (se 3 (by rfl) ⟨303617, by rfl⟩ : syracuseStep 1619293 = 607235) (by norm_num)
theorem B1521013 : Blo 798342 1521013 := bbase (se 5 (by rfl) ⟨71297, by rfl⟩ : syracuseStep 1521013 = 142595) (by norm_num)
theorem B898429 : Blo 798342 898429 := bbase (se 3 (by rfl) ⟨168455, by rfl⟩ : syracuseStep 898429 = 336911) (by norm_num)
theorem B898465 : Blo 798342 898465 := bbase (se 2 (by rfl) ⟨336924, by rfl⟩ : syracuseStep 898465 = 673849) (by norm_num)
theorem B832961 : Blo 798342 832961 := bbase (se 2 (by rfl) ⟨312360, by rfl⟩ : syracuseStep 832961 = 624721) (by norm_num)
theorem B898501 : Blo 798342 898501 := bbase (se 4 (by rfl) ⟨84234, by rfl⟩ : syracuseStep 898501 = 168469) (by norm_num)
theorem B898537 : Blo 798342 898537 := bbase (se 2 (by rfl) ⟨336951, by rfl⟩ : syracuseStep 898537 = 673903) (by norm_num)
theorem B898573 : Blo 798342 898573 := bbase (se 3 (by rfl) ⟨168482, by rfl⟩ : syracuseStep 898573 = 336965) (by norm_num)
theorem B1521173 : Blo 798342 1521173 := bbase (se 6 (by rfl) ⟨35652, by rfl⟩ : syracuseStep 1521173 = 71305) (by norm_num)
theorem B898609 : Blo 798342 898609 := bbase (se 2 (by rfl) ⟨336978, by rfl⟩ : syracuseStep 898609 = 673957) (by norm_num)
theorem B898645 : Blo 798342 898645 := bbase (se 8 (by rfl) ⟨5265, by rfl⟩ : syracuseStep 898645 = 10531) (by norm_num)
theorem B2700917 : Blo 798342 2700917 := bbase (se 5 (by rfl) ⟨126605, by rfl⟩ : syracuseStep 2700917 = 253211) (by norm_num)
theorem B898681 : Blo 798342 898681 := bbase (se 2 (by rfl) ⟨337005, by rfl⟩ : syracuseStep 898681 = 674011) (by norm_num)
theorem B5125781 : Blo 798342 5125781 := bbase (se 6 (by rfl) ⟨120135, by rfl⟩ : syracuseStep 5125781 = 240271) (by norm_num)
theorem B898717 : Blo 798342 898717 := bbase (se 3 (by rfl) ⟨168509, by rfl⟩ : syracuseStep 898717 = 337019) (by norm_num)
theorem B1521317 : Blo 798342 1521317 := bbase (se 4 (by rfl) ⟨142623, by rfl⟩ : syracuseStep 1521317 = 285247) (by norm_num)
theorem B898753 : Blo 798342 898753 := bbase (se 2 (by rfl) ⟨337032, by rfl⟩ : syracuseStep 898753 = 674065) (by norm_num)
theorem B898789 : Blo 798342 898789 := bbase (se 4 (by rfl) ⟨84261, by rfl⟩ : syracuseStep 898789 = 168523) (by norm_num)
theorem B898825 : Blo 798342 898825 := bbase (se 2 (by rfl) ⟨337059, by rfl⟩ : syracuseStep 898825 = 674119) (by norm_num)
theorem B898861 : Blo 798342 898861 := bbase (se 3 (by rfl) ⟨168536, by rfl⟩ : syracuseStep 898861 = 337073) (by norm_num)
theorem B2275141 : Blo 798342 2275141 := bbase (se 4 (by rfl) ⟨213294, by rfl⟩ : syracuseStep 2275141 = 426589) (by norm_num)
theorem B898897 : Blo 798342 898897 := bbase (se 2 (by rfl) ⟨337086, by rfl⟩ : syracuseStep 898897 = 674173) (by norm_num)
theorem B898933 : Blo 798342 898933 := bbase (se 5 (by rfl) ⟨42137, by rfl⟩ : syracuseStep 898933 = 84275) (by norm_num)
theorem B898969 : Blo 798342 898969 := bbase (se 2 (by rfl) ⟨337113, by rfl⟩ : syracuseStep 898969 = 674227) (by norm_num)
theorem B899005 : Blo 798342 899005 := bbase (se 3 (by rfl) ⟨168563, by rfl⟩ : syracuseStep 899005 = 337127) (by norm_num)
theorem B1521605 : Blo 798342 1521605 := bbase (se 4 (by rfl) ⟨142650, by rfl⟩ : syracuseStep 1521605 = 285301) (by norm_num)
theorem B899041 : Blo 798342 899041 := bbase (se 2 (by rfl) ⟨337140, by rfl⟩ : syracuseStep 899041 = 674281) (by norm_num)
theorem B899077 : Blo 798342 899077 := bbase (se 4 (by rfl) ⟨84288, by rfl⟩ : syracuseStep 899077 = 168577) (by norm_num)
theorem B2701349 : Blo 798342 2701349 := bbase (se 4 (by rfl) ⟨253251, by rfl⟩ : syracuseStep 2701349 = 506503) (by norm_num)
theorem B3422245 : Blo 798342 3422245 := bbase (se 4 (by rfl) ⟨320835, by rfl⟩ : syracuseStep 3422245 = 641671) (by norm_num)
theorem B899113 : Blo 798342 899113 := bbase (se 2 (by rfl) ⟨337167, by rfl⟩ : syracuseStep 899113 = 674335) (by norm_num)
theorem B899149 : Blo 798342 899149 := bbase (se 3 (by rfl) ⟨168590, by rfl⟩ : syracuseStep 899149 = 337181) (by norm_num)
theorem B1521757 : Blo 798342 1521757 := bbase (se 3 (by rfl) ⟨285329, by rfl⟩ : syracuseStep 1521757 = 570659) (by norm_num)
theorem B899185 : Blo 798342 899185 := bbase (se 2 (by rfl) ⟨337194, by rfl⟩ : syracuseStep 899185 = 674389) (by norm_num)
theorem B899221 : Blo 798342 899221 := bbase (se 6 (by rfl) ⟨21075, by rfl⟩ : syracuseStep 899221 = 42151) (by norm_num)
theorem B899257 : Blo 798342 899257 := bbase (se 2 (by rfl) ⟨337221, by rfl⟩ : syracuseStep 899257 = 674443) (by norm_num)
theorem B899293 : Blo 798342 899293 := bbase (se 3 (by rfl) ⟨168617, by rfl⟩ : syracuseStep 899293 = 337235) (by norm_num)
theorem B899329 : Blo 798342 899329 := bbase (se 2 (by rfl) ⟨337248, by rfl⟩ : syracuseStep 899329 = 674497) (by norm_num)
theorem B899365 : Blo 798342 899365 := bbase (se 4 (by rfl) ⟨84315, by rfl⟩ : syracuseStep 899365 = 168631) (by norm_num)
theorem B899401 : Blo 798342 899401 := bbase (se 2 (by rfl) ⟨337275, by rfl⟩ : syracuseStep 899401 = 674551) (by norm_num)
theorem B41564501 : Blo 798342 41564501 := bbase (se 10 (by rfl) ⟨60885, by rfl⟩ : syracuseStep 41564501 = 121771) (by norm_num)
theorem B899437 : Blo 798342 899437 := bbase (se 3 (by rfl) ⟨168644, by rfl⟩ : syracuseStep 899437 = 337289) (by norm_num)
theorem B2439557 : Blo 798342 2439557 := bbase (se 4 (by rfl) ⟨228708, by rfl⟩ : syracuseStep 2439557 = 457417) (by norm_num)
theorem B1948045 : Blo 798342 1948045 := bbase (se 3 (by rfl) ⟨365258, by rfl⟩ : syracuseStep 1948045 = 730517) (by norm_num)
theorem B1522061 : Blo 798342 1522061 := bbase (se 3 (by rfl) ⟨285386, by rfl⟩ : syracuseStep 1522061 = 570773) (by norm_num)
theorem B899473 : Blo 798342 899473 := bbase (se 2 (by rfl) ⟨337302, by rfl⟩ : syracuseStep 899473 = 674605) (by norm_num)
theorem B899509 : Blo 798342 899509 := bbase (se 5 (by rfl) ⟨42164, by rfl⟩ : syracuseStep 899509 = 84329) (by norm_num)
theorem B2701781 : Blo 798342 2701781 := bbase (se 7 (by rfl) ⟨31661, by rfl⟩ : syracuseStep 2701781 = 63323) (by norm_num)
theorem B899545 : Blo 798342 899545 := bbase (se 2 (by rfl) ⟨337329, by rfl⟩ : syracuseStep 899545 = 674659) (by norm_num)
theorem B1620461 : Blo 798342 1620461 := bbase (se 3 (by rfl) ⟨303836, by rfl⟩ : syracuseStep 1620461 = 607673) (by norm_num)
theorem B4045301 : Blo 798342 4045301 := bbase (se 5 (by rfl) ⟨189623, by rfl⟩ : syracuseStep 4045301 = 379247) (by norm_num)
theorem B899581 : Blo 798342 899581 := bbase (se 3 (by rfl) ⟨168671, by rfl⟩ : syracuseStep 899581 = 337343) (by norm_num)
theorem B899617 : Blo 798342 899617 := bbase (se 2 (by rfl) ⟨337356, by rfl⟩ : syracuseStep 899617 = 674713) (by norm_num)
theorem B899653 : Blo 798342 899653 := bbase (se 4 (by rfl) ⟨84342, by rfl⟩ : syracuseStep 899653 = 168685) (by norm_num)
theorem B899689 : Blo 798342 899689 := bbase (se 2 (by rfl) ⟨337383, by rfl⟩ : syracuseStep 899689 = 674767) (by norm_num)
theorem B899725 : Blo 798342 899725 := bbase (se 3 (by rfl) ⟨168698, by rfl⟩ : syracuseStep 899725 = 337397) (by norm_num)
theorem B899761 : Blo 798342 899761 := bbase (se 2 (by rfl) ⟨337410, by rfl⟩ : syracuseStep 899761 = 674821) (by norm_num)
theorem B899797 : Blo 798342 899797 := bbase (se 7 (by rfl) ⟨10544, by rfl⟩ : syracuseStep 899797 = 21089) (by norm_num)
theorem B899833 : Blo 798342 899833 := bbase (se 2 (by rfl) ⟨337437, by rfl⟩ : syracuseStep 899833 = 674875) (by norm_num)
theorem B899869 : Blo 798342 899869 := bbase (se 3 (by rfl) ⟨168725, by rfl⟩ : syracuseStep 899869 = 337451) (by norm_num)
theorem B899905 : Blo 798342 899905 := bbase (se 2 (by rfl) ⟨337464, by rfl⟩ : syracuseStep 899905 = 674929) (by norm_num)
theorem B3849029 : Blo 798342 3849029 := bbase (se 4 (by rfl) ⟨360846, by rfl⟩ : syracuseStep 3849029 = 721693) (by norm_num)
theorem B899941 : Blo 798342 899941 := bbase (se 4 (by rfl) ⟨84369, by rfl⟩ : syracuseStep 899941 = 168739) (by norm_num)
theorem B2702213 : Blo 798342 2702213 := bbase (se 4 (by rfl) ⟨253332, by rfl⟩ : syracuseStep 2702213 = 506665) (by norm_num)
theorem B899977 : Blo 798342 899977 := bbase (se 2 (by rfl) ⟨337491, by rfl⟩ : syracuseStep 899977 = 674983) (by norm_num)
theorem B5782421 : Blo 798342 5782421 := bbase (se 6 (by rfl) ⟨135525, by rfl⟩ : syracuseStep 5782421 = 271051) (by norm_num)
theorem B900013 : Blo 798342 900013 := bbase (se 3 (by rfl) ⟨168752, by rfl⟩ : syracuseStep 900013 = 337505) (by norm_num)
theorem B900049 : Blo 798342 900049 := bbase (se 2 (by rfl) ⟨337518, by rfl⟩ : syracuseStep 900049 = 675037) (by norm_num)
theorem B900085 : Blo 798342 900085 := bbase (se 5 (by rfl) ⟨42191, by rfl⟩ : syracuseStep 900085 = 84383) (by norm_num)
theorem B6077429 : Blo 798342 6077429 := bbase (se 5 (by rfl) ⟨284879, by rfl⟩ : syracuseStep 6077429 = 569759) (by norm_num)
theorem B900121 : Blo 798342 900121 := bbase (se 2 (by rfl) ⟨337545, by rfl⟩ : syracuseStep 900121 = 675091) (by norm_num)
theorem B900157 : Blo 798342 900157 := bbase (se 3 (by rfl) ⟨168779, by rfl⟩ : syracuseStep 900157 = 337559) (by norm_num)
theorem B15416405 : Blo 798342 15416405 := bbase (se 8 (by rfl) ⟨90330, by rfl⟩ : syracuseStep 15416405 = 180661) (by norm_num)
theorem B900193 : Blo 798342 900193 := bbase (se 2 (by rfl) ⟨337572, by rfl⟩ : syracuseStep 900193 = 675145) (by norm_num)
theorem B1522813 : Blo 798342 1522813 := bbase (se 3 (by rfl) ⟨285527, by rfl⟩ : syracuseStep 1522813 = 571055) (by norm_num)
theorem B900229 : Blo 798342 900229 := bbase (se 4 (by rfl) ⟨84396, by rfl⟩ : syracuseStep 900229 = 168793) (by norm_num)
theorem B2604197 : Blo 798342 2604197 := bbase (se 4 (by rfl) ⟨244143, by rfl⟩ : syracuseStep 2604197 = 488287) (by norm_num)
theorem B900265 : Blo 798342 900265 := bbase (se 2 (by rfl) ⟨337599, by rfl⟩ : syracuseStep 900265 = 675199) (by norm_num)
theorem B1621181 : Blo 798342 1621181 := bbase (se 3 (by rfl) ⟨303971, by rfl⟩ : syracuseStep 1621181 = 607943) (by norm_num)
theorem B900301 : Blo 798342 900301 := bbase (se 3 (by rfl) ⟨168806, by rfl⟩ : syracuseStep 900301 = 337613) (by norm_num)
theorem B900337 : Blo 798342 900337 := bbase (se 2 (by rfl) ⟨337626, by rfl⟩ : syracuseStep 900337 = 675253) (by norm_num)
theorem B1522957 : Blo 798342 1522957 := bbase (se 3 (by rfl) ⟨285554, by rfl⟩ : syracuseStep 1522957 = 571109) (by norm_num)
theorem B900373 : Blo 798342 900373 := bbase (se 6 (by rfl) ⟨21102, by rfl⟩ : syracuseStep 900373 = 42205) (by norm_num)
theorem B2702645 : Blo 798342 2702645 := bbase (se 5 (by rfl) ⟨126686, by rfl⟩ : syracuseStep 2702645 = 253373) (by norm_num)
theorem B900409 : Blo 798342 900409 := bbase (se 2 (by rfl) ⟨337653, by rfl⟩ : syracuseStep 900409 = 675307) (by norm_num)
theorem B900445 : Blo 798342 900445 := bbase (se 3 (by rfl) ⟨168833, by rfl⟩ : syracuseStep 900445 = 337667) (by norm_num)
theorem B1097069 : Blo 798342 1097069 := bbase (se 3 (by rfl) ⟨205700, by rfl⟩ : syracuseStep 1097069 = 411401) (by norm_num)
theorem B900481 : Blo 798342 900481 := bbase (se 2 (by rfl) ⟨337680, by rfl⟩ : syracuseStep 900481 = 675361) (by norm_num)
theorem B2735525 : Blo 798342 2735525 := bbase (se 4 (by rfl) ⟨256455, by rfl⟩ : syracuseStep 2735525 = 512911) (by norm_num)
theorem B900517 : Blo 798342 900517 := bbase (se 4 (by rfl) ⟨84423, by rfl⟩ : syracuseStep 900517 = 168847) (by norm_num)
theorem B1523117 : Blo 798342 1523117 := bbase (se 3 (by rfl) ⟨285584, by rfl⟩ : syracuseStep 1523117 = 571169) (by norm_num)
theorem B900553 : Blo 798342 900553 := bbase (se 2 (by rfl) ⟨337707, by rfl⟩ : syracuseStep 900553 = 675415) (by norm_num)
theorem B900589 : Blo 798342 900589 := bbase (se 3 (by rfl) ⟨168860, by rfl⟩ : syracuseStep 900589 = 337721) (by norm_num)
theorem B900625 : Blo 798342 900625 := bbase (se 2 (by rfl) ⟨337734, by rfl⟩ : syracuseStep 900625 = 675469) (by norm_num)
theorem B900661 : Blo 798342 900661 := bbase (se 5 (by rfl) ⟨42218, by rfl⟩ : syracuseStep 900661 = 84437) (by norm_num)
theorem B900697 : Blo 798342 900697 := bbase (se 2 (by rfl) ⟨337761, by rfl⟩ : syracuseStep 900697 = 675523) (by norm_num)
theorem B2637413 : Blo 798342 2637413 := bbase (se 4 (by rfl) ⟨247257, by rfl⟩ : syracuseStep 2637413 = 494515) (by norm_num)
theorem B900733 : Blo 798342 900733 := bbase (se 3 (by rfl) ⟨168887, by rfl⟩ : syracuseStep 900733 = 337775) (by norm_num)
theorem B900769 : Blo 798342 900769 := bbase (se 2 (by rfl) ⟨337788, by rfl⟩ : syracuseStep 900769 = 675577) (by norm_num)
theorem B900805 : Blo 798342 900805 := bbase (se 4 (by rfl) ⟨84450, by rfl⟩ : syracuseStep 900805 = 168901) (by norm_num)
theorem B2703077 : Blo 798342 2703077 := bbase (se 4 (by rfl) ⟨253413, by rfl⟩ : syracuseStep 2703077 = 506827) (by norm_num)
theorem B900841 : Blo 798342 900841 := bbase (se 2 (by rfl) ⟨337815, by rfl⟩ : syracuseStep 900841 = 675631) (by norm_num)
theorem B4046597 : Blo 798342 4046597 := bbase (se 4 (by rfl) ⟨379368, by rfl⟩ : syracuseStep 4046597 = 758737) (by norm_num)
theorem B900877 : Blo 798342 900877 := bbase (se 3 (by rfl) ⟨168914, by rfl⟩ : syracuseStep 900877 = 337829) (by norm_num)
theorem B900913 : Blo 798342 900913 := bbase (se 2 (by rfl) ⟨337842, by rfl⟩ : syracuseStep 900913 = 675685) (by norm_num)
theorem B900949 : Blo 798342 900949 := bbase (se 9 (by rfl) ⟨2639, by rfl⟩ : syracuseStep 900949 = 5279) (by norm_num)
theorem B900985 : Blo 798342 900985 := bbase (se 2 (by rfl) ⟨337869, by rfl⟩ : syracuseStep 900985 = 675739) (by norm_num)
theorem B901021 : Blo 798342 901021 := bbase (se 3 (by rfl) ⟨168941, by rfl⟩ : syracuseStep 901021 = 337883) (by norm_num)
theorem B901057 : Blo 798342 901057 := bbase (se 2 (by rfl) ⟨337896, by rfl⟩ : syracuseStep 901057 = 675793) (by norm_num)
theorem B901093 : Blo 798342 901093 := bbase (se 4 (by rfl) ⟨84477, by rfl⟩ : syracuseStep 901093 = 168955) (by norm_num)
theorem B901129 : Blo 798342 901129 := bbase (se 2 (by rfl) ⟨337923, by rfl⟩ : syracuseStep 901129 = 675847) (by norm_num)
theorem B901165 : Blo 798342 901165 := bbase (se 3 (by rfl) ⟨168968, by rfl⟩ : syracuseStep 901165 = 337937) (by norm_num)
theorem B3457093 : Blo 798342 3457093 := bbase (se 4 (by rfl) ⟨324102, by rfl⟩ : syracuseStep 3457093 = 648205) (by norm_num)
theorem B901201 : Blo 798342 901201 := bbase (se 2 (by rfl) ⟨337950, by rfl⟩ : syracuseStep 901201 = 675901) (by norm_num)
theorem B901237 : Blo 798342 901237 := bbase (se 5 (by rfl) ⟨42245, by rfl⟩ : syracuseStep 901237 = 84491) (by norm_num)
theorem B15384725 : Blo 798342 15384725 := bbase (se 6 (by rfl) ⟨360579, by rfl⟩ : syracuseStep 15384725 = 721159) (by norm_num)
theorem B2703509 : Blo 798342 2703509 := bbase (se 6 (by rfl) ⟨63363, by rfl⟩ : syracuseStep 2703509 = 126727) (by norm_num)
theorem B901273 : Blo 798342 901273 := bbase (se 2 (by rfl) ⟨337977, by rfl⟩ : syracuseStep 901273 = 675955) (by norm_num)
theorem B901309 : Blo 798342 901309 := bbase (se 3 (by rfl) ⟨168995, by rfl⟩ : syracuseStep 901309 = 337991) (by norm_num)
theorem B901345 : Blo 798342 901345 := bbase (se 2 (by rfl) ⟨338004, by rfl⟩ : syracuseStep 901345 = 676009) (by norm_num)
theorem B901381 : Blo 798342 901381 := bbase (se 4 (by rfl) ⟨84504, by rfl⟩ : syracuseStep 901381 = 169009) (by norm_num)
theorem B1622285 : Blo 798342 1622285 := bbase (se 3 (by rfl) ⟨304178, by rfl⟩ : syracuseStep 1622285 = 608357) (by norm_num)
theorem B901417 : Blo 798342 901417 := bbase (se 2 (by rfl) ⟨338031, by rfl⟩ : syracuseStep 901417 = 676063) (by norm_num)
theorem B4112693 : Blo 798342 4112693 := bbase (se 5 (by rfl) ⟨192782, by rfl⟩ : syracuseStep 4112693 = 385565) (by norm_num)
theorem B901453 : Blo 798342 901453 := bbase (se 3 (by rfl) ⟨169022, by rfl⟩ : syracuseStep 901453 = 338045) (by norm_num)
theorem B901489 : Blo 798342 901489 := bbase (se 2 (by rfl) ⟨338058, by rfl⟩ : syracuseStep 901489 = 676117) (by norm_num)
theorem B901525 : Blo 798342 901525 := bbase (se 6 (by rfl) ⟨21129, by rfl⟩ : syracuseStep 901525 = 42259) (by norm_num)
theorem B901561 : Blo 798342 901561 := bbase (se 2 (by rfl) ⟨338085, by rfl⟩ : syracuseStep 901561 = 676171) (by norm_num)
theorem B10961365 : Blo 798342 10961365 := bbase (se 7 (by rfl) ⟨128453, by rfl⟩ : syracuseStep 10961365 = 256907) (by norm_num)
theorem B901597 : Blo 798342 901597 := bbase (se 3 (by rfl) ⟨169049, by rfl⟩ : syracuseStep 901597 = 338099) (by norm_num)
theorem B901633 : Blo 798342 901633 := bbase (se 2 (by rfl) ⟨338112, by rfl⟩ : syracuseStep 901633 = 676225) (by norm_num)
theorem B901669 : Blo 798342 901669 := bbase (se 4 (by rfl) ⟨84531, by rfl⟩ : syracuseStep 901669 = 169063) (by norm_num)
theorem B5128757 : Blo 798342 5128757 := bbase (se 5 (by rfl) ⟨240410, by rfl⟩ : syracuseStep 5128757 = 480821) (by norm_num)
theorem B2703941 : Blo 798342 2703941 := bbase (se 4 (by rfl) ⟨253494, by rfl⟩ : syracuseStep 2703941 = 506989) (by norm_num)
theorem B901705 : Blo 798342 901705 := bbase (se 2 (by rfl) ⟨338139, by rfl⟩ : syracuseStep 901705 = 676279) (by norm_num)
theorem B2277989 : Blo 798342 2277989 := bbase (se 4 (by rfl) ⟨213561, by rfl⟩ : syracuseStep 2277989 = 427123) (by norm_num)
theorem B901741 : Blo 798342 901741 := bbase (se 3 (by rfl) ⟨169076, by rfl⟩ : syracuseStep 901741 = 338153) (by norm_num)
theorem B901777 : Blo 798342 901777 := bbase (se 2 (by rfl) ⟨338166, by rfl⟩ : syracuseStep 901777 = 676333) (by norm_num)
theorem B901813 : Blo 798342 901813 := bbase (se 5 (by rfl) ⟨42272, by rfl⟩ : syracuseStep 901813 = 84545) (by norm_num)
theorem B901849 : Blo 798342 901849 := bbase (se 2 (by rfl) ⟨338193, by rfl⟩ : syracuseStep 901849 = 676387) (by norm_num)
theorem B4113125 : Blo 798342 4113125 := bbase (se 4 (by rfl) ⟨385605, by rfl⟩ : syracuseStep 4113125 = 771211) (by norm_num)
theorem B901885 : Blo 798342 901885 := bbase (se 3 (by rfl) ⟨169103, by rfl⟩ : syracuseStep 901885 = 338207) (by norm_num)
theorem B901921 : Blo 798342 901921 := bbase (se 2 (by rfl) ⟨338220, by rfl⟩ : syracuseStep 901921 = 676441) (by norm_num)
theorem B901957 : Blo 798342 901957 := bbase (se 4 (by rfl) ⟨84558, by rfl⟩ : syracuseStep 901957 = 169117) (by norm_num)
theorem B901993 : Blo 798342 901993 := bbase (se 2 (by rfl) ⟨338247, by rfl⟩ : syracuseStep 901993 = 676495) (by norm_num)
theorem B902029 : Blo 798342 902029 := bbase (se 3 (by rfl) ⟨169130, by rfl⟩ : syracuseStep 902029 = 338261) (by norm_num)
theorem B902065 : Blo 798342 902065 := bbase (se 2 (by rfl) ⟨338274, by rfl⟩ : syracuseStep 902065 = 676549) (by norm_num)
theorem B902101 : Blo 798342 902101 := bbase (se 7 (by rfl) ⟨10571, by rfl⟩ : syracuseStep 902101 = 21143) (by norm_num)
theorem B3425237 : Blo 798342 3425237 := bbase (se 7 (by rfl) ⟨40139, by rfl⟩ : syracuseStep 3425237 = 80279) (by norm_num)
theorem B2704373 : Blo 798342 2704373 := bbase (se 5 (by rfl) ⟨126767, by rfl⟩ : syracuseStep 2704373 = 253535) (by norm_num)
theorem B902137 : Blo 798342 902137 := bbase (se 2 (by rfl) ⟨338301, by rfl⟩ : syracuseStep 902137 = 676603) (by norm_num)
theorem B4047893 : Blo 798342 4047893 := bbase (se 6 (by rfl) ⟨94872, by rfl⟩ : syracuseStep 4047893 = 189745) (by norm_num)
theorem B902173 : Blo 798342 902173 := bbase (se 3 (by rfl) ⟨169157, by rfl⟩ : syracuseStep 902173 = 338315) (by norm_num)
theorem B902209 : Blo 798342 902209 := bbase (se 2 (by rfl) ⟨338328, by rfl⟩ : syracuseStep 902209 = 676657) (by norm_num)
theorem B2049101 : Blo 798342 2049101 := bbase (se 3 (by rfl) ⟨384206, by rfl⟩ : syracuseStep 2049101 = 768413) (by norm_num)
theorem B902245 : Blo 798342 902245 := bbase (se 4 (by rfl) ⟨84585, by rfl⟩ : syracuseStep 902245 = 169171) (by norm_num)
theorem B902281 : Blo 798342 902281 := bbase (se 2 (by rfl) ⟨338355, by rfl⟩ : syracuseStep 902281 = 676711) (by norm_num)
theorem B902317 : Blo 798342 902317 := bbase (se 3 (by rfl) ⟨169184, by rfl⟩ : syracuseStep 902317 = 338369) (by norm_num)
theorem B3032261 : Blo 798342 3032261 := bbase (se 4 (by rfl) ⟨284274, by rfl⟩ : syracuseStep 3032261 = 568549) (by norm_num)
theorem B902353 : Blo 798342 902353 := bbase (se 2 (by rfl) ⟨338382, by rfl⟩ : syracuseStep 902353 = 676765) (by norm_num)
theorem B902389 : Blo 798342 902389 := bbase (se 5 (by rfl) ⟨42299, by rfl⟩ : syracuseStep 902389 = 84599) (by norm_num)
theorem B902425 : Blo 798342 902425 := bbase (se 2 (by rfl) ⟨338409, by rfl⟩ : syracuseStep 902425 = 676819) (by norm_num)
theorem B902461 : Blo 798342 902461 := bbase (se 3 (by rfl) ⟨169211, by rfl⟩ : syracuseStep 902461 = 338423) (by norm_num)
theorem B902497 : Blo 798342 902497 := bbase (se 2 (by rfl) ⟨338436, by rfl⟩ : syracuseStep 902497 = 676873) (by norm_num)
theorem B902533 : Blo 798342 902533 := bbase (se 4 (by rfl) ⟨84612, by rfl⟩ : syracuseStep 902533 = 169225) (by norm_num)
theorem B2704805 : Blo 798342 2704805 := bbase (se 4 (by rfl) ⟨253575, by rfl⟩ : syracuseStep 2704805 = 507151) (by norm_num)
theorem B902569 : Blo 798342 902569 := bbase (se 2 (by rfl) ⟨338463, by rfl⟩ : syracuseStep 902569 = 676927) (by norm_num)
theorem B3851717 : Blo 798342 3851717 := bbase (se 4 (by rfl) ⟨361098, by rfl⟩ : syracuseStep 3851717 = 722197) (by norm_num)
theorem B902605 : Blo 798342 902605 := bbase (se 3 (by rfl) ⟨169238, by rfl⟩ : syracuseStep 902605 = 338477) (by norm_num)
theorem B1918421 : Blo 798342 1918421 := bbase (se 7 (by rfl) ⟨22481, by rfl⟩ : syracuseStep 1918421 = 44963) (by norm_num)
theorem B1197533 : Blo 798342 1197533 := bbase (se 3 (by rfl) ⟨224537, by rfl⟩ : syracuseStep 1197533 = 449075) (by norm_num)
theorem B3032549 : Blo 798342 3032549 := bbase (se 4 (by rfl) ⟨284301, by rfl⟩ : syracuseStep 3032549 = 568603) (by norm_num)
theorem B1197557 : Blo 798342 1197557 := bbase (se 5 (by rfl) ⟨56135, by rfl⟩ : syracuseStep 1197557 = 112271) (by norm_num)
theorem B1197581 : Blo 798342 1197581 := bbase (se 3 (by rfl) ⟨224546, by rfl⟩ : syracuseStep 1197581 = 449093) (by norm_num)
theorem B1197605 : Blo 798342 1197605 := bbase (se 4 (by rfl) ⟨112275, by rfl⟩ : syracuseStep 1197605 = 224551) (by norm_num)
theorem B1197629 : Blo 798342 1197629 := bbase (se 3 (by rfl) ⟨224555, by rfl⟩ : syracuseStep 1197629 = 449111) (by norm_num)
theorem B1197653 : Blo 798342 1197653 := bbase (se 8 (by rfl) ⟨7017, by rfl⟩ : syracuseStep 1197653 = 14035) (by norm_num)
theorem B26297941 : Blo 798342 26297941 := bbase (se 8 (by rfl) ⟨154089, by rfl⟩ : syracuseStep 26297941 = 308179) (by norm_num)
theorem B1197677 : Blo 798342 1197677 := bbase (se 3 (by rfl) ⟨224564, by rfl⟩ : syracuseStep 1197677 = 449129) (by norm_num)
theorem B1197701 : Blo 798342 1197701 := bbase (se 4 (by rfl) ⟨112284, by rfl⟩ : syracuseStep 1197701 = 224569) (by norm_num)
theorem B1197725 : Blo 798342 1197725 := bbase (se 3 (by rfl) ⟨224573, by rfl⟩ : syracuseStep 1197725 = 449147) (by norm_num)
theorem B1197749 : Blo 798342 1197749 := bbase (se 5 (by rfl) ⟨56144, by rfl⟩ : syracuseStep 1197749 = 112289) (by norm_num)
theorem B1197773 : Blo 798342 1197773 := bbase (se 3 (by rfl) ⟨224582, by rfl⟩ : syracuseStep 1197773 = 449165) (by norm_num)
theorem B1197797 : Blo 798342 1197797 := bbase (se 4 (by rfl) ⟨112293, by rfl⟩ : syracuseStep 1197797 = 224587) (by norm_num)
theorem B1197821 : Blo 798342 1197821 := bbase (se 3 (by rfl) ⟨224591, by rfl⟩ : syracuseStep 1197821 = 449183) (by norm_num)
theorem B2279173 : Blo 798342 2279173 := bbase (se 4 (by rfl) ⟨213672, by rfl⟩ : syracuseStep 2279173 = 427345) (by norm_num)
theorem B1197845 : Blo 798342 1197845 := bbase (se 6 (by rfl) ⟨28074, by rfl⟩ : syracuseStep 1197845 = 56149) (by norm_num)
theorem B1197869 : Blo 798342 1197869 := bbase (se 3 (by rfl) ⟨224600, by rfl⟩ : syracuseStep 1197869 = 449201) (by norm_num)
theorem B1197893 : Blo 798342 1197893 := bbase (se 4 (by rfl) ⟨112302, by rfl⟩ : syracuseStep 1197893 = 224605) (by norm_num)
theorem B2705237 : Blo 798342 2705237 := bbase (se 9 (by rfl) ⟨7925, by rfl⟩ : syracuseStep 2705237 = 15851) (by norm_num)
theorem B1197917 : Blo 798342 1197917 := bbase (se 3 (by rfl) ⟨224609, by rfl⟩ : syracuseStep 1197917 = 449219) (by norm_num)
theorem B1197941 : Blo 798342 1197941 := bbase (se 5 (by rfl) ⟨56153, by rfl⟩ : syracuseStep 1197941 = 112307) (by norm_num)
theorem B1197965 : Blo 798342 1197965 := bbase (se 3 (by rfl) ⟨224618, by rfl⟩ : syracuseStep 1197965 = 449237) (by norm_num)
theorem B1197989 : Blo 798342 1197989 := bbase (se 4 (by rfl) ⟨112311, by rfl⟩ : syracuseStep 1197989 = 224623) (by norm_num)
theorem B2279333 : Blo 798342 2279333 := bbase (se 4 (by rfl) ⟨213687, by rfl⟩ : syracuseStep 2279333 = 427375) (by norm_num)
theorem B1198013 : Blo 798342 1198013 := bbase (se 3 (by rfl) ⟨224627, by rfl⟩ : syracuseStep 1198013 = 449255) (by norm_num)
theorem B3426245 : Blo 798342 3426245 := bbase (se 4 (by rfl) ⟨321210, by rfl⟩ : syracuseStep 3426245 = 642421) (by norm_num)
theorem B1198037 : Blo 798342 1198037 := bbase (se 7 (by rfl) ⟨14039, by rfl⟩ : syracuseStep 1198037 = 28079) (by norm_num)
theorem B1198061 : Blo 798342 1198061 := bbase (se 3 (by rfl) ⟨224636, by rfl⟩ : syracuseStep 1198061 = 449273) (by norm_num)
theorem B1198085 : Blo 798342 1198085 := bbase (se 4 (by rfl) ⟨112320, by rfl⟩ : syracuseStep 1198085 = 224641) (by norm_num)
theorem B1198109 : Blo 798342 1198109 := bbase (se 3 (by rfl) ⟨224645, by rfl⟩ : syracuseStep 1198109 = 449291) (by norm_num)
theorem B1198133 : Blo 798342 1198133 := bbase (se 5 (by rfl) ⟨56162, by rfl⟩ : syracuseStep 1198133 = 112325) (by norm_num)
theorem B1198157 : Blo 798342 1198157 := bbase (se 3 (by rfl) ⟨224654, by rfl⟩ : syracuseStep 1198157 = 449309) (by norm_num)
theorem B1198181 : Blo 798342 1198181 := bbase (se 4 (by rfl) ⟨112329, by rfl⟩ : syracuseStep 1198181 = 224659) (by norm_num)
theorem B1198205 : Blo 798342 1198205 := bbase (se 3 (by rfl) ⟨224663, by rfl⟩ : syracuseStep 1198205 = 449327) (by norm_num)
theorem B1198229 : Blo 798342 1198229 := bbase (se 6 (by rfl) ⟨28083, by rfl⟩ : syracuseStep 1198229 = 56167) (by norm_num)
theorem B2279573 : Blo 798342 2279573 := bbase (se 6 (by rfl) ⟨53427, by rfl⟩ : syracuseStep 2279573 = 106855) (by norm_num)
theorem B1820837 : Blo 798342 1820837 := bbase (se 4 (by rfl) ⟨170703, by rfl⟩ : syracuseStep 1820837 = 341407) (by norm_num)
theorem B1198253 : Blo 798342 1198253 := bbase (se 3 (by rfl) ⟨224672, by rfl⟩ : syracuseStep 1198253 = 449345) (by norm_num)
theorem B1198277 : Blo 798342 1198277 := bbase (se 4 (by rfl) ⟨112338, by rfl⟩ : syracuseStep 1198277 = 224677) (by norm_num)
theorem B1198301 : Blo 798342 1198301 := bbase (se 3 (by rfl) ⟨224681, by rfl⟩ : syracuseStep 1198301 = 449363) (by norm_num)
theorem B1198325 : Blo 798342 1198325 := bbase (se 5 (by rfl) ⟨56171, by rfl⟩ : syracuseStep 1198325 = 112343) (by norm_num)
theorem B2705669 : Blo 798342 2705669 := bbase (se 4 (by rfl) ⟨253656, by rfl⟩ : syracuseStep 2705669 = 507313) (by norm_num)
theorem B1198349 : Blo 798342 1198349 := bbase (se 3 (by rfl) ⟨224690, by rfl⟩ : syracuseStep 1198349 = 449381) (by norm_num)
theorem B1198373 : Blo 798342 1198373 := bbase (se 4 (by rfl) ⟨112347, by rfl⟩ : syracuseStep 1198373 = 224695) (by norm_num)
theorem B4049189 : Blo 798342 4049189 := bbase (se 4 (by rfl) ⟨379611, by rfl⟩ : syracuseStep 4049189 = 759223) (by norm_num)
theorem B1198397 : Blo 798342 1198397 := bbase (se 3 (by rfl) ⟨224699, by rfl⟩ : syracuseStep 1198397 = 449399) (by norm_num)
theorem B1198421 : Blo 798342 1198421 := bbase (se 10 (by rfl) ⟨1755, by rfl⟩ : syracuseStep 1198421 = 3511) (by norm_num)
theorem B7686485 : Blo 798342 7686485 := bbase (se 10 (by rfl) ⟨11259, by rfl⟩ : syracuseStep 7686485 = 22519) (by norm_num)
theorem B2279765 : Blo 798342 2279765 := bbase (se 10 (by rfl) ⟨3339, by rfl⟩ : syracuseStep 2279765 = 6679) (by norm_num)
theorem B1296749 : Blo 798342 1296749 := bbase (se 3 (by rfl) ⟨243140, by rfl⟩ : syracuseStep 1296749 = 486281) (by norm_num)
theorem B1198445 : Blo 798342 1198445 := bbase (se 3 (by rfl) ⟨224708, by rfl⟩ : syracuseStep 1198445 = 449417) (by norm_num)
theorem B1198469 : Blo 798342 1198469 := bbase (se 4 (by rfl) ⟨112356, by rfl⟩ : syracuseStep 1198469 = 224713) (by norm_num)
theorem B1198493 : Blo 798342 1198493 := bbase (se 3 (by rfl) ⟨224717, by rfl⟩ : syracuseStep 1198493 = 449435) (by norm_num)
theorem B1198517 : Blo 798342 1198517 := bbase (se 5 (by rfl) ⟨56180, by rfl⟩ : syracuseStep 1198517 = 112361) (by norm_num)
theorem B1198541 : Blo 798342 1198541 := bbase (se 3 (by rfl) ⟨224726, by rfl⟩ : syracuseStep 1198541 = 449453) (by norm_num)
theorem B1198565 : Blo 798342 1198565 := bbase (se 4 (by rfl) ⟨112365, by rfl⟩ : syracuseStep 1198565 = 224731) (by norm_num)
theorem B1198589 : Blo 798342 1198589 := bbase (se 3 (by rfl) ⟨224735, by rfl⟩ : syracuseStep 1198589 = 449471) (by norm_num)
theorem B1198613 : Blo 798342 1198613 := bbase (se 6 (by rfl) ⟨28092, by rfl⟩ : syracuseStep 1198613 = 56185) (by norm_num)
theorem B1198637 : Blo 798342 1198637 := bbase (se 3 (by rfl) ⟨224744, by rfl⟩ : syracuseStep 1198637 = 449489) (by norm_num)
theorem B1624637 : Blo 798342 1624637 := bbase (se 3 (by rfl) ⟨304619, by rfl⟩ : syracuseStep 1624637 = 609239) (by norm_num)
theorem B1198661 : Blo 798342 1198661 := bbase (se 4 (by rfl) ⟨112374, by rfl⟩ : syracuseStep 1198661 = 224749) (by norm_num)
theorem B4115029 : Blo 798342 4115029 := bbase (se 8 (by rfl) ⟨24111, by rfl⟩ : syracuseStep 4115029 = 48223) (by norm_num)
theorem B1198685 : Blo 798342 1198685 := bbase (se 3 (by rfl) ⟨224753, by rfl⟩ : syracuseStep 1198685 = 449507) (by norm_num)
theorem B1198709 : Blo 798342 1198709 := bbase (se 5 (by rfl) ⟨56189, by rfl⟩ : syracuseStep 1198709 = 112379) (by norm_num)
theorem B3033733 : Blo 798342 3033733 := bbase (se 4 (by rfl) ⟨284412, by rfl⟩ : syracuseStep 3033733 = 568825) (by norm_num)
theorem B1198733 : Blo 798342 1198733 := bbase (se 3 (by rfl) ⟨224762, by rfl⟩ : syracuseStep 1198733 = 449525) (by norm_num)
theorem B8440469 : Blo 798342 8440469 := bbase (se 6 (by rfl) ⟨197823, by rfl⟩ : syracuseStep 8440469 = 395647) (by norm_num)
theorem B1198757 : Blo 798342 1198757 := bbase (se 4 (by rfl) ⟨112383, by rfl⟩ : syracuseStep 1198757 = 224767) (by norm_num)
theorem B2706101 : Blo 798342 2706101 := bbase (se 5 (by rfl) ⟨126848, by rfl⟩ : syracuseStep 2706101 = 253697) (by norm_num)
theorem B1198781 : Blo 798342 1198781 := bbase (se 3 (by rfl) ⟨224771, by rfl⟩ : syracuseStep 1198781 = 449543) (by norm_num)
theorem B1198805 : Blo 798342 1198805 := bbase (se 7 (by rfl) ⟨14048, by rfl⟩ : syracuseStep 1198805 = 28097) (by norm_num)
theorem B1854181 : Blo 798342 1854181 := bbase (se 4 (by rfl) ⟨173829, by rfl⟩ : syracuseStep 1854181 = 347659) (by norm_num)
theorem B1198829 : Blo 798342 1198829 := bbase (se 3 (by rfl) ⟨224780, by rfl⟩ : syracuseStep 1198829 = 449561) (by norm_num)
theorem B1198853 : Blo 798342 1198853 := bbase (se 4 (by rfl) ⟨112392, by rfl⟩ : syracuseStep 1198853 = 224785) (by norm_num)
theorem B1198877 : Blo 798342 1198877 := bbase (se 3 (by rfl) ⟨224789, by rfl⟩ : syracuseStep 1198877 = 449579) (by norm_num)
theorem B1198901 : Blo 798342 1198901 := bbase (se 5 (by rfl) ⟨56198, by rfl⟩ : syracuseStep 1198901 = 112397) (by norm_num)
theorem B1198925 : Blo 798342 1198925 := bbase (se 3 (by rfl) ⟨224798, by rfl⟩ : syracuseStep 1198925 = 449597) (by norm_num)
theorem B1198949 : Blo 798342 1198949 := bbase (se 4 (by rfl) ⟨112401, by rfl⟩ : syracuseStep 1198949 = 224803) (by norm_num)
theorem B1198973 : Blo 798342 1198973 := bbase (se 3 (by rfl) ⟨224807, by rfl⟩ : syracuseStep 1198973 = 449615) (by norm_num)
theorem B1198997 : Blo 798342 1198997 := bbase (se 6 (by rfl) ⟨28101, by rfl⟩ : syracuseStep 1198997 = 56203) (by norm_num)
theorem B1199021 : Blo 798342 1199021 := bbase (se 3 (by rfl) ⟨224816, by rfl⟩ : syracuseStep 1199021 = 449633) (by norm_num)
theorem B3034037 : Blo 798342 3034037 := bbase (se 5 (by rfl) ⟨142220, by rfl⟩ : syracuseStep 3034037 = 284441) (by norm_num)
theorem B1199045 : Blo 798342 1199045 := bbase (se 4 (by rfl) ⟨112410, by rfl⟩ : syracuseStep 1199045 = 224821) (by norm_num)
theorem B1199069 : Blo 798342 1199069 := bbase (se 3 (by rfl) ⟨224825, by rfl⟩ : syracuseStep 1199069 = 449651) (by norm_num)
theorem B1199093 : Blo 798342 1199093 := bbase (se 5 (by rfl) ⟨56207, by rfl⟩ : syracuseStep 1199093 = 112415) (by norm_num)
theorem B1199117 : Blo 798342 1199117 := bbase (se 3 (by rfl) ⟨224834, by rfl⟩ : syracuseStep 1199117 = 449669) (by norm_num)
theorem B1199141 : Blo 798342 1199141 := bbase (se 4 (by rfl) ⟨112419, by rfl⟩ : syracuseStep 1199141 = 224839) (by norm_num)
theorem B1199165 : Blo 798342 1199165 := bbase (se 3 (by rfl) ⟨224843, by rfl⟩ : syracuseStep 1199165 = 449687) (by norm_num)
theorem B1199189 : Blo 798342 1199189 := bbase (se 8 (by rfl) ⟨7026, by rfl⟩ : syracuseStep 1199189 = 14053) (by norm_num)
theorem B2706533 : Blo 798342 2706533 := bbase (se 4 (by rfl) ⟨253737, by rfl⟩ : syracuseStep 2706533 = 507475) (by norm_num)
theorem B1199213 : Blo 798342 1199213 := bbase (se 3 (by rfl) ⟨224852, by rfl⟩ : syracuseStep 1199213 = 449705) (by norm_num)
theorem B1199237 : Blo 798342 1199237 := bbase (se 4 (by rfl) ⟨112428, by rfl⟩ : syracuseStep 1199237 = 224857) (by norm_num)
theorem B1199261 : Blo 798342 1199261 := bbase (se 3 (by rfl) ⟨224861, by rfl⟩ : syracuseStep 1199261 = 449723) (by norm_num)
theorem B1199285 : Blo 798342 1199285 := bbase (se 5 (by rfl) ⟨56216, by rfl⟩ : syracuseStep 1199285 = 112433) (by norm_num)
theorem B1199309 : Blo 798342 1199309 := bbase (se 3 (by rfl) ⟨224870, by rfl⟩ : syracuseStep 1199309 = 449741) (by norm_num)
theorem B1199333 : Blo 798342 1199333 := bbase (se 4 (by rfl) ⟨112437, by rfl⟩ : syracuseStep 1199333 = 224875) (by norm_num)
theorem B1199357 : Blo 798342 1199357 := bbase (se 3 (by rfl) ⟨224879, by rfl⟩ : syracuseStep 1199357 = 449759) (by norm_num)
theorem B1199381 : Blo 798342 1199381 := bbase (se 6 (by rfl) ⟨28110, by rfl⟩ : syracuseStep 1199381 = 56221) (by norm_num)
theorem B1199405 : Blo 798342 1199405 := bbase (se 3 (by rfl) ⟨224888, by rfl⟩ : syracuseStep 1199405 = 449777) (by norm_num)
theorem B2280757 : Blo 798342 2280757 := bbase (se 5 (by rfl) ⟨106910, by rfl⟩ : syracuseStep 2280757 = 213821) (by norm_num)
theorem B1199429 : Blo 798342 1199429 := bbase (se 4 (by rfl) ⟨112446, by rfl⟩ : syracuseStep 1199429 = 224893) (by norm_num)
theorem B1199453 : Blo 798342 1199453 := bbase (se 3 (by rfl) ⟨224897, by rfl⟩ : syracuseStep 1199453 = 449795) (by norm_num)
theorem B1199477 : Blo 798342 1199477 := bbase (se 5 (by rfl) ⟨56225, by rfl⟩ : syracuseStep 1199477 = 112451) (by norm_num)
theorem B1199501 : Blo 798342 1199501 := bbase (se 3 (by rfl) ⟨224906, by rfl⟩ : syracuseStep 1199501 = 449813) (by norm_num)
theorem B1199525 : Blo 798342 1199525 := bbase (se 4 (by rfl) ⟨112455, by rfl⟩ : syracuseStep 1199525 = 224911) (by norm_num)
theorem B1199549 : Blo 798342 1199549 := bbase (se 3 (by rfl) ⟨224915, by rfl⟩ : syracuseStep 1199549 = 449831) (by norm_num)
theorem B1199573 : Blo 798342 1199573 := bbase (se 7 (by rfl) ⟨14057, by rfl⟩ : syracuseStep 1199573 = 28115) (by norm_num)
theorem B1199597 : Blo 798342 1199597 := bbase (se 3 (by rfl) ⟨224924, by rfl⟩ : syracuseStep 1199597 = 449849) (by norm_num)
theorem B1199621 : Blo 798342 1199621 := bbase (se 4 (by rfl) ⟨112464, by rfl⟩ : syracuseStep 1199621 = 224929) (by norm_num)
theorem B2706965 : Blo 798342 2706965 := bbase (se 6 (by rfl) ⟨63444, by rfl⟩ : syracuseStep 2706965 = 126889) (by norm_num)
theorem B1199645 : Blo 798342 1199645 := bbase (se 3 (by rfl) ⟨224933, by rfl⟩ : syracuseStep 1199645 = 449867) (by norm_num)
theorem B1199669 : Blo 798342 1199669 := bbase (se 5 (by rfl) ⟨56234, by rfl⟩ : syracuseStep 1199669 = 112469) (by norm_num)
theorem B4050485 : Blo 798342 4050485 := bbase (se 5 (by rfl) ⟨189866, by rfl⟩ : syracuseStep 4050485 = 379733) (by norm_num)
theorem B1199693 : Blo 798342 1199693 := bbase (se 3 (by rfl) ⟨224942, by rfl⟩ : syracuseStep 1199693 = 449885) (by norm_num)
theorem B1199717 : Blo 798342 1199717 := bbase (se 4 (by rfl) ⟨112473, by rfl⟩ : syracuseStep 1199717 = 224947) (by norm_num)
theorem B1199741 : Blo 798342 1199741 := bbase (se 3 (by rfl) ⟨224951, by rfl⟩ : syracuseStep 1199741 = 449903) (by norm_num)
theorem B1199765 : Blo 798342 1199765 := bbase (se 6 (by rfl) ⟨28119, by rfl⟩ : syracuseStep 1199765 = 56239) (by norm_num)
theorem B1199789 : Blo 798342 1199789 := bbase (se 3 (by rfl) ⟨224960, by rfl⟩ : syracuseStep 1199789 = 449921) (by norm_num)
theorem B1199813 : Blo 798342 1199813 := bbase (se 4 (by rfl) ⟨112482, by rfl⟩ : syracuseStep 1199813 = 224965) (by norm_num)
theorem B1199837 : Blo 798342 1199837 := bbase (se 3 (by rfl) ⟨224969, by rfl⟩ : syracuseStep 1199837 = 449939) (by norm_num)
theorem B1199861 : Blo 798342 1199861 := bbase (se 5 (by rfl) ⟨56243, by rfl⟩ : syracuseStep 1199861 = 112487) (by norm_num)
theorem B1199885 : Blo 798342 1199885 := bbase (se 3 (by rfl) ⟨224978, by rfl⟩ : syracuseStep 1199885 = 449957) (by norm_num)
theorem B1199909 : Blo 798342 1199909 := bbase (se 4 (by rfl) ⟨112491, by rfl⟩ : syracuseStep 1199909 = 224983) (by norm_num)
theorem B1199933 : Blo 798342 1199933 := bbase (se 3 (by rfl) ⟨224987, by rfl⟩ : syracuseStep 1199933 = 449975) (by norm_num)
theorem B1199957 : Blo 798342 1199957 := bbase (se 9 (by rfl) ⟨3515, by rfl⟩ : syracuseStep 1199957 = 7031) (by norm_num)
theorem B1199981 : Blo 798342 1199981 := bbase (se 3 (by rfl) ⟨224996, by rfl⟩ : syracuseStep 1199981 = 449993) (by norm_num)
theorem B1822589 : Blo 798342 1822589 := bbase (se 3 (by rfl) ⟨341735, by rfl⟩ : syracuseStep 1822589 = 683471) (by norm_num)
theorem B1200005 : Blo 798342 1200005 := bbase (se 4 (by rfl) ⟨112500, by rfl⟩ : syracuseStep 1200005 = 225001) (by norm_num)
theorem B1200029 : Blo 798342 1200029 := bbase (se 3 (by rfl) ⟨225005, by rfl⟩ : syracuseStep 1200029 = 450011) (by norm_num)
theorem B1200053 : Blo 798342 1200053 := bbase (se 5 (by rfl) ⟨56252, by rfl⟩ : syracuseStep 1200053 = 112505) (by norm_num)
theorem B2707397 : Blo 798342 2707397 := bbase (se 4 (by rfl) ⟨253818, by rfl⟩ : syracuseStep 2707397 = 507637) (by norm_num)
theorem B1200077 : Blo 798342 1200077 := bbase (se 3 (by rfl) ⟨225014, by rfl⟩ : syracuseStep 1200077 = 450029) (by norm_num)
theorem B1200101 : Blo 798342 1200101 := bbase (se 4 (by rfl) ⟨112509, by rfl⟩ : syracuseStep 1200101 = 225019) (by norm_num)
theorem B1200125 : Blo 798342 1200125 := bbase (se 3 (by rfl) ⟨225023, by rfl⟩ : syracuseStep 1200125 = 450047) (by norm_num)
theorem B1200149 : Blo 798342 1200149 := bbase (se 6 (by rfl) ⟨28128, by rfl⟩ : syracuseStep 1200149 = 56257) (by norm_num)
theorem B1200173 : Blo 798342 1200173 := bbase (se 3 (by rfl) ⟨225032, by rfl⟩ : syracuseStep 1200173 = 450065) (by norm_num)
theorem B1200197 : Blo 798342 1200197 := bbase (se 4 (by rfl) ⟨112518, by rfl⟩ : syracuseStep 1200197 = 225037) (by norm_num)
theorem B1200221 : Blo 798342 1200221 := bbase (se 3 (by rfl) ⟨225041, by rfl⟩ : syracuseStep 1200221 = 450083) (by norm_num)
theorem B1200245 : Blo 798342 1200245 := bbase (se 5 (by rfl) ⟨56261, by rfl⟩ : syracuseStep 1200245 = 112523) (by norm_num)
theorem B1200269 : Blo 798342 1200269 := bbase (se 3 (by rfl) ⟨225050, by rfl⟩ : syracuseStep 1200269 = 450101) (by norm_num)
theorem B1200293 : Blo 798342 1200293 := bbase (se 4 (by rfl) ⟨112527, by rfl⟩ : syracuseStep 1200293 = 225055) (by norm_num)
theorem B1200317 : Blo 798342 1200317 := bbase (se 3 (by rfl) ⟨225059, by rfl⟩ : syracuseStep 1200317 = 450119) (by norm_num)
theorem B1200341 : Blo 798342 1200341 := bbase (se 7 (by rfl) ⟨14066, by rfl⟩ : syracuseStep 1200341 = 28133) (by norm_num)
theorem B1200365 : Blo 798342 1200365 := bbase (se 3 (by rfl) ⟨225068, by rfl⟩ : syracuseStep 1200365 = 450137) (by norm_num)
theorem B1200389 : Blo 798342 1200389 := bbase (se 4 (by rfl) ⟨112536, by rfl⟩ : syracuseStep 1200389 = 225073) (by norm_num)
theorem B1200413 : Blo 798342 1200413 := bbase (se 3 (by rfl) ⟨225077, by rfl⟩ : syracuseStep 1200413 = 450155) (by norm_num)
theorem B1200437 : Blo 798342 1200437 := bbase (se 5 (by rfl) ⟨56270, by rfl⟩ : syracuseStep 1200437 = 112541) (by norm_num)
theorem B1200461 : Blo 798342 1200461 := bbase (se 3 (by rfl) ⟨225086, by rfl⟩ : syracuseStep 1200461 = 450173) (by norm_num)
theorem B1200485 : Blo 798342 1200485 := bbase (se 4 (by rfl) ⟨112545, by rfl⟩ : syracuseStep 1200485 = 225091) (by norm_num)
theorem B2707829 : Blo 798342 2707829 := bbase (se 5 (by rfl) ⟨126929, by rfl⟩ : syracuseStep 2707829 = 253859) (by norm_num)
theorem B1200509 : Blo 798342 1200509 := bbase (se 3 (by rfl) ⟨225095, by rfl⟩ : syracuseStep 1200509 = 450191) (by norm_num)
theorem B2281861 : Blo 798342 2281861 := bbase (se 4 (by rfl) ⟨213924, by rfl⟩ : syracuseStep 2281861 = 427849) (by norm_num)
theorem B1200533 : Blo 798342 1200533 := bbase (se 6 (by rfl) ⟨28137, by rfl⟩ : syracuseStep 1200533 = 56275) (by norm_num)
theorem B1200557 : Blo 798342 1200557 := bbase (se 3 (by rfl) ⟨225104, by rfl⟩ : syracuseStep 1200557 = 450209) (by norm_num)
theorem B1921477 : Blo 798342 1921477 := bbase (se 4 (by rfl) ⟨180138, by rfl⟩ : syracuseStep 1921477 = 360277) (by norm_num)
theorem B1200581 : Blo 798342 1200581 := bbase (se 4 (by rfl) ⟨112554, by rfl⟩ : syracuseStep 1200581 = 225109) (by norm_num)
theorem B1200605 : Blo 798342 1200605 := bbase (se 3 (by rfl) ⟨225113, by rfl⟩ : syracuseStep 1200605 = 450227) (by norm_num)
theorem B1200629 : Blo 798342 1200629 := bbase (se 5 (by rfl) ⟨56279, by rfl⟩ : syracuseStep 1200629 = 112559) (by norm_num)
theorem B1200653 : Blo 798342 1200653 := bbase (se 3 (by rfl) ⟨225122, by rfl⟩ : syracuseStep 1200653 = 450245) (by norm_num)
theorem B1200677 : Blo 798342 1200677 := bbase (se 4 (by rfl) ⟨112563, by rfl⟩ : syracuseStep 1200677 = 225127) (by norm_num)
theorem B1200701 : Blo 798342 1200701 := bbase (se 3 (by rfl) ⟨225131, by rfl⟩ : syracuseStep 1200701 = 450263) (by norm_num)
theorem B1200725 : Blo 798342 1200725 := bbase (se 8 (by rfl) ⟨7035, by rfl⟩ : syracuseStep 1200725 = 14071) (by norm_num)
theorem B1200749 : Blo 798342 1200749 := bbase (se 3 (by rfl) ⟨225140, by rfl⟩ : syracuseStep 1200749 = 450281) (by norm_num)
theorem B1692269 : Blo 798342 1692269 := bbase (se 3 (by rfl) ⟨317300, by rfl⟩ : syracuseStep 1692269 = 634601) (by norm_num)
theorem B1200773 : Blo 798342 1200773 := bbase (se 4 (by rfl) ⟨112572, by rfl⟩ : syracuseStep 1200773 = 225145) (by norm_num)
theorem B1200797 : Blo 798342 1200797 := bbase (se 3 (by rfl) ⟨225149, by rfl⟩ : syracuseStep 1200797 = 450299) (by norm_num)
theorem B1200821 : Blo 798342 1200821 := bbase (se 5 (by rfl) ⟨56288, by rfl⟩ : syracuseStep 1200821 = 112577) (by norm_num)
theorem B1200845 : Blo 798342 1200845 := bbase (se 3 (by rfl) ⟨225158, by rfl⟩ : syracuseStep 1200845 = 450317) (by norm_num)
theorem B1200869 : Blo 798342 1200869 := bbase (se 4 (by rfl) ⟨112581, by rfl⟩ : syracuseStep 1200869 = 225163) (by norm_num)
theorem B5755637 : Blo 798342 5755637 := bbase (se 5 (by rfl) ⟨269795, by rfl⟩ : syracuseStep 5755637 = 539591) (by norm_num)
theorem B1200893 : Blo 798342 1200893 := bbase (se 3 (by rfl) ⟨225167, by rfl⟩ : syracuseStep 1200893 = 450335) (by norm_num)
theorem B1200917 : Blo 798342 1200917 := bbase (se 6 (by rfl) ⟨28146, by rfl⟩ : syracuseStep 1200917 = 56293) (by norm_num)
theorem B1200941 : Blo 798342 1200941 := bbase (se 3 (by rfl) ⟨225176, by rfl⟩ : syracuseStep 1200941 = 450353) (by norm_num)
theorem B4051781 : Blo 798342 4051781 := bbase (se 4 (by rfl) ⟨379854, by rfl⟩ : syracuseStep 4051781 = 759709) (by norm_num)
theorem B1200965 : Blo 798342 1200965 := bbase (se 4 (by rfl) ⟨112590, by rfl⟩ : syracuseStep 1200965 = 225181) (by norm_num)
theorem B1200989 : Blo 798342 1200989 := bbase (se 3 (by rfl) ⟨225185, by rfl⟩ : syracuseStep 1200989 = 450371) (by norm_num)
theorem B1201013 : Blo 798342 1201013 := bbase (se 5 (by rfl) ⟨56297, by rfl⟩ : syracuseStep 1201013 = 112595) (by norm_num)
theorem B1823629 : Blo 798342 1823629 := bbase (se 3 (by rfl) ⟨341930, by rfl⟩ : syracuseStep 1823629 = 683861) (by norm_num)
theorem B1201037 : Blo 798342 1201037 := bbase (se 3 (by rfl) ⟨225194, by rfl⟩ : syracuseStep 1201037 = 450389) (by norm_num)
theorem B1201061 : Blo 798342 1201061 := bbase (se 4 (by rfl) ⟨112599, by rfl⟩ : syracuseStep 1201061 = 225199) (by norm_num)
theorem B1201085 : Blo 798342 1201085 := bbase (se 3 (by rfl) ⟨225203, by rfl⟩ : syracuseStep 1201085 = 450407) (by norm_num)
theorem B1201109 : Blo 798342 1201109 := bbase (se 7 (by rfl) ⟨14075, by rfl⟩ : syracuseStep 1201109 = 28151) (by norm_num)
theorem B1201133 : Blo 798342 1201133 := bbase (se 3 (by rfl) ⟨225212, by rfl⟩ : syracuseStep 1201133 = 450425) (by norm_num)
theorem B3036149 : Blo 798342 3036149 := bbase (se 5 (by rfl) ⟨142319, by rfl⟩ : syracuseStep 3036149 = 284639) (by norm_num)
theorem B1201157 : Blo 798342 1201157 := bbase (se 4 (by rfl) ⟨112608, by rfl⟩ : syracuseStep 1201157 = 225217) (by norm_num)
theorem B1201181 : Blo 798342 1201181 := bbase (se 3 (by rfl) ⟨225221, by rfl⟩ : syracuseStep 1201181 = 450443) (by norm_num)
theorem B1922093 : Blo 798342 1922093 := bbase (se 3 (by rfl) ⟨360392, by rfl⟩ : syracuseStep 1922093 = 720785) (by norm_num)
theorem B1201205 : Blo 798342 1201205 := bbase (se 5 (by rfl) ⟨56306, by rfl⟩ : syracuseStep 1201205 = 112613) (by norm_num)
theorem B1201229 : Blo 798342 1201229 := bbase (se 3 (by rfl) ⟨225230, by rfl⟩ : syracuseStep 1201229 = 450461) (by norm_num)
theorem B1201253 : Blo 798342 1201253 := bbase (se 4 (by rfl) ⟨112617, by rfl⟩ : syracuseStep 1201253 = 225235) (by norm_num)
theorem B1201277 : Blo 798342 1201277 := bbase (se 3 (by rfl) ⟨225239, by rfl⟩ : syracuseStep 1201277 = 450479) (by norm_num)
theorem B1201301 : Blo 798342 1201301 := bbase (se 6 (by rfl) ⟨28155, by rfl⟩ : syracuseStep 1201301 = 56311) (by norm_num)
theorem B1201325 : Blo 798342 1201325 := bbase (se 3 (by rfl) ⟨225248, by rfl⟩ : syracuseStep 1201325 = 450497) (by norm_num)
theorem B1201349 : Blo 798342 1201349 := bbase (se 4 (by rfl) ⟨112626, by rfl⟩ : syracuseStep 1201349 = 225253) (by norm_num)
theorem B1201373 : Blo 798342 1201373 := bbase (se 3 (by rfl) ⟨225257, by rfl⟩ : syracuseStep 1201373 = 450515) (by norm_num)
theorem B1922285 : Blo 798342 1922285 := bbase (se 3 (by rfl) ⟨360428, by rfl⟩ : syracuseStep 1922285 = 720857) (by norm_num)
theorem B1201397 : Blo 798342 1201397 := bbase (se 5 (by rfl) ⟨56315, by rfl⟩ : syracuseStep 1201397 = 112631) (by norm_num)
theorem B1201421 : Blo 798342 1201421 := bbase (se 3 (by rfl) ⟨225266, by rfl⟩ : syracuseStep 1201421 = 450533) (by norm_num)
theorem B3036437 : Blo 798342 3036437 := bbase (se 6 (by rfl) ⟨71166, by rfl⟩ : syracuseStep 3036437 = 142333) (by norm_num)
theorem B1201445 : Blo 798342 1201445 := bbase (se 4 (by rfl) ⟨112635, by rfl⟩ : syracuseStep 1201445 = 225271) (by norm_num)
theorem B1201469 : Blo 798342 1201469 := bbase (se 3 (by rfl) ⟨225275, by rfl⟩ : syracuseStep 1201469 = 450551) (by norm_num)
theorem B1201493 : Blo 798342 1201493 := bbase (se 16 (by rfl) ⟨27, by rfl⟩ : syracuseStep 1201493 = 55) (by norm_num)
theorem B1201517 : Blo 798342 1201517 := bbase (se 3 (by rfl) ⟨225284, by rfl⟩ : syracuseStep 1201517 = 450569) (by norm_num)
theorem B1201541 : Blo 798342 1201541 := bbase (se 4 (by rfl) ⟨112644, by rfl⟩ : syracuseStep 1201541 = 225289) (by norm_num)
theorem B1201565 : Blo 798342 1201565 := bbase (se 3 (by rfl) ⟨225293, by rfl⟩ : syracuseStep 1201565 = 450587) (by norm_num)
theorem B1201589 : Blo 798342 1201589 := bbase (se 5 (by rfl) ⟨56324, by rfl⟩ : syracuseStep 1201589 = 112649) (by norm_num)
theorem B1201613 : Blo 798342 1201613 := bbase (se 3 (by rfl) ⟨225302, by rfl⟩ : syracuseStep 1201613 = 450605) (by norm_num)
theorem B1201637 : Blo 798342 1201637 := bbase (se 4 (by rfl) ⟨112653, by rfl⟩ : syracuseStep 1201637 = 225307) (by norm_num)
theorem B1201661 : Blo 798342 1201661 := bbase (se 3 (by rfl) ⟨225311, by rfl⟩ : syracuseStep 1201661 = 450623) (by norm_num)
theorem B1201685 : Blo 798342 1201685 := bbase (se 6 (by rfl) ⟨28164, by rfl⟩ : syracuseStep 1201685 = 56329) (by norm_num)
theorem B2020909 : Blo 798342 2020909 := bbase (se 3 (by rfl) ⟨378920, by rfl⟩ : syracuseStep 2020909 = 757841) (by norm_num)
theorem B1201709 : Blo 798342 1201709 := bbase (se 3 (by rfl) ⟨225320, by rfl⟩ : syracuseStep 1201709 = 450641) (by norm_num)
theorem B1201733 : Blo 798342 1201733 := bbase (se 4 (by rfl) ⟨112662, by rfl⟩ : syracuseStep 1201733 = 225325) (by norm_num)
theorem B1201757 : Blo 798342 1201757 := bbase (se 3 (by rfl) ⟨225329, by rfl⟩ : syracuseStep 1201757 = 450659) (by norm_num)
theorem B1201781 : Blo 798342 1201781 := bbase (se 5 (by rfl) ⟨56333, by rfl⟩ : syracuseStep 1201781 = 112667) (by norm_num)
theorem B1201805 : Blo 798342 1201805 := bbase (se 3 (by rfl) ⟨225338, by rfl⟩ : syracuseStep 1201805 = 450677) (by norm_num)
theorem B2021021 : Blo 798342 2021021 := bbase (se 3 (by rfl) ⟨378941, by rfl⟩ : syracuseStep 2021021 = 757883) (by norm_num)
theorem B1201829 : Blo 798342 1201829 := bbase (se 4 (by rfl) ⟨112671, by rfl⟩ : syracuseStep 1201829 = 225343) (by norm_num)
theorem B1201853 : Blo 798342 1201853 := bbase (se 3 (by rfl) ⟨225347, by rfl⟩ : syracuseStep 1201853 = 450695) (by norm_num)
theorem B1201877 : Blo 798342 1201877 := bbase (se 7 (by rfl) ⟨14084, by rfl⟩ : syracuseStep 1201877 = 28169) (by norm_num)
theorem B1201901 : Blo 798342 1201901 := bbase (se 3 (by rfl) ⟨225356, by rfl⟩ : syracuseStep 1201901 = 450713) (by norm_num)
theorem B1201925 : Blo 798342 1201925 := bbase (se 4 (by rfl) ⟨112680, by rfl⟩ : syracuseStep 1201925 = 225361) (by norm_num)
theorem B1201949 : Blo 798342 1201949 := bbase (se 3 (by rfl) ⟨225365, by rfl⟩ : syracuseStep 1201949 = 450731) (by norm_num)
theorem B1922861 : Blo 798342 1922861 := bbase (se 3 (by rfl) ⟨360536, by rfl⟩ : syracuseStep 1922861 = 721073) (by norm_num)
theorem B1201973 : Blo 798342 1201973 := bbase (se 5 (by rfl) ⟨56342, by rfl⟩ : syracuseStep 1201973 = 112685) (by norm_num)
theorem B1201997 : Blo 798342 1201997 := bbase (se 3 (by rfl) ⟨225374, by rfl⟩ : syracuseStep 1201997 = 450749) (by norm_num)
theorem B2021213 : Blo 798342 2021213 := bbase (se 3 (by rfl) ⟨378977, by rfl⟩ : syracuseStep 2021213 = 757955) (by norm_num)
theorem B1202021 : Blo 798342 1202021 := bbase (se 4 (by rfl) ⟨112689, by rfl⟩ : syracuseStep 1202021 = 225379) (by norm_num)
theorem B2283365 : Blo 798342 2283365 := bbase (se 4 (by rfl) ⟨214065, by rfl⟩ : syracuseStep 2283365 = 428131) (by norm_num)
theorem B1202045 : Blo 798342 1202045 := bbase (se 3 (by rfl) ⟨225383, by rfl⟩ : syracuseStep 1202045 = 450767) (by norm_num)
theorem B1202069 : Blo 798342 1202069 := bbase (se 6 (by rfl) ⟨28173, by rfl⟩ : syracuseStep 1202069 = 56347) (by norm_num)
theorem B1202093 : Blo 798342 1202093 := bbase (se 3 (by rfl) ⟨225392, by rfl⟩ : syracuseStep 1202093 = 450785) (by norm_num)
theorem B1202117 : Blo 798342 1202117 := bbase (se 4 (by rfl) ⟨112698, by rfl⟩ : syracuseStep 1202117 = 225397) (by norm_num)
theorem B1202141 : Blo 798342 1202141 := bbase (se 3 (by rfl) ⟨225401, by rfl⟩ : syracuseStep 1202141 = 450803) (by norm_num)
theorem B1202165 : Blo 798342 1202165 := bbase (se 5 (by rfl) ⟨56351, by rfl⟩ : syracuseStep 1202165 = 112703) (by norm_num)
theorem B1202189 : Blo 798342 1202189 := bbase (se 3 (by rfl) ⟨225410, by rfl⟩ : syracuseStep 1202189 = 450821) (by norm_num)
theorem B1202213 : Blo 798342 1202213 := bbase (se 4 (by rfl) ⟨112707, by rfl⟩ : syracuseStep 1202213 = 225415) (by norm_num)
theorem B1202237 : Blo 798342 1202237 := bbase (se 3 (by rfl) ⟨225419, by rfl⟩ : syracuseStep 1202237 = 450839) (by norm_num)
theorem B4053077 : Blo 798342 4053077 := bbase (se 8 (by rfl) ⟨23748, by rfl⟩ : syracuseStep 4053077 = 47497) (by norm_num)
theorem B1202261 : Blo 798342 1202261 := bbase (se 8 (by rfl) ⟨7044, by rfl⟩ : syracuseStep 1202261 = 14089) (by norm_num)
theorem B1202285 : Blo 798342 1202285 := bbase (se 3 (by rfl) ⟨225428, by rfl⟩ : syracuseStep 1202285 = 450857) (by norm_num)
theorem B1202309 : Blo 798342 1202309 := bbase (se 4 (by rfl) ⟨112716, by rfl⟩ : syracuseStep 1202309 = 225433) (by norm_num)
theorem B1202333 : Blo 798342 1202333 := bbase (se 3 (by rfl) ⟨225437, by rfl⟩ : syracuseStep 1202333 = 450875) (by norm_num)
theorem B1923245 : Blo 798342 1923245 := bbase (se 3 (by rfl) ⟨360608, by rfl⟩ : syracuseStep 1923245 = 721217) (by norm_num)
theorem B2021557 : Blo 798342 2021557 := bbase (se 5 (by rfl) ⟨94760, by rfl⟩ : syracuseStep 2021557 = 189521) (by norm_num)
theorem B1202357 : Blo 798342 1202357 := bbase (se 5 (by rfl) ⟨56360, by rfl⟩ : syracuseStep 1202357 = 112721) (by norm_num)
theorem B1202381 : Blo 798342 1202381 := bbase (se 3 (by rfl) ⟨225446, by rfl⟩ : syracuseStep 1202381 = 450893) (by norm_num)
theorem B1202405 : Blo 798342 1202405 := bbase (se 4 (by rfl) ⟨112725, by rfl⟩ : syracuseStep 1202405 = 225451) (by norm_num)
theorem B1202429 : Blo 798342 1202429 := bbase (se 3 (by rfl) ⟨225455, by rfl⟩ : syracuseStep 1202429 = 450911) (by norm_num)
theorem B1202453 : Blo 798342 1202453 := bbase (se 6 (by rfl) ⟨28182, by rfl⟩ : syracuseStep 1202453 = 56365) (by norm_num)
theorem B2021669 : Blo 798342 2021669 := bbase (se 4 (by rfl) ⟨189531, by rfl⟩ : syracuseStep 2021669 = 379063) (by norm_num)
theorem B1202477 : Blo 798342 1202477 := bbase (se 3 (by rfl) ⟨225464, by rfl⟩ : syracuseStep 1202477 = 450929) (by norm_num)
theorem B1202501 : Blo 798342 1202501 := bbase (se 4 (by rfl) ⟨112734, by rfl⟩ : syracuseStep 1202501 = 225469) (by norm_num)
theorem B6838613 : Blo 798342 6838613 := bbase (se 10 (by rfl) ⟨10017, by rfl⟩ : syracuseStep 6838613 = 20035) (by norm_num)
theorem B1202525 : Blo 798342 1202525 := bbase (se 3 (by rfl) ⟨225473, by rfl⟩ : syracuseStep 1202525 = 450947) (by norm_num)
theorem B1202549 : Blo 798342 1202549 := bbase (se 5 (by rfl) ⟨56369, by rfl⟩ : syracuseStep 1202549 = 112739) (by norm_num)
theorem B1202573 : Blo 798342 1202573 := bbase (se 3 (by rfl) ⟨225482, by rfl⟩ : syracuseStep 1202573 = 450965) (by norm_num)
theorem B1202597 : Blo 798342 1202597 := bbase (se 4 (by rfl) ⟨112743, by rfl⟩ : syracuseStep 1202597 = 225487) (by norm_num)
theorem B3037621 : Blo 798342 3037621 := bbase (se 5 (by rfl) ⟨142388, by rfl⟩ : syracuseStep 3037621 = 284777) (by norm_num)
theorem B1202621 : Blo 798342 1202621 := bbase (se 3 (by rfl) ⟨225491, by rfl⟩ : syracuseStep 1202621 = 450983) (by norm_num)
theorem B1202645 : Blo 798342 1202645 := bbase (se 7 (by rfl) ⟨14093, by rfl⟩ : syracuseStep 1202645 = 28187) (by norm_num)
theorem B2021861 : Blo 798342 2021861 := bbase (se 4 (by rfl) ⟨189549, by rfl⟩ : syracuseStep 2021861 = 379099) (by norm_num)
theorem B1202669 : Blo 798342 1202669 := bbase (se 3 (by rfl) ⟨225500, by rfl⟩ : syracuseStep 1202669 = 451001) (by norm_num)
theorem B1202693 : Blo 798342 1202693 := bbase (se 4 (by rfl) ⟨112752, by rfl⟩ : syracuseStep 1202693 = 225505) (by norm_num)
theorem B1202717 : Blo 798342 1202717 := bbase (se 3 (by rfl) ⟨225509, by rfl⟩ : syracuseStep 1202717 = 451019) (by norm_num)
theorem B1202741 : Blo 798342 1202741 := bbase (se 5 (by rfl) ⟨56378, by rfl⟩ : syracuseStep 1202741 = 112757) (by norm_num)
theorem B1202765 : Blo 798342 1202765 := bbase (se 3 (by rfl) ⟨225518, by rfl⟩ : syracuseStep 1202765 = 451037) (by norm_num)
theorem B6085205 : Blo 798342 6085205 := bbase (se 8 (by rfl) ⟨35655, by rfl⟩ : syracuseStep 6085205 = 71311) (by norm_num)
theorem B1202789 : Blo 798342 1202789 := bbase (se 4 (by rfl) ⟨112761, by rfl⟩ : syracuseStep 1202789 = 225523) (by norm_num)
theorem B1202813 : Blo 798342 1202813 := bbase (se 3 (by rfl) ⟨225527, by rfl⟩ : syracuseStep 1202813 = 451055) (by norm_num)
theorem B973453 : Blo 798342 973453 := bbase (se 3 (by rfl) ⟨182522, by rfl⟩ : syracuseStep 973453 = 365045) (by norm_num)
theorem B1202837 : Blo 798342 1202837 := bbase (se 6 (by rfl) ⟨28191, by rfl⟩ : syracuseStep 1202837 = 56383) (by norm_num)
theorem B1202861 : Blo 798342 1202861 := bbase (se 3 (by rfl) ⟨225536, by rfl⟩ : syracuseStep 1202861 = 451073) (by norm_num)
theorem B1202885 : Blo 798342 1202885 := bbase (se 4 (by rfl) ⟨112770, by rfl⟩ : syracuseStep 1202885 = 225541) (by norm_num)
theorem B1202909 : Blo 798342 1202909 := bbase (se 3 (by rfl) ⟨225545, by rfl⟩ : syracuseStep 1202909 = 451091) (by norm_num)
theorem B3037925 : Blo 798342 3037925 := bbase (se 4 (by rfl) ⟨284805, by rfl⟩ : syracuseStep 3037925 = 569611) (by norm_num)
theorem B1202933 : Blo 798342 1202933 := bbase (se 5 (by rfl) ⟨56387, by rfl⟩ : syracuseStep 1202933 = 112775) (by norm_num)
theorem B1202957 : Blo 798342 1202957 := bbase (se 3 (by rfl) ⟨225554, by rfl⟩ : syracuseStep 1202957 = 451109) (by norm_num)
theorem B1202981 : Blo 798342 1202981 := bbase (se 4 (by rfl) ⟨112779, by rfl⟩ : syracuseStep 1202981 = 225559) (by norm_num)
theorem B2022205 : Blo 798342 2022205 := bbase (se 3 (by rfl) ⟨379163, by rfl⟩ : syracuseStep 2022205 = 758327) (by norm_num)
theorem B1203005 : Blo 798342 1203005 := bbase (se 3 (by rfl) ⟨225563, by rfl⟩ : syracuseStep 1203005 = 451127) (by norm_num)
theorem B1203029 : Blo 798342 1203029 := bbase (se 9 (by rfl) ⟨3524, by rfl⟩ : syracuseStep 1203029 = 7049) (by norm_num)
theorem B1203053 : Blo 798342 1203053 := bbase (se 3 (by rfl) ⟨225572, by rfl⟩ : syracuseStep 1203053 = 451145) (by norm_num)
theorem B1203077 : Blo 798342 1203077 := bbase (se 4 (by rfl) ⟨112788, by rfl⟩ : syracuseStep 1203077 = 225577) (by norm_num)
theorem B1203101 : Blo 798342 1203101 := bbase (se 3 (by rfl) ⟨225581, by rfl⟩ : syracuseStep 1203101 = 451163) (by norm_num)
theorem B2022317 : Blo 798342 2022317 := bbase (se 3 (by rfl) ⟨379184, by rfl⟩ : syracuseStep 2022317 = 758369) (by norm_num)
theorem B1203125 : Blo 798342 1203125 := bbase (se 5 (by rfl) ⟨56396, by rfl⟩ : syracuseStep 1203125 = 112793) (by norm_num)
theorem B1203149 : Blo 798342 1203149 := bbase (se 3 (by rfl) ⟨225590, by rfl⟩ : syracuseStep 1203149 = 451181) (by norm_num)
theorem B1203173 : Blo 798342 1203173 := bbase (se 4 (by rfl) ⟨112797, by rfl⟩ : syracuseStep 1203173 = 225595) (by norm_num)
theorem B1203197 : Blo 798342 1203197 := bbase (se 3 (by rfl) ⟨225599, by rfl⟩ : syracuseStep 1203197 = 451199) (by norm_num)
theorem B1203221 : Blo 798342 1203221 := bbase (se 6 (by rfl) ⟨28200, by rfl⟩ : syracuseStep 1203221 = 56401) (by norm_num)
theorem B1203245 : Blo 798342 1203245 := bbase (se 3 (by rfl) ⟨225608, by rfl⟩ : syracuseStep 1203245 = 451217) (by norm_num)
theorem B1203269 : Blo 798342 1203269 := bbase (se 4 (by rfl) ⟨112806, by rfl⟩ : syracuseStep 1203269 = 225613) (by norm_num)
theorem B1203293 : Blo 798342 1203293 := bbase (se 3 (by rfl) ⟨225617, by rfl⟩ : syracuseStep 1203293 = 451235) (by norm_num)
theorem B2022509 : Blo 798342 2022509 := bbase (se 3 (by rfl) ⟨379220, by rfl⟩ : syracuseStep 2022509 = 758441) (by norm_num)
theorem B1203317 : Blo 798342 1203317 := bbase (se 5 (by rfl) ⟨56405, by rfl⟩ : syracuseStep 1203317 = 112811) (by norm_num)
theorem B1203341 : Blo 798342 1203341 := bbase (se 3 (by rfl) ⟨225626, by rfl⟩ : syracuseStep 1203341 = 451253) (by norm_num)
theorem B1367189 : Blo 798342 1367189 := bbase (se 6 (by rfl) ⟨32043, by rfl⟩ : syracuseStep 1367189 = 64087) (by norm_num)
theorem B1236125 : Blo 798342 1236125 := bbase (se 3 (by rfl) ⟨231773, by rfl⟩ : syracuseStep 1236125 = 463547) (by norm_num)
theorem B1203365 : Blo 798342 1203365 := bbase (se 4 (by rfl) ⟨112815, by rfl⟩ : syracuseStep 1203365 = 225631) (by norm_num)
theorem B1203389 : Blo 798342 1203389 := bbase (se 3 (by rfl) ⟨225635, by rfl⟩ : syracuseStep 1203389 = 451271) (by norm_num)
theorem B1203413 : Blo 798342 1203413 := bbase (se 7 (by rfl) ⟨14102, by rfl⟩ : syracuseStep 1203413 = 28205) (by norm_num)
theorem B1137901 : Blo 798342 1137901 := bbase (se 3 (by rfl) ⟨213356, by rfl⟩ : syracuseStep 1137901 = 426713) (by norm_num)
theorem B1203437 : Blo 798342 1203437 := bbase (se 3 (by rfl) ⟨225644, by rfl⟩ : syracuseStep 1203437 = 451289) (by norm_num)
theorem B1203461 : Blo 798342 1203461 := bbase (se 4 (by rfl) ⟨112824, by rfl⟩ : syracuseStep 1203461 = 225649) (by norm_num)
theorem B1203485 : Blo 798342 1203485 := bbase (se 3 (by rfl) ⟨225653, by rfl⟩ : syracuseStep 1203485 = 451307) (by norm_num)
theorem B1203509 : Blo 798342 1203509 := bbase (se 5 (by rfl) ⟨56414, by rfl⟩ : syracuseStep 1203509 = 112829) (by norm_num)
theorem B15621461 : Blo 798342 15621461 := bbase (se 11 (by rfl) ⟨11441, by rfl⟩ : syracuseStep 15621461 = 22883) (by norm_num)
theorem B4054373 : Blo 798342 4054373 := bbase (se 4 (by rfl) ⟨380097, by rfl⟩ : syracuseStep 4054373 = 760195) (by norm_num)
theorem B810425 : Blo 798342 810425 := bbase (se 2 (by rfl) ⟨303909, by rfl⟩ : syracuseStep 810425 = 607819) (by norm_num)
theorem B2022853 : Blo 798342 2022853 := bbase (se 4 (by rfl) ⟨189642, by rfl⟩ : syracuseStep 2022853 = 379285) (by norm_num)
theorem B2022965 : Blo 798342 2022965 := bbase (se 5 (by rfl) ⟨94826, by rfl⟩ : syracuseStep 2022965 = 189653) (by norm_num)
theorem B2023157 : Blo 798342 2023157 := bbase (se 5 (by rfl) ⟨94835, by rfl⟩ : syracuseStep 2023157 = 189671) (by norm_num)
theorem B810761 : Blo 798342 810761 := bbase (se 2 (by rfl) ⟨304035, by rfl⟩ : syracuseStep 810761 = 608071) (by norm_num)
theorem B1138493 : Blo 798342 1138493 := bbase (se 3 (by rfl) ⟨213467, by rfl⟩ : syracuseStep 1138493 = 426935) (by norm_num)
theorem B1138573 : Blo 798342 1138573 := bbase (se 3 (by rfl) ⟨213482, by rfl⟩ : syracuseStep 1138573 = 426965) (by norm_num)
theorem B1925005 : Blo 798342 1925005 := bbase (se 3 (by rfl) ⟨360938, by rfl⟩ : syracuseStep 1925005 = 721877) (by norm_num)
theorem B4317077 : Blo 798342 4317077 := bbase (se 6 (by rfl) ⟨101181, by rfl⟩ : syracuseStep 4317077 = 202363) (by norm_num)
theorem B974821 : Blo 798342 974821 := bbase (se 4 (by rfl) ⟨91389, by rfl⟩ : syracuseStep 974821 = 182779) (by norm_num)
theorem B1138693 : Blo 798342 1138693 := bbase (se 4 (by rfl) ⟨106752, by rfl⟩ : syracuseStep 1138693 = 213505) (by norm_num)
theorem B2023501 : Blo 798342 2023501 := bbase (se 3 (by rfl) ⟨379406, by rfl⟩ : syracuseStep 2023501 = 758813) (by norm_num)
theorem B1138789 : Blo 798342 1138789 := bbase (se 4 (by rfl) ⟨106761, by rfl⟩ : syracuseStep 1138789 = 213523) (by norm_num)
theorem B2023613 : Blo 798342 2023613 := bbase (se 3 (by rfl) ⟨379427, by rfl⟩ : syracuseStep 2023613 = 758855) (by norm_num)
theorem B8642837 : Blo 798342 8642837 := bbase (se 6 (by rfl) ⟨202566, by rfl⟩ : syracuseStep 8642837 = 405133) (by norm_num)
theorem B2023805 : Blo 798342 2023805 := bbase (se 3 (by rfl) ⟨379463, by rfl⟩ : syracuseStep 2023805 = 758927) (by norm_num)
theorem B5136853 : Blo 798342 5136853 := bbase (se 7 (by rfl) ⟨60197, by rfl⟩ : syracuseStep 5136853 = 120395) (by norm_num)
theorem B1139285 : Blo 798342 1139285 := bbase (se 8 (by rfl) ⟨6675, by rfl⟩ : syracuseStep 1139285 = 13351) (by norm_num)
theorem B4055669 : Blo 798342 4055669 := bbase (se 5 (by rfl) ⟨190109, by rfl⟩ : syracuseStep 4055669 = 380219) (by norm_num)
theorem B2024149 : Blo 798342 2024149 := bbase (se 7 (by rfl) ⟨23720, by rfl⟩ : syracuseStep 2024149 = 47441) (by norm_num)
theorem B4875029 : Blo 798342 4875029 := bbase (se 6 (by rfl) ⟨114258, by rfl⟩ : syracuseStep 4875029 = 228517) (by norm_num)
theorem B3040037 : Blo 798342 3040037 := bbase (se 4 (by rfl) ⟨285003, by rfl⟩ : syracuseStep 3040037 = 570007) (by norm_num)
theorem B2024261 : Blo 798342 2024261 := bbase (se 4 (by rfl) ⟨189774, by rfl⟩ : syracuseStep 2024261 = 379549) (by norm_num)
theorem B1926013 : Blo 798342 1926013 := bbase (se 3 (by rfl) ⟨361127, by rfl⟩ : syracuseStep 1926013 = 722255) (by norm_num)
theorem B9102293 : Blo 798342 9102293 := bbase (se 7 (by rfl) ⟨106667, by rfl⟩ : syracuseStep 9102293 = 213335) (by norm_num)
theorem B1926109 : Blo 798342 1926109 := bbase (se 3 (by rfl) ⟨361145, by rfl⟩ : syracuseStep 1926109 = 722291) (by norm_num)
theorem B2024453 : Blo 798342 2024453 := bbase (se 4 (by rfl) ⟨189792, by rfl⟩ : syracuseStep 2024453 = 379585) (by norm_num)
theorem B3040325 : Blo 798342 3040325 := bbase (se 4 (by rfl) ⟨285030, by rfl⟩ : syracuseStep 3040325 = 570061) (by norm_num)
theorem B1827917 : Blo 798342 1827917 := bbase (se 3 (by rfl) ⟨342734, by rfl⟩ : syracuseStep 1827917 = 685469) (by norm_num)
theorem B1139837 : Blo 798342 1139837 := bbase (se 3 (by rfl) ⟨213719, by rfl⟩ : syracuseStep 1139837 = 427439) (by norm_num)
theorem B3237029 : Blo 798342 3237029 := bbase (se 4 (by rfl) ⟨303471, by rfl⟩ : syracuseStep 3237029 = 606943) (by norm_num)
theorem B1729829 : Blo 798342 1729829 := bbase (se 4 (by rfl) ⟨162171, by rfl⟩ : syracuseStep 1729829 = 324343) (by norm_num)
theorem B2024797 : Blo 798342 2024797 := bbase (se 3 (by rfl) ⟨379649, by rfl⟩ : syracuseStep 2024797 = 759299) (by norm_num)
theorem B2024909 : Blo 798342 2024909 := bbase (se 3 (by rfl) ⟨379670, by rfl⟩ : syracuseStep 2024909 = 759341) (by norm_num)
theorem B1926629 : Blo 798342 1926629 := bbase (se 4 (by rfl) ⟨180621, by rfl⟩ : syracuseStep 1926629 = 361243) (by norm_num)
theorem B2025101 : Blo 798342 2025101 := bbase (se 3 (by rfl) ⟨379706, by rfl⟩ : syracuseStep 2025101 = 759413) (by norm_num)
theorem B976613 : Blo 798342 976613 := bbase (se 4 (by rfl) ⟨91557, by rfl⟩ : syracuseStep 976613 = 183115) (by norm_num)
theorem B1828645 : Blo 798342 1828645 := bbase (se 4 (by rfl) ⟨171435, by rfl⟩ : syracuseStep 1828645 = 342871) (by norm_num)
theorem B812837 : Blo 798342 812837 := bbase (se 4 (by rfl) ⟨76203, by rfl⟩ : syracuseStep 812837 = 152407) (by norm_num)
theorem B1140589 : Blo 798342 1140589 := bbase (se 3 (by rfl) ⟨213860, by rfl⟩ : syracuseStep 1140589 = 427721) (by norm_num)
theorem B4056965 : Blo 798342 4056965 := bbase (se 4 (by rfl) ⟨380340, by rfl⟩ : syracuseStep 4056965 = 760681) (by norm_num)
theorem B2025445 : Blo 798342 2025445 := bbase (se 4 (by rfl) ⟨189885, by rfl⟩ : syracuseStep 2025445 = 379771) (by norm_num)
theorem B1927157 : Blo 798342 1927157 := bbase (se 5 (by rfl) ⟨90335, by rfl⟩ : syracuseStep 1927157 = 180671) (by norm_num)
theorem B2025557 : Blo 798342 2025557 := bbase (se 8 (by rfl) ⟨11868, by rfl⟩ : syracuseStep 2025557 = 23737) (by norm_num)
theorem B1796309 : Blo 798342 1796309 := bbase (se 7 (by rfl) ⟨21050, by rfl⟩ : syracuseStep 1796309 = 42101) (by norm_num)
theorem B3041509 : Blo 798342 3041509 := bbase (se 4 (by rfl) ⟨285141, by rfl⟩ : syracuseStep 3041509 = 570283) (by norm_num)
theorem B1927397 : Blo 798342 1927397 := bbase (se 4 (by rfl) ⟨180693, by rfl⟩ : syracuseStep 1927397 = 361387) (by norm_num)
theorem B2025749 : Blo 798342 2025749 := bbase (se 6 (by rfl) ⟨47478, by rfl⟩ : syracuseStep 2025749 = 94957) (by norm_num)
theorem B1796381 : Blo 798342 1796381 := bbase (se 3 (by rfl) ⟨336821, by rfl⟩ : syracuseStep 1796381 = 673643) (by norm_num)
theorem B1796453 : Blo 798342 1796453 := bbase (se 4 (by rfl) ⟨168417, by rfl⟩ : syracuseStep 1796453 = 336835) (by norm_num)
theorem B1796525 : Blo 798342 1796525 := bbase (se 3 (by rfl) ⟨336848, by rfl⟩ : syracuseStep 1796525 = 673697) (by norm_num)
theorem B6482389 : Blo 798342 6482389 := bbase (se 7 (by rfl) ⟨75965, by rfl⟩ : syracuseStep 6482389 = 151931) (by norm_num)
theorem B1796597 : Blo 798342 1796597 := bbase (se 5 (by rfl) ⟨84215, by rfl⟩ : syracuseStep 1796597 = 168431) (by norm_num)
theorem B15362581 : Blo 798342 15362581 := bbase (se 6 (by rfl) ⟨360060, by rfl⟩ : syracuseStep 15362581 = 720121) (by norm_num)
theorem B3041813 : Blo 798342 3041813 := bbase (se 6 (by rfl) ⟨71292, by rfl⟩ : syracuseStep 3041813 = 142585) (by norm_num)
theorem B1796669 : Blo 798342 1796669 := bbase (se 3 (by rfl) ⟨336875, by rfl⟩ : syracuseStep 1796669 = 673751) (by norm_num)
theorem B2026093 : Blo 798342 2026093 := bbase (se 3 (by rfl) ⟨379892, by rfl⟩ : syracuseStep 2026093 = 759785) (by norm_num)
theorem B1796741 : Blo 798342 1796741 := bbase (se 4 (by rfl) ⟨168444, by rfl⟩ : syracuseStep 1796741 = 336889) (by norm_num)
theorem B1141381 : Blo 798342 1141381 := bbase (se 4 (by rfl) ⟨107004, by rfl⟩ : syracuseStep 1141381 = 214009) (by norm_num)
theorem B1796813 : Blo 798342 1796813 := bbase (se 3 (by rfl) ⟨336902, by rfl⟩ : syracuseStep 1796813 = 673805) (by norm_num)
theorem B2026205 : Blo 798342 2026205 := bbase (se 3 (by rfl) ⟨379913, by rfl⟩ : syracuseStep 2026205 = 759827) (by norm_num)
theorem B1796885 : Blo 798342 1796885 := bbase (se 6 (by rfl) ⟨42114, by rfl⟩ : syracuseStep 1796885 = 84229) (by norm_num)
theorem B1010485 : Blo 798342 1010485 := bbase (se 5 (by rfl) ⟨47366, by rfl⟩ : syracuseStep 1010485 = 94733) (by norm_num)
theorem B1796957 : Blo 798342 1796957 := bbase (se 3 (by rfl) ⟨336929, by rfl⟩ : syracuseStep 1796957 = 673859) (by norm_num)
theorem B2878325 : Blo 798342 2878325 := bbase (se 5 (by rfl) ⟨134921, by rfl⟩ : syracuseStep 2878325 = 269843) (by norm_num)
theorem B2026397 : Blo 798342 2026397 := bbase (se 3 (by rfl) ⟨379949, by rfl⟩ : syracuseStep 2026397 = 759899) (by norm_num)
theorem B1797029 : Blo 798342 1797029 := bbase (se 4 (by rfl) ⟨168471, by rfl⟩ : syracuseStep 1797029 = 336943) (by norm_num)
theorem B1141717 : Blo 798342 1141717 := bbase (se 7 (by rfl) ⟨13379, by rfl⟩ : syracuseStep 1141717 = 26759) (by norm_num)
theorem B1010657 : Blo 798342 1010657 := bbase (se 2 (by rfl) ⟨378996, by rfl⟩ : syracuseStep 1010657 = 757993) (by norm_num)
theorem B1797101 : Blo 798342 1797101 := bbase (se 3 (by rfl) ⟨336956, by rfl⟩ : syracuseStep 1797101 = 673913) (by norm_num)
theorem B3894293 : Blo 798342 3894293 := bbase (se 6 (by rfl) ⟨91272, by rfl⟩ : syracuseStep 3894293 = 182545) (by norm_num)
theorem B1010713 : Blo 798342 1010713 := bbase (se 2 (by rfl) ⟨379017, by rfl⟩ : syracuseStep 1010713 = 758035) (by norm_num)
theorem B1731629 : Blo 798342 1731629 := bbase (se 3 (by rfl) ⟨324680, by rfl⟩ : syracuseStep 1731629 = 649361) (by norm_num)
theorem B1797173 : Blo 798342 1797173 := bbase (se 5 (by rfl) ⟨84242, by rfl⟩ : syracuseStep 1797173 = 168485) (by norm_num)
theorem B1010809 : Blo 798342 1010809 := bbase (se 2 (by rfl) ⟨379053, by rfl⟩ : syracuseStep 1010809 = 758107) (by norm_num)
theorem B1797245 : Blo 798342 1797245 := bbase (se 3 (by rfl) ⟨336983, by rfl⟩ : syracuseStep 1797245 = 673967) (by norm_num)
theorem B4058261 : Blo 798342 4058261 := bbase (se 6 (by rfl) ⟨95115, by rfl⟩ : syracuseStep 4058261 = 190231) (by norm_num)
theorem B1141933 : Blo 798342 1141933 := bbase (se 3 (by rfl) ⟨214112, by rfl⟩ : syracuseStep 1141933 = 428225) (by norm_num)
theorem B1797317 : Blo 798342 1797317 := bbase (se 4 (by rfl) ⟨168498, by rfl⟩ : syracuseStep 1797317 = 336997) (by norm_num)
theorem B2026741 : Blo 798342 2026741 := bbase (se 5 (by rfl) ⟨95003, by rfl⟩ : syracuseStep 2026741 = 190007) (by norm_num)
theorem B1797389 : Blo 798342 1797389 := bbase (se 3 (by rfl) ⟨337010, by rfl⟩ : syracuseStep 1797389 = 674021) (by norm_num)
theorem B1010981 : Blo 798342 1010981 := bbase (se 4 (by rfl) ⟨94779, by rfl⟩ : syracuseStep 1010981 = 189559) (by norm_num)
theorem B1797461 : Blo 798342 1797461 := bbase (se 11 (by rfl) ⟨1316, by rfl⟩ : syracuseStep 1797461 = 2633) (by norm_num)
theorem B1011037 : Blo 798342 1011037 := bbase (se 3 (by rfl) ⟨189569, by rfl⟩ : syracuseStep 1011037 = 379139) (by norm_num)
theorem B2026853 : Blo 798342 2026853 := bbase (se 4 (by rfl) ⟨190017, by rfl⟩ : syracuseStep 2026853 = 380035) (by norm_num)
theorem B1797533 : Blo 798342 1797533 := bbase (se 3 (by rfl) ⟨337037, by rfl⟩ : syracuseStep 1797533 = 674075) (by norm_num)
theorem B1011133 : Blo 798342 1011133 := bbase (se 3 (by rfl) ⟨189587, by rfl⟩ : syracuseStep 1011133 = 379175) (by norm_num)
theorem B1797605 : Blo 798342 1797605 := bbase (se 4 (by rfl) ⟨168525, by rfl⟩ : syracuseStep 1797605 = 337051) (by norm_num)
theorem B2027045 : Blo 798342 2027045 := bbase (se 4 (by rfl) ⟨190035, by rfl⟩ : syracuseStep 2027045 = 380071) (by norm_num)
theorem B1142309 : Blo 798342 1142309 := bbase (se 4 (by rfl) ⟨107091, by rfl⟩ : syracuseStep 1142309 = 214183) (by norm_num)
theorem B1797677 : Blo 798342 1797677 := bbase (se 3 (by rfl) ⟨337064, by rfl⟩ : syracuseStep 1797677 = 674129) (by norm_num)
theorem B58453589 : Blo 798342 58453589 := bbase (se 8 (by rfl) ⟨342501, by rfl⟩ : syracuseStep 58453589 = 685003) (by norm_num)
theorem B1011305 : Blo 798342 1011305 := bbase (se 2 (by rfl) ⟨379239, by rfl⟩ : syracuseStep 1011305 = 758479) (by norm_num)
theorem B1797749 : Blo 798342 1797749 := bbase (se 5 (by rfl) ⟨84269, by rfl⟩ : syracuseStep 1797749 = 168539) (by norm_num)
theorem B1371773 : Blo 798342 1371773 := bbase (se 3 (by rfl) ⟨257207, by rfl⟩ : syracuseStep 1371773 = 514415) (by norm_num)
theorem B1011361 : Blo 798342 1011361 := bbase (se 2 (by rfl) ⟨379260, by rfl⟩ : syracuseStep 1011361 = 758521) (by norm_num)
theorem B1797821 : Blo 798342 1797821 := bbase (se 3 (by rfl) ⟨337091, by rfl⟩ : syracuseStep 1797821 = 674183) (by norm_num)
theorem B1011457 : Blo 798342 1011457 := bbase (se 2 (by rfl) ⟨379296, by rfl⟩ : syracuseStep 1011457 = 758593) (by norm_num)
theorem B1797893 : Blo 798342 1797893 := bbase (se 4 (by rfl) ⟨168552, by rfl⟩ : syracuseStep 1797893 = 337105) (by norm_num)
theorem B1797965 : Blo 798342 1797965 := bbase (se 3 (by rfl) ⟨337118, by rfl⟩ : syracuseStep 1797965 = 674237) (by norm_num)
theorem B2879333 : Blo 798342 2879333 := bbase (se 4 (by rfl) ⟨269937, by rfl⟩ : syracuseStep 2879333 = 539875) (by norm_num)
theorem B2027389 : Blo 798342 2027389 := bbase (se 3 (by rfl) ⟨380135, by rfl⟩ : syracuseStep 2027389 = 760271) (by norm_num)
theorem B1798037 : Blo 798342 1798037 := bbase (se 6 (by rfl) ⟨42141, by rfl⟩ : syracuseStep 1798037 = 84283) (by norm_num)
theorem B1011629 : Blo 798342 1011629 := bbase (se 3 (by rfl) ⟨189680, by rfl⟩ : syracuseStep 1011629 = 379361) (by norm_num)
theorem B1798109 : Blo 798342 1798109 := bbase (se 3 (by rfl) ⟨337145, by rfl⟩ : syracuseStep 1798109 = 674291) (by norm_num)
theorem B1011685 : Blo 798342 1011685 := bbase (se 4 (by rfl) ⟨94845, by rfl⟩ : syracuseStep 1011685 = 189691) (by norm_num)
theorem B2027501 : Blo 798342 2027501 := bbase (se 3 (by rfl) ⟨380156, by rfl⟩ : syracuseStep 2027501 = 760313) (by norm_num)
theorem B913429 : Blo 798342 913429 := bbase (se 6 (by rfl) ⟨21408, by rfl⟩ : syracuseStep 913429 = 42817) (by norm_num)
theorem B1798181 : Blo 798342 1798181 := bbase (se 4 (by rfl) ⟨168579, by rfl⟩ : syracuseStep 1798181 = 337159) (by norm_num)
theorem B1011781 : Blo 798342 1011781 := bbase (se 4 (by rfl) ⟨94854, by rfl⟩ : syracuseStep 1011781 = 189709) (by norm_num)
theorem B1798253 : Blo 798342 1798253 := bbase (se 3 (by rfl) ⟨337172, by rfl⟩ : syracuseStep 1798253 = 674345) (by norm_num)
theorem B2027693 : Blo 798342 2027693 := bbase (se 3 (by rfl) ⟨380192, by rfl⟩ : syracuseStep 2027693 = 760385) (by norm_num)
theorem B1798325 : Blo 798342 1798325 := bbase (se 5 (by rfl) ⟨84296, by rfl⟩ : syracuseStep 1798325 = 168593) (by norm_num)
theorem B1011953 : Blo 798342 1011953 := bbase (se 2 (by rfl) ⟨379482, by rfl⟩ : syracuseStep 1011953 = 758965) (by norm_num)
theorem B1798397 : Blo 798342 1798397 := bbase (se 3 (by rfl) ⟨337199, by rfl⟩ : syracuseStep 1798397 = 674399) (by norm_num)
theorem B1012009 : Blo 798342 1012009 := bbase (se 2 (by rfl) ⟨379503, by rfl⟩ : syracuseStep 1012009 = 759007) (by norm_num)
theorem B913721 : Blo 798342 913721 := bbase (se 2 (by rfl) ⟨342645, by rfl⟩ : syracuseStep 913721 = 685291) (by norm_num)
theorem B1798469 : Blo 798342 1798469 := bbase (se 4 (by rfl) ⟨168606, by rfl⟩ : syracuseStep 1798469 = 337213) (by norm_num)
theorem B1012105 : Blo 798342 1012105 := bbase (se 2 (by rfl) ⟨379539, by rfl⟩ : syracuseStep 1012105 = 759079) (by norm_num)
theorem B1798541 : Blo 798342 1798541 := bbase (se 3 (by rfl) ⟨337226, by rfl⟩ : syracuseStep 1798541 = 674453) (by norm_num)
theorem B4059557 : Blo 798342 4059557 := bbase (se 4 (by rfl) ⟨380583, by rfl⟩ : syracuseStep 4059557 = 761167) (by norm_num)
theorem B1798613 : Blo 798342 1798613 := bbase (se 7 (by rfl) ⟨21077, by rfl⟩ : syracuseStep 1798613 = 42155) (by norm_num)
theorem B913885 : Blo 798342 913885 := bbase (se 3 (by rfl) ⟨171353, by rfl⟩ : syracuseStep 913885 = 342707) (by norm_num)
theorem B2028037 : Blo 798342 2028037 := bbase (se 4 (by rfl) ⟨190128, by rfl⟩ : syracuseStep 2028037 = 380257) (by norm_num)
theorem B1798685 : Blo 798342 1798685 := bbase (se 3 (by rfl) ⟨337253, by rfl⟩ : syracuseStep 1798685 = 674507) (by norm_num)
theorem B1012277 : Blo 798342 1012277 := bbase (se 5 (by rfl) ⟨47450, by rfl⟩ : syracuseStep 1012277 = 94901) (by norm_num)
theorem B3043925 : Blo 798342 3043925 := bbase (se 8 (by rfl) ⟨17835, by rfl⟩ : syracuseStep 3043925 = 35671) (by norm_num)
theorem B1798757 : Blo 798342 1798757 := bbase (se 4 (by rfl) ⟨168633, by rfl⟩ : syracuseStep 1798757 = 337267) (by norm_num)
theorem B1012333 : Blo 798342 1012333 := bbase (se 3 (by rfl) ⟨189812, by rfl⟩ : syracuseStep 1012333 = 379625) (by norm_num)
theorem B2028149 : Blo 798342 2028149 := bbase (se 5 (by rfl) ⟨95069, by rfl⟩ : syracuseStep 2028149 = 190139) (by norm_num)
theorem B1798829 : Blo 798342 1798829 := bbase (se 3 (by rfl) ⟨337280, by rfl⟩ : syracuseStep 1798829 = 674561) (by norm_num)
theorem B1012429 : Blo 798342 1012429 := bbase (se 3 (by rfl) ⟨189830, by rfl⟩ : syracuseStep 1012429 = 379661) (by norm_num)
theorem B1798901 : Blo 798342 1798901 := bbase (se 5 (by rfl) ⟨84323, by rfl⟩ : syracuseStep 1798901 = 168647) (by norm_num)
theorem B914177 : Blo 798342 914177 := bbase (se 2 (by rfl) ⟨342816, by rfl⟩ : syracuseStep 914177 = 685633) (by norm_num)
theorem B2028341 : Blo 798342 2028341 := bbase (se 5 (by rfl) ⟨95078, by rfl⟩ : syracuseStep 2028341 = 190157) (by norm_num)
theorem B1798973 : Blo 798342 1798973 := bbase (se 3 (by rfl) ⟨337307, by rfl⟩ : syracuseStep 1798973 = 674615) (by norm_num)
theorem B3044213 : Blo 798342 3044213 := bbase (se 5 (by rfl) ⟨142697, by rfl⟩ : syracuseStep 3044213 = 285395) (by norm_num)
theorem B1012601 : Blo 798342 1012601 := bbase (se 2 (by rfl) ⟨379725, by rfl⟩ : syracuseStep 1012601 = 759451) (by norm_num)
theorem B1799045 : Blo 798342 1799045 := bbase (se 4 (by rfl) ⟨168660, by rfl⟩ : syracuseStep 1799045 = 337321) (by norm_num)
theorem B1012657 : Blo 798342 1012657 := bbase (se 2 (by rfl) ⟨379746, by rfl⟩ : syracuseStep 1012657 = 759493) (by norm_num)
theorem B1799117 : Blo 798342 1799117 := bbase (se 3 (by rfl) ⟨337334, by rfl⟩ : syracuseStep 1799117 = 674669) (by norm_num)
theorem B1012753 : Blo 798342 1012753 := bbase (se 2 (by rfl) ⟨379782, by rfl⟩ : syracuseStep 1012753 = 759565) (by norm_num)
theorem B1799189 : Blo 798342 1799189 := bbase (se 6 (by rfl) ⟨42168, by rfl⟩ : syracuseStep 1799189 = 84337) (by norm_num)
theorem B6157397 : Blo 798342 6157397 := bbase (se 8 (by rfl) ⟨36078, by rfl⟩ : syracuseStep 6157397 = 72157) (by norm_num)
theorem B1799261 : Blo 798342 1799261 := bbase (se 3 (by rfl) ⟨337361, by rfl⟩ : syracuseStep 1799261 = 674723) (by norm_num)
theorem B2028685 : Blo 798342 2028685 := bbase (se 3 (by rfl) ⟨380378, by rfl⟩ : syracuseStep 2028685 = 760757) (by norm_num)
theorem B1799333 : Blo 798342 1799333 := bbase (se 4 (by rfl) ⟨168687, by rfl⟩ : syracuseStep 1799333 = 337375) (by norm_num)
theorem B1733813 : Blo 798342 1733813 := bbase (se 5 (by rfl) ⟨81272, by rfl⟩ : syracuseStep 1733813 = 162545) (by norm_num)
theorem B1012925 : Blo 798342 1012925 := bbase (se 3 (by rfl) ⟨189923, by rfl⟩ : syracuseStep 1012925 = 379847) (by norm_num)
theorem B1799405 : Blo 798342 1799405 := bbase (se 3 (by rfl) ⟨337388, by rfl⟩ : syracuseStep 1799405 = 674777) (by norm_num)
theorem B1012981 : Blo 798342 1012981 := bbase (se 5 (by rfl) ⟨47483, by rfl⟩ : syracuseStep 1012981 = 94967) (by norm_num)
theorem B2028797 : Blo 798342 2028797 := bbase (se 3 (by rfl) ⟨380399, by rfl⟩ : syracuseStep 2028797 = 760799) (by norm_num)
theorem B1799477 : Blo 798342 1799477 := bbase (se 5 (by rfl) ⟨84350, by rfl⟩ : syracuseStep 1799477 = 168701) (by norm_num)
theorem B1013077 : Blo 798342 1013077 := bbase (se 13 (by rfl) ⟨185, by rfl⟩ : syracuseStep 1013077 = 371) (by norm_num)
theorem B1799549 : Blo 798342 1799549 := bbase (se 3 (by rfl) ⟨337415, by rfl⟩ : syracuseStep 1799549 = 674831) (by norm_num)
theorem B2028989 : Blo 798342 2028989 := bbase (se 3 (by rfl) ⟨380435, by rfl⟩ : syracuseStep 2028989 = 760871) (by norm_num)
theorem B1799621 : Blo 798342 1799621 := bbase (se 4 (by rfl) ⟨168714, by rfl⟩ : syracuseStep 1799621 = 337429) (by norm_num)
theorem B1013249 : Blo 798342 1013249 := bbase (se 2 (by rfl) ⟨379968, by rfl⟩ : syracuseStep 1013249 = 759937) (by norm_num)
theorem B1799693 : Blo 798342 1799693 := bbase (se 3 (by rfl) ⟨337442, by rfl⟩ : syracuseStep 1799693 = 674885) (by norm_num)
theorem B1013305 : Blo 798342 1013305 := bbase (se 2 (by rfl) ⟨379989, by rfl⟩ : syracuseStep 1013305 = 759979) (by norm_num)
theorem B1799765 : Blo 798342 1799765 := bbase (se 8 (by rfl) ⟨10545, by rfl⟩ : syracuseStep 1799765 = 21091) (by norm_num)
theorem B1013401 : Blo 798342 1013401 := bbase (se 2 (by rfl) ⟨380025, by rfl⟩ : syracuseStep 1013401 = 760051) (by norm_num)
theorem B1799837 : Blo 798342 1799837 := bbase (se 3 (by rfl) ⟨337469, by rfl⟩ : syracuseStep 1799837 = 674939) (by norm_num)
theorem B4060853 : Blo 798342 4060853 := bbase (se 5 (by rfl) ⟨190352, by rfl⟩ : syracuseStep 4060853 = 380705) (by norm_num)
theorem B1799909 : Blo 798342 1799909 := bbase (se 4 (by rfl) ⟨168741, by rfl⟩ : syracuseStep 1799909 = 337483) (by norm_num)
theorem B4552469 : Blo 798342 4552469 := bbase (se 6 (by rfl) ⟨106698, by rfl⟩ : syracuseStep 4552469 = 213397) (by norm_num)
theorem B2029333 : Blo 798342 2029333 := bbase (se 6 (by rfl) ⟨47562, by rfl⟩ : syracuseStep 2029333 = 95125) (by norm_num)
theorem B1799981 : Blo 798342 1799981 := bbase (se 3 (by rfl) ⟨337496, by rfl⟩ : syracuseStep 1799981 = 674993) (by norm_num)
theorem B1013573 : Blo 798342 1013573 := bbase (se 4 (by rfl) ⟨95022, by rfl⟩ : syracuseStep 1013573 = 190045) (by norm_num)
theorem B1800053 : Blo 798342 1800053 := bbase (se 5 (by rfl) ⟨84377, by rfl⟩ : syracuseStep 1800053 = 168755) (by norm_num)
theorem B1013629 : Blo 798342 1013629 := bbase (se 3 (by rfl) ⟨190055, by rfl⟩ : syracuseStep 1013629 = 380111) (by norm_num)
theorem B2029445 : Blo 798342 2029445 := bbase (se 4 (by rfl) ⟨190260, by rfl⟩ : syracuseStep 2029445 = 380521) (by norm_num)
theorem B1800125 : Blo 798342 1800125 := bbase (se 3 (by rfl) ⟨337523, by rfl⟩ : syracuseStep 1800125 = 675047) (by norm_num)
theorem B1013725 : Blo 798342 1013725 := bbase (se 3 (by rfl) ⟨190073, by rfl⟩ : syracuseStep 1013725 = 380147) (by norm_num)
theorem B1800197 : Blo 798342 1800197 := bbase (se 4 (by rfl) ⟨168768, by rfl⟩ : syracuseStep 1800197 = 337537) (by norm_num)
theorem B3045397 : Blo 798342 3045397 := bbase (se 6 (by rfl) ⟨71376, by rfl⟩ : syracuseStep 3045397 = 142753) (by norm_num)
theorem B2029637 : Blo 798342 2029637 := bbase (se 4 (by rfl) ⟨190278, by rfl⟩ : syracuseStep 2029637 = 380557) (by norm_num)
theorem B1800269 : Blo 798342 1800269 := bbase (se 3 (by rfl) ⟨337550, by rfl⟩ : syracuseStep 1800269 = 675101) (by norm_num)
theorem B1439869 : Blo 798342 1439869 := bbase (se 3 (by rfl) ⟨269975, by rfl⟩ : syracuseStep 1439869 = 539951) (by norm_num)
theorem B2881669 : Blo 798342 2881669 := bbase (se 4 (by rfl) ⟨270156, by rfl⟩ : syracuseStep 2881669 = 540313) (by norm_num)
theorem B1013897 : Blo 798342 1013897 := bbase (se 2 (by rfl) ⟨380211, by rfl⟩ : syracuseStep 1013897 = 760423) (by norm_num)
theorem B1800341 : Blo 798342 1800341 := bbase (se 6 (by rfl) ⟨42195, by rfl⟩ : syracuseStep 1800341 = 84391) (by norm_num)
theorem B1013953 : Blo 798342 1013953 := bbase (se 2 (by rfl) ⟨380232, by rfl⟩ : syracuseStep 1013953 = 760465) (by norm_num)
theorem B6846677 : Blo 798342 6846677 := bbase (se 7 (by rfl) ⟨80234, by rfl⟩ : syracuseStep 6846677 = 160469) (by norm_num)
theorem B1800413 : Blo 798342 1800413 := bbase (se 3 (by rfl) ⟨337577, by rfl⟩ : syracuseStep 1800413 = 675155) (by norm_num)
theorem B1014049 : Blo 798342 1014049 := bbase (se 2 (by rfl) ⟨380268, by rfl⟩ : syracuseStep 1014049 = 760537) (by norm_num)
theorem B1800485 : Blo 798342 1800485 := bbase (se 4 (by rfl) ⟨168795, by rfl⟩ : syracuseStep 1800485 = 337591) (by norm_num)
theorem B1538365 : Blo 798342 1538365 := bbase (se 3 (by rfl) ⟨288443, by rfl⟩ : syracuseStep 1538365 = 576887) (by norm_num)
theorem B3045701 : Blo 798342 3045701 := bbase (se 4 (by rfl) ⟨285534, by rfl⟩ : syracuseStep 3045701 = 571069) (by norm_num)
theorem B1800557 : Blo 798342 1800557 := bbase (se 3 (by rfl) ⟨337604, by rfl⟩ : syracuseStep 1800557 = 675209) (by norm_num)
theorem B2029981 : Blo 798342 2029981 := bbase (se 3 (by rfl) ⟨380621, by rfl⟩ : syracuseStep 2029981 = 761243) (by norm_num)
theorem B1800629 : Blo 798342 1800629 := bbase (se 5 (by rfl) ⟨84404, by rfl⟩ : syracuseStep 1800629 = 168809) (by norm_num)
theorem B1014221 : Blo 798342 1014221 := bbase (se 3 (by rfl) ⟨190166, by rfl⟩ : syracuseStep 1014221 = 380333) (by norm_num)
theorem B1800701 : Blo 798342 1800701 := bbase (se 3 (by rfl) ⟨337631, by rfl⟩ : syracuseStep 1800701 = 675263) (by norm_num)
theorem B1014277 : Blo 798342 1014277 := bbase (se 4 (by rfl) ⟨95088, by rfl⟩ : syracuseStep 1014277 = 190177) (by norm_num)
theorem B2030093 : Blo 798342 2030093 := bbase (se 3 (by rfl) ⟨380642, by rfl⟩ : syracuseStep 2030093 = 761285) (by norm_num)
theorem B1440301 : Blo 798342 1440301 := bbase (se 3 (by rfl) ⟨270056, by rfl⟩ : syracuseStep 1440301 = 540113) (by norm_num)
theorem B1800773 : Blo 798342 1800773 := bbase (se 4 (by rfl) ⟨168822, by rfl⟩ : syracuseStep 1800773 = 337645) (by norm_num)
theorem B1014373 : Blo 798342 1014373 := bbase (se 4 (by rfl) ⟨95097, by rfl⟩ : syracuseStep 1014373 = 190195) (by norm_num)
theorem B1800845 : Blo 798342 1800845 := bbase (se 3 (by rfl) ⟨337658, by rfl⟩ : syracuseStep 1800845 = 675317) (by norm_num)
theorem B5765813 : Blo 798342 5765813 := bbase (se 5 (by rfl) ⟨270272, by rfl⟩ : syracuseStep 5765813 = 540545) (by norm_num)
theorem B1440445 : Blo 798342 1440445 := bbase (se 3 (by rfl) ⟨270083, by rfl⟩ : syracuseStep 1440445 = 540167) (by norm_num)
theorem B2030285 : Blo 798342 2030285 := bbase (se 3 (by rfl) ⟨380678, by rfl⟩ : syracuseStep 2030285 = 761357) (by norm_num)
theorem B1800917 : Blo 798342 1800917 := bbase (se 7 (by rfl) ⟨21104, by rfl⟩ : syracuseStep 1800917 = 42209) (by norm_num)
theorem B1014545 : Blo 798342 1014545 := bbase (se 2 (by rfl) ⟨380454, by rfl⟩ : syracuseStep 1014545 = 760909) (by norm_num)
theorem B1800989 : Blo 798342 1800989 := bbase (se 3 (by rfl) ⟨337685, by rfl⟩ : syracuseStep 1800989 = 675371) (by norm_num)
theorem B1014601 : Blo 798342 1014601 := bbase (se 2 (by rfl) ⟨380475, by rfl⟩ : syracuseStep 1014601 = 760951) (by norm_num)
theorem B1801061 : Blo 798342 1801061 := bbase (se 4 (by rfl) ⟨168849, by rfl⟩ : syracuseStep 1801061 = 337699) (by norm_num)
theorem B1440661 : Blo 798342 1440661 := bbase (se 6 (by rfl) ⟨33765, by rfl⟩ : syracuseStep 1440661 = 67531) (by norm_num)
theorem B1014697 : Blo 798342 1014697 := bbase (se 2 (by rfl) ⟨380511, by rfl⟩ : syracuseStep 1014697 = 761023) (by norm_num)
theorem B1801133 : Blo 798342 1801133 := bbase (se 3 (by rfl) ⟨337712, by rfl⟩ : syracuseStep 1801133 = 675425) (by norm_num)
theorem B1801205 : Blo 798342 1801205 := bbase (se 5 (by rfl) ⟨84431, by rfl⟩ : syracuseStep 1801205 = 168863) (by norm_num)
theorem B2030629 : Blo 798342 2030629 := bbase (se 4 (by rfl) ⟨190371, by rfl⟩ : syracuseStep 2030629 = 380743) (by norm_num)
theorem B1801277 : Blo 798342 1801277 := bbase (se 3 (by rfl) ⟨337739, by rfl⟩ : syracuseStep 1801277 = 675479) (by norm_num)
theorem B1014869 : Blo 798342 1014869 := bbase (se 8 (by rfl) ⟨5946, by rfl⟩ : syracuseStep 1014869 = 11893) (by norm_num)
theorem B1801349 : Blo 798342 1801349 := bbase (se 4 (by rfl) ⟨168876, by rfl⟩ : syracuseStep 1801349 = 337753) (by norm_num)
theorem B1014925 : Blo 798342 1014925 := bbase (se 3 (by rfl) ⟨190298, by rfl⟩ : syracuseStep 1014925 = 380597) (by norm_num)
theorem B2030741 : Blo 798342 2030741 := bbase (se 6 (by rfl) ⟨47595, by rfl⟩ : syracuseStep 2030741 = 95191) (by norm_num)
theorem B1801421 : Blo 798342 1801421 := bbase (se 3 (by rfl) ⟨337766, by rfl⟩ : syracuseStep 1801421 = 675533) (by norm_num)
theorem B1015021 : Blo 798342 1015021 := bbase (se 3 (by rfl) ⟨190316, by rfl⟩ : syracuseStep 1015021 = 380633) (by norm_num)
theorem B1801493 : Blo 798342 1801493 := bbase (se 6 (by rfl) ⟨42222, by rfl⟩ : syracuseStep 1801493 = 84445) (by norm_num)
theorem B1801565 : Blo 798342 1801565 := bbase (se 3 (by rfl) ⟨337793, by rfl⟩ : syracuseStep 1801565 = 675587) (by norm_num)
theorem B1015193 : Blo 798342 1015193 := bbase (se 2 (by rfl) ⟨380697, by rfl⟩ : syracuseStep 1015193 = 761395) (by norm_num)
theorem B1801637 : Blo 798342 1801637 := bbase (se 4 (by rfl) ⟨168903, by rfl⟩ : syracuseStep 1801637 = 337807) (by norm_num)
theorem B1015249 : Blo 798342 1015249 := bbase (se 2 (by rfl) ⟨380718, by rfl⟩ : syracuseStep 1015249 = 761437) (by norm_num)
theorem B1441253 : Blo 798342 1441253 := bbase (se 4 (by rfl) ⟨135117, by rfl⟩ : syracuseStep 1441253 = 270235) (by norm_num)
theorem B1801709 : Blo 798342 1801709 := bbase (se 3 (by rfl) ⟨337820, by rfl⟩ : syracuseStep 1801709 = 675641) (by norm_num)
theorem B1015345 : Blo 798342 1015345 := bbase (se 2 (by rfl) ⟨380754, by rfl⟩ : syracuseStep 1015345 = 761509) (by norm_num)
theorem B5766709 : Blo 798342 5766709 := bbase (se 5 (by rfl) ⟨270314, by rfl⟩ : syracuseStep 5766709 = 540629) (by norm_num)
theorem B1801781 : Blo 798342 1801781 := bbase (se 5 (by rfl) ⟨84458, by rfl⟩ : syracuseStep 1801781 = 168917) (by norm_num)
theorem B1801853 : Blo 798342 1801853 := bbase (se 3 (by rfl) ⟨337847, by rfl⟩ : syracuseStep 1801853 = 675695) (by norm_num)
theorem B1539733 : Blo 798342 1539733 := bbase (se 6 (by rfl) ⟨36087, by rfl⟩ : syracuseStep 1539733 = 72175) (by norm_num)
theorem B1441469 : Blo 798342 1441469 := bbase (se 3 (by rfl) ⟨270275, by rfl⟩ : syracuseStep 1441469 = 540551) (by norm_num)
theorem B1801925 : Blo 798342 1801925 := bbase (se 4 (by rfl) ⟨168930, by rfl⟩ : syracuseStep 1801925 = 337861) (by norm_num)
theorem B1801997 : Blo 798342 1801997 := bbase (se 3 (by rfl) ⟨337874, by rfl⟩ : syracuseStep 1801997 = 675749) (by norm_num)
theorem B1802069 : Blo 798342 1802069 := bbase (se 9 (by rfl) ⟨5279, by rfl⟩ : syracuseStep 1802069 = 10559) (by norm_num)
theorem B1539965 : Blo 798342 1539965 := bbase (se 3 (by rfl) ⟨288743, by rfl⟩ : syracuseStep 1539965 = 577487) (by norm_num)
theorem B1802141 : Blo 798342 1802141 := bbase (se 3 (by rfl) ⟨337901, by rfl⟩ : syracuseStep 1802141 = 675803) (by norm_num)
theorem B1441757 : Blo 798342 1441757 := bbase (se 3 (by rfl) ⟨270329, by rfl⟩ : syracuseStep 1441757 = 540659) (by norm_num)
theorem B1802213 : Blo 798342 1802213 := bbase (se 4 (by rfl) ⟨168957, by rfl⟩ : syracuseStep 1802213 = 337915) (by norm_num)
theorem B1802321 : Blo 798342 1802321 := bstep (se 2 (by rfl) ⟨675870, by rfl⟩ : syracuseStep 1802321 = 1351741) B1351741
theorem B10256483 : Blo 798342 10256483 := bstep (se 1 (by rfl) ⟨7692362, by rfl⟩ : syracuseStep 10256483 = 15384725) B15384725
theorem B1802339 : Blo 798342 1802339 := bstep (se 1 (by rfl) ⟨1351754, by rfl⟩ : syracuseStep 1802339 = 2703509) B2703509
theorem B1081523 : Blo 798342 1081523 := bstep (se 1 (by rfl) ⟨811142, by rfl⟩ : syracuseStep 1081523 = 1622285) B1622285
theorem B1802609 : Blo 798342 1802609 := bstep (se 2 (by rfl) ⟨675978, by rfl⟩ : syracuseStep 1802609 = 1351957) B1351957
theorem B1802627 : Blo 798342 1802627 := bstep (se 1 (by rfl) ⟨1351970, by rfl⟩ : syracuseStep 1802627 = 2703941) B2703941
theorem B852563 : Blo 798342 852563 := bstep (se 1 (by rfl) ⟨639422, by rfl⟩ : syracuseStep 852563 = 1278845) B1278845
theorem B14615153 : Blo 798342 14615153 := bstep (se 2 (by rfl) ⟨5480682, by rfl⟩ : syracuseStep 14615153 = 10961365) B10961365
theorem B6849137 : Blo 798342 6849137 := bstep (se 2 (by rfl) ⟨2568426, by rfl⟩ : syracuseStep 6849137 = 5136853) B5136853
theorem B1802897 : Blo 798342 1802897 := bstep (se 2 (by rfl) ⟨676086, by rfl⟩ : syracuseStep 1802897 = 1352173) B1352173
theorem B1802915 : Blo 798342 1802915 := bstep (se 1 (by rfl) ⟨1352186, by rfl⟩ : syracuseStep 1802915 = 2704373) B2704373
theorem B852691 : Blo 798342 852691 := bstep (se 1 (by rfl) ⟨639518, by rfl⟩ : syracuseStep 852691 = 1279037) B1279037
theorem B1803185 : Blo 798342 1803185 := bstep (se 2 (by rfl) ⟨676194, by rfl⟩ : syracuseStep 1803185 = 1352389) B1352389
theorem B1803203 : Blo 798342 1803203 := bstep (se 1 (by rfl) ⟨1352402, by rfl⟩ : syracuseStep 1803203 = 2704805) B2704805
theorem B1278947 : Blo 798342 1278947 := bstep (se 1 (by rfl) ⟨959210, by rfl⟩ : syracuseStep 1278947 = 1918421) B1918421
theorem B1803473 : Blo 798342 1803473 := bstep (se 2 (by rfl) ⟨676302, by rfl⟩ : syracuseStep 1803473 = 1352605) B1352605
theorem B1803491 : Blo 798342 1803491 := bstep (se 1 (by rfl) ⟨1352618, by rfl⟩ : syracuseStep 1803491 = 2705237) B2705237
theorem B9733517 : Blo 798342 9733517 := bstep (se 3 (by rfl) ⟨1825034, by rfl⟩ : syracuseStep 9733517 = 3650069) B3650069
theorem B1803761 : Blo 798342 1803761 := bstep (se 2 (by rfl) ⟨676410, by rfl⟩ : syracuseStep 1803761 = 1352821) B1352821
theorem B853507 : Blo 798342 853507 := bstep (se 1 (by rfl) ⟨640130, by rfl⟩ : syracuseStep 853507 = 1280261) B1280261
theorem B1803779 : Blo 798342 1803779 := bstep (se 1 (by rfl) ⟨1352834, by rfl⟩ : syracuseStep 1803779 = 2705669) B2705669
theorem B4687409 : Blo 798342 4687409 := bstep (se 2 (by rfl) ⟨1757778, by rfl⟩ : syracuseStep 4687409 = 3515557) B3515557
theorem B1705553 : Blo 798342 1705553 := bstep (se 2 (by rfl) ⟨639582, by rfl⟩ : syracuseStep 1705553 = 1279165) B1279165
theorem B1443523 : Blo 798342 1443523 := bstep (se 1 (by rfl) ⟨1082642, by rfl⟩ : syracuseStep 1443523 = 2165285) B2165285
theorem B1279729 : Blo 798342 1279729 := bstep (se 2 (by rfl) ⟨479898, by rfl⟩ : syracuseStep 1279729 = 959797) B959797
theorem B1443587 : Blo 798342 1443587 := bstep (se 1 (by rfl) ⟨1082690, by rfl⟩ : syracuseStep 1443587 = 2165381) B2165381
theorem B1804049 : Blo 798342 1804049 := bstep (se 2 (by rfl) ⟨676518, by rfl⟩ : syracuseStep 1804049 = 1353037) B1353037
theorem B1804067 : Blo 798342 1804067 := bstep (se 1 (by rfl) ⟨1353050, by rfl⟩ : syracuseStep 1804067 = 2706101) B2706101
theorem B1804337 : Blo 798342 1804337 := bstep (se 2 (by rfl) ⟨676626, by rfl⟩ : syracuseStep 1804337 = 1353253) B1353253
theorem B1804355 : Blo 798342 1804355 := bstep (se 1 (by rfl) ⟨1353266, by rfl⟩ : syracuseStep 1804355 = 2706533) B2706533
theorem B35063921 : Blo 798342 35063921 := bstep (se 2 (by rfl) ⟨13148970, by rfl⟩ : syracuseStep 35063921 = 26297941) B26297941
theorem B17303665 : Blo 798342 17303665 := bstep (se 2 (by rfl) ⟨6488874, by rfl⟩ : syracuseStep 17303665 = 12977749) B12977749
theorem B1804625 : Blo 798342 1804625 := bstep (se 2 (by rfl) ⟨676734, by rfl⟩ : syracuseStep 1804625 = 1353469) B1353469
theorem B1706339 : Blo 798342 1706339 := bstep (se 1 (by rfl) ⟨1279754, by rfl⟩ : syracuseStep 1706339 = 2559509) B2559509
theorem B1804643 : Blo 798342 1804643 := bstep (se 1 (by rfl) ⟨1353482, by rfl⟩ : syracuseStep 1804643 = 2706965) B2706965
theorem B2165123 : Blo 798342 2165123 := bstep (se 1 (by rfl) ⟨1623842, by rfl⟩ : syracuseStep 2165123 = 3247685) B3247685
theorem B3410353 : Blo 798342 3410353 := bstep (se 2 (by rfl) ⟨1278882, by rfl⟩ : syracuseStep 3410353 = 2557765) B2557765
theorem B16452067 : Blo 798342 16452067 := bstep (se 1 (by rfl) ⟨12339050, by rfl⟩ : syracuseStep 16452067 = 24678101) B24678101
theorem B1215059 : Blo 798342 1215059 := bstep (se 1 (by rfl) ⟨911294, by rfl⟩ : syracuseStep 1215059 = 1822589) B1822589
theorem B1804913 : Blo 798342 1804913 := bstep (se 2 (by rfl) ⟨676842, by rfl⟩ : syracuseStep 1804913 = 1353685) B1353685
theorem B1804931 : Blo 798342 1804931 := bstep (se 1 (by rfl) ⟨1353698, by rfl⟩ : syracuseStep 1804931 = 2707397) B2707397
theorem B4557617 : Blo 798342 4557617 := bstep (se 2 (by rfl) ⟨1709106, by rfl⟩ : syracuseStep 4557617 = 3418213) B3418213
theorem B1805201 : Blo 798342 1805201 := bstep (se 2 (by rfl) ⟨676950, by rfl⟩ : syracuseStep 1805201 = 1353901) B1353901
theorem B1805219 : Blo 798342 1805219 := bstep (se 1 (by rfl) ⟨1353914, by rfl⟩ : syracuseStep 1805219 = 2707829) B2707829
theorem B2558893 : Blo 798342 2558893 := bstep (se 3 (by rfl) ⟨479792, by rfl⟩ : syracuseStep 2558893 = 959585) B959585
theorem B1707313 : Blo 798342 1707313 := bstep (se 2 (by rfl) ⟨640242, by rfl⟩ : syracuseStep 1707313 = 1280485) B1280485
theorem B20483441 : Blo 798342 20483441 := bstep (se 2 (by rfl) ⟨7681290, by rfl⟩ : syracuseStep 20483441 = 15362581) B15362581
theorem B1281395 : Blo 798342 1281395 := bstep (se 1 (by rfl) ⟨961046, by rfl⟩ : syracuseStep 1281395 = 1922093) B1922093
theorem B5475761 : Blo 798342 5475761 := bstep (se 2 (by rfl) ⟨2053410, by rfl⟩ : syracuseStep 5475761 = 4106821) B4106821
theorem B1281523 : Blo 798342 1281523 := bstep (se 1 (by rfl) ⟨961142, by rfl⟩ : syracuseStep 1281523 = 1922285) B1922285
theorem B1707569 : Blo 798342 1707569 := bstep (se 2 (by rfl) ⟨640338, by rfl⟩ : syracuseStep 1707569 = 1280677) B1280677
theorem B1347313 : Blo 798342 1347313 := bstep (se 2 (by rfl) ⟨505242, by rfl⟩ : syracuseStep 1347313 = 1010485) B1010485
theorem B1347347 : Blo 798342 1347347 := bstep (se 1 (by rfl) ⟨1010510, by rfl⟩ : syracuseStep 1347347 = 2021021) B2021021
theorem B11702069 : Blo 798342 11702069 := bstep (se 5 (by rfl) ⟨548534, by rfl⟩ : syracuseStep 11702069 = 1097069) B1097069
theorem B1281907 : Blo 798342 1281907 := bstep (se 1 (by rfl) ⟨961430, by rfl⟩ : syracuseStep 1281907 = 1922861) B1922861
theorem B1347475 : Blo 798342 1347475 := bstep (se 1 (by rfl) ⟨1010606, by rfl⟩ : syracuseStep 1347475 = 2021213) B2021213
theorem B1347617 : Blo 798342 1347617 := bstep (se 2 (by rfl) ⟨505356, by rfl⟩ : syracuseStep 1347617 = 1010713) B1010713
theorem B1282163 : Blo 798342 1282163 := bstep (se 1 (by rfl) ⟨961622, by rfl⟩ : syracuseStep 1282163 = 1923245) B1923245
theorem B1347745 : Blo 798342 1347745 := bstep (se 2 (by rfl) ⟨505404, by rfl⟩ : syracuseStep 1347745 = 1010809) B1010809
theorem B1347779 : Blo 798342 1347779 := bstep (se 1 (by rfl) ⟨1010834, by rfl⟩ : syracuseStep 1347779 = 2021669) B2021669
theorem B5836997 : Blo 798342 5836997 := bstep (se 4 (by rfl) ⟨547218, by rfl⟩ : syracuseStep 5836997 = 1094437) B1094437
theorem B3248333 : Blo 798342 3248333 := bstep (se 3 (by rfl) ⟨609062, by rfl⟩ : syracuseStep 3248333 = 1218125) B1218125
theorem B4559075 : Blo 798342 4559075 := bstep (se 1 (by rfl) ⟨3419306, by rfl⟩ : syracuseStep 4559075 = 6838613) B6838613
theorem B1347907 : Blo 798342 1347907 := bstep (se 1 (by rfl) ⟨1010930, by rfl⟩ : syracuseStep 1347907 = 2021861) B2021861
theorem B2560355 : Blo 798342 2560355 := bstep (se 1 (by rfl) ⟨1920266, by rfl⟩ : syracuseStep 2560355 = 3840533) B3840533
theorem B13668749 : Blo 798342 13668749 := bstep (se 3 (by rfl) ⟨2562890, by rfl⟩ : syracuseStep 13668749 = 5125781) B5125781
theorem B1348049 : Blo 798342 1348049 := bstep (se 2 (by rfl) ⟨505518, by rfl⟩ : syracuseStep 1348049 = 1011037) B1011037
theorem B1282625 : Blo 798342 1282625 := bstep (se 2 (by rfl) ⟨480984, by rfl⟩ : syracuseStep 1282625 = 961969) B961969
theorem B1348177 : Blo 798342 1348177 := bstep (se 2 (by rfl) ⟨505566, by rfl⟩ : syracuseStep 1348177 = 1011133) B1011133
theorem B1348211 : Blo 798342 1348211 := bstep (se 1 (by rfl) ⟨1011158, by rfl⟩ : syracuseStep 1348211 = 2022317) B2022317
theorem B1282721 : Blo 798342 1282721 := bstep (se 2 (by rfl) ⟨481020, by rfl⟩ : syracuseStep 1282721 = 962041) B962041
theorem B1282753 : Blo 798342 1282753 := bstep (se 2 (by rfl) ⟨481032, by rfl⟩ : syracuseStep 1282753 = 962065) B962065
theorem B1348339 : Blo 798342 1348339 := bstep (se 1 (by rfl) ⟨1011254, by rfl⟩ : syracuseStep 1348339 = 2022509) B2022509
theorem B2167565 : Blo 798342 2167565 := bstep (se 3 (by rfl) ⟨406418, by rfl⟩ : syracuseStep 2167565 = 812837) B812837
theorem B1708867 : Blo 798342 1708867 := bstep (se 1 (by rfl) ⟨1281650, by rfl⟩ : syracuseStep 1708867 = 2563301) B2563301
theorem B1348481 : Blo 798342 1348481 := bstep (se 2 (by rfl) ⟨505680, by rfl⟩ : syracuseStep 1348481 = 1011361) B1011361
theorem B1348609 : Blo 798342 1348609 := bstep (se 2 (by rfl) ⟨505728, by rfl⟩ : syracuseStep 1348609 = 1011457) B1011457
theorem B1348643 : Blo 798342 1348643 := bstep (se 1 (by rfl) ⟨1011482, by rfl⟩ : syracuseStep 1348643 = 2022965) B2022965
theorem B1709201 : Blo 798342 1709201 := bstep (se 2 (by rfl) ⟨640950, by rfl⟩ : syracuseStep 1709201 = 1281901) B1281901
theorem B1348771 : Blo 798342 1348771 := bstep (se 1 (by rfl) ⟨1011578, by rfl⟩ : syracuseStep 1348771 = 2023157) B2023157
theorem B4560077 : Blo 798342 4560077 := bstep (se 3 (by rfl) ⟨855014, by rfl⟩ : syracuseStep 4560077 = 1710029) B1710029
theorem B1348913 : Blo 798342 1348913 := bstep (se 2 (by rfl) ⟨505842, by rfl⟩ : syracuseStep 1348913 = 1011685) B1011685
theorem B7804259 : Blo 798342 7804259 := bstep (se 1 (by rfl) ⟨5853194, by rfl⟩ : syracuseStep 7804259 = 11706389) B11706389
theorem B1217905 : Blo 798342 1217905 := bstep (se 2 (by rfl) ⟨456714, by rfl⟩ : syracuseStep 1217905 = 913429) B913429
theorem B1349041 : Blo 798342 1349041 := bstep (se 2 (by rfl) ⟨505890, by rfl⟩ : syracuseStep 1349041 = 1011781) B1011781
theorem B1349075 : Blo 798342 1349075 := bstep (se 1 (by rfl) ⟨1011806, by rfl⟩ : syracuseStep 1349075 = 2023613) B2023613
theorem B4330979 : Blo 798342 4330979 := bstep (se 1 (by rfl) ⟨3248234, by rfl⟩ : syracuseStep 4330979 = 6496469) B6496469
theorem B1349203 : Blo 798342 1349203 := bstep (se 1 (by rfl) ⟨1011902, by rfl⟩ : syracuseStep 1349203 = 2023805) B2023805
theorem B1349345 : Blo 798342 1349345 := bstep (se 2 (by rfl) ⟨506004, by rfl⟩ : syracuseStep 1349345 = 1012009) B1012009
theorem B4855565 : Blo 798342 4855565 := bstep (se 3 (by rfl) ⟨910418, by rfl⟩ : syracuseStep 4855565 = 1820837) B1820837
theorem B1349473 : Blo 798342 1349473 := bstep (se 2 (by rfl) ⟨506052, by rfl⟩ : syracuseStep 1349473 = 1012105) B1012105
theorem B3250019 : Blo 798342 3250019 := bstep (se 1 (by rfl) ⟨2437514, by rfl⟩ : syracuseStep 3250019 = 4875029) B4875029
theorem B1349507 : Blo 798342 1349507 := bstep (se 1 (by rfl) ⟨1012130, by rfl⟩ : syracuseStep 1349507 = 2024261) B2024261
theorem B2561969 : Blo 798342 2561969 := bstep (se 2 (by rfl) ⟨960738, by rfl⟩ : syracuseStep 2561969 = 1921477) B1921477
theorem B6068195 : Blo 798342 6068195 := bstep (se 1 (by rfl) ⟨4551146, by rfl⟩ : syracuseStep 6068195 = 9102293) B9102293
theorem B1349635 : Blo 798342 1349635 := bstep (se 1 (by rfl) ⟨1012226, by rfl⟩ : syracuseStep 1349635 = 2024453) B2024453
theorem B1218611 : Blo 798342 1218611 := bstep (se 1 (by rfl) ⟨913958, by rfl⟩ : syracuseStep 1218611 = 1827917) B1827917
theorem B1153121 : Blo 798342 1153121 := bstep (se 2 (by rfl) ⟨432420, by rfl⟩ : syracuseStep 1153121 = 864841) B864841
theorem B2889827 : Blo 798342 2889827 := bstep (se 1 (by rfl) ⟨2167370, by rfl⟩ : syracuseStep 2889827 = 4334741) B4334741
theorem B1349777 : Blo 798342 1349777 := bstep (se 2 (by rfl) ⟨506166, by rfl⟩ : syracuseStep 1349777 = 1012333) B1012333
theorem B2431139 : Blo 798342 2431139 := bstep (se 1 (by rfl) ⟨1823354, by rfl⟩ : syracuseStep 2431139 = 3646709) B3646709
theorem B1153219 : Blo 798342 1153219 := bstep (se 1 (by rfl) ⟨864914, by rfl⟩ : syracuseStep 1153219 = 1729829) B1729829
theorem B1349905 : Blo 798342 1349905 := bstep (se 2 (by rfl) ⟨506214, by rfl⟩ : syracuseStep 1349905 = 1012429) B1012429
theorem B1710371 : Blo 798342 1710371 := bstep (se 1 (by rfl) ⟨1282778, by rfl⟩ : syracuseStep 1710371 = 2565557) B2565557
theorem B1349939 : Blo 798342 1349939 := bstep (se 1 (by rfl) ⟨1012454, by rfl⟩ : syracuseStep 1349939 = 2024909) B2024909
theorem B1284419 : Blo 798342 1284419 := bstep (se 1 (by rfl) ⟨963314, by rfl⟩ : syracuseStep 1284419 = 1926629) B1926629
theorem B1350067 : Blo 798342 1350067 := bstep (se 1 (by rfl) ⟨1012550, by rfl⟩ : syracuseStep 1350067 = 2025101) B2025101
theorem B2431505 : Blo 798342 2431505 := bstep (se 2 (by rfl) ⟨911814, by rfl⟩ : syracuseStep 2431505 = 1823629) B1823629
theorem B1350209 : Blo 798342 1350209 := bstep (se 2 (by rfl) ⟨506328, by rfl⟩ : syracuseStep 1350209 = 1012657) B1012657
theorem B1350337 : Blo 798342 1350337 := bstep (se 2 (by rfl) ⟨506376, by rfl⟩ : syracuseStep 1350337 = 1012753) B1012753
theorem B1350371 : Blo 798342 1350371 := bstep (se 1 (by rfl) ⟨1012778, by rfl⟩ : syracuseStep 1350371 = 2025557) B2025557
theorem B4922117 : Blo 798342 4922117 := bstep (se 4 (by rfl) ⟨461448, by rfl⟩ : syracuseStep 4922117 = 922897) B922897
theorem B3414797 : Blo 798342 3414797 := bstep (se 3 (by rfl) ⟨640274, by rfl⟩ : syracuseStep 3414797 = 1280549) B1280549
theorem B1284931 : Blo 798342 1284931 := bstep (se 1 (by rfl) ⟨963698, by rfl⟩ : syracuseStep 1284931 = 1927397) B1927397
theorem B4332365 : Blo 798342 4332365 := bstep (se 3 (by rfl) ⟨812318, by rfl⟩ : syracuseStep 4332365 = 1624637) B1624637
theorem B1350499 : Blo 798342 1350499 := bstep (se 1 (by rfl) ⟨1012874, by rfl⟩ : syracuseStep 1350499 = 2025749) B2025749
theorem B1284977 : Blo 798342 1284977 := bstep (se 2 (by rfl) ⟨481866, by rfl⟩ : syracuseStep 1284977 = 963733) B963733
theorem B1350641 : Blo 798342 1350641 := bstep (se 2 (by rfl) ⟨506490, by rfl⟩ : syracuseStep 1350641 = 1012981) B1012981
theorem B1350769 : Blo 798342 1350769 := bstep (se 2 (by rfl) ⟨506538, by rfl⟩ : syracuseStep 1350769 = 1013077) B1013077
theorem B2890865 : Blo 798342 2890865 := bstep (se 2 (by rfl) ⟨1084074, by rfl⟩ : syracuseStep 2890865 = 2168149) B2168149
theorem B1350803 : Blo 798342 1350803 := bstep (se 1 (by rfl) ⟨1013102, by rfl⟩ : syracuseStep 1350803 = 2026205) B2026205
theorem B1350931 : Blo 798342 1350931 := bstep (se 1 (by rfl) ⟨1013198, by rfl⟩ : syracuseStep 1350931 = 2026397) B2026397
theorem B2596195 : Blo 798342 2596195 := bstep (se 1 (by rfl) ⟨1947146, by rfl⟩ : syracuseStep 2596195 = 3894293) B3894293
theorem B1154419 : Blo 798342 1154419 := bstep (se 1 (by rfl) ⟨865814, by rfl⟩ : syracuseStep 1154419 = 1731629) B1731629
theorem B2694545 : Blo 798342 2694545 := bstep (se 2 (by rfl) ⟨1010454, by rfl⟩ : syracuseStep 2694545 = 2020909) B2020909
theorem B1351073 : Blo 798342 1351073 := bstep (se 2 (by rfl) ⟨506652, by rfl⟩ : syracuseStep 1351073 = 1013305) B1013305
theorem B1351201 : Blo 798342 1351201 := bstep (se 2 (by rfl) ⟨506700, by rfl⟩ : syracuseStep 1351201 = 1013401) B1013401
theorem B1351235 : Blo 798342 1351235 := bstep (se 1 (by rfl) ⟨1013426, by rfl⟩ : syracuseStep 1351235 = 2026853) B2026853
theorem B1351363 : Blo 798342 1351363 := bstep (se 1 (by rfl) ⟨1013522, by rfl⟩ : syracuseStep 1351363 = 2027045) B2027045
theorem B5119685 : Blo 798342 5119685 := bstep (se 4 (by rfl) ⟨479970, by rfl⟩ : syracuseStep 5119685 = 959941) B959941
theorem B38969059 : Blo 798342 38969059 := bstep (se 1 (by rfl) ⟨29226794, by rfl⟩ : syracuseStep 38969059 = 58453589) B58453589
theorem B1351505 : Blo 798342 1351505 := bstep (se 2 (by rfl) ⟨506814, by rfl⟩ : syracuseStep 1351505 = 1013629) B1013629
theorem B2695085 : Blo 798342 2695085 := bstep (se 3 (by rfl) ⟨505328, by rfl⟩ : syracuseStep 2695085 = 1010657) B1010657
theorem B2564045 : Blo 798342 2564045 := bstep (se 3 (by rfl) ⟨480758, by rfl⟩ : syracuseStep 2564045 = 961517) B961517
theorem B1351633 : Blo 798342 1351633 := bstep (se 2 (by rfl) ⟨506862, by rfl⟩ : syracuseStep 1351633 = 1013725) B1013725
theorem B2695139 : Blo 798342 2695139 := bstep (se 1 (by rfl) ⟨2021354, by rfl⟩ : syracuseStep 2695139 = 4042709) B4042709
theorem B1351667 : Blo 798342 1351667 := bstep (se 1 (by rfl) ⟨1013750, by rfl⟩ : syracuseStep 1351667 = 2027501) B2027501
theorem B4562993 : Blo 798342 4562993 := bstep (se 2 (by rfl) ⟨1711122, by rfl⟩ : syracuseStep 4562993 = 3422245) B3422245
theorem B1351795 : Blo 798342 1351795 := bstep (se 1 (by rfl) ⟨1013846, by rfl⟩ : syracuseStep 1351795 = 2027693) B2027693
theorem B3842225 : Blo 798342 3842225 := bstep (se 2 (by rfl) ⟨1440834, by rfl⟩ : syracuseStep 3842225 = 2881669) B2881669
theorem B2695409 : Blo 798342 2695409 := bstep (se 2 (by rfl) ⟨1010778, by rfl⟩ : syracuseStep 2695409 = 2021557) B2021557
theorem B1351937 : Blo 798342 1351937 := bstep (se 2 (by rfl) ⟨506976, by rfl⟩ : syracuseStep 1351937 = 1013953) B1013953
theorem B1712387 : Blo 798342 1712387 := bstep (se 1 (by rfl) ⟨1284290, by rfl⟩ : syracuseStep 1712387 = 2568581) B2568581
theorem B4858147 : Blo 798342 4858147 := bstep (se 1 (by rfl) ⟨3643610, by rfl⟩ : syracuseStep 4858147 = 7287221) B7287221
theorem B1352065 : Blo 798342 1352065 := bstep (se 2 (by rfl) ⟨507024, by rfl⟩ : syracuseStep 1352065 = 1014049) B1014049
theorem B1352099 : Blo 798342 1352099 := bstep (se 1 (by rfl) ⟨1014074, by rfl⟩ : syracuseStep 1352099 = 2028149) B2028149
theorem B1515971 : Blo 798342 1515971 := bstep (se 1 (by rfl) ⟨1136978, by rfl⟩ : syracuseStep 1515971 = 2273957) B2273957
theorem B2597393 : Blo 798342 2597393 := bstep (se 2 (by rfl) ⟨974022, by rfl⟩ : syracuseStep 2597393 = 1948045) B1948045
theorem B1352227 : Blo 798342 1352227 := bstep (se 1 (by rfl) ⟨1014170, by rfl⟩ : syracuseStep 1352227 = 2028341) B2028341
theorem B1352369 : Blo 798342 1352369 := bstep (se 2 (by rfl) ⟨507138, by rfl⟩ : syracuseStep 1352369 = 1014277) B1014277
theorem B1516259 : Blo 798342 1516259 := bstep (se 1 (by rfl) ⟨1137194, by rfl⟩ : syracuseStep 1516259 = 2274389) B2274389
theorem B4104931 : Blo 798342 4104931 := bstep (se 1 (by rfl) ⟨3078698, by rfl⟩ : syracuseStep 4104931 = 6157397) B6157397
theorem B2695949 : Blo 798342 2695949 := bstep (se 3 (by rfl) ⟨505490, by rfl⟩ : syracuseStep 2695949 = 1010981) B1010981
theorem B1155875 : Blo 798342 1155875 := bstep (se 1 (by rfl) ⟨866906, by rfl⟩ : syracuseStep 1155875 = 1733813) B1733813
theorem B1352497 : Blo 798342 1352497 := bstep (se 2 (by rfl) ⟨507186, by rfl⟩ : syracuseStep 1352497 = 1014373) B1014373
theorem B2696003 : Blo 798342 2696003 := bstep (se 1 (by rfl) ⟨2022002, by rfl⟩ : syracuseStep 2696003 = 4044005) B4044005
theorem B2564941 : Blo 798342 2564941 := bstep (se 3 (by rfl) ⟨480926, by rfl⟩ : syracuseStep 2564941 = 961853) B961853
theorem B1352531 : Blo 798342 1352531 := bstep (se 1 (by rfl) ⟨1014398, by rfl⟩ : syracuseStep 1352531 = 2028797) B2028797
theorem B1352659 : Blo 798342 1352659 := bstep (se 1 (by rfl) ⟨1014494, by rfl⟩ : syracuseStep 1352659 = 2028989) B2028989
theorem B2696273 : Blo 798342 2696273 := bstep (se 2 (by rfl) ⟨1011102, by rfl⟩ : syracuseStep 2696273 = 2022205) B2022205
theorem B1352801 : Blo 798342 1352801 := bstep (se 2 (by rfl) ⟨507300, by rfl⟩ : syracuseStep 1352801 = 1014601) B1014601
theorem B1352929 : Blo 798342 1352929 := bstep (se 2 (by rfl) ⟨507348, by rfl⟩ : syracuseStep 1352929 = 1014697) B1014697
theorem B1352963 : Blo 798342 1352963 := bstep (se 1 (by rfl) ⟨1014722, by rfl⟩ : syracuseStep 1352963 = 2029445) B2029445
theorem B1353091 : Blo 798342 1353091 := bstep (se 1 (by rfl) ⟨1014818, by rfl⟩ : syracuseStep 1353091 = 2029637) B2029637
theorem B4564451 : Blo 798342 4564451 := bstep (se 1 (by rfl) ⟨3423338, by rfl⟩ : syracuseStep 4564451 = 6846677) B6846677
theorem B1353233 : Blo 798342 1353233 := bstep (se 2 (by rfl) ⟨507462, by rfl⟩ : syracuseStep 1353233 = 1014925) B1014925
theorem B2696813 : Blo 798342 2696813 := bstep (se 3 (by rfl) ⟨505652, by rfl⟩ : syracuseStep 2696813 = 1011305) B1011305
theorem B1517201 : Blo 798342 1517201 := bstep (se 2 (by rfl) ⟨568950, by rfl⟩ : syracuseStep 1517201 = 1137901) B1137901
theorem B1353361 : Blo 798342 1353361 := bstep (se 2 (by rfl) ⟨507510, by rfl⟩ : syracuseStep 1353361 = 1015021) B1015021
theorem B2696867 : Blo 798342 2696867 := bstep (se 1 (by rfl) ⟨2022650, by rfl⟩ : syracuseStep 2696867 = 4045301) B4045301
theorem B1353395 : Blo 798342 1353395 := bstep (se 1 (by rfl) ⟨1015046, by rfl⟩ : syracuseStep 1353395 = 2030093) B2030093
theorem B3843875 : Blo 798342 3843875 := bstep (se 1 (by rfl) ⟨2882906, by rfl⟩ : syracuseStep 3843875 = 5765813) B5765813
theorem B1353523 : Blo 798342 1353523 := bstep (se 1 (by rfl) ⟨1015142, by rfl⟩ : syracuseStep 1353523 = 2030285) B2030285
theorem B2566019 : Blo 798342 2566019 := bstep (se 1 (by rfl) ⟨1924514, by rfl⟩ : syracuseStep 2566019 = 3849029) B3849029
theorem B6825869 : Blo 798342 6825869 := bstep (se 3 (by rfl) ⟨1279850, by rfl⟩ : syracuseStep 6825869 = 2559701) B2559701
theorem B2697137 : Blo 798342 2697137 := bstep (se 2 (by rfl) ⟨1011426, by rfl⟩ : syracuseStep 2697137 = 2022853) B2022853
theorem B1353665 : Blo 798342 1353665 := bstep (se 2 (by rfl) ⟨507624, by rfl⟩ : syracuseStep 1353665 = 1015249) B1015249
theorem B1353793 : Blo 798342 1353793 := bstep (se 2 (by rfl) ⟨507672, by rfl⟩ : syracuseStep 1353793 = 1015345) B1015345
theorem B1353827 : Blo 798342 1353827 := bstep (se 1 (by rfl) ⟨1015370, by rfl⟩ : syracuseStep 1353827 = 2030741) B2030741
theorem B5187725 : Blo 798342 5187725 := bstep (se 3 (by rfl) ⟨972698, by rfl⟩ : syracuseStep 5187725 = 1945397) B1945397
theorem B960835 : Blo 798342 960835 := bstep (se 1 (by rfl) ⟨720626, by rfl⟩ : syracuseStep 960835 = 1441253) B1441253
theorem B2697677 : Blo 798342 2697677 := bstep (se 3 (by rfl) ⟨505814, by rfl⟩ : syracuseStep 2697677 = 1011629) B1011629
theorem B960979 : Blo 798342 960979 := bstep (se 1 (by rfl) ⟨720734, by rfl⟩ : syracuseStep 960979 = 1441469) B1441469
theorem B2697731 : Blo 798342 2697731 := bstep (se 1 (by rfl) ⟨2023298, by rfl⟩ : syracuseStep 2697731 = 4046597) B4046597
theorem B1518097 : Blo 798342 1518097 := bstep (se 2 (by rfl) ⟨569286, by rfl⟩ : syracuseStep 1518097 = 1138573) B1138573
theorem B2566673 : Blo 798342 2566673 := bstep (se 2 (by rfl) ⟨962502, by rfl⟩ : syracuseStep 2566673 = 1925005) B1925005
theorem B3844685 : Blo 798342 3844685 := bstep (se 3 (by rfl) ⟨720878, by rfl⟩ : syracuseStep 3844685 = 1441757) B1441757
theorem B1026643 : Blo 798342 1026643 := bstep (se 1 (by rfl) ⟨769982, by rfl⟩ : syracuseStep 1026643 = 1539965) B1539965
theorem B1518257 : Blo 798342 1518257 := bstep (se 2 (by rfl) ⟨569346, by rfl⟩ : syracuseStep 1518257 = 1138693) B1138693
theorem B2698001 : Blo 798342 2698001 := bstep (se 2 (by rfl) ⟨1011750, by rfl⟩ : syracuseStep 2698001 = 2023501) B2023501
theorem B1157971 : Blo 798342 1157971 := bstep (se 1 (by rfl) ⟨868478, by rfl⟩ : syracuseStep 1157971 = 1736957) B1736957
theorem B3419171 : Blo 798342 3419171 := bstep (se 1 (by rfl) ⟨2564378, by rfl⟩ : syracuseStep 3419171 = 5128757) B5128757
theorem B1518659 : Blo 798342 1518659 := bstep (se 1 (by rfl) ⟨1138994, by rfl⟩ : syracuseStep 1518659 = 2277989) B2277989
theorem B6073541 : Blo 798342 6073541 := bstep (se 4 (by rfl) ⟨569394, by rfl⟩ : syracuseStep 6073541 = 1138789) B1138789
theorem B2698541 : Blo 798342 2698541 := bstep (se 3 (by rfl) ⟨505976, by rfl⟩ : syracuseStep 2698541 = 1011953) B1011953
theorem B4042061 : Blo 798342 4042061 := bstep (se 3 (by rfl) ⟨757886, by rfl⟩ : syracuseStep 4042061 = 1515773) B1515773
theorem B2698595 : Blo 798342 2698595 := bstep (se 1 (by rfl) ⟨2023946, by rfl⟩ : syracuseStep 2698595 = 4047893) B4047893
theorem B962003 : Blo 798342 962003 := bstep (se 1 (by rfl) ⟨721502, by rfl⟩ : syracuseStep 962003 = 1443005) B1443005
theorem B2436589 : Blo 798342 2436589 := bstep (se 3 (by rfl) ⟨456860, by rfl⟩ : syracuseStep 2436589 = 913721) B913721
theorem B2698865 : Blo 798342 2698865 := bstep (se 2 (by rfl) ⟨1012074, by rfl⟩ : syracuseStep 2698865 = 2024149) B2024149
theorem B798355 : Blo 798342 798355 := bstep (se 1 (by rfl) ⟨598766, by rfl⟩ : syracuseStep 798355 = 1197533) B1197533
theorem B798371 : Blo 798342 798371 := bstep (se 1 (by rfl) ⟨598778, by rfl⟩ : syracuseStep 798371 = 1197557) B1197557
theorem B2928305 : Blo 798342 2928305 := bstep (se 2 (by rfl) ⟨1098114, by rfl⟩ : syracuseStep 2928305 = 2196229) B2196229
theorem B798387 : Blo 798342 798387 := bstep (se 1 (by rfl) ⟨598790, by rfl⟩ : syracuseStep 798387 = 1197581) B1197581
theorem B798403 : Blo 798342 798403 := bstep (se 1 (by rfl) ⟨598802, by rfl⟩ : syracuseStep 798403 = 1197605) B1197605
theorem B798419 : Blo 798342 798419 := bstep (se 1 (by rfl) ⟨598814, by rfl⟩ : syracuseStep 798419 = 1197629) B1197629
theorem B798435 : Blo 798342 798435 := bstep (se 1 (by rfl) ⟨598826, by rfl⟩ : syracuseStep 798435 = 1197653) B1197653
theorem B798451 : Blo 798342 798451 := bstep (se 1 (by rfl) ⟨598838, by rfl⟩ : syracuseStep 798451 = 1197677) B1197677
theorem B798467 : Blo 798342 798467 := bstep (se 1 (by rfl) ⟨598850, by rfl⟩ : syracuseStep 798467 = 1197701) B1197701
theorem B798483 : Blo 798342 798483 := bstep (se 1 (by rfl) ⟨598862, by rfl⟩ : syracuseStep 798483 = 1197725) B1197725
theorem B798499 : Blo 798342 798499 := bstep (se 1 (by rfl) ⟨598874, by rfl⟩ : syracuseStep 798499 = 1197749) B1197749
theorem B2305837 : Blo 798342 2305837 := bstep (se 3 (by rfl) ⟨432344, by rfl⟩ : syracuseStep 2305837 = 864689) B864689
theorem B798515 : Blo 798342 798515 := bstep (se 1 (by rfl) ⟨598886, by rfl⟩ : syracuseStep 798515 = 1197773) B1197773
theorem B798531 : Blo 798342 798531 := bstep (se 1 (by rfl) ⟨598898, by rfl⟩ : syracuseStep 798531 = 1197797) B1197797
theorem B2568017 : Blo 798342 2568017 := bstep (se 2 (by rfl) ⟨963006, by rfl⟩ : syracuseStep 2568017 = 1926013) B1926013
theorem B798547 : Blo 798342 798547 := bstep (se 1 (by rfl) ⟨598910, by rfl⟩ : syracuseStep 798547 = 1197821) B1197821
theorem B798563 : Blo 798342 798563 := bstep (se 1 (by rfl) ⟨598922, by rfl⟩ : syracuseStep 798563 = 1197845) B1197845
theorem B798579 : Blo 798342 798579 := bstep (se 1 (by rfl) ⟨598934, by rfl⟩ : syracuseStep 798579 = 1197869) B1197869
theorem B798595 : Blo 798342 798595 := bstep (se 1 (by rfl) ⟨598946, by rfl⟩ : syracuseStep 798595 = 1197893) B1197893
theorem B798611 : Blo 798342 798611 := bstep (se 1 (by rfl) ⟨598958, by rfl⟩ : syracuseStep 798611 = 1197917) B1197917
theorem B798627 : Blo 798342 798627 := bstep (se 1 (by rfl) ⟨598970, by rfl⟩ : syracuseStep 798627 = 1197941) B1197941
theorem B798643 : Blo 798342 798643 := bstep (se 1 (by rfl) ⟨598982, by rfl⟩ : syracuseStep 798643 = 1197965) B1197965
theorem B798659 : Blo 798342 798659 := bstep (se 1 (by rfl) ⟨598994, by rfl⟩ : syracuseStep 798659 = 1197989) B1197989
theorem B1519555 : Blo 798342 1519555 := bstep (se 1 (by rfl) ⟨1139666, by rfl⟩ : syracuseStep 1519555 = 2279333) B2279333
theorem B798675 : Blo 798342 798675 := bstep (se 1 (by rfl) ⟨599006, by rfl⟩ : syracuseStep 798675 = 1198013) B1198013
theorem B798691 : Blo 798342 798691 := bstep (se 1 (by rfl) ⟨599018, by rfl⟩ : syracuseStep 798691 = 1198037) B1198037
theorem B798707 : Blo 798342 798707 := bstep (se 1 (by rfl) ⟨599030, by rfl⟩ : syracuseStep 798707 = 1198061) B1198061
theorem B798723 : Blo 798342 798723 := bstep (se 1 (by rfl) ⟨599042, by rfl⟩ : syracuseStep 798723 = 1198085) B1198085
theorem B798739 : Blo 798342 798739 := bstep (se 1 (by rfl) ⟨599054, by rfl⟩ : syracuseStep 798739 = 1198109) B1198109
theorem B798755 : Blo 798342 798755 := bstep (se 1 (by rfl) ⟨599066, by rfl⟩ : syracuseStep 798755 = 1198133) B1198133
theorem B798771 : Blo 798342 798771 := bstep (se 1 (by rfl) ⟨599078, by rfl⟩ : syracuseStep 798771 = 1198157) B1198157
theorem B798787 : Blo 798342 798787 := bstep (se 1 (by rfl) ⟨599090, by rfl⟩ : syracuseStep 798787 = 1198181) B1198181
theorem B798803 : Blo 798342 798803 := bstep (se 1 (by rfl) ⟨599102, by rfl⟩ : syracuseStep 798803 = 1198205) B1198205
theorem B798819 : Blo 798342 798819 := bstep (se 1 (by rfl) ⟨599114, by rfl⟩ : syracuseStep 798819 = 1198229) B1198229
theorem B1519715 : Blo 798342 1519715 := bstep (se 1 (by rfl) ⟨1139786, by rfl⟩ : syracuseStep 1519715 = 2279573) B2279573
theorem B798835 : Blo 798342 798835 := bstep (se 1 (by rfl) ⟨599126, by rfl⟩ : syracuseStep 798835 = 1198253) B1198253
theorem B798851 : Blo 798342 798851 := bstep (se 1 (by rfl) ⟨599138, by rfl⟩ : syracuseStep 798851 = 1198277) B1198277
theorem B2699405 : Blo 798342 2699405 := bstep (se 3 (by rfl) ⟨506138, by rfl⟩ : syracuseStep 2699405 = 1012277) B1012277
theorem B798867 : Blo 798342 798867 := bstep (se 1 (by rfl) ⟨599150, by rfl⟩ : syracuseStep 798867 = 1198301) B1198301
theorem B798883 : Blo 798342 798883 := bstep (se 1 (by rfl) ⟨599162, by rfl⟩ : syracuseStep 798883 = 1198325) B1198325
theorem B798899 : Blo 798342 798899 := bstep (se 1 (by rfl) ⟨599174, by rfl⟩ : syracuseStep 798899 = 1198349) B1198349
theorem B798915 : Blo 798342 798915 := bstep (se 1 (by rfl) ⟨599186, by rfl⟩ : syracuseStep 798915 = 1198373) B1198373
theorem B2699459 : Blo 798342 2699459 := bstep (se 1 (by rfl) ⟨2024594, by rfl⟩ : syracuseStep 2699459 = 4049189) B4049189
theorem B798931 : Blo 798342 798931 := bstep (se 1 (by rfl) ⟨599198, by rfl⟩ : syracuseStep 798931 = 1198397) B1198397
theorem B798947 : Blo 798342 798947 := bstep (se 1 (by rfl) ⟨599210, by rfl⟩ : syracuseStep 798947 = 1198421) B1198421
theorem B5124323 : Blo 798342 5124323 := bstep (se 1 (by rfl) ⟨3843242, by rfl⟩ : syracuseStep 5124323 = 7686485) B7686485
theorem B798963 : Blo 798342 798963 := bstep (se 1 (by rfl) ⟨599222, by rfl⟩ : syracuseStep 798963 = 1198445) B1198445
theorem B798979 : Blo 798342 798979 := bstep (se 1 (by rfl) ⟨599234, by rfl⟩ : syracuseStep 798979 = 1198469) B1198469
theorem B798995 : Blo 798342 798995 := bstep (se 1 (by rfl) ⟨599246, by rfl⟩ : syracuseStep 798995 = 1198493) B1198493
theorem B799011 : Blo 798342 799011 := bstep (se 1 (by rfl) ⟨599258, by rfl⟩ : syracuseStep 799011 = 1198517) B1198517
theorem B799027 : Blo 798342 799027 := bstep (se 1 (by rfl) ⟨599270, by rfl⟩ : syracuseStep 799027 = 1198541) B1198541
theorem B799043 : Blo 798342 799043 := bstep (se 1 (by rfl) ⟨599282, by rfl⟩ : syracuseStep 799043 = 1198565) B1198565
theorem B799059 : Blo 798342 799059 := bstep (se 1 (by rfl) ⟨599294, by rfl⟩ : syracuseStep 799059 = 1198589) B1198589
theorem B799075 : Blo 798342 799075 := bstep (se 1 (by rfl) ⟨599306, by rfl⟩ : syracuseStep 799075 = 1198613) B1198613
theorem B799091 : Blo 798342 799091 := bstep (se 1 (by rfl) ⟨599318, by rfl⟩ : syracuseStep 799091 = 1198637) B1198637
theorem B799107 : Blo 798342 799107 := bstep (se 1 (by rfl) ⟨599330, by rfl⟩ : syracuseStep 799107 = 1198661) B1198661
theorem B799123 : Blo 798342 799123 := bstep (se 1 (by rfl) ⟨599342, by rfl⟩ : syracuseStep 799123 = 1198685) B1198685
theorem B799139 : Blo 798342 799139 := bstep (se 1 (by rfl) ⟨599354, by rfl⟩ : syracuseStep 799139 = 1198709) B1198709
theorem B799155 : Blo 798342 799155 := bstep (se 1 (by rfl) ⟨599366, by rfl⟩ : syracuseStep 799155 = 1198733) B1198733
theorem B799171 : Blo 798342 799171 := bstep (se 1 (by rfl) ⟨599378, by rfl⟩ : syracuseStep 799171 = 1198757) B1198757
theorem B2273741 : Blo 798342 2273741 := bstep (se 3 (by rfl) ⟨426326, by rfl⟩ : syracuseStep 2273741 = 852653) B852653
theorem B2699729 : Blo 798342 2699729 := bstep (se 2 (by rfl) ⟨1012398, by rfl⟩ : syracuseStep 2699729 = 2024797) B2024797
theorem B799187 : Blo 798342 799187 := bstep (se 1 (by rfl) ⟨599390, by rfl⟩ : syracuseStep 799187 = 1198781) B1198781
theorem B799203 : Blo 798342 799203 := bstep (se 1 (by rfl) ⟨599402, by rfl⟩ : syracuseStep 799203 = 1198805) B1198805
theorem B799219 : Blo 798342 799219 := bstep (se 1 (by rfl) ⟨599414, by rfl⟩ : syracuseStep 799219 = 1198829) B1198829
theorem B799235 : Blo 798342 799235 := bstep (se 1 (by rfl) ⟨599426, by rfl⟩ : syracuseStep 799235 = 1198853) B1198853
theorem B799251 : Blo 798342 799251 := bstep (se 1 (by rfl) ⟨599438, by rfl⟩ : syracuseStep 799251 = 1198877) B1198877
theorem B799267 : Blo 798342 799267 := bstep (se 1 (by rfl) ⟨599450, by rfl⟩ : syracuseStep 799267 = 1198901) B1198901
theorem B799283 : Blo 798342 799283 := bstep (se 1 (by rfl) ⟨599462, by rfl⟩ : syracuseStep 799283 = 1198925) B1198925
theorem B799299 : Blo 798342 799299 := bstep (se 1 (by rfl) ⟨599474, by rfl⟩ : syracuseStep 799299 = 1198949) B1198949
theorem B799315 : Blo 798342 799315 := bstep (se 1 (by rfl) ⟨599486, by rfl⟩ : syracuseStep 799315 = 1198973) B1198973
theorem B799331 : Blo 798342 799331 := bstep (se 1 (by rfl) ⟨599498, by rfl⟩ : syracuseStep 799331 = 1198997) B1198997
theorem B799347 : Blo 798342 799347 := bstep (se 1 (by rfl) ⟨599510, by rfl⟩ : syracuseStep 799347 = 1199021) B1199021
theorem B799363 : Blo 798342 799363 := bstep (se 1 (by rfl) ⟨599522, by rfl⟩ : syracuseStep 799363 = 1199045) B1199045
theorem B15348365 : Blo 798342 15348365 := bstep (se 3 (by rfl) ⟨2877818, by rfl⟩ : syracuseStep 15348365 = 5755637) B5755637
theorem B2273933 : Blo 798342 2273933 := bstep (se 3 (by rfl) ⟨426362, by rfl⟩ : syracuseStep 2273933 = 852725) B852725
theorem B799379 : Blo 798342 799379 := bstep (se 1 (by rfl) ⟨599534, by rfl⟩ : syracuseStep 799379 = 1199069) B1199069
theorem B799395 : Blo 798342 799395 := bstep (se 1 (by rfl) ⟨599546, by rfl⟩ : syracuseStep 799395 = 1199093) B1199093
theorem B2437805 : Blo 798342 2437805 := bstep (se 3 (by rfl) ⟨457088, by rfl⟩ : syracuseStep 2437805 = 914177) B914177
theorem B799411 : Blo 798342 799411 := bstep (se 1 (by rfl) ⟨599558, by rfl⟩ : syracuseStep 799411 = 1199117) B1199117
theorem B799427 : Blo 798342 799427 := bstep (se 1 (by rfl) ⟨599570, by rfl⟩ : syracuseStep 799427 = 1199141) B1199141
theorem B799443 : Blo 798342 799443 := bstep (se 1 (by rfl) ⟨599582, by rfl⟩ : syracuseStep 799443 = 1199165) B1199165
theorem B799459 : Blo 798342 799459 := bstep (se 1 (by rfl) ⟨599594, by rfl⟩ : syracuseStep 799459 = 1199189) B1199189
theorem B3420913 : Blo 798342 3420913 := bstep (se 2 (by rfl) ⟨1282842, by rfl⟩ : syracuseStep 3420913 = 2565685) B2565685
theorem B799475 : Blo 798342 799475 := bstep (se 1 (by rfl) ⟨599606, by rfl⟩ : syracuseStep 799475 = 1199213) B1199213
theorem B799491 : Blo 798342 799491 := bstep (se 1 (by rfl) ⟨599618, by rfl⟩ : syracuseStep 799491 = 1199237) B1199237
theorem B799507 : Blo 798342 799507 := bstep (se 1 (by rfl) ⟨599630, by rfl⟩ : syracuseStep 799507 = 1199261) B1199261
theorem B799523 : Blo 798342 799523 := bstep (se 1 (by rfl) ⟨599642, by rfl⟩ : syracuseStep 799523 = 1199285) B1199285
theorem B799539 : Blo 798342 799539 := bstep (se 1 (by rfl) ⟨599654, by rfl⟩ : syracuseStep 799539 = 1199309) B1199309
theorem B799555 : Blo 798342 799555 := bstep (se 1 (by rfl) ⟨599666, by rfl⟩ : syracuseStep 799555 = 1199333) B1199333
theorem B799571 : Blo 798342 799571 := bstep (se 1 (by rfl) ⟨599678, by rfl⟩ : syracuseStep 799571 = 1199357) B1199357
theorem B799587 : Blo 798342 799587 := bstep (se 1 (by rfl) ⟨599690, by rfl⟩ : syracuseStep 799587 = 1199381) B1199381
theorem B799603 : Blo 798342 799603 := bstep (se 1 (by rfl) ⟨599702, by rfl⟩ : syracuseStep 799603 = 1199405) B1199405
theorem B799619 : Blo 798342 799619 := bstep (se 1 (by rfl) ⟨599714, by rfl⟩ : syracuseStep 799619 = 1199429) B1199429
theorem B4109197 : Blo 798342 4109197 := bstep (se 3 (by rfl) ⟨770474, by rfl⟩ : syracuseStep 4109197 = 1540949) B1540949
theorem B799635 : Blo 798342 799635 := bstep (se 1 (by rfl) ⟨599726, by rfl⟩ : syracuseStep 799635 = 1199453) B1199453
theorem B799651 : Blo 798342 799651 := bstep (se 1 (by rfl) ⟨599738, by rfl⟩ : syracuseStep 799651 = 1199477) B1199477
theorem B2569133 : Blo 798342 2569133 := bstep (se 3 (by rfl) ⟨481712, by rfl⟩ : syracuseStep 2569133 = 963425) B963425
theorem B799667 : Blo 798342 799667 := bstep (se 1 (by rfl) ⟨599750, by rfl⟩ : syracuseStep 799667 = 1199501) B1199501
theorem B799683 : Blo 798342 799683 := bstep (se 1 (by rfl) ⟨599762, by rfl⟩ : syracuseStep 799683 = 1199525) B1199525
theorem B799699 : Blo 798342 799699 := bstep (se 1 (by rfl) ⟨599774, by rfl⟩ : syracuseStep 799699 = 1199549) B1199549
theorem B799715 : Blo 798342 799715 := bstep (se 1 (by rfl) ⟨599786, by rfl⟩ : syracuseStep 799715 = 1199573) B1199573
theorem B2700269 : Blo 798342 2700269 := bstep (se 3 (by rfl) ⟨506300, by rfl⟩ : syracuseStep 2700269 = 1012601) B1012601
theorem B799731 : Blo 798342 799731 := bstep (se 1 (by rfl) ⟨599798, by rfl⟩ : syracuseStep 799731 = 1199597) B1199597
theorem B799747 : Blo 798342 799747 := bstep (se 1 (by rfl) ⟨599810, by rfl⟩ : syracuseStep 799747 = 1199621) B1199621
theorem B799763 : Blo 798342 799763 := bstep (se 1 (by rfl) ⟨599822, by rfl⟩ : syracuseStep 799763 = 1199645) B1199645
theorem B799779 : Blo 798342 799779 := bstep (se 1 (by rfl) ⟨599834, by rfl⟩ : syracuseStep 799779 = 1199669) B1199669
theorem B2700323 : Blo 798342 2700323 := bstep (se 1 (by rfl) ⟨2025242, by rfl⟩ : syracuseStep 2700323 = 4050485) B4050485
theorem B799795 : Blo 798342 799795 := bstep (se 1 (by rfl) ⟨599846, by rfl⟩ : syracuseStep 799795 = 1199693) B1199693
theorem B799811 : Blo 798342 799811 := bstep (se 1 (by rfl) ⟨599858, by rfl⟩ : syracuseStep 799811 = 1199717) B1199717
theorem B799827 : Blo 798342 799827 := bstep (se 1 (by rfl) ⟨599870, by rfl⟩ : syracuseStep 799827 = 1199741) B1199741
theorem B799843 : Blo 798342 799843 := bstep (se 1 (by rfl) ⟨599882, by rfl⟩ : syracuseStep 799843 = 1199765) B1199765
theorem B799859 : Blo 798342 799859 := bstep (se 1 (by rfl) ⟨599894, by rfl⟩ : syracuseStep 799859 = 1199789) B1199789
theorem B799875 : Blo 798342 799875 := bstep (se 1 (by rfl) ⟨599906, by rfl⟩ : syracuseStep 799875 = 1199813) B1199813
theorem B1520785 : Blo 798342 1520785 := bstep (se 2 (by rfl) ⟨570294, by rfl⟩ : syracuseStep 1520785 = 1140589) B1140589
theorem B898195 : Blo 798342 898195 := bstep (se 1 (by rfl) ⟨673646, by rfl⟩ : syracuseStep 898195 = 1347293) B1347293
theorem B799891 : Blo 798342 799891 := bstep (se 1 (by rfl) ⟨599918, by rfl⟩ : syracuseStep 799891 = 1199837) B1199837
theorem B799907 : Blo 798342 799907 := bstep (se 1 (by rfl) ⟨599930, by rfl⟩ : syracuseStep 799907 = 1199861) B1199861
theorem B1094833 : Blo 798342 1094833 := bstep (se 2 (by rfl) ⟨410562, by rfl⟩ : syracuseStep 1094833 = 821125) B821125
theorem B799923 : Blo 798342 799923 := bstep (se 1 (by rfl) ⟨599942, by rfl⟩ : syracuseStep 799923 = 1199885) B1199885
theorem B799939 : Blo 798342 799939 := bstep (se 1 (by rfl) ⟨599954, by rfl⟩ : syracuseStep 799939 = 1199909) B1199909
theorem B799955 : Blo 798342 799955 := bstep (se 1 (by rfl) ⟨599966, by rfl⟩ : syracuseStep 799955 = 1199933) B1199933
theorem B799971 : Blo 798342 799971 := bstep (se 1 (by rfl) ⟨599978, by rfl⟩ : syracuseStep 799971 = 1199957) B1199957
theorem B799987 : Blo 798342 799987 := bstep (se 1 (by rfl) ⟨599990, by rfl⟩ : syracuseStep 799987 = 1199981) B1199981
theorem B800003 : Blo 798342 800003 := bstep (se 1 (by rfl) ⟨600002, by rfl⟩ : syracuseStep 800003 = 1200005) B1200005
theorem B800019 : Blo 798342 800019 := bstep (se 1 (by rfl) ⟨600014, by rfl⟩ : syracuseStep 800019 = 1200029) B1200029
theorem B898339 : Blo 798342 898339 := bstep (se 1 (by rfl) ⟨673754, by rfl⟩ : syracuseStep 898339 = 1347509) B1347509
theorem B800035 : Blo 798342 800035 := bstep (se 1 (by rfl) ⟨600026, by rfl⟩ : syracuseStep 800035 = 1200053) B1200053
theorem B2700593 : Blo 798342 2700593 := bstep (se 2 (by rfl) ⟨1012722, by rfl⟩ : syracuseStep 2700593 = 2025445) B2025445
theorem B800051 : Blo 798342 800051 := bstep (se 1 (by rfl) ⟨600038, by rfl⟩ : syracuseStep 800051 = 1200077) B1200077
theorem B800067 : Blo 798342 800067 := bstep (se 1 (by rfl) ⟨600050, by rfl⟩ : syracuseStep 800067 = 1200101) B1200101
theorem B800083 : Blo 798342 800083 := bstep (se 1 (by rfl) ⟨600062, by rfl⟩ : syracuseStep 800083 = 1200125) B1200125
theorem B800099 : Blo 798342 800099 := bstep (se 1 (by rfl) ⟨600074, by rfl⟩ : syracuseStep 800099 = 1200149) B1200149
theorem B800115 : Blo 798342 800115 := bstep (se 1 (by rfl) ⟨600086, by rfl⟩ : syracuseStep 800115 = 1200173) B1200173
theorem B800131 : Blo 798342 800131 := bstep (se 1 (by rfl) ⟨600098, by rfl⟩ : syracuseStep 800131 = 1200197) B1200197
theorem B800147 : Blo 798342 800147 := bstep (se 1 (by rfl) ⟨600110, by rfl⟩ : syracuseStep 800147 = 1200221) B1200221
theorem B800163 : Blo 798342 800163 := bstep (se 1 (by rfl) ⟨600122, by rfl⟩ : syracuseStep 800163 = 1200245) B1200245
theorem B898483 : Blo 798342 898483 := bstep (se 1 (by rfl) ⟨673862, by rfl⟩ : syracuseStep 898483 = 1347725) B1347725
theorem B800179 : Blo 798342 800179 := bstep (se 1 (by rfl) ⟨600134, by rfl⟩ : syracuseStep 800179 = 1200269) B1200269
theorem B800195 : Blo 798342 800195 := bstep (se 1 (by rfl) ⟨600146, by rfl⟩ : syracuseStep 800195 = 1200293) B1200293
theorem B800211 : Blo 798342 800211 := bstep (se 1 (by rfl) ⟨600158, by rfl⟩ : syracuseStep 800211 = 1200317) B1200317
theorem B800227 : Blo 798342 800227 := bstep (se 1 (by rfl) ⟨600170, by rfl⟩ : syracuseStep 800227 = 1200341) B1200341
theorem B800243 : Blo 798342 800243 := bstep (se 1 (by rfl) ⟨600182, by rfl⟩ : syracuseStep 800243 = 1200365) B1200365
theorem B800259 : Blo 798342 800259 := bstep (se 1 (by rfl) ⟨600194, by rfl⟩ : syracuseStep 800259 = 1200389) B1200389
theorem B800275 : Blo 798342 800275 := bstep (se 1 (by rfl) ⟨600206, by rfl⟩ : syracuseStep 800275 = 1200413) B1200413
theorem B800291 : Blo 798342 800291 := bstep (se 1 (by rfl) ⟨600218, by rfl⟩ : syracuseStep 800291 = 1200437) B1200437
theorem B800307 : Blo 798342 800307 := bstep (se 1 (by rfl) ⟨600230, by rfl⟩ : syracuseStep 800307 = 1200461) B1200461
theorem B898627 : Blo 798342 898627 := bstep (se 1 (by rfl) ⟨673970, by rfl⟩ : syracuseStep 898627 = 1347941) B1347941
theorem B800323 : Blo 798342 800323 := bstep (se 1 (by rfl) ⟨600242, by rfl⟩ : syracuseStep 800323 = 1200485) B1200485
theorem B800339 : Blo 798342 800339 := bstep (se 1 (by rfl) ⟨600254, by rfl⟩ : syracuseStep 800339 = 1200509) B1200509
theorem B800355 : Blo 798342 800355 := bstep (se 1 (by rfl) ⟨600266, by rfl⟩ : syracuseStep 800355 = 1200533) B1200533
theorem B3126883 : Blo 798342 3126883 := bstep (se 1 (by rfl) ⟨2345162, by rfl⟩ : syracuseStep 3126883 = 4690325) B4690325
theorem B2274925 : Blo 798342 2274925 := bstep (se 3 (by rfl) ⟨426548, by rfl⟩ : syracuseStep 2274925 = 853097) B853097
theorem B800371 : Blo 798342 800371 := bstep (se 1 (by rfl) ⟨600278, by rfl⟩ : syracuseStep 800371 = 1200557) B1200557
theorem B800387 : Blo 798342 800387 := bstep (se 1 (by rfl) ⟨600290, by rfl⟩ : syracuseStep 800387 = 1200581) B1200581
theorem B800403 : Blo 798342 800403 := bstep (se 1 (by rfl) ⟨600302, by rfl⟩ : syracuseStep 800403 = 1200605) B1200605
theorem B800419 : Blo 798342 800419 := bstep (se 1 (by rfl) ⟨600314, by rfl⟩ : syracuseStep 800419 = 1200629) B1200629
theorem B800435 : Blo 798342 800435 := bstep (se 1 (by rfl) ⟨600326, by rfl⟩ : syracuseStep 800435 = 1200653) B1200653
theorem B800451 : Blo 798342 800451 := bstep (se 1 (by rfl) ⟨600338, by rfl⟩ : syracuseStep 800451 = 1200677) B1200677
theorem B898771 : Blo 798342 898771 := bstep (se 1 (by rfl) ⟨674078, by rfl⟩ : syracuseStep 898771 = 1348157) B1348157
theorem B800467 : Blo 798342 800467 := bstep (se 1 (by rfl) ⟨600350, by rfl⟩ : syracuseStep 800467 = 1200701) B1200701
theorem B800483 : Blo 798342 800483 := bstep (se 1 (by rfl) ⟨600362, by rfl⟩ : syracuseStep 800483 = 1200725) B1200725
theorem B800499 : Blo 798342 800499 := bstep (se 1 (by rfl) ⟨600374, by rfl⟩ : syracuseStep 800499 = 1200749) B1200749
theorem B1128179 : Blo 798342 1128179 := bstep (se 1 (by rfl) ⟨846134, by rfl⟩ : syracuseStep 1128179 = 1692269) B1692269
theorem B800515 : Blo 798342 800515 := bstep (se 1 (by rfl) ⟨600386, by rfl⟩ : syracuseStep 800515 = 1200773) B1200773
theorem B800531 : Blo 798342 800531 := bstep (se 1 (by rfl) ⟨600398, by rfl⟩ : syracuseStep 800531 = 1200797) B1200797
theorem B800547 : Blo 798342 800547 := bstep (se 1 (by rfl) ⟨600410, by rfl⟩ : syracuseStep 800547 = 1200821) B1200821
theorem B800563 : Blo 798342 800563 := bstep (se 1 (by rfl) ⟨600422, by rfl⟩ : syracuseStep 800563 = 1200845) B1200845
theorem B800579 : Blo 798342 800579 := bstep (se 1 (by rfl) ⟨600434, by rfl⟩ : syracuseStep 800579 = 1200869) B1200869
theorem B2701133 : Blo 798342 2701133 := bstep (se 3 (by rfl) ⟨506462, by rfl⟩ : syracuseStep 2701133 = 1012925) B1012925
theorem B800595 : Blo 798342 800595 := bstep (se 1 (by rfl) ⟨600446, by rfl⟩ : syracuseStep 800595 = 1200893) B1200893
theorem B898915 : Blo 798342 898915 := bstep (se 1 (by rfl) ⟨674186, by rfl⟩ : syracuseStep 898915 = 1348373) B1348373
theorem B800611 : Blo 798342 800611 := bstep (se 1 (by rfl) ⟨600458, by rfl⟩ : syracuseStep 800611 = 1200917) B1200917
theorem B800627 : Blo 798342 800627 := bstep (se 1 (by rfl) ⟨600470, by rfl⟩ : syracuseStep 800627 = 1200941) B1200941
theorem B2701187 : Blo 798342 2701187 := bstep (se 1 (by rfl) ⟨2025890, by rfl⟩ : syracuseStep 2701187 = 4051781) B4051781
theorem B800643 : Blo 798342 800643 := bstep (se 1 (by rfl) ⟨600482, by rfl⟩ : syracuseStep 800643 = 1200965) B1200965
theorem B800659 : Blo 798342 800659 := bstep (se 1 (by rfl) ⟨600494, by rfl⟩ : syracuseStep 800659 = 1200989) B1200989
theorem B800675 : Blo 798342 800675 := bstep (se 1 (by rfl) ⟨600506, by rfl⟩ : syracuseStep 800675 = 1201013) B1201013
theorem B800691 : Blo 798342 800691 := bstep (se 1 (by rfl) ⟨600518, by rfl⟩ : syracuseStep 800691 = 1201037) B1201037
theorem B800707 : Blo 798342 800707 := bstep (se 1 (by rfl) ⟨600530, by rfl⟩ : syracuseStep 800707 = 1201061) B1201061
theorem B800723 : Blo 798342 800723 := bstep (se 1 (by rfl) ⟨600542, by rfl⟩ : syracuseStep 800723 = 1201085) B1201085
theorem B800739 : Blo 798342 800739 := bstep (se 1 (by rfl) ⟨600554, by rfl⟩ : syracuseStep 800739 = 1201109) B1201109
theorem B2570221 : Blo 798342 2570221 := bstep (se 3 (by rfl) ⟨481916, by rfl⟩ : syracuseStep 2570221 = 963833) B963833
theorem B899059 : Blo 798342 899059 := bstep (se 1 (by rfl) ⟨674294, by rfl⟩ : syracuseStep 899059 = 1348589) B1348589
theorem B800755 : Blo 798342 800755 := bstep (se 1 (by rfl) ⟨600566, by rfl⟩ : syracuseStep 800755 = 1201133) B1201133
theorem B800771 : Blo 798342 800771 := bstep (se 1 (by rfl) ⟨600578, by rfl⟩ : syracuseStep 800771 = 1201157) B1201157
theorem B800787 : Blo 798342 800787 := bstep (se 1 (by rfl) ⟨600590, by rfl⟩ : syracuseStep 800787 = 1201181) B1201181
theorem B800803 : Blo 798342 800803 := bstep (se 1 (by rfl) ⟨600602, by rfl⟩ : syracuseStep 800803 = 1201205) B1201205
theorem B800819 : Blo 798342 800819 := bstep (se 1 (by rfl) ⟨600614, by rfl⟩ : syracuseStep 800819 = 1201229) B1201229
theorem B800835 : Blo 798342 800835 := bstep (se 1 (by rfl) ⟨600626, by rfl⟩ : syracuseStep 800835 = 1201253) B1201253
theorem B2734157 : Blo 798342 2734157 := bstep (se 3 (by rfl) ⟨512654, by rfl⟩ : syracuseStep 2734157 = 1025309) B1025309
theorem B800851 : Blo 798342 800851 := bstep (se 1 (by rfl) ⟨600638, by rfl⟩ : syracuseStep 800851 = 1201277) B1201277
theorem B800867 : Blo 798342 800867 := bstep (se 1 (by rfl) ⟨600650, by rfl⟩ : syracuseStep 800867 = 1201301) B1201301
theorem B5486705 : Blo 798342 5486705 := bstep (se 2 (by rfl) ⟨2057514, by rfl⟩ : syracuseStep 5486705 = 4115029) B4115029
theorem B800883 : Blo 798342 800883 := bstep (se 1 (by rfl) ⟨600662, by rfl⟩ : syracuseStep 800883 = 1201325) B1201325
theorem B5781617 : Blo 798342 5781617 := bstep (se 2 (by rfl) ⟨2168106, by rfl⟩ : syracuseStep 5781617 = 4336213) B4336213
theorem B899203 : Blo 798342 899203 := bstep (se 1 (by rfl) ⟨674402, by rfl⟩ : syracuseStep 899203 = 1348805) B1348805
theorem B800899 : Blo 798342 800899 := bstep (se 1 (by rfl) ⟨600674, by rfl⟩ : syracuseStep 800899 = 1201349) B1201349
theorem B2701457 : Blo 798342 2701457 := bstep (se 2 (by rfl) ⟨1013046, by rfl⟩ : syracuseStep 2701457 = 2026093) B2026093
theorem B800915 : Blo 798342 800915 := bstep (se 1 (by rfl) ⟨600686, by rfl⟩ : syracuseStep 800915 = 1201373) B1201373
theorem B800931 : Blo 798342 800931 := bstep (se 1 (by rfl) ⟨600698, by rfl⟩ : syracuseStep 800931 = 1201397) B1201397
theorem B4044977 : Blo 798342 4044977 := bstep (se 2 (by rfl) ⟨1516866, by rfl⟩ : syracuseStep 4044977 = 3033733) B3033733
theorem B1521841 : Blo 798342 1521841 := bstep (se 2 (by rfl) ⟨570690, by rfl⟩ : syracuseStep 1521841 = 1141381) B1141381
theorem B800947 : Blo 798342 800947 := bstep (se 1 (by rfl) ⟨600710, by rfl⟩ : syracuseStep 800947 = 1201421) B1201421
theorem B800963 : Blo 798342 800963 := bstep (se 1 (by rfl) ⟨600722, by rfl⟩ : syracuseStep 800963 = 1201445) B1201445
theorem B800979 : Blo 798342 800979 := bstep (se 1 (by rfl) ⟨600734, by rfl⟩ : syracuseStep 800979 = 1201469) B1201469
theorem B800995 : Blo 798342 800995 := bstep (se 1 (by rfl) ⟨600746, by rfl⟩ : syracuseStep 800995 = 1201493) B1201493
theorem B1620209 : Blo 798342 1620209 := bstep (se 2 (by rfl) ⟨607578, by rfl⟩ : syracuseStep 1620209 = 1215157) B1215157
theorem B801011 : Blo 798342 801011 := bstep (se 1 (by rfl) ⟨600758, by rfl⟩ : syracuseStep 801011 = 1201517) B1201517
theorem B801027 : Blo 798342 801027 := bstep (se 1 (by rfl) ⟨600770, by rfl⟩ : syracuseStep 801027 = 1201541) B1201541
theorem B899347 : Blo 798342 899347 := bstep (se 1 (by rfl) ⟨674510, by rfl⟩ : syracuseStep 899347 = 1349021) B1349021
theorem B801043 : Blo 798342 801043 := bstep (se 1 (by rfl) ⟨600782, by rfl⟩ : syracuseStep 801043 = 1201565) B1201565
theorem B801059 : Blo 798342 801059 := bstep (se 1 (by rfl) ⟨600794, by rfl⟩ : syracuseStep 801059 = 1201589) B1201589
theorem B5126449 : Blo 798342 5126449 := bstep (se 2 (by rfl) ⟨1922418, by rfl⟩ : syracuseStep 5126449 = 3844837) B3844837
theorem B2472241 : Blo 798342 2472241 := bstep (se 2 (by rfl) ⟨927090, by rfl⟩ : syracuseStep 2472241 = 1854181) B1854181
theorem B801075 : Blo 798342 801075 := bstep (se 1 (by rfl) ⟨600806, by rfl⟩ : syracuseStep 801075 = 1201613) B1201613
theorem B801091 : Blo 798342 801091 := bstep (se 1 (by rfl) ⟨600818, by rfl⟩ : syracuseStep 801091 = 1201637) B1201637
theorem B801107 : Blo 798342 801107 := bstep (se 1 (by rfl) ⟨600830, by rfl⟩ : syracuseStep 801107 = 1201661) B1201661
theorem B801123 : Blo 798342 801123 := bstep (se 1 (by rfl) ⟨600842, by rfl⟩ : syracuseStep 801123 = 1201685) B1201685
theorem B801139 : Blo 798342 801139 := bstep (se 1 (by rfl) ⟨600854, by rfl⟩ : syracuseStep 801139 = 1201709) B1201709
theorem B801155 : Blo 798342 801155 := bstep (se 1 (by rfl) ⟨600866, by rfl⟩ : syracuseStep 801155 = 1201733) B1201733
theorem B801171 : Blo 798342 801171 := bstep (se 1 (by rfl) ⟨600878, by rfl⟩ : syracuseStep 801171 = 1201757) B1201757
theorem B899491 : Blo 798342 899491 := bstep (se 1 (by rfl) ⟨674618, by rfl⟩ : syracuseStep 899491 = 1349237) B1349237
theorem B801187 : Blo 798342 801187 := bstep (se 1 (by rfl) ⟨600890, by rfl⟩ : syracuseStep 801187 = 1201781) B1201781
theorem B801203 : Blo 798342 801203 := bstep (se 1 (by rfl) ⟨600902, by rfl⟩ : syracuseStep 801203 = 1201805) B1201805
theorem B801219 : Blo 798342 801219 := bstep (se 1 (by rfl) ⟨600914, by rfl⟩ : syracuseStep 801219 = 1201829) B1201829
theorem B801235 : Blo 798342 801235 := bstep (se 1 (by rfl) ⟨600926, by rfl⟩ : syracuseStep 801235 = 1201853) B1201853
theorem B801251 : Blo 798342 801251 := bstep (se 1 (by rfl) ⟨600938, by rfl⟩ : syracuseStep 801251 = 1201877) B1201877
theorem B801267 : Blo 798342 801267 := bstep (se 1 (by rfl) ⟨600950, by rfl⟩ : syracuseStep 801267 = 1201901) B1201901
theorem B801283 : Blo 798342 801283 := bstep (se 1 (by rfl) ⟨600962, by rfl⟩ : syracuseStep 801283 = 1201925) B1201925
theorem B10271245 : Blo 798342 10271245 := bstep (se 3 (by rfl) ⟨1925858, by rfl⟩ : syracuseStep 10271245 = 3851717) B3851717
theorem B801299 : Blo 798342 801299 := bstep (se 1 (by rfl) ⟨600974, by rfl⟩ : syracuseStep 801299 = 1201949) B1201949
theorem B801315 : Blo 798342 801315 := bstep (se 1 (by rfl) ⟨600986, by rfl⟩ : syracuseStep 801315 = 1201973) B1201973
theorem B899635 : Blo 798342 899635 := bstep (se 1 (by rfl) ⟨674726, by rfl⟩ : syracuseStep 899635 = 1349453) B1349453
theorem B801331 : Blo 798342 801331 := bstep (se 1 (by rfl) ⟨600998, by rfl⟩ : syracuseStep 801331 = 1201997) B1201997
theorem B801347 : Blo 798342 801347 := bstep (se 1 (by rfl) ⟨601010, by rfl⟩ : syracuseStep 801347 = 1202021) B1202021
theorem B1522243 : Blo 798342 1522243 := bstep (se 1 (by rfl) ⟨1141682, by rfl⟩ : syracuseStep 1522243 = 2283365) B2283365
theorem B801363 : Blo 798342 801363 := bstep (se 1 (by rfl) ⟨601022, by rfl⟩ : syracuseStep 801363 = 1202045) B1202045
theorem B801379 : Blo 798342 801379 := bstep (se 1 (by rfl) ⟨601034, by rfl⟩ : syracuseStep 801379 = 1202069) B1202069
theorem B1522289 : Blo 798342 1522289 := bstep (se 2 (by rfl) ⟨570858, by rfl⟩ : syracuseStep 1522289 = 1141717) B1141717
theorem B801395 : Blo 798342 801395 := bstep (se 1 (by rfl) ⟨601046, by rfl⟩ : syracuseStep 801395 = 1202093) B1202093
theorem B801411 : Blo 798342 801411 := bstep (se 1 (by rfl) ⟨601058, by rfl⟩ : syracuseStep 801411 = 1202117) B1202117
theorem B3422861 : Blo 798342 3422861 := bstep (se 3 (by rfl) ⟨641786, by rfl⟩ : syracuseStep 3422861 = 1283573) B1283573
theorem B801427 : Blo 798342 801427 := bstep (se 1 (by rfl) ⟨601070, by rfl⟩ : syracuseStep 801427 = 1202141) B1202141
theorem B801443 : Blo 798342 801443 := bstep (se 1 (by rfl) ⟨601082, by rfl⟩ : syracuseStep 801443 = 1202165) B1202165
theorem B2701997 : Blo 798342 2701997 := bstep (se 3 (by rfl) ⟨506624, by rfl⟩ : syracuseStep 2701997 = 1013249) B1013249
theorem B801459 : Blo 798342 801459 := bstep (se 1 (by rfl) ⟨601094, by rfl⟩ : syracuseStep 801459 = 1202189) B1202189
theorem B899779 : Blo 798342 899779 := bstep (se 1 (by rfl) ⟨674834, by rfl⟩ : syracuseStep 899779 = 1349669) B1349669
theorem B1948355 : Blo 798342 1948355 := bstep (se 1 (by rfl) ⟨1461266, by rfl⟩ : syracuseStep 1948355 = 2922533) B2922533
theorem B801475 : Blo 798342 801475 := bstep (se 1 (by rfl) ⟨601106, by rfl⟩ : syracuseStep 801475 = 1202213) B1202213
theorem B801491 : Blo 798342 801491 := bstep (se 1 (by rfl) ⟨601118, by rfl⟩ : syracuseStep 801491 = 1202237) B1202237
theorem B2702051 : Blo 798342 2702051 := bstep (se 1 (by rfl) ⟨2026538, by rfl⟩ : syracuseStep 2702051 = 4053077) B4053077
theorem B801507 : Blo 798342 801507 := bstep (se 1 (by rfl) ⟨601130, by rfl⟩ : syracuseStep 801507 = 1202261) B1202261
theorem B801523 : Blo 798342 801523 := bstep (se 1 (by rfl) ⟨601142, by rfl⟩ : syracuseStep 801523 = 1202285) B1202285
theorem B801539 : Blo 798342 801539 := bstep (se 1 (by rfl) ⟨601154, by rfl⟩ : syracuseStep 801539 = 1202309) B1202309
theorem B801555 : Blo 798342 801555 := bstep (se 1 (by rfl) ⟨601166, by rfl⟩ : syracuseStep 801555 = 1202333) B1202333
theorem B801571 : Blo 798342 801571 := bstep (se 1 (by rfl) ⟨601178, by rfl⟩ : syracuseStep 801571 = 1202357) B1202357
theorem B801587 : Blo 798342 801587 := bstep (se 1 (by rfl) ⟨601190, by rfl⟩ : syracuseStep 801587 = 1202381) B1202381
theorem B801603 : Blo 798342 801603 := bstep (se 1 (by rfl) ⟨601202, by rfl⟩ : syracuseStep 801603 = 1202405) B1202405
theorem B899923 : Blo 798342 899923 := bstep (se 1 (by rfl) ⟨674942, by rfl⟩ : syracuseStep 899923 = 1349885) B1349885
theorem B801619 : Blo 798342 801619 := bstep (se 1 (by rfl) ⟨601214, by rfl⟩ : syracuseStep 801619 = 1202429) B1202429
theorem B801635 : Blo 798342 801635 := bstep (se 1 (by rfl) ⟨601226, by rfl⟩ : syracuseStep 801635 = 1202453) B1202453
theorem B801651 : Blo 798342 801651 := bstep (se 1 (by rfl) ⟨601238, by rfl⟩ : syracuseStep 801651 = 1202477) B1202477
theorem B801667 : Blo 798342 801667 := bstep (se 1 (by rfl) ⟨601250, by rfl⟩ : syracuseStep 801667 = 1202501) B1202501
theorem B1522577 : Blo 798342 1522577 := bstep (se 2 (by rfl) ⟨570966, by rfl⟩ : syracuseStep 1522577 = 1141933) B1141933
theorem B801683 : Blo 798342 801683 := bstep (se 1 (by rfl) ⟨601262, by rfl⟩ : syracuseStep 801683 = 1202525) B1202525
theorem B801699 : Blo 798342 801699 := bstep (se 1 (by rfl) ⟨601274, by rfl⟩ : syracuseStep 801699 = 1202549) B1202549
theorem B801715 : Blo 798342 801715 := bstep (se 1 (by rfl) ⟨601286, by rfl⟩ : syracuseStep 801715 = 1202573) B1202573
theorem B801731 : Blo 798342 801731 := bstep (se 1 (by rfl) ⟨601298, by rfl⟩ : syracuseStep 801731 = 1202597) B1202597
theorem B801747 : Blo 798342 801747 := bstep (se 1 (by rfl) ⟨601310, by rfl⟩ : syracuseStep 801747 = 1202621) B1202621
theorem B900067 : Blo 798342 900067 := bstep (se 1 (by rfl) ⟨675050, by rfl⟩ : syracuseStep 900067 = 1350101) B1350101
theorem B801763 : Blo 798342 801763 := bstep (se 1 (by rfl) ⟨601322, by rfl⟩ : syracuseStep 801763 = 1202645) B1202645
theorem B2702321 : Blo 798342 2702321 := bstep (se 2 (by rfl) ⟨1013370, by rfl⟩ : syracuseStep 2702321 = 2026741) B2026741
theorem B801779 : Blo 798342 801779 := bstep (se 1 (by rfl) ⟨601334, by rfl⟩ : syracuseStep 801779 = 1202669) B1202669
theorem B801795 : Blo 798342 801795 := bstep (se 1 (by rfl) ⟨601346, by rfl⟩ : syracuseStep 801795 = 1202693) B1202693
theorem B801811 : Blo 798342 801811 := bstep (se 1 (by rfl) ⟨601358, by rfl⟩ : syracuseStep 801811 = 1202717) B1202717
theorem B801827 : Blo 798342 801827 := bstep (se 1 (by rfl) ⟨601370, by rfl⟩ : syracuseStep 801827 = 1202741) B1202741
theorem B801843 : Blo 798342 801843 := bstep (se 1 (by rfl) ⟨601382, by rfl⟩ : syracuseStep 801843 = 1202765) B1202765
theorem B801859 : Blo 798342 801859 := bstep (se 1 (by rfl) ⟨601394, by rfl⟩ : syracuseStep 801859 = 1202789) B1202789
theorem B801875 : Blo 798342 801875 := bstep (se 1 (by rfl) ⟨601406, by rfl⟩ : syracuseStep 801875 = 1202813) B1202813
theorem B801891 : Blo 798342 801891 := bstep (se 1 (by rfl) ⟨601418, by rfl⟩ : syracuseStep 801891 = 1202837) B1202837
theorem B900211 : Blo 798342 900211 := bstep (se 1 (by rfl) ⟨675158, by rfl⟩ : syracuseStep 900211 = 1350317) B1350317
theorem B801907 : Blo 798342 801907 := bstep (se 1 (by rfl) ⟨601430, by rfl⟩ : syracuseStep 801907 = 1202861) B1202861
theorem B801923 : Blo 798342 801923 := bstep (se 1 (by rfl) ⟨601442, by rfl⟩ : syracuseStep 801923 = 1202885) B1202885
theorem B801939 : Blo 798342 801939 := bstep (se 1 (by rfl) ⟨601454, by rfl⟩ : syracuseStep 801939 = 1202909) B1202909
theorem B801955 : Blo 798342 801955 := bstep (se 1 (by rfl) ⟨601466, by rfl⟩ : syracuseStep 801955 = 1202933) B1202933
theorem B801971 : Blo 798342 801971 := bstep (se 1 (by rfl) ⟨601478, by rfl⟩ : syracuseStep 801971 = 1202957) B1202957
theorem B801987 : Blo 798342 801987 := bstep (se 1 (by rfl) ⟨601490, by rfl⟩ : syracuseStep 801987 = 1202981) B1202981
theorem B802003 : Blo 798342 802003 := bstep (se 1 (by rfl) ⟨601502, by rfl⟩ : syracuseStep 802003 = 1203005) B1203005
theorem B2079971 : Blo 798342 2079971 := bstep (se 1 (by rfl) ⟨1559978, by rfl⟩ : syracuseStep 2079971 = 3119957) B3119957
theorem B802019 : Blo 798342 802019 := bstep (se 1 (by rfl) ⟨601514, by rfl⟩ : syracuseStep 802019 = 1203029) B1203029
theorem B802035 : Blo 798342 802035 := bstep (se 1 (by rfl) ⟨601526, by rfl⟩ : syracuseStep 802035 = 1203053) B1203053
theorem B900355 : Blo 798342 900355 := bstep (se 1 (by rfl) ⟨675266, by rfl⟩ : syracuseStep 900355 = 1350533) B1350533
theorem B802051 : Blo 798342 802051 := bstep (se 1 (by rfl) ⟨601538, by rfl⟩ : syracuseStep 802051 = 1203077) B1203077
theorem B802067 : Blo 798342 802067 := bstep (se 1 (by rfl) ⟨601550, by rfl⟩ : syracuseStep 802067 = 1203101) B1203101
theorem B802083 : Blo 798342 802083 := bstep (se 1 (by rfl) ⟨601562, by rfl⟩ : syracuseStep 802083 = 1203125) B1203125
theorem B2276657 : Blo 798342 2276657 := bstep (se 2 (by rfl) ⟨853746, by rfl⟩ : syracuseStep 2276657 = 1707493) B1707493
theorem B802099 : Blo 798342 802099 := bstep (se 1 (by rfl) ⟨601574, by rfl⟩ : syracuseStep 802099 = 1203149) B1203149
theorem B802115 : Blo 798342 802115 := bstep (se 1 (by rfl) ⟨601586, by rfl⟩ : syracuseStep 802115 = 1203173) B1203173
theorem B802131 : Blo 798342 802131 := bstep (se 1 (by rfl) ⟨601598, by rfl⟩ : syracuseStep 802131 = 1203197) B1203197
theorem B802147 : Blo 798342 802147 := bstep (se 1 (by rfl) ⟨601610, by rfl⟩ : syracuseStep 802147 = 1203221) B1203221
theorem B802163 : Blo 798342 802163 := bstep (se 1 (by rfl) ⟨601622, by rfl⟩ : syracuseStep 802163 = 1203245) B1203245
theorem B802179 : Blo 798342 802179 := bstep (se 1 (by rfl) ⟨601634, by rfl⟩ : syracuseStep 802179 = 1203269) B1203269
theorem B900499 : Blo 798342 900499 := bstep (se 1 (by rfl) ⟨675374, by rfl⟩ : syracuseStep 900499 = 1350749) B1350749
theorem B802195 : Blo 798342 802195 := bstep (se 1 (by rfl) ⟨601646, by rfl⟩ : syracuseStep 802195 = 1203293) B1203293
theorem B802211 : Blo 798342 802211 := bstep (se 1 (by rfl) ⟨601658, by rfl⟩ : syracuseStep 802211 = 1203317) B1203317
theorem B802227 : Blo 798342 802227 := bstep (se 1 (by rfl) ⟨601670, by rfl⟩ : syracuseStep 802227 = 1203341) B1203341
theorem B802243 : Blo 798342 802243 := bstep (se 1 (by rfl) ⟨601682, by rfl⟩ : syracuseStep 802243 = 1203365) B1203365
theorem B802259 : Blo 798342 802259 := bstep (se 1 (by rfl) ⟨601694, by rfl⟩ : syracuseStep 802259 = 1203389) B1203389
theorem B802275 : Blo 798342 802275 := bstep (se 1 (by rfl) ⟨601706, by rfl⟩ : syracuseStep 802275 = 1203413) B1203413
theorem B2276849 : Blo 798342 2276849 := bstep (se 2 (by rfl) ⟨853818, by rfl⟩ : syracuseStep 2276849 = 1707637) B1707637
theorem B802291 : Blo 798342 802291 := bstep (se 1 (by rfl) ⟨601718, by rfl⟩ : syracuseStep 802291 = 1203437) B1203437
theorem B802307 : Blo 798342 802307 := bstep (se 1 (by rfl) ⟨601730, by rfl⟩ : syracuseStep 802307 = 1203461) B1203461
theorem B2702861 : Blo 798342 2702861 := bstep (se 3 (by rfl) ⟨506786, by rfl⟩ : syracuseStep 2702861 = 1013573) B1013573
theorem B802323 : Blo 798342 802323 := bstep (se 1 (by rfl) ⟨601742, by rfl⟩ : syracuseStep 802323 = 1203485) B1203485
theorem B900643 : Blo 798342 900643 := bstep (se 1 (by rfl) ⟨675482, by rfl⟩ : syracuseStep 900643 = 1350965) B1350965
theorem B802339 : Blo 798342 802339 := bstep (se 1 (by rfl) ⟨601754, by rfl⟩ : syracuseStep 802339 = 1203509) B1203509
theorem B2702915 : Blo 798342 2702915 := bstep (se 1 (by rfl) ⟨2027186, by rfl⟩ : syracuseStep 2702915 = 4054373) B4054373
theorem B4046435 : Blo 798342 4046435 := bstep (se 1 (by rfl) ⟨3034826, by rfl⟩ : syracuseStep 4046435 = 6069653) B6069653
theorem B900787 : Blo 798342 900787 := bstep (se 1 (by rfl) ⟨675590, by rfl⟩ : syracuseStep 900787 = 1351181) B1351181
theorem B900931 : Blo 798342 900931 := bstep (se 1 (by rfl) ⟨675698, by rfl⟩ : syracuseStep 900931 = 1351397) B1351397
theorem B10272581 : Blo 798342 10272581 := bstep (se 4 (by rfl) ⟨963054, by rfl⟩ : syracuseStep 10272581 = 1926109) B1926109
theorem B2703185 : Blo 798342 2703185 := bstep (se 2 (by rfl) ⟨1013694, by rfl⟩ : syracuseStep 2703185 = 2027389) B2027389
theorem B1752931 : Blo 798342 1752931 := bstep (se 1 (by rfl) ⟨1314698, by rfl⟩ : syracuseStep 1752931 = 2629397) B2629397
theorem B901075 : Blo 798342 901075 := bstep (se 1 (by rfl) ⟨675806, by rfl⟩ : syracuseStep 901075 = 1351613) B1351613
theorem B9748451 : Blo 798342 9748451 := bstep (se 1 (by rfl) ⟨7311338, by rfl⟩ : syracuseStep 9748451 = 14622677) B14622677
theorem B901219 : Blo 798342 901219 := bstep (se 1 (by rfl) ⟨675914, by rfl⟩ : syracuseStep 901219 = 1351829) B1351829
theorem B24658033 : Blo 798342 24658033 := bstep (se 2 (by rfl) ⟨9246762, by rfl⟩ : syracuseStep 24658033 = 18493525) B18493525
theorem B901363 : Blo 798342 901363 := bstep (se 1 (by rfl) ⟨676022, by rfl⟩ : syracuseStep 901363 = 1352045) B1352045
theorem B2703725 : Blo 798342 2703725 := bstep (se 3 (by rfl) ⟨506948, by rfl⟩ : syracuseStep 2703725 = 1013897) B1013897
theorem B901507 : Blo 798342 901507 := bstep (se 1 (by rfl) ⟨676130, by rfl⟩ : syracuseStep 901507 = 1352261) B1352261
theorem B4047245 : Blo 798342 4047245 := bstep (se 3 (by rfl) ⟨758858, by rfl⟩ : syracuseStep 4047245 = 1517717) B1517717
theorem B2703779 : Blo 798342 2703779 := bstep (se 1 (by rfl) ⟨2027834, by rfl⟩ : syracuseStep 2703779 = 4055669) B4055669
theorem B2277841 : Blo 798342 2277841 := bstep (se 2 (by rfl) ⟨854190, by rfl⟩ : syracuseStep 2277841 = 1708381) B1708381
theorem B901651 : Blo 798342 901651 := bstep (se 1 (by rfl) ⟨676238, by rfl⟩ : syracuseStep 901651 = 1352477) B1352477
theorem B901795 : Blo 798342 901795 := bstep (se 1 (by rfl) ⟨676346, by rfl⟩ : syracuseStep 901795 = 1352693) B1352693
theorem B2704049 : Blo 798342 2704049 := bstep (se 2 (by rfl) ⟨1014018, by rfl⟩ : syracuseStep 2704049 = 2028037) B2028037
theorem B2278115 : Blo 798342 2278115 := bstep (se 1 (by rfl) ⟨1708586, by rfl⟩ : syracuseStep 2278115 = 3417173) B3417173
theorem B901939 : Blo 798342 901939 := bstep (se 1 (by rfl) ⟨676454, by rfl⟩ : syracuseStep 901939 = 1352909) B1352909
theorem B6079373 : Blo 798342 6079373 := bstep (se 3 (by rfl) ⟨1139882, by rfl⟩ : syracuseStep 6079373 = 2279765) B2279765
theorem B2278307 : Blo 798342 2278307 := bstep (se 1 (by rfl) ⟨1708730, by rfl⟩ : syracuseStep 2278307 = 3417461) B3417461
theorem B902083 : Blo 798342 902083 := bstep (se 1 (by rfl) ⟨676562, by rfl⟩ : syracuseStep 902083 = 1353125) B1353125
theorem B3457997 : Blo 798342 3457997 := bstep (se 3 (by rfl) ⟨648374, by rfl⟩ : syracuseStep 3457997 = 1296749) B1296749
theorem B902227 : Blo 798342 902227 := bstep (se 1 (by rfl) ⟨676670, by rfl⟩ : syracuseStep 902227 = 1353341) B1353341
theorem B2704589 : Blo 798342 2704589 := bstep (se 3 (by rfl) ⟨507110, by rfl⟩ : syracuseStep 2704589 = 1014221) B1014221
theorem B902371 : Blo 798342 902371 := bstep (se 1 (by rfl) ⟨676778, by rfl⟩ : syracuseStep 902371 = 1353557) B1353557
theorem B2704643 : Blo 798342 2704643 := bstep (se 1 (by rfl) ⟨2028482, by rfl⟩ : syracuseStep 2704643 = 4056965) B4056965
theorem B902515 : Blo 798342 902515 := bstep (se 1 (by rfl) ⟨676886, by rfl⟩ : syracuseStep 902515 = 1353773) B1353773
theorem B1197521 : Blo 798342 1197521 := bstep (se 2 (by rfl) ⟨449070, by rfl⟩ : syracuseStep 1197521 = 898141) B898141
theorem B1197539 : Blo 798342 1197539 := bstep (se 1 (by rfl) ⟨898154, by rfl⟩ : syracuseStep 1197539 = 1796309) B1796309
theorem B1197569 : Blo 798342 1197569 := bstep (se 2 (by rfl) ⟨449088, by rfl⟩ : syracuseStep 1197569 = 898177) B898177
theorem B2704913 : Blo 798342 2704913 := bstep (se 2 (by rfl) ⟨1014342, by rfl⟩ : syracuseStep 2704913 = 2028685) B2028685
theorem B1197587 : Blo 798342 1197587 := bstep (se 1 (by rfl) ⟨898190, by rfl⟩ : syracuseStep 1197587 = 1796381) B1796381
theorem B1197617 : Blo 798342 1197617 := bstep (se 2 (by rfl) ⟨449106, by rfl⟩ : syracuseStep 1197617 = 898213) B898213
theorem B1197635 : Blo 798342 1197635 := bstep (se 1 (by rfl) ⟨898226, by rfl⟩ : syracuseStep 1197635 = 1796453) B1796453
theorem B1197665 : Blo 798342 1197665 := bstep (se 2 (by rfl) ⟨449124, by rfl⟩ : syracuseStep 1197665 = 898249) B898249
theorem B1197683 : Blo 798342 1197683 := bstep (se 1 (by rfl) ⟨898262, by rfl⟩ : syracuseStep 1197683 = 1796525) B1796525
theorem B1197713 : Blo 798342 1197713 := bstep (se 2 (by rfl) ⟨449142, by rfl⟩ : syracuseStep 1197713 = 898285) B898285
theorem B1197731 : Blo 798342 1197731 := bstep (se 1 (by rfl) ⟨898298, by rfl⟩ : syracuseStep 1197731 = 1796597) B1796597
theorem B1197761 : Blo 798342 1197761 := bstep (se 2 (by rfl) ⟨449160, by rfl⟩ : syracuseStep 1197761 = 898321) B898321
theorem B2279117 : Blo 798342 2279117 := bstep (se 3 (by rfl) ⟨427334, by rfl⟩ : syracuseStep 2279117 = 854669) B854669
theorem B1197779 : Blo 798342 1197779 := bstep (se 1 (by rfl) ⟨898334, by rfl⟩ : syracuseStep 1197779 = 1796669) B1796669
theorem B1197809 : Blo 798342 1197809 := bstep (se 2 (by rfl) ⟨449178, by rfl⟩ : syracuseStep 1197809 = 898357) B898357
theorem B1197827 : Blo 798342 1197827 := bstep (se 1 (by rfl) ⟨898370, by rfl⟩ : syracuseStep 1197827 = 1796741) B1796741
theorem B1197857 : Blo 798342 1197857 := bstep (se 2 (by rfl) ⟨449196, by rfl⟩ : syracuseStep 1197857 = 898393) B898393
theorem B1197875 : Blo 798342 1197875 := bstep (se 1 (by rfl) ⟨898406, by rfl⟩ : syracuseStep 1197875 = 1796813) B1796813
theorem B12994357 : Blo 798342 12994357 := bstep (se 5 (by rfl) ⟨609110, by rfl⟩ : syracuseStep 12994357 = 1218221) B1218221
theorem B1197905 : Blo 798342 1197905 := bstep (se 2 (by rfl) ⟨449214, by rfl⟩ : syracuseStep 1197905 = 898429) B898429
theorem B1197923 : Blo 798342 1197923 := bstep (se 1 (by rfl) ⟨898442, by rfl⟩ : syracuseStep 1197923 = 1796885) B1796885
theorem B1197953 : Blo 798342 1197953 := bstep (se 2 (by rfl) ⟨449232, by rfl⟩ : syracuseStep 1197953 = 898465) B898465
theorem B2279299 : Blo 798342 2279299 := bstep (se 1 (by rfl) ⟨1709474, by rfl⟩ : syracuseStep 2279299 = 3418949) B3418949
theorem B1197971 : Blo 798342 1197971 := bstep (se 1 (by rfl) ⟨898478, by rfl⟩ : syracuseStep 1197971 = 1796957) B1796957
theorem B1918883 : Blo 798342 1918883 := bstep (se 1 (by rfl) ⟨1439162, by rfl⟩ : syracuseStep 1918883 = 2878325) B2878325
theorem B1198001 : Blo 798342 1198001 := bstep (se 2 (by rfl) ⟨449250, by rfl⟩ : syracuseStep 1198001 = 898501) B898501
theorem B1198019 : Blo 798342 1198019 := bstep (se 1 (by rfl) ⟨898514, by rfl⟩ : syracuseStep 1198019 = 1797029) B1797029
theorem B1198049 : Blo 798342 1198049 := bstep (se 2 (by rfl) ⟨449268, by rfl⟩ : syracuseStep 1198049 = 898537) B898537
theorem B1198067 : Blo 798342 1198067 := bstep (se 1 (by rfl) ⟨898550, by rfl⟩ : syracuseStep 1198067 = 1797101) B1797101
theorem B1198097 : Blo 798342 1198097 := bstep (se 2 (by rfl) ⟨449286, by rfl⟩ : syracuseStep 1198097 = 898573) B898573
theorem B1198115 : Blo 798342 1198115 := bstep (se 1 (by rfl) ⟨898586, by rfl⟩ : syracuseStep 1198115 = 1797173) B1797173
theorem B2705453 : Blo 798342 2705453 := bstep (se 3 (by rfl) ⟨507272, by rfl⟩ : syracuseStep 2705453 = 1014545) B1014545
theorem B1198145 : Blo 798342 1198145 := bstep (se 2 (by rfl) ⟨449304, by rfl⟩ : syracuseStep 1198145 = 898609) B898609
theorem B1198163 : Blo 798342 1198163 := bstep (se 1 (by rfl) ⟨898622, by rfl⟩ : syracuseStep 1198163 = 1797245) B1797245
theorem B2705507 : Blo 798342 2705507 := bstep (se 1 (by rfl) ⟨2029130, by rfl⟩ : syracuseStep 2705507 = 4058261) B4058261
theorem B1198193 : Blo 798342 1198193 := bstep (se 2 (by rfl) ⟨449322, by rfl⟩ : syracuseStep 1198193 = 898645) B898645
theorem B1198211 : Blo 798342 1198211 := bstep (se 1 (by rfl) ⟨898658, by rfl⟩ : syracuseStep 1198211 = 1797317) B1797317
theorem B1230995 : Blo 798342 1230995 := bstep (se 1 (by rfl) ⟨923246, by rfl⟩ : syracuseStep 1230995 = 1846493) B1846493
theorem B1198241 : Blo 798342 1198241 := bstep (se 2 (by rfl) ⟨449340, by rfl⟩ : syracuseStep 1198241 = 898681) B898681
theorem B1198259 : Blo 798342 1198259 := bstep (se 1 (by rfl) ⟨898694, by rfl⟩ : syracuseStep 1198259 = 1797389) B1797389
theorem B1198289 : Blo 798342 1198289 := bstep (se 2 (by rfl) ⟨449358, by rfl⟩ : syracuseStep 1198289 = 898717) B898717
theorem B1198307 : Blo 798342 1198307 := bstep (se 1 (by rfl) ⟨898730, by rfl⟩ : syracuseStep 1198307 = 1797461) B1797461
theorem B1198337 : Blo 798342 1198337 := bstep (se 2 (by rfl) ⟨449376, by rfl⟩ : syracuseStep 1198337 = 898753) B898753
theorem B1198355 : Blo 798342 1198355 := bstep (se 1 (by rfl) ⟨898766, by rfl⟩ : syracuseStep 1198355 = 1797533) B1797533
theorem B1198385 : Blo 798342 1198385 := bstep (se 2 (by rfl) ⟨449394, by rfl⟩ : syracuseStep 1198385 = 898789) B898789
theorem B1198403 : Blo 798342 1198403 := bstep (se 1 (by rfl) ⟨898802, by rfl⟩ : syracuseStep 1198403 = 1797605) B1797605
theorem B1198433 : Blo 798342 1198433 := bstep (se 2 (by rfl) ⟨449412, by rfl⟩ : syracuseStep 1198433 = 898825) B898825
theorem B2279789 : Blo 798342 2279789 := bstep (se 3 (by rfl) ⟨427460, by rfl⟩ : syracuseStep 2279789 = 854921) B854921
theorem B2705777 : Blo 798342 2705777 := bstep (se 2 (by rfl) ⟨1014666, by rfl⟩ : syracuseStep 2705777 = 2029333) B2029333
theorem B1198451 : Blo 798342 1198451 := bstep (se 1 (by rfl) ⟨898838, by rfl⟩ : syracuseStep 1198451 = 1797677) B1797677
theorem B1198481 : Blo 798342 1198481 := bstep (se 2 (by rfl) ⟨449430, by rfl⟩ : syracuseStep 1198481 = 898861) B898861
theorem B1198499 : Blo 798342 1198499 := bstep (se 1 (by rfl) ⟨898874, by rfl⟩ : syracuseStep 1198499 = 1797749) B1797749
theorem B3033521 : Blo 798342 3033521 := bstep (se 2 (by rfl) ⟨1137570, by rfl⟩ : syracuseStep 3033521 = 2275141) B2275141
theorem B1198529 : Blo 798342 1198529 := bstep (se 2 (by rfl) ⟨449448, by rfl⟩ : syracuseStep 1198529 = 898897) B898897
theorem B1198547 : Blo 798342 1198547 := bstep (se 1 (by rfl) ⟨898910, by rfl⟩ : syracuseStep 1198547 = 1797821) B1797821
theorem B1198577 : Blo 798342 1198577 := bstep (se 2 (by rfl) ⟨449466, by rfl⟩ : syracuseStep 1198577 = 898933) B898933
theorem B1198595 : Blo 798342 1198595 := bstep (se 1 (by rfl) ⟨898946, by rfl⟩ : syracuseStep 1198595 = 1797893) B1797893
theorem B1198625 : Blo 798342 1198625 := bstep (se 2 (by rfl) ⟨449484, by rfl⟩ : syracuseStep 1198625 = 898969) B898969
theorem B1198643 : Blo 798342 1198643 := bstep (se 1 (by rfl) ⟨898982, by rfl⟩ : syracuseStep 1198643 = 1797965) B1797965
theorem B1919555 : Blo 798342 1919555 := bstep (se 1 (by rfl) ⟨1439666, by rfl⟩ : syracuseStep 1919555 = 2879333) B2879333
theorem B3426893 : Blo 798342 3426893 := bstep (se 3 (by rfl) ⟨642542, by rfl⟩ : syracuseStep 3426893 = 1285085) B1285085
theorem B1198673 : Blo 798342 1198673 := bstep (se 2 (by rfl) ⟨449502, by rfl⟩ : syracuseStep 1198673 = 899005) B899005
theorem B1198691 : Blo 798342 1198691 := bstep (se 1 (by rfl) ⟨899018, by rfl⟩ : syracuseStep 1198691 = 1798037) B1798037
theorem B1198721 : Blo 798342 1198721 := bstep (se 2 (by rfl) ⟨449520, by rfl⟩ : syracuseStep 1198721 = 899041) B899041
theorem B1198739 : Blo 798342 1198739 := bstep (se 1 (by rfl) ⟨899054, by rfl⟩ : syracuseStep 1198739 = 1798109) B1798109
theorem B1198769 : Blo 798342 1198769 := bstep (se 2 (by rfl) ⟨449538, by rfl⟩ : syracuseStep 1198769 = 899077) B899077
theorem B1198787 : Blo 798342 1198787 := bstep (se 1 (by rfl) ⟨899090, by rfl⟩ : syracuseStep 1198787 = 1798181) B1798181
theorem B1198817 : Blo 798342 1198817 := bstep (se 2 (by rfl) ⟨449556, by rfl⟩ : syracuseStep 1198817 = 899113) B899113
theorem B1198835 : Blo 798342 1198835 := bstep (se 1 (by rfl) ⟨899126, by rfl⟩ : syracuseStep 1198835 = 1798253) B1798253
theorem B2738947 : Blo 798342 2738947 := bstep (se 1 (by rfl) ⟨2054210, by rfl⟩ : syracuseStep 2738947 = 4108421) B4108421
theorem B1198865 : Blo 798342 1198865 := bstep (se 2 (by rfl) ⟨449574, by rfl⟩ : syracuseStep 1198865 = 899149) B899149
theorem B1198883 : Blo 798342 1198883 := bstep (se 1 (by rfl) ⟨899162, by rfl⟩ : syracuseStep 1198883 = 1798325) B1798325
theorem B1198913 : Blo 798342 1198913 := bstep (se 2 (by rfl) ⟨449592, by rfl⟩ : syracuseStep 1198913 = 899185) B899185
theorem B1919825 : Blo 798342 1919825 := bstep (se 2 (by rfl) ⟨719934, by rfl⟩ : syracuseStep 1919825 = 1439869) B1439869
theorem B1198931 : Blo 798342 1198931 := bstep (se 1 (by rfl) ⟨899198, by rfl⟩ : syracuseStep 1198931 = 1798397) B1798397
theorem B1198961 : Blo 798342 1198961 := bstep (se 2 (by rfl) ⟨449610, by rfl⟩ : syracuseStep 1198961 = 899221) B899221
theorem B1198979 : Blo 798342 1198979 := bstep (se 1 (by rfl) ⟨899234, by rfl⟩ : syracuseStep 1198979 = 1798469) B1798469
theorem B2706317 : Blo 798342 2706317 := bstep (se 3 (by rfl) ⟨507434, by rfl⟩ : syracuseStep 2706317 = 1014869) B1014869
theorem B1199009 : Blo 798342 1199009 := bstep (se 2 (by rfl) ⟨449628, by rfl⟩ : syracuseStep 1199009 = 899257) B899257
theorem B1199027 : Blo 798342 1199027 := bstep (se 1 (by rfl) ⟨899270, by rfl⟩ : syracuseStep 1199027 = 1798541) B1798541
theorem B2706371 : Blo 798342 2706371 := bstep (se 1 (by rfl) ⟨2029778, by rfl⟩ : syracuseStep 2706371 = 4059557) B4059557
theorem B1199057 : Blo 798342 1199057 := bstep (se 2 (by rfl) ⟨449646, by rfl⟩ : syracuseStep 1199057 = 899293) B899293
theorem B1199075 : Blo 798342 1199075 := bstep (se 1 (by rfl) ⟨899306, by rfl⟩ : syracuseStep 1199075 = 1798613) B1798613
theorem B1199105 : Blo 798342 1199105 := bstep (se 2 (by rfl) ⟨449664, by rfl⟩ : syracuseStep 1199105 = 899329) B899329
theorem B1199123 : Blo 798342 1199123 := bstep (se 1 (by rfl) ⟨899342, by rfl⟩ : syracuseStep 1199123 = 1798685) B1798685
theorem B1199153 : Blo 798342 1199153 := bstep (se 2 (by rfl) ⟨449682, by rfl⟩ : syracuseStep 1199153 = 899365) B899365
theorem B1199171 : Blo 798342 1199171 := bstep (se 1 (by rfl) ⟨899378, by rfl⟩ : syracuseStep 1199171 = 1798757) B1798757
theorem B3296333 : Blo 798342 3296333 := bstep (se 3 (by rfl) ⟨618062, by rfl⟩ : syracuseStep 3296333 = 1236125) B1236125
theorem B2051153 : Blo 798342 2051153 := bstep (se 2 (by rfl) ⟨769182, by rfl⟩ : syracuseStep 2051153 = 1538365) B1538365
theorem B1199201 : Blo 798342 1199201 := bstep (se 2 (by rfl) ⟨449700, by rfl⟩ : syracuseStep 1199201 = 899401) B899401
theorem B1199219 : Blo 798342 1199219 := bstep (se 1 (by rfl) ⟨899414, by rfl⟩ : syracuseStep 1199219 = 1798829) B1798829
theorem B1199249 : Blo 798342 1199249 := bstep (se 2 (by rfl) ⟨449718, by rfl⟩ : syracuseStep 1199249 = 899437) B899437
theorem B1199267 : Blo 798342 1199267 := bstep (se 1 (by rfl) ⟨899450, by rfl⟩ : syracuseStep 1199267 = 1798901) B1798901
theorem B1199297 : Blo 798342 1199297 := bstep (se 2 (by rfl) ⟨449736, by rfl⟩ : syracuseStep 1199297 = 899473) B899473
theorem B2706641 : Blo 798342 2706641 := bstep (se 2 (by rfl) ⟨1014990, by rfl⟩ : syracuseStep 2706641 = 2029981) B2029981
theorem B1199315 : Blo 798342 1199315 := bstep (se 1 (by rfl) ⟨899486, by rfl⟩ : syracuseStep 1199315 = 1798973) B1798973
theorem B1199345 : Blo 798342 1199345 := bstep (se 2 (by rfl) ⟨449754, by rfl⟩ : syracuseStep 1199345 = 899509) B899509
theorem B4050161 : Blo 798342 4050161 := bstep (se 2 (by rfl) ⟨1518810, by rfl⟩ : syracuseStep 4050161 = 3037621) B3037621
theorem B1199363 : Blo 798342 1199363 := bstep (se 1 (by rfl) ⟨899522, by rfl⟩ : syracuseStep 1199363 = 1799045) B1799045
theorem B9096461 : Blo 798342 9096461 := bstep (se 3 (by rfl) ⟨1705586, by rfl⟩ : syracuseStep 9096461 = 3411173) B3411173
theorem B1199393 : Blo 798342 1199393 := bstep (se 2 (by rfl) ⟨449772, by rfl⟩ : syracuseStep 1199393 = 899545) B899545
theorem B1199411 : Blo 798342 1199411 := bstep (se 1 (by rfl) ⟨899558, by rfl⟩ : syracuseStep 1199411 = 1799117) B1799117
theorem B13651253 : Blo 798342 13651253 := bstep (se 5 (by rfl) ⟨639902, by rfl⟩ : syracuseStep 13651253 = 1279805) B1279805
theorem B1199441 : Blo 798342 1199441 := bstep (se 2 (by rfl) ⟨449790, by rfl⟩ : syracuseStep 1199441 = 899581) B899581
theorem B1199459 : Blo 798342 1199459 := bstep (se 1 (by rfl) ⟨899594, by rfl⟩ : syracuseStep 1199459 = 1799189) B1799189
theorem B1199489 : Blo 798342 1199489 := bstep (se 2 (by rfl) ⟨449808, by rfl⟩ : syracuseStep 1199489 = 899617) B899617
theorem B1920401 : Blo 798342 1920401 := bstep (se 2 (by rfl) ⟨720150, by rfl⟩ : syracuseStep 1920401 = 1440301) B1440301
theorem B1199507 : Blo 798342 1199507 := bstep (se 1 (by rfl) ⟨899630, by rfl⟩ : syracuseStep 1199507 = 1799261) B1799261
theorem B1199537 : Blo 798342 1199537 := bstep (se 2 (by rfl) ⟨449826, by rfl⟩ : syracuseStep 1199537 = 899653) B899653
theorem B1625521 : Blo 798342 1625521 := bstep (se 2 (by rfl) ⟨609570, by rfl⟩ : syracuseStep 1625521 = 1219141) B1219141
theorem B1199555 : Blo 798342 1199555 := bstep (se 1 (by rfl) ⟨899666, by rfl⟩ : syracuseStep 1199555 = 1799333) B1799333
theorem B1199585 : Blo 798342 1199585 := bstep (se 2 (by rfl) ⟨449844, by rfl⟩ : syracuseStep 1199585 = 899689) B899689
theorem B1199603 : Blo 798342 1199603 := bstep (se 1 (by rfl) ⟨899702, by rfl⟩ : syracuseStep 1199603 = 1799405) B1799405
theorem B5131781 : Blo 798342 5131781 := bstep (se 4 (by rfl) ⟨481104, by rfl⟩ : syracuseStep 5131781 = 962209) B962209
theorem B2280973 : Blo 798342 2280973 := bstep (se 3 (by rfl) ⟨427682, by rfl⟩ : syracuseStep 2280973 = 855365) B855365
theorem B1297937 : Blo 798342 1297937 := bstep (se 2 (by rfl) ⟨486726, by rfl⟩ : syracuseStep 1297937 = 973453) B973453
theorem B1199633 : Blo 798342 1199633 := bstep (se 2 (by rfl) ⟨449862, by rfl⟩ : syracuseStep 1199633 = 899725) B899725
theorem B1199651 : Blo 798342 1199651 := bstep (se 1 (by rfl) ⟨899738, by rfl⟩ : syracuseStep 1199651 = 1799477) B1799477
theorem B1756721 : Blo 798342 1756721 := bstep (se 2 (by rfl) ⟨658770, by rfl⟩ : syracuseStep 1756721 = 1317541) B1317541
theorem B1199681 : Blo 798342 1199681 := bstep (se 2 (by rfl) ⟨449880, by rfl⟩ : syracuseStep 1199681 = 899761) B899761
theorem B1920593 : Blo 798342 1920593 := bstep (se 2 (by rfl) ⟨720222, by rfl⟩ : syracuseStep 1920593 = 1440445) B1440445
theorem B1199699 : Blo 798342 1199699 := bstep (se 1 (by rfl) ⟨899774, by rfl⟩ : syracuseStep 1199699 = 1799549) B1799549
theorem B1199729 : Blo 798342 1199729 := bstep (se 2 (by rfl) ⟨449898, by rfl⟩ : syracuseStep 1199729 = 899797) B899797
theorem B1199747 : Blo 798342 1199747 := bstep (se 1 (by rfl) ⟨899810, by rfl⟩ : syracuseStep 1199747 = 1799621) B1799621
theorem B1199777 : Blo 798342 1199777 := bstep (se 2 (by rfl) ⟨449916, by rfl⟩ : syracuseStep 1199777 = 899833) B899833
theorem B1199795 : Blo 798342 1199795 := bstep (se 1 (by rfl) ⟨899846, by rfl⟩ : syracuseStep 1199795 = 1799693) B1799693
theorem B1199825 : Blo 798342 1199825 := bstep (se 2 (by rfl) ⟨449934, by rfl⟩ : syracuseStep 1199825 = 899869) B899869
theorem B1199843 : Blo 798342 1199843 := bstep (se 1 (by rfl) ⟨899882, by rfl⟩ : syracuseStep 1199843 = 1799765) B1799765
theorem B2707181 : Blo 798342 2707181 := bstep (se 3 (by rfl) ⟨507596, by rfl⟩ : syracuseStep 2707181 = 1015193) B1015193
theorem B6082289 : Blo 798342 6082289 := bstep (se 2 (by rfl) ⟨2280858, by rfl⟩ : syracuseStep 6082289 = 4561717) B4561717
theorem B1199873 : Blo 798342 1199873 := bstep (se 2 (by rfl) ⟨449952, by rfl⟩ : syracuseStep 1199873 = 899905) B899905
theorem B1199891 : Blo 798342 1199891 := bstep (se 1 (by rfl) ⟨899918, by rfl⟩ : syracuseStep 1199891 = 1799837) B1799837
theorem B2707235 : Blo 798342 2707235 := bstep (se 1 (by rfl) ⟨2030426, by rfl⟩ : syracuseStep 2707235 = 4060853) B4060853
theorem B1199921 : Blo 798342 1199921 := bstep (se 2 (by rfl) ⟨449970, by rfl⟩ : syracuseStep 1199921 = 899941) B899941
theorem B1199939 : Blo 798342 1199939 := bstep (se 1 (by rfl) ⟨899954, by rfl⟩ : syracuseStep 1199939 = 1799909) B1799909
theorem B1199969 : Blo 798342 1199969 := bstep (se 2 (by rfl) ⟨449988, by rfl⟩ : syracuseStep 1199969 = 899977) B899977
theorem B3034979 : Blo 798342 3034979 := bstep (se 1 (by rfl) ⟨2276234, by rfl⟩ : syracuseStep 3034979 = 4552469) B4552469
theorem B1920881 : Blo 798342 1920881 := bstep (se 2 (by rfl) ⟨720330, by rfl⟩ : syracuseStep 1920881 = 1440661) B1440661
theorem B1199987 : Blo 798342 1199987 := bstep (se 1 (by rfl) ⟨899990, by rfl⟩ : syracuseStep 1199987 = 1799981) B1799981
theorem B1200017 : Blo 798342 1200017 := bstep (se 2 (by rfl) ⟨450006, by rfl⟩ : syracuseStep 1200017 = 900013) B900013
theorem B1200035 : Blo 798342 1200035 := bstep (se 1 (by rfl) ⟨900026, by rfl⟩ : syracuseStep 1200035 = 1800053) B1800053
theorem B1200065 : Blo 798342 1200065 := bstep (se 2 (by rfl) ⟨450024, by rfl⟩ : syracuseStep 1200065 = 900049) B900049
theorem B1200083 : Blo 798342 1200083 := bstep (se 1 (by rfl) ⟨900062, by rfl⟩ : syracuseStep 1200083 = 1800125) B1800125
theorem B1200113 : Blo 798342 1200113 := bstep (se 2 (by rfl) ⟨450042, by rfl⟩ : syracuseStep 1200113 = 900085) B900085
theorem B1200131 : Blo 798342 1200131 := bstep (se 1 (by rfl) ⟨900098, by rfl⟩ : syracuseStep 1200131 = 1800197) B1800197
theorem B1200161 : Blo 798342 1200161 := bstep (se 2 (by rfl) ⟨450060, by rfl⟩ : syracuseStep 1200161 = 900121) B900121
theorem B2707505 : Blo 798342 2707505 := bstep (se 2 (by rfl) ⟨1015314, by rfl⟩ : syracuseStep 2707505 = 2030629) B2030629
theorem B1200179 : Blo 798342 1200179 := bstep (se 1 (by rfl) ⟨900134, by rfl⟩ : syracuseStep 1200179 = 1800269) B1800269
theorem B1200209 : Blo 798342 1200209 := bstep (se 2 (by rfl) ⟨450078, by rfl⟩ : syracuseStep 1200209 = 900157) B900157
theorem B1626193 : Blo 798342 1626193 := bstep (se 2 (by rfl) ⟨609822, by rfl⟩ : syracuseStep 1626193 = 1219645) B1219645
theorem B1200227 : Blo 798342 1200227 := bstep (se 1 (by rfl) ⟨900170, by rfl⟩ : syracuseStep 1200227 = 1800341) B1800341
theorem B1200257 : Blo 798342 1200257 := bstep (se 2 (by rfl) ⟨450096, by rfl⟩ : syracuseStep 1200257 = 900193) B900193
theorem B1200275 : Blo 798342 1200275 := bstep (se 1 (by rfl) ⟨900206, by rfl⟩ : syracuseStep 1200275 = 1800413) B1800413
theorem B1200305 : Blo 798342 1200305 := bstep (se 2 (by rfl) ⟨450114, by rfl⟩ : syracuseStep 1200305 = 900229) B900229
theorem B1200323 : Blo 798342 1200323 := bstep (se 1 (by rfl) ⟨900242, by rfl⟩ : syracuseStep 1200323 = 1800485) B1800485
theorem B9752773 : Blo 798342 9752773 := bstep (se 4 (by rfl) ⟨914322, by rfl⟩ : syracuseStep 9752773 = 1828645) B1828645
theorem B1200353 : Blo 798342 1200353 := bstep (se 2 (by rfl) ⟨450132, by rfl⟩ : syracuseStep 1200353 = 900265) B900265
theorem B27709667 : Blo 798342 27709667 := bstep (se 1 (by rfl) ⟨20782250, by rfl⟩ : syracuseStep 27709667 = 41564501) B41564501
theorem B1200371 : Blo 798342 1200371 := bstep (se 1 (by rfl) ⟨900278, by rfl⟩ : syracuseStep 1200371 = 1800557) B1800557
theorem B1626371 : Blo 798342 1626371 := bstep (se 1 (by rfl) ⟨1219778, by rfl⟩ : syracuseStep 1626371 = 2439557) B2439557
theorem B1200401 : Blo 798342 1200401 := bstep (se 2 (by rfl) ⟨450150, by rfl⟩ : syracuseStep 1200401 = 900301) B900301
theorem B1200419 : Blo 798342 1200419 := bstep (se 1 (by rfl) ⟨900314, by rfl⟩ : syracuseStep 1200419 = 1800629) B1800629
theorem B1200449 : Blo 798342 1200449 := bstep (se 2 (by rfl) ⟨450168, by rfl⟩ : syracuseStep 1200449 = 900337) B900337
theorem B3658061 : Blo 798342 3658061 := bstep (se 3 (by rfl) ⟨685886, by rfl⟩ : syracuseStep 3658061 = 1371773) B1371773
theorem B1200467 : Blo 798342 1200467 := bstep (se 1 (by rfl) ⟨900350, by rfl⟩ : syracuseStep 1200467 = 1800701) B1800701
theorem B1200497 : Blo 798342 1200497 := bstep (se 2 (by rfl) ⟨450186, by rfl⟩ : syracuseStep 1200497 = 900373) B900373
theorem B1200515 : Blo 798342 1200515 := bstep (se 1 (by rfl) ⟨900386, by rfl⟩ : syracuseStep 1200515 = 1800773) B1800773
theorem B1200545 : Blo 798342 1200545 := bstep (se 2 (by rfl) ⟨450204, by rfl⟩ : syracuseStep 1200545 = 900409) B900409
theorem B1200563 : Blo 798342 1200563 := bstep (se 1 (by rfl) ⟨900422, by rfl⟩ : syracuseStep 1200563 = 1800845) B1800845
theorem B1200593 : Blo 798342 1200593 := bstep (se 2 (by rfl) ⟨450222, by rfl⟩ : syracuseStep 1200593 = 900445) B900445
theorem B1200611 : Blo 798342 1200611 := bstep (se 1 (by rfl) ⟨900458, by rfl⟩ : syracuseStep 1200611 = 1800917) B1800917
theorem B1200641 : Blo 798342 1200641 := bstep (se 2 (by rfl) ⟨450240, by rfl⟩ : syracuseStep 1200641 = 900481) B900481
theorem B1200659 : Blo 798342 1200659 := bstep (se 1 (by rfl) ⟨900494, by rfl⟩ : syracuseStep 1200659 = 1800989) B1800989
theorem B1200689 : Blo 798342 1200689 := bstep (se 2 (by rfl) ⟨450258, by rfl⟩ : syracuseStep 1200689 = 900517) B900517
theorem B2282033 : Blo 798342 2282033 := bstep (se 2 (by rfl) ⟨855762, by rfl⟩ : syracuseStep 2282033 = 1711525) B1711525
theorem B1200707 : Blo 798342 1200707 := bstep (se 1 (by rfl) ⟨900530, by rfl⟩ : syracuseStep 1200707 = 1801061) B1801061
theorem B1200737 : Blo 798342 1200737 := bstep (se 2 (by rfl) ⟨450276, by rfl⟩ : syracuseStep 1200737 = 900553) B900553
theorem B3854947 : Blo 798342 3854947 := bstep (se 1 (by rfl) ⟨2891210, by rfl⟩ : syracuseStep 3854947 = 5782421) B5782421
theorem B1200755 : Blo 798342 1200755 := bstep (se 1 (by rfl) ⟨900566, by rfl⟩ : syracuseStep 1200755 = 1801133) B1801133
theorem B1200785 : Blo 798342 1200785 := bstep (se 2 (by rfl) ⟨450294, by rfl⟩ : syracuseStep 1200785 = 900589) B900589
theorem B4051619 : Blo 798342 4051619 := bstep (se 1 (by rfl) ⟨3038714, by rfl⟩ : syracuseStep 4051619 = 6077429) B6077429
theorem B1200803 : Blo 798342 1200803 := bstep (se 1 (by rfl) ⟨900602, by rfl⟩ : syracuseStep 1200803 = 1801205) B1801205
theorem B1200833 : Blo 798342 1200833 := bstep (se 2 (by rfl) ⟨450312, by rfl⟩ : syracuseStep 1200833 = 900625) B900625
theorem B1200851 : Blo 798342 1200851 := bstep (se 1 (by rfl) ⟨900638, by rfl⟩ : syracuseStep 1200851 = 1801277) B1801277
theorem B10277603 : Blo 798342 10277603 := bstep (se 1 (by rfl) ⟨7708202, by rfl⟩ : syracuseStep 10277603 = 15416405) B15416405
theorem B7688945 : Blo 798342 7688945 := bstep (se 2 (by rfl) ⟨2883354, by rfl⟩ : syracuseStep 7688945 = 5766709) B5766709
theorem B1200881 : Blo 798342 1200881 := bstep (se 2 (by rfl) ⟨450330, by rfl⟩ : syracuseStep 1200881 = 900661) B900661
theorem B1200899 : Blo 798342 1200899 := bstep (se 1 (by rfl) ⟨900674, by rfl⟩ : syracuseStep 1200899 = 1801349) B1801349
theorem B1200929 : Blo 798342 1200929 := bstep (se 2 (by rfl) ⟨450348, by rfl⟩ : syracuseStep 1200929 = 900697) B900697
theorem B1200947 : Blo 798342 1200947 := bstep (se 1 (by rfl) ⟨900710, by rfl⟩ : syracuseStep 1200947 = 1801421) B1801421
theorem B3035981 : Blo 798342 3035981 := bstep (se 3 (by rfl) ⟨569246, by rfl⟩ : syracuseStep 3035981 = 1138493) B1138493
theorem B1200977 : Blo 798342 1200977 := bstep (se 2 (by rfl) ⟨450366, by rfl⟩ : syracuseStep 1200977 = 900733) B900733
theorem B1200995 : Blo 798342 1200995 := bstep (se 1 (by rfl) ⟨900746, by rfl⟩ : syracuseStep 1200995 = 1801493) B1801493
theorem B2052977 : Blo 798342 2052977 := bstep (se 2 (by rfl) ⟨769866, by rfl⟩ : syracuseStep 2052977 = 1539733) B1539733
theorem B1201025 : Blo 798342 1201025 := bstep (se 2 (by rfl) ⟨450384, by rfl⟩ : syracuseStep 1201025 = 900769) B900769
theorem B1201043 : Blo 798342 1201043 := bstep (se 1 (by rfl) ⟨900782, by rfl⟩ : syracuseStep 1201043 = 1801565) B1801565
theorem B1201073 : Blo 798342 1201073 := bstep (se 2 (by rfl) ⟨450402, by rfl⟩ : syracuseStep 1201073 = 900805) B900805
theorem B1823683 : Blo 798342 1823683 := bstep (se 1 (by rfl) ⟨1367762, by rfl⟩ : syracuseStep 1823683 = 2735525) B2735525
theorem B1201091 : Blo 798342 1201091 := bstep (se 1 (by rfl) ⟨900818, by rfl⟩ : syracuseStep 1201091 = 1801637) B1801637
theorem B1201121 : Blo 798342 1201121 := bstep (se 2 (by rfl) ⟨450420, by rfl⟩ : syracuseStep 1201121 = 900841) B900841
theorem B1201139 : Blo 798342 1201139 := bstep (se 1 (by rfl) ⟨900854, by rfl⟩ : syracuseStep 1201139 = 1801709) B1801709
theorem B1201169 : Blo 798342 1201169 := bstep (se 2 (by rfl) ⟨450438, by rfl⟩ : syracuseStep 1201169 = 900877) B900877
theorem B1201187 : Blo 798342 1201187 := bstep (se 1 (by rfl) ⟨900890, by rfl⟩ : syracuseStep 1201187 = 1801781) B1801781
theorem B1201217 : Blo 798342 1201217 := bstep (se 2 (by rfl) ⟨450456, by rfl⟩ : syracuseStep 1201217 = 900913) B900913
theorem B1758275 : Blo 798342 1758275 := bstep (se 1 (by rfl) ⟨1318706, by rfl⟩ : syracuseStep 1758275 = 2637413) B2637413
theorem B1201235 : Blo 798342 1201235 := bstep (se 1 (by rfl) ⟨900926, by rfl⟩ : syracuseStep 1201235 = 1801853) B1801853
theorem B1201265 : Blo 798342 1201265 := bstep (se 2 (by rfl) ⟨450474, by rfl⟩ : syracuseStep 1201265 = 900949) B900949
theorem B1201283 : Blo 798342 1201283 := bstep (se 1 (by rfl) ⟨900962, by rfl⟩ : syracuseStep 1201283 = 1801925) B1801925
theorem B1201313 : Blo 798342 1201313 := bstep (se 2 (by rfl) ⟨450492, by rfl⟩ : syracuseStep 1201313 = 900985) B900985
theorem B1201331 : Blo 798342 1201331 := bstep (se 1 (by rfl) ⟨900998, by rfl⟩ : syracuseStep 1201331 = 1801997) B1801997
theorem B1201361 : Blo 798342 1201361 := bstep (se 2 (by rfl) ⟨450510, by rfl⟩ : syracuseStep 1201361 = 901021) B901021
theorem B2282705 : Blo 798342 2282705 := bstep (se 2 (by rfl) ⟨856014, by rfl⟩ : syracuseStep 2282705 = 1712029) B1712029
theorem B1201379 : Blo 798342 1201379 := bstep (se 1 (by rfl) ⟨901034, by rfl⟩ : syracuseStep 1201379 = 1802069) B1802069
theorem B1201409 : Blo 798342 1201409 := bstep (se 2 (by rfl) ⟨450528, by rfl⟩ : syracuseStep 1201409 = 901057) B901057
theorem B1201427 : Blo 798342 1201427 := bstep (se 1 (by rfl) ⟨901070, by rfl⟩ : syracuseStep 1201427 = 1802141) B1802141
theorem B1299761 : Blo 798342 1299761 := bstep (se 2 (by rfl) ⟨487410, by rfl⟩ : syracuseStep 1299761 = 974821) B974821
theorem B1201457 : Blo 798342 1201457 := bstep (se 2 (by rfl) ⟨450546, by rfl⟩ : syracuseStep 1201457 = 901093) B901093
theorem B1201475 : Blo 798342 1201475 := bstep (se 1 (by rfl) ⟨901106, by rfl⟩ : syracuseStep 1201475 = 1802213) B1802213
theorem B1201505 : Blo 798342 1201505 := bstep (se 2 (by rfl) ⟨450564, by rfl⟩ : syracuseStep 1201505 = 901129) B901129
theorem B1201523 : Blo 798342 1201523 := bstep (se 1 (by rfl) ⟨901142, by rfl⟩ : syracuseStep 1201523 = 1802285) B1802285
theorem B1201553 : Blo 798342 1201553 := bstep (se 2 (by rfl) ⟨450582, by rfl⟩ : syracuseStep 1201553 = 901165) B901165
theorem B1201571 : Blo 798342 1201571 := bstep (se 1 (by rfl) ⟨901178, by rfl⟩ : syracuseStep 1201571 = 1802357) B1802357
theorem B4609457 : Blo 798342 4609457 := bstep (se 2 (by rfl) ⟨1728546, by rfl⟩ : syracuseStep 4609457 = 3457093) B3457093
theorem B1201601 : Blo 798342 1201601 := bstep (se 2 (by rfl) ⟨450600, by rfl⟩ : syracuseStep 1201601 = 901201) B901201
theorem B4052429 : Blo 798342 4052429 := bstep (se 3 (by rfl) ⟨759830, by rfl⟩ : syracuseStep 4052429 = 1519661) B1519661
theorem B1201619 : Blo 798342 1201619 := bstep (se 1 (by rfl) ⟨901214, by rfl⟩ : syracuseStep 1201619 = 1802429) B1802429
theorem B1201649 : Blo 798342 1201649 := bstep (se 2 (by rfl) ⟨450618, by rfl⟩ : syracuseStep 1201649 = 901237) B901237
theorem B1201667 : Blo 798342 1201667 := bstep (se 1 (by rfl) ⟨901250, by rfl⟩ : syracuseStep 1201667 = 1802501) B1802501
theorem B1201697 : Blo 798342 1201697 := bstep (se 2 (by rfl) ⟨450636, by rfl⟩ : syracuseStep 1201697 = 901273) B901273
theorem B2741795 : Blo 798342 2741795 := bstep (se 1 (by rfl) ⟨2056346, by rfl⟩ : syracuseStep 2741795 = 4112693) B4112693
theorem B1201715 : Blo 798342 1201715 := bstep (se 1 (by rfl) ⟨901286, by rfl⟩ : syracuseStep 1201715 = 1802573) B1802573
theorem B1201745 : Blo 798342 1201745 := bstep (se 2 (by rfl) ⟨450654, by rfl⟩ : syracuseStep 1201745 = 901309) B901309
theorem B1201763 : Blo 798342 1201763 := bstep (se 1 (by rfl) ⟨901322, by rfl⟩ : syracuseStep 1201763 = 1802645) B1802645
theorem B1201793 : Blo 798342 1201793 := bstep (se 2 (by rfl) ⟨450672, by rfl⟩ : syracuseStep 1201793 = 901345) B901345
theorem B1332883 : Blo 798342 1332883 := bstep (se 1 (by rfl) ⟨999662, by rfl⟩ : syracuseStep 1332883 = 1999325) B1999325
theorem B1201811 : Blo 798342 1201811 := bstep (se 1 (by rfl) ⟨901358, by rfl⟩ : syracuseStep 1201811 = 1802717) B1802717
theorem B1201841 : Blo 798342 1201841 := bstep (se 2 (by rfl) ⟨450690, by rfl⟩ : syracuseStep 1201841 = 901381) B901381
theorem B1201859 : Blo 798342 1201859 := bstep (se 1 (by rfl) ⟨901394, by rfl⟩ : syracuseStep 1201859 = 1802789) B1802789
theorem B1201889 : Blo 798342 1201889 := bstep (se 2 (by rfl) ⟨450708, by rfl⟩ : syracuseStep 1201889 = 901417) B901417
theorem B1201907 : Blo 798342 1201907 := bstep (se 1 (by rfl) ⟨901430, by rfl⟩ : syracuseStep 1201907 = 1802861) B1802861
theorem B1201937 : Blo 798342 1201937 := bstep (se 2 (by rfl) ⟨450726, by rfl⟩ : syracuseStep 1201937 = 901453) B901453
theorem B1201955 : Blo 798342 1201955 := bstep (se 1 (by rfl) ⟨901466, by rfl⟩ : syracuseStep 1201955 = 1802933) B1802933
theorem B1201985 : Blo 798342 1201985 := bstep (se 2 (by rfl) ⟨450744, by rfl⟩ : syracuseStep 1201985 = 901489) B901489
theorem B2742083 : Blo 798342 2742083 := bstep (se 1 (by rfl) ⟨2056562, by rfl⟩ : syracuseStep 2742083 = 4113125) B4113125
theorem B1202003 : Blo 798342 1202003 := bstep (se 1 (by rfl) ⟨901502, by rfl⟩ : syracuseStep 1202003 = 1803005) B1803005
theorem B2021233 : Blo 798342 2021233 := bstep (se 2 (by rfl) ⟨757962, by rfl⟩ : syracuseStep 2021233 = 1515925) B1515925
theorem B1202033 : Blo 798342 1202033 := bstep (se 2 (by rfl) ⟨450762, by rfl⟩ : syracuseStep 1202033 = 901525) B901525
theorem B1202051 : Blo 798342 1202051 := bstep (se 1 (by rfl) ⟨901538, by rfl⟩ : syracuseStep 1202051 = 1803077) B1803077
theorem B1202081 : Blo 798342 1202081 := bstep (se 2 (by rfl) ⟨450780, by rfl⟩ : syracuseStep 1202081 = 901561) B901561
theorem B1202099 : Blo 798342 1202099 := bstep (se 1 (by rfl) ⟨901574, by rfl⟩ : syracuseStep 1202099 = 1803149) B1803149
theorem B1202129 : Blo 798342 1202129 := bstep (se 2 (by rfl) ⟨450798, by rfl⟩ : syracuseStep 1202129 = 901597) B901597
theorem B7690211 : Blo 798342 7690211 := bstep (se 1 (by rfl) ⟨5767658, by rfl⟩ : syracuseStep 7690211 = 11535317) B11535317
theorem B1202147 : Blo 798342 1202147 := bstep (se 1 (by rfl) ⟨901610, by rfl⟩ : syracuseStep 1202147 = 1803221) B1803221
theorem B2283491 : Blo 798342 2283491 := bstep (se 1 (by rfl) ⟨1712618, by rfl⟩ : syracuseStep 2283491 = 3425237) B3425237
theorem B1202177 : Blo 798342 1202177 := bstep (se 2 (by rfl) ⟨450816, by rfl⟩ : syracuseStep 1202177 = 901633) B901633
theorem B1202195 : Blo 798342 1202195 := bstep (se 1 (by rfl) ⟨901646, by rfl⟩ : syracuseStep 1202195 = 1803293) B1803293
theorem B1202225 : Blo 798342 1202225 := bstep (se 2 (by rfl) ⟨450834, by rfl⟩ : syracuseStep 1202225 = 901669) B901669
theorem B1366067 : Blo 798342 1366067 := bstep (se 1 (by rfl) ⟨1024550, by rfl⟩ : syracuseStep 1366067 = 2049101) B2049101
theorem B1202243 : Blo 798342 1202243 := bstep (se 1 (by rfl) ⟨901682, by rfl⟩ : syracuseStep 1202243 = 1803365) B1803365
theorem B1202273 : Blo 798342 1202273 := bstep (se 2 (by rfl) ⟨450852, by rfl⟩ : syracuseStep 1202273 = 901705) B901705
theorem B4610147 : Blo 798342 4610147 := bstep (se 1 (by rfl) ⟨3457610, by rfl⟩ : syracuseStep 4610147 = 6915221) B6915221
theorem B9099377 : Blo 798342 9099377 := bstep (se 2 (by rfl) ⟨3412266, by rfl⟩ : syracuseStep 9099377 = 6824533) B6824533
theorem B1202291 : Blo 798342 1202291 := bstep (se 1 (by rfl) ⟨901718, by rfl⟩ : syracuseStep 1202291 = 1803437) B1803437
theorem B2021507 : Blo 798342 2021507 := bstep (se 1 (by rfl) ⟨1516130, by rfl⟩ : syracuseStep 2021507 = 3032261) B3032261
theorem B1202321 : Blo 798342 1202321 := bstep (se 2 (by rfl) ⟨450870, by rfl⟩ : syracuseStep 1202321 = 901741) B901741
theorem B1202339 : Blo 798342 1202339 := bstep (se 1 (by rfl) ⟨901754, by rfl⟩ : syracuseStep 1202339 = 1803509) B1803509
theorem B1202369 : Blo 798342 1202369 := bstep (se 2 (by rfl) ⟨450888, by rfl⟩ : syracuseStep 1202369 = 901777) B901777
theorem B1202387 : Blo 798342 1202387 := bstep (se 1 (by rfl) ⟨901790, by rfl⟩ : syracuseStep 1202387 = 1803581) B1803581
theorem B1202417 : Blo 798342 1202417 := bstep (se 2 (by rfl) ⟨450906, by rfl⟩ : syracuseStep 1202417 = 901813) B901813
theorem B1202435 : Blo 798342 1202435 := bstep (se 1 (by rfl) ⟨901826, by rfl⟩ : syracuseStep 1202435 = 1803653) B1803653
theorem B1202465 : Blo 798342 1202465 := bstep (se 2 (by rfl) ⟨450924, by rfl⟩ : syracuseStep 1202465 = 901849) B901849
theorem B2283821 : Blo 798342 2283821 := bstep (se 3 (by rfl) ⟨428216, by rfl⟩ : syracuseStep 2283821 = 856433) B856433
theorem B1202483 : Blo 798342 1202483 := bstep (se 1 (by rfl) ⟨901862, by rfl⟩ : syracuseStep 1202483 = 1803725) B1803725
theorem B2021699 : Blo 798342 2021699 := bstep (se 1 (by rfl) ⟨1516274, by rfl⟩ : syracuseStep 2021699 = 3032549) B3032549
theorem B9263429 : Blo 798342 9263429 := bstep (se 4 (by rfl) ⟨868446, by rfl⟩ : syracuseStep 9263429 = 1736893) B1736893
theorem B1202513 : Blo 798342 1202513 := bstep (se 2 (by rfl) ⟨450942, by rfl⟩ : syracuseStep 1202513 = 901885) B901885
theorem B1202531 : Blo 798342 1202531 := bstep (se 1 (by rfl) ⟨901898, by rfl⟩ : syracuseStep 1202531 = 1803797) B1803797
theorem B2283889 : Blo 798342 2283889 := bstep (se 2 (by rfl) ⟨856458, by rfl⟩ : syracuseStep 2283889 = 1712917) B1712917
theorem B1202561 : Blo 798342 1202561 := bstep (se 2 (by rfl) ⟨450960, by rfl⟩ : syracuseStep 1202561 = 901921) B901921
theorem B1202579 : Blo 798342 1202579 := bstep (se 1 (by rfl) ⟨901934, by rfl⟩ : syracuseStep 1202579 = 1803869) B1803869
theorem B1202609 : Blo 798342 1202609 := bstep (se 2 (by rfl) ⟨450978, by rfl⟩ : syracuseStep 1202609 = 901957) B901957
theorem B1202627 : Blo 798342 1202627 := bstep (se 1 (by rfl) ⟨901970, by rfl⟩ : syracuseStep 1202627 = 1803941) B1803941
theorem B1202657 : Blo 798342 1202657 := bstep (se 2 (by rfl) ⟨450996, by rfl⟩ : syracuseStep 1202657 = 901993) B901993
theorem B1202675 : Blo 798342 1202675 := bstep (se 1 (by rfl) ⟨902006, by rfl⟩ : syracuseStep 1202675 = 1804013) B1804013
theorem B1202705 : Blo 798342 1202705 := bstep (se 2 (by rfl) ⟨451014, by rfl⟩ : syracuseStep 1202705 = 902029) B902029
theorem B1202723 : Blo 798342 1202723 := bstep (se 1 (by rfl) ⟨902042, by rfl⟩ : syracuseStep 1202723 = 1804085) B1804085
theorem B1202753 : Blo 798342 1202753 := bstep (se 2 (by rfl) ⟨451032, by rfl⟩ : syracuseStep 1202753 = 902065) B902065
theorem B1137235 : Blo 798342 1137235 := bstep (se 1 (by rfl) ⟨852926, by rfl⟩ : syracuseStep 1137235 = 1705853) B1705853
theorem B1202771 : Blo 798342 1202771 := bstep (se 1 (by rfl) ⟨902078, by rfl⟩ : syracuseStep 1202771 = 1804157) B1804157
theorem B1202801 : Blo 798342 1202801 := bstep (se 2 (by rfl) ⟨451050, by rfl⟩ : syracuseStep 1202801 = 902101) B902101
theorem B1202819 : Blo 798342 1202819 := bstep (se 1 (by rfl) ⟨902114, by rfl⟩ : syracuseStep 1202819 = 1804229) B1804229
theorem B2284163 : Blo 798342 2284163 := bstep (se 1 (by rfl) ⟨1713122, by rfl⟩ : syracuseStep 2284163 = 3426245) B3426245
theorem B1202849 : Blo 798342 1202849 := bstep (se 2 (by rfl) ⟨451068, by rfl⟩ : syracuseStep 1202849 = 902137) B902137
theorem B1137331 : Blo 798342 1137331 := bstep (se 1 (by rfl) ⟨852998, by rfl⟩ : syracuseStep 1137331 = 1705997) B1705997
theorem B1202867 : Blo 798342 1202867 := bstep (se 1 (by rfl) ⟨902150, by rfl⟩ : syracuseStep 1202867 = 1804301) B1804301
theorem B1202897 : Blo 798342 1202897 := bstep (se 2 (by rfl) ⟨451086, by rfl⟩ : syracuseStep 1202897 = 902173) B902173
theorem B1202915 : Blo 798342 1202915 := bstep (se 1 (by rfl) ⟨902186, by rfl⟩ : syracuseStep 1202915 = 1804373) B1804373
theorem B1202945 : Blo 798342 1202945 := bstep (se 2 (by rfl) ⟨451104, by rfl⟩ : syracuseStep 1202945 = 902209) B902209
theorem B1202963 : Blo 798342 1202963 := bstep (se 1 (by rfl) ⟨902222, by rfl⟩ : syracuseStep 1202963 = 1804445) B1804445
theorem B1202993 : Blo 798342 1202993 := bstep (se 2 (by rfl) ⟨451122, by rfl⟩ : syracuseStep 1202993 = 902245) B902245
theorem B1203011 : Blo 798342 1203011 := bstep (se 1 (by rfl) ⟨902258, by rfl⟩ : syracuseStep 1203011 = 1804517) B1804517
theorem B1203041 : Blo 798342 1203041 := bstep (se 2 (by rfl) ⟨451140, by rfl⟩ : syracuseStep 1203041 = 902281) B902281
theorem B1203059 : Blo 798342 1203059 := bstep (se 1 (by rfl) ⟨902294, by rfl⟩ : syracuseStep 1203059 = 1804589) B1804589
theorem B3038093 : Blo 798342 3038093 := bstep (se 3 (by rfl) ⟨569642, by rfl⟩ : syracuseStep 3038093 = 1139285) B1139285
theorem B1203089 : Blo 798342 1203089 := bstep (se 2 (by rfl) ⟨451158, by rfl⟩ : syracuseStep 1203089 = 902317) B902317
theorem B1203107 : Blo 798342 1203107 := bstep (se 1 (by rfl) ⟨902330, by rfl⟩ : syracuseStep 1203107 = 1804661) B1804661
theorem B1203137 : Blo 798342 1203137 := bstep (se 2 (by rfl) ⟨451176, by rfl⟩ : syracuseStep 1203137 = 902353) B902353
theorem B1203155 : Blo 798342 1203155 := bstep (se 1 (by rfl) ⟨902366, by rfl⟩ : syracuseStep 1203155 = 1804733) B1804733
theorem B1203185 : Blo 798342 1203185 := bstep (se 2 (by rfl) ⟨451194, by rfl⟩ : syracuseStep 1203185 = 902389) B902389
theorem B1203203 : Blo 798342 1203203 := bstep (se 1 (by rfl) ⟨902402, by rfl⟩ : syracuseStep 1203203 = 1804805) B1804805
theorem B1203233 : Blo 798342 1203233 := bstep (se 2 (by rfl) ⟨451212, by rfl⟩ : syracuseStep 1203233 = 902425) B902425
theorem B1203251 : Blo 798342 1203251 := bstep (se 1 (by rfl) ⟨902438, by rfl⟩ : syracuseStep 1203251 = 1804877) B1804877
theorem B1203281 : Blo 798342 1203281 := bstep (se 2 (by rfl) ⟨451230, by rfl⟩ : syracuseStep 1203281 = 902461) B902461
theorem B5626979 : Blo 798342 5626979 := bstep (se 1 (by rfl) ⟨4220234, by rfl⟩ : syracuseStep 5626979 = 8440469) B8440469
theorem B1203299 : Blo 798342 1203299 := bstep (se 1 (by rfl) ⟨902474, by rfl⟩ : syracuseStep 1203299 = 1804949) B1804949
theorem B1203329 : Blo 798342 1203329 := bstep (se 2 (by rfl) ⟨451248, by rfl⟩ : syracuseStep 1203329 = 902497) B902497
theorem B1203347 : Blo 798342 1203347 := bstep (se 1 (by rfl) ⟨902510, by rfl⟩ : syracuseStep 1203347 = 1805021) B1805021
theorem B1137827 : Blo 798342 1137827 := bstep (se 1 (by rfl) ⟨853370, by rfl⟩ : syracuseStep 1137827 = 1706741) B1706741
theorem B1203377 : Blo 798342 1203377 := bstep (se 2 (by rfl) ⟨451266, by rfl⟩ : syracuseStep 1203377 = 902533) B902533
theorem B1203395 : Blo 798342 1203395 := bstep (se 1 (by rfl) ⟨902546, by rfl⟩ : syracuseStep 1203395 = 1805093) B1805093
theorem B1203425 : Blo 798342 1203425 := bstep (se 2 (by rfl) ⟨451284, by rfl⟩ : syracuseStep 1203425 = 902569) B902569
theorem B2022641 : Blo 798342 2022641 := bstep (se 2 (by rfl) ⟨758490, by rfl⟩ : syracuseStep 2022641 = 1516981) B1516981
theorem B1203443 : Blo 798342 1203443 := bstep (se 1 (by rfl) ⟨902582, by rfl⟩ : syracuseStep 1203443 = 1805165) B1805165
theorem B1203473 : Blo 798342 1203473 := bstep (se 2 (by rfl) ⟨451302, by rfl⟩ : syracuseStep 1203473 = 902605) B902605
theorem B2022691 : Blo 798342 2022691 := bstep (se 1 (by rfl) ⟨1517018, by rfl⟩ : syracuseStep 2022691 = 3034037) B3034037
theorem B1203491 : Blo 798342 1203491 := bstep (se 1 (by rfl) ⟨902618, by rfl⟩ : syracuseStep 1203491 = 1805237) B1805237
theorem B2022833 : Blo 798342 2022833 := bstep (se 2 (by rfl) ⟨758562, by rfl⟩ : syracuseStep 2022833 = 1517125) B1517125
theorem B20799089 : Blo 798342 20799089 := bstep (se 2 (by rfl) ⟨7799658, by rfl⟩ : syracuseStep 20799089 = 15599317) B15599317
theorem B3038897 : Blo 798342 3038897 := bstep (se 2 (by rfl) ⟨1139586, by rfl⟩ : syracuseStep 3038897 = 2279173) B2279173
theorem B1138465 : Blo 798342 1138465 := bstep (se 2 (by rfl) ⟨426924, by rfl⟩ : syracuseStep 1138465 = 853849) B853849
theorem B4874053 : Blo 798342 4874053 := bstep (se 4 (by rfl) ⟨456942, by rfl⟩ : syracuseStep 4874053 = 913885) B913885
theorem B6840389 : Blo 798342 6840389 := bstep (se 4 (by rfl) ⟨641286, by rfl⟩ : syracuseStep 6840389 = 1282573) B1282573
theorem B1138801 : Blo 798342 1138801 := bstep (se 2 (by rfl) ⟨427050, by rfl⟩ : syracuseStep 1138801 = 854101) B854101
theorem B4055345 : Blo 798342 4055345 := bstep (se 2 (by rfl) ⟨1520754, by rfl⟩ : syracuseStep 4055345 = 3041509) B3041509
theorem B3039565 : Blo 798342 3039565 := bstep (se 3 (by rfl) ⟨569918, by rfl⟩ : syracuseStep 3039565 = 1139837) B1139837
theorem B2023825 : Blo 798342 2023825 := bstep (se 2 (by rfl) ⟨758934, by rfl⟩ : syracuseStep 2023825 = 1517869) B1517869
theorem B38986181 : Blo 798342 38986181 := bstep (se 4 (by rfl) ⟨3654954, by rfl⟩ : syracuseStep 38986181 = 7309909) B7309909
theorem B8643185 : Blo 798342 8643185 := bstep (se 2 (by rfl) ⟨3241194, by rfl⟩ : syracuseStep 8643185 = 6482389) B6482389
theorem B2024099 : Blo 798342 2024099 := bstep (se 1 (by rfl) ⟨1518074, by rfl⟩ : syracuseStep 2024099 = 3036149) B3036149
theorem B1139393 : Blo 798342 1139393 := bstep (se 2 (by rfl) ⟨427272, by rfl⟩ : syracuseStep 1139393 = 854545) B854545
theorem B2024291 : Blo 798342 2024291 := bstep (se 1 (by rfl) ⟨1518218, by rfl⟩ : syracuseStep 2024291 = 3036437) B3036437
theorem B3040355 : Blo 798342 3040355 := bstep (se 1 (by rfl) ⟨2280266, by rfl⟩ : syracuseStep 3040355 = 4560533) B4560533
theorem B2221229 : Blo 798342 2221229 := bstep (se 3 (by rfl) ⟨416480, by rfl⟩ : syracuseStep 2221229 = 832961) B832961
theorem B1139923 : Blo 798342 1139923 := bstep (se 1 (by rfl) ⟨854942, by rfl⟩ : syracuseStep 1139923 = 1709885) B1709885
theorem B1926467 : Blo 798342 1926467 := bstep (se 1 (by rfl) ⟨1444850, by rfl⟩ : syracuseStep 1926467 = 2889701) B2889701
theorem B1140259 : Blo 798342 1140259 := bstep (se 1 (by rfl) ⟨855194, by rfl⟩ : syracuseStep 1140259 = 1710389) B1710389
theorem B5138083 : Blo 798342 5138083 := bstep (se 1 (by rfl) ⟨3853562, by rfl⟩ : syracuseStep 5138083 = 7707125) B7707125
theorem B4056803 : Blo 798342 4056803 := bstep (se 1 (by rfl) ⟨3042602, by rfl⟩ : syracuseStep 4056803 = 6085205) B6085205
theorem B3041009 : Blo 798342 3041009 := bstep (se 2 (by rfl) ⟨1140378, by rfl⟩ : syracuseStep 3041009 = 2280757) B2280757
theorem B2025233 : Blo 798342 2025233 := bstep (se 2 (by rfl) ⟨759462, by rfl⟩ : syracuseStep 2025233 = 1518925) B1518925
theorem B2025283 : Blo 798342 2025283 := bstep (se 1 (by rfl) ⟨1518962, by rfl⟩ : syracuseStep 2025283 = 3037925) B3037925
theorem B2025425 : Blo 798342 2025425 := bstep (se 2 (by rfl) ⟨759534, by rfl⟩ : syracuseStep 2025425 = 1519069) B1519069
theorem B1140817 : Blo 798342 1140817 := bstep (se 2 (by rfl) ⟨427806, by rfl⟩ : syracuseStep 1140817 = 855613) B855613
theorem B911459 : Blo 798342 911459 := bstep (se 1 (by rfl) ⟨683594, by rfl⟩ : syracuseStep 911459 = 1367189) B1367189
theorem B1140851 : Blo 798342 1140851 := bstep (se 1 (by rfl) ⟨855638, by rfl⟩ : syracuseStep 1140851 = 1711277) B1711277
theorem B1796273 : Blo 798342 1796273 := bstep (se 2 (by rfl) ⟨673602, by rfl⟩ : syracuseStep 1796273 = 1347205) B1347205
theorem B1796291 : Blo 798342 1796291 := bstep (se 1 (by rfl) ⟨1347218, by rfl⟩ : syracuseStep 1796291 = 2694437) B2694437
theorem B10414307 : Blo 798342 10414307 := bstep (se 1 (by rfl) ⟨7810730, by rfl⟩ : syracuseStep 10414307 = 15621461) B15621461
theorem B813283 : Blo 798342 813283 := bstep (se 1 (by rfl) ⟨609962, by rfl⟩ : syracuseStep 813283 = 1219925) B1219925
theorem B4548869 : Blo 798342 4548869 := bstep (se 4 (by rfl) ⟨426456, by rfl⟩ : syracuseStep 4548869 = 852913) B852913
theorem B1796561 : Blo 798342 1796561 := bstep (se 2 (by rfl) ⟨673710, by rfl⟩ : syracuseStep 1796561 = 1347421) B1347421
theorem B1796579 : Blo 798342 1796579 := bstep (se 1 (by rfl) ⟨1347434, by rfl⟩ : syracuseStep 1796579 = 2694869) B2694869
theorem B4057613 : Blo 798342 4057613 := bstep (se 3 (by rfl) ⟨760802, by rfl⟩ : syracuseStep 4057613 = 1521605) B1521605
theorem B2878051 : Blo 798342 2878051 := bstep (se 1 (by rfl) ⟨2158538, by rfl⟩ : syracuseStep 2878051 = 4317077) B4317077
theorem B5139085 : Blo 798342 5139085 := bstep (se 3 (by rfl) ⟨963578, by rfl⟩ : syracuseStep 5139085 = 1927157) B1927157
theorem B1141409 : Blo 798342 1141409 := bstep (se 2 (by rfl) ⟨428028, by rfl⟩ : syracuseStep 1141409 = 856057) B856057
theorem B1370801 : Blo 798342 1370801 := bstep (se 2 (by rfl) ⟨514050, by rfl⟩ : syracuseStep 1370801 = 1028101) B1028101
theorem B1796849 : Blo 798342 1796849 := bstep (se 2 (by rfl) ⟨673818, by rfl⟩ : syracuseStep 1796849 = 1347637) B1347637
theorem B1141489 : Blo 798342 1141489 := bstep (se 2 (by rfl) ⟨428058, by rfl⟩ : syracuseStep 1141489 = 856117) B856117
theorem B1796867 : Blo 798342 1796867 := bstep (se 1 (by rfl) ⟨1347650, by rfl⟩ : syracuseStep 1796867 = 2695301) B2695301
theorem B5761891 : Blo 798342 5761891 := bstep (se 1 (by rfl) ⟨4321418, by rfl⟩ : syracuseStep 5761891 = 8642837) B8642837
theorem B4549553 : Blo 798342 4549553 := bstep (se 2 (by rfl) ⟨1706082, by rfl⟩ : syracuseStep 4549553 = 3412165) B3412165
theorem B2026417 : Blo 798342 2026417 := bstep (se 2 (by rfl) ⟨759906, by rfl⟩ : syracuseStep 2026417 = 1519813) B1519813
theorem B1797137 : Blo 798342 1797137 := bstep (se 2 (by rfl) ⟨673926, by rfl⟩ : syracuseStep 1797137 = 1347853) B1347853
theorem B1797155 : Blo 798342 1797155 := bstep (se 1 (by rfl) ⟨1347866, by rfl⟩ : syracuseStep 1797155 = 2695733) B2695733
theorem B8219717 : Blo 798342 8219717 := bstep (se 4 (by rfl) ⟨770598, by rfl⟩ : syracuseStep 8219717 = 1541197) B1541197
theorem B1010819 : Blo 798342 1010819 := bstep (se 1 (by rfl) ⟨758114, by rfl⟩ : syracuseStep 1010819 = 1516229) B1516229
theorem B3042467 : Blo 798342 3042467 := bstep (se 1 (by rfl) ⟨2281850, by rfl⟩ : syracuseStep 3042467 = 4563701) B4563701
theorem B3042481 : Blo 798342 3042481 := bstep (se 2 (by rfl) ⟨1140930, by rfl⟩ : syracuseStep 3042481 = 2281861) B2281861
theorem B2026691 : Blo 798342 2026691 := bstep (se 1 (by rfl) ⟨1520018, by rfl⟩ : syracuseStep 2026691 = 3040037) B3040037
theorem B3239153 : Blo 798342 3239153 := bstep (se 2 (by rfl) ⟨1214682, by rfl⟩ : syracuseStep 3239153 = 2429365) B2429365
theorem B1797425 : Blo 798342 1797425 := bstep (se 2 (by rfl) ⟨674034, by rfl⟩ : syracuseStep 1797425 = 1348069) B1348069
theorem B1797443 : Blo 798342 1797443 := bstep (se 1 (by rfl) ⟨1348082, by rfl⟩ : syracuseStep 1797443 = 2696165) B2696165
theorem B2026883 : Blo 798342 2026883 := bstep (se 1 (by rfl) ⟨1520162, by rfl⟩ : syracuseStep 2026883 = 3040325) B3040325
theorem B2158019 : Blo 798342 2158019 := bstep (se 1 (by rfl) ⟨1618514, by rfl⟩ : syracuseStep 2158019 = 3237029) B3237029
theorem B1142275 : Blo 798342 1142275 := bstep (se 1 (by rfl) ⟨856706, by rfl⟩ : syracuseStep 1142275 = 1713413) B1713413
theorem B1797713 : Blo 798342 1797713 := bstep (se 2 (by rfl) ⟨674142, by rfl⟩ : syracuseStep 1797713 = 1348285) B1348285
theorem B1797731 : Blo 798342 1797731 := bstep (se 1 (by rfl) ⟨1348298, by rfl⟩ : syracuseStep 1797731 = 2696597) B2696597
theorem B1011523 : Blo 798342 1011523 := bstep (se 1 (by rfl) ⟨758642, by rfl⟩ : syracuseStep 1011523 = 1517285) B1517285
theorem B1798001 : Blo 798342 1798001 := bstep (se 2 (by rfl) ⟨674250, by rfl⟩ : syracuseStep 1798001 = 1348501) B1348501
theorem B1798019 : Blo 798342 1798019 := bstep (se 1 (by rfl) ⟨1348514, by rfl⟩ : syracuseStep 1798019 = 2697029) B2697029
theorem B1011619 : Blo 798342 1011619 := bstep (se 1 (by rfl) ⟨758714, by rfl⟩ : syracuseStep 1011619 = 1517429) B1517429
theorem B1798289 : Blo 798342 1798289 := bstep (se 2 (by rfl) ⟨674358, by rfl⟩ : syracuseStep 1798289 = 1348717) B1348717
theorem B1798307 : Blo 798342 1798307 := bstep (se 1 (by rfl) ⟨1348730, by rfl⟩ : syracuseStep 1798307 = 2697461) B2697461
theorem B2027825 : Blo 798342 2027825 := bstep (se 2 (by rfl) ⟨760434, by rfl⟩ : syracuseStep 2027825 = 1520869) B1520869
theorem B1732963 : Blo 798342 1732963 := bstep (se 1 (by rfl) ⟨1299722, by rfl⟩ : syracuseStep 1732963 = 2599445) B2599445
theorem B2027875 : Blo 798342 2027875 := bstep (se 1 (by rfl) ⟨1520906, by rfl⟩ : syracuseStep 2027875 = 3041813) B3041813
theorem B4551011 : Blo 798342 4551011 := bstep (se 1 (by rfl) ⟨3413258, by rfl⟩ : syracuseStep 4551011 = 6826517) B6826517
theorem B1012115 : Blo 798342 1012115 := bstep (se 1 (by rfl) ⟨759086, by rfl⟩ : syracuseStep 1012115 = 1518173) B1518173
theorem B1798577 : Blo 798342 1798577 := bstep (se 2 (by rfl) ⟨674466, by rfl⟩ : syracuseStep 1798577 = 1348933) B1348933
theorem B1798595 : Blo 798342 1798595 := bstep (se 1 (by rfl) ⟨1348946, by rfl⟩ : syracuseStep 1798595 = 2697893) B2697893
theorem B2159057 : Blo 798342 2159057 := bstep (se 2 (by rfl) ⟨809646, by rfl⟩ : syracuseStep 2159057 = 1619293) B1619293
theorem B2028017 : Blo 798342 2028017 := bstep (se 2 (by rfl) ⟨760506, by rfl⟩ : syracuseStep 2028017 = 1521013) B1521013
theorem B3043939 : Blo 798342 3043939 := bstep (se 1 (by rfl) ⟨2282954, by rfl⟩ : syracuseStep 3043939 = 4565909) B4565909
theorem B1798865 : Blo 798342 1798865 := bstep (se 2 (by rfl) ⟨674574, by rfl⟩ : syracuseStep 1798865 = 1349149) B1349149
theorem B1798883 : Blo 798342 1798883 := bstep (se 1 (by rfl) ⟨1349162, by rfl⟩ : syracuseStep 1798883 = 2698325) B2698325
theorem B1799153 : Blo 798342 1799153 := bstep (se 2 (by rfl) ⟨674682, by rfl⟩ : syracuseStep 1799153 = 1349365) B1349365
theorem B1799171 : Blo 798342 1799171 := bstep (se 1 (by rfl) ⟨1349378, by rfl⟩ : syracuseStep 1799171 = 2698757) B2698757
theorem B10417205 : Blo 798342 10417205 := bstep (se 5 (by rfl) ⟨488306, by rfl⟩ : syracuseStep 10417205 = 976613) B976613
theorem B1012819 : Blo 798342 1012819 := bstep (se 1 (by rfl) ⟨759614, by rfl⟩ : syracuseStep 1012819 = 1519229) B1519229
theorem B1012915 : Blo 798342 1012915 := bstep (se 1 (by rfl) ⟨759686, by rfl⟩ : syracuseStep 1012915 = 1519373) B1519373
theorem B1799441 : Blo 798342 1799441 := bstep (se 2 (by rfl) ⟨674790, by rfl⟩ : syracuseStep 1799441 = 1349581) B1349581
theorem B1799459 : Blo 798342 1799459 := bstep (se 1 (by rfl) ⟨1349594, by rfl⟩ : syracuseStep 1799459 = 2699189) B2699189
theorem B4060529 : Blo 798342 4060529 := bstep (se 2 (by rfl) ⟨1522698, by rfl⟩ : syracuseStep 4060529 = 3045397) B3045397
theorem B8648117 : Blo 798342 8648117 := bstep (se 5 (by rfl) ⟨405380, by rfl⟩ : syracuseStep 8648117 = 810761) B810761
theorem B2029009 : Blo 798342 2029009 := bstep (se 2 (by rfl) ⟨760878, by rfl⟩ : syracuseStep 2029009 = 1521757) B1521757
theorem B1799729 : Blo 798342 1799729 := bstep (se 2 (by rfl) ⟨674898, by rfl⟩ : syracuseStep 1799729 = 1349797) B1349797
theorem B1799747 : Blo 798342 1799747 := bstep (se 1 (by rfl) ⟨1349810, by rfl⟩ : syracuseStep 1799747 = 2699621) B2699621
theorem B1013411 : Blo 798342 1013411 := bstep (se 1 (by rfl) ⟨760058, by rfl⟩ : syracuseStep 1013411 = 1520117) B1520117
theorem B2029283 : Blo 798342 2029283 := bstep (se 1 (by rfl) ⟨1521962, by rfl⟩ : syracuseStep 2029283 = 3043925) B3043925
theorem B6944525 : Blo 798342 6944525 := bstep (se 3 (by rfl) ⟨1302098, by rfl⟩ : syracuseStep 6944525 = 2604197) B2604197
theorem B4323149 : Blo 798342 4323149 := bstep (se 3 (by rfl) ⟨810590, by rfl⟩ : syracuseStep 4323149 = 1621181) B1621181
theorem B1800017 : Blo 798342 1800017 := bstep (se 2 (by rfl) ⟨675006, by rfl⟩ : syracuseStep 1800017 = 1350013) B1350013
theorem B1800035 : Blo 798342 1800035 := bstep (se 1 (by rfl) ⟨1350026, by rfl⟩ : syracuseStep 1800035 = 2700053) B2700053
theorem B2029475 : Blo 798342 2029475 := bstep (se 1 (by rfl) ⟨1522106, by rfl⟩ : syracuseStep 2029475 = 3044213) B3044213
theorem B1800305 : Blo 798342 1800305 := bstep (se 2 (by rfl) ⟨675114, by rfl⟩ : syracuseStep 1800305 = 1350229) B1350229
theorem B1800323 : Blo 798342 1800323 := bstep (se 1 (by rfl) ⟨1350242, by rfl⟩ : syracuseStep 1800323 = 2700485) B2700485
theorem B1014115 : Blo 798342 1014115 := bstep (se 1 (by rfl) ⟨760586, by rfl⟩ : syracuseStep 1014115 = 1521173) B1521173
theorem B1800593 : Blo 798342 1800593 := bstep (se 2 (by rfl) ⟨675222, by rfl⟩ : syracuseStep 1800593 = 1350445) B1350445
theorem B2193809 : Blo 798342 2193809 := bstep (se 2 (by rfl) ⟨822678, by rfl⟩ : syracuseStep 2193809 = 1645357) B1645357
theorem B1800611 : Blo 798342 1800611 := bstep (se 1 (by rfl) ⟨1350458, by rfl⟩ : syracuseStep 1800611 = 2700917) B2700917
theorem B1014211 : Blo 798342 1014211 := bstep (se 1 (by rfl) ⟨760658, by rfl⟩ : syracuseStep 1014211 = 1521317) B1521317
theorem B2161133 : Blo 798342 2161133 := bstep (se 3 (by rfl) ⟨405212, by rfl⟩ : syracuseStep 2161133 = 810425) B810425
theorem B1800881 : Blo 798342 1800881 := bstep (se 2 (by rfl) ⟨675330, by rfl⟩ : syracuseStep 1800881 = 1350661) B1350661
theorem B1800899 : Blo 798342 1800899 := bstep (se 1 (by rfl) ⟨1350674, by rfl⟩ : syracuseStep 1800899 = 2701349) B2701349
theorem B3046157 : Blo 798342 3046157 := bstep (se 3 (by rfl) ⟨571154, by rfl⟩ : syracuseStep 3046157 = 1142309) B1142309
theorem B2030417 : Blo 798342 2030417 := bstep (se 2 (by rfl) ⟨761406, by rfl⟩ : syracuseStep 2030417 = 1522813) B1522813
theorem B2030467 : Blo 798342 2030467 := bstep (se 1 (by rfl) ⟨1522850, by rfl⟩ : syracuseStep 2030467 = 3045701) B3045701
theorem B1014707 : Blo 798342 1014707 := bstep (se 1 (by rfl) ⟨761030, by rfl⟩ : syracuseStep 1014707 = 1522061) B1522061
theorem B1801169 : Blo 798342 1801169 := bstep (se 2 (by rfl) ⟨675438, by rfl⟩ : syracuseStep 1801169 = 1350877) B1350877
theorem B1801187 : Blo 798342 1801187 := bstep (se 1 (by rfl) ⟨1350890, by rfl⟩ : syracuseStep 1801187 = 2701781) B2701781
theorem B1080307 : Blo 798342 1080307 := bstep (se 1 (by rfl) ⟨810230, by rfl⟩ : syracuseStep 1080307 = 1620461) B1620461
theorem B2030609 : Blo 798342 2030609 := bstep (se 2 (by rfl) ⟨761478, by rfl⟩ : syracuseStep 2030609 = 1522957) B1522957
theorem B1801457 : Blo 798342 1801457 := bstep (se 2 (by rfl) ⟨675546, by rfl⟩ : syracuseStep 1801457 = 1351093) B1351093
theorem B1801475 : Blo 798342 1801475 := bstep (se 1 (by rfl) ⟨1351106, by rfl⟩ : syracuseStep 1801475 = 2702213) B2702213
theorem B4554245 : Blo 798342 4554245 := bstep (se 4 (by rfl) ⟨426960, by rfl⟩ : syracuseStep 4554245 = 853921) B853921
theorem B1801745 : Blo 798342 1801745 := bstep (se 2 (by rfl) ⟨675654, by rfl⟩ : syracuseStep 1801745 = 1351309) B1351309
theorem B1801763 : Blo 798342 1801763 := bstep (se 1 (by rfl) ⟨1351322, by rfl⟩ : syracuseStep 1801763 = 2702645) B2702645
theorem B1015411 : Blo 798342 1015411 := bstep (se 1 (by rfl) ⟨761558, by rfl⟩ : syracuseStep 1015411 = 1523117) B1523117
theorem B1802033 : Blo 798342 1802033 := bstep (se 2 (by rfl) ⟨675762, by rfl⟩ : syracuseStep 1802033 = 1351525) B1351525
theorem B1802051 : Blo 798342 1802051 := bstep (se 1 (by rfl) ⟨1351538, by rfl⟩ : syracuseStep 1802051 = 2703077) B2703077
theorem B4554701 : Blo 798342 4554701 := bstep (se 3 (by rfl) ⟨854006, by rfl⟩ : syracuseStep 4554701 = 1708013) B1708013
theorem B1802393 : Blo 798342 1802393 := bstep (se 2 (by rfl) ⟨675897, by rfl⟩ : syracuseStep 1802393 = 1351795) B1351795
theorem B1802483 : Blo 798342 1802483 := bstep (se 1 (by rfl) ⟨1351862, by rfl⟩ : syracuseStep 1802483 = 2703725) B2703725
theorem B1802519 : Blo 798342 1802519 := bstep (se 1 (by rfl) ⟨1351889, by rfl⟩ : syracuseStep 1802519 = 2703779) B2703779
theorem B1802699 : Blo 798342 1802699 := bstep (se 1 (by rfl) ⟨1352024, by rfl⟩ : syracuseStep 1802699 = 2704049) B2704049
theorem B2884061 : Blo 798342 2884061 := bstep (se 3 (by rfl) ⟨540761, by rfl⟩ : syracuseStep 2884061 = 1081523) B1081523
theorem B1802753 : Blo 798342 1802753 := bstep (se 2 (by rfl) ⟨676032, by rfl⟩ : syracuseStep 1802753 = 1352065) B1352065
theorem B1802969 : Blo 798342 1802969 := bstep (se 2 (by rfl) ⟨676113, by rfl⟩ : syracuseStep 1802969 = 1352227) B1352227
theorem B1803059 : Blo 798342 1803059 := bstep (se 1 (by rfl) ⟨1352294, by rfl⟩ : syracuseStep 1803059 = 2704589) B2704589
theorem B1803095 : Blo 798342 1803095 := bstep (se 1 (by rfl) ⟨1352321, by rfl⟩ : syracuseStep 1803095 = 2704643) B2704643
theorem B6489011 : Blo 798342 6489011 := bstep (se 1 (by rfl) ⟨4866758, by rfl⟩ : syracuseStep 6489011 = 9733517) B9733517
theorem B5473241 : Blo 798342 5473241 := bstep (se 2 (by rfl) ⟨2052465, by rfl⟩ : syracuseStep 5473241 = 4104931) B4104931
theorem B1803275 : Blo 798342 1803275 := bstep (se 1 (by rfl) ⟨1352456, by rfl⟩ : syracuseStep 1803275 = 2704913) B2704913
theorem B1803329 : Blo 798342 1803329 := bstep (se 2 (by rfl) ⟨676248, by rfl⟩ : syracuseStep 1803329 = 1352497) B1352497
theorem B1279255 : Blo 798342 1279255 := bstep (se 1 (by rfl) ⟨959441, by rfl⟩ : syracuseStep 1279255 = 1918883) B1918883
theorem B1803545 : Blo 798342 1803545 := bstep (se 2 (by rfl) ⟨676329, by rfl⟩ : syracuseStep 1803545 = 1352659) B1352659
theorem B1803635 : Blo 798342 1803635 := bstep (se 1 (by rfl) ⟨1352726, by rfl⟩ : syracuseStep 1803635 = 2705453) B2705453
theorem B1803671 : Blo 798342 1803671 := bstep (se 1 (by rfl) ⟨1352753, by rfl⟩ : syracuseStep 1803671 = 2705507) B2705507
theorem B1803851 : Blo 798342 1803851 := bstep (se 1 (by rfl) ⟨1352888, by rfl⟩ : syracuseStep 1803851 = 2705777) B2705777
theorem B1443415 : Blo 798342 1443415 := bstep (se 1 (by rfl) ⟨1082561, by rfl⟩ : syracuseStep 1443415 = 2165123) B2165123
theorem B1803905 : Blo 798342 1803905 := bstep (se 2 (by rfl) ⟨676464, by rfl⟩ : syracuseStep 1803905 = 1352929) B1352929
theorem B6063821 : Blo 798342 6063821 := bstep (se 3 (by rfl) ⟨1136966, by rfl⟩ : syracuseStep 6063821 = 2273933) B2273933
theorem B1279703 : Blo 798342 1279703 := bstep (se 1 (by rfl) ⟨959777, by rfl⟩ : syracuseStep 1279703 = 1919555) B1919555
theorem B1804121 : Blo 798342 1804121 := bstep (se 2 (by rfl) ⟨676545, by rfl⟩ : syracuseStep 1804121 = 1353091) B1353091
theorem B1279883 : Blo 798342 1279883 := bstep (se 1 (by rfl) ⟨959912, by rfl⟩ : syracuseStep 1279883 = 1919825) B1919825
theorem B1804211 : Blo 798342 1804211 := bstep (se 1 (by rfl) ⟨1353158, by rfl⟩ : syracuseStep 1804211 = 2706317) B2706317
theorem B1804247 : Blo 798342 1804247 := bstep (se 1 (by rfl) ⟨1353185, by rfl⟩ : syracuseStep 1804247 = 2706371) B2706371
theorem B3082333 : Blo 798342 3082333 := bstep (se 3 (by rfl) ⟨577937, by rfl⟩ : syracuseStep 3082333 = 1155875) B1155875
theorem B1804427 : Blo 798342 1804427 := bstep (se 1 (by rfl) ⟨1353320, by rfl⟩ : syracuseStep 1804427 = 2706641) B2706641
theorem B6064307 : Blo 798342 6064307 := bstep (se 1 (by rfl) ⟨4548230, by rfl⟩ : syracuseStep 6064307 = 9096461) B9096461
theorem B1804481 : Blo 798342 1804481 := bstep (se 2 (by rfl) ⟨676680, by rfl⟩ : syracuseStep 1804481 = 1353361) B1353361
theorem B6850777 : Blo 798342 6850777 := bstep (se 2 (by rfl) ⟨2569041, by rfl⟩ : syracuseStep 6850777 = 5138083) B5138083
theorem B854263 : Blo 798342 854263 := bstep (se 1 (by rfl) ⟨640697, by rfl⟩ : syracuseStep 854263 = 1281395) B1281395
theorem B1280267 : Blo 798342 1280267 := bstep (se 1 (by rfl) ⟨960200, by rfl⟩ : syracuseStep 1280267 = 1920401) B1920401
theorem B1706305 : Blo 798342 1706305 := bstep (se 2 (by rfl) ⟨639864, by rfl⟩ : syracuseStep 1706305 = 1279729) B1279729
theorem B1280395 : Blo 798342 1280395 := bstep (se 1 (by rfl) ⟨960296, by rfl⟩ : syracuseStep 1280395 = 1920593) B1920593
theorem B1804697 : Blo 798342 1804697 := bstep (se 2 (by rfl) ⟨676761, by rfl⟩ : syracuseStep 1804697 = 1353523) B1353523
theorem B1804787 : Blo 798342 1804787 := bstep (se 1 (by rfl) ⟨1353590, by rfl⟩ : syracuseStep 1804787 = 2707181) B2707181
theorem B1804823 : Blo 798342 1804823 := bstep (se 1 (by rfl) ⟨1353617, by rfl⟩ : syracuseStep 1804823 = 2707235) B2707235
theorem B7801379 : Blo 798342 7801379 := bstep (se 1 (by rfl) ⟨5851034, by rfl⟩ : syracuseStep 7801379 = 11702069) B11702069
theorem B3410525 : Blo 798342 3410525 := bstep (se 3 (by rfl) ⟨639473, by rfl⟩ : syracuseStep 3410525 = 1278947) B1278947
theorem B1805003 : Blo 798342 1805003 := bstep (se 1 (by rfl) ⟨1353752, by rfl⟩ : syracuseStep 1805003 = 2707505) B2707505
theorem B1805057 : Blo 798342 1805057 := bstep (se 2 (by rfl) ⟨676896, by rfl⟩ : syracuseStep 1805057 = 1353793) B1353793
theorem B2165555 : Blo 798342 2165555 := bstep (se 1 (by rfl) ⟨1624166, by rfl⟩ : syracuseStep 2165555 = 3248333) B3248333
theorem B23071553 : Blo 798342 23071553 := bstep (se 2 (by rfl) ⟨8651832, by rfl⟩ : syracuseStep 23071553 = 17303665) B17303665
theorem B1084247 : Blo 798342 1084247 := bstep (se 1 (by rfl) ⟨813185, by rfl⟩ : syracuseStep 1084247 = 1626371) B1626371
theorem B1706903 : Blo 798342 1706903 := bstep (se 1 (by rfl) ⟨1280177, by rfl⟩ : syracuseStep 1706903 = 2560355) B2560355
theorem B9112499 : Blo 798342 9112499 := bstep (se 1 (by rfl) ⟨6834374, by rfl⟩ : syracuseStep 9112499 = 13668749) B13668749
theorem B855083 : Blo 798342 855083 := bstep (se 1 (by rfl) ⟨641312, by rfl⟩ : syracuseStep 855083 = 1282625) B1282625
theorem B4557869 : Blo 798342 4557869 := bstep (se 3 (by rfl) ⟨854600, by rfl⟩ : syracuseStep 4557869 = 1709201) B1709201
theorem B1281113 : Blo 798342 1281113 := bstep (se 2 (by rfl) ⟨480417, by rfl⟩ : syracuseStep 1281113 = 960835) B960835
theorem B6851735 : Blo 798342 6851735 := bstep (se 1 (by rfl) ⟨5138801, by rfl⟩ : syracuseStep 6851735 = 10277603) B10277603
theorem B1281305 : Blo 798342 1281305 := bstep (se 2 (by rfl) ⟨480489, by rfl⟩ : syracuseStep 1281305 = 960979) B960979
theorem B3837401 : Blo 798342 3837401 := bstep (se 2 (by rfl) ⟨1439025, by rfl⟩ : syracuseStep 3837401 = 2878051) B2878051
theorem B6852113 : Blo 798342 6852113 := bstep (se 2 (by rfl) ⟨2569542, by rfl⟩ : syracuseStep 6852113 = 5139085) B5139085
theorem B6065765 : Blo 798342 6065765 := bstep (se 4 (by rfl) ⟨568665, by rfl⟩ : syracuseStep 6065765 = 1137331) B1137331
theorem B2887319 : Blo 798342 2887319 := bstep (se 1 (by rfl) ⟨2165489, by rfl⟩ : syracuseStep 2887319 = 4330979) B4330979
theorem B1543961 : Blo 798342 1543961 := bstep (se 2 (by rfl) ⟨578985, by rfl⟩ : syracuseStep 1543961 = 1157971) B1157971
theorem B3411857 : Blo 798342 3411857 := bstep (se 2 (by rfl) ⟨1279446, by rfl⟩ : syracuseStep 3411857 = 2558893) B2558893
theorem B2166679 : Blo 798342 2166679 := bstep (se 1 (by rfl) ⟨1625009, by rfl⟩ : syracuseStep 2166679 = 3250019) B3250019
theorem B1707979 : Blo 798342 1707979 := bstep (se 1 (by rfl) ⟨1280984, by rfl⟩ : syracuseStep 1707979 = 2561969) B2561969
theorem B6066251 : Blo 798342 6066251 := bstep (se 1 (by rfl) ⟨4549688, by rfl⟩ : syracuseStep 6066251 = 9099377) B9099377
theorem B1347671 : Blo 798342 1347671 := bstep (se 1 (by rfl) ⟨1010753, by rfl⟩ : syracuseStep 1347671 = 2021507) B2021507
theorem B1347799 : Blo 798342 1347799 := bstep (se 1 (by rfl) ⟨1010849, by rfl⟩ : syracuseStep 1347799 = 2021699) B2021699
theorem B856279 : Blo 798342 856279 := bstep (se 1 (by rfl) ⟨642209, by rfl⟩ : syracuseStep 856279 = 1284419) B1284419
theorem B9113957 : Blo 798342 9113957 := bstep (se 4 (by rfl) ⟨854433, by rfl⟩ : syracuseStep 9113957 = 1708867) B1708867
theorem B3281411 : Blo 798342 3281411 := bstep (se 1 (by rfl) ⟨2461058, by rfl⟩ : syracuseStep 3281411 = 4922117) B4922117
theorem B2888243 : Blo 798342 2888243 := bstep (se 1 (by rfl) ⟨2166182, by rfl⟩ : syracuseStep 2888243 = 4332365) B4332365
theorem B2167361 : Blo 798342 2167361 := bstep (se 2 (by rfl) ⟨812760, by rfl⟩ : syracuseStep 2167361 = 1625521) B1625521
theorem B856651 : Blo 798342 856651 := bstep (se 1 (by rfl) ⟨642488, by rfl⟩ : syracuseStep 856651 = 1284977) B1284977
theorem B3248785 : Blo 798342 3248785 := bstep (se 2 (by rfl) ⟨1218294, by rfl⟩ : syracuseStep 3248785 = 2436589) B2436589
theorem B1708697 : Blo 798342 1708697 := bstep (se 2 (by rfl) ⟨640761, by rfl⟩ : syracuseStep 1708697 = 1281523) B1281523
theorem B1348427 : Blo 798342 1348427 := bstep (se 1 (by rfl) ⟨1011320, by rfl⟩ : syracuseStep 1348427 = 2022641) B2022641
theorem B1348555 : Blo 798342 1348555 := bstep (se 1 (by rfl) ⟨1011416, by rfl⟩ : syracuseStep 1348555 = 2022833) B2022833
theorem B13866059 : Blo 798342 13866059 := bstep (se 1 (by rfl) ⟨10399544, by rfl⟩ : syracuseStep 13866059 = 20799089) B20799089
theorem B1348697 : Blo 798342 1348697 := bstep (se 2 (by rfl) ⟨505761, by rfl⟩ : syracuseStep 1348697 = 1011523) B1011523
theorem B3413123 : Blo 798342 3413123 := bstep (se 1 (by rfl) ⟨2559842, by rfl⟩ : syracuseStep 3413123 = 5119685) B5119685
theorem B1709209 : Blo 798342 1709209 := bstep (se 2 (by rfl) ⟨640953, by rfl⟩ : syracuseStep 1709209 = 1281907) B1281907
theorem B1348825 : Blo 798342 1348825 := bstep (se 2 (by rfl) ⟨505809, by rfl⟩ : syracuseStep 1348825 = 1011619) B1011619
theorem B1709363 : Blo 798342 1709363 := bstep (se 1 (by rfl) ⟨1282022, by rfl⟩ : syracuseStep 1709363 = 2564045) B2564045
theorem B4560259 : Blo 798342 4560259 := bstep (se 1 (by rfl) ⟨3420194, by rfl⟩ : syracuseStep 4560259 = 6840389) B6840389
theorem B2168257 : Blo 798342 2168257 := bstep (se 2 (by rfl) ⟨813096, by rfl⟩ : syracuseStep 2168257 = 1626193) B1626193
theorem B2561483 : Blo 798342 2561483 := bstep (se 1 (by rfl) ⟨1921112, by rfl⟩ : syracuseStep 2561483 = 3842225) B3842225
theorem B3249629 : Blo 798342 3249629 := bstep (se 3 (by rfl) ⟨609305, by rfl⟩ : syracuseStep 3249629 = 1218611) B1218611
theorem B2430557 : Blo 798342 2430557 := bstep (se 3 (by rfl) ⟨455729, by rfl⟩ : syracuseStep 2430557 = 911459) B911459
theorem B25990787 : Blo 798342 25990787 := bstep (se 1 (by rfl) ⟨19493090, by rfl⟩ : syracuseStep 25990787 = 38986181) B38986181
theorem B3282653 : Blo 798342 3282653 := bstep (se 3 (by rfl) ⟨615497, by rfl⟩ : syracuseStep 3282653 = 1230995) B1230995
theorem B1349399 : Blo 798342 1349399 := bstep (se 1 (by rfl) ⟨1012049, by rfl⟩ : syracuseStep 1349399 = 2024099) B2024099
theorem B1349527 : Blo 798342 1349527 := bstep (se 1 (by rfl) ⟨1012145, by rfl⟩ : syracuseStep 1349527 = 2024291) B2024291
theorem B1284311 : Blo 798342 1284311 := bstep (se 1 (by rfl) ⟨963233, by rfl⟩ : syracuseStep 1284311 = 1926467) B1926467
theorem B1710337 : Blo 798342 1710337 := bstep (se 2 (by rfl) ⟨641376, by rfl⟩ : syracuseStep 1710337 = 1282753) B1282753
theorem B4561217 : Blo 798342 4561217 := bstep (se 2 (by rfl) ⟨1710456, by rfl⟩ : syracuseStep 4561217 = 3420913) B3420913
theorem B1350155 : Blo 798342 1350155 := bstep (se 1 (by rfl) ⟨1012616, by rfl⟩ : syracuseStep 1350155 = 2025233) B2025233
theorem B5478929 : Blo 798342 5478929 := bstep (se 2 (by rfl) ⟨2054598, by rfl⟩ : syracuseStep 5478929 = 4109197) B4109197
theorem B1710679 : Blo 798342 1710679 := bstep (se 1 (by rfl) ⟨1283009, by rfl⟩ : syracuseStep 1710679 = 2566019) B2566019
theorem B2431577 : Blo 798342 2431577 := bstep (se 2 (by rfl) ⟨911841, by rfl⟩ : syracuseStep 2431577 = 1823683) B1823683
theorem B1350283 : Blo 798342 1350283 := bstep (se 1 (by rfl) ⟨1012712, by rfl⟩ : syracuseStep 1350283 = 2025425) B2025425
theorem B1350425 : Blo 798342 1350425 := bstep (se 2 (by rfl) ⟨506409, by rfl⟩ : syracuseStep 1350425 = 1012819) B1012819
theorem B1350553 : Blo 798342 1350553 := bstep (se 2 (by rfl) ⟨506457, by rfl⟩ : syracuseStep 1350553 = 1012915) B1012915
theorem B1711115 : Blo 798342 1711115 := bstep (se 1 (by rfl) ⟨1283336, by rfl⟩ : syracuseStep 1711115 = 2566673) B2566673
theorem B2563123 : Blo 798342 2563123 := bstep (se 1 (by rfl) ⟨1922342, by rfl⟩ : syracuseStep 2563123 = 3844685) B3844685
theorem B6495493 : Blo 798342 6495493 := bstep (se 4 (by rfl) ⟨608952, by rfl⟩ : syracuseStep 6495493 = 1217905) B1217905
theorem B5479811 : Blo 798342 5479811 := bstep (se 1 (by rfl) ⟨4109858, by rfl⟩ : syracuseStep 5479811 = 8219717) B8219717
theorem B1351127 : Blo 798342 1351127 := bstep (se 1 (by rfl) ⟨1013345, by rfl⟩ : syracuseStep 1351127 = 2026691) B2026691
theorem B4169177 : Blo 798342 4169177 := bstep (se 2 (by rfl) ⟨1563441, by rfl⟩ : syracuseStep 4169177 = 3126883) B3126883
theorem B1777177 : Blo 798342 1777177 := bstep (se 2 (by rfl) ⟨666441, by rfl⟩ : syracuseStep 1777177 = 1332883) B1332883
theorem B2694707 : Blo 798342 2694707 := bstep (se 1 (by rfl) ⟨2021030, by rfl⟩ : syracuseStep 2694707 = 4042061) B4042061
theorem B1351255 : Blo 798342 1351255 := bstep (se 1 (by rfl) ⟨1013441, by rfl⟩ : syracuseStep 1351255 = 2026883) B2026883
theorem B2694977 : Blo 798342 2694977 := bstep (se 2 (by rfl) ⟨1010616, by rfl⟩ : syracuseStep 2694977 = 2021233) B2021233
theorem B1712011 : Blo 798342 1712011 := bstep (se 1 (by rfl) ⟨1284008, by rfl⟩ : syracuseStep 1712011 = 2568017) B2568017
theorem B3416215 : Blo 798342 3416215 := bstep (se 1 (by rfl) ⟨2562161, by rfl⟩ : syracuseStep 3416215 = 5124323) B5124323
theorem B1351883 : Blo 798342 1351883 := bstep (se 1 (by rfl) ⟨1013912, by rfl⟩ : syracuseStep 1351883 = 2027825) B2027825
theorem B8790221 : Blo 798342 8790221 := bstep (se 3 (by rfl) ⟨1648166, by rfl⟩ : syracuseStep 8790221 = 3296333) B3296333
theorem B1515827 : Blo 798342 1515827 := bstep (se 1 (by rfl) ⟨1136870, by rfl⟩ : syracuseStep 1515827 = 2273741) B2273741
theorem B1352011 : Blo 798342 1352011 := bstep (se 1 (by rfl) ⟨1014008, by rfl⟩ : syracuseStep 1352011 = 2028017) B2028017
theorem B2695517 : Blo 798342 2695517 := bstep (se 3 (by rfl) ⟨505409, by rfl⟩ : syracuseStep 2695517 = 1010819) B1010819
theorem B10232243 : Blo 798342 10232243 := bstep (se 1 (by rfl) ⟨7674182, by rfl⟩ : syracuseStep 10232243 = 15348365) B15348365
theorem B1352153 : Blo 798342 1352153 := bstep (se 2 (by rfl) ⟨507057, by rfl⟩ : syracuseStep 1352153 = 1014115) B1014115
theorem B1352281 : Blo 798342 1352281 := bstep (se 2 (by rfl) ⟨507105, by rfl⟩ : syracuseStep 1352281 = 1014211) B1014211
theorem B1712755 : Blo 798342 1712755 := bstep (se 1 (by rfl) ⟨1284566, by rfl⟩ : syracuseStep 1712755 = 2569133) B2569133
theorem B1516313 : Blo 798342 1516313 := bstep (se 2 (by rfl) ⟨568617, by rfl⟩ : syracuseStep 1516313 = 1137235) B1137235
theorem B1713241 : Blo 798342 1713241 := bstep (se 2 (by rfl) ⟨642465, by rfl⟩ : syracuseStep 1713241 = 1284931) B1284931
theorem B1352855 : Blo 798342 1352855 := bstep (se 1 (by rfl) ⟨1014641, by rfl⟩ : syracuseStep 1352855 = 2029283) B2029283
theorem B4629683 : Blo 798342 4629683 := bstep (se 1 (by rfl) ⟨3472262, by rfl⟩ : syracuseStep 4629683 = 6944525) B6944525
theorem B21898421 : Blo 798342 21898421 := bstep (se 5 (by rfl) ⟨1026488, by rfl⟩ : syracuseStep 21898421 = 2052977) B2052977
theorem B2565341 : Blo 798342 2565341 := bstep (se 3 (by rfl) ⟨481001, by rfl⟩ : syracuseStep 2565341 = 962003) B962003
theorem B1352983 : Blo 798342 1352983 := bstep (se 1 (by rfl) ⟨1014737, by rfl⟩ : syracuseStep 1352983 = 2029475) B2029475
theorem B6071597 : Blo 798342 6071597 := bstep (se 3 (by rfl) ⟨1138424, by rfl⟩ : syracuseStep 6071597 = 2276849) B2276849
theorem B2696651 : Blo 798342 2696651 := bstep (se 1 (by rfl) ⟨2022488, by rfl⟩ : syracuseStep 2696651 = 4044977) B4044977
theorem B2696921 : Blo 798342 2696921 := bstep (se 2 (by rfl) ⟨1011345, by rfl⟩ : syracuseStep 2696921 = 2022691) B2022691
theorem B7808813 : Blo 798342 7808813 := bstep (se 3 (by rfl) ⟨1464152, by rfl⟩ : syracuseStep 7808813 = 2928305) B2928305
theorem B9348965 : Blo 798342 9348965 := bstep (se 4 (by rfl) ⟨876465, by rfl⟩ : syracuseStep 9348965 = 1752931) B1752931
theorem B1353611 : Blo 798342 1353611 := bstep (se 1 (by rfl) ⟨1015208, by rfl⟩ : syracuseStep 1353611 = 2030417) B2030417
theorem B1353739 : Blo 798342 1353739 := bstep (se 1 (by rfl) ⟨1015304, by rfl⟩ : syracuseStep 1353739 = 2030609) B2030609
theorem B1386647 : Blo 798342 1386647 := bstep (se 1 (by rfl) ⟨1039985, by rfl⟩ : syracuseStep 1386647 = 2079971) B2079971
theorem B1353881 : Blo 798342 1353881 := bstep (se 2 (by rfl) ⟨507705, by rfl⟩ : syracuseStep 1353881 = 1015411) B1015411
theorem B1517771 : Blo 798342 1517771 := bstep (se 1 (by rfl) ⟨1138328, by rfl⟩ : syracuseStep 1517771 = 2276657) B2276657
theorem B5122349 : Blo 798342 5122349 := bstep (se 3 (by rfl) ⟨960440, by rfl⟩ : syracuseStep 5122349 = 1920881) B1920881
theorem B1517953 : Blo 798342 1517953 := bstep (se 2 (by rfl) ⟨569232, by rfl⟩ : syracuseStep 1517953 = 1138465) B1138465
theorem B2697623 : Blo 798342 2697623 := bstep (se 1 (by rfl) ⟨2023217, by rfl⟩ : syracuseStep 2697623 = 4046435) B4046435
theorem B6498737 : Blo 798342 6498737 := bstep (se 2 (by rfl) ⟨2437026, by rfl⟩ : syracuseStep 6498737 = 4874053) B4874053
theorem B6498967 : Blo 798342 6498967 := bstep (se 1 (by rfl) ⟨4874225, by rfl⟩ : syracuseStep 6498967 = 9748451) B9748451
theorem B1518401 : Blo 798342 1518401 := bstep (se 2 (by rfl) ⟨569400, by rfl⟩ : syracuseStep 1518401 = 1138801) B1138801
theorem B32877377 : Blo 798342 32877377 := bstep (se 2 (by rfl) ⟨12329016, by rfl⟩ : syracuseStep 32877377 = 24658033) B24658033
theorem B2698163 : Blo 798342 2698163 := bstep (se 1 (by rfl) ⟨2023622, by rfl⟩ : syracuseStep 2698163 = 4047245) B4047245
theorem B3419101 : Blo 798342 3419101 := bstep (se 3 (by rfl) ⟨641081, by rfl⟩ : syracuseStep 3419101 = 1282163) B1282163
theorem B9743435 : Blo 798342 9743435 := bstep (se 1 (by rfl) ⟨7307576, by rfl⟩ : syracuseStep 9743435 = 14615153) B14615153
theorem B4566091 : Blo 798342 4566091 := bstep (se 1 (by rfl) ⟨3424568, by rfl⟩ : syracuseStep 4566091 = 6849137) B6849137
theorem B1518743 : Blo 798342 1518743 := bstep (se 1 (by rfl) ⟨1139057, by rfl⟩ : syracuseStep 1518743 = 2278115) B2278115
theorem B2698433 : Blo 798342 2698433 := bstep (se 2 (by rfl) ⟨1011912, by rfl⟩ : syracuseStep 2698433 = 2023825) B2023825
theorem B2305331 : Blo 798342 2305331 := bstep (se 1 (by rfl) ⟨1728998, by rfl⟩ : syracuseStep 2305331 = 3457997) B3457997
theorem B4566365 : Blo 798342 4566365 := bstep (se 3 (by rfl) ⟨856193, by rfl⟩ : syracuseStep 4566365 = 1712387) B1712387
theorem B798347 : Blo 798342 798347 := bstep (se 1 (by rfl) ⟨598760, by rfl⟩ : syracuseStep 798347 = 1197521) B1197521
theorem B798359 : Blo 798342 798359 := bstep (se 1 (by rfl) ⟨598769, by rfl⟩ : syracuseStep 798359 = 1197539) B1197539
theorem B798379 : Blo 798342 798379 := bstep (se 1 (by rfl) ⟨598784, by rfl⟩ : syracuseStep 798379 = 1197569) B1197569
theorem B798391 : Blo 798342 798391 := bstep (se 1 (by rfl) ⟨598793, by rfl⟩ : syracuseStep 798391 = 1197587) B1197587
theorem B798411 : Blo 798342 798411 := bstep (se 1 (by rfl) ⟨598808, by rfl⟩ : syracuseStep 798411 = 1197617) B1197617
theorem B3124939 : Blo 798342 3124939 := bstep (se 1 (by rfl) ⟨2343704, by rfl⟩ : syracuseStep 3124939 = 4687409) B4687409
theorem B798423 : Blo 798342 798423 := bstep (se 1 (by rfl) ⟨598817, by rfl⟩ : syracuseStep 798423 = 1197635) B1197635
theorem B2698973 : Blo 798342 2698973 := bstep (se 3 (by rfl) ⟨506057, by rfl⟩ : syracuseStep 2698973 = 1012115) B1012115
theorem B798443 : Blo 798342 798443 := bstep (se 1 (by rfl) ⟨598832, by rfl⟩ : syracuseStep 798443 = 1197665) B1197665
theorem B798455 : Blo 798342 798455 := bstep (se 1 (by rfl) ⟨598841, by rfl⟩ : syracuseStep 798455 = 1197683) B1197683
theorem B798475 : Blo 798342 798475 := bstep (se 1 (by rfl) ⟨598856, by rfl⟩ : syracuseStep 798475 = 1197713) B1197713
theorem B3419921 : Blo 798342 3419921 := bstep (se 2 (by rfl) ⟨1282470, by rfl⟩ : syracuseStep 3419921 = 2564941) B2564941
theorem B798487 : Blo 798342 798487 := bstep (se 1 (by rfl) ⟨598865, by rfl⟩ : syracuseStep 798487 = 1197731) B1197731
theorem B798507 : Blo 798342 798507 := bstep (se 1 (by rfl) ⟨598880, by rfl⟩ : syracuseStep 798507 = 1197761) B1197761
theorem B1519411 : Blo 798342 1519411 := bstep (se 1 (by rfl) ⟨1139558, by rfl⟩ : syracuseStep 1519411 = 2279117) B2279117
theorem B798519 : Blo 798342 798519 := bstep (se 1 (by rfl) ⟨598889, by rfl⟩ : syracuseStep 798519 = 1197779) B1197779
theorem B798539 : Blo 798342 798539 := bstep (se 1 (by rfl) ⟨598904, by rfl⟩ : syracuseStep 798539 = 1197809) B1197809
theorem B798551 : Blo 798342 798551 := bstep (se 1 (by rfl) ⟨598913, by rfl⟩ : syracuseStep 798551 = 1197827) B1197827
theorem B4337509 : Blo 798342 4337509 := bstep (se 4 (by rfl) ⟨406641, by rfl⟩ : syracuseStep 4337509 = 813283) B813283
theorem B798571 : Blo 798342 798571 := bstep (se 1 (by rfl) ⟨598928, by rfl⟩ : syracuseStep 798571 = 1197857) B1197857
theorem B798583 : Blo 798342 798583 := bstep (se 1 (by rfl) ⟨598937, by rfl⟩ : syracuseStep 798583 = 1197875) B1197875
theorem B798603 : Blo 798342 798603 := bstep (se 1 (by rfl) ⟨598952, by rfl⟩ : syracuseStep 798603 = 1197905) B1197905
theorem B798615 : Blo 798342 798615 := bstep (se 1 (by rfl) ⟨598961, by rfl⟩ : syracuseStep 798615 = 1197923) B1197923
theorem B798635 : Blo 798342 798635 := bstep (se 1 (by rfl) ⟨598976, by rfl⟩ : syracuseStep 798635 = 1197953) B1197953
theorem B798647 : Blo 798342 798647 := bstep (se 1 (by rfl) ⟨598985, by rfl⟩ : syracuseStep 798647 = 1197971) B1197971
theorem B798667 : Blo 798342 798667 := bstep (se 1 (by rfl) ⟨599000, by rfl⟩ : syracuseStep 798667 = 1198001) B1198001
theorem B798679 : Blo 798342 798679 := bstep (se 1 (by rfl) ⟨599009, by rfl⟩ : syracuseStep 798679 = 1198019) B1198019
theorem B798699 : Blo 798342 798699 := bstep (se 1 (by rfl) ⟨599024, by rfl⟩ : syracuseStep 798699 = 1198049) B1198049
theorem B798711 : Blo 798342 798711 := bstep (se 1 (by rfl) ⟨599033, by rfl⟩ : syracuseStep 798711 = 1198067) B1198067
theorem B798731 : Blo 798342 798731 := bstep (se 1 (by rfl) ⟨599048, by rfl⟩ : syracuseStep 798731 = 1198097) B1198097
theorem B798743 : Blo 798342 798743 := bstep (se 1 (by rfl) ⟨599057, by rfl⟩ : syracuseStep 798743 = 1198115) B1198115
theorem B798763 : Blo 798342 798763 := bstep (se 1 (by rfl) ⟨599072, by rfl⟩ : syracuseStep 798763 = 1198145) B1198145
theorem B6926381 : Blo 798342 6926381 := bstep (se 3 (by rfl) ⟨1298696, by rfl⟩ : syracuseStep 6926381 = 2597393) B2597393
theorem B798775 : Blo 798342 798775 := bstep (se 1 (by rfl) ⟨599081, by rfl⟩ : syracuseStep 798775 = 1198163) B1198163
theorem B798795 : Blo 798342 798795 := bstep (se 1 (by rfl) ⟨599096, by rfl⟩ : syracuseStep 798795 = 1198193) B1198193
theorem B23375947 : Blo 798342 23375947 := bstep (se 1 (by rfl) ⟨17531960, by rfl⟩ : syracuseStep 23375947 = 35063921) B35063921
theorem B798807 : Blo 798342 798807 := bstep (se 1 (by rfl) ⟨599105, by rfl⟩ : syracuseStep 798807 = 1198211) B1198211
theorem B798827 : Blo 798342 798827 := bstep (se 1 (by rfl) ⟨599120, by rfl⟩ : syracuseStep 798827 = 1198241) B1198241
theorem B798839 : Blo 798342 798839 := bstep (se 1 (by rfl) ⟨599129, by rfl⟩ : syracuseStep 798839 = 1198259) B1198259
theorem B798859 : Blo 798342 798859 := bstep (se 1 (by rfl) ⟨599144, by rfl⟩ : syracuseStep 798859 = 1198289) B1198289
theorem B798871 : Blo 798342 798871 := bstep (se 1 (by rfl) ⟨599153, by rfl⟩ : syracuseStep 798871 = 1198307) B1198307
theorem B798891 : Blo 798342 798891 := bstep (se 1 (by rfl) ⟨599168, by rfl⟩ : syracuseStep 798891 = 1198337) B1198337
theorem B798903 : Blo 798342 798903 := bstep (se 1 (by rfl) ⟨599177, by rfl⟩ : syracuseStep 798903 = 1198355) B1198355
theorem B798923 : Blo 798342 798923 := bstep (se 1 (by rfl) ⟨599192, by rfl⟩ : syracuseStep 798923 = 1198385) B1198385
theorem B798935 : Blo 798342 798935 := bstep (se 1 (by rfl) ⟨599201, by rfl⟩ : syracuseStep 798935 = 1198403) B1198403
theorem B2273501 : Blo 798342 2273501 := bstep (se 3 (by rfl) ⟨426281, by rfl⟩ : syracuseStep 2273501 = 852563) B852563
theorem B798955 : Blo 798342 798955 := bstep (se 1 (by rfl) ⟨599216, by rfl⟩ : syracuseStep 798955 = 1198433) B1198433
theorem B1519859 : Blo 798342 1519859 := bstep (se 1 (by rfl) ⟨1139894, by rfl⟩ : syracuseStep 1519859 = 2279789) B2279789
theorem B798967 : Blo 798342 798967 := bstep (se 1 (by rfl) ⟨599225, by rfl⟩ : syracuseStep 798967 = 1198451) B1198451
theorem B798987 : Blo 798342 798987 := bstep (se 1 (by rfl) ⟨599240, by rfl⟩ : syracuseStep 798987 = 1198481) B1198481
theorem B798999 : Blo 798342 798999 := bstep (se 1 (by rfl) ⟨599249, by rfl⟩ : syracuseStep 798999 = 1198499) B1198499
theorem B1519897 : Blo 798342 1519897 := bstep (se 2 (by rfl) ⟨569961, by rfl⟩ : syracuseStep 1519897 = 1139923) B1139923
theorem B799019 : Blo 798342 799019 := bstep (se 1 (by rfl) ⟨599264, by rfl⟩ : syracuseStep 799019 = 1198529) B1198529
theorem B799031 : Blo 798342 799031 := bstep (se 1 (by rfl) ⟨599273, by rfl⟩ : syracuseStep 799031 = 1198547) B1198547
theorem B799051 : Blo 798342 799051 := bstep (se 1 (by rfl) ⟨599288, by rfl⟩ : syracuseStep 799051 = 1198577) B1198577
theorem B799063 : Blo 798342 799063 := bstep (se 1 (by rfl) ⟨599297, by rfl⟩ : syracuseStep 799063 = 1198595) B1198595
theorem B799083 : Blo 798342 799083 := bstep (se 1 (by rfl) ⟨599312, by rfl⟩ : syracuseStep 799083 = 1198625) B1198625
theorem B25932149 : Blo 798342 25932149 := bstep (se 5 (by rfl) ⟨1215569, by rfl⟩ : syracuseStep 25932149 = 2431139) B2431139
theorem B799095 : Blo 798342 799095 := bstep (se 1 (by rfl) ⟨599321, by rfl⟩ : syracuseStep 799095 = 1198643) B1198643
theorem B799115 : Blo 798342 799115 := bstep (se 1 (by rfl) ⟨599336, by rfl⟩ : syracuseStep 799115 = 1198673) B1198673
theorem B799127 : Blo 798342 799127 := bstep (se 1 (by rfl) ⟨599345, by rfl⟩ : syracuseStep 799127 = 1198691) B1198691
theorem B799147 : Blo 798342 799147 := bstep (se 1 (by rfl) ⟨599360, by rfl⟩ : syracuseStep 799147 = 1198721) B1198721
theorem B3420589 : Blo 798342 3420589 := bstep (se 3 (by rfl) ⟨641360, by rfl⟩ : syracuseStep 3420589 = 1282721) B1282721
theorem B799159 : Blo 798342 799159 := bstep (se 1 (by rfl) ⟨599369, by rfl⟩ : syracuseStep 799159 = 1198739) B1198739
theorem B799179 : Blo 798342 799179 := bstep (se 1 (by rfl) ⟨599384, by rfl⟩ : syracuseStep 799179 = 1198769) B1198769
theorem B799191 : Blo 798342 799191 := bstep (se 1 (by rfl) ⟨599393, by rfl⟩ : syracuseStep 799191 = 1198787) B1198787
theorem B799211 : Blo 798342 799211 := bstep (se 1 (by rfl) ⟨599408, by rfl⟩ : syracuseStep 799211 = 1198817) B1198817
theorem B799223 : Blo 798342 799223 := bstep (se 1 (by rfl) ⟨599417, by rfl⟩ : syracuseStep 799223 = 1198835) B1198835
theorem B799243 : Blo 798342 799243 := bstep (se 1 (by rfl) ⟨599432, by rfl⟩ : syracuseStep 799243 = 1198865) B1198865
theorem B799255 : Blo 798342 799255 := bstep (se 1 (by rfl) ⟨599441, by rfl⟩ : syracuseStep 799255 = 1198883) B1198883
theorem B799275 : Blo 798342 799275 := bstep (se 1 (by rfl) ⟨599456, by rfl⟩ : syracuseStep 799275 = 1198913) B1198913
theorem B799287 : Blo 798342 799287 := bstep (se 1 (by rfl) ⟨599465, by rfl⟩ : syracuseStep 799287 = 1198931) B1198931
theorem B799307 : Blo 798342 799307 := bstep (se 1 (by rfl) ⟨599480, by rfl⟩ : syracuseStep 799307 = 1198961) B1198961
theorem B799319 : Blo 798342 799319 := bstep (se 1 (by rfl) ⟨599489, by rfl⟩ : syracuseStep 799319 = 1198979) B1198979
theorem B4043357 : Blo 798342 4043357 := bstep (se 3 (by rfl) ⟨758129, by rfl⟩ : syracuseStep 4043357 = 1516259) B1516259
theorem B799339 : Blo 798342 799339 := bstep (se 1 (by rfl) ⟨599504, by rfl⟩ : syracuseStep 799339 = 1199009) B1199009
theorem B799351 : Blo 798342 799351 := bstep (se 1 (by rfl) ⟨599513, by rfl⟩ : syracuseStep 799351 = 1199027) B1199027
theorem B799371 : Blo 798342 799371 := bstep (se 1 (by rfl) ⟨599528, by rfl⟩ : syracuseStep 799371 = 1199057) B1199057
theorem B799383 : Blo 798342 799383 := bstep (se 1 (by rfl) ⟨599537, by rfl⟩ : syracuseStep 799383 = 1199075) B1199075
theorem B799403 : Blo 798342 799403 := bstep (se 1 (by rfl) ⟨599552, by rfl⟩ : syracuseStep 799403 = 1199105) B1199105
theorem B799415 : Blo 798342 799415 := bstep (se 1 (by rfl) ⟨599561, by rfl⟩ : syracuseStep 799415 = 1199123) B1199123
theorem B799435 : Blo 798342 799435 := bstep (se 1 (by rfl) ⟨599576, by rfl⟩ : syracuseStep 799435 = 1199153) B1199153
theorem B5780173 : Blo 798342 5780173 := bstep (se 3 (by rfl) ⟨1083782, by rfl⟩ : syracuseStep 5780173 = 2167565) B2167565
theorem B799447 : Blo 798342 799447 := bstep (se 1 (by rfl) ⟨599585, by rfl⟩ : syracuseStep 799447 = 1199171) B1199171
theorem B1520345 : Blo 798342 1520345 := bstep (se 2 (by rfl) ⟨570129, by rfl⟩ : syracuseStep 1520345 = 1140259) B1140259
theorem B799467 : Blo 798342 799467 := bstep (se 1 (by rfl) ⟨599600, by rfl⟩ : syracuseStep 799467 = 1199201) B1199201
theorem B799479 : Blo 798342 799479 := bstep (se 1 (by rfl) ⟨599609, by rfl⟩ : syracuseStep 799479 = 1199219) B1199219
theorem B799499 : Blo 798342 799499 := bstep (se 1 (by rfl) ⟨599624, by rfl⟩ : syracuseStep 799499 = 1199249) B1199249
theorem B799511 : Blo 798342 799511 := bstep (se 1 (by rfl) ⟨599633, by rfl⟩ : syracuseStep 799511 = 1199267) B1199267
theorem B799531 : Blo 798342 799531 := bstep (se 1 (by rfl) ⟨599648, by rfl⟩ : syracuseStep 799531 = 1199297) B1199297
theorem B799543 : Blo 798342 799543 := bstep (se 1 (by rfl) ⟨599657, by rfl⟩ : syracuseStep 799543 = 1199315) B1199315
theorem B799563 : Blo 798342 799563 := bstep (se 1 (by rfl) ⟨599672, by rfl⟩ : syracuseStep 799563 = 1199345) B1199345
theorem B2700107 : Blo 798342 2700107 := bstep (se 1 (by rfl) ⟨2025080, by rfl⟩ : syracuseStep 2700107 = 4050161) B4050161
theorem B799575 : Blo 798342 799575 := bstep (se 1 (by rfl) ⟨599681, by rfl⟩ : syracuseStep 799575 = 1199363) B1199363
theorem B799595 : Blo 798342 799595 := bstep (se 1 (by rfl) ⟨599696, by rfl⟩ : syracuseStep 799595 = 1199393) B1199393
theorem B799607 : Blo 798342 799607 := bstep (se 1 (by rfl) ⟨599705, by rfl⟩ : syracuseStep 799607 = 1199411) B1199411
theorem B799627 : Blo 798342 799627 := bstep (se 1 (by rfl) ⟨599720, by rfl⟩ : syracuseStep 799627 = 1199441) B1199441
theorem B799639 : Blo 798342 799639 := bstep (se 1 (by rfl) ⟨599729, by rfl⟩ : syracuseStep 799639 = 1199459) B1199459
theorem B799659 : Blo 798342 799659 := bstep (se 1 (by rfl) ⟨599744, by rfl⟩ : syracuseStep 799659 = 1199489) B1199489
theorem B799671 : Blo 798342 799671 := bstep (se 1 (by rfl) ⟨599753, by rfl⟩ : syracuseStep 799671 = 1199507) B1199507
theorem B799691 : Blo 798342 799691 := bstep (se 1 (by rfl) ⟨599768, by rfl⟩ : syracuseStep 799691 = 1199537) B1199537
theorem B3650507 : Blo 798342 3650507 := bstep (se 1 (by rfl) ⟨2737880, by rfl⟩ : syracuseStep 3650507 = 5475761) B5475761
theorem B799703 : Blo 798342 799703 := bstep (se 1 (by rfl) ⟨599777, by rfl⟩ : syracuseStep 799703 = 1199555) B1199555
theorem B799723 : Blo 798342 799723 := bstep (se 1 (by rfl) ⟨599792, by rfl⟩ : syracuseStep 799723 = 1199585) B1199585
theorem B799735 : Blo 798342 799735 := bstep (se 1 (by rfl) ⟨599801, by rfl⟩ : syracuseStep 799735 = 1199603) B1199603
theorem B3421187 : Blo 798342 3421187 := bstep (se 1 (by rfl) ⟨2565890, by rfl⟩ : syracuseStep 3421187 = 5131781) B5131781
theorem B865291 : Blo 798342 865291 := bstep (se 1 (by rfl) ⟨648968, by rfl⟩ : syracuseStep 865291 = 1297937) B1297937
theorem B799755 : Blo 798342 799755 := bstep (se 1 (by rfl) ⟨599816, by rfl⟩ : syracuseStep 799755 = 1199633) B1199633
theorem B799767 : Blo 798342 799767 := bstep (se 1 (by rfl) ⟨599825, by rfl⟩ : syracuseStep 799767 = 1199651) B1199651
theorem B799787 : Blo 798342 799787 := bstep (se 1 (by rfl) ⟨599840, by rfl⟩ : syracuseStep 799787 = 1199681) B1199681
theorem B799799 : Blo 798342 799799 := bstep (se 1 (by rfl) ⟨599849, by rfl⟩ : syracuseStep 799799 = 1199699) B1199699
theorem B799819 : Blo 798342 799819 := bstep (se 1 (by rfl) ⟨599864, by rfl⟩ : syracuseStep 799819 = 1199729) B1199729
theorem B799831 : Blo 798342 799831 := bstep (se 1 (by rfl) ⟨599873, by rfl⟩ : syracuseStep 799831 = 1199747) B1199747
theorem B2700377 : Blo 798342 2700377 := bstep (se 2 (by rfl) ⟨1012641, by rfl⟩ : syracuseStep 2700377 = 2025283) B2025283
theorem B6075485 : Blo 798342 6075485 := bstep (se 3 (by rfl) ⟨1139153, by rfl⟩ : syracuseStep 6075485 = 2278307) B2278307
theorem B799851 : Blo 798342 799851 := bstep (se 1 (by rfl) ⟨599888, by rfl⟩ : syracuseStep 799851 = 1199777) B1199777
theorem B799863 : Blo 798342 799863 := bstep (se 1 (by rfl) ⟨599897, by rfl⟩ : syracuseStep 799863 = 1199795) B1199795
theorem B799883 : Blo 798342 799883 := bstep (se 1 (by rfl) ⟨599912, by rfl⟩ : syracuseStep 799883 = 1199825) B1199825
theorem B799895 : Blo 798342 799895 := bstep (se 1 (by rfl) ⟨599921, by rfl⟩ : syracuseStep 799895 = 1199843) B1199843
theorem B799915 : Blo 798342 799915 := bstep (se 1 (by rfl) ⟨599936, by rfl⟩ : syracuseStep 799915 = 1199873) B1199873
theorem B898231 : Blo 798342 898231 := bstep (se 1 (by rfl) ⟨673673, by rfl⟩ : syracuseStep 898231 = 1347347) B1347347
theorem B799927 : Blo 798342 799927 := bstep (se 1 (by rfl) ⟨599945, by rfl⟩ : syracuseStep 799927 = 1199891) B1199891
theorem B799947 : Blo 798342 799947 := bstep (se 1 (by rfl) ⟨599960, by rfl⟩ : syracuseStep 799947 = 1199921) B1199921
theorem B799959 : Blo 798342 799959 := bstep (se 1 (by rfl) ⟨599969, by rfl⟩ : syracuseStep 799959 = 1199939) B1199939
theorem B799979 : Blo 798342 799979 := bstep (se 1 (by rfl) ⟨599984, by rfl⟩ : syracuseStep 799979 = 1199969) B1199969
theorem B799991 : Blo 798342 799991 := bstep (se 1 (by rfl) ⟨599993, by rfl⟩ : syracuseStep 799991 = 1199987) B1199987
theorem B800011 : Blo 798342 800011 := bstep (se 1 (by rfl) ⟨600008, by rfl⟩ : syracuseStep 800011 = 1200017) B1200017
theorem B800023 : Blo 798342 800023 := bstep (se 1 (by rfl) ⟨600017, by rfl⟩ : syracuseStep 800023 = 1200035) B1200035
theorem B800043 : Blo 798342 800043 := bstep (se 1 (by rfl) ⟨600032, by rfl⟩ : syracuseStep 800043 = 1200065) B1200065
theorem B800055 : Blo 798342 800055 := bstep (se 1 (by rfl) ⟨600041, by rfl⟩ : syracuseStep 800055 = 1200083) B1200083
theorem B800075 : Blo 798342 800075 := bstep (se 1 (by rfl) ⟨600056, by rfl⟩ : syracuseStep 800075 = 1200113) B1200113
theorem B800087 : Blo 798342 800087 := bstep (se 1 (by rfl) ⟨600065, by rfl⟩ : syracuseStep 800087 = 1200131) B1200131
theorem B898411 : Blo 798342 898411 := bstep (se 1 (by rfl) ⟨673808, by rfl⟩ : syracuseStep 898411 = 1347617) B1347617
theorem B800107 : Blo 798342 800107 := bstep (se 1 (by rfl) ⟨600080, by rfl⟩ : syracuseStep 800107 = 1200161) B1200161
theorem B800119 : Blo 798342 800119 := bstep (se 1 (by rfl) ⟨600089, by rfl⟩ : syracuseStep 800119 = 1200179) B1200179
theorem B800139 : Blo 798342 800139 := bstep (se 1 (by rfl) ⟨600104, by rfl⟩ : syracuseStep 800139 = 1200209) B1200209
theorem B800151 : Blo 798342 800151 := bstep (se 1 (by rfl) ⟨600113, by rfl⟩ : syracuseStep 800151 = 1200227) B1200227
theorem B800171 : Blo 798342 800171 := bstep (se 1 (by rfl) ⟨600128, by rfl⟩ : syracuseStep 800171 = 1200257) B1200257
theorem B800183 : Blo 798342 800183 := bstep (se 1 (by rfl) ⟨600137, by rfl⟩ : syracuseStep 800183 = 1200275) B1200275
theorem B1521089 : Blo 798342 1521089 := bstep (se 2 (by rfl) ⟨570408, by rfl⟩ : syracuseStep 1521089 = 1140817) B1140817
theorem B800203 : Blo 798342 800203 := bstep (se 1 (by rfl) ⟨600152, by rfl⟩ : syracuseStep 800203 = 1200305) B1200305
theorem B898519 : Blo 798342 898519 := bstep (se 1 (by rfl) ⟨673889, by rfl⟩ : syracuseStep 898519 = 1347779) B1347779
theorem B800215 : Blo 798342 800215 := bstep (se 1 (by rfl) ⟨600161, by rfl⟩ : syracuseStep 800215 = 1200323) B1200323
theorem B800235 : Blo 798342 800235 := bstep (se 1 (by rfl) ⟨600176, by rfl⟩ : syracuseStep 800235 = 1200353) B1200353
theorem B800247 : Blo 798342 800247 := bstep (se 1 (by rfl) ⟨600185, by rfl⟩ : syracuseStep 800247 = 1200371) B1200371
theorem B800267 : Blo 798342 800267 := bstep (se 1 (by rfl) ⟨600200, by rfl⟩ : syracuseStep 800267 = 1200401) B1200401
theorem B800279 : Blo 798342 800279 := bstep (se 1 (by rfl) ⟨600209, by rfl⟩ : syracuseStep 800279 = 1200419) B1200419
theorem B800299 : Blo 798342 800299 := bstep (se 1 (by rfl) ⟨600224, by rfl⟩ : syracuseStep 800299 = 1200449) B1200449
theorem B2438707 : Blo 798342 2438707 := bstep (se 1 (by rfl) ⟨1829030, by rfl⟩ : syracuseStep 2438707 = 3658061) B3658061
theorem B800311 : Blo 798342 800311 := bstep (se 1 (by rfl) ⟨600233, by rfl⟩ : syracuseStep 800311 = 1200467) B1200467
theorem B800331 : Blo 798342 800331 := bstep (se 1 (by rfl) ⟨600248, by rfl⟩ : syracuseStep 800331 = 1200497) B1200497
theorem B800343 : Blo 798342 800343 := bstep (se 1 (by rfl) ⟨600257, by rfl⟩ : syracuseStep 800343 = 1200515) B1200515
theorem B800363 : Blo 798342 800363 := bstep (se 1 (by rfl) ⟨600272, by rfl⟩ : syracuseStep 800363 = 1200545) B1200545
theorem B800375 : Blo 798342 800375 := bstep (se 1 (by rfl) ⟨600281, by rfl⟩ : syracuseStep 800375 = 1200563) B1200563
theorem B898699 : Blo 798342 898699 := bstep (se 1 (by rfl) ⟨674024, by rfl⟩ : syracuseStep 898699 = 1348049) B1348049
theorem B800395 : Blo 798342 800395 := bstep (se 1 (by rfl) ⟨600296, by rfl⟩ : syracuseStep 800395 = 1200593) B1200593
theorem B800407 : Blo 798342 800407 := bstep (se 1 (by rfl) ⟨600305, by rfl⟩ : syracuseStep 800407 = 1200611) B1200611
theorem B800427 : Blo 798342 800427 := bstep (se 1 (by rfl) ⟨600320, by rfl⟩ : syracuseStep 800427 = 1200641) B1200641
theorem B800439 : Blo 798342 800439 := bstep (se 1 (by rfl) ⟨600329, by rfl⟩ : syracuseStep 800439 = 1200659) B1200659
theorem B800459 : Blo 798342 800459 := bstep (se 1 (by rfl) ⟨600344, by rfl⟩ : syracuseStep 800459 = 1200689) B1200689
theorem B1521355 : Blo 798342 1521355 := bstep (se 1 (by rfl) ⟨1141016, by rfl⟩ : syracuseStep 1521355 = 2282033) B2282033
theorem B800471 : Blo 798342 800471 := bstep (se 1 (by rfl) ⟨600353, by rfl⟩ : syracuseStep 800471 = 1200707) B1200707
theorem B800491 : Blo 798342 800491 := bstep (se 1 (by rfl) ⟨600368, by rfl⟩ : syracuseStep 800491 = 1200737) B1200737
theorem B898807 : Blo 798342 898807 := bstep (se 1 (by rfl) ⟨674105, by rfl⟩ : syracuseStep 898807 = 1348211) B1348211
theorem B800503 : Blo 798342 800503 := bstep (se 1 (by rfl) ⟨600377, by rfl⟩ : syracuseStep 800503 = 1200755) B1200755
theorem B800523 : Blo 798342 800523 := bstep (se 1 (by rfl) ⟨600392, by rfl⟩ : syracuseStep 800523 = 1200785) B1200785
theorem B2701079 : Blo 798342 2701079 := bstep (se 1 (by rfl) ⟨2025809, by rfl⟩ : syracuseStep 2701079 = 4051619) B4051619
theorem B800535 : Blo 798342 800535 := bstep (se 1 (by rfl) ⟨600401, by rfl⟩ : syracuseStep 800535 = 1200803) B1200803
theorem B800555 : Blo 798342 800555 := bstep (se 1 (by rfl) ⟨600416, by rfl⟩ : syracuseStep 800555 = 1200833) B1200833
theorem B800567 : Blo 798342 800567 := bstep (se 1 (by rfl) ⟨600425, by rfl⟩ : syracuseStep 800567 = 1200851) B1200851
theorem B5125963 : Blo 798342 5125963 := bstep (se 1 (by rfl) ⟨3844472, by rfl⟩ : syracuseStep 5125963 = 7688945) B7688945
theorem B800587 : Blo 798342 800587 := bstep (se 1 (by rfl) ⟨600440, by rfl⟩ : syracuseStep 800587 = 1200881) B1200881
theorem B800599 : Blo 798342 800599 := bstep (se 1 (by rfl) ⟨600449, by rfl⟩ : syracuseStep 800599 = 1200899) B1200899
theorem B800619 : Blo 798342 800619 := bstep (se 1 (by rfl) ⟨600464, by rfl⟩ : syracuseStep 800619 = 1200929) B1200929
theorem B800631 : Blo 798342 800631 := bstep (se 1 (by rfl) ⟨600473, by rfl⟩ : syracuseStep 800631 = 1200947) B1200947
theorem B800651 : Blo 798342 800651 := bstep (se 1 (by rfl) ⟨600488, by rfl⟩ : syracuseStep 800651 = 1200977) B1200977
theorem B800663 : Blo 798342 800663 := bstep (se 1 (by rfl) ⟨600497, by rfl⟩ : syracuseStep 800663 = 1200995) B1200995
theorem B898987 : Blo 798342 898987 := bstep (se 1 (by rfl) ⟨674240, by rfl⟩ : syracuseStep 898987 = 1348481) B1348481
theorem B800683 : Blo 798342 800683 := bstep (se 1 (by rfl) ⟨600512, by rfl⟩ : syracuseStep 800683 = 1201025) B1201025
theorem B800695 : Blo 798342 800695 := bstep (se 1 (by rfl) ⟨600521, by rfl⟩ : syracuseStep 800695 = 1201043) B1201043
theorem B800715 : Blo 798342 800715 := bstep (se 1 (by rfl) ⟨600536, by rfl⟩ : syracuseStep 800715 = 1201073) B1201073
theorem B800727 : Blo 798342 800727 := bstep (se 1 (by rfl) ⟨600545, by rfl⟩ : syracuseStep 800727 = 1201091) B1201091
theorem B21936089 : Blo 798342 21936089 := bstep (se 2 (by rfl) ⟨8226033, by rfl⟩ : syracuseStep 21936089 = 16452067) B16452067
theorem B800747 : Blo 798342 800747 := bstep (se 1 (by rfl) ⟨600560, by rfl⟩ : syracuseStep 800747 = 1201121) B1201121
theorem B800759 : Blo 798342 800759 := bstep (se 1 (by rfl) ⟨600569, by rfl⟩ : syracuseStep 800759 = 1201139) B1201139
theorem B800779 : Blo 798342 800779 := bstep (se 1 (by rfl) ⟨600584, by rfl⟩ : syracuseStep 800779 = 1201169) B1201169
theorem B899095 : Blo 798342 899095 := bstep (se 1 (by rfl) ⟨674321, by rfl⟩ : syracuseStep 899095 = 1348643) B1348643
theorem B800791 : Blo 798342 800791 := bstep (se 1 (by rfl) ⟨600593, by rfl⟩ : syracuseStep 800791 = 1201187) B1201187
theorem B800811 : Blo 798342 800811 := bstep (se 1 (by rfl) ⟨600608, by rfl⟩ : syracuseStep 800811 = 1201217) B1201217
theorem B800823 : Blo 798342 800823 := bstep (se 1 (by rfl) ⟨600617, by rfl⟩ : syracuseStep 800823 = 1201235) B1201235
theorem B800843 : Blo 798342 800843 := bstep (se 1 (by rfl) ⟨600632, by rfl⟩ : syracuseStep 800843 = 1201265) B1201265
theorem B800855 : Blo 798342 800855 := bstep (se 1 (by rfl) ⟨600641, by rfl⟩ : syracuseStep 800855 = 1201283) B1201283
theorem B800875 : Blo 798342 800875 := bstep (se 1 (by rfl) ⟨600656, by rfl⟩ : syracuseStep 800875 = 1201313) B1201313
theorem B800887 : Blo 798342 800887 := bstep (se 1 (by rfl) ⟨600665, by rfl⟩ : syracuseStep 800887 = 1201331) B1201331
theorem B800907 : Blo 798342 800907 := bstep (se 1 (by rfl) ⟨600680, by rfl⟩ : syracuseStep 800907 = 1201361) B1201361
theorem B1521803 : Blo 798342 1521803 := bstep (se 1 (by rfl) ⟨1141352, by rfl⟩ : syracuseStep 1521803 = 2282705) B2282705
theorem B800919 : Blo 798342 800919 := bstep (se 1 (by rfl) ⟨600689, by rfl⟩ : syracuseStep 800919 = 1201379) B1201379
theorem B800939 : Blo 798342 800939 := bstep (se 1 (by rfl) ⟨600704, by rfl⟩ : syracuseStep 800939 = 1201409) B1201409
theorem B800951 : Blo 798342 800951 := bstep (se 1 (by rfl) ⟨600713, by rfl⟩ : syracuseStep 800951 = 1201427) B1201427
theorem B899275 : Blo 798342 899275 := bstep (se 1 (by rfl) ⟨674456, by rfl⟩ : syracuseStep 899275 = 1348913) B1348913
theorem B866507 : Blo 798342 866507 := bstep (se 1 (by rfl) ⟨649880, by rfl⟩ : syracuseStep 866507 = 1299761) B1299761
theorem B800971 : Blo 798342 800971 := bstep (se 1 (by rfl) ⟨600728, by rfl⟩ : syracuseStep 800971 = 1201457) B1201457
theorem B800983 : Blo 798342 800983 := bstep (se 1 (by rfl) ⟨600737, by rfl⟩ : syracuseStep 800983 = 1201475) B1201475
theorem B801003 : Blo 798342 801003 := bstep (se 1 (by rfl) ⟨600752, by rfl⟩ : syracuseStep 801003 = 1201505) B1201505
theorem B801015 : Blo 798342 801015 := bstep (se 1 (by rfl) ⟨600761, by rfl⟩ : syracuseStep 801015 = 1201523) B1201523
theorem B801035 : Blo 798342 801035 := bstep (se 1 (by rfl) ⟨600776, by rfl⟩ : syracuseStep 801035 = 1201553) B1201553
theorem B801047 : Blo 798342 801047 := bstep (se 1 (by rfl) ⟨600785, by rfl⟩ : syracuseStep 801047 = 1201571) B1201571
theorem B801067 : Blo 798342 801067 := bstep (se 1 (by rfl) ⟨600800, by rfl⟩ : syracuseStep 801067 = 1201601) B1201601
theorem B2701619 : Blo 798342 2701619 := bstep (se 1 (by rfl) ⟨2026214, by rfl⟩ : syracuseStep 2701619 = 4052429) B4052429
theorem B899383 : Blo 798342 899383 := bstep (se 1 (by rfl) ⟨674537, by rfl⟩ : syracuseStep 899383 = 1349075) B1349075
theorem B801079 : Blo 798342 801079 := bstep (se 1 (by rfl) ⟨600809, by rfl⟩ : syracuseStep 801079 = 1201619) B1201619
theorem B1521985 : Blo 798342 1521985 := bstep (se 2 (by rfl) ⟨570744, by rfl⟩ : syracuseStep 1521985 = 1141489) B1141489
theorem B801099 : Blo 798342 801099 := bstep (se 1 (by rfl) ⟨600824, by rfl⟩ : syracuseStep 801099 = 1201649) B1201649
theorem B801111 : Blo 798342 801111 := bstep (se 1 (by rfl) ⟨600833, by rfl⟩ : syracuseStep 801111 = 1201667) B1201667
theorem B3651929 : Blo 798342 3651929 := bstep (se 2 (by rfl) ⟨1369473, by rfl⟩ : syracuseStep 3651929 = 2738947) B2738947
theorem B801131 : Blo 798342 801131 := bstep (se 1 (by rfl) ⟨600848, by rfl⟩ : syracuseStep 801131 = 1201697) B1201697
theorem B801143 : Blo 798342 801143 := bstep (se 1 (by rfl) ⟨600857, by rfl⟩ : syracuseStep 801143 = 1201715) B1201715
theorem B801163 : Blo 798342 801163 := bstep (se 1 (by rfl) ⟨600872, by rfl⟩ : syracuseStep 801163 = 1201745) B1201745
theorem B801175 : Blo 798342 801175 := bstep (se 1 (by rfl) ⟨600881, by rfl⟩ : syracuseStep 801175 = 1201763) B1201763
theorem B801195 : Blo 798342 801195 := bstep (se 1 (by rfl) ⟨600896, by rfl⟩ : syracuseStep 801195 = 1201793) B1201793
theorem B801207 : Blo 798342 801207 := bstep (se 1 (by rfl) ⟨600905, by rfl⟩ : syracuseStep 801207 = 1201811) B1201811
theorem B801227 : Blo 798342 801227 := bstep (se 1 (by rfl) ⟨600920, by rfl⟩ : syracuseStep 801227 = 1201841) B1201841
theorem B801239 : Blo 798342 801239 := bstep (se 1 (by rfl) ⟨600929, by rfl⟩ : syracuseStep 801239 = 1201859) B1201859
theorem B7682521 : Blo 798342 7682521 := bstep (se 2 (by rfl) ⟨2880945, by rfl⟩ : syracuseStep 7682521 = 5761891) B5761891
theorem B899563 : Blo 798342 899563 := bstep (se 1 (by rfl) ⟨674672, by rfl⟩ : syracuseStep 899563 = 1349345) B1349345
theorem B801259 : Blo 798342 801259 := bstep (se 1 (by rfl) ⟨600944, by rfl⟩ : syracuseStep 801259 = 1201889) B1201889
theorem B801271 : Blo 798342 801271 := bstep (se 1 (by rfl) ⟨600953, by rfl⟩ : syracuseStep 801271 = 1201907) B1201907
theorem B801291 : Blo 798342 801291 := bstep (se 1 (by rfl) ⟨600968, by rfl⟩ : syracuseStep 801291 = 1201937) B1201937
theorem B801303 : Blo 798342 801303 := bstep (se 1 (by rfl) ⟨600977, by rfl⟩ : syracuseStep 801303 = 1201955) B1201955
theorem B801323 : Blo 798342 801323 := bstep (se 1 (by rfl) ⟨600992, by rfl⟩ : syracuseStep 801323 = 1201985) B1201985
theorem B801335 : Blo 798342 801335 := bstep (se 1 (by rfl) ⟨601001, by rfl⟩ : syracuseStep 801335 = 1202003) B1202003
theorem B2701889 : Blo 798342 2701889 := bstep (se 2 (by rfl) ⟨1013208, by rfl⟩ : syracuseStep 2701889 = 2026417) B2026417
theorem B801355 : Blo 798342 801355 := bstep (se 1 (by rfl) ⟨601016, by rfl⟩ : syracuseStep 801355 = 1202033) B1202033
theorem B899671 : Blo 798342 899671 := bstep (se 1 (by rfl) ⟨674753, by rfl⟩ : syracuseStep 899671 = 1349507) B1349507
theorem B801367 : Blo 798342 801367 := bstep (se 1 (by rfl) ⟨601025, by rfl⟩ : syracuseStep 801367 = 1202051) B1202051
theorem B801387 : Blo 798342 801387 := bstep (se 1 (by rfl) ⟨601040, by rfl⟩ : syracuseStep 801387 = 1202081) B1202081
theorem B801399 : Blo 798342 801399 := bstep (se 1 (by rfl) ⟨601049, by rfl⟩ : syracuseStep 801399 = 1202099) B1202099
theorem B801419 : Blo 798342 801419 := bstep (se 1 (by rfl) ⟨601064, by rfl⟩ : syracuseStep 801419 = 1202129) B1202129
theorem B4045463 : Blo 798342 4045463 := bstep (se 1 (by rfl) ⟨3034097, by rfl⟩ : syracuseStep 4045463 = 6068195) B6068195
theorem B5126807 : Blo 798342 5126807 := bstep (se 1 (by rfl) ⟨3845105, by rfl⟩ : syracuseStep 5126807 = 7690211) B7690211
theorem B801431 : Blo 798342 801431 := bstep (se 1 (by rfl) ⟨601073, by rfl⟩ : syracuseStep 801431 = 1202147) B1202147
theorem B1522327 : Blo 798342 1522327 := bstep (se 1 (by rfl) ⟨1141745, by rfl⟩ : syracuseStep 1522327 = 2283491) B2283491
theorem B801451 : Blo 798342 801451 := bstep (se 1 (by rfl) ⟨601088, by rfl⟩ : syracuseStep 801451 = 1202177) B1202177
theorem B801463 : Blo 798342 801463 := bstep (se 1 (by rfl) ⟨601097, by rfl⟩ : syracuseStep 801463 = 1202195) B1202195
theorem B801483 : Blo 798342 801483 := bstep (se 1 (by rfl) ⟨601112, by rfl⟩ : syracuseStep 801483 = 1202225) B1202225
theorem B801495 : Blo 798342 801495 := bstep (se 1 (by rfl) ⟨601121, by rfl⟩ : syracuseStep 801495 = 1202243) B1202243
theorem B801515 : Blo 798342 801515 := bstep (se 1 (by rfl) ⟨601136, by rfl⟩ : syracuseStep 801515 = 1202273) B1202273
theorem B801527 : Blo 798342 801527 := bstep (se 1 (by rfl) ⟨601145, by rfl⟩ : syracuseStep 801527 = 1202291) B1202291
theorem B899851 : Blo 798342 899851 := bstep (se 1 (by rfl) ⟨674888, by rfl⟩ : syracuseStep 899851 = 1349777) B1349777
theorem B801547 : Blo 798342 801547 := bstep (se 1 (by rfl) ⟨601160, by rfl⟩ : syracuseStep 801547 = 1202321) B1202321
theorem B801559 : Blo 798342 801559 := bstep (se 1 (by rfl) ⟨601169, by rfl⟩ : syracuseStep 801559 = 1202339) B1202339
theorem B801579 : Blo 798342 801579 := bstep (se 1 (by rfl) ⟨601184, by rfl⟩ : syracuseStep 801579 = 1202369) B1202369
theorem B801591 : Blo 798342 801591 := bstep (se 1 (by rfl) ⟨601193, by rfl⟩ : syracuseStep 801591 = 1202387) B1202387
theorem B801611 : Blo 798342 801611 := bstep (se 1 (by rfl) ⟨601208, by rfl⟩ : syracuseStep 801611 = 1202417) B1202417
theorem B801623 : Blo 798342 801623 := bstep (se 1 (by rfl) ⟨601217, by rfl⟩ : syracuseStep 801623 = 1202435) B1202435
theorem B801643 : Blo 798342 801643 := bstep (se 1 (by rfl) ⟨601232, by rfl⟩ : syracuseStep 801643 = 1202465) B1202465
theorem B1522547 : Blo 798342 1522547 := bstep (se 1 (by rfl) ⟨1141910, by rfl⟩ : syracuseStep 1522547 = 2283821) B2283821
theorem B899959 : Blo 798342 899959 := bstep (se 1 (by rfl) ⟨674969, by rfl⟩ : syracuseStep 899959 = 1349939) B1349939
theorem B801655 : Blo 798342 801655 := bstep (se 1 (by rfl) ⟨601241, by rfl⟩ : syracuseStep 801655 = 1202483) B1202483
theorem B6175619 : Blo 798342 6175619 := bstep (se 1 (by rfl) ⟨4631714, by rfl⟩ : syracuseStep 6175619 = 9263429) B9263429
theorem B801675 : Blo 798342 801675 := bstep (se 1 (by rfl) ⟨601256, by rfl⟩ : syracuseStep 801675 = 1202513) B1202513
theorem B801687 : Blo 798342 801687 := bstep (se 1 (by rfl) ⟨601265, by rfl⟩ : syracuseStep 801687 = 1202531) B1202531
theorem B801707 : Blo 798342 801707 := bstep (se 1 (by rfl) ⟨601280, by rfl⟩ : syracuseStep 801707 = 1202561) B1202561
theorem B801719 : Blo 798342 801719 := bstep (se 1 (by rfl) ⟨601289, by rfl⟩ : syracuseStep 801719 = 1202579) B1202579
theorem B801739 : Blo 798342 801739 := bstep (se 1 (by rfl) ⟨601304, by rfl⟩ : syracuseStep 801739 = 1202609) B1202609
theorem B801751 : Blo 798342 801751 := bstep (se 1 (by rfl) ⟨601313, by rfl⟩ : syracuseStep 801751 = 1202627) B1202627
theorem B801771 : Blo 798342 801771 := bstep (se 1 (by rfl) ⟨601328, by rfl⟩ : syracuseStep 801771 = 1202657) B1202657
theorem B801783 : Blo 798342 801783 := bstep (se 1 (by rfl) ⟨601337, by rfl⟩ : syracuseStep 801783 = 1202675) B1202675
theorem B1621003 : Blo 798342 1621003 := bstep (se 1 (by rfl) ⟨1215752, by rfl⟩ : syracuseStep 1621003 = 2431505) B2431505
theorem B801803 : Blo 798342 801803 := bstep (se 1 (by rfl) ⟨601352, by rfl⟩ : syracuseStep 801803 = 1202705) B1202705
theorem B801815 : Blo 798342 801815 := bstep (se 1 (by rfl) ⟨601361, by rfl⟩ : syracuseStep 801815 = 1202723) B1202723
theorem B900139 : Blo 798342 900139 := bstep (se 1 (by rfl) ⟨675104, by rfl⟩ : syracuseStep 900139 = 1350209) B1350209
theorem B801835 : Blo 798342 801835 := bstep (se 1 (by rfl) ⟨601376, by rfl⟩ : syracuseStep 801835 = 1202753) B1202753
theorem B801847 : Blo 798342 801847 := bstep (se 1 (by rfl) ⟨601385, by rfl⟩ : syracuseStep 801847 = 1202771) B1202771
theorem B2276417 : Blo 798342 2276417 := bstep (se 2 (by rfl) ⟨853656, by rfl⟩ : syracuseStep 2276417 = 1707313) B1707313
theorem B801867 : Blo 798342 801867 := bstep (se 1 (by rfl) ⟨601400, by rfl⟩ : syracuseStep 801867 = 1202801) B1202801
theorem B801879 : Blo 798342 801879 := bstep (se 1 (by rfl) ⟨601409, by rfl⟩ : syracuseStep 801879 = 1202819) B1202819
theorem B1522775 : Blo 798342 1522775 := bstep (se 1 (by rfl) ⟨1142081, by rfl⟩ : syracuseStep 1522775 = 2284163) B2284163
theorem B2702429 : Blo 798342 2702429 := bstep (se 3 (by rfl) ⟨506705, by rfl⟩ : syracuseStep 2702429 = 1013411) B1013411
theorem B801899 : Blo 798342 801899 := bstep (se 1 (by rfl) ⟨601424, by rfl⟩ : syracuseStep 801899 = 1202849) B1202849
theorem B801911 : Blo 798342 801911 := bstep (se 1 (by rfl) ⟨601433, by rfl⟩ : syracuseStep 801911 = 1202867) B1202867
theorem B801931 : Blo 798342 801931 := bstep (se 1 (by rfl) ⟨601448, by rfl⟩ : syracuseStep 801931 = 1202897) B1202897
theorem B900247 : Blo 798342 900247 := bstep (se 1 (by rfl) ⟨675185, by rfl⟩ : syracuseStep 900247 = 1350371) B1350371
theorem B801943 : Blo 798342 801943 := bstep (se 1 (by rfl) ⟨601457, by rfl⟩ : syracuseStep 801943 = 1202915) B1202915
theorem B801963 : Blo 798342 801963 := bstep (se 1 (by rfl) ⟨601472, by rfl⟩ : syracuseStep 801963 = 1202945) B1202945
theorem B2276531 : Blo 798342 2276531 := bstep (se 1 (by rfl) ⟨1707398, by rfl⟩ : syracuseStep 2276531 = 3414797) B3414797
theorem B801975 : Blo 798342 801975 := bstep (se 1 (by rfl) ⟨601481, by rfl⟩ : syracuseStep 801975 = 1202963) B1202963
theorem B801995 : Blo 798342 801995 := bstep (se 1 (by rfl) ⟨601496, by rfl⟩ : syracuseStep 801995 = 1202993) B1202993
theorem B802007 : Blo 798342 802007 := bstep (se 1 (by rfl) ⟨601505, by rfl⟩ : syracuseStep 802007 = 1203011) B1203011
theorem B802027 : Blo 798342 802027 := bstep (se 1 (by rfl) ⟨601520, by rfl⟩ : syracuseStep 802027 = 1203041) B1203041
theorem B802039 : Blo 798342 802039 := bstep (se 1 (by rfl) ⟨601529, by rfl⟩ : syracuseStep 802039 = 1203059) B1203059
theorem B802059 : Blo 798342 802059 := bstep (se 1 (by rfl) ⟨601544, by rfl⟩ : syracuseStep 802059 = 1203089) B1203089
theorem B802071 : Blo 798342 802071 := bstep (se 1 (by rfl) ⟨601553, by rfl⟩ : syracuseStep 802071 = 1203107) B1203107
theorem B802091 : Blo 798342 802091 := bstep (se 1 (by rfl) ⟨601568, by rfl⟩ : syracuseStep 802091 = 1203137) B1203137
theorem B802103 : Blo 798342 802103 := bstep (se 1 (by rfl) ⟨601577, by rfl⟩ : syracuseStep 802103 = 1203155) B1203155
theorem B900427 : Blo 798342 900427 := bstep (se 1 (by rfl) ⟨675320, by rfl⟩ : syracuseStep 900427 = 1350641) B1350641
theorem B802123 : Blo 798342 802123 := bstep (se 1 (by rfl) ⟨601592, by rfl⟩ : syracuseStep 802123 = 1203185) B1203185
theorem B802135 : Blo 798342 802135 := bstep (se 1 (by rfl) ⟨601601, by rfl⟩ : syracuseStep 802135 = 1203203) B1203203
theorem B1523033 : Blo 798342 1523033 := bstep (se 2 (by rfl) ⟨571137, by rfl⟩ : syracuseStep 1523033 = 1142275) B1142275
theorem B3849565 : Blo 798342 3849565 := bstep (se 3 (by rfl) ⟨721793, by rfl⟩ : syracuseStep 3849565 = 1443587) B1443587
theorem B802155 : Blo 798342 802155 := bstep (se 1 (by rfl) ⟨601616, by rfl⟩ : syracuseStep 802155 = 1203233) B1203233
theorem B802167 : Blo 798342 802167 := bstep (se 1 (by rfl) ⟨601625, by rfl⟩ : syracuseStep 802167 = 1203251) B1203251
theorem B802187 : Blo 798342 802187 := bstep (se 1 (by rfl) ⟨601640, by rfl⟩ : syracuseStep 802187 = 1203281) B1203281
theorem B3751319 : Blo 798342 3751319 := bstep (se 1 (by rfl) ⟨2813489, by rfl⟩ : syracuseStep 3751319 = 5626979) B5626979
theorem B802199 : Blo 798342 802199 := bstep (se 1 (by rfl) ⟨601649, by rfl⟩ : syracuseStep 802199 = 1203299) B1203299
theorem B802219 : Blo 798342 802219 := bstep (se 1 (by rfl) ⟨601664, by rfl⟩ : syracuseStep 802219 = 1203329) B1203329
theorem B900535 : Blo 798342 900535 := bstep (se 1 (by rfl) ⟨675401, by rfl⟩ : syracuseStep 900535 = 1350803) B1350803
theorem B802231 : Blo 798342 802231 := bstep (se 1 (by rfl) ⟨601673, by rfl⟩ : syracuseStep 802231 = 1203347) B1203347
theorem B802251 : Blo 798342 802251 := bstep (se 1 (by rfl) ⟨601688, by rfl⟩ : syracuseStep 802251 = 1203377) B1203377
theorem B802263 : Blo 798342 802263 := bstep (se 1 (by rfl) ⟨601697, by rfl⟩ : syracuseStep 802263 = 1203395) B1203395
theorem B802283 : Blo 798342 802283 := bstep (se 1 (by rfl) ⟨601712, by rfl⟩ : syracuseStep 802283 = 1203425) B1203425
theorem B802295 : Blo 798342 802295 := bstep (se 1 (by rfl) ⟨601721, by rfl⟩ : syracuseStep 802295 = 1203443) B1203443
theorem B802315 : Blo 798342 802315 := bstep (se 1 (by rfl) ⟨601736, by rfl⟩ : syracuseStep 802315 = 1203473) B1203473
theorem B802327 : Blo 798342 802327 := bstep (se 1 (by rfl) ⟨601745, by rfl⟩ : syracuseStep 802327 = 1203491) B1203491
theorem B900715 : Blo 798342 900715 := bstep (se 1 (by rfl) ⟨675536, by rfl⟩ : syracuseStep 900715 = 1351073) B1351073
theorem B900823 : Blo 798342 900823 := bstep (se 1 (by rfl) ⟨675617, by rfl⟩ : syracuseStep 900823 = 1351235) B1351235
theorem B901003 : Blo 798342 901003 := bstep (se 1 (by rfl) ⟨675752, by rfl⟩ : syracuseStep 901003 = 1351505) B1351505
theorem B901111 : Blo 798342 901111 := bstep (se 1 (by rfl) ⟨675833, by rfl⟩ : syracuseStep 901111 = 1351667) B1351667
theorem B901291 : Blo 798342 901291 := bstep (se 1 (by rfl) ⟨675968, by rfl⟩ : syracuseStep 901291 = 1351937) B1351937
theorem B2703563 : Blo 798342 2703563 := bstep (se 1 (by rfl) ⟨2027672, by rfl⟩ : syracuseStep 2703563 = 4055345) B4055345
theorem B901399 : Blo 798342 901399 := bstep (se 1 (by rfl) ⟨676049, by rfl⟩ : syracuseStep 901399 = 1352099) B1352099
theorem B901579 : Blo 798342 901579 := bstep (se 1 (by rfl) ⟨676184, by rfl⟩ : syracuseStep 901579 = 1352369) B1352369
theorem B2310617 : Blo 798342 2310617 := bstep (se 2 (by rfl) ⟨866481, by rfl⟩ : syracuseStep 2310617 = 1732963) B1732963
theorem B2703833 : Blo 798342 2703833 := bstep (se 2 (by rfl) ⟨1013937, by rfl⟩ : syracuseStep 2703833 = 2027875) B2027875
theorem B901687 : Blo 798342 901687 := bstep (se 1 (by rfl) ⟨676265, by rfl⟩ : syracuseStep 901687 = 1352531) B1352531
theorem B901867 : Blo 798342 901867 := bstep (se 1 (by rfl) ⟨676400, by rfl⟩ : syracuseStep 901867 = 1352801) B1352801
theorem B901975 : Blo 798342 901975 := bstep (se 1 (by rfl) ⟨676481, by rfl⟩ : syracuseStep 901975 = 1352963) B1352963
theorem B902155 : Blo 798342 902155 := bstep (se 1 (by rfl) ⟨676616, by rfl⟩ : syracuseStep 902155 = 1353233) B1353233
theorem B5850157 : Blo 798342 5850157 := bstep (se 3 (by rfl) ⟨1096904, by rfl⟩ : syracuseStep 5850157 = 2193809) B2193809
theorem B902263 : Blo 798342 902263 := bstep (se 1 (by rfl) ⟨676697, by rfl⟩ : syracuseStep 902263 = 1353395) B1353395
theorem B2704535 : Blo 798342 2704535 := bstep (se 1 (by rfl) ⟨2028401, by rfl⟩ : syracuseStep 2704535 = 4056803) B4056803
theorem B902443 : Blo 798342 902443 := bstep (se 1 (by rfl) ⟨676832, by rfl⟩ : syracuseStep 902443 = 1353665) B1353665
theorem B902551 : Blo 798342 902551 := bstep (se 1 (by rfl) ⟨676913, by rfl⟩ : syracuseStep 902551 = 1353827) B1353827
theorem B3458483 : Blo 798342 3458483 := bstep (se 1 (by rfl) ⟨2593862, by rfl⟩ : syracuseStep 3458483 = 5187725) B5187725
theorem B1197515 : Blo 798342 1197515 := bstep (se 1 (by rfl) ⟨898136, by rfl⟩ : syracuseStep 1197515 = 1796273) B1796273
theorem B1197527 : Blo 798342 1197527 := bstep (se 1 (by rfl) ⟨898145, by rfl⟩ : syracuseStep 1197527 = 1796291) B1796291
theorem B3032579 : Blo 798342 3032579 := bstep (se 1 (by rfl) ⟨2274434, by rfl⟩ : syracuseStep 3032579 = 4548869) B4548869
theorem B1197593 : Blo 798342 1197593 := bstep (se 2 (by rfl) ⟨449097, by rfl⟩ : syracuseStep 1197593 = 898195) B898195
theorem B1459777 : Blo 798342 1459777 := bstep (se 2 (by rfl) ⟨547416, by rfl⟩ : syracuseStep 1459777 = 1094833) B1094833
theorem B1197707 : Blo 798342 1197707 := bstep (se 1 (by rfl) ⟨898280, by rfl⟩ : syracuseStep 1197707 = 1796561) B1796561
theorem B1197719 : Blo 798342 1197719 := bstep (se 1 (by rfl) ⟨898289, by rfl⟩ : syracuseStep 1197719 = 1796579) B1796579
theorem B2705075 : Blo 798342 2705075 := bstep (se 1 (by rfl) ⟨2028806, by rfl⟩ : syracuseStep 2705075 = 4057613) B4057613
theorem B1197785 : Blo 798342 1197785 := bstep (se 2 (by rfl) ⟨449169, by rfl⟩ : syracuseStep 1197785 = 898339) B898339
theorem B3655469 : Blo 798342 3655469 := bstep (se 3 (by rfl) ⟨685400, by rfl⟩ : syracuseStep 3655469 = 1370801) B1370801
theorem B1197899 : Blo 798342 1197899 := bstep (se 1 (by rfl) ⟨898424, by rfl⟩ : syracuseStep 1197899 = 1796849) B1796849
theorem B1197911 : Blo 798342 1197911 := bstep (se 1 (by rfl) ⟨898433, by rfl⟩ : syracuseStep 1197911 = 1796867) B1796867
theorem B13846373 : Blo 798342 13846373 := bstep (se 4 (by rfl) ⟨1298097, by rfl⟩ : syracuseStep 13846373 = 2596195) B2596195
theorem B1197977 : Blo 798342 1197977 := bstep (se 2 (by rfl) ⟨449241, by rfl⟩ : syracuseStep 1197977 = 898483) B898483
theorem B2705345 : Blo 798342 2705345 := bstep (se 2 (by rfl) ⟨1014504, by rfl⟩ : syracuseStep 2705345 = 2029009) B2029009
theorem B3033035 : Blo 798342 3033035 := bstep (se 1 (by rfl) ⟨2274776, by rfl⟩ : syracuseStep 3033035 = 4549553) B4549553
theorem B1198091 : Blo 798342 1198091 := bstep (se 1 (by rfl) ⟨898568, by rfl⟩ : syracuseStep 1198091 = 1797137) B1797137
theorem B1198103 : Blo 798342 1198103 := bstep (se 1 (by rfl) ⟨898577, by rfl⟩ : syracuseStep 1198103 = 1797155) B1797155
theorem B2279447 : Blo 798342 2279447 := bstep (se 1 (by rfl) ⟨1709585, by rfl⟩ : syracuseStep 2279447 = 3419171) B3419171
theorem B1198169 : Blo 798342 1198169 := bstep (se 2 (by rfl) ⟨449313, by rfl⟩ : syracuseStep 1198169 = 898627) B898627
theorem B4049027 : Blo 798342 4049027 := bstep (se 1 (by rfl) ⟨3036770, by rfl⟩ : syracuseStep 4049027 = 6073541) B6073541
theorem B3033233 : Blo 798342 3033233 := bstep (se 2 (by rfl) ⟨1137462, by rfl⟩ : syracuseStep 3033233 = 2274925) B2274925
theorem B1198283 : Blo 798342 1198283 := bstep (se 1 (by rfl) ⟨898712, by rfl⟩ : syracuseStep 1198283 = 1797425) B1797425
theorem B1198295 : Blo 798342 1198295 := bstep (se 1 (by rfl) ⟨898721, by rfl⟩ : syracuseStep 1198295 = 1797443) B1797443
theorem B1198361 : Blo 798342 1198361 := bstep (se 2 (by rfl) ⟨449385, by rfl⟩ : syracuseStep 1198361 = 898771) B898771
theorem B1198475 : Blo 798342 1198475 := bstep (se 1 (by rfl) ⟨898856, by rfl⟩ : syracuseStep 1198475 = 1797713) B1797713
theorem B1198487 : Blo 798342 1198487 := bstep (se 1 (by rfl) ⟨898865, by rfl⟩ : syracuseStep 1198487 = 1797731) B1797731
theorem B1198553 : Blo 798342 1198553 := bstep (se 2 (by rfl) ⟨449457, by rfl⟩ : syracuseStep 1198553 = 898915) B898915
theorem B2705885 : Blo 798342 2705885 := bstep (se 3 (by rfl) ⟨507353, by rfl⟩ : syracuseStep 2705885 = 1014707) B1014707
theorem B1198667 : Blo 798342 1198667 := bstep (se 1 (by rfl) ⟨899000, by rfl⟩ : syracuseStep 1198667 = 1798001) B1798001
theorem B1198679 : Blo 798342 1198679 := bstep (se 1 (by rfl) ⟨899009, by rfl⟩ : syracuseStep 1198679 = 1798019) B1798019
theorem B3426961 : Blo 798342 3426961 := bstep (se 2 (by rfl) ⟨1285110, by rfl⟩ : syracuseStep 3426961 = 2570221) B2570221
theorem B1198745 : Blo 798342 1198745 := bstep (se 2 (by rfl) ⟨449529, by rfl⟩ : syracuseStep 1198745 = 899059) B899059
theorem B1198859 : Blo 798342 1198859 := bstep (se 1 (by rfl) ⟨899144, by rfl⟩ : syracuseStep 1198859 = 1798289) B1798289
theorem B1198871 : Blo 798342 1198871 := bstep (se 1 (by rfl) ⟨899153, by rfl⟩ : syracuseStep 1198871 = 1798307) B1798307
theorem B1198937 : Blo 798342 1198937 := bstep (se 2 (by rfl) ⟨449601, by rfl⟩ : syracuseStep 1198937 = 899203) B899203
theorem B3034007 : Blo 798342 3034007 := bstep (se 1 (by rfl) ⟨2275505, by rfl⟩ : syracuseStep 3034007 = 4551011) B4551011
theorem B1199051 : Blo 798342 1199051 := bstep (se 1 (by rfl) ⟨899288, by rfl⟩ : syracuseStep 1199051 = 1798577) B1798577
theorem B1199063 : Blo 798342 1199063 := bstep (se 1 (by rfl) ⟨899297, by rfl⟩ : syracuseStep 1199063 = 1798595) B1798595
theorem B1199129 : Blo 798342 1199129 := bstep (se 2 (by rfl) ⟨449673, by rfl⟩ : syracuseStep 1199129 = 899347) B899347
theorem B6835265 : Blo 798342 6835265 := bstep (se 2 (by rfl) ⟨2563224, by rfl⟩ : syracuseStep 6835265 = 5126449) B5126449
theorem B3296321 : Blo 798342 3296321 := bstep (se 2 (by rfl) ⟨1236120, by rfl⟩ : syracuseStep 3296321 = 2472241) B2472241
theorem B3034205 : Blo 798342 3034205 := bstep (se 3 (by rfl) ⟨568913, by rfl⟩ : syracuseStep 3034205 = 1137827) B1137827
theorem B1625203 : Blo 798342 1625203 := bstep (se 1 (by rfl) ⟨1218902, by rfl⟩ : syracuseStep 1625203 = 2437805) B2437805
theorem B1199243 : Blo 798342 1199243 := bstep (se 1 (by rfl) ⟨899432, by rfl⟩ : syracuseStep 1199243 = 1798865) B1798865
theorem B1199255 : Blo 798342 1199255 := bstep (se 1 (by rfl) ⟨899441, by rfl⟩ : syracuseStep 1199255 = 1798883) B1798883
theorem B1199321 : Blo 798342 1199321 := bstep (se 2 (by rfl) ⟨449745, by rfl⟩ : syracuseStep 1199321 = 899491) B899491
theorem B1199435 : Blo 798342 1199435 := bstep (se 1 (by rfl) ⟨899576, by rfl⟩ : syracuseStep 1199435 = 1799153) B1799153
theorem B1199447 : Blo 798342 1199447 := bstep (se 1 (by rfl) ⟨899585, by rfl⟩ : syracuseStep 1199447 = 1799171) B1799171
theorem B1199513 : Blo 798342 1199513 := bstep (se 2 (by rfl) ⟨449817, by rfl⟩ : syracuseStep 1199513 = 899635) B899635
theorem B1199627 : Blo 798342 1199627 := bstep (se 1 (by rfl) ⟨899720, by rfl⟩ : syracuseStep 1199627 = 1799441) B1799441
theorem B1199639 : Blo 798342 1199639 := bstep (se 1 (by rfl) ⟨899729, by rfl⟩ : syracuseStep 1199639 = 1799459) B1799459
theorem B2707019 : Blo 798342 2707019 := bstep (se 1 (by rfl) ⟨2030264, by rfl⟩ : syracuseStep 2707019 = 4060529) B4060529
theorem B1199705 : Blo 798342 1199705 := bstep (se 2 (by rfl) ⟨449889, by rfl⟩ : syracuseStep 1199705 = 899779) B899779
theorem B1199819 : Blo 798342 1199819 := bstep (se 1 (by rfl) ⟨899864, by rfl⟩ : syracuseStep 1199819 = 1799729) B1799729
theorem B1199831 : Blo 798342 1199831 := bstep (se 1 (by rfl) ⟨899873, by rfl⟩ : syracuseStep 1199831 = 1799747) B1799747
theorem B1199897 : Blo 798342 1199897 := bstep (se 2 (by rfl) ⟨449961, by rfl⟩ : syracuseStep 1199897 = 899923) B899923
theorem B2707289 : Blo 798342 2707289 := bstep (se 2 (by rfl) ⟨1015233, by rfl⟩ : syracuseStep 2707289 = 2030467) B2030467
theorem B1200011 : Blo 798342 1200011 := bstep (se 1 (by rfl) ⟨900008, by rfl⟩ : syracuseStep 1200011 = 1800017) B1800017
theorem B1200023 : Blo 798342 1200023 := bstep (se 1 (by rfl) ⟨900017, by rfl⟩ : syracuseStep 1200023 = 1800035) B1800035
theorem B1200089 : Blo 798342 1200089 := bstep (se 2 (by rfl) ⟨450033, by rfl⟩ : syracuseStep 1200089 = 900067) B900067
theorem B1822771 : Blo 798342 1822771 := bstep (se 1 (by rfl) ⟨1367078, by rfl⟩ : syracuseStep 1822771 = 2734157) B2734157
theorem B1200203 : Blo 798342 1200203 := bstep (se 1 (by rfl) ⟨900152, by rfl⟩ : syracuseStep 1200203 = 1800305) B1800305
theorem B3657803 : Blo 798342 3657803 := bstep (se 1 (by rfl) ⟨2743352, by rfl⟩ : syracuseStep 3657803 = 5486705) B5486705
theorem B3854411 : Blo 798342 3854411 := bstep (se 1 (by rfl) ⟨2890808, by rfl⟩ : syracuseStep 3854411 = 5781617) B5781617
theorem B1200215 : Blo 798342 1200215 := bstep (se 1 (by rfl) ⟨900161, by rfl⟩ : syracuseStep 1200215 = 1800323) B1800323
theorem B1200281 : Blo 798342 1200281 := bstep (se 2 (by rfl) ⟨450105, by rfl⟩ : syracuseStep 1200281 = 900211) B900211
theorem B1200395 : Blo 798342 1200395 := bstep (se 1 (by rfl) ⟨900296, by rfl⟩ : syracuseStep 1200395 = 1800593) B1800593
theorem B1200407 : Blo 798342 1200407 := bstep (se 1 (by rfl) ⟨900305, by rfl⟩ : syracuseStep 1200407 = 1800611) B1800611
theorem B1200473 : Blo 798342 1200473 := bstep (se 2 (by rfl) ⟨450177, by rfl⟩ : syracuseStep 1200473 = 900355) B900355
theorem B2281907 : Blo 798342 2281907 := bstep (se 1 (by rfl) ⟨1711430, by rfl⟩ : syracuseStep 2281907 = 3422861) B3422861
theorem B1200587 : Blo 798342 1200587 := bstep (se 1 (by rfl) ⟨900440, by rfl⟩ : syracuseStep 1200587 = 1800881) B1800881
theorem B1298903 : Blo 798342 1298903 := bstep (se 1 (by rfl) ⟨974177, by rfl⟩ : syracuseStep 1298903 = 1948355) B1948355
theorem B1200599 : Blo 798342 1200599 := bstep (se 1 (by rfl) ⟨900449, by rfl⟩ : syracuseStep 1200599 = 1800899) B1800899
theorem B1200665 : Blo 798342 1200665 := bstep (se 2 (by rfl) ⟨450249, by rfl⟩ : syracuseStep 1200665 = 900499) B900499
theorem B1200779 : Blo 798342 1200779 := bstep (se 1 (by rfl) ⟨900584, by rfl⟩ : syracuseStep 1200779 = 1801169) B1801169
theorem B1200791 : Blo 798342 1200791 := bstep (se 1 (by rfl) ⟨900593, by rfl⟩ : syracuseStep 1200791 = 1801187) B1801187
theorem B1200857 : Blo 798342 1200857 := bstep (se 2 (by rfl) ⟨450321, by rfl⟩ : syracuseStep 1200857 = 900643) B900643
theorem B1200971 : Blo 798342 1200971 := bstep (se 1 (by rfl) ⟨900728, by rfl⟩ : syracuseStep 1200971 = 1801457) B1801457
theorem B1200983 : Blo 798342 1200983 := bstep (se 1 (by rfl) ⟨900737, by rfl⟩ : syracuseStep 1200983 = 1801475) B1801475
theorem B1201049 : Blo 798342 1201049 := bstep (se 2 (by rfl) ⟨450393, by rfl⟩ : syracuseStep 1201049 = 900787) B900787
theorem B51958745 : Blo 798342 51958745 := bstep (se 2 (by rfl) ⟨19484529, by rfl⟩ : syracuseStep 51958745 = 38969059) B38969059
theorem B3036163 : Blo 798342 3036163 := bstep (se 1 (by rfl) ⟨2277122, by rfl⟩ : syracuseStep 3036163 = 4554245) B4554245
theorem B1201163 : Blo 798342 1201163 := bstep (se 1 (by rfl) ⟨900872, by rfl⟩ : syracuseStep 1201163 = 1801745) B1801745
theorem B1201175 : Blo 798342 1201175 := bstep (se 1 (by rfl) ⟨900881, by rfl⟩ : syracuseStep 1201175 = 1801763) B1801763
theorem B1201241 : Blo 798342 1201241 := bstep (se 2 (by rfl) ⟨450465, by rfl⟩ : syracuseStep 1201241 = 900931) B900931
theorem B1201355 : Blo 798342 1201355 := bstep (se 1 (by rfl) ⟨901016, by rfl⟩ : syracuseStep 1201355 = 1802033) B1802033
theorem B1201367 : Blo 798342 1201367 := bstep (se 1 (by rfl) ⟨901025, by rfl⟩ : syracuseStep 1201367 = 1802051) B1802051
theorem B1201433 : Blo 798342 1201433 := bstep (se 2 (by rfl) ⟨450537, by rfl⟩ : syracuseStep 1201433 = 901075) B901075
theorem B3036467 : Blo 798342 3036467 := bstep (se 1 (by rfl) ⟨2277350, by rfl⟩ : syracuseStep 3036467 = 4554701) B4554701
theorem B1201547 : Blo 798342 1201547 := bstep (se 1 (by rfl) ⟨901160, by rfl⟩ : syracuseStep 1201547 = 1802321) B1802321
theorem B6837655 : Blo 798342 6837655 := bstep (se 1 (by rfl) ⟨5128241, by rfl⟩ : syracuseStep 6837655 = 10256483) B10256483
theorem B1201559 : Blo 798342 1201559 := bstep (se 1 (by rfl) ⟨901169, by rfl⟩ : syracuseStep 1201559 = 1802339) B1802339
theorem B1201625 : Blo 798342 1201625 := bstep (se 2 (by rfl) ⟨450609, by rfl⟩ : syracuseStep 1201625 = 901219) B901219
theorem B1201739 : Blo 798342 1201739 := bstep (se 1 (by rfl) ⟨901304, by rfl⟩ : syracuseStep 1201739 = 1802609) B1802609
theorem B1201751 : Blo 798342 1201751 := bstep (se 1 (by rfl) ⟨901313, by rfl⟩ : syracuseStep 1201751 = 1802627) B1802627
theorem B1201817 : Blo 798342 1201817 := bstep (se 2 (by rfl) ⟨450681, by rfl⟩ : syracuseStep 1201817 = 901363) B901363
theorem B6477529 : Blo 798342 6477529 := bstep (se 2 (by rfl) ⟨2429073, by rfl⟩ : syracuseStep 6477529 = 4858147) B4858147
theorem B1201931 : Blo 798342 1201931 := bstep (se 1 (by rfl) ⟨901448, by rfl⟩ : syracuseStep 1201931 = 1802897) B1802897
theorem B4052753 : Blo 798342 4052753 := bstep (se 2 (by rfl) ⟨1519782, by rfl⟩ : syracuseStep 4052753 = 3039565) B3039565
theorem B1201943 : Blo 798342 1201943 := bstep (se 1 (by rfl) ⟨901457, by rfl⟩ : syracuseStep 1201943 = 1802915) B1802915
theorem B1202009 : Blo 798342 1202009 := bstep (se 2 (by rfl) ⟨450753, by rfl⟩ : syracuseStep 1202009 = 901507) B901507
theorem B4052915 : Blo 798342 4052915 := bstep (se 1 (by rfl) ⟨3039686, by rfl⟩ : syracuseStep 4052915 = 6079373) B6079373
theorem B3037121 : Blo 798342 3037121 := bstep (se 2 (by rfl) ⟨1138920, by rfl⟩ : syracuseStep 3037121 = 2277841) B2277841
theorem B1202123 : Blo 798342 1202123 := bstep (se 1 (by rfl) ⟨901592, by rfl⟩ : syracuseStep 1202123 = 1803185) B1803185
theorem B1202135 : Blo 798342 1202135 := bstep (se 1 (by rfl) ⟨901601, by rfl⟩ : syracuseStep 1202135 = 1803203) B1803203
theorem B1202201 : Blo 798342 1202201 := bstep (se 2 (by rfl) ⟨450825, by rfl⟩ : syracuseStep 1202201 = 901651) B901651
theorem B1202315 : Blo 798342 1202315 := bstep (se 1 (by rfl) ⟨901736, by rfl⟩ : syracuseStep 1202315 = 1803473) B1803473
theorem B1202327 : Blo 798342 1202327 := bstep (se 1 (by rfl) ⟨901745, by rfl⟩ : syracuseStep 1202327 = 1803491) B1803491
theorem B1202393 : Blo 798342 1202393 := bstep (se 2 (by rfl) ⟨450897, by rfl⟩ : syracuseStep 1202393 = 901795) B901795
theorem B1136921 : Blo 798342 1136921 := bstep (se 2 (by rfl) ⟨426345, by rfl⟩ : syracuseStep 1136921 = 852691) B852691
theorem B1202507 : Blo 798342 1202507 := bstep (se 1 (by rfl) ⟨901880, by rfl⟩ : syracuseStep 1202507 = 1803761) B1803761
theorem B1202519 : Blo 798342 1202519 := bstep (se 1 (by rfl) ⟨901889, by rfl⟩ : syracuseStep 1202519 = 1803779) B1803779
theorem B49174901 : Blo 798342 49174901 := bstep (se 5 (by rfl) ⟨2305073, by rfl⟩ : syracuseStep 49174901 = 4610147) B4610147
theorem B1137035 : Blo 798342 1137035 := bstep (se 1 (by rfl) ⟨852776, by rfl⟩ : syracuseStep 1137035 = 1705553) B1705553
theorem B1202585 : Blo 798342 1202585 := bstep (se 2 (by rfl) ⟨450969, by rfl⟩ : syracuseStep 1202585 = 901939) B901939
theorem B1202699 : Blo 798342 1202699 := bstep (se 1 (by rfl) ⟨902024, by rfl⟩ : syracuseStep 1202699 = 1804049) B1804049
theorem B1202711 : Blo 798342 1202711 := bstep (se 1 (by rfl) ⟨902033, by rfl⟩ : syracuseStep 1202711 = 1804067) B1804067
theorem B1202777 : Blo 798342 1202777 := bstep (se 2 (by rfl) ⟨451041, by rfl⟩ : syracuseStep 1202777 = 902083) B902083
theorem B1202891 : Blo 798342 1202891 := bstep (se 1 (by rfl) ⟨902168, by rfl⟩ : syracuseStep 1202891 = 1804337) B1804337
theorem B1202903 : Blo 798342 1202903 := bstep (se 1 (by rfl) ⟨902177, by rfl⟩ : syracuseStep 1202903 = 1804355) B1804355
theorem B1202969 : Blo 798342 1202969 := bstep (se 2 (by rfl) ⟨451113, by rfl⟩ : syracuseStep 1202969 = 902227) B902227
theorem B1203083 : Blo 798342 1203083 := bstep (se 1 (by rfl) ⟨902312, by rfl⟩ : syracuseStep 1203083 = 1804625) B1804625
theorem B1137559 : Blo 798342 1137559 := bstep (se 1 (by rfl) ⟨853169, by rfl⟩ : syracuseStep 1137559 = 1706339) B1706339
theorem B1203095 : Blo 798342 1203095 := bstep (se 1 (by rfl) ⟨902321, by rfl⟩ : syracuseStep 1203095 = 1804643) B1804643
theorem B2022347 : Blo 798342 2022347 := bstep (se 1 (by rfl) ⟨1516760, by rfl⟩ : syracuseStep 2022347 = 3033521) B3033521
theorem B1203161 : Blo 798342 1203161 := bstep (se 2 (by rfl) ⟨451185, by rfl⟩ : syracuseStep 1203161 = 902371) B902371
theorem B2284595 : Blo 798342 2284595 := bstep (se 1 (by rfl) ⟨1713446, by rfl⟩ : syracuseStep 2284595 = 3426893) B3426893
theorem B1203275 : Blo 798342 1203275 := bstep (se 1 (by rfl) ⟨902456, by rfl⟩ : syracuseStep 1203275 = 1804913) B1804913
theorem B1203287 : Blo 798342 1203287 := bstep (se 1 (by rfl) ⟨902465, by rfl⟩ : syracuseStep 1203287 = 1804931) B1804931
theorem B1203353 : Blo 798342 1203353 := bstep (se 2 (by rfl) ⟨451257, by rfl⟩ : syracuseStep 1203353 = 902515) B902515
theorem B3038381 : Blo 798342 3038381 := bstep (se 3 (by rfl) ⟨569696, by rfl⟩ : syracuseStep 3038381 = 1139393) B1139393
theorem B3038411 : Blo 798342 3038411 := bstep (se 1 (by rfl) ⟨2278808, by rfl⟩ : syracuseStep 3038411 = 4557617) B4557617
theorem B1203467 : Blo 798342 1203467 := bstep (se 1 (by rfl) ⟨902600, by rfl⟩ : syracuseStep 1203467 = 1805201) B1805201
theorem B1203479 : Blo 798342 1203479 := bstep (se 1 (by rfl) ⟨902609, by rfl⟩ : syracuseStep 1203479 = 1805219) B1805219
theorem B1367435 : Blo 798342 1367435 := bstep (se 1 (by rfl) ⟨1025576, by rfl⟩ : syracuseStep 1367435 = 2051153) B2051153
theorem B9100835 : Blo 798342 9100835 := bstep (se 1 (by rfl) ⟨6825626, by rfl⟩ : syracuseStep 9100835 = 13651253) B13651253
theorem B13655627 : Blo 798342 13655627 := bstep (se 1 (by rfl) ⟨10241720, by rfl⟩ : syracuseStep 13655627 = 20483441) B20483441
theorem B1924697 : Blo 798342 1924697 := bstep (se 2 (by rfl) ⟨721761, by rfl⟩ : syracuseStep 1924697 = 1443523) B1443523
theorem B1138379 : Blo 798342 1138379 := bstep (se 1 (by rfl) ⟨853784, by rfl⟩ : syracuseStep 1138379 = 1707569) B1707569
theorem B1171147 : Blo 798342 1171147 := bstep (se 1 (by rfl) ⟨878360, by rfl⟩ : syracuseStep 1171147 = 1756721) B1756721
theorem B17325809 : Blo 798342 17325809 := bstep (se 2 (by rfl) ⟨6497178, by rfl⟩ : syracuseStep 17325809 = 12994357) B12994357
theorem B4054859 : Blo 798342 4054859 := bstep (se 1 (by rfl) ⟨3041144, by rfl⟩ : syracuseStep 4054859 = 6082289) B6082289
theorem B3039065 : Blo 798342 3039065 := bstep (se 2 (by rfl) ⟨1139649, by rfl⟩ : syracuseStep 3039065 = 2279299) B2279299
theorem B2023319 : Blo 798342 2023319 := bstep (se 1 (by rfl) ⟨1517489, by rfl⟩ : syracuseStep 2023319 = 3034979) B3034979
theorem B3891331 : Blo 798342 3891331 := bstep (se 1 (by rfl) ⟨2918498, by rfl⟩ : syracuseStep 3891331 = 5836997) B5836997
theorem B27779213 : Blo 798342 27779213 := bstep (se 3 (by rfl) ⟨5208602, by rfl⟩ : syracuseStep 27779213 = 10417205) B10417205
theorem B18473111 : Blo 798342 18473111 := bstep (se 1 (by rfl) ⟨13854833, by rfl⟩ : syracuseStep 18473111 = 27709667) B27709667
theorem B3039383 : Blo 798342 3039383 := bstep (se 1 (by rfl) ⟨2279537, by rfl⟩ : syracuseStep 3039383 = 4559075) B4559075
theorem B5923277 : Blo 798342 5923277 := bstep (se 3 (by rfl) ⟨1110614, by rfl⟩ : syracuseStep 5923277 = 2221229) B2221229
theorem B2023987 : Blo 798342 2023987 := bstep (se 1 (by rfl) ⟨1517990, by rfl⟩ : syracuseStep 2023987 = 3035981) B3035981
theorem B4547137 : Blo 798342 4547137 := bstep (se 2 (by rfl) ⟨1705176, by rfl⟩ : syracuseStep 4547137 = 3410353) B3410353
theorem B2024129 : Blo 798342 2024129 := bstep (se 2 (by rfl) ⟨759048, by rfl⟩ : syracuseStep 2024129 = 1518097) B1518097
theorem B1172183 : Blo 798342 1172183 := bstep (se 1 (by rfl) ⟨879137, by rfl⟩ : syracuseStep 1172183 = 1758275) B1758275
theorem B1368857 : Blo 798342 1368857 := bstep (se 2 (by rfl) ⟨513321, by rfl⟩ : syracuseStep 1368857 = 1026643) B1026643
theorem B3040051 : Blo 798342 3040051 := bstep (se 1 (by rfl) ⟨2280038, by rfl⟩ : syracuseStep 3040051 = 4560077) B4560077
theorem B5202839 : Blo 798342 5202839 := bstep (se 1 (by rfl) ⟨3902129, by rfl⟩ : syracuseStep 5202839 = 7804259) B7804259
theorem B3072971 : Blo 798342 3072971 := bstep (se 1 (by rfl) ⟨2304728, by rfl⟩ : syracuseStep 3072971 = 4609457) B4609457
theorem B1827863 : Blo 798342 1827863 := bstep (se 1 (by rfl) ⟨1370897, by rfl⟩ : syracuseStep 1827863 = 2741795) B2741795
theorem B3237043 : Blo 798342 3237043 := bstep (se 1 (by rfl) ⟨2427782, by rfl⟩ : syracuseStep 3237043 = 4855565) B4855565
theorem B1828055 : Blo 798342 1828055 := bstep (se 1 (by rfl) ⟨1371041, by rfl⟩ : syracuseStep 1828055 = 2742083) B2742083
theorem B910711 : Blo 798342 910711 := bstep (se 1 (by rfl) ⟨683033, by rfl⟩ : syracuseStep 910711 = 1366067) B1366067
theorem B1926551 : Blo 798342 1926551 := bstep (se 1 (by rfl) ⟨1444913, by rfl⟩ : syracuseStep 1926551 = 2889827) B2889827
theorem B1140247 : Blo 798342 1140247 := bstep (se 1 (by rfl) ⟨855185, by rfl⟩ : syracuseStep 1140247 = 1710371) B1710371
theorem B4056641 : Blo 798342 4056641 := bstep (se 2 (by rfl) ⟨1521240, by rfl⟩ : syracuseStep 4056641 = 3042481) B3042481
theorem B2025395 : Blo 798342 2025395 := bstep (se 1 (by rfl) ⟨1519046, by rfl⟩ : syracuseStep 2025395 = 3038093) B3038093
theorem B3008477 : Blo 798342 3008477 := bstep (se 3 (by rfl) ⟨564089, by rfl⟩ : syracuseStep 3008477 = 1128179) B1128179
theorem B3041297 : Blo 798342 3041297 := bstep (se 2 (by rfl) ⟨1140486, by rfl⟩ : syracuseStep 3041297 = 2280973) B2280973
theorem B1927243 : Blo 798342 1927243 := bstep (se 1 (by rfl) ⟨1445432, by rfl⟩ : syracuseStep 1927243 = 2890865) B2890865
theorem B10250333 : Blo 798342 10250333 := bstep (se 3 (by rfl) ⟨1921937, by rfl⟩ : syracuseStep 10250333 = 3843875) B3843875
theorem B1796363 : Blo 798342 1796363 := bstep (se 1 (by rfl) ⟨1347272, by rfl⟩ : syracuseStep 1796363 = 2694545) B2694545
theorem B1796417 : Blo 798342 1796417 := bstep (se 2 (by rfl) ⟨673656, by rfl⟩ : syracuseStep 1796417 = 1347313) B1347313
theorem B3074449 : Blo 798342 3074449 := bstep (se 2 (by rfl) ⟨1152918, by rfl⟩ : syracuseStep 3074449 = 2305837) B2305837
theorem B2025931 : Blo 798342 2025931 := bstep (se 1 (by rfl) ⟨1519448, by rfl⟩ : syracuseStep 2025931 = 3038897) B3038897
theorem B1796633 : Blo 798342 1796633 := bstep (se 2 (by rfl) ⟨673737, by rfl⟩ : syracuseStep 1796633 = 1347475) B1347475
theorem B2026073 : Blo 798342 2026073 := bstep (se 2 (by rfl) ⟨759777, by rfl⟩ : syracuseStep 2026073 = 1519555) B1519555
theorem B5761637 : Blo 798342 5761637 := bstep (se 4 (by rfl) ⟨540153, by rfl⟩ : syracuseStep 5761637 = 1080307) B1080307
theorem B1796723 : Blo 798342 1796723 := bstep (se 1 (by rfl) ⟨1347542, by rfl⟩ : syracuseStep 1796723 = 2695085) B2695085
theorem B1796759 : Blo 798342 1796759 := bstep (se 1 (by rfl) ⟨1347569, by rfl⟩ : syracuseStep 1796759 = 2695139) B2695139
theorem B3041995 : Blo 798342 3041995 := bstep (se 1 (by rfl) ⟨2281496, by rfl⟩ : syracuseStep 3041995 = 4562993) B4562993
theorem B1796939 : Blo 798342 1796939 := bstep (se 1 (by rfl) ⟨1347704, by rfl⟩ : syracuseStep 1796939 = 2695409) B2695409
theorem B1796993 : Blo 798342 1796993 := bstep (se 2 (by rfl) ⟨673872, by rfl⟩ : syracuseStep 1796993 = 1347745) B1347745
theorem B3074989 : Blo 798342 3074989 := bstep (se 3 (by rfl) ⟨576560, by rfl⟩ : syracuseStep 3074989 = 1153121) B1153121
theorem B13003697 : Blo 798342 13003697 := bstep (se 2 (by rfl) ⟨4876386, by rfl⟩ : syracuseStep 13003697 = 9752773) B9752773
theorem B1010647 : Blo 798342 1010647 := bstep (se 1 (by rfl) ⟨757985, by rfl⟩ : syracuseStep 1010647 = 1515971) B1515971
theorem B3042269 : Blo 798342 3042269 := bstep (se 3 (by rfl) ⟨570425, by rfl⟩ : syracuseStep 3042269 = 1140851) B1140851
theorem B5762123 : Blo 798342 5762123 := bstep (se 1 (by rfl) ⟨4321592, by rfl⟩ : syracuseStep 5762123 = 8643185) B8643185
theorem B1797209 : Blo 798342 1797209 := bstep (se 2 (by rfl) ⟨673953, by rfl⟩ : syracuseStep 1797209 = 1347907) B1347907
theorem B1797299 : Blo 798342 1797299 := bstep (se 1 (by rfl) ⟨1347974, by rfl⟩ : syracuseStep 1797299 = 2695949) B2695949
theorem B1797335 : Blo 798342 1797335 := bstep (se 1 (by rfl) ⟨1348001, by rfl⟩ : syracuseStep 1797335 = 2696003) B2696003
theorem B1797515 : Blo 798342 1797515 := bstep (se 1 (by rfl) ⟨1348136, by rfl⟩ : syracuseStep 1797515 = 2696273) B2696273
theorem B2026903 : Blo 798342 2026903 := bstep (se 1 (by rfl) ⟨1520177, by rfl⟩ : syracuseStep 2026903 = 3040355) B3040355
theorem B1797569 : Blo 798342 1797569 := bstep (se 2 (by rfl) ⟨674088, by rfl⟩ : syracuseStep 1797569 = 1348177) B1348177
theorem B4058585 : Blo 798342 4058585 := bstep (se 2 (by rfl) ⟨1521969, by rfl⟩ : syracuseStep 4058585 = 3043939) B3043939
theorem B5139929 : Blo 798342 5139929 := bstep (se 2 (by rfl) ⟨1927473, by rfl⟩ : syracuseStep 5139929 = 3854947) B3854947
theorem B3042967 : Blo 798342 3042967 := bstep (se 1 (by rfl) ⟨2282225, by rfl⟩ : syracuseStep 3042967 = 4564451) B4564451
theorem B1797785 : Blo 798342 1797785 := bstep (se 2 (by rfl) ⟨674169, by rfl⟩ : syracuseStep 1797785 = 1348339) B1348339
theorem B1797875 : Blo 798342 1797875 := bstep (se 1 (by rfl) ⟨1348406, by rfl⟩ : syracuseStep 1797875 = 2696813) B2696813
theorem B1011467 : Blo 798342 1011467 := bstep (se 1 (by rfl) ⟨758600, by rfl⟩ : syracuseStep 1011467 = 1517201) B1517201
theorem B1797911 : Blo 798342 1797911 := bstep (se 1 (by rfl) ⟨1348433, by rfl⟩ : syracuseStep 1797911 = 2696867) B2696867
theorem B2027339 : Blo 798342 2027339 := bstep (se 1 (by rfl) ⟨1520504, by rfl⟩ : syracuseStep 2027339 = 3041009) B3041009
theorem B4550579 : Blo 798342 4550579 := bstep (se 1 (by rfl) ⟨3412934, by rfl⟩ : syracuseStep 4550579 = 6825869) B6825869
theorem B1798091 : Blo 798342 1798091 := bstep (se 1 (by rfl) ⟨1348568, by rfl⟩ : syracuseStep 1798091 = 2697137) B2697137
theorem B1798145 : Blo 798342 1798145 := bstep (se 2 (by rfl) ⟨674304, by rfl⟩ : syracuseStep 1798145 = 1348609) B1348609
theorem B6942871 : Blo 798342 6942871 := bstep (se 1 (by rfl) ⟨5207153, by rfl⟩ : syracuseStep 6942871 = 10414307) B10414307
theorem B2027713 : Blo 798342 2027713 := bstep (se 2 (by rfl) ⟨760392, by rfl⟩ : syracuseStep 2027713 = 1520785) B1520785
theorem B1798361 : Blo 798342 1798361 := bstep (se 2 (by rfl) ⟨674385, by rfl⟩ : syracuseStep 1798361 = 1348771) B1348771
theorem B3240157 : Blo 798342 3240157 := bstep (se 3 (by rfl) ⟨607529, by rfl⟩ : syracuseStep 3240157 = 1215059) B1215059
theorem B1798451 : Blo 798342 1798451 := bstep (se 1 (by rfl) ⟨1348838, by rfl⟩ : syracuseStep 1798451 = 2697677) B2697677
theorem B1798487 : Blo 798342 1798487 := bstep (se 1 (by rfl) ⟨1348865, by rfl⟩ : syracuseStep 1798487 = 2697731) B2697731
theorem B3043757 : Blo 798342 3043757 := bstep (se 3 (by rfl) ⟨570704, by rfl⟩ : syracuseStep 3043757 = 1141409) B1141409
theorem B1012171 : Blo 798342 1012171 := bstep (se 1 (by rfl) ⟨759128, by rfl⟩ : syracuseStep 1012171 = 1518257) B1518257
theorem B1798667 : Blo 798342 1798667 := bstep (se 1 (by rfl) ⟨1349000, by rfl⟩ : syracuseStep 1798667 = 2698001) B2698001
theorem B1798721 : Blo 798342 1798721 := bstep (se 2 (by rfl) ⟨674520, by rfl⟩ : syracuseStep 1798721 = 1349041) B1349041
theorem B6156901 : Blo 798342 6156901 := bstep (se 4 (by rfl) ⟨577209, by rfl⟩ : syracuseStep 6156901 = 1154419) B1154419
theorem B1012439 : Blo 798342 1012439 := bstep (se 1 (by rfl) ⟨759329, by rfl⟩ : syracuseStep 1012439 = 1518659) B1518659
theorem B2028311 : Blo 798342 2028311 := bstep (se 1 (by rfl) ⟨1521233, by rfl⟩ : syracuseStep 2028311 = 3042467) B3042467
theorem B1798937 : Blo 798342 1798937 := bstep (se 2 (by rfl) ⟨674601, by rfl⟩ : syracuseStep 1798937 = 1349203) B1349203
theorem B2159435 : Blo 798342 2159435 := bstep (se 1 (by rfl) ⟨1619576, by rfl⟩ : syracuseStep 2159435 = 3239153) B3239153
theorem B1799027 : Blo 798342 1799027 := bstep (se 1 (by rfl) ⟨1349270, by rfl⟩ : syracuseStep 1799027 = 2698541) B2698541
theorem B1799063 : Blo 798342 1799063 := bstep (se 1 (by rfl) ⟨1349297, by rfl⟩ : syracuseStep 1799063 = 2698595) B2698595
theorem B1438679 : Blo 798342 1438679 := bstep (se 1 (by rfl) ⟨1079009, by rfl⟩ : syracuseStep 1438679 = 2158019) B2158019
theorem B4060205 : Blo 798342 4060205 := bstep (se 3 (by rfl) ⟨761288, by rfl⟩ : syracuseStep 4060205 = 1522577) B1522577
theorem B1799243 : Blo 798342 1799243 := bstep (se 1 (by rfl) ⟨1349432, by rfl⟩ : syracuseStep 1799243 = 2698865) B2698865
theorem B1799297 : Blo 798342 1799297 := bstep (se 2 (by rfl) ⟨674736, by rfl⟩ : syracuseStep 1799297 = 1349473) B1349473
theorem B1799513 : Blo 798342 1799513 := bstep (se 2 (by rfl) ⟨674817, by rfl⟩ : syracuseStep 1799513 = 1349635) B1349635
theorem B4552037 : Blo 798342 4552037 := bstep (se 4 (by rfl) ⟨426753, by rfl⟩ : syracuseStep 4552037 = 853507) B853507
theorem B1013143 : Blo 798342 1013143 := bstep (se 1 (by rfl) ⟨759857, by rfl⟩ : syracuseStep 1013143 = 1519715) B1519715
theorem B1799603 : Blo 798342 1799603 := bstep (se 1 (by rfl) ⟨1349702, by rfl⟩ : syracuseStep 1799603 = 2699405) B2699405
theorem B1799639 : Blo 798342 1799639 := bstep (se 1 (by rfl) ⟨1349729, by rfl⟩ : syracuseStep 1799639 = 2699459) B2699459
theorem B2029121 : Blo 798342 2029121 := bstep (se 2 (by rfl) ⟨760920, by rfl⟩ : syracuseStep 2029121 = 1521841) B1521841
theorem B1537625 : Blo 798342 1537625 := bstep (se 2 (by rfl) ⟨576609, by rfl⟩ : syracuseStep 1537625 = 1153219) B1153219
theorem B1439371 : Blo 798342 1439371 := bstep (se 1 (by rfl) ⟨1079528, by rfl⟩ : syracuseStep 1439371 = 2159057) B2159057
theorem B1799819 : Blo 798342 1799819 := bstep (se 1 (by rfl) ⟨1349864, by rfl⟩ : syracuseStep 1799819 = 2699729) B2699729
theorem B1799873 : Blo 798342 1799873 := bstep (se 2 (by rfl) ⟨674952, by rfl⟩ : syracuseStep 1799873 = 1349905) B1349905
theorem B3045185 : Blo 798342 3045185 := bstep (se 2 (by rfl) ⟨1141944, by rfl⟩ : syracuseStep 3045185 = 2283889) B2283889
theorem B1800089 : Blo 798342 1800089 := bstep (se 2 (by rfl) ⟨675033, by rfl⟩ : syracuseStep 1800089 = 1350067) B1350067
theorem B1800179 : Blo 798342 1800179 := bstep (se 1 (by rfl) ⟨1350134, by rfl⟩ : syracuseStep 1800179 = 2700269) B2700269
theorem B13694993 : Blo 798342 13694993 := bstep (se 2 (by rfl) ⟨5135622, by rfl⟩ : syracuseStep 13694993 = 10271245) B10271245
theorem B1800215 : Blo 798342 1800215 := bstep (se 1 (by rfl) ⟨1350161, by rfl⟩ : syracuseStep 1800215 = 2700323) B2700323
theorem B2029657 : Blo 798342 2029657 := bstep (se 2 (by rfl) ⟨761121, by rfl⟩ : syracuseStep 2029657 = 1522243) B1522243
theorem B1800395 : Blo 798342 1800395 := bstep (se 1 (by rfl) ⟨1350296, by rfl⟩ : syracuseStep 1800395 = 2700593) B2700593
theorem B1800449 : Blo 798342 1800449 := bstep (se 2 (by rfl) ⟨675168, by rfl⟩ : syracuseStep 1800449 = 1350337) B1350337
theorem B5765411 : Blo 798342 5765411 := bstep (se 1 (by rfl) ⟨4324058, by rfl⟩ : syracuseStep 5765411 = 8648117) B8648117
theorem B1800665 : Blo 798342 1800665 := bstep (se 2 (by rfl) ⟨675249, by rfl⟩ : syracuseStep 1800665 = 1350499) B1350499
theorem B2882099 : Blo 798342 2882099 := bstep (se 1 (by rfl) ⟨2161574, by rfl⟩ : syracuseStep 2882099 = 4323149) B4323149
theorem B1800755 : Blo 798342 1800755 := bstep (se 1 (by rfl) ⟨1350566, by rfl⟩ : syracuseStep 1800755 = 2701133) B2701133
theorem B1800791 : Blo 798342 1800791 := bstep (se 1 (by rfl) ⟨1350593, by rfl⟩ : syracuseStep 1800791 = 2701187) B2701187
theorem B1800971 : Blo 798342 1800971 := bstep (se 1 (by rfl) ⟨1350728, by rfl⟩ : syracuseStep 1800971 = 2701457) B2701457
theorem B1801025 : Blo 798342 1801025 := bstep (se 2 (by rfl) ⟨675384, by rfl⟩ : syracuseStep 1801025 = 1350769) B1350769
theorem B1080139 : Blo 798342 1080139 := bstep (se 1 (by rfl) ⟨810104, by rfl⟩ : syracuseStep 1080139 = 1620209) B1620209
theorem B1440755 : Blo 798342 1440755 := bstep (se 1 (by rfl) ⟨1080566, by rfl⟩ : syracuseStep 1440755 = 2161133) B2161133
theorem B1801241 : Blo 798342 1801241 := bstep (se 2 (by rfl) ⟨675465, by rfl⟩ : syracuseStep 1801241 = 1350931) B1350931
theorem B1014859 : Blo 798342 1014859 := bstep (se 1 (by rfl) ⟨761144, by rfl⟩ : syracuseStep 1014859 = 1522289) B1522289
theorem B1801331 : Blo 798342 1801331 := bstep (se 1 (by rfl) ⟨1350998, by rfl⟩ : syracuseStep 1801331 = 2701997) B2701997
theorem B1801367 : Blo 798342 1801367 := bstep (se 1 (by rfl) ⟨1351025, by rfl⟩ : syracuseStep 1801367 = 2702051) B2702051
theorem B2030771 : Blo 798342 2030771 := bstep (se 1 (by rfl) ⟨1523078, by rfl⟩ : syracuseStep 2030771 = 3046157) B3046157
theorem B1801547 : Blo 798342 1801547 := bstep (se 1 (by rfl) ⟨1351160, by rfl⟩ : syracuseStep 1801547 = 2702321) B2702321
theorem B1801601 : Blo 798342 1801601 := bstep (se 2 (by rfl) ⟨675600, by rfl⟩ : syracuseStep 1801601 = 1351201) B1351201
theorem B1801817 : Blo 798342 1801817 := bstep (se 2 (by rfl) ⟨675681, by rfl⟩ : syracuseStep 1801817 = 1351363) B1351363
theorem B1801907 : Blo 798342 1801907 := bstep (se 1 (by rfl) ⟨1351430, by rfl⟩ : syracuseStep 1801907 = 2702861) B2702861
theorem B1801943 : Blo 798342 1801943 := bstep (se 1 (by rfl) ⟨1351457, by rfl⟩ : syracuseStep 1801943 = 2702915) B2702915
theorem B6848387 : Blo 798342 6848387 := bstep (se 1 (by rfl) ⟨5136290, by rfl⟩ : syracuseStep 6848387 = 10272581) B10272581
theorem B1802123 : Blo 798342 1802123 := bstep (se 1 (by rfl) ⟨1351592, by rfl⟩ : syracuseStep 1802123 = 2703185) B2703185
theorem B1802177 : Blo 798342 1802177 := bstep (se 2 (by rfl) ⟨675816, by rfl⟩ : syracuseStep 1802177 = 1351633) B1351633
theorem B1802375 : Blo 798342 1802375 := bstep (se 1 (by rfl) ⟨1351781, by rfl⟩ : syracuseStep 1802375 = 2703563) B2703563
theorem B4554953 : Blo 798342 4554953 := bstep (se 2 (by rfl) ⟨1708107, by rfl⟩ : syracuseStep 4554953 = 3416215) B3416215
theorem B1802555 : Blo 798342 1802555 := bstep (se 1 (by rfl) ⟨1351916, by rfl⟩ : syracuseStep 1802555 = 2703833) B2703833
theorem B1802681 : Blo 798342 1802681 := bstep (se 2 (by rfl) ⟨676005, by rfl⟩ : syracuseStep 1802681 = 1352011) B1352011
theorem B4326007 : Blo 798342 4326007 := bstep (se 1 (by rfl) ⟨3244505, by rfl⟩ : syracuseStep 4326007 = 6489011) B6489011
theorem B6062849 : Blo 798342 6062849 := bstep (se 2 (by rfl) ⟨2273568, by rfl⟩ : syracuseStep 6062849 = 4547137) B4547137
theorem B1803023 : Blo 798342 1803023 := bstep (se 1 (by rfl) ⟨1352267, by rfl⟩ : syracuseStep 1803023 = 2704535) B2704535
theorem B1803041 : Blo 798342 1803041 := bstep (se 2 (by rfl) ⟨676140, by rfl⟩ : syracuseStep 1803041 = 1352281) B1352281
theorem B1803383 : Blo 798342 1803383 := bstep (se 1 (by rfl) ⟨1352537, by rfl⟩ : syracuseStep 1803383 = 2705075) B2705075
theorem B853135 : Blo 798342 853135 := bstep (se 1 (by rfl) ⟨639851, by rfl⟩ : syracuseStep 853135 = 1279703) B1279703
theorem B6161645 : Blo 798342 6161645 := bstep (se 3 (by rfl) ⟨1155308, by rfl⟩ : syracuseStep 6161645 = 2310617) B2310617
theorem B853255 : Blo 798342 853255 := bstep (se 1 (by rfl) ⟨639941, by rfl⟩ : syracuseStep 853255 = 1279883) B1279883
theorem B1803563 : Blo 798342 1803563 := bstep (se 1 (by rfl) ⟨1352672, by rfl⟩ : syracuseStep 1803563 = 2705345) B2705345
theorem B8750429 : Blo 798342 8750429 := bstep (se 3 (by rfl) ⟨1640705, by rfl⟩ : syracuseStep 8750429 = 3281411) B3281411
theorem B7800209 : Blo 798342 7800209 := bstep (se 2 (by rfl) ⟨2925078, by rfl⟩ : syracuseStep 7800209 = 5850157) B5850157
theorem B853511 : Blo 798342 853511 := bstep (se 1 (by rfl) ⟨640133, by rfl⟩ : syracuseStep 853511 = 1280267) B1280267
theorem B1803923 : Blo 798342 1803923 := bstep (se 1 (by rfl) ⟨1352942, by rfl⟩ : syracuseStep 1803923 = 2705885) B2705885
theorem B1705673 : Blo 798342 1705673 := bstep (se 2 (by rfl) ⟨639627, by rfl⟩ : syracuseStep 1705673 = 1279255) B1279255
theorem B1803977 : Blo 798342 1803977 := bstep (se 2 (by rfl) ⟨676491, by rfl⟩ : syracuseStep 1803977 = 1352983) B1352983
theorem B1214281 : Blo 798342 1214281 := bstep (se 2 (by rfl) ⟨455355, by rfl⟩ : syracuseStep 1214281 = 910711) B910711
theorem B1443703 : Blo 798342 1443703 := bstep (se 1 (by rfl) ⟨1082777, by rfl⟩ : syracuseStep 1443703 = 2165555) B2165555
theorem B4556843 : Blo 798342 4556843 := bstep (se 1 (by rfl) ⟨3417632, by rfl⟩ : syracuseStep 4556843 = 6835265) B6835265
theorem B2197547 : Blo 798342 2197547 := bstep (se 1 (by rfl) ⟨1648160, by rfl⟩ : syracuseStep 2197547 = 3296321) B3296321
theorem B854075 : Blo 798342 854075 := bstep (se 1 (by rfl) ⟨640556, by rfl⟩ : syracuseStep 854075 = 1281113) B1281113
theorem B9242741 : Blo 798342 9242741 := bstep (se 5 (by rfl) ⟨433253, by rfl⟩ : syracuseStep 9242741 = 866507) B866507
theorem B2558267 : Blo 798342 2558267 := bstep (se 1 (by rfl) ⟨1918700, by rfl⟩ : syracuseStep 2558267 = 3837401) B3837401
theorem B1804679 : Blo 798342 1804679 := bstep (se 1 (by rfl) ⟨1353509, by rfl⟩ : syracuseStep 1804679 = 2707019) B2707019
theorem B1804859 : Blo 798342 1804859 := bstep (se 1 (by rfl) ⟨1353644, by rfl⟩ : syracuseStep 1804859 = 2707289) B2707289
theorem B3836477 : Blo 798342 3836477 := bstep (se 3 (by rfl) ⟨719339, by rfl⟩ : syracuseStep 3836477 = 1438679) B1438679
theorem B1804985 : Blo 798342 1804985 := bstep (se 2 (by rfl) ⟨676869, by rfl⟩ : syracuseStep 1804985 = 1353739) B1353739
theorem B1444907 : Blo 798342 1444907 := bstep (se 1 (by rfl) ⟨1083680, by rfl⟩ : syracuseStep 1444907 = 2167361) B2167361
theorem B1707193 : Blo 798342 1707193 := bstep (se 2 (by rfl) ⟨640197, by rfl⟩ : syracuseStep 1707193 = 1280395) B1280395
theorem B4099265 : Blo 798342 4099265 := bstep (se 2 (by rfl) ⟨1537224, by rfl⟩ : syracuseStep 4099265 = 3074449) B3074449
theorem B34639163 : Blo 798342 34639163 := bstep (se 1 (by rfl) ⟨25979372, by rfl⟩ : syracuseStep 34639163 = 51958745) B51958745
theorem B9244039 : Blo 798342 9244039 := bstep (se 1 (by rfl) ⟨6933029, by rfl⟩ : syracuseStep 9244039 = 13866059) B13866059
theorem B4558301 : Blo 798342 4558301 := bstep (se 3 (by rfl) ⟨854681, by rfl⟩ : syracuseStep 4558301 = 1709363) B1709363
theorem B1707655 : Blo 798342 1707655 := bstep (se 1 (by rfl) ⟨1280741, by rfl⟩ : syracuseStep 1707655 = 2561483) B2561483
theorem B2166419 : Blo 798342 2166419 := bstep (se 1 (by rfl) ⟨1624814, by rfl⟩ : syracuseStep 2166419 = 3249629) B3249629
theorem B4099985 : Blo 798342 4099985 := bstep (se 2 (by rfl) ⟨1537494, by rfl⟩ : syracuseStep 4099985 = 3074989) B3074989
theorem B1347529 : Blo 798342 1347529 := bstep (se 2 (by rfl) ⟨505323, by rfl⟩ : syracuseStep 1347529 = 1010647) B1010647
theorem B4558801 : Blo 798342 4558801 := bstep (se 2 (by rfl) ⟨1709550, by rfl⟩ : syracuseStep 4558801 = 3419101) B3419101
theorem B856207 : Blo 798342 856207 := bstep (se 1 (by rfl) ⟨642155, by rfl⟩ : syracuseStep 856207 = 1284311) B1284311
theorem B1348231 : Blo 798342 1348231 := bstep (se 1 (by rfl) ⟨1011173, by rfl⟩ : syracuseStep 1348231 = 2022347) B2022347
theorem B4166585 : Blo 798342 4166585 := bstep (se 2 (by rfl) ⟨1562469, by rfl⟩ : syracuseStep 4166585 = 3124939) B3124939
theorem B6067223 : Blo 798342 6067223 := bstep (se 1 (by rfl) ⟨4550417, by rfl⟩ : syracuseStep 6067223 = 9100835) B9100835
theorem B1283131 : Blo 798342 1283131 := bstep (se 1 (by rfl) ⟨962348, by rfl⟩ : syracuseStep 1283131 = 1924697) B1924697
theorem B2888905 : Blo 798342 2888905 := bstep (se 2 (by rfl) ⟨1083339, by rfl⟩ : syracuseStep 2888905 = 2166679) B2166679
theorem B1348879 : Blo 798342 1348879 := bstep (se 1 (by rfl) ⟨1011659, by rfl⟩ : syracuseStep 1348879 = 2023319) B2023319
theorem B2430361 : Blo 798342 2430361 := bstep (se 2 (by rfl) ⟨911385, by rfl⟩ : syracuseStep 2430361 = 1822771) B1822771
theorem B18519475 : Blo 798342 18519475 := bstep (se 1 (by rfl) ⟨13889606, by rfl⟩ : syracuseStep 18519475 = 27779213) B27779213
theorem B31167929 : Blo 798342 31167929 := bstep (se 2 (by rfl) ⟨11687973, by rfl⟩ : syracuseStep 31167929 = 23375947) B23375947
theorem B6821495 : Blo 798342 6821495 := bstep (se 1 (by rfl) ⟨5116121, by rfl⟩ : syracuseStep 6821495 = 10232243) B10232243
theorem B1349419 : Blo 798342 1349419 := bstep (se 1 (by rfl) ⟨1012064, by rfl⟩ : syracuseStep 1349419 = 2024129) B2024129
theorem B4560785 : Blo 798342 4560785 := bstep (se 2 (by rfl) ⟨1710294, by rfl⟩ : syracuseStep 4560785 = 3420589) B3420589
theorem B1349561 : Blo 798342 1349561 := bstep (se 2 (by rfl) ⟨506085, by rfl⟩ : syracuseStep 1349561 = 1012171) B1012171
theorem B1218575 : Blo 798342 1218575 := bstep (se 1 (by rfl) ⟨913931, by rfl⟩ : syracuseStep 1218575 = 1827863) B1827863
theorem B1710227 : Blo 798342 1710227 := bstep (se 1 (by rfl) ⟨1282670, by rfl⟩ : syracuseStep 1710227 = 2565341) B2565341
theorem B4331713 : Blo 798342 4331713 := bstep (se 2 (by rfl) ⟨1624392, by rfl⟩ : syracuseStep 4331713 = 3248785) B3248785
theorem B7706897 : Blo 798342 7706897 := bstep (se 2 (by rfl) ⟨2890086, by rfl⟩ : syracuseStep 7706897 = 5780173) B5780173
theorem B6232643 : Blo 798342 6232643 := bstep (se 1 (by rfl) ⟨4674482, by rfl⟩ : syracuseStep 6232643 = 9348965) B9348965
theorem B1350263 : Blo 798342 1350263 := bstep (se 1 (by rfl) ⟨1012697, by rfl⟩ : syracuseStep 1350263 = 2025395) B2025395
theorem B2005651 : Blo 798342 2005651 := bstep (se 1 (by rfl) ⟨1504238, by rfl⟩ : syracuseStep 2005651 = 3008477) B3008477
theorem B1153721 : Blo 798342 1153721 := bstep (se 2 (by rfl) ⟨432645, by rfl⟩ : syracuseStep 1153721 = 865291) B865291
theorem B924431 : Blo 798342 924431 := bstep (se 1 (by rfl) ⟨693323, by rfl⟩ : syracuseStep 924431 = 1386647) B1386647
theorem B3414899 : Blo 798342 3414899 := bstep (se 1 (by rfl) ⟨2561174, by rfl⟩ : syracuseStep 3414899 = 5122349) B5122349
theorem B4332491 : Blo 798342 4332491 := bstep (se 1 (by rfl) ⟨3249368, by rfl⟩ : syracuseStep 4332491 = 6498737) B6498737
theorem B1350715 : Blo 798342 1350715 := bstep (se 1 (by rfl) ⟨1013036, by rfl⟩ : syracuseStep 1350715 = 2026073) B2026073
theorem B3841091 : Blo 798342 3841091 := bstep (se 1 (by rfl) ⟨2880818, by rfl⟩ : syracuseStep 3841091 = 5761637) B5761637
theorem B9116873 : Blo 798342 9116873 := bstep (se 2 (by rfl) ⟨3418827, by rfl⟩ : syracuseStep 9116873 = 6837655) B6837655
theorem B1350857 : Blo 798342 1350857 := bstep (se 2 (by rfl) ⟨506571, by rfl⟩ : syracuseStep 1350857 = 1013143) B1013143
theorem B2891009 : Blo 798342 2891009 := bstep (se 2 (by rfl) ⟨1084128, by rfl⟩ : syracuseStep 2891009 = 2168257) B2168257
theorem B3841415 : Blo 798342 3841415 := bstep (se 1 (by rfl) ⟨2881061, by rfl⟩ : syracuseStep 3841415 = 5762123) B5762123
theorem B6495623 : Blo 798342 6495623 := bstep (se 1 (by rfl) ⟨4871717, by rfl⟩ : syracuseStep 6495623 = 9743435) B9743435
theorem B3251609 : Blo 798342 3251609 := bstep (se 2 (by rfl) ⟨1219353, by rfl⟩ : syracuseStep 3251609 = 2438707) B2438707
theorem B34676525 : Blo 798342 34676525 := bstep (se 3 (by rfl) ⟨6501848, by rfl⟩ : syracuseStep 34676525 = 13003697) B13003697
theorem B1351559 : Blo 798342 1351559 := bstep (se 1 (by rfl) ⟨1013669, by rfl⟩ : syracuseStep 1351559 = 2027339) B2027339
theorem B1515667 : Blo 798342 1515667 := bstep (se 1 (by rfl) ⟨1136750, by rfl⟩ : syracuseStep 1515667 = 2273501) B2273501
theorem B2695571 : Blo 798342 2695571 := bstep (se 1 (by rfl) ⟨2021678, by rfl⟩ : syracuseStep 2695571 = 4043357) B4043357
theorem B1352207 : Blo 798342 1352207 := bstep (se 1 (by rfl) ⟨1014155, by rfl⟩ : syracuseStep 1352207 = 2028311) B2028311
theorem B2433671 : Blo 798342 2433671 := bstep (se 1 (by rfl) ⟨1825253, by rfl⟩ : syracuseStep 2433671 = 3650507) B3650507
theorem B3416813 : Blo 798342 3416813 := bstep (se 3 (by rfl) ⟨640652, by rfl⟩ : syracuseStep 3416813 = 1281305) B1281305
theorem B1352747 : Blo 798342 1352747 := bstep (se 1 (by rfl) ⟨1014560, by rfl⟩ : syracuseStep 1352747 = 2029121) B2029121
theorem B1025083 : Blo 798342 1025083 := bstep (se 1 (by rfl) ⟨768812, by rfl⟩ : syracuseStep 1025083 = 1537625) B1537625
theorem B10003517 : Blo 798342 10003517 := bstep (se 3 (by rfl) ⟨1875659, by rfl⟩ : syracuseStep 10003517 = 3751319) B3751319
theorem B1516745 : Blo 798342 1516745 := bstep (se 2 (by rfl) ⟨568779, by rfl⟩ : syracuseStep 1516745 = 1137559) B1137559
theorem B14624059 : Blo 798342 14624059 := bstep (se 1 (by rfl) ⟨10968044, by rfl⟩ : syracuseStep 14624059 = 21936089) B21936089
theorem B3417497 : Blo 798342 3417497 := bstep (se 2 (by rfl) ⟨1281561, by rfl⟩ : syracuseStep 3417497 = 2563123) B2563123
theorem B1353145 : Blo 798342 1353145 := bstep (se 2 (by rfl) ⟨507429, by rfl⟩ : syracuseStep 1353145 = 1014859) B1014859
theorem B3843607 : Blo 798342 3843607 := bstep (se 1 (by rfl) ⟨2882705, by rfl⟩ : syracuseStep 3843607 = 5765411) B5765411
theorem B2434619 : Blo 798342 2434619 := bstep (se 1 (by rfl) ⟨1825964, by rfl⟩ : syracuseStep 2434619 = 3651929) B3651929
theorem B8660657 : Blo 798342 8660657 := bstep (se 2 (by rfl) ⟨3247746, by rfl⟩ : syracuseStep 8660657 = 6495493) B6495493
theorem B2696975 : Blo 798342 2696975 := bstep (se 1 (by rfl) ⟨2022731, by rfl⟩ : syracuseStep 2696975 = 4045463) B4045463
theorem B3417871 : Blo 798342 3417871 := bstep (se 1 (by rfl) ⟨2563403, by rfl⟩ : syracuseStep 3417871 = 5126807) B5126807
theorem B960503 : Blo 798342 960503 := bstep (se 1 (by rfl) ⟨720377, by rfl⟩ : syracuseStep 960503 = 1440755) B1440755
theorem B2697245 : Blo 798342 2697245 := bstep (se 3 (by rfl) ⟨505733, by rfl⟩ : syracuseStep 2697245 = 1011467) B1011467
theorem B2369569 : Blo 798342 2369569 := bstep (se 2 (by rfl) ⟨888588, by rfl⟩ : syracuseStep 2369569 = 1777177) B1777177
theorem B1517611 : Blo 798342 1517611 := bstep (se 1 (by rfl) ⟨1138208, by rfl⟩ : syracuseStep 1517611 = 2276417) B2276417
theorem B9119789 : Blo 798342 9119789 := bstep (se 3 (by rfl) ⟨1709960, by rfl⟩ : syracuseStep 9119789 = 3419921) B3419921
theorem B1517687 : Blo 798342 1517687 := bstep (se 1 (by rfl) ⟨1138265, by rfl⟩ : syracuseStep 1517687 = 2276531) B2276531
theorem B1353847 : Blo 798342 1353847 := bstep (se 1 (by rfl) ⟨1015385, by rfl⟩ : syracuseStep 1353847 = 2030771) B2030771
theorem B4565591 : Blo 798342 4565591 := bstep (se 1 (by rfl) ⟨3424193, by rfl⟩ : syracuseStep 4565591 = 6848387) B6848387
theorem B5188441 : Blo 798342 5188441 := bstep (se 2 (by rfl) ⟨1945665, by rfl⟩ : syracuseStep 5188441 = 3891331) B3891331
theorem B3648827 : Blo 798342 3648827 := bstep (se 1 (by rfl) ⟨2736620, by rfl⟩ : syracuseStep 3648827 = 5473241) B5473241
theorem B2698649 : Blo 798342 2698649 := bstep (se 2 (by rfl) ⟨1011993, by rfl⟩ : syracuseStep 2698649 = 2023987) B2023987
theorem B2305655 : Blo 798342 2305655 := bstep (se 1 (by rfl) ⟨1729241, by rfl⟩ : syracuseStep 2305655 = 3458483) B3458483
theorem B798343 : Blo 798342 798343 := bstep (se 1 (by rfl) ⟨598757, by rfl⟩ : syracuseStep 798343 = 1197515) B1197515
theorem B798351 : Blo 798342 798351 := bstep (se 1 (by rfl) ⟨598763, by rfl⟩ : syracuseStep 798351 = 1197527) B1197527
theorem B798395 : Blo 798342 798395 := bstep (se 1 (by rfl) ⟨598796, by rfl⟩ : syracuseStep 798395 = 1197593) B1197593
theorem B798471 : Blo 798342 798471 := bstep (se 1 (by rfl) ⟨598853, by rfl⟩ : syracuseStep 798471 = 1197707) B1197707
theorem B798479 : Blo 798342 798479 := bstep (se 1 (by rfl) ⟨598859, by rfl⟩ : syracuseStep 798479 = 1197719) B1197719
theorem B4042547 : Blo 798342 4042547 := bstep (se 1 (by rfl) ⟨3031910, by rfl⟩ : syracuseStep 4042547 = 6063821) B6063821
theorem B798523 : Blo 798342 798523 := bstep (se 1 (by rfl) ⟨598892, by rfl⟩ : syracuseStep 798523 = 1197785) B1197785
theorem B2436979 : Blo 798342 2436979 := bstep (se 1 (by rfl) ⟨1827734, by rfl⟩ : syracuseStep 2436979 = 3655469) B3655469
theorem B798599 : Blo 798342 798599 := bstep (se 1 (by rfl) ⟨598949, by rfl⟩ : syracuseStep 798599 = 1197899) B1197899
theorem B798607 : Blo 798342 798607 := bstep (se 1 (by rfl) ⟨598955, by rfl⟩ : syracuseStep 798607 = 1197911) B1197911
theorem B798651 : Blo 798342 798651 := bstep (se 1 (by rfl) ⟨598988, by rfl⟩ : syracuseStep 798651 = 1197977) B1197977
theorem B798727 : Blo 798342 798727 := bstep (se 1 (by rfl) ⟨599045, by rfl⟩ : syracuseStep 798727 = 1198091) B1198091
theorem B798735 : Blo 798342 798735 := bstep (se 1 (by rfl) ⟨599051, by rfl⟩ : syracuseStep 798735 = 1198103) B1198103
theorem B1519631 : Blo 798342 1519631 := bstep (se 1 (by rfl) ⟨1139723, by rfl⟩ : syracuseStep 1519631 = 2279447) B2279447
theorem B798779 : Blo 798342 798779 := bstep (se 1 (by rfl) ⟨599084, by rfl⟩ : syracuseStep 798779 = 1198169) B1198169
theorem B2699351 : Blo 798342 2699351 := bstep (se 1 (by rfl) ⟨2024513, by rfl⟩ : syracuseStep 2699351 = 4049027) B4049027
theorem B4042871 : Blo 798342 4042871 := bstep (se 1 (by rfl) ⟨3032153, by rfl⟩ : syracuseStep 4042871 = 6064307) B6064307
theorem B798855 : Blo 798342 798855 := bstep (se 1 (by rfl) ⟨599141, by rfl⟩ : syracuseStep 798855 = 1198283) B1198283
theorem B798863 : Blo 798342 798863 := bstep (se 1 (by rfl) ⟨599147, by rfl⟩ : syracuseStep 798863 = 1198295) B1198295
theorem B798907 : Blo 798342 798907 := bstep (se 1 (by rfl) ⟨599180, by rfl⟩ : syracuseStep 798907 = 1198361) B1198361
theorem B798983 : Blo 798342 798983 := bstep (se 1 (by rfl) ⟨599237, by rfl⟩ : syracuseStep 798983 = 1198475) B1198475
theorem B798991 : Blo 798342 798991 := bstep (se 1 (by rfl) ⟨599243, by rfl⟩ : syracuseStep 798991 = 1198487) B1198487
theorem B799035 : Blo 798342 799035 := bstep (se 1 (by rfl) ⟨599276, by rfl⟩ : syracuseStep 799035 = 1198553) B1198553
theorem B799111 : Blo 798342 799111 := bstep (se 1 (by rfl) ⟨599333, by rfl⟩ : syracuseStep 799111 = 1198667) B1198667
theorem B799119 : Blo 798342 799119 := bstep (se 1 (by rfl) ⟨599339, by rfl⟩ : syracuseStep 799119 = 1198679) B1198679
theorem B2273683 : Blo 798342 2273683 := bstep (se 1 (by rfl) ⟨1705262, by rfl⟩ : syracuseStep 2273683 = 3410525) B3410525
theorem B799163 : Blo 798342 799163 := bstep (se 1 (by rfl) ⟨599372, by rfl⟩ : syracuseStep 799163 = 1198745) B1198745
theorem B799239 : Blo 798342 799239 := bstep (se 1 (by rfl) ⟨599429, by rfl⟩ : syracuseStep 799239 = 1198859) B1198859
theorem B799247 : Blo 798342 799247 := bstep (se 1 (by rfl) ⟨599435, by rfl⟩ : syracuseStep 799247 = 1198871) B1198871
theorem B15381035 : Blo 798342 15381035 := bstep (se 1 (by rfl) ⟨11535776, by rfl⟩ : syracuseStep 15381035 = 23071553) B23071553
theorem B799291 : Blo 798342 799291 := bstep (se 1 (by rfl) ⟨599468, by rfl⟩ : syracuseStep 799291 = 1198937) B1198937
theorem B2699837 : Blo 798342 2699837 := bstep (se 3 (by rfl) ⟨506219, by rfl⟩ : syracuseStep 2699837 = 1012439) B1012439
theorem B6074999 : Blo 798342 6074999 := bstep (se 1 (by rfl) ⟨4556249, by rfl⟩ : syracuseStep 6074999 = 9112499) B9112499
theorem B799367 : Blo 798342 799367 := bstep (se 1 (by rfl) ⟨599525, by rfl⟩ : syracuseStep 799367 = 1199051) B1199051
theorem B799375 : Blo 798342 799375 := bstep (se 1 (by rfl) ⟨599531, by rfl⟩ : syracuseStep 799375 = 1199063) B1199063
theorem B799419 : Blo 798342 799419 := bstep (se 1 (by rfl) ⟨599564, by rfl⟩ : syracuseStep 799419 = 1199129) B1199129
theorem B3650285 : Blo 798342 3650285 := bstep (se 3 (by rfl) ⟨684428, by rfl⟩ : syracuseStep 3650285 = 1368857) B1368857
theorem B1946369 : Blo 798342 1946369 := bstep (se 2 (by rfl) ⟨729888, by rfl⟩ : syracuseStep 1946369 = 1459777) B1459777
theorem B799495 : Blo 798342 799495 := bstep (se 1 (by rfl) ⟨599621, by rfl⟩ : syracuseStep 799495 = 1199243) B1199243
theorem B799503 : Blo 798342 799503 := bstep (se 1 (by rfl) ⟨599627, by rfl⟩ : syracuseStep 799503 = 1199255) B1199255
theorem B4567823 : Blo 798342 4567823 := bstep (se 1 (by rfl) ⟨3425867, by rfl⟩ : syracuseStep 4567823 = 6851735) B6851735
theorem B799547 : Blo 798342 799547 := bstep (se 1 (by rfl) ⟨599660, by rfl⟩ : syracuseStep 799547 = 1199321) B1199321
theorem B799623 : Blo 798342 799623 := bstep (se 1 (by rfl) ⟨599717, by rfl⟩ : syracuseStep 799623 = 1199435) B1199435
theorem B799631 : Blo 798342 799631 := bstep (se 1 (by rfl) ⟨599723, by rfl⟩ : syracuseStep 799631 = 1199447) B1199447
theorem B799675 : Blo 798342 799675 := bstep (se 1 (by rfl) ⟨599756, by rfl⟩ : syracuseStep 799675 = 1199513) B1199513
theorem B799751 : Blo 798342 799751 := bstep (se 1 (by rfl) ⟨599813, by rfl⟩ : syracuseStep 799751 = 1199627) B1199627
theorem B4568075 : Blo 798342 4568075 := bstep (se 1 (by rfl) ⟨3426056, by rfl⟩ : syracuseStep 4568075 = 6852113) B6852113
theorem B799759 : Blo 798342 799759 := bstep (se 1 (by rfl) ⟨599819, by rfl⟩ : syracuseStep 799759 = 1199639) B1199639
theorem B799803 : Blo 798342 799803 := bstep (se 1 (by rfl) ⟨599852, by rfl⟩ : syracuseStep 799803 = 1199705) B1199705
theorem B13874237 : Blo 798342 13874237 := bstep (se 3 (by rfl) ⟨2601419, by rfl⟩ : syracuseStep 13874237 = 5202839) B5202839
theorem B4043843 : Blo 798342 4043843 := bstep (se 1 (by rfl) ⟨3032882, by rfl⟩ : syracuseStep 4043843 = 6065765) B6065765
theorem B799879 : Blo 798342 799879 := bstep (se 1 (by rfl) ⟨599909, by rfl⟩ : syracuseStep 799879 = 1199819) B1199819
theorem B799887 : Blo 798342 799887 := bstep (se 1 (by rfl) ⟨599915, by rfl⟩ : syracuseStep 799887 = 1199831) B1199831
theorem B799931 : Blo 798342 799931 := bstep (se 1 (by rfl) ⟨599948, by rfl⟩ : syracuseStep 799931 = 1199897) B1199897
theorem B800007 : Blo 798342 800007 := bstep (se 1 (by rfl) ⟨600005, by rfl⟩ : syracuseStep 800007 = 1200011) B1200011
theorem B2274571 : Blo 798342 2274571 := bstep (se 1 (by rfl) ⟨1705928, by rfl⟩ : syracuseStep 2274571 = 3411857) B3411857
theorem B800015 : Blo 798342 800015 := bstep (se 1 (by rfl) ⟨600011, by rfl⟩ : syracuseStep 800015 = 1200023) B1200023
theorem B800059 : Blo 798342 800059 := bstep (se 1 (by rfl) ⟨600044, by rfl⟩ : syracuseStep 800059 = 1200089) B1200089
theorem B4044167 : Blo 798342 4044167 := bstep (se 1 (by rfl) ⟨3033125, by rfl⟩ : syracuseStep 4044167 = 6066251) B6066251
theorem B800135 : Blo 798342 800135 := bstep (se 1 (by rfl) ⟨600101, by rfl⟩ : syracuseStep 800135 = 1200203) B1200203
theorem B2569607 : Blo 798342 2569607 := bstep (se 1 (by rfl) ⟨1927205, by rfl⟩ : syracuseStep 2569607 = 3854411) B3854411
theorem B898447 : Blo 798342 898447 := bstep (se 1 (by rfl) ⟨673835, by rfl⟩ : syracuseStep 898447 = 1347671) B1347671
theorem B800143 : Blo 798342 800143 := bstep (se 1 (by rfl) ⟨600107, by rfl⟩ : syracuseStep 800143 = 1200215) B1200215
theorem B2569657 : Blo 798342 2569657 := bstep (se 2 (by rfl) ⟨963621, by rfl⟩ : syracuseStep 2569657 = 1927243) B1927243
theorem B800187 : Blo 798342 800187 := bstep (se 1 (by rfl) ⟨600140, by rfl⟩ : syracuseStep 800187 = 1200281) B1200281
theorem B4109777 : Blo 798342 4109777 := bstep (se 2 (by rfl) ⟨1541166, by rfl⟩ : syracuseStep 4109777 = 3082333) B3082333
theorem B800263 : Blo 798342 800263 := bstep (se 1 (by rfl) ⟨600197, by rfl⟩ : syracuseStep 800263 = 1200395) B1200395
theorem B800271 : Blo 798342 800271 := bstep (se 1 (by rfl) ⟨600203, by rfl⟩ : syracuseStep 800271 = 1200407) B1200407
theorem B800315 : Blo 798342 800315 := bstep (se 1 (by rfl) ⟨600236, by rfl⟩ : syracuseStep 800315 = 1200473) B1200473
theorem B6075971 : Blo 798342 6075971 := bstep (se 1 (by rfl) ⟨4556978, by rfl⟩ : syracuseStep 6075971 = 9113957) B9113957
theorem B1521271 : Blo 798342 1521271 := bstep (se 1 (by rfl) ⟨1140953, by rfl⟩ : syracuseStep 1521271 = 2281907) B2281907
theorem B800391 : Blo 798342 800391 := bstep (se 1 (by rfl) ⟨600293, by rfl⟩ : syracuseStep 800391 = 1200587) B1200587
theorem B800399 : Blo 798342 800399 := bstep (se 1 (by rfl) ⟨600299, by rfl⟩ : syracuseStep 800399 = 1200599) B1200599
theorem B800443 : Blo 798342 800443 := bstep (se 1 (by rfl) ⟨600332, by rfl⟩ : syracuseStep 800443 = 1200665) B1200665
theorem B2275073 : Blo 798342 2275073 := bstep (se 2 (by rfl) ⟨853152, by rfl⟩ : syracuseStep 2275073 = 1706305) B1706305
theorem B800519 : Blo 798342 800519 := bstep (se 1 (by rfl) ⟨600389, by rfl⟩ : syracuseStep 800519 = 1200779) B1200779
theorem B800527 : Blo 798342 800527 := bstep (se 1 (by rfl) ⟨600395, by rfl⟩ : syracuseStep 800527 = 1200791) B1200791
theorem B800571 : Blo 798342 800571 := bstep (se 1 (by rfl) ⟨600428, by rfl⟩ : syracuseStep 800571 = 1200857) B1200857
theorem B898951 : Blo 798342 898951 := bstep (se 1 (by rfl) ⟨674213, by rfl⟩ : syracuseStep 898951 = 1348427) B1348427
theorem B800647 : Blo 798342 800647 := bstep (se 1 (by rfl) ⟨600485, by rfl⟩ : syracuseStep 800647 = 1200971) B1200971
theorem B800655 : Blo 798342 800655 := bstep (se 1 (by rfl) ⟨600491, by rfl⟩ : syracuseStep 800655 = 1200983) B1200983
theorem B2701241 : Blo 798342 2701241 := bstep (se 2 (by rfl) ⟨1012965, by rfl⟩ : syracuseStep 2701241 = 2025931) B2025931
theorem B800699 : Blo 798342 800699 := bstep (se 1 (by rfl) ⟨600524, by rfl⟩ : syracuseStep 800699 = 1201049) B1201049
theorem B800775 : Blo 798342 800775 := bstep (se 1 (by rfl) ⟨600581, by rfl⟩ : syracuseStep 800775 = 1201163) B1201163
theorem B800783 : Blo 798342 800783 := bstep (se 1 (by rfl) ⟨600587, by rfl⟩ : syracuseStep 800783 = 1201175) B1201175
theorem B899131 : Blo 798342 899131 := bstep (se 1 (by rfl) ⟨674348, by rfl⟩ : syracuseStep 899131 = 1348697) B1348697
theorem B800827 : Blo 798342 800827 := bstep (se 1 (by rfl) ⟨600620, by rfl⟩ : syracuseStep 800827 = 1201241) B1201241
theorem B2275415 : Blo 798342 2275415 := bstep (se 1 (by rfl) ⟨1706561, by rfl⟩ : syracuseStep 2275415 = 3413123) B3413123
theorem B800903 : Blo 798342 800903 := bstep (se 1 (by rfl) ⟨600677, by rfl⟩ : syracuseStep 800903 = 1201355) B1201355
theorem B800911 : Blo 798342 800911 := bstep (se 1 (by rfl) ⟨600683, by rfl⟩ : syracuseStep 800911 = 1201367) B1201367
theorem B800955 : Blo 798342 800955 := bstep (se 1 (by rfl) ⟨600716, by rfl⟩ : syracuseStep 800955 = 1201433) B1201433
theorem B4569281 : Blo 798342 4569281 := bstep (se 2 (by rfl) ⟨1713480, by rfl⟩ : syracuseStep 4569281 = 3426961) B3426961
theorem B8665289 : Blo 798342 8665289 := bstep (se 2 (by rfl) ⟨3249483, by rfl⟩ : syracuseStep 8665289 = 6498967) B6498967
theorem B801031 : Blo 798342 801031 := bstep (se 1 (by rfl) ⟨600773, by rfl⟩ : syracuseStep 801031 = 1201547) B1201547
theorem B801039 : Blo 798342 801039 := bstep (se 1 (by rfl) ⟨600779, by rfl⟩ : syracuseStep 801039 = 1201559) B1201559
theorem B801083 : Blo 798342 801083 := bstep (se 1 (by rfl) ⟨600812, by rfl⟩ : syracuseStep 801083 = 1201625) B1201625
theorem B801159 : Blo 798342 801159 := bstep (se 1 (by rfl) ⟨600869, by rfl⟩ : syracuseStep 801159 = 1201739) B1201739
theorem B801167 : Blo 798342 801167 := bstep (se 1 (by rfl) ⟨600875, by rfl⟩ : syracuseStep 801167 = 1201751) B1201751
theorem B1620371 : Blo 798342 1620371 := bstep (se 1 (by rfl) ⟨1215278, by rfl⟩ : syracuseStep 1620371 = 2430557) B2430557
theorem B801211 : Blo 798342 801211 := bstep (se 1 (by rfl) ⟨600908, by rfl⟩ : syracuseStep 801211 = 1201817) B1201817
theorem B801287 : Blo 798342 801287 := bstep (se 1 (by rfl) ⟨600965, by rfl⟩ : syracuseStep 801287 = 1201931) B1201931
theorem B2701835 : Blo 798342 2701835 := bstep (se 1 (by rfl) ⟨2026376, by rfl⟩ : syracuseStep 2701835 = 4052753) B4052753
theorem B899599 : Blo 798342 899599 := bstep (se 1 (by rfl) ⟨674699, by rfl⟩ : syracuseStep 899599 = 1349399) B1349399
theorem B801295 : Blo 798342 801295 := bstep (se 1 (by rfl) ⟨600971, by rfl⟩ : syracuseStep 801295 = 1201943) B1201943
theorem B801339 : Blo 798342 801339 := bstep (se 1 (by rfl) ⟨601004, by rfl⟩ : syracuseStep 801339 = 1202009) B1202009
theorem B2701943 : Blo 798342 2701943 := bstep (se 1 (by rfl) ⟨2026457, by rfl⟩ : syracuseStep 2701943 = 4052915) B4052915
theorem B801415 : Blo 798342 801415 := bstep (se 1 (by rfl) ⟨601061, by rfl⟩ : syracuseStep 801415 = 1202123) B1202123
theorem B801423 : Blo 798342 801423 := bstep (se 1 (by rfl) ⟨601067, by rfl⟩ : syracuseStep 801423 = 1202135) B1202135
theorem B801467 : Blo 798342 801467 := bstep (se 1 (by rfl) ⟨601100, by rfl⟩ : syracuseStep 801467 = 1202201) B1202201
theorem B801543 : Blo 798342 801543 := bstep (se 1 (by rfl) ⟨601157, by rfl⟩ : syracuseStep 801543 = 1202315) B1202315
theorem B801551 : Blo 798342 801551 := bstep (se 1 (by rfl) ⟨601163, by rfl⟩ : syracuseStep 801551 = 1202327) B1202327
theorem B801595 : Blo 798342 801595 := bstep (se 1 (by rfl) ⟨601196, by rfl⟩ : syracuseStep 801595 = 1202393) B1202393
theorem B801671 : Blo 798342 801671 := bstep (se 1 (by rfl) ⟨601253, by rfl⟩ : syracuseStep 801671 = 1202507) B1202507
theorem B801679 : Blo 798342 801679 := bstep (se 1 (by rfl) ⟨601259, by rfl⟩ : syracuseStep 801679 = 1202519) B1202519
theorem B32783267 : Blo 798342 32783267 := bstep (se 1 (by rfl) ⟨24587450, by rfl⟩ : syracuseStep 32783267 = 49174901) B49174901
theorem B801723 : Blo 798342 801723 := bstep (se 1 (by rfl) ⟨601292, by rfl⟩ : syracuseStep 801723 = 1202585) B1202585
theorem B900103 : Blo 798342 900103 := bstep (se 1 (by rfl) ⟨675077, by rfl⟩ : syracuseStep 900103 = 1350155) B1350155
theorem B801799 : Blo 798342 801799 := bstep (se 1 (by rfl) ⟨601349, by rfl⟩ : syracuseStep 801799 = 1202699) B1202699
theorem B3652619 : Blo 798342 3652619 := bstep (se 1 (by rfl) ⟨2739464, by rfl⟩ : syracuseStep 3652619 = 5478929) B5478929
theorem B801807 : Blo 798342 801807 := bstep (se 1 (by rfl) ⟨601355, by rfl⟩ : syracuseStep 801807 = 1202711) B1202711
theorem B801851 : Blo 798342 801851 := bstep (se 1 (by rfl) ⟨601388, by rfl⟩ : syracuseStep 801851 = 1202777) B1202777
theorem B801927 : Blo 798342 801927 := bstep (se 1 (by rfl) ⟨601445, by rfl⟩ : syracuseStep 801927 = 1202891) B1202891
theorem B801935 : Blo 798342 801935 := bstep (se 1 (by rfl) ⟨601451, by rfl⟩ : syracuseStep 801935 = 1202903) B1202903
theorem B900283 : Blo 798342 900283 := bstep (se 1 (by rfl) ⟨675212, by rfl⟩ : syracuseStep 900283 = 1350425) B1350425
theorem B801979 : Blo 798342 801979 := bstep (se 1 (by rfl) ⟨601484, by rfl⟩ : syracuseStep 801979 = 1202969) B1202969
theorem B2702537 : Blo 798342 2702537 := bstep (se 2 (by rfl) ⟨1013451, by rfl⟩ : syracuseStep 2702537 = 2026903) B2026903
theorem B802055 : Blo 798342 802055 := bstep (se 1 (by rfl) ⟨601541, by rfl⟩ : syracuseStep 802055 = 1203083) B1203083
theorem B802063 : Blo 798342 802063 := bstep (se 1 (by rfl) ⟨601547, by rfl⟩ : syracuseStep 802063 = 1203095) B1203095
theorem B802107 : Blo 798342 802107 := bstep (se 1 (by rfl) ⟨601580, by rfl⟩ : syracuseStep 802107 = 1203161) B1203161
theorem B1523063 : Blo 798342 1523063 := bstep (se 1 (by rfl) ⟨1142297, by rfl⟩ : syracuseStep 1523063 = 2284595) B2284595
theorem B802183 : Blo 798342 802183 := bstep (se 1 (by rfl) ⟨601637, by rfl⟩ : syracuseStep 802183 = 1203275) B1203275
theorem B802191 : Blo 798342 802191 := bstep (se 1 (by rfl) ⟨601643, by rfl⟩ : syracuseStep 802191 = 1203287) B1203287
theorem B802235 : Blo 798342 802235 := bstep (se 1 (by rfl) ⟨601676, by rfl⟩ : syracuseStep 802235 = 1203353) B1203353
theorem B802311 : Blo 798342 802311 := bstep (se 1 (by rfl) ⟨601733, by rfl⟩ : syracuseStep 802311 = 1203467) B1203467
theorem B802319 : Blo 798342 802319 := bstep (se 1 (by rfl) ⟨601739, by rfl⟩ : syracuseStep 802319 = 1203479) B1203479
theorem B3653207 : Blo 798342 3653207 := bstep (se 1 (by rfl) ⟨2739905, by rfl⟩ : syracuseStep 3653207 = 5479811) B5479811
theorem B900751 : Blo 798342 900751 := bstep (se 1 (by rfl) ⟨675563, by rfl⟩ : syracuseStep 900751 = 1351127) B1351127
theorem B5783345 : Blo 798342 5783345 := bstep (se 2 (by rfl) ⟨2168754, by rfl⟩ : syracuseStep 5783345 = 4337509) B4337509
theorem B11550539 : Blo 798342 11550539 := bstep (se 1 (by rfl) ⟨8662904, by rfl⟩ : syracuseStep 11550539 = 17325809) B17325809
theorem B2703239 : Blo 798342 2703239 := bstep (se 1 (by rfl) ⟨2027429, by rfl⟩ : syracuseStep 2703239 = 4054859) B4054859
theorem B2277305 : Blo 798342 2277305 := bstep (se 2 (by rfl) ⟨853989, by rfl⟩ : syracuseStep 2277305 = 1707979) B1707979
theorem B901255 : Blo 798342 901255 := bstep (se 1 (by rfl) ⟨675941, by rfl⟩ : syracuseStep 901255 = 1351883) B1351883
theorem B9257161 : Blo 798342 9257161 := bstep (se 2 (by rfl) ⟨3471435, by rfl⟩ : syracuseStep 9257161 = 6942871) B6942871
theorem B2703617 : Blo 798342 2703617 := bstep (se 2 (by rfl) ⟨1013856, by rfl⟩ : syracuseStep 2703617 = 2027713) B2027713
theorem B3948851 : Blo 798342 3948851 := bstep (se 1 (by rfl) ⟨2961638, by rfl⟩ : syracuseStep 3948851 = 5923277) B5923277
theorem B901435 : Blo 798342 901435 := bstep (se 1 (by rfl) ⟨676076, by rfl⟩ : syracuseStep 901435 = 1352153) B1352153
theorem B8667749 : Blo 798342 8667749 := bstep (se 4 (by rfl) ⟨812601, by rfl⟩ : syracuseStep 8667749 = 1625203) B1625203
theorem B2048647 : Blo 798342 2048647 := bstep (se 1 (by rfl) ⟨1536485, by rfl⟩ : syracuseStep 2048647 = 3072971) B3072971
theorem B3031789 : Blo 798342 3031789 := bstep (se 3 (by rfl) ⟨568460, by rfl⟩ : syracuseStep 3031789 = 1136921) B1136921
theorem B901903 : Blo 798342 901903 := bstep (se 1 (by rfl) ⟨676427, by rfl⟩ : syracuseStep 901903 = 1352855) B1352855
theorem B14598947 : Blo 798342 14598947 := bstep (se 1 (by rfl) ⟨10949210, by rfl⟩ : syracuseStep 14598947 = 21898421) B21898421
theorem B8209201 : Blo 798342 8209201 := bstep (se 2 (by rfl) ⟨3078450, by rfl⟩ : syracuseStep 8209201 = 6156901) B6156901
theorem B4047731 : Blo 798342 4047731 := bstep (se 1 (by rfl) ⟨3035798, by rfl⟩ : syracuseStep 4047731 = 6071597) B6071597
theorem B3032093 : Blo 798342 3032093 := bstep (se 3 (by rfl) ⟨568517, by rfl⟩ : syracuseStep 3032093 = 1137035) B1137035
theorem B2704427 : Blo 798342 2704427 := bstep (se 1 (by rfl) ⟨2028320, by rfl⟩ : syracuseStep 2704427 = 4056641) B4056641
theorem B902407 : Blo 798342 902407 := bstep (se 1 (by rfl) ⟨676805, by rfl⟩ : syracuseStep 902407 = 1353611) B1353611
theorem B4048217 : Blo 798342 4048217 := bstep (se 2 (by rfl) ⟨1518081, by rfl⟩ : syracuseStep 4048217 = 3036163) B3036163
theorem B6833555 : Blo 798342 6833555 := bstep (se 1 (by rfl) ⟨5125166, by rfl⟩ : syracuseStep 6833555 = 10250333) B10250333
theorem B902587 : Blo 798342 902587 := bstep (se 1 (by rfl) ⟨676940, by rfl⟩ : syracuseStep 902587 = 1353881) B1353881
theorem B7685597 : Blo 798342 7685597 := bstep (se 3 (by rfl) ⟨1441049, by rfl⟩ : syracuseStep 7685597 = 2882099) B2882099
theorem B1197575 : Blo 798342 1197575 := bstep (se 1 (by rfl) ⟨898181, by rfl⟩ : syracuseStep 1197575 = 1796363) B1796363
theorem B2278945 : Blo 798342 2278945 := bstep (se 2 (by rfl) ⟨854604, by rfl⟩ : syracuseStep 2278945 = 1709209) B1709209
theorem B1197611 : Blo 798342 1197611 := bstep (se 1 (by rfl) ⟨898208, by rfl⟩ : syracuseStep 1197611 = 1796417) B1796417
theorem B1197641 : Blo 798342 1197641 := bstep (se 2 (by rfl) ⟨449115, by rfl⟩ : syracuseStep 1197641 = 898231) B898231
theorem B1197755 : Blo 798342 1197755 := bstep (se 1 (by rfl) ⟨898316, by rfl⟩ : syracuseStep 1197755 = 1796633) B1796633
theorem B1197815 : Blo 798342 1197815 := bstep (se 1 (by rfl) ⟨898361, by rfl⟩ : syracuseStep 1197815 = 1796723) B1796723
theorem B1197839 : Blo 798342 1197839 := bstep (se 1 (by rfl) ⟨898379, by rfl⟩ : syracuseStep 1197839 = 1796759) B1796759
theorem B1197881 : Blo 798342 1197881 := bstep (se 2 (by rfl) ⟨449205, by rfl⟩ : syracuseStep 1197881 = 898411) B898411
theorem B6080345 : Blo 798342 6080345 := bstep (se 2 (by rfl) ⟨2280129, by rfl⟩ : syracuseStep 6080345 = 4560259) B4560259
theorem B1197959 : Blo 798342 1197959 := bstep (se 1 (by rfl) ⟨898469, by rfl⟩ : syracuseStep 1197959 = 1796939) B1796939
theorem B1197995 : Blo 798342 1197995 := bstep (se 1 (by rfl) ⟨898496, by rfl⟩ : syracuseStep 1197995 = 1796993) B1796993
theorem B1198025 : Blo 798342 1198025 := bstep (se 2 (by rfl) ⟨449259, by rfl⟩ : syracuseStep 1198025 = 898519) B898519
theorem B1198139 : Blo 798342 1198139 := bstep (se 1 (by rfl) ⟨898604, by rfl⟩ : syracuseStep 1198139 = 1797209) B1797209
theorem B1198199 : Blo 798342 1198199 := bstep (se 1 (by rfl) ⟨898649, by rfl⟩ : syracuseStep 1198199 = 1797299) B1797299
theorem B1198223 : Blo 798342 1198223 := bstep (se 1 (by rfl) ⟨898667, by rfl⟩ : syracuseStep 1198223 = 1797335) B1797335
theorem B1919161 : Blo 798342 1919161 := bstep (se 2 (by rfl) ⟨719685, by rfl⟩ : syracuseStep 1919161 = 1439371) B1439371
theorem B1198265 : Blo 798342 1198265 := bstep (se 2 (by rfl) ⟨449349, by rfl⟩ : syracuseStep 1198265 = 898699) B898699
theorem B12503285 : Blo 798342 12503285 := bstep (se 5 (by rfl) ⟨586091, by rfl⟩ : syracuseStep 12503285 = 1172183) B1172183
theorem B1198343 : Blo 798342 1198343 := bstep (se 1 (by rfl) ⟨898757, by rfl⟩ : syracuseStep 1198343 = 1797515) B1797515
theorem B8636705 : Blo 798342 8636705 := bstep (se 2 (by rfl) ⟨3238764, by rfl⟩ : syracuseStep 8636705 = 6477529) B6477529
theorem B1198379 : Blo 798342 1198379 := bstep (se 1 (by rfl) ⟨898784, by rfl⟩ : syracuseStep 1198379 = 1797569) B1797569
theorem B2705723 : Blo 798342 2705723 := bstep (se 1 (by rfl) ⟨2029292, by rfl⟩ : syracuseStep 2705723 = 4058585) B4058585
theorem B3426619 : Blo 798342 3426619 := bstep (se 1 (by rfl) ⟨2569964, by rfl⟩ : syracuseStep 3426619 = 5139929) B5139929
theorem B1198409 : Blo 798342 1198409 := bstep (se 2 (by rfl) ⟨449403, by rfl⟩ : syracuseStep 1198409 = 898807) B898807
theorem B6834617 : Blo 798342 6834617 := bstep (se 2 (by rfl) ⟨2562981, by rfl⟩ : syracuseStep 6834617 = 5125963) B5125963
theorem B1198523 : Blo 798342 1198523 := bstep (se 1 (by rfl) ⟨898892, by rfl⟩ : syracuseStep 1198523 = 1797785) B1797785
theorem B1198583 : Blo 798342 1198583 := bstep (se 1 (by rfl) ⟨898937, by rfl⟩ : syracuseStep 1198583 = 1797875) B1797875
theorem B1198607 : Blo 798342 1198607 := bstep (se 1 (by rfl) ⟨898955, by rfl⟩ : syracuseStep 1198607 = 1797911) B1797911
theorem B1198649 : Blo 798342 1198649 := bstep (se 2 (by rfl) ⟨449493, by rfl⟩ : syracuseStep 1198649 = 898987) B898987
theorem B3033719 : Blo 798342 3033719 := bstep (se 1 (by rfl) ⟨2275289, by rfl⟩ : syracuseStep 3033719 = 4550579) B4550579
theorem B1198727 : Blo 798342 1198727 := bstep (se 1 (by rfl) ⟨899045, by rfl⟩ : syracuseStep 1198727 = 1798091) B1798091
theorem B1198763 : Blo 798342 1198763 := bstep (se 1 (by rfl) ⟨899072, by rfl⟩ : syracuseStep 1198763 = 1798145) B1798145
theorem B1198793 : Blo 798342 1198793 := bstep (se 2 (by rfl) ⟨449547, by rfl⟩ : syracuseStep 1198793 = 899095) B899095
theorem B2280221 : Blo 798342 2280221 := bstep (se 3 (by rfl) ⟨427541, by rfl⟩ : syracuseStep 2280221 = 855083) B855083
theorem B2706209 : Blo 798342 2706209 := bstep (se 2 (by rfl) ⟨1014828, by rfl⟩ : syracuseStep 2706209 = 2029657) B2029657
theorem B6081317 : Blo 798342 6081317 := bstep (se 4 (by rfl) ⟨570123, by rfl⟩ : syracuseStep 6081317 = 1140247) B1140247
theorem B1198907 : Blo 798342 1198907 := bstep (se 1 (by rfl) ⟨899180, by rfl⟩ : syracuseStep 1198907 = 1798361) B1798361
theorem B1198967 : Blo 798342 1198967 := bstep (se 1 (by rfl) ⟨899225, by rfl⟩ : syracuseStep 1198967 = 1798451) B1798451
theorem B1198991 : Blo 798342 1198991 := bstep (se 1 (by rfl) ⟨899243, by rfl⟩ : syracuseStep 1198991 = 1798487) B1798487
theorem B17288099 : Blo 798342 17288099 := bstep (se 1 (by rfl) ⟨12966074, by rfl⟩ : syracuseStep 17288099 = 25932149) B25932149
theorem B1199033 : Blo 798342 1199033 := bstep (se 2 (by rfl) ⟨449637, by rfl⟩ : syracuseStep 1199033 = 899275) B899275
theorem B2280449 : Blo 798342 2280449 := bstep (se 2 (by rfl) ⟨855168, by rfl⟩ : syracuseStep 2280449 = 1710337) B1710337
theorem B1199111 : Blo 798342 1199111 := bstep (se 1 (by rfl) ⟨899333, by rfl⟩ : syracuseStep 1199111 = 1798667) B1798667
theorem B1199147 : Blo 798342 1199147 := bstep (se 1 (by rfl) ⟨899360, by rfl⟩ : syracuseStep 1199147 = 1798721) B1798721
theorem B1199177 : Blo 798342 1199177 := bstep (se 2 (by rfl) ⟨449691, by rfl⟩ : syracuseStep 1199177 = 899383) B899383
theorem B1199291 : Blo 798342 1199291 := bstep (se 1 (by rfl) ⟨899468, by rfl⟩ : syracuseStep 1199291 = 1798937) B1798937
theorem B1199351 : Blo 798342 1199351 := bstep (se 1 (by rfl) ⟨899513, by rfl⟩ : syracuseStep 1199351 = 1799027) B1799027
theorem B1199375 : Blo 798342 1199375 := bstep (se 1 (by rfl) ⟨899531, by rfl⟩ : syracuseStep 1199375 = 1799063) B1799063
theorem B10243361 : Blo 798342 10243361 := bstep (se 2 (by rfl) ⟨3841260, by rfl⟩ : syracuseStep 10243361 = 7682521) B7682521
theorem B1199417 : Blo 798342 1199417 := bstep (se 2 (by rfl) ⟨449781, by rfl⟩ : syracuseStep 1199417 = 899563) B899563
theorem B2280791 : Blo 798342 2280791 := bstep (se 1 (by rfl) ⟨1710593, by rfl⟩ : syracuseStep 2280791 = 3421187) B3421187
theorem B2706803 : Blo 798342 2706803 := bstep (se 1 (by rfl) ⟨2030102, by rfl⟩ : syracuseStep 2706803 = 4060205) B4060205
theorem B1199495 : Blo 798342 1199495 := bstep (se 1 (by rfl) ⟨899621, by rfl⟩ : syracuseStep 1199495 = 1799243) B1799243
theorem B4050323 : Blo 798342 4050323 := bstep (se 1 (by rfl) ⟨3037742, by rfl⟩ : syracuseStep 4050323 = 6075485) B6075485
theorem B1199531 : Blo 798342 1199531 := bstep (se 1 (by rfl) ⟨899648, by rfl⟩ : syracuseStep 1199531 = 1799297) B1799297
theorem B1199561 : Blo 798342 1199561 := bstep (se 2 (by rfl) ⟨449835, by rfl⟩ : syracuseStep 1199561 = 899671) B899671
theorem B2280905 : Blo 798342 2280905 := bstep (se 2 (by rfl) ⟨855339, by rfl⟩ : syracuseStep 2280905 = 1710679) B1710679
theorem B1199675 : Blo 798342 1199675 := bstep (se 1 (by rfl) ⟨899756, by rfl⟩ : syracuseStep 1199675 = 1799513) B1799513
theorem B3034691 : Blo 798342 3034691 := bstep (se 1 (by rfl) ⟨2276018, by rfl⟩ : syracuseStep 3034691 = 4552037) B4552037
theorem B1199735 : Blo 798342 1199735 := bstep (se 1 (by rfl) ⟨899801, by rfl⟩ : syracuseStep 1199735 = 1799603) B1799603
theorem B1199759 : Blo 798342 1199759 := bstep (se 1 (by rfl) ⟨899819, by rfl⟩ : syracuseStep 1199759 = 1799639) B1799639
theorem B1199801 : Blo 798342 1199801 := bstep (se 2 (by rfl) ⟨449925, by rfl⟩ : syracuseStep 1199801 = 899851) B899851
theorem B1199879 : Blo 798342 1199879 := bstep (se 1 (by rfl) ⟨899909, by rfl⟩ : syracuseStep 1199879 = 1799819) B1799819
theorem B1199915 : Blo 798342 1199915 := bstep (se 1 (by rfl) ⟨899936, by rfl⟩ : syracuseStep 1199915 = 1799873) B1799873
theorem B1199945 : Blo 798342 1199945 := bstep (se 2 (by rfl) ⟨449979, by rfl⟩ : syracuseStep 1199945 = 899959) B899959
theorem B1200059 : Blo 798342 1200059 := bstep (se 1 (by rfl) ⟨900044, by rfl⟩ : syracuseStep 1200059 = 1800089) B1800089
theorem B1200119 : Blo 798342 1200119 := bstep (se 1 (by rfl) ⟨900089, by rfl⟩ : syracuseStep 1200119 = 1800179) B1800179
theorem B9129995 : Blo 798342 9129995 := bstep (se 1 (by rfl) ⟨6847496, by rfl⟩ : syracuseStep 9129995 = 13694993) B13694993
theorem B1200143 : Blo 798342 1200143 := bstep (se 1 (by rfl) ⟨900107, by rfl⟩ : syracuseStep 1200143 = 1800215) B1800215
theorem B1200185 : Blo 798342 1200185 := bstep (se 2 (by rfl) ⟨450069, by rfl⟩ : syracuseStep 1200185 = 900139) B900139
theorem B1200263 : Blo 798342 1200263 := bstep (se 1 (by rfl) ⟨900197, by rfl⟩ : syracuseStep 1200263 = 1800395) B1800395
theorem B1200299 : Blo 798342 1200299 := bstep (se 1 (by rfl) ⟨900224, by rfl⟩ : syracuseStep 1200299 = 1800449) B1800449
theorem B1200329 : Blo 798342 1200329 := bstep (se 2 (by rfl) ⟨450123, by rfl⟩ : syracuseStep 1200329 = 900247) B900247
theorem B1200443 : Blo 798342 1200443 := bstep (se 1 (by rfl) ⟨900332, by rfl⟩ : syracuseStep 1200443 = 1800665) B1800665
theorem B1200503 : Blo 798342 1200503 := bstep (se 1 (by rfl) ⟨900377, by rfl⟩ : syracuseStep 1200503 = 1800755) B1800755
theorem B1200527 : Blo 798342 1200527 := bstep (se 1 (by rfl) ⟨900395, by rfl⟩ : syracuseStep 1200527 = 1800791) B1800791
theorem B1200569 : Blo 798342 1200569 := bstep (se 2 (by rfl) ⟨450213, by rfl⟩ : syracuseStep 1200569 = 900427) B900427
theorem B5132753 : Blo 798342 5132753 := bstep (se 2 (by rfl) ⟨1924782, by rfl⟩ : syracuseStep 5132753 = 3849565) B3849565
theorem B1200647 : Blo 798342 1200647 := bstep (se 1 (by rfl) ⟨900485, by rfl⟩ : syracuseStep 1200647 = 1800971) B1800971
theorem B3035677 : Blo 798342 3035677 := bstep (se 3 (by rfl) ⟨569189, by rfl⟩ : syracuseStep 3035677 = 1138379) B1138379
theorem B1200683 : Blo 798342 1200683 := bstep (se 1 (by rfl) ⟨900512, by rfl⟩ : syracuseStep 1200683 = 1801025) B1801025
theorem B1200713 : Blo 798342 1200713 := bstep (se 2 (by rfl) ⟨450267, by rfl⟩ : syracuseStep 1200713 = 900535) B900535
theorem B4117079 : Blo 798342 4117079 := bstep (se 1 (by rfl) ⟨3087809, by rfl⟩ : syracuseStep 4117079 = 6175619) B6175619
theorem B1200827 : Blo 798342 1200827 := bstep (se 1 (by rfl) ⟨900620, by rfl⟩ : syracuseStep 1200827 = 1801241) B1801241
theorem B4117229 : Blo 798342 4117229 := bstep (se 3 (by rfl) ⟨771980, by rfl⟩ : syracuseStep 4117229 = 1543961) B1543961
theorem B1200887 : Blo 798342 1200887 := bstep (se 1 (by rfl) ⟨900665, by rfl⟩ : syracuseStep 1200887 = 1801331) B1801331
theorem B1200911 : Blo 798342 1200911 := bstep (se 1 (by rfl) ⟨900683, by rfl⟩ : syracuseStep 1200911 = 1801367) B1801367
theorem B1200953 : Blo 798342 1200953 := bstep (se 2 (by rfl) ⟨450357, by rfl⟩ : syracuseStep 1200953 = 900715) B900715
theorem B1201031 : Blo 798342 1201031 := bstep (se 1 (by rfl) ⟨900773, by rfl⟩ : syracuseStep 1201031 = 1801547) B1801547
theorem B1201067 : Blo 798342 1201067 := bstep (se 1 (by rfl) ⟨900800, by rfl⟩ : syracuseStep 1201067 = 1801601) B1801601
theorem B1561529 : Blo 798342 1561529 := bstep (se 2 (by rfl) ⟨585573, by rfl⟩ : syracuseStep 1561529 = 1171147) B1171147
theorem B1201097 : Blo 798342 1201097 := bstep (se 2 (by rfl) ⟨450411, by rfl⟩ : syracuseStep 1201097 = 900823) B900823
theorem B1201211 : Blo 798342 1201211 := bstep (se 1 (by rfl) ⟨900908, by rfl⟩ : syracuseStep 1201211 = 1801817) B1801817
theorem B1201271 : Blo 798342 1201271 := bstep (se 1 (by rfl) ⟨900953, by rfl⟩ : syracuseStep 1201271 = 1801907) B1801907
theorem B1201295 : Blo 798342 1201295 := bstep (se 1 (by rfl) ⟨900971, by rfl⟩ : syracuseStep 1201295 = 1801943) B1801943
theorem B1201337 : Blo 798342 1201337 := bstep (se 2 (by rfl) ⟨450501, by rfl⟩ : syracuseStep 1201337 = 901003) B901003
theorem B2282681 : Blo 798342 2282681 := bstep (se 2 (by rfl) ⟨856005, by rfl⟩ : syracuseStep 2282681 = 1712011) B1712011
theorem B1201415 : Blo 798342 1201415 := bstep (se 1 (by rfl) ⟨901061, by rfl⟩ : syracuseStep 1201415 = 1802123) B1802123
theorem B1201451 : Blo 798342 1201451 := bstep (se 1 (by rfl) ⟨901088, by rfl⟩ : syracuseStep 1201451 = 1802177) B1802177
theorem B1201481 : Blo 798342 1201481 := bstep (se 2 (by rfl) ⟨450555, by rfl⟩ : syracuseStep 1201481 = 901111) B901111
theorem B1201595 : Blo 798342 1201595 := bstep (se 1 (by rfl) ⟨901196, by rfl⟩ : syracuseStep 1201595 = 1802393) B1802393
theorem B1201655 : Blo 798342 1201655 := bstep (se 1 (by rfl) ⟨901241, by rfl⟩ : syracuseStep 1201655 = 1802483) B1802483
theorem B1201679 : Blo 798342 1201679 := bstep (se 1 (by rfl) ⟨901259, by rfl⟩ : syracuseStep 1201679 = 1802519) B1802519
theorem B9754141 : Blo 798342 9754141 := bstep (se 3 (by rfl) ⟨1828901, by rfl⟩ : syracuseStep 9754141 = 3657803) B3657803
theorem B1201721 : Blo 798342 1201721 := bstep (se 2 (by rfl) ⟨450645, by rfl⟩ : syracuseStep 1201721 = 901291) B901291
theorem B1201799 : Blo 798342 1201799 := bstep (se 1 (by rfl) ⟨901349, by rfl⟩ : syracuseStep 1201799 = 1802699) B1802699
theorem B1922707 : Blo 798342 1922707 := bstep (se 1 (by rfl) ⟨1442030, by rfl⟩ : syracuseStep 1922707 = 2884061) B2884061
theorem B1201835 : Blo 798342 1201835 := bstep (se 1 (by rfl) ⟨901376, by rfl⟩ : syracuseStep 1201835 = 1802753) B1802753
theorem B1201865 : Blo 798342 1201865 := bstep (se 2 (by rfl) ⟨450699, by rfl⟩ : syracuseStep 1201865 = 901399) B901399
theorem B1201979 : Blo 798342 1201979 := bstep (se 1 (by rfl) ⟨901484, by rfl⟩ : syracuseStep 1201979 = 1802969) B1802969
theorem B1202039 : Blo 798342 1202039 := bstep (se 1 (by rfl) ⟨901529, by rfl⟩ : syracuseStep 1202039 = 1803059) B1803059
theorem B1202063 : Blo 798342 1202063 := bstep (se 1 (by rfl) ⟨901547, by rfl⟩ : syracuseStep 1202063 = 1803095) B1803095
theorem B1202105 : Blo 798342 1202105 := bstep (se 2 (by rfl) ⟨450789, by rfl⟩ : syracuseStep 1202105 = 901579) B901579
theorem B1202183 : Blo 798342 1202183 := bstep (se 1 (by rfl) ⟨901637, by rfl⟩ : syracuseStep 1202183 = 1803275) B1803275
theorem B1202219 : Blo 798342 1202219 := bstep (se 1 (by rfl) ⟨901664, by rfl⟩ : syracuseStep 1202219 = 1803329) B1803329
theorem B1202249 : Blo 798342 1202249 := bstep (se 2 (by rfl) ⟨450843, by rfl⟩ : syracuseStep 1202249 = 901687) B901687
theorem B2283673 : Blo 798342 2283673 := bstep (se 2 (by rfl) ⟨856377, by rfl⟩ : syracuseStep 2283673 = 1712755) B1712755
theorem B1202363 : Blo 798342 1202363 := bstep (se 1 (by rfl) ⟨901772, by rfl⟩ : syracuseStep 1202363 = 1803545) B1803545
theorem B1202423 : Blo 798342 1202423 := bstep (se 1 (by rfl) ⟨901817, by rfl⟩ : syracuseStep 1202423 = 1803635) B1803635
theorem B1202447 : Blo 798342 1202447 := bstep (se 1 (by rfl) ⟨901835, by rfl⟩ : syracuseStep 1202447 = 1803671) B1803671
theorem B1202489 : Blo 798342 1202489 := bstep (se 2 (by rfl) ⟨450933, by rfl⟩ : syracuseStep 1202489 = 901867) B901867
theorem B2021719 : Blo 798342 2021719 := bstep (se 1 (by rfl) ⟨1516289, by rfl⟩ : syracuseStep 2021719 = 3032579) B3032579
theorem B1202567 : Blo 798342 1202567 := bstep (se 1 (by rfl) ⟨901925, by rfl⟩ : syracuseStep 1202567 = 1803851) B1803851
theorem B4053401 : Blo 798342 4053401 := bstep (se 2 (by rfl) ⟨1520025, by rfl⟩ : syracuseStep 4053401 = 3040051) B3040051
theorem B1202603 : Blo 798342 1202603 := bstep (se 1 (by rfl) ⟨901952, by rfl⟩ : syracuseStep 1202603 = 1803905) B1803905
theorem B1202633 : Blo 798342 1202633 := bstep (se 2 (by rfl) ⟨450987, by rfl⟩ : syracuseStep 1202633 = 901975) B901975
theorem B1202747 : Blo 798342 1202747 := bstep (se 1 (by rfl) ⟨902060, by rfl⟩ : syracuseStep 1202747 = 1804121) B1804121
theorem B3463741 : Blo 798342 3463741 := bstep (se 3 (by rfl) ⟨649451, by rfl⟩ : syracuseStep 3463741 = 1298903) B1298903
theorem B9230915 : Blo 798342 9230915 := bstep (se 1 (by rfl) ⟨6923186, by rfl⟩ : syracuseStep 9230915 = 13846373) B13846373
theorem B1202807 : Blo 798342 1202807 := bstep (se 1 (by rfl) ⟨902105, by rfl⟩ : syracuseStep 1202807 = 1804211) B1804211
theorem B2022023 : Blo 798342 2022023 := bstep (se 1 (by rfl) ⟨1516517, by rfl⟩ : syracuseStep 2022023 = 3033035) B3033035
theorem B1202831 : Blo 798342 1202831 := bstep (se 1 (by rfl) ⟨902123, by rfl⟩ : syracuseStep 1202831 = 1804247) B1804247
theorem B1202873 : Blo 798342 1202873 := bstep (se 2 (by rfl) ⟨451077, by rfl⟩ : syracuseStep 1202873 = 902155) B902155
theorem B1202951 : Blo 798342 1202951 := bstep (se 1 (by rfl) ⟨902213, by rfl⟩ : syracuseStep 1202951 = 1804427) B1804427
theorem B2022155 : Blo 798342 2022155 := bstep (se 1 (by rfl) ⟨1516616, by rfl⟩ : syracuseStep 2022155 = 3033233) B3033233
theorem B1202987 : Blo 798342 1202987 := bstep (se 1 (by rfl) ⟨902240, by rfl⟩ : syracuseStep 1202987 = 1804481) B1804481
theorem B1203017 : Blo 798342 1203017 := bstep (se 2 (by rfl) ⟨451131, by rfl⟩ : syracuseStep 1203017 = 902263) B902263
theorem B4316057 : Blo 798342 4316057 := bstep (se 2 (by rfl) ⟨1618521, by rfl⟩ : syracuseStep 4316057 = 3237043) B3237043
theorem B1203131 : Blo 798342 1203131 := bstep (se 1 (by rfl) ⟨902348, by rfl⟩ : syracuseStep 1203131 = 1804697) B1804697
theorem B1203191 : Blo 798342 1203191 := bstep (se 1 (by rfl) ⟨902393, by rfl⟩ : syracuseStep 1203191 = 1804787) B1804787
theorem B1203215 : Blo 798342 1203215 := bstep (se 1 (by rfl) ⟨902411, by rfl⟩ : syracuseStep 1203215 = 1804823) B1804823
theorem B5200919 : Blo 798342 5200919 := bstep (se 1 (by rfl) ⟨3900689, by rfl⟩ : syracuseStep 5200919 = 7801379) B7801379
theorem B1203257 : Blo 798342 1203257 := bstep (se 2 (by rfl) ⟨451221, by rfl⟩ : syracuseStep 1203257 = 902443) B902443
theorem B1203335 : Blo 798342 1203335 := bstep (se 1 (by rfl) ⟨902501, by rfl⟩ : syracuseStep 1203335 = 1805003) B1805003
theorem B1203371 : Blo 798342 1203371 := bstep (se 1 (by rfl) ⟨902528, by rfl⟩ : syracuseStep 1203371 = 1805057) B1805057
theorem B1203401 : Blo 798342 1203401 := bstep (se 2 (by rfl) ⟨451275, by rfl⟩ : syracuseStep 1203401 = 902551) B902551
theorem B2022671 : Blo 798342 2022671 := bstep (se 1 (by rfl) ⟨1517003, by rfl⟩ : syracuseStep 2022671 = 3034007) B3034007
theorem B1137935 : Blo 798342 1137935 := bstep (se 1 (by rfl) ⟨853451, by rfl⟩ : syracuseStep 1137935 = 1706903) B1706903
theorem B3038579 : Blo 798342 3038579 := bstep (se 1 (by rfl) ⟨2278934, by rfl⟩ : syracuseStep 3038579 = 4557869) B4557869
theorem B2022803 : Blo 798342 2022803 := bstep (se 1 (by rfl) ⟨1517102, by rfl⟩ : syracuseStep 2022803 = 3034205) B3034205
theorem B1924553 : Blo 798342 1924553 := bstep (se 2 (by rfl) ⟨721707, by rfl⟩ : syracuseStep 1924553 = 1443415) B1443415
theorem B1924879 : Blo 798342 1924879 := bstep (se 1 (by rfl) ⟨1443659, by rfl⟩ : syracuseStep 1924879 = 2887319) B2887319
theorem B9134369 : Blo 798342 9134369 := bstep (se 2 (by rfl) ⟨3425388, by rfl⟩ : syracuseStep 9134369 = 6850777) B6850777
theorem B1139017 : Blo 798342 1139017 := bstep (se 2 (by rfl) ⟨427131, by rfl⟩ : syracuseStep 1139017 = 854263) B854263
theorem B1925495 : Blo 798342 1925495 := bstep (se 1 (by rfl) ⟨1444121, by rfl⟩ : syracuseStep 1925495 = 2888243) B2888243
theorem B1139131 : Blo 798342 1139131 := bstep (se 1 (by rfl) ⟨854348, by rfl⟩ : syracuseStep 1139131 = 1708697) B1708697
theorem B12345821 : Blo 798342 12345821 := bstep (se 3 (by rfl) ⟨2314841, by rfl⟩ : syracuseStep 12345821 = 4629683) B4629683
theorem B2023937 : Blo 798342 2023937 := bstep (se 2 (by rfl) ⟨758976, by rfl⟩ : syracuseStep 2023937 = 1517953) B1517953
theorem B4874813 : Blo 798342 4874813 := bstep (se 3 (by rfl) ⟨914027, by rfl⟩ : syracuseStep 4874813 = 1828055) B1828055
theorem B2024311 : Blo 798342 2024311 := bstep (se 1 (by rfl) ⟨1518233, by rfl⟩ : syracuseStep 2024311 = 3036467) B3036467
theorem B4055993 : Blo 798342 4055993 := bstep (se 2 (by rfl) ⟨1520997, by rfl⟩ : syracuseStep 4055993 = 3041995) B3041995
theorem B5137469 : Blo 798342 5137469 := bstep (se 3 (by rfl) ⟨963275, by rfl⟩ : syracuseStep 5137469 = 1926551) B1926551
theorem B17327191 : Blo 798342 17327191 := bstep (se 1 (by rfl) ⟨12995393, by rfl⟩ : syracuseStep 17327191 = 25990787) B25990787
theorem B2188435 : Blo 798342 2188435 := bstep (se 1 (by rfl) ⟨1641326, by rfl⟩ : syracuseStep 2188435 = 3282653) B3282653
theorem B2024747 : Blo 798342 2024747 := bstep (se 1 (by rfl) ⟨1518560, by rfl⟩ : syracuseStep 2024747 = 3037121) B3037121
theorem B6088121 : Blo 798342 6088121 := bstep (se 2 (by rfl) ⟨2283045, by rfl⟩ : syracuseStep 6088121 = 4566091) B4566091
theorem B3040811 : Blo 798342 3040811 := bstep (se 1 (by rfl) ⟨2280608, by rfl⟩ : syracuseStep 3040811 = 4561217) B4561217
theorem B1140743 : Blo 798342 1140743 := bstep (se 1 (by rfl) ⟨855557, by rfl⟩ : syracuseStep 1140743 = 1711115) B1711115
theorem B2025587 : Blo 798342 2025587 := bstep (se 1 (by rfl) ⟨1519190, by rfl⟩ : syracuseStep 2025587 = 3038381) B3038381
theorem B2025607 : Blo 798342 2025607 := bstep (se 1 (by rfl) ⟨1519205, by rfl⟩ : syracuseStep 2025607 = 3038411) B3038411
theorem B4057289 : Blo 798342 4057289 := bstep (se 2 (by rfl) ⟨1521483, by rfl⟩ : syracuseStep 4057289 = 3042967) B3042967
theorem B911623 : Blo 798342 911623 := bstep (se 1 (by rfl) ⟨683717, by rfl⟩ : syracuseStep 911623 = 1367435) B1367435
theorem B2779451 : Blo 798342 2779451 := bstep (se 1 (by rfl) ⟨2084588, by rfl⟩ : syracuseStep 2779451 = 4169177) B4169177
theorem B1796471 : Blo 798342 1796471 := bstep (se 1 (by rfl) ⟨1347353, by rfl⟩ : syracuseStep 1796471 = 2694707) B2694707
theorem B9103751 : Blo 798342 9103751 := bstep (se 1 (by rfl) ⟨6827813, by rfl⟩ : syracuseStep 9103751 = 13655627) B13655627
theorem B2025881 : Blo 798342 2025881 := bstep (se 2 (by rfl) ⟨759705, by rfl⟩ : syracuseStep 2025881 = 1519411) B1519411
theorem B1796651 : Blo 798342 1796651 := bstep (se 1 (by rfl) ⟨1347488, by rfl⟩ : syracuseStep 1796651 = 2694977) B2694977
theorem B2026043 : Blo 798342 2026043 := bstep (se 1 (by rfl) ⟨1519532, by rfl⟩ : syracuseStep 2026043 = 3039065) B3039065
theorem B12315407 : Blo 798342 12315407 := bstep (se 1 (by rfl) ⟨9236555, by rfl⟩ : syracuseStep 12315407 = 18473111) B18473111
theorem B2026255 : Blo 798342 2026255 := bstep (se 1 (by rfl) ⟨1519691, by rfl⟩ : syracuseStep 2026255 = 3039383) B3039383
theorem B5860147 : Blo 798342 5860147 := bstep (se 1 (by rfl) ⟨4395110, by rfl⟩ : syracuseStep 5860147 = 8790221) B8790221
theorem B1010551 : Blo 798342 1010551 := bstep (se 1 (by rfl) ⟨757913, by rfl⟩ : syracuseStep 1010551 = 1515827) B1515827
theorem B1797011 : Blo 798342 1797011 := bstep (se 1 (by rfl) ⟨1347758, by rfl⟩ : syracuseStep 1797011 = 2695517) B2695517
theorem B1797065 : Blo 798342 1797065 := bstep (se 2 (by rfl) ⟨673899, by rfl⟩ : syracuseStep 1797065 = 1347799) B1347799
theorem B1141705 : Blo 798342 1141705 := bstep (se 2 (by rfl) ⟨428139, by rfl⟩ : syracuseStep 1141705 = 856279) B856279
theorem B4320209 : Blo 798342 4320209 := bstep (se 2 (by rfl) ⟨1620078, by rfl⟩ : syracuseStep 4320209 = 3240157) B3240157
theorem B2026529 : Blo 798342 2026529 := bstep (se 2 (by rfl) ⟨759948, by rfl⟩ : syracuseStep 2026529 = 1519897) B1519897
theorem B9137285 : Blo 798342 9137285 := bstep (se 4 (by rfl) ⟨856620, by rfl⟩ : syracuseStep 9137285 = 1713241) B1713241
theorem B1010875 : Blo 798342 1010875 := bstep (se 1 (by rfl) ⟨758156, by rfl⟩ : syracuseStep 1010875 = 1516313) B1516313
theorem B1142201 : Blo 798342 1142201 := bstep (se 2 (by rfl) ⟨428325, by rfl⟩ : syracuseStep 1142201 = 856651) B856651
theorem B1797767 : Blo 798342 1797767 := bstep (se 1 (by rfl) ⟨1348325, by rfl⟩ : syracuseStep 1797767 = 2696651) B2696651
theorem B1797947 : Blo 798342 1797947 := bstep (se 1 (by rfl) ⟨1348460, by rfl⟩ : syracuseStep 1797947 = 2696921) B2696921
theorem B5205875 : Blo 798342 5205875 := bstep (se 1 (by rfl) ⟨3904406, by rfl⟩ : syracuseStep 5205875 = 7808813) B7808813
theorem B1798073 : Blo 798342 1798073 := bstep (se 2 (by rfl) ⟨674277, by rfl⟩ : syracuseStep 1798073 = 1348555) B1348555
theorem B2027531 : Blo 798342 2027531 := bstep (se 1 (by rfl) ⟨1520648, by rfl⟩ : syracuseStep 2027531 = 3041297) B3041297
theorem B1011847 : Blo 798342 1011847 := bstep (se 1 (by rfl) ⟨758885, by rfl⟩ : syracuseStep 1011847 = 1517771) B1517771
theorem B6484205 : Blo 798342 6484205 := bstep (se 3 (by rfl) ⟨1215788, by rfl⟩ : syracuseStep 6484205 = 2431577) B2431577
theorem B1798415 : Blo 798342 1798415 := bstep (se 1 (by rfl) ⟨1348811, by rfl⟩ : syracuseStep 1798415 = 2697623) B2697623
theorem B1798433 : Blo 798342 1798433 := bstep (se 2 (by rfl) ⟨674412, by rfl⟩ : syracuseStep 1798433 = 1348825) B1348825
theorem B21918251 : Blo 798342 21918251 := bstep (se 1 (by rfl) ⟨16438688, by rfl⟩ : syracuseStep 21918251 = 32877377) B32877377
theorem B1012267 : Blo 798342 1012267 := bstep (se 1 (by rfl) ⟨759200, by rfl⟩ : syracuseStep 1012267 = 1518401) B1518401
theorem B1798775 : Blo 798342 1798775 := bstep (se 1 (by rfl) ⟨1349081, by rfl⟩ : syracuseStep 1798775 = 2698163) B2698163
theorem B2028179 : Blo 798342 2028179 := bstep (se 1 (by rfl) ⟨1521134, by rfl⟩ : syracuseStep 2028179 = 3042269) B3042269
theorem B1012495 : Blo 798342 1012495 := bstep (se 1 (by rfl) ⟨759371, by rfl⟩ : syracuseStep 1012495 = 1518743) B1518743
theorem B1798955 : Blo 798342 1798955 := bstep (se 1 (by rfl) ⟨1349216, by rfl⟩ : syracuseStep 1798955 = 2698433) B2698433
theorem B1536887 : Blo 798342 1536887 := bstep (se 1 (by rfl) ⟨1152665, by rfl⟩ : syracuseStep 1536887 = 2305331) B2305331
theorem B3044243 : Blo 798342 3044243 := bstep (se 1 (by rfl) ⟨2283182, by rfl⟩ : syracuseStep 3044243 = 4566365) B4566365
theorem B2028473 : Blo 798342 2028473 := bstep (se 2 (by rfl) ⟨760677, by rfl⟩ : syracuseStep 2028473 = 1521355) B1521355
theorem B1799315 : Blo 798342 1799315 := bstep (se 1 (by rfl) ⟨1349486, by rfl⟩ : syracuseStep 1799315 = 2698973) B2698973
theorem B1799369 : Blo 798342 1799369 := bstep (se 2 (by rfl) ⟨674763, by rfl⟩ : syracuseStep 1799369 = 1349527) B1349527
theorem B4617587 : Blo 798342 4617587 := bstep (se 1 (by rfl) ⟨3463190, by rfl⟩ : syracuseStep 4617587 = 6926381) B6926381
theorem B1013239 : Blo 798342 1013239 := bstep (se 1 (by rfl) ⟨759929, by rfl⟩ : syracuseStep 1013239 = 1519859) B1519859
theorem B2029171 : Blo 798342 2029171 := bstep (se 1 (by rfl) ⟨1521878, by rfl⟩ : syracuseStep 2029171 = 3043757) B3043757
theorem B2029313 : Blo 798342 2029313 := bstep (se 2 (by rfl) ⟨760992, by rfl⟩ : syracuseStep 2029313 = 1521985) B1521985
theorem B1013563 : Blo 798342 1013563 := bstep (se 1 (by rfl) ⟨760172, by rfl⟩ : syracuseStep 1013563 = 1520345) B1520345
theorem B1439623 : Blo 798342 1439623 := bstep (se 1 (by rfl) ⟨1079717, by rfl⟩ : syracuseStep 1439623 = 2159435) B2159435
theorem B1800071 : Blo 798342 1800071 := bstep (se 1 (by rfl) ⟨1350053, by rfl⟩ : syracuseStep 1800071 = 2700107) B2700107
theorem B1800251 : Blo 798342 1800251 := bstep (se 1 (by rfl) ⟨1350188, by rfl⟩ : syracuseStep 1800251 = 2700377) B2700377
theorem B1800377 : Blo 798342 1800377 := bstep (se 2 (by rfl) ⟨675141, by rfl⟩ : syracuseStep 1800377 = 1350283) B1350283
theorem B2029769 : Blo 798342 2029769 := bstep (se 2 (by rfl) ⟨761163, by rfl⟩ : syracuseStep 2029769 = 1522327) B1522327
theorem B11565301 : Blo 798342 11565301 := bstep (se 5 (by rfl) ⟨542123, by rfl⟩ : syracuseStep 11565301 = 1084247) B1084247
theorem B1014059 : Blo 798342 1014059 := bstep (se 1 (by rfl) ⟨760544, by rfl⟩ : syracuseStep 1014059 = 1521089) B1521089
theorem B1440185 : Blo 798342 1440185 := bstep (se 2 (by rfl) ⟨540069, by rfl⟩ : syracuseStep 1440185 = 1080139) B1080139
theorem B1800719 : Blo 798342 1800719 := bstep (se 1 (by rfl) ⟨1350539, by rfl⟩ : syracuseStep 1800719 = 2701079) B2701079
theorem B1800737 : Blo 798342 1800737 := bstep (se 2 (by rfl) ⟨675276, by rfl⟩ : syracuseStep 1800737 = 1350553) B1350553
theorem B2030123 : Blo 798342 2030123 := bstep (se 1 (by rfl) ⟨1522592, by rfl⟩ : syracuseStep 2030123 = 3045185) B3045185
theorem B2161337 : Blo 798342 2161337 := bstep (se 2 (by rfl) ⟨810501, by rfl⟩ : syracuseStep 2161337 = 1621003) B1621003
theorem B1014535 : Blo 798342 1014535 := bstep (se 1 (by rfl) ⟨760901, by rfl⟩ : syracuseStep 1014535 = 1521803) B1521803
theorem B1801079 : Blo 798342 1801079 := bstep (se 1 (by rfl) ⟨1350809, by rfl⟩ : syracuseStep 1801079 = 2701619) B2701619
theorem B1801259 : Blo 798342 1801259 := bstep (se 1 (by rfl) ⟨1350944, by rfl⟩ : syracuseStep 1801259 = 2701889) B2701889
theorem B1015031 : Blo 798342 1015031 := bstep (se 1 (by rfl) ⟨761273, by rfl⟩ : syracuseStep 1015031 = 1522547) B1522547
theorem B1015183 : Blo 798342 1015183 := bstep (se 1 (by rfl) ⟨761387, by rfl⟩ : syracuseStep 1015183 = 1522775) B1522775
theorem B1801619 : Blo 798342 1801619 := bstep (se 1 (by rfl) ⟨1351214, by rfl⟩ : syracuseStep 1801619 = 2702429) B2702429
theorem B1801673 : Blo 798342 1801673 := bstep (se 2 (by rfl) ⟨675627, by rfl⟩ : syracuseStep 1801673 = 1351255) B1351255
theorem B1015355 : Blo 798342 1015355 := bstep (se 1 (by rfl) ⟨761516, by rfl⟩ : syracuseStep 1015355 = 1523033) B1523033
theorem B38961269 : Blo 798342 38961269 := bstep (se 5 (by rfl) ⟨1826309, by rfl⟩ : syracuseStep 38961269 = 3652619) B3652619
theorem B1802411 : Blo 798342 1802411 := bstep (se 1 (by rfl) ⟨1351808, by rfl⟩ : syracuseStep 1802411 = 2703617) B2703617
theorem B9732631 : Blo 798342 9732631 := bstep (se 1 (by rfl) ⟨7299473, by rfl⟩ : syracuseStep 9732631 = 14598947) B14598947
theorem B1802951 : Blo 798342 1802951 := bstep (se 1 (by rfl) ⟨1352213, by rfl⟩ : syracuseStep 1802951 = 2704427) B2704427
theorem B5768009 : Blo 798342 5768009 := bstep (se 2 (by rfl) ⟨2163003, by rfl⟩ : syracuseStep 5768009 = 4326007) B4326007
theorem B5833619 : Blo 798342 5833619 := bstep (se 1 (by rfl) ⟨4375214, by rfl⟩ : syracuseStep 5833619 = 8750429) B8750429
theorem B4555703 : Blo 798342 4555703 := bstep (se 1 (by rfl) ⟨3416777, by rfl⟩ : syracuseStep 4555703 = 6833555) B6833555
theorem B10945601 : Blo 798342 10945601 := bstep (se 2 (by rfl) ⟨4104600, by rfl⟩ : syracuseStep 10945601 = 8209201) B8209201
theorem B6161827 : Blo 798342 6161827 := bstep (se 1 (by rfl) ⟨4621370, by rfl⟩ : syracuseStep 6161827 = 9242741) B9242741
theorem B23102921 : Blo 798342 23102921 := bstep (se 2 (by rfl) ⟨8663595, by rfl⟩ : syracuseStep 23102921 = 17327191) B17327191
theorem B2917913 : Blo 798342 2917913 := bstep (se 2 (by rfl) ⟨1094217, by rfl⟩ : syracuseStep 2917913 = 2188435) B2188435
theorem B1705511 : Blo 798342 1705511 := bstep (se 1 (by rfl) ⟨1279133, by rfl⟩ : syracuseStep 1705511 = 2558267) B2558267
theorem B1803815 : Blo 798342 1803815 := bstep (se 1 (by rfl) ⟨1352861, by rfl⟩ : syracuseStep 1803815 = 2705723) B2705723
theorem B10978877 : Blo 798342 10978877 := bstep (se 3 (by rfl) ⟨2058539, by rfl⟩ : syracuseStep 10978877 = 4117079) B4117079
theorem B4556411 : Blo 798342 4556411 := bstep (se 1 (by rfl) ⟨3417308, by rfl⟩ : syracuseStep 4556411 = 6834617) B6834617
theorem B2557651 : Blo 798342 2557651 := bstep (se 1 (by rfl) ⟨1918238, by rfl⟩ : syracuseStep 2557651 = 3836477) B3836477
theorem B19498745 : Blo 798342 19498745 := bstep (se 2 (by rfl) ⟨7312029, by rfl⟩ : syracuseStep 19498745 = 14624059) B14624059
theorem B1804139 : Blo 798342 1804139 := bstep (se 1 (by rfl) ⟨1353104, by rfl⟩ : syracuseStep 1804139 = 2706209) B2706209
theorem B1804193 : Blo 798342 1804193 := bstep (se 2 (by rfl) ⟨676572, by rfl⟩ : syracuseStep 1804193 = 1353145) B1353145
theorem B9734093 : Blo 798342 9734093 := bstep (se 3 (by rfl) ⟨1825142, by rfl⟩ : syracuseStep 9734093 = 3650285) B3650285
theorem B1804535 : Blo 798342 1804535 := bstep (se 1 (by rfl) ⟨1353401, by rfl⟩ : syracuseStep 1804535 = 2706803) B2706803
theorem B4557161 : Blo 798342 4557161 := bstep (se 2 (by rfl) ⟨1708935, by rfl⟩ : syracuseStep 4557161 = 3417871) B3417871
theorem B1444279 : Blo 798342 1444279 := bstep (se 1 (by rfl) ⟨1083209, by rfl⟩ : syracuseStep 1444279 = 2166419) B2166419
theorem B4164077 : Blo 798342 4164077 := bstep (se 3 (by rfl) ⟨780764, by rfl⟩ : syracuseStep 4164077 = 1561529) B1561529
theorem B1805129 : Blo 798342 1805129 := bstep (se 2 (by rfl) ⟨676923, by rfl⟩ : syracuseStep 1805129 = 1353847) B1353847
theorem B2558881 : Blo 798342 2558881 := bstep (se 2 (by rfl) ⟨959580, by rfl⟩ : syracuseStep 2558881 = 1919161) B1919161
theorem B1215497 : Blo 798342 1215497 := bstep (se 2 (by rfl) ⟨455811, by rfl⟩ : syracuseStep 1215497 = 911623) B911623
theorem B20778619 : Blo 798342 20778619 := bstep (se 1 (by rfl) ⟨15583964, by rfl⟩ : syracuseStep 20778619 = 31167929) B31167929
theorem B6917921 : Blo 798342 6917921 := bstep (se 2 (by rfl) ⟨2594220, by rfl⟩ : syracuseStep 6917921 = 5188441) B5188441
theorem B1347401 : Blo 798342 1347401 := bstep (se 2 (by rfl) ⟨505275, by rfl⟩ : syracuseStep 1347401 = 1010551) B1010551
theorem B1347833 : Blo 798342 1347833 := bstep (se 2 (by rfl) ⟨505437, by rfl⟩ : syracuseStep 1347833 = 1010875) B1010875
theorem B1348015 : Blo 798342 1348015 := bstep (se 1 (by rfl) ⟨1011011, by rfl⟩ : syracuseStep 1348015 = 2022023) B2022023
theorem B1348103 : Blo 798342 1348103 := bstep (se 1 (by rfl) ⟨1011077, by rfl⟩ : syracuseStep 1348103 = 2022155) B2022155
theorem B12325385 : Blo 798342 12325385 := bstep (se 2 (by rfl) ⟨4622019, by rfl⟩ : syracuseStep 12325385 = 9244039) B9244039
theorem B2888327 : Blo 798342 2888327 := bstep (se 1 (by rfl) ⟨2166245, by rfl⟩ : syracuseStep 2888327 = 4332491) B4332491
theorem B2560727 : Blo 798342 2560727 := bstep (se 1 (by rfl) ⟨1920545, by rfl⟩ : syracuseStep 2560727 = 3841091) B3841091
theorem B1348447 : Blo 798342 1348447 := bstep (se 1 (by rfl) ⟨1011335, by rfl⟩ : syracuseStep 1348447 = 2022671) B2022671
theorem B2560943 : Blo 798342 2560943 := bstep (se 1 (by rfl) ⟨1920707, by rfl⟩ : syracuseStep 2560943 = 3841415) B3841415
theorem B4330415 : Blo 798342 4330415 := bstep (se 1 (by rfl) ⟨3247811, by rfl⟩ : syracuseStep 4330415 = 6495623) B6495623
theorem B1348535 : Blo 798342 1348535 := bstep (se 1 (by rfl) ⟨1011401, by rfl⟩ : syracuseStep 1348535 = 2022803) B2022803
theorem B2167739 : Blo 798342 2167739 := bstep (se 1 (by rfl) ⟨1625804, by rfl⟩ : syracuseStep 2167739 = 3251609) B3251609
theorem B1283035 : Blo 798342 1283035 := bstep (se 1 (by rfl) ⟨962276, by rfl⟩ : syracuseStep 1283035 = 1924553) B1924553
theorem B3249305 : Blo 798342 3249305 := bstep (se 2 (by rfl) ⟨1218489, by rfl⟩ : syracuseStep 3249305 = 2436979) B2436979
theorem B3249533 : Blo 798342 3249533 := bstep (se 3 (by rfl) ⟨609287, by rfl⟩ : syracuseStep 3249533 = 1218575) B1218575
theorem B1349129 : Blo 798342 1349129 := bstep (se 2 (by rfl) ⟨505923, by rfl⟩ : syracuseStep 1349129 = 1011847) B1011847
theorem B1283663 : Blo 798342 1283663 := bstep (se 1 (by rfl) ⟨962747, by rfl⟩ : syracuseStep 1283663 = 1925495) B1925495
theorem B8230547 : Blo 798342 8230547 := bstep (se 1 (by rfl) ⟨6172910, by rfl⟩ : syracuseStep 8230547 = 12345821) B12345821
theorem B1349291 : Blo 798342 1349291 := bstep (se 1 (by rfl) ⟨1011968, by rfl⟩ : syracuseStep 1349291 = 2023937) B2023937
theorem B3249875 : Blo 798342 3249875 := bstep (se 1 (by rfl) ⟨2437406, by rfl⟩ : syracuseStep 3249875 = 4874813) B4874813
theorem B1349689 : Blo 798342 1349689 := bstep (se 2 (by rfl) ⟨506133, by rfl⟩ : syracuseStep 1349689 = 1012267) B1012267
theorem B1349831 : Blo 798342 1349831 := bstep (se 1 (by rfl) ⟨1012373, by rfl⟩ : syracuseStep 1349831 = 2024747) B2024747
theorem B1349993 : Blo 798342 1349993 := bstep (se 2 (by rfl) ⟨506247, by rfl⟩ : syracuseStep 1349993 = 1012495) B1012495
theorem B5773771 : Blo 798342 5773771 := bstep (se 1 (by rfl) ⟨4330328, by rfl⟩ : syracuseStep 5773771 = 8660657) B8660657
theorem B3840493 : Blo 798342 3840493 := bstep (se 3 (by rfl) ⟨720092, by rfl⟩ : syracuseStep 3840493 = 1440185) B1440185
theorem B1350391 : Blo 798342 1350391 := bstep (se 1 (by rfl) ⟨1012793, by rfl⟩ : syracuseStep 1350391 = 2025587) B2025587
theorem B6069167 : Blo 798342 6069167 := bstep (se 1 (by rfl) ⟨4551875, by rfl⟩ : syracuseStep 6069167 = 9103751) B9103751
theorem B1350587 : Blo 798342 1350587 := bstep (se 1 (by rfl) ⟨1012940, by rfl⟩ : syracuseStep 1350587 = 2025881) B2025881
theorem B1350695 : Blo 798342 1350695 := bstep (se 1 (by rfl) ⟨1013021, by rfl⟩ : syracuseStep 1350695 = 2026043) B2026043
theorem B1350985 : Blo 798342 1350985 := bstep (se 2 (by rfl) ⟨506619, by rfl⟩ : syracuseStep 1350985 = 1013239) B1013239
theorem B1351019 : Blo 798342 1351019 := bstep (se 1 (by rfl) ⟨1013264, by rfl⟩ : syracuseStep 1351019 = 2026529) B2026529
theorem B2465149 : Blo 798342 2465149 := bstep (se 3 (by rfl) ⟨462215, by rfl⟩ : syracuseStep 2465149 = 924431) B924431
theorem B32841085 : Blo 798342 32841085 := bstep (se 3 (by rfl) ⟨6157703, by rfl⟩ : syracuseStep 32841085 = 12315407) B12315407
theorem B2563609 : Blo 798342 2563609 := bstep (se 2 (by rfl) ⟨961353, by rfl⟩ : syracuseStep 2563609 = 1922707) B1922707
theorem B1351417 : Blo 798342 1351417 := bstep (se 2 (by rfl) ⟨506781, by rfl⟩ : syracuseStep 1351417 = 1013563) B1013563
theorem B2695031 : Blo 798342 2695031 := bstep (se 1 (by rfl) ⟨2021273, by rfl⟩ : syracuseStep 2695031 = 4042547) B4042547
theorem B1351687 : Blo 798342 1351687 := bstep (se 1 (by rfl) ⟨1013765, by rfl⟩ : syracuseStep 1351687 = 2027531) B2027531
theorem B2695247 : Blo 798342 2695247 := bstep (se 1 (by rfl) ⟨2021435, by rfl⟩ : syracuseStep 2695247 = 4042871) B4042871
theorem B5775617 : Blo 798342 5775617 := bstep (se 2 (by rfl) ⟨2165856, by rfl⟩ : syracuseStep 5775617 = 4331713) B4331713
theorem B1352119 : Blo 798342 1352119 := bstep (se 1 (by rfl) ⟨1014089, by rfl⟩ : syracuseStep 1352119 = 2028179) B2028179
theorem B2695625 : Blo 798342 2695625 := bstep (se 2 (by rfl) ⟨1010859, by rfl⟩ : syracuseStep 2695625 = 2021719) B2021719
theorem B1024591 : Blo 798342 1024591 := bstep (se 1 (by rfl) ⟨768443, by rfl⟩ : syracuseStep 1024591 = 1536887) B1536887
theorem B1352315 : Blo 798342 1352315 := bstep (se 1 (by rfl) ⟨1014236, by rfl⟩ : syracuseStep 1352315 = 2028473) B2028473
theorem B7709357 : Blo 798342 7709357 := bstep (se 3 (by rfl) ⟨1445504, by rfl⟩ : syracuseStep 7709357 = 2891009) B2891009
theorem B9249491 : Blo 798342 9249491 := bstep (se 1 (by rfl) ⟨6937118, by rfl⟩ : syracuseStep 9249491 = 13874237) B13874237
theorem B2695895 : Blo 798342 2695895 := bstep (se 1 (by rfl) ⟨2021921, by rfl⟩ : syracuseStep 2695895 = 4043843) B4043843
theorem B2696111 : Blo 798342 2696111 := bstep (se 1 (by rfl) ⟨2022083, by rfl⟩ : syracuseStep 2696111 = 4044167) B4044167
theorem B1713071 : Blo 798342 1713071 := bstep (se 1 (by rfl) ⟨1284803, by rfl⟩ : syracuseStep 1713071 = 2569607) B2569607
theorem B1352713 : Blo 798342 1352713 := bstep (se 2 (by rfl) ⟨507267, by rfl⟩ : syracuseStep 1352713 = 1014535) B1014535
theorem B1516715 : Blo 798342 1516715 := bstep (se 1 (by rfl) ⟨1137536, by rfl⟩ : syracuseStep 1516715 = 2275073) B2275073
theorem B1352875 : Blo 798342 1352875 := bstep (se 1 (by rfl) ⟨1014656, by rfl⟩ : syracuseStep 1352875 = 2029313) B2029313
theorem B1516943 : Blo 798342 1516943 := bstep (se 1 (by rfl) ⟨1137707, by rfl⟩ : syracuseStep 1516943 = 2275415) B2275415
theorem B5776859 : Blo 798342 5776859 := bstep (se 1 (by rfl) ⟨4332644, by rfl⟩ : syracuseStep 5776859 = 8665289) B8665289
theorem B1353179 : Blo 798342 1353179 := bstep (se 1 (by rfl) ⟨1014884, by rfl⟩ : syracuseStep 1353179 = 2029769) B2029769
theorem B1353415 : Blo 798342 1353415 := bstep (se 1 (by rfl) ⟨1015061, by rfl⟩ : syracuseStep 1353415 = 2030123) B2030123
theorem B1353577 : Blo 798342 1353577 := bstep (se 2 (by rfl) ⟨507591, by rfl⟩ : syracuseStep 1353577 = 1015183) B1015183
theorem B7677989 : Blo 798342 7677989 := bstep (se 4 (by rfl) ⟨719811, by rfl⟩ : syracuseStep 7677989 = 1439623) B1439623
theorem B2566505 : Blo 798342 2566505 := bstep (se 2 (by rfl) ⟨962439, by rfl⟩ : syracuseStep 2566505 = 1924879) B1924879
theorem B2435471 : Blo 798342 2435471 := bstep (se 1 (by rfl) ⟨1826603, by rfl⟩ : syracuseStep 2435471 = 3653207) B3653207
theorem B1518203 : Blo 798342 1518203 := bstep (se 1 (by rfl) ⟨1138652, by rfl⟩ : syracuseStep 1518203 = 2277305) B2277305
theorem B5778499 : Blo 798342 5778499 := bstep (se 1 (by rfl) ⟨4333874, by rfl⟩ : syracuseStep 5778499 = 8667749) B8667749
theorem B1518689 : Blo 798342 1518689 := bstep (se 2 (by rfl) ⟨569508, by rfl⟩ : syracuseStep 1518689 = 1139017) B1139017
theorem B4041899 : Blo 798342 4041899 := bstep (se 1 (by rfl) ⟨3031424, by rfl⟩ : syracuseStep 4041899 = 6062849) B6062849
theorem B2698487 : Blo 798342 2698487 := bstep (se 1 (by rfl) ⟨2023865, by rfl⟩ : syracuseStep 2698487 = 4047731) B4047731
theorem B1518841 : Blo 798342 1518841 := bstep (se 2 (by rfl) ⟨569565, by rfl⟩ : syracuseStep 1518841 = 1139131) B1139131
theorem B10530269 : Blo 798342 10530269 := bstep (se 3 (by rfl) ⟨1974425, by rfl⟩ : syracuseStep 10530269 = 3948851) B3948851
theorem B4107763 : Blo 798342 4107763 := bstep (se 1 (by rfl) ⟨3080822, by rfl⟩ : syracuseStep 4107763 = 6161645) B6161645
theorem B2731529 : Blo 798342 2731529 := bstep (se 2 (by rfl) ⟨1024323, by rfl⟩ : syracuseStep 2731529 = 2048647) B2048647
theorem B2698811 : Blo 798342 2698811 := bstep (se 1 (by rfl) ⟨2024108, by rfl⟩ : syracuseStep 2698811 = 4048217) B4048217
theorem B4042385 : Blo 798342 4042385 := bstep (se 2 (by rfl) ⟨1515894, by rfl⟩ : syracuseStep 4042385 = 3031789) B3031789
theorem B5123731 : Blo 798342 5123731 := bstep (se 1 (by rfl) ⟨3842798, by rfl⟩ : syracuseStep 5123731 = 7685597) B7685597
theorem B798383 : Blo 798342 798383 := bstep (se 1 (by rfl) ⟨598787, by rfl⟩ : syracuseStep 798383 = 1197575) B1197575
theorem B798407 : Blo 798342 798407 := bstep (se 1 (by rfl) ⟨598805, by rfl⟩ : syracuseStep 798407 = 1197611) B1197611
theorem B798427 : Blo 798342 798427 := bstep (se 1 (by rfl) ⟨598820, by rfl⟩ : syracuseStep 798427 = 1197641) B1197641
theorem B798503 : Blo 798342 798503 := bstep (se 1 (by rfl) ⟨598877, by rfl⟩ : syracuseStep 798503 = 1197755) B1197755
theorem B2699081 : Blo 798342 2699081 := bstep (se 2 (by rfl) ⟨1012155, by rfl⟩ : syracuseStep 2699081 = 2024311) B2024311
theorem B798543 : Blo 798342 798543 := bstep (se 1 (by rfl) ⟨598907, by rfl⟩ : syracuseStep 798543 = 1197815) B1197815
theorem B798559 : Blo 798342 798559 := bstep (se 1 (by rfl) ⟨598919, by rfl⟩ : syracuseStep 798559 = 1197839) B1197839
theorem B798587 : Blo 798342 798587 := bstep (se 1 (by rfl) ⟨598940, by rfl⟩ : syracuseStep 798587 = 1197881) B1197881
theorem B798639 : Blo 798342 798639 := bstep (se 1 (by rfl) ⟨598979, by rfl⟩ : syracuseStep 798639 = 1197959) B1197959
theorem B798663 : Blo 798342 798663 := bstep (se 1 (by rfl) ⟨598997, by rfl⟩ : syracuseStep 798663 = 1197995) B1197995
theorem B798683 : Blo 798342 798683 := bstep (se 1 (by rfl) ⟨599012, by rfl⟩ : syracuseStep 798683 = 1198025) B1198025
theorem B798759 : Blo 798342 798759 := bstep (se 1 (by rfl) ⟨599069, by rfl⟩ : syracuseStep 798759 = 1198139) B1198139
theorem B798799 : Blo 798342 798799 := bstep (se 1 (by rfl) ⟨599099, by rfl⟩ : syracuseStep 798799 = 1198199) B1198199
theorem B798815 : Blo 798342 798815 := bstep (se 1 (by rfl) ⟨599111, by rfl⟩ : syracuseStep 798815 = 1198223) B1198223
theorem B798843 : Blo 798342 798843 := bstep (se 1 (by rfl) ⟨599132, by rfl⟩ : syracuseStep 798843 = 1198265) B1198265
theorem B8335523 : Blo 798342 8335523 := bstep (se 1 (by rfl) ⟨6251642, by rfl⟩ : syracuseStep 8335523 = 12503285) B12503285
theorem B798895 : Blo 798342 798895 := bstep (se 1 (by rfl) ⟨599171, by rfl⟩ : syracuseStep 798895 = 1198343) B1198343
theorem B798919 : Blo 798342 798919 := bstep (se 1 (by rfl) ⟨599189, by rfl⟩ : syracuseStep 798919 = 1198379) B1198379
theorem B798939 : Blo 798342 798939 := bstep (se 1 (by rfl) ⟨599204, by rfl⟩ : syracuseStep 798939 = 1198409) B1198409
theorem B799015 : Blo 798342 799015 := bstep (se 1 (by rfl) ⟨599261, by rfl⟩ : syracuseStep 799015 = 1198523) B1198523
theorem B799055 : Blo 798342 799055 := bstep (se 1 (by rfl) ⟨599291, by rfl⟩ : syracuseStep 799055 = 1198583) B1198583
theorem B799071 : Blo 798342 799071 := bstep (se 1 (by rfl) ⟨599303, by rfl⟩ : syracuseStep 799071 = 1198607) B1198607
theorem B799099 : Blo 798342 799099 := bstep (se 1 (by rfl) ⟨599324, by rfl⟩ : syracuseStep 799099 = 1198649) B1198649
theorem B799151 : Blo 798342 799151 := bstep (se 1 (by rfl) ⟨599363, by rfl⟩ : syracuseStep 799151 = 1198727) B1198727
theorem B799175 : Blo 798342 799175 := bstep (se 1 (by rfl) ⟨599381, by rfl⟩ : syracuseStep 799175 = 1198763) B1198763
theorem B799195 : Blo 798342 799195 := bstep (se 1 (by rfl) ⟨599396, by rfl⟩ : syracuseStep 799195 = 1198793) B1198793
theorem B1520147 : Blo 798342 1520147 := bstep (se 1 (by rfl) ⟨1140110, by rfl⟩ : syracuseStep 1520147 = 2280221) B2280221
theorem B799271 : Blo 798342 799271 := bstep (se 1 (by rfl) ⟨599453, by rfl⟩ : syracuseStep 799271 = 1198907) B1198907
theorem B799311 : Blo 798342 799311 := bstep (se 1 (by rfl) ⟨599483, by rfl⟩ : syracuseStep 799311 = 1198967) B1198967
theorem B799327 : Blo 798342 799327 := bstep (se 1 (by rfl) ⟨599495, by rfl⟩ : syracuseStep 799327 = 1198991) B1198991
theorem B799355 : Blo 798342 799355 := bstep (se 1 (by rfl) ⟨599516, by rfl⟩ : syracuseStep 799355 = 1199033) B1199033
theorem B1520299 : Blo 798342 1520299 := bstep (se 1 (by rfl) ⟨1140224, by rfl⟩ : syracuseStep 1520299 = 2280449) B2280449
theorem B5190317 : Blo 798342 5190317 := bstep (se 3 (by rfl) ⟨973184, by rfl⟩ : syracuseStep 5190317 = 1946369) B1946369
theorem B799407 : Blo 798342 799407 := bstep (se 1 (by rfl) ⟨599555, by rfl⟩ : syracuseStep 799407 = 1199111) B1199111
theorem B799431 : Blo 798342 799431 := bstep (se 1 (by rfl) ⟨599573, by rfl⟩ : syracuseStep 799431 = 1199147) B1199147
theorem B963271 : Blo 798342 963271 := bstep (se 1 (by rfl) ⟨722453, by rfl⟩ : syracuseStep 963271 = 1444907) B1444907
theorem B5124809 : Blo 798342 5124809 := bstep (se 2 (by rfl) ⟨1921803, by rfl⟩ : syracuseStep 5124809 = 3843607) B3843607
theorem B799451 : Blo 798342 799451 := bstep (se 1 (by rfl) ⟨599588, by rfl⟩ : syracuseStep 799451 = 1199177) B1199177
theorem B799527 : Blo 798342 799527 := bstep (se 1 (by rfl) ⟨599645, by rfl⟩ : syracuseStep 799527 = 1199291) B1199291
theorem B2732843 : Blo 798342 2732843 := bstep (se 1 (by rfl) ⟨2049632, by rfl⟩ : syracuseStep 2732843 = 4099265) B4099265
theorem B799567 : Blo 798342 799567 := bstep (se 1 (by rfl) ⟨599675, by rfl⟩ : syracuseStep 799567 = 1199351) B1199351
theorem B799583 : Blo 798342 799583 := bstep (se 1 (by rfl) ⟨599687, by rfl⟩ : syracuseStep 799583 = 1199375) B1199375
theorem B6828907 : Blo 798342 6828907 := bstep (se 1 (by rfl) ⟨5121680, by rfl⟩ : syracuseStep 6828907 = 10243361) B10243361
theorem B799611 : Blo 798342 799611 := bstep (se 1 (by rfl) ⟨599708, by rfl⟩ : syracuseStep 799611 = 1199417) B1199417
theorem B1520527 : Blo 798342 1520527 := bstep (se 1 (by rfl) ⟨1140395, by rfl⟩ : syracuseStep 1520527 = 2280791) B2280791
theorem B799663 : Blo 798342 799663 := bstep (se 1 (by rfl) ⟨599747, by rfl⟩ : syracuseStep 799663 = 1199495) B1199495
theorem B2700215 : Blo 798342 2700215 := bstep (se 1 (by rfl) ⟨2025161, by rfl⟩ : syracuseStep 2700215 = 4050323) B4050323
theorem B799687 : Blo 798342 799687 := bstep (se 1 (by rfl) ⟨599765, by rfl⟩ : syracuseStep 799687 = 1199531) B1199531
theorem B799707 : Blo 798342 799707 := bstep (se 1 (by rfl) ⟨599780, by rfl⟩ : syracuseStep 799707 = 1199561) B1199561
theorem B1520603 : Blo 798342 1520603 := bstep (se 1 (by rfl) ⟨1140452, by rfl⟩ : syracuseStep 1520603 = 2280905) B2280905
theorem B799783 : Blo 798342 799783 := bstep (se 1 (by rfl) ⟨599837, by rfl⟩ : syracuseStep 799783 = 1199675) B1199675
theorem B799823 : Blo 798342 799823 := bstep (se 1 (by rfl) ⟨599867, by rfl⟩ : syracuseStep 799823 = 1199735) B1199735
theorem B799839 : Blo 798342 799839 := bstep (se 1 (by rfl) ⟨599879, by rfl⟩ : syracuseStep 799839 = 1199759) B1199759
theorem B1619041 : Blo 798342 1619041 := bstep (se 2 (by rfl) ⟨607140, by rfl⟩ : syracuseStep 1619041 = 1214281) B1214281
theorem B799867 : Blo 798342 799867 := bstep (se 1 (by rfl) ⟨599900, by rfl⟩ : syracuseStep 799867 = 1199801) B1199801
theorem B799919 : Blo 798342 799919 := bstep (se 1 (by rfl) ⟨599939, by rfl⟩ : syracuseStep 799919 = 1199879) B1199879
theorem B799943 : Blo 798342 799943 := bstep (se 1 (by rfl) ⟨599957, by rfl⟩ : syracuseStep 799943 = 1199915) B1199915
theorem B799963 : Blo 798342 799963 := bstep (se 1 (by rfl) ⟨599972, by rfl⟩ : syracuseStep 799963 = 1199945) B1199945
theorem B2733323 : Blo 798342 2733323 := bstep (se 1 (by rfl) ⟨2049992, by rfl⟩ : syracuseStep 2733323 = 4099985) B4099985
theorem B800039 : Blo 798342 800039 := bstep (se 1 (by rfl) ⟨600029, by rfl⟩ : syracuseStep 800039 = 1200059) B1200059
theorem B800079 : Blo 798342 800079 := bstep (se 1 (by rfl) ⟨600059, by rfl⟩ : syracuseStep 800079 = 1200119) B1200119
theorem B800095 : Blo 798342 800095 := bstep (se 1 (by rfl) ⟨600071, by rfl⟩ : syracuseStep 800095 = 1200143) B1200143
theorem B800123 : Blo 798342 800123 := bstep (se 1 (by rfl) ⟨600092, by rfl⟩ : syracuseStep 800123 = 1200185) B1200185
theorem B3159425 : Blo 798342 3159425 := bstep (se 2 (by rfl) ⟨1184784, by rfl⟩ : syracuseStep 3159425 = 2369569) B2369569
theorem B800175 : Blo 798342 800175 := bstep (se 1 (by rfl) ⟨600131, by rfl⟩ : syracuseStep 800175 = 1200263) B1200263
theorem B800199 : Blo 798342 800199 := bstep (se 1 (by rfl) ⟨600149, by rfl⟩ : syracuseStep 800199 = 1200299) B1200299
theorem B800219 : Blo 798342 800219 := bstep (se 1 (by rfl) ⟨600164, by rfl⟩ : syracuseStep 800219 = 1200329) B1200329
theorem B2700809 : Blo 798342 2700809 := bstep (se 2 (by rfl) ⟨1012803, by rfl⟩ : syracuseStep 2700809 = 2025607) B2025607
theorem B800295 : Blo 798342 800295 := bstep (se 1 (by rfl) ⟨600221, by rfl⟩ : syracuseStep 800295 = 1200443) B1200443
theorem B800335 : Blo 798342 800335 := bstep (se 1 (by rfl) ⟨600251, by rfl⟩ : syracuseStep 800335 = 1200503) B1200503
theorem B800351 : Blo 798342 800351 := bstep (se 1 (by rfl) ⟨600263, by rfl⟩ : syracuseStep 800351 = 1200527) B1200527
theorem B800379 : Blo 798342 800379 := bstep (se 1 (by rfl) ⟨600284, by rfl⟩ : syracuseStep 800379 = 1200569) B1200569
theorem B3421835 : Blo 798342 3421835 := bstep (se 1 (by rfl) ⟨2566376, by rfl⟩ : syracuseStep 3421835 = 5132753) B5132753
theorem B800431 : Blo 798342 800431 := bstep (se 1 (by rfl) ⟨600323, by rfl⟩ : syracuseStep 800431 = 1200647) B1200647
theorem B800455 : Blo 798342 800455 := bstep (se 1 (by rfl) ⟨600341, by rfl⟩ : syracuseStep 800455 = 1200683) B1200683
theorem B800475 : Blo 798342 800475 := bstep (se 1 (by rfl) ⟨600356, by rfl⟩ : syracuseStep 800475 = 1200713) B1200713
theorem B4568825 : Blo 798342 4568825 := bstep (se 2 (by rfl) ⟨1713309, by rfl⟩ : syracuseStep 4568825 = 3426619) B3426619
theorem B800551 : Blo 798342 800551 := bstep (se 1 (by rfl) ⟨600413, by rfl⟩ : syracuseStep 800551 = 1200827) B1200827
theorem B800591 : Blo 798342 800591 := bstep (se 1 (by rfl) ⟨600443, by rfl⟩ : syracuseStep 800591 = 1200887) B1200887
theorem B800607 : Blo 798342 800607 := bstep (se 1 (by rfl) ⟨600455, by rfl⟩ : syracuseStep 800607 = 1200911) B1200911
theorem B4044653 : Blo 798342 4044653 := bstep (se 3 (by rfl) ⟨758372, by rfl⟩ : syracuseStep 4044653 = 1516745) B1516745
theorem B800635 : Blo 798342 800635 := bstep (se 1 (by rfl) ⟨600476, by rfl⟩ : syracuseStep 800635 = 1200953) B1200953
theorem B800687 : Blo 798342 800687 := bstep (se 1 (by rfl) ⟨600515, by rfl⟩ : syracuseStep 800687 = 1201031) B1201031
theorem B800711 : Blo 798342 800711 := bstep (se 1 (by rfl) ⟨600533, by rfl⟩ : syracuseStep 800711 = 1201067) B1201067
theorem B800731 : Blo 798342 800731 := bstep (se 1 (by rfl) ⟨600548, by rfl⟩ : syracuseStep 800731 = 1201097) B1201097
theorem B4044815 : Blo 798342 4044815 := bstep (se 1 (by rfl) ⟨3033611, by rfl⟩ : syracuseStep 4044815 = 6067223) B6067223
theorem B800807 : Blo 798342 800807 := bstep (se 1 (by rfl) ⟨600605, by rfl⟩ : syracuseStep 800807 = 1201211) B1201211
theorem B800847 : Blo 798342 800847 := bstep (se 1 (by rfl) ⟨600635, by rfl⟩ : syracuseStep 800847 = 1201271) B1201271
theorem B800863 : Blo 798342 800863 := bstep (se 1 (by rfl) ⟨600647, by rfl⟩ : syracuseStep 800863 = 1201295) B1201295
theorem B800891 : Blo 798342 800891 := bstep (se 1 (by rfl) ⟨600668, by rfl⟩ : syracuseStep 800891 = 1201337) B1201337
theorem B800943 : Blo 798342 800943 := bstep (se 1 (by rfl) ⟨600707, by rfl⟩ : syracuseStep 800943 = 1201415) B1201415
theorem B800967 : Blo 798342 800967 := bstep (se 1 (by rfl) ⟨600725, by rfl⟩ : syracuseStep 800967 = 1201451) B1201451
theorem B800987 : Blo 798342 800987 := bstep (se 1 (by rfl) ⟨600740, by rfl⟩ : syracuseStep 800987 = 1201481) B1201481
theorem B801063 : Blo 798342 801063 := bstep (se 1 (by rfl) ⟨600797, by rfl⟩ : syracuseStep 801063 = 1201595) B1201595
theorem B801103 : Blo 798342 801103 := bstep (se 1 (by rfl) ⟨600827, by rfl⟩ : syracuseStep 801103 = 1201655) B1201655
theorem B801119 : Blo 798342 801119 := bstep (se 1 (by rfl) ⟨600839, by rfl⟩ : syracuseStep 801119 = 1201679) B1201679
theorem B2701673 : Blo 798342 2701673 := bstep (se 2 (by rfl) ⟨1013127, by rfl⟩ : syracuseStep 2701673 = 2026255) B2026255
theorem B801147 : Blo 798342 801147 := bstep (se 1 (by rfl) ⟨600860, by rfl⟩ : syracuseStep 801147 = 1201721) B1201721
theorem B7813529 : Blo 798342 7813529 := bstep (se 2 (by rfl) ⟨2930073, by rfl⟩ : syracuseStep 7813529 = 5860147) B5860147
theorem B801199 : Blo 798342 801199 := bstep (se 1 (by rfl) ⟨600899, by rfl⟩ : syracuseStep 801199 = 1201799) B1201799
theorem B801223 : Blo 798342 801223 := bstep (se 1 (by rfl) ⟨600917, by rfl⟩ : syracuseStep 801223 = 1201835) B1201835
theorem B801243 : Blo 798342 801243 := bstep (se 1 (by rfl) ⟨600932, by rfl⟩ : syracuseStep 801243 = 1201865) B1201865
theorem B801319 : Blo 798342 801319 := bstep (se 1 (by rfl) ⟨600989, by rfl⟩ : syracuseStep 801319 = 1201979) B1201979
theorem B801359 : Blo 798342 801359 := bstep (se 1 (by rfl) ⟨601019, by rfl⟩ : syracuseStep 801359 = 1202039) B1202039
theorem B801375 : Blo 798342 801375 := bstep (se 1 (by rfl) ⟨601031, by rfl⟩ : syracuseStep 801375 = 1202063) B1202063
theorem B899707 : Blo 798342 899707 := bstep (se 1 (by rfl) ⟨674780, by rfl⟩ : syracuseStep 899707 = 1349561) B1349561
theorem B801403 : Blo 798342 801403 := bstep (se 1 (by rfl) ⟨601052, by rfl⟩ : syracuseStep 801403 = 1202105) B1202105
theorem B801455 : Blo 798342 801455 := bstep (se 1 (by rfl) ⟨601091, by rfl⟩ : syracuseStep 801455 = 1202183) B1202183
theorem B2276029 : Blo 798342 2276029 := bstep (se 3 (by rfl) ⟨426755, by rfl⟩ : syracuseStep 2276029 = 853511) B853511
theorem B801479 : Blo 798342 801479 := bstep (se 1 (by rfl) ⟨601109, by rfl⟩ : syracuseStep 801479 = 1202219) B1202219
theorem B801499 : Blo 798342 801499 := bstep (se 1 (by rfl) ⟨601124, by rfl⟩ : syracuseStep 801499 = 1202249) B1202249
theorem B801575 : Blo 798342 801575 := bstep (se 1 (by rfl) ⟨601181, by rfl⟩ : syracuseStep 801575 = 1202363) B1202363
theorem B801615 : Blo 798342 801615 := bstep (se 1 (by rfl) ⟨601211, by rfl⟩ : syracuseStep 801615 = 1202423) B1202423
theorem B801631 : Blo 798342 801631 := bstep (se 1 (by rfl) ⟨601223, by rfl⟩ : syracuseStep 801631 = 1202447) B1202447
theorem B801659 : Blo 798342 801659 := bstep (se 1 (by rfl) ⟨601244, by rfl⟩ : syracuseStep 801659 = 1202489) B1202489
theorem B2276257 : Blo 798342 2276257 := bstep (se 2 (by rfl) ⟨853596, by rfl⟩ : syracuseStep 2276257 = 1707193) B1707193
theorem B801711 : Blo 798342 801711 := bstep (se 1 (by rfl) ⟨601283, by rfl⟩ : syracuseStep 801711 = 1202567) B1202567
theorem B2702267 : Blo 798342 2702267 := bstep (se 1 (by rfl) ⟨2026700, by rfl⟩ : syracuseStep 2702267 = 4053401) B4053401
theorem B801735 : Blo 798342 801735 := bstep (se 1 (by rfl) ⟨601301, by rfl⟩ : syracuseStep 801735 = 1202603) B1202603
theorem B801755 : Blo 798342 801755 := bstep (se 1 (by rfl) ⟨601316, by rfl⟩ : syracuseStep 801755 = 1202633) B1202633
theorem B801831 : Blo 798342 801831 := bstep (se 1 (by rfl) ⟨601373, by rfl⟩ : syracuseStep 801831 = 1202747) B1202747
theorem B900175 : Blo 798342 900175 := bstep (se 1 (by rfl) ⟨675131, by rfl⟩ : syracuseStep 900175 = 1350263) B1350263
theorem B801871 : Blo 798342 801871 := bstep (se 1 (by rfl) ⟨601403, by rfl⟩ : syracuseStep 801871 = 1202807) B1202807
theorem B801887 : Blo 798342 801887 := bstep (se 1 (by rfl) ⟨601415, by rfl⟩ : syracuseStep 801887 = 1202831) B1202831
theorem B801915 : Blo 798342 801915 := bstep (se 1 (by rfl) ⟨601436, by rfl⟩ : syracuseStep 801915 = 1202873) B1202873
theorem B801967 : Blo 798342 801967 := bstep (se 1 (by rfl) ⟨601475, by rfl⟩ : syracuseStep 801967 = 1202951) B1202951
theorem B801991 : Blo 798342 801991 := bstep (se 1 (by rfl) ⟨601493, by rfl⟩ : syracuseStep 801991 = 1202987) B1202987
theorem B802011 : Blo 798342 802011 := bstep (se 1 (by rfl) ⟨601508, by rfl⟩ : syracuseStep 802011 = 1203017) B1203017
theorem B2276599 : Blo 798342 2276599 := bstep (se 1 (by rfl) ⟨1707449, by rfl⟩ : syracuseStep 2276599 = 3414899) B3414899
theorem B802087 : Blo 798342 802087 := bstep (se 1 (by rfl) ⟨601565, by rfl⟩ : syracuseStep 802087 = 1203131) B1203131
theorem B802127 : Blo 798342 802127 := bstep (se 1 (by rfl) ⟨601595, by rfl⟩ : syracuseStep 802127 = 1203191) B1203191
theorem B802143 : Blo 798342 802143 := bstep (se 1 (by rfl) ⟨601607, by rfl⟩ : syracuseStep 802143 = 1203215) B1203215
theorem B802171 : Blo 798342 802171 := bstep (se 1 (by rfl) ⟨601628, by rfl⟩ : syracuseStep 802171 = 1203257) B1203257
theorem B802223 : Blo 798342 802223 := bstep (se 1 (by rfl) ⟨601667, by rfl⟩ : syracuseStep 802223 = 1203335) B1203335
theorem B802247 : Blo 798342 802247 := bstep (se 1 (by rfl) ⟨601685, by rfl⟩ : syracuseStep 802247 = 1203371) B1203371
theorem B6077915 : Blo 798342 6077915 := bstep (se 1 (by rfl) ⟨4558436, by rfl⟩ : syracuseStep 6077915 = 9116873) B9116873
theorem B900571 : Blo 798342 900571 := bstep (se 1 (by rfl) ⟨675428, by rfl⟩ : syracuseStep 900571 = 1350857) B1350857
theorem B802267 : Blo 798342 802267 := bstep (se 1 (by rfl) ⟨601700, by rfl⟩ : syracuseStep 802267 = 1203401) B1203401
theorem B2276873 : Blo 798342 2276873 := bstep (se 2 (by rfl) ⟨853827, by rfl⟩ : syracuseStep 2276873 = 1707655) B1707655
theorem B23117683 : Blo 798342 23117683 := bstep (se 1 (by rfl) ⟨17338262, by rfl⟩ : syracuseStep 23117683 = 34676525) B34676525
theorem B901039 : Blo 798342 901039 := bstep (se 1 (by rfl) ⟨675779, by rfl⟩ : syracuseStep 901039 = 1351559) B1351559
theorem B6078401 : Blo 798342 6078401 := bstep (se 2 (by rfl) ⟨2279400, by rfl⟩ : syracuseStep 6078401 = 4558801) B4558801
theorem B2277533 : Blo 798342 2277533 := bstep (se 3 (by rfl) ⟨427037, by rfl⟩ : syracuseStep 2277533 = 854075) B854075
theorem B901471 : Blo 798342 901471 := bstep (se 1 (by rfl) ⟨676103, by rfl⟩ : syracuseStep 901471 = 1352207) B1352207
theorem B1622447 : Blo 798342 1622447 := bstep (se 1 (by rfl) ⟨1216835, by rfl⟩ : syracuseStep 1622447 = 2433671) B2433671
theorem B2277875 : Blo 798342 2277875 := bstep (se 1 (by rfl) ⟨1708406, by rfl⟩ : syracuseStep 2277875 = 3416813) B3416813
theorem B3031577 : Blo 798342 3031577 := bstep (se 2 (by rfl) ⟨1136841, by rfl⟩ : syracuseStep 3031577 = 2273683) B2273683
theorem B2703995 : Blo 798342 2703995 := bstep (se 1 (by rfl) ⟨2027996, by rfl⟩ : syracuseStep 2703995 = 4055993) B4055993
theorem B901831 : Blo 798342 901831 := bstep (se 1 (by rfl) ⟨676373, by rfl⟩ : syracuseStep 901831 = 1352747) B1352747
theorem B4047569 : Blo 798342 4047569 := bstep (se 2 (by rfl) ⟨1517838, by rfl⟩ : syracuseStep 4047569 = 3035677) B3035677
theorem B6669011 : Blo 798342 6669011 := bstep (se 1 (by rfl) ⟨5001758, by rfl⟩ : syracuseStep 6669011 = 10003517) B10003517
theorem B3424979 : Blo 798342 3424979 := bstep (se 1 (by rfl) ⟨2568734, by rfl⟩ : syracuseStep 3424979 = 5137469) B5137469
theorem B2704157 : Blo 798342 2704157 := bstep (se 3 (by rfl) ⟨507029, by rfl⟩ : syracuseStep 2704157 = 1014059) B1014059
theorem B2278331 : Blo 798342 2278331 := bstep (se 1 (by rfl) ⟨1708748, by rfl⟩ : syracuseStep 2278331 = 3417497) B3417497
theorem B1623079 : Blo 798342 1623079 := bstep (se 1 (by rfl) ⟨1217309, by rfl⟩ : syracuseStep 1623079 = 2434619) B2434619
theorem B6079859 : Blo 798342 6079859 := bstep (se 1 (by rfl) ⟨4559894, by rfl⟩ : syracuseStep 6079859 = 9119789) B9119789
theorem B2704859 : Blo 798342 2704859 := bstep (se 1 (by rfl) ⟨2028644, by rfl⟩ : syracuseStep 2704859 = 4057289) B4057289
theorem B1852967 : Blo 798342 1852967 := bstep (se 1 (by rfl) ⟨1389725, by rfl⟩ : syracuseStep 1852967 = 2779451) B2779451
theorem B1197647 : Blo 798342 1197647 := bstep (se 1 (by rfl) ⟨898235, by rfl⟩ : syracuseStep 1197647 = 1796471) B1796471
theorem B3851873 : Blo 798342 3851873 := bstep (se 2 (by rfl) ⟨1444452, by rfl⟩ : syracuseStep 3851873 = 2888905) B2888905
theorem B3032761 : Blo 798342 3032761 := bstep (se 2 (by rfl) ⟨1137285, by rfl⟩ : syracuseStep 3032761 = 2274571) B2274571
theorem B1197767 : Blo 798342 1197767 := bstep (se 1 (by rfl) ⟨898325, by rfl⟩ : syracuseStep 1197767 = 1796651) B1796651
theorem B1197929 : Blo 798342 1197929 := bstep (se 2 (by rfl) ⟨449223, by rfl⟩ : syracuseStep 1197929 = 898447) B898447
theorem B24692633 : Blo 798342 24692633 := bstep (se 2 (by rfl) ⟨9259737, by rfl⟩ : syracuseStep 24692633 = 18519475) B18519475
theorem B3426209 : Blo 798342 3426209 := bstep (se 2 (by rfl) ⟨1284828, by rfl⟩ : syracuseStep 3426209 = 2569657) B2569657
theorem B1198007 : Blo 798342 1198007 := bstep (se 1 (by rfl) ⟨898505, by rfl⟩ : syracuseStep 1198007 = 1797011) B1797011
theorem B1198043 : Blo 798342 1198043 := bstep (se 1 (by rfl) ⟨898532, by rfl⟩ : syracuseStep 1198043 = 1797065) B1797065
theorem B2705561 : Blo 798342 2705561 := bstep (se 2 (by rfl) ⟨1014585, by rfl⟩ : syracuseStep 2705561 = 2029171) B2029171
theorem B1198511 : Blo 798342 1198511 := bstep (se 1 (by rfl) ⟨898883, by rfl⟩ : syracuseStep 1198511 = 1797767) B1797767
theorem B1198601 : Blo 798342 1198601 := bstep (se 2 (by rfl) ⟨449475, by rfl⟩ : syracuseStep 1198601 = 898951) B898951
theorem B1198631 : Blo 798342 1198631 := bstep (se 1 (by rfl) ⟨898973, by rfl⟩ : syracuseStep 1198631 = 1797947) B1797947
theorem B1198715 : Blo 798342 1198715 := bstep (se 1 (by rfl) ⟨899036, by rfl⟩ : syracuseStep 1198715 = 1798073) B1798073
theorem B1198841 : Blo 798342 1198841 := bstep (se 2 (by rfl) ⟨449565, by rfl⟩ : syracuseStep 1198841 = 899131) B899131
theorem B1198943 : Blo 798342 1198943 := bstep (se 1 (by rfl) ⟨899207, by rfl⟩ : syracuseStep 1198943 = 1798415) B1798415
theorem B1198955 : Blo 798342 1198955 := bstep (se 1 (by rfl) ⟨899216, by rfl⟩ : syracuseStep 1198955 = 1798433) B1798433
theorem B15420401 : Blo 798342 15420401 := bstep (se 2 (by rfl) ⟨5782650, by rfl⟩ : syracuseStep 15420401 = 11565301) B11565301
theorem B1199183 : Blo 798342 1199183 := bstep (se 1 (by rfl) ⟨899387, by rfl⟩ : syracuseStep 1199183 = 1798775) B1798775
theorem B4049999 : Blo 798342 4049999 := bstep (se 1 (by rfl) ⟨3037499, by rfl⟩ : syracuseStep 4049999 = 6074999) B6074999
theorem B1199303 : Blo 798342 1199303 := bstep (se 1 (by rfl) ⟨899477, by rfl⟩ : syracuseStep 1199303 = 1798955) B1798955
theorem B2706749 : Blo 798342 2706749 := bstep (se 3 (by rfl) ⟨507515, by rfl⟩ : syracuseStep 2706749 = 1015031) B1015031
theorem B1199465 : Blo 798342 1199465 := bstep (se 2 (by rfl) ⟨449799, by rfl⟩ : syracuseStep 1199465 = 899599) B899599
theorem B3034493 : Blo 798342 3034493 := bstep (se 3 (by rfl) ⟨568967, by rfl⟩ : syracuseStep 3034493 = 1137935) B1137935
theorem B1199543 : Blo 798342 1199543 := bstep (se 1 (by rfl) ⟨899657, by rfl⟩ : syracuseStep 1199543 = 1799315) B1799315
theorem B1199579 : Blo 798342 1199579 := bstep (se 1 (by rfl) ⟨899684, by rfl⟩ : syracuseStep 1199579 = 1799369) B1799369
theorem B2674201 : Blo 798342 2674201 := bstep (se 2 (by rfl) ⟨1002825, by rfl⟩ : syracuseStep 2674201 = 2005651) B2005651
theorem B2739851 : Blo 798342 2739851 := bstep (se 1 (by rfl) ⟨2054888, by rfl⟩ : syracuseStep 2739851 = 4109777) B4109777
theorem B4050647 : Blo 798342 4050647 := bstep (se 1 (by rfl) ⟨3037985, by rfl⟩ : syracuseStep 4050647 = 6075971) B6075971
theorem B55529333 : Blo 798342 55529333 := bstep (se 5 (by rfl) ⟨2602937, by rfl⟩ : syracuseStep 55529333 = 5205875) B5205875
theorem B1200047 : Blo 798342 1200047 := bstep (se 1 (by rfl) ⟨900035, by rfl⟩ : syracuseStep 1200047 = 1800071) B1800071
theorem B1200137 : Blo 798342 1200137 := bstep (se 2 (by rfl) ⟨450051, by rfl⟩ : syracuseStep 1200137 = 900103) B900103
theorem B1200167 : Blo 798342 1200167 := bstep (se 1 (by rfl) ⟨900125, by rfl⟩ : syracuseStep 1200167 = 1800251) B1800251
theorem B1200251 : Blo 798342 1200251 := bstep (se 1 (by rfl) ⟨900188, by rfl⟩ : syracuseStep 1200251 = 1800377) B1800377
theorem B2707613 : Blo 798342 2707613 := bstep (se 3 (by rfl) ⟨507677, by rfl⟩ : syracuseStep 2707613 = 1015355) B1015355
theorem B1200377 : Blo 798342 1200377 := bstep (se 2 (by rfl) ⟨450141, by rfl⟩ : syracuseStep 1200377 = 900283) B900283
theorem B1200479 : Blo 798342 1200479 := bstep (se 1 (by rfl) ⟨900359, by rfl⟩ : syracuseStep 1200479 = 1800719) B1800719
theorem B1200491 : Blo 798342 1200491 := bstep (se 1 (by rfl) ⟨900368, by rfl⟩ : syracuseStep 1200491 = 1800737) B1800737
theorem B1200719 : Blo 798342 1200719 := bstep (se 1 (by rfl) ⟨900539, by rfl⟩ : syracuseStep 1200719 = 1801079) B1801079
theorem B1200839 : Blo 798342 1200839 := bstep (se 1 (by rfl) ⟨900629, by rfl⟩ : syracuseStep 1200839 = 1801259) B1801259
theorem B1201001 : Blo 798342 1201001 := bstep (se 2 (by rfl) ⟨450375, by rfl⟩ : syracuseStep 1201001 = 900751) B900751
theorem B1201079 : Blo 798342 1201079 := bstep (se 1 (by rfl) ⟨900809, by rfl⟩ : syracuseStep 1201079 = 1801619) B1801619
theorem B1201115 : Blo 798342 1201115 := bstep (se 1 (by rfl) ⟨900836, by rfl⟩ : syracuseStep 1201115 = 1801673) B1801673
theorem B3855563 : Blo 798342 3855563 := bstep (se 1 (by rfl) ⟨2891672, by rfl⟩ : syracuseStep 3855563 = 5783345) B5783345
theorem B10245365 : Blo 798342 10245365 := bstep (se 5 (by rfl) ⟨480251, by rfl⟩ : syracuseStep 10245365 = 960503) B960503
theorem B1201583 : Blo 798342 1201583 := bstep (se 1 (by rfl) ⟨901187, by rfl⟩ : syracuseStep 1201583 = 1802375) B1802375
theorem B3036635 : Blo 798342 3036635 := bstep (se 1 (by rfl) ⟨2277476, by rfl⟩ : syracuseStep 3036635 = 4554953) B4554953
theorem B1201673 : Blo 798342 1201673 := bstep (se 2 (by rfl) ⟨450627, by rfl⟩ : syracuseStep 1201673 = 901255) B901255
theorem B2020889 : Blo 798342 2020889 := bstep (se 2 (by rfl) ⟨757833, by rfl⟩ : syracuseStep 2020889 = 1515667) B1515667
theorem B1201703 : Blo 798342 1201703 := bstep (se 1 (by rfl) ⟨901277, by rfl⟩ : syracuseStep 1201703 = 1802555) B1802555
theorem B12342881 : Blo 798342 12342881 := bstep (se 2 (by rfl) ⟨4628580, by rfl⟩ : syracuseStep 12342881 = 9257161) B9257161
theorem B1201787 : Blo 798342 1201787 := bstep (se 1 (by rfl) ⟨901340, by rfl⟩ : syracuseStep 1201787 = 1802681) B1802681
theorem B1201913 : Blo 798342 1201913 := bstep (se 2 (by rfl) ⟨450717, by rfl⟩ : syracuseStep 1201913 = 901435) B901435
theorem B1202015 : Blo 798342 1202015 := bstep (se 1 (by rfl) ⟨901511, by rfl⟩ : syracuseStep 1202015 = 1803023) B1803023
theorem B1202027 : Blo 798342 1202027 := bstep (se 1 (by rfl) ⟨901520, by rfl⟩ : syracuseStep 1202027 = 1803041) B1803041
theorem B2021395 : Blo 798342 2021395 := bstep (se 1 (by rfl) ⟨1516046, by rfl⟩ : syracuseStep 2021395 = 3032093) B3032093
theorem B1202255 : Blo 798342 1202255 := bstep (se 1 (by rfl) ⟨901691, by rfl⟩ : syracuseStep 1202255 = 1803383) B1803383
theorem B1202375 : Blo 798342 1202375 := bstep (se 1 (by rfl) ⟨901781, by rfl⟩ : syracuseStep 1202375 = 1803563) B1803563
theorem B5200139 : Blo 798342 5200139 := bstep (se 1 (by rfl) ⟨3900104, by rfl⟩ : syracuseStep 5200139 = 7800209) B7800209
theorem B1202537 : Blo 798342 1202537 := bstep (se 2 (by rfl) ⟨450951, by rfl⟩ : syracuseStep 1202537 = 901903) B901903
theorem B1202615 : Blo 798342 1202615 := bstep (se 1 (by rfl) ⟨901961, by rfl⟩ : syracuseStep 1202615 = 1803923) B1803923
theorem B1137115 : Blo 798342 1137115 := bstep (se 1 (by rfl) ⟨852836, by rfl⟩ : syracuseStep 1137115 = 1705673) B1705673
theorem B1202651 : Blo 798342 1202651 := bstep (se 1 (by rfl) ⟨901988, by rfl⟩ : syracuseStep 1202651 = 1803977) B1803977
theorem B4053563 : Blo 798342 4053563 := bstep (se 1 (by rfl) ⟨3040172, by rfl⟩ : syracuseStep 4053563 = 6080345) B6080345
theorem B3037895 : Blo 798342 3037895 := bstep (se 1 (by rfl) ⟨2278421, by rfl⟩ : syracuseStep 3037895 = 4556843) B4556843
theorem B1465031 : Blo 798342 1465031 := bstep (se 1 (by rfl) ⟨1098773, by rfl⟩ : syracuseStep 1465031 = 2197547) B2197547
theorem B1366777 : Blo 798342 1366777 := bstep (se 2 (by rfl) ⟨512541, by rfl⟩ : syracuseStep 1366777 = 1025083) B1025083
theorem B5757803 : Blo 798342 5757803 := bstep (se 1 (by rfl) ⟨4318352, by rfl⟩ : syracuseStep 5757803 = 8636705) B8636705
theorem B1203119 : Blo 798342 1203119 := bstep (se 1 (by rfl) ⟨902339, by rfl⟩ : syracuseStep 1203119 = 1804679) B1804679
theorem B1137673 : Blo 798342 1137673 := bstep (se 2 (by rfl) ⟨426627, by rfl⟩ : syracuseStep 1137673 = 853255) B853255
theorem B1203209 : Blo 798342 1203209 := bstep (se 2 (by rfl) ⟨451203, by rfl⟩ : syracuseStep 1203209 = 902407) B902407
theorem B1203239 : Blo 798342 1203239 := bstep (se 1 (by rfl) ⟨902429, by rfl⟩ : syracuseStep 1203239 = 1804859) B1804859
theorem B2022479 : Blo 798342 2022479 := bstep (se 1 (by rfl) ⟨1516859, by rfl⟩ : syracuseStep 2022479 = 3033719) B3033719
theorem B1203323 : Blo 798342 1203323 := bstep (se 1 (by rfl) ⟨902492, by rfl⟩ : syracuseStep 1203323 = 1804985) B1804985
theorem B4054211 : Blo 798342 4054211 := bstep (se 1 (by rfl) ⟨3040658, by rfl⟩ : syracuseStep 4054211 = 6081317) B6081317
theorem B1203449 : Blo 798342 1203449 := bstep (se 2 (by rfl) ⟨451293, by rfl⟩ : syracuseStep 1203449 = 902587) B902587
theorem B11525399 : Blo 798342 11525399 := bstep (se 1 (by rfl) ⟨8644049, by rfl⟩ : syracuseStep 11525399 = 17288099) B17288099
theorem B3038593 : Blo 798342 3038593 := bstep (se 2 (by rfl) ⟨1139472, by rfl⟩ : syracuseStep 3038593 = 2278945) B2278945
theorem B23092775 : Blo 798342 23092775 := bstep (se 1 (by rfl) ⟨17319581, by rfl⟩ : syracuseStep 23092775 = 34639163) B34639163
theorem B3038867 : Blo 798342 3038867 := bstep (se 1 (by rfl) ⟨2279150, by rfl⟩ : syracuseStep 3038867 = 4558301) B4558301
theorem B2023127 : Blo 798342 2023127 := bstep (se 1 (by rfl) ⟨1517345, by rfl⟩ : syracuseStep 2023127 = 3034691) B3034691
theorem B1924937 : Blo 798342 1924937 := bstep (se 2 (by rfl) ⟨721851, by rfl⟩ : syracuseStep 1924937 = 1443703) B1443703
theorem B6086663 : Blo 798342 6086663 := bstep (se 1 (by rfl) ⟨4564997, by rfl⟩ : syracuseStep 6086663 = 9129995) B9129995
theorem B2023481 : Blo 798342 2023481 := bstep (se 2 (by rfl) ⟨758805, by rfl⟩ : syracuseStep 2023481 = 1517611) B1517611
theorem B18473285 : Blo 798342 18473285 := bstep (se 4 (by rfl) ⟨1731870, by rfl⟩ : syracuseStep 18473285 = 3463741) B3463741
theorem B6087149 : Blo 798342 6087149 := bstep (se 3 (by rfl) ⟨1141340, by rfl⟩ : syracuseStep 6087149 = 2282681) B2282681
theorem B2744819 : Blo 798342 2744819 := bstep (se 1 (by rfl) ⟨2058614, by rfl⟩ : syracuseStep 2744819 = 4117229) B4117229
theorem B2777723 : Blo 798342 2777723 := bstep (se 1 (by rfl) ⟨2083292, by rfl⟩ : syracuseStep 2777723 = 4166585) B4166585
theorem B4547663 : Blo 798342 4547663 := bstep (se 1 (by rfl) ⟨3410747, by rfl⟩ : syracuseStep 4547663 = 6821495) B6821495
theorem B3040523 : Blo 798342 3040523 := bstep (se 1 (by rfl) ⟨2280392, by rfl⟩ : syracuseStep 3040523 = 4560785) B4560785
theorem B1140151 : Blo 798342 1140151 := bstep (se 1 (by rfl) ⟨855113, by rfl⟩ : syracuseStep 1140151 = 1710227) B1710227
theorem B5137931 : Blo 798342 5137931 := bstep (se 1 (by rfl) ⟨3853448, by rfl⟩ : syracuseStep 5137931 = 7706897) B7706897
theorem B4155095 : Blo 798342 4155095 := bstep (se 1 (by rfl) ⟨3116321, by rfl⟩ : syracuseStep 4155095 = 6232643) B6232643
theorem B6153943 : Blo 798342 6153943 := bstep (se 1 (by rfl) ⟨4615457, by rfl⟩ : syracuseStep 6153943 = 9230915) B9230915
theorem B2877371 : Blo 798342 2877371 := bstep (se 1 (by rfl) ⟨2158028, by rfl⟩ : syracuseStep 2877371 = 4316057) B4316057
theorem B3467279 : Blo 798342 3467279 := bstep (se 1 (by rfl) ⟨2600459, by rfl⟩ : syracuseStep 3467279 = 5200919) B5200919
theorem B2025719 : Blo 798342 2025719 := bstep (se 1 (by rfl) ⟨1519289, by rfl⟩ : syracuseStep 2025719 = 3038579) B3038579
theorem B6089093 : Blo 798342 6089093 := bstep (se 4 (by rfl) ⟨570852, by rfl⟩ : syracuseStep 6089093 = 1141705) B1141705
theorem B1796705 : Blo 798342 1796705 := bstep (se 2 (by rfl) ⟨673764, by rfl⟩ : syracuseStep 1796705 = 1347529) B1347529
theorem B3041981 : Blo 798342 3041981 := bstep (se 3 (by rfl) ⟨570371, by rfl⟩ : syracuseStep 3041981 = 1140743) B1140743
theorem B1141609 : Blo 798342 1141609 := bstep (se 2 (by rfl) ⟨428103, by rfl⟩ : syracuseStep 1141609 = 856207) B856207
theorem B6089579 : Blo 798342 6089579 := bstep (se 1 (by rfl) ⟨4567184, by rfl⟩ : syracuseStep 6089579 = 9134369) B9134369
theorem B1797047 : Blo 798342 1797047 := bstep (se 1 (by rfl) ⟨1347785, by rfl⟩ : syracuseStep 1797047 = 2695571) B2695571
theorem B6843365 : Blo 798342 6843365 := bstep (se 4 (by rfl) ⟨641565, by rfl⟩ : syracuseStep 6843365 = 1283131) B1283131
theorem B4550053 : Blo 798342 4550053 := bstep (se 4 (by rfl) ⟨426567, by rfl⟩ : syracuseStep 4550053 = 853135) B853135
theorem B1797641 : Blo 798342 1797641 := bstep (se 2 (by rfl) ⟨674115, by rfl⟩ : syracuseStep 1797641 = 1348231) B1348231
theorem B4058747 : Blo 798342 4058747 := bstep (se 1 (by rfl) ⟨3044060, by rfl⟩ : syracuseStep 4058747 = 6088121) B6088121
theorem B2027207 : Blo 798342 2027207 := bstep (se 1 (by rfl) ⟨1520405, by rfl⟩ : syracuseStep 2027207 = 3040811) B3040811
theorem B4320989 : Blo 798342 4320989 := bstep (se 3 (by rfl) ⟨810185, by rfl⟩ : syracuseStep 4320989 = 1620371) B1620371
theorem B1797983 : Blo 798342 1797983 := bstep (se 1 (by rfl) ⟨1348487, by rfl⟩ : syracuseStep 1797983 = 2696975) B2696975
theorem B1798163 : Blo 798342 1798163 := bstep (se 1 (by rfl) ⟨1348622, by rfl⟩ : syracuseStep 1798163 = 2697245) B2697245
theorem B1011791 : Blo 798342 1011791 := bstep (se 1 (by rfl) ⟨758843, by rfl⟩ : syracuseStep 1011791 = 1517687) B1517687
theorem B1798505 : Blo 798342 1798505 := bstep (se 2 (by rfl) ⟨674439, by rfl⟩ : syracuseStep 1798505 = 1348879) B1348879
theorem B3043727 : Blo 798342 3043727 := bstep (se 1 (by rfl) ⟨2282795, by rfl⟩ : syracuseStep 3043727 = 4565591) B4565591
theorem B3076589 : Blo 798342 3076589 := bstep (se 3 (by rfl) ⟨576860, by rfl⟩ : syracuseStep 3076589 = 1153721) B1153721
theorem B5763565 : Blo 798342 5763565 := bstep (se 3 (by rfl) ⟨1080668, by rfl⟩ : syracuseStep 5763565 = 2161337) B2161337
theorem B3240481 : Blo 798342 3240481 := bstep (se 2 (by rfl) ⟨1215180, by rfl⟩ : syracuseStep 3240481 = 2430361) B2430361
theorem B2880139 : Blo 798342 2880139 := bstep (se 1 (by rfl) ⟨2160104, by rfl⟩ : syracuseStep 2880139 = 4320209) B4320209
theorem B13005521 : Blo 798342 13005521 := bstep (se 2 (by rfl) ⟨4877070, by rfl⟩ : syracuseStep 13005521 = 9754141) B9754141
theorem B6091523 : Blo 798342 6091523 := bstep (se 1 (by rfl) ⟨4568642, by rfl⟩ : syracuseStep 6091523 = 9137285) B9137285
theorem B2028361 : Blo 798342 2028361 := bstep (se 2 (by rfl) ⟨760635, by rfl⟩ : syracuseStep 2028361 = 1521271) B1521271
theorem B1799099 : Blo 798342 1799099 := bstep (se 1 (by rfl) ⟨1349324, by rfl⟩ : syracuseStep 1799099 = 2698649) B2698649
theorem B1799225 : Blo 798342 1799225 := bstep (se 2 (by rfl) ⟨674709, by rfl⟩ : syracuseStep 1799225 = 1349419) B1349419
theorem B1537103 : Blo 798342 1537103 := bstep (se 1 (by rfl) ⟨1152827, by rfl⟩ : syracuseStep 1537103 = 2305655) B2305655
theorem B1013087 : Blo 798342 1013087 := bstep (se 1 (by rfl) ⟨759815, by rfl⟩ : syracuseStep 1013087 = 1519631) B1519631
theorem B1799567 : Blo 798342 1799567 := bstep (se 1 (by rfl) ⟨1349675, by rfl⟩ : syracuseStep 1799567 = 2699351) B2699351
theorem B4322803 : Blo 798342 4322803 := bstep (se 1 (by rfl) ⟨3242102, by rfl⟩ : syracuseStep 4322803 = 6484205) B6484205
theorem B3044897 : Blo 798342 3044897 := bstep (se 2 (by rfl) ⟨1141836, by rfl⟩ : syracuseStep 3044897 = 2283673) B2283673
theorem B10254023 : Blo 798342 10254023 := bstep (se 1 (by rfl) ⟨7690517, by rfl⟩ : syracuseStep 10254023 = 15381035) B15381035
theorem B14612167 : Blo 798342 14612167 := bstep (se 1 (by rfl) ⟨10959125, by rfl⟩ : syracuseStep 14612167 = 21918251) B21918251
theorem B1799891 : Blo 798342 1799891 := bstep (se 1 (by rfl) ⟨1349918, by rfl⟩ : syracuseStep 1799891 = 2699837) B2699837
theorem B3045215 : Blo 798342 3045215 := bstep (se 1 (by rfl) ⟨2283911, by rfl⟩ : syracuseStep 3045215 = 4567823) B4567823
theorem B2029495 : Blo 798342 2029495 := bstep (se 1 (by rfl) ⟨1522121, by rfl⟩ : syracuseStep 2029495 = 3044243) B3044243
theorem B3045383 : Blo 798342 3045383 := bstep (se 1 (by rfl) ⟨2284037, by rfl⟩ : syracuseStep 3045383 = 4568075) B4568075
theorem B9730205 : Blo 798342 9730205 := bstep (se 3 (by rfl) ⟨1824413, by rfl⟩ : syracuseStep 9730205 = 3648827) B3648827
theorem B3078391 : Blo 798342 3078391 := bstep (se 1 (by rfl) ⟨2308793, by rfl⟩ : syracuseStep 3078391 = 4617587) B4617587
theorem B4061501 : Blo 798342 4061501 := bstep (se 3 (by rfl) ⟨761531, by rfl⟩ : syracuseStep 4061501 = 1523063) B1523063
theorem B3045869 : Blo 798342 3045869 := bstep (se 3 (by rfl) ⟨571100, by rfl⟩ : syracuseStep 3045869 = 1142201) B1142201
theorem B1800827 : Blo 798342 1800827 := bstep (se 1 (by rfl) ⟨1350620, by rfl⟩ : syracuseStep 1800827 = 2701241) B2701241
theorem B1800953 : Blo 798342 1800953 := bstep (se 2 (by rfl) ⟨675357, by rfl⟩ : syracuseStep 1800953 = 1350715) B1350715
theorem B3046187 : Blo 798342 3046187 := bstep (se 1 (by rfl) ⟨2284640, by rfl⟩ : syracuseStep 3046187 = 4569281) B4569281
theorem B1801223 : Blo 798342 1801223 := bstep (se 1 (by rfl) ⟨1350917, by rfl⟩ : syracuseStep 1801223 = 2701835) B2701835
theorem B1801295 : Blo 798342 1801295 := bstep (se 1 (by rfl) ⟨1350971, by rfl⟩ : syracuseStep 1801295 = 2701943) B2701943
theorem B21855511 : Blo 798342 21855511 := bstep (se 1 (by rfl) ⟨16391633, by rfl⟩ : syracuseStep 21855511 = 32783267) B32783267
theorem B1801691 : Blo 798342 1801691 := bstep (se 1 (by rfl) ⟨1351268, by rfl⟩ : syracuseStep 1801691 = 2702537) B2702537
theorem B7700359 : Blo 798342 7700359 := bstep (se 1 (by rfl) ⟨5775269, by rfl⟩ : syracuseStep 7700359 = 11550539) B11550539
theorem B1802159 : Blo 798342 1802159 := bstep (se 1 (by rfl) ⟨1351619, by rfl⟩ : syracuseStep 1802159 = 2703239) B2703239
theorem B1802249 : Blo 798342 1802249 := bstep (se 2 (by rfl) ⟨675843, by rfl⟩ : syracuseStep 1802249 = 1351687) B1351687
theorem B1081631 : Blo 798342 1081631 := bstep (se 1 (by rfl) ⟨811223, by rfl⟩ : syracuseStep 1081631 = 1622447) B1622447
theorem B1802663 : Blo 798342 1802663 := bstep (se 1 (by rfl) ⟨1351997, by rfl⟩ : syracuseStep 1802663 = 2703995) B2703995
theorem B1802771 : Blo 798342 1802771 := bstep (se 1 (by rfl) ⟨1352078, by rfl⟩ : syracuseStep 1802771 = 2704157) B2704157
theorem B1802825 : Blo 798342 1802825 := bstep (se 2 (by rfl) ⟨676059, by rfl⟩ : syracuseStep 1802825 = 1352119) B1352119
theorem B12976841 : Blo 798342 12976841 := bstep (se 2 (by rfl) ⟨4866315, by rfl⟩ : syracuseStep 12976841 = 9732631) B9732631
theorem B15401947 : Blo 798342 15401947 := bstep (se 1 (by rfl) ⟨11551460, by rfl⟩ : syracuseStep 15401947 = 23102921) B23102921
theorem B1803239 : Blo 798342 1803239 := bstep (se 1 (by rfl) ⟨1352429, by rfl⟩ : syracuseStep 1803239 = 2704859) B2704859
theorem B6489395 : Blo 798342 6489395 := bstep (se 1 (by rfl) ⟨4867046, by rfl⟩ : syracuseStep 6489395 = 9734093) B9734093
theorem B1803617 : Blo 798342 1803617 := bstep (se 2 (by rfl) ⟨676356, by rfl⟩ : syracuseStep 1803617 = 1352713) B1352713
theorem B32867693 : Blo 798342 32867693 := bstep (se 3 (by rfl) ⟨6162692, by rfl⟩ : syracuseStep 32867693 = 12325385) B12325385
theorem B2164105 : Blo 798342 2164105 := bstep (se 2 (by rfl) ⟨811539, by rfl⟩ : syracuseStep 2164105 = 1623079) B1623079
theorem B1803707 : Blo 798342 1803707 := bstep (se 1 (by rfl) ⟨1352780, by rfl⟩ : syracuseStep 1803707 = 2705561) B2705561
theorem B1803833 : Blo 798342 1803833 := bstep (se 2 (by rfl) ⟨676437, by rfl⟩ : syracuseStep 1803833 = 1352875) B1352875
theorem B1804499 : Blo 798342 1804499 := bstep (se 1 (by rfl) ⟨1353374, by rfl⟩ : syracuseStep 1804499 = 2706749) B2706749
theorem B1804553 : Blo 798342 1804553 := bstep (se 2 (by rfl) ⟨676707, by rfl⟩ : syracuseStep 1804553 = 1353415) B1353415
theorem B3410201 : Blo 798342 3410201 := bstep (se 2 (by rfl) ⟨1278825, by rfl⟩ : syracuseStep 3410201 = 2557651) B2557651
theorem B1804769 : Blo 798342 1804769 := bstep (se 2 (by rfl) ⟨676788, by rfl⟩ : syracuseStep 1804769 = 1353577) B1353577
theorem B1805075 : Blo 798342 1805075 := bstep (se 1 (by rfl) ⟨1353806, by rfl⟩ : syracuseStep 1805075 = 2707613) B2707613
theorem B1707151 : Blo 798342 1707151 := bstep (se 1 (by rfl) ⟨1280363, by rfl⟩ : syracuseStep 1707151 = 2560727) B2560727
theorem B2886943 : Blo 798342 2886943 := bstep (se 1 (by rfl) ⟨2165207, by rfl⟩ : syracuseStep 2886943 = 4330415) B4330415
theorem B1445159 : Blo 798342 1445159 := bstep (se 1 (by rfl) ⟨1083869, by rfl⟩ : syracuseStep 1445159 = 2167739) B2167739
theorem B2166203 : Blo 798342 2166203 := bstep (se 1 (by rfl) ⟨1624652, by rfl⟩ : syracuseStep 2166203 = 3249305) B3249305
theorem B2166355 : Blo 798342 2166355 := bstep (se 1 (by rfl) ⟨1624766, by rfl⟩ : syracuseStep 2166355 = 3249533) B3249533
theorem B1347259 : Blo 798342 1347259 := bstep (se 1 (by rfl) ⟨1010444, by rfl⟩ : syracuseStep 1347259 = 2020889) B2020889
theorem B855775 : Blo 798342 855775 := bstep (se 1 (by rfl) ⟨641831, by rfl⟩ : syracuseStep 855775 = 1283663) B1283663
theorem B8228587 : Blo 798342 8228587 := bstep (se 1 (by rfl) ⟨6171440, by rfl⟩ : syracuseStep 8228587 = 12342881) B12342881
theorem B2166583 : Blo 798342 2166583 := bstep (se 1 (by rfl) ⟨1624937, by rfl⟩ : syracuseStep 2166583 = 3249875) B3249875
theorem B3411841 : Blo 798342 3411841 := bstep (se 2 (by rfl) ⟨1279440, by rfl⟩ : syracuseStep 3411841 = 2558881) B2558881
theorem B7704665 : Blo 798342 7704665 := bstep (se 2 (by rfl) ⟨2889249, by rfl⟩ : syracuseStep 7704665 = 5778499) B5778499
theorem B6066737 : Blo 798342 6066737 := bstep (se 2 (by rfl) ⟨2275026, by rfl⟩ : syracuseStep 6066737 = 4550053) B4550053
theorem B11080253 : Blo 798342 11080253 := bstep (se 3 (by rfl) ⟨2077547, by rfl⟩ : syracuseStep 11080253 = 4155095) B4155095
theorem B3838535 : Blo 798342 3838535 := bstep (se 1 (by rfl) ⟨2878901, by rfl⟩ : syracuseStep 3838535 = 5757803) B5757803
theorem B1348319 : Blo 798342 1348319 := bstep (se 1 (by rfl) ⟨1011239, by rfl⟩ : syracuseStep 1348319 = 2022479) B2022479
theorem B1348751 : Blo 798342 1348751 := bstep (se 1 (by rfl) ⟨1011563, by rfl⟩ : syracuseStep 1348751 = 2023127) B2023127
theorem B1283291 : Blo 798342 1283291 := bstep (se 1 (by rfl) ⟨962468, by rfl⟩ : syracuseStep 1283291 = 1924937) B1924937
theorem B1348987 : Blo 798342 1348987 := bstep (se 1 (by rfl) ⟨1011740, by rfl⟩ : syracuseStep 1348987 = 2023481) B2023481
theorem B6166327 : Blo 798342 6166327 := bstep (se 1 (by rfl) ⟨4624745, by rfl⟩ : syracuseStep 6166327 = 9249491) B9249491
theorem B13867037 : Blo 798342 13867037 := bstep (se 3 (by rfl) ⟨2600069, by rfl⟩ : syracuseStep 13867037 = 5200139) B5200139
theorem B3840185 : Blo 798342 3840185 := bstep (se 2 (by rfl) ⟨1440069, by rfl⟩ : syracuseStep 3840185 = 2880139) B2880139
theorem B1710713 : Blo 798342 1710713 := bstep (se 2 (by rfl) ⟨641517, by rfl⟩ : syracuseStep 1710713 = 1283035) B1283035
theorem B5118659 : Blo 798342 5118659 := bstep (se 1 (by rfl) ⟨3838994, by rfl⟩ : syracuseStep 5118659 = 7677989) B7677989
theorem B116562725 : Blo 798342 116562725 := bstep (se 4 (by rfl) ⟨10927755, by rfl⟩ : syracuseStep 116562725 = 21855511) B21855511
theorem B1350479 : Blo 798342 1350479 := bstep (se 1 (by rfl) ⟨1012859, by rfl⟩ : syracuseStep 1350479 = 2025719) B2025719
theorem B3906749 : Blo 798342 3906749 := bstep (se 3 (by rfl) ⟨732515, by rfl⟩ : syracuseStep 3906749 = 1465031) B1465031
theorem B4562243 : Blo 798342 4562243 := bstep (se 1 (by rfl) ⟨3421682, by rfl⟩ : syracuseStep 4562243 = 6843365) B6843365
theorem B2694599 : Blo 798342 2694599 := bstep (se 1 (by rfl) ⟨2020949, by rfl⟩ : syracuseStep 2694599 = 4041899) B4041899
theorem B7020179 : Blo 798342 7020179 := bstep (se 1 (by rfl) ⟨5265134, by rfl⟩ : syracuseStep 7020179 = 10530269) B10530269
theorem B2694923 : Blo 798342 2694923 := bstep (se 1 (by rfl) ⟨2021192, by rfl⟩ : syracuseStep 2694923 = 4042385) B4042385
theorem B1351471 : Blo 798342 1351471 := bstep (se 1 (by rfl) ⟨1013603, by rfl⟩ : syracuseStep 1351471 = 2027207) B2027207
theorem B2695193 : Blo 798342 2695193 := bstep (se 2 (by rfl) ⟨1010697, by rfl⟩ : syracuseStep 2695193 = 2021395) B2021395
theorem B4104521 : Blo 798342 4104521 := bstep (se 2 (by rfl) ⟨1539195, by rfl⟩ : syracuseStep 4104521 = 3078391) B3078391
theorem B3416539 : Blo 798342 3416539 := bstep (se 1 (by rfl) ⟨2562404, by rfl⟩ : syracuseStep 3416539 = 5124809) B5124809
theorem B1516153 : Blo 798342 1516153 := bstep (se 2 (by rfl) ⟨568557, by rfl⟩ : syracuseStep 1516153 = 1137115) B1137115
theorem B5120657 : Blo 798342 5120657 := bstep (se 2 (by rfl) ⟨1920246, by rfl⟩ : syracuseStep 5120657 = 3840493) B3840493
theorem B1024735 : Blo 798342 1024735 := bstep (se 1 (by rfl) ⟨768551, by rfl⟩ : syracuseStep 1024735 = 1537103) B1537103
theorem B2106283 : Blo 798342 2106283 := bstep (se 1 (by rfl) ⟨1579712, by rfl⟩ : syracuseStep 2106283 = 3159425) B3159425
theorem B2696435 : Blo 798342 2696435 := bstep (se 1 (by rfl) ⟨2022326, by rfl⟩ : syracuseStep 2696435 = 4044653) B4044653
theorem B2696543 : Blo 798342 2696543 := bstep (se 1 (by rfl) ⟨2022407, by rfl⟩ : syracuseStep 2696543 = 4044815) B4044815
theorem B1516897 : Blo 798342 1516897 := bstep (se 2 (by rfl) ⟨568836, by rfl⟩ : syracuseStep 1516897 = 1137673) B1137673
theorem B7284077 : Blo 798342 7284077 := bstep (se 3 (by rfl) ⟨1365764, by rfl⟩ : syracuseStep 7284077 = 2731529) B2731529
theorem B3286865 : Blo 798342 3286865 := bstep (se 2 (by rfl) ⟨1232574, by rfl⟩ : syracuseStep 3286865 = 2465149) B2465149
theorem B43788113 : Blo 798342 43788113 := bstep (se 2 (by rfl) ⟨16420542, by rfl⟩ : syracuseStep 43788113 = 32841085) B32841085
theorem B3418145 : Blo 798342 3418145 := bstep (se 2 (by rfl) ⟨1281804, by rfl⟩ : syracuseStep 3418145 = 2563609) B2563609
theorem B1517915 : Blo 798342 1517915 := bstep (se 1 (by rfl) ⟨1138436, by rfl⟩ : syracuseStep 1517915 = 2276873) B2276873
theorem B10267145 : Blo 798342 10267145 := bstep (se 2 (by rfl) ⟨3850179, by rfl⟩ : syracuseStep 10267145 = 7700359) B7700359
theorem B1518355 : Blo 798342 1518355 := bstep (se 1 (by rfl) ⟨1138766, by rfl⟩ : syracuseStep 1518355 = 2277533) B2277533
theorem B2698109 : Blo 798342 2698109 := bstep (se 3 (by rfl) ⟨505895, by rfl⟩ : syracuseStep 2698109 = 1011791) B1011791
theorem B1518583 : Blo 798342 1518583 := bstep (se 1 (by rfl) ⟨1138937, by rfl⟩ : syracuseStep 1518583 = 2277875) B2277875
theorem B2698379 : Blo 798342 2698379 := bstep (se 1 (by rfl) ⟨2023784, by rfl⟩ : syracuseStep 2698379 = 4047569) B4047569
theorem B3845339 : Blo 798342 3845339 := bstep (se 1 (by rfl) ⟨2884004, by rfl⟩ : syracuseStep 3845339 = 5768009) B5768009
theorem B1518887 : Blo 798342 1518887 := bstep (se 1 (by rfl) ⟨1139165, by rfl⟩ : syracuseStep 1518887 = 2278331) B2278331
theorem B49262093 : Blo 798342 49262093 := bstep (se 3 (by rfl) ⟨9236642, by rfl⟩ : syracuseStep 49262093 = 18473285) B18473285
theorem B7319251 : Blo 798342 7319251 := bstep (se 1 (by rfl) ⟨5489438, by rfl⟩ : syracuseStep 7319251 = 10978877) B10978877
theorem B798431 : Blo 798342 798431 := bstep (se 1 (by rfl) ⟨598823, by rfl⟩ : syracuseStep 798431 = 1197647) B1197647
theorem B2567915 : Blo 798342 2567915 := bstep (se 1 (by rfl) ⟨1925936, by rfl⟩ : syracuseStep 2567915 = 3851873) B3851873
theorem B798511 : Blo 798342 798511 := bstep (se 1 (by rfl) ⟨598883, by rfl⟩ : syracuseStep 798511 = 1197767) B1197767
theorem B798619 : Blo 798342 798619 := bstep (se 1 (by rfl) ⟨598964, by rfl⟩ : syracuseStep 798619 = 1197929) B1197929
theorem B16461755 : Blo 798342 16461755 := bstep (se 1 (by rfl) ⟨12346316, by rfl⟩ : syracuseStep 16461755 = 24692633) B24692633
theorem B8204237 : Blo 798342 8204237 := bstep (se 3 (by rfl) ⟨1538294, by rfl⟩ : syracuseStep 8204237 = 3076589) B3076589
theorem B798671 : Blo 798342 798671 := bstep (se 1 (by rfl) ⟨599003, by rfl⟩ : syracuseStep 798671 = 1198007) B1198007
theorem B798695 : Blo 798342 798695 := bstep (se 1 (by rfl) ⟨599021, by rfl⟩ : syracuseStep 798695 = 1198043) B1198043
theorem B799007 : Blo 798342 799007 := bstep (se 1 (by rfl) ⟨599255, by rfl⟩ : syracuseStep 799007 = 1198511) B1198511
theorem B799067 : Blo 798342 799067 := bstep (se 1 (by rfl) ⟨599300, by rfl⟩ : syracuseStep 799067 = 1198601) B1198601
theorem B799087 : Blo 798342 799087 := bstep (se 1 (by rfl) ⟨599315, by rfl⟩ : syracuseStep 799087 = 1198631) B1198631
theorem B799143 : Blo 798342 799143 := bstep (se 1 (by rfl) ⟨599357, by rfl⟩ : syracuseStep 799143 = 1198715) B1198715
theorem B799227 : Blo 798342 799227 := bstep (se 1 (by rfl) ⟨599420, by rfl⟩ : syracuseStep 799227 = 1198841) B1198841
theorem B799295 : Blo 798342 799295 := bstep (se 1 (by rfl) ⟨599471, by rfl⟩ : syracuseStep 799295 = 1198943) B1198943
theorem B799303 : Blo 798342 799303 := bstep (se 1 (by rfl) ⟨599477, by rfl⟩ : syracuseStep 799303 = 1198955) B1198955
theorem B1520201 : Blo 798342 1520201 := bstep (se 2 (by rfl) ⟨570075, by rfl⟩ : syracuseStep 1520201 = 1140151) B1140151
theorem B799455 : Blo 798342 799455 := bstep (se 1 (by rfl) ⟨599591, by rfl⟩ : syracuseStep 799455 = 1199183) B1199183
theorem B2699999 : Blo 798342 2699999 := bstep (se 1 (by rfl) ⟨2024999, by rfl⟩ : syracuseStep 2699999 = 4049999) B4049999
theorem B799535 : Blo 798342 799535 := bstep (se 1 (by rfl) ⟨599651, by rfl⟩ : syracuseStep 799535 = 1199303) B1199303
theorem B799643 : Blo 798342 799643 := bstep (se 1 (by rfl) ⟨599732, by rfl⟩ : syracuseStep 799643 = 1199465) B1199465
theorem B4043681 : Blo 798342 4043681 := bstep (se 2 (by rfl) ⟨1516380, by rfl⟩ : syracuseStep 4043681 = 3032761) B3032761
theorem B8205257 : Blo 798342 8205257 := bstep (se 2 (by rfl) ⟨3076971, by rfl⟩ : syracuseStep 8205257 = 6153943) B6153943
theorem B799695 : Blo 798342 799695 := bstep (se 1 (by rfl) ⟨599771, by rfl⟩ : syracuseStep 799695 = 1199543) B1199543
theorem B799719 : Blo 798342 799719 := bstep (se 1 (by rfl) ⟨599789, by rfl⟩ : syracuseStep 799719 = 1199579) B1199579
theorem B6829181 : Blo 798342 6829181 := bstep (se 3 (by rfl) ⟨1280471, by rfl⟩ : syracuseStep 6829181 = 2560943) B2560943
theorem B2700431 : Blo 798342 2700431 := bstep (se 1 (by rfl) ⟨2025323, by rfl⟩ : syracuseStep 2700431 = 4050647) B4050647
theorem B898267 : Blo 798342 898267 := bstep (se 1 (by rfl) ⟨673700, by rfl⟩ : syracuseStep 898267 = 1347401) B1347401
theorem B800031 : Blo 798342 800031 := bstep (se 1 (by rfl) ⟨600023, by rfl⟩ : syracuseStep 800031 = 1200047) B1200047
theorem B800091 : Blo 798342 800091 := bstep (se 1 (by rfl) ⟨600068, by rfl⟩ : syracuseStep 800091 = 1200137) B1200137
theorem B800111 : Blo 798342 800111 := bstep (se 1 (by rfl) ⟨600083, by rfl⟩ : syracuseStep 800111 = 1200167) B1200167
theorem B800167 : Blo 798342 800167 := bstep (se 1 (by rfl) ⟨600125, by rfl⟩ : syracuseStep 800167 = 1200251) B1200251
theorem B898555 : Blo 798342 898555 := bstep (se 1 (by rfl) ⟨673916, by rfl⟩ : syracuseStep 898555 = 1347833) B1347833
theorem B800251 : Blo 798342 800251 := bstep (se 1 (by rfl) ⟨600188, by rfl⟩ : syracuseStep 800251 = 1200377) B1200377
theorem B800319 : Blo 798342 800319 := bstep (se 1 (by rfl) ⟨600239, by rfl⟩ : syracuseStep 800319 = 1200479) B1200479
theorem B800327 : Blo 798342 800327 := bstep (se 1 (by rfl) ⟨600245, by rfl⟩ : syracuseStep 800327 = 1200491) B1200491
theorem B898735 : Blo 798342 898735 := bstep (se 1 (by rfl) ⟨674051, by rfl⟩ : syracuseStep 898735 = 1348103) B1348103
theorem B800479 : Blo 798342 800479 := bstep (se 1 (by rfl) ⟨600359, by rfl⟩ : syracuseStep 800479 = 1200719) B1200719
theorem B800559 : Blo 798342 800559 := bstep (se 1 (by rfl) ⟨600419, by rfl⟩ : syracuseStep 800559 = 1200839) B1200839
theorem B800667 : Blo 798342 800667 := bstep (se 1 (by rfl) ⟨600500, by rfl⟩ : syracuseStep 800667 = 1201001) B1201001
theorem B899023 : Blo 798342 899023 := bstep (se 1 (by rfl) ⟨674267, by rfl⟩ : syracuseStep 899023 = 1348535) B1348535
theorem B800719 : Blo 798342 800719 := bstep (se 1 (by rfl) ⟨600539, by rfl⟩ : syracuseStep 800719 = 1201079) B1201079
theorem B800743 : Blo 798342 800743 := bstep (se 1 (by rfl) ⟨600557, by rfl⟩ : syracuseStep 800743 = 1201115) B1201115
theorem B7288861 : Blo 798342 7288861 := bstep (se 3 (by rfl) ⟨1366661, by rfl⟩ : syracuseStep 7288861 = 2733323) B2733323
theorem B2570375 : Blo 798342 2570375 := bstep (se 1 (by rfl) ⟨1927781, by rfl⟩ : syracuseStep 2570375 = 3855563) B3855563
theorem B6830243 : Blo 798342 6830243 := bstep (se 1 (by rfl) ⟨5122682, by rfl⟩ : syracuseStep 6830243 = 10245365) B10245365
theorem B2701565 : Blo 798342 2701565 := bstep (se 3 (by rfl) ⟨506543, by rfl⟩ : syracuseStep 2701565 = 1013087) B1013087
theorem B801055 : Blo 798342 801055 := bstep (se 1 (by rfl) ⟨600791, by rfl⟩ : syracuseStep 801055 = 1201583) B1201583
theorem B899419 : Blo 798342 899419 := bstep (se 1 (by rfl) ⟨674564, by rfl⟩ : syracuseStep 899419 = 1349129) B1349129
theorem B801115 : Blo 798342 801115 := bstep (se 1 (by rfl) ⟨600836, by rfl⟩ : syracuseStep 801115 = 1201673) B1201673
theorem B801135 : Blo 798342 801135 := bstep (se 1 (by rfl) ⟨600851, by rfl⟩ : syracuseStep 801135 = 1201703) B1201703
theorem B801191 : Blo 798342 801191 := bstep (se 1 (by rfl) ⟨600893, by rfl⟩ : syracuseStep 801191 = 1201787) B1201787
theorem B5487031 : Blo 798342 5487031 := bstep (se 1 (by rfl) ⟨4115273, by rfl⟩ : syracuseStep 5487031 = 8230547) B8230547
theorem B899527 : Blo 798342 899527 := bstep (se 1 (by rfl) ⟨674645, by rfl⟩ : syracuseStep 899527 = 1349291) B1349291
theorem B1522145 : Blo 798342 1522145 := bstep (se 2 (by rfl) ⟨570804, by rfl⟩ : syracuseStep 1522145 = 1141609) B1141609
theorem B801275 : Blo 798342 801275 := bstep (se 1 (by rfl) ⟨600956, by rfl⟩ : syracuseStep 801275 = 1201913) B1201913
theorem B801343 : Blo 798342 801343 := bstep (se 1 (by rfl) ⟨601007, by rfl⟩ : syracuseStep 801343 = 1202015) B1202015
theorem B801351 : Blo 798342 801351 := bstep (se 1 (by rfl) ⟨601013, by rfl⟩ : syracuseStep 801351 = 1202027) B1202027
theorem B7289477 : Blo 798342 7289477 := bstep (se 4 (by rfl) ⟨683388, by rfl⟩ : syracuseStep 7289477 = 1366777) B1366777
theorem B801503 : Blo 798342 801503 := bstep (se 1 (by rfl) ⟨601127, by rfl⟩ : syracuseStep 801503 = 1202255) B1202255
theorem B899887 : Blo 798342 899887 := bstep (se 1 (by rfl) ⟨674915, by rfl⟩ : syracuseStep 899887 = 1349831) B1349831
theorem B801583 : Blo 798342 801583 := bstep (se 1 (by rfl) ⟨601187, by rfl⟩ : syracuseStep 801583 = 1202375) B1202375
theorem B899995 : Blo 798342 899995 := bstep (se 1 (by rfl) ⟨674996, by rfl⟩ : syracuseStep 899995 = 1349993) B1349993
theorem B801691 : Blo 798342 801691 := bstep (se 1 (by rfl) ⟨601268, by rfl⟩ : syracuseStep 801691 = 1202537) B1202537
theorem B801743 : Blo 798342 801743 := bstep (se 1 (by rfl) ⟨601307, by rfl⟩ : syracuseStep 801743 = 1202615) B1202615
theorem B801767 : Blo 798342 801767 := bstep (se 1 (by rfl) ⟨601325, by rfl⟩ : syracuseStep 801767 = 1202651) B1202651
theorem B2702375 : Blo 798342 2702375 := bstep (se 1 (by rfl) ⟨2026781, by rfl⟩ : syracuseStep 2702375 = 4053563) B4053563
theorem B4046111 : Blo 798342 4046111 := bstep (se 1 (by rfl) ⟨3034583, by rfl⟩ : syracuseStep 4046111 = 6069167) B6069167
theorem B802079 : Blo 798342 802079 := bstep (se 1 (by rfl) ⟨601559, by rfl⟩ : syracuseStep 802079 = 1203119) B1203119
theorem B900391 : Blo 798342 900391 := bstep (se 1 (by rfl) ⟨675293, by rfl⟩ : syracuseStep 900391 = 1350587) B1350587
theorem B802139 : Blo 798342 802139 := bstep (se 1 (by rfl) ⟨601604, by rfl⟩ : syracuseStep 802139 = 1203209) B1203209
theorem B900463 : Blo 798342 900463 := bstep (se 1 (by rfl) ⟨675347, by rfl⟩ : syracuseStep 900463 = 1350695) B1350695
theorem B802159 : Blo 798342 802159 := bstep (se 1 (by rfl) ⟨601619, by rfl⟩ : syracuseStep 802159 = 1203239) B1203239
theorem B802215 : Blo 798342 802215 := bstep (se 1 (by rfl) ⟨601661, by rfl⟩ : syracuseStep 802215 = 1203323) B1203323
theorem B2702807 : Blo 798342 2702807 := bstep (se 1 (by rfl) ⟨2027105, by rfl⟩ : syracuseStep 2702807 = 4054211) B4054211
theorem B27704825 : Blo 798342 27704825 := bstep (se 2 (by rfl) ⟨10389309, by rfl⟩ : syracuseStep 27704825 = 20778619) B20778619
theorem B802299 : Blo 798342 802299 := bstep (se 1 (by rfl) ⟨601724, by rfl⟩ : syracuseStep 802299 = 1203449) B1203449
theorem B7683599 : Blo 798342 7683599 := bstep (se 1 (by rfl) ⟨5762699, by rfl⟩ : syracuseStep 7683599 = 11525399) B11525399
theorem B6831641 : Blo 798342 6831641 := bstep (se 2 (by rfl) ⟨2561865, by rfl⟩ : syracuseStep 6831641 = 5123731) B5123731
theorem B900679 : Blo 798342 900679 := bstep (se 1 (by rfl) ⟨675509, by rfl⟩ : syracuseStep 900679 = 1351019) B1351019
theorem B3850411 : Blo 798342 3850411 := bstep (se 1 (by rfl) ⟨2887808, by rfl⟩ : syracuseStep 3850411 = 5775617) B5775617
theorem B1851815 : Blo 798342 1851815 := bstep (se 1 (by rfl) ⟨1388861, by rfl⟩ : syracuseStep 1851815 = 2777723) B2777723
theorem B901543 : Blo 798342 901543 := bstep (se 1 (by rfl) ⟨676157, by rfl⟩ : syracuseStep 901543 = 1352315) B1352315
theorem B7684753 : Blo 798342 7684753 := bstep (se 2 (by rfl) ⟨2881782, by rfl⟩ : syracuseStep 7684753 = 5763565) B5763565
theorem B3031775 : Blo 798342 3031775 := bstep (se 1 (by rfl) ⟨2273831, by rfl⟩ : syracuseStep 3031775 = 4547663) B4547663
theorem B3851239 : Blo 798342 3851239 := bstep (se 1 (by rfl) ⟨2888429, by rfl⟩ : syracuseStep 3851239 = 5776859) B5776859
theorem B902119 : Blo 798342 902119 := bstep (se 1 (by rfl) ⟨676589, by rfl⟩ : syracuseStep 902119 = 1353179) B1353179
theorem B3425287 : Blo 798342 3425287 := bstep (se 1 (by rfl) ⟨2568965, by rfl⟩ : syracuseStep 3425287 = 5137931) B5137931
theorem B2704481 : Blo 798342 2704481 := bstep (se 2 (by rfl) ⟨1014180, by rfl⟩ : syracuseStep 2704481 = 2028361) B2028361
theorem B1918247 : Blo 798342 1918247 := bstep (se 1 (by rfl) ⟨1438685, by rfl⟩ : syracuseStep 1918247 = 2877371) B2877371
theorem B2311519 : Blo 798342 2311519 := bstep (se 1 (by rfl) ⟨1733639, by rfl⟩ : syracuseStep 2311519 = 3467279) B3467279
theorem B1623647 : Blo 798342 1623647 := bstep (se 1 (by rfl) ⟨1217735, by rfl⟩ : syracuseStep 1623647 = 2435471) B2435471
theorem B4048541 : Blo 798342 4048541 := bstep (se 3 (by rfl) ⟨759101, by rfl⟩ : syracuseStep 4048541 = 1518203) B1518203
theorem B1197803 : Blo 798342 1197803 := bstep (se 1 (by rfl) ⟨898352, by rfl⟩ : syracuseStep 1197803 = 1796705) B1796705
theorem B1198031 : Blo 798342 1198031 := bstep (se 1 (by rfl) ⟨898523, by rfl⟩ : syracuseStep 1198031 = 1797047) B1797047
theorem B19482889 : Blo 798342 19482889 := bstep (se 2 (by rfl) ⟨7306083, by rfl⟩ : syracuseStep 19482889 = 14612167) B14612167
theorem B1198427 : Blo 798342 1198427 := bstep (se 1 (by rfl) ⟨898820, by rfl⟩ : syracuseStep 1198427 = 1797641) B1797641
theorem B2705831 : Blo 798342 2705831 := bstep (se 1 (by rfl) ⟨2029373, by rfl⟩ : syracuseStep 2705831 = 4058747) B4058747
theorem B1198655 : Blo 798342 1198655 := bstep (se 1 (by rfl) ⟨898991, by rfl⟩ : syracuseStep 1198655 = 1797983) B1797983
theorem B2705993 : Blo 798342 2705993 := bstep (se 2 (by rfl) ⟨1014747, by rfl⟩ : syracuseStep 2705993 = 2029495) B2029495
theorem B21908069 : Blo 798342 21908069 := bstep (se 4 (by rfl) ⟨2053881, by rfl⟩ : syracuseStep 21908069 = 4107763) B4107763
theorem B1198775 : Blo 798342 1198775 := bstep (se 1 (by rfl) ⟨899081, by rfl⟩ : syracuseStep 1198775 = 1798163) B1798163
theorem B5557015 : Blo 798342 5557015 := bstep (se 1 (by rfl) ⟨4167761, by rfl⟩ : syracuseStep 5557015 = 8335523) B8335523
theorem B1199003 : Blo 798342 1199003 := bstep (se 1 (by rfl) ⟨899252, by rfl⟩ : syracuseStep 1199003 = 1798505) B1798505
theorem B4049837 : Blo 798342 4049837 := bstep (se 3 (by rfl) ⟨759344, by rfl⟩ : syracuseStep 4049837 = 1518689) B1518689
theorem B3460211 : Blo 798342 3460211 := bstep (se 1 (by rfl) ⟨2595158, by rfl⟩ : syracuseStep 3460211 = 5190317) B5190317
theorem B8670347 : Blo 798342 8670347 := bstep (se 1 (by rfl) ⟨6502760, by rfl⟩ : syracuseStep 8670347 = 13005521) B13005521
theorem B1821895 : Blo 798342 1821895 := bstep (se 1 (by rfl) ⟨1366421, by rfl⟩ : syracuseStep 1821895 = 2732843) B2732843
theorem B1199399 : Blo 798342 1199399 := bstep (se 1 (by rfl) ⟨899549, by rfl⟩ : syracuseStep 1199399 = 1799099) B1799099
theorem B1199483 : Blo 798342 1199483 := bstep (se 1 (by rfl) ⟨899612, by rfl⟩ : syracuseStep 1199483 = 1799225) B1799225
theorem B1199609 : Blo 798342 1199609 := bstep (se 2 (by rfl) ⟨449853, by rfl⟩ : syracuseStep 1199609 = 899707) B899707
theorem B3034705 : Blo 798342 3034705 := bstep (se 2 (by rfl) ⟨1138014, by rfl⟩ : syracuseStep 3034705 = 2276029) B2276029
theorem B1199711 : Blo 798342 1199711 := bstep (se 1 (by rfl) ⟨899783, by rfl⟩ : syracuseStep 1199711 = 1799567) B1799567
theorem B2281223 : Blo 798342 2281223 := bstep (se 1 (by rfl) ⟨1710917, by rfl⟩ : syracuseStep 2281223 = 3421835) B3421835
theorem B6836015 : Blo 798342 6836015 := bstep (se 1 (by rfl) ⟨5127011, by rfl⟩ : syracuseStep 6836015 = 10254023) B10254023
theorem B1199927 : Blo 798342 1199927 := bstep (se 1 (by rfl) ⟨899945, by rfl⟩ : syracuseStep 1199927 = 1799891) B1799891
theorem B3035009 : Blo 798342 3035009 := bstep (se 2 (by rfl) ⟨1138128, by rfl⟩ : syracuseStep 3035009 = 2276257) B2276257
theorem B1200233 : Blo 798342 1200233 := bstep (se 2 (by rfl) ⟨450087, by rfl⟩ : syracuseStep 1200233 = 900175) B900175
theorem B2707667 : Blo 798342 2707667 := bstep (se 1 (by rfl) ⟨2030750, by rfl⟩ : syracuseStep 2707667 = 4061501) B4061501
theorem B3035465 : Blo 798342 3035465 := bstep (se 2 (by rfl) ⟨1138299, by rfl⟩ : syracuseStep 3035465 = 2276599) B2276599
theorem B1200551 : Blo 798342 1200551 := bstep (se 1 (by rfl) ⟨900413, by rfl⟩ : syracuseStep 1200551 = 1800827) B1800827
theorem B1200635 : Blo 798342 1200635 := bstep (se 1 (by rfl) ⟨900476, by rfl⟩ : syracuseStep 1200635 = 1800953) B1800953
theorem B4051457 : Blo 798342 4051457 := bstep (se 2 (by rfl) ⟨1519296, by rfl⟩ : syracuseStep 4051457 = 3038593) B3038593
theorem B1200761 : Blo 798342 1200761 := bstep (se 2 (by rfl) ⟨450285, by rfl⟩ : syracuseStep 1200761 = 900571) B900571
theorem B1200815 : Blo 798342 1200815 := bstep (se 1 (by rfl) ⟨900611, by rfl⟩ : syracuseStep 1200815 = 1801223) B1801223
theorem B1200863 : Blo 798342 1200863 := bstep (se 1 (by rfl) ⟨900647, by rfl⟩ : syracuseStep 1200863 = 1801295) B1801295
theorem B4051943 : Blo 798342 4051943 := bstep (se 1 (by rfl) ⟨3038957, by rfl⟩ : syracuseStep 4051943 = 6077915) B6077915
theorem B1201127 : Blo 798342 1201127 := bstep (se 1 (by rfl) ⟨900845, by rfl⟩ : syracuseStep 1201127 = 1801691) B1801691
theorem B30823577 : Blo 798342 30823577 := bstep (se 2 (by rfl) ⟨11558841, by rfl⟩ : syracuseStep 30823577 = 23117683) B23117683
theorem B1201385 : Blo 798342 1201385 := bstep (se 2 (by rfl) ⟨450519, by rfl⟩ : syracuseStep 1201385 = 901039) B901039
theorem B1201439 : Blo 798342 1201439 := bstep (se 1 (by rfl) ⟨901079, by rfl⟩ : syracuseStep 1201439 = 1802159) B1802159
theorem B4052267 : Blo 798342 4052267 := bstep (se 1 (by rfl) ⟨3039200, by rfl⟩ : syracuseStep 4052267 = 6078401) B6078401
theorem B25974179 : Blo 798342 25974179 := bstep (se 1 (by rfl) ⟨19480634, by rfl⟩ : syracuseStep 25974179 = 38961269) B38961269
theorem B1201607 : Blo 798342 1201607 := bstep (se 1 (by rfl) ⟨901205, by rfl⟩ : syracuseStep 1201607 = 1802411) B1802411
theorem B2021051 : Blo 798342 2021051 := bstep (se 1 (by rfl) ⟨1515788, by rfl⟩ : syracuseStep 2021051 = 3031577) B3031577
theorem B1201961 : Blo 798342 1201961 := bstep (se 2 (by rfl) ⟨450735, by rfl⟩ : syracuseStep 1201961 = 901471) B901471
theorem B1201967 : Blo 798342 1201967 := bstep (se 1 (by rfl) ⟨901475, by rfl⟩ : syracuseStep 1201967 = 1802951) B1802951
theorem B2283319 : Blo 798342 2283319 := bstep (se 1 (by rfl) ⟨1712489, by rfl⟩ : syracuseStep 2283319 = 3424979) B3424979
theorem B3889079 : Blo 798342 3889079 := bstep (se 1 (by rfl) ⟨2916809, by rfl⟩ : syracuseStep 3889079 = 5833619) B5833619
theorem B3037135 : Blo 798342 3037135 := bstep (se 1 (by rfl) ⟨2277851, by rfl⟩ : syracuseStep 3037135 = 4555703) B4555703
theorem B7297067 : Blo 798342 7297067 := bstep (se 1 (by rfl) ⟨5472800, by rfl⟩ : syracuseStep 7297067 = 10945601) B10945601
theorem B1366121 : Blo 798342 1366121 := bstep (se 2 (by rfl) ⟨512295, by rfl⟩ : syracuseStep 1366121 = 1024591) B1024591
theorem B4053239 : Blo 798342 4053239 := bstep (se 1 (by rfl) ⟨3039929, by rfl⟩ : syracuseStep 4053239 = 6079859) B6079859
theorem B1202441 : Blo 798342 1202441 := bstep (se 2 (by rfl) ⟨450915, by rfl⟩ : syracuseStep 1202441 = 901831) B901831
theorem B1137007 : Blo 798342 1137007 := bstep (se 1 (by rfl) ⟨852755, by rfl⟩ : syracuseStep 1137007 = 1705511) B1705511
theorem B1235311 : Blo 798342 1235311 := bstep (se 1 (by rfl) ⟨926483, by rfl⟩ : syracuseStep 1235311 = 1852967) B1852967
theorem B1202543 : Blo 798342 1202543 := bstep (se 1 (by rfl) ⟨901907, by rfl⟩ : syracuseStep 1202543 = 1803815) B1803815
theorem B3037607 : Blo 798342 3037607 := bstep (se 1 (by rfl) ⟨2278205, by rfl⟩ : syracuseStep 3037607 = 4556411) B4556411
theorem B12999163 : Blo 798342 12999163 := bstep (se 1 (by rfl) ⟨9749372, by rfl⟩ : syracuseStep 12999163 = 19498745) B19498745
theorem B1202759 : Blo 798342 1202759 := bstep (se 1 (by rfl) ⟨902069, by rfl⟩ : syracuseStep 1202759 = 1804139) B1804139
theorem B1202795 : Blo 798342 1202795 := bstep (se 1 (by rfl) ⟨902096, by rfl⟩ : syracuseStep 1202795 = 1804193) B1804193
theorem B2284139 : Blo 798342 2284139 := bstep (se 1 (by rfl) ⟨1713104, by rfl⟩ : syracuseStep 2284139 = 3426209) B3426209
theorem B4053725 : Blo 798342 4053725 := bstep (se 3 (by rfl) ⟨760073, by rfl⟩ : syracuseStep 4053725 = 1520147) B1520147
theorem B1203023 : Blo 798342 1203023 := bstep (se 1 (by rfl) ⟨902267, by rfl⟩ : syracuseStep 1203023 = 1804535) B1804535
theorem B3038107 : Blo 798342 3038107 := bstep (se 1 (by rfl) ⟨2278580, by rfl⟩ : syracuseStep 3038107 = 4557161) B4557161
theorem B2776051 : Blo 798342 2776051 := bstep (se 1 (by rfl) ⟨2082038, by rfl⟩ : syracuseStep 2776051 = 4164077) B4164077
theorem B8215769 : Blo 798342 8215769 := bstep (se 2 (by rfl) ⟨3080913, by rfl⟩ : syracuseStep 8215769 = 6161827) B6161827
theorem B1203419 : Blo 798342 1203419 := bstep (se 1 (by rfl) ⟨902564, by rfl⟩ : syracuseStep 1203419 = 1805129) B1805129
theorem B17784029 : Blo 798342 17784029 := bstep (se 3 (by rfl) ⟨3334505, by rfl⟩ : syracuseStep 17784029 = 6669011) B6669011
theorem B10280267 : Blo 798342 10280267 := bstep (se 1 (by rfl) ⟨7710200, by rfl⟩ : syracuseStep 10280267 = 15420401) B15420401
theorem B810331 : Blo 798342 810331 := bstep (se 1 (by rfl) ⟨607748, by rfl⟩ : syracuseStep 810331 = 1215497) B1215497
theorem B2022995 : Blo 798342 2022995 := bstep (se 1 (by rfl) ⟨1517246, by rfl⟩ : syracuseStep 2022995 = 3034493) B3034493
theorem B1826567 : Blo 798342 1826567 := bstep (se 1 (by rfl) ⟨1369925, by rfl⟩ : syracuseStep 1826567 = 2739851) B2739851
theorem B37019555 : Blo 798342 37019555 := bstep (se 1 (by rfl) ⟨27764666, by rfl⟩ : syracuseStep 37019555 = 55529333) B55529333
theorem B1925551 : Blo 798342 1925551 := bstep (se 1 (by rfl) ⟨1444163, by rfl⟩ : syracuseStep 1925551 = 2888327) B2888327
theorem B1925705 : Blo 798342 1925705 := bstep (se 2 (by rfl) ⟨722139, by rfl⟩ : syracuseStep 1925705 = 1444279) B1444279
theorem B2024423 : Blo 798342 2024423 := bstep (se 1 (by rfl) ⟨1518317, by rfl⟩ : syracuseStep 2024423 = 3036635) B3036635
theorem B5137445 : Blo 798342 5137445 := bstep (se 4 (by rfl) ⟨481635, by rfl⟩ : syracuseStep 5137445 = 963271) B963271
theorem B2025121 : Blo 798342 2025121 := bstep (se 2 (by rfl) ⟨759420, by rfl⟩ : syracuseStep 2025121 = 1518841) B1518841
theorem B2025263 : Blo 798342 2025263 := bstep (se 1 (by rfl) ⟨1518947, by rfl⟩ : syracuseStep 2025263 = 3037895) B3037895
theorem B3565601 : Blo 798342 3565601 := bstep (se 2 (by rfl) ⟨1337100, by rfl⟩ : syracuseStep 3565601 = 2674201) B2674201
theorem B15395183 : Blo 798342 15395183 := bstep (se 1 (by rfl) ⟨11546387, by rfl⟩ : syracuseStep 15395183 = 23092775) B23092775
theorem B2025911 : Blo 798342 2025911 := bstep (se 1 (by rfl) ⟨1519433, by rfl⟩ : syracuseStep 2025911 = 3038867) B3038867
theorem B1796687 : Blo 798342 1796687 := bstep (se 1 (by rfl) ⟨1347515, by rfl⟩ : syracuseStep 1796687 = 2695031) B2695031
theorem B4057775 : Blo 798342 4057775 := bstep (se 1 (by rfl) ⟨3043331, by rfl⟩ : syracuseStep 4057775 = 6086663) B6086663
theorem B1796831 : Blo 798342 1796831 := bstep (se 1 (by rfl) ⟨1347623, by rfl⟩ : syracuseStep 1796831 = 2695247) B2695247
theorem B31124405 : Blo 798342 31124405 := bstep (se 5 (by rfl) ⟨1458956, by rfl⟩ : syracuseStep 31124405 = 2917913) B2917913
theorem B1797083 : Blo 798342 1797083 := bstep (se 1 (by rfl) ⟨1347812, by rfl⟩ : syracuseStep 1797083 = 2695625) B2695625
theorem B4058099 : Blo 798342 4058099 := bstep (se 1 (by rfl) ⟨3043574, by rfl⟩ : syracuseStep 4058099 = 6087149) B6087149
theorem B1829879 : Blo 798342 1829879 := bstep (se 1 (by rfl) ⟨1372409, by rfl⟩ : syracuseStep 1829879 = 2744819) B2744819
theorem B5139571 : Blo 798342 5139571 := bstep (se 1 (by rfl) ⟨3854678, by rfl⟩ : syracuseStep 5139571 = 7709357) B7709357
theorem B1797263 : Blo 798342 1797263 := bstep (se 1 (by rfl) ⟨1347947, by rfl⟩ : syracuseStep 1797263 = 2695895) B2695895
theorem B1797353 : Blo 798342 1797353 := bstep (se 2 (by rfl) ⟨674007, by rfl⟩ : syracuseStep 1797353 = 1348015) B1348015
theorem B1797407 : Blo 798342 1797407 := bstep (se 1 (by rfl) ⟨1348055, by rfl⟩ : syracuseStep 1797407 = 2696111) B2696111
theorem B1142047 : Blo 798342 1142047 := bstep (se 1 (by rfl) ⟨856535, by rfl⟩ : syracuseStep 1142047 = 1713071) B1713071
theorem B4320641 : Blo 798342 4320641 := bstep (se 2 (by rfl) ⟨1620240, by rfl⟩ : syracuseStep 4320641 = 3240481) B3240481
theorem B1011143 : Blo 798342 1011143 := bstep (se 1 (by rfl) ⟨758357, by rfl⟩ : syracuseStep 1011143 = 1516715) B1516715
theorem B2027015 : Blo 798342 2027015 := bstep (se 1 (by rfl) ⟨1520261, by rfl⟩ : syracuseStep 2027015 = 3040523) B3040523
theorem B2027065 : Blo 798342 2027065 := bstep (se 2 (by rfl) ⟨760149, by rfl⟩ : syracuseStep 2027065 = 1520299) B1520299
theorem B1011295 : Blo 798342 1011295 := bstep (se 1 (by rfl) ⟨758471, by rfl⟩ : syracuseStep 1011295 = 1516943) B1516943
theorem B6844013 : Blo 798342 6844013 := bstep (se 3 (by rfl) ⟨1283252, by rfl⟩ : syracuseStep 6844013 = 2566505) B2566505
theorem B1797929 : Blo 798342 1797929 := bstep (se 2 (by rfl) ⟨674223, by rfl⟩ : syracuseStep 1797929 = 1348447) B1348447
theorem B9105209 : Blo 798342 9105209 := bstep (se 2 (by rfl) ⟨3414453, by rfl⟩ : syracuseStep 9105209 = 6828907) B6828907
theorem B2027369 : Blo 798342 2027369 := bstep (se 2 (by rfl) ⟨760263, by rfl⟩ : syracuseStep 2027369 = 1520527) B1520527
theorem B2158721 : Blo 798342 2158721 := bstep (se 2 (by rfl) ⟨809520, by rfl⟩ : syracuseStep 2158721 = 1619041) B1619041
theorem B4059395 : Blo 798342 4059395 := bstep (se 1 (by rfl) ⟨3044546, by rfl⟩ : syracuseStep 4059395 = 6089093) B6089093
theorem B2027987 : Blo 798342 2027987 := bstep (se 1 (by rfl) ⟨1520990, by rfl⟩ : syracuseStep 2027987 = 3041981) B3041981
theorem B4059719 : Blo 798342 4059719 := bstep (se 1 (by rfl) ⟨3044789, by rfl⟩ : syracuseStep 4059719 = 6089579) B6089579
theorem B5763737 : Blo 798342 5763737 := bstep (se 2 (by rfl) ⟨2161401, by rfl⟩ : syracuseStep 5763737 = 4322803) B4322803
theorem B1798991 : Blo 798342 1798991 := bstep (se 1 (by rfl) ⟨1349243, by rfl⟩ : syracuseStep 1798991 = 2698487) B2698487
theorem B1799207 : Blo 798342 1799207 := bstep (se 1 (by rfl) ⟨1349405, by rfl⟩ : syracuseStep 1799207 = 2698811) B2698811
theorem B2880659 : Blo 798342 2880659 := bstep (se 1 (by rfl) ⟨2160494, by rfl⟩ : syracuseStep 2880659 = 4320989) B4320989
theorem B1799387 : Blo 798342 1799387 := bstep (se 1 (by rfl) ⟨1349540, by rfl⟩ : syracuseStep 1799387 = 2699081) B2699081
theorem B1799585 : Blo 798342 1799585 := bstep (se 2 (by rfl) ⟨674844, by rfl⟩ : syracuseStep 1799585 = 1349689) B1349689
theorem B2029151 : Blo 798342 2029151 := bstep (se 1 (by rfl) ⟨1521863, by rfl⟩ : syracuseStep 2029151 = 3043727) B3043727
theorem B73791157 : Blo 798342 73791157 := bstep (se 5 (by rfl) ⟨3458960, by rfl⟩ : syracuseStep 73791157 = 6917921) B6917921
theorem B4061015 : Blo 798342 4061015 := bstep (se 1 (by rfl) ⟨3045761, by rfl⟩ : syracuseStep 4061015 = 6091523) B6091523
theorem B7698361 : Blo 798342 7698361 := bstep (se 2 (by rfl) ⟨2886885, by rfl⟩ : syracuseStep 7698361 = 5773771) B5773771
theorem B1800143 : Blo 798342 1800143 := bstep (se 1 (by rfl) ⟨1350107, by rfl⟩ : syracuseStep 1800143 = 2700215) B2700215
theorem B1013735 : Blo 798342 1013735 := bstep (se 1 (by rfl) ⟨760301, by rfl⟩ : syracuseStep 1013735 = 1520603) B1520603
theorem B1800521 : Blo 798342 1800521 := bstep (se 2 (by rfl) ⟨675195, by rfl⟩ : syracuseStep 1800521 = 1350391) B1350391
theorem B1800539 : Blo 798342 1800539 := bstep (se 1 (by rfl) ⟨1350404, by rfl⟩ : syracuseStep 1800539 = 2700809) B2700809
theorem B2029931 : Blo 798342 2029931 := bstep (se 1 (by rfl) ⟨1522448, by rfl⟩ : syracuseStep 2029931 = 3044897) B3044897
theorem B3045883 : Blo 798342 3045883 := bstep (se 1 (by rfl) ⟨2284412, by rfl⟩ : syracuseStep 3045883 = 4568825) B4568825
theorem B2030143 : Blo 798342 2030143 := bstep (se 1 (by rfl) ⟨1522607, by rfl⟩ : syracuseStep 2030143 = 3045215) B3045215
theorem B2030255 : Blo 798342 2030255 := bstep (se 1 (by rfl) ⟨1522691, by rfl⟩ : syracuseStep 2030255 = 3045383) B3045383
theorem B6486803 : Blo 798342 6486803 := bstep (se 1 (by rfl) ⟨4865102, by rfl⟩ : syracuseStep 6486803 = 9730205) B9730205
theorem B1801115 : Blo 798342 1801115 := bstep (se 1 (by rfl) ⟨1350836, by rfl⟩ : syracuseStep 1801115 = 2701673) B2701673
theorem B5209019 : Blo 798342 5209019 := bstep (se 1 (by rfl) ⟨3906764, by rfl⟩ : syracuseStep 5209019 = 7813529) B7813529
theorem B2030579 : Blo 798342 2030579 := bstep (se 1 (by rfl) ⟨1522934, by rfl⟩ : syracuseStep 2030579 = 3045869) B3045869
theorem B1801313 : Blo 798342 1801313 := bstep (se 2 (by rfl) ⟨675492, by rfl⟩ : syracuseStep 1801313 = 1350985) B1350985
theorem B2030791 : Blo 798342 2030791 := bstep (se 1 (by rfl) ⟨1523093, by rfl⟩ : syracuseStep 2030791 = 3046187) B3046187
theorem B1801511 : Blo 798342 1801511 := bstep (se 1 (by rfl) ⟨1351133, by rfl⟩ : syracuseStep 1801511 = 2702267) B2702267
theorem B1801889 : Blo 798342 1801889 := bstep (se 2 (by rfl) ⟨675708, by rfl⟩ : syracuseStep 1801889 = 1351417) B1351417
theorem B8651227 : Blo 798342 8651227 := bstep (se 1 (by rfl) ⟨6488420, by rfl⟩ : syracuseStep 8651227 = 12976841) B12976841
theorem B4555385 : Blo 798342 4555385 := bstep (se 2 (by rfl) ⟨1708269, by rfl⟩ : syracuseStep 4555385 = 3416539) B3416539
theorem B1802987 : Blo 798342 1802987 := bstep (se 1 (by rfl) ⟨1352240, by rfl⟩ : syracuseStep 1802987 = 2704481) B2704481
theorem B2884349 : Blo 798342 2884349 := bstep (se 3 (by rfl) ⟨540815, by rfl⟩ : syracuseStep 2884349 = 1081631) B1081631
theorem B4326263 : Blo 798342 4326263 := bstep (se 1 (by rfl) ⟨3244697, by rfl⟩ : syracuseStep 4326263 = 6489395) B6489395
theorem B1082431 : Blo 798342 1082431 := bstep (se 1 (by rfl) ⟨811823, by rfl⟩ : syracuseStep 1082431 = 1623647) B1623647
theorem B1803887 : Blo 798342 1803887 := bstep (se 1 (by rfl) ⟨1352915, by rfl⟩ : syracuseStep 1803887 = 2705831) B2705831
theorem B1803995 : Blo 798342 1803995 := bstep (se 1 (by rfl) ⟨1352996, by rfl⟩ : syracuseStep 1803995 = 2705993) B2705993
theorem B3082025 : Blo 798342 3082025 := bstep (se 2 (by rfl) ⟨1155759, by rfl⟩ : syracuseStep 3082025 = 2311519) B2311519
theorem B2885473 : Blo 798342 2885473 := bstep (se 2 (by rfl) ⟨1082052, by rfl⟩ : syracuseStep 2885473 = 2164105) B2164105
theorem B6588325 : Blo 798342 6588325 := bstep (se 4 (by rfl) ⟨617655, by rfl⟩ : syracuseStep 6588325 = 1235311) B1235311
theorem B29264165 : Blo 798342 29264165 := bstep (se 4 (by rfl) ⟨2743515, by rfl⟩ : syracuseStep 29264165 = 5487031) B5487031
theorem B4557343 : Blo 798342 4557343 := bstep (se 1 (by rfl) ⟨3418007, by rfl⟩ : syracuseStep 4557343 = 6836015) B6836015
theorem B1805111 : Blo 798342 1805111 := bstep (se 1 (by rfl) ⟨1353833, by rfl⟩ : syracuseStep 1805111 = 2707667) B2707667
theorem B2559023 : Blo 798342 2559023 := bstep (se 1 (by rfl) ⟨1919267, by rfl⟩ : syracuseStep 2559023 = 3838535) B3838535
theorem B20549051 : Blo 798342 20549051 := bstep (se 1 (by rfl) ⟨15411788, by rfl⟩ : syracuseStep 20549051 = 30823577) B30823577
theorem B5115325 : Blo 798342 5115325 := bstep (se 3 (by rfl) ⟨959123, by rfl⟩ : syracuseStep 5115325 = 1918247) B1918247
theorem B855527 : Blo 798342 855527 := bstep (se 1 (by rfl) ⟨641645, by rfl⟩ : syracuseStep 855527 = 1283291) B1283291
theorem B1347367 : Blo 798342 1347367 := bstep (se 1 (by rfl) ⟨1010525, by rfl⟩ : syracuseStep 1347367 = 2021051) B2021051
theorem B2592719 : Blo 798342 2592719 := bstep (se 1 (by rfl) ⟨1944539, by rfl⟩ : syracuseStep 2592719 = 3889079) B3889079
theorem B9244691 : Blo 798342 9244691 := bstep (se 1 (by rfl) ⟨6933518, by rfl⟩ : syracuseStep 9244691 = 13867037) B13867037
theorem B2560123 : Blo 798342 2560123 := bstep (se 1 (by rfl) ⟨1920092, by rfl⟩ : syracuseStep 2560123 = 3840185) B3840185
theorem B6852761 : Blo 798342 6852761 := bstep (se 2 (by rfl) ⟨2569785, by rfl⟩ : syracuseStep 6852761 = 5139571) B5139571
theorem B3412439 : Blo 798342 3412439 := bstep (se 1 (by rfl) ⟨2559329, by rfl⟩ : syracuseStep 3412439 = 5118659) B5118659
theorem B2888473 : Blo 798342 2888473 := bstep (se 2 (by rfl) ⟨1083177, by rfl⟩ : syracuseStep 2888473 = 2166355) B2166355
theorem B1348393 : Blo 798342 1348393 := bstep (se 2 (by rfl) ⟨505647, by rfl⟩ : syracuseStep 1348393 = 1011295) B1011295
theorem B5477179 : Blo 798342 5477179 := bstep (se 1 (by rfl) ⟨4107884, by rfl⟩ : syracuseStep 5477179 = 8215769) B8215769
theorem B6853511 : Blo 798342 6853511 := bstep (se 1 (by rfl) ⟨5140133, by rfl⟩ : syracuseStep 6853511 = 10280267) B10280267
theorem B1348663 : Blo 798342 1348663 := bstep (se 1 (by rfl) ⟨1011497, by rfl⟩ : syracuseStep 1348663 = 2022995) B2022995
theorem B2888777 : Blo 798342 2888777 := bstep (se 2 (by rfl) ⟨1083291, by rfl⟩ : syracuseStep 2888777 = 2166583) B2166583
theorem B1217711 : Blo 798342 1217711 := bstep (se 1 (by rfl) ⟨913283, by rfl⟩ : syracuseStep 1217711 = 1826567) B1826567
theorem B24679703 : Blo 798342 24679703 := bstep (se 1 (by rfl) ⟨18509777, by rfl⟩ : syracuseStep 24679703 = 37019555) B37019555
theorem B3413771 : Blo 798342 3413771 := bstep (se 1 (by rfl) ⟨2560328, by rfl⟩ : syracuseStep 3413771 = 5120657) B5120657
theorem B1349615 : Blo 798342 1349615 := bstep (se 1 (by rfl) ⟨1012211, by rfl⟩ : syracuseStep 1349615 = 2024423) B2024423
theorem B4856051 : Blo 798342 4856051 := bstep (se 1 (by rfl) ⟨3642038, by rfl⟩ : syracuseStep 4856051 = 7284077) B7284077
theorem B1350175 : Blo 798342 1350175 := bstep (se 1 (by rfl) ⟨1012631, by rfl⟩ : syracuseStep 1350175 = 2025263) B2025263
theorem B10263455 : Blo 798342 10263455 := bstep (se 1 (by rfl) ⟨7697591, by rfl⟩ : syracuseStep 10263455 = 15395183) B15395183
theorem B1350607 : Blo 798342 1350607 := bstep (se 1 (by rfl) ⟨1012955, by rfl⟩ : syracuseStep 1350607 = 2025911) B2025911
theorem B20749603 : Blo 798342 20749603 := bstep (se 1 (by rfl) ⟨15562202, by rfl⟩ : syracuseStep 20749603 = 31124405) B31124405
theorem B1219919 : Blo 798342 1219919 := bstep (se 1 (by rfl) ⟨914939, by rfl⟩ : syracuseStep 1219919 = 1829879) B1829879
theorem B2563559 : Blo 798342 2563559 := bstep (se 1 (by rfl) ⟨1922669, by rfl⟩ : syracuseStep 2563559 = 3845339) B3845339
theorem B1351343 : Blo 798342 1351343 := bstep (se 1 (by rfl) ⟨1013507, by rfl⟩ : syracuseStep 1351343 = 2027015) B2027015
theorem B32841395 : Blo 798342 32841395 := bstep (se 1 (by rfl) ⟨24631046, by rfl⟩ : syracuseStep 32841395 = 49262093) B49262093
theorem B4562675 : Blo 798342 4562675 := bstep (se 1 (by rfl) ⟨3422006, by rfl⟩ : syracuseStep 4562675 = 6844013) B6844013
theorem B1711943 : Blo 798342 1711943 := bstep (se 1 (by rfl) ⟨1283957, by rfl⟩ : syracuseStep 1711943 = 2567915) B2567915
theorem B6070139 : Blo 798342 6070139 := bstep (se 1 (by rfl) ⟨4552604, by rfl⟩ : syracuseStep 6070139 = 9105209) B9105209
theorem B1351579 : Blo 798342 1351579 := bstep (se 1 (by rfl) ⟨1013684, by rfl⟩ : syracuseStep 1351579 = 2027369) B2027369
theorem B10264481 : Blo 798342 10264481 := bstep (se 2 (by rfl) ⟨3849180, by rfl⟩ : syracuseStep 10264481 = 7698361) B7698361
theorem B1351991 : Blo 798342 1351991 := bstep (se 1 (by rfl) ⟨1013993, by rfl⟩ : syracuseStep 1351991 = 2027987) B2027987
theorem B3842491 : Blo 798342 3842491 := bstep (se 1 (by rfl) ⟨2881868, by rfl⟩ : syracuseStep 3842491 = 5763737) B5763737
theorem B1516009 : Blo 798342 1516009 := bstep (se 2 (by rfl) ⟨568503, by rfl⟩ : syracuseStep 1516009 = 1137007) B1137007
theorem B2695787 : Blo 798342 2695787 := bstep (se 1 (by rfl) ⟨2021840, by rfl⟩ : syracuseStep 2695787 = 4043681) B4043681
theorem B1352767 : Blo 798342 1352767 := bstep (se 1 (by rfl) ⟨1014575, by rfl⟩ : syracuseStep 1352767 = 2029151) B2029151
theorem B39036005 : Blo 798342 39036005 := bstep (se 4 (by rfl) ⟨3659625, by rfl⟩ : syracuseStep 39036005 = 7319251) B7319251
theorem B5776541 : Blo 798342 5776541 := bstep (se 3 (by rfl) ⟨1083101, by rfl⟩ : syracuseStep 5776541 = 2166203) B2166203
theorem B4564133 : Blo 798342 4564133 := bstep (se 4 (by rfl) ⟨427887, by rfl⟩ : syracuseStep 4564133 = 855775) B855775
theorem B2696381 : Blo 798342 2696381 := bstep (se 3 (by rfl) ⟨505571, by rfl⟩ : syracuseStep 2696381 = 1011143) B1011143
theorem B1713583 : Blo 798342 1713583 := bstep (se 1 (by rfl) ⟨1285187, by rfl⟩ : syracuseStep 1713583 = 2570375) B2570375
theorem B1353287 : Blo 798342 1353287 := bstep (se 1 (by rfl) ⟨1014965, by rfl⟩ : syracuseStep 1353287 = 2029931) B2029931
theorem B4859651 : Blo 798342 4859651 := bstep (se 1 (by rfl) ⟨3644738, by rfl⟩ : syracuseStep 4859651 = 7289477) B7289477
theorem B1353503 : Blo 798342 1353503 := bstep (se 1 (by rfl) ⟨1015127, by rfl⟩ : syracuseStep 1353503 = 2030255) B2030255
theorem B1353719 : Blo 798342 1353719 := bstep (se 1 (by rfl) ⟨1015289, by rfl⟩ : syracuseStep 1353719 = 2030579) B2030579
theorem B2697407 : Blo 798342 2697407 := bstep (se 1 (by rfl) ⟨2023055, by rfl⟩ : syracuseStep 2697407 = 4046111) B4046111
theorem B5122399 : Blo 798342 5122399 := bstep (se 1 (by rfl) ⟨3841799, by rfl⟩ : syracuseStep 5122399 = 7683599) B7683599
theorem B2699027 : Blo 798342 2699027 := bstep (se 1 (by rfl) ⟨2024270, by rfl⟩ : syracuseStep 2699027 = 4048541) B4048541
theorem B798535 : Blo 798342 798535 := bstep (se 1 (by rfl) ⟨598901, by rfl⟩ : syracuseStep 798535 = 1197803) B1197803
theorem B798687 : Blo 798342 798687 := bstep (se 1 (by rfl) ⟨599015, by rfl⟩ : syracuseStep 798687 = 1198031) B1198031
theorem B4567049 : Blo 798342 4567049 := bstep (se 2 (by rfl) ⟨1712643, by rfl⟩ : syracuseStep 4567049 = 3425287) B3425287
theorem B2273467 : Blo 798342 2273467 := bstep (se 1 (by rfl) ⟨1705100, by rfl⟩ : syracuseStep 2273467 = 3410201) B3410201
theorem B798951 : Blo 798342 798951 := bstep (se 1 (by rfl) ⟨599213, by rfl⟩ : syracuseStep 798951 = 1198427) B1198427
theorem B799103 : Blo 798342 799103 := bstep (se 1 (by rfl) ⟨599327, by rfl⟩ : syracuseStep 799103 = 1198655) B1198655
theorem B799183 : Blo 798342 799183 := bstep (se 1 (by rfl) ⟨599387, by rfl⟩ : syracuseStep 799183 = 1198775) B1198775
theorem B799335 : Blo 798342 799335 := bstep (se 1 (by rfl) ⟨599501, by rfl⟩ : syracuseStep 799335 = 1199003) B1199003
theorem B2699891 : Blo 798342 2699891 := bstep (se 1 (by rfl) ⟨2024918, by rfl⟩ : syracuseStep 2699891 = 4049837) B4049837
theorem B2306807 : Blo 798342 2306807 := bstep (se 1 (by rfl) ⟨1730105, by rfl⟩ : syracuseStep 2306807 = 3460211) B3460211
theorem B5780231 : Blo 798342 5780231 := bstep (se 1 (by rfl) ⟨4335173, by rfl⟩ : syracuseStep 5780231 = 8670347) B8670347
theorem B799599 : Blo 798342 799599 := bstep (se 1 (by rfl) ⟨599699, by rfl⟩ : syracuseStep 799599 = 1199399) B1199399
theorem B2700161 : Blo 798342 2700161 := bstep (se 2 (by rfl) ⟨1012560, by rfl⟩ : syracuseStep 2700161 = 2025121) B2025121
theorem B10269605 : Blo 798342 10269605 := bstep (se 4 (by rfl) ⟨962775, by rfl⟩ : syracuseStep 10269605 = 1925551) B1925551
theorem B799655 : Blo 798342 799655 := bstep (se 1 (by rfl) ⟨599741, by rfl⟩ : syracuseStep 799655 = 1199483) B1199483
theorem B799739 : Blo 798342 799739 := bstep (se 1 (by rfl) ⟨599804, by rfl⟩ : syracuseStep 799739 = 1199609) B1199609
theorem B799807 : Blo 798342 799807 := bstep (se 1 (by rfl) ⟨599855, by rfl⟩ : syracuseStep 799807 = 1199711) B1199711
theorem B799951 : Blo 798342 799951 := bstep (se 1 (by rfl) ⟨599963, by rfl⟩ : syracuseStep 799951 = 1199927) B1199927
theorem B800155 : Blo 798342 800155 := bstep (se 1 (by rfl) ⟨600116, by rfl⟩ : syracuseStep 800155 = 1200233) B1200233
theorem B800367 : Blo 798342 800367 := bstep (se 1 (by rfl) ⟨600275, by rfl⟩ : syracuseStep 800367 = 1200551) B1200551
theorem B800423 : Blo 798342 800423 := bstep (se 1 (by rfl) ⟨600317, by rfl⟩ : syracuseStep 800423 = 1200635) B1200635
theorem B2700971 : Blo 798342 2700971 := bstep (se 1 (by rfl) ⟨2025728, by rfl⟩ : syracuseStep 2700971 = 4051457) B4051457
theorem B4044491 : Blo 798342 4044491 := bstep (se 1 (by rfl) ⟨3033368, by rfl⟩ : syracuseStep 4044491 = 6066737) B6066737
theorem B800507 : Blo 798342 800507 := bstep (se 1 (by rfl) ⟨600380, by rfl⟩ : syracuseStep 800507 = 1200761) B1200761
theorem B800543 : Blo 798342 800543 := bstep (se 1 (by rfl) ⟨600407, by rfl⟩ : syracuseStep 800543 = 1200815) B1200815
theorem B898879 : Blo 798342 898879 := bstep (se 1 (by rfl) ⟨674159, by rfl⟩ : syracuseStep 898879 = 1348319) B1348319
theorem B800575 : Blo 798342 800575 := bstep (se 1 (by rfl) ⟨600431, by rfl⟩ : syracuseStep 800575 = 1200863) B1200863
theorem B2701295 : Blo 798342 2701295 := bstep (se 1 (by rfl) ⟨2025971, by rfl⟩ : syracuseStep 2701295 = 4051943) B4051943
theorem B800751 : Blo 798342 800751 := bstep (se 1 (by rfl) ⟨600563, by rfl⟩ : syracuseStep 800751 = 1201127) B1201127
theorem B899167 : Blo 798342 899167 := bstep (se 1 (by rfl) ⟨674375, by rfl⟩ : syracuseStep 899167 = 1348751) B1348751
theorem B800923 : Blo 798342 800923 := bstep (se 1 (by rfl) ⟨600692, by rfl⟩ : syracuseStep 800923 = 1201385) B1201385
theorem B800959 : Blo 798342 800959 := bstep (se 1 (by rfl) ⟨600719, by rfl⟩ : syracuseStep 800959 = 1201439) B1201439
theorem B2701511 : Blo 798342 2701511 := bstep (se 1 (by rfl) ⟨2026133, by rfl⟩ : syracuseStep 2701511 = 4052267) B4052267
theorem B17316119 : Blo 798342 17316119 := bstep (se 1 (by rfl) ⟨12987089, by rfl⟩ : syracuseStep 17316119 = 25974179) B25974179
theorem B801071 : Blo 798342 801071 := bstep (se 1 (by rfl) ⟨600803, by rfl⟩ : syracuseStep 801071 = 1201607) B1201607
theorem B801307 : Blo 798342 801307 := bstep (se 1 (by rfl) ⟨600980, by rfl⟩ : syracuseStep 801307 = 1201961) B1201961
theorem B801311 : Blo 798342 801311 := bstep (se 1 (by rfl) ⟨600983, by rfl⟩ : syracuseStep 801311 = 1201967) B1201967
theorem B4864711 : Blo 798342 4864711 := bstep (se 1 (by rfl) ⟨3648533, by rfl⟩ : syracuseStep 4864711 = 7297067) B7297067
theorem B29637413 : Blo 798342 29637413 := bstep (se 4 (by rfl) ⟨2778507, by rfl⟩ : syracuseStep 29637413 = 5557015) B5557015
theorem B2702159 : Blo 798342 2702159 := bstep (se 1 (by rfl) ⟨2026619, by rfl⟩ : syracuseStep 2702159 = 4053239) B4053239
theorem B801627 : Blo 798342 801627 := bstep (se 1 (by rfl) ⟨601220, by rfl⟩ : syracuseStep 801627 = 1202441) B1202441
theorem B2276201 : Blo 798342 2276201 := bstep (se 2 (by rfl) ⟨853575, by rfl⟩ : syracuseStep 2276201 = 1707151) B1707151
theorem B801695 : Blo 798342 801695 := bstep (se 1 (by rfl) ⟨601271, by rfl⟩ : syracuseStep 801695 = 1202543) B1202543
theorem B3849257 : Blo 798342 3849257 := bstep (se 2 (by rfl) ⟨1443471, by rfl⟩ : syracuseStep 3849257 = 2886943) B2886943
theorem B1522729 : Blo 798342 1522729 := bstep (se 2 (by rfl) ⟨571023, by rfl⟩ : syracuseStep 1522729 = 1142047) B1142047
theorem B801839 : Blo 798342 801839 := bstep (se 1 (by rfl) ⟨601379, by rfl⟩ : syracuseStep 801839 = 1202759) B1202759
theorem B801863 : Blo 798342 801863 := bstep (se 1 (by rfl) ⟨601397, by rfl⟩ : syracuseStep 801863 = 1202795) B1202795
theorem B2702483 : Blo 798342 2702483 := bstep (se 1 (by rfl) ⟨2026862, by rfl⟩ : syracuseStep 2702483 = 4053725) B4053725
theorem B77708483 : Blo 798342 77708483 := bstep (se 1 (by rfl) ⟨58281362, by rfl⟩ : syracuseStep 77708483 = 116562725) B116562725
theorem B900319 : Blo 798342 900319 := bstep (se 1 (by rfl) ⟨675239, by rfl⟩ : syracuseStep 900319 = 1350479) B1350479
theorem B802015 : Blo 798342 802015 := bstep (se 1 (by rfl) ⟨601511, by rfl⟩ : syracuseStep 802015 = 1203023) B1203023
theorem B2702753 : Blo 798342 2702753 := bstep (se 2 (by rfl) ⟨1013532, by rfl⟩ : syracuseStep 2702753 = 2027065) B2027065
theorem B4046273 : Blo 798342 4046273 := bstep (se 2 (by rfl) ⟨1517352, by rfl⟩ : syracuseStep 4046273 = 3034705) B3034705
theorem B802279 : Blo 798342 802279 := bstep (se 1 (by rfl) ⟨601709, by rfl⟩ : syracuseStep 802279 = 1203419) B1203419
theorem B8764973 : Blo 798342 8764973 := bstep (se 3 (by rfl) ⟨1643432, by rfl⟩ : syracuseStep 8764973 = 3286865) B3286865
theorem B2703293 : Blo 798342 2703293 := bstep (se 3 (by rfl) ⟨506867, by rfl⟩ : syracuseStep 2703293 = 1013735) B1013735
theorem B2736347 : Blo 798342 2736347 := bstep (se 1 (by rfl) ⟨2052260, by rfl⟩ : syracuseStep 2736347 = 4104521) B4104521
theorem B3424963 : Blo 798342 3424963 := bstep (se 1 (by rfl) ⟨2568722, by rfl⟩ : syracuseStep 3424963 = 5137445) B5137445
theorem B9716773 : Blo 798342 9716773 := bstep (se 4 (by rfl) ⟨910947, by rfl⟩ : syracuseStep 9716773 = 1821895) B1821895
theorem B2278763 : Blo 798342 2278763 := bstep (se 1 (by rfl) ⟨1709072, by rfl⟩ : syracuseStep 2278763 = 3418145) B3418145
theorem B2377067 : Blo 798342 2377067 := bstep (se 1 (by rfl) ⟨1782800, by rfl⟩ : syracuseStep 2377067 = 3565601) B3565601
theorem B1197689 : Blo 798342 1197689 := bstep (se 2 (by rfl) ⟨449133, by rfl⟩ : syracuseStep 1197689 = 898267) B898267
theorem B1197791 : Blo 798342 1197791 := bstep (se 1 (by rfl) ⟨898343, by rfl⟩ : syracuseStep 1197791 = 1796687) B1796687
theorem B2705183 : Blo 798342 2705183 := bstep (se 1 (by rfl) ⟨2028887, by rfl⟩ : syracuseStep 2705183 = 4057775) B4057775
theorem B1197887 : Blo 798342 1197887 := bstep (se 1 (by rfl) ⟨898415, by rfl⟩ : syracuseStep 1197887 = 1796831) B1796831
theorem B1198055 : Blo 798342 1198055 := bstep (se 1 (by rfl) ⟨898541, by rfl⟩ : syracuseStep 1198055 = 1797083) B1797083
theorem B2705399 : Blo 798342 2705399 := bstep (se 1 (by rfl) ⟨2029049, by rfl⟩ : syracuseStep 2705399 = 4058099) B4058099
theorem B1198073 : Blo 798342 1198073 := bstep (se 2 (by rfl) ⟨449277, by rfl⟩ : syracuseStep 1198073 = 898555) B898555
theorem B1198175 : Blo 798342 1198175 := bstep (se 1 (by rfl) ⟨898631, by rfl⟩ : syracuseStep 1198175 = 1797263) B1797263
theorem B1198235 : Blo 798342 1198235 := bstep (se 1 (by rfl) ⟨898676, by rfl⟩ : syracuseStep 1198235 = 1797353) B1797353
theorem B1198271 : Blo 798342 1198271 := bstep (se 1 (by rfl) ⟨898703, by rfl⟩ : syracuseStep 1198271 = 1797407) B1797407
theorem B1198313 : Blo 798342 1198313 := bstep (se 2 (by rfl) ⟨449367, by rfl⟩ : syracuseStep 1198313 = 898735) B898735
theorem B98388209 : Blo 798342 98388209 := bstep (se 2 (by rfl) ⟨36895578, by rfl⟩ : syracuseStep 98388209 = 73791157) B73791157
theorem B1198619 : Blo 798342 1198619 := bstep (se 1 (by rfl) ⟨898964, by rfl⟩ : syracuseStep 1198619 = 1797929) B1797929
theorem B1198697 : Blo 798342 1198697 := bstep (se 2 (by rfl) ⟨449511, by rfl⟩ : syracuseStep 1198697 = 899023) B899023
theorem B4049513 : Blo 798342 4049513 := bstep (se 2 (by rfl) ⟨1518567, by rfl⟩ : syracuseStep 4049513 = 3037135) B3037135
theorem B9718481 : Blo 798342 9718481 := bstep (se 2 (by rfl) ⟨3644430, by rfl⟩ : syracuseStep 9718481 = 7288861) B7288861
theorem B2706263 : Blo 798342 2706263 := bstep (se 1 (by rfl) ⟨2029697, by rfl⟩ : syracuseStep 2706263 = 4059395) B4059395
theorem B2706479 : Blo 798342 2706479 := bstep (se 1 (by rfl) ⟨2029859, by rfl⟩ : syracuseStep 2706479 = 4059719) B4059719
theorem B1199225 : Blo 798342 1199225 := bstep (se 2 (by rfl) ⟨449709, by rfl⟩ : syracuseStep 1199225 = 899419) B899419
theorem B1199327 : Blo 798342 1199327 := bstep (se 1 (by rfl) ⟨899495, by rfl⟩ : syracuseStep 1199327 = 1798991) B1798991
theorem B1199369 : Blo 798342 1199369 := bstep (se 2 (by rfl) ⟨449763, by rfl⟩ : syracuseStep 1199369 = 899527) B899527
theorem B1199471 : Blo 798342 1199471 := bstep (se 1 (by rfl) ⟨899603, by rfl⟩ : syracuseStep 1199471 = 1799207) B1799207
theorem B2706857 : Blo 798342 2706857 := bstep (se 2 (by rfl) ⟨1015071, by rfl⟩ : syracuseStep 2706857 = 2030143) B2030143
theorem B1920439 : Blo 798342 1920439 := bstep (se 1 (by rfl) ⟨1440329, by rfl⟩ : syracuseStep 1920439 = 2880659) B2880659
theorem B3853757 : Blo 798342 3853757 := bstep (se 3 (by rfl) ⟨722579, by rfl⟩ : syracuseStep 3853757 = 1445159) B1445159
theorem B1199591 : Blo 798342 1199591 := bstep (se 1 (by rfl) ⟨899693, by rfl⟩ : syracuseStep 1199591 = 1799387) B1799387
theorem B1199723 : Blo 798342 1199723 := bstep (se 1 (by rfl) ⟨899792, by rfl⟩ : syracuseStep 1199723 = 1799585) B1799585
theorem B11521709 : Blo 798342 11521709 := bstep (se 3 (by rfl) ⟨2160320, by rfl⟩ : syracuseStep 11521709 = 4320641) B4320641
theorem B1199849 : Blo 798342 1199849 := bstep (se 2 (by rfl) ⟨449943, by rfl⟩ : syracuseStep 1199849 = 899887) B899887
theorem B1199993 : Blo 798342 1199993 := bstep (se 2 (by rfl) ⟨449997, by rfl⟩ : syracuseStep 1199993 = 899995) B899995
theorem B4050809 : Blo 798342 4050809 := bstep (se 2 (by rfl) ⟨1519053, by rfl⟩ : syracuseStep 4050809 = 3038107) B3038107
theorem B2707343 : Blo 798342 2707343 := bstep (se 1 (by rfl) ⟨2030507, by rfl⟩ : syracuseStep 2707343 = 4061015) B4061015
theorem B1200095 : Blo 798342 1200095 := bstep (se 1 (by rfl) ⟨900071, by rfl⟩ : syracuseStep 1200095 = 1800143) B1800143
theorem B1200347 : Blo 798342 1200347 := bstep (se 1 (by rfl) ⟨900260, by rfl⟩ : syracuseStep 1200347 = 1800521) B1800521
theorem B1200359 : Blo 798342 1200359 := bstep (se 1 (by rfl) ⟨900269, by rfl⟩ : syracuseStep 1200359 = 1800539) B1800539
theorem B2707721 : Blo 798342 2707721 := bstep (se 2 (by rfl) ⟨1015395, by rfl⟩ : syracuseStep 2707721 = 2030791) B2030791
theorem B1200521 : Blo 798342 1200521 := bstep (se 2 (by rfl) ⟨450195, by rfl⟩ : syracuseStep 1200521 = 900391) B900391
theorem B1200617 : Blo 798342 1200617 := bstep (se 2 (by rfl) ⟨450231, by rfl⟩ : syracuseStep 1200617 = 900463) B900463
theorem B1200743 : Blo 798342 1200743 := bstep (se 1 (by rfl) ⟨900557, by rfl⟩ : syracuseStep 1200743 = 1801115) B1801115
theorem B6083261 : Blo 798342 6083261 := bstep (se 3 (by rfl) ⟨1140611, by rfl⟩ : syracuseStep 6083261 = 2281223) B2281223
theorem B1200875 : Blo 798342 1200875 := bstep (se 1 (by rfl) ⟨900656, by rfl⟩ : syracuseStep 1200875 = 1801313) B1801313
theorem B1200905 : Blo 798342 1200905 := bstep (se 2 (by rfl) ⟨450339, by rfl⟩ : syracuseStep 1200905 = 900679) B900679
theorem B1201007 : Blo 798342 1201007 := bstep (se 1 (by rfl) ⟨900755, by rfl⟩ : syracuseStep 1201007 = 1801511) B1801511
theorem B18469883 : Blo 798342 18469883 := bstep (se 1 (by rfl) ⟨13852412, by rfl⟩ : syracuseStep 18469883 = 27704825) B27704825
theorem B1201259 : Blo 798342 1201259 := bstep (se 1 (by rfl) ⟨900944, by rfl⟩ : syracuseStep 1201259 = 1801889) B1801889
theorem B1201499 : Blo 798342 1201499 := bstep (se 1 (by rfl) ⟨901124, by rfl⟩ : syracuseStep 1201499 = 1802249) B1802249
theorem B5133881 : Blo 798342 5133881 := bstep (se 2 (by rfl) ⟨1925205, by rfl⟩ : syracuseStep 5133881 = 3850411) B3850411
theorem B1234543 : Blo 798342 1234543 := bstep (se 1 (by rfl) ⟨925907, by rfl⟩ : syracuseStep 1234543 = 1851815) B1851815
theorem B1201775 : Blo 798342 1201775 := bstep (se 1 (by rfl) ⟨901331, by rfl⟩ : syracuseStep 1201775 = 1802663) B1802663
theorem B1201847 : Blo 798342 1201847 := bstep (se 1 (by rfl) ⟨901385, by rfl⟩ : syracuseStep 1201847 = 1802771) B1802771
theorem B1201883 : Blo 798342 1201883 := bstep (se 1 (by rfl) ⟨901412, by rfl⟩ : syracuseStep 1201883 = 1802825) B1802825
theorem B2021183 : Blo 798342 2021183 := bstep (se 1 (by rfl) ⟨1515887, by rfl⟩ : syracuseStep 2021183 = 3031775) B3031775
theorem B1202057 : Blo 798342 1202057 := bstep (se 2 (by rfl) ⟨450771, by rfl⟩ : syracuseStep 1202057 = 901543) B901543
theorem B1202159 : Blo 798342 1202159 := bstep (se 1 (by rfl) ⟨901619, by rfl⟩ : syracuseStep 1202159 = 1803239) B1803239
theorem B2021537 : Blo 798342 2021537 := bstep (se 2 (by rfl) ⟨758076, by rfl⟩ : syracuseStep 2021537 = 1516153) B1516153
theorem B10246337 : Blo 798342 10246337 := bstep (se 2 (by rfl) ⟨3842376, by rfl⟩ : syracuseStep 10246337 = 7684753) B7684753
theorem B1202411 : Blo 798342 1202411 := bstep (se 1 (by rfl) ⟨901808, by rfl⟩ : syracuseStep 1202411 = 1803617) B1803617
theorem B21911795 : Blo 798342 21911795 := bstep (se 1 (by rfl) ⟨16433846, by rfl⟩ : syracuseStep 21911795 = 32867693) B32867693
theorem B1202471 : Blo 798342 1202471 := bstep (se 1 (by rfl) ⟨901853, by rfl⟩ : syracuseStep 1202471 = 1803707) B1803707
theorem B1366313 : Blo 798342 1366313 := bstep (se 2 (by rfl) ⟨512367, by rfl⟩ : syracuseStep 1366313 = 1024735) B1024735
theorem B1202555 : Blo 798342 1202555 := bstep (se 1 (by rfl) ⟨901916, by rfl⟩ : syracuseStep 1202555 = 1803833) B1803833
theorem B2808377 : Blo 798342 2808377 := bstep (se 2 (by rfl) ⟨1053141, by rfl⟩ : syracuseStep 2808377 = 2106283) B2106283
theorem B20535929 : Blo 798342 20535929 := bstep (se 2 (by rfl) ⟨7700973, by rfl⟩ : syracuseStep 20535929 = 15401947) B15401947
theorem B5134985 : Blo 798342 5134985 := bstep (se 2 (by rfl) ⟨1925619, by rfl⟩ : syracuseStep 5134985 = 3851239) B3851239
theorem B1202825 : Blo 798342 1202825 := bstep (se 2 (by rfl) ⟨451059, by rfl⟩ : syracuseStep 1202825 = 902119) B902119
theorem B1202999 : Blo 798342 1202999 := bstep (se 1 (by rfl) ⟨902249, by rfl⟩ : syracuseStep 1202999 = 1804499) B1804499
theorem B29547341 : Blo 798342 29547341 := bstep (se 3 (by rfl) ⟨5540126, by rfl⟩ : syracuseStep 29547341 = 11080253) B11080253
theorem B1203035 : Blo 798342 1203035 := bstep (se 1 (by rfl) ⟨902276, by rfl⟩ : syracuseStep 1203035 = 1804553) B1804553
theorem B5135213 : Blo 798342 5135213 := bstep (se 3 (by rfl) ⟨962852, by rfl⟩ : syracuseStep 5135213 = 1925705) B1925705
theorem B1203179 : Blo 798342 1203179 := bstep (se 1 (by rfl) ⟨902384, by rfl⟩ : syracuseStep 1203179 = 1804769) B1804769
theorem B14605379 : Blo 798342 14605379 := bstep (se 1 (by rfl) ⟨10954034, by rfl⟩ : syracuseStep 14605379 = 21908069) B21908069
theorem B2022529 : Blo 798342 2022529 := bstep (se 2 (by rfl) ⟨758448, by rfl⟩ : syracuseStep 2022529 = 1516897) B1516897
theorem B1203383 : Blo 798342 1203383 := bstep (se 1 (by rfl) ⟨902537, by rfl⟩ : syracuseStep 1203383 = 1805075) B1805075
theorem B21880685 : Blo 798342 21880685 := bstep (se 3 (by rfl) ⟨4102628, by rfl⟩ : syracuseStep 21880685 = 8205257) B8205257
theorem B2023339 : Blo 798342 2023339 := bstep (se 1 (by rfl) ⟨1517504, by rfl⟩ : syracuseStep 2023339 = 3035009) B3035009
theorem B5136443 : Blo 798342 5136443 := bstep (se 1 (by rfl) ⟨3852332, by rfl⟩ : syracuseStep 5136443 = 7704665) B7704665
theorem B2023643 : Blo 798342 2023643 := bstep (se 1 (by rfl) ⟨1517732, by rfl⟩ : syracuseStep 2023643 = 3035465) B3035465
theorem B25977185 : Blo 798342 25977185 := bstep (se 2 (by rfl) ⟨9741444, by rfl⟩ : syracuseStep 25977185 = 19482889) B19482889
theorem B2024473 : Blo 798342 2024473 := bstep (se 2 (by rfl) ⟨759177, by rfl⟩ : syracuseStep 2024473 = 1518355) B1518355
theorem B2024777 : Blo 798342 2024777 := bstep (se 2 (by rfl) ⟨759291, by rfl⟩ : syracuseStep 2024777 = 1518583) B1518583
theorem B910747 : Blo 798342 910747 := bstep (se 1 (by rfl) ⟨683060, by rfl⟩ : syracuseStep 910747 = 1366121) B1366121
theorem B2025071 : Blo 798342 2025071 := bstep (se 1 (by rfl) ⟨1518803, by rfl⟩ : syracuseStep 2025071 = 3037607) B3037607
theorem B1140475 : Blo 798342 1140475 := bstep (se 1 (by rfl) ⟨855356, by rfl⟩ : syracuseStep 1140475 = 1710713) B1710713
theorem B11856019 : Blo 798342 11856019 := bstep (se 1 (by rfl) ⟨8892014, by rfl⟩ : syracuseStep 11856019 = 17784029) B17784029
theorem B3041495 : Blo 798342 3041495 := bstep (se 1 (by rfl) ⟨2281121, by rfl⟩ : syracuseStep 3041495 = 4562243) B4562243
theorem B1796345 : Blo 798342 1796345 := bstep (se 2 (by rfl) ⟨673629, by rfl⟩ : syracuseStep 1796345 = 1347259) B1347259
theorem B1796399 : Blo 798342 1796399 := bstep (se 1 (by rfl) ⟨1347299, by rfl⟩ : syracuseStep 1796399 = 2694599) B2694599
theorem B10971449 : Blo 798342 10971449 := bstep (se 2 (by rfl) ⟨4114293, by rfl⟩ : syracuseStep 10971449 = 8228587) B8228587
theorem B4680119 : Blo 798342 4680119 := bstep (se 1 (by rfl) ⟨3510089, by rfl⟩ : syracuseStep 4680119 = 7020179) B7020179
theorem B4549121 : Blo 798342 4549121 := bstep (se 2 (by rfl) ⟨1705920, by rfl⟩ : syracuseStep 4549121 = 3411841) B3411841
theorem B1796615 : Blo 798342 1796615 := bstep (se 1 (by rfl) ⟨1347461, by rfl⟩ : syracuseStep 1796615 = 2694923) B2694923
theorem B14805605 : Blo 798342 14805605 := bstep (se 4 (by rfl) ⟨1388025, by rfl⟩ : syracuseStep 14805605 = 2776051) B2776051
theorem B1796795 : Blo 798342 1796795 := bstep (se 1 (by rfl) ⟨1347596, by rfl⟩ : syracuseStep 1796795 = 2695193) B2695193
theorem B1797623 : Blo 798342 1797623 := bstep (se 1 (by rfl) ⟨1348217, by rfl⟩ : syracuseStep 1797623 = 2696435) B2696435
theorem B1797695 : Blo 798342 1797695 := bstep (se 1 (by rfl) ⟨1348271, by rfl⟩ : syracuseStep 1797695 = 2696543) B2696543
theorem B29192075 : Blo 798342 29192075 := bstep (se 1 (by rfl) ⟨21894056, by rfl⟩ : syracuseStep 29192075 = 43788113) B43788113
theorem B1011943 : Blo 798342 1011943 := bstep (se 1 (by rfl) ⟨758957, by rfl⟩ : syracuseStep 1011943 = 1517915) B1517915
theorem B6091037 : Blo 798342 6091037 := bstep (se 3 (by rfl) ⟨1142069, by rfl⟩ : syracuseStep 6091037 = 2284139) B2284139
theorem B6844763 : Blo 798342 6844763 := bstep (se 1 (by rfl) ⟨5133572, by rfl⟩ : syracuseStep 6844763 = 10267145) B10267145
theorem B4321765 : Blo 798342 4321765 := bstep (se 4 (by rfl) ⟨405165, by rfl⟩ : syracuseStep 4321765 = 810331) B810331
theorem B1798649 : Blo 798342 1798649 := bstep (se 2 (by rfl) ⟨674493, by rfl⟩ : syracuseStep 1798649 = 1348987) B1348987
theorem B1798739 : Blo 798342 1798739 := bstep (se 1 (by rfl) ⟨1349054, by rfl⟩ : syracuseStep 1798739 = 2698109) B2698109
theorem B1798919 : Blo 798342 1798919 := bstep (se 1 (by rfl) ⟨1349189, by rfl⟩ : syracuseStep 1798919 = 2698379) B2698379
theorem B1012591 : Blo 798342 1012591 := bstep (se 1 (by rfl) ⟨759443, by rfl⟩ : syracuseStep 1012591 = 1518887) B1518887
theorem B8221769 : Blo 798342 8221769 := bstep (se 2 (by rfl) ⟨3083163, by rfl⟩ : syracuseStep 8221769 = 6166327) B6166327
theorem B3044425 : Blo 798342 3044425 := bstep (se 2 (by rfl) ⟨1141659, by rfl⟩ : syracuseStep 3044425 = 2283319) B2283319
theorem B10974503 : Blo 798342 10974503 := bstep (se 1 (by rfl) ⟨8230877, by rfl⟩ : syracuseStep 10974503 = 16461755) B16461755
theorem B5469491 : Blo 798342 5469491 := bstep (se 1 (by rfl) ⟨4102118, by rfl⟩ : syracuseStep 5469491 = 8204237) B8204237
theorem B1439147 : Blo 798342 1439147 := bstep (se 1 (by rfl) ⟨1079360, by rfl⟩ : syracuseStep 1439147 = 2158721) B2158721
theorem B1013467 : Blo 798342 1013467 := bstep (se 1 (by rfl) ⟨760100, by rfl⟩ : syracuseStep 1013467 = 1520201) B1520201
theorem B1799999 : Blo 798342 1799999 := bstep (se 1 (by rfl) ⟨1349999, by rfl⟩ : syracuseStep 1799999 = 2699999) B2699999
theorem B10417997 : Blo 798342 10417997 := bstep (se 3 (by rfl) ⟨1953374, by rfl⟩ : syracuseStep 10417997 = 3906749) B3906749
theorem B17332217 : Blo 798342 17332217 := bstep (se 2 (by rfl) ⟨6499581, by rfl⟩ : syracuseStep 17332217 = 12999163) B12999163
theorem B4061177 : Blo 798342 4061177 := bstep (se 2 (by rfl) ⟨1522941, by rfl⟩ : syracuseStep 4061177 = 3045883) B3045883
theorem B4552787 : Blo 798342 4552787 := bstep (se 1 (by rfl) ⟨3414590, by rfl⟩ : syracuseStep 4552787 = 6829181) B6829181
theorem B1800287 : Blo 798342 1800287 := bstep (se 1 (by rfl) ⟨1350215, by rfl⟩ : syracuseStep 1800287 = 2700431) B2700431
theorem B4553495 : Blo 798342 4553495 := bstep (se 1 (by rfl) ⟨3415121, by rfl⟩ : syracuseStep 4553495 = 6830243) B6830243
theorem B1801043 : Blo 798342 1801043 := bstep (se 1 (by rfl) ⟨1350782, by rfl⟩ : syracuseStep 1801043 = 2701565) B2701565
theorem B1014763 : Blo 798342 1014763 := bstep (se 1 (by rfl) ⟨761072, by rfl⟩ : syracuseStep 1014763 = 1522145) B1522145
theorem B4324535 : Blo 798342 4324535 := bstep (se 1 (by rfl) ⟨3243401, by rfl⟩ : syracuseStep 4324535 = 6486803) B6486803
theorem B3472679 : Blo 798342 3472679 := bstep (se 1 (by rfl) ⟨2604509, by rfl⟩ : syracuseStep 3472679 = 5209019) B5209019
theorem B1801583 : Blo 798342 1801583 := bstep (se 1 (by rfl) ⟨1351187, by rfl⟩ : syracuseStep 1801583 = 2702375) B2702375
theorem B1801871 : Blo 798342 1801871 := bstep (se 1 (by rfl) ⟨1351403, by rfl⟩ : syracuseStep 1801871 = 2702807) B2702807
theorem B4554427 : Blo 798342 4554427 := bstep (se 1 (by rfl) ⟨3415820, by rfl⟩ : syracuseStep 4554427 = 6831641) B6831641
theorem B1801961 : Blo 798342 1801961 := bstep (se 2 (by rfl) ⟨675735, by rfl⟩ : syracuseStep 1801961 = 1351471) B1351471
theorem B2884175 : Blo 798342 2884175 := bstep (se 1 (by rfl) ⟨2163131, by rfl⟩ : syracuseStep 2884175 = 4326263) B4326263
theorem B11534969 : Blo 798342 11534969 := bstep (se 2 (by rfl) ⟨4325613, by rfl⟩ : syracuseStep 11534969 = 8651227) B8651227
theorem B1803455 : Blo 798342 1803455 := bstep (se 1 (by rfl) ⟨1352591, by rfl⟩ : syracuseStep 1803455 = 2705183) B2705183
theorem B1803599 : Blo 798342 1803599 := bstep (se 1 (by rfl) ⟨1352699, by rfl⟩ : syracuseStep 1803599 = 2705399) B2705399
theorem B1443241 : Blo 798342 1443241 := bstep (se 2 (by rfl) ⟨541215, by rfl⟩ : syracuseStep 1443241 = 1082431) B1082431
theorem B1803689 : Blo 798342 1803689 := bstep (se 2 (by rfl) ⟨676383, by rfl⟩ : syracuseStep 1803689 = 1352767) B1352767
theorem B1804175 : Blo 798342 1804175 := bstep (se 1 (by rfl) ⟨1353131, by rfl⟩ : syracuseStep 1804175 = 2706263) B2706263
theorem B1706015 : Blo 798342 1706015 := bstep (se 1 (by rfl) ⟨1279511, by rfl⟩ : syracuseStep 1706015 = 2559023) B2559023
theorem B1804319 : Blo 798342 1804319 := bstep (se 1 (by rfl) ⟨1353239, by rfl⟩ : syracuseStep 1804319 = 2706479) B2706479
theorem B1804571 : Blo 798342 1804571 := bstep (se 1 (by rfl) ⟨1353428, by rfl⟩ : syracuseStep 1804571 = 2706857) B2706857
theorem B13699367 : Blo 798342 13699367 := bstep (se 1 (by rfl) ⟨10274525, by rfl⟩ : syracuseStep 13699367 = 20549051) B20549051
theorem B8784433 : Blo 798342 8784433 := bstep (se 2 (by rfl) ⟨3294162, by rfl⟩ : syracuseStep 8784433 = 6588325) B6588325
theorem B1804895 : Blo 798342 1804895 := bstep (se 1 (by rfl) ⟨1353671, by rfl⟩ : syracuseStep 1804895 = 2707343) B2707343
theorem B6163127 : Blo 798342 6163127 := bstep (se 1 (by rfl) ⟨4622345, by rfl⟩ : syracuseStep 6163127 = 9244691) B9244691
theorem B1805147 : Blo 798342 1805147 := bstep (se 1 (by rfl) ⟨1353860, by rfl⟩ : syracuseStep 1805147 = 2707721) B2707721
theorem B3247229 : Blo 798342 3247229 := bstep (se 3 (by rfl) ⟨608855, by rfl⟩ : syracuseStep 3247229 = 1217711) B1217711
theorem B14585309 : Blo 798342 14585309 := bstep (se 3 (by rfl) ⟨2734745, by rfl⟩ : syracuseStep 14585309 = 5469491) B5469491
theorem B16453135 : Blo 798342 16453135 := bstep (se 1 (by rfl) ⟨12339851, by rfl⟩ : syracuseStep 16453135 = 24679703) B24679703
theorem B3837725 : Blo 798342 3837725 := bstep (se 3 (by rfl) ⟨719573, by rfl⟩ : syracuseStep 3837725 = 1439147) B1439147
theorem B1347455 : Blo 798342 1347455 := bstep (se 1 (by rfl) ⟨1010591, by rfl⟩ : syracuseStep 1347455 = 2021183) B2021183
theorem B1347691 : Blo 798342 1347691 := bstep (se 1 (by rfl) ⟨1010768, by rfl⟩ : syracuseStep 1347691 = 2021537) B2021537
theorem B1872251 : Blo 798342 1872251 := bstep (se 1 (by rfl) ⟨1404188, by rfl⟩ : syracuseStep 1872251 = 2808377) B2808377
theorem B19698227 : Blo 798342 19698227 := bstep (se 1 (by rfl) ⟨14773670, by rfl⟩ : syracuseStep 19698227 = 29547341) B29547341
theorem B2560585 : Blo 798342 2560585 := bstep (se 2 (by rfl) ⟨960219, by rfl⟩ : syracuseStep 2560585 = 1920439) B1920439
theorem B6820433 : Blo 798342 6820433 := bstep (se 2 (by rfl) ⟨2557662, by rfl⟩ : syracuseStep 6820433 = 5115325) B5115325
theorem B9736919 : Blo 798342 9736919 := bstep (se 1 (by rfl) ⟨7302689, by rfl⟩ : syracuseStep 9736919 = 14605379) B14605379
theorem B1709039 : Blo 798342 1709039 := bstep (se 1 (by rfl) ⟨1281779, by rfl⟩ : syracuseStep 1709039 = 2563559) B2563559
theorem B21894263 : Blo 798342 21894263 := bstep (se 1 (by rfl) ⟨16420697, by rfl⟩ : syracuseStep 21894263 = 32841395) B32841395
theorem B14587123 : Blo 798342 14587123 := bstep (se 1 (by rfl) ⟨10940342, by rfl⟩ : syracuseStep 14587123 = 21880685) B21880685
theorem B1349095 : Blo 798342 1349095 := bstep (se 1 (by rfl) ⟨1011821, by rfl⟩ : syracuseStep 1349095 = 2023643) B2023643
theorem B3413497 : Blo 798342 3413497 := bstep (se 2 (by rfl) ⟨1280061, by rfl⟩ : syracuseStep 3413497 = 2560123) B2560123
theorem B1349257 : Blo 798342 1349257 := bstep (se 2 (by rfl) ⟨505971, by rfl⟩ : syracuseStep 1349257 = 1011943) B1011943
theorem B12949469 : Blo 798342 12949469 := bstep (se 3 (by rfl) ⟨2428025, by rfl⟩ : syracuseStep 12949469 = 4856051) B4856051
theorem B46176317 : Blo 798342 46176317 := bstep (se 3 (by rfl) ⟨8658059, by rfl⟩ : syracuseStep 46176317 = 17316119) B17316119
theorem B26024003 : Blo 798342 26024003 := bstep (se 1 (by rfl) ⟨19518002, by rfl⟩ : syracuseStep 26024003 = 39036005) B39036005
theorem B3643501 : Blo 798342 3643501 := bstep (se 3 (by rfl) ⟨683156, by rfl⟩ : syracuseStep 3643501 = 1366313) B1366313
theorem B1349851 : Blo 798342 1349851 := bstep (se 1 (by rfl) ⟨1012388, by rfl⟩ : syracuseStep 1349851 = 2024777) B2024777
theorem B1350047 : Blo 798342 1350047 := bstep (se 1 (by rfl) ⟨1012535, by rfl⟩ : syracuseStep 1350047 = 2025071) B2025071
theorem B1350121 : Blo 798342 1350121 := bstep (se 2 (by rfl) ⟨506295, by rfl⟩ : syracuseStep 1350121 = 1012591) B1012591
theorem B7314299 : Blo 798342 7314299 := bstep (se 1 (by rfl) ⟨5485724, by rfl⟩ : syracuseStep 7314299 = 10971449) B10971449
theorem B3120079 : Blo 798342 3120079 := bstep (se 1 (by rfl) ⟨2340059, by rfl⟩ : syracuseStep 3120079 = 4680119) B4680119
theorem B9870403 : Blo 798342 9870403 := bstep (se 1 (by rfl) ⟨7402802, by rfl⟩ : syracuseStep 9870403 = 14805605) B14805605
theorem B4857317 : Blo 798342 4857317 := bstep (se 4 (by rfl) ⟨455373, by rfl⟩ : syracuseStep 4857317 = 910747) B910747
theorem B1646057 : Blo 798342 1646057 := bstep (se 2 (by rfl) ⟨617271, by rfl⟩ : syracuseStep 1646057 = 1234543) B1234543
theorem B1351289 : Blo 798342 1351289 := bstep (se 2 (by rfl) ⟨506733, by rfl⟩ : syracuseStep 1351289 = 1013467) B1013467
theorem B4563175 : Blo 798342 4563175 := bstep (se 1 (by rfl) ⟨3422381, by rfl⟩ : syracuseStep 4563175 = 6844763) B6844763
theorem B5481179 : Blo 798342 5481179 := bstep (se 1 (by rfl) ⟨4110884, by rfl⟩ : syracuseStep 5481179 = 8221769) B8221769
theorem B7316335 : Blo 798342 7316335 := bstep (se 1 (by rfl) ⟨5487251, by rfl⟩ : syracuseStep 7316335 = 10974503) B10974503
theorem B3253117 : Blo 798342 3253117 := bstep (se 3 (by rfl) ⟨609959, by rfl⟩ : syracuseStep 3253117 = 1219919) B1219919
theorem B2696327 : Blo 798342 2696327 := bstep (se 1 (by rfl) ⟨2022245, by rfl⟩ : syracuseStep 2696327 = 4044491) B4044491
theorem B1353017 : Blo 798342 1353017 := bstep (se 2 (by rfl) ⟨507381, by rfl⟩ : syracuseStep 1353017 = 1014763) B1014763
theorem B2696705 : Blo 798342 2696705 := bstep (se 2 (by rfl) ⟨1011264, by rfl⟩ : syracuseStep 2696705 = 2022529) B2022529
theorem B27666137 : Blo 798342 27666137 := bstep (se 2 (by rfl) ⟨10374801, by rfl⟩ : syracuseStep 27666137 = 20749603) B20749603
theorem B1517467 : Blo 798342 1517467 := bstep (se 1 (by rfl) ⟨1138100, by rfl⟩ : syracuseStep 1517467 = 2276201) B2276201
theorem B2566171 : Blo 798342 2566171 := bstep (se 1 (by rfl) ⟨1924628, by rfl⟩ : syracuseStep 2566171 = 3849257) B3849257
theorem B6072569 : Blo 798342 6072569 := bstep (se 2 (by rfl) ⟨2277213, by rfl⟩ : syracuseStep 6072569 = 4554427) B4554427
theorem B2697515 : Blo 798342 2697515 := bstep (se 1 (by rfl) ⟨2023136, by rfl⟩ : syracuseStep 2697515 = 4046273) B4046273
theorem B5843315 : Blo 798342 5843315 := bstep (se 1 (by rfl) ⟨4382486, by rfl⟩ : syracuseStep 5843315 = 8764973) B8764973
theorem B2697785 : Blo 798342 2697785 := bstep (se 2 (by rfl) ⟨1011669, by rfl⟩ : syracuseStep 2697785 = 2023339) B2023339
theorem B5123321 : Blo 798342 5123321 := bstep (se 2 (by rfl) ⟨1921245, by rfl⟩ : syracuseStep 5123321 = 3842491) B3842491
theorem B1519175 : Blo 798342 1519175 := bstep (se 1 (by rfl) ⟨1139381, by rfl⟩ : syracuseStep 1519175 = 2278763) B2278763
theorem B4566617 : Blo 798342 4566617 := bstep (se 2 (by rfl) ⟨1712481, by rfl⟩ : syracuseStep 4566617 = 3424963) B3424963
theorem B798459 : Blo 798342 798459 := bstep (se 1 (by rfl) ⟨598844, by rfl⟩ : syracuseStep 798459 = 1197689) B1197689
theorem B798527 : Blo 798342 798527 := bstep (se 1 (by rfl) ⟨598895, by rfl⟩ : syracuseStep 798527 = 1197791) B1197791
theorem B798591 : Blo 798342 798591 := bstep (se 1 (by rfl) ⟨598943, by rfl⟩ : syracuseStep 798591 = 1197887) B1197887
theorem B798703 : Blo 798342 798703 := bstep (se 1 (by rfl) ⟨599027, by rfl⟩ : syracuseStep 798703 = 1198055) B1198055
theorem B798715 : Blo 798342 798715 := bstep (se 1 (by rfl) ⟨599036, by rfl⟩ : syracuseStep 798715 = 1198073) B1198073
theorem B2699297 : Blo 798342 2699297 := bstep (se 2 (by rfl) ⟨1012236, by rfl⟩ : syracuseStep 2699297 = 2024473) B2024473
theorem B12955697 : Blo 798342 12955697 := bstep (se 2 (by rfl) ⟨4858386, by rfl⟩ : syracuseStep 12955697 = 9716773) B9716773
theorem B798783 : Blo 798342 798783 := bstep (se 1 (by rfl) ⟨599087, by rfl⟩ : syracuseStep 798783 = 1198175) B1198175
theorem B798823 : Blo 798342 798823 := bstep (se 1 (by rfl) ⟨599117, by rfl⟩ : syracuseStep 798823 = 1198235) B1198235
theorem B798847 : Blo 798342 798847 := bstep (se 1 (by rfl) ⟨599135, by rfl⟩ : syracuseStep 798847 = 1198271) B1198271
theorem B798875 : Blo 798342 798875 := bstep (se 1 (by rfl) ⟨599156, by rfl⟩ : syracuseStep 798875 = 1198313) B1198313
theorem B19509443 : Blo 798342 19509443 := bstep (se 1 (by rfl) ⟨14632082, by rfl⟩ : syracuseStep 19509443 = 29264165) B29264165
theorem B799079 : Blo 798342 799079 := bstep (se 1 (by rfl) ⟨599309, by rfl⟩ : syracuseStep 799079 = 1198619) B1198619
theorem B799131 : Blo 798342 799131 := bstep (se 1 (by rfl) ⟨599348, by rfl⟩ : syracuseStep 799131 = 1198697) B1198697
theorem B2699675 : Blo 798342 2699675 := bstep (se 1 (by rfl) ⟨2024756, by rfl⟩ : syracuseStep 2699675 = 4049513) B4049513
theorem B799483 : Blo 798342 799483 := bstep (se 1 (by rfl) ⟨599612, by rfl⟩ : syracuseStep 799483 = 1199225) B1199225
theorem B799551 : Blo 798342 799551 := bstep (se 1 (by rfl) ⟨599663, by rfl⟩ : syracuseStep 799551 = 1199327) B1199327
theorem B799579 : Blo 798342 799579 := bstep (se 1 (by rfl) ⟨599684, by rfl⟩ : syracuseStep 799579 = 1199369) B1199369
theorem B799647 : Blo 798342 799647 := bstep (se 1 (by rfl) ⟨599735, by rfl⟩ : syracuseStep 799647 = 1199471) B1199471
theorem B2569171 : Blo 798342 2569171 := bstep (se 1 (by rfl) ⟨1926878, by rfl⟩ : syracuseStep 2569171 = 3853757) B3853757
theorem B799727 : Blo 798342 799727 := bstep (se 1 (by rfl) ⟨599795, by rfl⟩ : syracuseStep 799727 = 1199591) B1199591
theorem B1520633 : Blo 798342 1520633 := bstep (se 2 (by rfl) ⟨570237, by rfl⟩ : syracuseStep 1520633 = 1140475) B1140475
theorem B799815 : Blo 798342 799815 := bstep (se 1 (by rfl) ⟨599861, by rfl⟩ : syracuseStep 799815 = 1199723) B1199723
theorem B7681139 : Blo 798342 7681139 := bstep (se 1 (by rfl) ⟨5760854, by rfl⟩ : syracuseStep 7681139 = 11521709) B11521709
theorem B799899 : Blo 798342 799899 := bstep (se 1 (by rfl) ⟨599924, by rfl⟩ : syracuseStep 799899 = 1199849) B1199849
theorem B799995 : Blo 798342 799995 := bstep (se 1 (by rfl) ⟨599996, by rfl⟩ : syracuseStep 799995 = 1199993) B1199993
theorem B2700539 : Blo 798342 2700539 := bstep (se 1 (by rfl) ⟨2025404, by rfl⟩ : syracuseStep 2700539 = 4050809) B4050809
theorem B800063 : Blo 798342 800063 := bstep (se 1 (by rfl) ⟨600047, by rfl⟩ : syracuseStep 800063 = 1200095) B1200095
theorem B4568507 : Blo 798342 4568507 := bstep (se 1 (by rfl) ⟨3426380, by rfl⟩ : syracuseStep 4568507 = 6852761) B6852761
theorem B800231 : Blo 798342 800231 := bstep (se 1 (by rfl) ⟨600173, by rfl⟩ : syracuseStep 800231 = 1200347) B1200347
theorem B800239 : Blo 798342 800239 := bstep (se 1 (by rfl) ⟨600179, by rfl⟩ : syracuseStep 800239 = 1200359) B1200359
theorem B15808025 : Blo 798342 15808025 := bstep (se 2 (by rfl) ⟨5928009, by rfl⟩ : syracuseStep 15808025 = 11856019) B11856019
theorem B800347 : Blo 798342 800347 := bstep (se 1 (by rfl) ⟨600260, by rfl⟩ : syracuseStep 800347 = 1200521) B1200521
theorem B2274959 : Blo 798342 2274959 := bstep (se 1 (by rfl) ⟨1706219, by rfl⟩ : syracuseStep 2274959 = 3412439) B3412439
theorem B800411 : Blo 798342 800411 := bstep (se 1 (by rfl) ⟨600308, by rfl⟩ : syracuseStep 800411 = 1200617) B1200617
theorem B800495 : Blo 798342 800495 := bstep (se 1 (by rfl) ⟨600371, by rfl⟩ : syracuseStep 800495 = 1200743) B1200743
theorem B6829865 : Blo 798342 6829865 := bstep (se 2 (by rfl) ⟨2561199, by rfl⟩ : syracuseStep 6829865 = 5122399) B5122399
theorem B800583 : Blo 798342 800583 := bstep (se 1 (by rfl) ⟨600437, by rfl⟩ : syracuseStep 800583 = 1200875) B1200875
theorem B800603 : Blo 798342 800603 := bstep (se 1 (by rfl) ⟨600452, by rfl⟩ : syracuseStep 800603 = 1200905) B1200905
theorem B800671 : Blo 798342 800671 := bstep (se 1 (by rfl) ⟨600503, by rfl⟩ : syracuseStep 800671 = 1201007) B1201007
theorem B4569007 : Blo 798342 4569007 := bstep (se 1 (by rfl) ⟨3426755, by rfl⟩ : syracuseStep 4569007 = 6853511) B6853511
theorem B6076457 : Blo 798342 6076457 := bstep (se 2 (by rfl) ⟨2278671, by rfl⟩ : syracuseStep 6076457 = 4557343) B4557343
theorem B800839 : Blo 798342 800839 := bstep (se 1 (by rfl) ⟨600629, by rfl⟩ : syracuseStep 800839 = 1201259) B1201259
theorem B800999 : Blo 798342 800999 := bstep (se 1 (by rfl) ⟨600749, by rfl⟩ : syracuseStep 800999 = 1201499) B1201499
theorem B6338845 : Blo 798342 6338845 := bstep (se 3 (by rfl) ⟨1188533, by rfl⟩ : syracuseStep 6338845 = 2377067) B2377067
theorem B3422587 : Blo 798342 3422587 := bstep (se 1 (by rfl) ⟨2566940, by rfl⟩ : syracuseStep 3422587 = 5133881) B5133881
theorem B801183 : Blo 798342 801183 := bstep (se 1 (by rfl) ⟨600887, by rfl⟩ : syracuseStep 801183 = 1201775) B1201775
theorem B801231 : Blo 798342 801231 := bstep (se 1 (by rfl) ⟨600923, by rfl⟩ : syracuseStep 801231 = 1201847) B1201847
theorem B801255 : Blo 798342 801255 := bstep (se 1 (by rfl) ⟨600941, by rfl⟩ : syracuseStep 801255 = 1201883) B1201883
theorem B2275847 : Blo 798342 2275847 := bstep (se 1 (by rfl) ⟨1706885, by rfl⟩ : syracuseStep 2275847 = 3413771) B3413771
theorem B801371 : Blo 798342 801371 := bstep (se 1 (by rfl) ⟨601028, by rfl⟩ : syracuseStep 801371 = 1202057) B1202057
theorem B899743 : Blo 798342 899743 := bstep (se 1 (by rfl) ⟨674807, by rfl⟩ : syracuseStep 899743 = 1349615) B1349615
theorem B801439 : Blo 798342 801439 := bstep (se 1 (by rfl) ⟨601079, by rfl⟩ : syracuseStep 801439 = 1202159) B1202159
theorem B6830891 : Blo 798342 6830891 := bstep (se 1 (by rfl) ⟨5123168, by rfl⟩ : syracuseStep 6830891 = 10246337) B10246337
theorem B801607 : Blo 798342 801607 := bstep (se 1 (by rfl) ⟨601205, by rfl⟩ : syracuseStep 801607 = 1202411) B1202411
theorem B801647 : Blo 798342 801647 := bstep (se 1 (by rfl) ⟨601235, by rfl⟩ : syracuseStep 801647 = 1202471) B1202471
theorem B801703 : Blo 798342 801703 := bstep (se 1 (by rfl) ⟨601277, by rfl⟩ : syracuseStep 801703 = 1202555) B1202555
theorem B3423323 : Blo 798342 3423323 := bstep (se 1 (by rfl) ⟨2567492, by rfl⟩ : syracuseStep 3423323 = 5134985) B5134985
theorem B801883 : Blo 798342 801883 := bstep (se 1 (by rfl) ⟨601412, by rfl⟩ : syracuseStep 801883 = 1202825) B1202825
theorem B801999 : Blo 798342 801999 := bstep (se 1 (by rfl) ⟨601499, by rfl⟩ : syracuseStep 801999 = 1202999) B1202999
theorem B802023 : Blo 798342 802023 := bstep (se 1 (by rfl) ⟨601517, by rfl⟩ : syracuseStep 802023 = 1203035) B1203035
theorem B3423475 : Blo 798342 3423475 := bstep (se 1 (by rfl) ⟨2567606, by rfl⟩ : syracuseStep 3423475 = 5135213) B5135213
theorem B802119 : Blo 798342 802119 := bstep (se 1 (by rfl) ⟨601589, by rfl⟩ : syracuseStep 802119 = 1203179) B1203179
theorem B802255 : Blo 798342 802255 := bstep (se 1 (by rfl) ⟨601691, by rfl⟩ : syracuseStep 802255 = 1203383) B1203383
theorem B9125621 : Blo 798342 9125621 := bstep (se 5 (by rfl) ⟨427763, by rfl⟩ : syracuseStep 9125621 = 855527) B855527
theorem B900895 : Blo 798342 900895 := bstep (se 1 (by rfl) ⟨675671, by rfl⟩ : syracuseStep 900895 = 1351343) B1351343
theorem B4046759 : Blo 798342 4046759 := bstep (se 1 (by rfl) ⟨3035069, by rfl⟩ : syracuseStep 4046759 = 6070139) B6070139
theorem B3424295 : Blo 798342 3424295 := bstep (se 1 (by rfl) ⟨2568221, by rfl⟩ : syracuseStep 3424295 = 5136443) B5136443
theorem B901327 : Blo 798342 901327 := bstep (se 1 (by rfl) ⟨675995, by rfl⟩ : syracuseStep 901327 = 1351991) B1351991
theorem B17318123 : Blo 798342 17318123 := bstep (se 1 (by rfl) ⟨12988592, by rfl⟩ : syracuseStep 17318123 = 25977185) B25977185
theorem B3031289 : Blo 798342 3031289 := bstep (se 2 (by rfl) ⟨1136733, by rfl⟩ : syracuseStep 3031289 = 2273467) B2273467
theorem B3851027 : Blo 798342 3851027 := bstep (se 1 (by rfl) ⟨2888270, by rfl⟩ : syracuseStep 3851027 = 5776541) B5776541
theorem B3851297 : Blo 798342 3851297 := bstep (se 2 (by rfl) ⟨1444236, by rfl⟩ : syracuseStep 3851297 = 2888473) B2888473
theorem B902191 : Blo 798342 902191 := bstep (se 1 (by rfl) ⟨676643, by rfl⟩ : syracuseStep 902191 = 1353287) B1353287
theorem B902335 : Blo 798342 902335 := bstep (se 1 (by rfl) ⟨676751, by rfl⟩ : syracuseStep 902335 = 1353503) B1353503
theorem B902479 : Blo 798342 902479 := bstep (se 1 (by rfl) ⟨676859, by rfl⟩ : syracuseStep 902479 = 1353719) B1353719
theorem B1197563 : Blo 798342 1197563 := bstep (se 1 (by rfl) ⟨898172, by rfl⟩ : syracuseStep 1197563 = 1796345) B1796345
theorem B1197599 : Blo 798342 1197599 := bstep (se 1 (by rfl) ⟨898199, by rfl⟩ : syracuseStep 1197599 = 1796399) B1796399
theorem B3032747 : Blo 798342 3032747 := bstep (se 1 (by rfl) ⟨2274560, by rfl⟩ : syracuseStep 3032747 = 4549121) B4549121
theorem B1197743 : Blo 798342 1197743 := bstep (se 1 (by rfl) ⟨898307, by rfl⟩ : syracuseStep 1197743 = 1796615) B1796615
theorem B1197863 : Blo 798342 1197863 := bstep (se 1 (by rfl) ⟨898397, by rfl⟩ : syracuseStep 1197863 = 1796795) B1796795
theorem B1198415 : Blo 798342 1198415 := bstep (se 1 (by rfl) ⟨898811, by rfl⟩ : syracuseStep 1198415 = 1797623) B1797623
theorem B1198463 : Blo 798342 1198463 := bstep (se 1 (by rfl) ⟨898847, by rfl⟩ : syracuseStep 1198463 = 1797695) B1797695
theorem B1198505 : Blo 798342 1198505 := bstep (se 2 (by rfl) ⟨449439, by rfl⟩ : syracuseStep 1198505 = 898879) B898879
theorem B1198889 : Blo 798342 1198889 := bstep (se 2 (by rfl) ⟨449583, by rfl⟩ : syracuseStep 1198889 = 899167) B899167
theorem B1199099 : Blo 798342 1199099 := bstep (se 1 (by rfl) ⟨899324, by rfl⟩ : syracuseStep 1199099 = 1798649) B1798649
theorem B1199159 : Blo 798342 1199159 := bstep (se 1 (by rfl) ⟨899369, by rfl⟩ : syracuseStep 1199159 = 1798739) B1798739
theorem B1199279 : Blo 798342 1199279 := bstep (se 1 (by rfl) ⟨899459, by rfl⟩ : syracuseStep 1199279 = 1798919) B1798919
theorem B3853487 : Blo 798342 3853487 := bstep (se 1 (by rfl) ⟨2890115, by rfl⟩ : syracuseStep 3853487 = 5780231) B5780231
theorem B9260477 : Blo 798342 9260477 := bstep (se 3 (by rfl) ⟨1736339, by rfl⟩ : syracuseStep 9260477 = 3472679) B3472679
theorem B1199999 : Blo 798342 1199999 := bstep (se 1 (by rfl) ⟨899999, by rfl⟩ : syracuseStep 1199999 = 1799999) B1799999
theorem B11554811 : Blo 798342 11554811 := bstep (se 1 (by rfl) ⟨8666108, by rfl⟩ : syracuseStep 11554811 = 17332217) B17332217
theorem B2707451 : Blo 798342 2707451 := bstep (se 1 (by rfl) ⟨2030588, by rfl⟩ : syracuseStep 2707451 = 4061177) B4061177
theorem B3035191 : Blo 798342 3035191 := bstep (se 1 (by rfl) ⟨2276393, by rfl⟩ : syracuseStep 3035191 = 4552787) B4552787
theorem B1200191 : Blo 798342 1200191 := bstep (se 1 (by rfl) ⟨900143, by rfl⟩ : syracuseStep 1200191 = 1800287) B1800287
theorem B1200425 : Blo 798342 1200425 := bstep (se 2 (by rfl) ⟨450159, by rfl⟩ : syracuseStep 1200425 = 900319) B900319
theorem B15389189 : Blo 798342 15389189 := bstep (se 4 (by rfl) ⟨1442736, by rfl⟩ : syracuseStep 15389189 = 2885473) B2885473
theorem B3035663 : Blo 798342 3035663 := bstep (se 1 (by rfl) ⟨2276747, by rfl⟩ : syracuseStep 3035663 = 4553495) B4553495
theorem B1200695 : Blo 798342 1200695 := bstep (se 1 (by rfl) ⟨900521, by rfl⟩ : syracuseStep 1200695 = 1801043) B1801043
theorem B1201055 : Blo 798342 1201055 := bstep (se 1 (by rfl) ⟨900791, by rfl⟩ : syracuseStep 1201055 = 1801583) B1801583
theorem B1201247 : Blo 798342 1201247 := bstep (se 1 (by rfl) ⟨900935, by rfl⟩ : syracuseStep 1201247 = 1801871) B1801871
theorem B1201307 : Blo 798342 1201307 := bstep (se 1 (by rfl) ⟨900980, by rfl⟩ : syracuseStep 1201307 = 1801961) B1801961
theorem B3036923 : Blo 798342 3036923 := bstep (se 1 (by rfl) ⟨2277692, by rfl⟩ : syracuseStep 3036923 = 4555385) B4555385
theorem B1201991 : Blo 798342 1201991 := bstep (se 1 (by rfl) ⟨901493, by rfl⟩ : syracuseStep 1201991 = 1802987) B1802987
theorem B7296925 : Blo 798342 7296925 := bstep (se 3 (by rfl) ⟨1368173, by rfl⟩ : syracuseStep 7296925 = 2736347) B2736347
theorem B2021345 : Blo 798342 2021345 := bstep (se 2 (by rfl) ⟨758004, by rfl⟩ : syracuseStep 2021345 = 1516009) B1516009
theorem B1202591 : Blo 798342 1202591 := bstep (se 1 (by rfl) ⟨901943, by rfl⟩ : syracuseStep 1202591 = 1803887) B1803887
theorem B1202663 : Blo 798342 1202663 := bstep (se 1 (by rfl) ⟨901997, by rfl⟩ : syracuseStep 1202663 = 1803995) B1803995
theorem B2054683 : Blo 798342 2054683 := bstep (se 1 (by rfl) ⟨1541012, by rfl⟩ : syracuseStep 2054683 = 3082025) B3082025
theorem B65592139 : Blo 798342 65592139 := bstep (se 1 (by rfl) ⟨49194104, by rfl⟩ : syracuseStep 65592139 = 98388209) B98388209
theorem B1203407 : Blo 798342 1203407 := bstep (se 1 (by rfl) ⟨902555, by rfl⟩ : syracuseStep 1203407 = 1805111) B1805111
theorem B2284777 : Blo 798342 2284777 := bstep (se 2 (by rfl) ⟨856791, by rfl⟩ : syracuseStep 2284777 = 1713583) B1713583
theorem B7691597 : Blo 798342 7691597 := bstep (se 3 (by rfl) ⟨1442174, by rfl⟩ : syracuseStep 7691597 = 2884349) B2884349
theorem B1728479 : Blo 798342 1728479 := bstep (se 1 (by rfl) ⟨1296359, by rfl⟩ : syracuseStep 1728479 = 2592719) B2592719
theorem B4055507 : Blo 798342 4055507 := bstep (se 1 (by rfl) ⟨3041630, by rfl⟩ : syracuseStep 4055507 = 6083261) B6083261
theorem B12313255 : Blo 798342 12313255 := bstep (se 1 (by rfl) ⟨9234941, by rfl⟩ : syracuseStep 12313255 = 18469883) B18469883
theorem B1925851 : Blo 798342 1925851 := bstep (se 1 (by rfl) ⟨1444388, by rfl⟩ : syracuseStep 1925851 = 2888777) B2888777
theorem B14607863 : Blo 798342 14607863 := bstep (se 1 (by rfl) ⟨10955897, by rfl⟩ : syracuseStep 14607863 = 21911795) B21911795
theorem B13690619 : Blo 798342 13690619 := bstep (se 1 (by rfl) ⟨10267964, by rfl⟩ : syracuseStep 13690619 = 20535929) B20535929
theorem B6842303 : Blo 798342 6842303 := bstep (se 1 (by rfl) ⟨5131727, by rfl⟩ : syracuseStep 6842303 = 10263455) B10263455
theorem B27781325 : Blo 798342 27781325 := bstep (se 3 (by rfl) ⟨5208998, by rfl⟩ : syracuseStep 27781325 = 10417997) B10417997
theorem B1796489 : Blo 798342 1796489 := bstep (se 2 (by rfl) ⟨673683, by rfl⟩ : syracuseStep 1796489 = 1347367) B1347367
theorem B3041783 : Blo 798342 3041783 := bstep (se 1 (by rfl) ⟨2281337, by rfl⟩ : syracuseStep 3041783 = 4562675) B4562675
theorem B1141295 : Blo 798342 1141295 := bstep (se 1 (by rfl) ⟨855971, by rfl⟩ : syracuseStep 1141295 = 1711943) B1711943
theorem B6842987 : Blo 798342 6842987 := bstep (se 1 (by rfl) ⟨5132240, by rfl⟩ : syracuseStep 6842987 = 10264481) B10264481
theorem B1797191 : Blo 798342 1797191 := bstep (se 1 (by rfl) ⟨1347893, by rfl⟩ : syracuseStep 1797191 = 2695787) B2695787
theorem B5762353 : Blo 798342 5762353 := bstep (se 2 (by rfl) ⟨2160882, by rfl⟩ : syracuseStep 5762353 = 4321765) B4321765
theorem B3042755 : Blo 798342 3042755 := bstep (se 1 (by rfl) ⟨2282066, by rfl⟩ : syracuseStep 3042755 = 4564133) B4564133
theorem B1797587 : Blo 798342 1797587 := bstep (se 1 (by rfl) ⟨1348190, by rfl⟩ : syracuseStep 1797587 = 2696381) B2696381
theorem B1797857 : Blo 798342 1797857 := bstep (se 2 (by rfl) ⟨674196, by rfl⟩ : syracuseStep 1797857 = 1348393) B1348393
theorem B7302905 : Blo 798342 7302905 := bstep (se 2 (by rfl) ⟨2738589, by rfl⟩ : syracuseStep 7302905 = 5477179) B5477179
theorem B3239767 : Blo 798342 3239767 := bstep (se 1 (by rfl) ⟨2429825, by rfl⟩ : syracuseStep 3239767 = 4859651) B4859651
theorem B1798217 : Blo 798342 1798217 := bstep (se 2 (by rfl) ⟨674331, by rfl⟩ : syracuseStep 1798217 = 1348663) B1348663
theorem B4059233 : Blo 798342 4059233 := bstep (se 2 (by rfl) ⟨1522212, by rfl⟩ : syracuseStep 4059233 = 3044425) B3044425
theorem B1798271 : Blo 798342 1798271 := bstep (se 1 (by rfl) ⟨1348703, by rfl⟩ : syracuseStep 1798271 = 2697407) B2697407
theorem B2027663 : Blo 798342 2027663 := bstep (se 1 (by rfl) ⟨1520747, by rfl⟩ : syracuseStep 2027663 = 3041495) B3041495
theorem B25915949 : Blo 798342 25915949 := bstep (se 3 (by rfl) ⟨4859240, by rfl⟩ : syracuseStep 25915949 = 9718481) B9718481
theorem B1799351 : Blo 798342 1799351 := bstep (se 1 (by rfl) ⟨1349513, by rfl⟩ : syracuseStep 1799351 = 2699027) B2699027
theorem B19461383 : Blo 798342 19461383 := bstep (se 1 (by rfl) ⟨14596037, by rfl⟩ : syracuseStep 19461383 = 29192075) B29192075
theorem B3044699 : Blo 798342 3044699 := bstep (se 1 (by rfl) ⟨2283524, by rfl⟩ : syracuseStep 3044699 = 4567049) B4567049
theorem B4060691 : Blo 798342 4060691 := bstep (se 1 (by rfl) ⟨3045518, by rfl⟩ : syracuseStep 4060691 = 6091037) B6091037
theorem B1799927 : Blo 798342 1799927 := bstep (se 1 (by rfl) ⟨1349945, by rfl⟩ : syracuseStep 1799927 = 2699891) B2699891
theorem B1537871 : Blo 798342 1537871 := bstep (se 1 (by rfl) ⟨1153403, by rfl⟩ : syracuseStep 1537871 = 2306807) B2306807
theorem B1800107 : Blo 798342 1800107 := bstep (se 1 (by rfl) ⟨1350080, by rfl⟩ : syracuseStep 1800107 = 2700161) B2700161
theorem B6846403 : Blo 798342 6846403 := bstep (se 1 (by rfl) ⟨5134802, by rfl⟩ : syracuseStep 6846403 = 10269605) B10269605
theorem B1800233 : Blo 798342 1800233 := bstep (se 2 (by rfl) ⟨675087, by rfl⟩ : syracuseStep 1800233 = 1350175) B1350175
theorem B6486281 : Blo 798342 6486281 := bstep (se 2 (by rfl) ⟨2432355, by rfl⟩ : syracuseStep 6486281 = 4864711) B4864711
theorem B1800647 : Blo 798342 1800647 := bstep (se 1 (by rfl) ⟨1350485, by rfl⟩ : syracuseStep 1800647 = 2700971) B2700971
theorem B1800809 : Blo 798342 1800809 := bstep (se 2 (by rfl) ⟨675303, by rfl⟩ : syracuseStep 1800809 = 1350607) B1350607
theorem B1800863 : Blo 798342 1800863 := bstep (se 1 (by rfl) ⟨1350647, by rfl⟩ : syracuseStep 1800863 = 2701295) B2701295
theorem B2030305 : Blo 798342 2030305 := bstep (se 2 (by rfl) ⟨761364, by rfl⟩ : syracuseStep 2030305 = 1522729) B1522729
theorem B1801007 : Blo 798342 1801007 := bstep (se 1 (by rfl) ⟨1350755, by rfl⟩ : syracuseStep 1801007 = 2701511) B2701511
theorem B19758275 : Blo 798342 19758275 := bstep (se 1 (by rfl) ⟨14818706, by rfl⟩ : syracuseStep 19758275 = 29637413) B29637413
theorem B1801439 : Blo 798342 1801439 := bstep (se 1 (by rfl) ⟨1351079, by rfl⟩ : syracuseStep 1801439 = 2702159) B2702159
theorem B1801655 : Blo 798342 1801655 := bstep (se 1 (by rfl) ⟨1351241, by rfl⟩ : syracuseStep 1801655 = 2702483) B2702483
theorem B2883023 : Blo 798342 2883023 := bstep (se 1 (by rfl) ⟨2162267, by rfl⟩ : syracuseStep 2883023 = 4324535) B4324535
theorem B51805655 : Blo 798342 51805655 := bstep (se 1 (by rfl) ⟨38854241, by rfl⟩ : syracuseStep 51805655 = 77708483) B77708483
theorem B1801835 : Blo 798342 1801835 := bstep (se 1 (by rfl) ⟨1351376, by rfl⟩ : syracuseStep 1801835 = 2702753) B2702753
theorem B1802105 : Blo 798342 1802105 := bstep (se 2 (by rfl) ⟨675789, by rfl⟩ : syracuseStep 1802105 = 1351579) B1351579
theorem B1802195 : Blo 798342 1802195 := bstep (se 1 (by rfl) ⟨1351646, by rfl⟩ : syracuseStep 1802195 = 2703293) B2703293
theorem B16417673 : Blo 798342 16417673 := bstep (se 2 (by rfl) ⟨6156627, by rfl⟩ : syracuseStep 16417673 = 12313255) B12313255
theorem B2164819 : Blo 798342 2164819 := bstep (se 1 (by rfl) ⟨1623614, by rfl⟩ : syracuseStep 2164819 = 3247229) B3247229
theorem B2558483 : Blo 798342 2558483 := bstep (se 1 (by rfl) ⟨1918862, by rfl⟩ : syracuseStep 2558483 = 3837725) B3837725
theorem B7703207 : Blo 798342 7703207 := bstep (se 1 (by rfl) ⟨5777405, by rfl⟩ : syracuseStep 7703207 = 11554811) B11554811
theorem B1804967 : Blo 798342 1804967 := bstep (se 1 (by rfl) ⟨1353725, by rfl⟩ : syracuseStep 1804967 = 2707451) B2707451
theorem B1248167 : Blo 798342 1248167 := bstep (se 1 (by rfl) ⟨936125, by rfl⟩ : syracuseStep 1248167 = 1872251) B1872251
theorem B10259459 : Blo 798342 10259459 := bstep (se 1 (by rfl) ⟨7694594, by rfl⟩ : syracuseStep 10259459 = 15389189) B15389189
theorem B6491279 : Blo 798342 6491279 := bstep (se 1 (by rfl) ⟨4868459, by rfl⟩ : syracuseStep 6491279 = 9736919) B9736919
theorem B1347563 : Blo 798342 1347563 := bstep (se 1 (by rfl) ⟨1010672, by rfl⟩ : syracuseStep 1347563 = 2021345) B2021345
theorem B1152319 : Blo 798342 1152319 := bstep (se 1 (by rfl) ⟨864239, by rfl⟩ : syracuseStep 1152319 = 1728479) B1728479
theorem B3414113 : Blo 798342 3414113 := bstep (se 2 (by rfl) ⟨1280292, by rfl⟩ : syracuseStep 3414113 = 2560585) B2560585
theorem B9738575 : Blo 798342 9738575 := bstep (se 1 (by rfl) ⟨7303931, by rfl⟩ : syracuseStep 9738575 = 14607863) B14607863
theorem B4561535 : Blo 798342 4561535 := bstep (se 1 (by rfl) ⟨3421151, by rfl⟩ : syracuseStep 4561535 = 6842303) B6842303
theorem B18520883 : Blo 798342 18520883 := bstep (se 1 (by rfl) ⟨13890662, by rfl⟩ : syracuseStep 18520883 = 27781325) B27781325
theorem B4561991 : Blo 798342 4561991 := bstep (se 1 (by rfl) ⟨3421493, by rfl⟩ : syracuseStep 4561991 = 6842987) B6842987
theorem B3415547 : Blo 798342 3415547 := bstep (se 1 (by rfl) ⟨2561660, by rfl⟩ : syracuseStep 3415547 = 5123321) B5123321
theorem B1351775 : Blo 798342 1351775 := bstep (se 1 (by rfl) ⟨1013831, by rfl⟩ : syracuseStep 1351775 = 2027663) B2027663
theorem B4858001 : Blo 798342 4858001 := bstep (se 2 (by rfl) ⟨1821750, by rfl⟩ : syracuseStep 4858001 = 3643501) B3643501
theorem B17277299 : Blo 798342 17277299 := bstep (se 1 (by rfl) ⟨12957974, by rfl⟩ : syracuseStep 17277299 = 25915949) B25915949
theorem B4563449 : Blo 798342 4563449 := bstep (se 2 (by rfl) ⟨1711293, by rfl⟩ : syracuseStep 4563449 = 3422587) B3422587
theorem B5120759 : Blo 798342 5120759 := bstep (se 1 (by rfl) ⟨3840569, by rfl⟩ : syracuseStep 5120759 = 7681139) B7681139
theorem B1516639 : Blo 798342 1516639 := bstep (se 1 (by rfl) ⟨1137479, by rfl⟩ : syracuseStep 1516639 = 2274959) B2274959
theorem B4564633 : Blo 798342 4564633 := bstep (se 2 (by rfl) ⟨1711737, by rfl⟩ : syracuseStep 4564633 = 3423475) B3423475
theorem B1517231 : Blo 798342 1517231 := bstep (se 1 (by rfl) ⟨1137923, by rfl⟩ : syracuseStep 1517231 = 2275847) B2275847
theorem B17278757 : Blo 798342 17278757 := bstep (se 4 (by rfl) ⟨1619883, by rfl⟩ : syracuseStep 17278757 = 3239767) B3239767
theorem B2697839 : Blo 798342 2697839 := bstep (se 1 (by rfl) ⟨2023379, by rfl⟩ : syracuseStep 2697839 = 4046759) B4046759
theorem B11545415 : Blo 798342 11545415 := bstep (se 1 (by rfl) ⟨8659061, by rfl⟩ : syracuseStep 11545415 = 17318123) B17318123
theorem B2567351 : Blo 798342 2567351 := bstep (se 1 (by rfl) ⟨1925513, by rfl⟩ : syracuseStep 2567351 = 3851027) B3851027
theorem B2567531 : Blo 798342 2567531 := bstep (se 1 (by rfl) ⟨1925648, by rfl⟩ : syracuseStep 2567531 = 3851297) B3851297
theorem B2567801 : Blo 798342 2567801 := bstep (se 2 (by rfl) ⟨962925, by rfl⟩ : syracuseStep 2567801 = 1925851) B1925851
theorem B798375 : Blo 798342 798375 := bstep (se 1 (by rfl) ⟨598781, by rfl⟩ : syracuseStep 798375 = 1197563) B1197563
theorem B798399 : Blo 798342 798399 := bstep (se 1 (by rfl) ⟨598799, by rfl⟩ : syracuseStep 798399 = 1197599) B1197599
theorem B798495 : Blo 798342 798495 := bstep (se 1 (by rfl) ⟨598871, by rfl⟩ : syracuseStep 798495 = 1197743) B1197743
theorem B4337489 : Blo 798342 4337489 := bstep (se 2 (by rfl) ⟨1626558, by rfl⟩ : syracuseStep 4337489 = 3253117) B3253117
theorem B798575 : Blo 798342 798575 := bstep (se 1 (by rfl) ⟨598931, by rfl⟩ : syracuseStep 798575 = 1197863) B1197863
theorem B798943 : Blo 798342 798943 := bstep (se 1 (by rfl) ⟨599207, by rfl⟩ : syracuseStep 798943 = 1198415) B1198415
theorem B798975 : Blo 798342 798975 := bstep (se 1 (by rfl) ⟨599231, by rfl⟩ : syracuseStep 798975 = 1198463) B1198463
theorem B799003 : Blo 798342 799003 := bstep (se 1 (by rfl) ⟨599252, by rfl⟩ : syracuseStep 799003 = 1198505) B1198505
theorem B4108751 : Blo 798342 4108751 := bstep (se 1 (by rfl) ⟨3081563, by rfl⟩ : syracuseStep 4108751 = 6163127) B6163127
theorem B799259 : Blo 798342 799259 := bstep (se 1 (by rfl) ⟨599444, by rfl⟩ : syracuseStep 799259 = 1198889) B1198889
theorem B799399 : Blo 798342 799399 := bstep (se 1 (by rfl) ⟨599549, by rfl⟩ : syracuseStep 799399 = 1199099) B1199099
theorem B799439 : Blo 798342 799439 := bstep (se 1 (by rfl) ⟨599579, by rfl⟩ : syracuseStep 799439 = 1199159) B1199159
theorem B799519 : Blo 798342 799519 := bstep (se 1 (by rfl) ⟨599639, by rfl⟩ : syracuseStep 799519 = 1199279) B1199279
theorem B2568991 : Blo 798342 2568991 := bstep (se 1 (by rfl) ⟨1926743, by rfl⟩ : syracuseStep 2568991 = 3853487) B3853487
theorem B6173651 : Blo 798342 6173651 := bstep (se 1 (by rfl) ⟨4630238, by rfl⟩ : syracuseStep 6173651 = 9260477) B9260477
theorem B898303 : Blo 798342 898303 := bstep (se 1 (by rfl) ⟨673727, by rfl⟩ : syracuseStep 898303 = 1347455) B1347455
theorem B799999 : Blo 798342 799999 := bstep (se 1 (by rfl) ⟨599999, by rfl⟩ : syracuseStep 799999 = 1199999) B1199999
theorem B800127 : Blo 798342 800127 := bstep (se 1 (by rfl) ⟨600095, by rfl⟩ : syracuseStep 800127 = 1200191) B1200191
theorem B800283 : Blo 798342 800283 := bstep (se 1 (by rfl) ⟨600212, by rfl⟩ : syracuseStep 800283 = 1200425) B1200425
theorem B800463 : Blo 798342 800463 := bstep (se 1 (by rfl) ⟨600347, by rfl⟩ : syracuseStep 800463 = 1200695) B1200695
theorem B800703 : Blo 798342 800703 := bstep (se 1 (by rfl) ⟨600527, by rfl⟩ : syracuseStep 800703 = 1201055) B1201055
theorem B800831 : Blo 798342 800831 := bstep (se 1 (by rfl) ⟨600623, by rfl⟩ : syracuseStep 800831 = 1201247) B1201247
theorem B14596175 : Blo 798342 14596175 := bstep (se 1 (by rfl) ⟨10947131, by rfl⟩ : syracuseStep 14596175 = 21894263) B21894263
theorem B800871 : Blo 798342 800871 := bstep (se 1 (by rfl) ⟨600653, by rfl⟩ : syracuseStep 800871 = 1201307) B1201307
theorem B801327 : Blo 798342 801327 := bstep (se 1 (by rfl) ⟨600995, by rfl⟩ : syracuseStep 801327 = 1201991) B1201991
theorem B8632979 : Blo 798342 8632979 := bstep (se 1 (by rfl) ⟨6474734, by rfl⟩ : syracuseStep 8632979 = 12949469) B12949469
theorem B30784211 : Blo 798342 30784211 := bstep (se 1 (by rfl) ⟨23088158, by rfl⟩ : syracuseStep 30784211 = 46176317) B46176317
theorem B17349335 : Blo 798342 17349335 := bstep (se 1 (by rfl) ⟨13012001, by rfl⟩ : syracuseStep 17349335 = 26024003) B26024003
theorem B42154733 : Blo 798342 42154733 := bstep (se 3 (by rfl) ⟨7904012, by rfl⟩ : syracuseStep 42154733 = 15808025) B15808025
theorem B900031 : Blo 798342 900031 := bstep (se 1 (by rfl) ⟨675023, by rfl⟩ : syracuseStep 900031 = 1350047) B1350047
theorem B801727 : Blo 798342 801727 := bstep (se 1 (by rfl) ⟨601295, by rfl⟩ : syracuseStep 801727 = 1202591) B1202591
theorem B801775 : Blo 798342 801775 := bstep (se 1 (by rfl) ⟨601331, by rfl⟩ : syracuseStep 801775 = 1202663) B1202663
theorem B7683137 : Blo 798342 7683137 := bstep (se 2 (by rfl) ⟨2881176, by rfl⟩ : syracuseStep 7683137 = 5762353) B5762353
theorem B73776365 : Blo 798342 73776365 := bstep (se 3 (by rfl) ⟨13833068, by rfl⟩ : syracuseStep 73776365 = 27666137) B27666137
theorem B21937513 : Blo 798342 21937513 := bstep (se 2 (by rfl) ⟨8226567, by rfl⟩ : syracuseStep 21937513 = 16453135) B16453135
theorem B802271 : Blo 798342 802271 := bstep (se 1 (by rfl) ⟨601703, by rfl⟩ : syracuseStep 802271 = 1203407) B1203407
theorem B5127731 : Blo 798342 5127731 := bstep (se 1 (by rfl) ⟨3845798, by rfl⟩ : syracuseStep 5127731 = 7691597) B7691597
theorem B1097371 : Blo 798342 1097371 := bstep (se 1 (by rfl) ⟨823028, by rfl⟩ : syracuseStep 1097371 = 1646057) B1646057
theorem B900859 : Blo 798342 900859 := bstep (se 1 (by rfl) ⟨675644, by rfl⟩ : syracuseStep 900859 = 1351289) B1351289
theorem B4046921 : Blo 798342 4046921 := bstep (se 2 (by rfl) ⟨1517595, by rfl⟩ : syracuseStep 4046921 = 3035191) B3035191
theorem B2703671 : Blo 798342 2703671 := bstep (se 1 (by rfl) ⟨2027753, by rfl⟩ : syracuseStep 2703671 = 4055507) B4055507
theorem B3654119 : Blo 798342 3654119 := bstep (se 1 (by rfl) ⟨2740589, by rfl⟩ : syracuseStep 3654119 = 5481179) B5481179
theorem B902011 : Blo 798342 902011 := bstep (se 1 (by rfl) ⟨676508, by rfl⟩ : syracuseStep 902011 = 1353017) B1353017
theorem B9127079 : Blo 798342 9127079 := bstep (se 1 (by rfl) ⟨6845309, by rfl⟩ : syracuseStep 9127079 = 13690619) B13690619
theorem B3425561 : Blo 798342 3425561 := bstep (se 2 (by rfl) ⟨1284585, by rfl⟩ : syracuseStep 3425561 = 2569171) B2569171
theorem B4048379 : Blo 798342 4048379 := bstep (se 1 (by rfl) ⟨3036284, by rfl⟩ : syracuseStep 4048379 = 6072569) B6072569
theorem B1197659 : Blo 798342 1197659 := bstep (se 1 (by rfl) ⟨898244, by rfl⟩ : syracuseStep 1197659 = 1796489) B1796489
theorem B19449497 : Blo 798342 19449497 := bstep (se 2 (by rfl) ⟨7293561, by rfl⟩ : syracuseStep 19449497 = 14587123) B14587123
theorem B1198127 : Blo 798342 1198127 := bstep (se 1 (by rfl) ⟨898595, by rfl⟩ : syracuseStep 1198127 = 1797191) B1797191
theorem B1198391 : Blo 798342 1198391 := bstep (se 1 (by rfl) ⟨898793, by rfl⟩ : syracuseStep 1198391 = 1797587) B1797587
theorem B1198571 : Blo 798342 1198571 := bstep (se 1 (by rfl) ⟨898928, by rfl⟩ : syracuseStep 1198571 = 1797857) B1797857
theorem B4868603 : Blo 798342 4868603 := bstep (se 1 (by rfl) ⟨3651452, by rfl⟩ : syracuseStep 4868603 = 7302905) B7302905
theorem B9128537 : Blo 798342 9128537 := bstep (se 2 (by rfl) ⟨3423201, by rfl⟩ : syracuseStep 9128537 = 6846403) B6846403
theorem B8637131 : Blo 798342 8637131 := bstep (se 1 (by rfl) ⟨6477848, by rfl⟩ : syracuseStep 8637131 = 12955697) B12955697
theorem B1198811 : Blo 798342 1198811 := bstep (se 1 (by rfl) ⟨899108, by rfl⟩ : syracuseStep 1198811 = 1798217) B1798217
theorem B2706155 : Blo 798342 2706155 := bstep (se 1 (by rfl) ⟨2029616, by rfl⟩ : syracuseStep 2706155 = 4059233) B4059233
theorem B1198847 : Blo 798342 1198847 := bstep (se 1 (by rfl) ⟨899135, by rfl⟩ : syracuseStep 1198847 = 1798271) B1798271
theorem B2739577 : Blo 798342 2739577 := bstep (se 2 (by rfl) ⟨1027341, by rfl⟩ : syracuseStep 2739577 = 2054683) B2054683
theorem B1199567 : Blo 798342 1199567 := bstep (se 1 (by rfl) ⟨899675, by rfl⟩ : syracuseStep 1199567 = 1799351) B1799351
theorem B16403957 : Blo 798342 16403957 := bstep (se 5 (by rfl) ⟨768935, by rfl⟩ : syracuseStep 16403957 = 1537871) B1537871
theorem B1199657 : Blo 798342 1199657 := bstep (se 2 (by rfl) ⟨449871, by rfl⟩ : syracuseStep 1199657 = 899743) B899743
theorem B2707073 : Blo 798342 2707073 := bstep (se 2 (by rfl) ⟨1015152, by rfl⟩ : syracuseStep 2707073 = 2030305) B2030305
theorem B2707127 : Blo 798342 2707127 := bstep (se 1 (by rfl) ⟨2030345, by rfl⟩ : syracuseStep 2707127 = 4060691) B4060691
theorem B1199951 : Blo 798342 1199951 := bstep (se 1 (by rfl) ⟨899963, by rfl⟩ : syracuseStep 1199951 = 1799927) B1799927
theorem B1200071 : Blo 798342 1200071 := bstep (se 1 (by rfl) ⟨900053, by rfl⟩ : syracuseStep 1200071 = 1800107) B1800107
theorem B1200155 : Blo 798342 1200155 := bstep (se 1 (by rfl) ⟨900116, by rfl⟩ : syracuseStep 1200155 = 1800233) B1800233
theorem B4050971 : Blo 798342 4050971 := bstep (se 1 (by rfl) ⟨3038228, by rfl⟩ : syracuseStep 4050971 = 6076457) B6076457
theorem B13160537 : Blo 798342 13160537 := bstep (se 2 (by rfl) ⟨4935201, by rfl⟩ : syracuseStep 13160537 = 9870403) B9870403
theorem B4051133 : Blo 798342 4051133 := bstep (se 3 (by rfl) ⟨759587, by rfl⟩ : syracuseStep 4051133 = 1519175) B1519175
theorem B1200431 : Blo 798342 1200431 := bstep (se 1 (by rfl) ⟨900323, by rfl⟩ : syracuseStep 1200431 = 1800647) B1800647
theorem B1200539 : Blo 798342 1200539 := bstep (se 1 (by rfl) ⟨900404, by rfl⟩ : syracuseStep 1200539 = 1800809) B1800809
theorem B1200575 : Blo 798342 1200575 := bstep (se 1 (by rfl) ⟨900431, by rfl⟩ : syracuseStep 1200575 = 1800863) B1800863
theorem B1200671 : Blo 798342 1200671 := bstep (se 1 (by rfl) ⟨900503, by rfl⟩ : syracuseStep 1200671 = 1801007) B1801007
theorem B2282215 : Blo 798342 2282215 := bstep (se 1 (by rfl) ⟨1711661, by rfl⟩ : syracuseStep 2282215 = 3423323) B3423323
theorem B1200959 : Blo 798342 1200959 := bstep (se 1 (by rfl) ⟨900719, by rfl⟩ : syracuseStep 1200959 = 1801439) B1801439
theorem B1201103 : Blo 798342 1201103 := bstep (se 1 (by rfl) ⟨900827, by rfl⟩ : syracuseStep 1201103 = 1801655) B1801655
theorem B1922015 : Blo 798342 1922015 := bstep (se 1 (by rfl) ⟨1441511, by rfl⟩ : syracuseStep 1922015 = 2883023) B2883023
theorem B1201193 : Blo 798342 1201193 := bstep (se 2 (by rfl) ⟨450447, by rfl⟩ : syracuseStep 1201193 = 900895) B900895
theorem B1201223 : Blo 798342 1201223 := bstep (se 1 (by rfl) ⟨900917, by rfl⟩ : syracuseStep 1201223 = 1801835) B1801835
theorem B6083747 : Blo 798342 6083747 := bstep (se 1 (by rfl) ⟨4562810, by rfl⟩ : syracuseStep 6083747 = 9125621) B9125621
theorem B1201403 : Blo 798342 1201403 := bstep (se 1 (by rfl) ⟨901052, by rfl⟩ : syracuseStep 1201403 = 1802105) B1802105
theorem B1201463 : Blo 798342 1201463 := bstep (se 1 (by rfl) ⟨901097, by rfl⟩ : syracuseStep 1201463 = 1802195) B1802195
theorem B9131453 : Blo 798342 9131453 := bstep (se 3 (by rfl) ⟨1712147, by rfl⟩ : syracuseStep 9131453 = 3424295) B3424295
theorem B13686245 : Blo 798342 13686245 := bstep (se 4 (by rfl) ⟨1283085, by rfl⟩ : syracuseStep 13686245 = 2566171) B2566171
theorem B2020859 : Blo 798342 2020859 := bstep (se 1 (by rfl) ⟨1515644, by rfl⟩ : syracuseStep 2020859 = 3031289) B3031289
theorem B1201769 : Blo 798342 1201769 := bstep (se 2 (by rfl) ⟨450663, by rfl⟩ : syracuseStep 1201769 = 901327) B901327
theorem B6084233 : Blo 798342 6084233 := bstep (se 2 (by rfl) ⟨2281587, by rfl⟩ : syracuseStep 6084233 = 4563175) B4563175
theorem B1922783 : Blo 798342 1922783 := bstep (se 1 (by rfl) ⟨1442087, by rfl⟩ : syracuseStep 1922783 = 2884175) B2884175
theorem B7689979 : Blo 798342 7689979 := bstep (se 1 (by rfl) ⟨5767484, by rfl⟩ : syracuseStep 7689979 = 11534969) B11534969
theorem B1202303 : Blo 798342 1202303 := bstep (se 1 (by rfl) ⟨901727, by rfl⟩ : syracuseStep 1202303 = 1803455) B1803455
theorem B1202399 : Blo 798342 1202399 := bstep (se 1 (by rfl) ⟨901799, by rfl⟩ : syracuseStep 1202399 = 1803599) B1803599
theorem B1202459 : Blo 798342 1202459 := bstep (se 1 (by rfl) ⟨901844, by rfl⟩ : syracuseStep 1202459 = 1803689) B1803689
theorem B2021831 : Blo 798342 2021831 := bstep (se 1 (by rfl) ⟨1516373, by rfl⟩ : syracuseStep 2021831 = 3032747) B3032747
theorem B9755113 : Blo 798342 9755113 := bstep (se 2 (by rfl) ⟨3658167, by rfl⟩ : syracuseStep 9755113 = 7316335) B7316335
theorem B1202783 : Blo 798342 1202783 := bstep (se 1 (by rfl) ⟨902087, by rfl⟩ : syracuseStep 1202783 = 1804175) B1804175
theorem B1137343 : Blo 798342 1137343 := bstep (se 1 (by rfl) ⟨853007, by rfl⟩ : syracuseStep 1137343 = 1706015) B1706015
theorem B1202879 : Blo 798342 1202879 := bstep (se 1 (by rfl) ⟨902159, by rfl⟩ : syracuseStep 1202879 = 1804319) B1804319
theorem B1202921 : Blo 798342 1202921 := bstep (se 2 (by rfl) ⟨451095, by rfl⟩ : syracuseStep 1202921 = 902191) B902191
theorem B1203047 : Blo 798342 1203047 := bstep (se 1 (by rfl) ⟨902285, by rfl⟩ : syracuseStep 1203047 = 1804571) B1804571
theorem B9132911 : Blo 798342 9132911 := bstep (se 1 (by rfl) ⟨6849683, by rfl⟩ : syracuseStep 9132911 = 13699367) B13699367
theorem B1203113 : Blo 798342 1203113 := bstep (se 2 (by rfl) ⟨451167, by rfl⟩ : syracuseStep 1203113 = 902335) B902335
theorem B1203263 : Blo 798342 1203263 := bstep (se 1 (by rfl) ⟨902447, by rfl⟩ : syracuseStep 1203263 = 1804895) B1804895
theorem B1203305 : Blo 798342 1203305 := bstep (se 2 (by rfl) ⟨451239, by rfl⟩ : syracuseStep 1203305 = 902479) B902479
theorem B1924321 : Blo 798342 1924321 := bstep (se 2 (by rfl) ⟨721620, by rfl⟩ : syracuseStep 1924321 = 1443241) B1443241
theorem B1203431 : Blo 798342 1203431 := bstep (se 1 (by rfl) ⟨902573, by rfl⟩ : syracuseStep 1203431 = 1805147) B1805147
theorem B9723539 : Blo 798342 9723539 := bstep (se 1 (by rfl) ⟨7292654, by rfl⟩ : syracuseStep 9723539 = 14585309) B14585309
theorem B2023289 : Blo 798342 2023289 := bstep (se 2 (by rfl) ⟨758733, by rfl⟩ : syracuseStep 2023289 = 1517467) B1517467
theorem B4055021 : Blo 798342 4055021 := bstep (se 3 (by rfl) ⟨760316, by rfl⟩ : syracuseStep 4055021 = 1520633) B1520633
theorem B46850309 : Blo 798342 46850309 := bstep (se 4 (by rfl) ⟨4392216, by rfl⟩ : syracuseStep 46850309 = 8784433) B8784433
theorem B2023775 : Blo 798342 2023775 := bstep (se 1 (by rfl) ⟨1517831, by rfl⟩ : syracuseStep 2023775 = 3035663) B3035663
theorem B13132151 : Blo 798342 13132151 := bstep (se 1 (by rfl) ⟨9849113, by rfl⟩ : syracuseStep 13132151 = 19698227) B19698227
theorem B4546955 : Blo 798342 4546955 := bstep (se 1 (by rfl) ⟨3410216, by rfl⟩ : syracuseStep 4546955 = 6820433) B6820433
theorem B1139359 : Blo 798342 1139359 := bstep (se 1 (by rfl) ⟨854519, by rfl⟩ : syracuseStep 1139359 = 1709039) B1709039
theorem B2024615 : Blo 798342 2024615 := bstep (se 1 (by rfl) ⟨1518461, by rfl⟩ : syracuseStep 2024615 = 3036923) B3036923
theorem B4876199 : Blo 798342 4876199 := bstep (se 1 (by rfl) ⟨3657149, by rfl⟩ : syracuseStep 4876199 = 7314299) B7314299
theorem B3238211 : Blo 798342 3238211 := bstep (se 1 (by rfl) ⟨2428658, by rfl⟩ : syracuseStep 3238211 = 4857317) B4857317
theorem B1796921 : Blo 798342 1796921 := bstep (se 2 (by rfl) ⟨673845, by rfl⟩ : syracuseStep 1796921 = 1347691) B1347691
theorem B1797551 : Blo 798342 1797551 := bstep (se 1 (by rfl) ⟨1348163, by rfl⟩ : syracuseStep 1797551 = 2696327) B2696327
theorem B1797803 : Blo 798342 1797803 := bstep (se 1 (by rfl) ⟨1348352, by rfl⟩ : syracuseStep 1797803 = 2696705) B2696705
theorem B3043453 : Blo 798342 3043453 := bstep (se 3 (by rfl) ⟨570647, by rfl⟩ : syracuseStep 3043453 = 1141295) B1141295
theorem B1798343 : Blo 798342 1798343 := bstep (se 1 (by rfl) ⟨1348757, by rfl⟩ : syracuseStep 1798343 = 2697515) B2697515
theorem B3895543 : Blo 798342 3895543 := bstep (se 1 (by rfl) ⟨2921657, by rfl⟩ : syracuseStep 3895543 = 5843315) B5843315
theorem B2027855 : Blo 798342 2027855 := bstep (se 1 (by rfl) ⟨1520891, by rfl⟩ : syracuseStep 2027855 = 3041783) B3041783
theorem B1798523 : Blo 798342 1798523 := bstep (se 1 (by rfl) ⟨1348892, by rfl⟩ : syracuseStep 1798523 = 2697785) B2697785
theorem B1798793 : Blo 798342 1798793 := bstep (se 2 (by rfl) ⟨674547, by rfl⟩ : syracuseStep 1798793 = 1349095) B1349095
theorem B4551329 : Blo 798342 4551329 := bstep (se 2 (by rfl) ⟨1706748, by rfl⟩ : syracuseStep 4551329 = 3413497) B3413497
theorem B1799009 : Blo 798342 1799009 := bstep (se 2 (by rfl) ⟨674628, by rfl⟩ : syracuseStep 1799009 = 1349257) B1349257
theorem B2028503 : Blo 798342 2028503 := bstep (se 1 (by rfl) ⟨1521377, by rfl⟩ : syracuseStep 2028503 = 3042755) B3042755
theorem B3044411 : Blo 798342 3044411 := bstep (se 1 (by rfl) ⟨2283308, by rfl⟩ : syracuseStep 3044411 = 4566617) B4566617
theorem B9729233 : Blo 798342 9729233 := bstep (se 2 (by rfl) ⟨3648462, by rfl⟩ : syracuseStep 9729233 = 7296925) B7296925
theorem B6092009 : Blo 798342 6092009 := bstep (se 2 (by rfl) ⟨2284503, by rfl⟩ : syracuseStep 6092009 = 4569007) B4569007
theorem B1799531 : Blo 798342 1799531 := bstep (se 1 (by rfl) ⟨1349648, by rfl⟩ : syracuseStep 1799531 = 2699297) B2699297
theorem B13006295 : Blo 798342 13006295 := bstep (se 1 (by rfl) ⟨9754721, by rfl⟩ : syracuseStep 13006295 = 19509443) B19509443
theorem B1799783 : Blo 798342 1799783 := bstep (se 1 (by rfl) ⟨1349837, by rfl⟩ : syracuseStep 1799783 = 2699675) B2699675
theorem B1799801 : Blo 798342 1799801 := bstep (se 2 (by rfl) ⟨674925, by rfl⟩ : syracuseStep 1799801 = 1349851) B1349851
theorem B8451793 : Blo 798342 8451793 := bstep (se 2 (by rfl) ⟨3169422, by rfl⟩ : syracuseStep 8451793 = 6338845) B6338845
theorem B1800161 : Blo 798342 1800161 := bstep (se 2 (by rfl) ⟨675060, by rfl⟩ : syracuseStep 1800161 = 1350121) B1350121
theorem B1800359 : Blo 798342 1800359 := bstep (se 1 (by rfl) ⟨1350269, by rfl⟩ : syracuseStep 1800359 = 2700539) B2700539
theorem B12974255 : Blo 798342 12974255 := bstep (se 1 (by rfl) ⟨9730691, by rfl⟩ : syracuseStep 12974255 = 19461383) B19461383
theorem B2029799 : Blo 798342 2029799 := bstep (se 1 (by rfl) ⟨1522349, by rfl⟩ : syracuseStep 2029799 = 3044699) B3044699
theorem B3045671 : Blo 798342 3045671 := bstep (se 1 (by rfl) ⟨2284253, by rfl⟩ : syracuseStep 3045671 = 4568507) B4568507
theorem B87456185 : Blo 798342 87456185 := bstep (se 2 (by rfl) ⟨32796069, by rfl⟩ : syracuseStep 87456185 = 65592139) B65592139
theorem B4553243 : Blo 798342 4553243 := bstep (se 1 (by rfl) ⟨3414932, by rfl⟩ : syracuseStep 4553243 = 6829865) B6829865
theorem B4160105 : Blo 798342 4160105 := bstep (se 2 (by rfl) ⟨1560039, by rfl⟩ : syracuseStep 4160105 = 3120079) B3120079
theorem B4324187 : Blo 798342 4324187 := bstep (se 1 (by rfl) ⟨3243140, by rfl⟩ : syracuseStep 4324187 = 6486281) B6486281
theorem B3046369 : Blo 798342 3046369 := bstep (se 2 (by rfl) ⟨1142388, by rfl⟩ : syracuseStep 3046369 = 2284777) B2284777
theorem B4553927 : Blo 798342 4553927 := bstep (se 1 (by rfl) ⟨3415445, by rfl⟩ : syracuseStep 4553927 = 6830891) B6830891
theorem B13172183 : Blo 798342 13172183 := bstep (se 1 (by rfl) ⟨9879137, by rfl⟩ : syracuseStep 13172183 = 19758275) B19758275
theorem B34537103 : Blo 798342 34537103 := bstep (se 1 (by rfl) ⟨25902827, by rfl⟩ : syracuseStep 34537103 = 51805655) B51805655
theorem B1802447 : Blo 798342 1802447 := bstep (se 1 (by rfl) ⟨1351835, by rfl⟩ : syracuseStep 1802447 = 2703671) B2703671
theorem B10945115 : Blo 798342 10945115 := bstep (se 1 (by rfl) ⟨8208836, by rfl⟩ : syracuseStep 10945115 = 16417673) B16417673
theorem B3245735 : Blo 798342 3245735 := bstep (se 1 (by rfl) ⟨2434301, by rfl⟩ : syracuseStep 3245735 = 4868603) B4868603
theorem B1705655 : Blo 798342 1705655 := bstep (se 1 (by rfl) ⟨1279241, by rfl⟩ : syracuseStep 1705655 = 2558483) B2558483
theorem B1804103 : Blo 798342 1804103 := bstep (se 1 (by rfl) ⟨1353077, by rfl⟩ : syracuseStep 1804103 = 2706155) B2706155
theorem B4327519 : Blo 798342 4327519 := bstep (se 1 (by rfl) ⟨3245639, by rfl⟩ : syracuseStep 4327519 = 6491279) B6491279
theorem B1804715 : Blo 798342 1804715 := bstep (se 1 (by rfl) ⟨1353536, by rfl⟩ : syracuseStep 1804715 = 2707073) B2707073
theorem B1804751 : Blo 798342 1804751 := bstep (se 1 (by rfl) ⟨1353563, by rfl⟩ : syracuseStep 1804751 = 2707127) B2707127
theorem B2886425 : Blo 798342 2886425 := bstep (se 2 (by rfl) ⟨1082409, by rfl⟩ : syracuseStep 2886425 = 2164819) B2164819
theorem B1281343 : Blo 798342 1281343 := bstep (se 1 (by rfl) ⟨961007, by rfl⟩ : syracuseStep 1281343 = 1922015) B1922015
theorem B1347239 : Blo 798342 1347239 := bstep (se 1 (by rfl) ⟨1010429, by rfl⟩ : syracuseStep 1347239 = 2020859) B2020859
theorem B6492383 : Blo 798342 6492383 := bstep (se 1 (by rfl) ⟨4869287, by rfl⟩ : syracuseStep 6492383 = 9738575) B9738575
theorem B1347887 : Blo 798342 1347887 := bstep (se 1 (by rfl) ⟨1010915, by rfl⟩ : syracuseStep 1347887 = 2021831) B2021831
theorem B1348859 : Blo 798342 1348859 := bstep (se 1 (by rfl) ⟨1011644, by rfl⟩ : syracuseStep 1348859 = 2023289) B2023289
theorem B31233539 : Blo 798342 31233539 := bstep (se 1 (by rfl) ⟨23425154, by rfl⟩ : syracuseStep 31233539 = 46850309) B46850309
theorem B1349183 : Blo 798342 1349183 := bstep (se 1 (by rfl) ⟨1011887, by rfl⟩ : syracuseStep 1349183 = 2023775) B2023775
theorem B8754767 : Blo 798342 8754767 := bstep (se 1 (by rfl) ⟨6566075, by rfl⟩ : syracuseStep 8754767 = 13132151) B13132151
theorem B3413839 : Blo 798342 3413839 := bstep (se 1 (by rfl) ⟨2560379, by rfl⟩ : syracuseStep 3413839 = 5120759) B5120759
theorem B1349743 : Blo 798342 1349743 := bstep (se 1 (by rfl) ⟨1012307, by rfl⟩ : syracuseStep 1349743 = 2024615) B2024615
theorem B3250799 : Blo 798342 3250799 := bstep (se 1 (by rfl) ⟨2438099, by rfl⟩ : syracuseStep 3250799 = 4876199) B4876199
theorem B1711567 : Blo 798342 1711567 := bstep (se 1 (by rfl) ⟨1283675, by rfl⟩ : syracuseStep 1711567 = 2567351) B2567351
theorem B1711687 : Blo 798342 1711687 := bstep (se 1 (by rfl) ⟨1283765, by rfl⟩ : syracuseStep 1711687 = 2567531) B2567531
theorem B1711867 : Blo 798342 1711867 := bstep (se 1 (by rfl) ⟨1283900, by rfl⟩ : syracuseStep 1711867 = 2567801) B2567801
theorem B2891659 : Blo 798342 2891659 := bstep (se 1 (by rfl) ⟨2168744, by rfl⟩ : syracuseStep 2891659 = 4337489) B4337489
theorem B1351903 : Blo 798342 1351903 := bstep (se 1 (by rfl) ⟨1013927, by rfl⟩ : syracuseStep 1351903 = 2027855) B2027855
theorem B1352335 : Blo 798342 1352335 := bstep (se 1 (by rfl) ⟨1014251, by rfl⟩ : syracuseStep 1352335 = 2028503) B2028503
theorem B1516457 : Blo 798342 1516457 := bstep (se 2 (by rfl) ⟨568671, by rfl⟩ : syracuseStep 1516457 = 1137343) B1137343
theorem B1353199 : Blo 798342 1353199 := bstep (se 1 (by rfl) ⟨1014899, by rfl⟩ : syracuseStep 1353199 = 2029799) B2029799
theorem B58304123 : Blo 798342 58304123 := bstep (se 1 (by rfl) ⟨43728092, by rfl⟩ : syracuseStep 58304123 = 87456185) B87456185
theorem B2565761 : Blo 798342 2565761 := bstep (se 2 (by rfl) ⟨962160, by rfl⟩ : syracuseStep 2565761 = 1924321) B1924321
theorem B20522807 : Blo 798342 20522807 := bstep (se 1 (by rfl) ⟨15392105, by rfl⟩ : syracuseStep 20522807 = 30784211) B30784211
theorem B5122091 : Blo 798342 5122091 := bstep (se 1 (by rfl) ⟨3841568, by rfl⟩ : syracuseStep 5122091 = 7683137) B7683137
theorem B3418487 : Blo 798342 3418487 := bstep (se 1 (by rfl) ⟨2563865, by rfl⟩ : syracuseStep 3418487 = 5127731) B5127731
theorem B2697947 : Blo 798342 2697947 := bstep (se 1 (by rfl) ⟨2023460, by rfl⟩ : syracuseStep 2697947 = 4046921) B4046921
theorem B2436079 : Blo 798342 2436079 := bstep (se 1 (by rfl) ⟨1827059, by rfl⟩ : syracuseStep 2436079 = 3654119) B3654119
theorem B1519145 : Blo 798342 1519145 := bstep (se 2 (by rfl) ⟨569679, by rfl⟩ : syracuseStep 1519145 = 1139359) B1139359
theorem B2698919 : Blo 798342 2698919 := bstep (se 1 (by rfl) ⟨2024189, by rfl⟩ : syracuseStep 2698919 = 4048379) B4048379
theorem B798439 : Blo 798342 798439 := bstep (se 1 (by rfl) ⟨598829, by rfl⟩ : syracuseStep 798439 = 1197659) B1197659
theorem B798751 : Blo 798342 798751 := bstep (se 1 (by rfl) ⟨599063, by rfl⟩ : syracuseStep 798751 = 1198127) B1198127
theorem B798927 : Blo 798342 798927 := bstep (se 1 (by rfl) ⟨599195, by rfl⟩ : syracuseStep 798927 = 1198391) B1198391
theorem B799047 : Blo 798342 799047 := bstep (se 1 (by rfl) ⟨599285, by rfl⟩ : syracuseStep 799047 = 1198571) B1198571
theorem B799207 : Blo 798342 799207 := bstep (se 1 (by rfl) ⟨599405, by rfl⟩ : syracuseStep 799207 = 1198811) B1198811
theorem B799231 : Blo 798342 799231 := bstep (se 1 (by rfl) ⟨599423, by rfl⟩ : syracuseStep 799231 = 1198847) B1198847
theorem B832111 : Blo 798342 832111 := bstep (se 1 (by rfl) ⟨624083, by rfl⟩ : syracuseStep 832111 = 1248167) B1248167
theorem B799711 : Blo 798342 799711 := bstep (se 1 (by rfl) ⟨599783, by rfl⟩ : syracuseStep 799711 = 1199567) B1199567
theorem B799771 : Blo 798342 799771 := bstep (se 1 (by rfl) ⟨599828, by rfl⟩ : syracuseStep 799771 = 1199657) B1199657
theorem B799967 : Blo 798342 799967 := bstep (se 1 (by rfl) ⟨599975, by rfl⟩ : syracuseStep 799967 = 1199951) B1199951
theorem B800047 : Blo 798342 800047 := bstep (se 1 (by rfl) ⟨600035, by rfl⟩ : syracuseStep 800047 = 1200071) B1200071
theorem B898375 : Blo 798342 898375 := bstep (se 1 (by rfl) ⟨673781, by rfl⟩ : syracuseStep 898375 = 1347563) B1347563
theorem B800103 : Blo 798342 800103 := bstep (se 1 (by rfl) ⟨600077, by rfl⟩ : syracuseStep 800103 = 1200155) B1200155
theorem B2700647 : Blo 798342 2700647 := bstep (se 1 (by rfl) ⟨2025485, by rfl⟩ : syracuseStep 2700647 = 4050971) B4050971
theorem B2700755 : Blo 798342 2700755 := bstep (se 1 (by rfl) ⟨2025566, by rfl⟩ : syracuseStep 2700755 = 4051133) B4051133
theorem B800287 : Blo 798342 800287 := bstep (se 1 (by rfl) ⟨600215, by rfl⟩ : syracuseStep 800287 = 1200431) B1200431
theorem B800359 : Blo 798342 800359 := bstep (se 1 (by rfl) ⟨600269, by rfl⟩ : syracuseStep 800359 = 1200539) B1200539
theorem B800383 : Blo 798342 800383 := bstep (se 1 (by rfl) ⟨600287, by rfl⟩ : syracuseStep 800383 = 1200575) B1200575
theorem B800447 : Blo 798342 800447 := bstep (se 1 (by rfl) ⟨600335, by rfl⟩ : syracuseStep 800447 = 1200671) B1200671
theorem B800639 : Blo 798342 800639 := bstep (se 1 (by rfl) ⟨600479, by rfl⟩ : syracuseStep 800639 = 1200959) B1200959
theorem B800735 : Blo 798342 800735 := bstep (se 1 (by rfl) ⟨600551, by rfl⟩ : syracuseStep 800735 = 1201103) B1201103
theorem B800795 : Blo 798342 800795 := bstep (se 1 (by rfl) ⟨600596, by rfl⟩ : syracuseStep 800795 = 1201193) B1201193
theorem B800815 : Blo 798342 800815 := bstep (se 1 (by rfl) ⟨600611, by rfl⟩ : syracuseStep 800815 = 1201223) B1201223
theorem B800935 : Blo 798342 800935 := bstep (se 1 (by rfl) ⟨600701, by rfl⟩ : syracuseStep 800935 = 1201403) B1201403
theorem B800975 : Blo 798342 800975 := bstep (se 1 (by rfl) ⟨600731, by rfl⟩ : syracuseStep 800975 = 1201463) B1201463
theorem B9124163 : Blo 798342 9124163 := bstep (se 1 (by rfl) ⟨6843122, by rfl⟩ : syracuseStep 9124163 = 13686245) B13686245
theorem B801179 : Blo 798342 801179 := bstep (se 1 (by rfl) ⟨600884, by rfl⟩ : syracuseStep 801179 = 1201769) B1201769
theorem B2276075 : Blo 798342 2276075 := bstep (se 1 (by rfl) ⟨1707056, by rfl⟩ : syracuseStep 2276075 = 3414113) B3414113
theorem B801535 : Blo 798342 801535 := bstep (se 1 (by rfl) ⟨601151, by rfl⟩ : syracuseStep 801535 = 1202303) B1202303
theorem B801599 : Blo 798342 801599 := bstep (se 1 (by rfl) ⟨601199, by rfl⟩ : syracuseStep 801599 = 1202399) B1202399
theorem B801639 : Blo 798342 801639 := bstep (se 1 (by rfl) ⟨601229, by rfl⟩ : syracuseStep 801639 = 1202459) B1202459
theorem B801855 : Blo 798342 801855 := bstep (se 1 (by rfl) ⟨601391, by rfl⟩ : syracuseStep 801855 = 1202783) B1202783
theorem B4045949 : Blo 798342 4045949 := bstep (se 3 (by rfl) ⟨758615, by rfl⟩ : syracuseStep 4045949 = 1517231) B1517231
theorem B801919 : Blo 798342 801919 := bstep (se 1 (by rfl) ⟨601439, by rfl⟩ : syracuseStep 801919 = 1202879) B1202879
theorem B801947 : Blo 798342 801947 := bstep (se 1 (by rfl) ⟨601460, by rfl⟩ : syracuseStep 801947 = 1202921) B1202921
theorem B3652769 : Blo 798342 3652769 := bstep (se 2 (by rfl) ⟨1369788, by rfl⟩ : syracuseStep 3652769 = 2739577) B2739577
theorem B802031 : Blo 798342 802031 := bstep (se 1 (by rfl) ⟨601523, by rfl⟩ : syracuseStep 802031 = 1203047) B1203047
theorem B802075 : Blo 798342 802075 := bstep (se 1 (by rfl) ⟨601556, by rfl⟩ : syracuseStep 802075 = 1203113) B1203113
theorem B802175 : Blo 798342 802175 := bstep (se 1 (by rfl) ⟨601631, by rfl⟩ : syracuseStep 802175 = 1203263) B1203263
theorem B802203 : Blo 798342 802203 := bstep (se 1 (by rfl) ⟨601652, by rfl⟩ : syracuseStep 802203 = 1203305) B1203305
theorem B802287 : Blo 798342 802287 := bstep (se 1 (by rfl) ⟨601715, by rfl⟩ : syracuseStep 802287 = 1203431) B1203431
theorem B2703347 : Blo 798342 2703347 := bstep (se 1 (by rfl) ⟨2027510, by rfl⟩ : syracuseStep 2703347 = 4055021) B4055021
theorem B901183 : Blo 798342 901183 := bstep (se 1 (by rfl) ⟨675887, by rfl⟩ : syracuseStep 901183 = 1351775) B1351775
theorem B11518199 : Blo 798342 11518199 := bstep (se 1 (by rfl) ⟨8638649, by rfl⟩ : syracuseStep 11518199 = 17277299) B17277299
theorem B3031303 : Blo 798342 3031303 := bstep (se 1 (by rfl) ⟨2273477, by rfl⟩ : syracuseStep 3031303 = 4546955) B4546955
theorem B5194057 : Blo 798342 5194057 := bstep (se 2 (by rfl) ⟨1947771, by rfl⟩ : syracuseStep 5194057 = 3895543) B3895543
theorem B3425321 : Blo 798342 3425321 := bstep (se 2 (by rfl) ⟨1284495, by rfl⟩ : syracuseStep 3425321 = 2568991) B2568991
theorem B11519171 : Blo 798342 11519171 := bstep (se 1 (by rfl) ⟨8639378, by rfl⟩ : syracuseStep 11519171 = 17278757) B17278757
theorem B1197737 : Blo 798342 1197737 := bstep (se 2 (by rfl) ⟨449151, by rfl⟩ : syracuseStep 1197737 = 898303) B898303
theorem B1197947 : Blo 798342 1197947 := bstep (se 1 (by rfl) ⟨898460, by rfl⟩ : syracuseStep 1197947 = 1796921) B1796921
theorem B1198367 : Blo 798342 1198367 := bstep (se 1 (by rfl) ⟨898775, by rfl⟩ : syracuseStep 1198367 = 1797551) B1797551
theorem B1198535 : Blo 798342 1198535 := bstep (se 1 (by rfl) ⟨898901, by rfl⟩ : syracuseStep 1198535 = 1797803) B1797803
theorem B1198895 : Blo 798342 1198895 := bstep (se 1 (by rfl) ⟨899171, by rfl⟩ : syracuseStep 1198895 = 1798343) B1798343
theorem B1199015 : Blo 798342 1199015 := bstep (se 1 (by rfl) ⟨899261, by rfl⟩ : syracuseStep 1199015 = 1798523) B1798523
theorem B2739167 : Blo 798342 2739167 := bstep (se 1 (by rfl) ⟨2054375, by rfl⟩ : syracuseStep 2739167 = 4108751) B4108751
theorem B1199195 : Blo 798342 1199195 := bstep (se 1 (by rfl) ⟨899396, by rfl⟩ : syracuseStep 1199195 = 1798793) B1798793
theorem B3034219 : Blo 798342 3034219 := bstep (se 1 (by rfl) ⟨2275664, by rfl⟩ : syracuseStep 3034219 = 4551329) B4551329
theorem B1199339 : Blo 798342 1199339 := bstep (se 1 (by rfl) ⟨899504, by rfl⟩ : syracuseStep 1199339 = 1799009) B1799009
theorem B4115767 : Blo 798342 4115767 := bstep (se 1 (by rfl) ⟨3086825, by rfl⟩ : syracuseStep 4115767 = 6173651) B6173651
theorem B5852645 : Blo 798342 5852645 := bstep (se 4 (by rfl) ⟨548685, by rfl⟩ : syracuseStep 5852645 = 1097371) B1097371
theorem B1199687 : Blo 798342 1199687 := bstep (se 1 (by rfl) ⟨899765, by rfl⟩ : syracuseStep 1199687 = 1799531) B1799531
theorem B8670863 : Blo 798342 8670863 := bstep (se 1 (by rfl) ⟨6503147, by rfl⟩ : syracuseStep 8670863 = 13006295) B13006295
theorem B1199855 : Blo 798342 1199855 := bstep (se 1 (by rfl) ⟨899891, by rfl⟩ : syracuseStep 1199855 = 1799783) B1799783
theorem B1199867 : Blo 798342 1199867 := bstep (se 1 (by rfl) ⟨899900, by rfl⟩ : syracuseStep 1199867 = 1799801) B1799801
theorem B1200041 : Blo 798342 1200041 := bstep (se 2 (by rfl) ⟨450015, by rfl⟩ : syracuseStep 1200041 = 900031) B900031
theorem B41013221 : Blo 798342 41013221 := bstep (se 4 (by rfl) ⟨3844989, by rfl⟩ : syracuseStep 41013221 = 7689979) B7689979
theorem B1200107 : Blo 798342 1200107 := bstep (se 1 (by rfl) ⟨900080, by rfl⟩ : syracuseStep 1200107 = 1800161) B1800161
theorem B1200239 : Blo 798342 1200239 := bstep (se 1 (by rfl) ⟨900179, by rfl⟩ : syracuseStep 1200239 = 1800359) B1800359
theorem B3035495 : Blo 798342 3035495 := bstep (se 1 (by rfl) ⟨2276621, by rfl⟩ : syracuseStep 3035495 = 4553243) B4553243
theorem B2773403 : Blo 798342 2773403 := bstep (se 1 (by rfl) ⟨2080052, by rfl⟩ : syracuseStep 2773403 = 4160105) B4160105
theorem B5755319 : Blo 798342 5755319 := bstep (se 1 (by rfl) ⟨4316489, by rfl⟩ : syracuseStep 5755319 = 8632979) B8632979
theorem B29250017 : Blo 798342 29250017 := bstep (se 2 (by rfl) ⟨10968756, by rfl⟩ : syracuseStep 29250017 = 21937513) B21937513
theorem B28103155 : Blo 798342 28103155 := bstep (se 1 (by rfl) ⟨21077366, by rfl⟩ : syracuseStep 28103155 = 42154733) B42154733
theorem B3035951 : Blo 798342 3035951 := bstep (se 1 (by rfl) ⟨2276963, by rfl⟩ : syracuseStep 3035951 = 4553927) B4553927
theorem B1201145 : Blo 798342 1201145 := bstep (se 2 (by rfl) ⟨450429, by rfl⟩ : syracuseStep 1201145 = 900859) B900859
theorem B23024735 : Blo 798342 23024735 := bstep (se 1 (by rfl) ⟨17268551, by rfl⟩ : syracuseStep 23024735 = 34537103) B34537103
theorem B6084719 : Blo 798342 6084719 := bstep (se 1 (by rfl) ⟨4563539, by rfl⟩ : syracuseStep 6084719 = 9127079) B9127079
theorem B2283707 : Blo 798342 2283707 := bstep (se 1 (by rfl) ⟨1712780, by rfl⟩ : syracuseStep 2283707 = 3425561) B3425561
theorem B12966331 : Blo 798342 12966331 := bstep (se 1 (by rfl) ⟨9724748, by rfl⟩ : syracuseStep 12966331 = 19449497) B19449497
theorem B1202681 : Blo 798342 1202681 := bstep (se 2 (by rfl) ⟨451005, by rfl⟩ : syracuseStep 1202681 = 902011) B902011
theorem B2022185 : Blo 798342 2022185 := bstep (se 2 (by rfl) ⟨758319, by rfl⟩ : syracuseStep 2022185 = 1516639) B1516639
theorem B6085691 : Blo 798342 6085691 := bstep (se 1 (by rfl) ⟨4564268, by rfl⟩ : syracuseStep 6085691 = 9128537) B9128537
theorem B5135471 : Blo 798342 5135471 := bstep (se 1 (by rfl) ⟨3851603, by rfl⟩ : syracuseStep 5135471 = 7703207) B7703207
theorem B1203311 : Blo 798342 1203311 := bstep (se 1 (by rfl) ⟨902483, by rfl⟩ : syracuseStep 1203311 = 1804967) B1804967
theorem B5758087 : Blo 798342 5758087 := bstep (se 1 (by rfl) ⟨4318565, by rfl⟩ : syracuseStep 5758087 = 8637131) B8637131
theorem B6839639 : Blo 798342 6839639 := bstep (se 1 (by rfl) ⟨5129729, by rfl⟩ : syracuseStep 6839639 = 10259459) B10259459
theorem B6086177 : Blo 798342 6086177 := bstep (se 2 (by rfl) ⟨2282316, by rfl⟩ : syracuseStep 6086177 = 4564633) B4564633
theorem B10935971 : Blo 798342 10935971 := bstep (se 1 (by rfl) ⟨8201978, by rfl⟩ : syracuseStep 10935971 = 16403957) B16403957
theorem B8773691 : Blo 798342 8773691 := bstep (se 1 (by rfl) ⟨6580268, by rfl⟩ : syracuseStep 8773691 = 13160537) B13160537
theorem B4055831 : Blo 798342 4055831 := bstep (se 1 (by rfl) ⟨3041873, by rfl⟩ : syracuseStep 4055831 = 6083747) B6083747
theorem B6087635 : Blo 798342 6087635 := bstep (se 1 (by rfl) ⟨4565726, by rfl⟩ : syracuseStep 6087635 = 9131453) B9131453
theorem B4056155 : Blo 798342 4056155 := bstep (se 1 (by rfl) ⟨3042116, by rfl⟩ : syracuseStep 4056155 = 6084233) B6084233
theorem B3041023 : Blo 798342 3041023 := bstep (se 1 (by rfl) ⟨2280767, by rfl⟩ : syracuseStep 3041023 = 4561535) B4561535
theorem B12347255 : Blo 798342 12347255 := bstep (se 1 (by rfl) ⟨9260441, by rfl⟩ : syracuseStep 12347255 = 18520883) B18520883
theorem B6088607 : Blo 798342 6088607 := bstep (se 1 (by rfl) ⟨4566455, by rfl⟩ : syracuseStep 6088607 = 9132911) B9132911
theorem B3041327 : Blo 798342 3041327 := bstep (se 1 (by rfl) ⟨2280995, by rfl⟩ : syracuseStep 3041327 = 4561991) B4561991
theorem B6482359 : Blo 798342 6482359 := bstep (se 1 (by rfl) ⟨4861769, by rfl⟩ : syracuseStep 6482359 = 9723539) B9723539
theorem B3238667 : Blo 798342 3238667 := bstep (se 1 (by rfl) ⟨2429000, by rfl⟩ : syracuseStep 3238667 = 4858001) B4858001
theorem B4057937 : Blo 798342 4057937 := bstep (se 2 (by rfl) ⟨1521726, by rfl⟩ : syracuseStep 4057937 = 3043453) B3043453
theorem B3042299 : Blo 798342 3042299 := bstep (se 1 (by rfl) ⟨2281724, by rfl⟩ : syracuseStep 3042299 = 4563449) B4563449
theorem B3042953 : Blo 798342 3042953 := bstep (se 2 (by rfl) ⟨1141107, by rfl⟩ : syracuseStep 3042953 = 2282215) B2282215
theorem B2158807 : Blo 798342 2158807 := bstep (se 1 (by rfl) ⟨1619105, by rfl⟩ : syracuseStep 2158807 = 3238211) B3238211
theorem B1798559 : Blo 798342 1798559 := bstep (se 1 (by rfl) ⟨1348919, by rfl⟩ : syracuseStep 1798559 = 2697839) B2697839
theorem B1536425 : Blo 798342 1536425 := bstep (se 2 (by rfl) ⟨576159, by rfl⟩ : syracuseStep 1536425 = 1152319) B1152319
theorem B7696943 : Blo 798342 7696943 := bstep (se 1 (by rfl) ⟨5772707, by rfl⟩ : syracuseStep 7696943 = 11545415) B11545415
theorem B11269057 : Blo 798342 11269057 := bstep (se 2 (by rfl) ⟨4225896, by rfl⟩ : syracuseStep 11269057 = 8451793) B8451793
theorem B20509685 : Blo 798342 20509685 := bstep (se 5 (by rfl) ⟨961391, by rfl⟩ : syracuseStep 20509685 = 1922783) B1922783
theorem B13006817 : Blo 798342 13006817 := bstep (se 2 (by rfl) ⟨4877556, by rfl⟩ : syracuseStep 13006817 = 9755113) B9755113
theorem B2029607 : Blo 798342 2029607 := bstep (se 1 (by rfl) ⟨1522205, by rfl⟩ : syracuseStep 2029607 = 3044411) B3044411
theorem B6486155 : Blo 798342 6486155 := bstep (se 1 (by rfl) ⟨4864616, by rfl⟩ : syracuseStep 6486155 = 9729233) B9729233
theorem B4061339 : Blo 798342 4061339 := bstep (se 1 (by rfl) ⟨3046004, by rfl⟩ : syracuseStep 4061339 = 6092009) B6092009
theorem B4061825 : Blo 798342 4061825 := bstep (se 2 (by rfl) ⟨1523184, by rfl⟩ : syracuseStep 4061825 = 3046369) B3046369
theorem B9108125 : Blo 798342 9108125 := bstep (se 3 (by rfl) ⟨1707773, by rfl⟩ : syracuseStep 9108125 = 3415547) B3415547
theorem B9730783 : Blo 798342 9730783 := bstep (se 1 (by rfl) ⟨7298087, by rfl⟩ : syracuseStep 9730783 = 14596175) B14596175
theorem B8649503 : Blo 798342 8649503 := bstep (se 1 (by rfl) ⟨6487127, by rfl⟩ : syracuseStep 8649503 = 12974255) B12974255
theorem B2030447 : Blo 798342 2030447 := bstep (se 1 (by rfl) ⟨1522835, by rfl⟩ : syracuseStep 2030447 = 3045671) B3045671
theorem B11566223 : Blo 798342 11566223 := bstep (se 1 (by rfl) ⟨8674667, by rfl⟩ : syracuseStep 11566223 = 17349335) B17349335
theorem B2882791 : Blo 798342 2882791 := bstep (se 1 (by rfl) ⟨2162093, by rfl⟩ : syracuseStep 2882791 = 4324187) B4324187
theorem B49184243 : Blo 798342 49184243 := bstep (se 1 (by rfl) ⟨36888182, by rfl⟩ : syracuseStep 49184243 = 73776365) B73776365
theorem B8781455 : Blo 798342 8781455 := bstep (se 1 (by rfl) ⟨6586091, by rfl⟩ : syracuseStep 8781455 = 13172183) B13172183
theorem B23396509 : Blo 798342 23396509 := bstep (se 3 (by rfl) ⟨4386845, by rfl⟩ : syracuseStep 23396509 = 8773691) B8773691
theorem B1802537 : Blo 798342 1802537 := bstep (se 2 (by rfl) ⟨675951, by rfl⟩ : syracuseStep 1802537 = 1351903) B1351903
theorem B1803113 : Blo 798342 1803113 := bstep (se 2 (by rfl) ⟨676167, by rfl⟩ : syracuseStep 1803113 = 1352335) B1352335
theorem B2163823 : Blo 798342 2163823 := bstep (se 1 (by rfl) ⟨1622867, by rfl⟩ : syracuseStep 2163823 = 3245735) B3245735
theorem B1804265 : Blo 798342 1804265 := bstep (se 2 (by rfl) ⟨676599, by rfl⟩ : syracuseStep 1804265 = 1353199) B1353199
theorem B3901763 : Blo 798342 3901763 := bstep (se 1 (by rfl) ⟨2926322, by rfl⟩ : syracuseStep 3901763 = 5852645) B5852645
theorem B149883493 : Blo 798342 149883493 := bstep (se 4 (by rfl) ⟨14051577, by rfl⟩ : syracuseStep 149883493 = 28103155) B28103155
theorem B5770025 : Blo 798342 5770025 := bstep (se 2 (by rfl) ⟨2163759, by rfl⟩ : syracuseStep 5770025 = 4327519) B4327519
theorem B4328255 : Blo 798342 4328255 := bstep (se 1 (by rfl) ⟨3246191, by rfl⟩ : syracuseStep 4328255 = 6492383) B6492383
theorem B3836879 : Blo 798342 3836879 := bstep (se 1 (by rfl) ⟨2877659, by rfl⟩ : syracuseStep 3836879 = 5755319) B5755319
theorem B19500011 : Blo 798342 19500011 := bstep (se 1 (by rfl) ⟨14625008, by rfl⟩ : syracuseStep 19500011 = 29250017) B29250017
theorem B5836511 : Blo 798342 5836511 := bstep (se 1 (by rfl) ⟨4377383, by rfl⟩ : syracuseStep 5836511 = 8754767) B8754767
theorem B3248105 : Blo 798342 3248105 := bstep (se 2 (by rfl) ⟨1218039, by rfl⟩ : syracuseStep 3248105 = 2436079) B2436079
theorem B2167199 : Blo 798342 2167199 := bstep (se 1 (by rfl) ⟨1625399, by rfl⟩ : syracuseStep 2167199 = 3250799) B3250799
theorem B1708457 : Blo 798342 1708457 := bstep (se 2 (by rfl) ⟨640671, by rfl⟩ : syracuseStep 1708457 = 1281343) B1281343
theorem B1348123 : Blo 798342 1348123 := bstep (se 1 (by rfl) ⟨1011092, by rfl⟩ : syracuseStep 1348123 = 2022185) B2022185
theorem B4559759 : Blo 798342 4559759 := bstep (se 1 (by rfl) ⟨3419819, by rfl⟩ : syracuseStep 4559759 = 6839639) B6839639
theorem B38869415 : Blo 798342 38869415 := bstep (se 1 (by rfl) ⟨29152061, by rfl⟩ : syracuseStep 38869415 = 58304123) B58304123
theorem B8231503 : Blo 798342 8231503 := bstep (se 1 (by rfl) ⟨6173627, by rfl⟩ : syracuseStep 8231503 = 12347255) B12347255
theorem B3414727 : Blo 798342 3414727 := bstep (se 1 (by rfl) ⟨2561045, by rfl⟩ : syracuseStep 3414727 = 5122091) B5122091
theorem B1024283 : Blo 798342 1024283 := bstep (se 1 (by rfl) ⟨768212, by rfl⟩ : syracuseStep 1024283 = 1536425) B1536425
theorem B13673123 : Blo 798342 13673123 := bstep (se 1 (by rfl) ⟨10254842, by rfl⟩ : syracuseStep 13673123 = 20509685) B20509685
theorem B1353071 : Blo 798342 1353071 := bstep (se 1 (by rfl) ⟨1014803, by rfl⟩ : syracuseStep 1353071 = 2029607) B2029607
theorem B7677449 : Blo 798342 7677449 := bstep (se 2 (by rfl) ⟨2879043, by rfl⟩ : syracuseStep 7677449 = 5758087) B5758087
theorem B3843721 : Blo 798342 3843721 := bstep (se 2 (by rfl) ⟨1441395, by rfl⟩ : syracuseStep 3843721 = 2882791) B2882791
theorem B6072083 : Blo 798342 6072083 := bstep (se 1 (by rfl) ⟨4554062, by rfl⟩ : syracuseStep 6072083 = 9108125) B9108125
theorem B1517383 : Blo 798342 1517383 := bstep (se 1 (by rfl) ⟨1138037, by rfl⟩ : syracuseStep 1517383 = 2276075) B2276075
theorem B1353631 : Blo 798342 1353631 := bstep (se 1 (by rfl) ⟨1015223, by rfl⟩ : syracuseStep 1353631 = 2030447) B2030447
theorem B2697299 : Blo 798342 2697299 := bstep (se 1 (by rfl) ⟨2022974, by rfl⟩ : syracuseStep 2697299 = 4045949) B4045949
theorem B7710815 : Blo 798342 7710815 := bstep (se 1 (by rfl) ⟨5783111, by rfl⟩ : syracuseStep 7710815 = 11566223) B11566223
theorem B2435179 : Blo 798342 2435179 := bstep (se 1 (by rfl) ⟨1826384, by rfl⟩ : syracuseStep 2435179 = 3652769) B3652769
theorem B7678799 : Blo 798342 7678799 := bstep (se 1 (by rfl) ⟨5759099, by rfl⟩ : syracuseStep 7678799 = 11518199) B11518199
theorem B4041737 : Blo 798342 4041737 := bstep (se 2 (by rfl) ⟨1515651, by rfl⟩ : syracuseStep 4041737 = 3031303) B3031303
theorem B6925409 : Blo 798342 6925409 := bstep (se 2 (by rfl) ⟨2597028, by rfl⟩ : syracuseStep 6925409 = 5194057) B5194057
theorem B7679447 : Blo 798342 7679447 := bstep (se 1 (by rfl) ⟨5759585, by rfl⟩ : syracuseStep 7679447 = 11519171) B11519171
theorem B798491 : Blo 798342 798491 := bstep (se 1 (by rfl) ⟨598868, by rfl⟩ : syracuseStep 798491 = 1197737) B1197737
theorem B798631 : Blo 798342 798631 := bstep (se 1 (by rfl) ⟨598973, by rfl⟩ : syracuseStep 798631 = 1197947) B1197947
theorem B798911 : Blo 798342 798911 := bstep (se 1 (by rfl) ⟨599183, by rfl⟩ : syracuseStep 798911 = 1198367) B1198367
theorem B799023 : Blo 798342 799023 := bstep (se 1 (by rfl) ⟨599267, by rfl⟩ : syracuseStep 799023 = 1198535) B1198535
theorem B799263 : Blo 798342 799263 := bstep (se 1 (by rfl) ⟨599447, by rfl⟩ : syracuseStep 799263 = 1198895) B1198895
theorem B799343 : Blo 798342 799343 := bstep (se 1 (by rfl) ⟨599507, by rfl⟩ : syracuseStep 799343 = 1199015) B1199015
theorem B799463 : Blo 798342 799463 := bstep (se 1 (by rfl) ⟨599597, by rfl⟩ : syracuseStep 799463 = 1199195) B1199195
theorem B799559 : Blo 798342 799559 := bstep (se 1 (by rfl) ⟨599669, by rfl⟩ : syracuseStep 799559 = 1199339) B1199339
theorem B799791 : Blo 798342 799791 := bstep (se 1 (by rfl) ⟨599843, by rfl⟩ : syracuseStep 799791 = 1199687) B1199687
theorem B5780575 : Blo 798342 5780575 := bstep (se 1 (by rfl) ⟨4335431, by rfl⟩ : syracuseStep 5780575 = 8670863) B8670863
theorem B898159 : Blo 798342 898159 := bstep (se 1 (by rfl) ⟨673619, by rfl⟩ : syracuseStep 898159 = 1347239) B1347239
theorem B799903 : Blo 798342 799903 := bstep (se 1 (by rfl) ⟨599927, by rfl⟩ : syracuseStep 799903 = 1199855) B1199855
theorem B799911 : Blo 798342 799911 := bstep (se 1 (by rfl) ⟨599933, by rfl⟩ : syracuseStep 799911 = 1199867) B1199867
theorem B800027 : Blo 798342 800027 := bstep (se 1 (by rfl) ⟨600020, by rfl⟩ : syracuseStep 800027 = 1200041) B1200041
theorem B800071 : Blo 798342 800071 := bstep (se 1 (by rfl) ⟨600053, by rfl⟩ : syracuseStep 800071 = 1200107) B1200107
theorem B800159 : Blo 798342 800159 := bstep (se 1 (by rfl) ⟨600119, by rfl⟩ : syracuseStep 800159 = 1200239) B1200239
theorem B898591 : Blo 798342 898591 := bstep (se 1 (by rfl) ⟨673943, by rfl⟩ : syracuseStep 898591 = 1347887) B1347887
theorem B1848935 : Blo 798342 1848935 := bstep (se 1 (by rfl) ⟨1386701, by rfl⟩ : syracuseStep 1848935 = 2773403) B2773403
theorem B4437925 : Blo 798342 4437925 := bstep (se 4 (by rfl) ⟨416055, by rfl⟩ : syracuseStep 4437925 = 832111) B832111
theorem B800763 : Blo 798342 800763 := bstep (se 1 (by rfl) ⟨600572, by rfl⟩ : syracuseStep 800763 = 1201145) B1201145
theorem B15349823 : Blo 798342 15349823 := bstep (se 1 (by rfl) ⟨11512367, by rfl⟩ : syracuseStep 15349823 = 23024735) B23024735
theorem B899239 : Blo 798342 899239 := bstep (se 1 (by rfl) ⟨674429, by rfl⟩ : syracuseStep 899239 = 1348859) B1348859
theorem B20822359 : Blo 798342 20822359 := bstep (se 1 (by rfl) ⟨15616769, by rfl⟩ : syracuseStep 20822359 = 31233539) B31233539
theorem B899455 : Blo 798342 899455 := bstep (se 1 (by rfl) ⟨674591, by rfl⟩ : syracuseStep 899455 = 1349183) B1349183
theorem B1522471 : Blo 798342 1522471 := bstep (se 1 (by rfl) ⟨1141853, by rfl⟩ : syracuseStep 1522471 = 2283707) B2283707
theorem B4045625 : Blo 798342 4045625 := bstep (se 2 (by rfl) ⟨1517109, by rfl⟩ : syracuseStep 4045625 = 3034219) B3034219
theorem B801787 : Blo 798342 801787 := bstep (se 1 (by rfl) ⟨601340, by rfl⟩ : syracuseStep 801787 = 1202681) B1202681
theorem B5487689 : Blo 798342 5487689 := bstep (se 2 (by rfl) ⟨2057883, by rfl⟩ : syracuseStep 5487689 = 4115767) B4115767
theorem B3423647 : Blo 798342 3423647 := bstep (se 1 (by rfl) ⟨2567735, by rfl⟩ : syracuseStep 3423647 = 5135471) B5135471
theorem B802207 : Blo 798342 802207 := bstep (se 1 (by rfl) ⟨601655, by rfl⟩ : syracuseStep 802207 = 1203311) B1203311
theorem B7290647 : Blo 798342 7290647 := bstep (se 1 (by rfl) ⟨5467985, by rfl⟩ : syracuseStep 7290647 = 10935971) B10935971
theorem B2703887 : Blo 798342 2703887 := bstep (se 1 (by rfl) ⟨2027915, by rfl⟩ : syracuseStep 2703887 = 4055831) B4055831
theorem B2704103 : Blo 798342 2704103 := bstep (se 1 (by rfl) ⟨2028077, by rfl⟩ : syracuseStep 2704103 = 4056155) B4056155
theorem B13681871 : Blo 798342 13681871 := bstep (se 1 (by rfl) ⟨10261403, by rfl⟩ : syracuseStep 13681871 = 20522807) B20522807
theorem B15025409 : Blo 798342 15025409 := bstep (se 2 (by rfl) ⟨5634528, by rfl⟩ : syracuseStep 15025409 = 11269057) B11269057
theorem B2278991 : Blo 798342 2278991 := bstep (se 1 (by rfl) ⟨1709243, by rfl⟩ : syracuseStep 2278991 = 3418487) B3418487
theorem B1197833 : Blo 798342 1197833 := bstep (se 2 (by rfl) ⟨449187, by rfl⟩ : syracuseStep 1197833 = 898375) B898375
theorem B2705291 : Blo 798342 2705291 := bstep (se 1 (by rfl) ⟨2028968, by rfl⟩ : syracuseStep 2705291 = 4057937) B4057937
theorem B1199039 : Blo 798342 1199039 := bstep (se 1 (by rfl) ⟨899279, by rfl⟩ : syracuseStep 1199039 = 1798559) B1798559
theorem B5131295 : Blo 798342 5131295 := bstep (se 1 (by rfl) ⟨3848471, by rfl⟩ : syracuseStep 5131295 = 7696943) B7696943
theorem B17288441 : Blo 798342 17288441 := bstep (se 2 (by rfl) ⟨6483165, by rfl⟩ : syracuseStep 17288441 = 12966331) B12966331
theorem B8671211 : Blo 798342 8671211 := bstep (se 1 (by rfl) ⟨6503408, by rfl⟩ : syracuseStep 8671211 = 13006817) B13006817
theorem B2707559 : Blo 798342 2707559 := bstep (se 1 (by rfl) ⟨2030669, by rfl⟩ : syracuseStep 2707559 = 4061339) B4061339
theorem B6082775 : Blo 798342 6082775 := bstep (se 1 (by rfl) ⟨4562081, by rfl⟩ : syracuseStep 6082775 = 9124163) B9124163
theorem B2707883 : Blo 798342 2707883 := bstep (se 1 (by rfl) ⟨2030912, by rfl⟩ : syracuseStep 2707883 = 4061825) B4061825
theorem B2282089 : Blo 798342 2282089 := bstep (se 2 (by rfl) ⟨855783, by rfl⟩ : syracuseStep 2282089 = 1711567) B1711567
theorem B2282249 : Blo 798342 2282249 := bstep (se 2 (by rfl) ⟨855843, by rfl⟩ : syracuseStep 2282249 = 1711687) B1711687
theorem B32789495 : Blo 798342 32789495 := bstep (se 1 (by rfl) ⟨24592121, by rfl⟩ : syracuseStep 32789495 = 49184243) B49184243
theorem B2282489 : Blo 798342 2282489 := bstep (se 2 (by rfl) ⟨855933, by rfl⟩ : syracuseStep 2282489 = 1711867) B1711867
theorem B5854303 : Blo 798342 5854303 := bstep (se 1 (by rfl) ⟨4390727, by rfl⟩ : syracuseStep 5854303 = 8781455) B8781455
theorem B3855545 : Blo 798342 3855545 := bstep (se 2 (by rfl) ⟨1445829, by rfl⟩ : syracuseStep 3855545 = 2891659) B2891659
theorem B109368589 : Blo 798342 109368589 := bstep (se 3 (by rfl) ⟨20506610, by rfl⟩ : syracuseStep 109368589 = 41013221) B41013221
theorem B1201577 : Blo 798342 1201577 := bstep (se 2 (by rfl) ⟨450591, by rfl⟩ : syracuseStep 1201577 = 901183) B901183
theorem B1201631 : Blo 798342 1201631 := bstep (se 1 (by rfl) ⟨901223, by rfl⟩ : syracuseStep 1201631 = 1802447) B1802447
theorem B7296743 : Blo 798342 7296743 := bstep (se 1 (by rfl) ⟨5472557, by rfl⟩ : syracuseStep 7296743 = 10945115) B10945115
theorem B2283547 : Blo 798342 2283547 := bstep (se 1 (by rfl) ⟨1712660, by rfl⟩ : syracuseStep 2283547 = 3425321) B3425321
theorem B1202735 : Blo 798342 1202735 := bstep (se 1 (by rfl) ⟨902051, by rfl⟩ : syracuseStep 1202735 = 1804103) B1804103
theorem B1203143 : Blo 798342 1203143 := bstep (se 1 (by rfl) ⟨902357, by rfl⟩ : syracuseStep 1203143 = 1804715) B1804715
theorem B1203167 : Blo 798342 1203167 := bstep (se 1 (by rfl) ⟨902375, by rfl⟩ : syracuseStep 1203167 = 1804751) B1804751
theorem B1924283 : Blo 798342 1924283 := bstep (se 1 (by rfl) ⟨1443212, by rfl⟩ : syracuseStep 1924283 = 2886425) B2886425
theorem B1826111 : Blo 798342 1826111 := bstep (se 1 (by rfl) ⟨1369583, by rfl⟩ : syracuseStep 1826111 = 2739167) B2739167
theorem B4054697 : Blo 798342 4054697 := bstep (se 2 (by rfl) ⟨1520511, by rfl⟩ : syracuseStep 4054697 = 3041023) B3041023
theorem B2023663 : Blo 798342 2023663 := bstep (se 1 (by rfl) ⟨1517747, by rfl⟩ : syracuseStep 2023663 = 3035495) B3035495
theorem B2023967 : Blo 798342 2023967 := bstep (se 1 (by rfl) ⟨1517975, by rfl⟩ : syracuseStep 2023967 = 3035951) B3035951
theorem B8643145 : Blo 798342 8643145 := bstep (se 2 (by rfl) ⟨3241179, by rfl⟩ : syracuseStep 8643145 = 6482359) B6482359
theorem B51897509 : Blo 798342 51897509 := bstep (se 4 (by rfl) ⟨4865391, by rfl⟩ : syracuseStep 51897509 = 9730783) B9730783
theorem B4056479 : Blo 798342 4056479 := bstep (se 1 (by rfl) ⟨3042359, by rfl⟩ : syracuseStep 4056479 = 6084719) B6084719
theorem B6842029 : Blo 798342 6842029 := bstep (se 3 (by rfl) ⟨1282880, by rfl⟩ : syracuseStep 6842029 = 2565761) B2565761
theorem B4548413 : Blo 798342 4548413 := bstep (se 3 (by rfl) ⟨852827, by rfl⟩ : syracuseStep 4548413 = 1705655) B1705655
theorem B4057127 : Blo 798342 4057127 := bstep (se 1 (by rfl) ⟨3042845, by rfl⟩ : syracuseStep 4057127 = 6085691) B6085691
theorem B4057451 : Blo 798342 4057451 := bstep (se 1 (by rfl) ⟨3043088, by rfl⟩ : syracuseStep 4057451 = 6086177) B6086177
theorem B2878409 : Blo 798342 2878409 := bstep (se 2 (by rfl) ⟨1079403, by rfl⟩ : syracuseStep 2878409 = 2158807) B2158807
theorem B1010971 : Blo 798342 1010971 := bstep (se 1 (by rfl) ⟨758228, by rfl⟩ : syracuseStep 1010971 = 1516457) B1516457
theorem B4058423 : Blo 798342 4058423 := bstep (se 1 (by rfl) ⟨3043817, by rfl⟩ : syracuseStep 4058423 = 6087635) B6087635
theorem B4059071 : Blo 798342 4059071 := bstep (se 1 (by rfl) ⟨3044303, by rfl⟩ : syracuseStep 4059071 = 6088607) B6088607
theorem B2027551 : Blo 798342 2027551 := bstep (se 1 (by rfl) ⟨1520663, by rfl⟩ : syracuseStep 2027551 = 3041327) B3041327
theorem B1798631 : Blo 798342 1798631 := bstep (se 1 (by rfl) ⟨1348973, by rfl⟩ : syracuseStep 1798631 = 2697947) B2697947
theorem B2159111 : Blo 798342 2159111 := bstep (se 1 (by rfl) ⟨1619333, by rfl⟩ : syracuseStep 2159111 = 3238667) B3238667
theorem B2028199 : Blo 798342 2028199 := bstep (se 1 (by rfl) ⟨1521149, by rfl⟩ : syracuseStep 2028199 = 3042299) B3042299
theorem B1012763 : Blo 798342 1012763 := bstep (se 1 (by rfl) ⟨759572, by rfl⟩ : syracuseStep 1012763 = 1519145) B1519145
theorem B2028635 : Blo 798342 2028635 := bstep (se 1 (by rfl) ⟨1521476, by rfl⟩ : syracuseStep 2028635 = 3042953) B3042953
theorem B4551785 : Blo 798342 4551785 := bstep (se 2 (by rfl) ⟨1706919, by rfl⟩ : syracuseStep 4551785 = 3413839) B3413839
theorem B1799279 : Blo 798342 1799279 := bstep (se 1 (by rfl) ⟨1349459, by rfl⟩ : syracuseStep 1799279 = 2698919) B2698919
theorem B1799657 : Blo 798342 1799657 := bstep (se 2 (by rfl) ⟨674871, by rfl⟩ : syracuseStep 1799657 = 1349743) B1349743
theorem B1800431 : Blo 798342 1800431 := bstep (se 1 (by rfl) ⟨1350323, by rfl⟩ : syracuseStep 1800431 = 2700647) B2700647
theorem B1800503 : Blo 798342 1800503 := bstep (se 1 (by rfl) ⟨1350377, by rfl⟩ : syracuseStep 1800503 = 2700755) B2700755
theorem B4324103 : Blo 798342 4324103 := bstep (se 1 (by rfl) ⟨3243077, by rfl⟩ : syracuseStep 4324103 = 6486155) B6486155
theorem B5766335 : Blo 798342 5766335 := bstep (se 1 (by rfl) ⟨4324751, by rfl⟩ : syracuseStep 5766335 = 8649503) B8649503
theorem B1802231 : Blo 798342 1802231 := bstep (se 1 (by rfl) ⟨1351673, by rfl⟩ : syracuseStep 1802231 = 2703347) B2703347
theorem B1802591 : Blo 798342 1802591 := bstep (se 1 (by rfl) ⟨1351943, by rfl⟩ : syracuseStep 1802591 = 2703887) B2703887
theorem B1802735 : Blo 798342 1802735 := bstep (se 1 (by rfl) ⟨1352051, by rfl⟩ : syracuseStep 1802735 = 2704103) B2704103
theorem B124781381 : Blo 798342 124781381 := bstep (se 4 (by rfl) ⟨11698254, by rfl⟩ : syracuseStep 124781381 = 23396509) B23396509
theorem B4555885 : Blo 798342 4555885 := bstep (se 3 (by rfl) ⟨854228, by rfl⟩ : syracuseStep 4555885 = 1708457) B1708457
theorem B1803527 : Blo 798342 1803527 := bstep (se 1 (by rfl) ⟨1352645, by rfl⟩ : syracuseStep 1803527 = 2705291) B2705291
theorem B2885503 : Blo 798342 2885503 := bstep (se 1 (by rfl) ⟨2164127, by rfl⟩ : syracuseStep 2885503 = 4328255) B4328255
theorem B2557919 : Blo 798342 2557919 := bstep (se 1 (by rfl) ⟨1918439, by rfl⟩ : syracuseStep 2557919 = 3836879) B3836879
theorem B1804841 : Blo 798342 1804841 := bstep (se 2 (by rfl) ⟨676815, by rfl⟩ : syracuseStep 1804841 = 1353631) B1353631
theorem B1805039 : Blo 798342 1805039 := bstep (se 1 (by rfl) ⟨1353779, by rfl⟩ : syracuseStep 1805039 = 2707559) B2707559
theorem B3246905 : Blo 798342 3246905 := bstep (se 2 (by rfl) ⟨1217589, by rfl⟩ : syracuseStep 3246905 = 2435179) B2435179
theorem B1444799 : Blo 798342 1444799 := bstep (se 1 (by rfl) ⟨1083599, by rfl⟩ : syracuseStep 1444799 = 2167199) B2167199
theorem B1805255 : Blo 798342 1805255 := bstep (se 1 (by rfl) ⟨1353941, by rfl⟩ : syracuseStep 1805255 = 2707883) B2707883
theorem B1347961 : Blo 798342 1347961 := bstep (se 2 (by rfl) ⟨505485, by rfl⟩ : syracuseStep 1347961 = 1010971) B1010971
theorem B1349311 : Blo 798342 1349311 := bstep (se 1 (by rfl) ⟨1011983, by rfl⟩ : syracuseStep 1349311 = 2023967) B2023967
theorem B9115415 : Blo 798342 9115415 := bstep (se 1 (by rfl) ⟨6836561, by rfl⟩ : syracuseStep 9115415 = 13673123) B13673123
theorem B11540389 : Blo 798342 11540389 := bstep (se 4 (by rfl) ⟨1081911, by rfl⟩ : syracuseStep 11540389 = 2163823) B2163823
theorem B5118299 : Blo 798342 5118299 := bstep (se 1 (by rfl) ⟨3838724, by rfl⟩ : syracuseStep 5118299 = 7677449) B7677449
theorem B7805737 : Blo 798342 7805737 := bstep (se 2 (by rfl) ⟨2927151, by rfl⟩ : syracuseStep 7805737 = 5854303) B5854303
theorem B7707433 : Blo 798342 7707433 := bstep (se 2 (by rfl) ⟨2890287, by rfl⟩ : syracuseStep 7707433 = 5780575) B5780575
theorem B145824785 : Blo 798342 145824785 := bstep (se 2 (by rfl) ⟨54684294, by rfl⟩ : syracuseStep 145824785 = 109368589) B109368589
theorem B5119199 : Blo 798342 5119199 := bstep (se 1 (by rfl) ⟨3839399, by rfl⟩ : syracuseStep 5119199 = 7678799) B7678799
theorem B2694491 : Blo 798342 2694491 := bstep (se 1 (by rfl) ⟨2020868, by rfl⟩ : syracuseStep 2694491 = 4041737) B4041737
theorem B5119631 : Blo 798342 5119631 := bstep (se 1 (by rfl) ⟨3839723, by rfl⟩ : syracuseStep 5119631 = 7679447) B7679447
theorem B27763145 : Blo 798342 27763145 := bstep (se 2 (by rfl) ⟨10411179, by rfl⟩ : syracuseStep 27763145 = 20822359) B20822359
theorem B1352423 : Blo 798342 1352423 := bstep (se 1 (by rfl) ⟨1014317, by rfl⟩ : syracuseStep 1352423 = 2028635) B2028635
theorem B10233215 : Blo 798342 10233215 := bstep (se 1 (by rfl) ⟨7674911, by rfl⟩ : syracuseStep 10233215 = 15349823) B15349823
theorem B2697083 : Blo 798342 2697083 := bstep (se 1 (by rfl) ⟨2022812, by rfl⟩ : syracuseStep 2697083 = 4045625) B4045625
theorem B3844223 : Blo 798342 3844223 := bstep (se 1 (by rfl) ⟨2883167, by rfl⟩ : syracuseStep 3844223 = 5766335) B5766335
theorem B23668933 : Blo 798342 23668933 := bstep (se 4 (by rfl) ⟨2218962, by rfl⟩ : syracuseStep 23668933 = 4437925) B4437925
theorem B4860431 : Blo 798342 4860431 := bstep (se 1 (by rfl) ⟨3645323, by rfl⟩ : syracuseStep 4860431 = 7290647) B7290647
theorem B8661613 : Blo 798342 8661613 := bstep (se 3 (by rfl) ⟨1624052, by rfl⟩ : syracuseStep 8661613 = 3248105) B3248105
theorem B2698217 : Blo 798342 2698217 := bstep (se 2 (by rfl) ⟨1011831, by rfl⟩ : syracuseStep 2698217 = 2023663) B2023663
theorem B2731421 : Blo 798342 2731421 := bstep (se 3 (by rfl) ⟨512141, by rfl⟩ : syracuseStep 2731421 = 1024283) B1024283
theorem B9121247 : Blo 798342 9121247 := bstep (se 1 (by rfl) ⟨6840935, by rfl⟩ : syracuseStep 9121247 = 13681871) B13681871
theorem B1519327 : Blo 798342 1519327 := bstep (se 1 (by rfl) ⟨1139495, by rfl⟩ : syracuseStep 1519327 = 2278991) B2278991
theorem B798555 : Blo 798342 798555 := bstep (se 1 (by rfl) ⟨598916, by rfl⟩ : syracuseStep 798555 = 1197833) B1197833
theorem B2601175 : Blo 798342 2601175 := bstep (se 1 (by rfl) ⟨1950881, by rfl⟩ : syracuseStep 2601175 = 3901763) B3901763
theorem B3846683 : Blo 798342 3846683 := bstep (se 1 (by rfl) ⟨2885012, by rfl⟩ : syracuseStep 3846683 = 5770025) B5770025
theorem B799359 : Blo 798342 799359 := bstep (se 1 (by rfl) ⟨599519, by rfl⟩ : syracuseStep 799359 = 1199039) B1199039
theorem B3420863 : Blo 798342 3420863 := bstep (se 1 (by rfl) ⟨2565647, by rfl⟩ : syracuseStep 3420863 = 5131295) B5131295
theorem B5124961 : Blo 798342 5124961 := bstep (se 2 (by rfl) ⟨1921860, by rfl⟩ : syracuseStep 5124961 = 3843721) B3843721
theorem B9122705 : Blo 798342 9122705 := bstep (se 2 (by rfl) ⟨3421014, by rfl⟩ : syracuseStep 9122705 = 6842029) B6842029
theorem B87438653 : Blo 798342 87438653 := bstep (se 3 (by rfl) ⟨16394747, by rfl⟩ : syracuseStep 87438653 = 32789495) B32789495
theorem B5780807 : Blo 798342 5780807 := bstep (se 1 (by rfl) ⟨4335605, by rfl⟩ : syracuseStep 5780807 = 8671211) B8671211
theorem B2700701 : Blo 798342 2700701 := bstep (se 3 (by rfl) ⟨506381, by rfl⟩ : syracuseStep 2700701 = 1012763) B1012763
theorem B1521499 : Blo 798342 1521499 := bstep (se 1 (by rfl) ⟨1141124, by rfl⟩ : syracuseStep 1521499 = 2282249) B2282249
theorem B1521659 : Blo 798342 1521659 := bstep (se 1 (by rfl) ⟨1141244, by rfl⟩ : syracuseStep 1521659 = 2282489) B2282489
theorem B2570363 : Blo 798342 2570363 := bstep (se 1 (by rfl) ⟨1927772, by rfl⟩ : syracuseStep 2570363 = 3855545) B3855545
theorem B801051 : Blo 798342 801051 := bstep (se 1 (by rfl) ⟨600788, by rfl⟩ : syracuseStep 801051 = 1201577) B1201577
theorem B801087 : Blo 798342 801087 := bstep (se 1 (by rfl) ⟨600815, by rfl⟩ : syracuseStep 801087 = 1201631) B1201631
theorem B801823 : Blo 798342 801823 := bstep (se 1 (by rfl) ⟨601367, by rfl⟩ : syracuseStep 801823 = 1202735) B1202735
theorem B802095 : Blo 798342 802095 := bstep (se 1 (by rfl) ⟨601571, by rfl⟩ : syracuseStep 802095 = 1203143) B1203143
theorem B802111 : Blo 798342 802111 := bstep (se 1 (by rfl) ⟨601583, by rfl⟩ : syracuseStep 802111 = 1203167) B1203167
theorem B2703131 : Blo 798342 2703131 := bstep (se 1 (by rfl) ⟨2027348, by rfl⟩ : syracuseStep 2703131 = 4054697) B4054697
theorem B2703401 : Blo 798342 2703401 := bstep (se 2 (by rfl) ⟨1013775, by rfl⟩ : syracuseStep 2703401 = 2027551) B2027551
theorem B20562173 : Blo 798342 20562173 := bstep (se 3 (by rfl) ⟨3855407, by rfl⟩ : syracuseStep 20562173 = 7710815) B7710815
theorem B2704265 : Blo 798342 2704265 := bstep (se 2 (by rfl) ⟨1014099, by rfl⟩ : syracuseStep 2704265 = 2028199) B2028199
theorem B902047 : Blo 798342 902047 := bstep (se 1 (by rfl) ⟨676535, by rfl⟩ : syracuseStep 902047 = 1353071) B1353071
theorem B2704319 : Blo 798342 2704319 := bstep (se 1 (by rfl) ⟨2028239, by rfl⟩ : syracuseStep 2704319 = 4056479) B4056479
theorem B4048055 : Blo 798342 4048055 := bstep (se 1 (by rfl) ⟨3036041, by rfl⟩ : syracuseStep 4048055 = 6072083) B6072083
theorem B3032275 : Blo 798342 3032275 := bstep (se 1 (by rfl) ⟨2274206, by rfl⟩ : syracuseStep 3032275 = 4548413) B4548413
theorem B2704751 : Blo 798342 2704751 := bstep (se 1 (by rfl) ⟨2028563, by rfl⟩ : syracuseStep 2704751 = 4057127) B4057127
theorem B1197545 : Blo 798342 1197545 := bstep (se 2 (by rfl) ⟨449079, by rfl⟩ : syracuseStep 1197545 = 898159) B898159
theorem B2704967 : Blo 798342 2704967 := bstep (se 1 (by rfl) ⟨2028725, by rfl⟩ : syracuseStep 2704967 = 4057451) B4057451
theorem B1918939 : Blo 798342 1918939 := bstep (se 1 (by rfl) ⟨1439204, by rfl⟩ : syracuseStep 1918939 = 2878409) B2878409
theorem B1198121 : Blo 798342 1198121 := bstep (se 2 (by rfl) ⟨449295, by rfl⟩ : syracuseStep 1198121 = 898591) B898591
theorem B2705615 : Blo 798342 2705615 := bstep (se 1 (by rfl) ⟨2029211, by rfl⟩ : syracuseStep 2705615 = 4058423) B4058423
theorem B2706047 : Blo 798342 2706047 := bstep (se 1 (by rfl) ⟨2029535, by rfl⟩ : syracuseStep 2706047 = 4059071) B4059071
theorem B1198985 : Blo 798342 1198985 := bstep (se 2 (by rfl) ⟨449619, by rfl⟩ : syracuseStep 1198985 = 899239) B899239
theorem B1199087 : Blo 798342 1199087 := bstep (se 1 (by rfl) ⟨899315, by rfl⟩ : syracuseStep 1199087 = 1798631) B1798631
theorem B5131421 : Blo 798342 5131421 := bstep (se 3 (by rfl) ⟨962141, by rfl⟩ : syracuseStep 5131421 = 1924283) B1924283
theorem B1199273 : Blo 798342 1199273 := bstep (se 2 (by rfl) ⟨449727, by rfl⟩ : syracuseStep 1199273 = 899455) B899455
theorem B3034523 : Blo 798342 3034523 := bstep (se 1 (by rfl) ⟨2275892, by rfl⟩ : syracuseStep 3034523 = 4551785) B4551785
theorem B1199519 : Blo 798342 1199519 := bstep (se 1 (by rfl) ⟨899639, by rfl⟩ : syracuseStep 1199519 = 1799279) B1799279
theorem B4869629 : Blo 798342 4869629 := bstep (se 3 (by rfl) ⟨913055, by rfl⟩ : syracuseStep 4869629 = 1826111) B1826111
theorem B1199771 : Blo 798342 1199771 := bstep (se 1 (by rfl) ⟨899828, by rfl⟩ : syracuseStep 1199771 = 1799657) B1799657
theorem B1232623 : Blo 798342 1232623 := bstep (se 1 (by rfl) ⟨924467, by rfl⟩ : syracuseStep 1232623 = 1848935) B1848935
theorem B1200287 : Blo 798342 1200287 := bstep (se 1 (by rfl) ⟨900215, by rfl⟩ : syracuseStep 1200287 = 1800431) B1800431
theorem B1200335 : Blo 798342 1200335 := bstep (se 1 (by rfl) ⟨900251, by rfl⟩ : syracuseStep 1200335 = 1800503) B1800503
theorem B3658459 : Blo 798342 3658459 := bstep (se 1 (by rfl) ⟨2743844, by rfl⟩ : syracuseStep 3658459 = 5487689) B5487689
theorem B2282431 : Blo 798342 2282431 := bstep (se 1 (by rfl) ⟨1711823, by rfl⟩ : syracuseStep 2282431 = 3423647) B3423647
theorem B1201487 : Blo 798342 1201487 := bstep (se 1 (by rfl) ⟨901115, by rfl⟩ : syracuseStep 1201487 = 1802231) B1802231
theorem B1201691 : Blo 798342 1201691 := bstep (se 1 (by rfl) ⟨901268, by rfl⟩ : syracuseStep 1201691 = 1802537) B1802537
theorem B1202075 : Blo 798342 1202075 := bstep (se 1 (by rfl) ⟨901556, by rfl⟩ : syracuseStep 1202075 = 1803113) B1803113
theorem B11524193 : Blo 798342 11524193 := bstep (se 2 (by rfl) ⟨4321572, by rfl⟩ : syracuseStep 11524193 = 8643145) B8643145
theorem B10016939 : Blo 798342 10016939 := bstep (se 1 (by rfl) ⟨7512704, by rfl⟩ : syracuseStep 10016939 = 15025409) B15025409
theorem B1202843 : Blo 798342 1202843 := bstep (se 1 (by rfl) ⟨902132, by rfl⟩ : syracuseStep 1202843 = 1804265) B1804265
theorem B13000007 : Blo 798342 13000007 := bstep (se 1 (by rfl) ⟨9750005, by rfl⟩ : syracuseStep 13000007 = 19500011) B19500011
theorem B11525627 : Blo 798342 11525627 := bstep (se 1 (by rfl) ⟨8644220, by rfl⟩ : syracuseStep 11525627 = 17288441) B17288441
theorem B2023177 : Blo 798342 2023177 := bstep (se 2 (by rfl) ⟨758691, by rfl⟩ : syracuseStep 2023177 = 1517383) B1517383
theorem B3891007 : Blo 798342 3891007 := bstep (se 1 (by rfl) ⟨2918255, by rfl⟩ : syracuseStep 3891007 = 5836511) B5836511
theorem B4055183 : Blo 798342 4055183 := bstep (se 1 (by rfl) ⟨3041387, by rfl⟩ : syracuseStep 4055183 = 6082775) B6082775
theorem B3039839 : Blo 798342 3039839 := bstep (se 1 (by rfl) ⟨2279879, by rfl⟩ : syracuseStep 3039839 = 4559759) B4559759
theorem B199844657 : Blo 798342 199844657 := bstep (se 2 (by rfl) ⟨74941746, by rfl⟩ : syracuseStep 199844657 = 149883493) B149883493
theorem B25912943 : Blo 798342 25912943 := bstep (se 1 (by rfl) ⟨19434707, by rfl⟩ : syracuseStep 25912943 = 38869415) B38869415
theorem B19457981 : Blo 798342 19457981 := bstep (se 3 (by rfl) ⟨3648371, by rfl⟩ : syracuseStep 19457981 = 7296743) B7296743
theorem B1797497 : Blo 798342 1797497 := bstep (se 2 (by rfl) ⟨674061, by rfl⟩ : syracuseStep 1797497 = 1348123) B1348123
theorem B34598339 : Blo 798342 34598339 := bstep (se 1 (by rfl) ⟨25948754, by rfl⟩ : syracuseStep 34598339 = 51897509) B51897509
theorem B3042785 : Blo 798342 3042785 := bstep (se 2 (by rfl) ⟨1141044, by rfl⟩ : syracuseStep 3042785 = 2282089) B2282089
theorem B1798199 : Blo 798342 1798199 := bstep (se 1 (by rfl) ⟨1348649, by rfl⟩ : syracuseStep 1798199 = 2697299) B2697299
theorem B4616939 : Blo 798342 4616939 := bstep (se 1 (by rfl) ⟨3462704, by rfl⟩ : syracuseStep 4616939 = 6925409) B6925409
theorem B3044729 : Blo 798342 3044729 := bstep (se 2 (by rfl) ⟨1141773, by rfl⟩ : syracuseStep 3044729 = 2283547) B2283547
theorem B1439407 : Blo 798342 1439407 := bstep (se 1 (by rfl) ⟨1079555, by rfl⟩ : syracuseStep 1439407 = 2159111) B2159111
theorem B10975337 : Blo 798342 10975337 := bstep (se 2 (by rfl) ⟨4115751, by rfl⟩ : syracuseStep 10975337 = 8231503) B8231503
theorem B4552969 : Blo 798342 4552969 := bstep (se 2 (by rfl) ⟨1707363, by rfl⟩ : syracuseStep 4552969 = 3414727) B3414727
theorem B2029961 : Blo 798342 2029961 := bstep (se 2 (by rfl) ⟨761235, by rfl⟩ : syracuseStep 2029961 = 1522471) B1522471
theorem B2882735 : Blo 798342 2882735 := bstep (se 1 (by rfl) ⟨2162051, by rfl⟩ : syracuseStep 2882735 = 4324103) B4324103
theorem B1802267 : Blo 798342 1802267 := bstep (se 1 (by rfl) ⟨1351700, by rfl⟩ : syracuseStep 1802267 = 2703401) B2703401
theorem B1802843 : Blo 798342 1802843 := bstep (se 1 (by rfl) ⟨1352132, by rfl⟩ : syracuseStep 1802843 = 2704265) B2704265
theorem B1802879 : Blo 798342 1802879 := bstep (se 1 (by rfl) ⟨1352159, by rfl⟩ : syracuseStep 1802879 = 2704319) B2704319
theorem B1803167 : Blo 798342 1803167 := bstep (se 1 (by rfl) ⟨1352375, by rfl⟩ : syracuseStep 1803167 = 2704751) B2704751
theorem B1803311 : Blo 798342 1803311 := bstep (se 1 (by rfl) ⟨1352483, by rfl⟩ : syracuseStep 1803311 = 2704967) B2704967
theorem B1803743 : Blo 798342 1803743 := bstep (se 1 (by rfl) ⟨1352807, by rfl⟩ : syracuseStep 1803743 = 2705615) B2705615
theorem B1804031 : Blo 798342 1804031 := bstep (se 1 (by rfl) ⟨1353023, by rfl⟩ : syracuseStep 1804031 = 2706047) B2706047
theorem B2164603 : Blo 798342 2164603 := bstep (se 1 (by rfl) ⟨1623452, by rfl⟩ : syracuseStep 2164603 = 3246905) B3246905
theorem B3246419 : Blo 798342 3246419 := bstep (se 1 (by rfl) ⟨2434814, by rfl⟩ : syracuseStep 3246419 = 4869629) B4869629
theorem B2558585 : Blo 798342 2558585 := bstep (se 2 (by rfl) ⟨959469, by rfl⟩ : syracuseStep 2558585 = 1918939) B1918939
theorem B31558577 : Blo 798342 31558577 := bstep (se 2 (by rfl) ⟨11834466, by rfl⟩ : syracuseStep 31558577 = 23668933) B23668933
theorem B3412199 : Blo 798342 3412199 := bstep (se 1 (by rfl) ⟨2559149, by rfl⟩ : syracuseStep 3412199 = 5118299) B5118299
theorem B3412799 : Blo 798342 3412799 := bstep (se 1 (by rfl) ⟨2559599, by rfl⟩ : syracuseStep 3412799 = 5119199) B5119199
theorem B1643497 : Blo 798342 1643497 := bstep (se 2 (by rfl) ⟨616311, by rfl⟩ : syracuseStep 1643497 = 1232623) B1232623
theorem B3413087 : Blo 798342 3413087 := bstep (se 1 (by rfl) ⟨2559815, by rfl⟩ : syracuseStep 3413087 = 5119631) B5119631
theorem B6821117 : Blo 798342 6821117 := bstep (se 3 (by rfl) ⟨1278959, by rfl⟩ : syracuseStep 6821117 = 2557919) B2557919
theorem B6822143 : Blo 798342 6822143 := bstep (se 1 (by rfl) ⟨5116607, by rfl⟩ : syracuseStep 6822143 = 10233215) B10233215
theorem B17275295 : Blo 798342 17275295 := bstep (se 1 (by rfl) ⟨12956471, by rfl⟩ : syracuseStep 17275295 = 25912943) B25912943
theorem B2562815 : Blo 798342 2562815 := bstep (se 1 (by rfl) ⟨1922111, by rfl⟩ : syracuseStep 2562815 = 3844223) B3844223
theorem B6070625 : Blo 798342 6070625 := bstep (se 2 (by rfl) ⟨2276484, by rfl⟩ : syracuseStep 6070625 = 4552969) B4552969
theorem B2564455 : Blo 798342 2564455 := bstep (se 1 (by rfl) ⟨1923341, by rfl⟩ : syracuseStep 2564455 = 3846683) B3846683
theorem B7283789 : Blo 798342 7283789 := bstep (se 3 (by rfl) ⟨1365710, by rfl⟩ : syracuseStep 7283789 = 2731421) B2731421
theorem B7316891 : Blo 798342 7316891 := bstep (se 1 (by rfl) ⟨5487668, by rfl⟩ : syracuseStep 7316891 = 10975337) B10975337
theorem B1713575 : Blo 798342 1713575 := bstep (se 1 (by rfl) ⟨1285181, by rfl⟩ : syracuseStep 1713575 = 2570363) B2570363
theorem B1353307 : Blo 798342 1353307 := bstep (se 1 (by rfl) ⟨1014980, by rfl⟩ : syracuseStep 1353307 = 2029961) B2029961
theorem B2697569 : Blo 798342 2697569 := bstep (se 2 (by rfl) ⟨1011588, by rfl⟩ : syracuseStep 2697569 = 2023177) B2023177
theorem B5188009 : Blo 798342 5188009 := bstep (se 2 (by rfl) ⟨1945503, by rfl⟩ : syracuseStep 5188009 = 3891007) B3891007
theorem B13708115 : Blo 798342 13708115 := bstep (se 1 (by rfl) ⟨10281086, by rfl⟩ : syracuseStep 13708115 = 20562173) B20562173
theorem B2698703 : Blo 798342 2698703 := bstep (se 1 (by rfl) ⟨2024027, by rfl⟩ : syracuseStep 2698703 = 4048055) B4048055
theorem B798363 : Blo 798342 798363 := bstep (se 1 (by rfl) ⟨598772, by rfl⟩ : syracuseStep 798363 = 1197545) B1197545
theorem B798747 : Blo 798342 798747 := bstep (se 1 (by rfl) ⟨599060, by rfl⟩ : syracuseStep 798747 = 1198121) B1198121
theorem B6074513 : Blo 798342 6074513 := bstep (se 2 (by rfl) ⟨2277942, by rfl⟩ : syracuseStep 6074513 = 4555885) B4555885
theorem B4043033 : Blo 798342 4043033 := bstep (se 2 (by rfl) ⟨1516137, by rfl⟩ : syracuseStep 4043033 = 3032275) B3032275
theorem B799323 : Blo 798342 799323 := bstep (se 1 (by rfl) ⟨599492, by rfl⟩ : syracuseStep 799323 = 1198985) B1198985
theorem B963199 : Blo 798342 963199 := bstep (se 1 (by rfl) ⟨722399, by rfl⟩ : syracuseStep 963199 = 1444799) B1444799
theorem B799391 : Blo 798342 799391 := bstep (se 1 (by rfl) ⟨599543, by rfl⟩ : syracuseStep 799391 = 1199087) B1199087
theorem B3420947 : Blo 798342 3420947 := bstep (se 1 (by rfl) ⟨2565710, by rfl⟩ : syracuseStep 3420947 = 5131421) B5131421
theorem B799515 : Blo 798342 799515 := bstep (se 1 (by rfl) ⟨599636, by rfl⟩ : syracuseStep 799515 = 1199273) B1199273
theorem B799679 : Blo 798342 799679 := bstep (se 1 (by rfl) ⟨599759, by rfl⟩ : syracuseStep 799679 = 1199519) B1199519
theorem B799847 : Blo 798342 799847 := bstep (se 1 (by rfl) ⟨599885, by rfl⟩ : syracuseStep 799847 = 1199771) B1199771
theorem B3847337 : Blo 798342 3847337 := bstep (se 2 (by rfl) ⟨1442751, by rfl⟩ : syracuseStep 3847337 = 2885503) B2885503
theorem B800191 : Blo 798342 800191 := bstep (se 1 (by rfl) ⟨600143, by rfl⟩ : syracuseStep 800191 = 1200287) B1200287
theorem B800223 : Blo 798342 800223 := bstep (se 1 (by rfl) ⟨600167, by rfl⟩ : syracuseStep 800223 = 1200335) B1200335
theorem B11548817 : Blo 798342 11548817 := bstep (se 2 (by rfl) ⟨4330806, by rfl⟩ : syracuseStep 11548817 = 8661613) B8661613
theorem B800991 : Blo 798342 800991 := bstep (se 1 (by rfl) ⟨600743, by rfl⟩ : syracuseStep 800991 = 1201487) B1201487
theorem B801127 : Blo 798342 801127 := bstep (se 1 (by rfl) ⟨600845, by rfl⟩ : syracuseStep 801127 = 1201691) B1201691
theorem B6076943 : Blo 798342 6076943 := bstep (se 1 (by rfl) ⟨4557707, by rfl⟩ : syracuseStep 6076943 = 9115415) B9115415
theorem B801383 : Blo 798342 801383 := bstep (se 1 (by rfl) ⟨601037, by rfl⟩ : syracuseStep 801383 = 1202075) B1202075
theorem B7682795 : Blo 798342 7682795 := bstep (se 1 (by rfl) ⟨5762096, by rfl⟩ : syracuseStep 7682795 = 11524193) B11524193
theorem B801895 : Blo 798342 801895 := bstep (se 1 (by rfl) ⟨601421, by rfl⟩ : syracuseStep 801895 = 1202843) B1202843
theorem B8666671 : Blo 798342 8666671 := bstep (se 1 (by rfl) ⟨6500003, by rfl⟩ : syracuseStep 8666671 = 13000007) B13000007
theorem B7683751 : Blo 798342 7683751 := bstep (se 1 (by rfl) ⟨5762813, by rfl⟩ : syracuseStep 7683751 = 11525627) B11525627
theorem B2703455 : Blo 798342 2703455 := bstep (se 1 (by rfl) ⟨2027591, by rfl⟩ : syracuseStep 2703455 = 4055183) B4055183
theorem B901615 : Blo 798342 901615 := bstep (se 1 (by rfl) ⟨676211, by rfl⟩ : syracuseStep 901615 = 1352423) B1352423
theorem B6833281 : Blo 798342 6833281 := bstep (se 2 (by rfl) ⟨2562480, by rfl⟩ : syracuseStep 6833281 = 5124961) B5124961
theorem B1919209 : Blo 798342 1919209 := bstep (se 2 (by rfl) ⟨719703, by rfl⟩ : syracuseStep 1919209 = 1439407) B1439407
theorem B1198331 : Blo 798342 1198331 := bstep (se 1 (by rfl) ⟨898748, by rfl⟩ : syracuseStep 1198331 = 1797497) B1797497
theorem B6080831 : Blo 798342 6080831 := bstep (se 1 (by rfl) ⟨4560623, by rfl⟩ : syracuseStep 6080831 = 9121247) B9121247
theorem B15387185 : Blo 798342 15387185 := bstep (se 2 (by rfl) ⟨5770194, by rfl⟩ : syracuseStep 15387185 = 11540389) B11540389
theorem B1198799 : Blo 798342 1198799 := bstep (se 1 (by rfl) ⟨899099, by rfl⟩ : syracuseStep 1198799 = 1798199) B1798199
theorem B2280575 : Blo 798342 2280575 := bstep (se 1 (by rfl) ⟨1710431, by rfl⟩ : syracuseStep 2280575 = 3420863) B3420863
theorem B6081803 : Blo 798342 6081803 := bstep (se 1 (by rfl) ⟨4561352, by rfl⟩ : syracuseStep 6081803 = 9122705) B9122705
theorem B3853871 : Blo 798342 3853871 := bstep (se 1 (by rfl) ⟨2890403, by rfl⟩ : syracuseStep 3853871 = 5780807) B5780807
theorem B10407649 : Blo 798342 10407649 := bstep (se 2 (by rfl) ⟨3902868, by rfl⟩ : syracuseStep 10407649 = 7805737) B7805737
theorem B10276577 : Blo 798342 10276577 := bstep (se 2 (by rfl) ⟨3853716, by rfl⟩ : syracuseStep 10276577 = 7707433) B7707433
theorem B1921823 : Blo 798342 1921823 := bstep (se 1 (by rfl) ⟨1441367, by rfl⟩ : syracuseStep 1921823 = 2882735) B2882735
theorem B1201727 : Blo 798342 1201727 := bstep (se 1 (by rfl) ⟨901295, by rfl⟩ : syracuseStep 1201727 = 1802591) B1802591
theorem B1201823 : Blo 798342 1201823 := bstep (se 1 (by rfl) ⟨901367, by rfl⟩ : syracuseStep 1201823 = 1802735) B1802735
theorem B83187587 : Blo 798342 83187587 := bstep (se 1 (by rfl) ⟨62390690, by rfl⟩ : syracuseStep 83187587 = 124781381) B124781381
theorem B1202351 : Blo 798342 1202351 := bstep (se 1 (by rfl) ⟨901763, by rfl⟩ : syracuseStep 1202351 = 1803527) B1803527
theorem B1202729 : Blo 798342 1202729 := bstep (se 2 (by rfl) ⟨451023, by rfl⟩ : syracuseStep 1202729 = 902047) B902047
theorem B1203227 : Blo 798342 1203227 := bstep (se 1 (by rfl) ⟨902420, by rfl⟩ : syracuseStep 1203227 = 1804841) B1804841
theorem B1203359 : Blo 798342 1203359 := bstep (se 1 (by rfl) ⟨902519, by rfl⟩ : syracuseStep 1203359 = 1805039) B1805039
theorem B1203503 : Blo 798342 1203503 := bstep (se 1 (by rfl) ⟨902627, by rfl⟩ : syracuseStep 1203503 = 1805255) B1805255
theorem B2023015 : Blo 798342 2023015 := bstep (se 1 (by rfl) ⟨1517261, by rfl⟩ : syracuseStep 2023015 = 3034523) B3034523
theorem B6677959 : Blo 798342 6677959 := bstep (se 1 (by rfl) ⟨5008469, by rfl⟩ : syracuseStep 6677959 = 10016939) B10016939
theorem B97216523 : Blo 798342 97216523 := bstep (se 1 (by rfl) ⟨72912392, by rfl⟩ : syracuseStep 97216523 = 145824785) B145824785
theorem B1796327 : Blo 798342 1796327 := bstep (se 1 (by rfl) ⟨1347245, by rfl⟩ : syracuseStep 1796327 = 2694491) B2694491
theorem B2025769 : Blo 798342 2025769 := bstep (se 2 (by rfl) ⟨759663, by rfl⟩ : syracuseStep 2025769 = 1519327) B1519327
theorem B3468233 : Blo 798342 3468233 := bstep (se 2 (by rfl) ⟨1300587, by rfl⟩ : syracuseStep 3468233 = 2601175) B2601175
theorem B18508763 : Blo 798342 18508763 := bstep (se 1 (by rfl) ⟨13881572, by rfl⟩ : syracuseStep 18508763 = 27763145) B27763145
theorem B2026559 : Blo 798342 2026559 := bstep (se 1 (by rfl) ⟨1519919, by rfl⟩ : syracuseStep 2026559 = 3039839) B3039839
theorem B1797281 : Blo 798342 1797281 := bstep (se 2 (by rfl) ⟨673980, by rfl⟩ : syracuseStep 1797281 = 1347961) B1347961
theorem B133229771 : Blo 798342 133229771 := bstep (se 1 (by rfl) ⟨99922328, by rfl⟩ : syracuseStep 133229771 = 199844657) B199844657
theorem B4877945 : Blo 798342 4877945 := bstep (se 2 (by rfl) ⟨1829229, by rfl⟩ : syracuseStep 4877945 = 3658459) B3658459
theorem B1798055 : Blo 798342 1798055 := bstep (se 1 (by rfl) ⟨1348541, by rfl⟩ : syracuseStep 1798055 = 2697083) B2697083
theorem B3043241 : Blo 798342 3043241 := bstep (se 2 (by rfl) ⟨1141215, by rfl⟩ : syracuseStep 3043241 = 2282431) B2282431
theorem B12971987 : Blo 798342 12971987 := bstep (se 1 (by rfl) ⟨9728990, by rfl⟩ : syracuseStep 12971987 = 19457981) B19457981
theorem B3240287 : Blo 798342 3240287 := bstep (se 1 (by rfl) ⟨2430215, by rfl⟩ : syracuseStep 3240287 = 4860431) B4860431
theorem B1798811 : Blo 798342 1798811 := bstep (se 1 (by rfl) ⟨1349108, by rfl⟩ : syracuseStep 1798811 = 2698217) B2698217
theorem B1799081 : Blo 798342 1799081 := bstep (se 2 (by rfl) ⟨674655, by rfl⟩ : syracuseStep 1799081 = 1349311) B1349311
theorem B23065559 : Blo 798342 23065559 := bstep (se 1 (by rfl) ⟨17299169, by rfl⟩ : syracuseStep 23065559 = 34598339) B34598339
theorem B2028523 : Blo 798342 2028523 := bstep (se 1 (by rfl) ⟨1521392, by rfl⟩ : syracuseStep 2028523 = 3042785) B3042785
theorem B2028665 : Blo 798342 2028665 := bstep (se 2 (by rfl) ⟨760749, by rfl⟩ : syracuseStep 2028665 = 1521499) B1521499
theorem B3077959 : Blo 798342 3077959 := bstep (se 1 (by rfl) ⟨2308469, by rfl⟩ : syracuseStep 3077959 = 4616939) B4616939
theorem B58292435 : Blo 798342 58292435 := bstep (se 1 (by rfl) ⟨43719326, by rfl⟩ : syracuseStep 58292435 = 87438653) B87438653
theorem B2029819 : Blo 798342 2029819 := bstep (se 1 (by rfl) ⟨1522364, by rfl⟩ : syracuseStep 2029819 = 3044729) B3044729
theorem B1800467 : Blo 798342 1800467 := bstep (se 1 (by rfl) ⟨1350350, by rfl⟩ : syracuseStep 1800467 = 2700701) B2700701
theorem B1014439 : Blo 798342 1014439 := bstep (se 1 (by rfl) ⟨760829, by rfl⟩ : syracuseStep 1014439 = 1521659) B1521659
theorem B1802087 : Blo 798342 1802087 := bstep (se 1 (by rfl) ⟨1351565, by rfl⟩ : syracuseStep 1802087 = 2703131) B2703131
theorem B1802303 : Blo 798342 1802303 := bstep (se 1 (by rfl) ⟨1351727, by rfl⟩ : syracuseStep 1802303 = 2703455) B2703455
theorem B9111041 : Blo 798342 9111041 := bstep (se 2 (by rfl) ⟨3416640, by rfl⟩ : syracuseStep 9111041 = 6833281) B6833281
theorem B10258123 : Blo 798342 10258123 := bstep (se 1 (by rfl) ⟨7693592, by rfl⟩ : syracuseStep 10258123 = 15387185) B15387185
theorem B1804409 : Blo 798342 1804409 := bstep (se 2 (by rfl) ⟨676653, by rfl⟩ : syracuseStep 1804409 = 1353307) B1353307
theorem B6851051 : Blo 798342 6851051 := bstep (se 1 (by rfl) ⟨5138288, by rfl⟩ : syracuseStep 6851051 = 10276577) B10276577
theorem B2886137 : Blo 798342 2886137 := bstep (se 2 (by rfl) ⟨1082301, by rfl⟩ : syracuseStep 2886137 = 2164603) B2164603
theorem B2558945 : Blo 798342 2558945 := bstep (se 2 (by rfl) ⟨959604, by rfl⟩ : syracuseStep 2558945 = 1919209) B1919209
theorem B1281215 : Blo 798342 1281215 := bstep (se 1 (by rfl) ⟨960911, by rfl⟩ : syracuseStep 1281215 = 1921823) B1921823
theorem B6917345 : Blo 798342 6917345 := bstep (se 2 (by rfl) ⟨2594004, by rfl⟩ : syracuseStep 6917345 = 5188009) B5188009
theorem B1708543 : Blo 798342 1708543 := bstep (se 1 (by rfl) ⟨1281407, by rfl⟩ : syracuseStep 1708543 = 2562815) B2562815
theorem B4855859 : Blo 798342 4855859 := bstep (se 1 (by rfl) ⟨3641894, by rfl⟩ : syracuseStep 4855859 = 7283789) B7283789
theorem B1284265 : Blo 798342 1284265 := bstep (se 2 (by rfl) ⟨481599, by rfl⟩ : syracuseStep 1284265 = 963199) B963199
theorem B8657117 : Blo 798342 8657117 := bstep (se 3 (by rfl) ⟨1623209, by rfl⟩ : syracuseStep 8657117 = 3246419) B3246419
theorem B6822893 : Blo 798342 6822893 := bstep (se 3 (by rfl) ⟨1279292, by rfl⟩ : syracuseStep 6822893 = 2558585) B2558585
theorem B1351039 : Blo 798342 1351039 := bstep (se 1 (by rfl) ⟨1013279, by rfl⟩ : syracuseStep 1351039 = 2026559) B2026559
theorem B3251963 : Blo 798342 3251963 := bstep (se 1 (by rfl) ⟨2438972, by rfl⟩ : syracuseStep 3251963 = 4877945) B4877945
theorem B4103945 : Blo 798342 4103945 := bstep (se 2 (by rfl) ⟨1538979, by rfl⟩ : syracuseStep 4103945 = 3077959) B3077959
theorem B84156205 : Blo 798342 84156205 := bstep (se 3 (by rfl) ⟨15779288, by rfl⟩ : syracuseStep 84156205 = 31558577) B31558577
theorem B2695355 : Blo 798342 2695355 := bstep (se 1 (by rfl) ⟨2021516, by rfl⟩ : syracuseStep 2695355 = 4043033) B4043033
theorem B15377039 : Blo 798342 15377039 := bstep (se 1 (by rfl) ⟨11532779, by rfl⟩ : syracuseStep 15377039 = 23065559) B23065559
theorem B1352443 : Blo 798342 1352443 := bstep (se 1 (by rfl) ⟨1014332, by rfl⟩ : syracuseStep 1352443 = 2028665) B2028665
theorem B2564891 : Blo 798342 2564891 := bstep (se 1 (by rfl) ⟨1923668, by rfl⟩ : syracuseStep 2564891 = 3847337) B3847337
theorem B1352585 : Blo 798342 1352585 := bstep (se 2 (by rfl) ⟨507219, by rfl⟩ : syracuseStep 1352585 = 1014439) B1014439
theorem B5121863 : Blo 798342 5121863 := bstep (se 1 (by rfl) ⟨3841397, by rfl⟩ : syracuseStep 5121863 = 7682795) B7682795
theorem B2697353 : Blo 798342 2697353 := bstep (se 2 (by rfl) ⟨1011507, by rfl⟩ : syracuseStep 2697353 = 2023015) B2023015
theorem B3419273 : Blo 798342 3419273 := bstep (se 2 (by rfl) ⟨1282227, by rfl⟩ : syracuseStep 3419273 = 2564455) B2564455
theorem B798887 : Blo 798342 798887 := bstep (se 1 (by rfl) ⟨599165, by rfl⟩ : syracuseStep 798887 = 1198331) B1198331
theorem B799199 : Blo 798342 799199 := bstep (se 1 (by rfl) ⟨599399, by rfl⟩ : syracuseStep 799199 = 1198799) B1198799
theorem B1520383 : Blo 798342 1520383 := bstep (se 1 (by rfl) ⟨1140287, by rfl⟩ : syracuseStep 1520383 = 2280575) B2280575
theorem B2569247 : Blo 798342 2569247 := bstep (se 1 (by rfl) ⟨1926935, by rfl⟩ : syracuseStep 2569247 = 3853871) B3853871
theorem B2274799 : Blo 798342 2274799 := bstep (se 1 (by rfl) ⟨1706099, by rfl⟩ : syracuseStep 2274799 = 3412199) B3412199
theorem B2701025 : Blo 798342 2701025 := bstep (se 2 (by rfl) ⟨1012884, by rfl⟩ : syracuseStep 2701025 = 2025769) B2025769
theorem B2275199 : Blo 798342 2275199 := bstep (se 1 (by rfl) ⟨1706399, by rfl⟩ : syracuseStep 2275199 = 3412799) B3412799
theorem B2275391 : Blo 798342 2275391 := bstep (se 1 (by rfl) ⟨1706543, by rfl⟩ : syracuseStep 2275391 = 3413087) B3413087
theorem B801151 : Blo 798342 801151 := bstep (se 1 (by rfl) ⟨600863, by rfl⟩ : syracuseStep 801151 = 1201727) B1201727
theorem B4569533 : Blo 798342 4569533 := bstep (se 3 (by rfl) ⟨856787, by rfl⟩ : syracuseStep 4569533 = 1713575) B1713575
theorem B801215 : Blo 798342 801215 := bstep (se 1 (by rfl) ⟨600911, by rfl⟩ : syracuseStep 801215 = 1201823) B1201823
theorem B55458391 : Blo 798342 55458391 := bstep (se 1 (by rfl) ⟨41593793, by rfl⟩ : syracuseStep 55458391 = 83187587) B83187587
theorem B801567 : Blo 798342 801567 := bstep (se 1 (by rfl) ⟨601175, by rfl⟩ : syracuseStep 801567 = 1202351) B1202351
theorem B11516863 : Blo 798342 11516863 := bstep (se 1 (by rfl) ⟨8637647, by rfl⟩ : syracuseStep 11516863 = 17275295) B17275295
theorem B801819 : Blo 798342 801819 := bstep (se 1 (by rfl) ⟨601364, by rfl⟩ : syracuseStep 801819 = 1202729) B1202729
theorem B802151 : Blo 798342 802151 := bstep (se 1 (by rfl) ⟨601613, by rfl⟩ : syracuseStep 802151 = 1203227) B1203227
theorem B802239 : Blo 798342 802239 := bstep (se 1 (by rfl) ⟨601679, by rfl⟩ : syracuseStep 802239 = 1203359) B1203359
theorem B802335 : Blo 798342 802335 := bstep (se 1 (by rfl) ⟨601751, by rfl⟩ : syracuseStep 802335 = 1203503) B1203503
theorem B13876865 : Blo 798342 13876865 := bstep (se 2 (by rfl) ⟨5203824, by rfl⟩ : syracuseStep 13876865 = 10407649) B10407649
theorem B8765317 : Blo 798342 8765317 := bstep (se 4 (by rfl) ⟨821748, by rfl⟩ : syracuseStep 8765317 = 1643497) B1643497
theorem B4047083 : Blo 798342 4047083 := bstep (se 1 (by rfl) ⟨3035312, by rfl⟩ : syracuseStep 4047083 = 6070625) B6070625
theorem B2704697 : Blo 798342 2704697 := bstep (se 2 (by rfl) ⟨1014261, by rfl⟩ : syracuseStep 2704697 = 2028523) B2028523
theorem B1197551 : Blo 798342 1197551 := bstep (se 1 (by rfl) ⟨898163, by rfl⟩ : syracuseStep 1197551 = 1796327) B1796327
theorem B2312155 : Blo 798342 2312155 := bstep (se 1 (by rfl) ⟨1734116, by rfl⟩ : syracuseStep 2312155 = 3468233) B3468233
theorem B12339175 : Blo 798342 12339175 := bstep (se 1 (by rfl) ⟨9254381, by rfl⟩ : syracuseStep 12339175 = 18508763) B18508763
theorem B1198187 : Blo 798342 1198187 := bstep (se 1 (by rfl) ⟨898640, by rfl⟩ : syracuseStep 1198187 = 1797281) B1797281
theorem B88819847 : Blo 798342 88819847 := bstep (se 1 (by rfl) ⟨66614885, by rfl⟩ : syracuseStep 88819847 = 133229771) B133229771
theorem B1198703 : Blo 798342 1198703 := bstep (se 1 (by rfl) ⟨899027, by rfl⟩ : syracuseStep 1198703 = 1798055) B1798055
theorem B4049675 : Blo 798342 4049675 := bstep (se 1 (by rfl) ⟨3037256, by rfl⟩ : syracuseStep 4049675 = 6074513) B6074513
theorem B2706425 : Blo 798342 2706425 := bstep (se 2 (by rfl) ⟨1014909, by rfl⟩ : syracuseStep 2706425 = 2029819) B2029819
theorem B1199207 : Blo 798342 1199207 := bstep (se 1 (by rfl) ⟨899405, by rfl⟩ : syracuseStep 1199207 = 1798811) B1798811
theorem B2280631 : Blo 798342 2280631 := bstep (se 1 (by rfl) ⟨1710473, by rfl⟩ : syracuseStep 2280631 = 3420947) B3420947
theorem B1199387 : Blo 798342 1199387 := bstep (se 1 (by rfl) ⟨899540, by rfl⟩ : syracuseStep 1199387 = 1799081) B1799081
theorem B1200311 : Blo 798342 1200311 := bstep (se 1 (by rfl) ⟨900233, by rfl⟩ : syracuseStep 1200311 = 1800467) B1800467
theorem B4051295 : Blo 798342 4051295 := bstep (se 1 (by rfl) ⟨3038471, by rfl⟩ : syracuseStep 4051295 = 6076943) B6076943
theorem B11555561 : Blo 798342 11555561 := bstep (se 2 (by rfl) ⟨4333335, by rfl⟩ : syracuseStep 11555561 = 8666671) B8666671
theorem B10245001 : Blo 798342 10245001 := bstep (se 2 (by rfl) ⟨3841875, by rfl⟩ : syracuseStep 10245001 = 7683751) B7683751
theorem B1201391 : Blo 798342 1201391 := bstep (se 1 (by rfl) ⟨901043, by rfl⟩ : syracuseStep 1201391 = 1802087) B1802087
theorem B1201511 : Blo 798342 1201511 := bstep (se 1 (by rfl) ⟨901133, by rfl⟩ : syracuseStep 1201511 = 1802267) B1802267
theorem B1201895 : Blo 798342 1201895 := bstep (se 1 (by rfl) ⟨901421, by rfl⟩ : syracuseStep 1201895 = 1802843) B1802843
theorem B1201919 : Blo 798342 1201919 := bstep (se 1 (by rfl) ⟨901439, by rfl⟩ : syracuseStep 1201919 = 1802879) B1802879
theorem B1202111 : Blo 798342 1202111 := bstep (se 1 (by rfl) ⟨901583, by rfl⟩ : syracuseStep 1202111 = 1803167) B1803167
theorem B1202153 : Blo 798342 1202153 := bstep (se 2 (by rfl) ⟨450807, by rfl⟩ : syracuseStep 1202153 = 901615) B901615
theorem B1202207 : Blo 798342 1202207 := bstep (se 1 (by rfl) ⟨901655, by rfl⟩ : syracuseStep 1202207 = 1803311) B1803311
theorem B1202495 : Blo 798342 1202495 := bstep (se 1 (by rfl) ⟨901871, by rfl⟩ : syracuseStep 1202495 = 1803743) B1803743
theorem B1202687 : Blo 798342 1202687 := bstep (se 1 (by rfl) ⟨902015, by rfl⟩ : syracuseStep 1202687 = 1804031) B1804031
theorem B4053887 : Blo 798342 4053887 := bstep (se 1 (by rfl) ⟨3040415, by rfl⟩ : syracuseStep 4053887 = 6080831) B6080831
theorem B8903945 : Blo 798342 8903945 := bstep (se 2 (by rfl) ⟨3338979, by rfl⟩ : syracuseStep 8903945 = 6677959) B6677959
theorem B4054535 : Blo 798342 4054535 := bstep (se 1 (by rfl) ⟨3040901, by rfl⟩ : syracuseStep 4054535 = 6081803) B6081803
theorem B4547411 : Blo 798342 4547411 := bstep (se 1 (by rfl) ⟨3410558, by rfl⟩ : syracuseStep 4547411 = 6821117) B6821117
theorem B4548095 : Blo 798342 4548095 := bstep (se 1 (by rfl) ⟨3411071, by rfl⟩ : syracuseStep 4548095 = 6822143) B6822143
theorem B4877927 : Blo 798342 4877927 := bstep (se 1 (by rfl) ⟨3658445, by rfl⟩ : syracuseStep 4877927 = 7316891) B7316891
theorem B64811015 : Blo 798342 64811015 := bstep (se 1 (by rfl) ⟨48608261, by rfl⟩ : syracuseStep 64811015 = 97216523) B97216523
theorem B1798379 : Blo 798342 1798379 := bstep (se 1 (by rfl) ⟨1348784, by rfl⟩ : syracuseStep 1798379 = 2697569) B2697569
theorem B9138743 : Blo 798342 9138743 := bstep (se 1 (by rfl) ⟨6854057, by rfl⟩ : syracuseStep 9138743 = 13708115) B13708115
theorem B1799135 : Blo 798342 1799135 := bstep (se 1 (by rfl) ⟨1349351, by rfl⟩ : syracuseStep 1799135 = 2698703) B2698703
theorem B2028827 : Blo 798342 2028827 := bstep (se 1 (by rfl) ⟨1521620, by rfl⟩ : syracuseStep 2028827 = 3043241) B3043241
theorem B8647991 : Blo 798342 8647991 := bstep (se 1 (by rfl) ⟨6485993, by rfl⟩ : syracuseStep 8647991 = 12971987) B12971987
theorem B2160191 : Blo 798342 2160191 := bstep (se 1 (by rfl) ⟨1620143, by rfl⟩ : syracuseStep 2160191 = 3240287) B3240287
theorem B7699211 : Blo 798342 7699211 := bstep (se 1 (by rfl) ⟨5774408, by rfl⟩ : syracuseStep 7699211 = 11548817) B11548817
theorem B38861623 : Blo 798342 38861623 := bstep (se 1 (by rfl) ⟨29146217, by rfl⟩ : syracuseStep 38861623 = 58292435) B58292435
theorem B1803131 : Blo 798342 1803131 := bstep (se 1 (by rfl) ⟨1352348, by rfl⟩ : syracuseStep 1803131 = 2704697) B2704697
theorem B1803257 : Blo 798342 1803257 := bstep (se 2 (by rfl) ⟨676221, by rfl⟩ : syracuseStep 1803257 = 1352443) B1352443
theorem B59213231 : Blo 798342 59213231 := bstep (se 1 (by rfl) ⟨44409923, by rfl⟩ : syracuseStep 59213231 = 88819847) B88819847
theorem B1705963 : Blo 798342 1705963 := bstep (se 1 (by rfl) ⟨1279472, by rfl⟩ : syracuseStep 1705963 = 2558945) B2558945
theorem B1804283 : Blo 798342 1804283 := bstep (se 1 (by rfl) ⟨1353212, by rfl⟩ : syracuseStep 1804283 = 2706425) B2706425
theorem B3082873 : Blo 798342 3082873 := bstep (se 2 (by rfl) ⟨1156077, by rfl⟩ : syracuseStep 3082873 = 2312155) B2312155
theorem B16452233 : Blo 798342 16452233 := bstep (se 2 (by rfl) ⟨6169587, by rfl⟩ : syracuseStep 16452233 = 12339175) B12339175
theorem B7703707 : Blo 798342 7703707 := bstep (se 1 (by rfl) ⟨5777780, by rfl⟩ : syracuseStep 7703707 = 11555561) B11555561
theorem B5771411 : Blo 798342 5771411 := bstep (se 1 (by rfl) ⟨4328558, by rfl⟩ : syracuseStep 5771411 = 8657117) B8657117
theorem B5935963 : Blo 798342 5935963 := bstep (se 1 (by rfl) ⟨4451972, by rfl⟩ : syracuseStep 5935963 = 8903945) B8903945
theorem B2167975 : Blo 798342 2167975 := bstep (se 1 (by rfl) ⟨1625981, by rfl⟩ : syracuseStep 2167975 = 3251963) B3251963
theorem B6067709 : Blo 798342 6067709 := bstep (se 3 (by rfl) ⟨1137695, by rfl⟩ : syracuseStep 6067709 = 2275391) B2275391
theorem B1709927 : Blo 798342 1709927 := bstep (se 1 (by rfl) ⟨1282445, by rfl⟩ : syracuseStep 1709927 = 2564891) B2564891
theorem B3414575 : Blo 798342 3414575 := bstep (se 1 (by rfl) ⟨2560931, by rfl⟩ : syracuseStep 3414575 = 5121863) B5121863
theorem B3251951 : Blo 798342 3251951 := bstep (se 1 (by rfl) ⟨2438963, by rfl⟩ : syracuseStep 3251951 = 4877927) B4877927
theorem B1712353 : Blo 798342 1712353 := bstep (se 2 (by rfl) ⟨642132, by rfl⟩ : syracuseStep 1712353 = 1284265) B1284265
theorem B3416573 : Blo 798342 3416573 := bstep (se 3 (by rfl) ⟨640607, by rfl⟩ : syracuseStep 3416573 = 1281215) B1281215
theorem B1712831 : Blo 798342 1712831 := bstep (se 1 (by rfl) ⟨1284623, by rfl⟩ : syracuseStep 1712831 = 2569247) B2569247
theorem B1352551 : Blo 798342 1352551 := bstep (se 1 (by rfl) ⟨1014413, by rfl⟩ : syracuseStep 1352551 = 2028827) B2028827
theorem B51815497 : Blo 798342 51815497 := bstep (se 2 (by rfl) ⟨19430811, by rfl⟩ : syracuseStep 51815497 = 38861623) B38861623
theorem B1516799 : Blo 798342 1516799 := bstep (se 1 (by rfl) ⟨1137599, by rfl⟩ : syracuseStep 1516799 = 2275199) B2275199
theorem B112208273 : Blo 798342 112208273 := bstep (se 2 (by rfl) ⟨42078102, by rfl⟩ : syracuseStep 112208273 = 84156205) B84156205
theorem B9251243 : Blo 798342 9251243 := bstep (se 1 (by rfl) ⟨6938432, by rfl⟩ : syracuseStep 9251243 = 13876865) B13876865
theorem B2698055 : Blo 798342 2698055 := bstep (se 1 (by rfl) ⟨2023541, by rfl⟩ : syracuseStep 2698055 = 4047083) B4047083
theorem B798367 : Blo 798342 798367 := bstep (se 1 (by rfl) ⟨598775, by rfl⟩ : syracuseStep 798367 = 1197551) B1197551
theorem B6074027 : Blo 798342 6074027 := bstep (se 1 (by rfl) ⟨4555520, by rfl⟩ : syracuseStep 6074027 = 9111041) B9111041
theorem B798791 : Blo 798342 798791 := bstep (se 1 (by rfl) ⟨599093, by rfl⟩ : syracuseStep 798791 = 1198187) B1198187
theorem B4567367 : Blo 798342 4567367 := bstep (se 1 (by rfl) ⟨3425525, by rfl⟩ : syracuseStep 4567367 = 6851051) B6851051
theorem B799135 : Blo 798342 799135 := bstep (se 1 (by rfl) ⟨599351, by rfl⟩ : syracuseStep 799135 = 1198703) B1198703
theorem B2699783 : Blo 798342 2699783 := bstep (se 1 (by rfl) ⟨2024837, by rfl⟩ : syracuseStep 2699783 = 4049675) B4049675
theorem B799471 : Blo 798342 799471 := bstep (se 1 (by rfl) ⟨599603, by rfl⟩ : syracuseStep 799471 = 1199207) B1199207
theorem B799591 : Blo 798342 799591 := bstep (se 1 (by rfl) ⟨599693, by rfl⟩ : syracuseStep 799591 = 1199387) B1199387
theorem B13677497 : Blo 798342 13677497 := bstep (se 2 (by rfl) ⟨5129061, by rfl⟩ : syracuseStep 13677497 = 10258123) B10258123
theorem B800207 : Blo 798342 800207 := bstep (se 1 (by rfl) ⟨600155, by rfl⟩ : syracuseStep 800207 = 1200311) B1200311
theorem B2700863 : Blo 798342 2700863 := bstep (se 1 (by rfl) ⟨2025647, by rfl⟩ : syracuseStep 2700863 = 4051295) B4051295
theorem B800927 : Blo 798342 800927 := bstep (se 1 (by rfl) ⟨600695, by rfl⟩ : syracuseStep 800927 = 1201391) B1201391
theorem B801007 : Blo 798342 801007 := bstep (se 1 (by rfl) ⟨600755, by rfl⟩ : syracuseStep 801007 = 1201511) B1201511
theorem B801263 : Blo 798342 801263 := bstep (se 1 (by rfl) ⟨600947, by rfl⟩ : syracuseStep 801263 = 1201895) B1201895
theorem B801279 : Blo 798342 801279 := bstep (se 1 (by rfl) ⟨600959, by rfl⟩ : syracuseStep 801279 = 1201919) B1201919
theorem B801407 : Blo 798342 801407 := bstep (se 1 (by rfl) ⟨601055, by rfl⟩ : syracuseStep 801407 = 1202111) B1202111
theorem B801435 : Blo 798342 801435 := bstep (se 1 (by rfl) ⟨601076, by rfl⟩ : syracuseStep 801435 = 1202153) B1202153
theorem B801471 : Blo 798342 801471 := bstep (se 1 (by rfl) ⟨601103, by rfl⟩ : syracuseStep 801471 = 1202207) B1202207
theorem B801663 : Blo 798342 801663 := bstep (se 1 (by rfl) ⟨601247, by rfl⟩ : syracuseStep 801663 = 1202495) B1202495
theorem B801791 : Blo 798342 801791 := bstep (se 1 (by rfl) ⟨601343, by rfl⟩ : syracuseStep 801791 = 1202687) B1202687
theorem B2702591 : Blo 798342 2702591 := bstep (se 1 (by rfl) ⟨2026943, by rfl⟩ : syracuseStep 2702591 = 4053887) B4053887
theorem B2703023 : Blo 798342 2703023 := bstep (se 1 (by rfl) ⟨2027267, by rfl⟩ : syracuseStep 2703023 = 4054535) B4054535
theorem B2735963 : Blo 798342 2735963 := bstep (se 1 (by rfl) ⟨2051972, by rfl⟩ : syracuseStep 2735963 = 4103945) B4103945
theorem B3031607 : Blo 798342 3031607 := bstep (se 1 (by rfl) ⟨2273705, by rfl⟩ : syracuseStep 3031607 = 4547411) B4547411
theorem B901723 : Blo 798342 901723 := bstep (se 1 (by rfl) ⟨676292, by rfl⟩ : syracuseStep 901723 = 1352585) B1352585
theorem B2278057 : Blo 798342 2278057 := bstep (se 2 (by rfl) ⟨854271, by rfl⟩ : syracuseStep 2278057 = 1708543) B1708543
theorem B3032063 : Blo 798342 3032063 := bstep (se 1 (by rfl) ⟨2274047, by rfl⟩ : syracuseStep 3032063 = 4548095) B4548095
theorem B3033065 : Blo 798342 3033065 := bstep (se 2 (by rfl) ⟨1137399, by rfl⟩ : syracuseStep 3033065 = 2274799) B2274799
theorem B2279515 : Blo 798342 2279515 := bstep (se 1 (by rfl) ⟨1709636, by rfl⟩ : syracuseStep 2279515 = 3419273) B3419273
theorem B43207343 : Blo 798342 43207343 := bstep (se 1 (by rfl) ⟨32405507, by rfl⟩ : syracuseStep 43207343 = 64811015) B64811015
theorem B1198919 : Blo 798342 1198919 := bstep (se 1 (by rfl) ⟨899189, by rfl⟩ : syracuseStep 1198919 = 1798379) B1798379
theorem B1199423 : Blo 798342 1199423 := bstep (se 1 (by rfl) ⟨899567, by rfl⟩ : syracuseStep 1199423 = 1799135) B1799135
theorem B73944521 : Blo 798342 73944521 := bstep (se 2 (by rfl) ⟨27729195, by rfl⟩ : syracuseStep 73944521 = 55458391) B55458391
theorem B15355817 : Blo 798342 15355817 := bstep (se 2 (by rfl) ⟨5758431, by rfl⟩ : syracuseStep 15355817 = 11516863) B11516863
theorem B5132807 : Blo 798342 5132807 := bstep (se 1 (by rfl) ⟨3849605, by rfl⟩ : syracuseStep 5132807 = 7699211) B7699211
theorem B11687089 : Blo 798342 11687089 := bstep (se 2 (by rfl) ⟨4382658, by rfl⟩ : syracuseStep 11687089 = 8765317) B8765317
theorem B1201535 : Blo 798342 1201535 := bstep (se 1 (by rfl) ⟨901151, by rfl⟩ : syracuseStep 1201535 = 1802303) B1802303
theorem B1202939 : Blo 798342 1202939 := bstep (se 1 (by rfl) ⟨902204, by rfl⟩ : syracuseStep 1202939 = 1804409) B1804409
theorem B1924091 : Blo 798342 1924091 := bstep (se 1 (by rfl) ⟨1443068, by rfl⟩ : syracuseStep 1924091 = 2886137) B2886137
theorem B4611563 : Blo 798342 4611563 := bstep (se 1 (by rfl) ⟨3458672, by rfl⟩ : syracuseStep 4611563 = 6917345) B6917345
theorem B3237239 : Blo 798342 3237239 := bstep (se 1 (by rfl) ⟨2427929, by rfl⟩ : syracuseStep 3237239 = 4855859) B4855859
theorem B3040841 : Blo 798342 3040841 := bstep (se 2 (by rfl) ⟨1140315, by rfl⟩ : syracuseStep 3040841 = 2280631) B2280631
theorem B4548595 : Blo 798342 4548595 := bstep (se 1 (by rfl) ⟨3411446, by rfl⟩ : syracuseStep 4548595 = 6822893) B6822893
theorem B1796903 : Blo 798342 1796903 := bstep (se 1 (by rfl) ⟨1347677, by rfl⟩ : syracuseStep 1796903 = 2695355) B2695355
theorem B10251359 : Blo 798342 10251359 := bstep (se 1 (by rfl) ⟨7688519, by rfl⟩ : syracuseStep 10251359 = 15377039) B15377039
theorem B2027177 : Blo 798342 2027177 := bstep (se 2 (by rfl) ⟨760191, by rfl⟩ : syracuseStep 2027177 = 1520383) B1520383
theorem B13660001 : Blo 798342 13660001 := bstep (se 2 (by rfl) ⟨5122500, by rfl⟩ : syracuseStep 13660001 = 10245001) B10245001
theorem B1798235 : Blo 798342 1798235 := bstep (se 1 (by rfl) ⟨1348676, by rfl⟩ : syracuseStep 1798235 = 2697353) B2697353
theorem B6092495 : Blo 798342 6092495 := bstep (se 1 (by rfl) ⟨4569371, by rfl⟩ : syracuseStep 6092495 = 9138743) B9138743
theorem B5765327 : Blo 798342 5765327 := bstep (se 1 (by rfl) ⟨4323995, by rfl⟩ : syracuseStep 5765327 = 8647991) B8647991
theorem B1440127 : Blo 798342 1440127 := bstep (se 1 (by rfl) ⟨1080095, by rfl⟩ : syracuseStep 1440127 = 2160191) B2160191
theorem B1800683 : Blo 798342 1800683 := bstep (se 1 (by rfl) ⟨1350512, by rfl⟩ : syracuseStep 1800683 = 2701025) B2701025
theorem B3046355 : Blo 798342 3046355 := bstep (se 1 (by rfl) ⟨2284766, by rfl⟩ : syracuseStep 3046355 = 4569533) B4569533
theorem B1801385 : Blo 798342 1801385 := bstep (se 2 (by rfl) ⟨675519, by rfl⟩ : syracuseStep 1801385 = 1351039) B1351039
theorem B1803401 : Blo 798342 1803401 := bstep (se 2 (by rfl) ⟨676275, by rfl⟩ : syracuseStep 1803401 = 1352551) B1352551
theorem B28804895 : Blo 798342 28804895 := bstep (se 1 (by rfl) ⟨21603671, by rfl⟩ : syracuseStep 28804895 = 43207343) B43207343
theorem B6064793 : Blo 798342 6064793 := bstep (se 2 (by rfl) ⟨2274297, by rfl⟩ : syracuseStep 6064793 = 4548595) B4548595
theorem B1282727 : Blo 798342 1282727 := bstep (se 1 (by rfl) ⟨962045, by rfl⟩ : syracuseStep 1282727 = 1924091) B1924091
theorem B2167967 : Blo 798342 2167967 := bstep (se 1 (by rfl) ⟨1625975, by rfl⟩ : syracuseStep 2167967 = 3251951) B3251951
theorem B6167495 : Blo 798342 6167495 := bstep (se 1 (by rfl) ⟨4625621, by rfl⟩ : syracuseStep 6167495 = 9251243) B9251243
theorem B1351451 : Blo 798342 1351451 := bstep (se 1 (by rfl) ⟨1013588, by rfl⟩ : syracuseStep 1351451 = 2027177) B2027177
theorem B9118331 : Blo 798342 9118331 := bstep (se 1 (by rfl) ⟨6838748, by rfl⟩ : syracuseStep 9118331 = 13677497) B13677497
theorem B3843551 : Blo 798342 3843551 := bstep (se 1 (by rfl) ⟨2882663, by rfl⟩ : syracuseStep 3843551 = 5765327) B5765327
theorem B69087329 : Blo 798342 69087329 := bstep (se 2 (by rfl) ⟨25907748, by rfl⟩ : syracuseStep 69087329 = 51815497) B51815497
theorem B4567549 : Blo 798342 4567549 := bstep (se 3 (by rfl) ⟨856415, by rfl⟩ : syracuseStep 4567549 = 1712831) B1712831
theorem B799279 : Blo 798342 799279 := bstep (se 1 (by rfl) ⟨599459, by rfl⟩ : syracuseStep 799279 = 1198919) B1198919
theorem B799615 : Blo 798342 799615 := bstep (se 1 (by rfl) ⟨599711, by rfl⟩ : syracuseStep 799615 = 1199423) B1199423
theorem B49296347 : Blo 798342 49296347 := bstep (se 1 (by rfl) ⟨36972260, by rfl⟩ : syracuseStep 49296347 = 73944521) B73944521
theorem B10237211 : Blo 798342 10237211 := bstep (se 1 (by rfl) ⟨7677908, by rfl⟩ : syracuseStep 10237211 = 15355817) B15355817
theorem B2274617 : Blo 798342 2274617 := bstep (se 2 (by rfl) ⟨852981, by rfl⟩ : syracuseStep 2274617 = 1705963) B1705963
theorem B3847607 : Blo 798342 3847607 := bstep (se 1 (by rfl) ⟨2885705, by rfl⟩ : syracuseStep 3847607 = 5771411) B5771411
theorem B3421871 : Blo 798342 3421871 := bstep (se 1 (by rfl) ⟨2566403, by rfl⟩ : syracuseStep 3421871 = 5132807) B5132807
theorem B4110497 : Blo 798342 4110497 := bstep (se 2 (by rfl) ⟨1541436, by rfl⟩ : syracuseStep 4110497 = 3082873) B3082873
theorem B801023 : Blo 798342 801023 := bstep (se 1 (by rfl) ⟨600767, by rfl⟩ : syracuseStep 801023 = 1201535) B1201535
theorem B4045139 : Blo 798342 4045139 := bstep (se 1 (by rfl) ⟨3033854, by rfl⟩ : syracuseStep 4045139 = 6067709) B6067709
theorem B10271609 : Blo 798342 10271609 := bstep (se 2 (by rfl) ⟨3851853, by rfl⟩ : syracuseStep 10271609 = 7703707) B7703707
theorem B2276383 : Blo 798342 2276383 := bstep (se 1 (by rfl) ⟨1707287, by rfl⟩ : syracuseStep 2276383 = 3414575) B3414575
theorem B801959 : Blo 798342 801959 := bstep (se 1 (by rfl) ⟨601469, by rfl⟩ : syracuseStep 801959 = 1202939) B1202939
theorem B2277715 : Blo 798342 2277715 := bstep (se 1 (by rfl) ⟨1708286, by rfl⟩ : syracuseStep 2277715 = 3416573) B3416573
theorem B7914617 : Blo 798342 7914617 := bstep (se 2 (by rfl) ⟨2967981, by rfl⟩ : syracuseStep 7914617 = 5935963) B5935963
theorem B15582785 : Blo 798342 15582785 := bstep (se 2 (by rfl) ⟨5843544, by rfl⟩ : syracuseStep 15582785 = 11687089) B11687089
theorem B1197935 : Blo 798342 1197935 := bstep (se 1 (by rfl) ⟨898451, by rfl⟩ : syracuseStep 1197935 = 1796903) B1796903
theorem B6834239 : Blo 798342 6834239 := bstep (se 1 (by rfl) ⟨5125679, by rfl⟩ : syracuseStep 6834239 = 10251359) B10251359
theorem B4049351 : Blo 798342 4049351 := bstep (se 1 (by rfl) ⟨3037013, by rfl⟩ : syracuseStep 4049351 = 6074027) B6074027
theorem B1198823 : Blo 798342 1198823 := bstep (se 1 (by rfl) ⟨899117, by rfl⟩ : syracuseStep 1198823 = 1798235) B1798235
theorem B1920169 : Blo 798342 1920169 := bstep (se 2 (by rfl) ⟨720063, by rfl⟩ : syracuseStep 1920169 = 1440127) B1440127
theorem B1200455 : Blo 798342 1200455 := bstep (se 1 (by rfl) ⟨900341, by rfl⟩ : syracuseStep 1200455 = 1800683) B1800683
theorem B1200923 : Blo 798342 1200923 := bstep (se 1 (by rfl) ⟨900692, by rfl⟩ : syracuseStep 1200923 = 1801385) B1801385
theorem B1823975 : Blo 798342 1823975 := bstep (se 1 (by rfl) ⟨1367981, by rfl⟩ : syracuseStep 1823975 = 2735963) B2735963
theorem B2283137 : Blo 798342 2283137 := bstep (se 2 (by rfl) ⟨856176, by rfl⟩ : syracuseStep 2283137 = 1712353) B1712353
theorem B2021071 : Blo 798342 2021071 := bstep (se 1 (by rfl) ⟨1515803, by rfl⟩ : syracuseStep 2021071 = 3031607) B3031607
theorem B1202087 : Blo 798342 1202087 := bstep (se 1 (by rfl) ⟨901565, by rfl⟩ : syracuseStep 1202087 = 1803131) B1803131
theorem B1202171 : Blo 798342 1202171 := bstep (se 1 (by rfl) ⟨901628, by rfl⟩ : syracuseStep 1202171 = 1803257) B1803257
theorem B2021375 : Blo 798342 2021375 := bstep (se 1 (by rfl) ⟨1516031, by rfl⟩ : syracuseStep 2021375 = 3032063) B3032063
theorem B1202297 : Blo 798342 1202297 := bstep (se 2 (by rfl) ⟨450861, by rfl⟩ : syracuseStep 1202297 = 901723) B901723
theorem B3037409 : Blo 798342 3037409 := bstep (se 2 (by rfl) ⟨1139028, by rfl⟩ : syracuseStep 3037409 = 2278057) B2278057
theorem B39475487 : Blo 798342 39475487 := bstep (se 1 (by rfl) ⟨29606615, by rfl⟩ : syracuseStep 39475487 = 59213231) B59213231
theorem B2022043 : Blo 798342 2022043 := bstep (se 1 (by rfl) ⟨1516532, by rfl⟩ : syracuseStep 2022043 = 3033065) B3033065
theorem B1202855 : Blo 798342 1202855 := bstep (se 1 (by rfl) ⟨902141, by rfl⟩ : syracuseStep 1202855 = 1804283) B1804283
theorem B10968155 : Blo 798342 10968155 := bstep (se 1 (by rfl) ⟨8226116, by rfl⟩ : syracuseStep 10968155 = 16452233) B16452233
theorem B3039353 : Blo 798342 3039353 := bstep (se 2 (by rfl) ⟨1139757, by rfl⟩ : syracuseStep 3039353 = 2279515) B2279515
theorem B1139951 : Blo 798342 1139951 := bstep (se 1 (by rfl) ⟨854963, by rfl⟩ : syracuseStep 1139951 = 1709927) B1709927
theorem B3074375 : Blo 798342 3074375 := bstep (se 1 (by rfl) ⟨2305781, by rfl⟩ : syracuseStep 3074375 = 4611563) B4611563
theorem B1011199 : Blo 798342 1011199 := bstep (se 1 (by rfl) ⟨758399, by rfl⟩ : syracuseStep 1011199 = 1516799) B1516799
theorem B11562533 : Blo 798342 11562533 := bstep (se 4 (by rfl) ⟨1083987, by rfl⟩ : syracuseStep 11562533 = 2167975) B2167975
theorem B2158159 : Blo 798342 2158159 := bstep (se 1 (by rfl) ⟨1618619, by rfl⟩ : syracuseStep 2158159 = 3237239) B3237239
theorem B2027227 : Blo 798342 2027227 := bstep (se 1 (by rfl) ⟨1520420, by rfl⟩ : syracuseStep 2027227 = 3040841) B3040841
theorem B74805515 : Blo 798342 74805515 := bstep (se 1 (by rfl) ⟨56104136, by rfl⟩ : syracuseStep 74805515 = 112208273) B112208273
theorem B1798703 : Blo 798342 1798703 := bstep (se 1 (by rfl) ⟨1349027, by rfl⟩ : syracuseStep 1798703 = 2698055) B2698055
theorem B9106667 : Blo 798342 9106667 := bstep (se 1 (by rfl) ⟨6830000, by rfl⟩ : syracuseStep 9106667 = 13660001) B13660001
theorem B3044911 : Blo 798342 3044911 := bstep (se 1 (by rfl) ⟨2283683, by rfl⟩ : syracuseStep 3044911 = 4567367) B4567367
theorem B1799855 : Blo 798342 1799855 := bstep (se 1 (by rfl) ⟨1349891, by rfl⟩ : syracuseStep 1799855 = 2699783) B2699783
theorem B1800575 : Blo 798342 1800575 := bstep (se 1 (by rfl) ⟨1350431, by rfl⟩ : syracuseStep 1800575 = 2700863) B2700863
theorem B4061663 : Blo 798342 4061663 := bstep (se 1 (by rfl) ⟨3046247, by rfl⟩ : syracuseStep 4061663 = 6092495) B6092495
theorem B2030903 : Blo 798342 2030903 := bstep (se 1 (by rfl) ⟨1523177, by rfl⟩ : syracuseStep 2030903 = 3046355) B3046355
theorem B1801727 : Blo 798342 1801727 := bstep (se 1 (by rfl) ⟨1351295, by rfl⟩ : syracuseStep 1801727 = 2702591) B2702591
theorem B1802015 : Blo 798342 1802015 := bstep (se 1 (by rfl) ⟨1351511, by rfl⟩ : syracuseStep 1802015 = 2703023) B2703023
theorem B5276411 : Blo 798342 5276411 := bstep (se 1 (by rfl) ⟨3957308, by rfl⟩ : syracuseStep 5276411 = 7914617) B7914617
theorem B19203263 : Blo 798342 19203263 := bstep (se 1 (by rfl) ⟨14402447, by rfl⟩ : syracuseStep 19203263 = 28804895) B28804895
theorem B4556159 : Blo 798342 4556159 := bstep (se 1 (by rfl) ⟨3417119, by rfl⟩ : syracuseStep 4556159 = 6834239) B6834239
theorem B1445311 : Blo 798342 1445311 := bstep (se 1 (by rfl) ⟨1083983, by rfl⟩ : syracuseStep 1445311 = 2167967) B2167967
theorem B1215983 : Blo 798342 1215983 := bstep (se 1 (by rfl) ⟨911987, by rfl⟩ : syracuseStep 1215983 = 1823975) B1823975
theorem B1347583 : Blo 798342 1347583 := bstep (se 1 (by rfl) ⟨1010687, by rfl⟩ : syracuseStep 1347583 = 2021375) B2021375
theorem B26316991 : Blo 798342 26316991 := bstep (se 1 (by rfl) ⟨19737743, by rfl⟩ : syracuseStep 26316991 = 39475487) B39475487
theorem B1348265 : Blo 798342 1348265 := bstep (se 2 (by rfl) ⟨505599, by rfl⟩ : syracuseStep 1348265 = 1011199) B1011199
theorem B7312103 : Blo 798342 7312103 := bstep (se 1 (by rfl) ⟨5484077, by rfl⟩ : syracuseStep 7312103 = 10968155) B10968155
theorem B8198333 : Blo 798342 8198333 := bstep (se 3 (by rfl) ⟨1537187, by rfl⟩ : syracuseStep 8198333 = 3074375) B3074375
theorem B2562367 : Blo 798342 2562367 := bstep (se 1 (by rfl) ⟨1921775, by rfl⟩ : syracuseStep 2562367 = 3843551) B3843551
theorem B2694761 : Blo 798342 2694761 := bstep (se 2 (by rfl) ⟨1010535, by rfl⟩ : syracuseStep 2694761 = 2021071) B2021071
theorem B7708355 : Blo 798342 7708355 := bstep (se 1 (by rfl) ⟨5781266, by rfl⟩ : syracuseStep 7708355 = 11562533) B11562533
theorem B6071111 : Blo 798342 6071111 := bstep (se 1 (by rfl) ⟨4553333, by rfl⟩ : syracuseStep 6071111 = 9106667) B9106667
theorem B6824807 : Blo 798342 6824807 := bstep (se 1 (by rfl) ⟨5118605, by rfl⟩ : syracuseStep 6824807 = 10237211) B10237211
theorem B2696057 : Blo 798342 2696057 := bstep (se 2 (by rfl) ⟨1011021, by rfl⟩ : syracuseStep 2696057 = 2022043) B2022043
theorem B1516411 : Blo 798342 1516411 := bstep (se 1 (by rfl) ⟨1137308, by rfl⟩ : syracuseStep 1516411 = 2274617) B2274617
theorem B2565071 : Blo 798342 2565071 := bstep (se 1 (by rfl) ⟨1923803, by rfl⟩ : syracuseStep 2565071 = 3847607) B3847607
theorem B2696759 : Blo 798342 2696759 := bstep (se 1 (by rfl) ⟨2022569, by rfl⟩ : syracuseStep 2696759 = 4045139) B4045139
theorem B1353935 : Blo 798342 1353935 := bstep (se 1 (by rfl) ⟨1015451, by rfl⟩ : syracuseStep 1353935 = 2030903) B2030903
theorem B798623 : Blo 798342 798623 := bstep (se 1 (by rfl) ⟨598967, by rfl⟩ : syracuseStep 798623 = 1197935) B1197935
theorem B2699567 : Blo 798342 2699567 := bstep (se 1 (by rfl) ⟨2024675, by rfl⟩ : syracuseStep 2699567 = 4049351) B4049351
theorem B4043195 : Blo 798342 4043195 := bstep (se 1 (by rfl) ⟨3032396, by rfl⟩ : syracuseStep 4043195 = 6064793) B6064793
theorem B3420605 : Blo 798342 3420605 := bstep (se 3 (by rfl) ⟨641363, by rfl⟩ : syracuseStep 3420605 = 1282727) B1282727
theorem B799215 : Blo 798342 799215 := bstep (se 1 (by rfl) ⟨599411, by rfl⟩ : syracuseStep 799215 = 1198823) B1198823
theorem B800303 : Blo 798342 800303 := bstep (se 1 (by rfl) ⟨600227, by rfl⟩ : syracuseStep 800303 = 1200455) B1200455
theorem B800615 : Blo 798342 800615 := bstep (se 1 (by rfl) ⟨600461, by rfl⟩ : syracuseStep 800615 = 1200923) B1200923
theorem B1522091 : Blo 798342 1522091 := bstep (se 1 (by rfl) ⟨1141568, by rfl⟩ : syracuseStep 1522091 = 2283137) B2283137
theorem B801391 : Blo 798342 801391 := bstep (se 1 (by rfl) ⟨601043, by rfl⟩ : syracuseStep 801391 = 1202087) B1202087
theorem B801447 : Blo 798342 801447 := bstep (se 1 (by rfl) ⟨601085, by rfl⟩ : syracuseStep 801447 = 1202171) B1202171
theorem B801531 : Blo 798342 801531 := bstep (se 1 (by rfl) ⟨601148, by rfl⟩ : syracuseStep 801531 = 1202297) B1202297
theorem B801903 : Blo 798342 801903 := bstep (se 1 (by rfl) ⟨601427, by rfl⟩ : syracuseStep 801903 = 1202855) B1202855
theorem B4111663 : Blo 798342 4111663 := bstep (se 1 (by rfl) ⟨3083747, by rfl⟩ : syracuseStep 4111663 = 6167495) B6167495
theorem B2702969 : Blo 798342 2702969 := bstep (se 2 (by rfl) ⟨1013613, by rfl⟩ : syracuseStep 2702969 = 2027227) B2027227
theorem B900967 : Blo 798342 900967 := bstep (se 1 (by rfl) ⟨675725, by rfl⟩ : syracuseStep 900967 = 1351451) B1351451
theorem B6078887 : Blo 798342 6078887 := bstep (se 1 (by rfl) ⟨4559165, by rfl⟩ : syracuseStep 6078887 = 9118331) B9118331
theorem B166216373 : Blo 798342 166216373 := bstep (se 5 (by rfl) ⟨7791392, by rfl⟩ : syracuseStep 166216373 = 15582785) B15582785
theorem B10240901 : Blo 798342 10240901 := bstep (se 4 (by rfl) ⟨960084, by rfl⟩ : syracuseStep 10240901 = 1920169) B1920169
theorem B46058219 : Blo 798342 46058219 := bstep (se 1 (by rfl) ⟨34543664, by rfl⟩ : syracuseStep 46058219 = 69087329) B69087329
theorem B1199135 : Blo 798342 1199135 := bstep (se 1 (by rfl) ⟨899351, by rfl⟩ : syracuseStep 1199135 = 1798703) B1798703
theorem B1199903 : Blo 798342 1199903 := bstep (se 1 (by rfl) ⟨899927, by rfl⟩ : syracuseStep 1199903 = 1799855) B1799855
theorem B2281247 : Blo 798342 2281247 := bstep (se 1 (by rfl) ⟨1710935, by rfl⟩ : syracuseStep 2281247 = 3421871) B3421871
theorem B3035177 : Blo 798342 3035177 := bstep (se 2 (by rfl) ⟨1138191, by rfl⟩ : syracuseStep 3035177 = 2276383) B2276383
theorem B2740331 : Blo 798342 2740331 := bstep (se 1 (by rfl) ⟨2055248, by rfl⟩ : syracuseStep 2740331 = 4110497) B4110497
theorem B1200383 : Blo 798342 1200383 := bstep (se 1 (by rfl) ⟨900287, by rfl⟩ : syracuseStep 1200383 = 1800575) B1800575
theorem B2707775 : Blo 798342 2707775 := bstep (se 1 (by rfl) ⟨2030831, by rfl⟩ : syracuseStep 2707775 = 4061663) B4061663
theorem B1201151 : Blo 798342 1201151 := bstep (se 1 (by rfl) ⟨900863, by rfl⟩ : syracuseStep 1201151 = 1801727) B1801727
theorem B1201343 : Blo 798342 1201343 := bstep (se 1 (by rfl) ⟨901007, by rfl⟩ : syracuseStep 1201343 = 1802015) B1802015
theorem B3036953 : Blo 798342 3036953 := bstep (se 2 (by rfl) ⟨1138857, by rfl⟩ : syracuseStep 3036953 = 2277715) B2277715
theorem B1202267 : Blo 798342 1202267 := bstep (se 1 (by rfl) ⟨901700, by rfl⟩ : syracuseStep 1202267 = 1803401) B1803401
theorem B3039869 : Blo 798342 3039869 := bstep (se 3 (by rfl) ⟨569975, by rfl⟩ : syracuseStep 3039869 = 1139951) B1139951
theorem B2024939 : Blo 798342 2024939 := bstep (se 1 (by rfl) ⟨1518704, by rfl⟩ : syracuseStep 2024939 = 3037409) B3037409
theorem B2877545 : Blo 798342 2877545 := bstep (se 2 (by rfl) ⟨1079079, by rfl⟩ : syracuseStep 2877545 = 2158159) B2158159
theorem B2026235 : Blo 798342 2026235 := bstep (se 1 (by rfl) ⟨1519676, by rfl⟩ : syracuseStep 2026235 = 3039353) B3039353
theorem B6090065 : Blo 798342 6090065 := bstep (se 2 (by rfl) ⟨2283774, by rfl⟩ : syracuseStep 6090065 = 4567549) B4567549
theorem B4059881 : Blo 798342 4059881 := bstep (se 2 (by rfl) ⟨1522455, by rfl⟩ : syracuseStep 4059881 = 3044911) B3044911
theorem B49870343 : Blo 798342 49870343 := bstep (se 1 (by rfl) ⟨37402757, by rfl⟩ : syracuseStep 49870343 = 74805515) B74805515
theorem B32864231 : Blo 798342 32864231 := bstep (se 1 (by rfl) ⟨24648173, by rfl⟩ : syracuseStep 32864231 = 49296347) B49296347
theorem B6847739 : Blo 798342 6847739 := bstep (se 1 (by rfl) ⟨5135804, by rfl⟩ : syracuseStep 6847739 = 10271609) B10271609
theorem B30705479 : Blo 798342 30705479 := bstep (se 1 (by rfl) ⟨23029109, by rfl⟩ : syracuseStep 30705479 = 46058219) B46058219
theorem B1805183 : Blo 798342 1805183 := bstep (se 1 (by rfl) ⟨1353887, by rfl⟩ : syracuseStep 1805183 = 2707775) B2707775
theorem B7673453 : Blo 798342 7673453 := bstep (se 3 (by rfl) ⟨1438772, by rfl⟩ : syracuseStep 7673453 = 2877545) B2877545
theorem B1710047 : Blo 798342 1710047 := bstep (se 1 (by rfl) ⟨1282535, by rfl⟩ : syracuseStep 1710047 = 2565071) B2565071
theorem B1349959 : Blo 798342 1349959 := bstep (se 1 (by rfl) ⟨1012469, by rfl⟩ : syracuseStep 1349959 = 2024939) B2024939
theorem B1350823 : Blo 798342 1350823 := bstep (se 1 (by rfl) ⟨1013117, by rfl⟩ : syracuseStep 1350823 = 2026235) B2026235
theorem B2695463 : Blo 798342 2695463 := bstep (se 1 (by rfl) ⟨2021597, by rfl⟩ : syracuseStep 2695463 = 4043195) B4043195
theorem B3416489 : Blo 798342 3416489 := bstep (se 2 (by rfl) ⟨1281183, by rfl⟩ : syracuseStep 3416489 = 2562367) B2562367
theorem B5482217 : Blo 798342 5482217 := bstep (se 2 (by rfl) ⟨2055831, by rfl⟩ : syracuseStep 5482217 = 4111663) B4111663
theorem B4565159 : Blo 798342 4565159 := bstep (se 1 (by rfl) ⟨3423869, by rfl⟩ : syracuseStep 4565159 = 6847739) B6847739
theorem B3517607 : Blo 798342 3517607 := bstep (se 1 (by rfl) ⟨2638205, by rfl⟩ : syracuseStep 3517607 = 5276411) B5276411
theorem B6827267 : Blo 798342 6827267 := bstep (se 1 (by rfl) ⟨5120450, by rfl⟩ : syracuseStep 6827267 = 10240901) B10240901
theorem B799423 : Blo 798342 799423 := bstep (se 1 (by rfl) ⟨599567, by rfl⟩ : syracuseStep 799423 = 1199135) B1199135
theorem B799935 : Blo 798342 799935 := bstep (se 1 (by rfl) ⟨599951, by rfl⟩ : syracuseStep 799935 = 1199903) B1199903
theorem B1520831 : Blo 798342 1520831 := bstep (se 1 (by rfl) ⟨1140623, by rfl⟩ : syracuseStep 1520831 = 2281247) B2281247
theorem B800255 : Blo 798342 800255 := bstep (se 1 (by rfl) ⟨600191, by rfl⟩ : syracuseStep 800255 = 1200383) B1200383
theorem B898843 : Blo 798342 898843 := bstep (se 1 (by rfl) ⟨674132, by rfl⟩ : syracuseStep 898843 = 1348265) B1348265
theorem B800767 : Blo 798342 800767 := bstep (se 1 (by rfl) ⟨600575, by rfl⟩ : syracuseStep 800767 = 1201151) B1201151
theorem B800895 : Blo 798342 800895 := bstep (se 1 (by rfl) ⟨600671, by rfl⟩ : syracuseStep 800895 = 1201343) B1201343
theorem B801511 : Blo 798342 801511 := bstep (se 1 (by rfl) ⟨601133, by rfl⟩ : syracuseStep 801511 = 1202267) B1202267
theorem B4047407 : Blo 798342 4047407 := bstep (se 1 (by rfl) ⟨3035555, by rfl⟩ : syracuseStep 4047407 = 6071111) B6071111
theorem B902623 : Blo 798342 902623 := bstep (se 1 (by rfl) ⟨676967, by rfl⟩ : syracuseStep 902623 = 1353935) B1353935
theorem B2280403 : Blo 798342 2280403 := bstep (se 1 (by rfl) ⟨1710302, by rfl⟩ : syracuseStep 2280403 = 3420605) B3420605
theorem B2706587 : Blo 798342 2706587 := bstep (se 1 (by rfl) ⟨2029940, by rfl⟩ : syracuseStep 2706587 = 4059881) B4059881
theorem B33246895 : Blo 798342 33246895 := bstep (se 1 (by rfl) ⟨24935171, by rfl⟩ : syracuseStep 33246895 = 49870343) B49870343
theorem B21909487 : Blo 798342 21909487 := bstep (se 1 (by rfl) ⟨16432115, by rfl⟩ : syracuseStep 21909487 = 32864231) B32864231
theorem B1201289 : Blo 798342 1201289 := bstep (se 2 (by rfl) ⟨450483, by rfl⟩ : syracuseStep 1201289 = 900967) B900967
theorem B4052591 : Blo 798342 4052591 := bstep (se 1 (by rfl) ⟨3039443, by rfl⟩ : syracuseStep 4052591 = 6078887) B6078887
theorem B110810915 : Blo 798342 110810915 := bstep (se 1 (by rfl) ⟨83108186, by rfl⟩ : syracuseStep 110810915 = 166216373) B166216373
theorem B12802175 : Blo 798342 12802175 := bstep (se 1 (by rfl) ⟨9601631, by rfl⟩ : syracuseStep 12802175 = 19203263) B19203263
theorem B3037439 : Blo 798342 3037439 := bstep (se 1 (by rfl) ⟨2278079, by rfl⟩ : syracuseStep 3037439 = 4556159) B4556159
theorem B2021881 : Blo 798342 2021881 := bstep (se 2 (by rfl) ⟨758205, by rfl⟩ : syracuseStep 2021881 = 1516411) B1516411
theorem B2023451 : Blo 798342 2023451 := bstep (se 1 (by rfl) ⟨1517588, by rfl⟩ : syracuseStep 2023451 = 3035177) B3035177
theorem B1826887 : Blo 798342 1826887 := bstep (se 1 (by rfl) ⟨1370165, by rfl⟩ : syracuseStep 1826887 = 2740331) B2740331
theorem B4874735 : Blo 798342 4874735 := bstep (se 1 (by rfl) ⟨3656051, by rfl⟩ : syracuseStep 4874735 = 7312103) B7312103
theorem B2024635 : Blo 798342 2024635 := bstep (se 1 (by rfl) ⟨1518476, by rfl⟩ : syracuseStep 2024635 = 3036953) B3036953
theorem B5465555 : Blo 798342 5465555 := bstep (se 1 (by rfl) ⟨4099166, by rfl⟩ : syracuseStep 5465555 = 8198333) B8198333
theorem B1927081 : Blo 798342 1927081 := bstep (se 2 (by rfl) ⟨722655, by rfl⟩ : syracuseStep 1927081 = 1445311) B1445311
theorem B1796507 : Blo 798342 1796507 := bstep (se 1 (by rfl) ⟨1347380, by rfl⟩ : syracuseStep 1796507 = 2694761) B2694761
theorem B5138903 : Blo 798342 5138903 := bstep (se 1 (by rfl) ⟨3854177, by rfl⟩ : syracuseStep 5138903 = 7708355) B7708355
theorem B1796777 : Blo 798342 1796777 := bstep (se 2 (by rfl) ⟨673791, by rfl⟩ : syracuseStep 1796777 = 1347583) B1347583
theorem B35089321 : Blo 798342 35089321 := bstep (se 2 (by rfl) ⟨13158495, by rfl⟩ : syracuseStep 35089321 = 26316991) B26316991
theorem B2026579 : Blo 798342 2026579 := bstep (se 1 (by rfl) ⟨1519934, by rfl⟩ : syracuseStep 2026579 = 3039869) B3039869
theorem B4549871 : Blo 798342 4549871 := bstep (se 1 (by rfl) ⟨3412403, by rfl⟩ : syracuseStep 4549871 = 6824807) B6824807
theorem B1797371 : Blo 798342 1797371 := bstep (se 1 (by rfl) ⟨1348028, by rfl⟩ : syracuseStep 1797371 = 2696057) B2696057
theorem B1797839 : Blo 798342 1797839 := bstep (se 1 (by rfl) ⟨1348379, by rfl⟩ : syracuseStep 1797839 = 2696759) B2696759
theorem B4058909 : Blo 798342 4058909 := bstep (se 3 (by rfl) ⟨761045, by rfl⟩ : syracuseStep 4058909 = 1522091) B1522091
theorem B4060043 : Blo 798342 4060043 := bstep (se 1 (by rfl) ⟨3045032, by rfl⟩ : syracuseStep 4060043 = 6090065) B6090065
theorem B1799711 : Blo 798342 1799711 := bstep (se 1 (by rfl) ⟨1349783, by rfl⟩ : syracuseStep 1799711 = 2699567) B2699567
theorem B3242621 : Blo 798342 3242621 := bstep (se 3 (by rfl) ⟨607991, by rfl⟩ : syracuseStep 3242621 = 1215983) B1215983
theorem B1801979 : Blo 798342 1801979 := bstep (se 1 (by rfl) ⟨1351484, by rfl⟩ : syracuseStep 1801979 = 2702969) B2702969
theorem B1804391 : Blo 798342 1804391 := bstep (se 1 (by rfl) ⟨1353293, by rfl⟩ : syracuseStep 1804391 = 2706587) B2706587
theorem B5115635 : Blo 798342 5115635 := bstep (se 1 (by rfl) ⟨3836726, by rfl⟩ : syracuseStep 5115635 = 7673453) B7673453
theorem B1348967 : Blo 798342 1348967 := bstep (se 1 (by rfl) ⟨1011725, by rfl⟩ : syracuseStep 1348967 = 2023451) B2023451
theorem B3249823 : Blo 798342 3249823 := bstep (se 1 (by rfl) ⟨2437367, by rfl⟩ : syracuseStep 3249823 = 4874735) B4874735
theorem B3643703 : Blo 798342 3643703 := bstep (se 1 (by rfl) ⟨2732777, by rfl⟩ : syracuseStep 3643703 = 5465555) B5465555
theorem B13703741 : Blo 798342 13703741 := bstep (se 3 (by rfl) ⟨2569451, by rfl⟩ : syracuseStep 13703741 = 5138903) B5138903
theorem B2695841 : Blo 798342 2695841 := bstep (se 2 (by rfl) ⟨1010940, by rfl⟩ : syracuseStep 2695841 = 2021881) B2021881
theorem B2435849 : Blo 798342 2435849 := bstep (se 2 (by rfl) ⟨913443, by rfl⟩ : syracuseStep 2435849 = 1826887) B1826887
theorem B2698271 : Blo 798342 2698271 := bstep (se 1 (by rfl) ⟨2023703, by rfl⟩ : syracuseStep 2698271 = 4047407) B4047407
theorem B2699513 : Blo 798342 2699513 := bstep (se 2 (by rfl) ⟨1012317, by rfl⟩ : syracuseStep 2699513 = 2024635) B2024635
theorem B2569441 : Blo 798342 2569441 := bstep (se 2 (by rfl) ⟨963540, by rfl⟩ : syracuseStep 2569441 = 1927081) B1927081
theorem B800859 : Blo 798342 800859 := bstep (se 1 (by rfl) ⟨600644, by rfl⟩ : syracuseStep 800859 = 1201289) B1201289
theorem B2701727 : Blo 798342 2701727 := bstep (se 1 (by rfl) ⟨2026295, by rfl⟩ : syracuseStep 2701727 = 4052591) B4052591
theorem B73873943 : Blo 798342 73873943 := bstep (se 1 (by rfl) ⟨55405457, by rfl⟩ : syracuseStep 73873943 = 110810915) B110810915
theorem B8534783 : Blo 798342 8534783 := bstep (se 1 (by rfl) ⟨6401087, by rfl⟩ : syracuseStep 8534783 = 12802175) B12802175
theorem B2702105 : Blo 798342 2702105 := bstep (se 2 (by rfl) ⟨1013289, by rfl⟩ : syracuseStep 2702105 = 2026579) B2026579
theorem B29212649 : Blo 798342 29212649 := bstep (se 2 (by rfl) ⟨10954743, by rfl⟩ : syracuseStep 29212649 = 21909487) B21909487
theorem B2277659 : Blo 798342 2277659 := bstep (se 1 (by rfl) ⟨1708244, by rfl⟩ : syracuseStep 2277659 = 3416489) B3416489
theorem B3654811 : Blo 798342 3654811 := bstep (se 1 (by rfl) ⟨2741108, by rfl⟩ : syracuseStep 3654811 = 5482217) B5482217
theorem B1197671 : Blo 798342 1197671 := bstep (se 1 (by rfl) ⟨898253, by rfl⟩ : syracuseStep 1197671 = 1796507) B1796507
theorem B1197851 : Blo 798342 1197851 := bstep (se 1 (by rfl) ⟨898388, by rfl⟩ : syracuseStep 1197851 = 1796777) B1796777
theorem B2345071 : Blo 798342 2345071 := bstep (se 1 (by rfl) ⟨1758803, by rfl⟩ : syracuseStep 2345071 = 3517607) B3517607
theorem B3033247 : Blo 798342 3033247 := bstep (se 1 (by rfl) ⟨2274935, by rfl⟩ : syracuseStep 3033247 = 4549871) B4549871
theorem B1198247 : Blo 798342 1198247 := bstep (se 1 (by rfl) ⟨898685, by rfl⟩ : syracuseStep 1198247 = 1797371) B1797371
theorem B1198457 : Blo 798342 1198457 := bstep (se 2 (by rfl) ⟨449421, by rfl⟩ : syracuseStep 1198457 = 898843) B898843
theorem B1198559 : Blo 798342 1198559 := bstep (se 1 (by rfl) ⟨898919, by rfl⟩ : syracuseStep 1198559 = 1797839) B1797839
theorem B2705939 : Blo 798342 2705939 := bstep (se 1 (by rfl) ⟨2029454, by rfl⟩ : syracuseStep 2705939 = 4058909) B4058909
theorem B2706695 : Blo 798342 2706695 := bstep (se 1 (by rfl) ⟨2030021, by rfl⟩ : syracuseStep 2706695 = 4060043) B4060043
theorem B1199807 : Blo 798342 1199807 := bstep (se 1 (by rfl) ⟨899855, by rfl⟩ : syracuseStep 1199807 = 1799711) B1799711
theorem B1201319 : Blo 798342 1201319 := bstep (se 1 (by rfl) ⟨900989, by rfl⟩ : syracuseStep 1201319 = 1801979) B1801979
theorem B20470319 : Blo 798342 20470319 := bstep (se 1 (by rfl) ⟨15352739, by rfl⟩ : syracuseStep 20470319 = 30705479) B30705479
theorem B1203455 : Blo 798342 1203455 := bstep (se 1 (by rfl) ⟨902591, by rfl⟩ : syracuseStep 1203455 = 1805183) B1805183
theorem B1203497 : Blo 798342 1203497 := bstep (se 2 (by rfl) ⟨451311, by rfl⟩ : syracuseStep 1203497 = 902623) B902623
theorem B46785761 : Blo 798342 46785761 := bstep (se 2 (by rfl) ⟨17544660, by rfl⟩ : syracuseStep 46785761 = 35089321) B35089321
theorem B3040537 : Blo 798342 3040537 := bstep (se 2 (by rfl) ⟨1140201, by rfl⟩ : syracuseStep 3040537 = 2280403) B2280403
theorem B1140031 : Blo 798342 1140031 := bstep (se 1 (by rfl) ⟨855023, by rfl⟩ : syracuseStep 1140031 = 1710047) B1710047
theorem B2024959 : Blo 798342 2024959 := bstep (se 1 (by rfl) ⟨1518719, by rfl⟩ : syracuseStep 2024959 = 3037439) B3037439
theorem B44329193 : Blo 798342 44329193 := bstep (se 2 (by rfl) ⟨16623447, by rfl⟩ : syracuseStep 44329193 = 33246895) B33246895
theorem B1796975 : Blo 798342 1796975 := bstep (se 1 (by rfl) ⟨1347731, by rfl⟩ : syracuseStep 1796975 = 2695463) B2695463
theorem B3043439 : Blo 798342 3043439 := bstep (se 1 (by rfl) ⟨2282579, by rfl⟩ : syracuseStep 3043439 = 4565159) B4565159
theorem B4551511 : Blo 798342 4551511 := bstep (se 1 (by rfl) ⟨3413633, by rfl⟩ : syracuseStep 4551511 = 6827267) B6827267
theorem B1799945 : Blo 798342 1799945 := bstep (se 2 (by rfl) ⟨674979, by rfl⟩ : syracuseStep 1799945 = 1349959) B1349959
theorem B1013887 : Blo 798342 1013887 := bstep (se 1 (by rfl) ⟨760415, by rfl⟩ : syracuseStep 1013887 = 1520831) B1520831
theorem B1801097 : Blo 798342 1801097 := bstep (se 2 (by rfl) ⟨675411, by rfl⟩ : syracuseStep 1801097 = 1350823) B1350823
theorem B2161747 : Blo 798342 2161747 := bstep (se 1 (by rfl) ⟨1621310, by rfl⟩ : syracuseStep 2161747 = 3242621) B3242621
theorem B1803959 : Blo 798342 1803959 := bstep (se 1 (by rfl) ⟨1352969, by rfl⟩ : syracuseStep 1803959 = 2705939) B2705939
theorem B1804463 : Blo 798342 1804463 := bstep (se 1 (by rfl) ⟨1353347, by rfl⟩ : syracuseStep 1804463 = 2706695) B2706695
theorem B3410423 : Blo 798342 3410423 := bstep (se 1 (by rfl) ⟨2557817, by rfl⟩ : syracuseStep 3410423 = 5115635) B5115635
theorem B2429135 : Blo 798342 2429135 := bstep (se 1 (by rfl) ⟨1821851, by rfl⟩ : syracuseStep 2429135 = 3643703) B3643703
theorem B6068681 : Blo 798342 6068681 := bstep (se 2 (by rfl) ⟨2275755, by rfl⟩ : syracuseStep 6068681 = 4551511) B4551511
theorem B4333097 : Blo 798342 4333097 := bstep (se 2 (by rfl) ⟨1624911, by rfl⟩ : syracuseStep 4333097 = 3249823) B3249823
theorem B1351849 : Blo 798342 1351849 := bstep (se 2 (by rfl) ⟨506943, by rfl⟩ : syracuseStep 1351849 = 1013887) B1013887
theorem B19475099 : Blo 798342 19475099 := bstep (se 1 (by rfl) ⟨14606324, by rfl⟩ : syracuseStep 19475099 = 29212649) B29212649
theorem B1518439 : Blo 798342 1518439 := bstep (se 1 (by rfl) ⟨1138829, by rfl⟩ : syracuseStep 1518439 = 2277659) B2277659
theorem B798447 : Blo 798342 798447 := bstep (se 1 (by rfl) ⟨598835, by rfl⟩ : syracuseStep 798447 = 1197671) B1197671
theorem B798567 : Blo 798342 798567 := bstep (se 1 (by rfl) ⟨598925, by rfl⟩ : syracuseStep 798567 = 1197851) B1197851
theorem B798831 : Blo 798342 798831 := bstep (se 1 (by rfl) ⟨599123, by rfl⟩ : syracuseStep 798831 = 1198247) B1198247
theorem B798971 : Blo 798342 798971 := bstep (se 1 (by rfl) ⟨599228, by rfl⟩ : syracuseStep 798971 = 1198457) B1198457
theorem B799039 : Blo 798342 799039 := bstep (se 1 (by rfl) ⟨599279, by rfl⟩ : syracuseStep 799039 = 1198559) B1198559
theorem B1520041 : Blo 798342 1520041 := bstep (se 2 (by rfl) ⟨570015, by rfl⟩ : syracuseStep 1520041 = 1140031) B1140031
theorem B2699945 : Blo 798342 2699945 := bstep (se 2 (by rfl) ⟨1012479, by rfl⟩ : syracuseStep 2699945 = 2024959) B2024959
theorem B799871 : Blo 798342 799871 := bstep (se 1 (by rfl) ⟨599903, by rfl⟩ : syracuseStep 799871 = 1199807) B1199807
theorem B3126761 : Blo 798342 3126761 := bstep (se 2 (by rfl) ⟨1172535, by rfl⟩ : syracuseStep 3126761 = 2345071) B2345071
theorem B4044329 : Blo 798342 4044329 := bstep (se 2 (by rfl) ⟨1516623, by rfl⟩ : syracuseStep 4044329 = 3033247) B3033247
theorem B800879 : Blo 798342 800879 := bstep (se 1 (by rfl) ⟨600659, by rfl⟩ : syracuseStep 800879 = 1201319) B1201319
theorem B899311 : Blo 798342 899311 := bstep (se 1 (by rfl) ⟨674483, by rfl⟩ : syracuseStep 899311 = 1348967) B1348967
theorem B13646879 : Blo 798342 13646879 := bstep (se 1 (by rfl) ⟨10235159, by rfl⟩ : syracuseStep 13646879 = 20470319) B20470319
theorem B802303 : Blo 798342 802303 := bstep (se 1 (by rfl) ⟨601727, by rfl⟩ : syracuseStep 802303 = 1203455) B1203455
theorem B802331 : Blo 798342 802331 := bstep (se 1 (by rfl) ⟨601748, by rfl⟩ : syracuseStep 802331 = 1203497) B1203497
theorem B3425921 : Blo 798342 3425921 := bstep (se 2 (by rfl) ⟨1284720, by rfl⟩ : syracuseStep 3425921 = 2569441) B2569441
theorem B1623899 : Blo 798342 1623899 := bstep (se 1 (by rfl) ⟨1217924, by rfl⟩ : syracuseStep 1623899 = 2435849) B2435849
theorem B1197983 : Blo 798342 1197983 := bstep (se 1 (by rfl) ⟨898487, by rfl⟩ : syracuseStep 1197983 = 1796975) B1796975
theorem B1199963 : Blo 798342 1199963 := bstep (se 1 (by rfl) ⟨899972, by rfl⟩ : syracuseStep 1199963 = 1799945) B1799945
theorem B5689855 : Blo 798342 5689855 := bstep (se 1 (by rfl) ⟨4267391, by rfl⟩ : syracuseStep 5689855 = 8534783) B8534783
theorem B1200731 : Blo 798342 1200731 := bstep (se 1 (by rfl) ⟨900548, by rfl⟩ : syracuseStep 1200731 = 1801097) B1801097
theorem B1202927 : Blo 798342 1202927 := bstep (se 1 (by rfl) ⟨902195, by rfl⟩ : syracuseStep 1202927 = 1804391) B1804391
theorem B4873081 : Blo 798342 4873081 := bstep (se 2 (by rfl) ⟨1827405, by rfl⟩ : syracuseStep 4873081 = 3654811) B3654811
theorem B4054049 : Blo 798342 4054049 := bstep (se 2 (by rfl) ⟨1520268, by rfl⟩ : syracuseStep 4054049 = 3040537) B3040537
theorem B9135827 : Blo 798342 9135827 := bstep (se 1 (by rfl) ⟨6851870, by rfl⟩ : syracuseStep 9135827 = 13703741) B13703741
theorem B11529317 : Blo 798342 11529317 := bstep (se 4 (by rfl) ⟨1080873, by rfl⟩ : syracuseStep 11529317 = 2161747) B2161747
theorem B1797227 : Blo 798342 1797227 := bstep (se 1 (by rfl) ⟨1347920, by rfl⟩ : syracuseStep 1797227 = 2695841) B2695841
theorem B31190507 : Blo 798342 31190507 := bstep (se 1 (by rfl) ⟨23392880, by rfl⟩ : syracuseStep 31190507 = 46785761) B46785761
theorem B29552795 : Blo 798342 29552795 := bstep (se 1 (by rfl) ⟨22164596, by rfl⟩ : syracuseStep 29552795 = 44329193) B44329193
theorem B1798847 : Blo 798342 1798847 := bstep (se 1 (by rfl) ⟨1349135, by rfl⟩ : syracuseStep 1798847 = 2698271) B2698271
theorem B2028959 : Blo 798342 2028959 := bstep (se 1 (by rfl) ⟨1521719, by rfl⟩ : syracuseStep 2028959 = 3043439) B3043439
theorem B1799675 : Blo 798342 1799675 := bstep (se 1 (by rfl) ⟨1349756, by rfl⟩ : syracuseStep 1799675 = 2699513) B2699513
theorem B1801151 : Blo 798342 1801151 := bstep (se 1 (by rfl) ⟨1350863, by rfl⟩ : syracuseStep 1801151 = 2701727) B2701727
theorem B49249295 : Blo 798342 49249295 := bstep (se 1 (by rfl) ⟨36936971, by rfl⟩ : syracuseStep 49249295 = 73873943) B73873943
theorem B1801403 : Blo 798342 1801403 := bstep (se 1 (by rfl) ⟨1351052, by rfl⟩ : syracuseStep 1801403 = 2702105) B2702105
theorem B1802465 : Blo 798342 1802465 := bstep (se 2 (by rfl) ⟨675924, by rfl⟩ : syracuseStep 1802465 = 1351849) B1351849
theorem B4330397 : Blo 798342 4330397 := bstep (se 3 (by rfl) ⟨811949, by rfl⟩ : syracuseStep 4330397 = 1623899) B1623899
theorem B2888731 : Blo 798342 2888731 := bstep (se 1 (by rfl) ⟨2166548, by rfl⟩ : syracuseStep 2888731 = 4333097) B4333097
theorem B12983399 : Blo 798342 12983399 := bstep (se 1 (by rfl) ⟨9737549, by rfl⟩ : syracuseStep 12983399 = 19475099) B19475099
theorem B19701863 : Blo 798342 19701863 := bstep (se 1 (by rfl) ⟨14776397, by rfl⟩ : syracuseStep 19701863 = 29552795) B29552795
theorem B30744845 : Blo 798342 30744845 := bstep (se 3 (by rfl) ⟨5764658, by rfl⟩ : syracuseStep 30744845 = 11529317) B11529317
theorem B1352639 : Blo 798342 1352639 := bstep (se 1 (by rfl) ⟨1014479, by rfl⟩ : syracuseStep 1352639 = 2028959) B2028959
theorem B2696219 : Blo 798342 2696219 := bstep (se 1 (by rfl) ⟨2022164, by rfl⟩ : syracuseStep 2696219 = 4044329) B4044329
theorem B6497441 : Blo 798342 6497441 := bstep (se 2 (by rfl) ⟨2436540, by rfl⟩ : syracuseStep 6497441 = 4873081) B4873081
theorem B798655 : Blo 798342 798655 := bstep (se 1 (by rfl) ⟨598991, by rfl⟩ : syracuseStep 798655 = 1197983) B1197983
theorem B2273615 : Blo 798342 2273615 := bstep (se 1 (by rfl) ⟨1705211, by rfl⟩ : syracuseStep 2273615 = 3410423) B3410423
theorem B799975 : Blo 798342 799975 := bstep (se 1 (by rfl) ⟨599981, by rfl⟩ : syracuseStep 799975 = 1199963) B1199963
theorem B1619423 : Blo 798342 1619423 := bstep (se 1 (by rfl) ⟨1214567, by rfl⟩ : syracuseStep 1619423 = 2429135) B2429135
theorem B800487 : Blo 798342 800487 := bstep (se 1 (by rfl) ⟨600365, by rfl⟩ : syracuseStep 800487 = 1200731) B1200731
theorem B4045787 : Blo 798342 4045787 := bstep (se 1 (by rfl) ⟨3034340, by rfl⟩ : syracuseStep 4045787 = 6068681) B6068681
theorem B801951 : Blo 798342 801951 := bstep (se 1 (by rfl) ⟨601463, by rfl⟩ : syracuseStep 801951 = 1202927) B1202927
theorem B2702699 : Blo 798342 2702699 := bstep (se 1 (by rfl) ⟨2027024, by rfl⟩ : syracuseStep 2702699 = 4054049) B4054049
theorem B7586473 : Blo 798342 7586473 := bstep (se 2 (by rfl) ⟨2844927, by rfl⟩ : syracuseStep 7586473 = 5689855) B5689855
theorem B1198151 : Blo 798342 1198151 := bstep (se 1 (by rfl) ⟨898613, by rfl⟩ : syracuseStep 1198151 = 1797227) B1797227
theorem B20793671 : Blo 798342 20793671 := bstep (se 1 (by rfl) ⟨15595253, by rfl⟩ : syracuseStep 20793671 = 31190507) B31190507
theorem B1199081 : Blo 798342 1199081 := bstep (se 2 (by rfl) ⟨449655, by rfl⟩ : syracuseStep 1199081 = 899311) B899311
theorem B1199231 : Blo 798342 1199231 := bstep (se 1 (by rfl) ⟨899423, by rfl⟩ : syracuseStep 1199231 = 1798847) B1798847
theorem B2084507 : Blo 798342 2084507 := bstep (se 1 (by rfl) ⟨1563380, by rfl⟩ : syracuseStep 2084507 = 3126761) B3126761
theorem B1199783 : Blo 798342 1199783 := bstep (se 1 (by rfl) ⟨899837, by rfl⟩ : syracuseStep 1199783 = 1799675) B1799675
theorem B1200767 : Blo 798342 1200767 := bstep (se 1 (by rfl) ⟨900575, by rfl⟩ : syracuseStep 1200767 = 1801151) B1801151
theorem B9097919 : Blo 798342 9097919 := bstep (se 1 (by rfl) ⟨6823439, by rfl⟩ : syracuseStep 9097919 = 13646879) B13646879
theorem B1200935 : Blo 798342 1200935 := bstep (se 1 (by rfl) ⟨900701, by rfl⟩ : syracuseStep 1200935 = 1801403) B1801403
theorem B2283947 : Blo 798342 2283947 := bstep (se 1 (by rfl) ⟨1712960, by rfl⟩ : syracuseStep 2283947 = 3425921) B3425921
theorem B1202639 : Blo 798342 1202639 := bstep (se 1 (by rfl) ⟨901979, by rfl⟩ : syracuseStep 1202639 = 1803959) B1803959
theorem B1202975 : Blo 798342 1202975 := bstep (se 1 (by rfl) ⟨902231, by rfl⟩ : syracuseStep 1202975 = 1804463) B1804463
theorem B2024585 : Blo 798342 2024585 := bstep (se 2 (by rfl) ⟨759219, by rfl⟩ : syracuseStep 2024585 = 1518439) B1518439
theorem B2026721 : Blo 798342 2026721 := bstep (se 2 (by rfl) ⟨760020, by rfl⟩ : syracuseStep 2026721 = 1520041) B1520041
theorem B6090551 : Blo 798342 6090551 := bstep (se 1 (by rfl) ⟨4567913, by rfl⟩ : syracuseStep 6090551 = 9135827) B9135827
theorem B1799963 : Blo 798342 1799963 := bstep (se 1 (by rfl) ⟨1349972, by rfl⟩ : syracuseStep 1799963 = 2699945) B2699945
theorem B32832863 : Blo 798342 32832863 := bstep (se 1 (by rfl) ⟨24624647, by rfl⟩ : syracuseStep 32832863 = 49249295) B49249295
theorem B13862447 : Blo 798342 13862447 := bstep (se 1 (by rfl) ⟨10396835, by rfl⟩ : syracuseStep 13862447 = 20793671) B20793671
theorem B6065279 : Blo 798342 6065279 := bstep (se 1 (by rfl) ⟨4548959, by rfl⟩ : syracuseStep 6065279 = 9097919) B9097919
theorem B2886931 : Blo 798342 2886931 := bstep (se 1 (by rfl) ⟨2165198, by rfl⟩ : syracuseStep 2886931 = 4330397) B4330397
theorem B8655599 : Blo 798342 8655599 := bstep (se 1 (by rfl) ⟨6491699, by rfl⟩ : syracuseStep 8655599 = 12983399) B12983399
theorem B1349723 : Blo 798342 1349723 := bstep (se 1 (by rfl) ⟨1012292, by rfl⟩ : syracuseStep 1349723 = 2024585) B2024585
theorem B4331627 : Blo 798342 4331627 := bstep (se 1 (by rfl) ⟨3248720, by rfl⟩ : syracuseStep 4331627 = 6497441) B6497441
theorem B1351147 : Blo 798342 1351147 := bstep (se 1 (by rfl) ⟨1013360, by rfl⟩ : syracuseStep 1351147 = 2026721) B2026721
theorem B1515743 : Blo 798342 1515743 := bstep (se 1 (by rfl) ⟨1136807, by rfl⟩ : syracuseStep 1515743 = 2273615) B2273615
theorem B2697191 : Blo 798342 2697191 := bstep (se 1 (by rfl) ⟨2022893, by rfl⟩ : syracuseStep 2697191 = 4045787) B4045787
theorem B798767 : Blo 798342 798767 := bstep (se 1 (by rfl) ⟨599075, by rfl⟩ : syracuseStep 798767 = 1198151) B1198151
theorem B799387 : Blo 798342 799387 := bstep (se 1 (by rfl) ⟨599540, by rfl⟩ : syracuseStep 799387 = 1199081) B1199081
theorem B799487 : Blo 798342 799487 := bstep (se 1 (by rfl) ⟨599615, by rfl⟩ : syracuseStep 799487 = 1199231) B1199231
theorem B1389671 : Blo 798342 1389671 := bstep (se 1 (by rfl) ⟨1042253, by rfl⟩ : syracuseStep 1389671 = 2084507) B2084507
theorem B799855 : Blo 798342 799855 := bstep (se 1 (by rfl) ⟨599891, by rfl⟩ : syracuseStep 799855 = 1199783) B1199783
theorem B800511 : Blo 798342 800511 := bstep (se 1 (by rfl) ⟨600383, by rfl⟩ : syracuseStep 800511 = 1200767) B1200767
theorem B800623 : Blo 798342 800623 := bstep (se 1 (by rfl) ⟨600467, by rfl⟩ : syracuseStep 800623 = 1200935) B1200935
theorem B1522631 : Blo 798342 1522631 := bstep (se 1 (by rfl) ⟨1141973, by rfl⟩ : syracuseStep 1522631 = 2283947) B2283947
theorem B801759 : Blo 798342 801759 := bstep (se 1 (by rfl) ⟨601319, by rfl⟩ : syracuseStep 801759 = 1202639) B1202639
theorem B801983 : Blo 798342 801983 := bstep (se 1 (by rfl) ⟨601487, by rfl⟩ : syracuseStep 801983 = 1202975) B1202975
theorem B20496563 : Blo 798342 20496563 := bstep (se 1 (by rfl) ⟨15372422, by rfl⟩ : syracuseStep 20496563 = 30744845) B30744845
theorem B901759 : Blo 798342 901759 := bstep (se 1 (by rfl) ⟨676319, by rfl⟩ : syracuseStep 901759 = 1352639) B1352639
theorem B3851641 : Blo 798342 3851641 := bstep (se 2 (by rfl) ⟨1444365, by rfl⟩ : syracuseStep 3851641 = 2888731) B2888731
theorem B1199975 : Blo 798342 1199975 := bstep (se 1 (by rfl) ⟨899981, by rfl⟩ : syracuseStep 1199975 = 1799963) B1799963
theorem B1201643 : Blo 798342 1201643 := bstep (se 1 (by rfl) ⟨901232, by rfl⟩ : syracuseStep 1201643 = 1802465) B1802465
theorem B10115297 : Blo 798342 10115297 := bstep (se 2 (by rfl) ⟨3793236, by rfl⟩ : syracuseStep 10115297 = 7586473) B7586473
theorem B13134575 : Blo 798342 13134575 := bstep (se 1 (by rfl) ⟨9850931, by rfl⟩ : syracuseStep 13134575 = 19701863) B19701863
theorem B1797479 : Blo 798342 1797479 := bstep (se 1 (by rfl) ⟨1348109, by rfl⟩ : syracuseStep 1797479 = 2696219) B2696219
theorem B4060367 : Blo 798342 4060367 := bstep (se 1 (by rfl) ⟨3045275, by rfl⟩ : syracuseStep 4060367 = 6090551) B6090551
theorem B1079615 : Blo 798342 1079615 := bstep (se 1 (by rfl) ⟨809711, by rfl⟩ : syracuseStep 1079615 = 1619423) B1619423
theorem B21888575 : Blo 798342 21888575 := bstep (se 1 (by rfl) ⟨16416431, by rfl⟩ : syracuseStep 21888575 = 32832863) B32832863
theorem B1801799 : Blo 798342 1801799 := bstep (se 1 (by rfl) ⟨1351349, by rfl⟩ : syracuseStep 1801799 = 2702699) B2702699
theorem B13664375 : Blo 798342 13664375 := bstep (se 1 (by rfl) ⟨10248281, by rfl⟩ : syracuseStep 13664375 = 20496563) B20496563
theorem B9241631 : Blo 798342 9241631 := bstep (se 1 (by rfl) ⟨6931223, by rfl⟩ : syracuseStep 9241631 = 13862447) B13862447
theorem B2887751 : Blo 798342 2887751 := bstep (se 1 (by rfl) ⟨2165813, by rfl⟩ : syracuseStep 2887751 = 4331627) B4331627
theorem B8756383 : Blo 798342 8756383 := bstep (se 1 (by rfl) ⟨6567287, by rfl⟩ : syracuseStep 8756383 = 13134575) B13134575
theorem B926447 : Blo 798342 926447 := bstep (se 1 (by rfl) ⟨694835, by rfl⟩ : syracuseStep 926447 = 1389671) B1389671
theorem B14592383 : Blo 798342 14592383 := bstep (se 1 (by rfl) ⟨10944287, by rfl⟩ : syracuseStep 14592383 = 21888575) B21888575
theorem B23081597 : Blo 798342 23081597 := bstep (se 3 (by rfl) ⟨4327799, by rfl⟩ : syracuseStep 23081597 = 8655599) B8655599
theorem B4043519 : Blo 798342 4043519 := bstep (se 1 (by rfl) ⟨3032639, by rfl⟩ : syracuseStep 4043519 = 6065279) B6065279
theorem B799983 : Blo 798342 799983 := bstep (se 1 (by rfl) ⟨599987, by rfl⟩ : syracuseStep 799983 = 1199975) B1199975
theorem B801095 : Blo 798342 801095 := bstep (se 1 (by rfl) ⟨600821, by rfl⟩ : syracuseStep 801095 = 1201643) B1201643
theorem B899815 : Blo 798342 899815 := bstep (se 1 (by rfl) ⟨674861, by rfl⟩ : syracuseStep 899815 = 1349723) B1349723
theorem B3849241 : Blo 798342 3849241 := bstep (se 2 (by rfl) ⟨1443465, by rfl⟩ : syracuseStep 3849241 = 2886931) B2886931
theorem B1198319 : Blo 798342 1198319 := bstep (se 1 (by rfl) ⟨898739, by rfl⟩ : syracuseStep 1198319 = 1797479) B1797479
theorem B2706911 : Blo 798342 2706911 := bstep (se 1 (by rfl) ⟨2030183, by rfl⟩ : syracuseStep 2706911 = 4060367) B4060367
theorem B1201199 : Blo 798342 1201199 := bstep (se 1 (by rfl) ⟨900899, by rfl⟩ : syracuseStep 1201199 = 1801799) B1801799
theorem B1202345 : Blo 798342 1202345 := bstep (se 2 (by rfl) ⟨450879, by rfl⟩ : syracuseStep 1202345 = 901759) B901759
theorem B5135521 : Blo 798342 5135521 := bstep (se 2 (by rfl) ⟨1925820, by rfl⟩ : syracuseStep 5135521 = 3851641) B3851641
theorem B6743531 : Blo 798342 6743531 := bstep (se 1 (by rfl) ⟨5057648, by rfl⟩ : syracuseStep 6743531 = 10115297) B10115297
theorem B1010495 : Blo 798342 1010495 := bstep (se 1 (by rfl) ⟨757871, by rfl⟩ : syracuseStep 1010495 = 1515743) B1515743
theorem B2878973 : Blo 798342 2878973 := bstep (se 3 (by rfl) ⟨539807, by rfl⟩ : syracuseStep 2878973 = 1079615) B1079615
theorem B1798127 : Blo 798342 1798127 := bstep (se 1 (by rfl) ⟨1348595, by rfl⟩ : syracuseStep 1798127 = 2697191) B2697191
theorem B1015087 : Blo 798342 1015087 := bstep (se 1 (by rfl) ⟨761315, by rfl⟩ : syracuseStep 1015087 = 1522631) B1522631
theorem B1801529 : Blo 798342 1801529 := bstep (se 2 (by rfl) ⟨675573, by rfl⟩ : syracuseStep 1801529 = 1351147) B1351147
theorem B9109583 : Blo 798342 9109583 := bstep (se 1 (by rfl) ⟨6832187, by rfl⟩ : syracuseStep 9109583 = 13664375) B13664375
theorem B7700669 : Blo 798342 7700669 := bstep (se 3 (by rfl) ⟨1443875, by rfl⟩ : syracuseStep 7700669 = 2887751) B2887751
theorem B6161087 : Blo 798342 6161087 := bstep (se 1 (by rfl) ⟨4620815, by rfl⟩ : syracuseStep 6161087 = 9241631) B9241631
theorem B1804607 : Blo 798342 1804607 := bstep (se 1 (by rfl) ⟨1353455, by rfl⟩ : syracuseStep 1804607 = 2706911) B2706911
theorem B2694653 : Blo 798342 2694653 := bstep (se 3 (by rfl) ⟨505247, by rfl⟩ : syracuseStep 2694653 = 1010495) B1010495
theorem B2695679 : Blo 798342 2695679 := bstep (se 1 (by rfl) ⟨2021759, by rfl⟩ : syracuseStep 2695679 = 4043519) B4043519
theorem B11675177 : Blo 798342 11675177 := bstep (se 2 (by rfl) ⟨4378191, by rfl⟩ : syracuseStep 11675177 = 8756383) B8756383
theorem B1353449 : Blo 798342 1353449 := bstep (se 2 (by rfl) ⟨507543, by rfl⟩ : syracuseStep 1353449 = 1015087) B1015087
theorem B798879 : Blo 798342 798879 := bstep (se 1 (by rfl) ⟨599159, by rfl⟩ : syracuseStep 798879 = 1198319) B1198319
theorem B800799 : Blo 798342 800799 := bstep (se 1 (by rfl) ⟨600599, by rfl⟩ : syracuseStep 800799 = 1201199) B1201199
theorem B801563 : Blo 798342 801563 := bstep (se 1 (by rfl) ⟨601172, by rfl⟩ : syracuseStep 801563 = 1202345) B1202345
theorem B1919315 : Blo 798342 1919315 := bstep (se 1 (by rfl) ⟨1439486, by rfl⟩ : syracuseStep 1919315 = 2878973) B2878973
theorem B9882101 : Blo 798342 9882101 := bstep (se 5 (by rfl) ⟨463223, by rfl⟩ : syracuseStep 9882101 = 926447) B926447
theorem B1198751 : Blo 798342 1198751 := bstep (se 1 (by rfl) ⟨899063, by rfl⟩ : syracuseStep 1198751 = 1798127) B1798127
theorem B15387731 : Blo 798342 15387731 := bstep (se 1 (by rfl) ⟨11540798, by rfl⟩ : syracuseStep 15387731 = 23081597) B23081597
theorem B1199753 : Blo 798342 1199753 := bstep (se 2 (by rfl) ⟨449907, by rfl⟩ : syracuseStep 1199753 = 899815) B899815
theorem B5132321 : Blo 798342 5132321 := bstep (se 2 (by rfl) ⟨1924620, by rfl⟩ : syracuseStep 5132321 = 3849241) B3849241
theorem B1201019 : Blo 798342 1201019 := bstep (se 1 (by rfl) ⟨900764, by rfl⟩ : syracuseStep 1201019 = 1801529) B1801529
theorem B17982749 : Blo 798342 17982749 := bstep (se 3 (by rfl) ⟨3371765, by rfl⟩ : syracuseStep 17982749 = 6743531) B6743531
theorem B9728255 : Blo 798342 9728255 := bstep (se 1 (by rfl) ⟨7296191, by rfl⟩ : syracuseStep 9728255 = 14592383) B14592383
theorem B6847361 : Blo 798342 6847361 := bstep (se 2 (by rfl) ⟨2567760, by rfl⟩ : syracuseStep 6847361 = 5135521) B5135521
theorem B6588067 : Blo 798342 6588067 := bstep (se 1 (by rfl) ⟨4941050, by rfl⟩ : syracuseStep 6588067 = 9882101) B9882101
theorem B10258487 : Blo 798342 10258487 := bstep (se 1 (by rfl) ⟨7693865, by rfl⟩ : syracuseStep 10258487 = 15387731) B15387731
theorem B5118173 : Blo 798342 5118173 := bstep (se 3 (by rfl) ⟨959657, by rfl⟩ : syracuseStep 5118173 = 1919315) B1919315
theorem B4564907 : Blo 798342 4564907 := bstep (se 1 (by rfl) ⟨3423680, by rfl⟩ : syracuseStep 4564907 = 6847361) B6847361
theorem B6073055 : Blo 798342 6073055 := bstep (se 1 (by rfl) ⟨4554791, by rfl⟩ : syracuseStep 6073055 = 9109583) B9109583
theorem B4107391 : Blo 798342 4107391 := bstep (se 1 (by rfl) ⟨3080543, by rfl⟩ : syracuseStep 4107391 = 6161087) B6161087
theorem B799167 : Blo 798342 799167 := bstep (se 1 (by rfl) ⟨599375, by rfl⟩ : syracuseStep 799167 = 1198751) B1198751
theorem B799835 : Blo 798342 799835 := bstep (se 1 (by rfl) ⟨599876, by rfl⟩ : syracuseStep 799835 = 1199753) B1199753
theorem B3421547 : Blo 798342 3421547 := bstep (se 1 (by rfl) ⟨2566160, by rfl⟩ : syracuseStep 3421547 = 5132321) B5132321
theorem B800679 : Blo 798342 800679 := bstep (se 1 (by rfl) ⟨600509, by rfl⟩ : syracuseStep 800679 = 1201019) B1201019
theorem B7783451 : Blo 798342 7783451 := bstep (se 1 (by rfl) ⟨5837588, by rfl⟩ : syracuseStep 7783451 = 11675177) B11675177
theorem B902299 : Blo 798342 902299 := bstep (se 1 (by rfl) ⟨676724, by rfl⟩ : syracuseStep 902299 = 1353449) B1353449
theorem B5133779 : Blo 798342 5133779 := bstep (se 1 (by rfl) ⟨3850334, by rfl⟩ : syracuseStep 5133779 = 7700669) B7700669
theorem B1203071 : Blo 798342 1203071 := bstep (se 1 (by rfl) ⟨902303, by rfl⟩ : syracuseStep 1203071 = 1804607) B1804607
theorem B1796435 : Blo 798342 1796435 := bstep (se 1 (by rfl) ⟨1347326, by rfl⟩ : syracuseStep 1796435 = 2694653) B2694653
theorem B1797119 : Blo 798342 1797119 := bstep (se 1 (by rfl) ⟨1347839, by rfl⟩ : syracuseStep 1797119 = 2695679) B2695679
theorem B11988499 : Blo 798342 11988499 := bstep (se 1 (by rfl) ⟨8991374, by rfl⟩ : syracuseStep 11988499 = 17982749) B17982749
theorem B6485503 : Blo 798342 6485503 := bstep (se 1 (by rfl) ⟨4864127, by rfl⟩ : syracuseStep 6485503 = 9728255) B9728255
theorem B8784089 : Blo 798342 8784089 := bstep (se 2 (by rfl) ⟨3294033, by rfl⟩ : syracuseStep 8784089 = 6588067) B6588067
theorem B87624341 : Blo 798342 87624341 := bstep (se 6 (by rfl) ⟨2053695, by rfl⟩ : syracuseStep 87624341 = 4107391) B4107391
theorem B3412115 : Blo 798342 3412115 := bstep (se 1 (by rfl) ⟨2559086, by rfl⟩ : syracuseStep 3412115 = 5118173) B5118173
theorem B5188967 : Blo 798342 5188967 := bstep (se 1 (by rfl) ⟨3891725, by rfl⟩ : syracuseStep 5188967 = 7783451) B7783451
theorem B3422519 : Blo 798342 3422519 := bstep (se 1 (by rfl) ⟨2566889, by rfl⟩ : syracuseStep 3422519 = 5133779) B5133779
theorem B802047 : Blo 798342 802047 := bstep (se 1 (by rfl) ⟨601535, by rfl⟩ : syracuseStep 802047 = 1203071) B1203071
theorem B1197623 : Blo 798342 1197623 := bstep (se 1 (by rfl) ⟨898217, by rfl⟩ : syracuseStep 1197623 = 1796435) B1796435
theorem B4048703 : Blo 798342 4048703 := bstep (se 1 (by rfl) ⟨3036527, by rfl⟩ : syracuseStep 4048703 = 6073055) B6073055
theorem B1198079 : Blo 798342 1198079 := bstep (se 1 (by rfl) ⟨898559, by rfl⟩ : syracuseStep 1198079 = 1797119) B1797119
theorem B2281031 : Blo 798342 2281031 := bstep (se 1 (by rfl) ⟨1710773, by rfl⟩ : syracuseStep 2281031 = 3421547) B3421547
theorem B6838991 : Blo 798342 6838991 := bstep (se 1 (by rfl) ⟨5129243, by rfl⟩ : syracuseStep 6838991 = 10258487) B10258487
theorem B1203065 : Blo 798342 1203065 := bstep (se 2 (by rfl) ⟨451149, by rfl⟩ : syracuseStep 1203065 = 902299) B902299
theorem B15984665 : Blo 798342 15984665 := bstep (se 2 (by rfl) ⟨5994249, by rfl⟩ : syracuseStep 15984665 = 11988499) B11988499
theorem B3043271 : Blo 798342 3043271 := bstep (se 1 (by rfl) ⟨2282453, by rfl⟩ : syracuseStep 3043271 = 4564907) B4564907
theorem B8647337 : Blo 798342 8647337 := bstep (se 2 (by rfl) ⟨3242751, by rfl⟩ : syracuseStep 8647337 = 6485503) B6485503
theorem B4559327 : Blo 798342 4559327 := bstep (se 1 (by rfl) ⟨3419495, by rfl⟩ : syracuseStep 4559327 = 6838991) B6838991
theorem B10656443 : Blo 798342 10656443 := bstep (se 1 (by rfl) ⟨7992332, by rfl⟩ : syracuseStep 10656443 = 15984665) B15984665
theorem B798415 : Blo 798342 798415 := bstep (se 1 (by rfl) ⟨598811, by rfl⟩ : syracuseStep 798415 = 1197623) B1197623
theorem B2699135 : Blo 798342 2699135 := bstep (se 1 (by rfl) ⟨2024351, by rfl⟩ : syracuseStep 2699135 = 4048703) B4048703
theorem B798719 : Blo 798342 798719 := bstep (se 1 (by rfl) ⟨599039, by rfl⟩ : syracuseStep 798719 = 1198079) B1198079
theorem B1520687 : Blo 798342 1520687 := bstep (se 1 (by rfl) ⟨1140515, by rfl⟩ : syracuseStep 1520687 = 2281031) B2281031
theorem B2274743 : Blo 798342 2274743 := bstep (se 1 (by rfl) ⟨1706057, by rfl⟩ : syracuseStep 2274743 = 3412115) B3412115
theorem B802043 : Blo 798342 802043 := bstep (se 1 (by rfl) ⟨601532, by rfl⟩ : syracuseStep 802043 = 1203065) B1203065
theorem B3459311 : Blo 798342 3459311 := bstep (se 1 (by rfl) ⟨2594483, by rfl⟩ : syracuseStep 3459311 = 5188967) B5188967
theorem B2281679 : Blo 798342 2281679 := bstep (se 1 (by rfl) ⟨1711259, by rfl⟩ : syracuseStep 2281679 = 3422519) B3422519
theorem B5856059 : Blo 798342 5856059 := bstep (se 1 (by rfl) ⟨4392044, by rfl⟩ : syracuseStep 5856059 = 8784089) B8784089
theorem B58416227 : Blo 798342 58416227 := bstep (se 1 (by rfl) ⟨43812170, by rfl⟩ : syracuseStep 58416227 = 87624341) B87624341
theorem B2028847 : Blo 798342 2028847 := bstep (se 1 (by rfl) ⟨1521635, by rfl⟩ : syracuseStep 2028847 = 3043271) B3043271
theorem B5764891 : Blo 798342 5764891 := bstep (se 1 (by rfl) ⟨4323668, by rfl⟩ : syracuseStep 5764891 = 8647337) B8647337
theorem B3904039 : Blo 798342 3904039 := bstep (se 1 (by rfl) ⟨2928029, by rfl⟩ : syracuseStep 3904039 = 5856059) B5856059
theorem B1516495 : Blo 798342 1516495 := bstep (se 1 (by rfl) ⟨1137371, by rfl⟩ : syracuseStep 1516495 = 2274743) B2274743
theorem B2306207 : Blo 798342 2306207 := bstep (se 1 (by rfl) ⟨1729655, by rfl⟩ : syracuseStep 2306207 = 3459311) B3459311
theorem B1521119 : Blo 798342 1521119 := bstep (se 1 (by rfl) ⟨1140839, by rfl⟩ : syracuseStep 1521119 = 2281679) B2281679
theorem B38944151 : Blo 798342 38944151 := bstep (se 1 (by rfl) ⟨29208113, by rfl⟩ : syracuseStep 38944151 = 58416227) B58416227
theorem B2705129 : Blo 798342 2705129 := bstep (se 2 (by rfl) ⟨1014423, by rfl⟩ : syracuseStep 2705129 = 2028847) B2028847
theorem B7686521 : Blo 798342 7686521 := bstep (se 2 (by rfl) ⟨2882445, by rfl⟩ : syracuseStep 7686521 = 5764891) B5764891
theorem B3039551 : Blo 798342 3039551 := bstep (se 1 (by rfl) ⟨2279663, by rfl⟩ : syracuseStep 3039551 = 4559327) B4559327
theorem B7104295 : Blo 798342 7104295 := bstep (se 1 (by rfl) ⟨5328221, by rfl⟩ : syracuseStep 7104295 = 10656443) B10656443
theorem B1799423 : Blo 798342 1799423 := bstep (se 1 (by rfl) ⟨1349567, by rfl⟩ : syracuseStep 1799423 = 2699135) B2699135
theorem B1013791 : Blo 798342 1013791 := bstep (se 1 (by rfl) ⟨760343, by rfl⟩ : syracuseStep 1013791 = 1520687) B1520687
theorem B1803419 : Blo 798342 1803419 := bstep (se 1 (by rfl) ⟨1352564, by rfl⟩ : syracuseStep 1803419 = 2705129) B2705129
theorem B9472393 : Blo 798342 9472393 := bstep (se 2 (by rfl) ⟨3552147, by rfl⟩ : syracuseStep 9472393 = 7104295) B7104295
theorem B1351721 : Blo 798342 1351721 := bstep (se 2 (by rfl) ⟨506895, by rfl⟩ : syracuseStep 1351721 = 1013791) B1013791
theorem B25962767 : Blo 798342 25962767 := bstep (se 1 (by rfl) ⟨19472075, by rfl⟩ : syracuseStep 25962767 = 38944151) B38944151
theorem B5124347 : Blo 798342 5124347 := bstep (se 1 (by rfl) ⟨3843260, by rfl⟩ : syracuseStep 5124347 = 7686521) B7686521
theorem B1199615 : Blo 798342 1199615 := bstep (se 1 (by rfl) ⟨899711, by rfl⟩ : syracuseStep 1199615 = 1799423) B1799423
theorem B2021993 : Blo 798342 2021993 := bstep (se 2 (by rfl) ⟨758247, by rfl⟩ : syracuseStep 2021993 = 1516495) B1516495
theorem B4056317 : Blo 798342 4056317 := bstep (se 3 (by rfl) ⟨760559, by rfl⟩ : syracuseStep 4056317 = 1521119) B1521119
theorem B2026367 : Blo 798342 2026367 := bstep (se 1 (by rfl) ⟨1519775, by rfl⟩ : syracuseStep 2026367 = 3039551) B3039551
theorem B5205385 : Blo 798342 5205385 := bstep (se 2 (by rfl) ⟨1952019, by rfl⟩ : syracuseStep 5205385 = 3904039) B3904039
theorem B1537471 : Blo 798342 1537471 := bstep (se 1 (by rfl) ⟨1153103, by rfl⟩ : syracuseStep 1537471 = 2306207) B2306207
theorem B1347995 : Blo 798342 1347995 := bstep (se 1 (by rfl) ⟨1010996, by rfl⟩ : syracuseStep 1347995 = 2021993) B2021993
theorem B17308511 : Blo 798342 17308511 := bstep (se 1 (by rfl) ⟨12981383, by rfl⟩ : syracuseStep 17308511 = 25962767) B25962767
theorem B1350911 : Blo 798342 1350911 := bstep (se 1 (by rfl) ⟨1013183, by rfl⟩ : syracuseStep 1350911 = 2026367) B2026367
theorem B3416231 : Blo 798342 3416231 := bstep (se 1 (by rfl) ⟨2562173, by rfl⟩ : syracuseStep 3416231 = 5124347) B5124347
theorem B799743 : Blo 798342 799743 := bstep (se 1 (by rfl) ⟨599807, by rfl⟩ : syracuseStep 799743 = 1199615) B1199615
theorem B12629857 : Blo 798342 12629857 := bstep (se 2 (by rfl) ⟨4736196, by rfl⟩ : syracuseStep 12629857 = 9472393) B9472393
theorem B901147 : Blo 798342 901147 := bstep (se 1 (by rfl) ⟨675860, by rfl⟩ : syracuseStep 901147 = 1351721) B1351721
theorem B2704211 : Blo 798342 2704211 := bstep (se 1 (by rfl) ⟨2028158, by rfl⟩ : syracuseStep 2704211 = 4056317) B4056317
theorem B2049961 : Blo 798342 2049961 := bstep (se 2 (by rfl) ⟨768735, by rfl⟩ : syracuseStep 2049961 = 1537471) B1537471
theorem B1202279 : Blo 798342 1202279 := bstep (se 1 (by rfl) ⟨901709, by rfl⟩ : syracuseStep 1202279 = 1803419) B1803419
theorem B6940513 : Blo 798342 6940513 := bstep (se 2 (by rfl) ⟨2602692, by rfl⟩ : syracuseStep 6940513 = 5205385) B5205385
theorem B1802807 : Blo 798342 1802807 := bstep (se 1 (by rfl) ⟨1352105, by rfl⟩ : syracuseStep 1802807 = 2704211) B2704211
theorem B11539007 : Blo 798342 11539007 := bstep (se 1 (by rfl) ⟨8654255, by rfl⟩ : syracuseStep 11539007 = 17308511) B17308511
theorem B9254017 : Blo 798342 9254017 := bstep (se 2 (by rfl) ⟨3470256, by rfl⟩ : syracuseStep 9254017 = 6940513) B6940513
theorem B2733281 : Blo 798342 2733281 := bstep (se 2 (by rfl) ⟨1024980, by rfl⟩ : syracuseStep 2733281 = 2049961) B2049961
theorem B898663 : Blo 798342 898663 := bstep (se 1 (by rfl) ⟨673997, by rfl⟩ : syracuseStep 898663 = 1347995) B1347995
theorem B801519 : Blo 798342 801519 := bstep (se 1 (by rfl) ⟨601139, by rfl⟩ : syracuseStep 801519 = 1202279) B1202279
theorem B900607 : Blo 798342 900607 := bstep (se 1 (by rfl) ⟨675455, by rfl⟩ : syracuseStep 900607 = 1350911) B1350911
theorem B2277487 : Blo 798342 2277487 := bstep (se 1 (by rfl) ⟨1708115, by rfl⟩ : syracuseStep 2277487 = 3416231) B3416231
theorem B1201529 : Blo 798342 1201529 := bstep (se 2 (by rfl) ⟨450573, by rfl⟩ : syracuseStep 1201529 = 901147) B901147
theorem B16839809 : Blo 798342 16839809 := bstep (se 2 (by rfl) ⟨6314928, by rfl⟩ : syracuseStep 16839809 = 12629857) B12629857
theorem B801019 : Blo 798342 801019 := bstep (se 1 (by rfl) ⟨600764, by rfl⟩ : syracuseStep 801019 = 1201529) B1201529
theorem B12338689 : Blo 798342 12338689 := bstep (se 2 (by rfl) ⟨4627008, by rfl⟩ : syracuseStep 12338689 = 9254017) B9254017
theorem B1198217 : Blo 798342 1198217 := bstep (se 2 (by rfl) ⟨449331, by rfl⟩ : syracuseStep 1198217 = 898663) B898663
theorem B11226539 : Blo 798342 11226539 := bstep (se 1 (by rfl) ⟨8419904, by rfl⟩ : syracuseStep 11226539 = 16839809) B16839809
theorem B1822187 : Blo 798342 1822187 := bstep (se 1 (by rfl) ⟨1366640, by rfl⟩ : syracuseStep 1822187 = 2733281) B2733281
theorem B1200809 : Blo 798342 1200809 := bstep (se 2 (by rfl) ⟨450303, by rfl⟩ : syracuseStep 1200809 = 900607) B900607
theorem B3036649 : Blo 798342 3036649 := bstep (se 2 (by rfl) ⟨1138743, by rfl⟩ : syracuseStep 3036649 = 2277487) B2277487
theorem B1201871 : Blo 798342 1201871 := bstep (se 1 (by rfl) ⟨901403, by rfl⟩ : syracuseStep 1201871 = 1802807) B1802807
theorem B7692671 : Blo 798342 7692671 := bstep (se 1 (by rfl) ⟨5769503, by rfl⟩ : syracuseStep 7692671 = 11539007) B11539007
theorem B16451585 : Blo 798342 16451585 := bstep (se 2 (by rfl) ⟨6169344, by rfl⟩ : syracuseStep 16451585 = 12338689) B12338689
theorem B4859165 : Blo 798342 4859165 := bstep (se 3 (by rfl) ⟨911093, by rfl⟩ : syracuseStep 4859165 = 1822187) B1822187
theorem B798811 : Blo 798342 798811 := bstep (se 1 (by rfl) ⟨599108, by rfl⟩ : syracuseStep 798811 = 1198217) B1198217
theorem B7484359 : Blo 798342 7484359 := bstep (se 1 (by rfl) ⟨5613269, by rfl⟩ : syracuseStep 7484359 = 11226539) B11226539
theorem B800539 : Blo 798342 800539 := bstep (se 1 (by rfl) ⟨600404, by rfl⟩ : syracuseStep 800539 = 1200809) B1200809
theorem B801247 : Blo 798342 801247 := bstep (se 1 (by rfl) ⟨600935, by rfl⟩ : syracuseStep 801247 = 1201871) B1201871
theorem B5128447 : Blo 798342 5128447 := bstep (se 1 (by rfl) ⟨3846335, by rfl⟩ : syracuseStep 5128447 = 7692671) B7692671
theorem B4048865 : Blo 798342 4048865 := bstep (se 2 (by rfl) ⟨1518324, by rfl⟩ : syracuseStep 4048865 = 3036649) B3036649
theorem B2699243 : Blo 798342 2699243 := bstep (se 1 (by rfl) ⟨2024432, by rfl⟩ : syracuseStep 2699243 = 4048865) B4048865
theorem B9979145 : Blo 798342 9979145 := bstep (se 2 (by rfl) ⟨3742179, by rfl⟩ : syracuseStep 9979145 = 7484359) B7484359
theorem B6837929 : Blo 798342 6837929 := bstep (se 2 (by rfl) ⟨2564223, by rfl⟩ : syracuseStep 6837929 = 5128447) B5128447
theorem B10967723 : Blo 798342 10967723 := bstep (se 1 (by rfl) ⟨8225792, by rfl⟩ : syracuseStep 10967723 = 16451585) B16451585
theorem B3239443 : Blo 798342 3239443 := bstep (se 1 (by rfl) ⟨2429582, by rfl⟩ : syracuseStep 3239443 = 4859165) B4859165
theorem B6652763 : Blo 798342 6652763 := bstep (se 1 (by rfl) ⟨4989572, by rfl⟩ : syracuseStep 6652763 = 9979145) B9979145
theorem B4558619 : Blo 798342 4558619 := bstep (se 1 (by rfl) ⟨3418964, by rfl⟩ : syracuseStep 4558619 = 6837929) B6837929
theorem B7311815 : Blo 798342 7311815 := bstep (se 1 (by rfl) ⟨5483861, by rfl⟩ : syracuseStep 7311815 = 10967723) B10967723
theorem B4319257 : Blo 798342 4319257 := bstep (se 2 (by rfl) ⟨1619721, by rfl⟩ : syracuseStep 4319257 = 3239443) B3239443
theorem B1799495 : Blo 798342 1799495 := bstep (se 1 (by rfl) ⟨1349621, by rfl⟩ : syracuseStep 1799495 = 2699243) B2699243
theorem B4435175 : Blo 798342 4435175 := bstep (se 1 (by rfl) ⟨3326381, by rfl⟩ : syracuseStep 4435175 = 6652763) B6652763
theorem B1199663 : Blo 798342 1199663 := bstep (se 1 (by rfl) ⟨899747, by rfl⟩ : syracuseStep 1199663 = 1799495) B1799495
theorem B3039079 : Blo 798342 3039079 := bstep (se 1 (by rfl) ⟨2279309, by rfl⟩ : syracuseStep 3039079 = 4558619) B4558619
theorem B5759009 : Blo 798342 5759009 := bstep (se 2 (by rfl) ⟨2159628, by rfl⟩ : syracuseStep 5759009 = 4319257) B4319257
theorem B4874543 : Blo 798342 4874543 := bstep (se 1 (by rfl) ⟨3655907, by rfl⟩ : syracuseStep 4874543 = 7311815) B7311815
theorem B3839339 : Blo 798342 3839339 := bstep (se 1 (by rfl) ⟨2879504, by rfl⟩ : syracuseStep 3839339 = 5759009) B5759009
theorem B3249695 : Blo 798342 3249695 := bstep (se 1 (by rfl) ⟨2437271, by rfl⟩ : syracuseStep 3249695 = 4874543) B4874543
theorem B2956783 : Blo 798342 2956783 := bstep (se 1 (by rfl) ⟨2217587, by rfl⟩ : syracuseStep 2956783 = 4435175) B4435175
theorem B799775 : Blo 798342 799775 := bstep (se 1 (by rfl) ⟨599831, by rfl⟩ : syracuseStep 799775 = 1199663) B1199663
theorem B4052105 : Blo 798342 4052105 := bstep (se 2 (by rfl) ⟨1519539, by rfl⟩ : syracuseStep 4052105 = 3039079) B3039079
theorem B2166463 : Blo 798342 2166463 := bstep (se 1 (by rfl) ⟨1624847, by rfl⟩ : syracuseStep 2166463 = 3249695) B3249695
theorem B3942377 : Blo 798342 3942377 := bstep (se 2 (by rfl) ⟨1478391, by rfl⟩ : syracuseStep 3942377 = 2956783) B2956783
theorem B2701403 : Blo 798342 2701403 := bstep (se 1 (by rfl) ⟨2026052, by rfl⟩ : syracuseStep 2701403 = 4052105) B4052105
theorem B10238237 : Blo 798342 10238237 := bstep (se 3 (by rfl) ⟨1919669, by rfl⟩ : syracuseStep 10238237 = 3839339) B3839339
theorem B2888617 : Blo 798342 2888617 := bstep (se 2 (by rfl) ⟨1083231, by rfl⟩ : syracuseStep 2888617 = 2166463) B2166463
theorem B2628251 : Blo 798342 2628251 := bstep (se 1 (by rfl) ⟨1971188, by rfl⟩ : syracuseStep 2628251 = 3942377) B3942377
theorem B6825491 : Blo 798342 6825491 := bstep (se 1 (by rfl) ⟨5119118, by rfl⟩ : syracuseStep 6825491 = 10238237) B10238237
theorem B1800935 : Blo 798342 1800935 := bstep (se 1 (by rfl) ⟨1350701, by rfl⟩ : syracuseStep 1800935 = 2701403) B2701403
theorem B1752167 : Blo 798342 1752167 := bstep (se 1 (by rfl) ⟨1314125, by rfl⟩ : syracuseStep 1752167 = 2628251) B2628251
theorem B3851489 : Blo 798342 3851489 := bstep (se 2 (by rfl) ⟨1444308, by rfl⟩ : syracuseStep 3851489 = 2888617) B2888617
theorem B1200623 : Blo 798342 1200623 := bstep (se 1 (by rfl) ⟨900467, by rfl⟩ : syracuseStep 1200623 = 1800935) B1800935
theorem B4550327 : Blo 798342 4550327 := bstep (se 1 (by rfl) ⟨3412745, by rfl⟩ : syracuseStep 4550327 = 6825491) B6825491
theorem B2567659 : Blo 798342 2567659 := bstep (se 1 (by rfl) ⟨1925744, by rfl⟩ : syracuseStep 2567659 = 3851489) B3851489
theorem B800415 : Blo 798342 800415 := bstep (se 1 (by rfl) ⟨600311, by rfl⟩ : syracuseStep 800415 = 1200623) B1200623
theorem B3033551 : Blo 798342 3033551 := bstep (se 1 (by rfl) ⟨2275163, by rfl⟩ : syracuseStep 3033551 = 4550327) B4550327
theorem B1168111 : Blo 798342 1168111 := bstep (se 1 (by rfl) ⟨876083, by rfl⟩ : syracuseStep 1168111 = 1752167) B1752167
theorem B3423545 : Blo 798342 3423545 := bstep (se 2 (by rfl) ⟨1283829, by rfl⟩ : syracuseStep 3423545 = 2567659) B2567659
theorem B1557481 : Blo 798342 1557481 := bstep (se 2 (by rfl) ⟨584055, by rfl⟩ : syracuseStep 1557481 = 1168111) B1168111
theorem B2022367 : Blo 798342 2022367 := bstep (se 1 (by rfl) ⟨1516775, by rfl⟩ : syracuseStep 2022367 = 3033551) B3033551
theorem B2696489 : Blo 798342 2696489 := bstep (se 2 (by rfl) ⟨1011183, by rfl⟩ : syracuseStep 2696489 = 2022367) B2022367
theorem B2076641 : Blo 798342 2076641 := bstep (se 2 (by rfl) ⟨778740, by rfl⟩ : syracuseStep 2076641 = 1557481) B1557481
theorem B2282363 : Blo 798342 2282363 := bstep (se 1 (by rfl) ⟨1711772, by rfl⟩ : syracuseStep 2282363 = 3423545) B3423545
theorem B1384427 : Blo 798342 1384427 := bstep (se 1 (by rfl) ⟨1038320, by rfl⟩ : syracuseStep 1384427 = 2076641) B2076641
theorem B1521575 : Blo 798342 1521575 := bstep (se 1 (by rfl) ⟨1141181, by rfl⟩ : syracuseStep 1521575 = 2282363) B2282363
theorem B1797659 : Blo 798342 1797659 := bstep (se 1 (by rfl) ⟨1348244, by rfl⟩ : syracuseStep 1797659 = 2696489) B2696489
theorem B922951 : Blo 798342 922951 := bstep (se 1 (by rfl) ⟨692213, by rfl⟩ : syracuseStep 922951 = 1384427) B1384427
theorem B1198439 : Blo 798342 1198439 := bstep (se 1 (by rfl) ⟨898829, by rfl⟩ : syracuseStep 1198439 = 1797659) B1797659
theorem B1014383 : Blo 798342 1014383 := bstep (se 1 (by rfl) ⟨760787, by rfl⟩ : syracuseStep 1014383 = 1521575) B1521575
theorem B798959 : Blo 798342 798959 := bstep (se 1 (by rfl) ⟨599219, by rfl⟩ : syracuseStep 798959 = 1198439) B1198439
theorem B2705021 : Blo 798342 2705021 := bstep (se 3 (by rfl) ⟨507191, by rfl⟩ : syracuseStep 2705021 = 1014383) B1014383
theorem B1230601 : Blo 798342 1230601 := bstep (se 2 (by rfl) ⟨461475, by rfl⟩ : syracuseStep 1230601 = 922951) B922951
theorem B1803347 : Blo 798342 1803347 := bstep (se 1 (by rfl) ⟨1352510, by rfl⟩ : syracuseStep 1803347 = 2705021) B2705021
theorem B1640801 : Blo 798342 1640801 := bstep (se 2 (by rfl) ⟨615300, by rfl⟩ : syracuseStep 1640801 = 1230601) B1230601
theorem B1093867 : Blo 798342 1093867 := bstep (se 1 (by rfl) ⟨820400, by rfl⟩ : syracuseStep 1093867 = 1640801) B1640801
theorem B1202231 : Blo 798342 1202231 := bstep (se 1 (by rfl) ⟨901673, by rfl⟩ : syracuseStep 1202231 = 1803347) B1803347
theorem B5833957 : Blo 798342 5833957 := bstep (se 4 (by rfl) ⟨546933, by rfl⟩ : syracuseStep 5833957 = 1093867) B1093867
theorem B801487 : Blo 798342 801487 := bstep (se 1 (by rfl) ⟨601115, by rfl⟩ : syracuseStep 801487 = 1202231) B1202231
theorem B7778609 : Blo 798342 7778609 := bstep (se 2 (by rfl) ⟨2916978, by rfl⟩ : syracuseStep 7778609 = 5833957) B5833957
theorem B5185739 : Blo 798342 5185739 := bstep (se 1 (by rfl) ⟨3889304, by rfl⟩ : syracuseStep 5185739 = 7778609) B7778609
theorem B13828637 : Blo 798342 13828637 := bstep (se 3 (by rfl) ⟨2592869, by rfl⟩ : syracuseStep 13828637 = 5185739) B5185739
theorem B9219091 : Blo 798342 9219091 := bstep (se 1 (by rfl) ⟨6914318, by rfl⟩ : syracuseStep 9219091 = 13828637) B13828637
theorem B12292121 : Blo 798342 12292121 := bstep (se 2 (by rfl) ⟨4609545, by rfl⟩ : syracuseStep 12292121 = 9219091) B9219091
theorem B32778989 : Blo 798342 32778989 := bstep (se 3 (by rfl) ⟨6146060, by rfl⟩ : syracuseStep 32778989 = 12292121) B12292121
theorem B21852659 : Blo 798342 21852659 := bstep (se 1 (by rfl) ⟨16389494, by rfl⟩ : syracuseStep 21852659 = 32778989) B32778989
theorem B14568439 : Blo 798342 14568439 := bstep (se 1 (by rfl) ⟨10926329, by rfl⟩ : syracuseStep 14568439 = 21852659) B21852659
theorem B19424585 : Blo 798342 19424585 := bstep (se 2 (by rfl) ⟨7284219, by rfl⟩ : syracuseStep 19424585 = 14568439) B14568439
theorem B12949723 : Blo 798342 12949723 := bstep (se 1 (by rfl) ⟨9712292, by rfl⟩ : syracuseStep 12949723 = 19424585) B19424585
theorem B17266297 : Blo 798342 17266297 := bstep (se 2 (by rfl) ⟨6474861, by rfl⟩ : syracuseStep 17266297 = 12949723) B12949723
theorem B23021729 : Blo 798342 23021729 := bstep (se 2 (by rfl) ⟨8633148, by rfl⟩ : syracuseStep 23021729 = 17266297) B17266297
theorem B15347819 : Blo 798342 15347819 := bstep (se 1 (by rfl) ⟨11510864, by rfl⟩ : syracuseStep 15347819 = 23021729) B23021729
theorem B10231879 : Blo 798342 10231879 := bstep (se 1 (by rfl) ⟨7673909, by rfl⟩ : syracuseStep 10231879 = 15347819) B15347819
theorem B13642505 : Blo 798342 13642505 := bstep (se 2 (by rfl) ⟨5115939, by rfl⟩ : syracuseStep 13642505 = 10231879) B10231879
theorem B9095003 : Blo 798342 9095003 := bstep (se 1 (by rfl) ⟨6821252, by rfl⟩ : syracuseStep 9095003 = 13642505) B13642505
theorem B6063335 : Blo 798342 6063335 := bstep (se 1 (by rfl) ⟨4547501, by rfl⟩ : syracuseStep 6063335 = 9095003) B9095003
theorem B4042223 : Blo 798342 4042223 := bstep (se 1 (by rfl) ⟨3031667, by rfl⟩ : syracuseStep 4042223 = 6063335) B6063335
theorem B2694815 : Blo 798342 2694815 := bstep (se 1 (by rfl) ⟨2021111, by rfl⟩ : syracuseStep 2694815 = 4042223) B4042223
theorem B1796543 : Blo 798342 1796543 := bstep (se 1 (by rfl) ⟨1347407, by rfl⟩ : syracuseStep 1796543 = 2694815) B2694815
theorem B1197695 : Blo 798342 1197695 := bstep (se 1 (by rfl) ⟨898271, by rfl⟩ : syracuseStep 1197695 = 1796543) B1796543
theorem B798463 : Blo 798342 798463 := bstep (se 1 (by rfl) ⟨598847, by rfl⟩ : syracuseStep 798463 = 1197695) B1197695

theorem C0 (j : ℕ) (h1 : 199585 ≤ j) (h2 : j ≤ 200284) : Blo 798342 (4 * j + 3) := by
  interval_cases j
  · exact B798343
  · exact B798347
  · exact B798351
  · exact B798355
  · exact B798359
  · exact B798363
  · exact B798367
  · exact B798371
  · exact B798375
  · exact B798379
  · exact B798383
  · exact B798387
  · exact B798391
  · exact B798395
  · exact B798399
  · exact B798403
  · exact B798407
  · exact B798411
  · exact B798415
  · exact B798419
  · exact B798423
  · exact B798427
  · exact B798431
  · exact B798435
  · exact B798439
  · exact B798443
  · exact B798447
  · exact B798451
  · exact B798455
  · exact B798459
  · exact B798463
  · exact B798467
  · exact B798471
  · exact B798475
  · exact B798479
  · exact B798483
  · exact B798487
  · exact B798491
  · exact B798495
  · exact B798499
  · exact B798503
  · exact B798507
  · exact B798511
  · exact B798515
  · exact B798519
  · exact B798523
  · exact B798527
  · exact B798531
  · exact B798535
  · exact B798539
  · exact B798543
  · exact B798547
  · exact B798551
  · exact B798555
  · exact B798559
  · exact B798563
  · exact B798567
  · exact B798571
  · exact B798575
  · exact B798579
  · exact B798583
  · exact B798587
  · exact B798591
  · exact B798595
  · exact B798599
  · exact B798603
  · exact B798607
  · exact B798611
  · exact B798615
  · exact B798619
  · exact B798623
  · exact B798627
  · exact B798631
  · exact B798635
  · exact B798639
  · exact B798643
  · exact B798647
  · exact B798651
  · exact B798655
  · exact B798659
  · exact B798663
  · exact B798667
  · exact B798671
  · exact B798675
  · exact B798679
  · exact B798683
  · exact B798687
  · exact B798691
  · exact B798695
  · exact B798699
  · exact B798703
  · exact B798707
  · exact B798711
  · exact B798715
  · exact B798719
  · exact B798723
  · exact B798727
  · exact B798731
  · exact B798735
  · exact B798739
  · exact B798743
  · exact B798747
  · exact B798751
  · exact B798755
  · exact B798759
  · exact B798763
  · exact B798767
  · exact B798771
  · exact B798775
  · exact B798779
  · exact B798783
  · exact B798787
  · exact B798791
  · exact B798795
  · exact B798799
  · exact B798803
  · exact B798807
  · exact B798811
  · exact B798815
  · exact B798819
  · exact B798823
  · exact B798827
  · exact B798831
  · exact B798835
  · exact B798839
  · exact B798843
  · exact B798847
  · exact B798851
  · exact B798855
  · exact B798859
  · exact B798863
  · exact B798867
  · exact B798871
  · exact B798875
  · exact B798879
  · exact B798883
  · exact B798887
  · exact B798891
  · exact B798895
  · exact B798899
  · exact B798903
  · exact B798907
  · exact B798911
  · exact B798915
  · exact B798919
  · exact B798923
  · exact B798927
  · exact B798931
  · exact B798935
  · exact B798939
  · exact B798943
  · exact B798947
  · exact B798951
  · exact B798955
  · exact B798959
  · exact B798963
  · exact B798967
  · exact B798971
  · exact B798975
  · exact B798979
  · exact B798983
  · exact B798987
  · exact B798991
  · exact B798995
  · exact B798999
  · exact B799003
  · exact B799007
  · exact B799011
  · exact B799015
  · exact B799019
  · exact B799023
  · exact B799027
  · exact B799031
  · exact B799035
  · exact B799039
  · exact B799043
  · exact B799047
  · exact B799051
  · exact B799055
  · exact B799059
  · exact B799063
  · exact B799067
  · exact B799071
  · exact B799075
  · exact B799079
  · exact B799083
  · exact B799087
  · exact B799091
  · exact B799095
  · exact B799099
  · exact B799103
  · exact B799107
  · exact B799111
  · exact B799115
  · exact B799119
  · exact B799123
  · exact B799127
  · exact B799131
  · exact B799135
  · exact B799139
  · exact B799143
  · exact B799147
  · exact B799151
  · exact B799155
  · exact B799159
  · exact B799163
  · exact B799167
  · exact B799171
  · exact B799175
  · exact B799179
  · exact B799183
  · exact B799187
  · exact B799191
  · exact B799195
  · exact B799199
  · exact B799203
  · exact B799207
  · exact B799211
  · exact B799215
  · exact B799219
  · exact B799223
  · exact B799227
  · exact B799231
  · exact B799235
  · exact B799239
  · exact B799243
  · exact B799247
  · exact B799251
  · exact B799255
  · exact B799259
  · exact B799263
  · exact B799267
  · exact B799271
  · exact B799275
  · exact B799279
  · exact B799283
  · exact B799287
  · exact B799291
  · exact B799295
  · exact B799299
  · exact B799303
  · exact B799307
  · exact B799311
  · exact B799315
  · exact B799319
  · exact B799323
  · exact B799327
  · exact B799331
  · exact B799335
  · exact B799339
  · exact B799343
  · exact B799347
  · exact B799351
  · exact B799355
  · exact B799359
  · exact B799363
  · exact B799367
  · exact B799371
  · exact B799375
  · exact B799379
  · exact B799383
  · exact B799387
  · exact B799391
  · exact B799395
  · exact B799399
  · exact B799403
  · exact B799407
  · exact B799411
  · exact B799415
  · exact B799419
  · exact B799423
  · exact B799427
  · exact B799431
  · exact B799435
  · exact B799439
  · exact B799443
  · exact B799447
  · exact B799451
  · exact B799455
  · exact B799459
  · exact B799463
  · exact B799467
  · exact B799471
  · exact B799475
  · exact B799479
  · exact B799483
  · exact B799487
  · exact B799491
  · exact B799495
  · exact B799499
  · exact B799503
  · exact B799507
  · exact B799511
  · exact B799515
  · exact B799519
  · exact B799523
  · exact B799527
  · exact B799531
  · exact B799535
  · exact B799539
  · exact B799543
  · exact B799547
  · exact B799551
  · exact B799555
  · exact B799559
  · exact B799563
  · exact B799567
  · exact B799571
  · exact B799575
  · exact B799579
  · exact B799583
  · exact B799587
  · exact B799591
  · exact B799595
  · exact B799599
  · exact B799603
  · exact B799607
  · exact B799611
  · exact B799615
  · exact B799619
  · exact B799623
  · exact B799627
  · exact B799631
  · exact B799635
  · exact B799639
  · exact B799643
  · exact B799647
  · exact B799651
  · exact B799655
  · exact B799659
  · exact B799663
  · exact B799667
  · exact B799671
  · exact B799675
  · exact B799679
  · exact B799683
  · exact B799687
  · exact B799691
  · exact B799695
  · exact B799699
  · exact B799703
  · exact B799707
  · exact B799711
  · exact B799715
  · exact B799719
  · exact B799723
  · exact B799727
  · exact B799731
  · exact B799735
  · exact B799739
  · exact B799743
  · exact B799747
  · exact B799751
  · exact B799755
  · exact B799759
  · exact B799763
  · exact B799767
  · exact B799771
  · exact B799775
  · exact B799779
  · exact B799783
  · exact B799787
  · exact B799791
  · exact B799795
  · exact B799799
  · exact B799803
  · exact B799807
  · exact B799811
  · exact B799815
  · exact B799819
  · exact B799823
  · exact B799827
  · exact B799831
  · exact B799835
  · exact B799839
  · exact B799843
  · exact B799847
  · exact B799851
  · exact B799855
  · exact B799859
  · exact B799863
  · exact B799867
  · exact B799871
  · exact B799875
  · exact B799879
  · exact B799883
  · exact B799887
  · exact B799891
  · exact B799895
  · exact B799899
  · exact B799903
  · exact B799907
  · exact B799911
  · exact B799915
  · exact B799919
  · exact B799923
  · exact B799927
  · exact B799931
  · exact B799935
  · exact B799939
  · exact B799943
  · exact B799947
  · exact B799951
  · exact B799955
  · exact B799959
  · exact B799963
  · exact B799967
  · exact B799971
  · exact B799975
  · exact B799979
  · exact B799983
  · exact B799987
  · exact B799991
  · exact B799995
  · exact B799999
  · exact B800003
  · exact B800007
  · exact B800011
  · exact B800015
  · exact B800019
  · exact B800023
  · exact B800027
  · exact B800031
  · exact B800035
  · exact B800039
  · exact B800043
  · exact B800047
  · exact B800051
  · exact B800055
  · exact B800059
  · exact B800063
  · exact B800067
  · exact B800071
  · exact B800075
  · exact B800079
  · exact B800083
  · exact B800087
  · exact B800091
  · exact B800095
  · exact B800099
  · exact B800103
  · exact B800107
  · exact B800111
  · exact B800115
  · exact B800119
  · exact B800123
  · exact B800127
  · exact B800131
  · exact B800135
  · exact B800139
  · exact B800143
  · exact B800147
  · exact B800151
  · exact B800155
  · exact B800159
  · exact B800163
  · exact B800167
  · exact B800171
  · exact B800175
  · exact B800179
  · exact B800183
  · exact B800187
  · exact B800191
  · exact B800195
  · exact B800199
  · exact B800203
  · exact B800207
  · exact B800211
  · exact B800215
  · exact B800219
  · exact B800223
  · exact B800227
  · exact B800231
  · exact B800235
  · exact B800239
  · exact B800243
  · exact B800247
  · exact B800251
  · exact B800255
  · exact B800259
  · exact B800263
  · exact B800267
  · exact B800271
  · exact B800275
  · exact B800279
  · exact B800283
  · exact B800287
  · exact B800291
  · exact B800295
  · exact B800299
  · exact B800303
  · exact B800307
  · exact B800311
  · exact B800315
  · exact B800319
  · exact B800323
  · exact B800327
  · exact B800331
  · exact B800335
  · exact B800339
  · exact B800343
  · exact B800347
  · exact B800351
  · exact B800355
  · exact B800359
  · exact B800363
  · exact B800367
  · exact B800371
  · exact B800375
  · exact B800379
  · exact B800383
  · exact B800387
  · exact B800391
  · exact B800395
  · exact B800399
  · exact B800403
  · exact B800407
  · exact B800411
  · exact B800415
  · exact B800419
  · exact B800423
  · exact B800427
  · exact B800431
  · exact B800435
  · exact B800439
  · exact B800443
  · exact B800447
  · exact B800451
  · exact B800455
  · exact B800459
  · exact B800463
  · exact B800467
  · exact B800471
  · exact B800475
  · exact B800479
  · exact B800483
  · exact B800487
  · exact B800491
  · exact B800495
  · exact B800499
  · exact B800503
  · exact B800507
  · exact B800511
  · exact B800515
  · exact B800519
  · exact B800523
  · exact B800527
  · exact B800531
  · exact B800535
  · exact B800539
  · exact B800543
  · exact B800547
  · exact B800551
  · exact B800555
  · exact B800559
  · exact B800563
  · exact B800567
  · exact B800571
  · exact B800575
  · exact B800579
  · exact B800583
  · exact B800587
  · exact B800591
  · exact B800595
  · exact B800599
  · exact B800603
  · exact B800607
  · exact B800611
  · exact B800615
  · exact B800619
  · exact B800623
  · exact B800627
  · exact B800631
  · exact B800635
  · exact B800639
  · exact B800643
  · exact B800647
  · exact B800651
  · exact B800655
  · exact B800659
  · exact B800663
  · exact B800667
  · exact B800671
  · exact B800675
  · exact B800679
  · exact B800683
  · exact B800687
  · exact B800691
  · exact B800695
  · exact B800699
  · exact B800703
  · exact B800707
  · exact B800711
  · exact B800715
  · exact B800719
  · exact B800723
  · exact B800727
  · exact B800731
  · exact B800735
  · exact B800739
  · exact B800743
  · exact B800747
  · exact B800751
  · exact B800755
  · exact B800759
  · exact B800763
  · exact B800767
  · exact B800771
  · exact B800775
  · exact B800779
  · exact B800783
  · exact B800787
  · exact B800791
  · exact B800795
  · exact B800799
  · exact B800803
  · exact B800807
  · exact B800811
  · exact B800815
  · exact B800819
  · exact B800823
  · exact B800827
  · exact B800831
  · exact B800835
  · exact B800839
  · exact B800843
  · exact B800847
  · exact B800851
  · exact B800855
  · exact B800859
  · exact B800863
  · exact B800867
  · exact B800871
  · exact B800875
  · exact B800879
  · exact B800883
  · exact B800887
  · exact B800891
  · exact B800895
  · exact B800899
  · exact B800903
  · exact B800907
  · exact B800911
  · exact B800915
  · exact B800919
  · exact B800923
  · exact B800927
  · exact B800931
  · exact B800935
  · exact B800939
  · exact B800943
  · exact B800947
  · exact B800951
  · exact B800955
  · exact B800959
  · exact B800963
  · exact B800967
  · exact B800971
  · exact B800975
  · exact B800979
  · exact B800983
  · exact B800987
  · exact B800991
  · exact B800995
  · exact B800999
  · exact B801003
  · exact B801007
  · exact B801011
  · exact B801015
  · exact B801019
  · exact B801023
  · exact B801027
  · exact B801031
  · exact B801035
  · exact B801039
  · exact B801043
  · exact B801047
  · exact B801051
  · exact B801055
  · exact B801059
  · exact B801063
  · exact B801067
  · exact B801071
  · exact B801075
  · exact B801079
  · exact B801083
  · exact B801087
  · exact B801091
  · exact B801095
  · exact B801099
  · exact B801103
  · exact B801107
  · exact B801111
  · exact B801115
  · exact B801119
  · exact B801123
  · exact B801127
  · exact B801131
  · exact B801135
  · exact B801139

theorem C1 (j : ℕ) (h1 : 200285 ≤ j) (h2 : j ≤ 200584) : Blo 798342 (4 * j + 3) := by
  interval_cases j
  · exact B801143
  · exact B801147
  · exact B801151
  · exact B801155
  · exact B801159
  · exact B801163
  · exact B801167
  · exact B801171
  · exact B801175
  · exact B801179
  · exact B801183
  · exact B801187
  · exact B801191
  · exact B801195
  · exact B801199
  · exact B801203
  · exact B801207
  · exact B801211
  · exact B801215
  · exact B801219
  · exact B801223
  · exact B801227
  · exact B801231
  · exact B801235
  · exact B801239
  · exact B801243
  · exact B801247
  · exact B801251
  · exact B801255
  · exact B801259
  · exact B801263
  · exact B801267
  · exact B801271
  · exact B801275
  · exact B801279
  · exact B801283
  · exact B801287
  · exact B801291
  · exact B801295
  · exact B801299
  · exact B801303
  · exact B801307
  · exact B801311
  · exact B801315
  · exact B801319
  · exact B801323
  · exact B801327
  · exact B801331
  · exact B801335
  · exact B801339
  · exact B801343
  · exact B801347
  · exact B801351
  · exact B801355
  · exact B801359
  · exact B801363
  · exact B801367
  · exact B801371
  · exact B801375
  · exact B801379
  · exact B801383
  · exact B801387
  · exact B801391
  · exact B801395
  · exact B801399
  · exact B801403
  · exact B801407
  · exact B801411
  · exact B801415
  · exact B801419
  · exact B801423
  · exact B801427
  · exact B801431
  · exact B801435
  · exact B801439
  · exact B801443
  · exact B801447
  · exact B801451
  · exact B801455
  · exact B801459
  · exact B801463
  · exact B801467
  · exact B801471
  · exact B801475
  · exact B801479
  · exact B801483
  · exact B801487
  · exact B801491
  · exact B801495
  · exact B801499
  · exact B801503
  · exact B801507
  · exact B801511
  · exact B801515
  · exact B801519
  · exact B801523
  · exact B801527
  · exact B801531
  · exact B801535
  · exact B801539
  · exact B801543
  · exact B801547
  · exact B801551
  · exact B801555
  · exact B801559
  · exact B801563
  · exact B801567
  · exact B801571
  · exact B801575
  · exact B801579
  · exact B801583
  · exact B801587
  · exact B801591
  · exact B801595
  · exact B801599
  · exact B801603
  · exact B801607
  · exact B801611
  · exact B801615
  · exact B801619
  · exact B801623
  · exact B801627
  · exact B801631
  · exact B801635
  · exact B801639
  · exact B801643
  · exact B801647
  · exact B801651
  · exact B801655
  · exact B801659
  · exact B801663
  · exact B801667
  · exact B801671
  · exact B801675
  · exact B801679
  · exact B801683
  · exact B801687
  · exact B801691
  · exact B801695
  · exact B801699
  · exact B801703
  · exact B801707
  · exact B801711
  · exact B801715
  · exact B801719
  · exact B801723
  · exact B801727
  · exact B801731
  · exact B801735
  · exact B801739
  · exact B801743
  · exact B801747
  · exact B801751
  · exact B801755
  · exact B801759
  · exact B801763
  · exact B801767
  · exact B801771
  · exact B801775
  · exact B801779
  · exact B801783
  · exact B801787
  · exact B801791
  · exact B801795
  · exact B801799
  · exact B801803
  · exact B801807
  · exact B801811
  · exact B801815
  · exact B801819
  · exact B801823
  · exact B801827
  · exact B801831
  · exact B801835
  · exact B801839
  · exact B801843
  · exact B801847
  · exact B801851
  · exact B801855
  · exact B801859
  · exact B801863
  · exact B801867
  · exact B801871
  · exact B801875
  · exact B801879
  · exact B801883
  · exact B801887
  · exact B801891
  · exact B801895
  · exact B801899
  · exact B801903
  · exact B801907
  · exact B801911
  · exact B801915
  · exact B801919
  · exact B801923
  · exact B801927
  · exact B801931
  · exact B801935
  · exact B801939
  · exact B801943
  · exact B801947
  · exact B801951
  · exact B801955
  · exact B801959
  · exact B801963
  · exact B801967
  · exact B801971
  · exact B801975
  · exact B801979
  · exact B801983
  · exact B801987
  · exact B801991
  · exact B801995
  · exact B801999
  · exact B802003
  · exact B802007
  · exact B802011
  · exact B802015
  · exact B802019
  · exact B802023
  · exact B802027
  · exact B802031
  · exact B802035
  · exact B802039
  · exact B802043
  · exact B802047
  · exact B802051
  · exact B802055
  · exact B802059
  · exact B802063
  · exact B802067
  · exact B802071
  · exact B802075
  · exact B802079
  · exact B802083
  · exact B802087
  · exact B802091
  · exact B802095
  · exact B802099
  · exact B802103
  · exact B802107
  · exact B802111
  · exact B802115
  · exact B802119
  · exact B802123
  · exact B802127
  · exact B802131
  · exact B802135
  · exact B802139
  · exact B802143
  · exact B802147
  · exact B802151
  · exact B802155
  · exact B802159
  · exact B802163
  · exact B802167
  · exact B802171
  · exact B802175
  · exact B802179
  · exact B802183
  · exact B802187
  · exact B802191
  · exact B802195
  · exact B802199
  · exact B802203
  · exact B802207
  · exact B802211
  · exact B802215
  · exact B802219
  · exact B802223
  · exact B802227
  · exact B802231
  · exact B802235
  · exact B802239
  · exact B802243
  · exact B802247
  · exact B802251
  · exact B802255
  · exact B802259
  · exact B802263
  · exact B802267
  · exact B802271
  · exact B802275
  · exact B802279
  · exact B802283
  · exact B802287
  · exact B802291
  · exact B802295
  · exact B802299
  · exact B802303
  · exact B802307
  · exact B802311
  · exact B802315
  · exact B802319
  · exact B802323
  · exact B802327
  · exact B802331
  · exact B802335
  · exact B802339

theorem solution (m : ℕ) (hlo : 798342 ≤ m) (hhi : m ≤ 802342) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 199585 ≤ j := by omega
    have hj2 : j ≤ 200584 := by omega
    have hb : Blo 798342 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 200285 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
