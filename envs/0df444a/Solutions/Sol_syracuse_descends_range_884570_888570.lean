-- Prove2me | solution 1 for syracuse_descends_range_884570_888570
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:21:45.545637+00:00
-- url     : https://prove2.me/submissions/db5b99e3-960c-45a4-b311-76f657b62912

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


theorem B4620341 : Blo 884570 4620341 := bbase (se 5 (by rfl) ⟨216578, by rfl⟩ : syracuseStep 4620341 = 433157) (by norm_num)
theorem B1998917 : Blo 884570 1998917 := bbase (se 4 (by rfl) ⟨187398, by rfl⟩ : syracuseStep 1998917 = 374797) (by norm_num)
theorem B2130013 : Blo 884570 2130013 := bbase (se 3 (by rfl) ⟨399377, by rfl⟩ : syracuseStep 2130013 = 798755) (by norm_num)
theorem B1998989 : Blo 884570 1998989 := bbase (se 3 (by rfl) ⟨374810, by rfl⟩ : syracuseStep 1998989 = 749621) (by norm_num)
theorem B1999061 : Blo 884570 1999061 := bbase (se 7 (by rfl) ⟨23426, by rfl⟩ : syracuseStep 1999061 = 46853) (by norm_num)
theorem B1999133 : Blo 884570 1999133 := bbase (se 3 (by rfl) ⟨374837, by rfl⟩ : syracuseStep 1999133 = 749675) (by norm_num)
theorem B2392373 : Blo 884570 2392373 := bbase (se 5 (by rfl) ⟨112142, by rfl⟩ : syracuseStep 2392373 = 224285) (by norm_num)
theorem B2130245 : Blo 884570 2130245 := bbase (se 4 (by rfl) ⟨199710, by rfl⟩ : syracuseStep 2130245 = 399421) (by norm_num)
theorem B1999205 : Blo 884570 1999205 := bbase (se 4 (by rfl) ⟨187425, by rfl⟩ : syracuseStep 1999205 = 374851) (by norm_num)
theorem B2130293 : Blo 884570 2130293 := bbase (se 5 (by rfl) ⟨99857, by rfl⟩ : syracuseStep 2130293 = 199715) (by norm_num)
theorem B1999277 : Blo 884570 1999277 := bbase (se 3 (by rfl) ⟨374864, by rfl⟩ : syracuseStep 1999277 = 749729) (by norm_num)
theorem B3408421 : Blo 884570 3408421 := bbase (se 4 (by rfl) ⟨319539, by rfl⟩ : syracuseStep 3408421 = 639079) (by norm_num)
theorem B4489829 : Blo 884570 4489829 := bbase (se 4 (by rfl) ⟨420921, by rfl⟩ : syracuseStep 4489829 = 841843) (by norm_num)
theorem B2524117 : Blo 884570 2524117 := bbase (se 7 (by rfl) ⟨29579, by rfl⟩ : syracuseStep 2524117 = 59159) (by norm_num)
theorem B2458613 : Blo 884570 2458613 := bbase (se 5 (by rfl) ⟨115247, by rfl⟩ : syracuseStep 2458613 = 230495) (by norm_num)
theorem B2524277 : Blo 884570 2524277 := bbase (se 5 (by rfl) ⟨118325, by rfl⟩ : syracuseStep 2524277 = 236651) (by norm_num)
theorem B1475725 : Blo 884570 1475725 := bbase (se 3 (by rfl) ⟨276698, by rfl⟩ : syracuseStep 1475725 = 553397) (by norm_num)
theorem B2524517 : Blo 884570 2524517 := bbase (se 4 (by rfl) ⟨236673, by rfl⟩ : syracuseStep 2524517 = 473347) (by norm_num)
theorem B1705445 : Blo 884570 1705445 := bbase (se 4 (by rfl) ⟨159885, by rfl⟩ : syracuseStep 1705445 = 319771) (by norm_num)
theorem B2524709 : Blo 884570 2524709 := bbase (se 4 (by rfl) ⟨236691, by rfl⟩ : syracuseStep 2524709 = 473383) (by norm_num)
theorem B2393813 : Blo 884570 2393813 := bbase (se 7 (by rfl) ⟨28052, by rfl⟩ : syracuseStep 2393813 = 56105) (by norm_num)
theorem B2131685 : Blo 884570 2131685 := bbase (se 4 (by rfl) ⟨199845, by rfl⟩ : syracuseStep 2131685 = 399691) (by norm_num)
theorem B7767893 : Blo 884570 7767893 := bbase (se 9 (by rfl) ⟨22757, by rfl⟩ : syracuseStep 7767893 = 45515) (by norm_num)
theorem B4491125 : Blo 884570 4491125 := bbase (se 5 (by rfl) ⟨210521, by rfl⟩ : syracuseStep 4491125 = 421043) (by norm_num)
theorem B2590597 : Blo 884570 2590597 := bbase (se 4 (by rfl) ⟨242868, by rfl⟩ : syracuseStep 2590597 = 485737) (by norm_num)
theorem B2131877 : Blo 884570 2131877 := bbase (se 4 (by rfl) ⟨199863, by rfl⟩ : syracuseStep 2131877 = 399727) (by norm_num)
theorem B4261909 : Blo 884570 4261909 := bbase (se 6 (by rfl) ⟨99888, by rfl⟩ : syracuseStep 4261909 = 199777) (by norm_num)
theorem B4556837 : Blo 884570 4556837 := bbase (se 4 (by rfl) ⟨427203, by rfl⟩ : syracuseStep 4556837 = 854407) (by norm_num)
theorem B1050769 : Blo 884570 1050769 := bbase (se 2 (by rfl) ⟨394038, by rfl⟩ : syracuseStep 1050769 = 788077) (by norm_num)
theorem B2525701 : Blo 884570 2525701 := bbase (se 4 (by rfl) ⟨236784, by rfl⟩ : syracuseStep 2525701 = 473569) (by norm_num)
theorem B2394677 : Blo 884570 2394677 := bbase (se 5 (by rfl) ⟨112250, by rfl⟩ : syracuseStep 2394677 = 224501) (by norm_num)
theorem B4492421 : Blo 884570 4492421 := bbase (se 4 (by rfl) ⟨421164, by rfl⟩ : syracuseStep 4492421 = 842329) (by norm_num)
theorem B6393269 : Blo 884570 6393269 := bbase (se 5 (by rfl) ⟨299684, by rfl⟩ : syracuseStep 6393269 = 599369) (by norm_num)
theorem B2395637 : Blo 884570 2395637 := bbase (se 5 (by rfl) ⟨112295, by rfl⟩ : syracuseStep 2395637 = 224591) (by norm_num)
theorem B2526805 : Blo 884570 2526805 := bbase (se 8 (by rfl) ⟨14805, by rfl⟩ : syracuseStep 2526805 = 29611) (by norm_num)
theorem B2985605 : Blo 884570 2985605 := bbase (se 4 (by rfl) ⟨279900, by rfl⟩ : syracuseStep 2985605 = 559801) (by norm_num)
theorem B2133877 : Blo 884570 2133877 := bbase (se 5 (by rfl) ⟨100025, by rfl⟩ : syracuseStep 2133877 = 200051) (by norm_num)
theorem B15339413 : Blo 884570 15339413 := bbase (se 6 (by rfl) ⟨359517, by rfl⟩ : syracuseStep 15339413 = 719035) (by norm_num)
theorem B2986037 : Blo 884570 2986037 := bbase (se 5 (by rfl) ⟨139970, by rfl⟩ : syracuseStep 2986037 = 279941) (by norm_num)
theorem B5050421 : Blo 884570 5050421 := bbase (se 5 (by rfl) ⟨236738, by rfl⟩ : syracuseStep 5050421 = 473477) (by norm_num)
theorem B4493717 : Blo 884570 4493717 := bbase (se 6 (by rfl) ⟨105321, by rfl⟩ : syracuseStep 4493717 = 210643) (by norm_num)
theorem B1708445 : Blo 884570 1708445 := bbase (se 3 (by rfl) ⟨320333, by rfl⟩ : syracuseStep 1708445 = 640667) (by norm_num)
theorem B2134453 : Blo 884570 2134453 := bbase (se 5 (by rfl) ⟨100052, by rfl⟩ : syracuseStep 2134453 = 200105) (by norm_num)
theorem B2986469 : Blo 884570 2986469 := bbase (se 4 (by rfl) ⟨279981, by rfl⟩ : syracuseStep 2986469 = 559963) (by norm_num)
theorem B1708661 : Blo 884570 1708661 := bbase (se 5 (by rfl) ⟨80093, by rfl⟩ : syracuseStep 1708661 = 160187) (by norm_num)
theorem B2134781 : Blo 884570 2134781 := bbase (se 3 (by rfl) ⟨400271, by rfl⟩ : syracuseStep 2134781 = 800543) (by norm_num)
theorem B2134837 : Blo 884570 2134837 := bbase (se 5 (by rfl) ⟨100070, by rfl⟩ : syracuseStep 2134837 = 200141) (by norm_num)
theorem B2986901 : Blo 884570 2986901 := bbase (se 6 (by rfl) ⟨70005, by rfl⟩ : syracuseStep 2986901 = 140011) (by norm_num)
theorem B2528309 : Blo 884570 2528309 := bbase (se 5 (by rfl) ⟨118514, by rfl⟩ : syracuseStep 2528309 = 237029) (by norm_num)
theorem B4265045 : Blo 884570 4265045 := bbase (se 8 (by rfl) ⟨24990, by rfl⟩ : syracuseStep 4265045 = 49981) (by norm_num)
theorem B5051605 : Blo 884570 5051605 := bbase (se 7 (by rfl) ⟨59198, by rfl⟩ : syracuseStep 5051605 = 118397) (by norm_num)
theorem B6722837 : Blo 884570 6722837 := bbase (se 6 (by rfl) ⟨157566, by rfl⟩ : syracuseStep 6722837 = 315133) (by norm_num)
theorem B2987333 : Blo 884570 2987333 := bbase (se 4 (by rfl) ⟨280062, by rfl⟩ : syracuseStep 2987333 = 560125) (by norm_num)
theorem B1119577 : Blo 884570 1119577 := bbase (se 2 (by rfl) ⟨419841, by rfl⟩ : syracuseStep 1119577 = 839683) (by norm_num)
theorem B1709429 : Blo 884570 1709429 := bbase (se 5 (by rfl) ⟨80129, by rfl⟩ : syracuseStep 1709429 = 160259) (by norm_num)
theorem B1119673 : Blo 884570 1119673 := bbase (se 2 (by rfl) ⟨419877, by rfl⟩ : syracuseStep 1119673 = 839755) (by norm_num)
theorem B1119845 : Blo 884570 1119845 := bbase (se 4 (by rfl) ⟨104985, by rfl⟩ : syracuseStep 1119845 = 209971) (by norm_num)
theorem B2692709 : Blo 884570 2692709 := bbase (se 4 (by rfl) ⟨252441, by rfl⟩ : syracuseStep 2692709 = 504883) (by norm_num)
theorem B2692757 : Blo 884570 2692757 := bbase (se 6 (by rfl) ⟨63111, by rfl⟩ : syracuseStep 2692757 = 126223) (by norm_num)
theorem B1119901 : Blo 884570 1119901 := bbase (se 3 (by rfl) ⟨209981, by rfl⟩ : syracuseStep 1119901 = 419963) (by norm_num)
theorem B4495013 : Blo 884570 4495013 := bbase (se 4 (by rfl) ⟨421407, by rfl⟩ : syracuseStep 4495013 = 842815) (by norm_num)
theorem B7575221 : Blo 884570 7575221 := bbase (se 5 (by rfl) ⟨355088, by rfl⟩ : syracuseStep 7575221 = 710177) (by norm_num)
theorem B2987765 : Blo 884570 2987765 := bbase (se 5 (by rfl) ⟨140051, by rfl⟩ : syracuseStep 2987765 = 280103) (by norm_num)
theorem B1119997 : Blo 884570 1119997 := bbase (se 3 (by rfl) ⟨209999, by rfl⟩ : syracuseStep 1119997 = 419999) (by norm_num)
theorem B2561861 : Blo 884570 2561861 := bbase (se 4 (by rfl) ⟨240174, by rfl⟩ : syracuseStep 2561861 = 480349) (by norm_num)
theorem B3839845 : Blo 884570 3839845 := bbase (se 4 (by rfl) ⟨359985, by rfl⟩ : syracuseStep 3839845 = 719971) (by norm_num)
theorem B1120169 : Blo 884570 1120169 := bbase (se 2 (by rfl) ⟨420063, by rfl⟩ : syracuseStep 1120169 = 840127) (by norm_num)
theorem B1120225 : Blo 884570 1120225 := bbase (se 2 (by rfl) ⟨420084, by rfl⟩ : syracuseStep 1120225 = 840169) (by norm_num)
theorem B1120321 : Blo 884570 1120321 := bbase (se 2 (by rfl) ⟨420120, by rfl⟩ : syracuseStep 1120321 = 840241) (by norm_num)
theorem B2988197 : Blo 884570 2988197 := bbase (se 4 (by rfl) ⟨280143, by rfl⟩ : syracuseStep 2988197 = 560287) (by norm_num)
theorem B1120493 : Blo 884570 1120493 := bbase (se 3 (by rfl) ⟨210092, by rfl⟩ : syracuseStep 1120493 = 420185) (by norm_num)
theorem B1120549 : Blo 884570 1120549 := bbase (se 4 (by rfl) ⟨105051, by rfl⟩ : syracuseStep 1120549 = 210103) (by norm_num)
theorem B1120645 : Blo 884570 1120645 := bbase (se 4 (by rfl) ⟨105060, by rfl⟩ : syracuseStep 1120645 = 210121) (by norm_num)
theorem B2693621 : Blo 884570 2693621 := bbase (se 5 (by rfl) ⟨126263, by rfl⟩ : syracuseStep 2693621 = 252527) (by norm_num)
theorem B2398709 : Blo 884570 2398709 := bbase (se 5 (by rfl) ⟨112439, by rfl⟩ : syracuseStep 2398709 = 224879) (by norm_num)
theorem B1120817 : Blo 884570 1120817 := bbase (se 2 (by rfl) ⟨420306, by rfl⟩ : syracuseStep 1120817 = 840613) (by norm_num)
theorem B2988629 : Blo 884570 2988629 := bbase (se 8 (by rfl) ⟨17511, by rfl⟩ : syracuseStep 2988629 = 35023) (by norm_num)
theorem B2529893 : Blo 884570 2529893 := bbase (se 4 (by rfl) ⟨237177, by rfl⟩ : syracuseStep 2529893 = 474355) (by norm_num)
theorem B1120873 : Blo 884570 1120873 := bbase (se 2 (by rfl) ⟨420327, by rfl⟩ : syracuseStep 1120873 = 840655) (by norm_num)
theorem B1120969 : Blo 884570 1120969 := bbase (se 2 (by rfl) ⟨420363, by rfl⟩ : syracuseStep 1120969 = 840727) (by norm_num)
theorem B1121141 : Blo 884570 1121141 := bbase (se 5 (by rfl) ⟨52553, by rfl⟩ : syracuseStep 1121141 = 105107) (by norm_num)
theorem B1121197 : Blo 884570 1121197 := bbase (se 3 (by rfl) ⟨210224, by rfl⟩ : syracuseStep 1121197 = 420449) (by norm_num)
theorem B2726837 : Blo 884570 2726837 := bbase (se 5 (by rfl) ⟨127820, by rfl⟩ : syracuseStep 2726837 = 255641) (by norm_num)
theorem B4496309 : Blo 884570 4496309 := bbase (se 5 (by rfl) ⟨210764, by rfl⟩ : syracuseStep 4496309 = 421529) (by norm_num)
theorem B1350589 : Blo 884570 1350589 := bbase (se 3 (by rfl) ⟨253235, by rfl⟩ : syracuseStep 1350589 = 506471) (by norm_num)
theorem B2989061 : Blo 884570 2989061 := bbase (se 4 (by rfl) ⟨280224, by rfl⟩ : syracuseStep 2989061 = 560449) (by norm_num)
theorem B1121293 : Blo 884570 1121293 := bbase (se 3 (by rfl) ⟨210242, by rfl⟩ : syracuseStep 1121293 = 420485) (by norm_num)
theorem B5676085 : Blo 884570 5676085 := bbase (se 5 (by rfl) ⟨266066, by rfl⟩ : syracuseStep 5676085 = 532133) (by norm_num)
theorem B5053589 : Blo 884570 5053589 := bbase (se 6 (by rfl) ⟨118443, by rfl⟩ : syracuseStep 5053589 = 236887) (by norm_num)
theorem B1121465 : Blo 884570 1121465 := bbase (se 2 (by rfl) ⟨420549, by rfl⟩ : syracuseStep 1121465 = 841099) (by norm_num)
theorem B1121521 : Blo 884570 1121521 := bbase (se 2 (by rfl) ⟨420570, by rfl⟩ : syracuseStep 1121521 = 841141) (by norm_num)
theorem B957745 : Blo 884570 957745 := bbase (se 2 (by rfl) ⟨359154, by rfl⟩ : syracuseStep 957745 = 718309) (by norm_num)
theorem B1121617 : Blo 884570 1121617 := bbase (se 2 (by rfl) ⟨420606, by rfl⟩ : syracuseStep 1121617 = 841213) (by norm_num)
theorem B2989493 : Blo 884570 2989493 := bbase (se 5 (by rfl) ⟨140132, by rfl⟩ : syracuseStep 2989493 = 280265) (by norm_num)
theorem B1121789 : Blo 884570 1121789 := bbase (se 3 (by rfl) ⟨210335, by rfl⟩ : syracuseStep 1121789 = 420671) (by norm_num)
theorem B1121845 : Blo 884570 1121845 := bbase (se 5 (by rfl) ⟨52586, by rfl⟩ : syracuseStep 1121845 = 105173) (by norm_num)
theorem B1121941 : Blo 884570 1121941 := bbase (se 6 (by rfl) ⟨26295, by rfl⟩ : syracuseStep 1121941 = 52591) (by norm_num)
theorem B1154837 : Blo 884570 1154837 := bbase (se 6 (by rfl) ⟨27066, by rfl⟩ : syracuseStep 1154837 = 54133) (by norm_num)
theorem B4267829 : Blo 884570 4267829 := bbase (se 5 (by rfl) ⟨200054, by rfl⟩ : syracuseStep 4267829 = 400109) (by norm_num)
theorem B1122113 : Blo 884570 1122113 := bbase (se 2 (by rfl) ⟨420792, by rfl⟩ : syracuseStep 1122113 = 841585) (by norm_num)
theorem B2989925 : Blo 884570 2989925 := bbase (se 4 (by rfl) ⟨280305, by rfl⟩ : syracuseStep 2989925 = 560611) (by norm_num)
theorem B1122169 : Blo 884570 1122169 := bbase (se 2 (by rfl) ⟨420813, by rfl⟩ : syracuseStep 1122169 = 841627) (by norm_num)
theorem B2695045 : Blo 884570 2695045 := bbase (se 4 (by rfl) ⟨252660, by rfl⟩ : syracuseStep 2695045 = 505321) (by norm_num)
theorem B1122265 : Blo 884570 1122265 := bbase (se 2 (by rfl) ⟨420849, by rfl⟩ : syracuseStep 1122265 = 841699) (by norm_num)
theorem B6823925 : Blo 884570 6823925 := bbase (se 5 (by rfl) ⟨319871, by rfl⟩ : syracuseStep 6823925 = 639743) (by norm_num)
theorem B2400245 : Blo 884570 2400245 := bbase (se 5 (by rfl) ⟨112511, by rfl⟩ : syracuseStep 2400245 = 225023) (by norm_num)
theorem B16162901 : Blo 884570 16162901 := bbase (se 8 (by rfl) ⟨94704, by rfl⟩ : syracuseStep 16162901 = 189409) (by norm_num)
theorem B1122437 : Blo 884570 1122437 := bbase (se 4 (by rfl) ⟨105228, by rfl⟩ : syracuseStep 1122437 = 210457) (by norm_num)
theorem B1024153 : Blo 884570 1024153 := bbase (se 2 (by rfl) ⟨384057, by rfl⟩ : syracuseStep 1024153 = 768115) (by norm_num)
theorem B1679525 : Blo 884570 1679525 := bbase (se 4 (by rfl) ⟨157455, by rfl⟩ : syracuseStep 1679525 = 314911) (by norm_num)
theorem B1417381 : Blo 884570 1417381 := bbase (se 4 (by rfl) ⟨132879, by rfl⟩ : syracuseStep 1417381 = 265759) (by norm_num)
theorem B1122493 : Blo 884570 1122493 := bbase (se 3 (by rfl) ⟨210467, by rfl⟩ : syracuseStep 1122493 = 420935) (by norm_num)
theorem B4497605 : Blo 884570 4497605 := bbase (se 4 (by rfl) ⟨421650, by rfl⟩ : syracuseStep 4497605 = 843301) (by norm_num)
theorem B2990357 : Blo 884570 2990357 := bbase (se 6 (by rfl) ⟨70086, by rfl⟩ : syracuseStep 2990357 = 140173) (by norm_num)
theorem B1122589 : Blo 884570 1122589 := bbase (se 3 (by rfl) ⟨210485, by rfl⟩ : syracuseStep 1122589 = 420971) (by norm_num)
theorem B1122761 : Blo 884570 1122761 := bbase (se 2 (by rfl) ⟨421035, by rfl⟩ : syracuseStep 1122761 = 842071) (by norm_num)
theorem B1122817 : Blo 884570 1122817 := bbase (se 2 (by rfl) ⟨421056, by rfl⟩ : syracuseStep 1122817 = 842113) (by norm_num)
theorem B7578197 : Blo 884570 7578197 := bbase (se 8 (by rfl) ⟨44403, by rfl⟩ : syracuseStep 7578197 = 88807) (by norm_num)
theorem B1122913 : Blo 884570 1122913 := bbase (se 2 (by rfl) ⟨421092, by rfl⟩ : syracuseStep 1122913 = 842185) (by norm_num)
theorem B1417837 : Blo 884570 1417837 := bbase (se 3 (by rfl) ⟨265844, by rfl⟩ : syracuseStep 1417837 = 531689) (by norm_num)
theorem B2990789 : Blo 884570 2990789 := bbase (se 4 (by rfl) ⟨280386, by rfl⟩ : syracuseStep 2990789 = 560773) (by norm_num)
theorem B1123085 : Blo 884570 1123085 := bbase (se 3 (by rfl) ⟨210578, by rfl⟩ : syracuseStep 1123085 = 421157) (by norm_num)
theorem B1123141 : Blo 884570 1123141 := bbase (se 4 (by rfl) ⟨105294, by rfl⟩ : syracuseStep 1123141 = 210589) (by norm_num)
theorem B1680277 : Blo 884570 1680277 := bbase (se 6 (by rfl) ⟨39381, by rfl⟩ : syracuseStep 1680277 = 78763) (by norm_num)
theorem B1123237 : Blo 884570 1123237 := bbase (se 4 (by rfl) ⟨105303, by rfl⟩ : syracuseStep 1123237 = 210607) (by norm_num)
theorem B1516501 : Blo 884570 1516501 := bbase (se 7 (by rfl) ⟨17771, by rfl⟩ : syracuseStep 1516501 = 35543) (by norm_num)
theorem B1680421 : Blo 884570 1680421 := bbase (se 4 (by rfl) ⟨157539, by rfl⟩ : syracuseStep 1680421 = 315079) (by norm_num)
theorem B1123409 : Blo 884570 1123409 := bbase (se 2 (by rfl) ⟨421278, by rfl⟩ : syracuseStep 1123409 = 842557) (by norm_num)
theorem B2991221 : Blo 884570 2991221 := bbase (se 5 (by rfl) ⟨140213, by rfl⟩ : syracuseStep 2991221 = 280427) (by norm_num)
theorem B1123465 : Blo 884570 1123465 := bbase (se 2 (by rfl) ⟨421299, by rfl⟩ : syracuseStep 1123465 = 842599) (by norm_num)
theorem B4793525 : Blo 884570 4793525 := bbase (se 5 (by rfl) ⟨224696, by rfl⟩ : syracuseStep 4793525 = 449393) (by norm_num)
theorem B1680581 : Blo 884570 1680581 := bbase (se 4 (by rfl) ⟨157554, by rfl⟩ : syracuseStep 1680581 = 315109) (by norm_num)
theorem B1123561 : Blo 884570 1123561 := bbase (se 2 (by rfl) ⟨421335, by rfl⟩ : syracuseStep 1123561 = 842671) (by norm_num)
theorem B1418509 : Blo 884570 1418509 := bbase (se 3 (by rfl) ⟨265970, by rfl⟩ : syracuseStep 1418509 = 531941) (by norm_num)
theorem B5055797 : Blo 884570 5055797 := bbase (se 5 (by rfl) ⟨236990, by rfl⟩ : syracuseStep 5055797 = 473981) (by norm_num)
theorem B1680725 : Blo 884570 1680725 := bbase (se 12 (by rfl) ⟨615, by rfl⟩ : syracuseStep 1680725 = 1231) (by norm_num)
theorem B1123733 : Blo 884570 1123733 := bbase (se 6 (by rfl) ⟨26337, by rfl⟩ : syracuseStep 1123733 = 52675) (by norm_num)
theorem B4105637 : Blo 884570 4105637 := bbase (se 4 (by rfl) ⟨384903, by rfl⟩ : syracuseStep 4105637 = 769807) (by norm_num)
theorem B1123789 : Blo 884570 1123789 := bbase (se 3 (by rfl) ⟨210710, by rfl⟩ : syracuseStep 1123789 = 421421) (by norm_num)
theorem B2991653 : Blo 884570 2991653 := bbase (se 4 (by rfl) ⟨280467, by rfl⟩ : syracuseStep 2991653 = 560935) (by norm_num)
theorem B1123885 : Blo 884570 1123885 := bbase (se 3 (by rfl) ⟨210728, by rfl⟩ : syracuseStep 1123885 = 421457) (by norm_num)
theorem B1681013 : Blo 884570 1681013 := bbase (se 5 (by rfl) ⟨78797, by rfl⟩ : syracuseStep 1681013 = 157595) (by norm_num)
theorem B1418933 : Blo 884570 1418933 := bbase (se 5 (by rfl) ⟨66512, by rfl⟩ : syracuseStep 1418933 = 133025) (by norm_num)
theorem B7186133 : Blo 884570 7186133 := bbase (se 7 (by rfl) ⟨84212, by rfl⟩ : syracuseStep 7186133 = 168425) (by norm_num)
theorem B1124057 : Blo 884570 1124057 := bbase (se 2 (by rfl) ⟨421521, by rfl⟩ : syracuseStep 1124057 = 843043) (by norm_num)
theorem B1681165 : Blo 884570 1681165 := bbase (se 3 (by rfl) ⟨315218, by rfl⟩ : syracuseStep 1681165 = 630437) (by norm_num)
theorem B1124113 : Blo 884570 1124113 := bbase (se 2 (by rfl) ⟨421542, by rfl⟩ : syracuseStep 1124113 = 843085) (by norm_num)
theorem B9086741 : Blo 884570 9086741 := bbase (se 6 (by rfl) ⟨212970, by rfl⟩ : syracuseStep 9086741 = 425941) (by norm_num)
theorem B1124209 : Blo 884570 1124209 := bbase (se 2 (by rfl) ⟨421578, by rfl⟩ : syracuseStep 1124209 = 843157) (by norm_num)
theorem B1419221 : Blo 884570 1419221 := bbase (se 7 (by rfl) ⟨16631, by rfl⟩ : syracuseStep 1419221 = 33263) (by norm_num)
theorem B2992085 : Blo 884570 2992085 := bbase (se 7 (by rfl) ⟨35063, by rfl⟩ : syracuseStep 2992085 = 70127) (by norm_num)
theorem B4106213 : Blo 884570 4106213 := bbase (se 4 (by rfl) ⟨384957, by rfl⟩ : syracuseStep 4106213 = 769915) (by norm_num)
theorem B12757013 : Blo 884570 12757013 := bbase (se 6 (by rfl) ⟨298992, by rfl⟩ : syracuseStep 12757013 = 597985) (by norm_num)
theorem B1124381 : Blo 884570 1124381 := bbase (se 3 (by rfl) ⟨210821, by rfl⟩ : syracuseStep 1124381 = 421643) (by norm_num)
theorem B1681469 : Blo 884570 1681469 := bbase (se 3 (by rfl) ⟨315275, by rfl⟩ : syracuseStep 1681469 = 630551) (by norm_num)
theorem B3188821 : Blo 884570 3188821 := bbase (se 8 (by rfl) ⟨18684, by rfl⟩ : syracuseStep 3188821 = 37369) (by norm_num)
theorem B1124437 : Blo 884570 1124437 := bbase (se 8 (by rfl) ⟨6588, by rfl⟩ : syracuseStep 1124437 = 13177) (by norm_num)
theorem B1517741 : Blo 884570 1517741 := bbase (se 3 (by rfl) ⟨284576, by rfl⟩ : syracuseStep 1517741 = 569153) (by norm_num)
theorem B1124533 : Blo 884570 1124533 := bbase (se 5 (by rfl) ⟨52712, by rfl⟩ : syracuseStep 1124533 = 105425) (by norm_num)
theorem B2992517 : Blo 884570 2992517 := bbase (se 4 (by rfl) ⟨280548, by rfl⟩ : syracuseStep 2992517 = 561097) (by norm_num)
theorem B6400565 : Blo 884570 6400565 := bbase (se 5 (by rfl) ⟨300026, by rfl⟩ : syracuseStep 6400565 = 600053) (by norm_num)
theorem B4041397 : Blo 884570 4041397 := bbase (se 5 (by rfl) ⟨189440, by rfl⟩ : syracuseStep 4041397 = 378881) (by norm_num)
theorem B1420021 : Blo 884570 1420021 := bbase (se 5 (by rfl) ⟨66563, by rfl⟩ : syracuseStep 1420021 = 133127) (by norm_num)
theorem B1682221 : Blo 884570 1682221 := bbase (se 3 (by rfl) ⟨315416, by rfl⟩ : syracuseStep 1682221 = 630833) (by norm_num)
theorem B2239285 : Blo 884570 2239285 := bbase (se 5 (by rfl) ⟨104966, by rfl⟩ : syracuseStep 2239285 = 209933) (by norm_num)
theorem B3189557 : Blo 884570 3189557 := bbase (se 5 (by rfl) ⟨149510, by rfl⟩ : syracuseStep 3189557 = 299021) (by norm_num)
theorem B2992949 : Blo 884570 2992949 := bbase (se 5 (by rfl) ⟨140294, by rfl⟩ : syracuseStep 2992949 = 280589) (by norm_num)
theorem B1026965 : Blo 884570 1026965 := bbase (se 6 (by rfl) ⟨24069, by rfl⟩ : syracuseStep 1026965 = 48139) (by norm_num)
theorem B2239397 : Blo 884570 2239397 := bbase (se 4 (by rfl) ⟨209943, by rfl⟩ : syracuseStep 2239397 = 419887) (by norm_num)
theorem B1682365 : Blo 884570 1682365 := bbase (se 3 (by rfl) ⟨315443, by rfl⟩ : syracuseStep 1682365 = 630887) (by norm_num)
theorem B1682525 : Blo 884570 1682525 := bbase (se 3 (by rfl) ⟨315473, by rfl⟩ : syracuseStep 1682525 = 630947) (by norm_num)
theorem B2239589 : Blo 884570 2239589 := bbase (se 4 (by rfl) ⟨209961, by rfl⟩ : syracuseStep 2239589 = 419923) (by norm_num)
theorem B2993381 : Blo 884570 2993381 := bbase (se 4 (by rfl) ⟨280629, by rfl⟩ : syracuseStep 2993381 = 561259) (by norm_num)
theorem B1682669 : Blo 884570 1682669 := bbase (se 3 (by rfl) ⟨315500, by rfl⟩ : syracuseStep 1682669 = 631001) (by norm_num)
theorem B1420573 : Blo 884570 1420573 := bbase (se 3 (by rfl) ⟨266357, by rfl⟩ : syracuseStep 1420573 = 532715) (by norm_num)
theorem B2239933 : Blo 884570 2239933 := bbase (se 3 (by rfl) ⟨419987, by rfl⟩ : syracuseStep 2239933 = 839975) (by norm_num)
theorem B5385685 : Blo 884570 5385685 := bbase (se 7 (by rfl) ⟨63113, by rfl⟩ : syracuseStep 5385685 = 126227) (by norm_num)
theorem B3190261 : Blo 884570 3190261 := bbase (se 5 (by rfl) ⟨149543, by rfl⟩ : syracuseStep 3190261 = 299087) (by norm_num)
theorem B1682957 : Blo 884570 1682957 := bbase (se 3 (by rfl) ⟨315554, by rfl⟩ : syracuseStep 1682957 = 631109) (by norm_num)
theorem B1420829 : Blo 884570 1420829 := bbase (se 3 (by rfl) ⟨266405, by rfl⟩ : syracuseStep 1420829 = 532811) (by norm_num)
theorem B2240045 : Blo 884570 2240045 := bbase (se 3 (by rfl) ⟨420008, by rfl⟩ : syracuseStep 2240045 = 840017) (by norm_num)
theorem B2993813 : Blo 884570 2993813 := bbase (se 6 (by rfl) ⟨70167, by rfl⟩ : syracuseStep 2993813 = 140335) (by norm_num)
theorem B1683109 : Blo 884570 1683109 := bbase (se 4 (by rfl) ⟨157791, by rfl⟩ : syracuseStep 1683109 = 315583) (by norm_num)
theorem B2240237 : Blo 884570 2240237 := bbase (se 3 (by rfl) ⟨420044, by rfl⟩ : syracuseStep 2240237 = 840089) (by norm_num)
theorem B995161 : Blo 884570 995161 := bbase (se 2 (by rfl) ⟨373185, by rfl⟩ : syracuseStep 995161 = 746371) (by norm_num)
theorem B896881 : Blo 884570 896881 := bbase (se 2 (by rfl) ⟨336330, by rfl⟩ : syracuseStep 896881 = 672661) (by norm_num)
theorem B995197 : Blo 884570 995197 := bbase (se 3 (by rfl) ⟨186599, by rfl⟩ : syracuseStep 995197 = 373199) (by norm_num)
theorem B995233 : Blo 884570 995233 := bbase (se 2 (by rfl) ⟨373212, by rfl⟩ : syracuseStep 995233 = 746425) (by norm_num)
theorem B995269 : Blo 884570 995269 := bbase (se 4 (by rfl) ⟨93306, by rfl⟩ : syracuseStep 995269 = 186613) (by norm_num)
theorem B1683413 : Blo 884570 1683413 := bbase (se 7 (by rfl) ⟨19727, by rfl⟩ : syracuseStep 1683413 = 39455) (by norm_num)
theorem B995305 : Blo 884570 995305 := bbase (se 2 (by rfl) ⟨373239, by rfl⟩ : syracuseStep 995305 = 746479) (by norm_num)
theorem B995341 : Blo 884570 995341 := bbase (se 3 (by rfl) ⟨186626, by rfl⟩ : syracuseStep 995341 = 373253) (by norm_num)
theorem B995377 : Blo 884570 995377 := bbase (se 2 (by rfl) ⟨373266, by rfl⟩ : syracuseStep 995377 = 746533) (by norm_num)
theorem B2240581 : Blo 884570 2240581 := bbase (se 4 (by rfl) ⟨210054, by rfl⟩ : syracuseStep 2240581 = 420109) (by norm_num)
theorem B2994245 : Blo 884570 2994245 := bbase (se 4 (by rfl) ⟨280710, by rfl⟩ : syracuseStep 2994245 = 561421) (by norm_num)
theorem B995413 : Blo 884570 995413 := bbase (se 8 (by rfl) ⟨5832, by rfl⟩ : syracuseStep 995413 = 11665) (by norm_num)
theorem B995449 : Blo 884570 995449 := bbase (se 2 (by rfl) ⟨373293, by rfl⟩ : syracuseStep 995449 = 746587) (by norm_num)
theorem B995485 : Blo 884570 995485 := bbase (se 3 (by rfl) ⟨186653, by rfl⟩ : syracuseStep 995485 = 373307) (by norm_num)
theorem B2240693 : Blo 884570 2240693 := bbase (se 5 (by rfl) ⟨105032, by rfl⟩ : syracuseStep 2240693 = 210065) (by norm_num)
theorem B995521 : Blo 884570 995521 := bbase (se 2 (by rfl) ⟨373320, by rfl⟩ : syracuseStep 995521 = 746641) (by norm_num)
theorem B1421533 : Blo 884570 1421533 := bbase (se 3 (by rfl) ⟨266537, by rfl⟩ : syracuseStep 1421533 = 533075) (by norm_num)
theorem B995557 : Blo 884570 995557 := bbase (se 4 (by rfl) ⟨93333, by rfl⟩ : syracuseStep 995557 = 186667) (by norm_num)
theorem B995593 : Blo 884570 995593 := bbase (se 2 (by rfl) ⟨373347, by rfl⟩ : syracuseStep 995593 = 746695) (by norm_num)
theorem B995629 : Blo 884570 995629 := bbase (se 3 (by rfl) ⟨186680, by rfl⟩ : syracuseStep 995629 = 373361) (by norm_num)
theorem B995665 : Blo 884570 995665 := bbase (se 2 (by rfl) ⟨373374, by rfl⟩ : syracuseStep 995665 = 746749) (by norm_num)
theorem B995701 : Blo 884570 995701 := bbase (se 5 (by rfl) ⟨46673, by rfl⟩ : syracuseStep 995701 = 93347) (by norm_num)
theorem B2240885 : Blo 884570 2240885 := bbase (se 5 (by rfl) ⟨105041, by rfl⟩ : syracuseStep 2240885 = 210083) (by norm_num)
theorem B995737 : Blo 884570 995737 := bbase (se 2 (by rfl) ⟨373401, by rfl⟩ : syracuseStep 995737 = 746803) (by norm_num)
theorem B995773 : Blo 884570 995773 := bbase (se 3 (by rfl) ⟨186707, by rfl⟩ : syracuseStep 995773 = 373415) (by norm_num)
theorem B995809 : Blo 884570 995809 := bbase (se 2 (by rfl) ⟨373428, by rfl⟩ : syracuseStep 995809 = 746857) (by norm_num)
theorem B2994677 : Blo 884570 2994677 := bbase (se 5 (by rfl) ⟨140375, by rfl⟩ : syracuseStep 2994677 = 280751) (by norm_num)
theorem B995845 : Blo 884570 995845 := bbase (se 4 (by rfl) ⟨93360, by rfl⟩ : syracuseStep 995845 = 186721) (by norm_num)
theorem B995881 : Blo 884570 995881 := bbase (se 2 (by rfl) ⟨373455, by rfl⟩ : syracuseStep 995881 = 746911) (by norm_num)
theorem B995917 : Blo 884570 995917 := bbase (se 3 (by rfl) ⟨186734, by rfl⟩ : syracuseStep 995917 = 373469) (by norm_num)
theorem B995953 : Blo 884570 995953 := bbase (se 2 (by rfl) ⟨373482, by rfl⟩ : syracuseStep 995953 = 746965) (by norm_num)
theorem B1421957 : Blo 884570 1421957 := bbase (se 4 (by rfl) ⟨133308, by rfl⟩ : syracuseStep 1421957 = 266617) (by norm_num)
theorem B995989 : Blo 884570 995989 := bbase (se 6 (by rfl) ⟨23343, by rfl⟩ : syracuseStep 995989 = 46687) (by norm_num)
theorem B996025 : Blo 884570 996025 := bbase (se 2 (by rfl) ⟨373509, by rfl⟩ : syracuseStep 996025 = 747019) (by norm_num)
theorem B1684165 : Blo 884570 1684165 := bbase (se 4 (by rfl) ⟨157890, by rfl⟩ : syracuseStep 1684165 = 315781) (by norm_num)
theorem B2241229 : Blo 884570 2241229 := bbase (se 3 (by rfl) ⟨420230, by rfl⟩ : syracuseStep 2241229 = 840461) (by norm_num)
theorem B996061 : Blo 884570 996061 := bbase (se 3 (by rfl) ⟨186761, by rfl⟩ : syracuseStep 996061 = 373523) (by norm_num)
theorem B996097 : Blo 884570 996097 := bbase (se 2 (by rfl) ⟨373536, by rfl⟩ : syracuseStep 996097 = 747073) (by norm_num)
theorem B996133 : Blo 884570 996133 := bbase (se 4 (by rfl) ⟨93387, by rfl⟩ : syracuseStep 996133 = 186775) (by norm_num)
theorem B2241341 : Blo 884570 2241341 := bbase (se 3 (by rfl) ⟨420251, by rfl⟩ : syracuseStep 2241341 = 840503) (by norm_num)
theorem B996169 : Blo 884570 996169 := bbase (se 2 (by rfl) ⟨373563, by rfl⟩ : syracuseStep 996169 = 747127) (by norm_num)
theorem B1684309 : Blo 884570 1684309 := bbase (se 9 (by rfl) ⟨4934, by rfl⟩ : syracuseStep 1684309 = 9869) (by norm_num)
theorem B996205 : Blo 884570 996205 := bbase (se 3 (by rfl) ⟨186788, by rfl⟩ : syracuseStep 996205 = 373577) (by norm_num)
theorem B6730613 : Blo 884570 6730613 := bbase (se 5 (by rfl) ⟨315497, by rfl⟩ : syracuseStep 6730613 = 630995) (by norm_num)
theorem B996241 : Blo 884570 996241 := bbase (se 2 (by rfl) ⟨373590, by rfl⟩ : syracuseStep 996241 = 747181) (by norm_num)
theorem B2995109 : Blo 884570 2995109 := bbase (se 4 (by rfl) ⟨280791, by rfl⟩ : syracuseStep 2995109 = 561583) (by norm_num)
theorem B1422245 : Blo 884570 1422245 := bbase (se 4 (by rfl) ⟨133335, by rfl⟩ : syracuseStep 1422245 = 266671) (by norm_num)
theorem B996277 : Blo 884570 996277 := bbase (se 5 (by rfl) ⟨46700, by rfl⟩ : syracuseStep 996277 = 93401) (by norm_num)
theorem B996313 : Blo 884570 996313 := bbase (se 2 (by rfl) ⟨373617, by rfl⟩ : syracuseStep 996313 = 747235) (by norm_num)
theorem B1684469 : Blo 884570 1684469 := bbase (se 5 (by rfl) ⟨78959, by rfl⟩ : syracuseStep 1684469 = 157919) (by norm_num)
theorem B2241533 : Blo 884570 2241533 := bbase (se 3 (by rfl) ⟨420287, by rfl⟩ : syracuseStep 2241533 = 840575) (by norm_num)
theorem B996349 : Blo 884570 996349 := bbase (se 3 (by rfl) ⟨186815, by rfl⟩ : syracuseStep 996349 = 373631) (by norm_num)
theorem B996385 : Blo 884570 996385 := bbase (se 2 (by rfl) ⟨373644, by rfl⟩ : syracuseStep 996385 = 747289) (by norm_num)
theorem B996421 : Blo 884570 996421 := bbase (se 4 (by rfl) ⟨93414, by rfl⟩ : syracuseStep 996421 = 186829) (by norm_num)
theorem B996457 : Blo 884570 996457 := bbase (se 2 (by rfl) ⟨373671, by rfl⟩ : syracuseStep 996457 = 747343) (by norm_num)
theorem B1684613 : Blo 884570 1684613 := bbase (se 4 (by rfl) ⟨157932, by rfl⟩ : syracuseStep 1684613 = 315865) (by norm_num)
theorem B1422469 : Blo 884570 1422469 := bbase (se 4 (by rfl) ⟨133356, by rfl⟩ : syracuseStep 1422469 = 266713) (by norm_num)
theorem B996493 : Blo 884570 996493 := bbase (se 3 (by rfl) ⟨186842, by rfl⟩ : syracuseStep 996493 = 373685) (by norm_num)
theorem B1619117 : Blo 884570 1619117 := bbase (se 3 (by rfl) ⟨303584, by rfl⟩ : syracuseStep 1619117 = 607169) (by norm_num)
theorem B996529 : Blo 884570 996529 := bbase (se 2 (by rfl) ⟨373698, by rfl⟩ : syracuseStep 996529 = 747397) (by norm_num)
theorem B996565 : Blo 884570 996565 := bbase (se 7 (by rfl) ⟨11678, by rfl⟩ : syracuseStep 996565 = 23357) (by norm_num)
theorem B996601 : Blo 884570 996601 := bbase (se 2 (by rfl) ⟨373725, by rfl⟩ : syracuseStep 996601 = 747451) (by norm_num)
theorem B996637 : Blo 884570 996637 := bbase (se 3 (by rfl) ⟨186869, by rfl⟩ : syracuseStep 996637 = 373739) (by norm_num)
theorem B996673 : Blo 884570 996673 := bbase (se 2 (by rfl) ⟨373752, by rfl⟩ : syracuseStep 996673 = 747505) (by norm_num)
theorem B2241877 : Blo 884570 2241877 := bbase (se 13 (by rfl) ⟨410, by rfl⟩ : syracuseStep 2241877 = 821) (by norm_num)
theorem B2995541 : Blo 884570 2995541 := bbase (se 13 (by rfl) ⟨548, by rfl⟩ : syracuseStep 2995541 = 1097) (by norm_num)
theorem B996709 : Blo 884570 996709 := bbase (se 4 (by rfl) ⟨93441, by rfl⟩ : syracuseStep 996709 = 186883) (by norm_num)
theorem B996745 : Blo 884570 996745 := bbase (se 2 (by rfl) ⟨373779, by rfl⟩ : syracuseStep 996745 = 747559) (by norm_num)
theorem B1684901 : Blo 884570 1684901 := bbase (se 4 (by rfl) ⟨157959, by rfl⟩ : syracuseStep 1684901 = 315919) (by norm_num)
theorem B996781 : Blo 884570 996781 := bbase (se 3 (by rfl) ⟨186896, by rfl⟩ : syracuseStep 996781 = 373793) (by norm_num)
theorem B2241989 : Blo 884570 2241989 := bbase (se 4 (by rfl) ⟨210186, by rfl⟩ : syracuseStep 2241989 = 420373) (by norm_num)
theorem B996817 : Blo 884570 996817 := bbase (se 2 (by rfl) ⟨373806, by rfl⟩ : syracuseStep 996817 = 747613) (by norm_num)
theorem B996853 : Blo 884570 996853 := bbase (se 5 (by rfl) ⟨46727, by rfl⟩ : syracuseStep 996853 = 93455) (by norm_num)
theorem B6829589 : Blo 884570 6829589 := bbase (se 6 (by rfl) ⟨160068, by rfl⟩ : syracuseStep 6829589 = 320137) (by norm_num)
theorem B996889 : Blo 884570 996889 := bbase (se 2 (by rfl) ⟨373833, by rfl⟩ : syracuseStep 996889 = 747667) (by norm_num)
theorem B996925 : Blo 884570 996925 := bbase (se 3 (by rfl) ⟨186923, by rfl⟩ : syracuseStep 996925 = 373847) (by norm_num)
theorem B1685053 : Blo 884570 1685053 := bbase (se 3 (by rfl) ⟨315947, by rfl⟩ : syracuseStep 1685053 = 631895) (by norm_num)
theorem B3782213 : Blo 884570 3782213 := bbase (se 4 (by rfl) ⟨354582, by rfl⟩ : syracuseStep 3782213 = 709165) (by norm_num)
theorem B6305365 : Blo 884570 6305365 := bbase (se 8 (by rfl) ⟨36945, by rfl⟩ : syracuseStep 6305365 = 73891) (by norm_num)
theorem B996961 : Blo 884570 996961 := bbase (se 2 (by rfl) ⟨373860, by rfl⟩ : syracuseStep 996961 = 747721) (by norm_num)
theorem B2242181 : Blo 884570 2242181 := bbase (se 4 (by rfl) ⟨210204, by rfl⟩ : syracuseStep 2242181 = 420409) (by norm_num)
theorem B996997 : Blo 884570 996997 := bbase (se 4 (by rfl) ⟨93468, by rfl⟩ : syracuseStep 996997 = 186937) (by norm_num)
theorem B997033 : Blo 884570 997033 := bbase (se 2 (by rfl) ⟨373887, by rfl⟩ : syracuseStep 997033 = 747775) (by norm_num)
theorem B997069 : Blo 884570 997069 := bbase (se 3 (by rfl) ⟨186950, by rfl⟩ : syracuseStep 997069 = 373901) (by norm_num)
theorem B997105 : Blo 884570 997105 := bbase (se 2 (by rfl) ⟨373914, by rfl⟩ : syracuseStep 997105 = 747829) (by norm_num)
theorem B2995973 : Blo 884570 2995973 := bbase (se 4 (by rfl) ⟨280872, by rfl⟩ : syracuseStep 2995973 = 561745) (by norm_num)
theorem B2045717 : Blo 884570 2045717 := bbase (se 6 (by rfl) ⟨47946, by rfl⟩ : syracuseStep 2045717 = 95893) (by norm_num)
theorem B997141 : Blo 884570 997141 := bbase (se 6 (by rfl) ⟨23370, by rfl⟩ : syracuseStep 997141 = 46741) (by norm_num)
theorem B997177 : Blo 884570 997177 := bbase (se 2 (by rfl) ⟨373941, by rfl⟩ : syracuseStep 997177 = 747883) (by norm_num)
theorem B997213 : Blo 884570 997213 := bbase (se 3 (by rfl) ⟨186977, by rfl⟩ : syracuseStep 997213 = 373955) (by norm_num)
theorem B1685357 : Blo 884570 1685357 := bbase (se 3 (by rfl) ⟨316004, by rfl⟩ : syracuseStep 1685357 = 632009) (by norm_num)
theorem B997249 : Blo 884570 997249 := bbase (se 2 (by rfl) ⟨373968, by rfl⟩ : syracuseStep 997249 = 747937) (by norm_num)
theorem B997285 : Blo 884570 997285 := bbase (se 4 (by rfl) ⟨93495, by rfl⟩ : syracuseStep 997285 = 186991) (by norm_num)
theorem B997321 : Blo 884570 997321 := bbase (se 2 (by rfl) ⟨373995, by rfl⟩ : syracuseStep 997321 = 747991) (by norm_num)
theorem B2242525 : Blo 884570 2242525 := bbase (se 3 (by rfl) ⟨420473, by rfl⟩ : syracuseStep 2242525 = 840947) (by norm_num)
theorem B997357 : Blo 884570 997357 := bbase (se 3 (by rfl) ⟨187004, by rfl⟩ : syracuseStep 997357 = 374009) (by norm_num)
theorem B997393 : Blo 884570 997393 := bbase (se 2 (by rfl) ⟨374022, by rfl⟩ : syracuseStep 997393 = 748045) (by norm_num)
theorem B997429 : Blo 884570 997429 := bbase (se 5 (by rfl) ⟨46754, by rfl⟩ : syracuseStep 997429 = 93509) (by norm_num)
theorem B2242637 : Blo 884570 2242637 := bbase (se 3 (by rfl) ⟨420494, by rfl⟩ : syracuseStep 2242637 = 840989) (by norm_num)
theorem B997465 : Blo 884570 997465 := bbase (se 2 (by rfl) ⟨374049, by rfl⟩ : syracuseStep 997465 = 748099) (by norm_num)
theorem B997501 : Blo 884570 997501 := bbase (se 3 (by rfl) ⟨187031, by rfl⟩ : syracuseStep 997501 = 374063) (by norm_num)
theorem B1620109 : Blo 884570 1620109 := bbase (se 3 (by rfl) ⟨303770, by rfl⟩ : syracuseStep 1620109 = 607541) (by norm_num)
theorem B997537 : Blo 884570 997537 := bbase (se 2 (by rfl) ⟨374076, by rfl⟩ : syracuseStep 997537 = 748153) (by norm_num)
theorem B2996405 : Blo 884570 2996405 := bbase (se 5 (by rfl) ⟨140456, by rfl⟩ : syracuseStep 2996405 = 280913) (by norm_num)
theorem B997573 : Blo 884570 997573 := bbase (se 4 (by rfl) ⟨93522, by rfl⟩ : syracuseStep 997573 = 187045) (by norm_num)
theorem B997609 : Blo 884570 997609 := bbase (se 2 (by rfl) ⟨374103, by rfl⟩ : syracuseStep 997609 = 748207) (by norm_num)
theorem B2275565 : Blo 884570 2275565 := bbase (se 3 (by rfl) ⟨426668, by rfl⟩ : syracuseStep 2275565 = 853337) (by norm_num)
theorem B5683445 : Blo 884570 5683445 := bbase (se 5 (by rfl) ⟨266411, by rfl⟩ : syracuseStep 5683445 = 532823) (by norm_num)
theorem B2242829 : Blo 884570 2242829 := bbase (se 3 (by rfl) ⟨420530, by rfl⟩ : syracuseStep 2242829 = 841061) (by norm_num)
theorem B997645 : Blo 884570 997645 := bbase (se 3 (by rfl) ⟨187058, by rfl⟩ : syracuseStep 997645 = 374117) (by norm_num)
theorem B997681 : Blo 884570 997681 := bbase (se 2 (by rfl) ⟨374130, by rfl⟩ : syracuseStep 997681 = 748261) (by norm_num)
theorem B997717 : Blo 884570 997717 := bbase (se 10 (by rfl) ⟨1461, by rfl⟩ : syracuseStep 997717 = 2923) (by norm_num)
theorem B997753 : Blo 884570 997753 := bbase (se 2 (by rfl) ⟨374157, by rfl⟩ : syracuseStep 997753 = 748315) (by norm_num)
theorem B997789 : Blo 884570 997789 := bbase (se 3 (by rfl) ⟨187085, by rfl⟩ : syracuseStep 997789 = 374171) (by norm_num)
theorem B997825 : Blo 884570 997825 := bbase (se 2 (by rfl) ⟨374184, by rfl⟩ : syracuseStep 997825 = 748369) (by norm_num)
theorem B997861 : Blo 884570 997861 := bbase (se 4 (by rfl) ⟨93549, by rfl⟩ : syracuseStep 997861 = 187099) (by norm_num)
theorem B997897 : Blo 884570 997897 := bbase (se 2 (by rfl) ⟨374211, by rfl⟩ : syracuseStep 997897 = 748423) (by norm_num)
theorem B15120917 : Blo 884570 15120917 := bbase (se 6 (by rfl) ⟨354396, by rfl⟩ : syracuseStep 15120917 = 708793) (by norm_num)
theorem B7191061 : Blo 884570 7191061 := bbase (se 6 (by rfl) ⟨168540, by rfl⟩ : syracuseStep 7191061 = 337081) (by norm_num)
theorem B6404629 : Blo 884570 6404629 := bbase (se 6 (by rfl) ⟨150108, by rfl⟩ : syracuseStep 6404629 = 300217) (by norm_num)
theorem B1063469 : Blo 884570 1063469 := bbase (se 3 (by rfl) ⟨199400, by rfl⟩ : syracuseStep 1063469 = 398801) (by norm_num)
theorem B997933 : Blo 884570 997933 := bbase (se 3 (by rfl) ⟨187112, by rfl⟩ : syracuseStep 997933 = 374225) (by norm_num)
theorem B997969 : Blo 884570 997969 := bbase (se 2 (by rfl) ⟨374238, by rfl⟩ : syracuseStep 997969 = 748477) (by norm_num)
theorem B1686109 : Blo 884570 1686109 := bbase (se 3 (by rfl) ⟨316145, by rfl⟩ : syracuseStep 1686109 = 632291) (by norm_num)
theorem B2243173 : Blo 884570 2243173 := bbase (se 4 (by rfl) ⟨210297, by rfl⟩ : syracuseStep 2243173 = 420595) (by norm_num)
theorem B2996837 : Blo 884570 2996837 := bbase (se 4 (by rfl) ⟨280953, by rfl⟩ : syracuseStep 2996837 = 561907) (by norm_num)
theorem B998005 : Blo 884570 998005 := bbase (se 5 (by rfl) ⟨46781, by rfl⟩ : syracuseStep 998005 = 93563) (by norm_num)
theorem B998041 : Blo 884570 998041 := bbase (se 2 (by rfl) ⟨374265, by rfl⟩ : syracuseStep 998041 = 748531) (by norm_num)
theorem B998077 : Blo 884570 998077 := bbase (se 3 (by rfl) ⟨187139, by rfl⟩ : syracuseStep 998077 = 374279) (by norm_num)
theorem B2243285 : Blo 884570 2243285 := bbase (se 7 (by rfl) ⟨26288, by rfl⟩ : syracuseStep 2243285 = 52577) (by norm_num)
theorem B998113 : Blo 884570 998113 := bbase (se 2 (by rfl) ⟨374292, by rfl⟩ : syracuseStep 998113 = 748585) (by norm_num)
theorem B1686253 : Blo 884570 1686253 := bbase (se 3 (by rfl) ⟨316172, by rfl⟩ : syracuseStep 1686253 = 632345) (by norm_num)
theorem B998149 : Blo 884570 998149 := bbase (se 4 (by rfl) ⟨93576, by rfl⟩ : syracuseStep 998149 = 187153) (by norm_num)
theorem B998185 : Blo 884570 998185 := bbase (se 2 (by rfl) ⟨374319, by rfl⟩ : syracuseStep 998185 = 748639) (by norm_num)
theorem B998221 : Blo 884570 998221 := bbase (se 3 (by rfl) ⟨187166, by rfl⟩ : syracuseStep 998221 = 374333) (by norm_num)
theorem B1260373 : Blo 884570 1260373 := bbase (se 9 (by rfl) ⟨3692, by rfl⟩ : syracuseStep 1260373 = 7385) (by norm_num)
theorem B998257 : Blo 884570 998257 := bbase (se 2 (by rfl) ⟨374346, by rfl⟩ : syracuseStep 998257 = 748693) (by norm_num)
theorem B1063801 : Blo 884570 1063801 := bbase (se 2 (by rfl) ⟨398925, by rfl⟩ : syracuseStep 1063801 = 797851) (by norm_num)
theorem B1686413 : Blo 884570 1686413 := bbase (se 3 (by rfl) ⟨316202, by rfl⟩ : syracuseStep 1686413 = 632405) (by norm_num)
theorem B2243477 : Blo 884570 2243477 := bbase (se 6 (by rfl) ⟨52581, by rfl⟩ : syracuseStep 2243477 = 105163) (by norm_num)
theorem B998293 : Blo 884570 998293 := bbase (se 6 (by rfl) ⟨23397, by rfl⟩ : syracuseStep 998293 = 46795) (by norm_num)
theorem B998329 : Blo 884570 998329 := bbase (se 2 (by rfl) ⟨374373, by rfl⟩ : syracuseStep 998329 = 748747) (by norm_num)
theorem B998365 : Blo 884570 998365 := bbase (se 3 (by rfl) ⟨187193, by rfl⟩ : syracuseStep 998365 = 374387) (by norm_num)
theorem B998401 : Blo 884570 998401 := bbase (se 2 (by rfl) ⟨374400, by rfl⟩ : syracuseStep 998401 = 748801) (by norm_num)
theorem B2997269 : Blo 884570 2997269 := bbase (se 6 (by rfl) ⟨70248, by rfl⟩ : syracuseStep 2997269 = 140497) (by norm_num)
theorem B1686557 : Blo 884570 1686557 := bbase (se 3 (by rfl) ⟨316229, by rfl⟩ : syracuseStep 1686557 = 632459) (by norm_num)
theorem B998437 : Blo 884570 998437 := bbase (se 4 (by rfl) ⟨93603, by rfl⟩ : syracuseStep 998437 = 187207) (by norm_num)
theorem B998473 : Blo 884570 998473 := bbase (se 2 (by rfl) ⟨374427, by rfl⟩ : syracuseStep 998473 = 748855) (by norm_num)
theorem B998509 : Blo 884570 998509 := bbase (se 3 (by rfl) ⟨187220, by rfl⟩ : syracuseStep 998509 = 374441) (by norm_num)
theorem B998545 : Blo 884570 998545 := bbase (se 2 (by rfl) ⟨374454, by rfl⟩ : syracuseStep 998545 = 748909) (by norm_num)
theorem B998581 : Blo 884570 998581 := bbase (se 5 (by rfl) ⟨46808, by rfl⟩ : syracuseStep 998581 = 93617) (by norm_num)
theorem B998617 : Blo 884570 998617 := bbase (se 2 (by rfl) ⟨374481, by rfl⟩ : syracuseStep 998617 = 748963) (by norm_num)
theorem B2243821 : Blo 884570 2243821 := bbase (se 3 (by rfl) ⟨420716, by rfl⟩ : syracuseStep 2243821 = 841433) (by norm_num)
theorem B998653 : Blo 884570 998653 := bbase (se 3 (by rfl) ⟨187247, by rfl⟩ : syracuseStep 998653 = 374495) (by norm_num)
theorem B998689 : Blo 884570 998689 := bbase (se 2 (by rfl) ⟨374508, by rfl⟩ : syracuseStep 998689 = 749017) (by norm_num)
theorem B3783989 : Blo 884570 3783989 := bbase (se 5 (by rfl) ⟨177374, by rfl⟩ : syracuseStep 3783989 = 354749) (by norm_num)
theorem B1686845 : Blo 884570 1686845 := bbase (se 3 (by rfl) ⟨316283, by rfl⟩ : syracuseStep 1686845 = 632567) (by norm_num)
theorem B998725 : Blo 884570 998725 := bbase (se 4 (by rfl) ⟨93630, by rfl⟩ : syracuseStep 998725 = 187261) (by norm_num)
theorem B2243933 : Blo 884570 2243933 := bbase (se 3 (by rfl) ⟨420737, by rfl⟩ : syracuseStep 2243933 = 841475) (by norm_num)
theorem B998761 : Blo 884570 998761 := bbase (se 2 (by rfl) ⟨374535, by rfl⟩ : syracuseStep 998761 = 749071) (by norm_num)
theorem B998797 : Blo 884570 998797 := bbase (se 3 (by rfl) ⟨187274, by rfl⟩ : syracuseStep 998797 = 374549) (by norm_num)
theorem B2833829 : Blo 884570 2833829 := bbase (se 4 (by rfl) ⟨265671, by rfl⟩ : syracuseStep 2833829 = 531343) (by norm_num)
theorem B1260965 : Blo 884570 1260965 := bbase (se 4 (by rfl) ⟨118215, by rfl⟩ : syracuseStep 1260965 = 236431) (by norm_num)
theorem B998833 : Blo 884570 998833 := bbase (se 2 (by rfl) ⟨374562, by rfl⟩ : syracuseStep 998833 = 749125) (by norm_num)
theorem B2997701 : Blo 884570 2997701 := bbase (se 4 (by rfl) ⟨281034, by rfl⟩ : syracuseStep 2997701 = 562069) (by norm_num)
theorem B998869 : Blo 884570 998869 := bbase (se 7 (by rfl) ⟨11705, by rfl⟩ : syracuseStep 998869 = 23411) (by norm_num)
theorem B1261045 : Blo 884570 1261045 := bbase (se 5 (by rfl) ⟨59111, by rfl⟩ : syracuseStep 1261045 = 118223) (by norm_num)
theorem B998905 : Blo 884570 998905 := bbase (se 2 (by rfl) ⟨374589, by rfl⟩ : syracuseStep 998905 = 749179) (by norm_num)
theorem B2244125 : Blo 884570 2244125 := bbase (se 3 (by rfl) ⟨420773, by rfl⟩ : syracuseStep 2244125 = 841547) (by norm_num)
theorem B998941 : Blo 884570 998941 := bbase (se 3 (by rfl) ⟨187301, by rfl⟩ : syracuseStep 998941 = 374603) (by norm_num)
theorem B3784229 : Blo 884570 3784229 := bbase (se 4 (by rfl) ⟨354771, by rfl⟩ : syracuseStep 3784229 = 709543) (by norm_num)
theorem B1064497 : Blo 884570 1064497 := bbase (se 2 (by rfl) ⟨399186, by rfl⟩ : syracuseStep 1064497 = 798373) (by norm_num)
theorem B998977 : Blo 884570 998977 := bbase (se 2 (by rfl) ⟨374616, by rfl⟩ : syracuseStep 998977 = 749233) (by norm_num)
theorem B1064545 : Blo 884570 1064545 := bbase (se 2 (by rfl) ⟨399204, by rfl⟩ : syracuseStep 1064545 = 798409) (by norm_num)
theorem B999013 : Blo 884570 999013 := bbase (se 4 (by rfl) ⟨93657, by rfl⟩ : syracuseStep 999013 = 187315) (by norm_num)
theorem B1261165 : Blo 884570 1261165 := bbase (se 3 (by rfl) ⟨236468, by rfl⟩ : syracuseStep 1261165 = 472937) (by norm_num)
theorem B999049 : Blo 884570 999049 := bbase (se 2 (by rfl) ⟨374643, by rfl⟩ : syracuseStep 999049 = 749287) (by norm_num)
theorem B999085 : Blo 884570 999085 := bbase (se 3 (by rfl) ⟨187328, by rfl⟩ : syracuseStep 999085 = 374657) (by norm_num)
theorem B1261261 : Blo 884570 1261261 := bbase (se 3 (by rfl) ⟨236486, by rfl⟩ : syracuseStep 1261261 = 472973) (by norm_num)
theorem B999121 : Blo 884570 999121 := bbase (se 2 (by rfl) ⟨374670, by rfl⟩ : syracuseStep 999121 = 749341) (by norm_num)
theorem B1621741 : Blo 884570 1621741 := bbase (se 3 (by rfl) ⟨304076, by rfl⟩ : syracuseStep 1621741 = 608153) (by norm_num)
theorem B999157 : Blo 884570 999157 := bbase (se 5 (by rfl) ⟨46835, by rfl⟩ : syracuseStep 999157 = 93671) (by norm_num)
theorem B1195781 : Blo 884570 1195781 := bbase (se 4 (by rfl) ⟨112104, by rfl⟩ : syracuseStep 1195781 = 224209) (by norm_num)
theorem B1326869 : Blo 884570 1326869 := bbase (se 6 (by rfl) ⟨31098, by rfl⟩ : syracuseStep 1326869 = 62197) (by norm_num)
theorem B999193 : Blo 884570 999193 := bbase (se 2 (by rfl) ⟨374697, by rfl⟩ : syracuseStep 999193 = 749395) (by norm_num)
theorem B1326893 : Blo 884570 1326893 := bbase (se 3 (by rfl) ⟨248792, by rfl⟩ : syracuseStep 1326893 = 497585) (by norm_num)
theorem B999229 : Blo 884570 999229 := bbase (se 3 (by rfl) ⟨187355, by rfl⟩ : syracuseStep 999229 = 374711) (by norm_num)
theorem B1326917 : Blo 884570 1326917 := bbase (se 4 (by rfl) ⟨124398, by rfl⟩ : syracuseStep 1326917 = 248797) (by norm_num)
theorem B1326941 : Blo 884570 1326941 := bbase (se 3 (by rfl) ⟨248801, by rfl⟩ : syracuseStep 1326941 = 497603) (by norm_num)
theorem B999265 : Blo 884570 999265 := bbase (se 2 (by rfl) ⟨374724, by rfl⟩ : syracuseStep 999265 = 749449) (by norm_num)
theorem B1326965 : Blo 884570 1326965 := bbase (se 5 (by rfl) ⟨62201, by rfl⟩ : syracuseStep 1326965 = 124403) (by norm_num)
theorem B2244469 : Blo 884570 2244469 := bbase (se 5 (by rfl) ⟨105209, by rfl⟩ : syracuseStep 2244469 = 210419) (by norm_num)
theorem B2998133 : Blo 884570 2998133 := bbase (se 5 (by rfl) ⟨140537, by rfl⟩ : syracuseStep 2998133 = 281075) (by norm_num)
theorem B999301 : Blo 884570 999301 := bbase (se 4 (by rfl) ⟨93684, by rfl⟩ : syracuseStep 999301 = 187369) (by norm_num)
theorem B1326989 : Blo 884570 1326989 := bbase (se 3 (by rfl) ⟨248810, by rfl⟩ : syracuseStep 1326989 = 497621) (by norm_num)
theorem B1327013 : Blo 884570 1327013 := bbase (se 4 (by rfl) ⟨124407, by rfl⟩ : syracuseStep 1327013 = 248815) (by norm_num)
theorem B999337 : Blo 884570 999337 := bbase (se 2 (by rfl) ⟨374751, by rfl⟩ : syracuseStep 999337 = 749503) (by norm_num)
theorem B1327037 : Blo 884570 1327037 := bbase (se 3 (by rfl) ⟨248819, by rfl⟩ : syracuseStep 1327037 = 497639) (by norm_num)
theorem B999373 : Blo 884570 999373 := bbase (se 3 (by rfl) ⟨187382, by rfl⟩ : syracuseStep 999373 = 374765) (by norm_num)
theorem B1327061 : Blo 884570 1327061 := bbase (se 7 (by rfl) ⟨15551, by rfl⟩ : syracuseStep 1327061 = 31103) (by norm_num)
theorem B2244581 : Blo 884570 2244581 := bbase (se 4 (by rfl) ⟨210429, by rfl⟩ : syracuseStep 2244581 = 420859) (by norm_num)
theorem B1327085 : Blo 884570 1327085 := bbase (se 3 (by rfl) ⟨248828, by rfl⟩ : syracuseStep 1327085 = 497657) (by norm_num)
theorem B999409 : Blo 884570 999409 := bbase (se 2 (by rfl) ⟨374778, by rfl⟩ : syracuseStep 999409 = 749557) (by norm_num)
theorem B1327109 : Blo 884570 1327109 := bbase (se 4 (by rfl) ⟨124416, by rfl⟩ : syracuseStep 1327109 = 248833) (by norm_num)
theorem B999445 : Blo 884570 999445 := bbase (se 6 (by rfl) ⟨23424, by rfl⟩ : syracuseStep 999445 = 46849) (by norm_num)
theorem B1327133 : Blo 884570 1327133 := bbase (se 3 (by rfl) ⟨248837, by rfl⟩ : syracuseStep 1327133 = 497675) (by norm_num)
theorem B2768933 : Blo 884570 2768933 := bbase (se 4 (by rfl) ⟨259587, by rfl⟩ : syracuseStep 2768933 = 519175) (by norm_num)
theorem B1327157 : Blo 884570 1327157 := bbase (se 5 (by rfl) ⟨62210, by rfl⟩ : syracuseStep 1327157 = 124421) (by norm_num)
theorem B999481 : Blo 884570 999481 := bbase (se 2 (by rfl) ⟨374805, by rfl⟩ : syracuseStep 999481 = 749611) (by norm_num)
theorem B1327181 : Blo 884570 1327181 := bbase (se 3 (by rfl) ⟨248846, by rfl⟩ : syracuseStep 1327181 = 497693) (by norm_num)
theorem B999517 : Blo 884570 999517 := bbase (se 3 (by rfl) ⟨187409, by rfl⟩ : syracuseStep 999517 = 374819) (by norm_num)
theorem B1327205 : Blo 884570 1327205 := bbase (se 4 (by rfl) ⟨124425, by rfl⟩ : syracuseStep 1327205 = 248851) (by norm_num)
theorem B1327229 : Blo 884570 1327229 := bbase (se 3 (by rfl) ⟨248855, by rfl⟩ : syracuseStep 1327229 = 497711) (by norm_num)
theorem B999553 : Blo 884570 999553 := bbase (se 2 (by rfl) ⟨374832, by rfl⟩ : syracuseStep 999553 = 749665) (by norm_num)
theorem B3358853 : Blo 884570 3358853 := bbase (se 4 (by rfl) ⟨314892, by rfl⟩ : syracuseStep 3358853 = 629785) (by norm_num)
theorem B1327253 : Blo 884570 1327253 := bbase (se 6 (by rfl) ⟨31107, by rfl⟩ : syracuseStep 1327253 = 62215) (by norm_num)
theorem B2244773 : Blo 884570 2244773 := bbase (se 4 (by rfl) ⟨210447, by rfl⟩ : syracuseStep 2244773 = 420895) (by norm_num)
theorem B999589 : Blo 884570 999589 := bbase (se 4 (by rfl) ⟨93711, by rfl⟩ : syracuseStep 999589 = 187423) (by norm_num)
theorem B1327277 : Blo 884570 1327277 := bbase (se 3 (by rfl) ⟨248864, by rfl⟩ : syracuseStep 1327277 = 497729) (by norm_num)
theorem B1261757 : Blo 884570 1261757 := bbase (se 3 (by rfl) ⟨236579, by rfl⟩ : syracuseStep 1261757 = 473159) (by norm_num)
theorem B1327301 : Blo 884570 1327301 := bbase (se 4 (by rfl) ⟨124434, by rfl⟩ : syracuseStep 1327301 = 248869) (by norm_num)
theorem B999625 : Blo 884570 999625 := bbase (se 2 (by rfl) ⟨374859, by rfl⟩ : syracuseStep 999625 = 749719) (by norm_num)
theorem B1327325 : Blo 884570 1327325 := bbase (se 3 (by rfl) ⟨248873, by rfl⟩ : syracuseStep 1327325 = 497747) (by norm_num)
theorem B1327349 : Blo 884570 1327349 := bbase (se 5 (by rfl) ⟨62219, by rfl⟩ : syracuseStep 1327349 = 124439) (by norm_num)
theorem B1753349 : Blo 884570 1753349 := bbase (se 4 (by rfl) ⟨164376, by rfl⟩ : syracuseStep 1753349 = 328753) (by norm_num)
theorem B1327373 : Blo 884570 1327373 := bbase (se 3 (by rfl) ⟨248882, by rfl⟩ : syracuseStep 1327373 = 497765) (by norm_num)
theorem B1327397 : Blo 884570 1327397 := bbase (se 4 (by rfl) ⟨124443, by rfl⟩ : syracuseStep 1327397 = 248887) (by norm_num)
theorem B2998565 : Blo 884570 2998565 := bbase (se 4 (by rfl) ⟨281115, by rfl⟩ : syracuseStep 2998565 = 562231) (by norm_num)
theorem B1327421 : Blo 884570 1327421 := bbase (se 3 (by rfl) ⟨248891, by rfl⟩ : syracuseStep 1327421 = 497783) (by norm_num)
theorem B1327445 : Blo 884570 1327445 := bbase (se 10 (by rfl) ⟨1944, by rfl⟩ : syracuseStep 1327445 = 3889) (by norm_num)
theorem B6472021 : Blo 884570 6472021 := bbase (se 10 (by rfl) ⟨9480, by rfl⟩ : syracuseStep 6472021 = 18961) (by norm_num)
theorem B1327469 : Blo 884570 1327469 := bbase (se 3 (by rfl) ⟨248900, by rfl⟩ : syracuseStep 1327469 = 497801) (by norm_num)
theorem B1196413 : Blo 884570 1196413 := bbase (se 3 (by rfl) ⟨224327, by rfl⟩ : syracuseStep 1196413 = 448655) (by norm_num)
theorem B1327493 : Blo 884570 1327493 := bbase (se 4 (by rfl) ⟨124452, by rfl⟩ : syracuseStep 1327493 = 248905) (by norm_num)
theorem B1327517 : Blo 884570 1327517 := bbase (se 3 (by rfl) ⟨248909, by rfl⟩ : syracuseStep 1327517 = 497819) (by norm_num)
theorem B3359141 : Blo 884570 3359141 := bbase (se 4 (by rfl) ⟨314919, by rfl⟩ : syracuseStep 3359141 = 629839) (by norm_num)
theorem B1327541 : Blo 884570 1327541 := bbase (se 5 (by rfl) ⟨62228, by rfl⟩ : syracuseStep 1327541 = 124457) (by norm_num)
theorem B1327565 : Blo 884570 1327565 := bbase (se 3 (by rfl) ⟨248918, by rfl⟩ : syracuseStep 1327565 = 497837) (by norm_num)
theorem B1327589 : Blo 884570 1327589 := bbase (se 4 (by rfl) ⟨124461, by rfl⟩ : syracuseStep 1327589 = 248923) (by norm_num)
theorem B1327613 : Blo 884570 1327613 := bbase (se 3 (by rfl) ⟨248927, by rfl⟩ : syracuseStep 1327613 = 497855) (by norm_num)
theorem B2245117 : Blo 884570 2245117 := bbase (se 3 (by rfl) ⟨420959, by rfl⟩ : syracuseStep 2245117 = 841919) (by norm_num)
theorem B1327637 : Blo 884570 1327637 := bbase (se 6 (by rfl) ⟨31116, by rfl⟩ : syracuseStep 1327637 = 62233) (by norm_num)
theorem B6242837 : Blo 884570 6242837 := bbase (se 6 (by rfl) ⟨146316, by rfl⟩ : syracuseStep 6242837 = 292633) (by norm_num)
theorem B1327661 : Blo 884570 1327661 := bbase (se 3 (by rfl) ⟨248936, by rfl⟩ : syracuseStep 1327661 = 497873) (by norm_num)
theorem B1327685 : Blo 884570 1327685 := bbase (se 4 (by rfl) ⟨124470, by rfl⟩ : syracuseStep 1327685 = 248941) (by norm_num)
theorem B1327709 : Blo 884570 1327709 := bbase (se 3 (by rfl) ⟨248945, by rfl⟩ : syracuseStep 1327709 = 497891) (by norm_num)
theorem B2245229 : Blo 884570 2245229 := bbase (se 3 (by rfl) ⟨420980, by rfl⟩ : syracuseStep 2245229 = 841961) (by norm_num)
theorem B1327733 : Blo 884570 1327733 := bbase (se 5 (by rfl) ⟨62237, by rfl⟩ : syracuseStep 1327733 = 124475) (by norm_num)
theorem B1065593 : Blo 884570 1065593 := bbase (se 2 (by rfl) ⟨399597, by rfl⟩ : syracuseStep 1065593 = 799195) (by norm_num)
theorem B1327757 : Blo 884570 1327757 := bbase (se 3 (by rfl) ⟨248954, by rfl⟩ : syracuseStep 1327757 = 497909) (by norm_num)
theorem B1327781 : Blo 884570 1327781 := bbase (se 4 (by rfl) ⟨124479, by rfl⟩ : syracuseStep 1327781 = 248959) (by norm_num)
theorem B1327805 : Blo 884570 1327805 := bbase (se 3 (by rfl) ⟨248963, by rfl⟩ : syracuseStep 1327805 = 497927) (by norm_num)
theorem B1327829 : Blo 884570 1327829 := bbase (se 7 (by rfl) ⟨15560, by rfl⟩ : syracuseStep 1327829 = 31121) (by norm_num)
theorem B1262309 : Blo 884570 1262309 := bbase (se 4 (by rfl) ⟨118341, by rfl⟩ : syracuseStep 1262309 = 236683) (by norm_num)
theorem B1327853 : Blo 884570 1327853 := bbase (se 3 (by rfl) ⟨248972, by rfl⟩ : syracuseStep 1327853 = 497945) (by norm_num)
theorem B1327877 : Blo 884570 1327877 := bbase (se 4 (by rfl) ⟨124488, by rfl⟩ : syracuseStep 1327877 = 248977) (by norm_num)
theorem B1327901 : Blo 884570 1327901 := bbase (se 3 (by rfl) ⟨248981, by rfl⟩ : syracuseStep 1327901 = 497963) (by norm_num)
theorem B2245421 : Blo 884570 2245421 := bbase (se 3 (by rfl) ⟨421016, by rfl⟩ : syracuseStep 2245421 = 842033) (by norm_num)
theorem B1327925 : Blo 884570 1327925 := bbase (se 5 (by rfl) ⟨62246, by rfl⟩ : syracuseStep 1327925 = 124493) (by norm_num)
theorem B5391157 : Blo 884570 5391157 := bbase (se 5 (by rfl) ⟨252710, by rfl⟩ : syracuseStep 5391157 = 505421) (by norm_num)
theorem B1327949 : Blo 884570 1327949 := bbase (se 3 (by rfl) ⟨248990, by rfl⟩ : syracuseStep 1327949 = 497981) (by norm_num)
theorem B1327973 : Blo 884570 1327973 := bbase (se 4 (by rfl) ⟨124497, by rfl⟩ : syracuseStep 1327973 = 248995) (by norm_num)
theorem B1327997 : Blo 884570 1327997 := bbase (se 3 (by rfl) ⟨248999, by rfl⟩ : syracuseStep 1327997 = 497999) (by norm_num)
theorem B1328021 : Blo 884570 1328021 := bbase (se 6 (by rfl) ⟨31125, by rfl⟩ : syracuseStep 1328021 = 62251) (by norm_num)
theorem B1328045 : Blo 884570 1328045 := bbase (se 3 (by rfl) ⟨249008, by rfl⟩ : syracuseStep 1328045 = 498017) (by norm_num)
theorem B1065901 : Blo 884570 1065901 := bbase (se 3 (by rfl) ⟨199856, by rfl⟩ : syracuseStep 1065901 = 399713) (by norm_num)
theorem B1328069 : Blo 884570 1328069 := bbase (se 4 (by rfl) ⟨124506, by rfl⟩ : syracuseStep 1328069 = 249013) (by norm_num)
theorem B1328093 : Blo 884570 1328093 := bbase (se 3 (by rfl) ⟨249017, by rfl⟩ : syracuseStep 1328093 = 498035) (by norm_num)
theorem B1328117 : Blo 884570 1328117 := bbase (se 5 (by rfl) ⟨62255, by rfl⟩ : syracuseStep 1328117 = 124511) (by norm_num)
theorem B1328141 : Blo 884570 1328141 := bbase (se 3 (by rfl) ⟨249026, by rfl⟩ : syracuseStep 1328141 = 498053) (by norm_num)
theorem B1328165 : Blo 884570 1328165 := bbase (se 4 (by rfl) ⟨124515, by rfl⟩ : syracuseStep 1328165 = 249031) (by norm_num)
theorem B1328189 : Blo 884570 1328189 := bbase (se 3 (by rfl) ⟨249035, by rfl⟩ : syracuseStep 1328189 = 498071) (by norm_num)
theorem B1328213 : Blo 884570 1328213 := bbase (se 8 (by rfl) ⟨7782, by rfl⟩ : syracuseStep 1328213 = 15565) (by norm_num)
theorem B1066069 : Blo 884570 1066069 := bbase (se 8 (by rfl) ⟨6246, by rfl⟩ : syracuseStep 1066069 = 12493) (by norm_num)
theorem B1328237 : Blo 884570 1328237 := bbase (se 3 (by rfl) ⟨249044, by rfl⟩ : syracuseStep 1328237 = 498089) (by norm_num)
theorem B1328261 : Blo 884570 1328261 := bbase (se 4 (by rfl) ⟨124524, by rfl⟩ : syracuseStep 1328261 = 249049) (by norm_num)
theorem B2245765 : Blo 884570 2245765 := bbase (se 4 (by rfl) ⟨210540, by rfl⟩ : syracuseStep 2245765 = 421081) (by norm_num)
theorem B2278541 : Blo 884570 2278541 := bbase (se 3 (by rfl) ⟨427226, by rfl⟩ : syracuseStep 2278541 = 854453) (by norm_num)
theorem B1328285 : Blo 884570 1328285 := bbase (se 3 (by rfl) ⟨249053, by rfl⟩ : syracuseStep 1328285 = 498107) (by norm_num)
theorem B3884213 : Blo 884570 3884213 := bbase (se 5 (by rfl) ⟨182072, by rfl⟩ : syracuseStep 3884213 = 364145) (by norm_num)
theorem B1328309 : Blo 884570 1328309 := bbase (se 5 (by rfl) ⟨62264, by rfl⟩ : syracuseStep 1328309 = 124529) (by norm_num)
theorem B1328333 : Blo 884570 1328333 := bbase (se 3 (by rfl) ⟨249062, by rfl⟩ : syracuseStep 1328333 = 498125) (by norm_num)
theorem B2835685 : Blo 884570 2835685 := bbase (se 4 (by rfl) ⟨265845, by rfl⟩ : syracuseStep 2835685 = 531691) (by norm_num)
theorem B1328357 : Blo 884570 1328357 := bbase (se 4 (by rfl) ⟨124533, by rfl⟩ : syracuseStep 1328357 = 249067) (by norm_num)
theorem B2245877 : Blo 884570 2245877 := bbase (se 5 (by rfl) ⟨105275, by rfl⟩ : syracuseStep 2245877 = 210551) (by norm_num)
theorem B1328381 : Blo 884570 1328381 := bbase (se 3 (by rfl) ⟨249071, by rfl⟩ : syracuseStep 1328381 = 498143) (by norm_num)
theorem B1328405 : Blo 884570 1328405 := bbase (se 6 (by rfl) ⟨31134, by rfl⟩ : syracuseStep 1328405 = 62269) (by norm_num)
theorem B1066265 : Blo 884570 1066265 := bbase (se 2 (by rfl) ⟨399849, by rfl⟩ : syracuseStep 1066265 = 799699) (by norm_num)
theorem B1328429 : Blo 884570 1328429 := bbase (se 3 (by rfl) ⟨249080, by rfl⟩ : syracuseStep 1328429 = 498161) (by norm_num)
theorem B1328453 : Blo 884570 1328453 := bbase (se 4 (by rfl) ⟨124542, by rfl⟩ : syracuseStep 1328453 = 249085) (by norm_num)
theorem B1328477 : Blo 884570 1328477 := bbase (se 3 (by rfl) ⟨249089, by rfl⟩ : syracuseStep 1328477 = 498179) (by norm_num)
theorem B1328501 : Blo 884570 1328501 := bbase (se 5 (by rfl) ⟨62273, by rfl⟩ : syracuseStep 1328501 = 124547) (by norm_num)
theorem B5686645 : Blo 884570 5686645 := bbase (se 5 (by rfl) ⟨266561, by rfl⟩ : syracuseStep 5686645 = 533123) (by norm_num)
theorem B1328525 : Blo 884570 1328525 := bbase (se 3 (by rfl) ⟨249098, by rfl⟩ : syracuseStep 1328525 = 498197) (by norm_num)
theorem B1328549 : Blo 884570 1328549 := bbase (se 4 (by rfl) ⟨124551, by rfl⟩ : syracuseStep 1328549 = 249103) (by norm_num)
theorem B2246069 : Blo 884570 2246069 := bbase (se 5 (by rfl) ⟨105284, by rfl⟩ : syracuseStep 2246069 = 210569) (by norm_num)
theorem B1328573 : Blo 884570 1328573 := bbase (se 3 (by rfl) ⟨249107, by rfl⟩ : syracuseStep 1328573 = 498215) (by norm_num)
theorem B1328597 : Blo 884570 1328597 := bbase (se 7 (by rfl) ⟨15569, by rfl⟩ : syracuseStep 1328597 = 31139) (by norm_num)
theorem B1263061 : Blo 884570 1263061 := bbase (se 7 (by rfl) ⟨14801, by rfl⟩ : syracuseStep 1263061 = 29603) (by norm_num)
theorem B1328621 : Blo 884570 1328621 := bbase (se 3 (by rfl) ⟨249116, by rfl⟩ : syracuseStep 1328621 = 498233) (by norm_num)
theorem B1328645 : Blo 884570 1328645 := bbase (se 4 (by rfl) ⟨124560, by rfl⟩ : syracuseStep 1328645 = 249121) (by norm_num)
theorem B1328669 : Blo 884570 1328669 := bbase (se 3 (by rfl) ⟨249125, by rfl⟩ : syracuseStep 1328669 = 498251) (by norm_num)
theorem B1328693 : Blo 884570 1328693 := bbase (se 5 (by rfl) ⟨62282, by rfl⟩ : syracuseStep 1328693 = 124565) (by norm_num)
theorem B3360325 : Blo 884570 3360325 := bbase (se 4 (by rfl) ⟨315030, by rfl⟩ : syracuseStep 3360325 = 630061) (by norm_num)
theorem B1328717 : Blo 884570 1328717 := bbase (se 3 (by rfl) ⟨249134, by rfl⟩ : syracuseStep 1328717 = 498269) (by norm_num)
theorem B1328741 : Blo 884570 1328741 := bbase (se 4 (by rfl) ⟨124569, by rfl⟩ : syracuseStep 1328741 = 249139) (by norm_num)
theorem B1328765 : Blo 884570 1328765 := bbase (se 3 (by rfl) ⟨249143, by rfl⟩ : syracuseStep 1328765 = 498287) (by norm_num)
theorem B1328789 : Blo 884570 1328789 := bbase (se 6 (by rfl) ⟨31143, by rfl⟩ : syracuseStep 1328789 = 62287) (by norm_num)
theorem B1328813 : Blo 884570 1328813 := bbase (se 3 (by rfl) ⟨249152, by rfl⟩ : syracuseStep 1328813 = 498305) (by norm_num)
theorem B1328837 : Blo 884570 1328837 := bbase (se 4 (by rfl) ⟨124578, by rfl⟩ : syracuseStep 1328837 = 249157) (by norm_num)
theorem B1328861 : Blo 884570 1328861 := bbase (se 3 (by rfl) ⟨249161, by rfl⟩ : syracuseStep 1328861 = 498323) (by norm_num)
theorem B1328885 : Blo 884570 1328885 := bbase (se 5 (by rfl) ⟨62291, by rfl⟩ : syracuseStep 1328885 = 124583) (by norm_num)
theorem B1328909 : Blo 884570 1328909 := bbase (se 3 (by rfl) ⟨249170, by rfl⟩ : syracuseStep 1328909 = 498341) (by norm_num)
theorem B2246413 : Blo 884570 2246413 := bbase (se 3 (by rfl) ⟨421202, by rfl⟩ : syracuseStep 2246413 = 842405) (by norm_num)
theorem B3786517 : Blo 884570 3786517 := bbase (se 6 (by rfl) ⟨88746, by rfl⟩ : syracuseStep 3786517 = 177493) (by norm_num)
theorem B1328933 : Blo 884570 1328933 := bbase (se 4 (by rfl) ⟨124587, by rfl⟩ : syracuseStep 1328933 = 249175) (by norm_num)
theorem B1492789 : Blo 884570 1492789 := bbase (se 5 (by rfl) ⟨69974, by rfl⟩ : syracuseStep 1492789 = 139949) (by norm_num)
theorem B1328957 : Blo 884570 1328957 := bbase (se 3 (by rfl) ⟨249179, by rfl⟩ : syracuseStep 1328957 = 498359) (by norm_num)
theorem B1328981 : Blo 884570 1328981 := bbase (se 9 (by rfl) ⟨3893, by rfl⟩ : syracuseStep 1328981 = 7787) (by norm_num)
theorem B1329005 : Blo 884570 1329005 := bbase (se 3 (by rfl) ⟨249188, by rfl⟩ : syracuseStep 1329005 = 498377) (by norm_num)
theorem B3360629 : Blo 884570 3360629 := bbase (se 5 (by rfl) ⟨157529, by rfl⟩ : syracuseStep 3360629 = 315059) (by norm_num)
theorem B2246525 : Blo 884570 2246525 := bbase (se 3 (by rfl) ⟨421223, by rfl⟩ : syracuseStep 2246525 = 842447) (by norm_num)
theorem B1329029 : Blo 884570 1329029 := bbase (se 4 (by rfl) ⟨124596, by rfl⟩ : syracuseStep 1329029 = 249193) (by norm_num)
theorem B1492877 : Blo 884570 1492877 := bbase (se 3 (by rfl) ⟨279914, by rfl⟩ : syracuseStep 1492877 = 559829) (by norm_num)
theorem B1329053 : Blo 884570 1329053 := bbase (se 3 (by rfl) ⟨249197, by rfl⟩ : syracuseStep 1329053 = 498395) (by norm_num)
theorem B1329077 : Blo 884570 1329077 := bbase (se 5 (by rfl) ⟨62300, by rfl⟩ : syracuseStep 1329077 = 124601) (by norm_num)
theorem B1329101 : Blo 884570 1329101 := bbase (se 3 (by rfl) ⟨249206, by rfl⟩ : syracuseStep 1329101 = 498413) (by norm_num)
theorem B1329125 : Blo 884570 1329125 := bbase (se 4 (by rfl) ⟨124605, by rfl⟩ : syracuseStep 1329125 = 249211) (by norm_num)
theorem B1329149 : Blo 884570 1329149 := bbase (se 3 (by rfl) ⟨249215, by rfl⟩ : syracuseStep 1329149 = 498431) (by norm_num)
theorem B1493005 : Blo 884570 1493005 := bbase (se 3 (by rfl) ⟨279938, by rfl⟩ : syracuseStep 1493005 = 559877) (by norm_num)
theorem B1329173 : Blo 884570 1329173 := bbase (se 6 (by rfl) ⟨31152, by rfl⟩ : syracuseStep 1329173 = 62305) (by norm_num)
theorem B1329197 : Blo 884570 1329197 := bbase (se 3 (by rfl) ⟨249224, by rfl⟩ : syracuseStep 1329197 = 498449) (by norm_num)
theorem B2246717 : Blo 884570 2246717 := bbase (se 3 (by rfl) ⟨421259, by rfl⟩ : syracuseStep 2246717 = 842519) (by norm_num)
theorem B1329221 : Blo 884570 1329221 := bbase (se 4 (by rfl) ⟨124614, by rfl⟩ : syracuseStep 1329221 = 249229) (by norm_num)
theorem B1329245 : Blo 884570 1329245 := bbase (se 3 (by rfl) ⟨249233, by rfl⟩ : syracuseStep 1329245 = 498467) (by norm_num)
theorem B1493093 : Blo 884570 1493093 := bbase (se 4 (by rfl) ⟨139977, by rfl⟩ : syracuseStep 1493093 = 279955) (by norm_num)
theorem B1329269 : Blo 884570 1329269 := bbase (se 5 (by rfl) ⟨62309, by rfl⟩ : syracuseStep 1329269 = 124619) (by norm_num)
theorem B1329293 : Blo 884570 1329293 := bbase (se 3 (by rfl) ⟨249242, by rfl⟩ : syracuseStep 1329293 = 498485) (by norm_num)
theorem B1329317 : Blo 884570 1329317 := bbase (se 4 (by rfl) ⟨124623, by rfl⟩ : syracuseStep 1329317 = 249247) (by norm_num)
theorem B1329341 : Blo 884570 1329341 := bbase (se 3 (by rfl) ⟨249251, by rfl⟩ : syracuseStep 1329341 = 498503) (by norm_num)
theorem B1329365 : Blo 884570 1329365 := bbase (se 7 (by rfl) ⟨15578, by rfl⟩ : syracuseStep 1329365 = 31157) (by norm_num)
theorem B1493221 : Blo 884570 1493221 := bbase (se 4 (by rfl) ⟨139989, by rfl⟩ : syracuseStep 1493221 = 279979) (by norm_num)
theorem B1329389 : Blo 884570 1329389 := bbase (se 3 (by rfl) ⟨249260, by rfl⟩ : syracuseStep 1329389 = 498521) (by norm_num)
theorem B1263853 : Blo 884570 1263853 := bbase (se 3 (by rfl) ⟨236972, by rfl⟩ : syracuseStep 1263853 = 473945) (by norm_num)
theorem B1329413 : Blo 884570 1329413 := bbase (se 4 (by rfl) ⟨124632, by rfl⟩ : syracuseStep 1329413 = 249265) (by norm_num)
theorem B1329437 : Blo 884570 1329437 := bbase (se 3 (by rfl) ⟨249269, by rfl⟩ : syracuseStep 1329437 = 498539) (by norm_num)
theorem B1329461 : Blo 884570 1329461 := bbase (se 5 (by rfl) ⟨62318, by rfl⟩ : syracuseStep 1329461 = 124637) (by norm_num)
theorem B1493309 : Blo 884570 1493309 := bbase (se 3 (by rfl) ⟨279995, by rfl⟩ : syracuseStep 1493309 = 559991) (by norm_num)
theorem B1329485 : Blo 884570 1329485 := bbase (se 3 (by rfl) ⟨249278, by rfl⟩ : syracuseStep 1329485 = 498557) (by norm_num)
theorem B1329509 : Blo 884570 1329509 := bbase (se 4 (by rfl) ⟨124641, by rfl⟩ : syracuseStep 1329509 = 249283) (by norm_num)
theorem B1329533 : Blo 884570 1329533 := bbase (se 3 (by rfl) ⟨249287, by rfl⟩ : syracuseStep 1329533 = 498575) (by norm_num)
theorem B1329557 : Blo 884570 1329557 := bbase (se 6 (by rfl) ⟨31161, by rfl⟩ : syracuseStep 1329557 = 62323) (by norm_num)
theorem B2247061 : Blo 884570 2247061 := bbase (se 6 (by rfl) ⟨52665, by rfl⟩ : syracuseStep 2247061 = 105331) (by norm_num)
theorem B1329581 : Blo 884570 1329581 := bbase (se 3 (by rfl) ⟨249296, by rfl⟩ : syracuseStep 1329581 = 498593) (by norm_num)
theorem B1493437 : Blo 884570 1493437 := bbase (se 3 (by rfl) ⟨280019, by rfl⟩ : syracuseStep 1493437 = 560039) (by norm_num)
theorem B1329605 : Blo 884570 1329605 := bbase (se 4 (by rfl) ⟨124650, by rfl⟩ : syracuseStep 1329605 = 249301) (by norm_num)
theorem B1329629 : Blo 884570 1329629 := bbase (se 3 (by rfl) ⟨249305, by rfl⟩ : syracuseStep 1329629 = 498611) (by norm_num)
theorem B1329653 : Blo 884570 1329653 := bbase (se 5 (by rfl) ⟨62327, by rfl⟩ : syracuseStep 1329653 = 124655) (by norm_num)
theorem B2247173 : Blo 884570 2247173 := bbase (se 4 (by rfl) ⟨210672, by rfl⟩ : syracuseStep 2247173 = 421345) (by norm_num)
theorem B1329677 : Blo 884570 1329677 := bbase (se 3 (by rfl) ⟨249314, by rfl⟩ : syracuseStep 1329677 = 498629) (by norm_num)
theorem B1493525 : Blo 884570 1493525 := bbase (se 6 (by rfl) ⟨35004, by rfl⟩ : syracuseStep 1493525 = 70009) (by norm_num)
theorem B1329701 : Blo 884570 1329701 := bbase (se 4 (by rfl) ⟨124659, by rfl⟩ : syracuseStep 1329701 = 249319) (by norm_num)
theorem B2837045 : Blo 884570 2837045 := bbase (se 5 (by rfl) ⟨132986, by rfl⟩ : syracuseStep 2837045 = 265973) (by norm_num)
theorem B1329725 : Blo 884570 1329725 := bbase (se 3 (by rfl) ⟨249323, by rfl⟩ : syracuseStep 1329725 = 498647) (by norm_num)
theorem B1264189 : Blo 884570 1264189 := bbase (se 3 (by rfl) ⟨237035, by rfl⟩ : syracuseStep 1264189 = 474071) (by norm_num)
theorem B1329749 : Blo 884570 1329749 := bbase (se 8 (by rfl) ⟨7791, by rfl⟩ : syracuseStep 1329749 = 15583) (by norm_num)
theorem B1329773 : Blo 884570 1329773 := bbase (se 3 (by rfl) ⟨249332, by rfl⟩ : syracuseStep 1329773 = 498665) (by norm_num)
theorem B1329797 : Blo 884570 1329797 := bbase (se 4 (by rfl) ⟨124668, by rfl⟩ : syracuseStep 1329797 = 249337) (by norm_num)
theorem B1493653 : Blo 884570 1493653 := bbase (se 6 (by rfl) ⟨35007, by rfl⟩ : syracuseStep 1493653 = 70015) (by norm_num)
theorem B1329821 : Blo 884570 1329821 := bbase (se 3 (by rfl) ⟨249341, by rfl⟩ : syracuseStep 1329821 = 498683) (by norm_num)
theorem B1329845 : Blo 884570 1329845 := bbase (se 5 (by rfl) ⟨62336, by rfl⟩ : syracuseStep 1329845 = 124673) (by norm_num)
theorem B2247365 : Blo 884570 2247365 := bbase (se 4 (by rfl) ⟨210690, by rfl⟩ : syracuseStep 2247365 = 421381) (by norm_num)
theorem B1329869 : Blo 884570 1329869 := bbase (se 3 (by rfl) ⟨249350, by rfl⟩ : syracuseStep 1329869 = 498701) (by norm_num)
theorem B1329893 : Blo 884570 1329893 := bbase (se 4 (by rfl) ⟨124677, by rfl⟩ : syracuseStep 1329893 = 249355) (by norm_num)
theorem B1493741 : Blo 884570 1493741 := bbase (se 3 (by rfl) ⟨280076, by rfl⟩ : syracuseStep 1493741 = 560153) (by norm_num)
theorem B1329917 : Blo 884570 1329917 := bbase (se 3 (by rfl) ⟨249359, by rfl⟩ : syracuseStep 1329917 = 498719) (by norm_num)
theorem B8506133 : Blo 884570 8506133 := bbase (se 6 (by rfl) ⟨199362, by rfl⟩ : syracuseStep 8506133 = 398725) (by norm_num)
theorem B1329941 : Blo 884570 1329941 := bbase (se 6 (by rfl) ⟨31170, by rfl⟩ : syracuseStep 1329941 = 62341) (by norm_num)
theorem B1264405 : Blo 884570 1264405 := bbase (se 6 (by rfl) ⟨29634, by rfl⟩ : syracuseStep 1264405 = 59269) (by norm_num)
theorem B1329965 : Blo 884570 1329965 := bbase (se 3 (by rfl) ⟨249368, by rfl⟩ : syracuseStep 1329965 = 498737) (by norm_num)
theorem B1329989 : Blo 884570 1329989 := bbase (se 4 (by rfl) ⟨124686, by rfl⟩ : syracuseStep 1329989 = 249373) (by norm_num)
theorem B1330013 : Blo 884570 1330013 := bbase (se 3 (by rfl) ⟨249377, by rfl⟩ : syracuseStep 1330013 = 498755) (by norm_num)
theorem B1493869 : Blo 884570 1493869 := bbase (se 3 (by rfl) ⟨280100, by rfl⟩ : syracuseStep 1493869 = 560201) (by norm_num)
theorem B1330037 : Blo 884570 1330037 := bbase (se 5 (by rfl) ⟨62345, by rfl⟩ : syracuseStep 1330037 = 124691) (by norm_num)
theorem B1330061 : Blo 884570 1330061 := bbase (se 3 (by rfl) ⟨249386, by rfl⟩ : syracuseStep 1330061 = 498773) (by norm_num)
theorem B1330085 : Blo 884570 1330085 := bbase (se 4 (by rfl) ⟨124695, by rfl⟩ : syracuseStep 1330085 = 249391) (by norm_num)
theorem B1330109 : Blo 884570 1330109 := bbase (se 3 (by rfl) ⟨249395, by rfl⟩ : syracuseStep 1330109 = 498791) (by norm_num)
theorem B1493957 : Blo 884570 1493957 := bbase (se 4 (by rfl) ⟨140058, by rfl⟩ : syracuseStep 1493957 = 280117) (by norm_num)
theorem B1330133 : Blo 884570 1330133 := bbase (se 7 (by rfl) ⟨15587, by rfl⟩ : syracuseStep 1330133 = 31175) (by norm_num)
theorem B1330157 : Blo 884570 1330157 := bbase (se 3 (by rfl) ⟨249404, by rfl⟩ : syracuseStep 1330157 = 498809) (by norm_num)
theorem B1330181 : Blo 884570 1330181 := bbase (se 4 (by rfl) ⟨124704, by rfl⟩ : syracuseStep 1330181 = 249409) (by norm_num)
theorem B1330205 : Blo 884570 1330205 := bbase (se 3 (by rfl) ⟨249413, by rfl⟩ : syracuseStep 1330205 = 498827) (by norm_num)
theorem B2247709 : Blo 884570 2247709 := bbase (se 3 (by rfl) ⟨421445, by rfl⟩ : syracuseStep 2247709 = 842891) (by norm_num)
theorem B1330229 : Blo 884570 1330229 := bbase (se 5 (by rfl) ⟨62354, by rfl⟩ : syracuseStep 1330229 = 124709) (by norm_num)
theorem B1920061 : Blo 884570 1920061 := bbase (se 3 (by rfl) ⟨360011, by rfl⟩ : syracuseStep 1920061 = 720023) (by norm_num)
theorem B1494085 : Blo 884570 1494085 := bbase (se 4 (by rfl) ⟨140070, by rfl⟩ : syracuseStep 1494085 = 280141) (by norm_num)
theorem B1330253 : Blo 884570 1330253 := bbase (se 3 (by rfl) ⟨249422, by rfl⟩ : syracuseStep 1330253 = 498845) (by norm_num)
theorem B1330277 : Blo 884570 1330277 := bbase (se 4 (by rfl) ⟨124713, by rfl⟩ : syracuseStep 1330277 = 249427) (by norm_num)
theorem B1330301 : Blo 884570 1330301 := bbase (se 3 (by rfl) ⟨249431, by rfl⟩ : syracuseStep 1330301 = 498863) (by norm_num)
theorem B2247821 : Blo 884570 2247821 := bbase (se 3 (by rfl) ⟨421466, by rfl⟩ : syracuseStep 2247821 = 842933) (by norm_num)
theorem B1264781 : Blo 884570 1264781 := bbase (se 3 (by rfl) ⟨237146, by rfl⟩ : syracuseStep 1264781 = 474293) (by norm_num)
theorem B3591317 : Blo 884570 3591317 := bbase (se 6 (by rfl) ⟨84171, by rfl⟩ : syracuseStep 3591317 = 168343) (by norm_num)
theorem B1330325 : Blo 884570 1330325 := bbase (se 6 (by rfl) ⟨31179, by rfl⟩ : syracuseStep 1330325 = 62359) (by norm_num)
theorem B1494173 : Blo 884570 1494173 := bbase (se 3 (by rfl) ⟨280157, by rfl⟩ : syracuseStep 1494173 = 560315) (by norm_num)
theorem B1330349 : Blo 884570 1330349 := bbase (se 3 (by rfl) ⟨249440, by rfl⟩ : syracuseStep 1330349 = 498881) (by norm_num)
theorem B1330373 : Blo 884570 1330373 := bbase (se 4 (by rfl) ⟨124722, by rfl⟩ : syracuseStep 1330373 = 249445) (by norm_num)
theorem B1330397 : Blo 884570 1330397 := bbase (se 3 (by rfl) ⟨249449, by rfl⟩ : syracuseStep 1330397 = 498899) (by norm_num)
theorem B3788005 : Blo 884570 3788005 := bbase (se 4 (by rfl) ⟨355125, by rfl⟩ : syracuseStep 3788005 = 710251) (by norm_num)
theorem B3788021 : Blo 884570 3788021 := bbase (se 5 (by rfl) ⟨177563, by rfl⟩ : syracuseStep 3788021 = 355127) (by norm_num)
theorem B1330421 : Blo 884570 1330421 := bbase (se 5 (by rfl) ⟨62363, by rfl⟩ : syracuseStep 1330421 = 124727) (by norm_num)
theorem B1330445 : Blo 884570 1330445 := bbase (se 3 (by rfl) ⟨249458, by rfl⟩ : syracuseStep 1330445 = 498917) (by norm_num)
theorem B1494301 : Blo 884570 1494301 := bbase (se 3 (by rfl) ⟨280181, by rfl⟩ : syracuseStep 1494301 = 560363) (by norm_num)
theorem B1330469 : Blo 884570 1330469 := bbase (se 4 (by rfl) ⟨124731, by rfl⟩ : syracuseStep 1330469 = 249463) (by norm_num)
theorem B1330493 : Blo 884570 1330493 := bbase (se 3 (by rfl) ⟨249467, by rfl⟩ : syracuseStep 1330493 = 498935) (by norm_num)
theorem B2248013 : Blo 884570 2248013 := bbase (se 3 (by rfl) ⟨421502, by rfl⟩ : syracuseStep 2248013 = 843005) (by norm_num)
theorem B1330517 : Blo 884570 1330517 := bbase (se 11 (by rfl) ⟨974, by rfl⟩ : syracuseStep 1330517 = 1949) (by norm_num)
theorem B1330541 : Blo 884570 1330541 := bbase (se 3 (by rfl) ⟨249476, by rfl⟩ : syracuseStep 1330541 = 498953) (by norm_num)
theorem B1494389 : Blo 884570 1494389 := bbase (se 5 (by rfl) ⟨70049, by rfl⟩ : syracuseStep 1494389 = 140099) (by norm_num)
theorem B1330565 : Blo 884570 1330565 := bbase (se 4 (by rfl) ⟨124740, by rfl⟩ : syracuseStep 1330565 = 249481) (by norm_num)
theorem B1330589 : Blo 884570 1330589 := bbase (se 3 (by rfl) ⟨249485, by rfl⟩ : syracuseStep 1330589 = 498971) (by norm_num)
theorem B1330613 : Blo 884570 1330613 := bbase (se 5 (by rfl) ⟨62372, by rfl⟩ : syracuseStep 1330613 = 124745) (by norm_num)
theorem B1330637 : Blo 884570 1330637 := bbase (se 3 (by rfl) ⟨249494, by rfl⟩ : syracuseStep 1330637 = 498989) (by norm_num)
theorem B1330661 : Blo 884570 1330661 := bbase (se 4 (by rfl) ⟨124749, by rfl⟩ : syracuseStep 1330661 = 249499) (by norm_num)
theorem B3198437 : Blo 884570 3198437 := bbase (se 4 (by rfl) ⟨299853, by rfl⟩ : syracuseStep 3198437 = 599707) (by norm_num)
theorem B1494517 : Blo 884570 1494517 := bbase (se 5 (by rfl) ⟨70055, by rfl⟩ : syracuseStep 1494517 = 140111) (by norm_num)
theorem B1330685 : Blo 884570 1330685 := bbase (se 3 (by rfl) ⟨249503, by rfl⟩ : syracuseStep 1330685 = 499007) (by norm_num)
theorem B1330709 : Blo 884570 1330709 := bbase (se 6 (by rfl) ⟨31188, by rfl⟩ : syracuseStep 1330709 = 62377) (by norm_num)
theorem B1330733 : Blo 884570 1330733 := bbase (se 3 (by rfl) ⟨249512, by rfl⟩ : syracuseStep 1330733 = 499025) (by norm_num)
theorem B1330757 : Blo 884570 1330757 := bbase (se 4 (by rfl) ⟨124758, by rfl⟩ : syracuseStep 1330757 = 249517) (by norm_num)
theorem B1494605 : Blo 884570 1494605 := bbase (se 3 (by rfl) ⟨280238, by rfl⟩ : syracuseStep 1494605 = 560477) (by norm_num)
theorem B1199701 : Blo 884570 1199701 := bbase (se 8 (by rfl) ⟨7029, by rfl⟩ : syracuseStep 1199701 = 14059) (by norm_num)
theorem B1330781 : Blo 884570 1330781 := bbase (se 3 (by rfl) ⟨249521, by rfl⟩ : syracuseStep 1330781 = 499043) (by norm_num)
theorem B3198565 : Blo 884570 3198565 := bbase (se 4 (by rfl) ⟨299865, by rfl⟩ : syracuseStep 3198565 = 599731) (by norm_num)
theorem B1330805 : Blo 884570 1330805 := bbase (se 5 (by rfl) ⟨62381, by rfl⟩ : syracuseStep 1330805 = 124763) (by norm_num)
theorem B1330829 : Blo 884570 1330829 := bbase (se 3 (by rfl) ⟨249530, by rfl⟩ : syracuseStep 1330829 = 499061) (by norm_num)
theorem B1330853 : Blo 884570 1330853 := bbase (se 4 (by rfl) ⟨124767, by rfl⟩ : syracuseStep 1330853 = 249535) (by norm_num)
theorem B2248357 : Blo 884570 2248357 := bbase (se 4 (by rfl) ⟨210783, by rfl⟩ : syracuseStep 2248357 = 421567) (by norm_num)
theorem B1330877 : Blo 884570 1330877 := bbase (se 3 (by rfl) ⟨249539, by rfl⟩ : syracuseStep 1330877 = 499079) (by norm_num)
theorem B1494733 : Blo 884570 1494733 := bbase (se 3 (by rfl) ⟨280262, by rfl⟩ : syracuseStep 1494733 = 560525) (by norm_num)
theorem B1330901 : Blo 884570 1330901 := bbase (se 7 (by rfl) ⟨15596, by rfl⟩ : syracuseStep 1330901 = 31193) (by norm_num)
theorem B1330925 : Blo 884570 1330925 := bbase (se 3 (by rfl) ⟨249548, by rfl⟩ : syracuseStep 1330925 = 499097) (by norm_num)
theorem B1330949 : Blo 884570 1330949 := bbase (se 4 (by rfl) ⟨124776, by rfl⟩ : syracuseStep 1330949 = 249553) (by norm_num)
theorem B2248469 : Blo 884570 2248469 := bbase (se 6 (by rfl) ⟨52698, by rfl⟩ : syracuseStep 2248469 = 105397) (by norm_num)
theorem B1330973 : Blo 884570 1330973 := bbase (se 3 (by rfl) ⟨249557, by rfl⟩ : syracuseStep 1330973 = 499115) (by norm_num)
theorem B1494821 : Blo 884570 1494821 := bbase (se 4 (by rfl) ⟨140139, by rfl⟩ : syracuseStep 1494821 = 280279) (by norm_num)
theorem B1330997 : Blo 884570 1330997 := bbase (se 5 (by rfl) ⟨62390, by rfl⟩ : syracuseStep 1330997 = 124781) (by norm_num)
theorem B1331021 : Blo 884570 1331021 := bbase (se 3 (by rfl) ⟨249566, by rfl⟩ : syracuseStep 1331021 = 499133) (by norm_num)
theorem B1331045 : Blo 884570 1331045 := bbase (se 4 (by rfl) ⟨124785, by rfl⟩ : syracuseStep 1331045 = 249571) (by norm_num)
theorem B1331069 : Blo 884570 1331069 := bbase (se 3 (by rfl) ⟨249575, by rfl⟩ : syracuseStep 1331069 = 499151) (by norm_num)
theorem B1331093 : Blo 884570 1331093 := bbase (se 6 (by rfl) ⟨31197, by rfl⟩ : syracuseStep 1331093 = 62395) (by norm_num)
theorem B1494949 : Blo 884570 1494949 := bbase (se 4 (by rfl) ⟨140151, by rfl⟩ : syracuseStep 1494949 = 280303) (by norm_num)
theorem B1331117 : Blo 884570 1331117 := bbase (se 3 (by rfl) ⟨249584, by rfl⟩ : syracuseStep 1331117 = 499169) (by norm_num)
theorem B3362741 : Blo 884570 3362741 := bbase (se 5 (by rfl) ⟨157628, by rfl⟩ : syracuseStep 3362741 = 315257) (by norm_num)
theorem B1331141 : Blo 884570 1331141 := bbase (se 4 (by rfl) ⟨124794, by rfl⟩ : syracuseStep 1331141 = 249589) (by norm_num)
theorem B2248661 : Blo 884570 2248661 := bbase (se 7 (by rfl) ⟨26351, by rfl⟩ : syracuseStep 2248661 = 52703) (by norm_num)
theorem B1331165 : Blo 884570 1331165 := bbase (se 3 (by rfl) ⟨249593, by rfl⟩ : syracuseStep 1331165 = 499187) (by norm_num)
theorem B1331189 : Blo 884570 1331189 := bbase (se 5 (by rfl) ⟨62399, by rfl⟩ : syracuseStep 1331189 = 124799) (by norm_num)
theorem B1495037 : Blo 884570 1495037 := bbase (se 3 (by rfl) ⟨280319, by rfl⟩ : syracuseStep 1495037 = 560639) (by norm_num)
theorem B1331213 : Blo 884570 1331213 := bbase (se 3 (by rfl) ⟨249602, by rfl⟩ : syracuseStep 1331213 = 499205) (by norm_num)
theorem B1331237 : Blo 884570 1331237 := bbase (se 4 (by rfl) ⟨124803, by rfl⟩ : syracuseStep 1331237 = 249607) (by norm_num)
theorem B6377525 : Blo 884570 6377525 := bbase (se 5 (by rfl) ⟨298946, by rfl⟩ : syracuseStep 6377525 = 597893) (by norm_num)
theorem B1331261 : Blo 884570 1331261 := bbase (se 3 (by rfl) ⟨249611, by rfl⟩ : syracuseStep 1331261 = 499223) (by norm_num)
theorem B1331285 : Blo 884570 1331285 := bbase (se 8 (by rfl) ⟨7800, by rfl⟩ : syracuseStep 1331285 = 15601) (by norm_num)
theorem B1331309 : Blo 884570 1331309 := bbase (se 3 (by rfl) ⟨249620, by rfl⟩ : syracuseStep 1331309 = 499241) (by norm_num)
theorem B1495165 : Blo 884570 1495165 := bbase (se 3 (by rfl) ⟨280343, by rfl⟩ : syracuseStep 1495165 = 560687) (by norm_num)
theorem B1331333 : Blo 884570 1331333 := bbase (se 4 (by rfl) ⟨124812, by rfl⟩ : syracuseStep 1331333 = 249625) (by norm_num)
theorem B1331357 : Blo 884570 1331357 := bbase (se 3 (by rfl) ⟨249629, by rfl⟩ : syracuseStep 1331357 = 499259) (by norm_num)
theorem B1331381 : Blo 884570 1331381 := bbase (se 5 (by rfl) ⟨62408, by rfl⟩ : syracuseStep 1331381 = 124817) (by norm_num)
theorem B1331405 : Blo 884570 1331405 := bbase (se 3 (by rfl) ⟨249638, by rfl⟩ : syracuseStep 1331405 = 499277) (by norm_num)
theorem B3363029 : Blo 884570 3363029 := bbase (se 7 (by rfl) ⟨39410, by rfl⟩ : syracuseStep 3363029 = 78821) (by norm_num)
theorem B1495253 : Blo 884570 1495253 := bbase (se 7 (by rfl) ⟨17522, by rfl⟩ : syracuseStep 1495253 = 35045) (by norm_num)
theorem B1331429 : Blo 884570 1331429 := bbase (se 4 (by rfl) ⟨124821, by rfl⟩ : syracuseStep 1331429 = 249643) (by norm_num)
theorem B1331453 : Blo 884570 1331453 := bbase (se 3 (by rfl) ⟨249647, by rfl⟩ : syracuseStep 1331453 = 499295) (by norm_num)
theorem B1331477 : Blo 884570 1331477 := bbase (se 6 (by rfl) ⟨31206, by rfl⟩ : syracuseStep 1331477 = 62413) (by norm_num)
theorem B1331501 : Blo 884570 1331501 := bbase (se 3 (by rfl) ⟨249656, by rfl⟩ : syracuseStep 1331501 = 499313) (by norm_num)
theorem B2249005 : Blo 884570 2249005 := bbase (se 3 (by rfl) ⟨421688, by rfl⟩ : syracuseStep 2249005 = 843377) (by norm_num)
theorem B1331525 : Blo 884570 1331525 := bbase (se 4 (by rfl) ⟨124830, by rfl⟩ : syracuseStep 1331525 = 249661) (by norm_num)
theorem B1495381 : Blo 884570 1495381 := bbase (se 10 (by rfl) ⟨2190, by rfl⟩ : syracuseStep 1495381 = 4381) (by norm_num)
theorem B1331549 : Blo 884570 1331549 := bbase (se 3 (by rfl) ⟨249665, by rfl⟩ : syracuseStep 1331549 = 499331) (by norm_num)
theorem B3887461 : Blo 884570 3887461 := bbase (se 4 (by rfl) ⟨364449, by rfl⟩ : syracuseStep 3887461 = 728899) (by norm_num)
theorem B1331573 : Blo 884570 1331573 := bbase (se 5 (by rfl) ⟨62417, by rfl⟩ : syracuseStep 1331573 = 124835) (by norm_num)
theorem B1331597 : Blo 884570 1331597 := bbase (se 3 (by rfl) ⟨249674, by rfl⟩ : syracuseStep 1331597 = 499349) (by norm_num)
theorem B2249117 : Blo 884570 2249117 := bbase (se 3 (by rfl) ⟨421709, by rfl⟩ : syracuseStep 2249117 = 843419) (by norm_num)
theorem B1331621 : Blo 884570 1331621 := bbase (se 4 (by rfl) ⟨124839, by rfl⟩ : syracuseStep 1331621 = 249679) (by norm_num)
theorem B1495469 : Blo 884570 1495469 := bbase (se 3 (by rfl) ⟨280400, by rfl⟩ : syracuseStep 1495469 = 560801) (by norm_num)
theorem B1200565 : Blo 884570 1200565 := bbase (se 5 (by rfl) ⟨56276, by rfl⟩ : syracuseStep 1200565 = 112553) (by norm_num)
theorem B1331645 : Blo 884570 1331645 := bbase (se 3 (by rfl) ⟨249683, by rfl⟩ : syracuseStep 1331645 = 499367) (by norm_num)
theorem B6738389 : Blo 884570 6738389 := bbase (se 7 (by rfl) ⟨78965, by rfl⟩ : syracuseStep 6738389 = 157931) (by norm_num)
theorem B1331669 : Blo 884570 1331669 := bbase (se 7 (by rfl) ⟨15605, by rfl⟩ : syracuseStep 1331669 = 31211) (by norm_num)
theorem B1331693 : Blo 884570 1331693 := bbase (se 3 (by rfl) ⟨249692, by rfl⟩ : syracuseStep 1331693 = 499385) (by norm_num)
theorem B1331717 : Blo 884570 1331717 := bbase (se 4 (by rfl) ⟨124848, by rfl⟩ : syracuseStep 1331717 = 249697) (by norm_num)
theorem B18469397 : Blo 884570 18469397 := bbase (se 6 (by rfl) ⟨432876, by rfl⟩ : syracuseStep 18469397 = 865753) (by norm_num)
theorem B1331741 : Blo 884570 1331741 := bbase (se 3 (by rfl) ⟨249701, by rfl⟩ : syracuseStep 1331741 = 499403) (by norm_num)
theorem B1495597 : Blo 884570 1495597 := bbase (se 3 (by rfl) ⟨280424, by rfl⟩ : syracuseStep 1495597 = 560849) (by norm_num)
theorem B1331765 : Blo 884570 1331765 := bbase (se 5 (by rfl) ⟨62426, by rfl⟩ : syracuseStep 1331765 = 124853) (by norm_num)
theorem B1331789 : Blo 884570 1331789 := bbase (se 3 (by rfl) ⟨249710, by rfl⟩ : syracuseStep 1331789 = 499421) (by norm_num)
theorem B1331813 : Blo 884570 1331813 := bbase (se 4 (by rfl) ⟨124857, by rfl⟩ : syracuseStep 1331813 = 249715) (by norm_num)
theorem B1331837 : Blo 884570 1331837 := bbase (se 3 (by rfl) ⟨249719, by rfl⟩ : syracuseStep 1331837 = 499439) (by norm_num)
theorem B1495685 : Blo 884570 1495685 := bbase (se 4 (by rfl) ⟨140220, by rfl⟩ : syracuseStep 1495685 = 280441) (by norm_num)
theorem B1331861 : Blo 884570 1331861 := bbase (se 6 (by rfl) ⟨31215, by rfl⟩ : syracuseStep 1331861 = 62431) (by norm_num)
theorem B1331885 : Blo 884570 1331885 := bbase (se 3 (by rfl) ⟨249728, by rfl⟩ : syracuseStep 1331885 = 499457) (by norm_num)
theorem B1331909 : Blo 884570 1331909 := bbase (se 4 (by rfl) ⟨124866, by rfl⟩ : syracuseStep 1331909 = 249733) (by norm_num)
theorem B1331933 : Blo 884570 1331933 := bbase (se 3 (by rfl) ⟨249737, by rfl⟩ : syracuseStep 1331933 = 499475) (by norm_num)
theorem B1594093 : Blo 884570 1594093 := bbase (se 3 (by rfl) ⟨298892, by rfl⟩ : syracuseStep 1594093 = 597785) (by norm_num)
theorem B1331957 : Blo 884570 1331957 := bbase (se 5 (by rfl) ⟨62435, by rfl⟩ : syracuseStep 1331957 = 124871) (by norm_num)
theorem B1495813 : Blo 884570 1495813 := bbase (se 4 (by rfl) ⟨140232, by rfl⟩ : syracuseStep 1495813 = 280465) (by norm_num)
theorem B1200901 : Blo 884570 1200901 := bbase (se 4 (by rfl) ⟨112584, by rfl⟩ : syracuseStep 1200901 = 225169) (by norm_num)
theorem B1331981 : Blo 884570 1331981 := bbase (se 3 (by rfl) ⟨249746, by rfl⟩ : syracuseStep 1331981 = 499493) (by norm_num)
theorem B1332005 : Blo 884570 1332005 := bbase (se 4 (by rfl) ⟨124875, by rfl⟩ : syracuseStep 1332005 = 249751) (by norm_num)
theorem B1332029 : Blo 884570 1332029 := bbase (se 3 (by rfl) ⟨249755, by rfl⟩ : syracuseStep 1332029 = 499511) (by norm_num)
theorem B1332053 : Blo 884570 1332053 := bbase (se 9 (by rfl) ⟨3902, by rfl⟩ : syracuseStep 1332053 = 7805) (by norm_num)
theorem B1495901 : Blo 884570 1495901 := bbase (se 3 (by rfl) ⟨280481, by rfl⟩ : syracuseStep 1495901 = 560963) (by norm_num)
theorem B1332077 : Blo 884570 1332077 := bbase (se 3 (by rfl) ⟨249764, by rfl⟩ : syracuseStep 1332077 = 499529) (by norm_num)
theorem B1332101 : Blo 884570 1332101 := bbase (se 4 (by rfl) ⟨124884, by rfl⟩ : syracuseStep 1332101 = 249769) (by norm_num)
theorem B1332125 : Blo 884570 1332125 := bbase (se 3 (by rfl) ⟨249773, by rfl⟩ : syracuseStep 1332125 = 499547) (by norm_num)
theorem B1332149 : Blo 884570 1332149 := bbase (se 5 (by rfl) ⟨62444, by rfl⟩ : syracuseStep 1332149 = 124889) (by norm_num)
theorem B1332173 : Blo 884570 1332173 := bbase (se 3 (by rfl) ⟨249782, by rfl⟩ : syracuseStep 1332173 = 499565) (by norm_num)
theorem B1496029 : Blo 884570 1496029 := bbase (se 3 (by rfl) ⟨280505, by rfl⟩ : syracuseStep 1496029 = 561011) (by norm_num)
theorem B1332197 : Blo 884570 1332197 := bbase (se 4 (by rfl) ⟨124893, by rfl⟩ : syracuseStep 1332197 = 249787) (by norm_num)
theorem B1889261 : Blo 884570 1889261 := bbase (se 3 (by rfl) ⟨354236, by rfl⟩ : syracuseStep 1889261 = 708473) (by norm_num)
theorem B1332221 : Blo 884570 1332221 := bbase (se 3 (by rfl) ⟨249791, by rfl⟩ : syracuseStep 1332221 = 499583) (by norm_num)
theorem B1332245 : Blo 884570 1332245 := bbase (se 6 (by rfl) ⟨31224, by rfl⟩ : syracuseStep 1332245 = 62449) (by norm_num)
theorem B1332269 : Blo 884570 1332269 := bbase (se 3 (by rfl) ⟨249800, by rfl⟩ : syracuseStep 1332269 = 499601) (by norm_num)
theorem B1496117 : Blo 884570 1496117 := bbase (se 5 (by rfl) ⟨70130, by rfl⟩ : syracuseStep 1496117 = 140261) (by norm_num)
theorem B1332293 : Blo 884570 1332293 := bbase (se 4 (by rfl) ⟨124902, by rfl⟩ : syracuseStep 1332293 = 249805) (by norm_num)
theorem B1332317 : Blo 884570 1332317 := bbase (se 3 (by rfl) ⟨249809, by rfl⟩ : syracuseStep 1332317 = 499619) (by norm_num)
theorem B1889381 : Blo 884570 1889381 := bbase (se 4 (by rfl) ⟨177129, by rfl⟩ : syracuseStep 1889381 = 354259) (by norm_num)
theorem B1332341 : Blo 884570 1332341 := bbase (se 5 (by rfl) ⟨62453, by rfl⟩ : syracuseStep 1332341 = 124907) (by norm_num)
theorem B1332365 : Blo 884570 1332365 := bbase (se 3 (by rfl) ⟨249818, by rfl⟩ : syracuseStep 1332365 = 499637) (by norm_num)
theorem B1332389 : Blo 884570 1332389 := bbase (se 4 (by rfl) ⟨124911, by rfl⟩ : syracuseStep 1332389 = 249823) (by norm_num)
theorem B1496245 : Blo 884570 1496245 := bbase (se 5 (by rfl) ⟨70136, by rfl⟩ : syracuseStep 1496245 = 140273) (by norm_num)
theorem B1332413 : Blo 884570 1332413 := bbase (se 3 (by rfl) ⟨249827, by rfl⟩ : syracuseStep 1332413 = 499655) (by norm_num)
theorem B4478165 : Blo 884570 4478165 := bbase (se 7 (by rfl) ⟨52478, by rfl⟩ : syracuseStep 4478165 = 104957) (by norm_num)
theorem B1332437 : Blo 884570 1332437 := bbase (se 7 (by rfl) ⟨15614, by rfl⟩ : syracuseStep 1332437 = 31229) (by norm_num)
theorem B1332461 : Blo 884570 1332461 := bbase (se 3 (by rfl) ⟨249836, by rfl⟩ : syracuseStep 1332461 = 499673) (by norm_num)
theorem B1332485 : Blo 884570 1332485 := bbase (se 4 (by rfl) ⟨124920, by rfl⟩ : syracuseStep 1332485 = 249841) (by norm_num)
theorem B1135885 : Blo 884570 1135885 := bbase (se 3 (by rfl) ⟨212978, by rfl⟩ : syracuseStep 1135885 = 425957) (by norm_num)
theorem B1496333 : Blo 884570 1496333 := bbase (se 3 (by rfl) ⟨280562, by rfl⟩ : syracuseStep 1496333 = 561125) (by norm_num)
theorem B1332509 : Blo 884570 1332509 := bbase (se 3 (by rfl) ⟨249845, by rfl⟩ : syracuseStep 1332509 = 499691) (by norm_num)
theorem B1332533 : Blo 884570 1332533 := bbase (se 5 (by rfl) ⟨62462, by rfl⟩ : syracuseStep 1332533 = 124925) (by norm_num)
theorem B1332557 : Blo 884570 1332557 := bbase (se 3 (by rfl) ⟨249854, by rfl⟩ : syracuseStep 1332557 = 499709) (by norm_num)
theorem B1332581 : Blo 884570 1332581 := bbase (se 4 (by rfl) ⟨124929, by rfl⟩ : syracuseStep 1332581 = 249859) (by norm_num)
theorem B3364213 : Blo 884570 3364213 := bbase (se 5 (by rfl) ⟨157697, by rfl⟩ : syracuseStep 3364213 = 315395) (by norm_num)
theorem B1332605 : Blo 884570 1332605 := bbase (se 3 (by rfl) ⟨249863, by rfl⟩ : syracuseStep 1332605 = 499727) (by norm_num)
theorem B1496461 : Blo 884570 1496461 := bbase (se 3 (by rfl) ⟨280586, by rfl⟩ : syracuseStep 1496461 = 561173) (by norm_num)
theorem B1332629 : Blo 884570 1332629 := bbase (se 6 (by rfl) ⟨31233, by rfl⟩ : syracuseStep 1332629 = 62467) (by norm_num)
theorem B1332653 : Blo 884570 1332653 := bbase (se 3 (by rfl) ⟨249872, by rfl⟩ : syracuseStep 1332653 = 499745) (by norm_num)
theorem B3790277 : Blo 884570 3790277 := bbase (se 4 (by rfl) ⟨355338, by rfl⟩ : syracuseStep 3790277 = 710677) (by norm_num)
theorem B1332677 : Blo 884570 1332677 := bbase (se 4 (by rfl) ⟨124938, by rfl⟩ : syracuseStep 1332677 = 249877) (by norm_num)
theorem B1332701 : Blo 884570 1332701 := bbase (se 3 (by rfl) ⟨249881, by rfl⟩ : syracuseStep 1332701 = 499763) (by norm_num)
theorem B1496549 : Blo 884570 1496549 := bbase (se 4 (by rfl) ⟨140301, by rfl⟩ : syracuseStep 1496549 = 280603) (by norm_num)
theorem B1332725 : Blo 884570 1332725 := bbase (se 5 (by rfl) ⟨62471, by rfl⟩ : syracuseStep 1332725 = 124943) (by norm_num)
theorem B1332749 : Blo 884570 1332749 := bbase (se 3 (by rfl) ⟨249890, by rfl⟩ : syracuseStep 1332749 = 499781) (by norm_num)
theorem B1332773 : Blo 884570 1332773 := bbase (se 4 (by rfl) ⟨124947, by rfl⟩ : syracuseStep 1332773 = 249895) (by norm_num)
theorem B1332797 : Blo 884570 1332797 := bbase (se 3 (by rfl) ⟨249899, by rfl⟩ : syracuseStep 1332797 = 499799) (by norm_num)
theorem B1365581 : Blo 884570 1365581 := bbase (se 3 (by rfl) ⟨256046, by rfl⟩ : syracuseStep 1365581 = 512093) (by norm_num)
theorem B1332821 : Blo 884570 1332821 := bbase (se 8 (by rfl) ⟨7809, by rfl⟩ : syracuseStep 1332821 = 15619) (by norm_num)
theorem B1594973 : Blo 884570 1594973 := bbase (se 3 (by rfl) ⟨299057, by rfl⟩ : syracuseStep 1594973 = 598115) (by norm_num)
theorem B1496677 : Blo 884570 1496677 := bbase (se 4 (by rfl) ⟨140313, by rfl⟩ : syracuseStep 1496677 = 280627) (by norm_num)
theorem B1332845 : Blo 884570 1332845 := bbase (se 3 (by rfl) ⟨249908, by rfl⟩ : syracuseStep 1332845 = 499817) (by norm_num)
theorem B3200629 : Blo 884570 3200629 := bbase (se 5 (by rfl) ⟨150029, by rfl⟩ : syracuseStep 3200629 = 300059) (by norm_num)
theorem B3364517 : Blo 884570 3364517 := bbase (se 4 (by rfl) ⟨315423, by rfl⟩ : syracuseStep 3364517 = 630847) (by norm_num)
theorem B1496765 : Blo 884570 1496765 := bbase (se 3 (by rfl) ⟨280643, by rfl⟩ : syracuseStep 1496765 = 561287) (by norm_num)
theorem B1890013 : Blo 884570 1890013 := bbase (se 3 (by rfl) ⟨354377, by rfl⟩ : syracuseStep 1890013 = 708755) (by norm_num)
theorem B10082069 : Blo 884570 10082069 := bbase (se 6 (by rfl) ⟨236298, by rfl⟩ : syracuseStep 10082069 = 472597) (by norm_num)
theorem B1595189 : Blo 884570 1595189 := bbase (se 5 (by rfl) ⟨74774, by rfl⟩ : syracuseStep 1595189 = 149549) (by norm_num)
theorem B1496893 : Blo 884570 1496893 := bbase (se 3 (by rfl) ⟨280667, by rfl⟩ : syracuseStep 1496893 = 561335) (by norm_num)
theorem B2840453 : Blo 884570 2840453 := bbase (se 4 (by rfl) ⟨266292, by rfl⟩ : syracuseStep 2840453 = 532585) (by norm_num)
theorem B1496981 : Blo 884570 1496981 := bbase (se 6 (by rfl) ⟨35085, by rfl⟩ : syracuseStep 1496981 = 70171) (by norm_num)
theorem B1595333 : Blo 884570 1595333 := bbase (se 4 (by rfl) ⟨149562, by rfl⟩ : syracuseStep 1595333 = 299125) (by norm_num)
theorem B1595413 : Blo 884570 1595413 := bbase (se 6 (by rfl) ⟨37392, by rfl⟩ : syracuseStep 1595413 = 74785) (by norm_num)
theorem B1497109 : Blo 884570 1497109 := bbase (se 6 (by rfl) ⟨35088, by rfl⟩ : syracuseStep 1497109 = 70177) (by norm_num)
theorem B2021429 : Blo 884570 2021429 := bbase (se 5 (by rfl) ⟨94754, by rfl⟩ : syracuseStep 2021429 = 189509) (by norm_num)
theorem B4053077 : Blo 884570 4053077 := bbase (se 8 (by rfl) ⟨23748, by rfl⟩ : syracuseStep 4053077 = 47497) (by norm_num)
theorem B1497197 : Blo 884570 1497197 := bbase (se 3 (by rfl) ⟨280724, by rfl⟩ : syracuseStep 1497197 = 561449) (by norm_num)
theorem B1366253 : Blo 884570 1366253 := bbase (se 3 (by rfl) ⟨256172, by rfl⟩ : syracuseStep 1366253 = 512345) (by norm_num)
theorem B1497325 : Blo 884570 1497325 := bbase (se 3 (by rfl) ⟨280748, by rfl⟩ : syracuseStep 1497325 = 561497) (by norm_num)
theorem B1497413 : Blo 884570 1497413 := bbase (se 4 (by rfl) ⟨140382, by rfl⟩ : syracuseStep 1497413 = 280765) (by norm_num)
theorem B1497541 : Blo 884570 1497541 := bbase (se 4 (by rfl) ⟨140394, by rfl⟩ : syracuseStep 1497541 = 280789) (by norm_num)
theorem B4479461 : Blo 884570 4479461 := bbase (se 4 (by rfl) ⟨419949, by rfl⟩ : syracuseStep 4479461 = 839899) (by norm_num)
theorem B1497629 : Blo 884570 1497629 := bbase (se 3 (by rfl) ⟨280805, by rfl⟩ : syracuseStep 1497629 = 561611) (by norm_num)
theorem B1890901 : Blo 884570 1890901 := bbase (se 8 (by rfl) ⟨11079, by rfl⟩ : syracuseStep 1890901 = 22159) (by norm_num)
theorem B8182421 : Blo 884570 8182421 := bbase (se 6 (by rfl) ⟨191775, by rfl⟩ : syracuseStep 8182421 = 383551) (by norm_num)
theorem B1497757 : Blo 884570 1497757 := bbase (se 3 (by rfl) ⟨280829, by rfl⟩ : syracuseStep 1497757 = 561659) (by norm_num)
theorem B1891021 : Blo 884570 1891021 := bbase (se 3 (by rfl) ⟨354566, by rfl⟩ : syracuseStep 1891021 = 709133) (by norm_num)
theorem B1497845 : Blo 884570 1497845 := bbase (se 5 (by rfl) ⟨70211, by rfl⟩ : syracuseStep 1497845 = 140423) (by norm_num)
theorem B3595013 : Blo 884570 3595013 := bbase (se 4 (by rfl) ⟨337032, by rfl⟩ : syracuseStep 3595013 = 674065) (by norm_num)
theorem B1497973 : Blo 884570 1497973 := bbase (se 5 (by rfl) ⟨70217, by rfl⟩ : syracuseStep 1497973 = 140435) (by norm_num)
theorem B3234725 : Blo 884570 3234725 := bbase (se 4 (by rfl) ⟨303255, by rfl⟩ : syracuseStep 3234725 = 606511) (by norm_num)
theorem B1891277 : Blo 884570 1891277 := bbase (se 3 (by rfl) ⟨354614, by rfl⟩ : syracuseStep 1891277 = 709229) (by norm_num)
theorem B1498061 : Blo 884570 1498061 := bbase (se 3 (by rfl) ⟨280886, by rfl⟩ : syracuseStep 1498061 = 561773) (by norm_num)
theorem B1498189 : Blo 884570 1498189 := bbase (se 3 (by rfl) ⟨280910, by rfl⟩ : syracuseStep 1498189 = 561821) (by norm_num)
theorem B2841733 : Blo 884570 2841733 := bbase (se 4 (by rfl) ⟨266412, by rfl⟩ : syracuseStep 2841733 = 532825) (by norm_num)
theorem B1498277 : Blo 884570 1498277 := bbase (se 4 (by rfl) ⟨140463, by rfl⟩ : syracuseStep 1498277 = 280927) (by norm_num)
theorem B5692693 : Blo 884570 5692693 := bbase (se 6 (by rfl) ⟨133422, by rfl⟩ : syracuseStep 5692693 = 266845) (by norm_num)
theorem B1498405 : Blo 884570 1498405 := bbase (se 4 (by rfl) ⟨140475, by rfl⟩ : syracuseStep 1498405 = 280951) (by norm_num)
theorem B4545877 : Blo 884570 4545877 := bbase (se 11 (by rfl) ⟨3329, by rfl⟩ : syracuseStep 4545877 = 6659) (by norm_num)
theorem B1498493 : Blo 884570 1498493 := bbase (se 3 (by rfl) ⟨280967, by rfl⟩ : syracuseStep 1498493 = 561935) (by norm_num)
theorem B3071461 : Blo 884570 3071461 := bbase (se 4 (by rfl) ⟨287949, by rfl⟩ : syracuseStep 3071461 = 575899) (by norm_num)
theorem B1498621 : Blo 884570 1498621 := bbase (se 3 (by rfl) ⟨280991, by rfl⟩ : syracuseStep 1498621 = 561983) (by norm_num)
theorem B4251221 : Blo 884570 4251221 := bbase (se 8 (by rfl) ⟨24909, by rfl⟩ : syracuseStep 4251221 = 49819) (by norm_num)
theorem B1498709 : Blo 884570 1498709 := bbase (se 8 (by rfl) ⟨8781, by rfl⟩ : syracuseStep 1498709 = 17563) (by norm_num)
theorem B4546165 : Blo 884570 4546165 := bbase (se 5 (by rfl) ⟨213101, by rfl⟩ : syracuseStep 4546165 = 426203) (by norm_num)
theorem B1990349 : Blo 884570 1990349 := bbase (se 3 (by rfl) ⟨373190, by rfl⟩ : syracuseStep 1990349 = 746381) (by norm_num)
theorem B1498837 : Blo 884570 1498837 := bbase (se 7 (by rfl) ⟨17564, by rfl⟩ : syracuseStep 1498837 = 35129) (by norm_num)
theorem B3366629 : Blo 884570 3366629 := bbase (se 4 (by rfl) ⟨315621, by rfl⟩ : syracuseStep 3366629 = 631243) (by norm_num)
theorem B4480757 : Blo 884570 4480757 := bbase (se 5 (by rfl) ⟨210035, by rfl⟩ : syracuseStep 4480757 = 420071) (by norm_num)
theorem B1990421 : Blo 884570 1990421 := bbase (se 6 (by rfl) ⟨46650, by rfl⟩ : syracuseStep 1990421 = 93301) (by norm_num)
theorem B1498925 : Blo 884570 1498925 := bbase (se 3 (by rfl) ⟨281048, by rfl⟩ : syracuseStep 1498925 = 562097) (by norm_num)
theorem B1892165 : Blo 884570 1892165 := bbase (se 4 (by rfl) ⟨177390, by rfl⟩ : syracuseStep 1892165 = 354781) (by norm_num)
theorem B1990493 : Blo 884570 1990493 := bbase (se 3 (by rfl) ⟨373217, by rfl⟩ : syracuseStep 1990493 = 746435) (by norm_num)
theorem B2023309 : Blo 884570 2023309 := bbase (se 3 (by rfl) ⟨379370, by rfl⟩ : syracuseStep 2023309 = 758741) (by norm_num)
theorem B1990565 : Blo 884570 1990565 := bbase (se 4 (by rfl) ⟨186615, by rfl⟩ : syracuseStep 1990565 = 373231) (by norm_num)
theorem B1499053 : Blo 884570 1499053 := bbase (se 3 (by rfl) ⟨281072, by rfl⟩ : syracuseStep 1499053 = 562145) (by norm_num)
theorem B1990637 : Blo 884570 1990637 := bbase (se 3 (by rfl) ⟨373244, by rfl⟩ : syracuseStep 1990637 = 746489) (by norm_num)
theorem B974845 : Blo 884570 974845 := bbase (se 3 (by rfl) ⟨182783, by rfl⟩ : syracuseStep 974845 = 365567) (by norm_num)
theorem B3366917 : Blo 884570 3366917 := bbase (se 4 (by rfl) ⟨315648, by rfl⟩ : syracuseStep 3366917 = 631297) (by norm_num)
theorem B1499141 : Blo 884570 1499141 := bbase (se 4 (by rfl) ⟨140544, by rfl⟩ : syracuseStep 1499141 = 281089) (by norm_num)
theorem B1990709 : Blo 884570 1990709 := bbase (se 5 (by rfl) ⟨93314, by rfl⟩ : syracuseStep 1990709 = 186629) (by norm_num)
theorem B1892405 : Blo 884570 1892405 := bbase (se 5 (by rfl) ⟨88706, by rfl⟩ : syracuseStep 1892405 = 177413) (by norm_num)
theorem B1990781 : Blo 884570 1990781 := bbase (se 3 (by rfl) ⟨373271, by rfl⟩ : syracuseStep 1990781 = 746543) (by norm_num)
theorem B1499269 : Blo 884570 1499269 := bbase (se 4 (by rfl) ⟨140556, by rfl⟩ : syracuseStep 1499269 = 281113) (by norm_num)
theorem B1990853 : Blo 884570 1990853 := bbase (se 4 (by rfl) ⟨186642, by rfl⟩ : syracuseStep 1990853 = 373285) (by norm_num)
theorem B1499357 : Blo 884570 1499357 := bbase (se 3 (by rfl) ⟨281129, by rfl⟩ : syracuseStep 1499357 = 562259) (by norm_num)
theorem B1990925 : Blo 884570 1990925 := bbase (se 3 (by rfl) ⟨373298, by rfl⟩ : syracuseStep 1990925 = 746597) (by norm_num)
theorem B4251973 : Blo 884570 4251973 := bbase (se 4 (by rfl) ⟨398622, by rfl⟩ : syracuseStep 4251973 = 797245) (by norm_num)
theorem B1990997 : Blo 884570 1990997 := bbase (se 10 (by rfl) ⟨2916, by rfl⟩ : syracuseStep 1990997 = 5833) (by norm_num)
theorem B1991069 : Blo 884570 1991069 := bbase (se 3 (by rfl) ⟨373325, by rfl⟩ : syracuseStep 1991069 = 746651) (by norm_num)
theorem B2843093 : Blo 884570 2843093 := bbase (se 7 (by rfl) ⟨33317, by rfl⟩ : syracuseStep 2843093 = 66635) (by norm_num)
theorem B1991141 : Blo 884570 1991141 := bbase (se 4 (by rfl) ⟨186669, by rfl⟩ : syracuseStep 1991141 = 373339) (by norm_num)
theorem B1991213 : Blo 884570 1991213 := bbase (se 3 (by rfl) ⟨373352, by rfl⟩ : syracuseStep 1991213 = 746705) (by norm_num)
theorem B1892909 : Blo 884570 1892909 := bbase (se 3 (by rfl) ⟨354920, by rfl⟩ : syracuseStep 1892909 = 709841) (by norm_num)
theorem B1892917 : Blo 884570 1892917 := bbase (se 5 (by rfl) ⟨88730, by rfl⟩ : syracuseStep 1892917 = 177461) (by norm_num)
theorem B2843221 : Blo 884570 2843221 := bbase (se 8 (by rfl) ⟨16659, by rfl⟩ : syracuseStep 2843221 = 33319) (by norm_num)
theorem B1991285 : Blo 884570 1991285 := bbase (se 5 (by rfl) ⟨93341, by rfl⟩ : syracuseStep 1991285 = 186683) (by norm_num)
theorem B1991357 : Blo 884570 1991357 := bbase (se 3 (by rfl) ⟨373379, by rfl⟩ : syracuseStep 1991357 = 746759) (by norm_num)
theorem B8086229 : Blo 884570 8086229 := bbase (se 7 (by rfl) ⟨94760, by rfl⟩ : syracuseStep 8086229 = 189521) (by norm_num)
theorem B1991429 : Blo 884570 1991429 := bbase (se 4 (by rfl) ⟨186696, by rfl⟩ : syracuseStep 1991429 = 373393) (by norm_num)
theorem B1991501 : Blo 884570 1991501 := bbase (se 3 (by rfl) ⟨373406, by rfl⟩ : syracuseStep 1991501 = 746813) (by norm_num)
theorem B2843477 : Blo 884570 2843477 := bbase (se 9 (by rfl) ⟨8330, by rfl⟩ : syracuseStep 2843477 = 16661) (by norm_num)
theorem B1991573 : Blo 884570 1991573 := bbase (se 6 (by rfl) ⟨46677, by rfl⟩ : syracuseStep 1991573 = 93355) (by norm_num)
theorem B3597205 : Blo 884570 3597205 := bbase (se 6 (by rfl) ⟨84309, by rfl⟩ : syracuseStep 3597205 = 168619) (by norm_num)
theorem B1991645 : Blo 884570 1991645 := bbase (se 3 (by rfl) ⟨373433, by rfl⟩ : syracuseStep 1991645 = 746867) (by norm_num)
theorem B4482053 : Blo 884570 4482053 := bbase (se 4 (by rfl) ⟨420192, by rfl⟩ : syracuseStep 4482053 = 840385) (by norm_num)
theorem B2024477 : Blo 884570 2024477 := bbase (se 3 (by rfl) ⟨379589, by rfl⟩ : syracuseStep 2024477 = 759179) (by norm_num)
theorem B1991717 : Blo 884570 1991717 := bbase (se 4 (by rfl) ⟨186723, by rfl⟩ : syracuseStep 1991717 = 373447) (by norm_num)
theorem B1991789 : Blo 884570 1991789 := bbase (se 3 (by rfl) ⟨373460, by rfl⟩ : syracuseStep 1991789 = 746921) (by norm_num)
theorem B3368101 : Blo 884570 3368101 := bbase (se 4 (by rfl) ⟨315759, by rfl⟩ : syracuseStep 3368101 = 631519) (by norm_num)
theorem B1991861 : Blo 884570 1991861 := bbase (se 5 (by rfl) ⟨93368, by rfl⟩ : syracuseStep 1991861 = 186737) (by norm_num)
theorem B1991933 : Blo 884570 1991933 := bbase (se 3 (by rfl) ⟨373487, by rfl⟩ : syracuseStep 1991933 = 746975) (by norm_num)
theorem B1992005 : Blo 884570 1992005 := bbase (se 4 (by rfl) ⟨186750, by rfl⟩ : syracuseStep 1992005 = 373501) (by norm_num)
theorem B1598821 : Blo 884570 1598821 := bbase (se 4 (by rfl) ⟨149889, by rfl⟩ : syracuseStep 1598821 = 299779) (by norm_num)
theorem B3794309 : Blo 884570 3794309 := bbase (se 4 (by rfl) ⟨355716, by rfl⟩ : syracuseStep 3794309 = 711433) (by norm_num)
theorem B1992077 : Blo 884570 1992077 := bbase (se 3 (by rfl) ⟨373514, by rfl⟩ : syracuseStep 1992077 = 747029) (by norm_num)
theorem B1992149 : Blo 884570 1992149 := bbase (se 7 (by rfl) ⟨23345, by rfl⟩ : syracuseStep 1992149 = 46691) (by norm_num)
theorem B3368405 : Blo 884570 3368405 := bbase (se 7 (by rfl) ⟨39473, by rfl⟩ : syracuseStep 3368405 = 78947) (by norm_num)
theorem B1992221 : Blo 884570 1992221 := bbase (se 3 (by rfl) ⟨373541, by rfl⟩ : syracuseStep 1992221 = 747083) (by norm_num)
theorem B1992293 : Blo 884570 1992293 := bbase (se 4 (by rfl) ⟨186777, by rfl⟩ : syracuseStep 1992293 = 373555) (by norm_num)
theorem B1894045 : Blo 884570 1894045 := bbase (se 3 (by rfl) ⟨355133, by rfl⟩ : syracuseStep 1894045 = 710267) (by norm_num)
theorem B1992365 : Blo 884570 1992365 := bbase (se 3 (by rfl) ⟨373568, by rfl⟩ : syracuseStep 1992365 = 747137) (by norm_num)
theorem B1992437 : Blo 884570 1992437 := bbase (se 5 (by rfl) ⟨93395, by rfl⟩ : syracuseStep 1992437 = 186791) (by norm_num)
theorem B1992509 : Blo 884570 1992509 := bbase (se 3 (by rfl) ⟨373595, by rfl⟩ : syracuseStep 1992509 = 747191) (by norm_num)
theorem B1992581 : Blo 884570 1992581 := bbase (se 4 (by rfl) ⟨186804, by rfl⟩ : syracuseStep 1992581 = 373609) (by norm_num)
theorem B1992653 : Blo 884570 1992653 := bbase (se 3 (by rfl) ⟨373622, by rfl⟩ : syracuseStep 1992653 = 747245) (by norm_num)
theorem B1992725 : Blo 884570 1992725 := bbase (se 6 (by rfl) ⟨46704, by rfl⟩ : syracuseStep 1992725 = 93409) (by norm_num)
theorem B1894421 : Blo 884570 1894421 := bbase (se 6 (by rfl) ⟨44400, by rfl⟩ : syracuseStep 1894421 = 88801) (by norm_num)
theorem B1009757 : Blo 884570 1009757 := bbase (se 3 (by rfl) ⟨189329, by rfl⟩ : syracuseStep 1009757 = 378659) (by norm_num)
theorem B1992797 : Blo 884570 1992797 := bbase (se 3 (by rfl) ⟨373649, by rfl⟩ : syracuseStep 1992797 = 747299) (by norm_num)
theorem B1992869 : Blo 884570 1992869 := bbase (se 4 (by rfl) ⟨186831, by rfl⟩ : syracuseStep 1992869 = 373663) (by norm_num)
theorem B4548773 : Blo 884570 4548773 := bbase (se 4 (by rfl) ⟨426447, by rfl⟩ : syracuseStep 4548773 = 852895) (by norm_num)
theorem B1992941 : Blo 884570 1992941 := bbase (se 3 (by rfl) ⟨373676, by rfl⟩ : syracuseStep 1992941 = 747353) (by norm_num)
theorem B1796357 : Blo 884570 1796357 := bbase (se 4 (by rfl) ⟨168408, by rfl⟩ : syracuseStep 1796357 = 336817) (by norm_num)
theorem B4483349 : Blo 884570 4483349 := bbase (se 6 (by rfl) ⟨105078, by rfl⟩ : syracuseStep 4483349 = 210157) (by norm_num)
theorem B2025773 : Blo 884570 2025773 := bbase (se 3 (by rfl) ⟨379832, by rfl⟩ : syracuseStep 2025773 = 759665) (by norm_num)
theorem B1993013 : Blo 884570 1993013 := bbase (se 5 (by rfl) ⟨93422, by rfl⟩ : syracuseStep 1993013 = 186845) (by norm_num)
theorem B1993085 : Blo 884570 1993085 := bbase (se 3 (by rfl) ⟨373703, by rfl⟩ : syracuseStep 1993085 = 747407) (by norm_num)
theorem B1599917 : Blo 884570 1599917 := bbase (se 3 (by rfl) ⟨299984, by rfl⟩ : syracuseStep 1599917 = 599969) (by norm_num)
theorem B1993157 : Blo 884570 1993157 := bbase (se 4 (by rfl) ⟨186858, by rfl⟩ : syracuseStep 1993157 = 373717) (by norm_num)
theorem B1993229 : Blo 884570 1993229 := bbase (se 3 (by rfl) ⟨373730, by rfl⟩ : syracuseStep 1993229 = 747461) (by norm_num)
theorem B3074597 : Blo 884570 3074597 := bbase (se 4 (by rfl) ⟨288243, by rfl⟩ : syracuseStep 3074597 = 576487) (by norm_num)
theorem B1993301 : Blo 884570 1993301 := bbase (se 8 (by rfl) ⟨11679, by rfl⟩ : syracuseStep 1993301 = 23359) (by norm_num)
theorem B1993373 : Blo 884570 1993373 := bbase (se 3 (by rfl) ⟨373757, by rfl⟩ : syracuseStep 1993373 = 747515) (by norm_num)
theorem B1010341 : Blo 884570 1010341 := bbase (se 4 (by rfl) ⟨94719, by rfl⟩ : syracuseStep 1010341 = 189439) (by norm_num)
theorem B1993445 : Blo 884570 1993445 := bbase (se 4 (by rfl) ⟨186885, by rfl⟩ : syracuseStep 1993445 = 373771) (by norm_num)
theorem B1993517 : Blo 884570 1993517 := bbase (se 3 (by rfl) ⟨373784, by rfl⟩ : syracuseStep 1993517 = 747569) (by norm_num)
theorem B1796917 : Blo 884570 1796917 := bbase (se 5 (by rfl) ⟨84230, by rfl⟩ : syracuseStep 1796917 = 168461) (by norm_num)
theorem B944989 : Blo 884570 944989 := bbase (se 3 (by rfl) ⟨177185, by rfl⟩ : syracuseStep 944989 = 354371) (by norm_num)
theorem B1993589 : Blo 884570 1993589 := bbase (se 5 (by rfl) ⟨93449, by rfl⟩ : syracuseStep 1993589 = 186899) (by norm_num)
theorem B5401525 : Blo 884570 5401525 := bbase (se 5 (by rfl) ⟨253196, by rfl⟩ : syracuseStep 5401525 = 506393) (by norm_num)
theorem B1993661 : Blo 884570 1993661 := bbase (se 3 (by rfl) ⟨373811, by rfl⟩ : syracuseStep 1993661 = 747623) (by norm_num)
theorem B945109 : Blo 884570 945109 := bbase (se 7 (by rfl) ⟨11075, by rfl⟩ : syracuseStep 945109 = 22151) (by norm_num)
theorem B1993733 : Blo 884570 1993733 := bbase (se 4 (by rfl) ⟨186912, by rfl⟩ : syracuseStep 1993733 = 373825) (by norm_num)
theorem B1993805 : Blo 884570 1993805 := bbase (se 3 (by rfl) ⟨373838, by rfl⟩ : syracuseStep 1993805 = 747677) (by norm_num)
theorem B1993877 : Blo 884570 1993877 := bbase (se 6 (by rfl) ⟨46731, by rfl⟩ : syracuseStep 1993877 = 93463) (by norm_num)
theorem B912569 : Blo 884570 912569 := bbase (se 2 (by rfl) ⟨342213, by rfl⟩ : syracuseStep 912569 = 684427) (by norm_num)
theorem B945361 : Blo 884570 945361 := bbase (se 2 (by rfl) ⟨354510, by rfl⟩ : syracuseStep 945361 = 709021) (by norm_num)
theorem B945365 : Blo 884570 945365 := bbase (se 7 (by rfl) ⟨11078, by rfl⟩ : syracuseStep 945365 = 22157) (by norm_num)
theorem B1993949 : Blo 884570 1993949 := bbase (se 3 (by rfl) ⟨373865, by rfl⟩ : syracuseStep 1993949 = 747731) (by norm_num)
theorem B2845925 : Blo 884570 2845925 := bbase (se 4 (by rfl) ⟨266805, by rfl⟩ : syracuseStep 2845925 = 533611) (by norm_num)
theorem B1994021 : Blo 884570 1994021 := bbase (se 4 (by rfl) ⟨186939, by rfl⟩ : syracuseStep 1994021 = 373879) (by norm_num)
theorem B1994093 : Blo 884570 1994093 := bbase (se 3 (by rfl) ⟨373892, by rfl⟩ : syracuseStep 1994093 = 747785) (by norm_num)
theorem B1994165 : Blo 884570 1994165 := bbase (se 5 (by rfl) ⟨93476, by rfl⟩ : syracuseStep 1994165 = 186953) (by norm_num)
theorem B1797589 : Blo 884570 1797589 := bbase (se 7 (by rfl) ⟨21065, by rfl⟩ : syracuseStep 1797589 = 42131) (by norm_num)
theorem B1994237 : Blo 884570 1994237 := bbase (se 3 (by rfl) ⟨373919, by rfl⟩ : syracuseStep 1994237 = 747839) (by norm_num)
theorem B3370517 : Blo 884570 3370517 := bbase (se 6 (by rfl) ⟨78996, by rfl⟩ : syracuseStep 3370517 = 157993) (by norm_num)
theorem B4484645 : Blo 884570 4484645 := bbase (se 4 (by rfl) ⟨420435, by rfl⟩ : syracuseStep 4484645 = 840871) (by norm_num)
theorem B1994309 : Blo 884570 1994309 := bbase (se 4 (by rfl) ⟨186966, by rfl⟩ : syracuseStep 1994309 = 373933) (by norm_num)
theorem B1896061 : Blo 884570 1896061 := bbase (se 3 (by rfl) ⟨355511, by rfl⟩ : syracuseStep 1896061 = 711023) (by norm_num)
theorem B1994381 : Blo 884570 1994381 := bbase (se 3 (by rfl) ⟨373946, by rfl⟩ : syracuseStep 1994381 = 747893) (by norm_num)
theorem B1011349 : Blo 884570 1011349 := bbase (se 6 (by rfl) ⟨23703, by rfl⟩ : syracuseStep 1011349 = 47407) (by norm_num)
theorem B1994453 : Blo 884570 1994453 := bbase (se 7 (by rfl) ⟨23372, by rfl⟩ : syracuseStep 1994453 = 46745) (by norm_num)
theorem B945929 : Blo 884570 945929 := bbase (se 2 (by rfl) ⟨354723, by rfl⟩ : syracuseStep 945929 = 709447) (by norm_num)
theorem B9596693 : Blo 884570 9596693 := bbase (se 6 (by rfl) ⟨224922, by rfl⟩ : syracuseStep 9596693 = 449845) (by norm_num)
theorem B1994525 : Blo 884570 1994525 := bbase (se 3 (by rfl) ⟨373973, by rfl⟩ : syracuseStep 1994525 = 747947) (by norm_num)
theorem B3370805 : Blo 884570 3370805 := bbase (se 5 (by rfl) ⟨158006, by rfl⟩ : syracuseStep 3370805 = 316013) (by norm_num)
theorem B1011517 : Blo 884570 1011517 := bbase (se 3 (by rfl) ⟨189659, by rfl⟩ : syracuseStep 1011517 = 379319) (by norm_num)
theorem B1994597 : Blo 884570 1994597 := bbase (se 4 (by rfl) ⟨186993, by rfl⟩ : syracuseStep 1994597 = 373987) (by norm_num)
theorem B1994669 : Blo 884570 1994669 := bbase (se 3 (by rfl) ⟨374000, by rfl⟩ : syracuseStep 1994669 = 748001) (by norm_num)
theorem B2125757 : Blo 884570 2125757 := bbase (se 3 (by rfl) ⟨398579, by rfl⟩ : syracuseStep 2125757 = 797159) (by norm_num)
theorem B946117 : Blo 884570 946117 := bbase (se 4 (by rfl) ⟨88698, by rfl⟩ : syracuseStep 946117 = 177397) (by norm_num)
theorem B2191301 : Blo 884570 2191301 := bbase (se 4 (by rfl) ⟨205434, by rfl⟩ : syracuseStep 2191301 = 410869) (by norm_num)
theorem B1994741 : Blo 884570 1994741 := bbase (se 5 (by rfl) ⟨93503, by rfl⟩ : syracuseStep 1994741 = 187007) (by norm_num)
theorem B6746165 : Blo 884570 6746165 := bbase (se 5 (by rfl) ⟨316226, by rfl⟩ : syracuseStep 6746165 = 632453) (by norm_num)
theorem B1994813 : Blo 884570 1994813 := bbase (se 3 (by rfl) ⟨374027, by rfl⟩ : syracuseStep 1994813 = 748055) (by norm_num)
theorem B1994885 : Blo 884570 1994885 := bbase (se 4 (by rfl) ⟨187020, by rfl⟩ : syracuseStep 1994885 = 374041) (by norm_num)
theorem B5042357 : Blo 884570 5042357 := bbase (se 5 (by rfl) ⟨236360, by rfl⟩ : syracuseStep 5042357 = 472721) (by norm_num)
theorem B1994957 : Blo 884570 1994957 := bbase (se 3 (by rfl) ⟨374054, by rfl⟩ : syracuseStep 1994957 = 748109) (by norm_num)
theorem B1995029 : Blo 884570 1995029 := bbase (se 6 (by rfl) ⟨46758, by rfl⟩ : syracuseStep 1995029 = 93517) (by norm_num)
theorem B2519333 : Blo 884570 2519333 := bbase (se 4 (by rfl) ⟨236187, by rfl⟩ : syracuseStep 2519333 = 472375) (by norm_num)
theorem B5402933 : Blo 884570 5402933 := bbase (se 5 (by rfl) ⟨253262, by rfl⟩ : syracuseStep 5402933 = 506525) (by norm_num)
theorem B2126141 : Blo 884570 2126141 := bbase (se 3 (by rfl) ⟨398651, by rfl⟩ : syracuseStep 2126141 = 797303) (by norm_num)
theorem B1438021 : Blo 884570 1438021 := bbase (se 4 (by rfl) ⟨134814, by rfl⟩ : syracuseStep 1438021 = 269629) (by norm_num)
theorem B1995101 : Blo 884570 1995101 := bbase (se 3 (by rfl) ⟨374081, by rfl⟩ : syracuseStep 1995101 = 748163) (by norm_num)
theorem B1995173 : Blo 884570 1995173 := bbase (se 4 (by rfl) ⟨187047, by rfl⟩ : syracuseStep 1995173 = 374095) (by norm_num)
theorem B1995245 : Blo 884570 1995245 := bbase (se 3 (by rfl) ⟨374108, by rfl⟩ : syracuseStep 1995245 = 748217) (by norm_num)
theorem B1896949 : Blo 884570 1896949 := bbase (se 5 (by rfl) ⟨88919, by rfl⟩ : syracuseStep 1896949 = 177839) (by norm_num)
theorem B2126341 : Blo 884570 2126341 := bbase (se 4 (by rfl) ⟨199344, by rfl⟩ : syracuseStep 2126341 = 398689) (by norm_num)
theorem B1995317 : Blo 884570 1995317 := bbase (se 5 (by rfl) ⟨93530, by rfl⟩ : syracuseStep 1995317 = 187061) (by norm_num)
theorem B1798757 : Blo 884570 1798757 := bbase (se 4 (by rfl) ⟨168633, by rfl⟩ : syracuseStep 1798757 = 337267) (by norm_num)
theorem B1995389 : Blo 884570 1995389 := bbase (se 3 (by rfl) ⟨374135, by rfl⟩ : syracuseStep 1995389 = 748271) (by norm_num)
theorem B1995461 : Blo 884570 1995461 := bbase (se 4 (by rfl) ⟨187074, by rfl⟩ : syracuseStep 1995461 = 374149) (by norm_num)
theorem B946937 : Blo 884570 946937 := bbase (se 2 (by rfl) ⟨355101, by rfl⟩ : syracuseStep 946937 = 710203) (by norm_num)
theorem B1995533 : Blo 884570 1995533 := bbase (se 3 (by rfl) ⟨374162, by rfl⟩ : syracuseStep 1995533 = 748325) (by norm_num)
theorem B4485941 : Blo 884570 4485941 := bbase (se 5 (by rfl) ⟨210278, by rfl⟩ : syracuseStep 4485941 = 420557) (by norm_num)
theorem B1995605 : Blo 884570 1995605 := bbase (se 9 (by rfl) ⟨5846, by rfl⟩ : syracuseStep 1995605 = 11693) (by norm_num)
theorem B3240805 : Blo 884570 3240805 := bbase (se 4 (by rfl) ⟨303825, by rfl⟩ : syracuseStep 3240805 = 607651) (by norm_num)
theorem B1995677 : Blo 884570 1995677 := bbase (se 3 (by rfl) ⟨374189, by rfl⟩ : syracuseStep 1995677 = 748379) (by norm_num)
theorem B6157237 : Blo 884570 6157237 := bbase (se 5 (by rfl) ⟨288620, by rfl⟩ : syracuseStep 6157237 = 577241) (by norm_num)
theorem B3371989 : Blo 884570 3371989 := bbase (se 7 (by rfl) ⟨39515, by rfl⟩ : syracuseStep 3371989 = 79031) (by norm_num)
theorem B1995749 : Blo 884570 1995749 := bbase (se 4 (by rfl) ⟨187101, by rfl⟩ : syracuseStep 1995749 = 374203) (by norm_num)
theorem B1897445 : Blo 884570 1897445 := bbase (se 4 (by rfl) ⟨177885, by rfl⟩ : syracuseStep 1897445 = 355771) (by norm_num)
theorem B2520085 : Blo 884570 2520085 := bbase (se 6 (by rfl) ⟨59064, by rfl⟩ : syracuseStep 2520085 = 118129) (by norm_num)
theorem B1995821 : Blo 884570 1995821 := bbase (se 3 (by rfl) ⟨374216, by rfl⟩ : syracuseStep 1995821 = 748433) (by norm_num)
theorem B1995893 : Blo 884570 1995893 := bbase (se 5 (by rfl) ⟨93557, by rfl⟩ : syracuseStep 1995893 = 187115) (by norm_num)
theorem B1537165 : Blo 884570 1537165 := bbase (se 3 (by rfl) ⟨288218, by rfl⟩ : syracuseStep 1537165 = 576437) (by norm_num)
theorem B947381 : Blo 884570 947381 := bbase (se 5 (by rfl) ⟨44408, by rfl⟩ : syracuseStep 947381 = 88817) (by norm_num)
theorem B1995965 : Blo 884570 1995965 := bbase (se 3 (by rfl) ⟨374243, by rfl⟩ : syracuseStep 1995965 = 748487) (by norm_num)
theorem B1996037 : Blo 884570 1996037 := bbase (se 4 (by rfl) ⟨187128, by rfl⟩ : syracuseStep 1996037 = 374257) (by norm_num)
theorem B3372293 : Blo 884570 3372293 := bbase (se 4 (by rfl) ⟨316152, by rfl⟩ : syracuseStep 3372293 = 632305) (by norm_num)
theorem B1799453 : Blo 884570 1799453 := bbase (se 3 (by rfl) ⟨337397, by rfl⟩ : syracuseStep 1799453 = 674795) (by norm_num)
theorem B1996109 : Blo 884570 1996109 := bbase (se 3 (by rfl) ⟨374270, by rfl⟩ : syracuseStep 1996109 = 748541) (by norm_num)
theorem B1996181 : Blo 884570 1996181 := bbase (se 6 (by rfl) ⟨46785, by rfl⟩ : syracuseStep 1996181 = 93571) (by norm_num)
theorem B947629 : Blo 884570 947629 := bbase (se 3 (by rfl) ⟨177680, by rfl⟩ : syracuseStep 947629 = 355361) (by norm_num)
theorem B1996253 : Blo 884570 1996253 := bbase (se 3 (by rfl) ⟨374297, by rfl⟩ : syracuseStep 1996253 = 748595) (by norm_num)
theorem B1996325 : Blo 884570 1996325 := bbase (se 4 (by rfl) ⟨187155, by rfl⟩ : syracuseStep 1996325 = 374311) (by norm_num)
theorem B1996397 : Blo 884570 1996397 := bbase (se 3 (by rfl) ⟨374324, by rfl⟩ : syracuseStep 1996397 = 748649) (by norm_num)
theorem B1996469 : Blo 884570 1996469 := bbase (se 5 (by rfl) ⟨93584, by rfl⟩ : syracuseStep 1996469 = 187169) (by norm_num)
theorem B1996541 : Blo 884570 1996541 := bbase (se 3 (by rfl) ⟨374351, by rfl⟩ : syracuseStep 1996541 = 748703) (by norm_num)
theorem B1996613 : Blo 884570 1996613 := bbase (se 4 (by rfl) ⟨187182, by rfl⟩ : syracuseStep 1996613 = 374365) (by norm_num)
theorem B948061 : Blo 884570 948061 := bbase (se 3 (by rfl) ⟨177761, by rfl⟩ : syracuseStep 948061 = 355523) (by norm_num)
theorem B1996685 : Blo 884570 1996685 := bbase (se 3 (by rfl) ⟨374378, by rfl⟩ : syracuseStep 1996685 = 748757) (by norm_num)
theorem B948133 : Blo 884570 948133 := bbase (se 4 (by rfl) ⟨88887, by rfl⟩ : syracuseStep 948133 = 177775) (by norm_num)
theorem B1800101 : Blo 884570 1800101 := bbase (se 4 (by rfl) ⟨168759, by rfl⟩ : syracuseStep 1800101 = 337519) (by norm_num)
theorem B2160557 : Blo 884570 2160557 := bbase (se 3 (by rfl) ⟨405104, by rfl⟩ : syracuseStep 2160557 = 810209) (by norm_num)
theorem B1996757 : Blo 884570 1996757 := bbase (se 7 (by rfl) ⟨23399, by rfl⟩ : syracuseStep 1996757 = 46799) (by norm_num)
theorem B1996829 : Blo 884570 1996829 := bbase (se 3 (by rfl) ⟨374405, by rfl⟩ : syracuseStep 1996829 = 748811) (by norm_num)
theorem B2127917 : Blo 884570 2127917 := bbase (se 3 (by rfl) ⟨398984, by rfl⟩ : syracuseStep 2127917 = 797969) (by norm_num)
theorem B4487237 : Blo 884570 4487237 := bbase (se 4 (by rfl) ⟨420678, by rfl⟩ : syracuseStep 4487237 = 841357) (by norm_num)
theorem B1996901 : Blo 884570 1996901 := bbase (se 4 (by rfl) ⟨187209, by rfl⟩ : syracuseStep 1996901 = 374419) (by norm_num)
theorem B1996973 : Blo 884570 1996973 := bbase (se 3 (by rfl) ⟨374432, by rfl⟩ : syracuseStep 1996973 = 748865) (by norm_num)
theorem B1997045 : Blo 884570 1997045 := bbase (se 5 (by rfl) ⟨93611, by rfl⟩ : syracuseStep 1997045 = 187223) (by norm_num)
theorem B948505 : Blo 884570 948505 := bbase (se 2 (by rfl) ⟨355689, by rfl⟩ : syracuseStep 948505 = 711379) (by norm_num)
theorem B1997117 : Blo 884570 1997117 := bbase (se 3 (by rfl) ⟨374459, by rfl⟩ : syracuseStep 1997117 = 748919) (by norm_num)
theorem B1997189 : Blo 884570 1997189 := bbase (se 4 (by rfl) ⟨187236, by rfl⟩ : syracuseStep 1997189 = 374473) (by norm_num)
theorem B1997261 : Blo 884570 1997261 := bbase (se 3 (by rfl) ⟨374486, by rfl⟩ : syracuseStep 1997261 = 748973) (by norm_num)
theorem B1997333 : Blo 884570 1997333 := bbase (se 6 (by rfl) ⟨46812, by rfl⟩ : syracuseStep 1997333 = 93625) (by norm_num)
theorem B1997405 : Blo 884570 1997405 := bbase (se 3 (by rfl) ⟨374513, by rfl⟩ : syracuseStep 1997405 = 749027) (by norm_num)
theorem B1997477 : Blo 884570 1997477 := bbase (se 4 (by rfl) ⟨187263, by rfl⟩ : syracuseStep 1997477 = 374527) (by norm_num)
theorem B1997549 : Blo 884570 1997549 := bbase (se 3 (by rfl) ⟨374540, by rfl⟩ : syracuseStep 1997549 = 749081) (by norm_num)
theorem B1997621 : Blo 884570 1997621 := bbase (se 5 (by rfl) ⟨93638, by rfl⟩ : syracuseStep 1997621 = 187277) (by norm_num)
theorem B1997693 : Blo 884570 1997693 := bbase (se 3 (by rfl) ⟨374567, by rfl⟩ : syracuseStep 1997693 = 749135) (by norm_num)
theorem B1801109 : Blo 884570 1801109 := bbase (se 6 (by rfl) ⟨42213, by rfl⟩ : syracuseStep 1801109 = 84427) (by norm_num)
theorem B4258757 : Blo 884570 4258757 := bbase (se 4 (by rfl) ⟨399258, by rfl⟩ : syracuseStep 4258757 = 798517) (by norm_num)
theorem B1997765 : Blo 884570 1997765 := bbase (se 4 (by rfl) ⟨187290, by rfl⟩ : syracuseStep 1997765 = 374581) (by norm_num)
theorem B1997837 : Blo 884570 1997837 := bbase (se 3 (by rfl) ⟨374594, by rfl⟩ : syracuseStep 1997837 = 749189) (by norm_num)
theorem B1997909 : Blo 884570 1997909 := bbase (se 8 (by rfl) ⟨11706, by rfl⟩ : syracuseStep 1997909 = 23413) (by norm_num)
theorem B1440877 : Blo 884570 1440877 := bbase (se 3 (by rfl) ⟨270164, by rfl⟩ : syracuseStep 1440877 = 540329) (by norm_num)
theorem B1997981 : Blo 884570 1997981 := bbase (se 3 (by rfl) ⟨374621, by rfl⟩ : syracuseStep 1997981 = 749243) (by norm_num)
theorem B1998053 : Blo 884570 1998053 := bbase (se 4 (by rfl) ⟨187317, by rfl⟩ : syracuseStep 1998053 = 374635) (by norm_num)
theorem B1998125 : Blo 884570 1998125 := bbase (se 3 (by rfl) ⟨374648, by rfl⟩ : syracuseStep 1998125 = 749297) (by norm_num)
theorem B4488533 : Blo 884570 4488533 := bbase (se 11 (by rfl) ⟨3287, by rfl⟩ : syracuseStep 4488533 = 6575) (by norm_num)
theorem B1998197 : Blo 884570 1998197 := bbase (se 5 (by rfl) ⟨93665, by rfl⟩ : syracuseStep 1998197 = 187331) (by norm_num)
theorem B2162093 : Blo 884570 2162093 := bbase (se 3 (by rfl) ⟨405392, by rfl⟩ : syracuseStep 2162093 = 810785) (by norm_num)
theorem B2129341 : Blo 884570 2129341 := bbase (se 3 (by rfl) ⟨399251, by rfl⟩ : syracuseStep 2129341 = 798503) (by norm_num)
theorem B1998269 : Blo 884570 1998269 := bbase (se 3 (by rfl) ⟨374675, by rfl⟩ : syracuseStep 1998269 = 749351) (by norm_num)
theorem B1998341 : Blo 884570 1998341 := bbase (se 4 (by rfl) ⟨187344, by rfl⟩ : syracuseStep 1998341 = 374689) (by norm_num)
theorem B1998413 : Blo 884570 1998413 := bbase (se 3 (by rfl) ⟨374702, by rfl⟩ : syracuseStep 1998413 = 749405) (by norm_num)
theorem B1998485 : Blo 884570 1998485 := bbase (se 6 (by rfl) ⟨46839, by rfl⟩ : syracuseStep 1998485 = 93679) (by norm_num)
theorem B1998557 : Blo 884570 1998557 := bbase (se 3 (by rfl) ⟨374729, by rfl⟩ : syracuseStep 1998557 = 749459) (by norm_num)
theorem B1998629 : Blo 884570 1998629 := bbase (se 4 (by rfl) ⟨187371, by rfl⟩ : syracuseStep 1998629 = 374743) (by norm_num)
theorem B2522933 : Blo 884570 2522933 := bbase (se 5 (by rfl) ⟨118262, by rfl⟩ : syracuseStep 2522933 = 236525) (by norm_num)
theorem B1998701 : Blo 884570 1998701 := bbase (se 3 (by rfl) ⟨374756, by rfl⟩ : syracuseStep 1998701 = 749513) (by norm_num)
theorem B1441669 : Blo 884570 1441669 := bbase (se 4 (by rfl) ⟨135156, by rfl⟩ : syracuseStep 1441669 = 270313) (by norm_num)
theorem B1998773 : Blo 884570 1998773 := bbase (se 5 (by rfl) ⟨93692, by rfl⟩ : syracuseStep 1998773 = 187385) (by norm_num)
theorem B20742101 : Blo 884570 20742101 := bbase (se 7 (by rfl) ⟨243071, by rfl⟩ : syracuseStep 20742101 = 486143) (by norm_num)
theorem B1998845 : Blo 884570 1998845 := bbase (se 3 (by rfl) ⟨374783, by rfl⟩ : syracuseStep 1998845 = 749567) (by norm_num)
theorem B884739 : Blo 884570 884739 := bstep (se 1 (by rfl) ⟨663554, by rfl⟩ : syracuseStep 884739 = 1327109) B1327109
theorem B884755 : Blo 884570 884755 := bstep (se 1 (by rfl) ⟨663566, by rfl⟩ : syracuseStep 884755 = 1327133) B1327133
theorem B884771 : Blo 884570 884771 := bstep (se 1 (by rfl) ⟨663578, by rfl⟩ : syracuseStep 884771 = 1327157) B1327157
theorem B3080227 : Blo 884570 3080227 := bstep (se 1 (by rfl) ⟨2310170, by rfl⟩ : syracuseStep 3080227 = 4620341) B4620341
theorem B884787 : Blo 884570 884787 := bstep (se 1 (by rfl) ⟨663590, by rfl⟩ : syracuseStep 884787 = 1327181) B1327181
theorem B884803 : Blo 884570 884803 := bstep (se 1 (by rfl) ⟨663602, by rfl⟩ : syracuseStep 884803 = 1327205) B1327205
theorem B884819 : Blo 884570 884819 := bstep (se 1 (by rfl) ⟨663614, by rfl⟩ : syracuseStep 884819 = 1327229) B1327229
theorem B884835 : Blo 884570 884835 := bstep (se 1 (by rfl) ⟨663626, by rfl⟩ : syracuseStep 884835 = 1327253) B1327253
theorem B884851 : Blo 884570 884851 := bstep (se 1 (by rfl) ⟨663638, by rfl⟩ : syracuseStep 884851 = 1327277) B1327277
theorem B884867 : Blo 884570 884867 := bstep (se 1 (by rfl) ⟨663650, by rfl⟩ : syracuseStep 884867 = 1327301) B1327301
theorem B884883 : Blo 884570 884883 := bstep (se 1 (by rfl) ⟨663662, by rfl⟩ : syracuseStep 884883 = 1327325) B1327325
theorem B884899 : Blo 884570 884899 := bstep (se 1 (by rfl) ⟨663674, by rfl⟩ : syracuseStep 884899 = 1327349) B1327349
theorem B1999025 : Blo 884570 1999025 := bstep (se 2 (by rfl) ⟨749634, by rfl⟩ : syracuseStep 1999025 = 1499269) B1499269
theorem B884915 : Blo 884570 884915 := bstep (se 1 (by rfl) ⟨663686, by rfl⟩ : syracuseStep 884915 = 1327373) B1327373
theorem B884931 : Blo 884570 884931 := bstep (se 1 (by rfl) ⟨663698, by rfl⟩ : syracuseStep 884931 = 1327397) B1327397
theorem B1999043 : Blo 884570 1999043 := bstep (se 1 (by rfl) ⟨1499282, by rfl⟩ : syracuseStep 1999043 = 2998565) B2998565
theorem B884947 : Blo 884570 884947 := bstep (se 1 (by rfl) ⟨663710, by rfl⟩ : syracuseStep 884947 = 1327421) B1327421
theorem B884963 : Blo 884570 884963 := bstep (se 1 (by rfl) ⟨663722, by rfl⟩ : syracuseStep 884963 = 1327445) B1327445
theorem B884979 : Blo 884570 884979 := bstep (se 1 (by rfl) ⟨663734, by rfl⟩ : syracuseStep 884979 = 1327469) B1327469
theorem B884995 : Blo 884570 884995 := bstep (se 1 (by rfl) ⟨663746, by rfl⟩ : syracuseStep 884995 = 1327493) B1327493
theorem B885011 : Blo 884570 885011 := bstep (se 1 (by rfl) ⟨663758, by rfl⟩ : syracuseStep 885011 = 1327517) B1327517
theorem B885027 : Blo 884570 885027 := bstep (se 1 (by rfl) ⟨663770, by rfl⟩ : syracuseStep 885027 = 1327541) B1327541
theorem B885043 : Blo 884570 885043 := bstep (se 1 (by rfl) ⟨663782, by rfl⟩ : syracuseStep 885043 = 1327565) B1327565
theorem B885059 : Blo 884570 885059 := bstep (se 1 (by rfl) ⟨663794, by rfl⟩ : syracuseStep 885059 = 1327589) B1327589
theorem B885075 : Blo 884570 885075 := bstep (se 1 (by rfl) ⟨663806, by rfl⟩ : syracuseStep 885075 = 1327613) B1327613
theorem B885091 : Blo 884570 885091 := bstep (se 1 (by rfl) ⟨663818, by rfl⟩ : syracuseStep 885091 = 1327637) B1327637
theorem B885107 : Blo 884570 885107 := bstep (se 1 (by rfl) ⟨663830, by rfl⟩ : syracuseStep 885107 = 1327661) B1327661
theorem B885123 : Blo 884570 885123 := bstep (se 1 (by rfl) ⟨663842, by rfl⟩ : syracuseStep 885123 = 1327685) B1327685
theorem B885139 : Blo 884570 885139 := bstep (se 1 (by rfl) ⟨663854, by rfl⟩ : syracuseStep 885139 = 1327709) B1327709
theorem B885155 : Blo 884570 885155 := bstep (se 1 (by rfl) ⟨663866, by rfl⟩ : syracuseStep 885155 = 1327733) B1327733
theorem B5669297 : Blo 884570 5669297 := bstep (se 2 (by rfl) ⟨2125986, by rfl⟩ : syracuseStep 5669297 = 4251973) B4251973
theorem B885171 : Blo 884570 885171 := bstep (se 1 (by rfl) ⟨663878, by rfl⟩ : syracuseStep 885171 = 1327757) B1327757
theorem B885187 : Blo 884570 885187 := bstep (se 1 (by rfl) ⟨663890, by rfl⟩ : syracuseStep 885187 = 1327781) B1327781
theorem B885203 : Blo 884570 885203 := bstep (se 1 (by rfl) ⟨663902, by rfl⟩ : syracuseStep 885203 = 1327805) B1327805
theorem B885219 : Blo 884570 885219 := bstep (se 1 (by rfl) ⟨663914, by rfl⟩ : syracuseStep 885219 = 1327829) B1327829
theorem B885235 : Blo 884570 885235 := bstep (se 1 (by rfl) ⟨663926, by rfl⟩ : syracuseStep 885235 = 1327853) B1327853
theorem B885251 : Blo 884570 885251 := bstep (se 1 (by rfl) ⟨663938, by rfl⟩ : syracuseStep 885251 = 1327877) B1327877
theorem B885267 : Blo 884570 885267 := bstep (se 1 (by rfl) ⟨663950, by rfl⟩ : syracuseStep 885267 = 1327901) B1327901
theorem B885283 : Blo 884570 885283 := bstep (se 1 (by rfl) ⟨663962, by rfl⟩ : syracuseStep 885283 = 1327925) B1327925
theorem B885299 : Blo 884570 885299 := bstep (se 1 (by rfl) ⟨663974, by rfl⟩ : syracuseStep 885299 = 1327949) B1327949
theorem B885315 : Blo 884570 885315 := bstep (se 1 (by rfl) ⟨663986, by rfl⟩ : syracuseStep 885315 = 1327973) B1327973
theorem B885331 : Blo 884570 885331 := bstep (se 1 (by rfl) ⟨663998, by rfl⟩ : syracuseStep 885331 = 1327997) B1327997
theorem B885347 : Blo 884570 885347 := bstep (se 1 (by rfl) ⟨664010, by rfl⟩ : syracuseStep 885347 = 1328021) B1328021
theorem B885363 : Blo 884570 885363 := bstep (se 1 (by rfl) ⟨664022, by rfl⟩ : syracuseStep 885363 = 1328045) B1328045
theorem B885379 : Blo 884570 885379 := bstep (se 1 (by rfl) ⟨664034, by rfl⟩ : syracuseStep 885379 = 1328069) B1328069
theorem B885395 : Blo 884570 885395 := bstep (se 1 (by rfl) ⟨664046, by rfl⟩ : syracuseStep 885395 = 1328093) B1328093
theorem B1639075 : Blo 884570 1639075 := bstep (se 1 (by rfl) ⟨1229306, by rfl⟩ : syracuseStep 1639075 = 2458613) B2458613
theorem B885411 : Blo 884570 885411 := bstep (se 1 (by rfl) ⟨664058, by rfl⟩ : syracuseStep 885411 = 1328117) B1328117
theorem B885427 : Blo 884570 885427 := bstep (se 1 (by rfl) ⟨664070, by rfl⟩ : syracuseStep 885427 = 1328141) B1328141
theorem B885443 : Blo 884570 885443 := bstep (se 1 (by rfl) ⟨664082, by rfl⟩ : syracuseStep 885443 = 1328165) B1328165
theorem B885459 : Blo 884570 885459 := bstep (se 1 (by rfl) ⟨664094, by rfl⟩ : syracuseStep 885459 = 1328189) B1328189
theorem B885475 : Blo 884570 885475 := bstep (se 1 (by rfl) ⟨664106, by rfl⟩ : syracuseStep 885475 = 1328213) B1328213
theorem B2523889 : Blo 884570 2523889 := bstep (se 2 (by rfl) ⟨946458, by rfl⟩ : syracuseStep 2523889 = 1892917) B1892917
theorem B885491 : Blo 884570 885491 := bstep (se 1 (by rfl) ⟨664118, by rfl⟩ : syracuseStep 885491 = 1328237) B1328237
theorem B885507 : Blo 884570 885507 := bstep (se 1 (by rfl) ⟨664130, by rfl⟩ : syracuseStep 885507 = 1328261) B1328261
theorem B885523 : Blo 884570 885523 := bstep (se 1 (by rfl) ⟨664142, by rfl⟩ : syracuseStep 885523 = 1328285) B1328285
theorem B2589475 : Blo 884570 2589475 := bstep (se 1 (by rfl) ⟨1942106, by rfl⟩ : syracuseStep 2589475 = 3884213) B3884213
theorem B885539 : Blo 884570 885539 := bstep (se 1 (by rfl) ⟨664154, by rfl⟩ : syracuseStep 885539 = 1328309) B1328309
theorem B885555 : Blo 884570 885555 := bstep (se 1 (by rfl) ⟨664166, by rfl⟩ : syracuseStep 885555 = 1328333) B1328333
theorem B885571 : Blo 884570 885571 := bstep (se 1 (by rfl) ⟨664178, by rfl⟩ : syracuseStep 885571 = 1328357) B1328357
theorem B885587 : Blo 884570 885587 := bstep (se 1 (by rfl) ⟨664190, by rfl⟩ : syracuseStep 885587 = 1328381) B1328381
theorem B885603 : Blo 884570 885603 := bstep (se 1 (by rfl) ⟨664202, by rfl⟩ : syracuseStep 885603 = 1328405) B1328405
theorem B885619 : Blo 884570 885619 := bstep (se 1 (by rfl) ⟨664214, by rfl⟩ : syracuseStep 885619 = 1328429) B1328429
theorem B885635 : Blo 884570 885635 := bstep (se 1 (by rfl) ⟨664226, by rfl⟩ : syracuseStep 885635 = 1328453) B1328453
theorem B885651 : Blo 884570 885651 := bstep (se 1 (by rfl) ⟨664238, by rfl⟩ : syracuseStep 885651 = 1328477) B1328477
theorem B885667 : Blo 884570 885667 := bstep (se 1 (by rfl) ⟨664250, by rfl⟩ : syracuseStep 885667 = 1328501) B1328501
theorem B885683 : Blo 884570 885683 := bstep (se 1 (by rfl) ⟨664262, by rfl⟩ : syracuseStep 885683 = 1328525) B1328525
theorem B885699 : Blo 884570 885699 := bstep (se 1 (by rfl) ⟨664274, by rfl⟩ : syracuseStep 885699 = 1328549) B1328549
theorem B885715 : Blo 884570 885715 := bstep (se 1 (by rfl) ⟨664286, by rfl⟩ : syracuseStep 885715 = 1328573) B1328573
theorem B885731 : Blo 884570 885731 := bstep (se 1 (by rfl) ⟨664298, by rfl⟩ : syracuseStep 885731 = 1328597) B1328597
theorem B885747 : Blo 884570 885747 := bstep (se 1 (by rfl) ⟨664310, by rfl⟩ : syracuseStep 885747 = 1328621) B1328621
theorem B885763 : Blo 884570 885763 := bstep (se 1 (by rfl) ⟨664322, by rfl⟩ : syracuseStep 885763 = 1328645) B1328645
theorem B885779 : Blo 884570 885779 := bstep (se 1 (by rfl) ⟨664334, by rfl⟩ : syracuseStep 885779 = 1328669) B1328669
theorem B885795 : Blo 884570 885795 := bstep (se 1 (by rfl) ⟨664346, by rfl⟩ : syracuseStep 885795 = 1328693) B1328693
theorem B885811 : Blo 884570 885811 := bstep (se 1 (by rfl) ⟨664358, by rfl⟩ : syracuseStep 885811 = 1328717) B1328717
theorem B885827 : Blo 884570 885827 := bstep (se 1 (by rfl) ⟨664370, by rfl⟩ : syracuseStep 885827 = 1328741) B1328741
theorem B885843 : Blo 884570 885843 := bstep (se 1 (by rfl) ⟨664382, by rfl⟩ : syracuseStep 885843 = 1328765) B1328765
theorem B885859 : Blo 884570 885859 := bstep (se 1 (by rfl) ⟨664394, by rfl⟩ : syracuseStep 885859 = 1328789) B1328789
theorem B885875 : Blo 884570 885875 := bstep (se 1 (by rfl) ⟨664406, by rfl⟩ : syracuseStep 885875 = 1328813) B1328813
theorem B885891 : Blo 884570 885891 := bstep (se 1 (by rfl) ⟨664418, by rfl⟩ : syracuseStep 885891 = 1328837) B1328837
theorem B885907 : Blo 884570 885907 := bstep (se 1 (by rfl) ⟨664430, by rfl⟩ : syracuseStep 885907 = 1328861) B1328861
theorem B885923 : Blo 884570 885923 := bstep (se 1 (by rfl) ⟨664442, by rfl⟩ : syracuseStep 885923 = 1328885) B1328885
theorem B885939 : Blo 884570 885939 := bstep (se 1 (by rfl) ⟨664454, by rfl⟩ : syracuseStep 885939 = 1328909) B1328909
theorem B885955 : Blo 884570 885955 := bstep (se 1 (by rfl) ⟨664466, by rfl⟩ : syracuseStep 885955 = 1328933) B1328933
theorem B885971 : Blo 884570 885971 := bstep (se 1 (by rfl) ⟨664478, by rfl⟩ : syracuseStep 885971 = 1328957) B1328957
theorem B5178595 : Blo 884570 5178595 := bstep (se 1 (by rfl) ⟨3883946, by rfl⟩ : syracuseStep 5178595 = 7767893) B7767893
theorem B885987 : Blo 884570 885987 := bstep (se 1 (by rfl) ⟨664490, by rfl⟩ : syracuseStep 885987 = 1328981) B1328981
theorem B886003 : Blo 884570 886003 := bstep (se 1 (by rfl) ⟨664502, by rfl⟩ : syracuseStep 886003 = 1329005) B1329005
theorem B886019 : Blo 884570 886019 := bstep (se 1 (by rfl) ⟨664514, by rfl⟩ : syracuseStep 886019 = 1329029) B1329029
theorem B886035 : Blo 884570 886035 := bstep (se 1 (by rfl) ⟨664526, by rfl⟩ : syracuseStep 886035 = 1329053) B1329053
theorem B886051 : Blo 884570 886051 := bstep (se 1 (by rfl) ⟨664538, by rfl⟩ : syracuseStep 886051 = 1329077) B1329077
theorem B886067 : Blo 884570 886067 := bstep (se 1 (by rfl) ⟨664550, by rfl⟩ : syracuseStep 886067 = 1329101) B1329101
theorem B886083 : Blo 884570 886083 := bstep (se 1 (by rfl) ⟨664562, by rfl⟩ : syracuseStep 886083 = 1329125) B1329125
theorem B886099 : Blo 884570 886099 := bstep (se 1 (by rfl) ⟨664574, by rfl⟩ : syracuseStep 886099 = 1329149) B1329149
theorem B886115 : Blo 884570 886115 := bstep (se 1 (by rfl) ⟨664586, by rfl⟩ : syracuseStep 886115 = 1329173) B1329173
theorem B886131 : Blo 884570 886131 := bstep (se 1 (by rfl) ⟨664598, by rfl⟩ : syracuseStep 886131 = 1329197) B1329197
theorem B886147 : Blo 884570 886147 := bstep (se 1 (by rfl) ⟨664610, by rfl⟩ : syracuseStep 886147 = 1329221) B1329221
theorem B16647565 : Blo 884570 16647565 := bstep (se 3 (by rfl) ⟨3121418, by rfl⟩ : syracuseStep 16647565 = 6242837) B6242837
theorem B886163 : Blo 884570 886163 := bstep (se 1 (by rfl) ⟨664622, by rfl⟩ : syracuseStep 886163 = 1329245) B1329245
theorem B886179 : Blo 884570 886179 := bstep (se 1 (by rfl) ⟨664634, by rfl⟩ : syracuseStep 886179 = 1329269) B1329269
theorem B886195 : Blo 884570 886195 := bstep (se 1 (by rfl) ⟨664646, by rfl⟩ : syracuseStep 886195 = 1329293) B1329293
theorem B886211 : Blo 884570 886211 := bstep (se 1 (by rfl) ⟨664658, by rfl⟩ : syracuseStep 886211 = 1329317) B1329317
theorem B5047757 : Blo 884570 5047757 := bstep (se 3 (by rfl) ⟨946454, by rfl⟩ : syracuseStep 5047757 = 1892909) B1892909
theorem B886227 : Blo 884570 886227 := bstep (se 1 (by rfl) ⟨664670, by rfl⟩ : syracuseStep 886227 = 1329341) B1329341
theorem B886243 : Blo 884570 886243 := bstep (se 1 (by rfl) ⟨664682, by rfl⟩ : syracuseStep 886243 = 1329365) B1329365
theorem B886259 : Blo 884570 886259 := bstep (se 1 (by rfl) ⟨664694, by rfl⟩ : syracuseStep 886259 = 1329389) B1329389
theorem B886275 : Blo 884570 886275 := bstep (se 1 (by rfl) ⟨664706, by rfl⟩ : syracuseStep 886275 = 1329413) B1329413
theorem B1967633 : Blo 884570 1967633 := bstep (se 2 (by rfl) ⟨737862, by rfl⟩ : syracuseStep 1967633 = 1475725) B1475725
theorem B886291 : Blo 884570 886291 := bstep (se 1 (by rfl) ⟨664718, by rfl⟩ : syracuseStep 886291 = 1329437) B1329437
theorem B886307 : Blo 884570 886307 := bstep (se 1 (by rfl) ⟨664730, by rfl⟩ : syracuseStep 886307 = 1329461) B1329461
theorem B4490801 : Blo 884570 4490801 := bstep (se 2 (by rfl) ⟨1684050, by rfl⟩ : syracuseStep 4490801 = 3368101) B3368101
theorem B886323 : Blo 884570 886323 := bstep (se 1 (by rfl) ⟨664742, by rfl⟩ : syracuseStep 886323 = 1329485) B1329485
theorem B886339 : Blo 884570 886339 := bstep (se 1 (by rfl) ⟨664754, by rfl⟩ : syracuseStep 886339 = 1329509) B1329509
theorem B886355 : Blo 884570 886355 := bstep (se 1 (by rfl) ⟨664766, by rfl⟩ : syracuseStep 886355 = 1329533) B1329533
theorem B886371 : Blo 884570 886371 := bstep (se 1 (by rfl) ⟨664778, by rfl⟩ : syracuseStep 886371 = 1329557) B1329557
theorem B886387 : Blo 884570 886387 := bstep (se 1 (by rfl) ⟨664790, by rfl⟩ : syracuseStep 886387 = 1329581) B1329581
theorem B886403 : Blo 884570 886403 := bstep (se 1 (by rfl) ⟨664802, by rfl⟩ : syracuseStep 886403 = 1329605) B1329605
theorem B886419 : Blo 884570 886419 := bstep (se 1 (by rfl) ⟨664814, by rfl⟩ : syracuseStep 886419 = 1329629) B1329629
theorem B886435 : Blo 884570 886435 := bstep (se 1 (by rfl) ⟨664826, by rfl⟩ : syracuseStep 886435 = 1329653) B1329653
theorem B886451 : Blo 884570 886451 := bstep (se 1 (by rfl) ⟨664838, by rfl⟩ : syracuseStep 886451 = 1329677) B1329677
theorem B886467 : Blo 884570 886467 := bstep (se 1 (by rfl) ⟨664850, by rfl⟩ : syracuseStep 886467 = 1329701) B1329701
theorem B886483 : Blo 884570 886483 := bstep (se 1 (by rfl) ⟨664862, by rfl⟩ : syracuseStep 886483 = 1329725) B1329725
theorem B886499 : Blo 884570 886499 := bstep (se 1 (by rfl) ⟨664874, by rfl⟩ : syracuseStep 886499 = 1329749) B1329749
theorem B886515 : Blo 884570 886515 := bstep (se 1 (by rfl) ⟨664886, by rfl⟩ : syracuseStep 886515 = 1329773) B1329773
theorem B886531 : Blo 884570 886531 := bstep (se 1 (by rfl) ⟨664898, by rfl⟩ : syracuseStep 886531 = 1329797) B1329797
theorem B886547 : Blo 884570 886547 := bstep (se 1 (by rfl) ⟨664910, by rfl⟩ : syracuseStep 886547 = 1329821) B1329821
theorem B886563 : Blo 884570 886563 := bstep (se 1 (by rfl) ⟨664922, by rfl⟩ : syracuseStep 886563 = 1329845) B1329845
theorem B886579 : Blo 884570 886579 := bstep (se 1 (by rfl) ⟨664934, by rfl⟩ : syracuseStep 886579 = 1329869) B1329869
theorem B886595 : Blo 884570 886595 := bstep (se 1 (by rfl) ⟨664946, by rfl⟩ : syracuseStep 886595 = 1329893) B1329893
theorem B886611 : Blo 884570 886611 := bstep (se 1 (by rfl) ⟨664958, by rfl⟩ : syracuseStep 886611 = 1329917) B1329917
theorem B5670755 : Blo 884570 5670755 := bstep (se 1 (by rfl) ⟨4253066, by rfl⟩ : syracuseStep 5670755 = 8506133) B8506133
theorem B886627 : Blo 884570 886627 := bstep (se 1 (by rfl) ⟨664970, by rfl⟩ : syracuseStep 886627 = 1329941) B1329941
theorem B886643 : Blo 884570 886643 := bstep (se 1 (by rfl) ⟨664982, by rfl⟩ : syracuseStep 886643 = 1329965) B1329965
theorem B886659 : Blo 884570 886659 := bstep (se 1 (by rfl) ⟨664994, by rfl⟩ : syracuseStep 886659 = 1329989) B1329989
theorem B886675 : Blo 884570 886675 := bstep (se 1 (by rfl) ⟨665006, by rfl⟩ : syracuseStep 886675 = 1330013) B1330013
theorem B886691 : Blo 884570 886691 := bstep (se 1 (by rfl) ⟨665018, by rfl⟩ : syracuseStep 886691 = 1330037) B1330037
theorem B886707 : Blo 884570 886707 := bstep (se 1 (by rfl) ⟨665030, by rfl⟩ : syracuseStep 886707 = 1330061) B1330061
theorem B9734069 : Blo 884570 9734069 := bstep (se 5 (by rfl) ⟨456284, by rfl⟩ : syracuseStep 9734069 = 912569) B912569
theorem B886723 : Blo 884570 886723 := bstep (se 1 (by rfl) ⟨665042, by rfl⟩ : syracuseStep 886723 = 1330085) B1330085
theorem B886739 : Blo 884570 886739 := bstep (se 1 (by rfl) ⟨665054, by rfl⟩ : syracuseStep 886739 = 1330109) B1330109
theorem B886755 : Blo 884570 886755 := bstep (se 1 (by rfl) ⟨665066, by rfl⟩ : syracuseStep 886755 = 1330133) B1330133
theorem B2525165 : Blo 884570 2525165 := bstep (se 3 (by rfl) ⟨473468, by rfl⟩ : syracuseStep 2525165 = 946937) B946937
theorem B886771 : Blo 884570 886771 := bstep (se 1 (by rfl) ⟨665078, by rfl⟩ : syracuseStep 886771 = 1330157) B1330157
theorem B886787 : Blo 884570 886787 := bstep (se 1 (by rfl) ⟨665090, by rfl⟩ : syracuseStep 886787 = 1330181) B1330181
theorem B886803 : Blo 884570 886803 := bstep (se 1 (by rfl) ⟨665102, by rfl⟩ : syracuseStep 886803 = 1330205) B1330205
theorem B886819 : Blo 884570 886819 := bstep (se 1 (by rfl) ⟨665114, by rfl⟩ : syracuseStep 886819 = 1330229) B1330229
theorem B886835 : Blo 884570 886835 := bstep (se 1 (by rfl) ⟨665126, by rfl⟩ : syracuseStep 886835 = 1330253) B1330253
theorem B886851 : Blo 884570 886851 := bstep (se 1 (by rfl) ⟨665138, by rfl⟩ : syracuseStep 886851 = 1330277) B1330277
theorem B886867 : Blo 884570 886867 := bstep (se 1 (by rfl) ⟨665150, by rfl⟩ : syracuseStep 886867 = 1330301) B1330301
theorem B2394211 : Blo 884570 2394211 := bstep (se 1 (by rfl) ⟨1795658, by rfl⟩ : syracuseStep 2394211 = 3591317) B3591317
theorem B886883 : Blo 884570 886883 := bstep (se 1 (by rfl) ⟨665162, by rfl⟩ : syracuseStep 886883 = 1330325) B1330325
theorem B886899 : Blo 884570 886899 := bstep (se 1 (by rfl) ⟨665174, by rfl⟩ : syracuseStep 886899 = 1330349) B1330349
theorem B886915 : Blo 884570 886915 := bstep (se 1 (by rfl) ⟨665186, by rfl⟩ : syracuseStep 886915 = 1330373) B1330373
theorem B886931 : Blo 884570 886931 := bstep (se 1 (by rfl) ⟨665198, by rfl⟩ : syracuseStep 886931 = 1330397) B1330397
theorem B2525347 : Blo 884570 2525347 := bstep (se 1 (by rfl) ⟨1894010, by rfl⟩ : syracuseStep 2525347 = 3788021) B3788021
theorem B886947 : Blo 884570 886947 := bstep (se 1 (by rfl) ⟨665210, by rfl⟩ : syracuseStep 886947 = 1330421) B1330421
theorem B886963 : Blo 884570 886963 := bstep (se 1 (by rfl) ⟨665222, by rfl⟩ : syracuseStep 886963 = 1330445) B1330445
theorem B886979 : Blo 884570 886979 := bstep (se 1 (by rfl) ⟨665234, by rfl⟩ : syracuseStep 886979 = 1330469) B1330469
theorem B2525393 : Blo 884570 2525393 := bstep (se 2 (by rfl) ⟨947022, by rfl⟩ : syracuseStep 2525393 = 1894045) B1894045
theorem B886995 : Blo 884570 886995 := bstep (se 1 (by rfl) ⟨665246, by rfl⟩ : syracuseStep 886995 = 1330493) B1330493
theorem B887011 : Blo 884570 887011 := bstep (se 1 (by rfl) ⟨665258, by rfl⟩ : syracuseStep 887011 = 1330517) B1330517
theorem B887027 : Blo 884570 887027 := bstep (se 1 (by rfl) ⟨665270, by rfl⟩ : syracuseStep 887027 = 1330541) B1330541
theorem B887043 : Blo 884570 887043 := bstep (se 1 (by rfl) ⟨665282, by rfl⟩ : syracuseStep 887043 = 1330565) B1330565
theorem B887059 : Blo 884570 887059 := bstep (se 1 (by rfl) ⟨665294, by rfl⟩ : syracuseStep 887059 = 1330589) B1330589
theorem B4262179 : Blo 884570 4262179 := bstep (se 1 (by rfl) ⟨3196634, by rfl⟩ : syracuseStep 4262179 = 6393269) B6393269
theorem B887075 : Blo 884570 887075 := bstep (se 1 (by rfl) ⟨665306, by rfl⟩ : syracuseStep 887075 = 1330613) B1330613
theorem B887091 : Blo 884570 887091 := bstep (se 1 (by rfl) ⟨665318, by rfl⟩ : syracuseStep 887091 = 1330637) B1330637
theorem B887107 : Blo 884570 887107 := bstep (se 1 (by rfl) ⟨665330, by rfl⟩ : syracuseStep 887107 = 1330661) B1330661
theorem B2132291 : Blo 884570 2132291 := bstep (se 1 (by rfl) ⟨1599218, by rfl⟩ : syracuseStep 2132291 = 3198437) B3198437
theorem B887123 : Blo 884570 887123 := bstep (se 1 (by rfl) ⟨665342, by rfl⟩ : syracuseStep 887123 = 1330685) B1330685
theorem B887139 : Blo 884570 887139 := bstep (se 1 (by rfl) ⟨665354, by rfl⟩ : syracuseStep 887139 = 1330709) B1330709
theorem B5048689 : Blo 884570 5048689 := bstep (se 2 (by rfl) ⟨1893258, by rfl⟩ : syracuseStep 5048689 = 3786517) B3786517
theorem B887155 : Blo 884570 887155 := bstep (se 1 (by rfl) ⟨665366, by rfl⟩ : syracuseStep 887155 = 1330733) B1330733
theorem B887171 : Blo 884570 887171 := bstep (se 1 (by rfl) ⟨665378, by rfl⟩ : syracuseStep 887171 = 1330757) B1330757
theorem B887187 : Blo 884570 887187 := bstep (se 1 (by rfl) ⟨665390, by rfl⟩ : syracuseStep 887187 = 1330781) B1330781
theorem B887203 : Blo 884570 887203 := bstep (se 1 (by rfl) ⟨665402, by rfl⟩ : syracuseStep 887203 = 1330805) B1330805
theorem B887219 : Blo 884570 887219 := bstep (se 1 (by rfl) ⟨665414, by rfl⟩ : syracuseStep 887219 = 1330829) B1330829
theorem B887235 : Blo 884570 887235 := bstep (se 1 (by rfl) ⟨665426, by rfl⟩ : syracuseStep 887235 = 1330853) B1330853
theorem B887251 : Blo 884570 887251 := bstep (se 1 (by rfl) ⟨665438, by rfl⟩ : syracuseStep 887251 = 1330877) B1330877
theorem B887267 : Blo 884570 887267 := bstep (se 1 (by rfl) ⟨665450, by rfl⟩ : syracuseStep 887267 = 1330901) B1330901
theorem B887283 : Blo 884570 887283 := bstep (se 1 (by rfl) ⟨665462, by rfl⟩ : syracuseStep 887283 = 1330925) B1330925
theorem B887299 : Blo 884570 887299 := bstep (se 1 (by rfl) ⟨665474, by rfl⟩ : syracuseStep 887299 = 1330949) B1330949
theorem B887315 : Blo 884570 887315 := bstep (se 1 (by rfl) ⟨665486, by rfl⟩ : syracuseStep 887315 = 1330973) B1330973
theorem B887331 : Blo 884570 887331 := bstep (se 1 (by rfl) ⟨665498, by rfl⟩ : syracuseStep 887331 = 1330997) B1330997
theorem B887347 : Blo 884570 887347 := bstep (se 1 (by rfl) ⟨665510, by rfl⟩ : syracuseStep 887347 = 1331021) B1331021
theorem B887363 : Blo 884570 887363 := bstep (se 1 (by rfl) ⟨665522, by rfl⟩ : syracuseStep 887363 = 1331045) B1331045
theorem B887379 : Blo 884570 887379 := bstep (se 1 (by rfl) ⟨665534, by rfl⟩ : syracuseStep 887379 = 1331069) B1331069
theorem B887395 : Blo 884570 887395 := bstep (se 1 (by rfl) ⟨665546, by rfl⟩ : syracuseStep 887395 = 1331093) B1331093
theorem B887411 : Blo 884570 887411 := bstep (se 1 (by rfl) ⟨665558, by rfl⟩ : syracuseStep 887411 = 1331117) B1331117
theorem B887427 : Blo 884570 887427 := bstep (se 1 (by rfl) ⟨665570, by rfl⟩ : syracuseStep 887427 = 1331141) B1331141
theorem B887443 : Blo 884570 887443 := bstep (se 1 (by rfl) ⟨665582, by rfl⟩ : syracuseStep 887443 = 1331165) B1331165
theorem B887459 : Blo 884570 887459 := bstep (se 1 (by rfl) ⟨665594, by rfl⟩ : syracuseStep 887459 = 1331189) B1331189
theorem B887475 : Blo 884570 887475 := bstep (se 1 (by rfl) ⟨665606, by rfl⟩ : syracuseStep 887475 = 1331213) B1331213
theorem B887491 : Blo 884570 887491 := bstep (se 1 (by rfl) ⟨665618, by rfl⟩ : syracuseStep 887491 = 1331237) B1331237
theorem B11340485 : Blo 884570 11340485 := bstep (se 4 (by rfl) ⟨1063170, by rfl⟩ : syracuseStep 11340485 = 2126341) B2126341
theorem B887507 : Blo 884570 887507 := bstep (se 1 (by rfl) ⟨665630, by rfl⟩ : syracuseStep 887507 = 1331261) B1331261
theorem B887523 : Blo 884570 887523 := bstep (se 1 (by rfl) ⟨665642, by rfl⟩ : syracuseStep 887523 = 1331285) B1331285
theorem B887539 : Blo 884570 887539 := bstep (se 1 (by rfl) ⟨665654, by rfl⟩ : syracuseStep 887539 = 1331309) B1331309
theorem B887555 : Blo 884570 887555 := bstep (se 1 (by rfl) ⟨665666, by rfl⟩ : syracuseStep 887555 = 1331333) B1331333
theorem B887571 : Blo 884570 887571 := bstep (se 1 (by rfl) ⟨665678, by rfl⟩ : syracuseStep 887571 = 1331357) B1331357
theorem B887587 : Blo 884570 887587 := bstep (se 1 (by rfl) ⟨665690, by rfl⟩ : syracuseStep 887587 = 1331381) B1331381
theorem B887603 : Blo 884570 887603 := bstep (se 1 (by rfl) ⟨665702, by rfl⟩ : syracuseStep 887603 = 1331405) B1331405
theorem B887619 : Blo 884570 887619 := bstep (se 1 (by rfl) ⟨665714, by rfl⟩ : syracuseStep 887619 = 1331429) B1331429
theorem B887635 : Blo 884570 887635 := bstep (se 1 (by rfl) ⟨665726, by rfl⟩ : syracuseStep 887635 = 1331453) B1331453
theorem B887651 : Blo 884570 887651 := bstep (se 1 (by rfl) ⟨665738, by rfl⟩ : syracuseStep 887651 = 1331477) B1331477
theorem B887667 : Blo 884570 887667 := bstep (se 1 (by rfl) ⟨665750, by rfl⟩ : syracuseStep 887667 = 1331501) B1331501
theorem B887683 : Blo 884570 887683 := bstep (se 1 (by rfl) ⟨665762, by rfl⟩ : syracuseStep 887683 = 1331525) B1331525
theorem B887699 : Blo 884570 887699 := bstep (se 1 (by rfl) ⟨665774, by rfl⟩ : syracuseStep 887699 = 1331549) B1331549
theorem B887715 : Blo 884570 887715 := bstep (se 1 (by rfl) ⟨665786, by rfl⟩ : syracuseStep 887715 = 1331573) B1331573
theorem B887731 : Blo 884570 887731 := bstep (se 1 (by rfl) ⟨665798, by rfl⟩ : syracuseStep 887731 = 1331597) B1331597
theorem B11373493 : Blo 884570 11373493 := bstep (se 5 (by rfl) ⟨533132, by rfl⟩ : syracuseStep 11373493 = 1066265) B1066265
theorem B887747 : Blo 884570 887747 := bstep (se 1 (by rfl) ⟨665810, by rfl⟩ : syracuseStep 887747 = 1331621) B1331621
theorem B887763 : Blo 884570 887763 := bstep (se 1 (by rfl) ⟨665822, by rfl⟩ : syracuseStep 887763 = 1331645) B1331645
theorem B4492259 : Blo 884570 4492259 := bstep (se 1 (by rfl) ⟨3369194, by rfl⟩ : syracuseStep 4492259 = 6738389) B6738389
theorem B887779 : Blo 884570 887779 := bstep (se 1 (by rfl) ⟨665834, by rfl⟩ : syracuseStep 887779 = 1331669) B1331669
theorem B887795 : Blo 884570 887795 := bstep (se 1 (by rfl) ⟨665846, by rfl⟩ : syracuseStep 887795 = 1331693) B1331693
theorem B887811 : Blo 884570 887811 := bstep (se 1 (by rfl) ⟨665858, by rfl⟩ : syracuseStep 887811 = 1331717) B1331717
theorem B887827 : Blo 884570 887827 := bstep (se 1 (by rfl) ⟨665870, by rfl⟩ : syracuseStep 887827 = 1331741) B1331741
theorem B887843 : Blo 884570 887843 := bstep (se 1 (by rfl) ⟨665882, by rfl⟩ : syracuseStep 887843 = 1331765) B1331765
theorem B887859 : Blo 884570 887859 := bstep (se 1 (by rfl) ⟨665894, by rfl⟩ : syracuseStep 887859 = 1331789) B1331789
theorem B887875 : Blo 884570 887875 := bstep (se 1 (by rfl) ⟨665906, by rfl⟩ : syracuseStep 887875 = 1331813) B1331813
theorem B887891 : Blo 884570 887891 := bstep (se 1 (by rfl) ⟨665918, by rfl⟩ : syracuseStep 887891 = 1331837) B1331837
theorem B887907 : Blo 884570 887907 := bstep (se 1 (by rfl) ⟨665930, by rfl⟩ : syracuseStep 887907 = 1331861) B1331861
theorem B887923 : Blo 884570 887923 := bstep (se 1 (by rfl) ⟨665942, by rfl⟩ : syracuseStep 887923 = 1331885) B1331885
theorem B887939 : Blo 884570 887939 := bstep (se 1 (by rfl) ⟨665954, by rfl⟩ : syracuseStep 887939 = 1331909) B1331909
theorem B887955 : Blo 884570 887955 := bstep (se 1 (by rfl) ⟨665966, by rfl⟩ : syracuseStep 887955 = 1331933) B1331933
theorem B887971 : Blo 884570 887971 := bstep (se 1 (by rfl) ⟨665978, by rfl⟩ : syracuseStep 887971 = 1331957) B1331957
theorem B887987 : Blo 884570 887987 := bstep (se 1 (by rfl) ⟨665990, by rfl⟩ : syracuseStep 887987 = 1331981) B1331981
theorem B888003 : Blo 884570 888003 := bstep (se 1 (by rfl) ⟨666002, by rfl⟩ : syracuseStep 888003 = 1332005) B1332005
theorem B888019 : Blo 884570 888019 := bstep (se 1 (by rfl) ⟨666014, by rfl⟩ : syracuseStep 888019 = 1332029) B1332029
theorem B888035 : Blo 884570 888035 := bstep (se 1 (by rfl) ⟨666026, by rfl⟩ : syracuseStep 888035 = 1332053) B1332053
theorem B888051 : Blo 884570 888051 := bstep (se 1 (by rfl) ⟨666038, by rfl⟩ : syracuseStep 888051 = 1332077) B1332077
theorem B888067 : Blo 884570 888067 := bstep (se 1 (by rfl) ⟨666050, by rfl⟩ : syracuseStep 888067 = 1332101) B1332101
theorem B888083 : Blo 884570 888083 := bstep (se 1 (by rfl) ⟨666062, by rfl⟩ : syracuseStep 888083 = 1332125) B1332125
theorem B888099 : Blo 884570 888099 := bstep (se 1 (by rfl) ⟨666074, by rfl⟩ : syracuseStep 888099 = 1332149) B1332149
theorem B888115 : Blo 884570 888115 := bstep (se 1 (by rfl) ⟨666086, by rfl⟩ : syracuseStep 888115 = 1332173) B1332173
theorem B888131 : Blo 884570 888131 := bstep (se 1 (by rfl) ⟨666098, by rfl⟩ : syracuseStep 888131 = 1332197) B1332197
theorem B888147 : Blo 884570 888147 := bstep (se 1 (by rfl) ⟨666110, by rfl⟩ : syracuseStep 888147 = 1332221) B1332221
theorem B888163 : Blo 884570 888163 := bstep (se 1 (by rfl) ⟨666122, by rfl⟩ : syracuseStep 888163 = 1332245) B1332245
theorem B888179 : Blo 884570 888179 := bstep (se 1 (by rfl) ⟨666134, by rfl⟩ : syracuseStep 888179 = 1332269) B1332269
theorem B888195 : Blo 884570 888195 := bstep (se 1 (by rfl) ⟨666146, by rfl⟩ : syracuseStep 888195 = 1332293) B1332293
theorem B888211 : Blo 884570 888211 := bstep (se 1 (by rfl) ⟨666158, by rfl⟩ : syracuseStep 888211 = 1332317) B1332317
theorem B888227 : Blo 884570 888227 := bstep (se 1 (by rfl) ⟨666170, by rfl⟩ : syracuseStep 888227 = 1332341) B1332341
theorem B888243 : Blo 884570 888243 := bstep (se 1 (by rfl) ⟨666182, by rfl⟩ : syracuseStep 888243 = 1332365) B1332365
theorem B888259 : Blo 884570 888259 := bstep (se 1 (by rfl) ⟨666194, by rfl⟩ : syracuseStep 888259 = 1332389) B1332389
theorem B888275 : Blo 884570 888275 := bstep (se 1 (by rfl) ⟨666206, by rfl⟩ : syracuseStep 888275 = 1332413) B1332413
theorem B2985443 : Blo 884570 2985443 := bstep (se 1 (by rfl) ⟨2239082, by rfl⟩ : syracuseStep 2985443 = 4478165) B4478165
theorem B888291 : Blo 884570 888291 := bstep (se 1 (by rfl) ⟨666218, by rfl⟩ : syracuseStep 888291 = 1332437) B1332437
theorem B888307 : Blo 884570 888307 := bstep (se 1 (by rfl) ⟨666230, by rfl⟩ : syracuseStep 888307 = 1332461) B1332461
theorem B888323 : Blo 884570 888323 := bstep (se 1 (by rfl) ⟨666242, by rfl⟩ : syracuseStep 888323 = 1332485) B1332485
theorem B888339 : Blo 884570 888339 := bstep (se 1 (by rfl) ⟨666254, by rfl⟩ : syracuseStep 888339 = 1332509) B1332509
theorem B888355 : Blo 884570 888355 := bstep (se 1 (by rfl) ⟨666266, by rfl⟩ : syracuseStep 888355 = 1332533) B1332533
theorem B1347121 : Blo 884570 1347121 := bstep (se 2 (by rfl) ⟨505170, by rfl⟩ : syracuseStep 1347121 = 1010341) B1010341
theorem B888371 : Blo 884570 888371 := bstep (se 1 (by rfl) ⟨666278, by rfl⟩ : syracuseStep 888371 = 1332557) B1332557
theorem B888387 : Blo 884570 888387 := bstep (se 1 (by rfl) ⟨666290, by rfl⟩ : syracuseStep 888387 = 1332581) B1332581
theorem B888403 : Blo 884570 888403 := bstep (se 1 (by rfl) ⟨666302, by rfl⟩ : syracuseStep 888403 = 1332605) B1332605
theorem B888419 : Blo 884570 888419 := bstep (se 1 (by rfl) ⟨666314, by rfl⟩ : syracuseStep 888419 = 1332629) B1332629
theorem B888435 : Blo 884570 888435 := bstep (se 1 (by rfl) ⟨666326, by rfl⟩ : syracuseStep 888435 = 1332653) B1332653
theorem B2526851 : Blo 884570 2526851 := bstep (se 1 (by rfl) ⟨1895138, by rfl⟩ : syracuseStep 2526851 = 3790277) B3790277
theorem B888451 : Blo 884570 888451 := bstep (se 1 (by rfl) ⟨666338, by rfl⟩ : syracuseStep 888451 = 1332677) B1332677
theorem B888467 : Blo 884570 888467 := bstep (se 1 (by rfl) ⟨666350, by rfl⟩ : syracuseStep 888467 = 1332701) B1332701
theorem B888483 : Blo 884570 888483 := bstep (se 1 (by rfl) ⟨666362, by rfl⟩ : syracuseStep 888483 = 1332725) B1332725
theorem B888499 : Blo 884570 888499 := bstep (se 1 (by rfl) ⟨666374, by rfl⟩ : syracuseStep 888499 = 1332749) B1332749
theorem B888515 : Blo 884570 888515 := bstep (se 1 (by rfl) ⟨666386, by rfl⟩ : syracuseStep 888515 = 1332773) B1332773
theorem B888531 : Blo 884570 888531 := bstep (se 1 (by rfl) ⟨666398, by rfl⟩ : syracuseStep 888531 = 1332797) B1332797
theorem B888547 : Blo 884570 888547 := bstep (se 1 (by rfl) ⟨666410, by rfl⟩ : syracuseStep 888547 = 1332821) B1332821
theorem B2985713 : Blo 884570 2985713 := bstep (se 2 (by rfl) ⟨1119642, by rfl⟩ : syracuseStep 2985713 = 2239285) B2239285
theorem B2395889 : Blo 884570 2395889 := bstep (se 2 (by rfl) ⟨898458, by rfl⟩ : syracuseStep 2395889 = 1796917) B1796917
theorem B888563 : Blo 884570 888563 := bstep (se 1 (by rfl) ⟨666422, by rfl⟩ : syracuseStep 888563 = 1332845) B1332845
theorem B4493069 : Blo 884570 4493069 := bstep (se 3 (by rfl) ⟨842450, by rfl⟩ : syracuseStep 4493069 = 1684901) B1684901
theorem B5050147 : Blo 884570 5050147 := bstep (se 1 (by rfl) ⟨3787610, by rfl⟩ : syracuseStep 5050147 = 7575221) B7575221
theorem B6721379 : Blo 884570 6721379 := bstep (se 1 (by rfl) ⟨5041034, by rfl⟩ : syracuseStep 6721379 = 10082069) B10082069
theorem B1707907 : Blo 884570 1707907 := bstep (se 1 (by rfl) ⟨1280930, by rfl⟩ : syracuseStep 1707907 = 2561861) B2561861
theorem B7573445 : Blo 884570 7573445 := bstep (se 4 (by rfl) ⟨710010, by rfl⟩ : syracuseStep 7573445 = 1420021) B1420021
theorem B2560081 : Blo 884570 2560081 := bstep (se 2 (by rfl) ⟨960030, by rfl⟩ : syracuseStep 2560081 = 1920061) B1920061
theorem B2986253 : Blo 884570 2986253 := bstep (se 3 (by rfl) ⟨559922, by rfl⟩ : syracuseStep 2986253 = 1119845) B1119845
theorem B5050673 : Blo 884570 5050673 := bstep (se 2 (by rfl) ⟨1894002, by rfl⟩ : syracuseStep 5050673 = 3788005) B3788005
theorem B2986307 : Blo 884570 2986307 := bstep (se 1 (by rfl) ⟨2239730, by rfl⟩ : syracuseStep 2986307 = 4479461) B4479461
theorem B2396675 : Blo 884570 2396675 := bstep (se 1 (by rfl) ⟨1797506, by rfl⟩ : syracuseStep 2396675 = 3595013) B3595013
theorem B2986577 : Blo 884570 2986577 := bstep (se 2 (by rfl) ⟨1119966, by rfl⟩ : syracuseStep 2986577 = 2239933) B2239933
theorem B7180913 : Blo 884570 7180913 := bstep (se 2 (by rfl) ⟨2692842, by rfl⟩ : syracuseStep 7180913 = 5385685) B5385685
theorem B2396785 : Blo 884570 2396785 := bstep (se 2 (by rfl) ⟨898794, by rfl⟩ : syracuseStep 2396785 = 1797589) B1797589
theorem B4264753 : Blo 884570 4264753 := bstep (se 2 (by rfl) ⟨1599282, by rfl⟩ : syracuseStep 4264753 = 3198565) B3198565
theorem B2528081 : Blo 884570 2528081 := bstep (se 2 (by rfl) ⟨948030, by rfl⟩ : syracuseStep 2528081 = 1896061) B1896061
theorem B2987117 : Blo 884570 2987117 := bstep (se 3 (by rfl) ⟨560084, by rfl⟩ : syracuseStep 2987117 = 1120169) B1120169
theorem B2987171 : Blo 884570 2987171 := bstep (se 1 (by rfl) ⟨2240378, by rfl⟩ : syracuseStep 2987171 = 4480757) B4480757
theorem B2987441 : Blo 884570 2987441 := bstep (se 2 (by rfl) ⟨1120290, by rfl⟩ : syracuseStep 2987441 = 2240581) B2240581
theorem B1119683 : Blo 884570 1119683 := bstep (se 1 (by rfl) ⟨839762, by rfl⟩ : syracuseStep 1119683 = 1679525) B1679525
theorem B5674445 : Blo 884570 5674445 := bstep (se 3 (by rfl) ⟨1063958, by rfl⟩ : syracuseStep 5674445 = 2127917) B2127917
theorem B2692685 : Blo 884570 2692685 := bstep (se 3 (by rfl) ⟨504878, by rfl⟩ : syracuseStep 2692685 = 1009757) B1009757
theorem B5052131 : Blo 884570 5052131 := bstep (se 1 (by rfl) ⟨3789098, by rfl⟩ : syracuseStep 5052131 = 7578197) B7578197
theorem B5183281 : Blo 884570 5183281 := bstep (se 2 (by rfl) ⟨1943730, by rfl⟩ : syracuseStep 5183281 = 3887461) B3887461
theorem B2987981 : Blo 884570 2987981 := bstep (se 3 (by rfl) ⟨560246, by rfl⟩ : syracuseStep 2987981 = 1120493) B1120493
theorem B2988035 : Blo 884570 2988035 := bstep (se 1 (by rfl) ⟨2241026, by rfl⟩ : syracuseStep 2988035 = 4482053) B4482053
theorem B1349651 : Blo 884570 1349651 := bstep (se 1 (by rfl) ⟨1012238, by rfl⟩ : syracuseStep 1349651 = 2024477) B2024477
theorem B8198213 : Blo 884570 8198213 := bstep (se 4 (by rfl) ⟨768582, by rfl⟩ : syracuseStep 8198213 = 1537165) B1537165
theorem B1120387 : Blo 884570 1120387 := bstep (se 1 (by rfl) ⟨840290, by rfl⟩ : syracuseStep 1120387 = 1680581) B1680581
theorem B1120483 : Blo 884570 1120483 := bstep (se 1 (by rfl) ⟨840362, by rfl⟩ : syracuseStep 1120483 = 1680725) B1680725
theorem B2529539 : Blo 884570 2529539 := bstep (se 1 (by rfl) ⟨1897154, by rfl⟩ : syracuseStep 2529539 = 3794309) B3794309
theorem B2988305 : Blo 884570 2988305 := bstep (se 2 (by rfl) ⟨1120614, by rfl⟩ : syracuseStep 2988305 = 2241229) B2241229
theorem B4266445 : Blo 884570 4266445 := bstep (se 3 (by rfl) ⟨799958, by rfl⟩ : syracuseStep 4266445 = 1599917) B1599917
theorem B4790755 : Blo 884570 4790755 := bstep (se 1 (by rfl) ⟨3593066, by rfl⟩ : syracuseStep 4790755 = 7186133) B7186133
theorem B4495985 : Blo 884570 4495985 := bstep (se 2 (by rfl) ⟨1685994, by rfl⟩ : syracuseStep 4495985 = 3371989) B3371989
theorem B7182989 : Blo 884570 7182989 := bstep (se 3 (by rfl) ⟨1346810, by rfl⟩ : syracuseStep 7182989 = 2693621) B2693621
theorem B1120979 : Blo 884570 1120979 := bstep (se 1 (by rfl) ⟨840734, by rfl⟩ : syracuseStep 1120979 = 1681469) B1681469
theorem B2988845 : Blo 884570 2988845 := bstep (se 3 (by rfl) ⟨560408, by rfl⟩ : syracuseStep 2988845 = 1120817) B1120817
theorem B2988899 : Blo 884570 2988899 := bstep (se 1 (by rfl) ⟨2241674, by rfl⟩ : syracuseStep 2988899 = 4483349) B4483349
theorem B1350515 : Blo 884570 1350515 := bstep (se 1 (by rfl) ⟨1012886, by rfl⟩ : syracuseStep 1350515 = 2025773) B2025773
theorem B1514513 : Blo 884570 1514513 := bstep (se 2 (by rfl) ⟨567942, by rfl⟩ : syracuseStep 1514513 = 1135885) B1135885
theorem B4267043 : Blo 884570 4267043 := bstep (se 1 (by rfl) ⟨3200282, by rfl⟩ : syracuseStep 4267043 = 6400565) B6400565
theorem B2989169 : Blo 884570 2989169 := bstep (se 2 (by rfl) ⟨1120938, by rfl⟩ : syracuseStep 2989169 = 2241877) B2241877
theorem B8527045 : Blo 884570 8527045 := bstep (se 4 (by rfl) ⟨799410, by rfl⟩ : syracuseStep 8527045 = 1598821) B1598821
theorem B1121683 : Blo 884570 1121683 := bstep (se 1 (by rfl) ⟨841262, by rfl⟩ : syracuseStep 1121683 = 1682525) B1682525
theorem B4267505 : Blo 884570 4267505 := bstep (se 2 (by rfl) ⟨1600314, by rfl⟩ : syracuseStep 4267505 = 3200629) B3200629
theorem B1121779 : Blo 884570 1121779 := bstep (se 1 (by rfl) ⟨841334, by rfl⟩ : syracuseStep 1121779 = 1682669) B1682669
theorem B5054021 : Blo 884570 5054021 := bstep (se 4 (by rfl) ⟨473814, by rfl⟩ : syracuseStep 5054021 = 947629) B947629
theorem B2989709 : Blo 884570 2989709 := bstep (se 3 (by rfl) ⟨560570, by rfl⟩ : syracuseStep 2989709 = 1121141) B1121141
theorem B2989763 : Blo 884570 2989763 := bstep (se 1 (by rfl) ⟨2242322, by rfl⟩ : syracuseStep 2989763 = 4484645) B4484645
theorem B5119793 : Blo 884570 5119793 := bstep (se 2 (by rfl) ⟨1919922, by rfl⟩ : syracuseStep 5119793 = 3839845) B3839845
theorem B6397795 : Blo 884570 6397795 := bstep (se 1 (by rfl) ⟨4798346, by rfl⟩ : syracuseStep 6397795 = 9596693) B9596693
theorem B2990033 : Blo 884570 2990033 := bstep (se 2 (by rfl) ⟨1121262, by rfl⟩ : syracuseStep 2990033 = 2242525) B2242525
theorem B1417171 : Blo 884570 1417171 := bstep (se 1 (by rfl) ⟨1062878, by rfl⟩ : syracuseStep 1417171 = 2125757) B2125757
theorem B1122275 : Blo 884570 1122275 := bstep (se 1 (by rfl) ⟨841706, by rfl⟩ : syracuseStep 1122275 = 1683413) B1683413
theorem B4497443 : Blo 884570 4497443 := bstep (se 1 (by rfl) ⟨3373082, by rfl⟩ : syracuseStep 4497443 = 6746165) B6746165
theorem B1679555 : Blo 884570 1679555 := bstep (se 1 (by rfl) ⟨1259666, by rfl⟩ : syracuseStep 1679555 = 2519333) B2519333
theorem B1417427 : Blo 884570 1417427 := bstep (se 1 (by rfl) ⟨1063070, by rfl⟩ : syracuseStep 1417427 = 2126141) B2126141
theorem B2990573 : Blo 884570 2990573 := bstep (se 3 (by rfl) ⟨560732, by rfl⟩ : syracuseStep 2990573 = 1121465) B1121465
theorem B5677573 : Blo 884570 5677573 := bstep (se 4 (by rfl) ⟨532272, by rfl⟩ : syracuseStep 5677573 = 1064545) B1064545
theorem B2990627 : Blo 884570 2990627 := bstep (se 1 (by rfl) ⟨2242970, by rfl⟩ : syracuseStep 2990627 = 4485941) B4485941
theorem B1122979 : Blo 884570 1122979 := bstep (se 1 (by rfl) ⟨842234, by rfl⟩ : syracuseStep 1122979 = 1684469) B1684469
theorem B1123075 : Blo 884570 1123075 := bstep (se 1 (by rfl) ⟨842306, by rfl⟩ : syracuseStep 1123075 = 1684613) B1684613
theorem B2990897 : Blo 884570 2990897 := bstep (se 2 (by rfl) ⟨1121586, by rfl⟩ : syracuseStep 2990897 = 2243173) B2243173
theorem B4498253 : Blo 884570 4498253 := bstep (se 3 (by rfl) ⟨843422, by rfl⟩ : syracuseStep 4498253 = 1686845) B1686845
theorem B6726725 : Blo 884570 6726725 := bstep (se 4 (by rfl) ⟨630630, by rfl⟩ : syracuseStep 6726725 = 1261261) B1261261
theorem B1680497 : Blo 884570 1680497 := bstep (se 2 (by rfl) ⟨630186, by rfl⟩ : syracuseStep 1680497 = 1260373) B1260373
theorem B1418401 : Blo 884570 1418401 := bstep (se 2 (by rfl) ⟨531900, by rfl⟩ : syracuseStep 1418401 = 1063801) B1063801
theorem B1123571 : Blo 884570 1123571 := bstep (se 1 (by rfl) ⟨842678, by rfl⟩ : syracuseStep 1123571 = 1685357) B1685357
theorem B2991437 : Blo 884570 2991437 := bstep (se 3 (by rfl) ⟨560894, by rfl⟩ : syracuseStep 2991437 = 1121789) B1121789
theorem B2991491 : Blo 884570 2991491 := bstep (se 1 (by rfl) ⟨2243618, by rfl⟩ : syracuseStep 2991491 = 4487237) B4487237
theorem B2991761 : Blo 884570 2991761 := bstep (se 2 (by rfl) ⟨1121910, by rfl⟩ : syracuseStep 2991761 = 2243821) B2243821
theorem B1124275 : Blo 884570 1124275 := bstep (se 1 (by rfl) ⟨843206, by rfl⟩ : syracuseStep 1124275 = 1686413) B1686413
theorem B1681393 : Blo 884570 1681393 := bstep (se 2 (by rfl) ⟨630522, by rfl⟩ : syracuseStep 1681393 = 1261045) B1261045
theorem B3188749 : Blo 884570 3188749 := bstep (se 3 (by rfl) ⟨597890, by rfl⟩ : syracuseStep 3188749 = 1195781) B1195781
theorem B1124371 : Blo 884570 1124371 := bstep (se 1 (by rfl) ⟨843278, by rfl⟩ : syracuseStep 1124371 = 1686557) B1686557
theorem B1419329 : Blo 884570 1419329 := bstep (se 2 (by rfl) ⟨532248, by rfl⟩ : syracuseStep 1419329 = 1064497) B1064497
theorem B1681553 : Blo 884570 1681553 := bstep (se 2 (by rfl) ⟨630582, by rfl⟩ : syracuseStep 1681553 = 1261165) B1261165
theorem B2992301 : Blo 884570 2992301 := bstep (se 3 (by rfl) ⟨561056, by rfl⟩ : syracuseStep 2992301 = 1122113) B1122113
theorem B2992355 : Blo 884570 2992355 := bstep (se 1 (by rfl) ⟨2244266, by rfl⟩ : syracuseStep 2992355 = 4488533) B4488533
theorem B40905101 : Blo 884570 40905101 := bstep (se 3 (by rfl) ⟨7669706, by rfl⟩ : syracuseStep 40905101 = 15339413) B15339413
theorem B2992625 : Blo 884570 2992625 := bstep (se 2 (by rfl) ⟨1122234, by rfl⟩ : syracuseStep 2992625 = 2244469) B2244469
theorem B2697745 : Blo 884570 2697745 := bstep (se 2 (by rfl) ⟨1011654, by rfl⟩ : syracuseStep 2697745 = 2023309) B2023309
theorem B1681955 : Blo 884570 1681955 := bstep (se 1 (by rfl) ⟨1261466, by rfl⟩ : syracuseStep 1681955 = 2522933) B2522933
theorem B2239235 : Blo 884570 2239235 := bstep (se 1 (by rfl) ⟨1679426, by rfl⟩ : syracuseStep 2239235 = 3358853) B3358853
theorem B7383821 : Blo 884570 7383821 := bstep (se 3 (by rfl) ⟨1384466, by rfl⟩ : syracuseStep 7383821 = 2768933) B2768933
theorem B1420163 : Blo 884570 1420163 := bstep (se 1 (by rfl) ⟨1065122, by rfl⟩ : syracuseStep 1420163 = 2130245) B2130245
theorem B1420195 : Blo 884570 1420195 := bstep (se 1 (by rfl) ⟨1065146, by rfl⟩ : syracuseStep 1420195 = 2130293) B2130293
theorem B2239427 : Blo 884570 2239427 := bstep (se 1 (by rfl) ⟨1679570, by rfl⟩ : syracuseStep 2239427 = 3359141) B3359141
theorem B2993165 : Blo 884570 2993165 := bstep (se 3 (by rfl) ⟨561218, by rfl⟩ : syracuseStep 2993165 = 1122437) B1122437
theorem B2993219 : Blo 884570 2993219 := bstep (se 1 (by rfl) ⟨2244914, by rfl⟩ : syracuseStep 2993219 = 4489829) B4489829
theorem B8629361 : Blo 884570 8629361 := bstep (se 2 (by rfl) ⟨3236010, by rfl⟩ : syracuseStep 8629361 = 6472021) B6472021
theorem B2993489 : Blo 884570 2993489 := bstep (se 2 (by rfl) ⟨1122558, by rfl⟩ : syracuseStep 2993489 = 2245117) B2245117
theorem B1682851 : Blo 884570 1682851 := bstep (se 1 (by rfl) ⟨1262138, by rfl⟩ : syracuseStep 1682851 = 2524277) B2524277
theorem B1683011 : Blo 884570 1683011 := bstep (se 1 (by rfl) ⟨1262258, by rfl⟩ : syracuseStep 1683011 = 2524517) B2524517
theorem B7188209 : Blo 884570 7188209 := bstep (se 2 (by rfl) ⟨2695578, by rfl⟩ : syracuseStep 7188209 = 5391157) B5391157
theorem B1421123 : Blo 884570 1421123 := bstep (se 1 (by rfl) ⟨1065842, by rfl⟩ : syracuseStep 1421123 = 2131685) B2131685
theorem B7581509 : Blo 884570 7581509 := bstep (se 4 (by rfl) ⟨710766, by rfl⟩ : syracuseStep 7581509 = 1421533) B1421533
theorem B2994029 : Blo 884570 2994029 := bstep (se 3 (by rfl) ⟨561380, by rfl⟩ : syracuseStep 2994029 = 1122761) B1122761
theorem B2240369 : Blo 884570 2240369 := bstep (se 2 (by rfl) ⟨840138, by rfl⟩ : syracuseStep 2240369 = 1680277) B1680277
theorem B4796273 : Blo 884570 4796273 := bstep (se 2 (by rfl) ⟨1798602, by rfl⟩ : syracuseStep 4796273 = 3597205) B3597205
theorem B1421201 : Blo 884570 1421201 := bstep (se 2 (by rfl) ⟨532950, by rfl⟩ : syracuseStep 1421201 = 1065901) B1065901
theorem B2240419 : Blo 884570 2240419 := bstep (se 1 (by rfl) ⟨1680314, by rfl⟩ : syracuseStep 2240419 = 3360629) B3360629
theorem B2994083 : Blo 884570 2994083 := bstep (se 1 (by rfl) ⟨2245562, by rfl⟩ : syracuseStep 2994083 = 4491125) B4491125
theorem B995251 : Blo 884570 995251 := bstep (se 1 (by rfl) ⟨746438, by rfl⟩ : syracuseStep 995251 = 1492877) B1492877
theorem B2240561 : Blo 884570 2240561 := bstep (se 2 (by rfl) ⟨840210, by rfl⟩ : syracuseStep 2240561 = 1680421) B1680421
theorem B995395 : Blo 884570 995395 := bstep (se 1 (by rfl) ⟨746546, by rfl⟩ : syracuseStep 995395 = 1493093) B1493093
theorem B1421425 : Blo 884570 1421425 := bstep (se 2 (by rfl) ⟨533034, by rfl⟩ : syracuseStep 1421425 = 1066069) B1066069
theorem B2994353 : Blo 884570 2994353 := bstep (se 2 (by rfl) ⟨1122882, by rfl⟩ : syracuseStep 2994353 = 2245765) B2245765
theorem B995539 : Blo 884570 995539 := bstep (se 1 (by rfl) ⟨746654, by rfl⟩ : syracuseStep 995539 = 1493309) B1493309
theorem B3780913 : Blo 884570 3780913 := bstep (se 2 (by rfl) ⟨1417842, by rfl⟩ : syracuseStep 3780913 = 2835685) B2835685
theorem B995683 : Blo 884570 995683 := bstep (se 1 (by rfl) ⟨746762, by rfl⟩ : syracuseStep 995683 = 1493525) B1493525
theorem B7582193 : Blo 884570 7582193 := bstep (se 2 (by rfl) ⟨2843322, by rfl⟩ : syracuseStep 7582193 = 5686645) B5686645
theorem B995827 : Blo 884570 995827 := bstep (se 1 (by rfl) ⟨746870, by rfl⟩ : syracuseStep 995827 = 1493741) B1493741
theorem B10105397 : Blo 884570 10105397 := bstep (se 5 (by rfl) ⟨473690, by rfl⟩ : syracuseStep 10105397 = 947381) B947381
theorem B1684081 : Blo 884570 1684081 := bstep (se 2 (by rfl) ⟨631530, by rfl⟩ : syracuseStep 1684081 = 1263061) B1263061
theorem B995971 : Blo 884570 995971 := bstep (se 1 (by rfl) ⟨746978, by rfl⟩ : syracuseStep 995971 = 1493957) B1493957
theorem B2994893 : Blo 884570 2994893 := bstep (se 3 (by rfl) ⟨561542, by rfl⟩ : syracuseStep 2994893 = 1123085) B1123085
theorem B2994947 : Blo 884570 2994947 := bstep (se 1 (by rfl) ⟨2246210, by rfl⟩ : syracuseStep 2994947 = 4492421) B4492421
theorem B996115 : Blo 884570 996115 := bstep (se 1 (by rfl) ⟨747086, by rfl⟩ : syracuseStep 996115 = 1494173) B1494173
theorem B996259 : Blo 884570 996259 := bstep (se 1 (by rfl) ⟨747194, by rfl⟩ : syracuseStep 996259 = 1494389) B1494389
theorem B6403013 : Blo 884570 6403013 := bstep (se 4 (by rfl) ⟨600282, by rfl⟩ : syracuseStep 6403013 = 1200565) B1200565
theorem B2241553 : Blo 884570 2241553 := bstep (se 2 (by rfl) ⟨840582, by rfl⟩ : syracuseStep 2241553 = 1681165) B1681165
theorem B2995217 : Blo 884570 2995217 := bstep (se 2 (by rfl) ⟨1123206, by rfl⟩ : syracuseStep 2995217 = 2246413) B2246413
theorem B996403 : Blo 884570 996403 := bstep (se 1 (by rfl) ⟨747302, by rfl⟩ : syracuseStep 996403 = 1494605) B1494605
theorem B3454129 : Blo 884570 3454129 := bstep (se 2 (by rfl) ⟨1295298, by rfl⟩ : syracuseStep 3454129 = 2590597) B2590597
theorem B996547 : Blo 884570 996547 := bstep (se 1 (by rfl) ⟨747410, by rfl⟩ : syracuseStep 996547 = 1494821) B1494821
theorem B5059853 : Blo 884570 5059853 := bstep (se 3 (by rfl) ⟨948722, by rfl⟩ : syracuseStep 5059853 = 1897445) B1897445
theorem B2241827 : Blo 884570 2241827 := bstep (se 1 (by rfl) ⟨1681370, by rfl⟩ : syracuseStep 2241827 = 3362741) B3362741
theorem B996691 : Blo 884570 996691 := bstep (se 1 (by rfl) ⟨747518, by rfl⟩ : syracuseStep 996691 = 1495037) B1495037
theorem B5682545 : Blo 884570 5682545 := bstep (se 2 (by rfl) ⟨2130954, by rfl⟩ : syracuseStep 5682545 = 4261909) B4261909
theorem B38352325 : Blo 884570 38352325 := bstep (se 4 (by rfl) ⟨3595530, by rfl⟩ : syracuseStep 38352325 = 7191061) B7191061
theorem B2242019 : Blo 884570 2242019 := bstep (se 1 (by rfl) ⟨1681514, by rfl⟩ : syracuseStep 2242019 = 3363029) B3363029
theorem B996835 : Blo 884570 996835 := bstep (se 1 (by rfl) ⟨747626, by rfl⟩ : syracuseStep 996835 = 1495253) B1495253
theorem B2995757 : Blo 884570 2995757 := bstep (se 3 (by rfl) ⟨561704, by rfl⟩ : syracuseStep 2995757 = 1123409) B1123409
theorem B2995811 : Blo 884570 2995811 := bstep (se 1 (by rfl) ⟨2246858, by rfl⟩ : syracuseStep 2995811 = 4493717) B4493717
theorem B996979 : Blo 884570 996979 := bstep (se 1 (by rfl) ⟨747734, by rfl⟩ : syracuseStep 996979 = 1495469) B1495469
theorem B1685137 : Blo 884570 1685137 := bstep (se 2 (by rfl) ⟨631926, by rfl⟩ : syracuseStep 1685137 = 1263853) B1263853
theorem B6076109 : Blo 884570 6076109 := bstep (se 3 (by rfl) ⟨1139270, by rfl⟩ : syracuseStep 6076109 = 2278541) B2278541
theorem B997123 : Blo 884570 997123 := bstep (se 1 (by rfl) ⟨747842, by rfl⟩ : syracuseStep 997123 = 1495685) B1495685
theorem B1423187 : Blo 884570 1423187 := bstep (se 1 (by rfl) ⟨1067390, by rfl⟩ : syracuseStep 1423187 = 2134781) B2134781
theorem B2996081 : Blo 884570 2996081 := bstep (se 2 (by rfl) ⟨1123530, by rfl⟩ : syracuseStep 2996081 = 2247061) B2247061
theorem B997267 : Blo 884570 997267 := bstep (se 1 (by rfl) ⟨747950, by rfl⟩ : syracuseStep 997267 = 1495901) B1495901
theorem B1259507 : Blo 884570 1259507 := bstep (se 1 (by rfl) ⟨944630, by rfl⟩ : syracuseStep 1259507 = 1889261) B1889261
theorem B997411 : Blo 884570 997411 := bstep (se 1 (by rfl) ⟨748058, by rfl⟩ : syracuseStep 997411 = 1496117) B1496117
theorem B1685539 : Blo 884570 1685539 := bstep (se 1 (by rfl) ⟨1264154, by rfl⟩ : syracuseStep 1685539 = 2528309) B2528309
theorem B1259587 : Blo 884570 1259587 := bstep (se 1 (by rfl) ⟨944690, by rfl⟩ : syracuseStep 1259587 = 1889381) B1889381
theorem B4798541 : Blo 884570 4798541 := bstep (se 3 (by rfl) ⟨899726, by rfl⟩ : syracuseStep 4798541 = 1799453) B1799453
theorem B1685585 : Blo 884570 1685585 := bstep (se 2 (by rfl) ⟨632094, by rfl⟩ : syracuseStep 1685585 = 1264189) B1264189
theorem B997555 : Blo 884570 997555 := bstep (se 1 (by rfl) ⟨748166, by rfl⟩ : syracuseStep 997555 = 1496333) B1496333
theorem B5388529 : Blo 884570 5388529 := bstep (se 2 (by rfl) ⟨2020698, by rfl⟩ : syracuseStep 5388529 = 4041397) B4041397
theorem B997699 : Blo 884570 997699 := bstep (se 1 (by rfl) ⟨748274, by rfl⟩ : syracuseStep 997699 = 1496549) B1496549
theorem B1685873 : Blo 884570 1685873 := bstep (se 2 (by rfl) ⟨632202, by rfl⟩ : syracuseStep 1685873 = 1264405) B1264405
theorem B2996621 : Blo 884570 2996621 := bstep (se 3 (by rfl) ⟨561866, by rfl⟩ : syracuseStep 2996621 = 1123733) B1123733
theorem B2242961 : Blo 884570 2242961 := bstep (se 2 (by rfl) ⟨841110, by rfl⟩ : syracuseStep 2242961 = 1682221) B1682221
theorem B1063315 : Blo 884570 1063315 := bstep (se 1 (by rfl) ⟨797486, by rfl⟩ : syracuseStep 1063315 = 1594973) B1594973
theorem B2243011 : Blo 884570 2243011 := bstep (se 1 (by rfl) ⟨1682258, by rfl⟩ : syracuseStep 2243011 = 3364517) B3364517
theorem B2996675 : Blo 884570 2996675 := bstep (se 1 (by rfl) ⟨2247506, by rfl⟩ : syracuseStep 2996675 = 4495013) B4495013
theorem B997843 : Blo 884570 997843 := bstep (se 1 (by rfl) ⟨748382, by rfl⟩ : syracuseStep 997843 = 1496765) B1496765
theorem B1063459 : Blo 884570 1063459 := bstep (se 1 (by rfl) ⟨797594, by rfl⟩ : syracuseStep 1063459 = 1595189) B1595189
theorem B18233909 : Blo 884570 18233909 := bstep (se 5 (by rfl) ⟨854714, by rfl⟩ : syracuseStep 18233909 = 1709429) B1709429
theorem B2243153 : Blo 884570 2243153 := bstep (se 2 (by rfl) ⟨841182, by rfl⟩ : syracuseStep 2243153 = 1682365) B1682365
theorem B997987 : Blo 884570 997987 := bstep (se 1 (by rfl) ⟨748490, by rfl⟩ : syracuseStep 997987 = 1496981) B1496981
theorem B1260145 : Blo 884570 1260145 := bstep (se 2 (by rfl) ⟨472554, by rfl⟩ : syracuseStep 1260145 = 945109) B945109
theorem B2996945 : Blo 884570 2996945 := bstep (se 2 (by rfl) ⟨1123854, by rfl⟩ : syracuseStep 2996945 = 2247709) B2247709
theorem B2702051 : Blo 884570 2702051 := bstep (se 1 (by rfl) ⟨2026538, by rfl⟩ : syracuseStep 2702051 = 4053077) B4053077
theorem B998131 : Blo 884570 998131 := bstep (se 1 (by rfl) ⟨748598, by rfl⟩ : syracuseStep 998131 = 1497197) B1497197
theorem B6732557 : Blo 884570 6732557 := bstep (se 3 (by rfl) ⟨1262354, by rfl⟩ : syracuseStep 6732557 = 2524709) B2524709
theorem B998275 : Blo 884570 998275 := bstep (se 1 (by rfl) ⟨748706, by rfl⟩ : syracuseStep 998275 = 1497413) B1497413
theorem B998419 : Blo 884570 998419 := bstep (se 1 (by rfl) ⟨748814, by rfl⟩ : syracuseStep 998419 = 1497629) B1497629
theorem B1686595 : Blo 884570 1686595 := bstep (se 1 (by rfl) ⟨1264946, by rfl⟩ : syracuseStep 1686595 = 2529893) B2529893
theorem B5454947 : Blo 884570 5454947 := bstep (se 1 (by rfl) ⟨4091210, by rfl⟩ : syracuseStep 5454947 = 8182421) B8182421
theorem B998563 : Blo 884570 998563 := bstep (se 1 (by rfl) ⟨748922, by rfl⟩ : syracuseStep 998563 = 1497845) B1497845
theorem B2997485 : Blo 884570 2997485 := bstep (se 3 (by rfl) ⟨562028, by rfl⟩ : syracuseStep 2997485 = 1124057) B1124057
theorem B1817891 : Blo 884570 1817891 := bstep (se 1 (by rfl) ⟨1363418, by rfl⟩ : syracuseStep 1817891 = 2726837) B2726837
theorem B2997539 : Blo 884570 2997539 := bstep (se 1 (by rfl) ⟨2248154, by rfl⟩ : syracuseStep 2997539 = 4496309) B4496309
theorem B1260851 : Blo 884570 1260851 := bstep (se 1 (by rfl) ⟨945638, by rfl⟩ : syracuseStep 1260851 = 1891277) B1891277
theorem B998707 : Blo 884570 998707 := bstep (se 1 (by rfl) ⟨749030, by rfl⟩ : syracuseStep 998707 = 1498061) B1498061
theorem B998851 : Blo 884570 998851 := bstep (se 1 (by rfl) ⟨749138, by rfl⟩ : syracuseStep 998851 = 1498277) B1498277
theorem B2244145 : Blo 884570 2244145 := bstep (se 2 (by rfl) ⟨841554, by rfl⟩ : syracuseStep 2244145 = 1683109) B1683109
theorem B2997809 : Blo 884570 2997809 := bstep (se 2 (by rfl) ⟨1124178, by rfl⟩ : syracuseStep 2997809 = 2248357) B2248357
theorem B998995 : Blo 884570 998995 := bstep (se 1 (by rfl) ⟨749246, by rfl⟩ : syracuseStep 998995 = 1498493) B1498493
theorem B2834147 : Blo 884570 2834147 := bstep (se 1 (by rfl) ⟨2125610, by rfl⟩ : syracuseStep 2834147 = 4251221) B4251221
theorem B999139 : Blo 884570 999139 := bstep (se 1 (by rfl) ⟨749354, by rfl⟩ : syracuseStep 999139 = 1498709) B1498709
theorem B5685005 : Blo 884570 5685005 := bstep (se 3 (by rfl) ⟨1065938, by rfl⟩ : syracuseStep 5685005 = 2131877) B2131877
theorem B4800269 : Blo 884570 4800269 := bstep (se 3 (by rfl) ⟨900050, by rfl⟩ : syracuseStep 4800269 = 1800101) B1800101
theorem B1326881 : Blo 884570 1326881 := bstep (se 2 (by rfl) ⟨497580, by rfl⟩ : syracuseStep 1326881 = 995161) B995161
theorem B1326899 : Blo 884570 1326899 := bstep (se 1 (by rfl) ⟨995174, by rfl⟩ : syracuseStep 1326899 = 1990349) B1990349
theorem B1195841 : Blo 884570 1195841 := bstep (se 2 (by rfl) ⟨448440, by rfl⟩ : syracuseStep 1195841 = 896881) B896881
theorem B2244419 : Blo 884570 2244419 := bstep (se 1 (by rfl) ⟨1683314, by rfl⟩ : syracuseStep 2244419 = 3366629) B3366629
theorem B1326929 : Blo 884570 1326929 := bstep (se 2 (by rfl) ⟨497598, by rfl⟩ : syracuseStep 1326929 = 995197) B995197
theorem B1326947 : Blo 884570 1326947 := bstep (se 1 (by rfl) ⟨995210, by rfl⟩ : syracuseStep 1326947 = 1990421) B1990421
theorem B999283 : Blo 884570 999283 := bstep (se 1 (by rfl) ⟨749462, by rfl⟩ : syracuseStep 999283 = 1498925) B1498925
theorem B1326977 : Blo 884570 1326977 := bstep (se 2 (by rfl) ⟨497616, by rfl⟩ : syracuseStep 1326977 = 995233) B995233
theorem B3784589 : Blo 884570 3784589 := bstep (se 3 (by rfl) ⟨709610, by rfl⟩ : syracuseStep 3784589 = 1419221) B1419221
theorem B1326995 : Blo 884570 1326995 := bstep (se 1 (by rfl) ⟨995246, by rfl⟩ : syracuseStep 1326995 = 1990493) B1990493
theorem B1327025 : Blo 884570 1327025 := bstep (se 2 (by rfl) ⟨497634, by rfl⟩ : syracuseStep 1327025 = 995269) B995269
theorem B1261489 : Blo 884570 1261489 := bstep (se 2 (by rfl) ⟨473058, by rfl⟩ : syracuseStep 1261489 = 946117) B946117
theorem B1327043 : Blo 884570 1327043 := bstep (se 1 (by rfl) ⟨995282, by rfl⟩ : syracuseStep 1327043 = 1990565) B1990565
theorem B1327073 : Blo 884570 1327073 := bstep (se 2 (by rfl) ⟨497652, by rfl⟩ : syracuseStep 1327073 = 995305) B995305
theorem B1327091 : Blo 884570 1327091 := bstep (se 1 (by rfl) ⟨995318, by rfl⟩ : syracuseStep 1327091 = 1990637) B1990637
theorem B2244611 : Blo 884570 2244611 := bstep (se 1 (by rfl) ⟨1683458, by rfl⟩ : syracuseStep 2244611 = 3366917) B3366917
theorem B999427 : Blo 884570 999427 := bstep (se 1 (by rfl) ⟨749570, by rfl⟩ : syracuseStep 999427 = 1499141) B1499141
theorem B1327121 : Blo 884570 1327121 := bstep (se 2 (by rfl) ⟨497670, by rfl⟩ : syracuseStep 1327121 = 995341) B995341
theorem B1327139 : Blo 884570 1327139 := bstep (se 1 (by rfl) ⟨995354, by rfl⟩ : syracuseStep 1327139 = 1990709) B1990709
theorem B1261603 : Blo 884570 1261603 := bstep (se 1 (by rfl) ⟨946202, by rfl⟩ : syracuseStep 1261603 = 1892405) B1892405
theorem B1327169 : Blo 884570 1327169 := bstep (se 2 (by rfl) ⟨497688, by rfl⟩ : syracuseStep 1327169 = 995377) B995377
theorem B2998349 : Blo 884570 2998349 := bstep (se 3 (by rfl) ⟨562190, by rfl⟩ : syracuseStep 2998349 = 1124381) B1124381
theorem B1327187 : Blo 884570 1327187 := bstep (se 1 (by rfl) ⟨995390, by rfl⟩ : syracuseStep 1327187 = 1990781) B1990781
theorem B1327217 : Blo 884570 1327217 := bstep (se 2 (by rfl) ⟨497706, by rfl⟩ : syracuseStep 1327217 = 995413) B995413
theorem B1327235 : Blo 884570 1327235 := bstep (se 1 (by rfl) ⟨995426, by rfl⟩ : syracuseStep 1327235 = 1990853) B1990853
theorem B2998403 : Blo 884570 2998403 := bstep (se 1 (by rfl) ⟨2248802, by rfl⟩ : syracuseStep 2998403 = 4497605) B4497605
theorem B5390477 : Blo 884570 5390477 := bstep (se 3 (by rfl) ⟨1010714, by rfl⟩ : syracuseStep 5390477 = 2021429) B2021429
theorem B999571 : Blo 884570 999571 := bstep (se 1 (by rfl) ⟨749678, by rfl⟩ : syracuseStep 999571 = 1499357) B1499357
theorem B1327265 : Blo 884570 1327265 := bstep (se 2 (by rfl) ⟨497724, by rfl⟩ : syracuseStep 1327265 = 995449) B995449
theorem B1327283 : Blo 884570 1327283 := bstep (se 1 (by rfl) ⟨995462, by rfl⟩ : syracuseStep 1327283 = 1990925) B1990925
theorem B1327313 : Blo 884570 1327313 := bstep (se 2 (by rfl) ⟨497742, by rfl⟩ : syracuseStep 1327313 = 995485) B995485
theorem B1327331 : Blo 884570 1327331 := bstep (se 1 (by rfl) ⟨995498, by rfl⟩ : syracuseStep 1327331 = 1990997) B1990997
theorem B1327361 : Blo 884570 1327361 := bstep (se 2 (by rfl) ⟨497760, by rfl⟩ : syracuseStep 1327361 = 995521) B995521
theorem B1327379 : Blo 884570 1327379 := bstep (se 1 (by rfl) ⟨995534, by rfl⟩ : syracuseStep 1327379 = 1991069) B1991069
theorem B1327409 : Blo 884570 1327409 := bstep (se 2 (by rfl) ⟨497778, by rfl⟩ : syracuseStep 1327409 = 995557) B995557
theorem B1327427 : Blo 884570 1327427 := bstep (se 1 (by rfl) ⟨995570, by rfl⟩ : syracuseStep 1327427 = 1991141) B1991141
theorem B1327457 : Blo 884570 1327457 := bstep (se 2 (by rfl) ⟨497796, by rfl⟩ : syracuseStep 1327457 = 995593) B995593
theorem B1327475 : Blo 884570 1327475 := bstep (se 1 (by rfl) ⟨995606, by rfl⟩ : syracuseStep 1327475 = 1991213) B1991213
theorem B1327505 : Blo 884570 1327505 := bstep (se 2 (by rfl) ⟨497814, by rfl⟩ : syracuseStep 1327505 = 995629) B995629
theorem B2998673 : Blo 884570 2998673 := bstep (se 2 (by rfl) ⟨1124502, by rfl⟩ : syracuseStep 2998673 = 2249005) B2249005
theorem B1327523 : Blo 884570 1327523 := bstep (se 1 (by rfl) ⟨995642, by rfl⟩ : syracuseStep 1327523 = 1991285) B1991285
theorem B1917361 : Blo 884570 1917361 := bstep (se 2 (by rfl) ⟨719010, by rfl⟩ : syracuseStep 1917361 = 1438021) B1438021
theorem B1327553 : Blo 884570 1327553 := bstep (se 2 (by rfl) ⟨497832, by rfl⟩ : syracuseStep 1327553 = 995665) B995665
theorem B1327571 : Blo 884570 1327571 := bstep (se 1 (by rfl) ⟨995678, by rfl⟩ : syracuseStep 1327571 = 1991357) B1991357
theorem B5390819 : Blo 884570 5390819 := bstep (se 1 (by rfl) ⟨4043114, by rfl⟩ : syracuseStep 5390819 = 8086229) B8086229
theorem B1327601 : Blo 884570 1327601 := bstep (se 2 (by rfl) ⟨497850, by rfl⟩ : syracuseStep 1327601 = 995701) B995701
theorem B1327619 : Blo 884570 1327619 := bstep (se 1 (by rfl) ⟨995714, by rfl⟩ : syracuseStep 1327619 = 1991429) B1991429
theorem B1327649 : Blo 884570 1327649 := bstep (se 2 (by rfl) ⟨497868, by rfl⟩ : syracuseStep 1327649 = 995737) B995737
theorem B1327667 : Blo 884570 1327667 := bstep (se 1 (by rfl) ⟨995750, by rfl⟩ : syracuseStep 1327667 = 1991501) B1991501
theorem B1327697 : Blo 884570 1327697 := bstep (se 2 (by rfl) ⟨497886, by rfl⟩ : syracuseStep 1327697 = 995773) B995773
theorem B1327715 : Blo 884570 1327715 := bstep (se 1 (by rfl) ⟨995786, by rfl⟩ : syracuseStep 1327715 = 1991573) B1991573
theorem B1327745 : Blo 884570 1327745 := bstep (se 2 (by rfl) ⟨497904, by rfl⟩ : syracuseStep 1327745 = 995809) B995809
theorem B1327763 : Blo 884570 1327763 := bstep (se 1 (by rfl) ⟨995822, by rfl⟩ : syracuseStep 1327763 = 1991645) B1991645
theorem B1327793 : Blo 884570 1327793 := bstep (se 2 (by rfl) ⟨497922, by rfl⟩ : syracuseStep 1327793 = 995845) B995845
theorem B1327811 : Blo 884570 1327811 := bstep (se 1 (by rfl) ⟨995858, by rfl⟩ : syracuseStep 1327811 = 1991717) B1991717
theorem B15155909 : Blo 884570 15155909 := bstep (se 4 (by rfl) ⟨1420866, by rfl⟩ : syracuseStep 15155909 = 2841733) B2841733
theorem B1327841 : Blo 884570 1327841 := bstep (se 2 (by rfl) ⟨497940, by rfl⟩ : syracuseStep 1327841 = 995881) B995881
theorem B1327859 : Blo 884570 1327859 := bstep (se 1 (by rfl) ⟨995894, by rfl⟩ : syracuseStep 1327859 = 1991789) B1991789
theorem B1327889 : Blo 884570 1327889 := bstep (se 2 (by rfl) ⟨497958, by rfl⟩ : syracuseStep 1327889 = 995917) B995917
theorem B1327907 : Blo 884570 1327907 := bstep (se 1 (by rfl) ⟨995930, by rfl⟩ : syracuseStep 1327907 = 1991861) B1991861
theorem B3195683 : Blo 884570 3195683 := bstep (se 1 (by rfl) ⟨2396762, by rfl⟩ : syracuseStep 3195683 = 4793525) B4793525
theorem B1327937 : Blo 884570 1327937 := bstep (se 2 (by rfl) ⟨497976, by rfl⟩ : syracuseStep 1327937 = 995953) B995953
theorem B1327955 : Blo 884570 1327955 := bstep (se 1 (by rfl) ⟨995966, by rfl⟩ : syracuseStep 1327955 = 1991933) B1991933
theorem B1327985 : Blo 884570 1327985 := bstep (se 2 (by rfl) ⟨497994, by rfl⟩ : syracuseStep 1327985 = 995989) B995989
theorem B1328003 : Blo 884570 1328003 := bstep (se 1 (by rfl) ⟨996002, by rfl⟩ : syracuseStep 1328003 = 1992005) B1992005
theorem B1328033 : Blo 884570 1328033 := bstep (se 2 (by rfl) ⟨498012, by rfl⟩ : syracuseStep 1328033 = 996025) B996025
theorem B2245553 : Blo 884570 2245553 := bstep (se 2 (by rfl) ⟨842082, by rfl⟩ : syracuseStep 2245553 = 1684165) B1684165
theorem B1328051 : Blo 884570 1328051 := bstep (se 1 (by rfl) ⟨996038, by rfl⟩ : syracuseStep 1328051 = 1992077) B1992077
theorem B2737091 : Blo 884570 2737091 := bstep (se 1 (by rfl) ⟨2052818, by rfl⟩ : syracuseStep 2737091 = 4105637) B4105637
theorem B1328081 : Blo 884570 1328081 := bstep (se 2 (by rfl) ⟨498030, by rfl⟩ : syracuseStep 1328081 = 996061) B996061
theorem B1328099 : Blo 884570 1328099 := bstep (se 1 (by rfl) ⟨996074, by rfl⟩ : syracuseStep 1328099 = 1992149) B1992149
theorem B2245603 : Blo 884570 2245603 := bstep (se 1 (by rfl) ⟨1684202, by rfl⟩ : syracuseStep 2245603 = 3368405) B3368405
theorem B1328129 : Blo 884570 1328129 := bstep (se 2 (by rfl) ⟨498048, by rfl⟩ : syracuseStep 1328129 = 996097) B996097
theorem B1328147 : Blo 884570 1328147 := bstep (se 1 (by rfl) ⟨996110, by rfl⟩ : syracuseStep 1328147 = 1992221) B1992221
theorem B1328177 : Blo 884570 1328177 := bstep (se 2 (by rfl) ⟨498066, by rfl⟩ : syracuseStep 1328177 = 996133) B996133
theorem B1328195 : Blo 884570 1328195 := bstep (se 1 (by rfl) ⟨996146, by rfl⟩ : syracuseStep 1328195 = 1992293) B1992293
theorem B1328225 : Blo 884570 1328225 := bstep (se 2 (by rfl) ⟨498084, by rfl⟩ : syracuseStep 1328225 = 996169) B996169
theorem B2245745 : Blo 884570 2245745 := bstep (se 2 (by rfl) ⟨842154, by rfl⟩ : syracuseStep 2245745 = 1684309) B1684309
theorem B1328243 : Blo 884570 1328243 := bstep (se 1 (by rfl) ⟨996182, by rfl⟩ : syracuseStep 1328243 = 1992365) B1992365
theorem B1328273 : Blo 884570 1328273 := bstep (se 2 (by rfl) ⟨498102, by rfl⟩ : syracuseStep 1328273 = 996205) B996205
theorem B1328291 : Blo 884570 1328291 := bstep (se 1 (by rfl) ⟨996218, by rfl⟩ : syracuseStep 1328291 = 1992437) B1992437
theorem B1328321 : Blo 884570 1328321 := bstep (se 2 (by rfl) ⟨498120, by rfl⟩ : syracuseStep 1328321 = 996241) B996241
theorem B1328339 : Blo 884570 1328339 := bstep (se 1 (by rfl) ⟨996254, by rfl⟩ : syracuseStep 1328339 = 1992509) B1992509
theorem B8209649 : Blo 884570 8209649 := bstep (se 2 (by rfl) ⟨3078618, by rfl⟩ : syracuseStep 8209649 = 6157237) B6157237
theorem B1328369 : Blo 884570 1328369 := bstep (se 2 (by rfl) ⟨498138, by rfl⟩ : syracuseStep 1328369 = 996277) B996277
theorem B1328387 : Blo 884570 1328387 := bstep (se 1 (by rfl) ⟨996290, by rfl⟩ : syracuseStep 1328387 = 1992581) B1992581
theorem B1328417 : Blo 884570 1328417 := bstep (se 2 (by rfl) ⟨498156, by rfl⟩ : syracuseStep 1328417 = 996313) B996313
theorem B1328435 : Blo 884570 1328435 := bstep (se 1 (by rfl) ⟨996326, by rfl⟩ : syracuseStep 1328435 = 1992653) B1992653
theorem B2737475 : Blo 884570 2737475 := bstep (se 1 (by rfl) ⟨2053106, by rfl⟩ : syracuseStep 2737475 = 4106213) B4106213
theorem B1328465 : Blo 884570 1328465 := bstep (se 2 (by rfl) ⟨498174, by rfl⟩ : syracuseStep 1328465 = 996349) B996349
theorem B8504675 : Blo 884570 8504675 := bstep (se 1 (by rfl) ⟨6378506, by rfl⟩ : syracuseStep 8504675 = 12757013) B12757013
theorem B1328483 : Blo 884570 1328483 := bstep (se 1 (by rfl) ⟨996362, by rfl⟩ : syracuseStep 1328483 = 1992725) B1992725
theorem B1262947 : Blo 884570 1262947 := bstep (se 1 (by rfl) ⟨947210, by rfl⟩ : syracuseStep 1262947 = 1894421) B1894421
theorem B3360113 : Blo 884570 3360113 := bstep (se 2 (by rfl) ⟨1260042, by rfl⟩ : syracuseStep 3360113 = 2520085) B2520085
theorem B1328513 : Blo 884570 1328513 := bstep (se 2 (by rfl) ⟨498192, by rfl⟩ : syracuseStep 1328513 = 996385) B996385
theorem B1328531 : Blo 884570 1328531 := bstep (se 1 (by rfl) ⟨996398, by rfl⟩ : syracuseStep 1328531 = 1992797) B1992797
theorem B1328561 : Blo 884570 1328561 := bstep (se 2 (by rfl) ⟨498210, by rfl⟩ : syracuseStep 1328561 = 996421) B996421
theorem B1328579 : Blo 884570 1328579 := bstep (se 1 (by rfl) ⟨996434, by rfl⟩ : syracuseStep 1328579 = 1992869) B1992869
theorem B3032515 : Blo 884570 3032515 := bstep (se 1 (by rfl) ⟨2274386, by rfl⟩ : syracuseStep 3032515 = 4548773) B4548773
theorem B2835917 : Blo 884570 2835917 := bstep (se 3 (by rfl) ⟨531734, by rfl⟩ : syracuseStep 2835917 = 1063469) B1063469
theorem B1328609 : Blo 884570 1328609 := bstep (se 2 (by rfl) ⟨498228, by rfl⟩ : syracuseStep 1328609 = 996457) B996457
theorem B1328627 : Blo 884570 1328627 := bstep (se 1 (by rfl) ⟨996470, by rfl⟩ : syracuseStep 1328627 = 1992941) B1992941
theorem B1197571 : Blo 884570 1197571 := bstep (se 1 (by rfl) ⟨898178, by rfl⟩ : syracuseStep 1197571 = 1796357) B1796357
theorem B1328657 : Blo 884570 1328657 := bstep (se 2 (by rfl) ⟨498246, by rfl⟩ : syracuseStep 1328657 = 996493) B996493
theorem B1328675 : Blo 884570 1328675 := bstep (se 1 (by rfl) ⟨996506, by rfl⟩ : syracuseStep 1328675 = 1993013) B1993013
theorem B1328705 : Blo 884570 1328705 := bstep (se 2 (by rfl) ⟨498264, by rfl⟩ : syracuseStep 1328705 = 996529) B996529
theorem B1328723 : Blo 884570 1328723 := bstep (se 1 (by rfl) ⟨996542, by rfl⟩ : syracuseStep 1328723 = 1993085) B1993085
theorem B1328753 : Blo 884570 1328753 := bstep (se 2 (by rfl) ⟨498282, by rfl⟩ : syracuseStep 1328753 = 996565) B996565
theorem B6735473 : Blo 884570 6735473 := bstep (se 2 (by rfl) ⟨2525802, by rfl⟩ : syracuseStep 6735473 = 5051605) B5051605
theorem B1328771 : Blo 884570 1328771 := bstep (se 1 (by rfl) ⟨996578, by rfl⟩ : syracuseStep 1328771 = 1993157) B1993157
theorem B1328801 : Blo 884570 1328801 := bstep (se 2 (by rfl) ⟨498300, by rfl⟩ : syracuseStep 1328801 = 996601) B996601
theorem B1328819 : Blo 884570 1328819 := bstep (se 1 (by rfl) ⟨996614, by rfl⟩ : syracuseStep 1328819 = 1993229) B1993229
theorem B2049731 : Blo 884570 2049731 := bstep (se 1 (by rfl) ⟨1537298, by rfl⟩ : syracuseStep 2049731 = 3074597) B3074597
theorem B1328849 : Blo 884570 1328849 := bstep (se 2 (by rfl) ⟨498318, by rfl⟩ : syracuseStep 1328849 = 996637) B996637
theorem B1328867 : Blo 884570 1328867 := bstep (se 1 (by rfl) ⟨996650, by rfl⟩ : syracuseStep 1328867 = 1993301) B1993301
theorem B1328897 : Blo 884570 1328897 := bstep (se 2 (by rfl) ⟨498336, by rfl⟩ : syracuseStep 1328897 = 996673) B996673
theorem B1328915 : Blo 884570 1328915 := bstep (se 1 (by rfl) ⟨996686, by rfl⟩ : syracuseStep 1328915 = 1993373) B1993373
theorem B1492769 : Blo 884570 1492769 := bstep (se 2 (by rfl) ⟨559788, by rfl⟩ : syracuseStep 1492769 = 1119577) B1119577
theorem B1328945 : Blo 884570 1328945 := bstep (se 2 (by rfl) ⟨498354, by rfl⟩ : syracuseStep 1328945 = 996709) B996709
theorem B1328963 : Blo 884570 1328963 := bstep (se 1 (by rfl) ⟨996722, by rfl⟩ : syracuseStep 1328963 = 1993445) B1993445
theorem B1328993 : Blo 884570 1328993 := bstep (se 2 (by rfl) ⟨498372, by rfl⟩ : syracuseStep 1328993 = 996745) B996745
theorem B1329011 : Blo 884570 1329011 := bstep (se 1 (by rfl) ⟨996758, by rfl⟩ : syracuseStep 1329011 = 1993517) B1993517
theorem B1329041 : Blo 884570 1329041 := bstep (se 2 (by rfl) ⟨498390, by rfl⟩ : syracuseStep 1329041 = 996781) B996781
theorem B1492897 : Blo 884570 1492897 := bstep (se 2 (by rfl) ⟨559836, by rfl⟩ : syracuseStep 1492897 = 1119673) B1119673
theorem B1329059 : Blo 884570 1329059 := bstep (se 1 (by rfl) ⟨996794, by rfl⟩ : syracuseStep 1329059 = 1993589) B1993589
theorem B1329089 : Blo 884570 1329089 := bstep (se 2 (by rfl) ⟨498408, by rfl⟩ : syracuseStep 1329089 = 996817) B996817
theorem B1492931 : Blo 884570 1492931 := bstep (se 1 (by rfl) ⟨1119698, by rfl⟩ : syracuseStep 1492931 = 2239397) B2239397
theorem B1329107 : Blo 884570 1329107 := bstep (se 1 (by rfl) ⟨996830, by rfl⟩ : syracuseStep 1329107 = 1993661) B1993661
theorem B1329137 : Blo 884570 1329137 := bstep (se 2 (by rfl) ⟨498426, by rfl⟩ : syracuseStep 1329137 = 996853) B996853
theorem B1329155 : Blo 884570 1329155 := bstep (se 1 (by rfl) ⟨996866, by rfl⟩ : syracuseStep 1329155 = 1993733) B1993733
theorem B1329185 : Blo 884570 1329185 := bstep (se 2 (by rfl) ⟨498444, by rfl⟩ : syracuseStep 1329185 = 996889) B996889
theorem B1329203 : Blo 884570 1329203 := bstep (se 1 (by rfl) ⟨996902, by rfl⟩ : syracuseStep 1329203 = 1993805) B1993805
theorem B1493059 : Blo 884570 1493059 := bstep (se 1 (by rfl) ⟨1119794, by rfl⟩ : syracuseStep 1493059 = 2239589) B2239589
theorem B1329233 : Blo 884570 1329233 := bstep (se 2 (by rfl) ⟨498462, by rfl⟩ : syracuseStep 1329233 = 996925) B996925
theorem B2246737 : Blo 884570 2246737 := bstep (se 2 (by rfl) ⟨842526, by rfl⟩ : syracuseStep 2246737 = 1685053) B1685053
theorem B1329251 : Blo 884570 1329251 := bstep (se 1 (by rfl) ⟨996938, by rfl⟩ : syracuseStep 1329251 = 1993877) B1993877
theorem B8407153 : Blo 884570 8407153 := bstep (se 2 (by rfl) ⟨3152682, by rfl⟩ : syracuseStep 8407153 = 6305365) B6305365
theorem B1329281 : Blo 884570 1329281 := bstep (se 2 (by rfl) ⟨498480, by rfl⟩ : syracuseStep 1329281 = 996961) B996961
theorem B8505485 : Blo 884570 8505485 := bstep (se 3 (by rfl) ⟨1594778, by rfl⟩ : syracuseStep 8505485 = 3189557) B3189557
theorem B1329299 : Blo 884570 1329299 := bstep (se 1 (by rfl) ⟨996974, by rfl⟩ : syracuseStep 1329299 = 1993949) B1993949
theorem B1329329 : Blo 884570 1329329 := bstep (se 2 (by rfl) ⟨498498, by rfl⟩ : syracuseStep 1329329 = 996997) B996997
theorem B1329347 : Blo 884570 1329347 := bstep (se 1 (by rfl) ⟨997010, by rfl⟩ : syracuseStep 1329347 = 1994021) B1994021
theorem B1493201 : Blo 884570 1493201 := bstep (se 2 (by rfl) ⟨559950, by rfl⟩ : syracuseStep 1493201 = 1119901) B1119901
theorem B1329377 : Blo 884570 1329377 := bstep (se 2 (by rfl) ⟨498516, by rfl⟩ : syracuseStep 1329377 = 997033) B997033
theorem B1329395 : Blo 884570 1329395 := bstep (se 1 (by rfl) ⟨997046, by rfl⟩ : syracuseStep 1329395 = 1994093) B1994093
theorem B1329425 : Blo 884570 1329425 := bstep (se 2 (by rfl) ⟨498534, by rfl⟩ : syracuseStep 1329425 = 997069) B997069
theorem B1329443 : Blo 884570 1329443 := bstep (se 1 (by rfl) ⟨997082, by rfl⟩ : syracuseStep 1329443 = 1994165) B1994165
theorem B1329473 : Blo 884570 1329473 := bstep (se 2 (by rfl) ⟨498552, by rfl⟩ : syracuseStep 1329473 = 997105) B997105
theorem B1493329 : Blo 884570 1493329 := bstep (se 2 (by rfl) ⟨559998, by rfl⟩ : syracuseStep 1493329 = 1119997) B1119997
theorem B1329491 : Blo 884570 1329491 := bstep (se 1 (by rfl) ⟨997118, by rfl⟩ : syracuseStep 1329491 = 1994237) B1994237
theorem B2247011 : Blo 884570 2247011 := bstep (se 1 (by rfl) ⟨1685258, by rfl⟩ : syracuseStep 2247011 = 3370517) B3370517
theorem B1329521 : Blo 884570 1329521 := bstep (se 2 (by rfl) ⟨498570, by rfl⟩ : syracuseStep 1329521 = 997141) B997141
theorem B1493363 : Blo 884570 1493363 := bstep (se 1 (by rfl) ⟨1120022, by rfl⟩ : syracuseStep 1493363 = 2240045) B2240045
theorem B1329539 : Blo 884570 1329539 := bstep (se 1 (by rfl) ⟨997154, by rfl⟩ : syracuseStep 1329539 = 1994309) B1994309
theorem B2738573 : Blo 884570 2738573 := bstep (se 3 (by rfl) ⟨513482, by rfl⟩ : syracuseStep 2738573 = 1026965) B1026965
theorem B1329569 : Blo 884570 1329569 := bstep (se 2 (by rfl) ⟨498588, by rfl⟩ : syracuseStep 1329569 = 997177) B997177
theorem B1329587 : Blo 884570 1329587 := bstep (se 1 (by rfl) ⟨997190, by rfl⟩ : syracuseStep 1329587 = 1994381) B1994381
theorem B1329617 : Blo 884570 1329617 := bstep (se 2 (by rfl) ⟨498606, by rfl⟩ : syracuseStep 1329617 = 997213) B997213
theorem B1264081 : Blo 884570 1264081 := bstep (se 2 (by rfl) ⟨474030, by rfl⟩ : syracuseStep 1264081 = 948061) B948061
theorem B1329635 : Blo 884570 1329635 := bstep (se 1 (by rfl) ⟨997226, by rfl⟩ : syracuseStep 1329635 = 1994453) B1994453
theorem B1493491 : Blo 884570 1493491 := bstep (se 1 (by rfl) ⟨1120118, by rfl⟩ : syracuseStep 1493491 = 2240237) B2240237
theorem B1329665 : Blo 884570 1329665 := bstep (se 2 (by rfl) ⟨498624, by rfl⟩ : syracuseStep 1329665 = 997249) B997249
theorem B1329683 : Blo 884570 1329683 := bstep (se 1 (by rfl) ⟨997262, by rfl⟩ : syracuseStep 1329683 = 1994525) B1994525
theorem B2247203 : Blo 884570 2247203 := bstep (se 1 (by rfl) ⟨1685402, by rfl⟩ : syracuseStep 2247203 = 3370805) B3370805
theorem B1329713 : Blo 884570 1329713 := bstep (se 2 (by rfl) ⟨498642, by rfl⟩ : syracuseStep 1329713 = 997285) B997285
theorem B1264177 : Blo 884570 1264177 := bstep (se 2 (by rfl) ⟨474066, by rfl⟩ : syracuseStep 1264177 = 948133) B948133
theorem B1329731 : Blo 884570 1329731 := bstep (se 1 (by rfl) ⟨997298, by rfl⟩ : syracuseStep 1329731 = 1994597) B1994597
theorem B1329761 : Blo 884570 1329761 := bstep (se 2 (by rfl) ⟨498660, by rfl⟩ : syracuseStep 1329761 = 997321) B997321
theorem B1329779 : Blo 884570 1329779 := bstep (se 1 (by rfl) ⟨997334, by rfl⟩ : syracuseStep 1329779 = 1994669) B1994669
theorem B1493633 : Blo 884570 1493633 := bstep (se 2 (by rfl) ⟨560112, by rfl⟩ : syracuseStep 1493633 = 1120225) B1120225
theorem B1460867 : Blo 884570 1460867 := bstep (se 1 (by rfl) ⟨1095650, by rfl⟩ : syracuseStep 1460867 = 2191301) B2191301
theorem B1329809 : Blo 884570 1329809 := bstep (se 2 (by rfl) ⟨498678, by rfl⟩ : syracuseStep 1329809 = 997357) B997357
theorem B1329827 : Blo 884570 1329827 := bstep (se 1 (by rfl) ⟨997370, by rfl⟩ : syracuseStep 1329827 = 1994741) B1994741
theorem B1329857 : Blo 884570 1329857 := bstep (se 2 (by rfl) ⟨498696, by rfl⟩ : syracuseStep 1329857 = 997393) B997393
theorem B1329875 : Blo 884570 1329875 := bstep (se 1 (by rfl) ⟨997406, by rfl⟩ : syracuseStep 1329875 = 1994813) B1994813
theorem B1329905 : Blo 884570 1329905 := bstep (se 2 (by rfl) ⟨498714, by rfl⟩ : syracuseStep 1329905 = 997429) B997429
theorem B1493761 : Blo 884570 1493761 := bstep (se 2 (by rfl) ⟨560160, by rfl⟩ : syracuseStep 1493761 = 1120321) B1120321
theorem B1329923 : Blo 884570 1329923 := bstep (se 1 (by rfl) ⟨997442, by rfl⟩ : syracuseStep 1329923 = 1994885) B1994885
theorem B1329953 : Blo 884570 1329953 := bstep (se 2 (by rfl) ⟨498732, by rfl⟩ : syracuseStep 1329953 = 997465) B997465
theorem B1493795 : Blo 884570 1493795 := bstep (se 1 (by rfl) ⟨1120346, by rfl⟩ : syracuseStep 1493795 = 2240693) B2240693
theorem B3361571 : Blo 884570 3361571 := bstep (se 1 (by rfl) ⟨2521178, by rfl⟩ : syracuseStep 3361571 = 5042357) B5042357
theorem B1329971 : Blo 884570 1329971 := bstep (se 1 (by rfl) ⟨997478, by rfl⟩ : syracuseStep 1329971 = 1994957) B1994957
theorem B1330001 : Blo 884570 1330001 := bstep (se 2 (by rfl) ⟨498750, by rfl⟩ : syracuseStep 1330001 = 997501) B997501
theorem B1330019 : Blo 884570 1330019 := bstep (se 1 (by rfl) ⟨997514, by rfl⟩ : syracuseStep 1330019 = 1995029) B1995029
theorem B1330049 : Blo 884570 1330049 := bstep (se 2 (by rfl) ⟨498768, by rfl⟩ : syracuseStep 1330049 = 997537) B997537
theorem B1330067 : Blo 884570 1330067 := bstep (se 1 (by rfl) ⟨997550, by rfl⟩ : syracuseStep 1330067 = 1995101) B1995101
theorem B1493923 : Blo 884570 1493923 := bstep (se 1 (by rfl) ⟨1120442, by rfl⟩ : syracuseStep 1493923 = 2240885) B2240885
theorem B1330097 : Blo 884570 1330097 := bstep (se 2 (by rfl) ⟨498786, by rfl⟩ : syracuseStep 1330097 = 997573) B997573
theorem B1330115 : Blo 884570 1330115 := bstep (se 1 (by rfl) ⟨997586, by rfl⟩ : syracuseStep 1330115 = 1995173) B1995173
theorem B1330145 : Blo 884570 1330145 := bstep (se 2 (by rfl) ⟨498804, by rfl⟩ : syracuseStep 1330145 = 997609) B997609
theorem B1330163 : Blo 884570 1330163 := bstep (se 1 (by rfl) ⟨997622, by rfl⟩ : syracuseStep 1330163 = 1995245) B1995245
theorem B1330193 : Blo 884570 1330193 := bstep (se 2 (by rfl) ⟨498822, by rfl⟩ : syracuseStep 1330193 = 997645) B997645
theorem B1264673 : Blo 884570 1264673 := bstep (se 2 (by rfl) ⟨474252, by rfl⟩ : syracuseStep 1264673 = 948505) B948505
theorem B1330211 : Blo 884570 1330211 := bstep (se 1 (by rfl) ⟨997658, by rfl⟩ : syracuseStep 1330211 = 1995317) B1995317
theorem B1494065 : Blo 884570 1494065 := bstep (se 2 (by rfl) ⟨560274, by rfl⟩ : syracuseStep 1494065 = 1120549) B1120549
theorem B1330241 : Blo 884570 1330241 := bstep (se 2 (by rfl) ⟨498840, by rfl⟩ : syracuseStep 1330241 = 997681) B997681
theorem B1199171 : Blo 884570 1199171 := bstep (se 1 (by rfl) ⟨899378, by rfl⟩ : syracuseStep 1199171 = 1798757) B1798757
theorem B1330259 : Blo 884570 1330259 := bstep (se 1 (by rfl) ⟨997694, by rfl⟩ : syracuseStep 1330259 = 1995389) B1995389
theorem B1330289 : Blo 884570 1330289 := bstep (se 2 (by rfl) ⟨498858, by rfl⟩ : syracuseStep 1330289 = 997717) B997717
theorem B1330307 : Blo 884570 1330307 := bstep (se 1 (by rfl) ⟨997730, by rfl⟩ : syracuseStep 1330307 = 1995461) B1995461
theorem B1330337 : Blo 884570 1330337 := bstep (se 2 (by rfl) ⟨498876, by rfl⟩ : syracuseStep 1330337 = 997753) B997753
theorem B1494193 : Blo 884570 1494193 := bstep (se 2 (by rfl) ⟨560322, by rfl⟩ : syracuseStep 1494193 = 1120645) B1120645
theorem B1330355 : Blo 884570 1330355 := bstep (se 1 (by rfl) ⟨997766, by rfl⟩ : syracuseStep 1330355 = 1995533) B1995533
theorem B1330385 : Blo 884570 1330385 := bstep (se 2 (by rfl) ⟨498894, by rfl⟩ : syracuseStep 1330385 = 997789) B997789
theorem B1494227 : Blo 884570 1494227 := bstep (se 1 (by rfl) ⟨1120670, by rfl⟩ : syracuseStep 1494227 = 2241341) B2241341
theorem B1330403 : Blo 884570 1330403 := bstep (se 1 (by rfl) ⟨997802, by rfl⟩ : syracuseStep 1330403 = 1995605) B1995605
theorem B1330433 : Blo 884570 1330433 := bstep (se 2 (by rfl) ⟨498912, by rfl⟩ : syracuseStep 1330433 = 997825) B997825
theorem B1330451 : Blo 884570 1330451 := bstep (se 1 (by rfl) ⟨997838, by rfl⟩ : syracuseStep 1330451 = 1995677) B1995677
theorem B1330481 : Blo 884570 1330481 := bstep (se 2 (by rfl) ⟨498930, by rfl⟩ : syracuseStep 1330481 = 997861) B997861
theorem B1330499 : Blo 884570 1330499 := bstep (se 1 (by rfl) ⟨997874, by rfl⟩ : syracuseStep 1330499 = 1995749) B1995749
theorem B1494355 : Blo 884570 1494355 := bstep (se 1 (by rfl) ⟨1120766, by rfl⟩ : syracuseStep 1494355 = 2241533) B2241533
theorem B1330529 : Blo 884570 1330529 := bstep (se 2 (by rfl) ⟨498948, by rfl⟩ : syracuseStep 1330529 = 997897) B997897
theorem B8539505 : Blo 884570 8539505 := bstep (se 2 (by rfl) ⟨3202314, by rfl⟩ : syracuseStep 8539505 = 6404629) B6404629
theorem B1330547 : Blo 884570 1330547 := bstep (se 1 (by rfl) ⟨997910, by rfl⟩ : syracuseStep 1330547 = 1995821) B1995821
theorem B1330577 : Blo 884570 1330577 := bstep (se 2 (by rfl) ⟨498966, by rfl⟩ : syracuseStep 1330577 = 997933) B997933
theorem B1330595 : Blo 884570 1330595 := bstep (se 1 (by rfl) ⟨997946, by rfl⟩ : syracuseStep 1330595 = 1995893) B1995893
theorem B1330625 : Blo 884570 1330625 := bstep (se 2 (by rfl) ⟨498984, by rfl⟩ : syracuseStep 1330625 = 997969) B997969
theorem B5393861 : Blo 884570 5393861 := bstep (se 4 (by rfl) ⟨505674, by rfl⟩ : syracuseStep 5393861 = 1011349) B1011349
theorem B2248145 : Blo 884570 2248145 := bstep (se 2 (by rfl) ⟨843054, by rfl⟩ : syracuseStep 2248145 = 1686109) B1686109
theorem B1330643 : Blo 884570 1330643 := bstep (se 1 (by rfl) ⟨997982, by rfl⟩ : syracuseStep 1330643 = 1995965) B1995965
theorem B1494497 : Blo 884570 1494497 := bstep (se 2 (by rfl) ⟨560436, by rfl⟩ : syracuseStep 1494497 = 1120873) B1120873
theorem B1330673 : Blo 884570 1330673 := bstep (se 2 (by rfl) ⟨499002, by rfl⟩ : syracuseStep 1330673 = 998005) B998005
theorem B1330691 : Blo 884570 1330691 := bstep (se 1 (by rfl) ⟨998018, by rfl⟩ : syracuseStep 1330691 = 1996037) B1996037
theorem B2248195 : Blo 884570 2248195 := bstep (se 1 (by rfl) ⟨1686146, by rfl⟩ : syracuseStep 2248195 = 3372293) B3372293
theorem B1330721 : Blo 884570 1330721 := bstep (se 2 (by rfl) ⟨499020, by rfl⟩ : syracuseStep 1330721 = 998041) B998041
theorem B1330739 : Blo 884570 1330739 := bstep (se 1 (by rfl) ⟨998054, by rfl⟩ : syracuseStep 1330739 = 1996109) B1996109
theorem B1330769 : Blo 884570 1330769 := bstep (se 2 (by rfl) ⟨499038, by rfl⟩ : syracuseStep 1330769 = 998077) B998077
theorem B1494625 : Blo 884570 1494625 := bstep (se 2 (by rfl) ⟨560484, by rfl⟩ : syracuseStep 1494625 = 1120969) B1120969
theorem B1330787 : Blo 884570 1330787 := bstep (se 1 (by rfl) ⟨998090, by rfl⟩ : syracuseStep 1330787 = 1996181) B1996181
theorem B1330817 : Blo 884570 1330817 := bstep (se 2 (by rfl) ⟨499056, by rfl⟩ : syracuseStep 1330817 = 998113) B998113
theorem B1494659 : Blo 884570 1494659 := bstep (se 1 (by rfl) ⟨1120994, by rfl⟩ : syracuseStep 1494659 = 2241989) B2241989
theorem B2248337 : Blo 884570 2248337 := bstep (se 2 (by rfl) ⟨843126, by rfl⟩ : syracuseStep 2248337 = 1686253) B1686253
theorem B1330835 : Blo 884570 1330835 := bstep (se 1 (by rfl) ⟨998126, by rfl⟩ : syracuseStep 1330835 = 1996253) B1996253
theorem B1330865 : Blo 884570 1330865 := bstep (se 2 (by rfl) ⟨499074, by rfl⟩ : syracuseStep 1330865 = 998149) B998149
theorem B1330883 : Blo 884570 1330883 := bstep (se 1 (by rfl) ⟨998162, by rfl⟩ : syracuseStep 1330883 = 1996325) B1996325
theorem B1330913 : Blo 884570 1330913 := bstep (se 2 (by rfl) ⟨499092, by rfl⟩ : syracuseStep 1330913 = 998185) B998185
theorem B1330931 : Blo 884570 1330931 := bstep (se 1 (by rfl) ⟨998198, by rfl⟩ : syracuseStep 1330931 = 1996397) B1996397
theorem B1494787 : Blo 884570 1494787 := bstep (se 1 (by rfl) ⟨1121090, by rfl⟩ : syracuseStep 1494787 = 2242181) B2242181
theorem B3362573 : Blo 884570 3362573 := bstep (se 3 (by rfl) ⟨630482, by rfl⟩ : syracuseStep 3362573 = 1260965) B1260965
theorem B1330961 : Blo 884570 1330961 := bstep (se 2 (by rfl) ⟨499110, by rfl⟩ : syracuseStep 1330961 = 998221) B998221
theorem B1330979 : Blo 884570 1330979 := bstep (se 1 (by rfl) ⟨998234, by rfl⟩ : syracuseStep 1330979 = 1996469) B1996469
theorem B1331009 : Blo 884570 1331009 := bstep (se 2 (by rfl) ⟨499128, by rfl⟩ : syracuseStep 1331009 = 998257) B998257
theorem B1331027 : Blo 884570 1331027 := bstep (se 1 (by rfl) ⟨998270, by rfl⟩ : syracuseStep 1331027 = 1996541) B1996541
theorem B1363811 : Blo 884570 1363811 := bstep (se 1 (by rfl) ⟨1022858, by rfl⟩ : syracuseStep 1363811 = 2045717) B2045717
theorem B1331057 : Blo 884570 1331057 := bstep (se 2 (by rfl) ⟨499146, by rfl⟩ : syracuseStep 1331057 = 998293) B998293
theorem B1331075 : Blo 884570 1331075 := bstep (se 1 (by rfl) ⟨998306, by rfl⟩ : syracuseStep 1331075 = 1996613) B1996613
theorem B1494929 : Blo 884570 1494929 := bstep (se 2 (by rfl) ⟨560598, by rfl⟩ : syracuseStep 1494929 = 1121197) B1121197
theorem B1331105 : Blo 884570 1331105 := bstep (se 2 (by rfl) ⟨499164, by rfl⟩ : syracuseStep 1331105 = 998329) B998329
theorem B1331123 : Blo 884570 1331123 := bstep (se 1 (by rfl) ⟨998342, by rfl⟩ : syracuseStep 1331123 = 1996685) B1996685
theorem B1331153 : Blo 884570 1331153 := bstep (se 2 (by rfl) ⟨499182, by rfl⟩ : syracuseStep 1331153 = 998365) B998365
theorem B1331171 : Blo 884570 1331171 := bstep (se 1 (by rfl) ⟨998378, by rfl⟩ : syracuseStep 1331171 = 1996757) B1996757
theorem B1331201 : Blo 884570 1331201 := bstep (se 2 (by rfl) ⟨499200, by rfl⟩ : syracuseStep 1331201 = 998401) B998401
theorem B1495057 : Blo 884570 1495057 := bstep (se 2 (by rfl) ⟨560646, by rfl⟩ : syracuseStep 1495057 = 1121293) B1121293
theorem B1331219 : Blo 884570 1331219 := bstep (se 1 (by rfl) ⟨998414, by rfl⟩ : syracuseStep 1331219 = 1996829) B1996829
theorem B1331249 : Blo 884570 1331249 := bstep (se 2 (by rfl) ⟨499218, by rfl⟩ : syracuseStep 1331249 = 998437) B998437
theorem B1495091 : Blo 884570 1495091 := bstep (se 1 (by rfl) ⟨1121318, by rfl⟩ : syracuseStep 1495091 = 2242637) B2242637
theorem B1331267 : Blo 884570 1331267 := bstep (se 1 (by rfl) ⟨998450, by rfl⟩ : syracuseStep 1331267 = 1996901) B1996901
theorem B1331297 : Blo 884570 1331297 := bstep (se 2 (by rfl) ⟨499236, by rfl⟩ : syracuseStep 1331297 = 998473) B998473
theorem B1331315 : Blo 884570 1331315 := bstep (se 1 (by rfl) ⟨998486, by rfl⟩ : syracuseStep 1331315 = 1996973) B1996973
theorem B1921169 : Blo 884570 1921169 := bstep (se 2 (by rfl) ⟨720438, by rfl⟩ : syracuseStep 1921169 = 1440877) B1440877
theorem B1331345 : Blo 884570 1331345 := bstep (se 2 (by rfl) ⟨499254, by rfl⟩ : syracuseStep 1331345 = 998509) B998509
theorem B3788963 : Blo 884570 3788963 := bstep (se 1 (by rfl) ⟨2841722, by rfl⟩ : syracuseStep 3788963 = 5683445) B5683445
theorem B1331363 : Blo 884570 1331363 := bstep (se 1 (by rfl) ⟨998522, by rfl⟩ : syracuseStep 1331363 = 1997045) B1997045
theorem B1495219 : Blo 884570 1495219 := bstep (se 1 (by rfl) ⟨1121414, by rfl⟩ : syracuseStep 1495219 = 2242829) B2242829
theorem B1331393 : Blo 884570 1331393 := bstep (se 2 (by rfl) ⟨499272, by rfl⟩ : syracuseStep 1331393 = 998545) B998545
theorem B1331411 : Blo 884570 1331411 := bstep (se 1 (by rfl) ⟨998558, by rfl⟩ : syracuseStep 1331411 = 1997117) B1997117
theorem B1331441 : Blo 884570 1331441 := bstep (se 2 (by rfl) ⟨499290, by rfl⟩ : syracuseStep 1331441 = 998581) B998581
theorem B1331459 : Blo 884570 1331459 := bstep (se 1 (by rfl) ⟨998594, by rfl⟩ : syracuseStep 1331459 = 1997189) B1997189
theorem B1331489 : Blo 884570 1331489 := bstep (se 2 (by rfl) ⟨499308, by rfl⟩ : syracuseStep 1331489 = 998617) B998617
theorem B1331507 : Blo 884570 1331507 := bstep (se 1 (by rfl) ⟨998630, by rfl⟩ : syracuseStep 1331507 = 1997261) B1997261
theorem B1495361 : Blo 884570 1495361 := bstep (se 2 (by rfl) ⟨560760, by rfl⟩ : syracuseStep 1495361 = 1121521) B1121521
theorem B5394757 : Blo 884570 5394757 := bstep (se 4 (by rfl) ⟨505758, by rfl⟩ : syracuseStep 5394757 = 1011517) B1011517
theorem B1331537 : Blo 884570 1331537 := bstep (se 2 (by rfl) ⟨499326, by rfl⟩ : syracuseStep 1331537 = 998653) B998653
theorem B10080611 : Blo 884570 10080611 := bstep (se 1 (by rfl) ⟨7560458, by rfl⟩ : syracuseStep 10080611 = 15120917) B15120917
theorem B1331555 : Blo 884570 1331555 := bstep (se 1 (by rfl) ⟨998666, by rfl⟩ : syracuseStep 1331555 = 1997333) B1997333
theorem B7590257 : Blo 884570 7590257 := bstep (se 2 (by rfl) ⟨2846346, by rfl⟩ : syracuseStep 7590257 = 5692693) B5692693
theorem B1331585 : Blo 884570 1331585 := bstep (se 2 (by rfl) ⟨499344, by rfl⟩ : syracuseStep 1331585 = 998689) B998689
theorem B1331603 : Blo 884570 1331603 := bstep (se 1 (by rfl) ⟨998702, by rfl⟩ : syracuseStep 1331603 = 1997405) B1997405
theorem B1331633 : Blo 884570 1331633 := bstep (se 2 (by rfl) ⟨499362, by rfl⟩ : syracuseStep 1331633 = 998725) B998725
theorem B1495489 : Blo 884570 1495489 := bstep (se 2 (by rfl) ⟨560808, by rfl⟩ : syracuseStep 1495489 = 1121617) B1121617
theorem B1331651 : Blo 884570 1331651 := bstep (se 1 (by rfl) ⟨998738, by rfl⟩ : syracuseStep 1331651 = 1997477) B1997477
theorem B1331681 : Blo 884570 1331681 := bstep (se 2 (by rfl) ⟨499380, by rfl⟩ : syracuseStep 1331681 = 998761) B998761
theorem B1495523 : Blo 884570 1495523 := bstep (se 1 (by rfl) ⟨1121642, by rfl⟩ : syracuseStep 1495523 = 2243285) B2243285
theorem B1331699 : Blo 884570 1331699 := bstep (se 1 (by rfl) ⟨998774, by rfl⟩ : syracuseStep 1331699 = 1997549) B1997549
theorem B1331729 : Blo 884570 1331729 := bstep (se 2 (by rfl) ⟨499398, by rfl⟩ : syracuseStep 1331729 = 998797) B998797
theorem B1331747 : Blo 884570 1331747 := bstep (se 1 (by rfl) ⟨998810, by rfl⟩ : syracuseStep 1331747 = 1997621) B1997621
theorem B1331777 : Blo 884570 1331777 := bstep (se 2 (by rfl) ⟨499416, by rfl⟩ : syracuseStep 1331777 = 998833) B998833
theorem B2839121 : Blo 884570 2839121 := bstep (se 2 (by rfl) ⟨1064670, by rfl⟩ : syracuseStep 2839121 = 2129341) B2129341
theorem B1331795 : Blo 884570 1331795 := bstep (se 1 (by rfl) ⟨998846, by rfl⟩ : syracuseStep 1331795 = 1997693) B1997693
theorem B1495651 : Blo 884570 1495651 := bstep (se 1 (by rfl) ⟨1121738, by rfl⟩ : syracuseStep 1495651 = 2243477) B2243477
theorem B1200739 : Blo 884570 1200739 := bstep (se 1 (by rfl) ⟨900554, by rfl⟩ : syracuseStep 1200739 = 1801109) B1801109
theorem B1331825 : Blo 884570 1331825 := bstep (se 2 (by rfl) ⟨499434, by rfl⟩ : syracuseStep 1331825 = 998869) B998869
theorem B2839171 : Blo 884570 2839171 := bstep (se 1 (by rfl) ⟨2129378, by rfl⟩ : syracuseStep 2839171 = 4258757) B4258757
theorem B1331843 : Blo 884570 1331843 := bstep (se 1 (by rfl) ⟨998882, by rfl⟩ : syracuseStep 1331843 = 1997765) B1997765
theorem B1331873 : Blo 884570 1331873 := bstep (se 2 (by rfl) ⟨499452, by rfl⟩ : syracuseStep 1331873 = 998905) B998905
theorem B1331891 : Blo 884570 1331891 := bstep (se 1 (by rfl) ⟨998918, by rfl⟩ : syracuseStep 1331891 = 1997837) B1997837
theorem B1331921 : Blo 884570 1331921 := bstep (se 2 (by rfl) ⟨499470, by rfl⟩ : syracuseStep 1331921 = 998941) B998941
theorem B1331939 : Blo 884570 1331939 := bstep (se 1 (by rfl) ⟨998954, by rfl⟩ : syracuseStep 1331939 = 1997909) B1997909
theorem B1495793 : Blo 884570 1495793 := bstep (se 2 (by rfl) ⟨560922, by rfl⟩ : syracuseStep 1495793 = 1121845) B1121845
theorem B1331969 : Blo 884570 1331969 := bstep (se 2 (by rfl) ⟨499488, by rfl⟩ : syracuseStep 1331969 = 998977) B998977
theorem B1331987 : Blo 884570 1331987 := bstep (se 1 (by rfl) ⟨998990, by rfl⟩ : syracuseStep 1331987 = 1997981) B1997981
theorem B1332017 : Blo 884570 1332017 := bstep (se 2 (by rfl) ⟨499506, by rfl⟩ : syracuseStep 1332017 = 999013) B999013
theorem B1332035 : Blo 884570 1332035 := bstep (se 1 (by rfl) ⟨999026, by rfl⟩ : syracuseStep 1332035 = 1998053) B1998053
theorem B1332065 : Blo 884570 1332065 := bstep (se 2 (by rfl) ⟨499524, by rfl⟩ : syracuseStep 1332065 = 999049) B999049
theorem B1495921 : Blo 884570 1495921 := bstep (se 2 (by rfl) ⟨560970, by rfl⟩ : syracuseStep 1495921 = 1121941) B1121941
theorem B1332083 : Blo 884570 1332083 := bstep (se 1 (by rfl) ⟨999062, by rfl⟩ : syracuseStep 1332083 = 1998125) B1998125
theorem B1332113 : Blo 884570 1332113 := bstep (se 2 (by rfl) ⟨499542, by rfl⟩ : syracuseStep 1332113 = 999085) B999085
theorem B1495955 : Blo 884570 1495955 := bstep (se 1 (by rfl) ⟨1121966, by rfl⟩ : syracuseStep 1495955 = 2243933) B2243933
theorem B1332131 : Blo 884570 1332131 := bstep (se 1 (by rfl) ⟨999098, by rfl⟩ : syracuseStep 1332131 = 1998197) B1998197
theorem B1332161 : Blo 884570 1332161 := bstep (se 2 (by rfl) ⟨499560, by rfl⟩ : syracuseStep 1332161 = 999121) B999121
theorem B1889219 : Blo 884570 1889219 := bstep (se 1 (by rfl) ⟨1416914, by rfl⟩ : syracuseStep 1889219 = 2833829) B2833829
theorem B1332179 : Blo 884570 1332179 := bstep (se 1 (by rfl) ⟨999134, by rfl⟩ : syracuseStep 1332179 = 1998269) B1998269
theorem B1332209 : Blo 884570 1332209 := bstep (se 2 (by rfl) ⟨499578, by rfl⟩ : syracuseStep 1332209 = 999157) B999157
theorem B1332227 : Blo 884570 1332227 := bstep (se 1 (by rfl) ⟨999170, by rfl⟩ : syracuseStep 1332227 = 1998341) B1998341
theorem B1496083 : Blo 884570 1496083 := bstep (se 1 (by rfl) ⟨1122062, by rfl⟩ : syracuseStep 1496083 = 2244125) B2244125
theorem B1332257 : Blo 884570 1332257 := bstep (se 2 (by rfl) ⟨499596, by rfl⟩ : syracuseStep 1332257 = 999193) B999193
theorem B1332275 : Blo 884570 1332275 := bstep (se 1 (by rfl) ⟨999206, by rfl⟩ : syracuseStep 1332275 = 1998413) B1998413
theorem B1332305 : Blo 884570 1332305 := bstep (se 2 (by rfl) ⟨499614, by rfl⟩ : syracuseStep 1332305 = 999229) B999229
theorem B1332323 : Blo 884570 1332323 := bstep (se 1 (by rfl) ⟨999242, by rfl⟩ : syracuseStep 1332323 = 1998485) B1998485
theorem B1332353 : Blo 884570 1332353 := bstep (se 2 (by rfl) ⟨499632, by rfl⟩ : syracuseStep 1332353 = 999265) B999265
theorem B1332371 : Blo 884570 1332371 := bstep (se 1 (by rfl) ⟨999278, by rfl⟩ : syracuseStep 1332371 = 1998557) B1998557
theorem B1496225 : Blo 884570 1496225 := bstep (se 2 (by rfl) ⟨561084, by rfl⟩ : syracuseStep 1496225 = 1122169) B1122169
theorem B3593393 : Blo 884570 3593393 := bstep (se 2 (by rfl) ⟨1347522, by rfl⟩ : syracuseStep 3593393 = 2695045) B2695045
theorem B1922225 : Blo 884570 1922225 := bstep (se 2 (by rfl) ⟨720834, by rfl⟩ : syracuseStep 1922225 = 1441669) B1441669
theorem B1332401 : Blo 884570 1332401 := bstep (se 2 (by rfl) ⟨499650, by rfl⟩ : syracuseStep 1332401 = 999301) B999301
theorem B1332419 : Blo 884570 1332419 := bstep (se 1 (by rfl) ⟨999314, by rfl⟩ : syracuseStep 1332419 = 1998629) B1998629
theorem B1332449 : Blo 884570 1332449 := bstep (se 2 (by rfl) ⟨499668, by rfl⟩ : syracuseStep 1332449 = 999337) B999337
theorem B1332467 : Blo 884570 1332467 := bstep (se 1 (by rfl) ⟨999350, by rfl⟩ : syracuseStep 1332467 = 1998701) B1998701
theorem B1332497 : Blo 884570 1332497 := bstep (se 2 (by rfl) ⟨499686, by rfl⟩ : syracuseStep 1332497 = 999373) B999373
theorem B1496353 : Blo 884570 1496353 := bstep (se 2 (by rfl) ⟨561132, by rfl⟩ : syracuseStep 1496353 = 1122265) B1122265
theorem B1332515 : Blo 884570 1332515 := bstep (se 1 (by rfl) ⟨999386, by rfl⟩ : syracuseStep 1332515 = 1998773) B1998773
theorem B1332545 : Blo 884570 1332545 := bstep (se 2 (by rfl) ⟨499704, by rfl⟩ : syracuseStep 1332545 = 999409) B999409
theorem B1496387 : Blo 884570 1496387 := bstep (se 1 (by rfl) ⟨1122290, by rfl⟩ : syracuseStep 1496387 = 2244581) B2244581
theorem B5199173 : Blo 884570 5199173 := bstep (se 4 (by rfl) ⟨487422, by rfl⟩ : syracuseStep 5199173 = 974845) B974845
theorem B1332563 : Blo 884570 1332563 := bstep (se 1 (by rfl) ⟨999422, by rfl⟩ : syracuseStep 1332563 = 1998845) B1998845
theorem B1332593 : Blo 884570 1332593 := bstep (se 2 (by rfl) ⟨499722, by rfl⟩ : syracuseStep 1332593 = 999445) B999445
theorem B1332611 : Blo 884570 1332611 := bstep (se 1 (by rfl) ⟨999458, by rfl⟩ : syracuseStep 1332611 = 1998917) B1998917
theorem B1332641 : Blo 884570 1332641 := bstep (se 2 (by rfl) ⟨499740, by rfl⟩ : syracuseStep 1332641 = 999481) B999481
theorem B1332659 : Blo 884570 1332659 := bstep (se 1 (by rfl) ⟨999494, by rfl⟩ : syracuseStep 1332659 = 1998989) B1998989
theorem B1496515 : Blo 884570 1496515 := bstep (se 1 (by rfl) ⟨1122386, by rfl⟩ : syracuseStep 1496515 = 2244773) B2244773
theorem B2840017 : Blo 884570 2840017 := bstep (se 2 (by rfl) ⟨1065006, by rfl⟩ : syracuseStep 2840017 = 2130013) B2130013
theorem B1332689 : Blo 884570 1332689 := bstep (se 2 (by rfl) ⟨499758, by rfl⟩ : syracuseStep 1332689 = 999517) B999517
theorem B1332707 : Blo 884570 1332707 := bstep (se 1 (by rfl) ⟨999530, by rfl⟩ : syracuseStep 1332707 = 1999061) B1999061
theorem B1332737 : Blo 884570 1332737 := bstep (se 2 (by rfl) ⟨499776, by rfl⟩ : syracuseStep 1332737 = 999553) B999553
theorem B1332755 : Blo 884570 1332755 := bstep (se 1 (by rfl) ⟨999566, by rfl⟩ : syracuseStep 1332755 = 1999133) B1999133
theorem B1332785 : Blo 884570 1332785 := bstep (se 2 (by rfl) ⟨499794, by rfl⟩ : syracuseStep 1332785 = 999589) B999589
theorem B1332803 : Blo 884570 1332803 := bstep (se 1 (by rfl) ⟨999602, by rfl⟩ : syracuseStep 1332803 = 1999205) B1999205
theorem B1496657 : Blo 884570 1496657 := bstep (se 2 (by rfl) ⟨561246, by rfl⟩ : syracuseStep 1496657 = 1122493) B1122493
theorem B1332833 : Blo 884570 1332833 := bstep (se 2 (by rfl) ⟨499812, by rfl⟩ : syracuseStep 1332833 = 999625) B999625
theorem B1332851 : Blo 884570 1332851 := bstep (se 1 (by rfl) ⟨999638, by rfl⟩ : syracuseStep 1332851 = 1999277) B1999277
theorem B1496785 : Blo 884570 1496785 := bstep (se 2 (by rfl) ⟨561294, by rfl⟩ : syracuseStep 1496785 = 1122589) B1122589
theorem B1496819 : Blo 884570 1496819 := bstep (se 1 (by rfl) ⟨1122614, by rfl⟩ : syracuseStep 1496819 = 2245229) B2245229
theorem B3364685 : Blo 884570 3364685 := bstep (se 3 (by rfl) ⟨630878, by rfl⟩ : syracuseStep 3364685 = 1261757) B1261757
theorem B1496947 : Blo 884570 1496947 := bstep (se 1 (by rfl) ⟨1122710, by rfl⟩ : syracuseStep 1496947 = 2245421) B2245421
theorem B1497089 : Blo 884570 1497089 := bstep (se 2 (by rfl) ⟨561408, by rfl⟩ : syracuseStep 1497089 = 1122817) B1122817
theorem B4544561 : Blo 884570 4544561 := bstep (se 2 (by rfl) ⟨1704210, by rfl⟩ : syracuseStep 4544561 = 3408421) B3408421
theorem B3790961 : Blo 884570 3790961 := bstep (se 2 (by rfl) ⟨1421610, by rfl⟩ : syracuseStep 3790961 = 2843221) B2843221
theorem B1497217 : Blo 884570 1497217 := bstep (se 2 (by rfl) ⟨561456, by rfl⟩ : syracuseStep 1497217 = 1122913) B1122913
theorem B5462149 : Blo 884570 5462149 := bstep (se 4 (by rfl) ⟨512076, by rfl⟩ : syracuseStep 5462149 = 1024153) B1024153
theorem B6379661 : Blo 884570 6379661 := bstep (se 3 (by rfl) ⟨1196186, by rfl⟩ : syracuseStep 6379661 = 2392373) B2392373
theorem B1890449 : Blo 884570 1890449 := bstep (se 2 (by rfl) ⟨708918, by rfl⟩ : syracuseStep 1890449 = 1417837) B1417837
theorem B1497251 : Blo 884570 1497251 := bstep (se 1 (by rfl) ⟨1122938, by rfl⟩ : syracuseStep 1497251 = 2245877) B2245877
theorem B7559365 : Blo 884570 7559365 := bstep (se 4 (by rfl) ⟨708690, by rfl⟩ : syracuseStep 7559365 = 1417381) B1417381
theorem B1497379 : Blo 884570 1497379 := bstep (se 1 (by rfl) ⟨1123034, by rfl⟩ : syracuseStep 1497379 = 2246069) B2246069
theorem B1136963 : Blo 884570 1136963 := bstep (se 1 (by rfl) ⟨852722, by rfl⟩ : syracuseStep 1136963 = 1705445) B1705445
theorem B1497521 : Blo 884570 1497521 := bstep (se 2 (by rfl) ⟨561570, by rfl⟩ : syracuseStep 1497521 = 1123141) B1123141
theorem B1595875 : Blo 884570 1595875 := bstep (se 1 (by rfl) ⟨1196906, by rfl⟩ : syracuseStep 1595875 = 2393813) B2393813
theorem B1497649 : Blo 884570 1497649 := bstep (se 2 (by rfl) ⟨561618, by rfl⟩ : syracuseStep 1497649 = 1123237) B1123237
theorem B1497683 : Blo 884570 1497683 := bstep (se 1 (by rfl) ⟨1123262, by rfl⟩ : syracuseStep 1497683 = 2246525) B2246525
theorem B3365489 : Blo 884570 3365489 := bstep (se 2 (by rfl) ⟨1262058, by rfl⟩ : syracuseStep 3365489 = 2524117) B2524117
theorem B1497811 : Blo 884570 1497811 := bstep (se 1 (by rfl) ⟨1123358, by rfl⟩ : syracuseStep 1497811 = 2246717) B2246717
theorem B1497953 : Blo 884570 1497953 := bstep (se 2 (by rfl) ⟨561732, by rfl⟩ : syracuseStep 1497953 = 1123465) B1123465
theorem B1498081 : Blo 884570 1498081 := bstep (se 2 (by rfl) ⟨561780, by rfl⟩ : syracuseStep 1498081 = 1123561) B1123561
theorem B2841581 : Blo 884570 2841581 := bstep (se 3 (by rfl) ⟨532796, by rfl⟩ : syracuseStep 2841581 = 1065593) B1065593
theorem B1498115 : Blo 884570 1498115 := bstep (se 1 (by rfl) ⟨1123586, by rfl⟩ : syracuseStep 1498115 = 2247173) B2247173
theorem B1891345 : Blo 884570 1891345 := bstep (se 2 (by rfl) ⟨709254, by rfl⟩ : syracuseStep 1891345 = 1418509) B1418509
theorem B1891363 : Blo 884570 1891363 := bstep (se 1 (by rfl) ⟨1418522, by rfl⟩ : syracuseStep 1891363 = 2837045) B2837045
theorem B1596451 : Blo 884570 1596451 := bstep (se 1 (by rfl) ⟨1197338, by rfl⟩ : syracuseStep 1596451 = 2394677) B2394677
theorem B1498243 : Blo 884570 1498243 := bstep (se 1 (by rfl) ⟨1123682, by rfl⟩ : syracuseStep 1498243 = 2247365) B2247365
theorem B3366157 : Blo 884570 3366157 := bstep (se 3 (by rfl) ⟨631154, by rfl⟩ : syracuseStep 3366157 = 1262309) B1262309
theorem B1498385 : Blo 884570 1498385 := bstep (se 2 (by rfl) ⟨561894, by rfl⟩ : syracuseStep 1498385 = 1123789) B1123789
theorem B6380869 : Blo 884570 6380869 := bstep (se 4 (by rfl) ⟨598206, by rfl⟩ : syracuseStep 6380869 = 1196413) B1196413
theorem B1498513 : Blo 884570 1498513 := bstep (se 2 (by rfl) ⟨561942, by rfl⟩ : syracuseStep 1498513 = 1123885) B1123885
theorem B4480433 : Blo 884570 4480433 := bstep (se 2 (by rfl) ⟨1680162, by rfl⟩ : syracuseStep 4480433 = 3360325) B3360325
theorem B1498547 : Blo 884570 1498547 := bstep (se 1 (by rfl) ⟨1123910, by rfl⟩ : syracuseStep 1498547 = 2247821) B2247821
theorem B1498675 : Blo 884570 1498675 := bstep (se 1 (by rfl) ⟨1124006, by rfl⟩ : syracuseStep 1498675 = 2248013) B2248013
theorem B1597091 : Blo 884570 1597091 := bstep (se 1 (by rfl) ⟨1197818, by rfl⟩ : syracuseStep 1597091 = 2395637) B2395637
theorem B1498817 : Blo 884570 1498817 := bstep (se 2 (by rfl) ⟨562056, by rfl⟩ : syracuseStep 1498817 = 1124113) B1124113
theorem B1990385 : Blo 884570 1990385 := bstep (se 2 (by rfl) ⟨746394, by rfl⟩ : syracuseStep 1990385 = 1492789) B1492789
theorem B1990403 : Blo 884570 1990403 := bstep (se 1 (by rfl) ⟨1492802, by rfl⟩ : syracuseStep 1990403 = 2985605) B2985605
theorem B3792653 : Blo 884570 3792653 := bstep (se 3 (by rfl) ⟨711122, by rfl⟩ : syracuseStep 3792653 = 1422245) B1422245
theorem B24272693 : Blo 884570 24272693 := bstep (se 5 (by rfl) ⟨1137782, by rfl⟩ : syracuseStep 24272693 = 2275565) B2275565
theorem B1498945 : Blo 884570 1498945 := bstep (se 2 (by rfl) ⟨562104, by rfl⟩ : syracuseStep 1498945 = 1124209) B1124209
theorem B1498979 : Blo 884570 1498979 := bstep (se 1 (by rfl) ⟨1124234, by rfl⟩ : syracuseStep 1498979 = 2248469) B2248469
theorem B10117061 : Blo 884570 10117061 := bstep (se 4 (by rfl) ⟨948474, by rfl⟩ : syracuseStep 10117061 = 1896949) B1896949
theorem B1499107 : Blo 884570 1499107 := bstep (se 1 (by rfl) ⟨1124330, by rfl⟩ : syracuseStep 1499107 = 2248661) B2248661
theorem B1990673 : Blo 884570 1990673 := bstep (se 2 (by rfl) ⟨746502, by rfl⟩ : syracuseStep 1990673 = 1493005) B1493005
theorem B1990691 : Blo 884570 1990691 := bstep (se 1 (by rfl) ⟨1493018, by rfl⟩ : syracuseStep 1990691 = 2986037) B2986037
theorem B4251683 : Blo 884570 4251683 := bstep (se 1 (by rfl) ⟨3188762, by rfl⟩ : syracuseStep 4251683 = 6377525) B6377525
theorem B3366947 : Blo 884570 3366947 := bstep (se 1 (by rfl) ⟨2525210, by rfl⟩ : syracuseStep 3366947 = 5050421) B5050421
theorem B18702389 : Blo 884570 18702389 := bstep (se 5 (by rfl) ⟨876674, by rfl⟩ : syracuseStep 18702389 = 1753349) B1753349
theorem B4251761 : Blo 884570 4251761 := bstep (se 2 (by rfl) ⟨1594410, by rfl⟩ : syracuseStep 4251761 = 3188821) B3188821
theorem B1499249 : Blo 884570 1499249 := bstep (se 2 (by rfl) ⟨562218, by rfl⟩ : syracuseStep 1499249 = 1124437) B1124437
theorem B1401025 : Blo 884570 1401025 := bstep (se 2 (by rfl) ⟨525384, by rfl⟩ : syracuseStep 1401025 = 1050769) B1050769
theorem B1499377 : Blo 884570 1499377 := bstep (se 2 (by rfl) ⟨562266, by rfl⟩ : syracuseStep 1499377 = 1124533) B1124533
theorem B1138963 : Blo 884570 1138963 := bstep (se 1 (by rfl) ⟨854222, by rfl⟩ : syracuseStep 1138963 = 1708445) B1708445
theorem B1499411 : Blo 884570 1499411 := bstep (se 1 (by rfl) ⟨1124558, by rfl⟩ : syracuseStep 1499411 = 2249117) B2249117
theorem B1990961 : Blo 884570 1990961 := bstep (se 2 (by rfl) ⟨746610, by rfl⟩ : syracuseStep 1990961 = 1493221) B1493221
theorem B1990979 : Blo 884570 1990979 := bstep (se 1 (by rfl) ⟨1493234, by rfl⟩ : syracuseStep 1990979 = 2986469) B2986469
theorem B12312931 : Blo 884570 12312931 := bstep (se 1 (by rfl) ⟨9234698, by rfl⟩ : syracuseStep 12312931 = 18469397) B18469397
theorem B1139107 : Blo 884570 1139107 := bstep (se 1 (by rfl) ⟨854330, by rfl⟩ : syracuseStep 1139107 = 1708661) B1708661
theorem B1991249 : Blo 884570 1991249 := bstep (se 2 (by rfl) ⟨746718, by rfl⟩ : syracuseStep 1991249 = 1493437) B1493437
theorem B1991267 : Blo 884570 1991267 := bstep (se 1 (by rfl) ⟨1493450, by rfl⟩ : syracuseStep 1991267 = 2986901) B2986901
theorem B3367601 : Blo 884570 3367601 := bstep (se 2 (by rfl) ⟨1262850, by rfl⟩ : syracuseStep 3367601 = 2525701) B2525701
theorem B2843363 : Blo 884570 2843363 := bstep (se 1 (by rfl) ⟨2132522, by rfl⟩ : syracuseStep 2843363 = 4265045) B4265045
theorem B4481891 : Blo 884570 4481891 := bstep (se 1 (by rfl) ⟨3361418, by rfl⟩ : syracuseStep 4481891 = 6722837) B6722837
theorem B1991537 : Blo 884570 1991537 := bstep (se 2 (by rfl) ⟨746826, by rfl⟩ : syracuseStep 1991537 = 1493653) B1493653
theorem B1991555 : Blo 884570 1991555 := bstep (se 1 (by rfl) ⟨1493666, by rfl⟩ : syracuseStep 1991555 = 2987333) B2987333
theorem B910387 : Blo 884570 910387 := bstep (se 1 (by rfl) ⟨682790, by rfl⟩ : syracuseStep 910387 = 1365581) B1365581
theorem B1795139 : Blo 884570 1795139 := bstep (se 1 (by rfl) ⟨1346354, by rfl⟩ : syracuseStep 1795139 = 2692709) B2692709
theorem B1795171 : Blo 884570 1795171 := bstep (se 1 (by rfl) ⟨1346378, by rfl⟩ : syracuseStep 1795171 = 2692757) B2692757
theorem B1991825 : Blo 884570 1991825 := bstep (se 2 (by rfl) ⟨746934, by rfl⟩ : syracuseStep 1991825 = 1493869) B1493869
theorem B1991843 : Blo 884570 1991843 := bstep (se 1 (by rfl) ⟨1493882, by rfl⟩ : syracuseStep 1991843 = 2987765) B2987765
theorem B7202033 : Blo 884570 7202033 := bstep (se 2 (by rfl) ⟨2700762, by rfl⟩ : syracuseStep 7202033 = 5401525) B5401525
theorem B1893635 : Blo 884570 1893635 := bstep (se 1 (by rfl) ⟨1420226, by rfl⟩ : syracuseStep 1893635 = 2840453) B2840453
theorem B1992113 : Blo 884570 1992113 := bstep (se 2 (by rfl) ⟨747042, by rfl⟩ : syracuseStep 1992113 = 1494085) B1494085
theorem B1992131 : Blo 884570 1992131 := bstep (se 1 (by rfl) ⟨1494098, by rfl⟩ : syracuseStep 1992131 = 2988197) B2988197
theorem B910835 : Blo 884570 910835 := bstep (se 1 (by rfl) ⟨683126, by rfl⟩ : syracuseStep 910835 = 1366253) B1366253
theorem B4482701 : Blo 884570 4482701 := bstep (se 3 (by rfl) ⟨840506, by rfl⟩ : syracuseStep 4482701 = 1681013) B1681013
theorem B1599139 : Blo 884570 1599139 := bstep (se 1 (by rfl) ⟨1199354, by rfl⟩ : syracuseStep 1599139 = 2398709) B2398709
theorem B1992401 : Blo 884570 1992401 := bstep (se 2 (by rfl) ⟨747150, by rfl⟩ : syracuseStep 1992401 = 1494301) B1494301
theorem B1894097 : Blo 884570 1894097 := bstep (se 2 (by rfl) ⟨710286, by rfl⟩ : syracuseStep 1894097 = 1420573) B1420573
theorem B1992419 : Blo 884570 1992419 := bstep (se 1 (by rfl) ⟨1494314, by rfl⟩ : syracuseStep 1992419 = 2988629) B2988629
theorem B23062325 : Blo 884570 23062325 := bstep (se 5 (by rfl) ⟨1081046, by rfl⟩ : syracuseStep 23062325 = 2162093) B2162093
theorem B5039941 : Blo 884570 5039941 := bstep (se 4 (by rfl) ⟨472494, by rfl⟩ : syracuseStep 5039941 = 944989) B944989
theorem B2156483 : Blo 884570 2156483 := bstep (se 1 (by rfl) ⟨1617362, by rfl⟩ : syracuseStep 2156483 = 3234725) B3234725
theorem B4253681 : Blo 884570 4253681 := bstep (se 2 (by rfl) ⟨1595130, by rfl⟩ : syracuseStep 4253681 = 3190261) B3190261
theorem B1992689 : Blo 884570 1992689 := bstep (se 2 (by rfl) ⟨747258, by rfl⟩ : syracuseStep 1992689 = 1494517) B1494517
theorem B1992707 : Blo 884570 1992707 := bstep (se 1 (by rfl) ⟨1494530, by rfl⟩ : syracuseStep 1992707 = 2989061) B2989061
theorem B3369059 : Blo 884570 3369059 := bstep (se 1 (by rfl) ⟨2526794, by rfl⟩ : syracuseStep 3369059 = 5053589) B5053589
theorem B3369073 : Blo 884570 3369073 := bstep (se 2 (by rfl) ⟨1263402, by rfl⟩ : syracuseStep 3369073 = 2526805) B2526805
theorem B1599601 : Blo 884570 1599601 := bstep (se 2 (by rfl) ⟨599850, by rfl⟩ : syracuseStep 1599601 = 1199701) B1199701
theorem B1992977 : Blo 884570 1992977 := bstep (se 2 (by rfl) ⟨747366, by rfl⟩ : syracuseStep 1992977 = 1494733) B1494733
theorem B1992995 : Blo 884570 1992995 := bstep (se 1 (by rfl) ⟨1494746, by rfl⟩ : syracuseStep 1992995 = 2989493) B2989493
theorem B8088005 : Blo 884570 8088005 := bstep (se 4 (by rfl) ⟨758250, by rfl⟩ : syracuseStep 8088005 = 1516501) B1516501
theorem B2845169 : Blo 884570 2845169 := bstep (se 2 (by rfl) ⟨1066938, by rfl⟩ : syracuseStep 2845169 = 2133877) B2133877
theorem B4254221 : Blo 884570 4254221 := bstep (se 3 (by rfl) ⟨797666, by rfl⟩ : syracuseStep 4254221 = 1595333) B1595333
theorem B2845219 : Blo 884570 2845219 := bstep (se 1 (by rfl) ⟨2133914, by rfl⟩ : syracuseStep 2845219 = 4267829) B4267829
theorem B1993265 : Blo 884570 1993265 := bstep (se 2 (by rfl) ⟨747474, by rfl⟩ : syracuseStep 1993265 = 1494949) B1494949
theorem B1993283 : Blo 884570 1993283 := bstep (se 1 (by rfl) ⟨1494962, by rfl⟩ : syracuseStep 1993283 = 2989925) B2989925
theorem B4549283 : Blo 884570 4549283 := bstep (se 1 (by rfl) ⟨3411962, by rfl⟩ : syracuseStep 4549283 = 6823925) B6823925
theorem B1600163 : Blo 884570 1600163 := bstep (se 1 (by rfl) ⟨1200122, by rfl⟩ : syracuseStep 1600163 = 2400245) B2400245
theorem B10775267 : Blo 884570 10775267 := bstep (se 1 (by rfl) ⟨8081450, by rfl⟩ : syracuseStep 10775267 = 16162901) B16162901
theorem B12151565 : Blo 884570 12151565 := bstep (se 3 (by rfl) ⟨2278418, by rfl⟩ : syracuseStep 12151565 = 4556837) B4556837
theorem B1993553 : Blo 884570 1993553 := bstep (se 2 (by rfl) ⟨747582, by rfl⟩ : syracuseStep 1993553 = 1495165) B1495165
theorem B1993571 : Blo 884570 1993571 := bstep (se 1 (by rfl) ⟨1495178, by rfl⟩ : syracuseStep 1993571 = 2990357) B2990357
theorem B1895395 : Blo 884570 1895395 := bstep (se 1 (by rfl) ⟨1421546, by rfl⟩ : syracuseStep 1895395 = 2843093) B2843093
theorem B1993841 : Blo 884570 1993841 := bstep (se 2 (by rfl) ⟨747690, by rfl⟩ : syracuseStep 1993841 = 1495381) B1495381
theorem B1993859 : Blo 884570 1993859 := bstep (se 1 (by rfl) ⟨1495394, by rfl⟩ : syracuseStep 1993859 = 2990789) B2990789
theorem B1895651 : Blo 884570 1895651 := bstep (se 1 (by rfl) ⟨1421738, by rfl⟩ : syracuseStep 1895651 = 2843477) B2843477
theorem B2845937 : Blo 884570 2845937 := bstep (se 2 (by rfl) ⟨1067226, by rfl⟩ : syracuseStep 2845937 = 2134453) B2134453
theorem B1994129 : Blo 884570 1994129 := bstep (se 2 (by rfl) ⟨747798, by rfl⟩ : syracuseStep 1994129 = 1495597) B1495597
theorem B1994147 : Blo 884570 1994147 := bstep (se 1 (by rfl) ⟨1495610, by rfl⟩ : syracuseStep 1994147 = 2991221) B2991221
theorem B3370531 : Blo 884570 3370531 := bstep (se 1 (by rfl) ⟨2527898, by rfl⟩ : syracuseStep 3370531 = 5055797) B5055797
theorem B2125457 : Blo 884570 2125457 := bstep (se 2 (by rfl) ⟨797046, by rfl⟩ : syracuseStep 2125457 = 1594093) B1594093
theorem B1994417 : Blo 884570 1994417 := bstep (se 2 (by rfl) ⟨747906, by rfl⟩ : syracuseStep 1994417 = 1495813) B1495813
theorem B1601201 : Blo 884570 1601201 := bstep (se 2 (by rfl) ⟨600450, by rfl⟩ : syracuseStep 1601201 = 1200901) B1200901
theorem B1994435 : Blo 884570 1994435 := bstep (se 1 (by rfl) ⟨1495826, by rfl⟩ : syracuseStep 1994435 = 2991653) B2991653
theorem B2846449 : Blo 884570 2846449 := bstep (se 2 (by rfl) ⟨1067418, by rfl⟩ : syracuseStep 2846449 = 2134837) B2134837
theorem B5041925 : Blo 884570 5041925 := bstep (se 4 (by rfl) ⟨472680, by rfl⟩ : syracuseStep 5041925 = 945361) B945361
theorem B945955 : Blo 884570 945955 := bstep (se 1 (by rfl) ⟨709466, by rfl⟩ : syracuseStep 945955 = 1418933) B1418933
theorem B4321073 : Blo 884570 4321073 := bstep (se 2 (by rfl) ⟨1620402, by rfl⟩ : syracuseStep 4321073 = 3240805) B3240805
theorem B6057827 : Blo 884570 6057827 := bstep (se 1 (by rfl) ⟨4543370, by rfl⟩ : syracuseStep 6057827 = 9086741) B9086741
theorem B1994705 : Blo 884570 1994705 := bstep (se 2 (by rfl) ⟨748014, by rfl⟩ : syracuseStep 1994705 = 1496029) B1496029
theorem B1994723 : Blo 884570 1994723 := bstep (se 1 (by rfl) ⟨1496042, by rfl⟩ : syracuseStep 1994723 = 2992085) B2992085
theorem B1011827 : Blo 884570 1011827 := bstep (se 1 (by rfl) ⟨758870, by rfl⟩ : syracuseStep 1011827 = 1517741) B1517741
theorem B1896625 : Blo 884570 1896625 := bstep (se 2 (by rfl) ⟨711234, by rfl⟩ : syracuseStep 1896625 = 1422469) B1422469
theorem B1994993 : Blo 884570 1994993 := bstep (se 2 (by rfl) ⟨748122, by rfl⟩ : syracuseStep 1994993 = 1496245) B1496245
theorem B1995011 : Blo 884570 1995011 := bstep (se 1 (by rfl) ⟨1496258, by rfl⟩ : syracuseStep 1995011 = 2992517) B2992517
theorem B4485617 : Blo 884570 4485617 := bstep (se 2 (by rfl) ⟨1682106, by rfl⟩ : syracuseStep 4485617 = 3364213) B3364213
theorem B1995281 : Blo 884570 1995281 := bstep (se 2 (by rfl) ⟨748230, by rfl⟩ : syracuseStep 1995281 = 1496461) B1496461
theorem B1995299 : Blo 884570 1995299 := bstep (se 1 (by rfl) ⟨1496474, by rfl⟩ : syracuseStep 1995299 = 2992949) B2992949
theorem B1995569 : Blo 884570 1995569 := bstep (se 2 (by rfl) ⟨748338, by rfl⟩ : syracuseStep 1995569 = 1496677) B1496677
theorem B1995587 : Blo 884570 1995587 := bstep (se 1 (by rfl) ⟨1496690, by rfl⟩ : syracuseStep 1995587 = 2993381) B2993381
theorem B1897283 : Blo 884570 1897283 := bstep (se 1 (by rfl) ⟨1422962, by rfl⟩ : syracuseStep 1897283 = 2845925) B2845925
theorem B2520017 : Blo 884570 2520017 := bstep (se 2 (by rfl) ⟨945006, by rfl⟩ : syracuseStep 2520017 = 1890013) B1890013
theorem B947219 : Blo 884570 947219 := bstep (se 1 (by rfl) ⟨710414, by rfl⟩ : syracuseStep 947219 = 1420829) B1420829
theorem B1995857 : Blo 884570 1995857 := bstep (se 2 (by rfl) ⟨748446, by rfl⟩ : syracuseStep 1995857 = 1496893) B1496893
theorem B1995875 : Blo 884570 1995875 := bstep (se 1 (by rfl) ⟨1496906, by rfl⟩ : syracuseStep 1995875 = 2993813) B2993813
theorem B2127217 : Blo 884570 2127217 := bstep (se 2 (by rfl) ⟨797706, by rfl⟩ : syracuseStep 2127217 = 1595413) B1595413
theorem B1996145 : Blo 884570 1996145 := bstep (se 2 (by rfl) ⟨748554, by rfl⟩ : syracuseStep 1996145 = 1497109) B1497109
theorem B1996163 : Blo 884570 1996163 := bstep (se 1 (by rfl) ⟨1497122, by rfl⟩ : syracuseStep 1996163 = 2994245) B2994245
theorem B2160145 : Blo 884570 2160145 := bstep (se 2 (by rfl) ⟨810054, by rfl⟩ : syracuseStep 2160145 = 1620109) B1620109
theorem B3601955 : Blo 884570 3601955 := bstep (se 1 (by rfl) ⟨2701466, by rfl⟩ : syracuseStep 3601955 = 5402933) B5402933
theorem B1996433 : Blo 884570 1996433 := bstep (se 2 (by rfl) ⟨748662, by rfl⟩ : syracuseStep 1996433 = 1497325) B1497325
theorem B1996451 : Blo 884570 1996451 := bstep (se 1 (by rfl) ⟨1497338, by rfl⟩ : syracuseStep 1996451 = 2994677) B2994677
theorem B3372749 : Blo 884570 3372749 := bstep (se 3 (by rfl) ⟨632390, by rfl⟩ : syracuseStep 3372749 = 1264781) B1264781
theorem B947971 : Blo 884570 947971 := bstep (se 1 (by rfl) ⟨710978, by rfl⟩ : syracuseStep 947971 = 1421957) B1421957
theorem B2520973 : Blo 884570 2520973 := bstep (se 3 (by rfl) ⟨472682, by rfl⟩ : syracuseStep 2520973 = 945365) B945365
theorem B4487075 : Blo 884570 4487075 := bstep (se 1 (by rfl) ⟨3365306, by rfl⟩ : syracuseStep 4487075 = 6730613) B6730613
theorem B1996721 : Blo 884570 1996721 := bstep (se 2 (by rfl) ⟨748770, by rfl⟩ : syracuseStep 1996721 = 1497541) B1497541
theorem B1996739 : Blo 884570 1996739 := bstep (se 1 (by rfl) ⟨1497554, by rfl⟩ : syracuseStep 1996739 = 2995109) B2995109
theorem B2521201 : Blo 884570 2521201 := bstep (se 2 (by rfl) ⟨945450, by rfl⟩ : syracuseStep 2521201 = 1890901) B1890901
theorem B1079411 : Blo 884570 1079411 := bstep (se 1 (by rfl) ⟨809558, by rfl⟩ : syracuseStep 1079411 = 1619117) B1619117
theorem B1997009 : Blo 884570 1997009 := bstep (se 2 (by rfl) ⟨748878, by rfl⟩ : syracuseStep 1997009 = 1497757) B1497757
theorem B1997027 : Blo 884570 1997027 := bstep (se 1 (by rfl) ⟨1497770, by rfl⟩ : syracuseStep 1997027 = 2995541) B2995541
theorem B2521361 : Blo 884570 2521361 := bstep (se 2 (by rfl) ⟨945510, by rfl⟩ : syracuseStep 2521361 = 1891021) B1891021
theorem B4553059 : Blo 884570 4553059 := bstep (se 1 (by rfl) ⟨3414794, by rfl⟩ : syracuseStep 4553059 = 6829589) B6829589
theorem B2521475 : Blo 884570 2521475 := bstep (se 1 (by rfl) ⟨1891106, by rfl⟩ : syracuseStep 2521475 = 3782213) B3782213
theorem B1997297 : Blo 884570 1997297 := bstep (se 2 (by rfl) ⟨748986, by rfl⟩ : syracuseStep 1997297 = 1497973) B1497973
theorem B1997315 : Blo 884570 1997315 := bstep (se 1 (by rfl) ⟨1497986, by rfl⟩ : syracuseStep 1997315 = 2995973) B2995973
theorem B1800785 : Blo 884570 1800785 := bstep (se 2 (by rfl) ⟨675294, by rfl⟩ : syracuseStep 1800785 = 1350589) B1350589
theorem B1440371 : Blo 884570 1440371 := bstep (se 1 (by rfl) ⟨1080278, by rfl⟩ : syracuseStep 1440371 = 2160557) B2160557
theorem B4487885 : Blo 884570 4487885 := bstep (se 3 (by rfl) ⟨841478, by rfl⟩ : syracuseStep 4487885 = 1682957) B1682957
theorem B7568113 : Blo 884570 7568113 := bstep (se 2 (by rfl) ⟨2838042, by rfl⟩ : syracuseStep 7568113 = 5676085) B5676085
theorem B1997585 : Blo 884570 1997585 := bstep (se 2 (by rfl) ⟨749094, by rfl⟩ : syracuseStep 1997585 = 1498189) B1498189
theorem B1997603 : Blo 884570 1997603 := bstep (se 1 (by rfl) ⟨1498202, by rfl⟩ : syracuseStep 1997603 = 2996405) B2996405
theorem B1997873 : Blo 884570 1997873 := bstep (se 2 (by rfl) ⟨749202, by rfl⟩ : syracuseStep 1997873 = 1498405) B1498405
theorem B1276993 : Blo 884570 1276993 := bstep (se 2 (by rfl) ⟨478872, by rfl⟩ : syracuseStep 1276993 = 957745) B957745
theorem B1997891 : Blo 884570 1997891 := bstep (se 1 (by rfl) ⟨1498418, by rfl⟩ : syracuseStep 1997891 = 2996837) B2996837
theorem B6061169 : Blo 884570 6061169 := bstep (se 2 (by rfl) ⟨2272938, by rfl⟩ : syracuseStep 6061169 = 4545877) B4545877
theorem B4095281 : Blo 884570 4095281 := bstep (se 2 (by rfl) ⟨1535730, by rfl⟩ : syracuseStep 4095281 = 3071461) B3071461
theorem B1998161 : Blo 884570 1998161 := bstep (se 2 (by rfl) ⟨749310, by rfl⟩ : syracuseStep 1998161 = 1498621) B1498621
theorem B1998179 : Blo 884570 1998179 := bstep (se 1 (by rfl) ⟨1498634, by rfl⟩ : syracuseStep 1998179 = 2997269) B2997269
theorem B2522477 : Blo 884570 2522477 := bstep (se 3 (by rfl) ⟨472964, by rfl⟩ : syracuseStep 2522477 = 945929) B945929
theorem B3079565 : Blo 884570 3079565 := bstep (se 3 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 3079565 = 1154837) B1154837
theorem B6061553 : Blo 884570 6061553 := bstep (se 2 (by rfl) ⟨2273082, by rfl⟩ : syracuseStep 6061553 = 4546165) B4546165
theorem B5045773 : Blo 884570 5045773 := bstep (se 3 (by rfl) ⟨946082, by rfl⟩ : syracuseStep 5045773 = 1892165) B1892165
theorem B2522659 : Blo 884570 2522659 := bstep (se 1 (by rfl) ⟨1891994, by rfl⟩ : syracuseStep 2522659 = 3783989) B3783989
theorem B1998449 : Blo 884570 1998449 := bstep (se 2 (by rfl) ⟨749418, by rfl⟩ : syracuseStep 1998449 = 1498837) B1498837
theorem B1998467 : Blo 884570 1998467 := bstep (se 1 (by rfl) ⟨1498850, by rfl⟩ : syracuseStep 1998467 = 2997701) B2997701
theorem B2162321 : Blo 884570 2162321 := bstep (se 2 (by rfl) ⟨810870, by rfl⟩ : syracuseStep 2162321 = 1621741) B1621741
theorem B2522819 : Blo 884570 2522819 := bstep (se 1 (by rfl) ⟨1892114, by rfl⟩ : syracuseStep 2522819 = 3784229) B3784229
theorem B884579 : Blo 884570 884579 := bstep (se 1 (by rfl) ⟨663434, by rfl⟩ : syracuseStep 884579 = 1326869) B1326869
theorem B884595 : Blo 884570 884595 := bstep (se 1 (by rfl) ⟨663446, by rfl⟩ : syracuseStep 884595 = 1326893) B1326893
theorem B884611 : Blo 884570 884611 := bstep (se 1 (by rfl) ⟨663458, by rfl⟩ : syracuseStep 884611 = 1326917) B1326917
theorem B1998737 : Blo 884570 1998737 := bstep (se 2 (by rfl) ⟨749526, by rfl⟩ : syracuseStep 1998737 = 1499053) B1499053
theorem B884627 : Blo 884570 884627 := bstep (se 1 (by rfl) ⟨663470, by rfl⟩ : syracuseStep 884627 = 1326941) B1326941
theorem B884643 : Blo 884570 884643 := bstep (se 1 (by rfl) ⟨663482, by rfl⟩ : syracuseStep 884643 = 1326965) B1326965
theorem B1998755 : Blo 884570 1998755 := bstep (se 1 (by rfl) ⟨1499066, by rfl⟩ : syracuseStep 1998755 = 2998133) B2998133
theorem B884659 : Blo 884570 884659 := bstep (se 1 (by rfl) ⟨663494, by rfl⟩ : syracuseStep 884659 = 1326989) B1326989
theorem B884675 : Blo 884570 884675 := bstep (se 1 (by rfl) ⟨663506, by rfl⟩ : syracuseStep 884675 = 1327013) B1327013
theorem B884691 : Blo 884570 884691 := bstep (se 1 (by rfl) ⟨663518, by rfl⟩ : syracuseStep 884691 = 1327037) B1327037
theorem B884707 : Blo 884570 884707 := bstep (se 1 (by rfl) ⟨663530, by rfl⟩ : syracuseStep 884707 = 1327061) B1327061
theorem B13828067 : Blo 884570 13828067 := bstep (se 1 (by rfl) ⟨10371050, by rfl⟩ : syracuseStep 13828067 = 20742101) B20742101
theorem B884723 : Blo 884570 884723 := bstep (se 1 (by rfl) ⟨663542, by rfl⟩ : syracuseStep 884723 = 1327085) B1327085
theorem B884747 : Blo 884570 884747 := bstep (se 1 (by rfl) ⟨663560, by rfl⟩ : syracuseStep 884747 = 1327121) B1327121
theorem B884759 : Blo 884570 884759 := bstep (se 1 (by rfl) ⟨663569, by rfl⟩ : syracuseStep 884759 = 1327139) B1327139
theorem B884779 : Blo 884570 884779 := bstep (se 1 (by rfl) ⟨663584, by rfl⟩ : syracuseStep 884779 = 1327169) B1327169
theorem B1998899 : Blo 884570 1998899 := bstep (se 1 (by rfl) ⟨1499174, by rfl⟩ : syracuseStep 1998899 = 2998349) B2998349
theorem B884791 : Blo 884570 884791 := bstep (se 1 (by rfl) ⟨663593, by rfl⟩ : syracuseStep 884791 = 1327187) B1327187
theorem B884811 : Blo 884570 884811 := bstep (se 1 (by rfl) ⟨663608, by rfl⟩ : syracuseStep 884811 = 1327217) B1327217
theorem B884823 : Blo 884570 884823 := bstep (se 1 (by rfl) ⟨663617, by rfl⟩ : syracuseStep 884823 = 1327235) B1327235
theorem B1998935 : Blo 884570 1998935 := bstep (se 1 (by rfl) ⟨1499201, by rfl⟩ : syracuseStep 1998935 = 2998403) B2998403
theorem B884843 : Blo 884570 884843 := bstep (se 1 (by rfl) ⟨663632, by rfl⟩ : syracuseStep 884843 = 1327265) B1327265
theorem B884855 : Blo 884570 884855 := bstep (se 1 (by rfl) ⟨663641, by rfl⟩ : syracuseStep 884855 = 1327283) B1327283
theorem B884875 : Blo 884570 884875 := bstep (se 1 (by rfl) ⟨663656, by rfl⟩ : syracuseStep 884875 = 1327313) B1327313
theorem B884887 : Blo 884570 884887 := bstep (se 1 (by rfl) ⟨663665, by rfl⟩ : syracuseStep 884887 = 1327331) B1327331
theorem B884907 : Blo 884570 884907 := bstep (se 1 (by rfl) ⟨663680, by rfl⟩ : syracuseStep 884907 = 1327361) B1327361
theorem B884919 : Blo 884570 884919 := bstep (se 1 (by rfl) ⟨663689, by rfl⟩ : syracuseStep 884919 = 1327379) B1327379
theorem B884939 : Blo 884570 884939 := bstep (se 1 (by rfl) ⟨663704, by rfl⟩ : syracuseStep 884939 = 1327409) B1327409
theorem B884951 : Blo 884570 884951 := bstep (se 1 (by rfl) ⟨663713, by rfl⟩ : syracuseStep 884951 = 1327427) B1327427
theorem B884971 : Blo 884570 884971 := bstep (se 1 (by rfl) ⟨663728, by rfl⟩ : syracuseStep 884971 = 1327457) B1327457
theorem B884983 : Blo 884570 884983 := bstep (se 1 (by rfl) ⟨663737, by rfl⟩ : syracuseStep 884983 = 1327475) B1327475
theorem B1868033 : Blo 884570 1868033 := bstep (se 2 (by rfl) ⟨700512, by rfl⟩ : syracuseStep 1868033 = 1401025) B1401025
theorem B885003 : Blo 884570 885003 := bstep (se 1 (by rfl) ⟨663752, by rfl⟩ : syracuseStep 885003 = 1327505) B1327505
theorem B1999115 : Blo 884570 1999115 := bstep (se 1 (by rfl) ⟨1499336, by rfl⟩ : syracuseStep 1999115 = 2998673) B2998673
theorem B885015 : Blo 884570 885015 := bstep (se 1 (by rfl) ⟨663761, by rfl⟩ : syracuseStep 885015 = 1327523) B1327523
theorem B885035 : Blo 884570 885035 := bstep (se 1 (by rfl) ⟨663776, by rfl⟩ : syracuseStep 885035 = 1327553) B1327553
theorem B885047 : Blo 884570 885047 := bstep (se 1 (by rfl) ⟨663785, by rfl⟩ : syracuseStep 885047 = 1327571) B1327571
theorem B1999169 : Blo 884570 1999169 := bstep (se 2 (by rfl) ⟨749688, by rfl⟩ : syracuseStep 1999169 = 1499377) B1499377
theorem B885067 : Blo 884570 885067 := bstep (se 1 (by rfl) ⟨663800, by rfl⟩ : syracuseStep 885067 = 1327601) B1327601
theorem B885079 : Blo 884570 885079 := bstep (se 1 (by rfl) ⟨663809, by rfl⟩ : syracuseStep 885079 = 1327619) B1327619
theorem B885099 : Blo 884570 885099 := bstep (se 1 (by rfl) ⟨663824, by rfl⟩ : syracuseStep 885099 = 1327649) B1327649
theorem B885111 : Blo 884570 885111 := bstep (se 1 (by rfl) ⟨663833, by rfl⟩ : syracuseStep 885111 = 1327667) B1327667
theorem B885131 : Blo 884570 885131 := bstep (se 1 (by rfl) ⟨663848, by rfl⟩ : syracuseStep 885131 = 1327697) B1327697
theorem B885143 : Blo 884570 885143 := bstep (se 1 (by rfl) ⟨663857, by rfl⟩ : syracuseStep 885143 = 1327715) B1327715
theorem B885163 : Blo 884570 885163 := bstep (se 1 (by rfl) ⟨663872, by rfl⟩ : syracuseStep 885163 = 1327745) B1327745
theorem B885175 : Blo 884570 885175 := bstep (se 1 (by rfl) ⟨663881, by rfl⟩ : syracuseStep 885175 = 1327763) B1327763
theorem B885195 : Blo 884570 885195 := bstep (se 1 (by rfl) ⟨663896, by rfl⟩ : syracuseStep 885195 = 1327793) B1327793
theorem B885207 : Blo 884570 885207 := bstep (se 1 (by rfl) ⟨663905, by rfl⟩ : syracuseStep 885207 = 1327811) B1327811
theorem B16417241 : Blo 884570 16417241 := bstep (se 2 (by rfl) ⟨6156465, by rfl⟩ : syracuseStep 16417241 = 12312931) B12312931
theorem B885227 : Blo 884570 885227 := bstep (se 1 (by rfl) ⟨663920, by rfl⟩ : syracuseStep 885227 = 1327841) B1327841
theorem B885239 : Blo 884570 885239 := bstep (se 1 (by rfl) ⟨663929, by rfl⟩ : syracuseStep 885239 = 1327859) B1327859
theorem B885259 : Blo 884570 885259 := bstep (se 1 (by rfl) ⟨663944, by rfl⟩ : syracuseStep 885259 = 1327889) B1327889
theorem B885271 : Blo 884570 885271 := bstep (se 1 (by rfl) ⟨663953, by rfl⟩ : syracuseStep 885271 = 1327907) B1327907
theorem B2130455 : Blo 884570 2130455 := bstep (se 1 (by rfl) ⟨1597841, by rfl⟩ : syracuseStep 2130455 = 3195683) B3195683
theorem B885291 : Blo 884570 885291 := bstep (se 1 (by rfl) ⟨663968, by rfl⟩ : syracuseStep 885291 = 1327937) B1327937
theorem B885303 : Blo 884570 885303 := bstep (se 1 (by rfl) ⟨663977, by rfl⟩ : syracuseStep 885303 = 1327955) B1327955
theorem B2556481 : Blo 884570 2556481 := bstep (se 2 (by rfl) ⟨958680, by rfl⟩ : syracuseStep 2556481 = 1917361) B1917361
theorem B885323 : Blo 884570 885323 := bstep (se 1 (by rfl) ⟨663992, by rfl⟩ : syracuseStep 885323 = 1327985) B1327985
theorem B885335 : Blo 884570 885335 := bstep (se 1 (by rfl) ⟨664001, by rfl⟩ : syracuseStep 885335 = 1328003) B1328003
theorem B885355 : Blo 884570 885355 := bstep (se 1 (by rfl) ⟨664016, by rfl⟩ : syracuseStep 885355 = 1328033) B1328033
theorem B885367 : Blo 884570 885367 := bstep (se 1 (by rfl) ⟨664025, by rfl⟩ : syracuseStep 885367 = 1328051) B1328051
theorem B885387 : Blo 884570 885387 := bstep (se 1 (by rfl) ⟨664040, by rfl⟩ : syracuseStep 885387 = 1328081) B1328081
theorem B885399 : Blo 884570 885399 := bstep (se 1 (by rfl) ⟨664049, by rfl⟩ : syracuseStep 885399 = 1328099) B1328099
theorem B885419 : Blo 884570 885419 := bstep (se 1 (by rfl) ⟨664064, by rfl⟩ : syracuseStep 885419 = 1328129) B1328129
theorem B7570097 : Blo 884570 7570097 := bstep (se 2 (by rfl) ⟨2838786, by rfl⟩ : syracuseStep 7570097 = 5677573) B5677573
theorem B885431 : Blo 884570 885431 := bstep (se 1 (by rfl) ⟨664073, by rfl⟩ : syracuseStep 885431 = 1328147) B1328147
theorem B885451 : Blo 884570 885451 := bstep (se 1 (by rfl) ⟨664088, by rfl⟩ : syracuseStep 885451 = 1328177) B1328177
theorem B885463 : Blo 884570 885463 := bstep (se 1 (by rfl) ⟨664097, by rfl⟩ : syracuseStep 885463 = 1328195) B1328195
theorem B885483 : Blo 884570 885483 := bstep (se 1 (by rfl) ⟨664112, by rfl⟩ : syracuseStep 885483 = 1328225) B1328225
theorem B885495 : Blo 884570 885495 := bstep (se 1 (by rfl) ⟨664121, by rfl⟩ : syracuseStep 885495 = 1328243) B1328243
theorem B885515 : Blo 884570 885515 := bstep (se 1 (by rfl) ⟨664136, by rfl⟩ : syracuseStep 885515 = 1328273) B1328273
theorem B885527 : Blo 884570 885527 := bstep (se 1 (by rfl) ⟨664145, by rfl⟩ : syracuseStep 885527 = 1328291) B1328291
theorem B885547 : Blo 884570 885547 := bstep (se 1 (by rfl) ⟨664160, by rfl⟩ : syracuseStep 885547 = 1328321) B1328321
theorem B885559 : Blo 884570 885559 := bstep (se 1 (by rfl) ⟨664169, by rfl⟩ : syracuseStep 885559 = 1328339) B1328339
theorem B885579 : Blo 884570 885579 := bstep (se 1 (by rfl) ⟨664184, by rfl⟩ : syracuseStep 885579 = 1328369) B1328369
theorem B5473099 : Blo 884570 5473099 := bstep (se 1 (by rfl) ⟨4104824, by rfl⟩ : syracuseStep 5473099 = 8209649) B8209649
theorem B885591 : Blo 884570 885591 := bstep (se 1 (by rfl) ⟨664193, by rfl⟩ : syracuseStep 885591 = 1328387) B1328387
theorem B885611 : Blo 884570 885611 := bstep (se 1 (by rfl) ⟨664208, by rfl⟩ : syracuseStep 885611 = 1328417) B1328417
theorem B885623 : Blo 884570 885623 := bstep (se 1 (by rfl) ⟨664217, by rfl⟩ : syracuseStep 885623 = 1328435) B1328435
theorem B885643 : Blo 884570 885643 := bstep (se 1 (by rfl) ⟨664232, by rfl⟩ : syracuseStep 885643 = 1328465) B1328465
theorem B5669783 : Blo 884570 5669783 := bstep (se 1 (by rfl) ⟨4252337, by rfl⟩ : syracuseStep 5669783 = 8504675) B8504675
theorem B885655 : Blo 884570 885655 := bstep (se 1 (by rfl) ⟨664241, by rfl⟩ : syracuseStep 885655 = 1328483) B1328483
theorem B885675 : Blo 884570 885675 := bstep (se 1 (by rfl) ⟨664256, by rfl⟩ : syracuseStep 885675 = 1328513) B1328513
theorem B885687 : Blo 884570 885687 := bstep (se 1 (by rfl) ⟨664265, by rfl⟩ : syracuseStep 885687 = 1328531) B1328531
theorem B885707 : Blo 884570 885707 := bstep (se 1 (by rfl) ⟨664280, by rfl⟩ : syracuseStep 885707 = 1328561) B1328561
theorem B885719 : Blo 884570 885719 := bstep (se 1 (by rfl) ⟨664289, by rfl⟩ : syracuseStep 885719 = 1328579) B1328579
theorem B885739 : Blo 884570 885739 := bstep (se 1 (by rfl) ⟨664304, by rfl⟩ : syracuseStep 885739 = 1328609) B1328609
theorem B885751 : Blo 884570 885751 := bstep (se 1 (by rfl) ⟨664313, by rfl⟩ : syracuseStep 885751 = 1328627) B1328627
theorem B1311755 : Blo 884570 1311755 := bstep (se 1 (by rfl) ⟨983816, by rfl⟩ : syracuseStep 1311755 = 1967633) B1967633
theorem B885771 : Blo 884570 885771 := bstep (se 1 (by rfl) ⟨664328, by rfl⟩ : syracuseStep 885771 = 1328657) B1328657
theorem B885783 : Blo 884570 885783 := bstep (se 1 (by rfl) ⟨664337, by rfl⟩ : syracuseStep 885783 = 1328675) B1328675
theorem B885803 : Blo 884570 885803 := bstep (se 1 (by rfl) ⟨664352, by rfl⟩ : syracuseStep 885803 = 1328705) B1328705
theorem B885815 : Blo 884570 885815 := bstep (se 1 (by rfl) ⟨664361, by rfl⟩ : syracuseStep 885815 = 1328723) B1328723
theorem B885835 : Blo 884570 885835 := bstep (se 1 (by rfl) ⟨664376, by rfl⟩ : syracuseStep 885835 = 1328753) B1328753
theorem B4490315 : Blo 884570 4490315 := bstep (se 1 (by rfl) ⟨3367736, by rfl⟩ : syracuseStep 4490315 = 6735473) B6735473
theorem B885847 : Blo 884570 885847 := bstep (se 1 (by rfl) ⟨664385, by rfl⟩ : syracuseStep 885847 = 1328771) B1328771
theorem B885867 : Blo 884570 885867 := bstep (se 1 (by rfl) ⟨664400, by rfl⟩ : syracuseStep 885867 = 1328801) B1328801
theorem B885879 : Blo 884570 885879 := bstep (se 1 (by rfl) ⟨664409, by rfl⟩ : syracuseStep 885879 = 1328819) B1328819
theorem B885899 : Blo 884570 885899 := bstep (se 1 (by rfl) ⟨664424, by rfl⟩ : syracuseStep 885899 = 1328849) B1328849
theorem B885911 : Blo 884570 885911 := bstep (se 1 (by rfl) ⟨664433, by rfl⟩ : syracuseStep 885911 = 1328867) B1328867
theorem B885931 : Blo 884570 885931 := bstep (se 1 (by rfl) ⟨664448, by rfl⟩ : syracuseStep 885931 = 1328897) B1328897
theorem B885943 : Blo 884570 885943 := bstep (se 1 (by rfl) ⟨664457, by rfl⟩ : syracuseStep 885943 = 1328915) B1328915
theorem B885963 : Blo 884570 885963 := bstep (se 1 (by rfl) ⟨664472, by rfl⟩ : syracuseStep 885963 = 1328945) B1328945
theorem B885975 : Blo 884570 885975 := bstep (se 1 (by rfl) ⟨664481, by rfl⟩ : syracuseStep 885975 = 1328963) B1328963
theorem B885995 : Blo 884570 885995 := bstep (se 1 (by rfl) ⟨664496, by rfl⟩ : syracuseStep 885995 = 1328993) B1328993
theorem B886007 : Blo 884570 886007 := bstep (se 1 (by rfl) ⟨664505, by rfl⟩ : syracuseStep 886007 = 1329011) B1329011
theorem B886027 : Blo 884570 886027 := bstep (se 1 (by rfl) ⟨664520, by rfl⟩ : syracuseStep 886027 = 1329041) B1329041
theorem B886039 : Blo 884570 886039 := bstep (se 1 (by rfl) ⟨664529, by rfl⟩ : syracuseStep 886039 = 1329059) B1329059
theorem B6489379 : Blo 884570 6489379 := bstep (se 1 (by rfl) ⟨4867034, by rfl⟩ : syracuseStep 6489379 = 9734069) B9734069
theorem B886059 : Blo 884570 886059 := bstep (se 1 (by rfl) ⟨664544, by rfl⟩ : syracuseStep 886059 = 1329089) B1329089
theorem B886071 : Blo 884570 886071 := bstep (se 1 (by rfl) ⟨664553, by rfl⟩ : syracuseStep 886071 = 1329107) B1329107
theorem B886091 : Blo 884570 886091 := bstep (se 1 (by rfl) ⟨664568, by rfl⟩ : syracuseStep 886091 = 1329137) B1329137
theorem B886103 : Blo 884570 886103 := bstep (se 1 (by rfl) ⟨664577, by rfl⟩ : syracuseStep 886103 = 1329155) B1329155
theorem B6391133 : Blo 884570 6391133 := bstep (se 3 (by rfl) ⟨1198337, by rfl⟩ : syracuseStep 6391133 = 2396675) B2396675
theorem B886123 : Blo 884570 886123 := bstep (se 1 (by rfl) ⟨664592, by rfl⟩ : syracuseStep 886123 = 1329185) B1329185
theorem B886135 : Blo 884570 886135 := bstep (se 1 (by rfl) ⟨664601, by rfl⟩ : syracuseStep 886135 = 1329203) B1329203
theorem B886155 : Blo 884570 886155 := bstep (se 1 (by rfl) ⟨664616, by rfl⟩ : syracuseStep 886155 = 1329233) B1329233
theorem B886167 : Blo 884570 886167 := bstep (se 1 (by rfl) ⟨664625, by rfl⟩ : syracuseStep 886167 = 1329251) B1329251
theorem B1213849 : Blo 884570 1213849 := bstep (se 2 (by rfl) ⟨455193, by rfl⟩ : syracuseStep 1213849 = 910387) B910387
theorem B886187 : Blo 884570 886187 := bstep (se 1 (by rfl) ⟨664640, by rfl⟩ : syracuseStep 886187 = 1329281) B1329281
theorem B5670323 : Blo 884570 5670323 := bstep (se 1 (by rfl) ⟨4252742, by rfl⟩ : syracuseStep 5670323 = 8505485) B8505485
theorem B886199 : Blo 884570 886199 := bstep (se 1 (by rfl) ⟨664649, by rfl⟩ : syracuseStep 886199 = 1329299) B1329299
theorem B886219 : Blo 884570 886219 := bstep (se 1 (by rfl) ⟨664664, by rfl⟩ : syracuseStep 886219 = 1329329) B1329329
theorem B886231 : Blo 884570 886231 := bstep (se 1 (by rfl) ⟨664673, by rfl⟩ : syracuseStep 886231 = 1329347) B1329347
theorem B2393561 : Blo 884570 2393561 := bstep (se 2 (by rfl) ⟨897585, by rfl⟩ : syracuseStep 2393561 = 1795171) B1795171
theorem B886251 : Blo 884570 886251 := bstep (se 1 (by rfl) ⟨664688, by rfl⟩ : syracuseStep 886251 = 1329377) B1329377
theorem B886263 : Blo 884570 886263 := bstep (se 1 (by rfl) ⟨664697, by rfl⟩ : syracuseStep 886263 = 1329395) B1329395
theorem B886283 : Blo 884570 886283 := bstep (se 1 (by rfl) ⟨664712, by rfl⟩ : syracuseStep 886283 = 1329425) B1329425
theorem B886295 : Blo 884570 886295 := bstep (se 1 (by rfl) ⟨664721, by rfl⟩ : syracuseStep 886295 = 1329443) B1329443
theorem B886315 : Blo 884570 886315 := bstep (se 1 (by rfl) ⟨664736, by rfl⟩ : syracuseStep 886315 = 1329473) B1329473
theorem B886327 : Blo 884570 886327 := bstep (se 1 (by rfl) ⟨664745, by rfl⟩ : syracuseStep 886327 = 1329491) B1329491
theorem B886347 : Blo 884570 886347 := bstep (se 1 (by rfl) ⟨664760, by rfl⟩ : syracuseStep 886347 = 1329521) B1329521
theorem B886359 : Blo 884570 886359 := bstep (se 1 (by rfl) ⟨664769, by rfl⟩ : syracuseStep 886359 = 1329539) B1329539
theorem B886379 : Blo 884570 886379 := bstep (se 1 (by rfl) ⟨664784, by rfl⟩ : syracuseStep 886379 = 1329569) B1329569
theorem B886391 : Blo 884570 886391 := bstep (se 1 (by rfl) ⟨664793, by rfl⟩ : syracuseStep 886391 = 1329587) B1329587
theorem B886411 : Blo 884570 886411 := bstep (se 1 (by rfl) ⟨664808, by rfl⟩ : syracuseStep 886411 = 1329617) B1329617
theorem B886423 : Blo 884570 886423 := bstep (se 1 (by rfl) ⟨664817, by rfl⟩ : syracuseStep 886423 = 1329635) B1329635
theorem B886443 : Blo 884570 886443 := bstep (se 1 (by rfl) ⟨664832, by rfl⟩ : syracuseStep 886443 = 1329665) B1329665
theorem B886455 : Blo 884570 886455 := bstep (se 1 (by rfl) ⟨664841, by rfl⟩ : syracuseStep 886455 = 1329683) B1329683
theorem B886475 : Blo 884570 886475 := bstep (se 1 (by rfl) ⟨664856, by rfl⟩ : syracuseStep 886475 = 1329713) B1329713
theorem B886487 : Blo 884570 886487 := bstep (se 1 (by rfl) ⟨664865, by rfl⟩ : syracuseStep 886487 = 1329731) B1329731
theorem B886507 : Blo 884570 886507 := bstep (se 1 (by rfl) ⟨664880, by rfl⟩ : syracuseStep 886507 = 1329761) B1329761
theorem B886519 : Blo 884570 886519 := bstep (se 1 (by rfl) ⟨664889, by rfl⟩ : syracuseStep 886519 = 1329779) B1329779
theorem B886539 : Blo 884570 886539 := bstep (se 1 (by rfl) ⟨664904, by rfl⟩ : syracuseStep 886539 = 1329809) B1329809
theorem B886551 : Blo 884570 886551 := bstep (se 1 (by rfl) ⟨664913, by rfl⟩ : syracuseStep 886551 = 1329827) B1329827
theorem B886571 : Blo 884570 886571 := bstep (se 1 (by rfl) ⟨664928, by rfl⟩ : syracuseStep 886571 = 1329857) B1329857
theorem B886583 : Blo 884570 886583 := bstep (se 1 (by rfl) ⟨664937, by rfl⟩ : syracuseStep 886583 = 1329875) B1329875
theorem B886603 : Blo 884570 886603 := bstep (se 1 (by rfl) ⟨664952, by rfl⟩ : syracuseStep 886603 = 1329905) B1329905
theorem B886615 : Blo 884570 886615 := bstep (se 1 (by rfl) ⟨664961, by rfl⟩ : syracuseStep 886615 = 1329923) B1329923
theorem B886635 : Blo 884570 886635 := bstep (se 1 (by rfl) ⟨664976, by rfl⟩ : syracuseStep 886635 = 1329953) B1329953
theorem B886647 : Blo 884570 886647 := bstep (se 1 (by rfl) ⟨664985, by rfl⟩ : syracuseStep 886647 = 1329971) B1329971
theorem B886667 : Blo 884570 886667 := bstep (se 1 (by rfl) ⟨665000, by rfl⟩ : syracuseStep 886667 = 1330001) B1330001
theorem B886679 : Blo 884570 886679 := bstep (se 1 (by rfl) ⟨665009, by rfl⟩ : syracuseStep 886679 = 1330019) B1330019
theorem B886699 : Blo 884570 886699 := bstep (se 1 (by rfl) ⟨665024, by rfl⟩ : syracuseStep 886699 = 1330049) B1330049
theorem B886711 : Blo 884570 886711 := bstep (se 1 (by rfl) ⟨665033, by rfl⟩ : syracuseStep 886711 = 1330067) B1330067
theorem B886731 : Blo 884570 886731 := bstep (se 1 (by rfl) ⟨665048, by rfl⟩ : syracuseStep 886731 = 1330097) B1330097
theorem B886743 : Blo 884570 886743 := bstep (se 1 (by rfl) ⟨665057, by rfl⟩ : syracuseStep 886743 = 1330115) B1330115
theorem B886763 : Blo 884570 886763 := bstep (se 1 (by rfl) ⟨665072, by rfl⟩ : syracuseStep 886763 = 1330145) B1330145
theorem B886775 : Blo 884570 886775 := bstep (se 1 (by rfl) ⟨665081, by rfl⟩ : syracuseStep 886775 = 1330163) B1330163
theorem B886795 : Blo 884570 886795 := bstep (se 1 (by rfl) ⟨665096, by rfl⟩ : syracuseStep 886795 = 1330193) B1330193
theorem B886807 : Blo 884570 886807 := bstep (se 1 (by rfl) ⟨665105, by rfl⟩ : syracuseStep 886807 = 1330211) B1330211
theorem B886827 : Blo 884570 886827 := bstep (se 1 (by rfl) ⟨665120, by rfl⟩ : syracuseStep 886827 = 1330241) B1330241
theorem B886839 : Blo 884570 886839 := bstep (se 1 (by rfl) ⟨665129, by rfl⟩ : syracuseStep 886839 = 1330259) B1330259
theorem B886859 : Blo 884570 886859 := bstep (se 1 (by rfl) ⟨665144, by rfl⟩ : syracuseStep 886859 = 1330289) B1330289
theorem B886871 : Blo 884570 886871 := bstep (se 1 (by rfl) ⟨665153, by rfl⟩ : syracuseStep 886871 = 1330307) B1330307
theorem B886891 : Blo 884570 886891 := bstep (se 1 (by rfl) ⟨665168, by rfl⟩ : syracuseStep 886891 = 1330337) B1330337
theorem B886903 : Blo 884570 886903 := bstep (se 1 (by rfl) ⟨665177, by rfl⟩ : syracuseStep 886903 = 1330355) B1330355
theorem B886923 : Blo 884570 886923 := bstep (se 1 (by rfl) ⟨665192, by rfl⟩ : syracuseStep 886923 = 1330385) B1330385
theorem B886935 : Blo 884570 886935 := bstep (se 1 (by rfl) ⟨665201, by rfl⟩ : syracuseStep 886935 = 1330403) B1330403
theorem B886955 : Blo 884570 886955 := bstep (se 1 (by rfl) ⟨665216, by rfl⟩ : syracuseStep 886955 = 1330433) B1330433
theorem B886967 : Blo 884570 886967 := bstep (se 1 (by rfl) ⟨665225, by rfl⟩ : syracuseStep 886967 = 1330451) B1330451
theorem B886987 : Blo 884570 886987 := bstep (se 1 (by rfl) ⟨665240, by rfl⟩ : syracuseStep 886987 = 1330481) B1330481
theorem B886999 : Blo 884570 886999 := bstep (se 1 (by rfl) ⟨665249, by rfl⟩ : syracuseStep 886999 = 1330499) B1330499
theorem B2132185 : Blo 884570 2132185 := bstep (se 2 (by rfl) ⟨799569, by rfl⟩ : syracuseStep 2132185 = 1599139) B1599139
theorem B887019 : Blo 884570 887019 := bstep (se 1 (by rfl) ⟨665264, by rfl⟩ : syracuseStep 887019 = 1330529) B1330529
theorem B887031 : Blo 884570 887031 := bstep (se 1 (by rfl) ⟨665273, by rfl⟩ : syracuseStep 887031 = 1330547) B1330547
theorem B887051 : Blo 884570 887051 := bstep (se 1 (by rfl) ⟨665288, by rfl⟩ : syracuseStep 887051 = 1330577) B1330577
theorem B887063 : Blo 884570 887063 := bstep (se 1 (by rfl) ⟨665297, by rfl⟩ : syracuseStep 887063 = 1330595) B1330595
theorem B887083 : Blo 884570 887083 := bstep (se 1 (by rfl) ⟨665312, by rfl⟩ : syracuseStep 887083 = 1330625) B1330625
theorem B887095 : Blo 884570 887095 := bstep (se 1 (by rfl) ⟨665321, by rfl⟩ : syracuseStep 887095 = 1330643) B1330643
theorem B887115 : Blo 884570 887115 := bstep (se 1 (by rfl) ⟨665336, by rfl⟩ : syracuseStep 887115 = 1330673) B1330673
theorem B887127 : Blo 884570 887127 := bstep (se 1 (by rfl) ⟨665345, by rfl⟩ : syracuseStep 887127 = 1330691) B1330691
theorem B887147 : Blo 884570 887147 := bstep (se 1 (by rfl) ⟨665360, by rfl⟩ : syracuseStep 887147 = 1330721) B1330721
theorem B887159 : Blo 884570 887159 := bstep (se 1 (by rfl) ⟨665369, by rfl⟩ : syracuseStep 887159 = 1330739) B1330739
theorem B887179 : Blo 884570 887179 := bstep (se 1 (by rfl) ⟨665384, by rfl⟩ : syracuseStep 887179 = 1330769) B1330769
theorem B887191 : Blo 884570 887191 := bstep (se 1 (by rfl) ⟨665393, by rfl⟩ : syracuseStep 887191 = 1330787) B1330787
theorem B887211 : Blo 884570 887211 := bstep (se 1 (by rfl) ⟨665408, by rfl⟩ : syracuseStep 887211 = 1330817) B1330817
theorem B6719921 : Blo 884570 6719921 := bstep (se 2 (by rfl) ⟨2519970, by rfl⟩ : syracuseStep 6719921 = 5039941) B5039941
theorem B887223 : Blo 884570 887223 := bstep (se 1 (by rfl) ⟨665417, by rfl⟩ : syracuseStep 887223 = 1330835) B1330835
theorem B887243 : Blo 884570 887243 := bstep (se 1 (by rfl) ⟨665432, by rfl⟩ : syracuseStep 887243 = 1330865) B1330865
theorem B887255 : Blo 884570 887255 := bstep (se 1 (by rfl) ⟨665441, by rfl⟩ : syracuseStep 887255 = 1330883) B1330883
theorem B887275 : Blo 884570 887275 := bstep (se 1 (by rfl) ⟨665456, by rfl⟩ : syracuseStep 887275 = 1330913) B1330913
theorem B887287 : Blo 884570 887287 := bstep (se 1 (by rfl) ⟨665465, by rfl⟩ : syracuseStep 887287 = 1330931) B1330931
theorem B887307 : Blo 884570 887307 := bstep (se 1 (by rfl) ⟨665480, by rfl⟩ : syracuseStep 887307 = 1330961) B1330961
theorem B887319 : Blo 884570 887319 := bstep (se 1 (by rfl) ⟨665489, by rfl⟩ : syracuseStep 887319 = 1330979) B1330979
theorem B887339 : Blo 884570 887339 := bstep (se 1 (by rfl) ⟨665504, by rfl⟩ : syracuseStep 887339 = 1331009) B1331009
theorem B887351 : Blo 884570 887351 := bstep (se 1 (by rfl) ⟨665513, by rfl⟩ : syracuseStep 887351 = 1331027) B1331027
theorem B887371 : Blo 884570 887371 := bstep (se 1 (by rfl) ⟨665528, by rfl⟩ : syracuseStep 887371 = 1331057) B1331057
theorem B887383 : Blo 884570 887383 := bstep (se 1 (by rfl) ⟨665537, by rfl⟩ : syracuseStep 887383 = 1331075) B1331075
theorem B887403 : Blo 884570 887403 := bstep (se 1 (by rfl) ⟨665552, by rfl⟩ : syracuseStep 887403 = 1331105) B1331105
theorem B887415 : Blo 884570 887415 := bstep (se 1 (by rfl) ⟨665561, by rfl⟩ : syracuseStep 887415 = 1331123) B1331123
theorem B5048963 : Blo 884570 5048963 := bstep (se 1 (by rfl) ⟨3786722, by rfl⟩ : syracuseStep 5048963 = 7573445) B7573445
theorem B887435 : Blo 884570 887435 := bstep (se 1 (by rfl) ⟨665576, by rfl⟩ : syracuseStep 887435 = 1331153) B1331153
theorem B887447 : Blo 884570 887447 := bstep (se 1 (by rfl) ⟨665585, by rfl⟩ : syracuseStep 887447 = 1331171) B1331171
theorem B887467 : Blo 884570 887467 := bstep (se 1 (by rfl) ⟨665600, by rfl⟩ : syracuseStep 887467 = 1331201) B1331201
theorem B887479 : Blo 884570 887479 := bstep (se 1 (by rfl) ⟨665609, by rfl⟩ : syracuseStep 887479 = 1331219) B1331219
theorem B887499 : Blo 884570 887499 := bstep (se 1 (by rfl) ⟨665624, by rfl⟩ : syracuseStep 887499 = 1331249) B1331249
theorem B887511 : Blo 884570 887511 := bstep (se 1 (by rfl) ⟨665633, by rfl⟩ : syracuseStep 887511 = 1331267) B1331267
theorem B2525917 : Blo 884570 2525917 := bstep (se 3 (by rfl) ⟨473609, by rfl⟩ : syracuseStep 2525917 = 947219) B947219
theorem B887531 : Blo 884570 887531 := bstep (se 1 (by rfl) ⟨665648, by rfl⟩ : syracuseStep 887531 = 1331297) B1331297
theorem B887543 : Blo 884570 887543 := bstep (se 1 (by rfl) ⟨665657, by rfl⟩ : syracuseStep 887543 = 1331315) B1331315
theorem B1280779 : Blo 884570 1280779 := bstep (se 1 (by rfl) ⟨960584, by rfl⟩ : syracuseStep 1280779 = 1921169) B1921169
theorem B887563 : Blo 884570 887563 := bstep (se 1 (by rfl) ⟨665672, by rfl⟩ : syracuseStep 887563 = 1331345) B1331345
theorem B2525975 : Blo 884570 2525975 := bstep (se 1 (by rfl) ⟨1894481, by rfl⟩ : syracuseStep 2525975 = 3788963) B3788963
theorem B887575 : Blo 884570 887575 := bstep (se 1 (by rfl) ⟨665681, by rfl⟩ : syracuseStep 887575 = 1331363) B1331363
theorem B887595 : Blo 884570 887595 := bstep (se 1 (by rfl) ⟨665696, by rfl⟩ : syracuseStep 887595 = 1331393) B1331393
theorem B887607 : Blo 884570 887607 := bstep (se 1 (by rfl) ⟨665705, by rfl⟩ : syracuseStep 887607 = 1331411) B1331411
theorem B11209537 : Blo 884570 11209537 := bstep (se 2 (by rfl) ⟨4203576, by rfl⟩ : syracuseStep 11209537 = 8407153) B8407153
theorem B4492097 : Blo 884570 4492097 := bstep (se 2 (by rfl) ⟨1684536, by rfl⟩ : syracuseStep 4492097 = 3369073) B3369073
theorem B2132801 : Blo 884570 2132801 := bstep (se 2 (by rfl) ⟨799800, by rfl⟩ : syracuseStep 2132801 = 1599601) B1599601
theorem B887627 : Blo 884570 887627 := bstep (se 1 (by rfl) ⟨665720, by rfl⟩ : syracuseStep 887627 = 1331441) B1331441
theorem B887639 : Blo 884570 887639 := bstep (se 1 (by rfl) ⟨665729, by rfl⟩ : syracuseStep 887639 = 1331459) B1331459
theorem B5671781 : Blo 884570 5671781 := bstep (se 4 (by rfl) ⟨531729, by rfl⟩ : syracuseStep 5671781 = 1063459) B1063459
theorem B887659 : Blo 884570 887659 := bstep (se 1 (by rfl) ⟨665744, by rfl⟩ : syracuseStep 887659 = 1331489) B1331489
theorem B887671 : Blo 884570 887671 := bstep (se 1 (by rfl) ⟨665753, by rfl⟩ : syracuseStep 887671 = 1331507) B1331507
theorem B887691 : Blo 884570 887691 := bstep (se 1 (by rfl) ⟨665768, by rfl⟩ : syracuseStep 887691 = 1331537) B1331537
theorem B6720407 : Blo 884570 6720407 := bstep (se 1 (by rfl) ⟨5040305, by rfl⟩ : syracuseStep 6720407 = 10080611) B10080611
theorem B887703 : Blo 884570 887703 := bstep (se 1 (by rfl) ⟨665777, by rfl⟩ : syracuseStep 887703 = 1331555) B1331555
theorem B887723 : Blo 884570 887723 := bstep (se 1 (by rfl) ⟨665792, by rfl⟩ : syracuseStep 887723 = 1331585) B1331585
theorem B887735 : Blo 884570 887735 := bstep (se 1 (by rfl) ⟨665801, by rfl⟩ : syracuseStep 887735 = 1331603) B1331603
theorem B887755 : Blo 884570 887755 := bstep (se 1 (by rfl) ⟨665816, by rfl⟩ : syracuseStep 887755 = 1331633) B1331633
theorem B887767 : Blo 884570 887767 := bstep (se 1 (by rfl) ⟨665825, by rfl⟩ : syracuseStep 887767 = 1331651) B1331651
theorem B887787 : Blo 884570 887787 := bstep (se 1 (by rfl) ⟨665840, by rfl⟩ : syracuseStep 887787 = 1331681) B1331681
theorem B887799 : Blo 884570 887799 := bstep (se 1 (by rfl) ⟨665849, by rfl⟩ : syracuseStep 887799 = 1331699) B1331699
theorem B887819 : Blo 884570 887819 := bstep (se 1 (by rfl) ⟨665864, by rfl⟩ : syracuseStep 887819 = 1331729) B1331729
theorem B887831 : Blo 884570 887831 := bstep (se 1 (by rfl) ⟨665873, by rfl⟩ : syracuseStep 887831 = 1331747) B1331747
theorem B887851 : Blo 884570 887851 := bstep (se 1 (by rfl) ⟨665888, by rfl⟩ : syracuseStep 887851 = 1331777) B1331777
theorem B887863 : Blo 884570 887863 := bstep (se 1 (by rfl) ⟨665897, by rfl⟩ : syracuseStep 887863 = 1331795) B1331795
theorem B4787275 : Blo 884570 4787275 := bstep (se 1 (by rfl) ⟨3590456, by rfl⟩ : syracuseStep 4787275 = 7180913) B7180913
theorem B887883 : Blo 884570 887883 := bstep (se 1 (by rfl) ⟨665912, by rfl⟩ : syracuseStep 887883 = 1331825) B1331825
theorem B887895 : Blo 884570 887895 := bstep (se 1 (by rfl) ⟨665921, by rfl⟩ : syracuseStep 887895 = 1331843) B1331843
theorem B887915 : Blo 884570 887915 := bstep (se 1 (by rfl) ⟨665936, by rfl⟩ : syracuseStep 887915 = 1331873) B1331873
theorem B887927 : Blo 884570 887927 := bstep (se 1 (by rfl) ⟨665945, by rfl⟩ : syracuseStep 887927 = 1331891) B1331891
theorem B887947 : Blo 884570 887947 := bstep (se 1 (by rfl) ⟨665960, by rfl⟩ : syracuseStep 887947 = 1331921) B1331921
theorem B887959 : Blo 884570 887959 := bstep (se 1 (by rfl) ⟨665969, by rfl⟩ : syracuseStep 887959 = 1331939) B1331939
theorem B887979 : Blo 884570 887979 := bstep (se 1 (by rfl) ⟨665984, by rfl⟩ : syracuseStep 887979 = 1331969) B1331969
theorem B887991 : Blo 884570 887991 := bstep (se 1 (by rfl) ⟨665993, by rfl⟩ : syracuseStep 887991 = 1331987) B1331987
theorem B888011 : Blo 884570 888011 := bstep (se 1 (by rfl) ⟨666008, by rfl⟩ : syracuseStep 888011 = 1332017) B1332017
theorem B888023 : Blo 884570 888023 := bstep (se 1 (by rfl) ⟨666017, by rfl⟩ : syracuseStep 888023 = 1332035) B1332035
theorem B888043 : Blo 884570 888043 := bstep (se 1 (by rfl) ⟨666032, by rfl⟩ : syracuseStep 888043 = 1332065) B1332065
theorem B888055 : Blo 884570 888055 := bstep (se 1 (by rfl) ⟨666041, by rfl⟩ : syracuseStep 888055 = 1332083) B1332083
theorem B888075 : Blo 884570 888075 := bstep (se 1 (by rfl) ⟨666056, by rfl⟩ : syracuseStep 888075 = 1332113) B1332113
theorem B888087 : Blo 884570 888087 := bstep (se 1 (by rfl) ⟨666065, by rfl⟩ : syracuseStep 888087 = 1332131) B1332131
theorem B888107 : Blo 884570 888107 := bstep (se 1 (by rfl) ⟨666080, by rfl⟩ : syracuseStep 888107 = 1332161) B1332161
theorem B888119 : Blo 884570 888119 := bstep (se 1 (by rfl) ⟨666089, by rfl⟩ : syracuseStep 888119 = 1332179) B1332179
theorem B888139 : Blo 884570 888139 := bstep (se 1 (by rfl) ⟨666104, by rfl⟩ : syracuseStep 888139 = 1332209) B1332209
theorem B888151 : Blo 884570 888151 := bstep (se 1 (by rfl) ⟨666113, by rfl⟩ : syracuseStep 888151 = 1332227) B1332227
theorem B888171 : Blo 884570 888171 := bstep (se 1 (by rfl) ⟨666128, by rfl⟩ : syracuseStep 888171 = 1332257) B1332257
theorem B888183 : Blo 884570 888183 := bstep (se 1 (by rfl) ⟨666137, by rfl⟩ : syracuseStep 888183 = 1332275) B1332275
theorem B888203 : Blo 884570 888203 := bstep (se 1 (by rfl) ⟨666152, by rfl⟩ : syracuseStep 888203 = 1332305) B1332305
theorem B888215 : Blo 884570 888215 := bstep (se 1 (by rfl) ⟨666161, by rfl⟩ : syracuseStep 888215 = 1332323) B1332323
theorem B888235 : Blo 884570 888235 := bstep (se 1 (by rfl) ⟨666176, by rfl⟩ : syracuseStep 888235 = 1332353) B1332353
theorem B888247 : Blo 884570 888247 := bstep (se 1 (by rfl) ⟨666185, by rfl⟩ : syracuseStep 888247 = 1332371) B1332371
theorem B2395595 : Blo 884570 2395595 := bstep (se 1 (by rfl) ⟨1796696, by rfl⟩ : syracuseStep 2395595 = 3593393) B3593393
theorem B888267 : Blo 884570 888267 := bstep (se 1 (by rfl) ⟨666200, by rfl⟩ : syracuseStep 888267 = 1332401) B1332401
theorem B888279 : Blo 884570 888279 := bstep (se 1 (by rfl) ⟨666209, by rfl⟩ : syracuseStep 888279 = 1332419) B1332419
theorem B888299 : Blo 884570 888299 := bstep (se 1 (by rfl) ⟨666224, by rfl⟩ : syracuseStep 888299 = 1332449) B1332449
theorem B888311 : Blo 884570 888311 := bstep (se 1 (by rfl) ⟨666233, by rfl⟩ : syracuseStep 888311 = 1332467) B1332467
theorem B888331 : Blo 884570 888331 := bstep (se 1 (by rfl) ⟨666248, by rfl⟩ : syracuseStep 888331 = 1332497) B1332497
theorem B888343 : Blo 884570 888343 := bstep (se 1 (by rfl) ⟨666257, by rfl⟩ : syracuseStep 888343 = 1332515) B1332515
theorem B888363 : Blo 884570 888363 := bstep (se 1 (by rfl) ⟨666272, by rfl⟩ : syracuseStep 888363 = 1332545) B1332545
theorem B888375 : Blo 884570 888375 := bstep (se 1 (by rfl) ⟨666281, by rfl⟩ : syracuseStep 888375 = 1332563) B1332563
theorem B888395 : Blo 884570 888395 := bstep (se 1 (by rfl) ⟨666296, by rfl⟩ : syracuseStep 888395 = 1332593) B1332593
theorem B888407 : Blo 884570 888407 := bstep (se 1 (by rfl) ⟨666305, by rfl⟩ : syracuseStep 888407 = 1332611) B1332611
theorem B888427 : Blo 884570 888427 := bstep (se 1 (by rfl) ⟨666320, by rfl⟩ : syracuseStep 888427 = 1332641) B1332641
theorem B888439 : Blo 884570 888439 := bstep (se 1 (by rfl) ⟨666329, by rfl⟩ : syracuseStep 888439 = 1332659) B1332659
theorem B888459 : Blo 884570 888459 := bstep (se 1 (by rfl) ⟨666344, by rfl⟩ : syracuseStep 888459 = 1332689) B1332689
theorem B888471 : Blo 884570 888471 := bstep (se 1 (by rfl) ⟨666353, by rfl⟩ : syracuseStep 888471 = 1332707) B1332707
theorem B888491 : Blo 884570 888491 := bstep (se 1 (by rfl) ⟨666368, by rfl⟩ : syracuseStep 888491 = 1332737) B1332737
theorem B888503 : Blo 884570 888503 := bstep (se 1 (by rfl) ⟨666377, by rfl⟩ : syracuseStep 888503 = 1332755) B1332755
theorem B888523 : Blo 884570 888523 := bstep (se 1 (by rfl) ⟨666392, by rfl⟩ : syracuseStep 888523 = 1332785) B1332785
theorem B888535 : Blo 884570 888535 := bstep (se 1 (by rfl) ⟨666401, by rfl⟩ : syracuseStep 888535 = 1332803) B1332803
theorem B888555 : Blo 884570 888555 := bstep (se 1 (by rfl) ⟨666416, by rfl⟩ : syracuseStep 888555 = 1332833) B1332833
theorem B888567 : Blo 884570 888567 := bstep (se 1 (by rfl) ⟨666425, by rfl⟩ : syracuseStep 888567 = 1332851) B1332851
theorem B2985821 : Blo 884570 2985821 := bstep (se 3 (by rfl) ⟨559841, by rfl⟩ : syracuseStep 2985821 = 1119683) B1119683
theorem B2527193 : Blo 884570 2527193 := bstep (se 2 (by rfl) ⟨947697, by rfl⟩ : syracuseStep 2527193 = 1895395) B1895395
theorem B2527307 : Blo 884570 2527307 := bstep (se 1 (by rfl) ⟨1895480, by rfl⟩ : syracuseStep 2527307 = 3790961) B3790961
theorem B9605213 : Blo 884570 9605213 := bstep (se 3 (by rfl) ⟨1800977, by rfl⟩ : syracuseStep 9605213 = 3601955) B3601955
theorem B4788659 : Blo 884570 4788659 := bstep (se 1 (by rfl) ⟨3591494, by rfl⟩ : syracuseStep 4788659 = 7182989) B7182989
theorem B4494041 : Blo 884570 4494041 := bstep (se 2 (by rfl) ⟨1685265, by rfl⟩ : syracuseStep 4494041 = 3370531) B3370531
theorem B2986955 : Blo 884570 2986955 := bstep (se 1 (by rfl) ⟨2240216, by rfl⟩ : syracuseStep 2986955 = 4480433) B4480433
theorem B2528435 : Blo 884570 2528435 := bstep (se 1 (by rfl) ⟨1896326, by rfl⟩ : syracuseStep 2528435 = 3792653) B3792653
theorem B3413195 : Blo 884570 3413195 := bstep (se 1 (by rfl) ⟨2559896, by rfl⟩ : syracuseStep 3413195 = 5119793) B5119793
theorem B2987225 : Blo 884570 2987225 := bstep (se 2 (by rfl) ⟨1120209, by rfl⟩ : syracuseStep 2987225 = 2240419) B2240419
theorem B11343149 : Blo 884570 11343149 := bstep (se 3 (by rfl) ⟨2126840, by rfl⟩ : syracuseStep 11343149 = 4253681) B4253681
theorem B3413441 : Blo 884570 3413441 := bstep (se 2 (by rfl) ⟨1280040, by rfl⟩ : syracuseStep 3413441 = 2560081) B2560081
theorem B2528833 : Blo 884570 2528833 := bstep (se 2 (by rfl) ⟨948312, by rfl⟩ : syracuseStep 2528833 = 1896625) B1896625
theorem B2987927 : Blo 884570 2987927 := bstep (se 1 (by rfl) ⟨2240945, by rfl⟩ : syracuseStep 2987927 = 4481891) B4481891
theorem B1120331 : Blo 884570 1120331 := bstep (se 1 (by rfl) ⟨840248, by rfl⟩ : syracuseStep 1120331 = 1680497) B1680497
theorem B4495661 : Blo 884570 4495661 := bstep (se 3 (by rfl) ⟨842936, by rfl⟩ : syracuseStep 4495661 = 1685873) B1685873
theorem B2988467 : Blo 884570 2988467 := bstep (se 1 (by rfl) ⟨2241350, by rfl⟩ : syracuseStep 2988467 = 4482701) B4482701
theorem B2988737 : Blo 884570 2988737 := bstep (se 2 (by rfl) ⟨1120776, by rfl⟩ : syracuseStep 2988737 = 2241553) B2241553
theorem B1121035 : Blo 884570 1121035 := bstep (se 1 (by rfl) ⟨840776, by rfl⟩ : syracuseStep 1121035 = 1681553) B1681553
theorem B1121303 : Blo 884570 1121303 := bstep (se 1 (by rfl) ⟨840977, by rfl⟩ : syracuseStep 1121303 = 1681955) B1681955
theorem B7183511 : Blo 884570 7183511 := bstep (se 1 (by rfl) ⟨5387633, by rfl⟩ : syracuseStep 7183511 = 10775267) B10775267
theorem B8101043 : Blo 884570 8101043 := bstep (se 1 (by rfl) ⟨6075782, by rfl⟩ : syracuseStep 8101043 = 12151565) B12151565
theorem B2989277 : Blo 884570 2989277 := bstep (se 3 (by rfl) ⟨560489, by rfl⟩ : syracuseStep 2989277 = 1120979) B1120979
theorem B1122007 : Blo 884570 1122007 := bstep (se 1 (by rfl) ⟨841505, by rfl⟩ : syracuseStep 1122007 = 1683011) B1683011
theorem B1416971 : Blo 884570 1416971 := bstep (se 1 (by rfl) ⟨1062728, by rfl⟩ : syracuseStep 1416971 = 2125457) B2125457
theorem B4792139 : Blo 884570 4792139 := bstep (se 1 (by rfl) ⟨3594104, by rfl⟩ : syracuseStep 4792139 = 7188209) B7188209
theorem B5054339 : Blo 884570 5054339 := bstep (se 1 (by rfl) ⟨3790754, by rfl⟩ : syracuseStep 5054339 = 7581509) B7581509
theorem B4038551 : Blo 884570 4038551 := bstep (se 1 (by rfl) ⟨3028913, by rfl⟩ : syracuseStep 4038551 = 6057827) B6057827
theorem B1679449 : Blo 884570 1679449 := bstep (se 2 (by rfl) ⟨629793, by rfl⟩ : syracuseStep 1679449 = 1259587) B1259587
theorem B7282865 : Blo 884570 7282865 := bstep (se 2 (by rfl) ⟨2731074, by rfl⟩ : syracuseStep 7282865 = 5462149) B5462149
theorem B7184645 : Blo 884570 7184645 := bstep (se 4 (by rfl) ⟨673560, by rfl⟩ : syracuseStep 7184645 = 1347121) B1347121
theorem B7184705 : Blo 884570 7184705 := bstep (se 2 (by rfl) ⟨2694264, by rfl⟩ : syracuseStep 7184705 = 5388529) B5388529
theorem B2990411 : Blo 884570 2990411 := bstep (se 1 (by rfl) ⟨2242808, by rfl⟩ : syracuseStep 2990411 = 4485617) B4485617
theorem B5054795 : Blo 884570 5054795 := bstep (se 1 (by rfl) ⟨3791096, by rfl⟩ : syracuseStep 5054795 = 7582193) B7582193
theorem B6070745 : Blo 884570 6070745 := bstep (se 2 (by rfl) ⟨2276529, by rfl⟩ : syracuseStep 6070745 = 4553059) B4553059
theorem B1417753 : Blo 884570 1417753 := bstep (se 2 (by rfl) ⟨531657, by rfl⟩ : syracuseStep 1417753 = 1063315) B1063315
theorem B245998133 : Blo 884570 245998133 := bstep (se 5 (by rfl) ⟨11531162, by rfl⟩ : syracuseStep 245998133 = 23062325) B23062325
theorem B2990681 : Blo 884570 2990681 := bstep (se 2 (by rfl) ⟨1121505, by rfl⟩ : syracuseStep 2990681 = 2243011) B2243011
theorem B4268675 : Blo 884570 4268675 := bstep (se 1 (by rfl) ⟨3201506, by rfl⟩ : syracuseStep 4268675 = 6403013) B6403013
theorem B1680011 : Blo 884570 1680011 := bstep (se 1 (by rfl) ⟨1260008, by rfl⟩ : syracuseStep 1680011 = 2520017) B2520017
theorem B1680193 : Blo 884570 1680193 := bstep (se 2 (by rfl) ⟨630072, by rfl⟩ : syracuseStep 1680193 = 1260145) B1260145
theorem B2991383 : Blo 884570 2991383 := bstep (se 1 (by rfl) ⟨2243537, by rfl⟩ : syracuseStep 2991383 = 4487075) B4487075
theorem B1123723 : Blo 884570 1123723 := bstep (se 1 (by rfl) ⟨842792, by rfl⟩ : syracuseStep 1123723 = 1685585) B1685585
theorem B1680907 : Blo 884570 1680907 := bstep (se 1 (by rfl) ⟨1260680, by rfl⟩ : syracuseStep 1680907 = 2521361) B2521361
theorem B1680983 : Blo 884570 1680983 := bstep (se 1 (by rfl) ⟨1260737, by rfl⟩ : syracuseStep 1680983 = 2521475) B2521475
theorem B960247 : Blo 884570 960247 := bstep (se 1 (by rfl) ⟨720185, by rfl⟩ : syracuseStep 960247 = 1440371) B1440371
theorem B2991923 : Blo 884570 2991923 := bstep (se 1 (by rfl) ⟨2243942, by rfl⟩ : syracuseStep 2991923 = 4487885) B4487885
theorem B6727697 : Blo 884570 6727697 := bstep (se 2 (by rfl) ⟨2522886, by rfl⟩ : syracuseStep 6727697 = 5045773) B5045773
theorem B2992193 : Blo 884570 2992193 := bstep (se 2 (by rfl) ⟨1122072, by rfl⟩ : syracuseStep 2992193 = 2244145) B2244145
theorem B4040779 : Blo 884570 4040779 := bstep (se 1 (by rfl) ⟨3030584, by rfl⟩ : syracuseStep 4040779 = 6061169) B6061169
theorem B3188909 : Blo 884570 3188909 := bstep (se 3 (by rfl) ⟨597920, by rfl⟩ : syracuseStep 3188909 = 1195841) B1195841
theorem B2730187 : Blo 884570 2730187 := bstep (se 1 (by rfl) ⟨2047640, by rfl⟩ : syracuseStep 2730187 = 4095281) B4095281
theorem B1681651 : Blo 884570 1681651 := bstep (se 1 (by rfl) ⟨1261238, by rfl⟩ : syracuseStep 1681651 = 2522477) B2522477
theorem B4041035 : Blo 884570 4041035 := bstep (se 1 (by rfl) ⟨3030776, by rfl⟩ : syracuseStep 4041035 = 6061553) B6061553
theorem B1681879 : Blo 884570 1681879 := bstep (se 1 (by rfl) ⟨1261409, by rfl⟩ : syracuseStep 1681879 = 2522819) B2522819
theorem B8530393 : Blo 884570 8530393 := bstep (se 2 (by rfl) ⟨3198897, by rfl⟩ : syracuseStep 8530393 = 6397795) B6397795
theorem B1681985 : Blo 884570 1681985 := bstep (se 2 (by rfl) ⟨630744, by rfl⟩ : syracuseStep 1681985 = 1261489) B1261489
theorem B2992733 : Blo 884570 2992733 := bstep (se 3 (by rfl) ⟨561137, by rfl⟩ : syracuseStep 2992733 = 1122275) B1122275
theorem B9218711 : Blo 884570 9218711 := bstep (se 1 (by rfl) ⟨6914033, by rfl⟩ : syracuseStep 9218711 = 13828067) B13828067
theorem B1682137 : Blo 884570 1682137 := bstep (se 2 (by rfl) ⟨630801, by rfl⟩ : syracuseStep 1682137 = 1261603) B1261603
theorem B4106969 : Blo 884570 4106969 := bstep (se 2 (by rfl) ⟨1540113, by rfl⟩ : syracuseStep 4106969 = 3080227) B3080227
theorem B3779531 : Blo 884570 3779531 := bstep (se 1 (by rfl) ⟨2834648, by rfl⟩ : syracuseStep 3779531 = 5669297) B5669297
theorem B2698205 : Blo 884570 2698205 := bstep (se 3 (by rfl) ⟨505913, by rfl⟩ : syracuseStep 2698205 = 1011827) B1011827
theorem B1518617 : Blo 884570 1518617 := bstep (se 2 (by rfl) ⟨569481, by rfl⟩ : syracuseStep 1518617 = 1138963) B1138963
theorem B10103939 : Blo 884570 10103939 := bstep (se 1 (by rfl) ⟨7577954, by rfl⟩ : syracuseStep 10103939 = 15155909) B15155909
theorem B1518809 : Blo 884570 1518809 := bstep (se 2 (by rfl) ⟨569553, by rfl⟩ : syracuseStep 1518809 = 1139107) B1139107
theorem B2240075 : Blo 884570 2240075 := bstep (se 1 (by rfl) ⟨1680056, by rfl⟩ : syracuseStep 2240075 = 3360113) B3360113
theorem B2993867 : Blo 884570 2993867 := bstep (se 1 (by rfl) ⟨2245400, by rfl⟩ : syracuseStep 2993867 = 4490801) B4490801
theorem B3452633 : Blo 884570 3452633 := bstep (se 2 (by rfl) ⟨1294737, by rfl⟩ : syracuseStep 3452633 = 2589475) B2589475
theorem B995179 : Blo 884570 995179 := bstep (se 1 (by rfl) ⟨746384, by rfl⟩ : syracuseStep 995179 = 1492769) B1492769
theorem B3780503 : Blo 884570 3780503 := bstep (se 1 (by rfl) ⟨2835377, by rfl⟩ : syracuseStep 3780503 = 5670755) B5670755
theorem B995287 : Blo 884570 995287 := bstep (se 1 (by rfl) ⟨746465, by rfl⟩ : syracuseStep 995287 = 1492931) B1492931
theorem B2994137 : Blo 884570 2994137 := bstep (se 2 (by rfl) ⟨1122801, by rfl⟩ : syracuseStep 2994137 = 2245603) B2245603
theorem B1683443 : Blo 884570 1683443 := bstep (se 1 (by rfl) ⟨1262582, by rfl⟩ : syracuseStep 1683443 = 2525165) B2525165
theorem B995467 : Blo 884570 995467 := bstep (se 1 (by rfl) ⟨746600, by rfl⟩ : syracuseStep 995467 = 1493201) B1493201
theorem B1683595 : Blo 884570 1683595 := bstep (se 1 (by rfl) ⟨1262696, by rfl⟩ : syracuseStep 1683595 = 2525393) B2525393
theorem B995575 : Blo 884570 995575 := bstep (se 1 (by rfl) ⟨746681, by rfl⟩ : syracuseStep 995575 = 1493363) B1493363
theorem B995755 : Blo 884570 995755 := bstep (se 1 (by rfl) ⟨746816, by rfl⟩ : syracuseStep 995755 = 1493633) B1493633
theorem B1683929 : Blo 884570 1683929 := bstep (se 2 (by rfl) ⟨631473, by rfl⟩ : syracuseStep 1683929 = 1262947) B1262947
theorem B22196753 : Blo 884570 22196753 := bstep (se 2 (by rfl) ⟨8323782, by rfl⟩ : syracuseStep 22196753 = 16647565) B16647565
theorem B995863 : Blo 884570 995863 := bstep (se 1 (by rfl) ⟨746897, by rfl⟩ : syracuseStep 995863 = 1493795) B1493795
theorem B2241047 : Blo 884570 2241047 := bstep (se 1 (by rfl) ⟨1680785, by rfl⟩ : syracuseStep 2241047 = 3361571) B3361571
theorem B4043353 : Blo 884570 4043353 := bstep (se 2 (by rfl) ⟨1516257, by rfl⟩ : syracuseStep 4043353 = 3032515) B3032515
theorem B2994839 : Blo 884570 2994839 := bstep (se 1 (by rfl) ⟨2246129, by rfl⟩ : syracuseStep 2994839 = 4492259) B4492259
theorem B996043 : Blo 884570 996043 := bstep (se 1 (by rfl) ⟨747032, by rfl⟩ : syracuseStep 996043 = 1494065) B1494065
theorem B996151 : Blo 884570 996151 := bstep (se 1 (by rfl) ⟨747113, by rfl⟩ : syracuseStep 996151 = 1494227) B1494227
theorem B5059421 : Blo 884570 5059421 := bstep (se 3 (by rfl) ⟨948641, by rfl⟩ : syracuseStep 5059421 = 1897283) B1897283
theorem B996331 : Blo 884570 996331 := bstep (se 1 (by rfl) ⟨747248, by rfl⟩ : syracuseStep 996331 = 1494497) B1494497
theorem B996439 : Blo 884570 996439 := bstep (se 1 (by rfl) ⟨747329, by rfl⟩ : syracuseStep 996439 = 1494659) B1494659
theorem B1684567 : Blo 884570 1684567 := bstep (se 1 (by rfl) ⟨1263425, by rfl⟩ : syracuseStep 1684567 = 2526851) B2526851
theorem B2241715 : Blo 884570 2241715 := bstep (se 1 (by rfl) ⟨1681286, by rfl⟩ : syracuseStep 2241715 = 3362573) B3362573
theorem B2995379 : Blo 884570 2995379 := bstep (se 1 (by rfl) ⟨2246534, by rfl⟩ : syracuseStep 2995379 = 4493069) B4493069
theorem B996619 : Blo 884570 996619 := bstep (se 1 (by rfl) ⟨747464, by rfl⟩ : syracuseStep 996619 = 1494929) B1494929
theorem B2241857 : Blo 884570 2241857 := bstep (se 2 (by rfl) ⟨840696, by rfl⟩ : syracuseStep 2241857 = 1681393) B1681393
theorem B996727 : Blo 884570 996727 := bstep (se 1 (by rfl) ⟨747545, by rfl⟩ : syracuseStep 996727 = 1495091) B1495091
theorem B2995649 : Blo 884570 2995649 := bstep (se 2 (by rfl) ⟨1123368, by rfl⟩ : syracuseStep 2995649 = 2246737) B2246737
theorem B3192281 : Blo 884570 3192281 := bstep (se 2 (by rfl) ⟨1197105, by rfl⟩ : syracuseStep 3192281 = 2394211) B2394211
theorem B996907 : Blo 884570 996907 := bstep (se 1 (by rfl) ⟨747680, by rfl⟩ : syracuseStep 996907 = 1495361) B1495361
theorem B5060171 : Blo 884570 5060171 := bstep (se 1 (by rfl) ⟨3795128, by rfl⟩ : syracuseStep 5060171 = 7590257) B7590257
theorem B997015 : Blo 884570 997015 := bstep (se 1 (by rfl) ⟨747761, by rfl⟩ : syracuseStep 997015 = 1495523) B1495523
theorem B5682905 : Blo 884570 5682905 := bstep (se 2 (by rfl) ⟨2131089, by rfl⟩ : syracuseStep 5682905 = 4262179) B4262179
theorem B5125933 : Blo 884570 5125933 := bstep (se 3 (by rfl) ⟨961112, by rfl⟩ : syracuseStep 5125933 = 1922225) B1922225
theorem B6731585 : Blo 884570 6731585 := bstep (se 2 (by rfl) ⟨2524344, by rfl⟩ : syracuseStep 6731585 = 5048689) B5048689
theorem B997195 : Blo 884570 997195 := bstep (se 1 (by rfl) ⟨747896, by rfl⟩ : syracuseStep 997195 = 1495793) B1495793
theorem B1685387 : Blo 884570 1685387 := bstep (se 1 (by rfl) ⟨1264040, by rfl⟩ : syracuseStep 1685387 = 2528081) B2528081
theorem B997303 : Blo 884570 997303 := bstep (se 1 (by rfl) ⟨747977, by rfl⟩ : syracuseStep 997303 = 1495955) B1495955
theorem B1685441 : Blo 884570 1685441 := bstep (se 2 (by rfl) ⟨632040, by rfl⟩ : syracuseStep 1685441 = 1264081) B1264081
theorem B1259479 : Blo 884570 1259479 := bstep (se 1 (by rfl) ⟨944609, by rfl⟩ : syracuseStep 1259479 = 1889219) B1889219
theorem B2996189 : Blo 884570 2996189 := bstep (se 3 (by rfl) ⟨561785, by rfl⟩ : syracuseStep 2996189 = 1123571) B1123571
theorem B997483 : Blo 884570 997483 := bstep (se 1 (by rfl) ⟨748112, by rfl⟩ : syracuseStep 997483 = 1496225) B1496225
theorem B997591 : Blo 884570 997591 := bstep (se 1 (by rfl) ⟨748193, by rfl⟩ : syracuseStep 997591 = 1496387) B1496387
theorem B3782963 : Blo 884570 3782963 := bstep (se 1 (by rfl) ⟨2837222, by rfl⟩ : syracuseStep 3782963 = 5674445) B5674445
theorem B997771 : Blo 884570 997771 := bstep (se 1 (by rfl) ⟨748328, by rfl⟩ : syracuseStep 997771 = 1496657) B1496657
theorem B997879 : Blo 884570 997879 := bstep (se 1 (by rfl) ⟨748409, by rfl⟩ : syracuseStep 997879 = 1496819) B1496819
theorem B2243123 : Blo 884570 2243123 := bstep (se 1 (by rfl) ⟨1682342, by rfl⟩ : syracuseStep 2243123 = 3364685) B3364685
theorem B998059 : Blo 884570 998059 := bstep (se 1 (by rfl) ⟨748544, by rfl⟩ : syracuseStep 998059 = 1497089) B1497089
theorem B899767 : Blo 884570 899767 := bstep (se 1 (by rfl) ⟨674825, by rfl⟩ : syracuseStep 899767 = 1349651) B1349651
theorem B3029707 : Blo 884570 3029707 := bstep (se 1 (by rfl) ⟨2272280, by rfl⟩ : syracuseStep 3029707 = 4544561) B4544561
theorem B1260299 : Blo 884570 1260299 := bstep (se 1 (by rfl) ⟨945224, by rfl⟩ : syracuseStep 1260299 = 1890449) B1890449
theorem B998167 : Blo 884570 998167 := bstep (se 1 (by rfl) ⟨748625, by rfl⟩ : syracuseStep 998167 = 1497251) B1497251
theorem B1686359 : Blo 884570 1686359 := bstep (se 1 (by rfl) ⟨1264769, by rfl⟩ : syracuseStep 1686359 = 2529539) B2529539
theorem B998347 : Blo 884570 998347 := bstep (se 1 (by rfl) ⟨748760, by rfl⟩ : syracuseStep 998347 = 1497521) B1497521
theorem B998455 : Blo 884570 998455 := bstep (se 1 (by rfl) ⟨748841, by rfl⟩ : syracuseStep 998455 = 1497683) B1497683
theorem B2243659 : Blo 884570 2243659 := bstep (se 1 (by rfl) ⟨1682744, by rfl⟩ : syracuseStep 2243659 = 3365489) B3365489
theorem B2997323 : Blo 884570 2997323 := bstep (se 1 (by rfl) ⟨2247992, by rfl⟩ : syracuseStep 2997323 = 4495985) B4495985
theorem B2243801 : Blo 884570 2243801 := bstep (se 2 (by rfl) ⟨841425, by rfl⟩ : syracuseStep 2243801 = 1682851) B1682851
theorem B998635 : Blo 884570 998635 := bstep (se 1 (by rfl) ⟨748976, by rfl⟩ : syracuseStep 998635 = 1497953) B1497953
theorem B900343 : Blo 884570 900343 := bstep (se 1 (by rfl) ⟨675257, by rfl⟩ : syracuseStep 900343 = 1350515) B1350515
theorem B998743 : Blo 884570 998743 := bstep (se 1 (by rfl) ⟨749057, by rfl⟩ : syracuseStep 998743 = 1498115) B1498115
theorem B2997593 : Blo 884570 2997593 := bstep (se 2 (by rfl) ⟨1124097, by rfl⟩ : syracuseStep 2997593 = 2248195) B2248195
theorem B998923 : Blo 884570 998923 := bstep (se 1 (by rfl) ⟨749192, by rfl⟩ : syracuseStep 998923 = 1498385) B1498385
theorem B999031 : Blo 884570 999031 := bstep (se 1 (by rfl) ⟨749273, by rfl⟩ : syracuseStep 999031 = 1498547) B1498547
theorem B1261273 : Blo 884570 1261273 := bstep (se 2 (by rfl) ⟨472977, by rfl⟩ : syracuseStep 1261273 = 945955) B945955
theorem B6733529 : Blo 884570 6733529 := bstep (se 2 (by rfl) ⟨2525073, by rfl⟩ : syracuseStep 6733529 = 5050147) B5050147
theorem B999211 : Blo 884570 999211 := bstep (se 1 (by rfl) ⟨749408, by rfl⟩ : syracuseStep 999211 = 1498817) B1498817
theorem B1326923 : Blo 884570 1326923 := bstep (se 1 (by rfl) ⟨995192, by rfl⟩ : syracuseStep 1326923 = 1990385) B1990385
theorem B1326935 : Blo 884570 1326935 := bstep (se 1 (by rfl) ⟨995201, by rfl⟩ : syracuseStep 1326935 = 1990403) B1990403
theorem B2277209 : Blo 884570 2277209 := bstep (se 2 (by rfl) ⟨853953, by rfl⟩ : syracuseStep 2277209 = 1707907) B1707907
theorem B9715573 : Blo 884570 9715573 := bstep (se 5 (by rfl) ⟨455417, by rfl⟩ : syracuseStep 9715573 = 910835) B910835
theorem B999319 : Blo 884570 999319 := bstep (se 1 (by rfl) ⟨749489, by rfl⟩ : syracuseStep 999319 = 1498979) B1498979
theorem B1327001 : Blo 884570 1327001 := bstep (se 2 (by rfl) ⟨497625, by rfl⟩ : syracuseStep 1327001 = 995251) B995251
theorem B3358685 : Blo 884570 3358685 := bstep (se 3 (by rfl) ⟨629753, by rfl⟩ : syracuseStep 3358685 = 1259507) B1259507
theorem B1327115 : Blo 884570 1327115 := bstep (se 1 (by rfl) ⟨995336, by rfl⟩ : syracuseStep 1327115 = 1990673) B1990673
theorem B1327127 : Blo 884570 1327127 := bstep (se 1 (by rfl) ⟨995345, by rfl⟩ : syracuseStep 1327127 = 1990691) B1990691
theorem B2834455 : Blo 884570 2834455 := bstep (se 1 (by rfl) ⟨2125841, by rfl⟩ : syracuseStep 2834455 = 4251683) B4251683
theorem B2244631 : Blo 884570 2244631 := bstep (se 1 (by rfl) ⟨1683473, by rfl⟩ : syracuseStep 2244631 = 3366947) B3366947
theorem B2998295 : Blo 884570 2998295 := bstep (se 1 (by rfl) ⟨2248721, by rfl⟩ : syracuseStep 2998295 = 4497443) B4497443
theorem B12468259 : Blo 884570 12468259 := bstep (se 1 (by rfl) ⟨9351194, by rfl⟩ : syracuseStep 12468259 = 18702389) B18702389
theorem B2834507 : Blo 884570 2834507 := bstep (se 1 (by rfl) ⟨2125880, by rfl⟩ : syracuseStep 2834507 = 4251761) B4251761
theorem B999499 : Blo 884570 999499 := bstep (se 1 (by rfl) ⟨749624, by rfl⟩ : syracuseStep 999499 = 1499249) B1499249
theorem B1327193 : Blo 884570 1327193 := bstep (se 2 (by rfl) ⟨497697, by rfl⟩ : syracuseStep 1327193 = 995395) B995395
theorem B3784877 : Blo 884570 3784877 := bstep (se 3 (by rfl) ⟨709664, by rfl⟩ : syracuseStep 3784877 = 1419329) B1419329
theorem B999607 : Blo 884570 999607 := bstep (se 1 (by rfl) ⟨749705, by rfl⟩ : syracuseStep 999607 = 1499411) B1499411
theorem B1327307 : Blo 884570 1327307 := bstep (se 1 (by rfl) ⟨995480, by rfl⟩ : syracuseStep 1327307 = 1990961) B1990961
theorem B1327319 : Blo 884570 1327319 := bstep (se 1 (by rfl) ⟨995489, by rfl⟩ : syracuseStep 1327319 = 1990979) B1990979
theorem B1327385 : Blo 884570 1327385 := bstep (se 2 (by rfl) ⟨497769, by rfl⟩ : syracuseStep 1327385 = 995539) B995539
theorem B1327499 : Blo 884570 1327499 := bstep (se 1 (by rfl) ⟨995624, by rfl⟩ : syracuseStep 1327499 = 1991249) B1991249
theorem B1327511 : Blo 884570 1327511 := bstep (se 1 (by rfl) ⟨995633, by rfl⟩ : syracuseStep 1327511 = 1991267) B1991267
theorem B7193009 : Blo 884570 7193009 := bstep (se 2 (by rfl) ⟨2697378, by rfl⟩ : syracuseStep 7193009 = 5394757) B5394757
theorem B2245067 : Blo 884570 2245067 := bstep (se 1 (by rfl) ⟨1683800, by rfl⟩ : syracuseStep 2245067 = 3367601) B3367601
theorem B1327577 : Blo 884570 1327577 := bstep (se 2 (by rfl) ⟨497841, by rfl⟩ : syracuseStep 1327577 = 995683) B995683
theorem B2998835 : Blo 884570 2998835 := bstep (se 1 (by rfl) ⟨2249126, by rfl⟩ : syracuseStep 2998835 = 4498253) B4498253
theorem B1327691 : Blo 884570 1327691 := bstep (se 1 (by rfl) ⟨995768, by rfl⟩ : syracuseStep 1327691 = 1991537) B1991537
theorem B1327703 : Blo 884570 1327703 := bstep (se 1 (by rfl) ⟨995777, by rfl⟩ : syracuseStep 1327703 = 1991555) B1991555
theorem B1327769 : Blo 884570 1327769 := bstep (se 2 (by rfl) ⟨497913, by rfl⟩ : syracuseStep 1327769 = 995827) B995827
theorem B1196759 : Blo 884570 1196759 := bstep (se 1 (by rfl) ⟨897569, by rfl⟩ : syracuseStep 1196759 = 1795139) B1795139
theorem B1327883 : Blo 884570 1327883 := bstep (se 1 (by rfl) ⟨995912, by rfl⟩ : syracuseStep 1327883 = 1991825) B1991825
theorem B1327895 : Blo 884570 1327895 := bstep (se 1 (by rfl) ⟨995921, by rfl⟩ : syracuseStep 1327895 = 1991843) B1991843
theorem B3195713 : Blo 884570 3195713 := bstep (se 2 (by rfl) ⟨1198392, by rfl⟩ : syracuseStep 3195713 = 2396785) B2396785
theorem B2245441 : Blo 884570 2245441 := bstep (se 2 (by rfl) ⟨842040, by rfl⟩ : syracuseStep 2245441 = 1684081) B1684081
theorem B4801355 : Blo 884570 4801355 := bstep (se 1 (by rfl) ⟨3601016, by rfl⟩ : syracuseStep 4801355 = 7202033) B7202033
theorem B1262423 : Blo 884570 1262423 := bstep (se 1 (by rfl) ⟨946817, by rfl⟩ : syracuseStep 1262423 = 1893635) B1893635
theorem B1327961 : Blo 884570 1327961 := bstep (se 2 (by rfl) ⟨497985, by rfl⟩ : syracuseStep 1327961 = 995971) B995971
theorem B3785561 : Blo 884570 3785561 := bstep (se 2 (by rfl) ⟨1419585, by rfl⟩ : syracuseStep 3785561 = 2839171) B2839171
theorem B3031901 : Blo 884570 3031901 := bstep (se 3 (by rfl) ⟨568481, by rfl⟩ : syracuseStep 3031901 = 1136963) B1136963
theorem B5686109 : Blo 884570 5686109 := bstep (se 3 (by rfl) ⟨1066145, by rfl⟩ : syracuseStep 5686109 = 2132291) B2132291
theorem B1328075 : Blo 884570 1328075 := bstep (se 1 (by rfl) ⟨996056, by rfl⟩ : syracuseStep 1328075 = 1992113) B1992113
theorem B1328087 : Blo 884570 1328087 := bstep (se 1 (by rfl) ⟨996065, by rfl⟩ : syracuseStep 1328087 = 1992131) B1992131
theorem B1328153 : Blo 884570 1328153 := bstep (se 2 (by rfl) ⟨498057, by rfl⟩ : syracuseStep 1328153 = 996115) B996115
theorem B5686337 : Blo 884570 5686337 := bstep (se 2 (by rfl) ⟨2132376, by rfl⟩ : syracuseStep 5686337 = 4264753) B4264753
theorem B1328267 : Blo 884570 1328267 := bstep (se 1 (by rfl) ⟨996200, by rfl⟩ : syracuseStep 1328267 = 1992401) B1992401
theorem B1262731 : Blo 884570 1262731 := bstep (se 1 (by rfl) ⟨947048, by rfl⟩ : syracuseStep 1262731 = 1894097) B1894097
theorem B1328279 : Blo 884570 1328279 := bstep (se 1 (by rfl) ⟨996209, by rfl⟩ : syracuseStep 1328279 = 1992419) B1992419
theorem B1328345 : Blo 884570 1328345 := bstep (se 2 (by rfl) ⟨498129, by rfl⟩ : syracuseStep 1328345 = 996259) B996259
theorem B1328459 : Blo 884570 1328459 := bstep (se 1 (by rfl) ⟨996344, by rfl⟩ : syracuseStep 1328459 = 1992689) B1992689
theorem B1328471 : Blo 884570 1328471 := bstep (se 1 (by rfl) ⟨996353, by rfl⟩ : syracuseStep 1328471 = 1992707) B1992707
theorem B15582581 : Blo 884570 15582581 := bstep (se 5 (by rfl) ⟨730433, by rfl⟩ : syracuseStep 15582581 = 1460867) B1460867
theorem B2246039 : Blo 884570 2246039 := bstep (se 1 (by rfl) ⟨1684529, by rfl⟩ : syracuseStep 2246039 = 3369059) B3369059
theorem B1328537 : Blo 884570 1328537 := bstep (se 2 (by rfl) ⟨498201, by rfl⟩ : syracuseStep 1328537 = 996403) B996403
theorem B1328651 : Blo 884570 1328651 := bstep (se 1 (by rfl) ⟨996488, by rfl⟩ : syracuseStep 1328651 = 1992977) B1992977
theorem B1328663 : Blo 884570 1328663 := bstep (se 1 (by rfl) ⟨996497, by rfl⟩ : syracuseStep 1328663 = 1992995) B1992995
theorem B4605505 : Blo 884570 4605505 := bstep (se 2 (by rfl) ⟨1727064, by rfl⟩ : syracuseStep 4605505 = 3454129) B3454129
theorem B1328729 : Blo 884570 1328729 := bstep (se 2 (by rfl) ⟨498273, by rfl⟩ : syracuseStep 1328729 = 996547) B996547
theorem B5392003 : Blo 884570 5392003 := bstep (se 1 (by rfl) ⟨4044002, by rfl⟩ : syracuseStep 5392003 = 8088005) B8088005
theorem B2836147 : Blo 884570 2836147 := bstep (se 1 (by rfl) ⟨2127110, by rfl⟩ : syracuseStep 2836147 = 4254221) B4254221
theorem B1328843 : Blo 884570 1328843 := bstep (se 1 (by rfl) ⟨996632, by rfl⟩ : syracuseStep 1328843 = 1993265) B1993265
theorem B1328855 : Blo 884570 1328855 := bstep (se 1 (by rfl) ⟨996641, by rfl⟩ : syracuseStep 1328855 = 1993283) B1993283
theorem B3032855 : Blo 884570 3032855 := bstep (se 1 (by rfl) ⟨2274641, by rfl⟩ : syracuseStep 3032855 = 4549283) B4549283
theorem B1066775 : Blo 884570 1066775 := bstep (se 1 (by rfl) ⟨800081, by rfl⟩ : syracuseStep 1066775 = 1600163) B1600163
theorem B1328921 : Blo 884570 1328921 := bstep (se 2 (by rfl) ⟨498345, by rfl⟩ : syracuseStep 1328921 = 996691) B996691
theorem B2836289 : Blo 884570 2836289 := bstep (se 2 (by rfl) ⟨1063608, by rfl⟩ : syracuseStep 2836289 = 2127217) B2127217
theorem B1492823 : Blo 884570 1492823 := bstep (se 1 (by rfl) ⟨1119617, by rfl⟩ : syracuseStep 1492823 = 2239235) B2239235
theorem B1329035 : Blo 884570 1329035 := bstep (se 1 (by rfl) ⟨996776, by rfl⟩ : syracuseStep 1329035 = 1993553) B1993553
theorem B1329047 : Blo 884570 1329047 := bstep (se 1 (by rfl) ⟨996785, by rfl⟩ : syracuseStep 1329047 = 1993571) B1993571
theorem B51136433 : Blo 884570 51136433 := bstep (se 2 (by rfl) ⟨19176162, by rfl⟩ : syracuseStep 51136433 = 38352325) B38352325
theorem B3786689 : Blo 884570 3786689 := bstep (se 2 (by rfl) ⟨1420008, by rfl⟩ : syracuseStep 3786689 = 2840017) B2840017
theorem B1492951 : Blo 884570 1492951 := bstep (se 1 (by rfl) ⟨1119713, by rfl⟩ : syracuseStep 1492951 = 2239427) B2239427
theorem B1329113 : Blo 884570 1329113 := bstep (se 2 (by rfl) ⟨498417, by rfl⟩ : syracuseStep 1329113 = 996835) B996835
theorem B5752907 : Blo 884570 5752907 := bstep (se 1 (by rfl) ⟨4314680, by rfl⟩ : syracuseStep 5752907 = 8629361) B8629361
theorem B1329227 : Blo 884570 1329227 := bstep (se 1 (by rfl) ⟨996920, by rfl⟩ : syracuseStep 1329227 = 1993841) B1993841
theorem B1329239 : Blo 884570 1329239 := bstep (se 1 (by rfl) ⟨996929, by rfl⟩ : syracuseStep 1329239 = 1993859) B1993859
theorem B1263767 : Blo 884570 1263767 := bstep (se 1 (by rfl) ⟨947825, by rfl⟩ : syracuseStep 1263767 = 1895651) B1895651
theorem B1329305 : Blo 884570 1329305 := bstep (se 2 (by rfl) ⟨498489, by rfl⟩ : syracuseStep 1329305 = 996979) B996979
theorem B2246849 : Blo 884570 2246849 := bstep (se 2 (by rfl) ⟨842568, by rfl⟩ : syracuseStep 2246849 = 1685137) B1685137
theorem B1329419 : Blo 884570 1329419 := bstep (se 1 (by rfl) ⟨997064, by rfl⟩ : syracuseStep 1329419 = 1994129) B1994129
theorem B1329431 : Blo 884570 1329431 := bstep (se 1 (by rfl) ⟨997073, by rfl⟩ : syracuseStep 1329431 = 1994147) B1994147
theorem B1329497 : Blo 884570 1329497 := bstep (se 2 (by rfl) ⟨498561, by rfl⟩ : syracuseStep 1329497 = 997123) B997123
theorem B1263961 : Blo 884570 1263961 := bstep (se 2 (by rfl) ⟨473985, by rfl⟩ : syracuseStep 1263961 = 947971) B947971
theorem B1329611 : Blo 884570 1329611 := bstep (se 1 (by rfl) ⟨997208, by rfl⟩ : syracuseStep 1329611 = 1994417) B1994417
theorem B1067467 : Blo 884570 1067467 := bstep (se 1 (by rfl) ⟨800600, by rfl⟩ : syracuseStep 1067467 = 1601201) B1601201
theorem B1329623 : Blo 884570 1329623 := bstep (se 1 (by rfl) ⟨997217, by rfl⟩ : syracuseStep 1329623 = 1994435) B1994435
theorem B3361283 : Blo 884570 3361283 := bstep (se 1 (by rfl) ⟨2520962, by rfl⟩ : syracuseStep 3361283 = 5041925) B5041925
theorem B3361297 : Blo 884570 3361297 := bstep (se 2 (by rfl) ⟨1260486, by rfl⟩ : syracuseStep 3361297 = 2520973) B2520973
theorem B1329689 : Blo 884570 1329689 := bstep (se 2 (by rfl) ⟨498633, by rfl⟩ : syracuseStep 1329689 = 997267) B997267
theorem B1493579 : Blo 884570 1493579 := bstep (se 1 (by rfl) ⟨1120184, by rfl⟩ : syracuseStep 1493579 = 2240369) B2240369
theorem B3197515 : Blo 884570 3197515 := bstep (se 1 (by rfl) ⟨2398136, by rfl⟩ : syracuseStep 3197515 = 4796273) B4796273
theorem B1329803 : Blo 884570 1329803 := bstep (se 1 (by rfl) ⟨997352, by rfl⟩ : syracuseStep 1329803 = 1994705) B1994705
theorem B1329815 : Blo 884570 1329815 := bstep (se 1 (by rfl) ⟨997361, by rfl⟩ : syracuseStep 1329815 = 1994723) B1994723
theorem B1493707 : Blo 884570 1493707 := bstep (se 1 (by rfl) ⟨1120280, by rfl⟩ : syracuseStep 1493707 = 2240561) B2240561
theorem B1329881 : Blo 884570 1329881 := bstep (se 2 (by rfl) ⟨498705, by rfl⟩ : syracuseStep 1329881 = 997411) B997411
theorem B2247385 : Blo 884570 2247385 := bstep (se 2 (by rfl) ⟨842769, by rfl⟩ : syracuseStep 2247385 = 1685539) B1685539
theorem B3361601 : Blo 884570 3361601 := bstep (se 2 (by rfl) ⟨1260600, by rfl⟩ : syracuseStep 3361601 = 2521201) B2521201
theorem B1329995 : Blo 884570 1329995 := bstep (se 1 (by rfl) ⟨997496, by rfl⟩ : syracuseStep 1329995 = 1994993) B1994993
theorem B1330007 : Blo 884570 1330007 := bstep (se 1 (by rfl) ⟨997505, by rfl⟩ : syracuseStep 1330007 = 1995011) B1995011
theorem B1493849 : Blo 884570 1493849 := bstep (se 2 (by rfl) ⟨560193, by rfl⟩ : syracuseStep 1493849 = 1120387) B1120387
theorem B3197789 : Blo 884570 3197789 := bstep (se 3 (by rfl) ⟨599585, by rfl⟩ : syracuseStep 3197789 = 1199171) B1199171
theorem B1330073 : Blo 884570 1330073 := bstep (se 2 (by rfl) ⟨498777, by rfl⟩ : syracuseStep 1330073 = 997555) B997555
theorem B10079153 : Blo 884570 10079153 := bstep (se 2 (by rfl) ⟨3779682, by rfl⟩ : syracuseStep 10079153 = 7559365) B7559365
theorem B1493977 : Blo 884570 1493977 := bstep (se 2 (by rfl) ⟨560241, by rfl⟩ : syracuseStep 1493977 = 1120483) B1120483
theorem B1330187 : Blo 884570 1330187 := bstep (se 1 (by rfl) ⟨997640, by rfl⟩ : syracuseStep 1330187 = 1995281) B1995281
theorem B1330199 : Blo 884570 1330199 := bstep (se 1 (by rfl) ⟨997649, by rfl⟩ : syracuseStep 1330199 = 1995299) B1995299
theorem B6736931 : Blo 884570 6736931 := bstep (se 1 (by rfl) ⟨5052698, by rfl⟩ : syracuseStep 6736931 = 10105397) B10105397
theorem B1330265 : Blo 884570 1330265 := bstep (se 2 (by rfl) ⟨498849, by rfl⟩ : syracuseStep 1330265 = 997699) B997699
theorem B1330379 : Blo 884570 1330379 := bstep (se 1 (by rfl) ⟨997784, by rfl⟩ : syracuseStep 1330379 = 1995569) B1995569
theorem B1330391 : Blo 884570 1330391 := bstep (se 1 (by rfl) ⟨997793, by rfl⟩ : syracuseStep 1330391 = 1995587) B1995587
theorem B5688593 : Blo 884570 5688593 := bstep (se 2 (by rfl) ⟨2133222, by rfl⟩ : syracuseStep 5688593 = 4266445) B4266445
theorem B1330457 : Blo 884570 1330457 := bstep (se 2 (by rfl) ⟨498921, by rfl⟩ : syracuseStep 1330457 = 997843) B997843
theorem B1330571 : Blo 884570 1330571 := bstep (se 1 (by rfl) ⟨997928, by rfl⟩ : syracuseStep 1330571 = 1995857) B1995857
theorem B1330583 : Blo 884570 1330583 := bstep (se 1 (by rfl) ⟨997937, by rfl⟩ : syracuseStep 1330583 = 1995875) B1995875
theorem B1330649 : Blo 884570 1330649 := bstep (se 2 (by rfl) ⟨498993, by rfl⟩ : syracuseStep 1330649 = 997987) B997987
theorem B3362269 : Blo 884570 3362269 := bstep (se 3 (by rfl) ⟨630425, by rfl⟩ : syracuseStep 3362269 = 1260851) B1260851
theorem B1494551 : Blo 884570 1494551 := bstep (se 1 (by rfl) ⟨1120913, by rfl⟩ : syracuseStep 1494551 = 2241827) B2241827
theorem B3788363 : Blo 884570 3788363 := bstep (se 1 (by rfl) ⟨2841272, by rfl⟩ : syracuseStep 3788363 = 5682545) B5682545
theorem B1330763 : Blo 884570 1330763 := bstep (se 1 (by rfl) ⟨998072, by rfl⟩ : syracuseStep 1330763 = 1996145) B1996145
theorem B1330775 : Blo 884570 1330775 := bstep (se 1 (by rfl) ⟨998081, by rfl⟩ : syracuseStep 1330775 = 1996163) B1996163
theorem B1494679 : Blo 884570 1494679 := bstep (se 1 (by rfl) ⟨1121009, by rfl⟩ : syracuseStep 1494679 = 2242019) B2242019
theorem B1330841 : Blo 884570 1330841 := bstep (se 2 (by rfl) ⟨499065, by rfl⟩ : syracuseStep 1330841 = 998131) B998131
theorem B1330955 : Blo 884570 1330955 := bstep (se 1 (by rfl) ⟨998216, by rfl⟩ : syracuseStep 1330955 = 1996433) B1996433
theorem B1330967 : Blo 884570 1330967 := bstep (se 1 (by rfl) ⟨998225, by rfl⟩ : syracuseStep 1330967 = 1996451) B1996451
theorem B4050739 : Blo 884570 4050739 := bstep (se 1 (by rfl) ⟨3038054, by rfl⟩ : syracuseStep 4050739 = 6076109) B6076109
theorem B2248499 : Blo 884570 2248499 := bstep (se 1 (by rfl) ⟨1686374, by rfl⟩ : syracuseStep 2248499 = 3372749) B3372749
theorem B1331033 : Blo 884570 1331033 := bstep (se 2 (by rfl) ⟨499137, by rfl⟩ : syracuseStep 1331033 = 998275) B998275
theorem B1331147 : Blo 884570 1331147 := bstep (se 1 (by rfl) ⟨998360, by rfl⟩ : syracuseStep 1331147 = 1996721) B1996721
theorem B1331159 : Blo 884570 1331159 := bstep (se 1 (by rfl) ⟨998369, by rfl⟩ : syracuseStep 1331159 = 1996739) B1996739
theorem B1331225 : Blo 884570 1331225 := bstep (se 2 (by rfl) ⟨499209, by rfl⟩ : syracuseStep 1331225 = 998419) B998419
theorem B3199027 : Blo 884570 3199027 := bstep (se 1 (by rfl) ⟨2399270, by rfl⟩ : syracuseStep 3199027 = 4798541) B4798541
theorem B2248793 : Blo 884570 2248793 := bstep (se 2 (by rfl) ⟨843297, by rfl⟩ : syracuseStep 2248793 = 1686595) B1686595
theorem B1331339 : Blo 884570 1331339 := bstep (se 1 (by rfl) ⟨998504, by rfl⟩ : syracuseStep 1331339 = 1997009) B1997009
theorem B1331351 : Blo 884570 1331351 := bstep (se 1 (by rfl) ⟨998513, by rfl⟩ : syracuseStep 1331351 = 1997027) B1997027
theorem B1331417 : Blo 884570 1331417 := bstep (se 2 (by rfl) ⟨499281, by rfl⟩ : syracuseStep 1331417 = 998563) B998563
theorem B1495307 : Blo 884570 1495307 := bstep (se 1 (by rfl) ⟨1121480, by rfl⟩ : syracuseStep 1495307 = 2242961) B2242961
theorem B1331531 : Blo 884570 1331531 := bstep (se 1 (by rfl) ⟨998648, by rfl⟩ : syracuseStep 1331531 = 1997297) B1997297
theorem B1331543 : Blo 884570 1331543 := bstep (se 1 (by rfl) ⟨998657, by rfl⟩ : syracuseStep 1331543 = 1997315) B1997315
theorem B1495435 : Blo 884570 1495435 := bstep (se 1 (by rfl) ⟨1121576, by rfl⟩ : syracuseStep 1495435 = 2243153) B2243153
theorem B1200523 : Blo 884570 1200523 := bstep (se 1 (by rfl) ⟨900392, by rfl⟩ : syracuseStep 1200523 = 1800785) B1800785
theorem B1331609 : Blo 884570 1331609 := bstep (se 2 (by rfl) ⟨499353, by rfl⟩ : syracuseStep 1331609 = 998707) B998707
theorem B8507825 : Blo 884570 8507825 := bstep (se 2 (by rfl) ⟨3190434, by rfl⟩ : syracuseStep 8507825 = 6380869) B6380869
theorem B1331723 : Blo 884570 1331723 := bstep (se 1 (by rfl) ⟨998792, by rfl⟩ : syracuseStep 1331723 = 1997585) B1997585
theorem B1331735 : Blo 884570 1331735 := bstep (se 1 (by rfl) ⟨998801, by rfl⟩ : syracuseStep 1331735 = 1997603) B1997603
theorem B1495577 : Blo 884570 1495577 := bstep (se 2 (by rfl) ⟨560841, by rfl⟩ : syracuseStep 1495577 = 1121683) B1121683
theorem B1331801 : Blo 884570 1331801 := bstep (se 2 (by rfl) ⟨499425, by rfl⟩ : syracuseStep 1331801 = 998851) B998851
theorem B7557725 : Blo 884570 7557725 := bstep (se 3 (by rfl) ⟨1417073, by rfl⟩ : syracuseStep 7557725 = 2834147) B2834147
theorem B1495705 : Blo 884570 1495705 := bstep (se 2 (by rfl) ⟨560889, by rfl⟩ : syracuseStep 1495705 = 1121779) B1121779
theorem B1331915 : Blo 884570 1331915 := bstep (se 1 (by rfl) ⟨998936, by rfl⟩ : syracuseStep 1331915 = 1997873) B1997873
theorem B12800717 : Blo 884570 12800717 := bstep (se 3 (by rfl) ⟨2400134, by rfl⟩ : syracuseStep 12800717 = 4800269) B4800269
theorem B1331927 : Blo 884570 1331927 := bstep (se 1 (by rfl) ⟨998945, by rfl⟩ : syracuseStep 1331927 = 1997891) B1997891
theorem B3363545 : Blo 884570 3363545 := bstep (se 2 (by rfl) ⟨1261329, by rfl⟩ : syracuseStep 3363545 = 2522659) B2522659
theorem B1331993 : Blo 884570 1331993 := bstep (se 2 (by rfl) ⟨499497, by rfl⟩ : syracuseStep 1331993 = 998995) B998995
theorem B3789661 : Blo 884570 3789661 := bstep (se 3 (by rfl) ⟨710561, by rfl⟩ : syracuseStep 3789661 = 1421123) B1421123
theorem B1332107 : Blo 884570 1332107 := bstep (se 1 (by rfl) ⟨999080, by rfl⟩ : syracuseStep 1332107 = 1998161) B1998161
theorem B1332119 : Blo 884570 1332119 := bstep (se 1 (by rfl) ⟨999089, by rfl⟩ : syracuseStep 1332119 = 1998179) B1998179
theorem B2053043 : Blo 884570 2053043 := bstep (se 1 (by rfl) ⟨1539782, by rfl⟩ : syracuseStep 2053043 = 3079565) B3079565
theorem B1332185 : Blo 884570 1332185 := bstep (se 2 (by rfl) ⟨499569, by rfl⟩ : syracuseStep 1332185 = 999139) B999139
theorem B1332299 : Blo 884570 1332299 := bstep (se 1 (by rfl) ⟨999224, by rfl⟩ : syracuseStep 1332299 = 1998449) B1998449
theorem B1332311 : Blo 884570 1332311 := bstep (se 1 (by rfl) ⟨999233, by rfl⟩ : syracuseStep 1332311 = 1998467) B1998467
theorem B1332377 : Blo 884570 1332377 := bstep (se 2 (by rfl) ⟨499641, by rfl⟩ : syracuseStep 1332377 = 999283) B999283
theorem B3790003 : Blo 884570 3790003 := bstep (se 1 (by rfl) ⟨2842502, by rfl⟩ : syracuseStep 3790003 = 5685005) B5685005
theorem B1496279 : Blo 884570 1496279 := bstep (se 1 (by rfl) ⟨1122209, by rfl⟩ : syracuseStep 1496279 = 2244419) B2244419
theorem B1332491 : Blo 884570 1332491 := bstep (se 1 (by rfl) ⟨999368, by rfl⟩ : syracuseStep 1332491 = 1998737) B1998737
theorem B1332503 : Blo 884570 1332503 := bstep (se 1 (by rfl) ⟨999377, by rfl⟩ : syracuseStep 1332503 = 1998755) B1998755
theorem B1889561 : Blo 884570 1889561 := bstep (se 2 (by rfl) ⟨708585, by rfl⟩ : syracuseStep 1889561 = 1417171) B1417171
theorem B1496407 : Blo 884570 1496407 := bstep (se 1 (by rfl) ⟨1122305, by rfl⟩ : syracuseStep 1496407 = 2244611) B2244611
theorem B1332569 : Blo 884570 1332569 := bstep (se 2 (by rfl) ⟨499713, by rfl⟩ : syracuseStep 1332569 = 999427) B999427
theorem B3593651 : Blo 884570 3593651 := bstep (se 1 (by rfl) ⟨2695238, by rfl⟩ : syracuseStep 3593651 = 5390477) B5390477
theorem B1332683 : Blo 884570 1332683 := bstep (se 1 (by rfl) ⟨999512, by rfl⟩ : syracuseStep 1332683 = 1999025) B1999025
theorem B1332695 : Blo 884570 1332695 := bstep (se 1 (by rfl) ⟨999521, by rfl⟩ : syracuseStep 1332695 = 1999043) B1999043
theorem B1332761 : Blo 884570 1332761 := bstep (se 2 (by rfl) ⟨499785, by rfl⟩ : syracuseStep 1332761 = 999571) B999571
theorem B3593879 : Blo 884570 3593879 := bstep (se 1 (by rfl) ⟨2695409, by rfl⟩ : syracuseStep 3593879 = 5390819) B5390819
theorem B4478813 : Blo 884570 4478813 := bstep (se 3 (by rfl) ⟨839777, by rfl⟩ : syracuseStep 4478813 = 1679555) B1679555
theorem B1497035 : Blo 884570 1497035 := bstep (se 1 (by rfl) ⟨1122776, by rfl⟩ : syracuseStep 1497035 = 2245553) B2245553
theorem B87447605 : Blo 884570 87447605 := bstep (se 5 (by rfl) ⟨4099106, by rfl⟩ : syracuseStep 87447605 = 8198213) B8198213
theorem B1497163 : Blo 884570 1497163 := bstep (se 1 (by rfl) ⟨1122872, by rfl⟩ : syracuseStep 1497163 = 2245745) B2245745
theorem B1824983 : Blo 884570 1824983 := bstep (se 1 (by rfl) ⟨1368737, by rfl⟩ : syracuseStep 1824983 = 2737475) B2737475
theorem B2185433 : Blo 884570 2185433 := bstep (se 2 (by rfl) ⟨819537, by rfl⟩ : syracuseStep 2185433 = 1639075) B1639075
theorem B1497305 : Blo 884570 1497305 := bstep (se 2 (by rfl) ⟨561489, by rfl⟩ : syracuseStep 1497305 = 1122979) B1122979
theorem B1890611 : Blo 884570 1890611 := bstep (se 1 (by rfl) ⟨1417958, by rfl⟩ : syracuseStep 1890611 = 2835917) B2835917
theorem B3365171 : Blo 884570 3365171 := bstep (se 1 (by rfl) ⟨2523878, by rfl⟩ : syracuseStep 3365171 = 5047757) B5047757
theorem B3365185 : Blo 884570 3365185 := bstep (se 2 (by rfl) ⟨1261944, by rfl⟩ : syracuseStep 3365185 = 2523889) B2523889
theorem B1497433 : Blo 884570 1497433 := bstep (se 2 (by rfl) ⟨561537, by rfl⟩ : syracuseStep 1497433 = 1123075) B1123075
theorem B1366487 : Blo 884570 1366487 := bstep (se 1 (by rfl) ⟨1024865, by rfl⟩ : syracuseStep 1366487 = 2049731) B2049731
theorem B1891201 : Blo 884570 1891201 := bstep (se 2 (by rfl) ⟨709200, by rfl⟩ : syracuseStep 1891201 = 1418401) B1418401
theorem B1498007 : Blo 884570 1498007 := bstep (se 1 (by rfl) ⟨1123505, by rfl⟩ : syracuseStep 1498007 = 2247011) B2247011
theorem B1825715 : Blo 884570 1825715 := bstep (se 1 (by rfl) ⟨1369286, by rfl⟩ : syracuseStep 1825715 = 2738573) B2738573
theorem B6904793 : Blo 884570 6904793 := bstep (se 2 (by rfl) ⟨2589297, by rfl⟩ : syracuseStep 6904793 = 5178595) B5178595
theorem B1498135 : Blo 884570 1498135 := bstep (se 1 (by rfl) ⟨1123601, by rfl⟩ : syracuseStep 1498135 = 2247203) B2247203
theorem B7560323 : Blo 884570 7560323 := bstep (se 1 (by rfl) ⟨5670242, by rfl⟩ : syracuseStep 7560323 = 11340485) B11340485
theorem B1596761 : Blo 884570 1596761 := bstep (se 2 (by rfl) ⟨598785, by rfl⟩ : syracuseStep 1596761 = 1197571) B1197571
theorem B5693003 : Blo 884570 5693003 := bstep (se 1 (by rfl) ⟨4269752, by rfl⟩ : syracuseStep 5693003 = 8539505) B8539505
theorem B3595907 : Blo 884570 3595907 := bstep (se 1 (by rfl) ⟨2696930, by rfl⟩ : syracuseStep 3595907 = 5393861) B5393861
theorem B1498763 : Blo 884570 1498763 := bstep (se 1 (by rfl) ⟨1124072, by rfl⟩ : syracuseStep 1498763 = 2248145) B2248145
theorem B1990295 : Blo 884570 1990295 := bstep (se 1 (by rfl) ⟨1492721, by rfl⟩ : syracuseStep 1990295 = 2985443) B2985443
theorem B1498891 : Blo 884570 1498891 := bstep (se 1 (by rfl) ⟨1124168, by rfl⟩ : syracuseStep 1498891 = 2248337) B2248337
theorem B1990475 : Blo 884570 1990475 := bstep (se 1 (by rfl) ⟨1492856, by rfl⟩ : syracuseStep 1990475 = 2985713) B2985713
theorem B1597259 : Blo 884570 1597259 := bstep (se 1 (by rfl) ⟨1197944, by rfl⟩ : syracuseStep 1597259 = 2395889) B2395889
theorem B7298909 : Blo 884570 7298909 := bstep (se 3 (by rfl) ⟨1368545, by rfl⟩ : syracuseStep 7298909 = 2737091) B2737091
theorem B1990529 : Blo 884570 1990529 := bstep (se 2 (by rfl) ⟨746448, by rfl⟩ : syracuseStep 1990529 = 1492897) B1492897
theorem B4480919 : Blo 884570 4480919 := bstep (se 1 (by rfl) ⟨3360689, by rfl⟩ : syracuseStep 4480919 = 6721379) B6721379
theorem B1499033 : Blo 884570 1499033 := bstep (se 2 (by rfl) ⟨562137, by rfl⟩ : syracuseStep 1499033 = 1124275) B1124275
theorem B4251665 : Blo 884570 4251665 := bstep (se 2 (by rfl) ⟨1594374, by rfl⟩ : syracuseStep 4251665 = 3188749) B3188749
theorem B1499161 : Blo 884570 1499161 := bstep (se 2 (by rfl) ⟨562185, by rfl⟩ : syracuseStep 1499161 = 1124371) B1124371
theorem B1990745 : Blo 884570 1990745 := bstep (se 2 (by rfl) ⟨746529, by rfl⟩ : syracuseStep 1990745 = 1493059) B1493059
theorem B1990835 : Blo 884570 1990835 := bstep (se 1 (by rfl) ⟨1493126, by rfl⟩ : syracuseStep 1990835 = 2986253) B2986253
theorem B3367115 : Blo 884570 3367115 := bstep (se 1 (by rfl) ⟨2525336, by rfl⟩ : syracuseStep 3367115 = 5050673) B5050673
theorem B1990871 : Blo 884570 1990871 := bstep (se 1 (by rfl) ⟨1493153, by rfl⟩ : syracuseStep 1990871 = 2986307) B2986307
theorem B3367129 : Blo 884570 3367129 := bstep (se 2 (by rfl) ⟨1262673, by rfl⟩ : syracuseStep 3367129 = 2525347) B2525347
theorem B6742277 : Blo 884570 6742277 := bstep (se 4 (by rfl) ⟨632088, by rfl⟩ : syracuseStep 6742277 = 1264177) B1264177
theorem B1991051 : Blo 884570 1991051 := bstep (se 1 (by rfl) ⟨1493288, by rfl⟩ : syracuseStep 1991051 = 2986577) B2986577
theorem B1892747 : Blo 884570 1892747 := bstep (se 1 (by rfl) ⟨1419560, by rfl⟩ : syracuseStep 1892747 = 2839121) B2839121
theorem B1991105 : Blo 884570 1991105 := bstep (se 2 (by rfl) ⟨746664, by rfl⟩ : syracuseStep 1991105 = 1493329) B1493329
theorem B1991321 : Blo 884570 1991321 := bstep (se 2 (by rfl) ⟨746745, by rfl⟩ : syracuseStep 1991321 = 1493491) B1493491
theorem B3596993 : Blo 884570 3596993 := bstep (se 2 (by rfl) ⟨1348872, by rfl⟩ : syracuseStep 3596993 = 2697745) B2697745
theorem B3793625 : Blo 884570 3793625 := bstep (se 2 (by rfl) ⟨1422609, by rfl⟩ : syracuseStep 3793625 = 2845219) B2845219
theorem B1991411 : Blo 884570 1991411 := bstep (se 1 (by rfl) ⟨1493558, by rfl⟩ : syracuseStep 1991411 = 2987117) B2987117
theorem B1991447 : Blo 884570 1991447 := bstep (se 1 (by rfl) ⟨1493585, by rfl⟩ : syracuseStep 1991447 = 2987171) B2987171
theorem B3466115 : Blo 884570 3466115 := bstep (se 1 (by rfl) ⟨2599586, by rfl⟩ : syracuseStep 3466115 = 5199173) B5199173
theorem B1991627 : Blo 884570 1991627 := bstep (se 1 (by rfl) ⟨1493720, by rfl⟩ : syracuseStep 1991627 = 2987441) B2987441
theorem B1991681 : Blo 884570 1991681 := bstep (se 2 (by rfl) ⟨746880, by rfl⟩ : syracuseStep 1991681 = 1493761) B1493761
theorem B1795123 : Blo 884570 1795123 := bstep (se 1 (by rfl) ⟨1346342, by rfl⟩ : syracuseStep 1795123 = 2692685) B2692685
theorem B3368087 : Blo 884570 3368087 := bstep (se 1 (by rfl) ⟨2526065, by rfl⟩ : syracuseStep 3368087 = 5052131) B5052131
theorem B1991897 : Blo 884570 1991897 := bstep (se 2 (by rfl) ⟨746961, by rfl⟩ : syracuseStep 1991897 = 1493923) B1493923
theorem B1893593 : Blo 884570 1893593 := bstep (se 2 (by rfl) ⟨710097, by rfl⟩ : syracuseStep 1893593 = 1420195) B1420195
theorem B15164657 : Blo 884570 15164657 := bstep (se 2 (by rfl) ⟨5686746, by rfl⟩ : syracuseStep 15164657 = 11373493) B11373493
theorem B1991987 : Blo 884570 1991987 := bstep (se 1 (by rfl) ⟨1493990, by rfl⟩ : syracuseStep 1991987 = 2987981) B2987981
theorem B1992023 : Blo 884570 1992023 := bstep (se 1 (by rfl) ⟨1494017, by rfl⟩ : syracuseStep 1992023 = 2988035) B2988035
theorem B4253107 : Blo 884570 4253107 := bstep (se 1 (by rfl) ⟨3189830, by rfl⟩ : syracuseStep 4253107 = 6379661) B6379661
theorem B1992203 : Blo 884570 1992203 := bstep (se 1 (by rfl) ⟨1494152, by rfl⟩ : syracuseStep 1992203 = 2988305) B2988305
theorem B1992257 : Blo 884570 1992257 := bstep (se 2 (by rfl) ⟨747096, by rfl⟩ : syracuseStep 1992257 = 1494193) B1494193
theorem B1992473 : Blo 884570 1992473 := bstep (se 2 (by rfl) ⟨747177, by rfl⟩ : syracuseStep 1992473 = 1494355) B1494355
theorem B1992563 : Blo 884570 1992563 := bstep (se 1 (by rfl) ⟨1494422, by rfl⟩ : syracuseStep 1992563 = 2988845) B2988845
theorem B1992599 : Blo 884570 1992599 := bstep (se 1 (by rfl) ⟨1494449, by rfl⟩ : syracuseStep 1992599 = 2988899) B2988899
theorem B1894387 : Blo 884570 1894387 := bstep (se 1 (by rfl) ⟨1420790, by rfl⟩ : syracuseStep 1894387 = 2841581) B2841581
theorem B1009675 : Blo 884570 1009675 := bstep (se 1 (by rfl) ⟨757256, by rfl⟩ : syracuseStep 1009675 = 1514513) B1514513
theorem B2844695 : Blo 884570 2844695 := bstep (se 1 (by rfl) ⟨2133521, by rfl⟩ : syracuseStep 2844695 = 4267043) B4267043
theorem B1992779 : Blo 884570 1992779 := bstep (se 1 (by rfl) ⟨1494584, by rfl⟩ : syracuseStep 1992779 = 2989169) B2989169
theorem B1992833 : Blo 884570 1992833 := bstep (se 2 (by rfl) ⟨747312, by rfl⟩ : syracuseStep 1992833 = 1494625) B1494625
theorem B3795265 : Blo 884570 3795265 := bstep (se 2 (by rfl) ⟨1423224, by rfl⟩ : syracuseStep 3795265 = 2846449) B2846449
theorem B2845003 : Blo 884570 2845003 := bstep (se 1 (by rfl) ⟨2133752, by rfl⟩ : syracuseStep 2845003 = 4267505) B4267505
theorem B1993049 : Blo 884570 1993049 := bstep (se 2 (by rfl) ⟨747393, by rfl⟩ : syracuseStep 1993049 = 1494787) B1494787
theorem B3369347 : Blo 884570 3369347 := bstep (se 1 (by rfl) ⟨2527010, by rfl⟩ : syracuseStep 3369347 = 5054021) B5054021
theorem B1993139 : Blo 884570 1993139 := bstep (se 1 (by rfl) ⟨1494854, by rfl⟩ : syracuseStep 1993139 = 2989709) B2989709
theorem B1993175 : Blo 884570 1993175 := bstep (se 1 (by rfl) ⟨1494881, by rfl⟩ : syracuseStep 1993175 = 2989763) B2989763
theorem B16181795 : Blo 884570 16181795 := bstep (se 1 (by rfl) ⟨12136346, by rfl⟩ : syracuseStep 16181795 = 24272693) B24272693
theorem B6744707 : Blo 884570 6744707 := bstep (se 1 (by rfl) ⟨5058530, by rfl⟩ : syracuseStep 6744707 = 10117061) B10117061
theorem B1993355 : Blo 884570 1993355 := bstep (se 1 (by rfl) ⟨1495016, by rfl⟩ : syracuseStep 1993355 = 2990033) B2990033
theorem B1993409 : Blo 884570 1993409 := bstep (se 2 (by rfl) ⟨747528, by rfl⟩ : syracuseStep 1993409 = 1495057) B1495057
theorem B944951 : Blo 884570 944951 := bstep (se 1 (by rfl) ⟨708713, by rfl⟩ : syracuseStep 944951 = 1417427) B1417427
theorem B1895233 : Blo 884570 1895233 := bstep (se 2 (by rfl) ⟨710712, by rfl⟩ : syracuseStep 1895233 = 1421425) B1421425
theorem B1993625 : Blo 884570 1993625 := bstep (se 2 (by rfl) ⟨747609, by rfl⟩ : syracuseStep 1993625 = 1495219) B1495219
theorem B2878429 : Blo 884570 2878429 := bstep (se 3 (by rfl) ⟨539705, by rfl⟩ : syracuseStep 2878429 = 1079411) B1079411
theorem B1993715 : Blo 884570 1993715 := bstep (se 1 (by rfl) ⟨1495286, by rfl⟩ : syracuseStep 1993715 = 2990573) B2990573
theorem B1993751 : Blo 884570 1993751 := bstep (se 1 (by rfl) ⟨1495313, by rfl⟩ : syracuseStep 1993751 = 2990627) B2990627
theorem B5041217 : Blo 884570 5041217 := bstep (se 2 (by rfl) ⟨1890456, by rfl⟩ : syracuseStep 5041217 = 3780913) B3780913
theorem B1895575 : Blo 884570 1895575 := bstep (se 1 (by rfl) ⟨1421681, by rfl⟩ : syracuseStep 1895575 = 2843363) B2843363
theorem B1993931 : Blo 884570 1993931 := bstep (se 1 (by rfl) ⟨1495448, by rfl⟩ : syracuseStep 1993931 = 2990897) B2990897
theorem B1993985 : Blo 884570 1993985 := bstep (se 2 (by rfl) ⟨747744, by rfl⟩ : syracuseStep 1993985 = 1495489) B1495489
theorem B4484483 : Blo 884570 4484483 := bstep (se 1 (by rfl) ⟨3363362, by rfl⟩ : syracuseStep 4484483 = 6726725) B6726725
theorem B1994201 : Blo 884570 1994201 := bstep (se 2 (by rfl) ⟨747825, by rfl⟩ : syracuseStep 1994201 = 1495651) B1495651
theorem B1600985 : Blo 884570 1600985 := bstep (se 2 (by rfl) ⟨600369, by rfl⟩ : syracuseStep 1600985 = 1200739) B1200739
theorem B1994291 : Blo 884570 1994291 := bstep (se 1 (by rfl) ⟨1495718, by rfl⟩ : syracuseStep 1994291 = 2991437) B2991437
theorem B1994327 : Blo 884570 1994327 := bstep (se 1 (by rfl) ⟨1495745, by rfl⟩ : syracuseStep 1994327 = 2991491) B2991491
theorem B109080269 : Blo 884570 109080269 := bstep (se 3 (by rfl) ⟨20452550, by rfl⟩ : syracuseStep 109080269 = 40905101) B40905101
theorem B1994507 : Blo 884570 1994507 := bstep (se 1 (by rfl) ⟨1495880, by rfl⟩ : syracuseStep 1994507 = 2991761) B2991761
theorem B1994561 : Blo 884570 1994561 := bstep (se 2 (by rfl) ⟨747960, by rfl⟩ : syracuseStep 1994561 = 1495921) B1495921
theorem B1437655 : Blo 884570 1437655 := bstep (se 1 (by rfl) ⟨1078241, by rfl⟩ : syracuseStep 1437655 = 2156483) B2156483
theorem B1994777 : Blo 884570 1994777 := bstep (se 2 (by rfl) ⟨748041, by rfl⟩ : syracuseStep 1994777 = 1496083) B1496083
theorem B1994867 : Blo 884570 1994867 := bstep (se 1 (by rfl) ⟨1496150, by rfl⟩ : syracuseStep 1994867 = 2992301) B2992301
theorem B1994903 : Blo 884570 1994903 := bstep (se 1 (by rfl) ⟨1496177, by rfl⟩ : syracuseStep 1994903 = 2992355) B2992355
theorem B1995083 : Blo 884570 1995083 := bstep (se 1 (by rfl) ⟨1496312, by rfl⟩ : syracuseStep 1995083 = 2992625) B2992625
theorem B1896779 : Blo 884570 1896779 := bstep (se 1 (by rfl) ⟨1422584, by rfl⟩ : syracuseStep 1896779 = 2845169) B2845169
theorem B1995137 : Blo 884570 1995137 := bstep (se 2 (by rfl) ⟨748176, by rfl⟩ : syracuseStep 1995137 = 1496353) B1496353
theorem B946775 : Blo 884570 946775 := bstep (se 1 (by rfl) ⟨710081, by rfl⟩ : syracuseStep 946775 = 1420163) B1420163
theorem B1995353 : Blo 884570 1995353 := bstep (se 2 (by rfl) ⟨748257, by rfl⟩ : syracuseStep 1995353 = 1496515) B1496515
theorem B1995443 : Blo 884570 1995443 := bstep (se 1 (by rfl) ⟨1496582, by rfl⟩ : syracuseStep 1995443 = 2993165) B2993165
theorem B2880193 : Blo 884570 2880193 := bstep (se 2 (by rfl) ⟨1080072, by rfl⟩ : syracuseStep 2880193 = 2160145) B2160145
theorem B19690189 : Blo 884570 19690189 := bstep (se 3 (by rfl) ⟨3691910, by rfl⟩ : syracuseStep 19690189 = 7383821) B7383821
theorem B1995479 : Blo 884570 1995479 := bstep (se 1 (by rfl) ⟨1496609, by rfl⟩ : syracuseStep 1995479 = 2993219) B2993219
theorem B1897291 : Blo 884570 1897291 := bstep (se 1 (by rfl) ⟨1422968, by rfl⟩ : syracuseStep 1897291 = 2845937) B2845937
theorem B1995659 : Blo 884570 1995659 := bstep (se 1 (by rfl) ⟨1496744, by rfl⟩ : syracuseStep 1995659 = 2993489) B2993489
theorem B1995713 : Blo 884570 1995713 := bstep (se 2 (by rfl) ⟨748392, by rfl⟩ : syracuseStep 1995713 = 1496785) B1496785
theorem B6911041 : Blo 884570 6911041 := bstep (se 2 (by rfl) ⟨2591640, by rfl⟩ : syracuseStep 6911041 = 5183281) B5183281
theorem B1995929 : Blo 884570 1995929 := bstep (se 2 (by rfl) ⟨748473, by rfl⟩ : syracuseStep 1995929 = 1496947) B1496947
theorem B2880715 : Blo 884570 2880715 := bstep (se 1 (by rfl) ⟨2160536, by rfl⟩ : syracuseStep 2880715 = 4321073) B4321073
theorem B1996019 : Blo 884570 1996019 := bstep (se 1 (by rfl) ⟨1497014, by rfl⟩ : syracuseStep 1996019 = 2994029) B2994029
theorem B947467 : Blo 884570 947467 := bstep (se 1 (by rfl) ⟨710600, by rfl⟩ : syracuseStep 947467 = 1421201) B1421201
theorem B1996055 : Blo 884570 1996055 := bstep (se 1 (by rfl) ⟨1497041, by rfl⟩ : syracuseStep 1996055 = 2994083) B2994083
theorem B3372461 : Blo 884570 3372461 := bstep (se 3 (by rfl) ⟨632336, by rfl⟩ : syracuseStep 3372461 = 1264673) B1264673
theorem B1996235 : Blo 884570 1996235 := bstep (se 1 (by rfl) ⟨1497176, by rfl⟩ : syracuseStep 1996235 = 2994353) B2994353
theorem B1996289 : Blo 884570 1996289 := bstep (se 2 (by rfl) ⟨748608, by rfl⟩ : syracuseStep 1996289 = 1497217) B1497217
theorem B1996505 : Blo 884570 1996505 := bstep (se 2 (by rfl) ⟨748689, by rfl⟩ : syracuseStep 1996505 = 1497379) B1497379
theorem B1996595 : Blo 884570 1996595 := bstep (se 1 (by rfl) ⟨1497446, by rfl⟩ : syracuseStep 1996595 = 2994893) B2994893
theorem B1996631 : Blo 884570 1996631 := bstep (se 1 (by rfl) ⟨1497473, by rfl⟩ : syracuseStep 1996631 = 2994947) B2994947
theorem B2127833 : Blo 884570 2127833 := bstep (se 2 (by rfl) ⟨797937, by rfl⟩ : syracuseStep 2127833 = 1595875) B1595875
theorem B6387673 : Blo 884570 6387673 := bstep (se 2 (by rfl) ⟨2395377, by rfl⟩ : syracuseStep 6387673 = 4790755) B4790755
theorem B1996811 : Blo 884570 1996811 := bstep (se 1 (by rfl) ⟨1497608, by rfl⟩ : syracuseStep 1996811 = 2995217) B2995217
theorem B1996865 : Blo 884570 1996865 := bstep (se 2 (by rfl) ⟨748824, by rfl⟩ : syracuseStep 1996865 = 1497649) B1497649
theorem B3373235 : Blo 884570 3373235 := bstep (se 1 (by rfl) ⟨2529926, by rfl⟩ : syracuseStep 3373235 = 5059853) B5059853
theorem B1997081 : Blo 884570 1997081 := bstep (se 2 (by rfl) ⟨748905, by rfl⟩ : syracuseStep 1997081 = 1497811) B1497811
theorem B10090817 : Blo 884570 10090817 := bstep (se 2 (by rfl) ⟨3784056, by rfl⟩ : syracuseStep 10090817 = 7568113) B7568113
theorem B1997171 : Blo 884570 1997171 := bstep (se 1 (by rfl) ⟨1497878, by rfl⟩ : syracuseStep 1997171 = 2995757) B2995757
theorem B1997207 : Blo 884570 1997207 := bstep (se 1 (by rfl) ⟨1497905, by rfl⟩ : syracuseStep 1997207 = 2995811) B2995811
theorem B948791 : Blo 884570 948791 := bstep (se 1 (by rfl) ⟨711593, by rfl⟩ : syracuseStep 948791 = 1423187) B1423187
theorem B1997387 : Blo 884570 1997387 := bstep (se 1 (by rfl) ⟨1498040, by rfl⟩ : syracuseStep 1997387 = 2996081) B2996081
theorem B1997441 : Blo 884570 1997441 := bstep (se 2 (by rfl) ⟨749040, by rfl⟩ : syracuseStep 1997441 = 1498081) B1498081
theorem B2521793 : Blo 884570 2521793 := bstep (se 2 (by rfl) ⟨945672, by rfl⟩ : syracuseStep 2521793 = 1891345) B1891345
theorem B2521817 : Blo 884570 2521817 := bstep (se 2 (by rfl) ⟨945681, by rfl⟩ : syracuseStep 2521817 = 1891363) B1891363
theorem B2128601 : Blo 884570 2128601 := bstep (se 2 (by rfl) ⟨798225, by rfl⟩ : syracuseStep 2128601 = 1596451) B1596451
theorem B1702657 : Blo 884570 1702657 := bstep (se 2 (by rfl) ⟨638496, by rfl⟩ : syracuseStep 1702657 = 1276993) B1276993
theorem B1997657 : Blo 884570 1997657 := bstep (se 2 (by rfl) ⟨749121, by rfl⟩ : syracuseStep 1997657 = 1498243) B1498243
theorem B11369393 : Blo 884570 11369393 := bstep (se 2 (by rfl) ⟨4263522, by rfl⟩ : syracuseStep 11369393 = 8527045) B8527045
theorem B1997747 : Blo 884570 1997747 := bstep (se 1 (by rfl) ⟨1498310, by rfl⟩ : syracuseStep 1997747 = 2996621) B2996621
theorem B1997783 : Blo 884570 1997783 := bstep (se 1 (by rfl) ⟨1498337, by rfl⟩ : syracuseStep 1997783 = 2996675) B2996675
theorem B4488209 : Blo 884570 4488209 := bstep (se 2 (by rfl) ⟨1683078, by rfl⟩ : syracuseStep 4488209 = 3366157) B3366157
theorem B12155939 : Blo 884570 12155939 := bstep (se 1 (by rfl) ⟨9116954, by rfl⟩ : syracuseStep 12155939 = 18233909) B18233909
theorem B4258909 : Blo 884570 4258909 := bstep (se 3 (by rfl) ⟨798545, by rfl⟩ : syracuseStep 4258909 = 1597091) B1597091
theorem B1997963 : Blo 884570 1997963 := bstep (se 1 (by rfl) ⟨1498472, by rfl⟩ : syracuseStep 1997963 = 2996945) B2996945
theorem B1801367 : Blo 884570 1801367 := bstep (se 1 (by rfl) ⟨1351025, by rfl⟩ : syracuseStep 1801367 = 2702051) B2702051
theorem B4488371 : Blo 884570 4488371 := bstep (se 1 (by rfl) ⟨3366278, by rfl⟩ : syracuseStep 4488371 = 6732557) B6732557
theorem B1998017 : Blo 884570 1998017 := bstep (se 2 (by rfl) ⟨749256, by rfl⟩ : syracuseStep 1998017 = 1498513) B1498513
theorem B3636631 : Blo 884570 3636631 := bstep (se 1 (by rfl) ⟨2727473, by rfl⟩ : syracuseStep 3636631 = 5454947) B5454947
theorem B1998233 : Blo 884570 1998233 := bstep (se 2 (by rfl) ⟨749337, by rfl⟩ : syracuseStep 1998233 = 1498675) B1498675
theorem B1998323 : Blo 884570 1998323 := bstep (se 1 (by rfl) ⟨1498742, by rfl⟩ : syracuseStep 1998323 = 2997485) B2997485
theorem B1211927 : Blo 884570 1211927 := bstep (se 1 (by rfl) ⟨908945, by rfl⟩ : syracuseStep 1211927 = 1817891) B1817891
theorem B1998359 : Blo 884570 1998359 := bstep (se 1 (by rfl) ⟨1498769, by rfl⟩ : syracuseStep 1998359 = 2997539) B2997539
theorem B3636829 : Blo 884570 3636829 := bstep (se 3 (by rfl) ⟨681905, by rfl⟩ : syracuseStep 3636829 = 1363811) B1363811
theorem B1998539 : Blo 884570 1998539 := bstep (se 1 (by rfl) ⟨1498904, by rfl⟩ : syracuseStep 1998539 = 2997809) B2997809
theorem B1998593 : Blo 884570 1998593 := bstep (se 2 (by rfl) ⟨749472, by rfl⟩ : syracuseStep 1998593 = 1498945) B1498945
theorem B1441547 : Blo 884570 1441547 := bstep (se 1 (by rfl) ⟨1081160, by rfl⟩ : syracuseStep 1441547 = 2162321) B2162321
theorem B884587 : Blo 884570 884587 := bstep (se 1 (by rfl) ⟨663440, by rfl⟩ : syracuseStep 884587 = 1326881) B1326881
theorem B884599 : Blo 884570 884599 := bstep (se 1 (by rfl) ⟨663449, by rfl⟩ : syracuseStep 884599 = 1326899) B1326899
theorem B884619 : Blo 884570 884619 := bstep (se 1 (by rfl) ⟨663464, by rfl⟩ : syracuseStep 884619 = 1326929) B1326929
theorem B884631 : Blo 884570 884631 := bstep (se 1 (by rfl) ⟨663473, by rfl⟩ : syracuseStep 884631 = 1326947) B1326947
theorem B884651 : Blo 884570 884651 := bstep (se 1 (by rfl) ⟨663488, by rfl⟩ : syracuseStep 884651 = 1326977) B1326977
theorem B2523059 : Blo 884570 2523059 := bstep (se 1 (by rfl) ⟨1892294, by rfl⟩ : syracuseStep 2523059 = 3784589) B3784589
theorem B884663 : Blo 884570 884663 := bstep (se 1 (by rfl) ⟨663497, by rfl⟩ : syracuseStep 884663 = 1326995) B1326995
theorem B884683 : Blo 884570 884683 := bstep (se 1 (by rfl) ⟨663512, by rfl⟩ : syracuseStep 884683 = 1327025) B1327025
theorem B884695 : Blo 884570 884695 := bstep (se 1 (by rfl) ⟨663521, by rfl⟩ : syracuseStep 884695 = 1327043) B1327043
theorem B1998809 : Blo 884570 1998809 := bstep (se 2 (by rfl) ⟨749553, by rfl⟩ : syracuseStep 1998809 = 1499107) B1499107
theorem B884715 : Blo 884570 884715 := bstep (se 1 (by rfl) ⟨663536, by rfl⟩ : syracuseStep 884715 = 1327073) B1327073
theorem B884727 : Blo 884570 884727 := bstep (se 1 (by rfl) ⟨663545, by rfl⟩ : syracuseStep 884727 = 1327091) B1327091
theorem B884743 : Blo 884570 884743 := bstep (se 1 (by rfl) ⟨663557, by rfl⟩ : syracuseStep 884743 = 1327115) B1327115
theorem B884751 : Blo 884570 884751 := bstep (se 1 (by rfl) ⟨663563, by rfl⟩ : syracuseStep 884751 = 1327127) B1327127
theorem B1998863 : Blo 884570 1998863 := bstep (se 1 (by rfl) ⟨1499147, by rfl⟩ : syracuseStep 1998863 = 2998295) B2998295
theorem B1998881 : Blo 884570 1998881 := bstep (se 2 (by rfl) ⟨749580, by rfl⟩ : syracuseStep 1998881 = 1499161) B1499161
theorem B884795 : Blo 884570 884795 := bstep (se 1 (by rfl) ⟨663596, by rfl⟩ : syracuseStep 884795 = 1327193) B1327193
theorem B2523251 : Blo 884570 2523251 := bstep (se 1 (by rfl) ⟨1892438, by rfl⟩ : syracuseStep 2523251 = 3784877) B3784877
theorem B884871 : Blo 884570 884871 := bstep (se 1 (by rfl) ⟨663653, by rfl⟩ : syracuseStep 884871 = 1327307) B1327307
theorem B884879 : Blo 884570 884879 := bstep (se 1 (by rfl) ⟨663659, by rfl⟩ : syracuseStep 884879 = 1327319) B1327319
theorem B884923 : Blo 884570 884923 := bstep (se 1 (by rfl) ⟨663692, by rfl⟩ : syracuseStep 884923 = 1327385) B1327385
theorem B884999 : Blo 884570 884999 := bstep (se 1 (by rfl) ⟨663749, by rfl⟩ : syracuseStep 884999 = 1327499) B1327499
theorem B885007 : Blo 884570 885007 := bstep (se 1 (by rfl) ⟨663755, by rfl⟩ : syracuseStep 885007 = 1327511) B1327511
theorem B4489505 : Blo 884570 4489505 := bstep (se 2 (by rfl) ⟨1683564, by rfl⟩ : syracuseStep 4489505 = 3367129) B3367129
theorem B885051 : Blo 884570 885051 := bstep (se 1 (by rfl) ⟨663788, by rfl⟩ : syracuseStep 885051 = 1327577) B1327577
theorem B10944827 : Blo 884570 10944827 := bstep (se 1 (by rfl) ⟨8208620, by rfl⟩ : syracuseStep 10944827 = 16417241) B16417241
theorem B1999223 : Blo 884570 1999223 := bstep (se 1 (by rfl) ⟨1499417, by rfl⟩ : syracuseStep 1999223 = 2998835) B2998835
theorem B885127 : Blo 884570 885127 := bstep (se 1 (by rfl) ⟨663845, by rfl⟩ : syracuseStep 885127 = 1327691) B1327691
theorem B885135 : Blo 884570 885135 := bstep (se 1 (by rfl) ⟨663851, by rfl⟩ : syracuseStep 885135 = 1327703) B1327703
theorem B885179 : Blo 884570 885179 := bstep (se 1 (by rfl) ⟨663884, by rfl⟩ : syracuseStep 885179 = 1327769) B1327769
theorem B5046731 : Blo 884570 5046731 := bstep (se 1 (by rfl) ⟨3785048, by rfl⟩ : syracuseStep 5046731 = 7570097) B7570097
theorem B885255 : Blo 884570 885255 := bstep (se 1 (by rfl) ⟨663941, by rfl⟩ : syracuseStep 885255 = 1327883) B1327883
theorem B885263 : Blo 884570 885263 := bstep (se 1 (by rfl) ⟨663947, by rfl⟩ : syracuseStep 885263 = 1327895) B1327895
theorem B2130475 : Blo 884570 2130475 := bstep (se 1 (by rfl) ⟨1597856, by rfl⟩ : syracuseStep 2130475 = 3195713) B3195713
theorem B932774453 : Blo 884570 932774453 := bstep (se 5 (by rfl) ⟨43723802, by rfl⟩ : syracuseStep 932774453 = 87447605) B87447605
theorem B885307 : Blo 884570 885307 := bstep (se 1 (by rfl) ⟨663980, by rfl⟩ : syracuseStep 885307 = 1327961) B1327961
theorem B2523707 : Blo 884570 2523707 := bstep (se 1 (by rfl) ⟨1892780, by rfl⟩ : syracuseStep 2523707 = 3785561) B3785561
theorem B885383 : Blo 884570 885383 := bstep (se 1 (by rfl) ⟨664037, by rfl⟩ : syracuseStep 885383 = 1328075) B1328075
theorem B885391 : Blo 884570 885391 := bstep (se 1 (by rfl) ⟨664043, by rfl⟩ : syracuseStep 885391 = 1328087) B1328087
theorem B4981421 : Blo 884570 4981421 := bstep (se 3 (by rfl) ⟨934016, by rfl⟩ : syracuseStep 4981421 = 1868033) B1868033
theorem B885435 : Blo 884570 885435 := bstep (se 1 (by rfl) ⟨664076, by rfl⟩ : syracuseStep 885435 = 1328153) B1328153
theorem B3408641 : Blo 884570 3408641 := bstep (se 2 (by rfl) ⟨1278240, by rfl⟩ : syracuseStep 3408641 = 2556481) B2556481
theorem B885511 : Blo 884570 885511 := bstep (se 1 (by rfl) ⟨664133, by rfl⟩ : syracuseStep 885511 = 1328267) B1328267
theorem B885519 : Blo 884570 885519 := bstep (se 1 (by rfl) ⟨664139, by rfl⟩ : syracuseStep 885519 = 1328279) B1328279
theorem B885563 : Blo 884570 885563 := bstep (se 1 (by rfl) ⟨664172, by rfl⟩ : syracuseStep 885563 = 1328345) B1328345
theorem B885639 : Blo 884570 885639 := bstep (se 1 (by rfl) ⟨664229, by rfl⟩ : syracuseStep 885639 = 1328459) B1328459
theorem B885647 : Blo 884570 885647 := bstep (se 1 (by rfl) ⟨664235, by rfl⟩ : syracuseStep 885647 = 1328471) B1328471
theorem B4260755 : Blo 884570 4260755 := bstep (se 1 (by rfl) ⟨3195566, by rfl⟩ : syracuseStep 4260755 = 6391133) B6391133
theorem B10388387 : Blo 884570 10388387 := bstep (se 1 (by rfl) ⟨7791290, by rfl⟩ : syracuseStep 10388387 = 15582581) B15582581
theorem B885691 : Blo 884570 885691 := bstep (se 1 (by rfl) ⟨664268, by rfl⟩ : syracuseStep 885691 = 1328537) B1328537
theorem B885767 : Blo 884570 885767 := bstep (se 1 (by rfl) ⟨664325, by rfl⟩ : syracuseStep 885767 = 1328651) B1328651
theorem B885775 : Blo 884570 885775 := bstep (se 1 (by rfl) ⟨664331, by rfl⟩ : syracuseStep 885775 = 1328663) B1328663
theorem B885819 : Blo 884570 885819 := bstep (se 1 (by rfl) ⟨664364, by rfl⟩ : syracuseStep 885819 = 1328729) B1328729
theorem B885895 : Blo 884570 885895 := bstep (se 1 (by rfl) ⟨664421, by rfl⟩ : syracuseStep 885895 = 1328843) B1328843
theorem B885903 : Blo 884570 885903 := bstep (se 1 (by rfl) ⟨664427, by rfl⟩ : syracuseStep 885903 = 1328855) B1328855
theorem B885947 : Blo 884570 885947 := bstep (se 1 (by rfl) ⟨664460, by rfl⟩ : syracuseStep 885947 = 1328921) B1328921
theorem B4490477 : Blo 884570 4490477 := bstep (se 3 (by rfl) ⟨841964, by rfl⟩ : syracuseStep 4490477 = 1683929) B1683929
theorem B16188653 : Blo 884570 16188653 := bstep (se 3 (by rfl) ⟨3035372, by rfl⟩ : syracuseStep 16188653 = 6070745) B6070745
theorem B886023 : Blo 884570 886023 := bstep (se 1 (by rfl) ⟨664517, by rfl⟩ : syracuseStep 886023 = 1329035) B1329035
theorem B886031 : Blo 884570 886031 := bstep (se 1 (by rfl) ⟨664523, by rfl⟩ : syracuseStep 886031 = 1329047) B1329047
theorem B2524459 : Blo 884570 2524459 := bstep (se 1 (by rfl) ⟨1893344, by rfl⟩ : syracuseStep 2524459 = 3786689) B3786689
theorem B886075 : Blo 884570 886075 := bstep (se 1 (by rfl) ⟨664556, by rfl⟩ : syracuseStep 886075 = 1329113) B1329113
theorem B3835271 : Blo 884570 3835271 := bstep (se 1 (by rfl) ⟨2876453, by rfl⟩ : syracuseStep 3835271 = 5752907) B5752907
theorem B886151 : Blo 884570 886151 := bstep (se 1 (by rfl) ⟨664613, by rfl⟩ : syracuseStep 886151 = 1329227) B1329227
theorem B886159 : Blo 884570 886159 := bstep (se 1 (by rfl) ⟨664619, by rfl⟩ : syracuseStep 886159 = 1329239) B1329239
theorem B2393497 : Blo 884570 2393497 := bstep (se 2 (by rfl) ⟨897561, by rfl⟩ : syracuseStep 2393497 = 1795123) B1795123
theorem B886203 : Blo 884570 886203 := bstep (se 1 (by rfl) ⟨664652, by rfl⟩ : syracuseStep 886203 = 1329305) B1329305
theorem B886279 : Blo 884570 886279 := bstep (se 1 (by rfl) ⟨664709, by rfl⟩ : syracuseStep 886279 = 1329419) B1329419
theorem B886287 : Blo 884570 886287 := bstep (se 1 (by rfl) ⟨664715, by rfl⟩ : syracuseStep 886287 = 1329431) B1329431
theorem B886331 : Blo 884570 886331 := bstep (se 1 (by rfl) ⟨664748, by rfl⟩ : syracuseStep 886331 = 1329497) B1329497
theorem B2524733 : Blo 884570 2524733 := bstep (se 3 (by rfl) ⟨473387, by rfl⟩ : syracuseStep 2524733 = 946775) B946775
theorem B886407 : Blo 884570 886407 := bstep (se 1 (by rfl) ⟨664805, by rfl⟩ : syracuseStep 886407 = 1329611) B1329611
theorem B886415 : Blo 884570 886415 := bstep (se 1 (by rfl) ⟨664811, by rfl⟩ : syracuseStep 886415 = 1329623) B1329623
theorem B886459 : Blo 884570 886459 := bstep (se 1 (by rfl) ⟨664844, by rfl⟩ : syracuseStep 886459 = 1329689) B1329689
theorem B8652505 : Blo 884570 8652505 := bstep (se 2 (by rfl) ⟨3244689, by rfl⟩ : syracuseStep 8652505 = 6489379) B6489379
theorem B886535 : Blo 884570 886535 := bstep (se 1 (by rfl) ⟨664901, by rfl⟩ : syracuseStep 886535 = 1329803) B1329803
theorem B886543 : Blo 884570 886543 := bstep (se 1 (by rfl) ⟨664907, by rfl⟩ : syracuseStep 886543 = 1329815) B1329815
theorem B886587 : Blo 884570 886587 := bstep (se 1 (by rfl) ⟨664940, by rfl⟩ : syracuseStep 886587 = 1329881) B1329881
theorem B886663 : Blo 884570 886663 := bstep (se 1 (by rfl) ⟨664997, by rfl⟩ : syracuseStep 886663 = 1329995) B1329995
theorem B886671 : Blo 884570 886671 := bstep (se 1 (by rfl) ⟨665003, by rfl⟩ : syracuseStep 886671 = 1330007) B1330007
theorem B2131859 : Blo 884570 2131859 := bstep (se 1 (by rfl) ⟨1598894, by rfl⟩ : syracuseStep 2131859 = 3197789) B3197789
theorem B5670809 : Blo 884570 5670809 := bstep (se 2 (by rfl) ⟨2126553, by rfl⟩ : syracuseStep 5670809 = 4253107) B4253107
theorem B886715 : Blo 884570 886715 := bstep (se 1 (by rfl) ⟨665036, by rfl⟩ : syracuseStep 886715 = 1330073) B1330073
theorem B6719435 : Blo 884570 6719435 := bstep (se 1 (by rfl) ⟨5039576, by rfl⟩ : syracuseStep 6719435 = 10079153) B10079153
theorem B886791 : Blo 884570 886791 := bstep (se 1 (by rfl) ⟨665093, by rfl⟩ : syracuseStep 886791 = 1330187) B1330187
theorem B886799 : Blo 884570 886799 := bstep (se 1 (by rfl) ⟨665099, by rfl⟩ : syracuseStep 886799 = 1330199) B1330199
theorem B4491287 : Blo 884570 4491287 := bstep (se 1 (by rfl) ⟨3368465, by rfl⟩ : syracuseStep 4491287 = 6736931) B6736931
theorem B886843 : Blo 884570 886843 := bstep (se 1 (by rfl) ⟨665132, by rfl⟩ : syracuseStep 886843 = 1330265) B1330265
theorem B886919 : Blo 884570 886919 := bstep (se 1 (by rfl) ⟨665189, by rfl⟩ : syracuseStep 886919 = 1330379) B1330379
theorem B886927 : Blo 884570 886927 := bstep (se 1 (by rfl) ⟨665195, by rfl⟩ : syracuseStep 886927 = 1330391) B1330391
theorem B886971 : Blo 884570 886971 := bstep (se 1 (by rfl) ⟨665228, by rfl⟩ : syracuseStep 886971 = 1330457) B1330457
theorem B887047 : Blo 884570 887047 := bstep (se 1 (by rfl) ⟨665285, by rfl⟩ : syracuseStep 887047 = 1330571) B1330571
theorem B887055 : Blo 884570 887055 := bstep (se 1 (by rfl) ⟨665291, by rfl⟩ : syracuseStep 887055 = 1330583) B1330583
theorem B887099 : Blo 884570 887099 := bstep (se 1 (by rfl) ⟨665324, by rfl⟩ : syracuseStep 887099 = 1330649) B1330649
theorem B1280329 : Blo 884570 1280329 := bstep (se 2 (by rfl) ⟨480123, by rfl⟩ : syracuseStep 1280329 = 960247) B960247
theorem B2525575 : Blo 884570 2525575 := bstep (se 1 (by rfl) ⟨1894181, by rfl⟩ : syracuseStep 2525575 = 3788363) B3788363
theorem B887175 : Blo 884570 887175 := bstep (se 1 (by rfl) ⟨665381, by rfl⟩ : syracuseStep 887175 = 1330763) B1330763
theorem B887183 : Blo 884570 887183 := bstep (se 1 (by rfl) ⟨665387, by rfl⟩ : syracuseStep 887183 = 1330775) B1330775
theorem B887227 : Blo 884570 887227 := bstep (se 1 (by rfl) ⟨665420, by rfl⟩ : syracuseStep 887227 = 1330841) B1330841
theorem B887303 : Blo 884570 887303 := bstep (se 1 (by rfl) ⟨665477, by rfl⟩ : syracuseStep 887303 = 1330955) B1330955
theorem B887311 : Blo 884570 887311 := bstep (se 1 (by rfl) ⟨665483, by rfl⟩ : syracuseStep 887311 = 1330967) B1330967
theorem B887355 : Blo 884570 887355 := bstep (se 1 (by rfl) ⟨665516, by rfl⟩ : syracuseStep 887355 = 1331033) B1331033
theorem B887431 : Blo 884570 887431 := bstep (se 1 (by rfl) ⟨665573, by rfl⟩ : syracuseStep 887431 = 1331147) B1331147
theorem B887439 : Blo 884570 887439 := bstep (se 1 (by rfl) ⟨665579, by rfl⟩ : syracuseStep 887439 = 1331159) B1331159
theorem B2525849 : Blo 884570 2525849 := bstep (se 2 (by rfl) ⟨947193, by rfl⟩ : syracuseStep 2525849 = 1894387) B1894387
theorem B1346233 : Blo 884570 1346233 := bstep (se 2 (by rfl) ⟨504837, by rfl⟩ : syracuseStep 1346233 = 1009675) B1009675
theorem B887483 : Blo 884570 887483 := bstep (se 1 (by rfl) ⟨665612, by rfl⟩ : syracuseStep 887483 = 1331225) B1331225
theorem B887559 : Blo 884570 887559 := bstep (se 1 (by rfl) ⟨665669, by rfl⟩ : syracuseStep 887559 = 1331339) B1331339
theorem B887567 : Blo 884570 887567 := bstep (se 1 (by rfl) ⟨665675, by rfl⟩ : syracuseStep 887567 = 1331351) B1331351
theorem B887611 : Blo 884570 887611 := bstep (se 1 (by rfl) ⟨665708, by rfl⟩ : syracuseStep 887611 = 1331417) B1331417
theorem B887687 : Blo 884570 887687 := bstep (se 1 (by rfl) ⟨665765, by rfl⟩ : syracuseStep 887687 = 1331531) B1331531
theorem B887695 : Blo 884570 887695 := bstep (se 1 (by rfl) ⟨665771, by rfl⟩ : syracuseStep 887695 = 1331543) B1331543
theorem B3640249 : Blo 884570 3640249 := bstep (se 2 (by rfl) ⟨1365093, by rfl⟩ : syracuseStep 3640249 = 2730187) B2730187
theorem B887739 : Blo 884570 887739 := bstep (se 1 (by rfl) ⟨665804, by rfl⟩ : syracuseStep 887739 = 1331609) B1331609
theorem B5671883 : Blo 884570 5671883 := bstep (se 1 (by rfl) ⟨4253912, by rfl⟩ : syracuseStep 5671883 = 8507825) B8507825
theorem B887815 : Blo 884570 887815 := bstep (se 1 (by rfl) ⟨665861, by rfl⟩ : syracuseStep 887815 = 1331723) B1331723
theorem B887823 : Blo 884570 887823 := bstep (se 1 (by rfl) ⟨665867, by rfl⟩ : syracuseStep 887823 = 1331735) B1331735
theorem B887867 : Blo 884570 887867 := bstep (se 1 (by rfl) ⟨665900, by rfl⟩ : syracuseStep 887867 = 1331801) B1331801
theorem B887943 : Blo 884570 887943 := bstep (se 1 (by rfl) ⟨665957, by rfl⟩ : syracuseStep 887943 = 1331915) B1331915
theorem B887951 : Blo 884570 887951 := bstep (se 1 (by rfl) ⟨665963, by rfl⟩ : syracuseStep 887951 = 1331927) B1331927
theorem B887995 : Blo 884570 887995 := bstep (se 1 (by rfl) ⟨665996, by rfl⟩ : syracuseStep 887995 = 1331993) B1331993
theorem B888071 : Blo 884570 888071 := bstep (se 1 (by rfl) ⟨666053, by rfl⟩ : syracuseStep 888071 = 1332107) B1332107
theorem B888079 : Blo 884570 888079 := bstep (se 1 (by rfl) ⟨666059, by rfl⟩ : syracuseStep 888079 = 1332119) B1332119
theorem B11373857 : Blo 884570 11373857 := bstep (se 2 (by rfl) ⟨4265196, by rfl⟩ : syracuseStep 11373857 = 8530393) B8530393
theorem B888123 : Blo 884570 888123 := bstep (se 1 (by rfl) ⟨666092, by rfl⟩ : syracuseStep 888123 = 1332185) B1332185
theorem B888199 : Blo 884570 888199 := bstep (se 1 (by rfl) ⟨666149, by rfl⟩ : syracuseStep 888199 = 1332299) B1332299
theorem B888207 : Blo 884570 888207 := bstep (se 1 (by rfl) ⟨666155, by rfl⟩ : syracuseStep 888207 = 1332311) B1332311
theorem B4263353 : Blo 884570 4263353 := bstep (se 2 (by rfl) ⟨1598757, by rfl⟩ : syracuseStep 4263353 = 3197515) B3197515
theorem B888251 : Blo 884570 888251 := bstep (se 1 (by rfl) ⟨666188, by rfl⟩ : syracuseStep 888251 = 1332377) B1332377
theorem B888327 : Blo 884570 888327 := bstep (se 1 (by rfl) ⟨666245, by rfl⟩ : syracuseStep 888327 = 1332491) B1332491
theorem B888335 : Blo 884570 888335 := bstep (se 1 (by rfl) ⟨666251, by rfl⟩ : syracuseStep 888335 = 1332503) B1332503
theorem B888379 : Blo 884570 888379 := bstep (se 1 (by rfl) ⟨666284, by rfl⟩ : syracuseStep 888379 = 1332569) B1332569
theorem B888455 : Blo 884570 888455 := bstep (se 1 (by rfl) ⟨666341, by rfl⟩ : syracuseStep 888455 = 1332683) B1332683
theorem B888463 : Blo 884570 888463 := bstep (se 1 (by rfl) ⟨666347, by rfl⟩ : syracuseStep 888463 = 1332695) B1332695
theorem B888507 : Blo 884570 888507 := bstep (se 1 (by rfl) ⟨666380, by rfl⟩ : syracuseStep 888507 = 1332761) B1332761
theorem B16158437 : Blo 884570 16158437 := bstep (se 4 (by rfl) ⟨1514853, by rfl⟩ : syracuseStep 16158437 = 3029707) B3029707
theorem B14946049 : Blo 884570 14946049 := bstep (se 2 (by rfl) ⟨5604768, by rfl⟩ : syracuseStep 14946049 = 11209537) B11209537
theorem B2526977 : Blo 884570 2526977 := bstep (se 2 (by rfl) ⟨947616, by rfl⟩ : syracuseStep 2526977 = 1895233) B1895233
theorem B2395919 : Blo 884570 2395919 := bstep (se 1 (by rfl) ⟨1796939, by rfl⟩ : syracuseStep 2395919 = 3593879) B3593879
theorem B2985875 : Blo 884570 2985875 := bstep (se 1 (by rfl) ⟨2239406, by rfl⟩ : syracuseStep 2985875 = 4478813) B4478813
theorem B3837905 : Blo 884570 3837905 := bstep (se 2 (by rfl) ⟨1439214, by rfl⟩ : syracuseStep 3837905 = 2878429) B2878429
theorem B1216655 : Blo 884570 1216655 := bstep (se 1 (by rfl) ⟨912491, by rfl⟩ : syracuseStep 1216655 = 1824983) B1824983
theorem B2527433 : Blo 884570 2527433 := bstep (se 2 (by rfl) ⟨947787, by rfl⟩ : syracuseStep 2527433 = 1895575) B1895575
theorem B1217143 : Blo 884570 1217143 := bstep (se 1 (by rfl) ⟨912857, by rfl⟩ : syracuseStep 1217143 = 1825715) B1825715
theorem B4789007 : Blo 884570 4789007 := bstep (se 1 (by rfl) ⟨3591755, by rfl⟩ : syracuseStep 4789007 = 7183511) B7183511
theorem B4494365 : Blo 884570 4494365 := bstep (se 3 (by rfl) ⟨842693, by rfl⟩ : syracuseStep 4494365 = 1685387) B1685387
theorem B2397271 : Blo 884570 2397271 := bstep (se 1 (by rfl) ⟨1797953, by rfl⟩ : syracuseStep 2397271 = 3595907) B3595907
theorem B2987279 : Blo 884570 2987279 := bstep (se 1 (by rfl) ⟨2240459, by rfl⟩ : syracuseStep 2987279 = 4480919) B4480919
theorem B2692367 : Blo 884570 2692367 := bstep (se 1 (by rfl) ⟨2019275, by rfl⟩ : syracuseStep 2692367 = 4038551) B4038551
theorem B4265369 : Blo 884570 4265369 := bstep (se 2 (by rfl) ⟨1599513, by rfl⟩ : syracuseStep 4265369 = 3199027) B3199027
theorem B4855243 : Blo 884570 4855243 := bstep (se 1 (by rfl) ⟨3641432, by rfl⟩ : syracuseStep 4855243 = 7282865) B7282865
theorem B4789763 : Blo 884570 4789763 := bstep (se 1 (by rfl) ⟨3592322, by rfl⟩ : syracuseStep 4789763 = 7184645) B7184645
theorem B4494851 : Blo 884570 4494851 := bstep (se 1 (by rfl) ⟨3371138, by rfl⟩ : syracuseStep 4494851 = 6742277) B6742277
theorem B2987549 : Blo 884570 2987549 := bstep (se 3 (by rfl) ⟨560165, by rfl⟩ : syracuseStep 2987549 = 1120331) B1120331
theorem B1120007 : Blo 884570 1120007 := bstep (se 1 (by rfl) ⟨840005, by rfl⟩ : syracuseStep 1120007 = 1680011) B1680011
theorem B2397995 : Blo 884570 2397995 := bstep (se 1 (by rfl) ⟨1798496, by rfl⟩ : syracuseStep 2397995 = 3596993) B3596993
theorem B2529083 : Blo 884570 2529083 := bstep (se 1 (by rfl) ⟨1896812, by rfl⟩ : syracuseStep 2529083 = 3793625) B3793625
theorem B22714181 : Blo 884570 22714181 := bstep (se 4 (by rfl) ⟨2129454, by rfl⟩ : syracuseStep 22714181 = 4258909) B4258909
theorem B3840257 : Blo 884570 3840257 := bstep (se 2 (by rfl) ⟨1440096, by rfl⟩ : syracuseStep 3840257 = 2880193) B2880193
theorem B1120655 : Blo 884570 1120655 := bstep (se 1 (by rfl) ⟨840491, by rfl⟩ : syracuseStep 1120655 = 1680983) B1680983
theorem B2529721 : Blo 884570 2529721 := bstep (se 2 (by rfl) ⟨948645, by rfl⟩ : syracuseStep 2529721 = 1897291) B1897291
theorem B5052881 : Blo 884570 5052881 := bstep (se 2 (by rfl) ⟨1894830, by rfl⟩ : syracuseStep 5052881 = 3789661) B3789661
theorem B9214721 : Blo 884570 9214721 := bstep (se 2 (by rfl) ⟨3455520, by rfl⟩ : syracuseStep 9214721 = 6911041) B6911041
theorem B2530109 : Blo 884570 2530109 := bstep (se 3 (by rfl) ⟨474395, by rfl⟩ : syracuseStep 2530109 = 948791) B948791
theorem B2694023 : Blo 884570 2694023 := bstep (se 1 (by rfl) ⟨2020517, by rfl⟩ : syracuseStep 2694023 = 4041035) B4041035
theorem B2988953 : Blo 884570 2988953 := bstep (se 2 (by rfl) ⟨1120857, by rfl⟩ : syracuseStep 2988953 = 2241715) B2241715
theorem B5053337 : Blo 884570 5053337 := bstep (se 2 (by rfl) ⟨1895001, by rfl⟩ : syracuseStep 5053337 = 3790003) B3790003
theorem B3840953 : Blo 884570 3840953 := bstep (se 2 (by rfl) ⟨1440357, by rfl⟩ : syracuseStep 3840953 = 2880715) B2880715
theorem B10787863 : Blo 884570 10787863 := bstep (se 1 (by rfl) ⟨8090897, by rfl⟩ : syracuseStep 10787863 = 16181795) B16181795
theorem B4496471 : Blo 884570 4496471 := bstep (se 1 (by rfl) ⟨3372353, by rfl⟩ : syracuseStep 4496471 = 6744707) B6744707
theorem B6724781 : Blo 884570 6724781 := bstep (se 3 (by rfl) ⟨1260896, by rfl⟩ : syracuseStep 6724781 = 2521793) B2521793
theorem B4496957 : Blo 884570 4496957 := bstep (se 3 (by rfl) ⟨843179, by rfl⟩ : syracuseStep 4496957 = 1686359) B1686359
theorem B2989655 : Blo 884570 2989655 := bstep (se 1 (by rfl) ⟨2242241, by rfl⟩ : syracuseStep 2989655 = 4484483) B4484483
theorem B72720179 : Blo 884570 72720179 := bstep (se 1 (by rfl) ⟨54540134, by rfl⟩ : syracuseStep 72720179 = 109080269) B109080269
theorem B2301755 : Blo 884570 2301755 := bstep (se 1 (by rfl) ⟨1726316, by rfl⟩ : syracuseStep 2301755 = 3452633) B3452633
theorem B1679305 : Blo 884570 1679305 := bstep (se 2 (by rfl) ⟨629739, by rfl⟩ : syracuseStep 1679305 = 1259479) B1259479
theorem B2990141 : Blo 884570 2990141 := bstep (se 3 (by rfl) ⟨560651, by rfl⟩ : syracuseStep 2990141 = 1121303) B1121303
theorem B2270209 : Blo 884570 2270209 := bstep (se 2 (by rfl) ⟨851328, by rfl⟩ : syracuseStep 2270209 = 1702657) B1702657
theorem B1123627 : Blo 884570 1123627 := bstep (se 1 (by rfl) ⟨842720, by rfl⟩ : syracuseStep 1123627 = 1685441) B1685441
theorem B1418555 : Blo 884570 1418555 := bstep (se 1 (by rfl) ⟨1063916, by rfl⟩ : syracuseStep 1418555 = 2127833) B2127833
theorem B2991545 : Blo 884570 2991545 := bstep (se 2 (by rfl) ⟨1121829, by rfl⟩ : syracuseStep 2991545 = 2243659) B2243659
theorem B6727211 : Blo 884570 6727211 := bstep (se 1 (by rfl) ⟨5045408, by rfl⟩ : syracuseStep 6727211 = 10090817) B10090817
theorem B1681211 : Blo 884570 1681211 := bstep (se 1 (by rfl) ⟨1260908, by rfl⟩ : syracuseStep 1681211 = 2521817) B2521817
theorem B1419067 : Blo 884570 1419067 := bstep (se 1 (by rfl) ⟨1064300, by rfl⟩ : syracuseStep 1419067 = 2128601) B2128601
theorem B7579595 : Blo 884570 7579595 := bstep (se 1 (by rfl) ⟨5684696, by rfl⟩ : syracuseStep 7579595 = 11369393) B11369393
theorem B2992139 : Blo 884570 2992139 := bstep (se 1 (by rfl) ⟨2244104, by rfl⟩ : syracuseStep 2992139 = 4488209) B4488209
theorem B8103959 : Blo 884570 8103959 := bstep (se 1 (by rfl) ⟨6077969, by rfl⟩ : syracuseStep 8103959 = 12155939) B12155939
theorem B3778589 : Blo 884570 3778589 := bstep (se 3 (by rfl) ⟨708485, by rfl⟩ : syracuseStep 3778589 = 1416971) B1416971
theorem B2992247 : Blo 884570 2992247 := bstep (se 1 (by rfl) ⟨2244185, by rfl⟩ : syracuseStep 2992247 = 4488371) B4488371
theorem B1681697 : Blo 884570 1681697 := bstep (se 2 (by rfl) ⟨630636, by rfl⟩ : syracuseStep 1681697 = 1261273) B1261273
theorem B12954097 : Blo 884570 12954097 := bstep (se 2 (by rfl) ⟨4857786, by rfl⟩ : syracuseStep 12954097 = 9715573) B9715573
theorem B961031 : Blo 884570 961031 := bstep (se 1 (by rfl) ⟨720773, by rfl⟩ : syracuseStep 961031 = 1441547) B1441547
theorem B1518139 : Blo 884570 1518139 := bstep (se 1 (by rfl) ⟨1138604, by rfl⟩ : syracuseStep 1518139 = 2277209) B2277209
theorem B1682039 : Blo 884570 1682039 := bstep (se 1 (by rfl) ⟨1261529, by rfl⟩ : syracuseStep 1682039 = 2523059) B2523059
theorem B2239123 : Blo 884570 2239123 := bstep (se 1 (by rfl) ⟨1679342, by rfl⟩ : syracuseStep 2239123 = 3358685) B3358685
theorem B3779273 : Blo 884570 3779273 := bstep (se 2 (by rfl) ⟨1417227, by rfl⟩ : syracuseStep 3779273 = 2834455) B2834455
theorem B2992841 : Blo 884570 2992841 := bstep (se 2 (by rfl) ⟨1122315, by rfl⟩ : syracuseStep 2992841 = 2244631) B2244631
theorem B2239265 : Blo 884570 2239265 := bstep (se 2 (by rfl) ⟨839724, by rfl⟩ : syracuseStep 2239265 = 1679449) B1679449
theorem B66497381 : Blo 884570 66497381 := bstep (se 4 (by rfl) ⟨6234129, by rfl⟩ : syracuseStep 66497381 = 12468259) B12468259
theorem B1420303 : Blo 884570 1420303 := bstep (se 1 (by rfl) ⟨1065227, by rfl⟩ : syracuseStep 1420303 = 2130455) B2130455
theorem B3779855 : Blo 884570 3779855 := bstep (se 1 (by rfl) ⟨2834891, by rfl⟩ : syracuseStep 3779855 = 5669783) B5669783
theorem B2993543 : Blo 884570 2993543 := bstep (se 1 (by rfl) ⟨2245157, by rfl⟩ : syracuseStep 2993543 = 4490315) B4490315
theorem B3780215 : Blo 884570 3780215 := bstep (se 1 (by rfl) ⟨2835161, by rfl⟩ : syracuseStep 3780215 = 5670323) B5670323
theorem B2240257 : Blo 884570 2240257 := bstep (se 2 (by rfl) ⟨840096, by rfl⟩ : syracuseStep 2240257 = 1680193) B1680193
theorem B2993921 : Blo 884570 2993921 := bstep (se 2 (by rfl) ⟨1122720, by rfl⟩ : syracuseStep 2993921 = 2245441) B2245441
theorem B19181357 : Blo 884570 19181357 := bstep (se 3 (by rfl) ⟨3596504, by rfl⟩ : syracuseStep 19181357 = 7193009) B7193009
theorem B995215 : Blo 884570 995215 := bstep (se 1 (by rfl) ⟨746411, by rfl⟩ : syracuseStep 995215 = 1492823) B1492823
theorem B34090955 : Blo 884570 34090955 := bstep (se 1 (by rfl) ⟨25568216, by rfl⟩ : syracuseStep 34090955 = 51136433) B51136433
theorem B1683641 : Blo 884570 1683641 := bstep (se 2 (by rfl) ⟨631365, by rfl⟩ : syracuseStep 1683641 = 1262731) B1262731
theorem B2240855 : Blo 884570 2240855 := bstep (se 1 (by rfl) ⟨1680641, by rfl⟩ : syracuseStep 2240855 = 3361283) B3361283
theorem B995719 : Blo 884570 995719 := bstep (se 1 (by rfl) ⟨746789, by rfl⟩ : syracuseStep 995719 = 1493579) B1493579
theorem B1683983 : Blo 884570 1683983 := bstep (se 1 (by rfl) ⟨1262987, by rfl⟩ : syracuseStep 1683983 = 2525975) B2525975
theorem B2241067 : Blo 884570 2241067 := bstep (se 1 (by rfl) ⟨1680800, by rfl⟩ : syracuseStep 2241067 = 3361601) B3361601
theorem B2994731 : Blo 884570 2994731 := bstep (se 1 (by rfl) ⟨2246048, by rfl⟩ : syracuseStep 2994731 = 4492097) B4492097
theorem B1421867 : Blo 884570 1421867 := bstep (se 1 (by rfl) ⟨1066400, by rfl⟩ : syracuseStep 1421867 = 2132801) B2132801
theorem B995899 : Blo 884570 995899 := bstep (se 1 (by rfl) ⟨746924, by rfl⟩ : syracuseStep 995899 = 1493849) B1493849
theorem B3191357 : Blo 884570 3191357 := bstep (se 3 (by rfl) ⟨598379, by rfl⟩ : syracuseStep 3191357 = 1196759) B1196759
theorem B3781187 : Blo 884570 3781187 := bstep (se 1 (by rfl) ⟨2835890, by rfl⟩ : syracuseStep 3781187 = 5671781) B5671781
theorem B2241209 : Blo 884570 2241209 := bstep (se 2 (by rfl) ⟨840453, by rfl⟩ : syracuseStep 2241209 = 1680907) B1680907
theorem B7189337 : Blo 884570 7189337 := bstep (se 2 (by rfl) ⟨2696001, by rfl⟩ : syracuseStep 7189337 = 5392003) B5392003
theorem B3781529 : Blo 884570 3781529 := bstep (se 2 (by rfl) ⟨1418073, by rfl⟩ : syracuseStep 3781529 = 2836147) B2836147
theorem B996367 : Blo 884570 996367 := bstep (se 1 (by rfl) ⟨747275, by rfl⟩ : syracuseStep 996367 = 1494551) B1494551
theorem B1684795 : Blo 884570 1684795 := bstep (se 1 (by rfl) ⟨1263596, by rfl⟩ : syracuseStep 1684795 = 2527193) B2527193
theorem B1684871 : Blo 884570 1684871 := bstep (se 1 (by rfl) ⟨1263653, by rfl⟩ : syracuseStep 1684871 = 2527307) B2527307
theorem B6403475 : Blo 884570 6403475 := bstep (se 1 (by rfl) ⟨4802606, by rfl⟩ : syracuseStep 6403475 = 9605213) B9605213
theorem B5387705 : Blo 884570 5387705 := bstep (se 2 (by rfl) ⟨2020389, by rfl⟩ : syracuseStep 5387705 = 4040779) B4040779
theorem B996871 : Blo 884570 996871 := bstep (se 1 (by rfl) ⟨747653, by rfl⟩ : syracuseStep 996871 = 1495307) B1495307
theorem B2242201 : Blo 884570 2242201 := bstep (se 2 (by rfl) ⟨840825, by rfl⟩ : syracuseStep 2242201 = 1681651) B1681651
theorem B997051 : Blo 884570 997051 := bstep (se 1 (by rfl) ⟨747788, by rfl⟩ : syracuseStep 997051 = 1495577) B1495577
theorem B5060353 : Blo 884570 5060353 := bstep (se 2 (by rfl) ⟨1897632, by rfl⟩ : syracuseStep 5060353 = 3795265) B3795265
theorem B1685281 : Blo 884570 1685281 := bstep (se 2 (by rfl) ⟨631980, by rfl⟩ : syracuseStep 1685281 = 1263961) B1263961
theorem B8533811 : Blo 884570 8533811 := bstep (se 1 (by rfl) ⟨6400358, by rfl⟩ : syracuseStep 8533811 = 12800717) B12800717
theorem B2242363 : Blo 884570 2242363 := bstep (se 1 (by rfl) ⟨1681772, by rfl⟩ : syracuseStep 2242363 = 3363545) B3363545
theorem B2996027 : Blo 884570 2996027 := bstep (se 1 (by rfl) ⟨2247020, by rfl⟩ : syracuseStep 2996027 = 4494041) B4494041
theorem B1423289 : Blo 884570 1423289 := bstep (se 2 (by rfl) ⟨533733, by rfl⟩ : syracuseStep 1423289 = 1067467) B1067467
theorem B2242505 : Blo 884570 2242505 := bstep (se 2 (by rfl) ⟨840939, by rfl⟩ : syracuseStep 2242505 = 1681879) B1681879
theorem B1685623 : Blo 884570 1685623 := bstep (se 1 (by rfl) ⟨1264217, by rfl⟩ : syracuseStep 1685623 = 2528435) B2528435
theorem B2275463 : Blo 884570 2275463 := bstep (se 1 (by rfl) ⟨1706597, by rfl⟩ : syracuseStep 2275463 = 3413195) B3413195
theorem B997519 : Blo 884570 997519 := bstep (se 1 (by rfl) ⟨748139, by rfl⟩ : syracuseStep 997519 = 1496279) B1496279
theorem B1259707 : Blo 884570 1259707 := bstep (se 1 (by rfl) ⟨944780, by rfl⟩ : syracuseStep 1259707 = 1889561) B1889561
theorem B2242849 : Blo 884570 2242849 := bstep (se 2 (by rfl) ⟨841068, by rfl⟩ : syracuseStep 2242849 = 1682137) B1682137
theorem B2996513 : Blo 884570 2996513 := bstep (se 2 (by rfl) ⟨1123692, by rfl⟩ : syracuseStep 2996513 = 2247385) B2247385
theorem B4798757 : Blo 884570 4798757 := bstep (se 4 (by rfl) ⟨449883, by rfl⟩ : syracuseStep 4798757 = 899767) B899767
theorem B2275627 : Blo 884570 2275627 := bstep (se 1 (by rfl) ⟨1706720, by rfl⟩ : syracuseStep 2275627 = 3413441) B3413441
theorem B9583069 : Blo 884570 9583069 := bstep (se 3 (by rfl) ⟨1796825, by rfl⟩ : syracuseStep 9583069 = 3593651) B3593651
theorem B998023 : Blo 884570 998023 := bstep (se 1 (by rfl) ⟨748517, by rfl⟩ : syracuseStep 998023 = 1497035) B1497035
theorem B6830821 : Blo 884570 6830821 := bstep (se 4 (by rfl) ⟨640389, by rfl⟩ : syracuseStep 6830821 = 1280779) B1280779
theorem B1456955 : Blo 884570 1456955 := bstep (se 1 (by rfl) ⟨1092716, by rfl⟩ : syracuseStep 1456955 = 2185433) B2185433
theorem B998203 : Blo 884570 998203 := bstep (se 1 (by rfl) ⟨748652, by rfl⟩ : syracuseStep 998203 = 1497305) B1497305
theorem B2997107 : Blo 884570 2997107 := bstep (se 1 (by rfl) ⟨2247830, by rfl⟩ : syracuseStep 2997107 = 4495661) B4495661
theorem B1260407 : Blo 884570 1260407 := bstep (se 1 (by rfl) ⟨945305, by rfl⟩ : syracuseStep 1260407 = 1890611) B1890611
theorem B2243447 : Blo 884570 2243447 := bstep (se 1 (by rfl) ⟨1682585, by rfl⟩ : syracuseStep 2243447 = 3365171) B3365171
theorem B998671 : Blo 884570 998671 := bstep (se 1 (by rfl) ⟨749003, by rfl⟩ : syracuseStep 998671 = 1498007) B1498007
theorem B4603195 : Blo 884570 4603195 := bstep (se 1 (by rfl) ⟨3452396, by rfl⟩ : syracuseStep 4603195 = 6904793) B6904793
theorem B1064507 : Blo 884570 1064507 := bstep (se 1 (by rfl) ⟨798380, by rfl⟩ : syracuseStep 1064507 = 1596761) B1596761
theorem B999175 : Blo 884570 999175 := bstep (se 1 (by rfl) ⟨749381, by rfl⟩ : syracuseStep 999175 = 1498763) B1498763
theorem B1326863 : Blo 884570 1326863 := bstep (se 1 (by rfl) ⟨995147, by rfl⟩ : syracuseStep 1326863 = 1990295) B1990295
theorem B1326905 : Blo 884570 1326905 := bstep (se 2 (by rfl) ⟨497589, by rfl⟩ : syracuseStep 1326905 = 995179) B995179
theorem B1326983 : Blo 884570 1326983 := bstep (se 1 (by rfl) ⟨995237, by rfl⟩ : syracuseStep 1326983 = 1990475) B1990475
theorem B1064839 : Blo 884570 1064839 := bstep (se 1 (by rfl) ⟨798629, by rfl⟩ : syracuseStep 1064839 = 1597259) B1597259
theorem B3194759 : Blo 884570 3194759 := bstep (se 1 (by rfl) ⟨2396069, by rfl⟩ : syracuseStep 3194759 = 4792139) B4792139
theorem B4865939 : Blo 884570 4865939 := bstep (se 1 (by rfl) ⟨3649454, by rfl⟩ : syracuseStep 4865939 = 7298909) B7298909
theorem B1327019 : Blo 884570 1327019 := bstep (se 1 (by rfl) ⟨995264, by rfl⟩ : syracuseStep 1327019 = 1990529) B1990529
theorem B999355 : Blo 884570 999355 := bstep (se 1 (by rfl) ⟨749516, by rfl⟩ : syracuseStep 999355 = 1499033) B1499033
theorem B1327049 : Blo 884570 1327049 := bstep (se 2 (by rfl) ⟨497643, by rfl⟩ : syracuseStep 1327049 = 995287) B995287
theorem B1916873 : Blo 884570 1916873 := bstep (se 2 (by rfl) ⟨718827, by rfl⟩ : syracuseStep 1916873 = 1437655) B1437655
theorem B2834443 : Blo 884570 2834443 := bstep (se 1 (by rfl) ⟨2125832, by rfl⟩ : syracuseStep 2834443 = 4251665) B4251665
theorem B1327163 : Blo 884570 1327163 := bstep (se 1 (by rfl) ⟨995372, by rfl⟩ : syracuseStep 1327163 = 1990745) B1990745
theorem B1327223 : Blo 884570 1327223 := bstep (se 1 (by rfl) ⟨995417, by rfl⟩ : syracuseStep 1327223 = 1990835) B1990835
theorem B2244743 : Blo 884570 2244743 := bstep (se 1 (by rfl) ⟨1683557, by rfl⟩ : syracuseStep 2244743 = 3367115) B3367115
theorem B1327247 : Blo 884570 1327247 := bstep (se 1 (by rfl) ⟨995435, by rfl⟩ : syracuseStep 1327247 = 1990871) B1990871
theorem B1327289 : Blo 884570 1327289 := bstep (se 2 (by rfl) ⟨497733, by rfl⟩ : syracuseStep 1327289 = 995467) B995467
theorem B2244793 : Blo 884570 2244793 := bstep (se 2 (by rfl) ⟨841797, by rfl⟩ : syracuseStep 2244793 = 1683595) B1683595
theorem B12927221 : Blo 884570 12927221 := bstep (se 5 (by rfl) ⟨605963, by rfl⟩ : syracuseStep 12927221 = 1211927) B1211927
theorem B1327367 : Blo 884570 1327367 := bstep (se 1 (by rfl) ⟨995525, by rfl⟩ : syracuseStep 1327367 = 1991051) B1991051
theorem B1261831 : Blo 884570 1261831 := bstep (se 1 (by rfl) ⟨946373, by rfl⟩ : syracuseStep 1261831 = 1892747) B1892747
theorem B1327403 : Blo 884570 1327403 := bstep (se 1 (by rfl) ⟨995552, by rfl⟩ : syracuseStep 1327403 = 1991105) B1991105
theorem B1327433 : Blo 884570 1327433 := bstep (se 2 (by rfl) ⟨497787, by rfl⟩ : syracuseStep 1327433 = 995575) B995575
theorem B1327547 : Blo 884570 1327547 := bstep (se 1 (by rfl) ⟨995660, by rfl⟩ : syracuseStep 1327547 = 1991321) B1991321
theorem B1327607 : Blo 884570 1327607 := bstep (se 1 (by rfl) ⟨995705, by rfl⟩ : syracuseStep 1327607 = 1991411) B1991411
theorem B1327631 : Blo 884570 1327631 := bstep (se 1 (by rfl) ⟨995723, by rfl⟩ : syracuseStep 1327631 = 1991447) B1991447
theorem B1327673 : Blo 884570 1327673 := bstep (se 2 (by rfl) ⟨497877, by rfl⟩ : syracuseStep 1327673 = 995755) B995755
theorem B2310743 : Blo 884570 2310743 := bstep (se 1 (by rfl) ⟨1733057, by rfl⟩ : syracuseStep 2310743 = 3466115) B3466115
theorem B1327751 : Blo 884570 1327751 := bstep (se 1 (by rfl) ⟨995813, by rfl⟩ : syracuseStep 1327751 = 1991627) B1991627
theorem B1327787 : Blo 884570 1327787 := bstep (se 1 (by rfl) ⟨995840, by rfl⟩ : syracuseStep 1327787 = 1991681) B1991681
theorem B1327817 : Blo 884570 1327817 := bstep (se 2 (by rfl) ⟨497931, by rfl⟩ : syracuseStep 1327817 = 995863) B995863
theorem B2245391 : Blo 884570 2245391 := bstep (se 1 (by rfl) ⟨1684043, by rfl⟩ : syracuseStep 2245391 = 3368087) B3368087
theorem B5391137 : Blo 884570 5391137 := bstep (se 2 (by rfl) ⟨2021676, by rfl⟩ : syracuseStep 5391137 = 4043353) B4043353
theorem B1327931 : Blo 884570 1327931 := bstep (se 1 (by rfl) ⟨995948, by rfl⟩ : syracuseStep 1327931 = 1991897) B1991897
theorem B1262395 : Blo 884570 1262395 := bstep (se 1 (by rfl) ⟨946796, by rfl⟩ : syracuseStep 1262395 = 1893593) B1893593
theorem B10109771 : Blo 884570 10109771 := bstep (se 1 (by rfl) ⟨7582328, by rfl⟩ : syracuseStep 10109771 = 15164657) B15164657
theorem B1327991 : Blo 884570 1327991 := bstep (se 1 (by rfl) ⟨995993, by rfl⟩ : syracuseStep 1327991 = 1991987) B1991987
theorem B1328015 : Blo 884570 1328015 := bstep (se 1 (by rfl) ⟨996011, by rfl⟩ : syracuseStep 1328015 = 1992023) B1992023
theorem B1328057 : Blo 884570 1328057 := bstep (se 2 (by rfl) ⟨498021, by rfl⟩ : syracuseStep 1328057 = 996043) B996043
theorem B1328135 : Blo 884570 1328135 := bstep (se 1 (by rfl) ⟨996101, by rfl⟩ : syracuseStep 1328135 = 1992203) B1992203
theorem B1328171 : Blo 884570 1328171 := bstep (se 1 (by rfl) ⟨996128, by rfl⟩ : syracuseStep 1328171 = 1992257) B1992257
theorem B1328201 : Blo 884570 1328201 := bstep (se 2 (by rfl) ⟨498075, by rfl⟩ : syracuseStep 1328201 = 996151) B996151
theorem B1328315 : Blo 884570 1328315 := bstep (se 1 (by rfl) ⟨996236, by rfl⟩ : syracuseStep 1328315 = 1992473) B1992473
theorem B1328375 : Blo 884570 1328375 := bstep (se 1 (by rfl) ⟨996281, by rfl⟩ : syracuseStep 1328375 = 1992563) B1992563
theorem B1328399 : Blo 884570 1328399 := bstep (se 1 (by rfl) ⟨996299, by rfl⟩ : syracuseStep 1328399 = 1992599) B1992599
theorem B1328441 : Blo 884570 1328441 := bstep (se 2 (by rfl) ⟨498165, by rfl⟩ : syracuseStep 1328441 = 996331) B996331
theorem B1328519 : Blo 884570 1328519 := bstep (se 1 (by rfl) ⟨996389, by rfl⟩ : syracuseStep 1328519 = 1992779) B1992779
theorem B1328555 : Blo 884570 1328555 := bstep (se 1 (by rfl) ⟨996416, by rfl⟩ : syracuseStep 1328555 = 1992833) B1992833
theorem B1328585 : Blo 884570 1328585 := bstep (se 2 (by rfl) ⟨498219, by rfl⟩ : syracuseStep 1328585 = 996439) B996439
theorem B2246089 : Blo 884570 2246089 := bstep (se 2 (by rfl) ⟨842283, by rfl⟩ : syracuseStep 2246089 = 1684567) B1684567
theorem B1328699 : Blo 884570 1328699 := bstep (se 1 (by rfl) ⟨996524, by rfl⟩ : syracuseStep 1328699 = 1993049) B1993049
theorem B2246231 : Blo 884570 2246231 := bstep (se 1 (by rfl) ⟨1684673, by rfl⟩ : syracuseStep 2246231 = 3369347) B3369347
theorem B1328759 : Blo 884570 1328759 := bstep (se 1 (by rfl) ⟨996569, by rfl⟩ : syracuseStep 1328759 = 1993139) B1993139
theorem B1328783 : Blo 884570 1328783 := bstep (se 1 (by rfl) ⟨996587, by rfl⟩ : syracuseStep 1328783 = 1993175) B1993175
theorem B1328825 : Blo 884570 1328825 := bstep (se 2 (by rfl) ⟨498309, by rfl⟩ : syracuseStep 1328825 = 996619) B996619
theorem B1263289 : Blo 884570 1263289 := bstep (se 2 (by rfl) ⟨473733, by rfl⟩ : syracuseStep 1263289 = 947467) B947467
theorem B1328903 : Blo 884570 1328903 := bstep (se 1 (by rfl) ⟨996677, by rfl⟩ : syracuseStep 1328903 = 1993355) B1993355
theorem B6145807 : Blo 884570 6145807 := bstep (se 1 (by rfl) ⟨4609355, by rfl⟩ : syracuseStep 6145807 = 9218711) B9218711
theorem B1328939 : Blo 884570 1328939 := bstep (se 1 (by rfl) ⟨996704, by rfl⟩ : syracuseStep 1328939 = 1993409) B1993409
theorem B2737979 : Blo 884570 2737979 := bstep (se 1 (by rfl) ⟨2053484, by rfl⟩ : syracuseStep 2737979 = 4106969) B4106969
theorem B1328969 : Blo 884570 1328969 := bstep (se 2 (by rfl) ⟨498363, by rfl⟩ : syracuseStep 1328969 = 996727) B996727
theorem B1329083 : Blo 884570 1329083 := bstep (se 1 (by rfl) ⟨996812, by rfl⟩ : syracuseStep 1329083 = 1993625) B1993625
theorem B1329143 : Blo 884570 1329143 := bstep (se 1 (by rfl) ⟨996857, by rfl⟩ : syracuseStep 1329143 = 1993715) B1993715
theorem B1329167 : Blo 884570 1329167 := bstep (se 1 (by rfl) ⟨996875, by rfl⟩ : syracuseStep 1329167 = 1993751) B1993751
theorem B3360797 : Blo 884570 3360797 := bstep (se 3 (by rfl) ⟨630149, by rfl⟩ : syracuseStep 3360797 = 1260299) B1260299
theorem B3360811 : Blo 884570 3360811 := bstep (se 1 (by rfl) ⟨2520608, by rfl⟩ : syracuseStep 3360811 = 5041217) B5041217
theorem B1329209 : Blo 884570 1329209 := bstep (se 2 (by rfl) ⟨498453, by rfl⟩ : syracuseStep 1329209 = 996907) B996907
theorem B6735959 : Blo 884570 6735959 := bstep (se 1 (by rfl) ⟨5051969, by rfl⟩ : syracuseStep 6735959 = 10103939) B10103939
theorem B6473861 : Blo 884570 6473861 := bstep (se 4 (by rfl) ⟨606924, by rfl⟩ : syracuseStep 6473861 = 1213849) B1213849
theorem B1329287 : Blo 884570 1329287 := bstep (se 1 (by rfl) ⟨996965, by rfl⟩ : syracuseStep 1329287 = 1993931) B1993931
theorem B1329323 : Blo 884570 1329323 := bstep (se 1 (by rfl) ⟨996992, by rfl⟩ : syracuseStep 1329323 = 1993985) B1993985
theorem B1329353 : Blo 884570 1329353 := bstep (se 2 (by rfl) ⟨498507, by rfl⟩ : syracuseStep 1329353 = 997015) B997015
theorem B1329467 : Blo 884570 1329467 := bstep (se 1 (by rfl) ⟨997100, by rfl⟩ : syracuseStep 1329467 = 1994201) B1994201
theorem B1067323 : Blo 884570 1067323 := bstep (se 1 (by rfl) ⟨800492, by rfl⟩ : syracuseStep 1067323 = 1600985) B1600985
theorem B1329527 : Blo 884570 1329527 := bstep (se 1 (by rfl) ⟨997145, by rfl⟩ : syracuseStep 1329527 = 1994291) B1994291
theorem B1493383 : Blo 884570 1493383 := bstep (se 1 (by rfl) ⟨1120037, by rfl⟩ : syracuseStep 1493383 = 2240075) B2240075
theorem B1329551 : Blo 884570 1329551 := bstep (se 1 (by rfl) ⟨997163, by rfl⟩ : syracuseStep 1329551 = 1994327) B1994327
theorem B6834577 : Blo 884570 6834577 := bstep (se 2 (by rfl) ⟨2562966, by rfl⟩ : syracuseStep 6834577 = 5125933) B5125933
theorem B1329593 : Blo 884570 1329593 := bstep (se 2 (by rfl) ⟨498597, by rfl⟩ : syracuseStep 1329593 = 997195) B997195
theorem B1329671 : Blo 884570 1329671 := bstep (se 1 (by rfl) ⟨997253, by rfl⟩ : syracuseStep 1329671 = 1994507) B1994507
theorem B1329707 : Blo 884570 1329707 := bstep (se 1 (by rfl) ⟨997280, by rfl⟩ : syracuseStep 1329707 = 1994561) B1994561
theorem B1329737 : Blo 884570 1329737 := bstep (se 2 (by rfl) ⟨498651, by rfl⟩ : syracuseStep 1329737 = 997303) B997303
theorem B7195213 : Blo 884570 7195213 := bstep (se 3 (by rfl) ⟨1349102, by rfl⟩ : syracuseStep 7195213 = 2698205) B2698205
theorem B1329851 : Blo 884570 1329851 := bstep (se 1 (by rfl) ⟨997388, by rfl⟩ : syracuseStep 1329851 = 1994777) B1994777
theorem B1329911 : Blo 884570 1329911 := bstep (se 1 (by rfl) ⟨997433, by rfl⟩ : syracuseStep 1329911 = 1994867) B1994867
theorem B1329935 : Blo 884570 1329935 := bstep (se 1 (by rfl) ⟨997451, by rfl⟩ : syracuseStep 1329935 = 1994903) B1994903
theorem B1329977 : Blo 884570 1329977 := bstep (se 2 (by rfl) ⟨498741, by rfl⟩ : syracuseStep 1329977 = 997483) B997483
theorem B1330055 : Blo 884570 1330055 := bstep (se 1 (by rfl) ⟨997541, by rfl⟩ : syracuseStep 1330055 = 1995083) B1995083
theorem B1264519 : Blo 884570 1264519 := bstep (se 1 (by rfl) ⟨948389, by rfl⟩ : syracuseStep 1264519 = 1896779) B1896779
theorem B1330091 : Blo 884570 1330091 := bstep (se 1 (by rfl) ⟨997568, by rfl⟩ : syracuseStep 1330091 = 1995137) B1995137
theorem B1330121 : Blo 884570 1330121 := bstep (se 2 (by rfl) ⟨498795, by rfl⟩ : syracuseStep 1330121 = 997591) B997591
theorem B24562693 : Blo 884570 24562693 := bstep (se 4 (by rfl) ⟨2302752, by rfl⟩ : syracuseStep 24562693 = 4605505) B4605505
theorem B14797835 : Blo 884570 14797835 := bstep (se 1 (by rfl) ⟨11098376, by rfl⟩ : syracuseStep 14797835 = 22196753) B22196753
theorem B1494031 : Blo 884570 1494031 := bstep (se 1 (by rfl) ⟨1120523, by rfl⟩ : syracuseStep 1494031 = 2241047) B2241047
theorem B1330235 : Blo 884570 1330235 := bstep (se 1 (by rfl) ⟨997676, by rfl⟩ : syracuseStep 1330235 = 1995353) B1995353
theorem B1330295 : Blo 884570 1330295 := bstep (se 1 (by rfl) ⟨997721, by rfl⟩ : syracuseStep 1330295 = 1995443) B1995443
theorem B1330319 : Blo 884570 1330319 := bstep (se 1 (by rfl) ⟨997739, by rfl⟩ : syracuseStep 1330319 = 1995479) B1995479
theorem B1330361 : Blo 884570 1330361 := bstep (se 2 (by rfl) ⟨498885, by rfl⟩ : syracuseStep 1330361 = 997771) B997771
theorem B4050157 : Blo 884570 4050157 := bstep (se 3 (by rfl) ⟨759404, by rfl⟩ : syracuseStep 4050157 = 1518809) B1518809
theorem B1330439 : Blo 884570 1330439 := bstep (se 1 (by rfl) ⟨997829, by rfl⟩ : syracuseStep 1330439 = 1995659) B1995659
theorem B1330475 : Blo 884570 1330475 := bstep (se 1 (by rfl) ⟨997856, by rfl⟩ : syracuseStep 1330475 = 1995713) B1995713
theorem B1330505 : Blo 884570 1330505 := bstep (se 2 (by rfl) ⟨498939, by rfl⟩ : syracuseStep 1330505 = 997879) B997879
theorem B1330619 : Blo 884570 1330619 := bstep (se 1 (by rfl) ⟨997964, by rfl⟩ : syracuseStep 1330619 = 1995929) B1995929
theorem B1330679 : Blo 884570 1330679 := bstep (se 1 (by rfl) ⟨998009, by rfl⟩ : syracuseStep 1330679 = 1996019) B1996019
theorem B1330703 : Blo 884570 1330703 := bstep (se 1 (by rfl) ⟨998027, by rfl⟩ : syracuseStep 1330703 = 1996055) B1996055
theorem B1494571 : Blo 884570 1494571 := bstep (se 1 (by rfl) ⟨1120928, by rfl⟩ : syracuseStep 1494571 = 2241857) B2241857
theorem B1330745 : Blo 884570 1330745 := bstep (se 2 (by rfl) ⟨499029, by rfl⟩ : syracuseStep 1330745 = 998059) B998059
theorem B2248307 : Blo 884570 2248307 := bstep (se 1 (by rfl) ⟨1686230, by rfl⟩ : syracuseStep 2248307 = 3372461) B3372461
theorem B1330823 : Blo 884570 1330823 := bstep (se 1 (by rfl) ⟨998117, by rfl⟩ : syracuseStep 1330823 = 1996235) B1996235
theorem B1330859 : Blo 884570 1330859 := bstep (se 1 (by rfl) ⟨998144, by rfl⟩ : syracuseStep 1330859 = 1996289) B1996289
theorem B1494713 : Blo 884570 1494713 := bstep (se 2 (by rfl) ⟨560517, by rfl⟩ : syracuseStep 1494713 = 1121035) B1121035
theorem B1330889 : Blo 884570 1330889 := bstep (se 2 (by rfl) ⟨499083, by rfl⟩ : syracuseStep 1330889 = 998167) B998167
theorem B3788603 : Blo 884570 3788603 := bstep (se 1 (by rfl) ⟨2841452, by rfl⟩ : syracuseStep 3788603 = 5682905) B5682905
theorem B1331003 : Blo 884570 1331003 := bstep (se 1 (by rfl) ⟨998252, by rfl⟩ : syracuseStep 1331003 = 1996505) B1996505
theorem B1331063 : Blo 884570 1331063 := bstep (se 1 (by rfl) ⟨998297, by rfl⟩ : syracuseStep 1331063 = 1996595) B1996595
theorem B1331087 : Blo 884570 1331087 := bstep (se 1 (by rfl) ⟨998315, by rfl⟩ : syracuseStep 1331087 = 1996631) B1996631
theorem B1331129 : Blo 884570 1331129 := bstep (se 2 (by rfl) ⟨499173, by rfl⟩ : syracuseStep 1331129 = 998347) B998347
theorem B1331207 : Blo 884570 1331207 := bstep (se 1 (by rfl) ⟨998405, by rfl⟩ : syracuseStep 1331207 = 1996811) B1996811
theorem B1331243 : Blo 884570 1331243 := bstep (se 1 (by rfl) ⟨998432, by rfl⟩ : syracuseStep 1331243 = 1996865) B1996865
theorem B1331273 : Blo 884570 1331273 := bstep (se 2 (by rfl) ⟨499227, by rfl⟩ : syracuseStep 1331273 = 998455) B998455
theorem B2248823 : Blo 884570 2248823 := bstep (se 1 (by rfl) ⟨1686617, by rfl⟩ : syracuseStep 2248823 = 3373235) B3373235
theorem B1331387 : Blo 884570 1331387 := bstep (se 1 (by rfl) ⟨998540, by rfl⟩ : syracuseStep 1331387 = 1997081) B1997081
theorem B1331447 : Blo 884570 1331447 := bstep (se 1 (by rfl) ⟨998585, by rfl⟩ : syracuseStep 1331447 = 1997171) B1997171
theorem B1331471 : Blo 884570 1331471 := bstep (se 1 (by rfl) ⟨998603, by rfl⟩ : syracuseStep 1331471 = 1997207) B1997207
theorem B1331513 : Blo 884570 1331513 := bstep (se 2 (by rfl) ⟨499317, by rfl⟩ : syracuseStep 1331513 = 998635) B998635
theorem B1200457 : Blo 884570 1200457 := bstep (se 2 (by rfl) ⟨450171, by rfl⟩ : syracuseStep 1200457 = 900343) B900343
theorem B1495415 : Blo 884570 1495415 := bstep (se 1 (by rfl) ⟨1121561, by rfl⟩ : syracuseStep 1495415 = 2243123) B2243123
theorem B1331591 : Blo 884570 1331591 := bstep (se 1 (by rfl) ⟨998693, by rfl⟩ : syracuseStep 1331591 = 1997387) B1997387
theorem B1331627 : Blo 884570 1331627 := bstep (se 1 (by rfl) ⟨998720, by rfl⟩ : syracuseStep 1331627 = 1997441) B1997441
theorem B1331657 : Blo 884570 1331657 := bstep (se 2 (by rfl) ⟨499371, by rfl⟩ : syracuseStep 1331657 = 998743) B998743
theorem B1331771 : Blo 884570 1331771 := bstep (se 1 (by rfl) ⟨998828, by rfl⟩ : syracuseStep 1331771 = 1997657) B1997657
theorem B1331831 : Blo 884570 1331831 := bstep (se 1 (by rfl) ⟨998873, by rfl⟩ : syracuseStep 1331831 = 1997747) B1997747
theorem B1331855 : Blo 884570 1331855 := bstep (se 1 (by rfl) ⟨998891, by rfl⟩ : syracuseStep 1331855 = 1997783) B1997783
theorem B1331897 : Blo 884570 1331897 := bstep (se 2 (by rfl) ⟨499461, by rfl⟩ : syracuseStep 1331897 = 998923) B998923
theorem B1331975 : Blo 884570 1331975 := bstep (se 1 (by rfl) ⟨998981, by rfl⟩ : syracuseStep 1331975 = 1997963) B1997963
theorem B1200911 : Blo 884570 1200911 := bstep (se 1 (by rfl) ⟨900683, by rfl⟩ : syracuseStep 1200911 = 1801367) B1801367
theorem B1332011 : Blo 884570 1332011 := bstep (se 1 (by rfl) ⟨999008, by rfl⟩ : syracuseStep 1332011 = 1998017) B1998017
theorem B1495867 : Blo 884570 1495867 := bstep (se 1 (by rfl) ⟨1121900, by rfl⟩ : syracuseStep 1495867 = 2243801) B2243801
theorem B1332041 : Blo 884570 1332041 := bstep (se 2 (by rfl) ⟨499515, by rfl⟩ : syracuseStep 1332041 = 999031) B999031
theorem B1332155 : Blo 884570 1332155 := bstep (se 1 (by rfl) ⟨999116, by rfl⟩ : syracuseStep 1332155 = 1998233) B1998233
theorem B1496009 : Blo 884570 1496009 := bstep (se 2 (by rfl) ⟨561003, by rfl⟩ : syracuseStep 1496009 = 1122007) B1122007
theorem B1332215 : Blo 884570 1332215 := bstep (se 1 (by rfl) ⟨999161, by rfl⟩ : syracuseStep 1332215 = 1998323) B1998323
theorem B1332239 : Blo 884570 1332239 := bstep (se 1 (by rfl) ⟨999179, by rfl⟩ : syracuseStep 1332239 = 1998359) B1998359
theorem B1332281 : Blo 884570 1332281 := bstep (se 2 (by rfl) ⟨499605, by rfl⟩ : syracuseStep 1332281 = 999211) B999211
theorem B1332359 : Blo 884570 1332359 := bstep (se 1 (by rfl) ⟨999269, by rfl⟩ : syracuseStep 1332359 = 1998539) B1998539
theorem B1332395 : Blo 884570 1332395 := bstep (se 1 (by rfl) ⟨999296, by rfl⟩ : syracuseStep 1332395 = 1998593) B1998593
theorem B1332425 : Blo 884570 1332425 := bstep (se 2 (by rfl) ⟨499659, by rfl⟩ : syracuseStep 1332425 = 999319) B999319
theorem B1332539 : Blo 884570 1332539 := bstep (se 1 (by rfl) ⟨999404, by rfl⟩ : syracuseStep 1332539 = 1998809) B1998809
theorem B1332599 : Blo 884570 1332599 := bstep (se 1 (by rfl) ⟨999449, by rfl⟩ : syracuseStep 1332599 = 1998899) B1998899
theorem B1889671 : Blo 884570 1889671 := bstep (se 1 (by rfl) ⟨1417253, by rfl⟩ : syracuseStep 1889671 = 2834507) B2834507
theorem B1332623 : Blo 884570 1332623 := bstep (se 1 (by rfl) ⟨999467, by rfl⟩ : syracuseStep 1332623 = 1998935) B1998935
theorem B1332665 : Blo 884570 1332665 := bstep (se 2 (by rfl) ⟨499749, by rfl⟩ : syracuseStep 1332665 = 999499) B999499
theorem B1332743 : Blo 884570 1332743 := bstep (se 1 (by rfl) ⟨999557, by rfl⟩ : syracuseStep 1332743 = 1999115) B1999115
theorem B1332779 : Blo 884570 1332779 := bstep (se 1 (by rfl) ⟨999584, by rfl⟩ : syracuseStep 1332779 = 1999169) B1999169
theorem B1332809 : Blo 884570 1332809 := bstep (se 2 (by rfl) ⟨499803, by rfl⟩ : syracuseStep 1332809 = 999607) B999607
theorem B1496711 : Blo 884570 1496711 := bstep (se 1 (by rfl) ⟨1122533, by rfl⟩ : syracuseStep 1496711 = 2245067) B2245067
theorem B3200903 : Blo 884570 3200903 := bstep (se 1 (by rfl) ⟨2400677, by rfl⟩ : syracuseStep 3200903 = 4801355) B4801355
theorem B2021267 : Blo 884570 2021267 := bstep (se 1 (by rfl) ⟨1515950, by rfl⟩ : syracuseStep 2021267 = 3031901) B3031901
theorem B3790739 : Blo 884570 3790739 := bstep (se 1 (by rfl) ⟨2843054, by rfl⟩ : syracuseStep 3790739 = 5686109) B5686109
theorem B3790891 : Blo 884570 3790891 := bstep (se 1 (by rfl) ⟨2843168, by rfl⟩ : syracuseStep 3790891 = 5686337) B5686337
theorem B19159213 : Blo 884570 19159213 := bstep (se 3 (by rfl) ⟨3592352, by rfl⟩ : syracuseStep 19159213 = 7184705) B7184705
theorem B1497359 : Blo 884570 1497359 := bstep (se 1 (by rfl) ⟨1123019, by rfl⟩ : syracuseStep 1497359 = 2246039) B2246039
theorem B1595707 : Blo 884570 1595707 := bstep (se 1 (by rfl) ⟨1196780, by rfl⟩ : syracuseStep 1595707 = 2393561) B2393561
theorem B7297465 : Blo 884570 7297465 := bstep (se 2 (by rfl) ⟨2736549, by rfl⟩ : syracuseStep 7297465 = 5473099) B5473099
theorem B12769757 : Blo 884570 12769757 := bstep (se 3 (by rfl) ⟨2394329, by rfl⟩ : syracuseStep 12769757 = 4788659) B4788659
theorem B2021903 : Blo 884570 2021903 := bstep (se 1 (by rfl) ⟨1516427, by rfl⟩ : syracuseStep 2021903 = 3032855) B3032855
theorem B1890859 : Blo 884570 1890859 := bstep (se 1 (by rfl) ⟨1418144, by rfl⟩ : syracuseStep 1890859 = 2836289) B2836289
theorem B1497899 : Blo 884570 1497899 := bstep (se 1 (by rfl) ⟨1123424, by rfl⟩ : syracuseStep 1497899 = 2246849) B2246849
theorem B4479947 : Blo 884570 4479947 := bstep (se 1 (by rfl) ⟨3359960, by rfl⟩ : syracuseStep 4479947 = 6719921) B6719921
theorem B3365975 : Blo 884570 3365975 := bstep (se 1 (by rfl) ⟨2524481, by rfl⟩ : syracuseStep 3365975 = 5048963) B5048963
theorem B1498297 : Blo 884570 1498297 := bstep (se 2 (by rfl) ⟨561861, by rfl⟩ : syracuseStep 1498297 = 1123723) B1123723
theorem B4480271 : Blo 884570 4480271 := bstep (se 1 (by rfl) ⟨3360203, by rfl⟩ : syracuseStep 4480271 = 6720407) B6720407
theorem B3792395 : Blo 884570 3792395 := bstep (se 1 (by rfl) ⟨2844296, by rfl⟩ : syracuseStep 3792395 = 5688593) B5688593
theorem B3366461 : Blo 884570 3366461 := bstep (se 3 (by rfl) ⟨631211, by rfl⟩ : syracuseStep 3366461 = 1262423) B1262423
theorem B1597063 : Blo 884570 1597063 := bstep (se 1 (by rfl) ⟨1197797, by rfl⟩ : syracuseStep 1597063 = 2395595) B2395595
theorem B1498999 : Blo 884570 1498999 := bstep (se 1 (by rfl) ⟨1124249, by rfl⟩ : syracuseStep 1498999 = 2248499) B2248499
theorem B1990547 : Blo 884570 1990547 := bstep (se 1 (by rfl) ⟨1492910, by rfl⟩ : syracuseStep 1990547 = 2985821) B2985821
theorem B1990601 : Blo 884570 1990601 := bstep (se 2 (by rfl) ⟨746475, by rfl⟩ : syracuseStep 1990601 = 1492951) B1492951
theorem B3498013 : Blo 884570 3498013 := bstep (se 3 (by rfl) ⟨655877, by rfl⟩ : syracuseStep 3498013 = 1311755) B1311755
theorem B1499195 : Blo 884570 1499195 := bstep (se 1 (by rfl) ⟨1124396, by rfl⟩ : syracuseStep 1499195 = 2248793) B2248793
theorem B7561349 : Blo 884570 7561349 := bstep (se 4 (by rfl) ⟨708876, by rfl⟩ : syracuseStep 7561349 = 1417753) B1417753
theorem B2842913 : Blo 884570 2842913 := bstep (se 2 (by rfl) ⟨1066092, by rfl⟩ : syracuseStep 2842913 = 2132185) B2132185
theorem B5038483 : Blo 884570 5038483 := bstep (se 1 (by rfl) ⟨3778862, by rfl⟩ : syracuseStep 5038483 = 7557725) B7557725
theorem B3793337 : Blo 884570 3793337 := bstep (se 2 (by rfl) ⟨1422501, by rfl⟩ : syracuseStep 3793337 = 2845003) B2845003
theorem B1368695 : Blo 884570 1368695 := bstep (se 1 (by rfl) ⟨1026521, by rfl⟩ : syracuseStep 1368695 = 2053043) B2053043
theorem B1991303 : Blo 884570 1991303 := bstep (se 1 (by rfl) ⟨1493477, by rfl⟩ : syracuseStep 1991303 = 2986955) B2986955
theorem B4481729 : Blo 884570 4481729 := bstep (se 2 (by rfl) ⟨1680648, by rfl⟩ : syracuseStep 4481729 = 3361297) B3361297
theorem B1991483 : Blo 884570 1991483 := bstep (se 1 (by rfl) ⟨1493612, by rfl⟩ : syracuseStep 1991483 = 2987225) B2987225
theorem B7562099 : Blo 884570 7562099 := bstep (se 1 (by rfl) ⟨5671574, by rfl⟩ : syracuseStep 7562099 = 11343149) B11343149
theorem B1991609 : Blo 884570 1991609 := bstep (se 2 (by rfl) ⟨746853, by rfl⟩ : syracuseStep 1991609 = 1493707) B1493707
theorem B3367889 : Blo 884570 3367889 := bstep (se 2 (by rfl) ⟨1262958, by rfl⟩ : syracuseStep 3367889 = 2525917) B2525917
theorem B105014341 : Blo 884570 105014341 := bstep (se 4 (by rfl) ⟨9845094, by rfl⟩ : syracuseStep 105014341 = 19690189) B19690189
theorem B1991951 : Blo 884570 1991951 := bstep (se 1 (by rfl) ⟨1493963, by rfl⟩ : syracuseStep 1991951 = 2987927) B2987927
theorem B1991969 : Blo 884570 1991969 := bstep (se 2 (by rfl) ⟨746988, by rfl⟩ : syracuseStep 1991969 = 1493977) B1493977
theorem B6383033 : Blo 884570 6383033 := bstep (se 2 (by rfl) ⟨2393637, by rfl⟩ : syracuseStep 6383033 = 4787275) B4787275
theorem B1992311 : Blo 884570 1992311 := bstep (se 1 (by rfl) ⟨1494233, by rfl⟩ : syracuseStep 1992311 = 2988467) B2988467
theorem B910991 : Blo 884570 910991 := bstep (se 1 (by rfl) ⟨683243, by rfl⟩ : syracuseStep 910991 = 1366487) B1366487
theorem B1992491 : Blo 884570 1992491 := bstep (se 1 (by rfl) ⟨1494368, by rfl⟩ : syracuseStep 1992491 = 2988737) B2988737
theorem B4483025 : Blo 884570 4483025 := bstep (se 2 (by rfl) ⟨1681134, by rfl⟩ : syracuseStep 4483025 = 3362269) B3362269
theorem B2844733 : Blo 884570 2844733 := bstep (se 3 (by rfl) ⟨533387, by rfl⟩ : syracuseStep 2844733 = 1066775) B1066775
theorem B5040215 : Blo 884570 5040215 := bstep (se 1 (by rfl) ⟨3780161, by rfl⟩ : syracuseStep 5040215 = 7560323) B7560323
theorem B5400695 : Blo 884570 5400695 := bstep (se 1 (by rfl) ⟨4050521, by rfl⟩ : syracuseStep 5400695 = 8101043) B8101043
theorem B1992851 : Blo 884570 1992851 := bstep (se 1 (by rfl) ⟨1494638, by rfl⟩ : syracuseStep 1992851 = 2989277) B2989277
theorem B1992905 : Blo 884570 1992905 := bstep (se 2 (by rfl) ⟨747339, by rfl⟩ : syracuseStep 1992905 = 1494679) B1494679
theorem B3795335 : Blo 884570 3795335 := bstep (se 1 (by rfl) ⟨2846501, by rfl⟩ : syracuseStep 3795335 = 5693003) B5693003
theorem B5400985 : Blo 884570 5400985 := bstep (se 2 (by rfl) ⟨2025369, by rfl⟩ : syracuseStep 5400985 = 4050739) B4050739
theorem B3369559 : Blo 884570 3369559 := bstep (se 1 (by rfl) ⟨2527169, by rfl⟩ : syracuseStep 3369559 = 5054339) B5054339
theorem B1993607 : Blo 884570 1993607 := bstep (se 1 (by rfl) ⟨1495205, by rfl⟩ : syracuseStep 1993607 = 2990411) B2990411
theorem B3369863 : Blo 884570 3369863 := bstep (se 1 (by rfl) ⟨2527397, by rfl⟩ : syracuseStep 3369863 = 5054795) B5054795
theorem B163998755 : Blo 884570 163998755 := bstep (se 1 (by rfl) ⟨122999066, by rfl⟩ : syracuseStep 163998755 = 245998133) B245998133
theorem B1993787 : Blo 884570 1993787 := bstep (se 1 (by rfl) ⟨1495340, by rfl⟩ : syracuseStep 1993787 = 2990681) B2990681
theorem B3370045 : Blo 884570 3370045 := bstep (se 3 (by rfl) ⟨631883, by rfl⟩ : syracuseStep 3370045 = 1263767) B1263767
theorem B2845783 : Blo 884570 2845783 := bstep (se 1 (by rfl) ⟨2134337, by rfl⟩ : syracuseStep 2845783 = 4268675) B4268675
theorem B1993913 : Blo 884570 1993913 := bstep (se 2 (by rfl) ⟨747717, by rfl⟩ : syracuseStep 1993913 = 1495435) B1495435
theorem B1600697 : Blo 884570 1600697 := bstep (se 2 (by rfl) ⟨600261, by rfl⟩ : syracuseStep 1600697 = 1200523) B1200523
theorem B10087901 : Blo 884570 10087901 := bstep (se 3 (by rfl) ⟨1891481, by rfl⟩ : syracuseStep 10087901 = 3782963) B3782963
theorem B1994255 : Blo 884570 1994255 := bstep (se 1 (by rfl) ⟨1495691, by rfl⟩ : syracuseStep 1994255 = 2991383) B2991383
theorem B1994273 : Blo 884570 1994273 := bstep (se 2 (by rfl) ⟨747852, by rfl⟩ : syracuseStep 1994273 = 1495705) B1495705
theorem B1994615 : Blo 884570 1994615 := bstep (se 1 (by rfl) ⟨1495961, by rfl⟩ : syracuseStep 1994615 = 2991923) B2991923
theorem B4485131 : Blo 884570 4485131 := bstep (se 1 (by rfl) ⟨3363848, by rfl⟩ : syracuseStep 4485131 = 6727697) B6727697
theorem B1896463 : Blo 884570 1896463 := bstep (se 1 (by rfl) ⟨1422347, by rfl⟩ : syracuseStep 1896463 = 2844695) B2844695
theorem B1994795 : Blo 884570 1994795 := bstep (se 1 (by rfl) ⟨1496096, by rfl⟩ : syracuseStep 1994795 = 2992193) B2992193
theorem B2125939 : Blo 884570 2125939 := bstep (se 1 (by rfl) ⟨1594454, by rfl⟩ : syracuseStep 2125939 = 3188909) B3188909
theorem B4485293 : Blo 884570 4485293 := bstep (se 3 (by rfl) ⟨840992, by rfl⟩ : syracuseStep 4485293 = 1681985) B1681985
theorem B1995155 : Blo 884570 1995155 := bstep (se 1 (by rfl) ⟨1496366, by rfl⟩ : syracuseStep 1995155 = 2992733) B2992733
theorem B1995209 : Blo 884570 1995209 := bstep (se 2 (by rfl) ⟨748203, by rfl⟩ : syracuseStep 1995209 = 1496407) B1496407
theorem B2519687 : Blo 884570 2519687 := bstep (se 1 (by rfl) ⟨1889765, by rfl⟩ : syracuseStep 2519687 = 3779531) B3779531
theorem B1012411 : Blo 884570 1012411 := bstep (se 1 (by rfl) ⟨759308, by rfl⟩ : syracuseStep 1012411 = 1518617) B1518617
theorem B3371777 : Blo 884570 3371777 := bstep (se 2 (by rfl) ⟨1264416, by rfl⟩ : syracuseStep 3371777 = 2528833) B2528833
theorem B2519869 : Blo 884570 2519869 := bstep (se 3 (by rfl) ⟨472475, by rfl⟩ : syracuseStep 2519869 = 944951) B944951
theorem B1995911 : Blo 884570 1995911 := bstep (se 1 (by rfl) ⟨1496933, by rfl⟩ : syracuseStep 1995911 = 2993867) B2993867
theorem B2520335 : Blo 884570 2520335 := bstep (se 1 (by rfl) ⟨1890251, by rfl⟩ : syracuseStep 2520335 = 3780503) B3780503
theorem B8516897 : Blo 884570 8516897 := bstep (se 2 (by rfl) ⟨3193836, by rfl⟩ : syracuseStep 8516897 = 6387673) B6387673
theorem B1996091 : Blo 884570 1996091 := bstep (se 1 (by rfl) ⟨1497068, by rfl⟩ : syracuseStep 1996091 = 2994137) B2994137
theorem B1996217 : Blo 884570 1996217 := bstep (se 2 (by rfl) ⟨748581, by rfl⟩ : syracuseStep 1996217 = 1497163) B1497163
theorem B4486913 : Blo 884570 4486913 := bstep (se 2 (by rfl) ⟨1682592, by rfl⟩ : syracuseStep 4486913 = 3365185) B3365185
theorem B1996559 : Blo 884570 1996559 := bstep (se 1 (by rfl) ⟨1497419, by rfl⟩ : syracuseStep 1996559 = 2994839) B2994839
theorem B1996577 : Blo 884570 1996577 := bstep (se 2 (by rfl) ⟨748716, by rfl⟩ : syracuseStep 1996577 = 1497433) B1497433
theorem B19396421 : Blo 884570 19396421 := bstep (se 4 (by rfl) ⟨1818414, by rfl⟩ : syracuseStep 19396421 = 3636829) B3636829
theorem B3372947 : Blo 884570 3372947 := bstep (se 1 (by rfl) ⟨2529710, by rfl⟩ : syracuseStep 3372947 = 5059421) B5059421
theorem B1996919 : Blo 884570 1996919 := bstep (se 1 (by rfl) ⟨1497689, by rfl⟩ : syracuseStep 1996919 = 2995379) B2995379
theorem B1997099 : Blo 884570 1997099 := bstep (se 1 (by rfl) ⟨1497824, by rfl⟩ : syracuseStep 1997099 = 2995649) B2995649
theorem B2128187 : Blo 884570 2128187 := bstep (se 1 (by rfl) ⟨1596140, by rfl⟩ : syracuseStep 2128187 = 3192281) B3192281
theorem B3373447 : Blo 884570 3373447 := bstep (se 1 (by rfl) ⟨2530085, by rfl⟩ : syracuseStep 3373447 = 5060171) B5060171
theorem B2521601 : Blo 884570 2521601 := bstep (se 2 (by rfl) ⟨945600, by rfl⟩ : syracuseStep 2521601 = 1891201) B1891201
theorem B4487723 : Blo 884570 4487723 := bstep (se 1 (by rfl) ⟨3365792, by rfl⟩ : syracuseStep 4487723 = 6731585) B6731585
theorem B1997459 : Blo 884570 1997459 := bstep (se 1 (by rfl) ⟨1498094, by rfl⟩ : syracuseStep 1997459 = 2996189) B2996189
theorem B1997513 : Blo 884570 1997513 := bstep (se 2 (by rfl) ⟨749067, by rfl⟩ : syracuseStep 1997513 = 1498135) B1498135
theorem B4848841 : Blo 884570 4848841 := bstep (se 2 (by rfl) ⟨1818315, by rfl⟩ : syracuseStep 4848841 = 3636631) B3636631
theorem B1998215 : Blo 884570 1998215 := bstep (se 1 (by rfl) ⟨1498661, by rfl⟩ : syracuseStep 1998215 = 2997323) B2997323
theorem B1998395 : Blo 884570 1998395 := bstep (se 1 (by rfl) ⟨1498796, by rfl⟩ : syracuseStep 1998395 = 2997593) B2997593
theorem B1998521 : Blo 884570 1998521 := bstep (se 2 (by rfl) ⟨749445, by rfl⟩ : syracuseStep 1998521 = 1498891) B1498891
theorem B4489019 : Blo 884570 4489019 := bstep (se 1 (by rfl) ⟨3366764, by rfl⟩ : syracuseStep 4489019 = 6733529) B6733529
theorem B884615 : Blo 884570 884615 := bstep (se 1 (by rfl) ⟨663461, by rfl⟩ : syracuseStep 884615 = 1326923) B1326923
theorem B884623 : Blo 884570 884623 := bstep (se 1 (by rfl) ⟨663467, by rfl⟩ : syracuseStep 884623 = 1326935) B1326935
theorem B884667 : Blo 884570 884667 := bstep (se 1 (by rfl) ⟨663500, by rfl⟩ : syracuseStep 884667 = 1327001) B1327001
theorem B4489181 : Blo 884570 4489181 := bstep (se 3 (by rfl) ⟨841721, by rfl⟩ : syracuseStep 4489181 = 1683443) B1683443
theorem B884775 : Blo 884570 884775 := bstep (se 1 (by rfl) ⟨663581, by rfl⟩ : syracuseStep 884775 = 1327163) B1327163
theorem B884815 : Blo 884570 884815 := bstep (se 1 (by rfl) ⟨663611, by rfl⟩ : syracuseStep 884815 = 1327223) B1327223
theorem B884831 : Blo 884570 884831 := bstep (se 1 (by rfl) ⟨663623, by rfl⟩ : syracuseStep 884831 = 1327247) B1327247
theorem B884859 : Blo 884570 884859 := bstep (se 1 (by rfl) ⟨663644, by rfl⟩ : syracuseStep 884859 = 1327289) B1327289
theorem B8618147 : Blo 884570 8618147 := bstep (se 1 (by rfl) ⟨6463610, by rfl⟩ : syracuseStep 8618147 = 12927221) B12927221
theorem B884911 : Blo 884570 884911 := bstep (se 1 (by rfl) ⟨663683, by rfl⟩ : syracuseStep 884911 = 1327367) B1327367
theorem B884935 : Blo 884570 884935 := bstep (se 1 (by rfl) ⟨663701, by rfl⟩ : syracuseStep 884935 = 1327403) B1327403
theorem B884955 : Blo 884570 884955 := bstep (se 1 (by rfl) ⟨663716, by rfl⟩ : syracuseStep 884955 = 1327433) B1327433
theorem B885031 : Blo 884570 885031 := bstep (se 1 (by rfl) ⟨663773, by rfl⟩ : syracuseStep 885031 = 1327547) B1327547
theorem B885071 : Blo 884570 885071 := bstep (se 1 (by rfl) ⟨663803, by rfl⟩ : syracuseStep 885071 = 1327607) B1327607
theorem B885087 : Blo 884570 885087 := bstep (se 1 (by rfl) ⟨663815, by rfl⟩ : syracuseStep 885087 = 1327631) B1327631
theorem B885115 : Blo 884570 885115 := bstep (se 1 (by rfl) ⟨663836, by rfl⟩ : syracuseStep 885115 = 1327673) B1327673
theorem B1540495 : Blo 884570 1540495 := bstep (se 1 (by rfl) ⟨1155371, by rfl⟩ : syracuseStep 1540495 = 2310743) B2310743
theorem B885167 : Blo 884570 885167 := bstep (se 1 (by rfl) ⟨663875, by rfl⟩ : syracuseStep 885167 = 1327751) B1327751
theorem B885191 : Blo 884570 885191 := bstep (se 1 (by rfl) ⟨663893, by rfl⟩ : syracuseStep 885191 = 1327787) B1327787
theorem B885211 : Blo 884570 885211 := bstep (se 1 (by rfl) ⟨663908, by rfl⟩ : syracuseStep 885211 = 1327817) B1327817
theorem B6717977 : Blo 884570 6717977 := bstep (se 2 (by rfl) ⟨2519241, by rfl⟩ : syracuseStep 6717977 = 5038483) B5038483
theorem B885287 : Blo 884570 885287 := bstep (se 1 (by rfl) ⟨663965, by rfl⟩ : syracuseStep 885287 = 1327931) B1327931
theorem B885327 : Blo 884570 885327 := bstep (se 1 (by rfl) ⟨663995, by rfl⟩ : syracuseStep 885327 = 1327991) B1327991
theorem B885343 : Blo 884570 885343 := bstep (se 1 (by rfl) ⟨664007, by rfl⟩ : syracuseStep 885343 = 1328015) B1328015
theorem B885371 : Blo 884570 885371 := bstep (se 1 (by rfl) ⟨664028, by rfl⟩ : syracuseStep 885371 = 1328057) B1328057
theorem B885423 : Blo 884570 885423 := bstep (se 1 (by rfl) ⟨664067, by rfl⟩ : syracuseStep 885423 = 1328135) B1328135
theorem B885447 : Blo 884570 885447 := bstep (se 1 (by rfl) ⟨664085, by rfl⟩ : syracuseStep 885447 = 1328171) B1328171
theorem B885467 : Blo 884570 885467 := bstep (se 1 (by rfl) ⟨664100, by rfl⟩ : syracuseStep 885467 = 1328201) B1328201
theorem B885543 : Blo 884570 885543 := bstep (se 1 (by rfl) ⟨664157, by rfl⟩ : syracuseStep 885543 = 1328315) B1328315
theorem B885583 : Blo 884570 885583 := bstep (se 1 (by rfl) ⟨664187, by rfl⟩ : syracuseStep 885583 = 1328375) B1328375
theorem B885599 : Blo 884570 885599 := bstep (se 1 (by rfl) ⟨664199, by rfl⟩ : syracuseStep 885599 = 1328399) B1328399
theorem B885627 : Blo 884570 885627 := bstep (se 1 (by rfl) ⟨664220, by rfl⟩ : syracuseStep 885627 = 1328441) B1328441
theorem B885679 : Blo 884570 885679 := bstep (se 1 (by rfl) ⟨664259, by rfl⟩ : syracuseStep 885679 = 1328519) B1328519
theorem B2556847 : Blo 884570 2556847 := bstep (se 1 (by rfl) ⟨1917635, by rfl⟩ : syracuseStep 2556847 = 3835271) B3835271
theorem B885703 : Blo 884570 885703 := bstep (se 1 (by rfl) ⟨664277, by rfl⟩ : syracuseStep 885703 = 1328555) B1328555
theorem B885723 : Blo 884570 885723 := bstep (se 1 (by rfl) ⟨664292, by rfl⟩ : syracuseStep 885723 = 1328585) B1328585
theorem B885799 : Blo 884570 885799 := bstep (se 1 (by rfl) ⟨664349, by rfl⟩ : syracuseStep 885799 = 1328699) B1328699
theorem B885839 : Blo 884570 885839 := bstep (se 1 (by rfl) ⟨664379, by rfl⟩ : syracuseStep 885839 = 1328759) B1328759
theorem B885855 : Blo 884570 885855 := bstep (se 1 (by rfl) ⟨664391, by rfl⟩ : syracuseStep 885855 = 1328783) B1328783
theorem B885883 : Blo 884570 885883 := bstep (se 1 (by rfl) ⟨664412, by rfl⟩ : syracuseStep 885883 = 1328825) B1328825
theorem B885935 : Blo 884570 885935 := bstep (se 1 (by rfl) ⟨664451, by rfl⟩ : syracuseStep 885935 = 1328903) B1328903
theorem B885959 : Blo 884570 885959 := bstep (se 1 (by rfl) ⟨664469, by rfl⟩ : syracuseStep 885959 = 1328939) B1328939
theorem B885979 : Blo 884570 885979 := bstep (se 1 (by rfl) ⟨664484, by rfl⟩ : syracuseStep 885979 = 1328969) B1328969
theorem B886055 : Blo 884570 886055 := bstep (se 1 (by rfl) ⟨664541, by rfl⟩ : syracuseStep 886055 = 1329083) B1329083
theorem B886095 : Blo 884570 886095 := bstep (se 1 (by rfl) ⟨664571, by rfl⟩ : syracuseStep 886095 = 1329143) B1329143
theorem B886111 : Blo 884570 886111 := bstep (se 1 (by rfl) ⟨664583, by rfl⟩ : syracuseStep 886111 = 1329167) B1329167
theorem B886139 : Blo 884570 886139 := bstep (se 1 (by rfl) ⟨664604, by rfl⟩ : syracuseStep 886139 = 1329209) B1329209
theorem B4490639 : Blo 884570 4490639 := bstep (se 1 (by rfl) ⟨3367979, by rfl⟩ : syracuseStep 4490639 = 6735959) B6735959
theorem B886191 : Blo 884570 886191 := bstep (se 1 (by rfl) ⟨664643, by rfl⟩ : syracuseStep 886191 = 1329287) B1329287
theorem B140019121 : Blo 884570 140019121 := bstep (se 2 (by rfl) ⟨52507170, by rfl⟩ : syracuseStep 140019121 = 105014341) B105014341
theorem B886215 : Blo 884570 886215 := bstep (se 1 (by rfl) ⟨664661, by rfl⟩ : syracuseStep 886215 = 1329323) B1329323
theorem B886235 : Blo 884570 886235 := bstep (se 1 (by rfl) ⟨664676, by rfl⟩ : syracuseStep 886235 = 1329353) B1329353
theorem B12977653 : Blo 884570 12977653 := bstep (se 5 (by rfl) ⟨608327, by rfl⟩ : syracuseStep 12977653 = 1216655) B1216655
theorem B886311 : Blo 884570 886311 := bstep (se 1 (by rfl) ⟨664733, by rfl⟩ : syracuseStep 886311 = 1329467) B1329467
theorem B886351 : Blo 884570 886351 := bstep (se 1 (by rfl) ⟨664763, by rfl⟩ : syracuseStep 886351 = 1329527) B1329527
theorem B886367 : Blo 884570 886367 := bstep (se 1 (by rfl) ⟨664775, by rfl⟩ : syracuseStep 886367 = 1329551) B1329551
theorem B886395 : Blo 884570 886395 := bstep (se 1 (by rfl) ⟨664796, by rfl⟩ : syracuseStep 886395 = 1329593) B1329593
theorem B886447 : Blo 884570 886447 := bstep (se 1 (by rfl) ⟨664835, by rfl⟩ : syracuseStep 886447 = 1329671) B1329671
theorem B886471 : Blo 884570 886471 := bstep (se 1 (by rfl) ⟨664853, by rfl⟩ : syracuseStep 886471 = 1329707) B1329707
theorem B886491 : Blo 884570 886491 := bstep (se 1 (by rfl) ⟨664868, by rfl⟩ : syracuseStep 886491 = 1329737) B1329737
theorem B886567 : Blo 884570 886567 := bstep (se 1 (by rfl) ⟨664925, by rfl⟩ : syracuseStep 886567 = 1329851) B1329851
theorem B886607 : Blo 884570 886607 := bstep (se 1 (by rfl) ⟨664955, by rfl⟩ : syracuseStep 886607 = 1329911) B1329911
theorem B886623 : Blo 884570 886623 := bstep (se 1 (by rfl) ⟨664967, by rfl⟩ : syracuseStep 886623 = 1329935) B1329935
theorem B886651 : Blo 884570 886651 := bstep (se 1 (by rfl) ⟨664988, by rfl⟩ : syracuseStep 886651 = 1329977) B1329977
theorem B886703 : Blo 884570 886703 := bstep (se 1 (by rfl) ⟨665027, by rfl⟩ : syracuseStep 886703 = 1330055) B1330055
theorem B886727 : Blo 884570 886727 := bstep (se 1 (by rfl) ⟨665045, by rfl⟩ : syracuseStep 886727 = 1330091) B1330091
theorem B886747 : Blo 884570 886747 := bstep (se 1 (by rfl) ⟨665060, by rfl⟩ : syracuseStep 886747 = 1330121) B1330121
theorem B9865223 : Blo 884570 9865223 := bstep (se 1 (by rfl) ⟨7398917, by rfl⟩ : syracuseStep 9865223 = 14797835) B14797835
theorem B886823 : Blo 884570 886823 := bstep (se 1 (by rfl) ⟨665117, by rfl⟩ : syracuseStep 886823 = 1330235) B1330235
theorem B886863 : Blo 884570 886863 := bstep (se 1 (by rfl) ⟨665147, by rfl⟩ : syracuseStep 886863 = 1330295) B1330295
theorem B886879 : Blo 884570 886879 := bstep (se 1 (by rfl) ⟨665159, by rfl⟩ : syracuseStep 886879 = 1330319) B1330319
theorem B886907 : Blo 884570 886907 := bstep (se 1 (by rfl) ⟨665180, by rfl⟩ : syracuseStep 886907 = 1330361) B1330361
theorem B886959 : Blo 884570 886959 := bstep (se 1 (by rfl) ⟨665219, by rfl⟩ : syracuseStep 886959 = 1330439) B1330439
theorem B886983 : Blo 884570 886983 := bstep (se 1 (by rfl) ⟨665237, by rfl⟩ : syracuseStep 886983 = 1330475) B1330475
theorem B887003 : Blo 884570 887003 := bstep (se 1 (by rfl) ⟨665252, by rfl⟩ : syracuseStep 887003 = 1330505) B1330505
theorem B11536673 : Blo 884570 11536673 := bstep (se 2 (by rfl) ⟨4326252, by rfl⟩ : syracuseStep 11536673 = 8652505) B8652505
theorem B887079 : Blo 884570 887079 := bstep (se 1 (by rfl) ⟨665309, by rfl⟩ : syracuseStep 887079 = 1330619) B1330619
theorem B887119 : Blo 884570 887119 := bstep (se 1 (by rfl) ⟨665339, by rfl⟩ : syracuseStep 887119 = 1330679) B1330679
theorem B887135 : Blo 884570 887135 := bstep (se 1 (by rfl) ⟨665351, by rfl⟩ : syracuseStep 887135 = 1330703) B1330703
theorem B8194409 : Blo 884570 8194409 := bstep (se 2 (by rfl) ⟨3072903, by rfl⟩ : syracuseStep 8194409 = 6145807) B6145807
theorem B887163 : Blo 884570 887163 := bstep (se 1 (by rfl) ⟨665372, by rfl⟩ : syracuseStep 887163 = 1330745) B1330745
theorem B887215 : Blo 884570 887215 := bstep (se 1 (by rfl) ⟨665411, by rfl⟩ : syracuseStep 887215 = 1330823) B1330823
theorem B887239 : Blo 884570 887239 := bstep (se 1 (by rfl) ⟨665429, by rfl⟩ : syracuseStep 887239 = 1330859) B1330859
theorem B887259 : Blo 884570 887259 := bstep (se 1 (by rfl) ⟨665444, by rfl⟩ : syracuseStep 887259 = 1330889) B1330889
theorem B2525735 : Blo 884570 2525735 := bstep (se 1 (by rfl) ⟨1894301, by rfl⟩ : syracuseStep 2525735 = 3788603) B3788603
theorem B887335 : Blo 884570 887335 := bstep (se 1 (by rfl) ⟨665501, by rfl⟩ : syracuseStep 887335 = 1331003) B1331003
theorem B887375 : Blo 884570 887375 := bstep (se 1 (by rfl) ⟨665531, by rfl⟩ : syracuseStep 887375 = 1331063) B1331063
theorem B887391 : Blo 884570 887391 := bstep (se 1 (by rfl) ⟨665543, by rfl⟩ : syracuseStep 887391 = 1331087) B1331087
theorem B887419 : Blo 884570 887419 := bstep (se 1 (by rfl) ⟨665564, by rfl⟩ : syracuseStep 887419 = 1331129) B1331129
theorem B2558603 : Blo 884570 2558603 := bstep (se 1 (by rfl) ⟨1918952, by rfl⟩ : syracuseStep 2558603 = 3837905) B3837905
theorem B887471 : Blo 884570 887471 := bstep (se 1 (by rfl) ⟨665603, by rfl⟩ : syracuseStep 887471 = 1331207) B1331207
theorem B887495 : Blo 884570 887495 := bstep (se 1 (by rfl) ⟨665621, by rfl⟩ : syracuseStep 887495 = 1331243) B1331243
theorem B887515 : Blo 884570 887515 := bstep (se 1 (by rfl) ⟨665636, by rfl⟩ : syracuseStep 887515 = 1331273) B1331273
theorem B887591 : Blo 884570 887591 := bstep (se 1 (by rfl) ⟨665693, by rfl⟩ : syracuseStep 887591 = 1331387) B1331387
theorem B887631 : Blo 884570 887631 := bstep (se 1 (by rfl) ⟨665723, by rfl⟩ : syracuseStep 887631 = 1331447) B1331447
theorem B887647 : Blo 884570 887647 := bstep (se 1 (by rfl) ⟨665735, by rfl⟩ : syracuseStep 887647 = 1331471) B1331471
theorem B887675 : Blo 884570 887675 := bstep (se 1 (by rfl) ⟨665756, by rfl⟩ : syracuseStep 887675 = 1331513) B1331513
theorem B887727 : Blo 884570 887727 := bstep (se 1 (by rfl) ⟨665795, by rfl⟩ : syracuseStep 887727 = 1331591) B1331591
theorem B887751 : Blo 884570 887751 := bstep (se 1 (by rfl) ⟨665813, by rfl⟩ : syracuseStep 887751 = 1331627) B1331627
theorem B887771 : Blo 884570 887771 := bstep (se 1 (by rfl) ⟨665828, by rfl⟩ : syracuseStep 887771 = 1331657) B1331657
theorem B887847 : Blo 884570 887847 := bstep (se 1 (by rfl) ⟨665885, by rfl⟩ : syracuseStep 887847 = 1331771) B1331771
theorem B38374469 : Blo 884570 38374469 := bstep (se 4 (by rfl) ⟨3597606, by rfl⟩ : syracuseStep 38374469 = 7195213) B7195213
theorem B887887 : Blo 884570 887887 := bstep (se 1 (by rfl) ⟨665915, by rfl⟩ : syracuseStep 887887 = 1331831) B1331831
theorem B887903 : Blo 884570 887903 := bstep (se 1 (by rfl) ⟨665927, by rfl⟩ : syracuseStep 887903 = 1331855) B1331855
theorem B887931 : Blo 884570 887931 := bstep (se 1 (by rfl) ⟨665948, by rfl⟩ : syracuseStep 887931 = 1331897) B1331897
theorem B887983 : Blo 884570 887983 := bstep (se 1 (by rfl) ⟨665987, by rfl⟩ : syracuseStep 887983 = 1331975) B1331975
theorem B9112769 : Blo 884570 9112769 := bstep (se 2 (by rfl) ⟨3417288, by rfl⟩ : syracuseStep 9112769 = 6834577) B6834577
theorem B888007 : Blo 884570 888007 := bstep (se 1 (by rfl) ⟨666005, by rfl⟩ : syracuseStep 888007 = 1332011) B1332011
theorem B888027 : Blo 884570 888027 := bstep (se 1 (by rfl) ⟨666020, by rfl⟩ : syracuseStep 888027 = 1332041) B1332041
theorem B888103 : Blo 884570 888103 := bstep (se 1 (by rfl) ⟨666077, by rfl⟩ : syracuseStep 888103 = 1332155) B1332155
theorem B17272129 : Blo 884570 17272129 := bstep (se 2 (by rfl) ⟨6477048, by rfl⟩ : syracuseStep 17272129 = 12954097) B12954097
theorem B888143 : Blo 884570 888143 := bstep (se 1 (by rfl) ⟨666107, by rfl⟩ : syracuseStep 888143 = 1332215) B1332215
theorem B888159 : Blo 884570 888159 := bstep (se 1 (by rfl) ⟨666119, by rfl⟩ : syracuseStep 888159 = 1332239) B1332239
theorem B888187 : Blo 884570 888187 := bstep (se 1 (by rfl) ⟨666140, by rfl⟩ : syracuseStep 888187 = 1332281) B1332281
theorem B6720893 : Blo 884570 6720893 := bstep (se 3 (by rfl) ⟨1260167, by rfl⟩ : syracuseStep 6720893 = 2520335) B2520335
theorem B888239 : Blo 884570 888239 := bstep (se 1 (by rfl) ⟨666179, by rfl⟩ : syracuseStep 888239 = 1332359) B1332359
theorem B888263 : Blo 884570 888263 := bstep (se 1 (by rfl) ⟨666197, by rfl⟩ : syracuseStep 888263 = 1332395) B1332395
theorem B4492745 : Blo 884570 4492745 := bstep (se 2 (by rfl) ⟨1684779, by rfl⟩ : syracuseStep 4492745 = 3369559) B3369559
theorem B888283 : Blo 884570 888283 := bstep (se 1 (by rfl) ⟨666212, by rfl⟩ : syracuseStep 888283 = 1332425) B1332425
theorem B2985497 : Blo 884570 2985497 := bstep (se 2 (by rfl) ⟨1119561, by rfl⟩ : syracuseStep 2985497 = 2239123) B2239123
theorem B888359 : Blo 884570 888359 := bstep (se 1 (by rfl) ⟨666269, by rfl⟩ : syracuseStep 888359 = 1332539) B1332539
theorem B888399 : Blo 884570 888399 := bstep (se 1 (by rfl) ⟨666299, by rfl⟩ : syracuseStep 888399 = 1332599) B1332599
theorem B888415 : Blo 884570 888415 := bstep (se 1 (by rfl) ⟨666311, by rfl⟩ : syracuseStep 888415 = 1332623) B1332623
theorem B888443 : Blo 884570 888443 := bstep (se 1 (by rfl) ⟨666332, by rfl⟩ : syracuseStep 888443 = 1332665) B1332665
theorem B888495 : Blo 884570 888495 := bstep (se 1 (by rfl) ⟨666371, by rfl⟩ : syracuseStep 888495 = 1332743) B1332743
theorem B888519 : Blo 884570 888519 := bstep (se 1 (by rfl) ⟨666389, by rfl⟩ : syracuseStep 888519 = 1332779) B1332779
theorem B888539 : Blo 884570 888539 := bstep (se 1 (by rfl) ⟨666404, by rfl⟩ : syracuseStep 888539 = 1332809) B1332809
theorem B15142787 : Blo 884570 15142787 := bstep (se 1 (by rfl) ⟨11357090, by rfl⟩ : syracuseStep 15142787 = 22714181) B22714181
theorem B4853665 : Blo 884570 4853665 := bstep (se 2 (by rfl) ⟨1820124, by rfl⟩ : syracuseStep 4853665 = 3640249) B3640249
theorem B2133935 : Blo 884570 2133935 := bstep (se 1 (by rfl) ⟨1600451, by rfl⟩ : syracuseStep 2133935 = 3200903) B3200903
theorem B1347511 : Blo 884570 1347511 := bstep (se 1 (by rfl) ⟨1010633, by rfl⟩ : syracuseStep 1347511 = 2021267) B2021267
theorem B2527159 : Blo 884570 2527159 := bstep (se 1 (by rfl) ⟨1895369, by rfl⟩ : syracuseStep 2527159 = 3790739) B3790739
theorem B4493393 : Blo 884570 4493393 := bstep (se 2 (by rfl) ⟨1685022, by rfl⟩ : syracuseStep 4493393 = 3370045) B3370045
theorem B1347935 : Blo 884570 1347935 := bstep (se 1 (by rfl) ⟨1010951, by rfl⟩ : syracuseStep 1347935 = 2021903) B2021903
theorem B2429309 : Blo 884570 2429309 := bstep (se 3 (by rfl) ⟨455495, by rfl⟩ : syracuseStep 2429309 = 910991) B910991
theorem B2986631 : Blo 884570 2986631 := bstep (se 1 (by rfl) ⟨2239973, by rfl⟩ : syracuseStep 2986631 = 4479947) B4479947
theorem B2986685 : Blo 884570 2986685 := bstep (se 3 (by rfl) ⟨560003, by rfl⟩ : syracuseStep 2986685 = 1120007) B1120007
theorem B2986847 : Blo 884570 2986847 := bstep (se 1 (by rfl) ⟨2240135, by rfl⟩ : syracuseStep 2986847 = 4480271) B4480271
theorem B19928065 : Blo 884570 19928065 := bstep (se 2 (by rfl) ⟨7473024, by rfl⟩ : syracuseStep 19928065 = 14946049) B14946049
theorem B2987009 : Blo 884570 2987009 := bstep (se 2 (by rfl) ⟨1120128, by rfl⟩ : syracuseStep 2987009 = 2240257) B2240257
theorem B2528263 : Blo 884570 2528263 := bstep (se 1 (by rfl) ⟨1896197, by rfl⟩ : syracuseStep 2528263 = 3792395) B3792395
theorem B2528617 : Blo 884570 2528617 := bstep (se 2 (by rfl) ⟨948231, by rfl⟩ : syracuseStep 2528617 = 1896463) B1896463
theorem B2528891 : Blo 884570 2528891 := bstep (se 1 (by rfl) ⟨1896668, by rfl⟩ : syracuseStep 2528891 = 3793337) B3793337
theorem B2987819 : Blo 884570 2987819 := bstep (se 1 (by rfl) ⟨2240864, by rfl⟩ : syracuseStep 2987819 = 4481729) B4481729
theorem B2988089 : Blo 884570 2988089 := bstep (se 2 (by rfl) ⟨1120533, by rfl⟩ : syracuseStep 2988089 = 2241067) B2241067
theorem B1349881 : Blo 884570 1349881 := bstep (se 2 (by rfl) ⟨506205, by rfl⟩ : syracuseStep 1349881 = 1012411) B1012411
theorem B2988413 : Blo 884570 2988413 := bstep (se 3 (by rfl) ⟨560327, by rfl⟩ : syracuseStep 2988413 = 1120655) B1120655
theorem B25860485 : Blo 884570 25860485 := bstep (se 4 (by rfl) ⟨2424420, by rfl⟩ : syracuseStep 25860485 = 4848841) B4848841
theorem B1120807 : Blo 884570 1120807 := bstep (se 1 (by rfl) ⟨840605, by rfl⟩ : syracuseStep 1120807 = 1681211) B1681211
theorem B5053063 : Blo 884570 5053063 := bstep (se 1 (by rfl) ⟨3789797, by rfl⟩ : syracuseStep 5053063 = 7579595) B7579595
theorem B2988683 : Blo 884570 2988683 := bstep (se 1 (by rfl) ⟨2241512, by rfl⟩ : syracuseStep 2988683 = 4483025) B4483025
theorem B2562749 : Blo 884570 2562749 := bstep (se 3 (by rfl) ⟨480515, by rfl⟩ : syracuseStep 2562749 = 961031) B961031
theorem B1121131 : Blo 884570 1121131 := bstep (se 1 (by rfl) ⟨840848, by rfl⟩ : syracuseStep 1121131 = 1681697) B1681697
theorem B2530223 : Blo 884570 2530223 := bstep (se 1 (by rfl) ⟨1897667, by rfl⟩ : syracuseStep 2530223 = 3795335) B3795335
theorem B1121359 : Blo 884570 1121359 := bstep (se 1 (by rfl) ⟨841019, by rfl⟩ : syracuseStep 1121359 = 1682039) B1682039
theorem B2989601 : Blo 884570 2989601 := bstep (se 2 (by rfl) ⟨1121100, by rfl⟩ : syracuseStep 2989601 = 2242201) B2242201
theorem B6725267 : Blo 884570 6725267 := bstep (se 1 (by rfl) ⟨5043950, by rfl⟩ : syracuseStep 6725267 = 10087901) B10087901
theorem B2989817 : Blo 884570 2989817 := bstep (se 2 (by rfl) ⟨1121181, by rfl⟩ : syracuseStep 2989817 = 2242363) B2242363
theorem B12787571 : Blo 884570 12787571 := bstep (se 1 (by rfl) ⟨9590678, by rfl⟩ : syracuseStep 12787571 = 19181357) B19181357
theorem B2990087 : Blo 884570 2990087 := bstep (se 1 (by rfl) ⟨2242565, by rfl⟩ : syracuseStep 2990087 = 4485131) B4485131
theorem B5054521 : Blo 884570 5054521 := bstep (se 2 (by rfl) ⟨1895445, by rfl⟩ : syracuseStep 5054521 = 3790891) B3790891
theorem B2990195 : Blo 884570 2990195 := bstep (se 1 (by rfl) ⟨2242646, by rfl⟩ : syracuseStep 2990195 = 4485293) B4485293
theorem B1122427 : Blo 884570 1122427 := bstep (se 1 (by rfl) ⟨841820, by rfl⟩ : syracuseStep 1122427 = 1683641) B1683641
theorem B1679609 : Blo 884570 1679609 := bstep (se 2 (by rfl) ⟨629853, by rfl⟩ : syracuseStep 1679609 = 1259707) B1259707
theorem B1122655 : Blo 884570 1122655 := bstep (se 1 (by rfl) ⟨841991, by rfl⟩ : syracuseStep 1122655 = 1683983) B1683983
theorem B2990465 : Blo 884570 2990465 := bstep (se 2 (by rfl) ⟨1121424, by rfl⟩ : syracuseStep 2990465 = 2242849) B2242849
theorem B1679791 : Blo 884570 1679791 := bstep (se 1 (by rfl) ⟨1259843, by rfl⟩ : syracuseStep 1679791 = 2519687) B2519687
theorem B4497929 : Blo 884570 4497929 := bstep (se 2 (by rfl) ⟨1686723, by rfl⟩ : syracuseStep 4497929 = 3373447) B3373447
theorem B4792891 : Blo 884570 4792891 := bstep (se 1 (by rfl) ⟨3594668, by rfl⟩ : syracuseStep 4792891 = 7189337) B7189337
theorem B5677931 : Blo 884570 5677931 := bstep (se 1 (by rfl) ⟨4258448, by rfl⟩ : syracuseStep 5677931 = 8516897) B8516897
theorem B1123247 : Blo 884570 1123247 := bstep (se 1 (by rfl) ⟨842435, by rfl⟩ : syracuseStep 1123247 = 1684871) B1684871
theorem B4268983 : Blo 884570 4268983 := bstep (se 1 (by rfl) ⟨3201737, by rfl⟩ : syracuseStep 4268983 = 6403475) B6403475
theorem B2991275 : Blo 884570 2991275 := bstep (se 1 (by rfl) ⟨2243456, by rfl⟩ : syracuseStep 2991275 = 4486913) B4486913
theorem B1516975 : Blo 884570 1516975 := bstep (se 1 (by rfl) ⟨1137731, by rfl⟩ : syracuseStep 1516975 = 2275463) B2275463
theorem B1418791 : Blo 884570 1418791 := bstep (se 1 (by rfl) ⟨1064093, by rfl⟩ : syracuseStep 1418791 = 2128187) B2128187
theorem B1681067 : Blo 884570 1681067 := bstep (se 1 (by rfl) ⟨1260800, by rfl⟩ : syracuseStep 1681067 = 2521601) B2521601
theorem B2991815 : Blo 884570 2991815 := bstep (se 1 (by rfl) ⟨2243861, by rfl⟩ : syracuseStep 2991815 = 4487723) B4487723
theorem B6137593 : Blo 884570 6137593 := bstep (se 2 (by rfl) ⟨2301597, by rfl⟩ : syracuseStep 6137593 = 4603195) B4603195
theorem B6138013 : Blo 884570 6138013 := bstep (se 3 (by rfl) ⟨1150877, by rfl⟩ : syracuseStep 6138013 = 2301755) B2301755
theorem B1419785 : Blo 884570 1419785 := bstep (se 2 (by rfl) ⟨532419, by rfl⟩ : syracuseStep 1419785 = 1064839) B1064839
theorem B2992679 : Blo 884570 2992679 := bstep (se 1 (by rfl) ⟨2244509, by rfl⟩ : syracuseStep 2992679 = 4489019) B4489019
theorem B2239073 : Blo 884570 2239073 := bstep (se 2 (by rfl) ⟨839652, by rfl⟩ : syracuseStep 2239073 = 1679305) B1679305
theorem B2992787 : Blo 884570 2992787 := bstep (se 1 (by rfl) ⟨2244590, by rfl⟩ : syracuseStep 2992787 = 4489181) B4489181
theorem B3779257 : Blo 884570 3779257 := bstep (se 2 (by rfl) ⟨1417221, by rfl⟩ : syracuseStep 3779257 = 2834443) B2834443
theorem B4664017 : Blo 884570 4664017 := bstep (se 2 (by rfl) ⟨1749006, by rfl⟩ : syracuseStep 4664017 = 3498013) B3498013
theorem B2993003 : Blo 884570 2993003 := bstep (se 1 (by rfl) ⟨2244752, by rfl⟩ : syracuseStep 2993003 = 4489505) B4489505
theorem B2993057 : Blo 884570 2993057 := bstep (se 2 (by rfl) ⟨1122396, by rfl⟩ : syracuseStep 2993057 = 2244793) B2244793
theorem B6728669 : Blo 884570 6728669 := bstep (se 3 (by rfl) ⟨1261625, by rfl⟩ : syracuseStep 6728669 = 2523251) B2523251
theorem B1682441 : Blo 884570 1682441 := bstep (se 2 (by rfl) ⟨630915, by rfl⟩ : syracuseStep 1682441 = 1261831) B1261831
theorem B621849635 : Blo 884570 621849635 := bstep (se 1 (by rfl) ⟨466387226, by rfl⟩ : syracuseStep 621849635 = 932774453) B932774453
theorem B1682471 : Blo 884570 1682471 := bstep (se 1 (by rfl) ⟨1261853, by rfl⟩ : syracuseStep 1682471 = 2523707) B2523707
theorem B3320947 : Blo 884570 3320947 := bstep (se 1 (by rfl) ⟨2490710, by rfl⟩ : syracuseStep 3320947 = 4981421) B4981421
theorem B2272427 : Blo 884570 2272427 := bstep (se 1 (by rfl) ⟨1704320, by rfl⟩ : syracuseStep 2272427 = 3408641) B3408641
theorem B6925591 : Blo 884570 6925591 := bstep (se 1 (by rfl) ⟨5194193, by rfl⟩ : syracuseStep 6925591 = 10388387) B10388387
theorem B2993651 : Blo 884570 2993651 := bstep (se 1 (by rfl) ⟨2245238, by rfl⟩ : syracuseStep 2993651 = 4490477) B4490477
theorem B10792435 : Blo 884570 10792435 := bstep (se 1 (by rfl) ⟨8094326, by rfl⟩ : syracuseStep 10792435 = 16188653) B16188653
theorem B1683155 : Blo 884570 1683155 := bstep (se 1 (by rfl) ⟨1262366, by rfl⟩ : syracuseStep 1683155 = 2524733) B2524733
theorem B1683193 : Blo 884570 1683193 := bstep (se 2 (by rfl) ⟨631197, by rfl⟩ : syracuseStep 1683193 = 1262395) B1262395
theorem B1421239 : Blo 884570 1421239 := bstep (se 1 (by rfl) ⟨1065929, by rfl⟩ : syracuseStep 1421239 = 2131859) B2131859
theorem B3780539 : Blo 884570 3780539 := bstep (se 1 (by rfl) ⟨2835404, by rfl⟩ : syracuseStep 3780539 = 5670809) B5670809
theorem B3026945 : Blo 884570 3026945 := bstep (se 2 (by rfl) ⟨1135104, by rfl⟩ : syracuseStep 3026945 = 2270209) B2270209
theorem B2994191 : Blo 884570 2994191 := bstep (se 1 (by rfl) ⟨2245643, by rfl⟩ : syracuseStep 2994191 = 4491287) B4491287
theorem B2240531 : Blo 884570 2240531 := bstep (se 1 (by rfl) ⟨1680398, by rfl⟩ : syracuseStep 2240531 = 3360797) B3360797
theorem B3649853 : Blo 884570 3649853 := bstep (se 3 (by rfl) ⟨684347, by rfl⟩ : syracuseStep 3649853 = 1368695) B1368695
theorem B1683899 : Blo 884570 1683899 := bstep (se 1 (by rfl) ⟨1262924, by rfl⟩ : syracuseStep 1683899 = 2525849) B2525849
theorem B3191329 : Blo 884570 3191329 := bstep (se 2 (by rfl) ⟨1196748, by rfl⟩ : syracuseStep 3191329 = 2393497) B2393497
theorem B2994785 : Blo 884570 2994785 := bstep (se 2 (by rfl) ⟨1123044, by rfl⟩ : syracuseStep 2994785 = 2246089) B2246089
theorem B3781255 : Blo 884570 3781255 := bstep (se 1 (by rfl) ⟨2835941, by rfl⟩ : syracuseStep 3781255 = 5671883) B5671883
theorem B7582571 : Blo 884570 7582571 := bstep (se 1 (by rfl) ⟨5686928, by rfl⟩ : syracuseStep 7582571 = 11373857) B11373857
theorem B1684385 : Blo 884570 1684385 := bstep (se 2 (by rfl) ⟨631644, by rfl⟩ : syracuseStep 1684385 = 1263289) B1263289
theorem B996475 : Blo 884570 996475 := bstep (se 1 (by rfl) ⟨747356, by rfl⟩ : syracuseStep 996475 = 1494713) B1494713
theorem B1684651 : Blo 884570 1684651 := bstep (se 1 (by rfl) ⟨1263488, by rfl⟩ : syracuseStep 1684651 = 2526977) B2526977
theorem B1684955 : Blo 884570 1684955 := bstep (se 1 (by rfl) ⟨1263716, by rfl⟩ : syracuseStep 1684955 = 2527433) B2527433
theorem B996943 : Blo 884570 996943 := bstep (se 1 (by rfl) ⟨747707, by rfl⟩ : syracuseStep 996943 = 1495415) B1495415
theorem B1423097 : Blo 884570 1423097 := bstep (se 2 (by rfl) ⟨533661, by rfl⟩ : syracuseStep 1423097 = 1067323) B1067323
theorem B3192671 : Blo 884570 3192671 := bstep (se 1 (by rfl) ⟨2394503, by rfl⟩ : syracuseStep 3192671 = 4789007) B4789007
theorem B997339 : Blo 884570 997339 := bstep (se 1 (by rfl) ⟨748004, by rfl⟩ : syracuseStep 997339 = 1496009) B1496009
theorem B2996243 : Blo 884570 2996243 := bstep (se 1 (by rfl) ⟨2247182, by rfl⟩ : syracuseStep 2996243 = 4494365) B4494365
theorem B3193175 : Blo 884570 3193175 := bstep (se 1 (by rfl) ⟨2394881, by rfl⟩ : syracuseStep 3193175 = 4789763) B4789763
theorem B2996567 : Blo 884570 2996567 := bstep (se 1 (by rfl) ⟨2247425, by rfl⟩ : syracuseStep 2996567 = 4494851) B4494851
theorem B997807 : Blo 884570 997807 := bstep (se 1 (by rfl) ⟨748355, by rfl⟩ : syracuseStep 997807 = 1496711) B1496711
theorem B1686025 : Blo 884570 1686025 := bstep (se 2 (by rfl) ⟨632259, by rfl⟩ : syracuseStep 1686025 = 1264519) B1264519
theorem B32750257 : Blo 884570 32750257 := bstep (se 2 (by rfl) ⟨12281346, by rfl⟩ : syracuseStep 32750257 = 24562693) B24562693
theorem B998239 : Blo 884570 998239 := bstep (se 1 (by rfl) ⟨748679, by rfl⟩ : syracuseStep 998239 = 1497359) B1497359
theorem B6143147 : Blo 884570 6143147 := bstep (se 1 (by rfl) ⟨4607360, by rfl⟩ : syracuseStep 6143147 = 9214721) B9214721
theorem B998599 : Blo 884570 998599 := bstep (se 1 (by rfl) ⟨748949, by rfl⟩ : syracuseStep 998599 = 1497899) B1497899
theorem B1686739 : Blo 884570 1686739 := bstep (se 1 (by rfl) ⟨1265054, by rfl⟩ : syracuseStep 1686739 = 2530109) B2530109
theorem B2243983 : Blo 884570 2243983 := bstep (se 1 (by rfl) ⟨1682987, by rfl⟩ : syracuseStep 2243983 = 3365975) B3365975
theorem B2997647 : Blo 884570 2997647 := bstep (se 1 (by rfl) ⟨2248235, by rfl⟩ : syracuseStep 2997647 = 4496471) B4496471
theorem B2244307 : Blo 884570 2244307 := bstep (se 1 (by rfl) ⟨1683230, by rfl⟩ : syracuseStep 2244307 = 3366461) B3366461
theorem B2997971 : Blo 884570 2997971 := bstep (se 1 (by rfl) ⟨2248478, by rfl⟩ : syracuseStep 2997971 = 4496957) B4496957
theorem B1326953 : Blo 884570 1326953 := bstep (se 2 (by rfl) ⟨497607, by rfl⟩ : syracuseStep 1326953 = 995215) B995215
theorem B48480119 : Blo 884570 48480119 := bstep (se 1 (by rfl) ⟨36360089, by rfl⟩ : syracuseStep 48480119 = 72720179) B72720179
theorem B1327031 : Blo 884570 1327031 := bstep (se 1 (by rfl) ⟨995273, by rfl⟩ : syracuseStep 1327031 = 1990547) B1990547
theorem B1327067 : Blo 884570 1327067 := bstep (se 1 (by rfl) ⟨995300, by rfl⟩ : syracuseStep 1327067 = 1990601) B1990601
theorem B999463 : Blo 884570 999463 := bstep (se 1 (by rfl) ⟨749597, by rfl⟩ : syracuseStep 999463 = 1499195) B1499195
theorem B10076237 : Blo 884570 10076237 := bstep (se 3 (by rfl) ⟨1889294, by rfl⟩ : syracuseStep 10076237 = 3778589) B3778589
theorem B2834585 : Blo 884570 2834585 := bstep (se 2 (by rfl) ⟨1062969, by rfl⟩ : syracuseStep 2834585 = 2125939) B2125939
theorem B1327535 : Blo 884570 1327535 := bstep (se 1 (by rfl) ⟨995651, by rfl⟩ : syracuseStep 1327535 = 1991303) B1991303
theorem B1327625 : Blo 884570 1327625 := bstep (se 2 (by rfl) ⟨497859, by rfl⟩ : syracuseStep 1327625 = 995719) B995719
theorem B1327655 : Blo 884570 1327655 := bstep (se 1 (by rfl) ⟨995741, by rfl⟩ : syracuseStep 1327655 = 1991483) B1991483
theorem B1327739 : Blo 884570 1327739 := bstep (se 1 (by rfl) ⟨995804, by rfl⟩ : syracuseStep 1327739 = 1991609) B1991609
theorem B2245259 : Blo 884570 2245259 := bstep (se 1 (by rfl) ⟨1683944, by rfl⟩ : syracuseStep 2245259 = 3367889) B3367889
theorem B10240685 : Blo 884570 10240685 := bstep (se 3 (by rfl) ⟨1920128, by rfl⟩ : syracuseStep 10240685 = 3840257) B3840257
theorem B1327865 : Blo 884570 1327865 := bstep (se 2 (by rfl) ⟨497949, by rfl⟩ : syracuseStep 1327865 = 995899) B995899
theorem B1622857 : Blo 884570 1622857 := bstep (se 2 (by rfl) ⟨608571, by rfl⟩ : syracuseStep 1622857 = 1217143) B1217143
theorem B1327967 : Blo 884570 1327967 := bstep (se 1 (by rfl) ⟨995975, by rfl⟩ : syracuseStep 1327967 = 1991951) B1991951
theorem B1327979 : Blo 884570 1327979 := bstep (se 1 (by rfl) ⟨995984, by rfl⟩ : syracuseStep 1327979 = 1991969) B1991969
theorem B1328207 : Blo 884570 1328207 := bstep (se 1 (by rfl) ⟨996155, by rfl⟩ : syracuseStep 1328207 = 1992311) B1992311
theorem B3359825 : Blo 884570 3359825 := bstep (se 2 (by rfl) ⟨1259934, by rfl⟩ : syracuseStep 3359825 = 2519869) B2519869
theorem B1328327 : Blo 884570 1328327 := bstep (se 1 (by rfl) ⟨996245, by rfl⟩ : syracuseStep 1328327 = 1992491) B1992491
theorem B1328489 : Blo 884570 1328489 := bstep (se 2 (by rfl) ⟨498183, by rfl⟩ : syracuseStep 1328489 = 996367) B996367
theorem B3360143 : Blo 884570 3360143 := bstep (se 1 (by rfl) ⟨2520107, by rfl⟩ : syracuseStep 3360143 = 5040215) B5040215
theorem B1328567 : Blo 884570 1328567 := bstep (se 1 (by rfl) ⟨996425, by rfl⟩ : syracuseStep 1328567 = 1992851) B1992851
theorem B3196361 : Blo 884570 3196361 := bstep (se 2 (by rfl) ⟨1198635, by rfl⟩ : syracuseStep 3196361 = 2397271) B2397271
theorem B1328603 : Blo 884570 1328603 := bstep (se 1 (by rfl) ⟨996452, by rfl⟩ : syracuseStep 1328603 = 1992905) B1992905
theorem B27313685 : Blo 884570 27313685 := bstep (se 6 (by rfl) ⟨640164, by rfl⟩ : syracuseStep 27313685 = 1280329) B1280329
theorem B2246393 : Blo 884570 2246393 := bstep (se 2 (by rfl) ⟨842397, by rfl⟩ : syracuseStep 2246393 = 1684795) B1684795
theorem B1492843 : Blo 884570 1492843 := bstep (se 1 (by rfl) ⟨1119632, by rfl⟩ : syracuseStep 1492843 = 2239265) B2239265
theorem B1329071 : Blo 884570 1329071 := bstep (se 1 (by rfl) ⟨996803, by rfl⟩ : syracuseStep 1329071 = 1993607) B1993607
theorem B2246575 : Blo 884570 2246575 := bstep (se 1 (by rfl) ⟨1684931, by rfl⟩ : syracuseStep 2246575 = 3369863) B3369863
theorem B6473657 : Blo 884570 6473657 := bstep (se 2 (by rfl) ⟨2427621, by rfl⟩ : syracuseStep 6473657 = 4855243) B4855243
theorem B1329161 : Blo 884570 1329161 := bstep (se 2 (by rfl) ⟨498435, by rfl⟩ : syracuseStep 1329161 = 996871) B996871
theorem B109332503 : Blo 884570 109332503 := bstep (se 1 (by rfl) ⟨81999377, by rfl⟩ : syracuseStep 109332503 = 163998755) B163998755
theorem B1329191 : Blo 884570 1329191 := bstep (se 1 (by rfl) ⟨996893, by rfl⟩ : syracuseStep 1329191 = 1993787) B1993787
theorem B1329275 : Blo 884570 1329275 := bstep (se 1 (by rfl) ⟨996956, by rfl⟩ : syracuseStep 1329275 = 1993913) B1993913
theorem B1067131 : Blo 884570 1067131 := bstep (se 1 (by rfl) ⟨800348, by rfl⟩ : syracuseStep 1067131 = 1600697) B1600697
theorem B1329401 : Blo 884570 1329401 := bstep (se 2 (by rfl) ⟨498525, by rfl⟩ : syracuseStep 1329401 = 997051) B997051
theorem B3361085 : Blo 884570 3361085 := bstep (se 3 (by rfl) ⟨630203, by rfl⟩ : syracuseStep 3361085 = 1260407) B1260407
theorem B1329503 : Blo 884570 1329503 := bstep (se 1 (by rfl) ⟨997127, by rfl⟩ : syracuseStep 1329503 = 1994255) B1994255
theorem B1329515 : Blo 884570 1329515 := bstep (se 1 (by rfl) ⟨997136, by rfl⟩ : syracuseStep 1329515 = 1994273) B1994273
theorem B2247041 : Blo 884570 2247041 := bstep (se 2 (by rfl) ⟨842640, by rfl⟩ : syracuseStep 2247041 = 1685281) B1685281
theorem B10242541 : Blo 884570 10242541 := bstep (se 3 (by rfl) ⟨1920476, by rfl⟩ : syracuseStep 10242541 = 3840953) B3840953
theorem B1329743 : Blo 884570 1329743 := bstep (se 1 (by rfl) ⟨997307, by rfl⟩ : syracuseStep 1329743 = 1994615) B1994615
theorem B22727303 : Blo 884570 22727303 := bstep (se 1 (by rfl) ⟨17045477, by rfl⟩ : syracuseStep 22727303 = 34090955) B34090955
theorem B1329863 : Blo 884570 1329863 := bstep (se 1 (by rfl) ⟨997397, by rfl⟩ : syracuseStep 1329863 = 1994795) B1994795
theorem B2247497 : Blo 884570 2247497 := bstep (se 2 (by rfl) ⟨842811, by rfl⟩ : syracuseStep 2247497 = 1685623) B1685623
theorem B1330025 : Blo 884570 1330025 := bstep (se 2 (by rfl) ⟨498759, by rfl⟩ : syracuseStep 1330025 = 997519) B997519
theorem B1493903 : Blo 884570 1493903 := bstep (se 1 (by rfl) ⟨1120427, by rfl⟩ : syracuseStep 1493903 = 2240855) B2240855
theorem B25545617 : Blo 884570 25545617 := bstep (se 2 (by rfl) ⟨9579606, by rfl⟩ : syracuseStep 25545617 = 19159213) B19159213
theorem B1330103 : Blo 884570 1330103 := bstep (se 1 (by rfl) ⟨997577, by rfl⟩ : syracuseStep 1330103 = 1995155) B1995155
theorem B1330139 : Blo 884570 1330139 := bstep (se 1 (by rfl) ⟨997604, by rfl⟩ : syracuseStep 1330139 = 1995209) B1995209
theorem B3034169 : Blo 884570 3034169 := bstep (se 2 (by rfl) ⟨1137813, by rfl⟩ : syracuseStep 3034169 = 2275627) B2275627
theorem B1494139 : Blo 884570 1494139 := bstep (se 1 (by rfl) ⟨1120604, by rfl⟩ : syracuseStep 1494139 = 2241209) B2241209
theorem B2247851 : Blo 884570 2247851 := bstep (se 1 (by rfl) ⟨1685888, by rfl⟩ : syracuseStep 2247851 = 3371777) B3371777
theorem B1330607 : Blo 884570 1330607 := bstep (se 1 (by rfl) ⟨997955, by rfl⟩ : syracuseStep 1330607 = 1995911) B1995911
theorem B1330697 : Blo 884570 1330697 := bstep (se 2 (by rfl) ⟨499011, by rfl⟩ : syracuseStep 1330697 = 998023) B998023
theorem B1330727 : Blo 884570 1330727 := bstep (se 1 (by rfl) ⟨998045, by rfl⟩ : syracuseStep 1330727 = 1996091) B1996091
theorem B3591803 : Blo 884570 3591803 := bstep (se 1 (by rfl) ⟨2693852, by rfl⟩ : syracuseStep 3591803 = 5387705) B5387705
theorem B1330811 : Blo 884570 1330811 := bstep (se 1 (by rfl) ⟨998108, by rfl⟩ : syracuseStep 1330811 = 1996217) B1996217
theorem B1330937 : Blo 884570 1330937 := bstep (se 2 (by rfl) ⟨499101, by rfl⟩ : syracuseStep 1330937 = 998203) B998203
theorem B1331039 : Blo 884570 1331039 := bstep (se 1 (by rfl) ⟨998279, by rfl⟩ : syracuseStep 1331039 = 1996559) B1996559
theorem B1331051 : Blo 884570 1331051 := bstep (se 1 (by rfl) ⟨998288, by rfl⟩ : syracuseStep 1331051 = 1996577) B1996577
theorem B5689207 : Blo 884570 5689207 := bstep (se 1 (by rfl) ⟨4266905, by rfl⟩ : syracuseStep 5689207 = 8533811) B8533811
theorem B12930947 : Blo 884570 12930947 := bstep (se 1 (by rfl) ⟨9698210, by rfl⟩ : syracuseStep 12930947 = 19396421) B19396421
theorem B2248631 : Blo 884570 2248631 := bstep (se 1 (by rfl) ⟨1686473, by rfl⟩ : syracuseStep 2248631 = 3372947) B3372947
theorem B1495003 : Blo 884570 1495003 := bstep (se 1 (by rfl) ⟨1121252, by rfl⟩ : syracuseStep 1495003 = 2242505) B2242505
theorem B1331279 : Blo 884570 1331279 := bstep (se 1 (by rfl) ⟨998459, by rfl⟩ : syracuseStep 1331279 = 1996919) B1996919
theorem B2838685 : Blo 884570 2838685 := bstep (se 3 (by rfl) ⟨532253, by rfl⟩ : syracuseStep 2838685 = 1064507) B1064507
theorem B3199171 : Blo 884570 3199171 := bstep (se 1 (by rfl) ⟨2399378, by rfl⟩ : syracuseStep 3199171 = 4798757) B4798757
theorem B1331399 : Blo 884570 1331399 := bstep (se 1 (by rfl) ⟨998549, by rfl⟩ : syracuseStep 1331399 = 1997099) B1997099
theorem B1331561 : Blo 884570 1331561 := bstep (se 2 (by rfl) ⟨499335, by rfl⟩ : syracuseStep 1331561 = 998671) B998671
theorem B1331639 : Blo 884570 1331639 := bstep (se 1 (by rfl) ⟨998729, by rfl⟩ : syracuseStep 1331639 = 1997459) B1997459
theorem B1331675 : Blo 884570 1331675 := bstep (se 1 (by rfl) ⟨998756, by rfl⟩ : syracuseStep 1331675 = 1997513) B1997513
theorem B971303 : Blo 884570 971303 := bstep (se 1 (by rfl) ⟨728477, by rfl⟩ : syracuseStep 971303 = 1456955) B1456955
theorem B1495631 : Blo 884570 1495631 := bstep (se 1 (by rfl) ⟨1121723, by rfl⟩ : syracuseStep 1495631 = 2243447) B2243447
theorem B1332143 : Blo 884570 1332143 := bstep (se 1 (by rfl) ⟨999107, by rfl⟩ : syracuseStep 1332143 = 1998215) B1998215
theorem B1332233 : Blo 884570 1332233 := bstep (se 2 (by rfl) ⟨499587, by rfl⟩ : syracuseStep 1332233 = 999175) B999175
theorem B1332263 : Blo 884570 1332263 := bstep (se 1 (by rfl) ⟨999197, by rfl⟩ : syracuseStep 1332263 = 1998395) B1998395
theorem B1332347 : Blo 884570 1332347 := bstep (se 1 (by rfl) ⟨999260, by rfl⟩ : syracuseStep 1332347 = 1998521) B1998521
theorem B1332473 : Blo 884570 1332473 := bstep (se 2 (by rfl) ⟨499677, by rfl⟩ : syracuseStep 1332473 = 999355) B999355
theorem B1332575 : Blo 884570 1332575 := bstep (se 1 (by rfl) ⟨999431, by rfl⟩ : syracuseStep 1332575 = 1998863) B1998863
theorem B1332587 : Blo 884570 1332587 := bstep (se 1 (by rfl) ⟨999440, by rfl⟩ : syracuseStep 1332587 = 1998881) B1998881
theorem B1496495 : Blo 884570 1496495 := bstep (se 1 (by rfl) ⟨1122371, by rfl⟩ : syracuseStep 1496495 = 2244743) B2244743
theorem B7296551 : Blo 884570 7296551 := bstep (se 1 (by rfl) ⟨5472413, by rfl⟩ : syracuseStep 7296551 = 10944827) B10944827
theorem B1332815 : Blo 884570 1332815 := bstep (se 1 (by rfl) ⟨999611, by rfl⟩ : syracuseStep 1332815 = 1999223) B1999223
theorem B3364487 : Blo 884570 3364487 := bstep (se 1 (by rfl) ⟨2523365, by rfl⟩ : syracuseStep 3364487 = 5046731) B5046731
theorem B1496927 : Blo 884570 1496927 := bstep (se 1 (by rfl) ⟨1122695, by rfl⟩ : syracuseStep 1496927 = 2245391) B2245391
theorem B3594091 : Blo 884570 3594091 := bstep (se 1 (by rfl) ⟨2695568, by rfl⟩ : syracuseStep 3594091 = 5391137) B5391137
theorem B6739847 : Blo 884570 6739847 := bstep (se 1 (by rfl) ⟨5054885, by rfl⟩ : syracuseStep 6739847 = 10109771) B10109771
theorem B2840503 : Blo 884570 2840503 := bstep (se 1 (by rfl) ⟨2130377, by rfl⟩ : syracuseStep 2840503 = 4260755) B4260755
theorem B2840633 : Blo 884570 2840633 := bstep (se 2 (by rfl) ⟨1065237, by rfl⟩ : syracuseStep 2840633 = 2130475) B2130475
theorem B1497487 : Blo 884570 1497487 := bstep (se 1 (by rfl) ⟨1123115, by rfl⟩ : syracuseStep 1497487 = 2246231) B2246231
theorem B1825319 : Blo 884570 1825319 := bstep (se 1 (by rfl) ⟨1368989, by rfl⟩ : syracuseStep 1825319 = 2737979) B2737979
theorem B4479623 : Blo 884570 4479623 := bstep (se 1 (by rfl) ⟨3359717, by rfl⟩ : syracuseStep 4479623 = 6719435) B6719435
theorem B4315907 : Blo 884570 4315907 := bstep (se 1 (by rfl) ⟨3236930, by rfl⟩ : syracuseStep 4315907 = 6473861) B6473861
theorem B8510285 : Blo 884570 8510285 := bstep (se 3 (by rfl) ⟨1595678, by rfl⟩ : syracuseStep 8510285 = 3191357) B3191357
theorem B8510437 : Blo 884570 8510437 := bstep (se 4 (by rfl) ⟨797853, by rfl⟩ : syracuseStep 8510437 = 1595707) B1595707
theorem B3365945 : Blo 884570 3365945 := bstep (se 2 (by rfl) ⟨1262229, by rfl⟩ : syracuseStep 3365945 = 2524459) B2524459
theorem B1498169 : Blo 884570 1498169 := bstep (se 2 (by rfl) ⟨561813, by rfl⟩ : syracuseStep 1498169 = 1123627) B1123627
theorem B3202429 : Blo 884570 3202429 := bstep (se 3 (by rfl) ⟨600455, by rfl⟩ : syracuseStep 3202429 = 1200911) B1200911
theorem B2842235 : Blo 884570 2842235 := bstep (se 1 (by rfl) ⟨2131676, by rfl⟩ : syracuseStep 2842235 = 4263353) B4263353
theorem B1498871 : Blo 884570 1498871 := bstep (se 1 (by rfl) ⟨1124153, by rfl⟩ : syracuseStep 1498871 = 2248307) B2248307
theorem B1892089 : Blo 884570 1892089 := bstep (se 2 (by rfl) ⟨709533, by rfl⟩ : syracuseStep 1892089 = 1419067) B1419067
theorem B10772291 : Blo 884570 10772291 := bstep (se 1 (by rfl) ⟨8079218, by rfl⟩ : syracuseStep 10772291 = 16158437) B16158437
theorem B1990583 : Blo 884570 1990583 := bstep (se 1 (by rfl) ⟨1492937, by rfl⟩ : syracuseStep 1990583 = 2985875) B2985875
theorem B4481081 : Blo 884570 4481081 := bstep (se 2 (by rfl) ⟨1680405, by rfl⟩ : syracuseStep 4481081 = 3360811) B3360811
theorem B1499215 : Blo 884570 1499215 := bstep (se 1 (by rfl) ⟨1124411, by rfl⟩ : syracuseStep 1499215 = 2248823) B2248823
theorem B3792977 : Blo 884570 3792977 := bstep (se 2 (by rfl) ⟨1422366, by rfl⟩ : syracuseStep 3792977 = 2844733) B2844733
theorem B1991177 : Blo 884570 1991177 := bstep (se 2 (by rfl) ⟨746691, by rfl⟩ : syracuseStep 1991177 = 1493383) B1493383
theorem B3367433 : Blo 884570 3367433 := bstep (se 2 (by rfl) ⟨1262787, by rfl⟩ : syracuseStep 3367433 = 2525575) B2525575
theorem B7201313 : Blo 884570 7201313 := bstep (se 2 (by rfl) ⟨2700492, by rfl⟩ : syracuseStep 7201313 = 5400985) B5400985
theorem B2024185 : Blo 884570 2024185 := bstep (se 2 (by rfl) ⟨759069, by rfl⟩ : syracuseStep 2024185 = 1518139) B1518139
theorem B1991519 : Blo 884570 1991519 := bstep (se 1 (by rfl) ⟨1493639, by rfl⟩ : syracuseStep 1991519 = 2987279) B2987279
theorem B1794911 : Blo 884570 1794911 := bstep (se 1 (by rfl) ⟨1346183, by rfl⟩ : syracuseStep 1794911 = 2692367) B2692367
theorem B1794977 : Blo 884570 1794977 := bstep (se 2 (by rfl) ⟨673116, by rfl⟩ : syracuseStep 1794977 = 1346233) B1346233
theorem B2843579 : Blo 884570 2843579 := bstep (se 1 (by rfl) ⟨2132684, by rfl⟩ : syracuseStep 2843579 = 4265369) B4265369
theorem B1991699 : Blo 884570 1991699 := bstep (se 1 (by rfl) ⟨1493774, by rfl⟩ : syracuseStep 1991699 = 2987549) B2987549
theorem B1598663 : Blo 884570 1598663 := bstep (se 1 (by rfl) ⟨1198997, by rfl⟩ : syracuseStep 1598663 = 2397995) B2397995
theorem B1992041 : Blo 884570 1992041 := bstep (se 2 (by rfl) ⟨747015, by rfl⟩ : syracuseStep 1992041 = 1494031) B1494031
theorem B1893737 : Blo 884570 1893737 := bstep (se 2 (by rfl) ⟨710151, by rfl⟩ : syracuseStep 1893737 = 1420303) B1420303
theorem B3794377 : Blo 884570 3794377 := bstep (se 2 (by rfl) ⟨1422891, by rfl⟩ : syracuseStep 3794377 = 2845783) B2845783
theorem B3368587 : Blo 884570 3368587 := bstep (se 1 (by rfl) ⟨2526440, by rfl⟩ : syracuseStep 3368587 = 5052881) B5052881
theorem B5400209 : Blo 884570 5400209 := bstep (se 2 (by rfl) ⟨2025078, by rfl⟩ : syracuseStep 5400209 = 4050157) B4050157
theorem B8513171 : Blo 884570 8513171 := bstep (se 1 (by rfl) ⟨6384878, by rfl⟩ : syracuseStep 8513171 = 12769757) B12769757
theorem B1796015 : Blo 884570 1796015 := bstep (se 1 (by rfl) ⟨1347011, by rfl⟩ : syracuseStep 1796015 = 2694023) B2694023
theorem B1992635 : Blo 884570 1992635 := bstep (se 1 (by rfl) ⟨1494476, by rfl⟩ : syracuseStep 1992635 = 2988953) B2988953
theorem B3368891 : Blo 884570 3368891 := bstep (se 1 (by rfl) ⟨2526668, by rfl⟩ : syracuseStep 3368891 = 5053337) B5053337
theorem B1992761 : Blo 884570 1992761 := bstep (se 2 (by rfl) ⟨747285, by rfl⟩ : syracuseStep 1992761 = 1494571) B1494571
theorem B4483187 : Blo 884570 4483187 := bstep (se 1 (by rfl) ⟨3362390, by rfl⟩ : syracuseStep 4483187 = 6724781) B6724781
theorem B6744221 : Blo 884570 6744221 := bstep (se 3 (by rfl) ⟨1264541, by rfl⟩ : syracuseStep 6744221 = 2529083) B2529083
theorem B1993103 : Blo 884570 1993103 := bstep (se 1 (by rfl) ⟨1494827, by rfl⟩ : syracuseStep 1993103 = 2989655) B2989655
theorem B3795437 : Blo 884570 3795437 := bstep (se 3 (by rfl) ⟨711644, by rfl⟩ : syracuseStep 3795437 = 1423289) B1423289
theorem B1993427 : Blo 884570 1993427 := bstep (se 1 (by rfl) ⟨1495070, by rfl⟩ : syracuseStep 1993427 = 2990141) B2990141
theorem B5040899 : Blo 884570 5040899 := bstep (se 1 (by rfl) ⟨3780674, by rfl⟩ : syracuseStep 5040899 = 7561349) B7561349
theorem B1895275 : Blo 884570 1895275 := bstep (se 1 (by rfl) ⟨1421456, by rfl⟩ : syracuseStep 1895275 = 2842913) B2842913
theorem B1600609 : Blo 884570 1600609 := bstep (se 2 (by rfl) ⟨600228, by rfl⟩ : syracuseStep 1600609 = 1200457) B1200457
theorem B5041399 : Blo 884570 5041399 := bstep (se 1 (by rfl) ⟨3781049, by rfl⟩ : syracuseStep 5041399 = 7562099) B7562099
theorem B945703 : Blo 884570 945703 := bstep (se 1 (by rfl) ⟨709277, by rfl⟩ : syracuseStep 945703 = 1418555) B1418555
theorem B4255355 : Blo 884570 4255355 := bstep (se 1 (by rfl) ⟨3191516, by rfl⟩ : syracuseStep 4255355 = 6383033) B6383033
theorem B1994363 : Blo 884570 1994363 := bstep (se 1 (by rfl) ⟨1495772, by rfl⟩ : syracuseStep 1994363 = 2991545) B2991545
theorem B4484807 : Blo 884570 4484807 := bstep (se 1 (by rfl) ⟨3363605, by rfl⟩ : syracuseStep 4484807 = 6727211) B6727211
theorem B1994489 : Blo 884570 1994489 := bstep (se 2 (by rfl) ⟨747933, by rfl⟩ : syracuseStep 1994489 = 1495867) B1495867
theorem B1994759 : Blo 884570 1994759 := bstep (se 1 (by rfl) ⟨1496069, by rfl⟩ : syracuseStep 1994759 = 2992139) B2992139
theorem B5402639 : Blo 884570 5402639 := bstep (se 1 (by rfl) ⟨4051979, by rfl⟩ : syracuseStep 5402639 = 8103959) B8103959
theorem B1994831 : Blo 884570 1994831 := bstep (se 1 (by rfl) ⟨1496123, by rfl⟩ : syracuseStep 1994831 = 2992247) B2992247
theorem B3600463 : Blo 884570 3600463 := bstep (se 1 (by rfl) ⟨2700347, by rfl⟩ : syracuseStep 3600463 = 5400695) B5400695
theorem B2519515 : Blo 884570 2519515 := bstep (se 1 (by rfl) ⟨1889636, by rfl⟩ : syracuseStep 2519515 = 3779273) B3779273
theorem B1995227 : Blo 884570 1995227 := bstep (se 1 (by rfl) ⟨1496420, by rfl⟩ : syracuseStep 1995227 = 2992841) B2992841
theorem B2519561 : Blo 884570 2519561 := bstep (se 2 (by rfl) ⟨944835, by rfl⟩ : syracuseStep 2519561 = 1889671) B1889671
theorem B44331587 : Blo 884570 44331587 := bstep (se 1 (by rfl) ⟨33248690, by rfl⟩ : syracuseStep 44331587 = 66497381) B66497381
theorem B2519903 : Blo 884570 2519903 := bstep (se 1 (by rfl) ⟨1889927, by rfl⟩ : syracuseStep 2519903 = 3779855) B3779855
theorem B1995695 : Blo 884570 1995695 := bstep (se 1 (by rfl) ⟨1496771, by rfl⟩ : syracuseStep 1995695 = 2993543) B2993543
theorem B6747137 : Blo 884570 6747137 := bstep (se 2 (by rfl) ⟨2530176, by rfl⟩ : syracuseStep 6747137 = 5060353) B5060353
theorem B2520143 : Blo 884570 2520143 := bstep (se 1 (by rfl) ⟨1890107, by rfl⟩ : syracuseStep 2520143 = 3780215) B3780215
theorem B1995947 : Blo 884570 1995947 := bstep (se 1 (by rfl) ⟨1496960, by rfl⟩ : syracuseStep 1995947 = 2993921) B2993921
theorem B1996487 : Blo 884570 1996487 := bstep (se 1 (by rfl) ⟨1497365, by rfl⟩ : syracuseStep 1996487 = 2994731) B2994731
theorem B947911 : Blo 884570 947911 := bstep (se 1 (by rfl) ⟨710933, by rfl⟩ : syracuseStep 947911 = 1421867) B1421867
theorem B2520791 : Blo 884570 2520791 := bstep (se 1 (by rfl) ⟨1890593, by rfl⟩ : syracuseStep 2520791 = 3781187) B3781187
theorem B9729953 : Blo 884570 9729953 := bstep (se 2 (by rfl) ⟨3648732, by rfl⟩ : syracuseStep 9729953 = 7297465) B7297465
theorem B3372961 : Blo 884570 3372961 := bstep (se 2 (by rfl) ⟨1264860, by rfl⟩ : syracuseStep 3372961 = 2529721) B2529721
theorem B2521019 : Blo 884570 2521019 := bstep (se 1 (by rfl) ⟨1890764, by rfl⟩ : syracuseStep 2521019 = 3781529) B3781529
theorem B12777425 : Blo 884570 12777425 := bstep (se 2 (by rfl) ⟨4791534, by rfl⟩ : syracuseStep 12777425 = 9583069) B9583069
theorem B2521145 : Blo 884570 2521145 := bstep (se 2 (by rfl) ⟨945429, by rfl⟩ : syracuseStep 2521145 = 1890859) B1890859
theorem B9107761 : Blo 884570 9107761 := bstep (se 2 (by rfl) ⟨3415410, by rfl⟩ : syracuseStep 9107761 = 6830821) B6830821
theorem B1997351 : Blo 884570 1997351 := bstep (se 1 (by rfl) ⟨1498013, by rfl⟩ : syracuseStep 1997351 = 2996027) B2996027
theorem B14383817 : Blo 884570 14383817 := bstep (se 2 (by rfl) ⟨5393931, by rfl⟩ : syracuseStep 14383817 = 10787863) B10787863
theorem B1997675 : Blo 884570 1997675 := bstep (se 1 (by rfl) ⟨1498256, by rfl⟩ : syracuseStep 1997675 = 2996513) B2996513
theorem B1997729 : Blo 884570 1997729 := bstep (se 2 (by rfl) ⟨749148, by rfl⟩ : syracuseStep 1997729 = 1498297) B1498297
theorem B1998071 : Blo 884570 1998071 := bstep (se 1 (by rfl) ⟨1498553, by rfl⟩ : syracuseStep 1998071 = 2997107) B2997107
theorem B6389117 : Blo 884570 6389117 := bstep (se 3 (by rfl) ⟨1197959, by rfl⟩ : syracuseStep 6389117 = 2395919) B2395919
theorem B2129417 : Blo 884570 2129417 := bstep (se 2 (by rfl) ⟨798531, by rfl⟩ : syracuseStep 2129417 = 1597063) B1597063
theorem B8519357 : Blo 884570 8519357 := bstep (se 3 (by rfl) ⟨1597379, by rfl⟩ : syracuseStep 8519357 = 3194759) B3194759
theorem B1998665 : Blo 884570 1998665 := bstep (se 2 (by rfl) ⟨749499, by rfl⟩ : syracuseStep 1998665 = 1498999) B1498999
theorem B884575 : Blo 884570 884575 := bstep (se 1 (by rfl) ⟨663431, by rfl⟩ : syracuseStep 884575 = 1326863) B1326863
theorem B884603 : Blo 884570 884603 := bstep (se 1 (by rfl) ⟨663452, by rfl⟩ : syracuseStep 884603 = 1326905) B1326905
theorem B884655 : Blo 884570 884655 := bstep (se 1 (by rfl) ⟨663491, by rfl⟩ : syracuseStep 884655 = 1326983) B1326983
theorem B3243959 : Blo 884570 3243959 := bstep (se 1 (by rfl) ⟨2432969, by rfl⟩ : syracuseStep 3243959 = 4865939) B4865939
theorem B884679 : Blo 884570 884679 := bstep (se 1 (by rfl) ⟨663509, by rfl⟩ : syracuseStep 884679 = 1327019) B1327019
theorem B884699 : Blo 884570 884699 := bstep (se 1 (by rfl) ⟨663524, by rfl⟩ : syracuseStep 884699 = 1327049) B1327049
theorem B1277915 : Blo 884570 1277915 := bstep (se 1 (by rfl) ⟨958436, by rfl⟩ : syracuseStep 1277915 = 1916873) B1916873
theorem B6717491 : Blo 884570 6717491 := bstep (se 1 (by rfl) ⟨5038118, by rfl⟩ : syracuseStep 6717491 = 10076237) B10076237
theorem B1998953 : Blo 884570 1998953 := bstep (se 2 (by rfl) ⟨749607, by rfl⟩ : syracuseStep 1998953 = 1499215) B1499215
theorem B885023 : Blo 884570 885023 := bstep (se 1 (by rfl) ⟨663767, by rfl⟩ : syracuseStep 885023 = 1327535) B1327535
theorem B885083 : Blo 884570 885083 := bstep (se 1 (by rfl) ⟨663812, by rfl⟩ : syracuseStep 885083 = 1327625) B1327625
theorem B885103 : Blo 884570 885103 := bstep (se 1 (by rfl) ⟨663827, by rfl⟩ : syracuseStep 885103 = 1327655) B1327655
theorem B885159 : Blo 884570 885159 := bstep (se 1 (by rfl) ⟨663869, by rfl⟩ : syracuseStep 885159 = 1327739) B1327739
theorem B885243 : Blo 884570 885243 := bstep (se 1 (by rfl) ⟨663932, by rfl⟩ : syracuseStep 885243 = 1327865) B1327865
theorem B885311 : Blo 884570 885311 := bstep (se 1 (by rfl) ⟨663983, by rfl⟩ : syracuseStep 885311 = 1327967) B1327967
theorem B885319 : Blo 884570 885319 := bstep (se 1 (by rfl) ⟨663989, by rfl⟩ : syracuseStep 885319 = 1327979) B1327979
theorem B885471 : Blo 884570 885471 := bstep (se 1 (by rfl) ⟨664103, by rfl⟩ : syracuseStep 885471 = 1328207) B1328207
theorem B6390521 : Blo 884570 6390521 := bstep (se 2 (by rfl) ⟨2396445, by rfl⟩ : syracuseStep 6390521 = 4792891) B4792891
theorem B885551 : Blo 884570 885551 := bstep (se 1 (by rfl) ⟨664163, by rfl⟩ : syracuseStep 885551 = 1328327) B1328327
theorem B885659 : Blo 884570 885659 := bstep (se 1 (by rfl) ⟨664244, by rfl⟩ : syracuseStep 885659 = 1328489) B1328489
theorem B885711 : Blo 884570 885711 := bstep (se 1 (by rfl) ⟨664283, by rfl⟩ : syracuseStep 885711 = 1328567) B1328567
theorem B885735 : Blo 884570 885735 := bstep (se 1 (by rfl) ⟨664301, by rfl⟩ : syracuseStep 885735 = 1328603) B1328603
theorem B2163809 : Blo 884570 2163809 := bstep (se 2 (by rfl) ⟨811428, by rfl⟩ : syracuseStep 2163809 = 1622857) B1622857
theorem B3409129 : Blo 884570 3409129 := bstep (se 2 (by rfl) ⟨1278423, by rfl⟩ : syracuseStep 3409129 = 2556847) B2556847
theorem B886047 : Blo 884570 886047 := bstep (se 1 (by rfl) ⟨664535, by rfl⟩ : syracuseStep 886047 = 1329071) B1329071
theorem B886107 : Blo 884570 886107 := bstep (se 1 (by rfl) ⟨664580, by rfl⟩ : syracuseStep 886107 = 1329161) B1329161
theorem B886127 : Blo 884570 886127 := bstep (se 1 (by rfl) ⟨664595, by rfl⟩ : syracuseStep 886127 = 1329191) B1329191
theorem B886183 : Blo 884570 886183 := bstep (se 1 (by rfl) ⟨664637, by rfl⟩ : syracuseStep 886183 = 1329275) B1329275
theorem B2590141 : Blo 884570 2590141 := bstep (se 3 (by rfl) ⟨485651, by rfl⟩ : syracuseStep 2590141 = 971303) B971303
theorem B886267 : Blo 884570 886267 := bstep (se 1 (by rfl) ⟨664700, by rfl⟩ : syracuseStep 886267 = 1329401) B1329401
theorem B886335 : Blo 884570 886335 := bstep (se 1 (by rfl) ⟨664751, by rfl⟩ : syracuseStep 886335 = 1329503) B1329503
theorem B886343 : Blo 884570 886343 := bstep (se 1 (by rfl) ⟨664757, by rfl⟩ : syracuseStep 886343 = 1329515) B1329515
theorem B886495 : Blo 884570 886495 := bstep (se 1 (by rfl) ⟨664871, by rfl⟩ : syracuseStep 886495 = 1329743) B1329743
theorem B1705735 : Blo 884570 1705735 := bstep (se 1 (by rfl) ⟨1279301, by rfl⟩ : syracuseStep 1705735 = 2558603) B2558603
theorem B886575 : Blo 884570 886575 := bstep (se 1 (by rfl) ⟨664931, by rfl⟩ : syracuseStep 886575 = 1329863) B1329863
theorem B886683 : Blo 884570 886683 := bstep (se 1 (by rfl) ⟨665012, by rfl⟩ : syracuseStep 886683 = 1330025) B1330025
theorem B886735 : Blo 884570 886735 := bstep (se 1 (by rfl) ⟨665051, by rfl⟩ : syracuseStep 886735 = 1330103) B1330103
theorem B886759 : Blo 884570 886759 := bstep (se 1 (by rfl) ⟨665069, by rfl⟩ : syracuseStep 886759 = 1330139) B1330139
theorem B17303537 : Blo 884570 17303537 := bstep (se 2 (by rfl) ⟨6488826, by rfl⟩ : syracuseStep 17303537 = 12977653) B12977653
theorem B4491449 : Blo 884570 4491449 := bstep (se 2 (by rfl) ⟨1684293, by rfl⟩ : syracuseStep 4491449 = 3368587) B3368587
theorem B887071 : Blo 884570 887071 := bstep (se 1 (by rfl) ⟨665303, by rfl⟩ : syracuseStep 887071 = 1330607) B1330607
theorem B887131 : Blo 884570 887131 := bstep (se 1 (by rfl) ⟨665348, by rfl⟩ : syracuseStep 887131 = 1330697) B1330697
theorem B887151 : Blo 884570 887151 := bstep (se 1 (by rfl) ⟨665363, by rfl⟩ : syracuseStep 887151 = 1330727) B1330727
theorem B2394535 : Blo 884570 2394535 := bstep (se 1 (by rfl) ⟨1795901, by rfl⟩ : syracuseStep 2394535 = 3591803) B3591803
theorem B887207 : Blo 884570 887207 := bstep (se 1 (by rfl) ⟨665405, by rfl⟩ : syracuseStep 887207 = 1330811) B1330811
theorem B887291 : Blo 884570 887291 := bstep (se 1 (by rfl) ⟨665468, by rfl⟩ : syracuseStep 887291 = 1330937) B1330937
theorem B887359 : Blo 884570 887359 := bstep (se 1 (by rfl) ⟨665519, by rfl⟩ : syracuseStep 887359 = 1331039) B1331039
theorem B887367 : Blo 884570 887367 := bstep (se 1 (by rfl) ⟨665525, by rfl⟩ : syracuseStep 887367 = 1331051) B1331051
theorem B8620631 : Blo 884570 8620631 := bstep (se 1 (by rfl) ⟨6465473, by rfl⟩ : syracuseStep 8620631 = 12930947) B12930947
theorem B10095191 : Blo 884570 10095191 := bstep (se 1 (by rfl) ⟨7571393, by rfl⟩ : syracuseStep 10095191 = 15142787) B15142787
theorem B887519 : Blo 884570 887519 := bstep (se 1 (by rfl) ⟨665639, by rfl⟩ : syracuseStep 887519 = 1331279) B1331279
theorem B887599 : Blo 884570 887599 := bstep (se 1 (by rfl) ⟨665699, by rfl⟩ : syracuseStep 887599 = 1331399) B1331399
theorem B887707 : Blo 884570 887707 := bstep (se 1 (by rfl) ⟨665780, by rfl⟩ : syracuseStep 887707 = 1331561) B1331561
theorem B887759 : Blo 884570 887759 := bstep (se 1 (by rfl) ⟨665819, by rfl⟩ : syracuseStep 887759 = 1331639) B1331639
theorem B887783 : Blo 884570 887783 := bstep (se 1 (by rfl) ⟨665837, by rfl⟩ : syracuseStep 887783 = 1331675) B1331675
theorem B4263101 : Blo 884570 4263101 := bstep (se 3 (by rfl) ⟨799331, by rfl⟩ : syracuseStep 4263101 = 1598663) B1598663
theorem B888095 : Blo 884570 888095 := bstep (se 1 (by rfl) ⟨666071, by rfl⟩ : syracuseStep 888095 = 1332143) B1332143
theorem B888155 : Blo 884570 888155 := bstep (se 1 (by rfl) ⟨666116, by rfl⟩ : syracuseStep 888155 = 1332233) B1332233
theorem B888175 : Blo 884570 888175 := bstep (se 1 (by rfl) ⟨666131, by rfl⟩ : syracuseStep 888175 = 1332263) B1332263
theorem B888231 : Blo 884570 888231 := bstep (se 1 (by rfl) ⟨666173, by rfl⟩ : syracuseStep 888231 = 1332347) B1332347
theorem B888315 : Blo 884570 888315 := bstep (se 1 (by rfl) ⟨666236, by rfl⟩ : syracuseStep 888315 = 1332473) B1332473
theorem B888383 : Blo 884570 888383 := bstep (se 1 (by rfl) ⟨666287, by rfl⟩ : syracuseStep 888383 = 1332575) B1332575
theorem B888391 : Blo 884570 888391 := bstep (se 1 (by rfl) ⟨666293, by rfl⟩ : syracuseStep 888391 = 1332587) B1332587
theorem B5049965 : Blo 884570 5049965 := bstep (se 3 (by rfl) ⟨946868, by rfl⟩ : syracuseStep 5049965 = 1893737) B1893737
theorem B888543 : Blo 884570 888543 := bstep (se 1 (by rfl) ⟨666407, by rfl⟩ : syracuseStep 888543 = 1332815) B1332815
theorem B2527033 : Blo 884570 2527033 := bstep (se 2 (by rfl) ⟨947637, by rfl⟩ : syracuseStep 2527033 = 1895275) B1895275
theorem B8523629 : Blo 884570 8523629 := bstep (se 3 (by rfl) ⟨1598180, by rfl⟩ : syracuseStep 8523629 = 3196361) B3196361
theorem B4493231 : Blo 884570 4493231 := bstep (se 1 (by rfl) ⟨3369923, by rfl⟩ : syracuseStep 4493231 = 6739847) B6739847
theorem B2134145 : Blo 884570 2134145 := bstep (se 2 (by rfl) ⟨800304, by rfl⟩ : syracuseStep 2134145 = 1600609) B1600609
theorem B4427929 : Blo 884570 4427929 := bstep (se 2 (by rfl) ⟨1660473, by rfl⟩ : syracuseStep 4427929 = 3320947) B3320947
theorem B17240323 : Blo 884570 17240323 := bstep (se 1 (by rfl) ⟨12930242, by rfl⟩ : syracuseStep 17240323 = 25860485) B25860485
theorem B6721865 : Blo 884570 6721865 := bstep (se 2 (by rfl) ⟨2520699, by rfl⟩ : syracuseStep 6721865 = 5041399) B5041399
theorem B1216879 : Blo 884570 1216879 := bstep (se 1 (by rfl) ⟨912659, by rfl⟩ : syracuseStep 1216879 = 1825319) B1825319
theorem B2986415 : Blo 884570 2986415 := bstep (se 1 (by rfl) ⟨2239811, by rfl⟩ : syracuseStep 2986415 = 4479623) B4479623
theorem B1708499 : Blo 884570 1708499 := bstep (se 1 (by rfl) ⟨1281374, by rfl⟩ : syracuseStep 1708499 = 2562749) B2562749
theorem B5673523 : Blo 884570 5673523 := bstep (se 1 (by rfl) ⟨4255142, by rfl⟩ : syracuseStep 5673523 = 8510285) B8510285
theorem B14389913 : Blo 884570 14389913 := bstep (se 2 (by rfl) ⟨5396217, by rfl⟩ : syracuseStep 14389913 = 10792435) B10792435
theorem B8525047 : Blo 884570 8525047 := bstep (se 1 (by rfl) ⟨6393785, by rfl⟩ : syracuseStep 8525047 = 12787571) B12787571
theorem B2987387 : Blo 884570 2987387 := bstep (se 1 (by rfl) ⟨2240540, by rfl⟩ : syracuseStep 2987387 = 4481081) B4481081
theorem B2528651 : Blo 884570 2528651 := bstep (se 1 (by rfl) ⟨1896488, by rfl⟩ : syracuseStep 2528651 = 3792977) B3792977
theorem B1119739 : Blo 884570 1119739 := bstep (se 1 (by rfl) ⟨839804, by rfl⟩ : syracuseStep 1119739 = 1679609) B1679609
theorem B4265561 : Blo 884570 4265561 := bstep (se 2 (by rfl) ⟨1599585, by rfl⟩ : syracuseStep 4265561 = 3199171) B3199171
theorem B5675447 : Blo 884570 5675447 := bstep (se 1 (by rfl) ⟨4256585, by rfl⟩ : syracuseStep 5675447 = 8513171) B8513171
theorem B1120711 : Blo 884570 1120711 := bstep (se 1 (by rfl) ⟨840533, by rfl⟩ : syracuseStep 1120711 = 1681067) B1681067
theorem B2988791 : Blo 884570 2988791 := bstep (se 1 (by rfl) ⟨2241593, by rfl⟩ : syracuseStep 2988791 = 4483187) B4483187
theorem B4496147 : Blo 884570 4496147 := bstep (se 1 (by rfl) ⟨3372110, by rfl⟩ : syracuseStep 4496147 = 6744221) B6744221
theorem B36936485 : Blo 884570 36936485 := bstep (se 4 (by rfl) ⟨3462795, by rfl⟩ : syracuseStep 36936485 = 6925591) B6925591
theorem B2530291 : Blo 884570 2530291 := bstep (se 1 (by rfl) ⟨1897718, by rfl⟩ : syracuseStep 2530291 = 3795437) B3795437
theorem B1121627 : Blo 884570 1121627 := bstep (se 1 (by rfl) ⟨841220, by rfl⟩ : syracuseStep 1121627 = 1682441) B1682441
theorem B11509085 : Blo 884570 11509085 := bstep (se 3 (by rfl) ⟨2157953, by rfl⟩ : syracuseStep 11509085 = 4315907) B4315907
theorem B1514951 : Blo 884570 1514951 := bstep (se 1 (by rfl) ⟨1136213, by rfl⟩ : syracuseStep 1514951 = 2272427) B2272427
theorem B2989871 : Blo 884570 2989871 := bstep (se 1 (by rfl) ⟨2242403, by rfl⟩ : syracuseStep 2989871 = 4484807) B4484807
theorem B1122103 : Blo 884570 1122103 := bstep (se 1 (by rfl) ⟨841577, by rfl⟩ : syracuseStep 1122103 = 1683155) B1683155
theorem B4792121 : Blo 884570 4792121 := bstep (se 2 (by rfl) ⟨1797045, by rfl⟩ : syracuseStep 4792121 = 3594091) B3594091
theorem B4497281 : Blo 884570 4497281 := bstep (se 2 (by rfl) ⟨1686480, by rfl⟩ : syracuseStep 4497281 = 3372961) B3372961
theorem B2433235 : Blo 884570 2433235 := bstep (se 1 (by rfl) ⟨1824926, by rfl⟩ : syracuseStep 2433235 = 3649853) B3649853
theorem B1122599 : Blo 884570 1122599 := bstep (se 1 (by rfl) ⟨841949, by rfl⟩ : syracuseStep 1122599 = 1683899) B1683899
theorem B1679707 : Blo 884570 1679707 := bstep (se 1 (by rfl) ⟨1259780, by rfl⟩ : syracuseStep 1679707 = 2519561) B2519561
theorem B1679935 : Blo 884570 1679935 := bstep (se 1 (by rfl) ⟨1259951, by rfl⟩ : syracuseStep 1679935 = 2519903) B2519903
theorem B5055047 : Blo 884570 5055047 := bstep (se 1 (by rfl) ⟨3791285, by rfl⟩ : syracuseStep 5055047 = 7582571) B7582571
theorem B1122923 : Blo 884570 1122923 := bstep (se 1 (by rfl) ⟨842192, by rfl⟩ : syracuseStep 1122923 = 1684385) B1684385
theorem B4498091 : Blo 884570 4498091 := bstep (se 1 (by rfl) ⟨3373568, by rfl⟩ : syracuseStep 4498091 = 6747137) B6747137
theorem B1680095 : Blo 884570 1680095 := bstep (se 1 (by rfl) ⟨1260071, by rfl⟩ : syracuseStep 1680095 = 2520143) B2520143
theorem B1123303 : Blo 884570 1123303 := bstep (se 1 (by rfl) ⟨842477, by rfl⟩ : syracuseStep 1123303 = 1684955) B1684955
theorem B19145717 : Blo 884570 19145717 := bstep (se 5 (by rfl) ⟨897455, by rfl⟩ : syracuseStep 19145717 = 1794911) B1794911
theorem B1680527 : Blo 884570 1680527 := bstep (se 1 (by rfl) ⟨1260395, by rfl⟩ : syracuseStep 1680527 = 2520791) B2520791
theorem B1680679 : Blo 884570 1680679 := bstep (se 1 (by rfl) ⟨1260509, by rfl⟩ : syracuseStep 1680679 = 2521019) B2521019
theorem B11347249 : Blo 884570 11347249 := bstep (se 2 (by rfl) ⟨4255218, by rfl⟩ : syracuseStep 11347249 = 8510437) B8510437
theorem B1680763 : Blo 884570 1680763 := bstep (se 1 (by rfl) ⟨1260572, by rfl⟩ : syracuseStep 1680763 = 2521145) B2521145
theorem B11347613 : Blo 884570 11347613 := bstep (se 3 (by rfl) ⟨2127677, by rfl⟩ : syracuseStep 11347613 = 4255355) B4255355
theorem B4269905 : Blo 884570 4269905 := bstep (se 2 (by rfl) ⟨1601214, by rfl⟩ : syracuseStep 4269905 = 3202429) B3202429
theorem B2991977 : Blo 884570 2991977 := bstep (se 2 (by rfl) ⟨1121991, by rfl⟩ : syracuseStep 2991977 = 2243983) B2243983
theorem B2992409 : Blo 884570 2992409 := bstep (se 2 (by rfl) ⟨1122153, by rfl⟩ : syracuseStep 2992409 = 2244307) B2244307
theorem B1419611 : Blo 884570 1419611 := bstep (se 1 (by rfl) ⟨1064708, by rfl⟩ : syracuseStep 1419611 = 2129417) B2129417
theorem B5679571 : Blo 884570 5679571 := bstep (se 1 (by rfl) ⟨4259678, by rfl⟩ : syracuseStep 5679571 = 8519357) B8519357
theorem B32320079 : Blo 884570 32320079 := bstep (se 1 (by rfl) ⟨24240059, by rfl⟩ : syracuseStep 32320079 = 48480119) B48480119
theorem B5745431 : Blo 884570 5745431 := bstep (se 1 (by rfl) ⟨4309073, by rfl⟩ : syracuseStep 5745431 = 8618147) B8618147
theorem B6827123 : Blo 884570 6827123 := bstep (se 1 (by rfl) ⟨5120342, by rfl⟩ : syracuseStep 6827123 = 10240685) B10240685
theorem B2239721 : Blo 884570 2239721 := bstep (se 2 (by rfl) ⟨839895, by rfl⟩ : syracuseStep 2239721 = 1679791) B1679791
theorem B2239883 : Blo 884570 2239883 := bstep (se 1 (by rfl) ⟨1679912, by rfl⟩ : syracuseStep 2239883 = 3359825) B3359825
theorem B2240095 : Blo 884570 2240095 := bstep (se 1 (by rfl) ⟨1680071, by rfl⟩ : syracuseStep 2240095 = 3360143) B3360143
theorem B2993759 : Blo 884570 2993759 := bstep (se 1 (by rfl) ⟨2245319, by rfl⟩ : syracuseStep 2993759 = 4490639) B4490639
theorem B2698913 : Blo 884570 2698913 := bstep (se 2 (by rfl) ⟨1012092, by rfl⟩ : syracuseStep 2698913 = 2024185) B2024185
theorem B72888335 : Blo 884570 72888335 := bstep (se 1 (by rfl) ⟨54666251, by rfl⟩ : syracuseStep 72888335 = 109332503) B109332503
theorem B2240723 : Blo 884570 2240723 := bstep (se 1 (by rfl) ⟨1680542, by rfl⟩ : syracuseStep 2240723 = 3361085) B3361085
theorem B1683823 : Blo 884570 1683823 := bstep (se 1 (by rfl) ⟨1262867, by rfl⟩ : syracuseStep 1683823 = 2525735) B2525735
theorem B15151535 : Blo 884570 15151535 := bstep (se 1 (by rfl) ⟨11363651, by rfl⟩ : syracuseStep 15151535 = 22727303) B22727303
theorem B995935 : Blo 884570 995935 := bstep (se 1 (by rfl) ⟨746951, by rfl⟩ : syracuseStep 995935 = 1493903) B1493903
theorem B5059169 : Blo 884570 5059169 := bstep (se 2 (by rfl) ⟨1897188, by rfl⟩ : syracuseStep 5059169 = 3794377) B3794377
theorem B6075179 : Blo 884570 6075179 := bstep (se 1 (by rfl) ⟨4556384, by rfl⟩ : syracuseStep 6075179 = 9112769) B9112769
theorem B2995163 : Blo 884570 2995163 := bstep (se 1 (by rfl) ⟨2246372, by rfl⟩ : syracuseStep 2995163 = 4492745) B4492745
theorem B2995325 : Blo 884570 2995325 := bstep (se 3 (by rfl) ⟨561623, by rfl⟩ : syracuseStep 2995325 = 1123247) B1123247
theorem B2995433 : Blo 884570 2995433 := bstep (se 2 (by rfl) ⟨1123287, by rfl⟩ : syracuseStep 2995433 = 2246575) B2246575
theorem B1422623 : Blo 884570 1422623 := bstep (se 1 (by rfl) ⟨1066967, by rfl⟩ : syracuseStep 1422623 = 2133935) B2133935
theorem B2995595 : Blo 884570 2995595 := bstep (se 1 (by rfl) ⟨2246696, by rfl⟩ : syracuseStep 2995595 = 4493393) B4493393
theorem B1422841 : Blo 884570 1422841 := bstep (se 2 (by rfl) ⟨533565, by rfl⟩ : syracuseStep 1422841 = 1067131) B1067131
theorem B1619539 : Blo 884570 1619539 := bstep (se 1 (by rfl) ⟨1214654, by rfl⟩ : syracuseStep 1619539 = 2429309) B2429309
theorem B997087 : Blo 884570 997087 := bstep (se 1 (by rfl) ⟨747815, by rfl⟩ : syracuseStep 997087 = 1495631) B1495631
theorem B997663 : Blo 884570 997663 := bstep (se 1 (by rfl) ⟨748247, by rfl⟩ : syracuseStep 997663 = 1496495) B1496495
theorem B4864367 : Blo 884570 4864367 := bstep (se 1 (by rfl) ⟨3648275, by rfl⟩ : syracuseStep 4864367 = 7296551) B7296551
theorem B1685927 : Blo 884570 1685927 := bstep (se 1 (by rfl) ⟨1264445, by rfl⟩ : syracuseStep 1685927 = 2528891) B2528891
theorem B2242991 : Blo 884570 2242991 := bstep (se 1 (by rfl) ⟨1682243, by rfl⟩ : syracuseStep 2242991 = 3364487) B3364487
theorem B997951 : Blo 884570 997951 := bstep (se 1 (by rfl) ⟨748463, by rfl⟩ : syracuseStep 997951 = 1496927) B1496927
theorem B1686815 : Blo 884570 1686815 := bstep (se 1 (by rfl) ⟨1265111, by rfl⟩ : syracuseStep 1686815 = 2530223) B2530223
theorem B2243963 : Blo 884570 2243963 := bstep (se 1 (by rfl) ⟨1682972, by rfl⟩ : syracuseStep 2243963 = 3365945) B3365945
theorem B998779 : Blo 884570 998779 := bstep (se 1 (by rfl) ⟨749084, by rfl⟩ : syracuseStep 998779 = 1498169) B1498169
theorem B1260937 : Blo 884570 1260937 := bstep (se 2 (by rfl) ⟨472851, by rfl⟩ : syracuseStep 1260937 = 945703) B945703
theorem B2244257 : Blo 884570 2244257 := bstep (se 2 (by rfl) ⟨841596, by rfl⟩ : syracuseStep 2244257 = 1683193) B1683193
theorem B7585609 : Blo 884570 7585609 := bstep (se 2 (by rfl) ⟨2844603, by rfl⟩ : syracuseStep 7585609 = 5689207) B5689207
theorem B999247 : Blo 884570 999247 := bstep (se 1 (by rfl) ⟨749435, by rfl⟩ : syracuseStep 999247 = 1498871) B1498871
theorem B1327055 : Blo 884570 1327055 := bstep (se 1 (by rfl) ⟨995291, by rfl⟩ : syracuseStep 1327055 = 1990583) B1990583
theorem B4800617 : Blo 884570 4800617 := bstep (se 2 (by rfl) ⟨1800231, by rfl⟩ : syracuseStep 4800617 = 3600463) B3600463
theorem B3784913 : Blo 884570 3784913 := bstep (se 2 (by rfl) ⟨1419342, by rfl⟩ : syracuseStep 3784913 = 2838685) B2838685
theorem B1327451 : Blo 884570 1327451 := bstep (se 1 (by rfl) ⟨995588, by rfl⟩ : syracuseStep 1327451 = 1991177) B1991177
theorem B2244955 : Blo 884570 2244955 := bstep (se 1 (by rfl) ⟨1683716, by rfl⟩ : syracuseStep 2244955 = 3367433) B3367433
theorem B2998619 : Blo 884570 2998619 := bstep (se 1 (by rfl) ⟨2248964, by rfl⟩ : syracuseStep 2998619 = 4497929) B4497929
theorem B4800875 : Blo 884570 4800875 := bstep (se 1 (by rfl) ⟨3600656, by rfl⟩ : syracuseStep 4800875 = 7201313) B7201313
theorem B1327679 : Blo 884570 1327679 := bstep (se 1 (by rfl) ⟨995759, by rfl⟩ : syracuseStep 1327679 = 1991519) B1991519
theorem B3785287 : Blo 884570 3785287 := bstep (se 1 (by rfl) ⟨2838965, by rfl⟩ : syracuseStep 3785287 = 5677931) B5677931
theorem B1196651 : Blo 884570 1196651 := bstep (se 1 (by rfl) ⟨897488, by rfl⟩ : syracuseStep 1196651 = 1794977) B1794977
theorem B3359353 : Blo 884570 3359353 := bstep (se 2 (by rfl) ⟨1259757, by rfl⟩ : syracuseStep 3359353 = 2519515) B2519515
theorem B1327799 : Blo 884570 1327799 := bstep (se 1 (by rfl) ⟨995849, by rfl⟩ : syracuseStep 1327799 = 1991699) B1991699
theorem B1328027 : Blo 884570 1328027 := bstep (se 1 (by rfl) ⟨996020, by rfl⟩ : syracuseStep 1328027 = 1992041) B1992041
theorem B1197343 : Blo 884570 1197343 := bstep (se 1 (by rfl) ⟨898007, by rfl⟩ : syracuseStep 1197343 = 1796015) B1796015
theorem B1328423 : Blo 884570 1328423 := bstep (se 1 (by rfl) ⟨996317, by rfl⟩ : syracuseStep 1328423 = 1992635) B1992635
theorem B2245927 : Blo 884570 2245927 := bstep (se 1 (by rfl) ⟨1684445, by rfl⟩ : syracuseStep 2245927 = 3368891) B3368891
theorem B1328507 : Blo 884570 1328507 := bstep (se 1 (by rfl) ⟨996380, by rfl⟩ : syracuseStep 1328507 = 1992761) B1992761
theorem B1328633 : Blo 884570 1328633 := bstep (se 2 (by rfl) ⟨498237, by rfl⟩ : syracuseStep 1328633 = 996475) B996475
theorem B2246201 : Blo 884570 2246201 := bstep (se 2 (by rfl) ⟨842325, by rfl⟩ : syracuseStep 2246201 = 1684651) B1684651
theorem B1328735 : Blo 884570 1328735 := bstep (se 1 (by rfl) ⟨996551, by rfl⟩ : syracuseStep 1328735 = 1993103) B1993103
theorem B1492715 : Blo 884570 1492715 := bstep (se 1 (by rfl) ⟨1119536, by rfl⟩ : syracuseStep 1492715 = 2239073) B2239073
theorem B1328951 : Blo 884570 1328951 := bstep (se 1 (by rfl) ⟨996713, by rfl⟩ : syracuseStep 1328951 = 1993427) B1993427
theorem B3360599 : Blo 884570 3360599 := bstep (se 1 (by rfl) ⟨2520449, by rfl⟩ : syracuseStep 3360599 = 5040899) B5040899
theorem B414566423 : Blo 884570 414566423 := bstep (se 1 (by rfl) ⟨310924817, by rfl⟩ : syracuseStep 414566423 = 621849635) B621849635
theorem B1329257 : Blo 884570 1329257 := bstep (se 2 (by rfl) ⟨498471, by rfl⟩ : syracuseStep 1329257 = 996943) B996943
theorem B746768645 : Blo 884570 746768645 := bstep (se 4 (by rfl) ⟨70009560, by rfl⟩ : syracuseStep 746768645 = 140019121) B140019121
theorem B1263881 : Blo 884570 1263881 := bstep (se 2 (by rfl) ⟨473955, by rfl⟩ : syracuseStep 1263881 = 947911) B947911
theorem B1329575 : Blo 884570 1329575 := bstep (se 1 (by rfl) ⟨997181, by rfl⟩ : syracuseStep 1329575 = 1994363) B1994363
theorem B1329659 : Blo 884570 1329659 := bstep (se 1 (by rfl) ⟨997244, by rfl⟩ : syracuseStep 1329659 = 1994489) B1994489
theorem B3787337 : Blo 884570 3787337 := bstep (se 2 (by rfl) ⟨1420251, by rfl⟩ : syracuseStep 3787337 = 2840503) B2840503
theorem B1329785 : Blo 884570 1329785 := bstep (se 2 (by rfl) ⟨498669, by rfl⟩ : syracuseStep 1329785 = 997339) B997339
theorem B2017963 : Blo 884570 2017963 := bstep (se 1 (by rfl) ⟨1513472, by rfl⟩ : syracuseStep 2017963 = 3026945) B3026945
theorem B1329839 : Blo 884570 1329839 := bstep (se 1 (by rfl) ⟨997379, by rfl⟩ : syracuseStep 1329839 = 1994759) B1994759
theorem B1493687 : Blo 884570 1493687 := bstep (se 1 (by rfl) ⟨1120265, by rfl⟩ : syracuseStep 1493687 = 2240531) B2240531
theorem B1329887 : Blo 884570 1329887 := bstep (se 1 (by rfl) ⟨997415, by rfl⟩ : syracuseStep 1329887 = 1994831) B1994831
theorem B1330151 : Blo 884570 1330151 := bstep (se 1 (by rfl) ⟨997613, by rfl⟩ : syracuseStep 1330151 = 1995227) B1995227
theorem B12143681 : Blo 884570 12143681 := bstep (se 2 (by rfl) ⟨4553880, by rfl⟩ : syracuseStep 12143681 = 9107761) B9107761
theorem B1330409 : Blo 884570 1330409 := bstep (se 2 (by rfl) ⟨498903, by rfl⟩ : syracuseStep 1330409 = 997807) B997807
theorem B1330463 : Blo 884570 1330463 := bstep (se 1 (by rfl) ⟨997847, by rfl⟩ : syracuseStep 1330463 = 1995695) B1995695
theorem B2248033 : Blo 884570 2248033 := bstep (se 2 (by rfl) ⟨843012, by rfl⟩ : syracuseStep 2248033 = 1686025) B1686025
theorem B1494409 : Blo 884570 1494409 := bstep (se 2 (by rfl) ⟨560403, by rfl⟩ : syracuseStep 1494409 = 1120807) B1120807
theorem B1330631 : Blo 884570 1330631 := bstep (se 1 (by rfl) ⟨997973, by rfl⟩ : syracuseStep 1330631 = 1995947) B1995947
theorem B6737417 : Blo 884570 6737417 := bstep (se 2 (by rfl) ⟨2526531, by rfl⟩ : syracuseStep 6737417 = 5053063) B5053063
theorem B43667009 : Blo 884570 43667009 := bstep (se 2 (by rfl) ⟨16375128, by rfl⟩ : syracuseStep 43667009 = 32750257) B32750257
theorem B1330985 : Blo 884570 1330985 := bstep (se 2 (by rfl) ⟨499119, by rfl⟩ : syracuseStep 1330985 = 998239) B998239
theorem B1330991 : Blo 884570 1330991 := bstep (se 1 (by rfl) ⟨998243, by rfl⟩ : syracuseStep 1330991 = 1996487) B1996487
theorem B1494841 : Blo 884570 1494841 := bstep (se 2 (by rfl) ⟨560565, by rfl⟩ : syracuseStep 1494841 = 1121131) B1121131
theorem B1495145 : Blo 884570 1495145 := bstep (se 2 (by rfl) ⟨560679, by rfl⟩ : syracuseStep 1495145 = 1121359) B1121359
theorem B1331465 : Blo 884570 1331465 := bstep (se 2 (by rfl) ⟨499299, by rfl⟩ : syracuseStep 1331465 = 998599) B998599
theorem B2248985 : Blo 884570 2248985 := bstep (se 2 (by rfl) ⟨843369, by rfl⟩ : syracuseStep 2248985 = 1686739) B1686739
theorem B1331567 : Blo 884570 1331567 := bstep (se 1 (by rfl) ⟨998675, by rfl⟩ : syracuseStep 1331567 = 1997351) B1997351
theorem B9589211 : Blo 884570 9589211 := bstep (se 1 (by rfl) ⟨7191908, by rfl⟩ : syracuseStep 9589211 = 14383817) B14383817
theorem B1331783 : Blo 884570 1331783 := bstep (se 1 (by rfl) ⟨998837, by rfl⟩ : syracuseStep 1331783 = 1997675) B1997675
theorem B1331819 : Blo 884570 1331819 := bstep (se 1 (by rfl) ⟨998864, by rfl⟩ : syracuseStep 1331819 = 1997729) B1997729
theorem B1332047 : Blo 884570 1332047 := bstep (se 1 (by rfl) ⟨999035, by rfl⟩ : syracuseStep 1332047 = 1998071) B1998071
theorem B28726109 : Blo 884570 28726109 := bstep (se 3 (by rfl) ⟨5386145, by rfl⟩ : syracuseStep 28726109 = 10772291) B10772291
theorem B1332443 : Blo 884570 1332443 := bstep (se 1 (by rfl) ⟨999332, by rfl⟩ : syracuseStep 1332443 = 1998665) B1998665
theorem B1332617 : Blo 884570 1332617 := bstep (se 2 (by rfl) ⟨499731, by rfl⟩ : syracuseStep 1332617 = 999463) B999463
theorem B6739361 : Blo 884570 6739361 := bstep (se 2 (by rfl) ⟨2527260, by rfl⟩ : syracuseStep 6739361 = 5054521) B5054521
theorem B1889723 : Blo 884570 1889723 := bstep (se 1 (by rfl) ⟨1417292, by rfl⟩ : syracuseStep 1889723 = 2834585) B2834585
theorem B1496569 : Blo 884570 1496569 := bstep (se 2 (by rfl) ⟨561213, by rfl⟩ : syracuseStep 1496569 = 1122427) B1122427
theorem B4478651 : Blo 884570 4478651 := bstep (se 1 (by rfl) ⟨3358988, by rfl⟩ : syracuseStep 4478651 = 6717977) B6717977
theorem B1496839 : Blo 884570 1496839 := bstep (se 1 (by rfl) ⟨1122629, by rfl⟩ : syracuseStep 1496839 = 2245259) B2245259
theorem B1496873 : Blo 884570 1496873 := bstep (se 2 (by rfl) ⟨561327, by rfl⟩ : syracuseStep 1496873 = 1122655) B1122655
theorem B2053993 : Blo 884570 2053993 := bstep (se 2 (by rfl) ⟨770247, by rfl⟩ : syracuseStep 2053993 = 1540495) B1540495
theorem B3594493 : Blo 884570 3594493 := bstep (se 3 (by rfl) ⟨673967, by rfl⟩ : syracuseStep 3594493 = 1347935) B1347935
theorem B18209123 : Blo 884570 18209123 := bstep (se 1 (by rfl) ⟨13656842, by rfl⟩ : syracuseStep 18209123 = 27313685) B27313685
theorem B1497595 : Blo 884570 1497595 := bstep (se 1 (by rfl) ⟨1123196, by rfl⟩ : syracuseStep 1497595 = 2246393) B2246393
theorem B5691977 : Blo 884570 5691977 := bstep (se 2 (by rfl) ⟨2134491, by rfl⟩ : syracuseStep 5691977 = 4268983) B4268983
theorem B4315771 : Blo 884570 4315771 := bstep (se 1 (by rfl) ⟨3236828, by rfl⟩ : syracuseStep 4315771 = 6473657) B6473657
theorem B7199365 : Blo 884570 7199365 := bstep (se 4 (by rfl) ⟨674940, by rfl⟩ : syracuseStep 7199365 = 1349881) B1349881
theorem B6576815 : Blo 884570 6576815 := bstep (se 1 (by rfl) ⟨4932611, by rfl⟩ : syracuseStep 6576815 = 9865223) B9865223
theorem B5462939 : Blo 884570 5462939 := bstep (se 1 (by rfl) ⟨4097204, by rfl⟩ : syracuseStep 5462939 = 8194409) B8194409
theorem B1498027 : Blo 884570 1498027 := bstep (se 1 (by rfl) ⟨1123520, by rfl⟩ : syracuseStep 1498027 = 2247041) B2247041
theorem B1498331 : Blo 884570 1498331 := bstep (se 1 (by rfl) ⟨1123748, by rfl⟩ : syracuseStep 1498331 = 2247497) B2247497
theorem B17030411 : Blo 884570 17030411 := bstep (se 1 (by rfl) ⟨12772808, by rfl⟩ : syracuseStep 17030411 = 25545617) B25545617
theorem B2022779 : Blo 884570 2022779 := bstep (se 1 (by rfl) ⟨1517084, by rfl⟩ : syracuseStep 2022779 = 3034169) B3034169
theorem B25582979 : Blo 884570 25582979 := bstep (se 1 (by rfl) ⟨19187234, by rfl⟩ : syracuseStep 25582979 = 38374469) B38374469
theorem B1891721 : Blo 884570 1891721 := bstep (se 2 (by rfl) ⟨709395, by rfl⟩ : syracuseStep 1891721 = 1418791) B1418791
theorem B1498567 : Blo 884570 1498567 := bstep (se 1 (by rfl) ⟨1123925, by rfl⟩ : syracuseStep 1498567 = 2247851) B2247851
theorem B4480595 : Blo 884570 4480595 := bstep (se 1 (by rfl) ⟨3360446, by rfl⟩ : syracuseStep 4480595 = 6720893) B6720893
theorem B1990331 : Blo 884570 1990331 := bstep (se 1 (by rfl) ⟨1492748, by rfl⟩ : syracuseStep 1990331 = 2985497) B2985497
theorem B1990457 : Blo 884570 1990457 := bstep (se 2 (by rfl) ⟨746421, by rfl⟩ : syracuseStep 1990457 = 1492843) B1492843
theorem B1499087 : Blo 884570 1499087 := bstep (se 1 (by rfl) ⟨1124315, by rfl⟩ : syracuseStep 1499087 = 2248631) B2248631
theorem B8184017 : Blo 884570 8184017 := bstep (se 2 (by rfl) ⟨3069006, by rfl⟩ : syracuseStep 8184017 = 6138013) B6138013
theorem B1991087 : Blo 884570 1991087 := bstep (se 1 (by rfl) ⟨1493315, by rfl⟩ : syracuseStep 1991087 = 2986631) B2986631
theorem B1991123 : Blo 884570 1991123 := bstep (se 1 (by rfl) ⟨1493342, by rfl⟩ : syracuseStep 1991123 = 2986685) B2986685
theorem B1991231 : Blo 884570 1991231 := bstep (se 1 (by rfl) ⟨1493423, by rfl⟩ : syracuseStep 1991231 = 2986847) B2986847
theorem B13656721 : Blo 884570 13656721 := bstep (se 2 (by rfl) ⟨5121270, by rfl⟩ : syracuseStep 13656721 = 10242541) B10242541
theorem B1991339 : Blo 884570 1991339 := bstep (se 1 (by rfl) ⟨1493504, by rfl⟩ : syracuseStep 1991339 = 2987009) B2987009
theorem B5039009 : Blo 884570 5039009 := bstep (se 2 (by rfl) ⟨1889628, by rfl⟩ : syracuseStep 5039009 = 3779257) B3779257
theorem B6218689 : Blo 884570 6218689 := bstep (se 2 (by rfl) ⟨2332008, by rfl⟩ : syracuseStep 6218689 = 4664017) B4664017
theorem B1991879 : Blo 884570 1991879 := bstep (se 1 (by rfl) ⟨1493909, by rfl⟩ : syracuseStep 1991879 = 2987819) B2987819
theorem B1992059 : Blo 884570 1992059 := bstep (se 1 (by rfl) ⟨1494044, by rfl⟩ : syracuseStep 1992059 = 2988089) B2988089
theorem B1893755 : Blo 884570 1893755 := bstep (se 1 (by rfl) ⟨1420316, by rfl⟩ : syracuseStep 1893755 = 2840633) B2840633
theorem B1992185 : Blo 884570 1992185 := bstep (se 2 (by rfl) ⟨747069, by rfl⟩ : syracuseStep 1992185 = 1494139) B1494139
theorem B1992275 : Blo 884570 1992275 := bstep (se 1 (by rfl) ⟨1494206, by rfl⟩ : syracuseStep 1992275 = 2988413) B2988413
theorem B23029505 : Blo 884570 23029505 := bstep (se 2 (by rfl) ⟨8636064, by rfl⟩ : syracuseStep 23029505 = 17272129) B17272129
theorem B1992455 : Blo 884570 1992455 := bstep (se 1 (by rfl) ⟨1494341, by rfl⟩ : syracuseStep 1992455 = 2988683) B2988683
theorem B1993067 : Blo 884570 1993067 := bstep (se 1 (by rfl) ⟨1494800, by rfl⟩ : syracuseStep 1993067 = 2989601) B2989601
theorem B1894823 : Blo 884570 1894823 := bstep (se 1 (by rfl) ⟨1421117, by rfl⟩ : syracuseStep 1894823 = 2842235) B2842235
theorem B4483511 : Blo 884570 4483511 := bstep (se 1 (by rfl) ⟨3362633, by rfl⟩ : syracuseStep 4483511 = 6725267) B6725267
theorem B1993211 : Blo 884570 1993211 := bstep (se 1 (by rfl) ⟨1494908, by rfl⟩ : syracuseStep 1993211 = 2989817) B2989817
theorem B1796681 : Blo 884570 1796681 := bstep (se 2 (by rfl) ⟨673755, by rfl⟩ : syracuseStep 1796681 = 1347511) B1347511
theorem B1894985 : Blo 884570 1894985 := bstep (se 2 (by rfl) ⟨710619, by rfl⟩ : syracuseStep 1894985 = 1421239) B1421239
theorem B3369545 : Blo 884570 3369545 := bstep (se 2 (by rfl) ⟨1263579, by rfl⟩ : syracuseStep 3369545 = 2527159) B2527159
theorem B1993337 : Blo 884570 1993337 := bstep (se 2 (by rfl) ⟨747501, by rfl⟩ : syracuseStep 1993337 = 1495003) B1495003
theorem B1993391 : Blo 884570 1993391 := bstep (se 1 (by rfl) ⟨1495043, by rfl⟩ : syracuseStep 1993391 = 2990087) B2990087
theorem B1993463 : Blo 884570 1993463 := bstep (se 1 (by rfl) ⟨1495097, by rfl⟩ : syracuseStep 1993463 = 2990195) B2990195
theorem B1993643 : Blo 884570 1993643 := bstep (se 1 (by rfl) ⟨1495232, by rfl⟩ : syracuseStep 1993643 = 2990465) B2990465
theorem B1895719 : Blo 884570 1895719 := bstep (se 1 (by rfl) ⟨1421789, by rfl⟩ : syracuseStep 1895719 = 2843579) B2843579
theorem B4255105 : Blo 884570 4255105 := bstep (se 2 (by rfl) ⟨1595664, by rfl⟩ : syracuseStep 4255105 = 3191329) B3191329
theorem B30764461 : Blo 884570 30764461 := bstep (se 3 (by rfl) ⟨5768336, by rfl⟩ : syracuseStep 30764461 = 11536673) B11536673
theorem B1994183 : Blo 884570 1994183 := bstep (se 1 (by rfl) ⟨1495637, by rfl⟩ : syracuseStep 1994183 = 2991275) B2991275
theorem B5041673 : Blo 884570 5041673 := bstep (se 2 (by rfl) ⟨1890627, by rfl⟩ : syracuseStep 5041673 = 3781255) B3781255
theorem B3600139 : Blo 884570 3600139 := bstep (se 1 (by rfl) ⟨2700104, by rfl⟩ : syracuseStep 3600139 = 5400209) B5400209
theorem B1994543 : Blo 884570 1994543 := bstep (se 1 (by rfl) ⟨1495907, by rfl⟩ : syracuseStep 1994543 = 2991815) B2991815
theorem B26570753 : Blo 884570 26570753 := bstep (se 2 (by rfl) ⟨9964032, by rfl⟩ : syracuseStep 26570753 = 19928065) B19928065
theorem B3371017 : Blo 884570 3371017 := bstep (se 2 (by rfl) ⟨1264131, by rfl⟩ : syracuseStep 3371017 = 2528263) B2528263
theorem B946523 : Blo 884570 946523 := bstep (se 1 (by rfl) ⟨709892, by rfl⟩ : syracuseStep 946523 = 1419785) B1419785
theorem B1995119 : Blo 884570 1995119 := bstep (se 1 (by rfl) ⟨1496339, by rfl⟩ : syracuseStep 1995119 = 2992679) B2992679
theorem B1995191 : Blo 884570 1995191 := bstep (se 1 (by rfl) ⟨1496393, by rfl⟩ : syracuseStep 1995191 = 2992787) B2992787
theorem B3371489 : Blo 884570 3371489 := bstep (se 2 (by rfl) ⟨1264308, by rfl⟩ : syracuseStep 3371489 = 2528617) B2528617
theorem B1995335 : Blo 884570 1995335 := bstep (se 1 (by rfl) ⟨1496501, by rfl⟩ : syracuseStep 1995335 = 2993003) B2993003
theorem B1995371 : Blo 884570 1995371 := bstep (se 1 (by rfl) ⟨1496528, by rfl⟩ : syracuseStep 1995371 = 2993057) B2993057
theorem B4485779 : Blo 884570 4485779 := bstep (se 1 (by rfl) ⟨3364334, by rfl⟩ : syracuseStep 4485779 = 6728669) B6728669
theorem B8090533 : Blo 884570 8090533 := bstep (se 4 (by rfl) ⟨758487, by rfl⟩ : syracuseStep 8090533 = 1516975) B1516975
theorem B1995767 : Blo 884570 1995767 := bstep (se 1 (by rfl) ⟨1496825, by rfl⟩ : syracuseStep 1995767 = 2993651) B2993651
theorem B2520359 : Blo 884570 2520359 := bstep (se 1 (by rfl) ⟨1890269, by rfl⟩ : syracuseStep 2520359 = 3780539) B3780539
theorem B1996127 : Blo 884570 1996127 := bstep (se 1 (by rfl) ⟨1497095, by rfl⟩ : syracuseStep 1996127 = 2994191) B2994191
theorem B3601759 : Blo 884570 3601759 := bstep (se 1 (by rfl) ⟨2701319, by rfl⟩ : syracuseStep 3601759 = 5402639) B5402639
theorem B4486589 : Blo 884570 4486589 := bstep (se 3 (by rfl) ⟨841235, by rfl⟩ : syracuseStep 4486589 = 1682471) B1682471
theorem B29554391 : Blo 884570 29554391 := bstep (se 1 (by rfl) ⟨22165793, by rfl⟩ : syracuseStep 29554391 = 44331587) B44331587
theorem B1996523 : Blo 884570 1996523 := bstep (se 1 (by rfl) ⟨1497392, by rfl⟩ : syracuseStep 1996523 = 2994785) B2994785
theorem B1996649 : Blo 884570 1996649 := bstep (se 2 (by rfl) ⟨748743, by rfl⟩ : syracuseStep 1996649 = 1497487) B1497487
theorem B948731 : Blo 884570 948731 := bstep (se 1 (by rfl) ⟨711548, by rfl⟩ : syracuseStep 948731 = 1423097) B1423097
theorem B2128447 : Blo 884570 2128447 := bstep (se 1 (by rfl) ⟨1596335, by rfl⟩ : syracuseStep 2128447 = 3192671) B3192671
theorem B6486635 : Blo 884570 6486635 := bstep (se 1 (by rfl) ⟨4864976, by rfl⟩ : syracuseStep 6486635 = 9729953) B9729953
theorem B32733829 : Blo 884570 32733829 := bstep (se 4 (by rfl) ⟨3068796, by rfl⟩ : syracuseStep 32733829 = 6137593) B6137593
theorem B8518283 : Blo 884570 8518283 := bstep (se 1 (by rfl) ⟨6388712, by rfl⟩ : syracuseStep 8518283 = 12777425) B12777425
theorem B1997495 : Blo 884570 1997495 := bstep (se 1 (by rfl) ⟨1498121, by rfl⟩ : syracuseStep 1997495 = 2996243) B2996243
theorem B2128783 : Blo 884570 2128783 := bstep (se 1 (by rfl) ⟨1596587, by rfl⟩ : syracuseStep 2128783 = 3193175) B3193175
theorem B1997711 : Blo 884570 1997711 := bstep (se 1 (by rfl) ⟨1498283, by rfl⟩ : syracuseStep 1997711 = 2996567) B2996567
theorem B4095431 : Blo 884570 4095431 := bstep (se 1 (by rfl) ⟨3071573, by rfl⟩ : syracuseStep 4095431 = 6143147) B6143147
theorem B25886213 : Blo 884570 25886213 := bstep (se 4 (by rfl) ⟨2426832, by rfl⟩ : syracuseStep 25886213 = 4853665) B4853665
theorem B4259411 : Blo 884570 4259411 := bstep (se 1 (by rfl) ⟨3194558, by rfl⟩ : syracuseStep 4259411 = 6389117) B6389117
theorem B1998431 : Blo 884570 1998431 := bstep (se 1 (by rfl) ⟨1498823, by rfl⟩ : syracuseStep 1998431 = 2997647) B2997647
theorem B13631093 : Blo 884570 13631093 := bstep (se 5 (by rfl) ⟨638957, by rfl⟩ : syracuseStep 13631093 = 1277915) B1277915
theorem B2522785 : Blo 884570 2522785 := bstep (se 2 (by rfl) ⟨946044, by rfl⟩ : syracuseStep 2522785 = 1892089) B1892089
theorem B1998647 : Blo 884570 1998647 := bstep (se 1 (by rfl) ⟨1498985, by rfl⟩ : syracuseStep 1998647 = 2997971) B2997971
theorem B884635 : Blo 884570 884635 := bstep (se 1 (by rfl) ⟨663476, by rfl⟩ : syracuseStep 884635 = 1326953) B1326953
theorem B884687 : Blo 884570 884687 := bstep (se 1 (by rfl) ⟨663515, by rfl⟩ : syracuseStep 884687 = 1327031) B1327031
theorem B2162639 : Blo 884570 2162639 := bstep (se 1 (by rfl) ⟨1621979, by rfl⟩ : syracuseStep 2162639 = 3243959) B3243959
theorem B884711 : Blo 884570 884711 := bstep (se 1 (by rfl) ⟨663533, by rfl⟩ : syracuseStep 884711 = 1327067) B1327067
theorem B2523275 : Blo 884570 2523275 := bstep (se 1 (by rfl) ⟨1892456, by rfl⟩ : syracuseStep 2523275 = 3784913) B3784913
theorem B884967 : Blo 884570 884967 := bstep (se 1 (by rfl) ⟨663725, by rfl⟩ : syracuseStep 884967 = 1327451) B1327451
theorem B1999079 : Blo 884570 1999079 := bstep (se 1 (by rfl) ⟨1499309, by rfl⟩ : syracuseStep 1999079 = 2998619) B2998619
theorem B3244313 : Blo 884570 3244313 := bstep (se 2 (by rfl) ⟨1216617, by rfl⟩ : syracuseStep 3244313 = 2433235) B2433235
theorem B885119 : Blo 884570 885119 := bstep (se 1 (by rfl) ⟨663839, by rfl⟩ : syracuseStep 885119 = 1327679) B1327679
theorem B885199 : Blo 884570 885199 := bstep (se 1 (by rfl) ⟨663899, by rfl⟩ : syracuseStep 885199 = 1327799) B1327799
theorem B4260347 : Blo 884570 4260347 := bstep (se 1 (by rfl) ⟨3195260, by rfl⟩ : syracuseStep 4260347 = 6390521) B6390521
theorem B885351 : Blo 884570 885351 := bstep (se 1 (by rfl) ⟨664013, by rfl⟩ : syracuseStep 885351 = 1328027) B1328027
theorem B1442539 : Blo 884570 1442539 := bstep (se 1 (by rfl) ⟨1081904, by rfl⟩ : syracuseStep 1442539 = 2163809) B2163809
theorem B5047049 : Blo 884570 5047049 := bstep (se 2 (by rfl) ⟨1892643, by rfl⟩ : syracuseStep 5047049 = 3785287) B3785287
theorem B885615 : Blo 884570 885615 := bstep (se 1 (by rfl) ⟨664211, by rfl⟩ : syracuseStep 885615 = 1328423) B1328423
theorem B2524061 : Blo 884570 2524061 := bstep (se 3 (by rfl) ⟨473261, by rfl⟩ : syracuseStep 2524061 = 946523) B946523
theorem B885671 : Blo 884570 885671 := bstep (se 1 (by rfl) ⟨664253, by rfl⟩ : syracuseStep 885671 = 1328507) B1328507
theorem B885755 : Blo 884570 885755 := bstep (se 1 (by rfl) ⟨664316, by rfl⟩ : syracuseStep 885755 = 1328633) B1328633
theorem B885823 : Blo 884570 885823 := bstep (se 1 (by rfl) ⟨664367, by rfl⟩ : syracuseStep 885823 = 1328735) B1328735
theorem B885967 : Blo 884570 885967 := bstep (se 1 (by rfl) ⟨664475, by rfl⟩ : syracuseStep 885967 = 1328951) B1328951
theorem B4555997 : Blo 884570 4555997 := bstep (se 3 (by rfl) ⟨854249, by rfl⟩ : syracuseStep 4555997 = 1708499) B1708499
theorem B8291585 : Blo 884570 8291585 := bstep (se 2 (by rfl) ⟨3109344, by rfl⟩ : syracuseStep 8291585 = 6218689) B6218689
theorem B11535691 : Blo 884570 11535691 := bstep (se 1 (by rfl) ⟨8651768, by rfl⟩ : syracuseStep 11535691 = 17303537) B17303537
theorem B886171 : Blo 884570 886171 := bstep (se 1 (by rfl) ⟨664628, by rfl⟩ : syracuseStep 886171 = 1329257) B1329257
theorem B497845763 : Blo 884570 497845763 := bstep (se 1 (by rfl) ⟨373384322, by rfl⟩ : syracuseStep 497845763 = 746768645) B746768645
theorem B886383 : Blo 884570 886383 := bstep (se 1 (by rfl) ⟨664787, by rfl⟩ : syracuseStep 886383 = 1329575) B1329575
theorem B886439 : Blo 884570 886439 := bstep (se 1 (by rfl) ⟨664829, by rfl⟩ : syracuseStep 886439 = 1329659) B1329659
theorem B886523 : Blo 884570 886523 := bstep (se 1 (by rfl) ⟨664892, by rfl⟩ : syracuseStep 886523 = 1329785) B1329785
theorem B886559 : Blo 884570 886559 := bstep (se 1 (by rfl) ⟨664919, by rfl⟩ : syracuseStep 886559 = 1329839) B1329839
theorem B886591 : Blo 884570 886591 := bstep (se 1 (by rfl) ⟨664943, by rfl⟩ : syracuseStep 886591 = 1329887) B1329887
theorem B886767 : Blo 884570 886767 := bstep (se 1 (by rfl) ⟨665075, by rfl⟩ : syracuseStep 886767 = 1330151) B1330151
theorem B8095787 : Blo 884570 8095787 := bstep (se 1 (by rfl) ⟨6071840, by rfl⟩ : syracuseStep 8095787 = 12143681) B12143681
theorem B886939 : Blo 884570 886939 := bstep (se 1 (by rfl) ⟨665204, by rfl⟩ : syracuseStep 886939 = 1330409) B1330409
theorem B886975 : Blo 884570 886975 := bstep (se 1 (by rfl) ⟨665231, by rfl⟩ : syracuseStep 886975 = 1330463) B1330463
theorem B887087 : Blo 884570 887087 := bstep (se 1 (by rfl) ⟨665315, by rfl⟩ : syracuseStep 887087 = 1330631) B1330631
theorem B4491611 : Blo 884570 4491611 := bstep (se 1 (by rfl) ⟨3368708, by rfl⟩ : syracuseStep 4491611 = 6737417) B6737417
theorem B887323 : Blo 884570 887323 := bstep (se 1 (by rfl) ⟨665492, by rfl⟩ : syracuseStep 887323 = 1330985) B1330985
theorem B887327 : Blo 884570 887327 := bstep (se 1 (by rfl) ⟨665495, by rfl⟩ : syracuseStep 887327 = 1330991) B1330991
theorem B887643 : Blo 884570 887643 := bstep (se 1 (by rfl) ⟨665732, by rfl⟩ : syracuseStep 887643 = 1331465) B1331465
theorem B887711 : Blo 884570 887711 := bstep (se 1 (by rfl) ⟨665783, by rfl⟩ : syracuseStep 887711 = 1331567) B1331567
theorem B6392807 : Blo 884570 6392807 := bstep (se 1 (by rfl) ⟨4794605, by rfl⟩ : syracuseStep 6392807 = 9589211) B9589211
theorem B887855 : Blo 884570 887855 := bstep (se 1 (by rfl) ⟨665891, by rfl⟩ : syracuseStep 887855 = 1331783) B1331783
theorem B887879 : Blo 884570 887879 := bstep (se 1 (by rfl) ⟨665909, by rfl⟩ : syracuseStep 887879 = 1331819) B1331819
theorem B888031 : Blo 884570 888031 := bstep (se 1 (by rfl) ⟨666023, by rfl⟩ : syracuseStep 888031 = 1332047) B1332047
theorem B7572761 : Blo 884570 7572761 := bstep (se 2 (by rfl) ⟨2839785, by rfl⟩ : syracuseStep 7572761 = 5679571) B5679571
theorem B888295 : Blo 884570 888295 := bstep (se 1 (by rfl) ⟨666221, by rfl⟩ : syracuseStep 888295 = 1332443) B1332443
theorem B888411 : Blo 884570 888411 := bstep (se 1 (by rfl) ⟨666308, by rfl⟩ : syracuseStep 888411 = 1332617) B1332617
theorem B4492907 : Blo 884570 4492907 := bstep (se 1 (by rfl) ⟨3369680, by rfl⟩ : syracuseStep 4492907 = 6739361) B6739361
theorem B2985767 : Blo 884570 2985767 := bstep (se 1 (by rfl) ⟨2239325, by rfl⟩ : syracuseStep 2985767 = 4478651) B4478651
theorem B11374829 : Blo 884570 11374829 := bstep (se 3 (by rfl) ⟨2132780, by rfl⟩ : syracuseStep 11374829 = 4265561) B4265561
theorem B2527625 : Blo 884570 2527625 := bstep (se 2 (by rfl) ⟨947859, by rfl⟩ : syracuseStep 2527625 = 1895719) B1895719
theorem B5673473 : Blo 884570 5673473 := bstep (se 2 (by rfl) ⟨2127552, by rfl⟩ : syracuseStep 5673473 = 4255105) B4255105
theorem B3641959 : Blo 884570 3641959 := bstep (se 1 (by rfl) ⟨2731469, by rfl⟩ : syracuseStep 3641959 = 5462939) B5462939
theorem B2986793 : Blo 884570 2986793 := bstep (se 2 (by rfl) ⟨1120047, by rfl⟩ : syracuseStep 2986793 = 2240095) B2240095
theorem B2987063 : Blo 884570 2987063 := bstep (se 1 (by rfl) ⟨2240297, by rfl⟩ : syracuseStep 2987063 = 4480595) B4480595
theorem B4494689 : Blo 884570 4494689 := bstep (se 2 (by rfl) ⟨1685508, by rfl⟩ : syracuseStep 4494689 = 3371017) B3371017
theorem B1120063 : Blo 884570 1120063 := bstep (se 1 (by rfl) ⟨840047, by rfl⟩ : syracuseStep 1120063 = 1680095) B1680095
theorem B10787377 : Blo 884570 10787377 := bstep (se 2 (by rfl) ⟨4045266, by rfl⟩ : syracuseStep 10787377 = 8090533) B8090533
theorem B2529949 : Blo 884570 2529949 := bstep (se 3 (by rfl) ⟨474365, by rfl⟩ : syracuseStep 2529949 = 948731) B948731
theorem B4791149 : Blo 884570 4791149 := bstep (se 3 (by rfl) ⟨898340, by rfl⟩ : syracuseStep 4791149 = 1796681) B1796681
theorem B10099565 : Blo 884570 10099565 := bstep (se 3 (by rfl) ⟨1893668, by rfl⟩ : syracuseStep 10099565 = 3787337) B3787337
theorem B2989007 : Blo 884570 2989007 := bstep (se 1 (by rfl) ⟨2241755, by rfl⟩ : syracuseStep 2989007 = 4483511) B4483511
theorem B25960085 : Blo 884570 25960085 := bstep (se 6 (by rfl) ⟨608439, by rfl⟩ : syracuseStep 25960085 = 1216879) B1216879
theorem B10101023 : Blo 884570 10101023 := bstep (se 1 (by rfl) ⟨7575767, by rfl⟩ : syracuseStep 10101023 = 15151535) B15151535
theorem B4792657 : Blo 884570 4792657 := bstep (se 2 (by rfl) ⟨1797246, by rfl⟩ : syracuseStep 4792657 = 3594493) B3594493
theorem B2990519 : Blo 884570 2990519 := bstep (se 1 (by rfl) ⟨2242889, by rfl⟩ : syracuseStep 2990519 = 4485779) B4485779
theorem B1680239 : Blo 884570 1680239 := bstep (se 1 (by rfl) ⟨1260179, by rfl⟩ : syracuseStep 1680239 = 2520359) B2520359
theorem B2991005 : Blo 884570 2991005 := bstep (se 3 (by rfl) ⟨560813, by rfl⟩ : syracuseStep 2991005 = 1121627) B1121627
theorem B2991059 : Blo 884570 2991059 := bstep (se 1 (by rfl) ⟨2243294, by rfl⟩ : syracuseStep 2991059 = 4486589) B4486589
theorem B19702927 : Blo 884570 19702927 := bstep (se 1 (by rfl) ⟨14777195, by rfl⟩ : syracuseStep 19702927 = 29554391) B29554391
theorem B1123951 : Blo 884570 1123951 := bstep (se 1 (by rfl) ⟨842963, by rfl⟩ : syracuseStep 1123951 = 1685927) B1685927
theorem B5678855 : Blo 884570 5678855 := bstep (se 1 (by rfl) ⟨4259141, by rfl⟩ : syracuseStep 5678855 = 8518283) B8518283
theorem B1681249 : Blo 884570 1681249 := bstep (se 2 (by rfl) ⟨630468, by rfl⟩ : syracuseStep 1681249 = 1260937) B1260937
theorem B1124543 : Blo 884570 1124543 := bstep (se 1 (by rfl) ⟨843407, by rfl⟩ : syracuseStep 1124543 = 1686815) B1686815
theorem B2730287 : Blo 884570 2730287 := bstep (se 1 (by rfl) ⟨2047715, by rfl⟩ : syracuseStep 2730287 = 4095431) B4095431
theorem B9087395 : Blo 884570 9087395 := bstep (se 1 (by rfl) ⟨6815546, by rfl⟩ : syracuseStep 9087395 = 13631093) B13631093
theorem B2239609 : Blo 884570 2239609 := bstep (se 2 (by rfl) ⟨839853, by rfl⟩ : syracuseStep 2239609 = 1679707) B1679707
theorem B2993273 : Blo 884570 2993273 := bstep (se 2 (by rfl) ⟨1122477, by rfl⟩ : syracuseStep 2993273 = 2244955) B2244955
theorem B2239913 : Blo 884570 2239913 := bstep (se 2 (by rfl) ⟨839967, by rfl⟩ : syracuseStep 2239913 = 1679935) B1679935
theorem B2993597 : Blo 884570 2993597 := bstep (se 3 (by rfl) ⟨561299, by rfl⟩ : syracuseStep 2993597 = 1122599) B1122599
theorem B995143 : Blo 884570 995143 := bstep (se 1 (by rfl) ⟨746357, by rfl⟩ : syracuseStep 995143 = 1492715) B1492715
theorem B2240399 : Blo 884570 2240399 := bstep (se 1 (by rfl) ⟨1680299, by rfl⟩ : syracuseStep 2240399 = 3360599) B3360599
theorem B276377615 : Blo 884570 276377615 := bstep (se 1 (by rfl) ⟨207283211, by rfl⟩ : syracuseStep 276377615 = 414566423) B414566423
theorem B2994299 : Blo 884570 2994299 := bstep (se 1 (by rfl) ⟨2245724, by rfl⟩ : syracuseStep 2994299 = 4491449) B4491449
theorem B3191069 : Blo 884570 3191069 := bstep (se 3 (by rfl) ⟨598325, by rfl⟩ : syracuseStep 3191069 = 1196651) B1196651
theorem B2994461 : Blo 884570 2994461 := bstep (se 3 (by rfl) ⟨561461, by rfl⟩ : syracuseStep 2994461 = 1122923) B1122923
theorem B2240905 : Blo 884570 2240905 := bstep (se 2 (by rfl) ⟨840339, by rfl⟩ : syracuseStep 2240905 = 1680679) B1680679
theorem B2994569 : Blo 884570 2994569 := bstep (se 2 (by rfl) ⟨1122963, by rfl⟩ : syracuseStep 2994569 = 2245927) B2245927
theorem B5747087 : Blo 884570 5747087 := bstep (se 1 (by rfl) ⟨4310315, by rfl⟩ : syracuseStep 5747087 = 8620631) B8620631
theorem B6730127 : Blo 884570 6730127 := bstep (se 1 (by rfl) ⟨5047595, by rfl⟩ : syracuseStep 6730127 = 10095191) B10095191
theorem B34550165 : Blo 884570 34550165 := bstep (se 6 (by rfl) ⟨809769, by rfl⟩ : syracuseStep 34550165 = 1619539) B1619539
theorem B995791 : Blo 884570 995791 := bstep (se 1 (by rfl) ⟨746843, by rfl⟩ : syracuseStep 995791 = 1493687) B1493687
theorem B2241017 : Blo 884570 2241017 := bstep (se 2 (by rfl) ⟨840381, by rfl⟩ : syracuseStep 2241017 = 1680763) B1680763
theorem B3453521 : Blo 884570 3453521 := bstep (se 2 (by rfl) ⟨1295070, by rfl⟩ : syracuseStep 3453521 = 2590141) B2590141
theorem B2274313 : Blo 884570 2274313 := bstep (se 2 (by rfl) ⟨852867, by rfl⟩ : syracuseStep 2274313 = 1705735) B1705735
theorem B29111339 : Blo 884570 29111339 := bstep (se 1 (by rfl) ⟨21833504, by rfl⟩ : syracuseStep 29111339 = 43667009) B43667009
theorem B5682419 : Blo 884570 5682419 := bstep (se 1 (by rfl) ⟨4261814, by rfl⟩ : syracuseStep 5682419 = 8523629) B8523629
theorem B2995487 : Blo 884570 2995487 := bstep (se 1 (by rfl) ⟨2246615, by rfl⟩ : syracuseStep 2995487 = 4493231) B4493231
theorem B996763 : Blo 884570 996763 := bstep (se 1 (by rfl) ⟨747572, by rfl⟩ : syracuseStep 996763 = 1495145) B1495145
theorem B3192713 : Blo 884570 3192713 := bstep (se 2 (by rfl) ⟨1197267, by rfl⟩ : syracuseStep 3192713 = 2394535) B2394535
theorem B19150739 : Blo 884570 19150739 := bstep (se 1 (by rfl) ⟨14363054, by rfl⟩ : syracuseStep 19150739 = 28726109) B28726109
theorem B23017445 : Blo 884570 23017445 := bstep (se 4 (by rfl) ⟨2157885, by rfl⟩ : syracuseStep 23017445 = 4315771) B4315771
theorem B10762469 : Blo 884570 10762469 := bstep (se 4 (by rfl) ⟨1008981, by rfl⟩ : syracuseStep 10762469 = 2017963) B2017963
theorem B1685767 : Blo 884570 1685767 := bstep (se 1 (by rfl) ⟨1264325, by rfl⟩ : syracuseStep 1685767 = 2528651) B2528651
theorem B1259815 : Blo 884570 1259815 := bstep (se 1 (by rfl) ⟨944861, by rfl⟩ : syracuseStep 1259815 = 1889723) B1889723
theorem B997915 : Blo 884570 997915 := bstep (se 1 (by rfl) ⟨748436, by rfl⟩ : syracuseStep 997915 = 1496873) B1496873
theorem B12139415 : Blo 884570 12139415 := bstep (se 1 (by rfl) ⟨9104561, by rfl⟩ : syracuseStep 12139415 = 18209123) B18209123
theorem B3783631 : Blo 884570 3783631 := bstep (se 1 (by rfl) ⟨2837723, by rfl⟩ : syracuseStep 3783631 = 5675447) B5675447
theorem B2997377 : Blo 884570 2997377 := bstep (se 2 (by rfl) ⟨1124016, by rfl⟩ : syracuseStep 2997377 = 2248033) B2248033
theorem B2997431 : Blo 884570 2997431 := bstep (se 1 (by rfl) ⟨2248073, by rfl⟩ : syracuseStep 2997431 = 4496147) B4496147
theorem B24624323 : Blo 884570 24624323 := bstep (se 1 (by rfl) ⟨18468242, by rfl⟩ : syracuseStep 24624323 = 36936485) B36936485
theorem B998887 : Blo 884570 998887 := bstep (se 1 (by rfl) ⟨749165, by rfl⟩ : syracuseStep 998887 = 1498331) B1498331
theorem B11353607 : Blo 884570 11353607 := bstep (se 1 (by rfl) ⟨8515205, by rfl⟩ : syracuseStep 11353607 = 17030411) B17030411
theorem B17055319 : Blo 884570 17055319 := bstep (se 1 (by rfl) ⟨12791489, by rfl⟩ : syracuseStep 17055319 = 25582979) B25582979
theorem B4800185 : Blo 884570 4800185 := bstep (se 2 (by rfl) ⟨1800069, by rfl⟩ : syracuseStep 4800185 = 3600139) B3600139
theorem B1326887 : Blo 884570 1326887 := bstep (se 1 (by rfl) ⟨995165, by rfl⟩ : syracuseStep 1326887 = 1990331) B1990331
theorem B1326971 : Blo 884570 1326971 := bstep (se 1 (by rfl) ⟨995228, by rfl⟩ : syracuseStep 1326971 = 1990457) B1990457
theorem B3194747 : Blo 884570 3194747 := bstep (se 1 (by rfl) ⟨2396060, by rfl⟩ : syracuseStep 3194747 = 4792121) B4792121
theorem B2998187 : Blo 884570 2998187 := bstep (se 1 (by rfl) ⟨2248640, by rfl⟩ : syracuseStep 2998187 = 4497281) B4497281
theorem B999391 : Blo 884570 999391 := bstep (se 1 (by rfl) ⟨749543, by rfl⟩ : syracuseStep 999391 = 1499087) B1499087
theorem B5456011 : Blo 884570 5456011 := bstep (se 1 (by rfl) ⟨4092008, by rfl⟩ : syracuseStep 5456011 = 8184017) B8184017
theorem B1327391 : Blo 884570 1327391 := bstep (se 1 (by rfl) ⟨995543, by rfl⟩ : syracuseStep 1327391 = 1991087) B1991087
theorem B1327415 : Blo 884570 1327415 := bstep (se 1 (by rfl) ⟨995561, by rfl⟩ : syracuseStep 1327415 = 1991123) B1991123
theorem B22987097 : Blo 884570 22987097 := bstep (se 2 (by rfl) ⟨8620161, by rfl⟩ : syracuseStep 22987097 = 17240323) B17240323
theorem B1327487 : Blo 884570 1327487 := bstep (se 1 (by rfl) ⟨995615, by rfl⟩ : syracuseStep 1327487 = 1991231) B1991231
theorem B1327559 : Blo 884570 1327559 := bstep (se 1 (by rfl) ⟨995669, by rfl⟩ : syracuseStep 1327559 = 1991339) B1991339
theorem B2998727 : Blo 884570 2998727 := bstep (se 1 (by rfl) ⟨2249045, by rfl⟩ : syracuseStep 2998727 = 4498091) B4498091
theorem B2245097 : Blo 884570 2245097 := bstep (se 2 (by rfl) ⟨841911, by rfl⟩ : syracuseStep 2245097 = 1683823) B1683823
theorem B3359339 : Blo 884570 3359339 := bstep (se 1 (by rfl) ⟨2519504, by rfl⟩ : syracuseStep 3359339 = 5039009) B5039009
theorem B12763811 : Blo 884570 12763811 := bstep (se 1 (by rfl) ⟨9572858, by rfl⟩ : syracuseStep 12763811 = 19145717) B19145717
theorem B1327913 : Blo 884570 1327913 := bstep (se 2 (by rfl) ⟨497967, by rfl⟩ : syracuseStep 1327913 = 995935) B995935
theorem B1327919 : Blo 884570 1327919 := bstep (se 1 (by rfl) ⟨995939, by rfl⟩ : syracuseStep 1327919 = 1991879) B1991879
theorem B3785629 : Blo 884570 3785629 := bstep (se 3 (by rfl) ⟨709805, by rfl⟩ : syracuseStep 3785629 = 1419611) B1419611
theorem B1328039 : Blo 884570 1328039 := bstep (se 1 (by rfl) ⟨996029, by rfl⟩ : syracuseStep 1328039 = 1992059) B1992059
theorem B1262503 : Blo 884570 1262503 := bstep (se 1 (by rfl) ⟨946877, by rfl⟩ : syracuseStep 1262503 = 1893755) B1893755
theorem B1328123 : Blo 884570 1328123 := bstep (se 1 (by rfl) ⟨996092, by rfl⟩ : syracuseStep 1328123 = 1992185) B1992185
theorem B1328183 : Blo 884570 1328183 := bstep (se 1 (by rfl) ⟨996137, by rfl⟩ : syracuseStep 1328183 = 1992275) B1992275
theorem B15353003 : Blo 884570 15353003 := bstep (se 1 (by rfl) ⟨11514752, by rfl⟩ : syracuseStep 15353003 = 23029505) B23029505
theorem B1328303 : Blo 884570 1328303 := bstep (se 1 (by rfl) ⟨996227, by rfl⟩ : syracuseStep 1328303 = 1992455) B1992455
theorem B1328711 : Blo 884570 1328711 := bstep (se 1 (by rfl) ⟨996533, by rfl⟩ : syracuseStep 1328711 = 1993067) B1993067
theorem B1263215 : Blo 884570 1263215 := bstep (se 1 (by rfl) ⟨947411, by rfl⟩ : syracuseStep 1263215 = 1894823) B1894823
theorem B1328807 : Blo 884570 1328807 := bstep (se 1 (by rfl) ⟨996605, by rfl⟩ : syracuseStep 1328807 = 1993211) B1993211
theorem B1263323 : Blo 884570 1263323 := bstep (se 1 (by rfl) ⟨947492, by rfl⟩ : syracuseStep 1263323 = 1894985) B1894985
theorem B2246363 : Blo 884570 2246363 := bstep (se 1 (by rfl) ⟨1684772, by rfl⟩ : syracuseStep 2246363 = 3369545) B3369545
theorem B21546719 : Blo 884570 21546719 := bstep (se 1 (by rfl) ⟨16160039, by rfl⟩ : syracuseStep 21546719 = 32320079) B32320079
theorem B1328891 : Blo 884570 1328891 := bstep (se 1 (by rfl) ⟨996668, by rfl⟩ : syracuseStep 1328891 = 1993337) B1993337
theorem B1328927 : Blo 884570 1328927 := bstep (se 1 (by rfl) ⟨996695, by rfl⟩ : syracuseStep 1328927 = 1993391) B1993391
theorem B4802345 : Blo 884570 4802345 := bstep (se 2 (by rfl) ⟨1800879, by rfl⟩ : syracuseStep 4802345 = 3601759) B3601759
theorem B1328975 : Blo 884570 1328975 := bstep (se 1 (by rfl) ⟨996731, by rfl⟩ : syracuseStep 1328975 = 1993463) B1993463
theorem B1329095 : Blo 884570 1329095 := bstep (se 1 (by rfl) ⟨996821, by rfl⟩ : syracuseStep 1329095 = 1993643) B1993643
theorem B1492985 : Blo 884570 1492985 := bstep (se 2 (by rfl) ⟨559869, by rfl⟩ : syracuseStep 1492985 = 1119739) B1119739
theorem B1493147 : Blo 884570 1493147 := bstep (se 1 (by rfl) ⟨1119860, by rfl⟩ : syracuseStep 1493147 = 2239721) B2239721
theorem B1493255 : Blo 884570 1493255 := bstep (se 1 (by rfl) ⟨1119941, by rfl⟩ : syracuseStep 1493255 = 2239883) B2239883
theorem B1329449 : Blo 884570 1329449 := bstep (se 2 (by rfl) ⟨498543, by rfl⟩ : syracuseStep 1329449 = 997087) B997087
theorem B1329455 : Blo 884570 1329455 := bstep (se 1 (by rfl) ⟨997091, by rfl⟩ : syracuseStep 1329455 = 1994183) B1994183
theorem B3361115 : Blo 884570 3361115 := bstep (se 1 (by rfl) ⟨2520836, by rfl⟩ : syracuseStep 3361115 = 5041673) B5041673
theorem B2738657 : Blo 884570 2738657 := bstep (se 2 (by rfl) ⟨1026996, by rfl⟩ : syracuseStep 2738657 = 2053993) B2053993
theorem B1329695 : Blo 884570 1329695 := bstep (se 1 (by rfl) ⟨997271, by rfl⟩ : syracuseStep 1329695 = 1994543) B1994543
theorem B17713835 : Blo 884570 17713835 := bstep (se 1 (by rfl) ⟨13285376, by rfl⟩ : syracuseStep 17713835 = 26570753) B26570753
theorem B1493815 : Blo 884570 1493815 := bstep (se 1 (by rfl) ⟨1120361, by rfl⟩ : syracuseStep 1493815 = 2240723) B2240723
theorem B1330079 : Blo 884570 1330079 := bstep (se 1 (by rfl) ⟨997559, by rfl⟩ : syracuseStep 1330079 = 1995119) B1995119
theorem B1330127 : Blo 884570 1330127 := bstep (se 1 (by rfl) ⟨997595, by rfl⟩ : syracuseStep 1330127 = 1995191) B1995191
theorem B18205661 : Blo 884570 18205661 := bstep (se 3 (by rfl) ⟨3413561, by rfl⟩ : syracuseStep 18205661 = 6827123) B6827123
theorem B2247659 : Blo 884570 2247659 := bstep (se 1 (by rfl) ⟨1685744, by rfl⟩ : syracuseStep 2247659 = 3371489) B3371489
theorem B1330217 : Blo 884570 1330217 := bstep (se 2 (by rfl) ⟨498831, by rfl⟩ : syracuseStep 1330217 = 997663) B997663
theorem B1330223 : Blo 884570 1330223 := bstep (se 1 (by rfl) ⟨997667, by rfl⟩ : syracuseStep 1330223 = 1995335) B1995335
theorem B1330247 : Blo 884570 1330247 := bstep (se 1 (by rfl) ⟨997685, by rfl⟩ : syracuseStep 1330247 = 1995371) B1995371
theorem B4050119 : Blo 884570 4050119 := bstep (se 1 (by rfl) ⟨3037589, by rfl⟩ : syracuseStep 4050119 = 6075179) B6075179
theorem B1494281 : Blo 884570 1494281 := bstep (se 2 (by rfl) ⟨560355, by rfl⟩ : syracuseStep 1494281 = 1120711) B1120711
theorem B1330511 : Blo 884570 1330511 := bstep (se 1 (by rfl) ⟨997883, by rfl⟩ : syracuseStep 1330511 = 1995767) B1995767
theorem B2837929 : Blo 884570 2837929 := bstep (se 2 (by rfl) ⟨1064223, by rfl⟩ : syracuseStep 2837929 = 2128447) B2128447
theorem B1330601 : Blo 884570 1330601 := bstep (se 2 (by rfl) ⟨498975, by rfl⟩ : syracuseStep 1330601 = 997951) B997951
theorem B1330751 : Blo 884570 1330751 := bstep (se 1 (by rfl) ⟨998063, by rfl⟩ : syracuseStep 1330751 = 1996127) B1996127
theorem B30690893 : Blo 884570 30690893 := bstep (se 3 (by rfl) ⟨5754542, by rfl⟩ : syracuseStep 30690893 = 11509085) B11509085
theorem B5394077 : Blo 884570 5394077 := bstep (se 3 (by rfl) ⟨1011389, by rfl⟩ : syracuseStep 5394077 = 2022779) B2022779
theorem B1331015 : Blo 884570 1331015 := bstep (se 1 (by rfl) ⟨998261, by rfl⟩ : syracuseStep 1331015 = 1996523) B1996523
theorem B2838377 : Blo 884570 2838377 := bstep (se 2 (by rfl) ⟨1064391, by rfl⟩ : syracuseStep 2838377 = 2128783) B2128783
theorem B1331099 : Blo 884570 1331099 := bstep (se 1 (by rfl) ⟨998324, by rfl⟩ : syracuseStep 1331099 = 1996649) B1996649
theorem B1495327 : Blo 884570 1495327 := bstep (se 1 (by rfl) ⟨1121495, by rfl⟩ : syracuseStep 1495327 = 2242991) B2242991
theorem B1331663 : Blo 884570 1331663 := bstep (se 1 (by rfl) ⟨998747, by rfl⟩ : syracuseStep 1331663 = 1997495) B1997495
theorem B1331705 : Blo 884570 1331705 := bstep (se 2 (by rfl) ⟨499389, by rfl⟩ : syracuseStep 1331705 = 998779) B998779
theorem B1331807 : Blo 884570 1331807 := bstep (se 1 (by rfl) ⟨998855, by rfl⟩ : syracuseStep 1331807 = 1997711) B1997711
theorem B3363713 : Blo 884570 3363713 := bstep (se 2 (by rfl) ⟨1261392, by rfl⟩ : syracuseStep 3363713 = 2522785) B2522785
theorem B1495975 : Blo 884570 1495975 := bstep (se 1 (by rfl) ⟨1121981, by rfl⟩ : syracuseStep 1495975 = 2243963) B2243963
theorem B17257475 : Blo 884570 17257475 := bstep (se 1 (by rfl) ⟨12943106, by rfl⟩ : syracuseStep 17257475 = 25886213) B25886213
theorem B2839607 : Blo 884570 2839607 := bstep (se 1 (by rfl) ⟨2129705, by rfl⟩ : syracuseStep 2839607 = 4259411) B4259411
theorem B1332287 : Blo 884570 1332287 := bstep (se 1 (by rfl) ⟨999215, by rfl⟩ : syracuseStep 1332287 = 1998431) B1998431
theorem B1496137 : Blo 884570 1496137 := bstep (se 2 (by rfl) ⟨561051, by rfl⟩ : syracuseStep 1496137 = 1122103) B1122103
theorem B10114145 : Blo 884570 10114145 := bstep (se 2 (by rfl) ⟨3792804, by rfl⟩ : syracuseStep 10114145 = 7585609) B7585609
theorem B1332329 : Blo 884570 1332329 := bstep (se 2 (by rfl) ⟨499623, by rfl⟩ : syracuseStep 1332329 = 999247) B999247
theorem B1496171 : Blo 884570 1496171 := bstep (se 1 (by rfl) ⟨1122128, by rfl⟩ : syracuseStep 1496171 = 2244257) B2244257
theorem B1332431 : Blo 884570 1332431 := bstep (se 1 (by rfl) ⟨999323, by rfl⟩ : syracuseStep 1332431 = 1998647) B1998647
theorem B4478327 : Blo 884570 4478327 := bstep (se 1 (by rfl) ⟨3358745, by rfl⟩ : syracuseStep 4478327 = 6717491) B6717491
theorem B3200411 : Blo 884570 3200411 := bstep (se 1 (by rfl) ⟨2400308, by rfl⟩ : syracuseStep 3200411 = 4800617) B4800617
theorem B1332635 : Blo 884570 1332635 := bstep (se 1 (by rfl) ⟨999476, by rfl⟩ : syracuseStep 1332635 = 1998953) B1998953
theorem B5691053 : Blo 884570 5691053 := bstep (se 3 (by rfl) ⟨1067072, by rfl⟩ : syracuseStep 5691053 = 2134145) B2134145
theorem B23615621 : Blo 884570 23615621 := bstep (se 4 (by rfl) ⟨2213964, by rfl⟩ : syracuseStep 23615621 = 4427929) B4427929
theorem B4479137 : Blo 884570 4479137 := bstep (se 2 (by rfl) ⟨1679676, by rfl⟩ : syracuseStep 4479137 = 3359353) B3359353
theorem B18208961 : Blo 884570 18208961 := bstep (se 2 (by rfl) ⟨6828360, by rfl⟩ : syracuseStep 18208961 = 13656721) B13656721
theorem B12802333 : Blo 884570 12802333 := bstep (se 3 (by rfl) ⟨2400437, by rfl⟩ : syracuseStep 12802333 = 4800875) B4800875
theorem B1497467 : Blo 884570 1497467 := bstep (se 1 (by rfl) ⟨1123100, by rfl⟩ : syracuseStep 1497467 = 2246201) B2246201
theorem B1497737 : Blo 884570 1497737 := bstep (se 2 (by rfl) ⟨561651, by rfl⟩ : syracuseStep 1497737 = 1123303) B1123303
theorem B4545505 : Blo 884570 4545505 := bstep (se 2 (by rfl) ⟨1704564, by rfl⟩ : syracuseStep 4545505 = 3409129) B3409129
theorem B1596457 : Blo 884570 1596457 := bstep (se 2 (by rfl) ⟨598671, by rfl⟩ : syracuseStep 1596457 = 1197343) B1197343
theorem B15129665 : Blo 884570 15129665 := bstep (se 2 (by rfl) ⟨5673624, by rfl⟩ : syracuseStep 15129665 = 11347249) B11347249
theorem B2842067 : Blo 884570 2842067 := bstep (se 1 (by rfl) ⟨2131550, by rfl⟩ : syracuseStep 2842067 = 4263101) B4263101
theorem B3366643 : Blo 884570 3366643 := bstep (se 1 (by rfl) ⟨2524982, by rfl⟩ : syracuseStep 3366643 = 5049965) B5049965
theorem B1499323 : Blo 884570 1499323 := bstep (se 1 (by rfl) ⟨1124492, by rfl⟩ : syracuseStep 1499323 = 2248985) B2248985
theorem B4481243 : Blo 884570 4481243 := bstep (se 1 (by rfl) ⟨3360932, by rfl⟩ : syracuseStep 4481243 = 6721865) B6721865
theorem B1990943 : Blo 884570 1990943 := bstep (se 1 (by rfl) ⟨1493207, by rfl⟩ : syracuseStep 1990943 = 2986415) B2986415
theorem B4481405 : Blo 884570 4481405 := bstep (se 3 (by rfl) ⟨840263, by rfl⟩ : syracuseStep 4481405 = 1680527) B1680527
theorem B9593275 : Blo 884570 9593275 := bstep (se 1 (by rfl) ⟨7194956, by rfl⟩ : syracuseStep 9593275 = 14389913) B14389913
theorem B3793661 : Blo 884570 3793661 := bstep (se 3 (by rfl) ⟨711311, by rfl⟩ : syracuseStep 3793661 = 1422623) B1422623
theorem B1991591 : Blo 884570 1991591 := bstep (se 1 (by rfl) ⟨1493693, by rfl⟩ : syracuseStep 1991591 = 2987387) B2987387
theorem B3794651 : Blo 884570 3794651 := bstep (se 1 (by rfl) ⟨2845988, by rfl⟩ : syracuseStep 3794651 = 5691977) B5691977
theorem B4384543 : Blo 884570 4384543 := bstep (se 1 (by rfl) ⟨3288407, by rfl⟩ : syracuseStep 4384543 = 6576815) B6576815
theorem B1992527 : Blo 884570 1992527 := bstep (se 1 (by rfl) ⟨1494395, by rfl⟩ : syracuseStep 1992527 = 2988791) B2988791
theorem B1992545 : Blo 884570 1992545 := bstep (se 2 (by rfl) ⟨747204, by rfl⟩ : syracuseStep 1992545 = 1494409) B1494409
theorem B41019281 : Blo 884570 41019281 := bstep (se 2 (by rfl) ⟨15382230, by rfl⟩ : syracuseStep 41019281 = 30764461) B30764461
theorem B1009967 : Blo 884570 1009967 := bstep (se 1 (by rfl) ⟨757475, by rfl⟩ : syracuseStep 1009967 = 1514951) B1514951
theorem B1993121 : Blo 884570 1993121 := bstep (se 2 (by rfl) ⟨747420, by rfl⟩ : syracuseStep 1993121 = 1494841) B1494841
theorem B3369377 : Blo 884570 3369377 := bstep (se 2 (by rfl) ⟨1263516, by rfl⟩ : syracuseStep 3369377 = 2527033) B2527033
theorem B1993247 : Blo 884570 1993247 := bstep (se 1 (by rfl) ⟨1494935, by rfl⟩ : syracuseStep 1993247 = 2989871) B2989871
theorem B3370031 : Blo 884570 3370031 := bstep (se 1 (by rfl) ⟨2527523, by rfl⟩ : syracuseStep 3370031 = 5055047) B5055047
theorem B3370349 : Blo 884570 3370349 := bstep (se 3 (by rfl) ⟨631940, by rfl⟩ : syracuseStep 3370349 = 1263881) B1263881
theorem B7564697 : Blo 884570 7564697 := bstep (se 2 (by rfl) ⟨2836761, by rfl⟩ : syracuseStep 7564697 = 5673523) B5673523
theorem B7565075 : Blo 884570 7565075 := bstep (se 1 (by rfl) ⟨5673806, by rfl⟩ : syracuseStep 7565075 = 11347613) B11347613
theorem B2846603 : Blo 884570 2846603 := bstep (se 1 (by rfl) ⟨2134952, by rfl⟩ : syracuseStep 2846603 = 4269905) B4269905
theorem B1994651 : Blo 884570 1994651 := bstep (se 1 (by rfl) ⟨1495988, by rfl⟩ : syracuseStep 1994651 = 2991977) B2991977
theorem B1994939 : Blo 884570 1994939 := bstep (se 1 (by rfl) ⟨1496204, by rfl⟩ : syracuseStep 1994939 = 2992409) B2992409
theorem B11366729 : Blo 884570 11366729 := bstep (se 2 (by rfl) ⟨4262523, by rfl⟩ : syracuseStep 11366729 = 8525047) B8525047
theorem B3830287 : Blo 884570 3830287 := bstep (se 1 (by rfl) ⟨2872715, by rfl⟩ : syracuseStep 3830287 = 5745431) B5745431
theorem B1995425 : Blo 884570 1995425 := bstep (se 2 (by rfl) ⟨748284, by rfl⟩ : syracuseStep 1995425 = 1496569) B1496569
theorem B1897121 : Blo 884570 1897121 := bstep (se 2 (by rfl) ⟨711420, by rfl⟩ : syracuseStep 1897121 = 1422841) B1422841
theorem B1995785 : Blo 884570 1995785 := bstep (se 2 (by rfl) ⟨748419, by rfl⟩ : syracuseStep 1995785 = 1496839) B1496839
theorem B1995839 : Blo 884570 1995839 := bstep (se 1 (by rfl) ⟨1496879, by rfl⟩ : syracuseStep 1995839 = 2993759) B2993759
theorem B1799275 : Blo 884570 1799275 := bstep (se 1 (by rfl) ⟨1349456, by rfl⟩ : syracuseStep 1799275 = 2698913) B2698913
theorem B48592223 : Blo 884570 48592223 := bstep (se 1 (by rfl) ⟨36444167, by rfl⟩ : syracuseStep 48592223 = 72888335) B72888335
theorem B3372779 : Blo 884570 3372779 := bstep (se 1 (by rfl) ⟨2529584, by rfl⟩ : syracuseStep 3372779 = 5059169) B5059169
theorem B1996775 : Blo 884570 1996775 := bstep (se 1 (by rfl) ⟨1497581, by rfl⟩ : syracuseStep 1996775 = 2995163) B2995163
theorem B1996793 : Blo 884570 1996793 := bstep (se 2 (by rfl) ⟨748797, by rfl⟩ : syracuseStep 1996793 = 1497595) B1497595
theorem B1996883 : Blo 884570 1996883 := bstep (se 1 (by rfl) ⟨1497662, by rfl⟩ : syracuseStep 1996883 = 2995325) B2995325
theorem B1996955 : Blo 884570 1996955 := bstep (se 1 (by rfl) ⟨1497716, by rfl⟩ : syracuseStep 1996955 = 2995433) B2995433
theorem B43645105 : Blo 884570 43645105 := bstep (se 2 (by rfl) ⟨16366914, by rfl⟩ : syracuseStep 43645105 = 32733829) B32733829
theorem B9599153 : Blo 884570 9599153 := bstep (se 2 (by rfl) ⟨3599682, by rfl⟩ : syracuseStep 9599153 = 7199365) B7199365
theorem B1997063 : Blo 884570 1997063 := bstep (se 1 (by rfl) ⟨1497797, by rfl⟩ : syracuseStep 1997063 = 2995595) B2995595
theorem B5044589 : Blo 884570 5044589 := bstep (se 3 (by rfl) ⟨945860, by rfl⟩ : syracuseStep 5044589 = 1891721) B1891721
theorem B1997369 : Blo 884570 1997369 := bstep (se 2 (by rfl) ⟨749013, by rfl⟩ : syracuseStep 1997369 = 1498027) B1498027
theorem B3373721 : Blo 884570 3373721 := bstep (se 2 (by rfl) ⟨1265145, by rfl⟩ : syracuseStep 3373721 = 2530291) B2530291
theorem B3242911 : Blo 884570 3242911 := bstep (se 1 (by rfl) ⟨2432183, by rfl⟩ : syracuseStep 3242911 = 4864367) B4864367
theorem B4324423 : Blo 884570 4324423 := bstep (se 1 (by rfl) ⟨3243317, by rfl⟩ : syracuseStep 4324423 = 6486635) B6486635
theorem B1998089 : Blo 884570 1998089 := bstep (se 2 (by rfl) ⟨749283, by rfl⟩ : syracuseStep 1998089 = 1498567) B1498567
theorem B5767037 : Blo 884570 5767037 := bstep (se 3 (by rfl) ⟨1081319, by rfl⟩ : syracuseStep 5767037 = 2162639) B2162639
theorem B884703 : Blo 884570 884703 := bstep (se 1 (by rfl) ⟨663527, by rfl⟩ : syracuseStep 884703 = 1327055) B1327055
theorem B7274681 : Blo 884570 7274681 := bstep (se 2 (by rfl) ⟨2728005, by rfl⟩ : syracuseStep 7274681 = 5456011) B5456011
theorem B2162875 : Blo 884570 2162875 := bstep (se 1 (by rfl) ⟨1622156, by rfl⟩ : syracuseStep 2162875 = 3244313) B3244313
theorem B884927 : Blo 884570 884927 := bstep (se 1 (by rfl) ⟨663695, by rfl⟩ : syracuseStep 884927 = 1327391) B1327391
theorem B884943 : Blo 884570 884943 := bstep (se 1 (by rfl) ⟨663707, by rfl⟩ : syracuseStep 884943 = 1327415) B1327415
theorem B1999097 : Blo 884570 1999097 := bstep (se 2 (by rfl) ⟨749661, by rfl⟩ : syracuseStep 1999097 = 1499323) B1499323
theorem B884991 : Blo 884570 884991 := bstep (se 1 (by rfl) ⟨663743, by rfl⟩ : syracuseStep 884991 = 1327487) B1327487
theorem B885039 : Blo 884570 885039 := bstep (se 1 (by rfl) ⟨663779, by rfl⟩ : syracuseStep 885039 = 1327559) B1327559
theorem B1999151 : Blo 884570 1999151 := bstep (se 1 (by rfl) ⟨1499363, by rfl⟩ : syracuseStep 1999151 = 2998727) B2998727
theorem B6390209 : Blo 884570 6390209 := bstep (se 2 (by rfl) ⟨2396328, by rfl⟩ : syracuseStep 6390209 = 4792657) B4792657
theorem B885275 : Blo 884570 885275 := bstep (se 1 (by rfl) ⟨663956, by rfl⟩ : syracuseStep 885275 = 1327913) B1327913
theorem B885279 : Blo 884570 885279 := bstep (se 1 (by rfl) ⟨663959, by rfl⟩ : syracuseStep 885279 = 1327919) B1327919
theorem B885359 : Blo 884570 885359 := bstep (se 1 (by rfl) ⟨664019, by rfl⟩ : syracuseStep 885359 = 1328039) B1328039
theorem B885415 : Blo 884570 885415 := bstep (se 1 (by rfl) ⟨664061, by rfl⟩ : syracuseStep 885415 = 1328123) B1328123
theorem B885455 : Blo 884570 885455 := bstep (se 1 (by rfl) ⟨664091, by rfl⟩ : syracuseStep 885455 = 1328183) B1328183
theorem B885535 : Blo 884570 885535 := bstep (se 1 (by rfl) ⟨664151, by rfl⟩ : syracuseStep 885535 = 1328303) B1328303
theorem B885807 : Blo 884570 885807 := bstep (se 1 (by rfl) ⟨664355, by rfl⟩ : syracuseStep 885807 = 1328711) B1328711
theorem B885871 : Blo 884570 885871 := bstep (se 1 (by rfl) ⟨664403, by rfl⟩ : syracuseStep 885871 = 1328807) B1328807
theorem B885927 : Blo 884570 885927 := bstep (se 1 (by rfl) ⟨664445, by rfl⟩ : syracuseStep 885927 = 1328891) B1328891
theorem B885951 : Blo 884570 885951 := bstep (se 1 (by rfl) ⟨664463, by rfl⟩ : syracuseStep 885951 = 1328927) B1328927
theorem B5047505 : Blo 884570 5047505 := bstep (se 2 (by rfl) ⟨1892814, by rfl⟩ : syracuseStep 5047505 = 3785629) B3785629
theorem B885983 : Blo 884570 885983 := bstep (se 1 (by rfl) ⟨664487, by rfl⟩ : syracuseStep 885983 = 1328975) B1328975
theorem B886063 : Blo 884570 886063 := bstep (se 1 (by rfl) ⟨664547, by rfl⟩ : syracuseStep 886063 = 1329095) B1329095
theorem B886299 : Blo 884570 886299 := bstep (se 1 (by rfl) ⟨664724, by rfl⟩ : syracuseStep 886299 = 1329449) B1329449
theorem B886303 : Blo 884570 886303 := bstep (se 1 (by rfl) ⟨664727, by rfl⟩ : syracuseStep 886303 = 1329455) B1329455
theorem B9209389 : Blo 884570 9209389 := bstep (se 3 (by rfl) ⟨1726760, by rfl⟩ : syracuseStep 9209389 = 3453521) B3453521
theorem B886463 : Blo 884570 886463 := bstep (se 1 (by rfl) ⟨664847, by rfl⟩ : syracuseStep 886463 = 1329695) B1329695
theorem B886719 : Blo 884570 886719 := bstep (se 1 (by rfl) ⟨665039, by rfl⟩ : syracuseStep 886719 = 1330079) B1330079
theorem B886751 : Blo 884570 886751 := bstep (se 1 (by rfl) ⟨665063, by rfl⟩ : syracuseStep 886751 = 1330127) B1330127
theorem B4261871 : Blo 884570 4261871 := bstep (se 1 (by rfl) ⟨3196403, by rfl⟩ : syracuseStep 4261871 = 6392807) B6392807
theorem B886811 : Blo 884570 886811 := bstep (se 1 (by rfl) ⟨665108, by rfl⟩ : syracuseStep 886811 = 1330217) B1330217
theorem B886815 : Blo 884570 886815 := bstep (se 1 (by rfl) ⟨665111, by rfl⟩ : syracuseStep 886815 = 1330223) B1330223
theorem B886831 : Blo 884570 886831 := bstep (se 1 (by rfl) ⟨665123, by rfl⟩ : syracuseStep 886831 = 1330247) B1330247
theorem B5048507 : Blo 884570 5048507 := bstep (se 1 (by rfl) ⟨3786380, by rfl⟩ : syracuseStep 5048507 = 7572761) B7572761
theorem B887007 : Blo 884570 887007 := bstep (se 1 (by rfl) ⟨665255, by rfl⟩ : syracuseStep 887007 = 1330511) B1330511
theorem B887067 : Blo 884570 887067 := bstep (se 1 (by rfl) ⟨665300, by rfl⟩ : syracuseStep 887067 = 1330601) B1330601
theorem B887167 : Blo 884570 887167 := bstep (se 1 (by rfl) ⟨665375, by rfl⟩ : syracuseStep 887167 = 1330751) B1330751
theorem B887343 : Blo 884570 887343 := bstep (se 1 (by rfl) ⟨665507, by rfl⟩ : syracuseStep 887343 = 1331015) B1331015
theorem B887399 : Blo 884570 887399 := bstep (se 1 (by rfl) ⟨665549, by rfl⟩ : syracuseStep 887399 = 1331099) B1331099
theorem B887775 : Blo 884570 887775 := bstep (se 1 (by rfl) ⟨665831, by rfl⟩ : syracuseStep 887775 = 1331663) B1331663
theorem B887803 : Blo 884570 887803 := bstep (se 1 (by rfl) ⟨665852, by rfl⟩ : syracuseStep 887803 = 1331705) B1331705
theorem B887871 : Blo 884570 887871 := bstep (se 1 (by rfl) ⟨665903, by rfl⟩ : syracuseStep 887871 = 1331807) B1331807
theorem B888191 : Blo 884570 888191 := bstep (se 1 (by rfl) ⟨666143, by rfl⟩ : syracuseStep 888191 = 1332287) B1332287
theorem B888219 : Blo 884570 888219 := bstep (se 1 (by rfl) ⟨666164, by rfl⟩ : syracuseStep 888219 = 1332329) B1332329
theorem B888287 : Blo 884570 888287 := bstep (se 1 (by rfl) ⟨666215, by rfl⟩ : syracuseStep 888287 = 1332431) B1332431
theorem B2985551 : Blo 884570 2985551 := bstep (se 1 (by rfl) ⟨2239163, by rfl⟩ : syracuseStep 2985551 = 4478327) B4478327
theorem B2133607 : Blo 884570 2133607 := bstep (se 1 (by rfl) ⟨1600205, by rfl⟩ : syracuseStep 2133607 = 3200411) B3200411
theorem B888423 : Blo 884570 888423 := bstep (se 1 (by rfl) ⟨666317, by rfl⟩ : syracuseStep 888423 = 1332635) B1332635
theorem B2986091 : Blo 884570 2986091 := bstep (se 1 (by rfl) ⟨2239568, by rfl⟩ : syracuseStep 2986091 = 4479137) B4479137
theorem B2986145 : Blo 884570 2986145 := bstep (se 2 (by rfl) ⟨1119804, by rfl⟩ : syracuseStep 2986145 = 2239609) B2239609
theorem B96932213 : Blo 884570 96932213 := bstep (se 5 (by rfl) ⟨4543697, by rfl⟩ : syracuseStep 96932213 = 9087395) B9087395
theorem B17306723 : Blo 884570 17306723 := bstep (se 1 (by rfl) ⟨12980042, by rfl⟩ : syracuseStep 17306723 = 25960085) B25960085
theorem B2987495 : Blo 884570 2987495 := bstep (se 1 (by rfl) ⟨2240621, by rfl⟩ : syracuseStep 2987495 = 4481243) B4481243
theorem B2987603 : Blo 884570 2987603 := bstep (se 1 (by rfl) ⟨2240702, by rfl⟩ : syracuseStep 2987603 = 4481405) B4481405
theorem B25597741 : Blo 884570 25597741 := bstep (se 3 (by rfl) ⟨4799576, by rfl⟩ : syracuseStep 25597741 = 9599153) B9599153
theorem B2529107 : Blo 884570 2529107 := bstep (se 1 (by rfl) ⟨1896830, by rfl⟩ : syracuseStep 2529107 = 3793661) B3793661
theorem B2987873 : Blo 884570 2987873 := bstep (se 2 (by rfl) ⟨1120452, by rfl⟩ : syracuseStep 2987873 = 2240905) B2240905
theorem B1120159 : Blo 884570 1120159 := bstep (se 1 (by rfl) ⟨840119, by rfl⟩ : syracuseStep 1120159 = 1680239) B1680239
theorem B2693245 : Blo 884570 2693245 := bstep (se 3 (by rfl) ⟨504983, by rfl⟩ : syracuseStep 2693245 = 1009967) B1009967
theorem B7280765 : Blo 884570 7280765 := bstep (se 3 (by rfl) ⟨1365143, by rfl⟩ : syracuseStep 7280765 = 2730287) B2730287
theorem B4855945 : Blo 884570 4855945 := bstep (se 2 (by rfl) ⟨1820979, by rfl⟩ : syracuseStep 4855945 = 3641959) B3641959
theorem B2529767 : Blo 884570 2529767 := bstep (se 1 (by rfl) ⟨1897325, by rfl⟩ : syracuseStep 2529767 = 3794651) B3794651
theorem B2399033 : Blo 884570 2399033 := bstep (se 2 (by rfl) ⟨899637, by rfl⟩ : syracuseStep 2399033 = 1799275) B1799275
theorem B7577819 : Blo 884570 7577819 := bstep (se 1 (by rfl) ⟨5683364, by rfl⟩ : syracuseStep 7577819 = 11366729) B11366729
theorem B1679753 : Blo 884570 1679753 := bstep (se 2 (by rfl) ⟨629907, by rfl⟩ : syracuseStep 1679753 = 1259815) B1259815
theorem B19407559 : Blo 884570 19407559 := bstep (se 1 (by rfl) ⟨14555669, by rfl⟩ : syracuseStep 19407559 = 29111339) B29111339
theorem B7578845 : Blo 884570 7578845 := bstep (se 3 (by rfl) ⟨1421033, by rfl⟩ : syracuseStep 7578845 = 2842067) B2842067
theorem B15344963 : Blo 884570 15344963 := bstep (se 1 (by rfl) ⟨11508722, by rfl⟩ : syracuseStep 15344963 = 23017445) B23017445
theorem B3844691 : Blo 884570 3844691 := bstep (se 1 (by rfl) ⟨2883518, by rfl⟩ : syracuseStep 3844691 = 5767037) B5767037
theorem B1682183 : Blo 884570 1682183 := bstep (se 1 (by rfl) ⟨1261637, by rfl⟩ : syracuseStep 1682183 = 2523275) B2523275
theorem B2239559 : Blo 884570 2239559 := bstep (se 1 (by rfl) ⟨1679669, by rfl⟩ : syracuseStep 2239559 = 3359339) B3359339
theorem B12791033 : Blo 884570 12791033 := bstep (se 2 (by rfl) ⟨4796637, by rfl⟩ : syracuseStep 12791033 = 9593275) B9593275
theorem B1682707 : Blo 884570 1682707 := bstep (se 1 (by rfl) ⟨1262030, by rfl⟩ : syracuseStep 1682707 = 2524061) B2524061
theorem B10235335 : Blo 884570 10235335 := bstep (se 1 (by rfl) ⟨7676501, by rfl⟩ : syracuseStep 10235335 = 15353003) B15353003
theorem B14364479 : Blo 884570 14364479 := bstep (se 1 (by rfl) ⟨10773359, by rfl⟩ : syracuseStep 14364479 = 21546719) B21546719
theorem B1683337 : Blo 884570 1683337 := bstep (se 2 (by rfl) ⟨631251, by rfl⟩ : syracuseStep 1683337 = 1262503) B1262503
theorem B995323 : Blo 884570 995323 := bstep (se 1 (by rfl) ⟨746492, by rfl⟩ : syracuseStep 995323 = 1492985) B1492985
theorem B995431 : Blo 884570 995431 := bstep (se 1 (by rfl) ⟨746573, by rfl⟩ : syracuseStep 995431 = 1493147) B1493147
theorem B995503 : Blo 884570 995503 := bstep (se 1 (by rfl) ⟨746627, by rfl⟩ : syracuseStep 995503 = 1493255) B1493255
theorem B2240743 : Blo 884570 2240743 := bstep (se 1 (by rfl) ⟨1680557, by rfl⟩ : syracuseStep 2240743 = 3361115) B3361115
theorem B2994407 : Blo 884570 2994407 := bstep (se 1 (by rfl) ⟨2245805, by rfl⟩ : syracuseStep 2994407 = 4491611) B4491611
theorem B15380921 : Blo 884570 15380921 := bstep (se 2 (by rfl) ⟨5767845, by rfl⟩ : syracuseStep 15380921 = 11535691) B11535691
theorem B11809223 : Blo 884570 11809223 := bstep (se 1 (by rfl) ⟨8856917, by rfl⟩ : syracuseStep 11809223 = 17713835) B17713835
theorem B996187 : Blo 884570 996187 := bstep (se 1 (by rfl) ⟨747140, by rfl⟩ : syracuseStep 996187 = 1494281) B1494281
theorem B5846057 : Blo 884570 5846057 := bstep (se 2 (by rfl) ⟨2192271, by rfl⟩ : syracuseStep 5846057 = 4384543) B4384543
theorem B20460595 : Blo 884570 20460595 := bstep (se 1 (by rfl) ⟨15345446, by rfl⟩ : syracuseStep 20460595 = 30690893) B30690893
theorem B2995271 : Blo 884570 2995271 := bstep (se 1 (by rfl) ⟨2246453, by rfl⟩ : syracuseStep 2995271 = 4492907) B4492907
theorem B2241665 : Blo 884570 2241665 := bstep (se 2 (by rfl) ⟨840624, by rfl⟩ : syracuseStep 2241665 = 1681249) B1681249
theorem B46019933 : Blo 884570 46019933 := bstep (se 3 (by rfl) ⟨8628737, by rfl⟩ : syracuseStep 46019933 = 17257475) B17257475
theorem B7583219 : Blo 884570 7583219 := bstep (se 1 (by rfl) ⟨5687414, by rfl⟩ : syracuseStep 7583219 = 11374829) B11374829
theorem B3782315 : Blo 884570 3782315 := bstep (se 1 (by rfl) ⟨2836736, by rfl⟩ : syracuseStep 3782315 = 5673473) B5673473
theorem B2242475 : Blo 884570 2242475 := bstep (se 1 (by rfl) ⟨1681856, by rfl⟩ : syracuseStep 2242475 = 3363713) B3363713
theorem B997447 : Blo 884570 997447 := bstep (se 1 (by rfl) ⟨748085, by rfl⟩ : syracuseStep 997447 = 1496171) B1496171
theorem B2996459 : Blo 884570 2996459 := bstep (se 1 (by rfl) ⟨2247344, by rfl⟩ : syracuseStep 2996459 = 4494689) B4494689
theorem B15743747 : Blo 884570 15743747 := bstep (se 1 (by rfl) ⟨11807810, by rfl⟩ : syracuseStep 15743747 = 23615621) B23615621
theorem B12139307 : Blo 884570 12139307 := bstep (se 1 (by rfl) ⟨9104480, by rfl⟩ : syracuseStep 12139307 = 18208961) B18208961
theorem B998311 : Blo 884570 998311 := bstep (se 1 (by rfl) ⟨748733, by rfl⟩ : syracuseStep 998311 = 1497467) B1497467
theorem B998491 : Blo 884570 998491 := bstep (se 1 (by rfl) ⟨748868, by rfl⟩ : syracuseStep 998491 = 1497737) B1497737
theorem B3783905 : Blo 884570 3783905 := bstep (se 2 (by rfl) ⟨1418964, by rfl⟩ : syracuseStep 3783905 = 2837929) B2837929
theorem B3194099 : Blo 884570 3194099 := bstep (se 1 (by rfl) ⟨2395574, by rfl⟩ : syracuseStep 3194099 = 4791149) B4791149
theorem B6733043 : Blo 884570 6733043 := bstep (se 1 (by rfl) ⟨5049782, by rfl⟩ : syracuseStep 6733043 = 10099565) B10099565
theorem B1326857 : Blo 884570 1326857 := bstep (se 2 (by rfl) ⟨497571, by rfl⟩ : syracuseStep 1326857 = 995143) B995143
theorem B1327295 : Blo 884570 1327295 := bstep (se 1 (by rfl) ⟨995471, by rfl⟩ : syracuseStep 1327295 = 1990943) B1990943
theorem B6734015 : Blo 884570 6734015 := bstep (se 1 (by rfl) ⟨5050511, by rfl⟩ : syracuseStep 6734015 = 10101023) B10101023
theorem B2998781 : Blo 884570 2998781 := bstep (se 3 (by rfl) ⟨562271, by rfl⟩ : syracuseStep 2998781 = 1124543) B1124543
theorem B1327721 : Blo 884570 1327721 := bstep (se 2 (by rfl) ⟨497895, by rfl⟩ : syracuseStep 1327721 = 995791) B995791
theorem B1327727 : Blo 884570 1327727 := bstep (se 1 (by rfl) ⟨995795, by rfl⟩ : syracuseStep 1327727 = 1991591) B1991591
theorem B3785903 : Blo 884570 3785903 := bstep (se 1 (by rfl) ⟨2839427, by rfl⟩ : syracuseStep 3785903 = 5678855) B5678855
theorem B1328351 : Blo 884570 1328351 := bstep (se 1 (by rfl) ⟨996263, by rfl⟩ : syracuseStep 1328351 = 1992527) B1992527
theorem B1328363 : Blo 884570 1328363 := bstep (se 1 (by rfl) ⟨996272, by rfl⟩ : syracuseStep 1328363 = 1992545) B1992545
theorem B27346187 : Blo 884570 27346187 := bstep (se 1 (by rfl) ⟨20509640, by rfl⟩ : syracuseStep 27346187 = 41019281) B41019281
theorem B3032417 : Blo 884570 3032417 := bstep (se 2 (by rfl) ⟨1137156, by rfl⟩ : syracuseStep 3032417 = 2274313) B2274313
theorem B1328747 : Blo 884570 1328747 := bstep (se 1 (by rfl) ⟨996560, by rfl⟩ : syracuseStep 1328747 = 1993121) B1993121
theorem B2246251 : Blo 884570 2246251 := bstep (se 1 (by rfl) ⟨1684688, by rfl⟩ : syracuseStep 2246251 = 3369377) B3369377
theorem B1328831 : Blo 884570 1328831 := bstep (se 1 (by rfl) ⟨996623, by rfl⟩ : syracuseStep 1328831 = 1993247) B1993247
theorem B1329017 : Blo 884570 1329017 := bstep (se 2 (by rfl) ⟨498381, by rfl⟩ : syracuseStep 1329017 = 996763) B996763
theorem B2246687 : Blo 884570 2246687 := bstep (se 1 (by rfl) ⟨1685015, by rfl⟩ : syracuseStep 2246687 = 3370031) B3370031
theorem B2246899 : Blo 884570 2246899 := bstep (se 1 (by rfl) ⟨1685174, by rfl⟩ : syracuseStep 2246899 = 3370349) B3370349
theorem B1493275 : Blo 884570 1493275 := bstep (se 1 (by rfl) ⟨1119956, by rfl⟩ : syracuseStep 1493275 = 2239913) B2239913
theorem B1493417 : Blo 884570 1493417 := bstep (se 2 (by rfl) ⟨560031, by rfl⟩ : syracuseStep 1493417 = 1120063) B1120063
theorem B48548429 : Blo 884570 48548429 := bstep (se 3 (by rfl) ⟨9102830, by rfl⟩ : syracuseStep 48548429 = 18205661) B18205661
theorem B1493599 : Blo 884570 1493599 := bstep (se 1 (by rfl) ⟨1120199, by rfl⟩ : syracuseStep 1493599 = 2240399) B2240399
theorem B1329767 : Blo 884570 1329767 := bstep (se 1 (by rfl) ⟨997325, by rfl⟩ : syracuseStep 1329767 = 1994651) B1994651
theorem B1329959 : Blo 884570 1329959 := bstep (se 1 (by rfl) ⟨997469, by rfl⟩ : syracuseStep 1329959 = 1994939) B1994939
theorem B1494011 : Blo 884570 1494011 := bstep (se 1 (by rfl) ⟨1120508, by rfl⟩ : syracuseStep 1494011 = 2241017) B2241017
theorem B2247689 : Blo 884570 2247689 := bstep (se 2 (by rfl) ⟨842883, by rfl⟩ : syracuseStep 2247689 = 1685767) B1685767
theorem B1330283 : Blo 884570 1330283 := bstep (se 1 (by rfl) ⟨997712, by rfl⟩ : syracuseStep 1330283 = 1995425) B1995425
theorem B1264747 : Blo 884570 1264747 := bstep (se 1 (by rfl) ⟨948560, by rfl⟩ : syracuseStep 1264747 = 1897121) B1897121
theorem B10800317 : Blo 884570 10800317 := bstep (se 3 (by rfl) ⟨2025059, by rfl⟩ : syracuseStep 10800317 = 4050119) B4050119
theorem B1330523 : Blo 884570 1330523 := bstep (se 1 (by rfl) ⟨997892, by rfl⟩ : syracuseStep 1330523 = 1995785) B1995785
theorem B1330553 : Blo 884570 1330553 := bstep (se 2 (by rfl) ⟨498957, by rfl⟩ : syracuseStep 1330553 = 997915) B997915
theorem B1330559 : Blo 884570 1330559 := bstep (se 1 (by rfl) ⟨997919, by rfl⟩ : syracuseStep 1330559 = 1995839) B1995839
theorem B3788279 : Blo 884570 3788279 := bstep (se 1 (by rfl) ⟨2841209, by rfl⟩ : syracuseStep 3788279 = 5682419) B5682419
theorem B32394815 : Blo 884570 32394815 := bstep (se 1 (by rfl) ⟨24296111, by rfl⟩ : syracuseStep 32394815 = 48592223) B48592223
theorem B2248519 : Blo 884570 2248519 := bstep (se 1 (by rfl) ⟨1686389, by rfl⟩ : syracuseStep 2248519 = 3372779) B3372779
theorem B12767159 : Blo 884570 12767159 := bstep (se 1 (by rfl) ⟨9575369, by rfl⟩ : syracuseStep 12767159 = 19150739) B19150739
theorem B1331183 : Blo 884570 1331183 := bstep (se 1 (by rfl) ⟨998387, by rfl⟩ : syracuseStep 1331183 = 1996775) B1996775
theorem B1331195 : Blo 884570 1331195 := bstep (se 1 (by rfl) ⟨998396, by rfl⟩ : syracuseStep 1331195 = 1996793) B1996793
theorem B1331255 : Blo 884570 1331255 := bstep (se 1 (by rfl) ⟨998441, by rfl⟩ : syracuseStep 1331255 = 1996883) B1996883
theorem B1331303 : Blo 884570 1331303 := bstep (se 1 (by rfl) ⟨998477, by rfl⟩ : syracuseStep 1331303 = 1996955) B1996955
theorem B1331375 : Blo 884570 1331375 := bstep (se 1 (by rfl) ⟨998531, by rfl⟩ : syracuseStep 1331375 = 1997063) B1997063
theorem B3363059 : Blo 884570 3363059 := bstep (se 1 (by rfl) ⟨2522294, by rfl⟩ : syracuseStep 3363059 = 5044589) B5044589
theorem B1331579 : Blo 884570 1331579 := bstep (se 1 (by rfl) ⟨998684, by rfl⟩ : syracuseStep 1331579 = 1997369) B1997369
theorem B2249147 : Blo 884570 2249147 := bstep (se 1 (by rfl) ⟨1686860, by rfl⟩ : syracuseStep 2249147 = 3373721) B3373721
theorem B1331849 : Blo 884570 1331849 := bstep (se 2 (by rfl) ⟨499443, by rfl⟩ : syracuseStep 1331849 = 998887) B998887
theorem B1332059 : Blo 884570 1332059 := bstep (se 1 (by rfl) ⟨999044, by rfl⟩ : syracuseStep 1332059 = 1998089) B1998089
theorem B7590941 : Blo 884570 7590941 := bstep (se 3 (by rfl) ⟨1423301, by rfl⟩ : syracuseStep 7590941 = 2846603) B2846603
theorem B3200123 : Blo 884570 3200123 := bstep (se 1 (by rfl) ⟨2400092, by rfl⟩ : syracuseStep 3200123 = 4800185) B4800185
theorem B1332521 : Blo 884570 1332521 := bstep (se 2 (by rfl) ⟨499695, by rfl⟩ : syracuseStep 1332521 = 999391) B999391
theorem B1332719 : Blo 884570 1332719 := bstep (se 1 (by rfl) ⟨999539, by rfl⟩ : syracuseStep 1332719 = 1999079) B1999079
theorem B15324731 : Blo 884570 15324731 := bstep (se 1 (by rfl) ⟨11493548, by rfl⟩ : syracuseStep 15324731 = 22987097) B22987097
theorem B1496731 : Blo 884570 1496731 := bstep (se 1 (by rfl) ⟨1122548, by rfl⟩ : syracuseStep 1496731 = 2245097) B2245097
theorem B2840231 : Blo 884570 2840231 := bstep (se 1 (by rfl) ⟨2130173, by rfl⟩ : syracuseStep 2840231 = 4260347) B4260347
theorem B8509207 : Blo 884570 8509207 := bstep (se 1 (by rfl) ⟨6381905, by rfl⟩ : syracuseStep 8509207 = 12763811) B12763811
theorem B3364699 : Blo 884570 3364699 := bstep (se 1 (by rfl) ⟨2523524, by rfl⟩ : syracuseStep 3364699 = 5047049) B5047049
theorem B3037331 : Blo 884570 3037331 := bstep (se 1 (by rfl) ⟨2277998, by rfl⟩ : syracuseStep 3037331 = 4555997) B4555997
theorem B5527723 : Blo 884570 5527723 := bstep (se 1 (by rfl) ⟨4145792, by rfl⟩ : syracuseStep 5527723 = 8291585) B8291585
theorem B331897175 : Blo 884570 331897175 := bstep (se 1 (by rfl) ⟨248922881, by rfl⟩ : syracuseStep 331897175 = 497845763) B497845763
theorem B6740333 : Blo 884570 6740333 := bstep (se 3 (by rfl) ⟨1263812, by rfl⟩ : syracuseStep 6740333 = 2527625) B2527625
theorem B1497575 : Blo 884570 1497575 := bstep (se 1 (by rfl) ⟨1123181, by rfl⟩ : syracuseStep 1497575 = 2246363) B2246363
theorem B3201563 : Blo 884570 3201563 := bstep (se 1 (by rfl) ⟨2401172, by rfl⟩ : syracuseStep 3201563 = 4802345) B4802345
theorem B5397191 : Blo 884570 5397191 := bstep (se 1 (by rfl) ⟨4047893, by rfl⟩ : syracuseStep 5397191 = 8095787) B8095787
theorem B26270569 : Blo 884570 26270569 := bstep (se 2 (by rfl) ⟨9851463, by rfl⟩ : syracuseStep 26270569 = 19702927) B19702927
theorem B1498439 : Blo 884570 1498439 := bstep (se 1 (by rfl) ⟨1123829, by rfl⟩ : syracuseStep 1498439 = 2247659) B2247659
theorem B1498601 : Blo 884570 1498601 := bstep (se 2 (by rfl) ⟨561975, by rfl⟩ : syracuseStep 1498601 = 1123951) B1123951
theorem B3596051 : Blo 884570 3596051 := bstep (se 1 (by rfl) ⟨2697038, by rfl⟩ : syracuseStep 3596051 = 5394077) B5394077
theorem B1990511 : Blo 884570 1990511 := bstep (se 1 (by rfl) ⟨1492883, by rfl⟩ : syracuseStep 1990511 = 2985767) B2985767
theorem B1892251 : Blo 884570 1892251 := bstep (se 1 (by rfl) ⟨1419188, by rfl⟩ : syracuseStep 1892251 = 2838377) B2838377
theorem B1991195 : Blo 884570 1991195 := bstep (se 1 (by rfl) ⟨1493396, by rfl⟩ : syracuseStep 1991195 = 2986793) B2986793
theorem B1991375 : Blo 884570 1991375 := bstep (se 1 (by rfl) ⟨1493531, by rfl⟩ : syracuseStep 1991375 = 2987063) B2987063
theorem B1893071 : Blo 884570 1893071 := bstep (se 1 (by rfl) ⟨1419803, by rfl⟩ : syracuseStep 1893071 = 2839607) B2839607
theorem B6742763 : Blo 884570 6742763 := bstep (se 1 (by rfl) ⟨5057072, by rfl⟩ : syracuseStep 6742763 = 10114145) B10114145
theorem B1991753 : Blo 884570 1991753 := bstep (se 2 (by rfl) ⟨746907, by rfl⟩ : syracuseStep 1991753 = 1493815) B1493815
theorem B3794035 : Blo 884570 3794035 := bstep (se 1 (by rfl) ⟨2845526, by rfl⟩ : syracuseStep 3794035 = 5691053) B5691053
theorem B7693541 : Blo 884570 7693541 := bstep (se 4 (by rfl) ⟨721269, by rfl⟩ : syracuseStep 7693541 = 1442539) B1442539
theorem B3368573 : Blo 884570 3368573 := bstep (se 3 (by rfl) ⟨631607, by rfl⟩ : syracuseStep 3368573 = 1263215) B1263215
theorem B3368861 : Blo 884570 3368861 := bstep (se 3 (by rfl) ⟨631661, by rfl⟩ : syracuseStep 3368861 = 1263323) B1263323
theorem B1992671 : Blo 884570 1992671 := bstep (se 1 (by rfl) ⟨1494503, by rfl⟩ : syracuseStep 1992671 = 2989007) B2989007
theorem B10086443 : Blo 884570 10086443 := bstep (se 1 (by rfl) ⟨7564832, by rfl⟩ : syracuseStep 10086443 = 15129665) B15129665
theorem B1993679 : Blo 884570 1993679 := bstep (se 1 (by rfl) ⟨1495259, by rfl⟩ : syracuseStep 1993679 = 2990519) B2990519
theorem B1993769 : Blo 884570 1993769 := bstep (se 2 (by rfl) ⟨747663, by rfl⟩ : syracuseStep 1993769 = 1495327) B1495327
theorem B1994003 : Blo 884570 1994003 := bstep (se 1 (by rfl) ⟨1495502, by rfl⟩ : syracuseStep 1994003 = 2991005) B2991005
theorem B1994039 : Blo 884570 1994039 := bstep (se 1 (by rfl) ⟨1495529, by rfl⟩ : syracuseStep 1994039 = 2991059) B2991059
theorem B5107049 : Blo 884570 5107049 := bstep (se 2 (by rfl) ⟨1915143, by rfl⟩ : syracuseStep 5107049 = 3830287) B3830287
theorem B1994633 : Blo 884570 1994633 := bstep (se 2 (by rfl) ⟨747987, by rfl⟩ : syracuseStep 1994633 = 1495975) B1495975
theorem B7303085 : Blo 884570 7303085 := bstep (se 3 (by rfl) ⟨1369328, by rfl⟩ : syracuseStep 7303085 = 2738657) B2738657
theorem B1994849 : Blo 884570 1994849 := bstep (se 2 (by rfl) ⟨748068, by rfl⟩ : syracuseStep 1994849 = 1496137) B1496137
theorem B1995515 : Blo 884570 1995515 := bstep (se 1 (by rfl) ⟨1496636, by rfl⟩ : syracuseStep 1995515 = 2993273) B2993273
theorem B5043131 : Blo 884570 5043131 := bstep (se 1 (by rfl) ⟨3782348, by rfl⟩ : syracuseStep 5043131 = 7564697) B7564697
theorem B1995731 : Blo 884570 1995731 := bstep (se 1 (by rfl) ⟨1496798, by rfl⟩ : syracuseStep 1995731 = 2993597) B2993597
theorem B5043383 : Blo 884570 5043383 := bstep (se 1 (by rfl) ⟨3782537, by rfl⟩ : syracuseStep 5043383 = 7565075) B7565075
theorem B184251743 : Blo 884570 184251743 := bstep (se 1 (by rfl) ⟨138188807, by rfl⟩ : syracuseStep 184251743 = 276377615) B276377615
theorem B1996199 : Blo 884570 1996199 := bstep (se 1 (by rfl) ⟨1497149, by rfl⟩ : syracuseStep 1996199 = 2994299) B2994299
theorem B2127379 : Blo 884570 2127379 := bstep (se 1 (by rfl) ⟨1595534, by rfl⟩ : syracuseStep 2127379 = 3191069) B3191069
theorem B1996307 : Blo 884570 1996307 := bstep (se 1 (by rfl) ⟨1497230, by rfl⟩ : syracuseStep 1996307 = 2994461) B2994461
theorem B58193473 : Blo 884570 58193473 := bstep (se 2 (by rfl) ⟨21822552, by rfl⟩ : syracuseStep 58193473 = 43645105) B43645105
theorem B1996379 : Blo 884570 1996379 := bstep (se 1 (by rfl) ⟨1497284, by rfl⟩ : syracuseStep 1996379 = 2994569) B2994569
theorem B3831391 : Blo 884570 3831391 := bstep (se 1 (by rfl) ⟨2873543, by rfl⟩ : syracuseStep 3831391 = 5747087) B5747087
theorem B4486751 : Blo 884570 4486751 := bstep (se 1 (by rfl) ⟨3365063, by rfl⟩ : syracuseStep 4486751 = 6730127) B6730127
theorem B23033443 : Blo 884570 23033443 := bstep (se 1 (by rfl) ⟨17275082, by rfl⟩ : syracuseStep 23033443 = 34550165) B34550165
theorem B17069777 : Blo 884570 17069777 := bstep (se 2 (by rfl) ⟨6401166, by rfl⟩ : syracuseStep 17069777 = 12802333) B12802333
theorem B14383169 : Blo 884570 14383169 := bstep (se 2 (by rfl) ⟨5393688, by rfl⟩ : syracuseStep 14383169 = 10787377) B10787377
theorem B1996991 : Blo 884570 1996991 := bstep (se 1 (by rfl) ⟨1497743, by rfl⟩ : syracuseStep 1996991 = 2995487) B2995487
theorem B3373265 : Blo 884570 3373265 := bstep (se 2 (by rfl) ⟨1264974, by rfl⟩ : syracuseStep 3373265 = 2529949) B2529949
theorem B4323881 : Blo 884570 4323881 := bstep (se 2 (by rfl) ⟨1621455, by rfl⟩ : syracuseStep 4323881 = 3242911) B3242911
theorem B2128475 : Blo 884570 2128475 := bstep (se 1 (by rfl) ⟨1596356, by rfl⟩ : syracuseStep 2128475 = 3192713) B3192713
theorem B5044841 : Blo 884570 5044841 := bstep (se 2 (by rfl) ⟨1891815, by rfl⟩ : syracuseStep 5044841 = 3783631) B3783631
theorem B6060673 : Blo 884570 6060673 := bstep (se 2 (by rfl) ⟨2272752, by rfl⟩ : syracuseStep 6060673 = 4545505) B4545505
theorem B2128609 : Blo 884570 2128609 := bstep (se 2 (by rfl) ⟨798228, by rfl⟩ : syracuseStep 2128609 = 1596457) B1596457
theorem B5765897 : Blo 884570 5765897 := bstep (se 2 (by rfl) ⟨2162211, by rfl⟩ : syracuseStep 5765897 = 4324423) B4324423
theorem B7174979 : Blo 884570 7174979 := bstep (se 1 (by rfl) ⟨5381234, by rfl⟩ : syracuseStep 7174979 = 10762469) B10762469
theorem B8092943 : Blo 884570 8092943 := bstep (se 1 (by rfl) ⟨6069707, by rfl⟩ : syracuseStep 8092943 = 12139415) B12139415
theorem B1998251 : Blo 884570 1998251 := bstep (se 1 (by rfl) ⟨1498688, by rfl⟩ : syracuseStep 1998251 = 2997377) B2997377
theorem B22740425 : Blo 884570 22740425 := bstep (se 2 (by rfl) ⟨8527659, by rfl⟩ : syracuseStep 22740425 = 17055319) B17055319
theorem B1998287 : Blo 884570 1998287 := bstep (se 1 (by rfl) ⟨1498715, by rfl⟩ : syracuseStep 1998287 = 2997431) B2997431
theorem B16416215 : Blo 884570 16416215 := bstep (se 1 (by rfl) ⟨12312161, by rfl⟩ : syracuseStep 16416215 = 24624323) B24624323
theorem B4488857 : Blo 884570 4488857 := bstep (se 2 (by rfl) ⟨1683321, by rfl⟩ : syracuseStep 4488857 = 3366643) B3366643
theorem B7569071 : Blo 884570 7569071 := bstep (se 1 (by rfl) ⟨5676803, by rfl⟩ : syracuseStep 7569071 = 11353607) B11353607
theorem B884591 : Blo 884570 884591 := bstep (se 1 (by rfl) ⟨663443, by rfl⟩ : syracuseStep 884591 = 1326887) B1326887
theorem B884647 : Blo 884570 884647 := bstep (se 1 (by rfl) ⟨663485, by rfl⟩ : syracuseStep 884647 = 1326971) B1326971
theorem B2129831 : Blo 884570 2129831 := bstep (se 1 (by rfl) ⟨1597373, by rfl⟩ : syracuseStep 2129831 = 3194747) B3194747
theorem B1998791 : Blo 884570 1998791 := bstep (se 1 (by rfl) ⟨1499093, by rfl⟩ : syracuseStep 1998791 = 2998187) B2998187
theorem B4849787 : Blo 884570 4849787 := bstep (se 1 (by rfl) ⟨3637340, by rfl⟩ : syracuseStep 4849787 = 7274681) B7274681
theorem B884863 : Blo 884570 884863 := bstep (se 1 (by rfl) ⟨663647, by rfl⟩ : syracuseStep 884863 = 1327295) B1327295
theorem B4489343 : Blo 884570 4489343 := bstep (se 1 (by rfl) ⟨3367007, by rfl⟩ : syracuseStep 4489343 = 6734015) B6734015
theorem B2883833 : Blo 884570 2883833 := bstep (se 2 (by rfl) ⟨1081437, by rfl⟩ : syracuseStep 2883833 = 2162875) B2162875
theorem B1999187 : Blo 884570 1999187 := bstep (se 1 (by rfl) ⟨1499390, by rfl⟩ : syracuseStep 1999187 = 2998781) B2998781
theorem B885147 : Blo 884570 885147 := bstep (se 1 (by rfl) ⟨663860, by rfl⟩ : syracuseStep 885147 = 1327721) B1327721
theorem B885151 : Blo 884570 885151 := bstep (se 1 (by rfl) ⟨663863, by rfl⟩ : syracuseStep 885151 = 1327727) B1327727
theorem B2523935 : Blo 884570 2523935 := bstep (se 1 (by rfl) ⟨1892951, by rfl⟩ : syracuseStep 2523935 = 3785903) B3785903
theorem B885567 : Blo 884570 885567 := bstep (se 1 (by rfl) ⟨664175, by rfl⟩ : syracuseStep 885567 = 1328351) B1328351
theorem B885575 : Blo 884570 885575 := bstep (se 1 (by rfl) ⟨664181, by rfl⟩ : syracuseStep 885575 = 1328363) B1328363
theorem B885831 : Blo 884570 885831 := bstep (se 1 (by rfl) ⟨664373, by rfl⟩ : syracuseStep 885831 = 1328747) B1328747
theorem B885887 : Blo 884570 885887 := bstep (se 1 (by rfl) ⟨664415, by rfl⟩ : syracuseStep 885887 = 1328831) B1328831
theorem B17040557 : Blo 884570 17040557 := bstep (se 3 (by rfl) ⟨3195104, by rfl⟩ : syracuseStep 17040557 = 6390209) B6390209
theorem B886011 : Blo 884570 886011 := bstep (se 1 (by rfl) ⟨664508, by rfl⟩ : syracuseStep 886011 = 1329017) B1329017
theorem B886511 : Blo 884570 886511 := bstep (se 1 (by rfl) ⟨664883, by rfl⟩ : syracuseStep 886511 = 1329767) B1329767
theorem B886639 : Blo 884570 886639 := bstep (se 1 (by rfl) ⟨664979, by rfl⟩ : syracuseStep 886639 = 1329959) B1329959
theorem B5048189 : Blo 884570 5048189 := bstep (se 3 (by rfl) ⟨946535, by rfl⟩ : syracuseStep 5048189 = 1893071) B1893071
theorem B886855 : Blo 884570 886855 := bstep (se 1 (by rfl) ⟨665141, by rfl⟩ : syracuseStep 886855 = 1330283) B1330283
theorem B887015 : Blo 884570 887015 := bstep (se 1 (by rfl) ⟨665261, by rfl⟩ : syracuseStep 887015 = 1330523) B1330523
theorem B887035 : Blo 884570 887035 := bstep (se 1 (by rfl) ⟨665276, by rfl⟩ : syracuseStep 887035 = 1330553) B1330553
theorem B887039 : Blo 884570 887039 := bstep (se 1 (by rfl) ⟨665279, by rfl⟩ : syracuseStep 887039 = 1330559) B1330559
theorem B2525519 : Blo 884570 2525519 := bstep (se 1 (by rfl) ⟨1894139, by rfl⟩ : syracuseStep 2525519 = 3788279) B3788279
theorem B21596543 : Blo 884570 21596543 := bstep (se 1 (by rfl) ⟨16197407, by rfl⟩ : syracuseStep 21596543 = 32394815) B32394815
theorem B887455 : Blo 884570 887455 := bstep (se 1 (by rfl) ⟨665591, by rfl⟩ : syracuseStep 887455 = 1331183) B1331183
theorem B887463 : Blo 884570 887463 := bstep (se 1 (by rfl) ⟨665597, by rfl⟩ : syracuseStep 887463 = 1331195) B1331195
theorem B887503 : Blo 884570 887503 := bstep (se 1 (by rfl) ⟨665627, by rfl⟩ : syracuseStep 887503 = 1331255) B1331255
theorem B887535 : Blo 884570 887535 := bstep (se 1 (by rfl) ⟨665651, by rfl⟩ : syracuseStep 887535 = 1331303) B1331303
theorem B887583 : Blo 884570 887583 := bstep (se 1 (by rfl) ⟨665687, by rfl⟩ : syracuseStep 887583 = 1331375) B1331375
theorem B64621475 : Blo 884570 64621475 := bstep (se 1 (by rfl) ⟨48466106, by rfl⟩ : syracuseStep 64621475 = 96932213) B96932213
theorem B887719 : Blo 884570 887719 := bstep (se 1 (by rfl) ⟨665789, by rfl⟩ : syracuseStep 887719 = 1331579) B1331579
theorem B887899 : Blo 884570 887899 := bstep (se 1 (by rfl) ⟨665924, by rfl⟩ : syracuseStep 887899 = 1331849) B1331849
theorem B888039 : Blo 884570 888039 := bstep (se 1 (by rfl) ⟨666029, by rfl⟩ : syracuseStep 888039 = 1332059) B1332059
theorem B11537815 : Blo 884570 11537815 := bstep (se 1 (by rfl) ⟨8653361, by rfl⟩ : syracuseStep 11537815 = 17306723) B17306723
theorem B2133415 : Blo 884570 2133415 := bstep (se 1 (by rfl) ⟨1600061, by rfl⟩ : syracuseStep 2133415 = 3200123) B3200123
theorem B888347 : Blo 884570 888347 := bstep (se 1 (by rfl) ⟨666260, by rfl⟩ : syracuseStep 888347 = 1332521) B1332521
theorem B888479 : Blo 884570 888479 := bstep (se 1 (by rfl) ⟨666359, by rfl⟩ : syracuseStep 888479 = 1332719) B1332719
theorem B4853843 : Blo 884570 4853843 := bstep (se 1 (by rfl) ⟨3640382, by rfl⟩ : syracuseStep 4853843 = 7280765) B7280765
theorem B4493555 : Blo 884570 4493555 := bstep (se 1 (by rfl) ⟨3370166, by rfl⟩ : syracuseStep 4493555 = 6740333) B6740333
theorem B7573949 : Blo 884570 7573949 := bstep (se 3 (by rfl) ⟨1420115, by rfl⟩ : syracuseStep 7573949 = 2840231) B2840231
theorem B2397367 : Blo 884570 2397367 := bstep (se 1 (by rfl) ⟨1798025, by rfl⟩ : syracuseStep 2397367 = 3596051) B3596051
theorem B5051879 : Blo 884570 5051879 := bstep (se 1 (by rfl) ⟨3788909, by rfl⟩ : syracuseStep 5051879 = 7577819) B7577819
theorem B1119835 : Blo 884570 1119835 := bstep (se 1 (by rfl) ⟨839876, by rfl⟩ : syracuseStep 1119835 = 1679753) B1679753
theorem B2987657 : Blo 884570 2987657 := bstep (se 2 (by rfl) ⟨1120371, by rfl⟩ : syracuseStep 2987657 = 2240743) B2240743
theorem B4495175 : Blo 884570 4495175 := bstep (se 1 (by rfl) ⟨3371381, by rfl⟩ : syracuseStep 4495175 = 6742763) B6742763
theorem B5052563 : Blo 884570 5052563 := bstep (se 1 (by rfl) ⟨3789422, by rfl⟩ : syracuseStep 5052563 = 7578845) B7578845
theorem B10229975 : Blo 884570 10229975 := bstep (se 1 (by rfl) ⟨7672481, by rfl⟩ : syracuseStep 10229975 = 15344963) B15344963
theorem B6724295 : Blo 884570 6724295 := bstep (se 1 (by rfl) ⟨5043221, by rfl⟩ : syracuseStep 6724295 = 10086443) B10086443
theorem B5675933 : Blo 884570 5675933 := bstep (se 3 (by rfl) ⟨1064237, by rfl⟩ : syracuseStep 5675933 = 2128475) B2128475
theorem B2563127 : Blo 884570 2563127 := bstep (se 1 (by rfl) ⟨1922345, by rfl⟩ : syracuseStep 2563127 = 3844691) B3844691
theorem B1121455 : Blo 884570 1121455 := bstep (se 1 (by rfl) ⟨841091, by rfl⟩ : syracuseStep 1121455 = 1682183) B1682183
theorem B30711257 : Blo 884570 30711257 := bstep (se 2 (by rfl) ⟨11516721, by rfl⟩ : syracuseStep 30711257 = 23033443) B23033443
theorem B8527355 : Blo 884570 8527355 := bstep (se 1 (by rfl) ⟨6395516, by rfl⟩ : syracuseStep 8527355 = 12791033) B12791033
theorem B11345609 : Blo 884570 11345609 := bstep (se 2 (by rfl) ⟨4254603, by rfl⟩ : syracuseStep 11345609 = 8509207) B8509207
theorem B9576319 : Blo 884570 9576319 := bstep (se 1 (by rfl) ⟨7182239, by rfl⟩ : syracuseStep 9576319 = 14364479) B14364479
theorem B7872815 : Blo 884570 7872815 := bstep (se 1 (by rfl) ⟨5904611, by rfl⟩ : syracuseStep 7872815 = 11809223) B11809223
theorem B30679955 : Blo 884570 30679955 := bstep (se 1 (by rfl) ⟨23009966, by rfl⟩ : syracuseStep 30679955 = 46019933) B46019933
theorem B5055479 : Blo 884570 5055479 := bstep (se 1 (by rfl) ⟨3791609, by rfl⟩ : syracuseStep 5055479 = 7583219) B7583219
theorem B2991167 : Blo 884570 2991167 := bstep (se 1 (by rfl) ⟨2243375, by rfl⟩ : syracuseStep 2991167 = 4486751) B4486751
theorem B11379851 : Blo 884570 11379851 := bstep (se 1 (by rfl) ⟨8534888, by rfl⟩ : syracuseStep 11379851 = 17069777) B17069777
theorem B77899573 : Blo 884570 77899573 := bstep (se 5 (by rfl) ⟨3651542, by rfl⟩ : syracuseStep 77899573 = 7303085) B7303085
theorem B10495831 : Blo 884570 10495831 := bstep (se 1 (by rfl) ⟨7871873, by rfl⟩ : syracuseStep 10495831 = 15743747) B15743747
theorem B3843931 : Blo 884570 3843931 := bstep (se 1 (by rfl) ⟨2882948, by rfl⟩ : syracuseStep 3843931 = 5765897) B5765897
theorem B2992571 : Blo 884570 2992571 := bstep (se 1 (by rfl) ⟨2244428, by rfl⟩ : syracuseStep 2992571 = 4488857) B4488857
theorem B1419887 : Blo 884570 1419887 := bstep (se 1 (by rfl) ⟨1064915, by rfl⟩ : syracuseStep 1419887 = 2129831) B2129831
theorem B18230791 : Blo 884570 18230791 := bstep (se 1 (by rfl) ⟨13673093, by rfl⟩ : syracuseStep 18230791 = 27346187) B27346187
theorem B5058713 : Blo 884570 5058713 := bstep (se 2 (by rfl) ⟨1897017, by rfl⟩ : syracuseStep 5058713 = 3794035) B3794035
theorem B995611 : Blo 884570 995611 := bstep (se 1 (by rfl) ⟨746708, by rfl⟩ : syracuseStep 995611 = 1493417) B1493417
theorem B996007 : Blo 884570 996007 := bstep (se 1 (by rfl) ⟨747005, by rfl⟩ : syracuseStep 996007 = 1494011) B1494011
theorem B2995001 : Blo 884570 2995001 := bstep (se 2 (by rfl) ⟨1123125, by rfl⟩ : syracuseStep 2995001 = 2246251) B2246251
theorem B2242039 : Blo 884570 2242039 := bstep (se 1 (by rfl) ⟨1681529, by rfl⟩ : syracuseStep 2242039 = 3363059) B3363059
theorem B2995865 : Blo 884570 2995865 := bstep (se 2 (by rfl) ⟨1123449, by rfl⟩ : syracuseStep 2995865 = 2246899) B2246899
theorem B5060627 : Blo 884570 5060627 := bstep (se 1 (by rfl) ⟨3795470, by rfl⟩ : syracuseStep 5060627 = 7590941) B7590941
theorem B11352581 : Blo 884570 11352581 := bstep (se 4 (by rfl) ⟨1064304, by rfl⟩ : syracuseStep 11352581 = 2128609) B2128609
theorem B1686071 : Blo 884570 1686071 := bstep (se 1 (by rfl) ⟨1264553, by rfl⟩ : syracuseStep 1686071 = 2529107) B2529107
theorem B1686329 : Blo 884570 1686329 := bstep (se 2 (by rfl) ⟨632373, by rfl⟩ : syracuseStep 1686329 = 1264747) B1264747
theorem B221264783 : Blo 884570 221264783 := bstep (se 1 (by rfl) ⟨165948587, by rfl⟩ : syracuseStep 221264783 = 331897175) B331897175
theorem B998383 : Blo 884570 998383 := bstep (se 1 (by rfl) ⟨748787, by rfl⟩ : syracuseStep 998383 = 1497575) B1497575
theorem B1686511 : Blo 884570 1686511 := bstep (se 1 (by rfl) ⟨1264883, by rfl⟩ : syracuseStep 1686511 = 2529767) B2529767
theorem B2243609 : Blo 884570 2243609 := bstep (se 2 (by rfl) ⟨841353, by rfl⟩ : syracuseStep 2243609 = 1682707) B1682707
theorem B13647113 : Blo 884570 13647113 := bstep (se 2 (by rfl) ⟨5117667, by rfl⟩ : syracuseStep 13647113 = 10235335) B10235335
theorem B998959 : Blo 884570 998959 := bstep (se 1 (by rfl) ⟨749219, by rfl⟩ : syracuseStep 998959 = 1498439) B1498439
theorem B999067 : Blo 884570 999067 := bstep (se 1 (by rfl) ⟨749300, by rfl⟩ : syracuseStep 999067 = 1498601) B1498601
theorem B2998025 : Blo 884570 2998025 := bstep (se 2 (by rfl) ⟨1124259, by rfl⟩ : syracuseStep 2998025 = 2248519) B2248519
theorem B2244449 : Blo 884570 2244449 := bstep (se 2 (by rfl) ⟨841668, by rfl⟩ : syracuseStep 2244449 = 1683337) B1683337
theorem B1327007 : Blo 884570 1327007 := bstep (se 1 (by rfl) ⟨995255, by rfl⟩ : syracuseStep 1327007 = 1990511) B1990511
theorem B1327097 : Blo 884570 1327097 := bstep (se 2 (by rfl) ⟨497661, by rfl⟩ : syracuseStep 1327097 = 995323) B995323
theorem B1327241 : Blo 884570 1327241 := bstep (se 2 (by rfl) ⟨497715, by rfl⟩ : syracuseStep 1327241 = 995431) B995431
theorem B1327337 : Blo 884570 1327337 := bstep (se 2 (by rfl) ⟨497751, by rfl⟩ : syracuseStep 1327337 = 995503) B995503
theorem B1327463 : Blo 884570 1327463 := bstep (se 1 (by rfl) ⟨995597, by rfl⟩ : syracuseStep 1327463 = 1991195) B1991195
theorem B1327583 : Blo 884570 1327583 := bstep (se 1 (by rfl) ⟨995687, by rfl⟩ : syracuseStep 1327583 = 1991375) B1991375
theorem B1327835 : Blo 884570 1327835 := bstep (se 1 (by rfl) ⟨995876, by rfl⟩ : syracuseStep 1327835 = 1991753) B1991753
theorem B5129027 : Blo 884570 5129027 := bstep (se 1 (by rfl) ⟨3846770, by rfl⟩ : syracuseStep 5129027 = 7693541) B7693541
theorem B2245715 : Blo 884570 2245715 := bstep (se 1 (by rfl) ⟨1684286, by rfl⟩ : syracuseStep 2245715 = 3368573) B3368573
theorem B1328249 : Blo 884570 1328249 := bstep (se 2 (by rfl) ⟨498093, by rfl⟩ : syracuseStep 1328249 = 996187) B996187
theorem B2245907 : Blo 884570 2245907 := bstep (se 1 (by rfl) ⟨1684430, by rfl⟩ : syracuseStep 2245907 = 3368861) B3368861
theorem B1328447 : Blo 884570 1328447 := bstep (se 1 (by rfl) ⟨996335, by rfl⟩ : syracuseStep 1328447 = 1992671) B1992671
theorem B27280793 : Blo 884570 27280793 := bstep (se 2 (by rfl) ⟨10230297, by rfl⟩ : syracuseStep 27280793 = 20460595) B20460595
theorem B8537501 : Blo 884570 8537501 := bstep (se 3 (by rfl) ⟨1600781, by rfl⟩ : syracuseStep 8537501 = 3201563) B3201563
theorem B1329119 : Blo 884570 1329119 := bstep (se 1 (by rfl) ⟨996839, by rfl⟩ : syracuseStep 1329119 = 1993679) B1993679
theorem B2836505 : Blo 884570 2836505 := bstep (se 2 (by rfl) ⟨1063689, by rfl⟩ : syracuseStep 2836505 = 2127379) B2127379
theorem B1329179 : Blo 884570 1329179 := bstep (se 1 (by rfl) ⟨996884, by rfl⟩ : syracuseStep 1329179 = 1993769) B1993769
theorem B1493039 : Blo 884570 1493039 := bstep (se 1 (by rfl) ⟨1119779, by rfl⟩ : syracuseStep 1493039 = 2239559) B2239559
theorem B1329335 : Blo 884570 1329335 := bstep (se 1 (by rfl) ⟨997001, by rfl⟩ : syracuseStep 1329335 = 1994003) B1994003
theorem B1329359 : Blo 884570 1329359 := bstep (se 1 (by rfl) ⟨997019, by rfl⟩ : syracuseStep 1329359 = 1994039) B1994039
theorem B34130321 : Blo 884570 34130321 := bstep (se 2 (by rfl) ⟨12798870, by rfl⟩ : syracuseStep 34130321 = 25597741) B25597741
theorem B1493545 : Blo 884570 1493545 := bstep (se 2 (by rfl) ⟨560079, by rfl⟩ : syracuseStep 1493545 = 1120159) B1120159
theorem B1329755 : Blo 884570 1329755 := bstep (se 1 (by rfl) ⟨997316, by rfl⟩ : syracuseStep 1329755 = 1994633) B1994633
theorem B1329899 : Blo 884570 1329899 := bstep (se 1 (by rfl) ⟨997424, by rfl⟩ : syracuseStep 1329899 = 1994849) B1994849
theorem B1329929 : Blo 884570 1329929 := bstep (se 2 (by rfl) ⟨498723, by rfl⟩ : syracuseStep 1329929 = 997447) B997447
theorem B3590993 : Blo 884570 3590993 := bstep (se 2 (by rfl) ⟨1346622, by rfl⟩ : syracuseStep 3590993 = 2693245) B2693245
theorem B6474593 : Blo 884570 6474593 := bstep (se 2 (by rfl) ⟨2427972, by rfl⟩ : syracuseStep 6474593 = 4855945) B4855945
theorem B1330343 : Blo 884570 1330343 := bstep (se 1 (by rfl) ⟨997757, by rfl⟩ : syracuseStep 1330343 = 1995515) B1995515
theorem B3362087 : Blo 884570 3362087 := bstep (se 1 (by rfl) ⟨2521565, by rfl⟩ : syracuseStep 3362087 = 5043131) B5043131
theorem B1330487 : Blo 884570 1330487 := bstep (se 1 (by rfl) ⟨997865, by rfl⟩ : syracuseStep 1330487 = 1995731) B1995731
theorem B1494443 : Blo 884570 1494443 := bstep (se 1 (by rfl) ⟨1120832, by rfl⟩ : syracuseStep 1494443 = 2241665) B2241665
theorem B3362255 : Blo 884570 3362255 := bstep (se 1 (by rfl) ⟨2521691, by rfl⟩ : syracuseStep 3362255 = 5043383) B5043383
theorem B8080897 : Blo 884570 8080897 := bstep (se 2 (by rfl) ⟨3030336, by rfl⟩ : syracuseStep 8080897 = 6060673) B6060673
theorem B122834495 : Blo 884570 122834495 := bstep (se 1 (by rfl) ⟨92125871, by rfl⟩ : syracuseStep 122834495 = 184251743) B184251743
theorem B1330799 : Blo 884570 1330799 := bstep (se 1 (by rfl) ⟨998099, by rfl⟩ : syracuseStep 1330799 = 1996199) B1996199
theorem B1330871 : Blo 884570 1330871 := bstep (se 1 (by rfl) ⟨998153, by rfl⟩ : syracuseStep 1330871 = 1996307) B1996307
theorem B1330919 : Blo 884570 1330919 := bstep (se 1 (by rfl) ⟨998189, by rfl⟩ : syracuseStep 1330919 = 1996379) B1996379
theorem B1331081 : Blo 884570 1331081 := bstep (se 2 (by rfl) ⟨499155, by rfl⟩ : syracuseStep 1331081 = 998311) B998311
theorem B1494983 : Blo 884570 1494983 := bstep (se 1 (by rfl) ⟨1121237, by rfl⟩ : syracuseStep 1494983 = 2242475) B2242475
theorem B9588779 : Blo 884570 9588779 := bstep (se 1 (by rfl) ⟨7191584, by rfl⟩ : syracuseStep 9588779 = 14383169) B14383169
theorem B1331321 : Blo 884570 1331321 := bstep (se 2 (by rfl) ⟨499245, by rfl⟩ : syracuseStep 1331321 = 998491) B998491
theorem B1331327 : Blo 884570 1331327 := bstep (se 1 (by rfl) ⟨998495, by rfl⟩ : syracuseStep 1331327 = 1996991) B1996991
theorem B2248843 : Blo 884570 2248843 := bstep (se 1 (by rfl) ⟨1686632, by rfl⟩ : syracuseStep 2248843 = 3373265) B3373265
theorem B3363227 : Blo 884570 3363227 := bstep (se 1 (by rfl) ⟨2522420, by rfl⟩ : syracuseStep 3363227 = 5044841) B5044841
theorem B5395295 : Blo 884570 5395295 := bstep (se 1 (by rfl) ⟨4046471, by rfl⟩ : syracuseStep 5395295 = 8092943) B8092943
theorem B1332167 : Blo 884570 1332167 := bstep (se 1 (by rfl) ⟨999125, by rfl⟩ : syracuseStep 1332167 = 1998251) B1998251
theorem B15160283 : Blo 884570 15160283 := bstep (se 1 (by rfl) ⟨11370212, by rfl⟩ : syracuseStep 15160283 = 22740425) B22740425
theorem B1332191 : Blo 884570 1332191 := bstep (se 1 (by rfl) ⟨999143, by rfl⟩ : syracuseStep 1332191 = 1998287) B1998287
theorem B1332527 : Blo 884570 1332527 := bstep (se 1 (by rfl) ⟨999395, by rfl⟩ : syracuseStep 1332527 = 1998791) B1998791
theorem B1332731 : Blo 884570 1332731 := bstep (se 1 (by rfl) ⟨999548, by rfl⟩ : syracuseStep 1332731 = 1999097) B1999097
theorem B1332767 : Blo 884570 1332767 := bstep (se 1 (by rfl) ⟨999575, by rfl⟩ : syracuseStep 1332767 = 1999151) B1999151
theorem B3365003 : Blo 884570 3365003 := bstep (se 1 (by rfl) ⟨2523752, by rfl⟩ : syracuseStep 3365003 = 5047505) B5047505
theorem B2021611 : Blo 884570 2021611 := bstep (se 1 (by rfl) ⟨1516208, by rfl⟩ : syracuseStep 2021611 = 3032417) B3032417
theorem B25876745 : Blo 884570 25876745 := bstep (se 2 (by rfl) ⟨9703779, by rfl⟩ : syracuseStep 25876745 = 19407559) B19407559
theorem B2841247 : Blo 884570 2841247 := bstep (se 1 (by rfl) ⟨2130935, by rfl⟩ : syracuseStep 2841247 = 4261871) B4261871
theorem B1497791 : Blo 884570 1497791 := bstep (se 1 (by rfl) ⟨1123343, by rfl⟩ : syracuseStep 1497791 = 2246687) B2246687
theorem B3365671 : Blo 884570 3365671 := bstep (se 1 (by rfl) ⟨2524253, by rfl⟩ : syracuseStep 3365671 = 5048507) B5048507
theorem B32365619 : Blo 884570 32365619 := bstep (se 1 (by rfl) ⟨24274214, by rfl⟩ : syracuseStep 32365619 = 48548429) B48548429
theorem B1498459 : Blo 884570 1498459 := bstep (se 1 (by rfl) ⟨1123844, by rfl⟩ : syracuseStep 1498459 = 2247689) B2247689
theorem B12279185 : Blo 884570 12279185 := bstep (se 2 (by rfl) ⟨4604694, by rfl⟩ : syracuseStep 12279185 = 9209389) B9209389
theorem B1990367 : Blo 884570 1990367 := bstep (se 1 (by rfl) ⟨1492775, by rfl⟩ : syracuseStep 1990367 = 2985551) B2985551
theorem B8511439 : Blo 884570 8511439 := bstep (se 1 (by rfl) ⟨6383579, by rfl⟩ : syracuseStep 8511439 = 12767159) B12767159
theorem B1990727 : Blo 884570 1990727 := bstep (se 1 (by rfl) ⟨1493045, by rfl⟩ : syracuseStep 1990727 = 2986091) B2986091
theorem B1990763 : Blo 884570 1990763 := bstep (se 1 (by rfl) ⟨1493072, by rfl⟩ : syracuseStep 1990763 = 2986145) B2986145
theorem B1499431 : Blo 884570 1499431 := bstep (se 1 (by rfl) ⟨1124573, by rfl⟩ : syracuseStep 1499431 = 2249147) B2249147
theorem B1991033 : Blo 884570 1991033 := bstep (se 2 (by rfl) ⟨746637, by rfl⟩ : syracuseStep 1991033 = 1493275) B1493275
theorem B1991465 : Blo 884570 1991465 := bstep (se 2 (by rfl) ⟨746799, by rfl⟩ : syracuseStep 1991465 = 1493599) B1493599
theorem B1991663 : Blo 884570 1991663 := bstep (se 1 (by rfl) ⟨1493747, by rfl⟩ : syracuseStep 1991663 = 2987495) B2987495
theorem B10216487 : Blo 884570 10216487 := bstep (se 1 (by rfl) ⟨7662365, by rfl⟩ : syracuseStep 10216487 = 15324731) B15324731
theorem B1991735 : Blo 884570 1991735 := bstep (se 1 (by rfl) ⟨1493801, by rfl⟩ : syracuseStep 1991735 = 2987603) B2987603
theorem B1991915 : Blo 884570 1991915 := bstep (se 1 (by rfl) ⟨1493936, by rfl⟩ : syracuseStep 1991915 = 2987873) B2987873
theorem B2024887 : Blo 884570 2024887 := bstep (se 1 (by rfl) ⟨1518665, by rfl⟩ : syracuseStep 2024887 = 3037331) B3037331
theorem B3598127 : Blo 884570 3598127 := bstep (se 1 (by rfl) ⟨2698595, by rfl⟩ : syracuseStep 3598127 = 5397191) B5397191
theorem B1599355 : Blo 884570 1599355 := bstep (se 1 (by rfl) ⟨1199516, by rfl⟩ : syracuseStep 1599355 = 2399033) B2399033
theorem B2844809 : Blo 884570 2844809 := bstep (se 2 (by rfl) ⟨1066803, by rfl⟩ : syracuseStep 2844809 = 2133607) B2133607
theorem B77591297 : Blo 884570 77591297 := bstep (se 2 (by rfl) ⟨29096736, by rfl⟩ : syracuseStep 77591297 = 58193473) B58193473
theorem B5108521 : Blo 884570 5108521 := bstep (se 2 (by rfl) ⟨1915695, by rfl⟩ : syracuseStep 5108521 = 3831391) B3831391
theorem B1995641 : Blo 884570 1995641 := bstep (se 2 (by rfl) ⟨748365, by rfl⟩ : syracuseStep 1995641 = 1496731) B1496731
theorem B3404699 : Blo 884570 3404699 := bstep (se 1 (by rfl) ⟨2553524, by rfl⟩ : syracuseStep 3404699 = 5107049) B5107049
theorem B4486265 : Blo 884570 4486265 := bstep (se 2 (by rfl) ⟨1682349, by rfl⟩ : syracuseStep 4486265 = 3364699) B3364699
theorem B1996271 : Blo 884570 1996271 := bstep (se 1 (by rfl) ⟨1497203, by rfl⟩ : syracuseStep 1996271 = 2994407) B2994407
theorem B7370297 : Blo 884570 7370297 := bstep (se 2 (by rfl) ⟨2763861, by rfl⟩ : syracuseStep 7370297 = 5527723) B5527723
theorem B10253947 : Blo 884570 10253947 := bstep (se 1 (by rfl) ⟨7690460, by rfl⟩ : syracuseStep 10253947 = 15380921) B15380921
theorem B28800845 : Blo 884570 28800845 := bstep (se 3 (by rfl) ⟨5400158, by rfl⟩ : syracuseStep 28800845 = 10800317) B10800317
theorem B3897371 : Blo 884570 3897371 := bstep (se 1 (by rfl) ⟨2923028, by rfl⟩ : syracuseStep 3897371 = 5846057) B5846057
theorem B1996847 : Blo 884570 1996847 := bstep (se 1 (by rfl) ⟨1497635, by rfl⟩ : syracuseStep 1996847 = 2995271) B2995271
theorem B2521543 : Blo 884570 2521543 := bstep (se 1 (by rfl) ⟨1891157, by rfl⟩ : syracuseStep 2521543 = 3782315) B3782315
theorem B35027425 : Blo 884570 35027425 := bstep (se 2 (by rfl) ⟨13135284, by rfl⟩ : syracuseStep 35027425 = 26270569) B26270569
theorem B1997639 : Blo 884570 1997639 := bstep (se 1 (by rfl) ⟨1498229, by rfl⟩ : syracuseStep 1997639 = 2996459) B2996459
theorem B2882587 : Blo 884570 2882587 := bstep (se 1 (by rfl) ⟨2161940, by rfl⟩ : syracuseStep 2882587 = 4323881) B4323881
theorem B8092871 : Blo 884570 8092871 := bstep (se 1 (by rfl) ⟨6069653, by rfl⟩ : syracuseStep 8092871 = 12139307) B12139307
theorem B4783319 : Blo 884570 4783319 := bstep (se 1 (by rfl) ⟨3587489, by rfl⟩ : syracuseStep 4783319 = 7174979) B7174979
theorem B2522603 : Blo 884570 2522603 := bstep (se 1 (by rfl) ⟨1891952, by rfl⟩ : syracuseStep 2522603 = 3783905) B3783905
theorem B2129399 : Blo 884570 2129399 := bstep (se 1 (by rfl) ⟨1597049, by rfl⟩ : syracuseStep 2129399 = 3194099) B3194099
theorem B4488695 : Blo 884570 4488695 := bstep (se 1 (by rfl) ⟨3366521, by rfl⟩ : syracuseStep 4488695 = 6733043) B6733043
theorem B10944143 : Blo 884570 10944143 := bstep (se 1 (by rfl) ⟨8208107, by rfl⟩ : syracuseStep 10944143 = 16416215) B16416215
theorem B5046047 : Blo 884570 5046047 := bstep (se 1 (by rfl) ⟨3784535, by rfl⟩ : syracuseStep 5046047 = 7569071) B7569071
theorem B884571 : Blo 884570 884571 := bstep (se 1 (by rfl) ⟨663428, by rfl⟩ : syracuseStep 884571 = 1326857) B1326857
theorem B2523001 : Blo 884570 2523001 := bstep (se 2 (by rfl) ⟨946125, by rfl⟩ : syracuseStep 2523001 = 1892251) B1892251
theorem B884827 : Blo 884570 884827 := bstep (se 1 (by rfl) ⟨663620, by rfl⟩ : syracuseStep 884827 = 1327241) B1327241
theorem B884891 : Blo 884570 884891 := bstep (se 1 (by rfl) ⟨663668, by rfl⟩ : syracuseStep 884891 = 1327337) B1327337
theorem B884975 : Blo 884570 884975 := bstep (se 1 (by rfl) ⟨663731, by rfl⟩ : syracuseStep 884975 = 1327463) B1327463
theorem B885055 : Blo 884570 885055 := bstep (se 1 (by rfl) ⟨663791, by rfl⟩ : syracuseStep 885055 = 1327583) B1327583
theorem B1999241 : Blo 884570 1999241 := bstep (se 2 (by rfl) ⟨749715, by rfl⟩ : syracuseStep 1999241 = 1499431) B1499431
theorem B885223 : Blo 884570 885223 := bstep (se 1 (by rfl) ⟨663917, by rfl⟩ : syracuseStep 885223 = 1327835) B1327835
theorem B885499 : Blo 884570 885499 := bstep (se 1 (by rfl) ⟨664124, by rfl⟩ : syracuseStep 885499 = 1328249) B1328249
theorem B885631 : Blo 884570 885631 := bstep (se 1 (by rfl) ⟨664223, by rfl⟩ : syracuseStep 885631 = 1328447) B1328447
theorem B18187195 : Blo 884570 18187195 := bstep (se 1 (by rfl) ⟨13640396, by rfl⟩ : syracuseStep 18187195 = 27280793) B27280793
theorem B886079 : Blo 884570 886079 := bstep (se 1 (by rfl) ⟨664559, by rfl⟩ : syracuseStep 886079 = 1329119) B1329119
theorem B886119 : Blo 884570 886119 := bstep (se 1 (by rfl) ⟨664589, by rfl⟩ : syracuseStep 886119 = 1329179) B1329179
theorem B886223 : Blo 884570 886223 := bstep (se 1 (by rfl) ⟨664667, by rfl⟩ : syracuseStep 886223 = 1329335) B1329335
theorem B886239 : Blo 884570 886239 := bstep (se 1 (by rfl) ⟨664679, by rfl⟩ : syracuseStep 886239 = 1329359) B1329359
theorem B886503 : Blo 884570 886503 := bstep (se 1 (by rfl) ⟨664877, by rfl⟩ : syracuseStep 886503 = 1329755) B1329755
theorem B886599 : Blo 884570 886599 := bstep (se 1 (by rfl) ⟨664949, by rfl⟩ : syracuseStep 886599 = 1329899) B1329899
theorem B886619 : Blo 884570 886619 := bstep (se 1 (by rfl) ⟨664964, by rfl⟩ : syracuseStep 886619 = 1329929) B1329929
theorem B2393995 : Blo 884570 2393995 := bstep (se 1 (by rfl) ⟨1795496, by rfl⟩ : syracuseStep 2393995 = 3590993) B3590993
theorem B886895 : Blo 884570 886895 := bstep (se 1 (by rfl) ⟨665171, by rfl⟩ : syracuseStep 886895 = 1330343) B1330343
theorem B886991 : Blo 884570 886991 := bstep (se 1 (by rfl) ⟨665243, by rfl⟩ : syracuseStep 886991 = 1330487) B1330487
theorem B14387453 : Blo 884570 14387453 := bstep (se 3 (by rfl) ⟨2697647, by rfl⟩ : syracuseStep 14387453 = 5395295) B5395295
theorem B81889663 : Blo 884570 81889663 := bstep (se 1 (by rfl) ⟨61417247, by rfl⟩ : syracuseStep 81889663 = 122834495) B122834495
theorem B887199 : Blo 884570 887199 := bstep (se 1 (by rfl) ⟨665399, by rfl⟩ : syracuseStep 887199 = 1330799) B1330799
theorem B13994441 : Blo 884570 13994441 := bstep (se 2 (by rfl) ⟨5247915, by rfl⟩ : syracuseStep 13994441 = 10495831) B10495831
theorem B887247 : Blo 884570 887247 := bstep (se 1 (by rfl) ⟨665435, by rfl⟩ : syracuseStep 887247 = 1330871) B1330871
theorem B887279 : Blo 884570 887279 := bstep (se 1 (by rfl) ⟨665459, by rfl⟩ : syracuseStep 887279 = 1330919) B1330919
theorem B887387 : Blo 884570 887387 := bstep (se 1 (by rfl) ⟨665540, by rfl⟩ : syracuseStep 887387 = 1331081) B1331081
theorem B6392519 : Blo 884570 6392519 := bstep (se 1 (by rfl) ⟨4794389, by rfl⟩ : syracuseStep 6392519 = 9588779) B9588779
theorem B887547 : Blo 884570 887547 := bstep (se 1 (by rfl) ⟨665660, by rfl⟩ : syracuseStep 887547 = 1331321) B1331321
theorem B887551 : Blo 884570 887551 := bstep (se 1 (by rfl) ⟨665663, by rfl⟩ : syracuseStep 887551 = 1331327) B1331327
theorem B5049299 : Blo 884570 5049299 := bstep (se 1 (by rfl) ⟨3786974, by rfl⟩ : syracuseStep 5049299 = 7573949) B7573949
theorem B888111 : Blo 884570 888111 := bstep (se 1 (by rfl) ⟨666083, by rfl⟩ : syracuseStep 888111 = 1332167) B1332167
theorem B888127 : Blo 884570 888127 := bstep (se 1 (by rfl) ⟨666095, by rfl⟩ : syracuseStep 888127 = 1332191) B1332191
theorem B888351 : Blo 884570 888351 := bstep (se 1 (by rfl) ⟨666263, by rfl⟩ : syracuseStep 888351 = 1332527) B1332527
theorem B888487 : Blo 884570 888487 := bstep (se 1 (by rfl) ⟨666365, by rfl⟩ : syracuseStep 888487 = 1332731) B1332731
theorem B888511 : Blo 884570 888511 := bstep (se 1 (by rfl) ⟨666383, by rfl⟩ : syracuseStep 888511 = 1332767) B1332767
theorem B6819983 : Blo 884570 6819983 := bstep (se 1 (by rfl) ⟨5114987, by rfl⟩ : syracuseStep 6819983 = 10229975) B10229975
theorem B5248543 : Blo 884570 5248543 := bstep (se 1 (by rfl) ⟨3936407, by rfl⟩ : syracuseStep 5248543 = 7872815) B7872815
theorem B20453303 : Blo 884570 20453303 := bstep (se 1 (by rfl) ⟨15339977, by rfl⟩ : syracuseStep 20453303 = 30679955) B30679955
theorem B2398751 : Blo 884570 2398751 := bstep (se 1 (by rfl) ⟨1799063, by rfl⟩ : syracuseStep 2398751 = 3598127) B3598127
theorem B2989385 : Blo 884570 2989385 := bstep (se 2 (by rfl) ⟨1121019, by rfl⟩ : syracuseStep 2989385 = 2242039) B2242039
theorem B13671929 : Blo 884570 13671929 := bstep (se 2 (by rfl) ⟨5126973, by rfl⟩ : syracuseStep 13671929 = 10253947) B10253947
theorem B2695481 : Blo 884570 2695481 := bstep (se 2 (by rfl) ⟨1010805, by rfl⟩ : syracuseStep 2695481 = 2021611) B2021611
theorem B2269799 : Blo 884570 2269799 := bstep (se 1 (by rfl) ⟨1702349, by rfl⟩ : syracuseStep 2269799 = 3404699) B3404699
theorem B46703233 : Blo 884570 46703233 := bstep (se 2 (by rfl) ⟨17513712, by rfl⟩ : syracuseStep 46703233 = 35027425) B35027425
theorem B2990843 : Blo 884570 2990843 := bstep (se 1 (by rfl) ⟨2243132, by rfl⟩ : syracuseStep 2990843 = 4486265) B4486265
theorem B2598247 : Blo 884570 2598247 := bstep (se 1 (by rfl) ⟨1948685, by rfl⟩ : syracuseStep 2598247 = 3897371) B3897371
theorem B3843449 : Blo 884570 3843449 := bstep (se 2 (by rfl) ⟨1441293, by rfl⟩ : syracuseStep 3843449 = 2882587) B2882587
theorem B1124047 : Blo 884570 1124047 := bstep (se 1 (by rfl) ⟨843035, by rfl⟩ : syracuseStep 1124047 = 1686071) B1686071
theorem B1124219 : Blo 884570 1124219 := bstep (se 1 (by rfl) ⟨843164, by rfl⟩ : syracuseStep 1124219 = 1686329) B1686329
theorem B8529893 : Blo 884570 8529893 := bstep (se 4 (by rfl) ⟨799677, by rfl⟩ : syracuseStep 8529893 = 1599355) B1599355
theorem B3188879 : Blo 884570 3188879 := bstep (se 1 (by rfl) ⟨2391659, by rfl⟩ : syracuseStep 3188879 = 4783319) B4783319
theorem B1681735 : Blo 884570 1681735 := bstep (se 1 (by rfl) ⟨1261301, by rfl⟩ : syracuseStep 1681735 = 2522603) B2522603
theorem B1419599 : Blo 884570 1419599 := bstep (se 1 (by rfl) ⟨1064699, by rfl⟩ : syracuseStep 1419599 = 2129399) B2129399
theorem B2992463 : Blo 884570 2992463 := bstep (se 1 (by rfl) ⟨2244347, by rfl⟩ : syracuseStep 2992463 = 4488695) B4488695
theorem B11348585 : Blo 884570 11348585 := bstep (se 2 (by rfl) ⟨4255719, by rfl⟩ : syracuseStep 11348585 = 8511439) B8511439
theorem B2992895 : Blo 884570 2992895 := bstep (se 1 (by rfl) ⟨2244671, by rfl⟩ : syracuseStep 2992895 = 4489343) B4489343
theorem B1682623 : Blo 884570 1682623 := bstep (se 1 (by rfl) ⟨1261967, by rfl⟩ : syracuseStep 1682623 = 2523935) B2523935
theorem B3419351 : Blo 884570 3419351 := bstep (se 1 (by rfl) ⟨2564513, by rfl⟩ : syracuseStep 3419351 = 5129027) B5129027
theorem B27340021 : Blo 884570 27340021 := bstep (se 5 (by rfl) ⟨1281563, by rfl⟩ : syracuseStep 27340021 = 2563127) B2563127
theorem B995359 : Blo 884570 995359 := bstep (se 1 (by rfl) ⟨746519, by rfl⟩ : syracuseStep 995359 = 1493039) B1493039
theorem B1683679 : Blo 884570 1683679 := bstep (se 1 (by rfl) ⟨1262759, by rfl⟩ : syracuseStep 1683679 = 2525519) B2525519
theorem B14397695 : Blo 884570 14397695 := bstep (se 1 (by rfl) ⟨10798271, by rfl⟩ : syracuseStep 14397695 = 21596543) B21596543
theorem B22753547 : Blo 884570 22753547 := bstep (se 1 (by rfl) ⟨17065160, by rfl⟩ : syracuseStep 22753547 = 34130321) B34130321
theorem B2699849 : Blo 884570 2699849 := bstep (se 2 (by rfl) ⟨1012443, by rfl⟩ : syracuseStep 2699849 = 2024887) B2024887
theorem B206910125 : Blo 884570 206910125 := bstep (se 3 (by rfl) ⟨38795648, by rfl⟩ : syracuseStep 206910125 = 77591297) B77591297
theorem B2241391 : Blo 884570 2241391 := bstep (se 1 (by rfl) ⟨1681043, by rfl⟩ : syracuseStep 2241391 = 3362087) B3362087
theorem B996295 : Blo 884570 996295 := bstep (se 1 (by rfl) ⟨747221, by rfl⟩ : syracuseStep 996295 = 1494443) B1494443
theorem B2241503 : Blo 884570 2241503 := bstep (se 1 (by rfl) ⟨1681127, by rfl⟩ : syracuseStep 2241503 = 3362255) B3362255
theorem B5125241 : Blo 884570 5125241 := bstep (se 2 (by rfl) ⟨1921965, by rfl⟩ : syracuseStep 5125241 = 3843931) B3843931
theorem B996655 : Blo 884570 996655 := bstep (se 1 (by rfl) ⟨747491, by rfl⟩ : syracuseStep 996655 = 1494983) B1494983
theorem B27243965 : Blo 884570 27243965 := bstep (se 3 (by rfl) ⟨5108243, by rfl⟩ : syracuseStep 27243965 = 10216487) B10216487
theorem B2995703 : Blo 884570 2995703 := bstep (se 1 (by rfl) ⟨2246777, by rfl⟩ : syracuseStep 2995703 = 4493555) B4493555
theorem B2242151 : Blo 884570 2242151 := bstep (se 1 (by rfl) ⟨1681613, by rfl⟩ : syracuseStep 2242151 = 3363227) B3363227
theorem B10106855 : Blo 884570 10106855 := bstep (se 1 (by rfl) ⟨7580141, by rfl⟩ : syracuseStep 10106855 = 15160283) B15160283
theorem B2996783 : Blo 884570 2996783 := bstep (se 1 (by rfl) ⟨2247587, by rfl⟩ : syracuseStep 2996783 = 4495175) B4495175
theorem B2243335 : Blo 884570 2243335 := bstep (se 1 (by rfl) ⟨1682501, by rfl⟩ : syracuseStep 2243335 = 3365003) B3365003
theorem B17251163 : Blo 884570 17251163 := bstep (se 1 (by rfl) ⟨12938372, by rfl⟩ : syracuseStep 17251163 = 25876745) B25876745
theorem B998527 : Blo 884570 998527 := bstep (se 1 (by rfl) ⟨748895, by rfl⟩ : syracuseStep 998527 = 1497791) B1497791
theorem B15383753 : Blo 884570 15383753 := bstep (se 2 (by rfl) ⟨5768907, by rfl⟩ : syracuseStep 15383753 = 11537815) B11537815
theorem B3783955 : Blo 884570 3783955 := bstep (se 1 (by rfl) ⟨2837966, by rfl⟩ : syracuseStep 3783955 = 5675933) B5675933
theorem B21577079 : Blo 884570 21577079 := bstep (se 1 (by rfl) ⟨16182809, by rfl⟩ : syracuseStep 21577079 = 32365619) B32365619
theorem B5684903 : Blo 884570 5684903 := bstep (se 1 (by rfl) ⟨4263677, by rfl⟩ : syracuseStep 5684903 = 8527355) B8527355
theorem B1326911 : Blo 884570 1326911 := bstep (se 1 (by rfl) ⟨995183, by rfl⟩ : syracuseStep 1326911 = 1990367) B1990367
theorem B1327151 : Blo 884570 1327151 := bstep (se 1 (by rfl) ⟨995363, by rfl⟩ : syracuseStep 1327151 = 1990727) B1990727
theorem B1327175 : Blo 884570 1327175 := bstep (se 1 (by rfl) ⟨995381, by rfl⟩ : syracuseStep 1327175 = 1990763) B1990763
theorem B2998457 : Blo 884570 2998457 := bstep (se 2 (by rfl) ⟨1124421, by rfl⟩ : syracuseStep 2998457 = 2248843) B2248843
theorem B1327355 : Blo 884570 1327355 := bstep (se 1 (by rfl) ⟨995516, by rfl⟩ : syracuseStep 1327355 = 1991033) B1991033
theorem B1327481 : Blo 884570 1327481 := bstep (se 2 (by rfl) ⟨497805, by rfl⟩ : syracuseStep 1327481 = 995611) B995611
theorem B1327643 : Blo 884570 1327643 := bstep (se 1 (by rfl) ⟨995732, by rfl⟩ : syracuseStep 1327643 = 1991465) B1991465
theorem B1327775 : Blo 884570 1327775 := bstep (se 1 (by rfl) ⟨995831, by rfl⟩ : syracuseStep 1327775 = 1991663) B1991663
theorem B1327823 : Blo 884570 1327823 := bstep (se 1 (by rfl) ⟨995867, by rfl⟩ : syracuseStep 1327823 = 1991735) B1991735
theorem B7586567 : Blo 884570 7586567 := bstep (se 1 (by rfl) ⟨5689925, by rfl⟩ : syracuseStep 7586567 = 11379851) B11379851
theorem B1327943 : Blo 884570 1327943 := bstep (se 1 (by rfl) ⟨995957, by rfl⟩ : syracuseStep 1327943 = 1991915) B1991915
theorem B1328009 : Blo 884570 1328009 := bstep (se 2 (by rfl) ⟨498003, by rfl⟩ : syracuseStep 1328009 = 996007) B996007
theorem B3196489 : Blo 884570 3196489 := bstep (se 2 (by rfl) ⟨1198683, by rfl⟩ : syracuseStep 3196489 = 2397367) B2397367
theorem B3786365 : Blo 884570 3786365 := bstep (se 3 (by rfl) ⟨709943, by rfl⟩ : syracuseStep 3786365 = 1419887) B1419887
theorem B1493113 : Blo 884570 1493113 := bstep (se 2 (by rfl) ⟨559917, by rfl⟩ : syracuseStep 1493113 = 1119835) B1119835
theorem B1330427 : Blo 884570 1330427 := bstep (se 1 (by rfl) ⟨997820, by rfl⟩ : syracuseStep 1330427 = 1995641) B1995641
theorem B3362057 : Blo 884570 3362057 := bstep (se 2 (by rfl) ⟨1260771, by rfl⟩ : syracuseStep 3362057 = 2521543) B2521543
theorem B3788329 : Blo 884570 3788329 := bstep (se 2 (by rfl) ⟨1420623, by rfl⟩ : syracuseStep 3788329 = 2841247) B2841247
theorem B1330847 : Blo 884570 1330847 := bstep (se 1 (by rfl) ⟨998135, by rfl⟩ : syracuseStep 1330847 = 1996271) B1996271
theorem B1331177 : Blo 884570 1331177 := bstep (se 2 (by rfl) ⟨499191, by rfl⟩ : syracuseStep 1331177 = 998383) B998383
theorem B2248681 : Blo 884570 2248681 := bstep (se 2 (by rfl) ⟨843255, by rfl⟩ : syracuseStep 2248681 = 1686511) B1686511
theorem B1331231 : Blo 884570 1331231 := bstep (se 1 (by rfl) ⟨998423, by rfl⟩ : syracuseStep 1331231 = 1996847) B1996847
theorem B1495273 : Blo 884570 1495273 := bstep (se 2 (by rfl) ⟨560727, by rfl⟩ : syracuseStep 1495273 = 1121455) B1121455
theorem B1331759 : Blo 884570 1331759 := bstep (se 1 (by rfl) ⟨998819, by rfl⟩ : syracuseStep 1331759 = 1997639) B1997639
theorem B147509855 : Blo 884570 147509855 := bstep (se 1 (by rfl) ⟨110632391, by rfl⟩ : syracuseStep 147509855 = 221264783) B221264783
theorem B1495739 : Blo 884570 1495739 := bstep (se 1 (by rfl) ⟨1121804, by rfl⟩ : syracuseStep 1495739 = 2243609) B2243609
theorem B1331945 : Blo 884570 1331945 := bstep (se 2 (by rfl) ⟨499479, by rfl⟩ : syracuseStep 1331945 = 998959) B998959
theorem B5395247 : Blo 884570 5395247 := bstep (se 1 (by rfl) ⟨4046435, by rfl⟩ : syracuseStep 5395247 = 8092871) B8092871
theorem B9098075 : Blo 884570 9098075 := bstep (se 1 (by rfl) ⟨6823556, by rfl⟩ : syracuseStep 9098075 = 13647113) B13647113
theorem B1332089 : Blo 884570 1332089 := bstep (se 2 (by rfl) ⟨499533, by rfl⟩ : syracuseStep 1332089 = 999067) B999067
theorem B7296095 : Blo 884570 7296095 := bstep (se 1 (by rfl) ⟨5472071, by rfl⟩ : syracuseStep 7296095 = 10944143) B10944143
theorem B3364001 : Blo 884570 3364001 := bstep (se 2 (by rfl) ⟨1261500, by rfl⟩ : syracuseStep 3364001 = 2523001) B2523001
theorem B12768425 : Blo 884570 12768425 := bstep (se 2 (by rfl) ⟨4788159, by rfl⟩ : syracuseStep 12768425 = 9576319) B9576319
theorem B3364031 : Blo 884570 3364031 := bstep (se 1 (by rfl) ⟨2523023, by rfl⟩ : syracuseStep 3364031 = 5046047) B5046047
theorem B1496299 : Blo 884570 1496299 := bstep (se 1 (by rfl) ⟨1122224, by rfl⟩ : syracuseStep 1496299 = 2244449) B2244449
theorem B3233191 : Blo 884570 3233191 := bstep (se 1 (by rfl) ⟨2424893, by rfl⟩ : syracuseStep 3233191 = 4849787) B4849787
theorem B1922555 : Blo 884570 1922555 := bstep (se 1 (by rfl) ⟨1441916, by rfl⟩ : syracuseStep 1922555 = 2883833) B2883833
theorem B1332791 : Blo 884570 1332791 := bstep (se 1 (by rfl) ⟨999593, by rfl⟩ : syracuseStep 1332791 = 1999187) B1999187
theorem B1497143 : Blo 884570 1497143 := bstep (se 1 (by rfl) ⟨1122857, by rfl⟩ : syracuseStep 1497143 = 2245715) B2245715
theorem B11360371 : Blo 884570 11360371 := bstep (se 1 (by rfl) ⟨8520278, by rfl⟩ : syracuseStep 11360371 = 17040557) B17040557
theorem B1497271 : Blo 884570 1497271 := bstep (se 1 (by rfl) ⟨1122953, by rfl⟩ : syracuseStep 1497271 = 2245907) B2245907
theorem B3365459 : Blo 884570 3365459 := bstep (se 1 (by rfl) ⟨2524094, by rfl⟩ : syracuseStep 3365459 = 5048189) B5048189
theorem B43080983 : Blo 884570 43080983 := bstep (se 1 (by rfl) ⟨32310737, by rfl⟩ : syracuseStep 43080983 = 64621475) B64621475
theorem B3235895 : Blo 884570 3235895 := bstep (se 1 (by rfl) ⟨2426921, by rfl⟩ : syracuseStep 3235895 = 4853843) B4853843
theorem B1991393 : Blo 884570 1991393 := bstep (se 2 (by rfl) ⟨746772, by rfl⟩ : syracuseStep 1991393 = 1493545) B1493545
theorem B3367919 : Blo 884570 3367919 := bstep (se 1 (by rfl) ⟨2525939, by rfl⟩ : syracuseStep 3367919 = 5051879) B5051879
theorem B22766669 : Blo 884570 22766669 := bstep (se 3 (by rfl) ⟨4268750, by rfl⟩ : syracuseStep 22766669 = 8537501) B8537501
theorem B1991771 : Blo 884570 1991771 := bstep (se 1 (by rfl) ⟨1493828, by rfl⟩ : syracuseStep 1991771 = 2987657) B2987657
theorem B3368375 : Blo 884570 3368375 := bstep (se 1 (by rfl) ⟨2526281, by rfl⟩ : syracuseStep 3368375 = 5052563) B5052563
theorem B4482863 : Blo 884570 4482863 := bstep (se 1 (by rfl) ⟨3362147, by rfl⟩ : syracuseStep 4482863 = 6724295) B6724295
theorem B2844553 : Blo 884570 2844553 := bstep (se 2 (by rfl) ⟨1066707, by rfl⟩ : syracuseStep 2844553 = 2133415) B2133415
theorem B10774529 : Blo 884570 10774529 := bstep (se 2 (by rfl) ⟨4040448, by rfl⟩ : syracuseStep 10774529 = 8080897) B8080897
theorem B24307721 : Blo 884570 24307721 := bstep (se 2 (by rfl) ⟨9115395, by rfl⟩ : syracuseStep 24307721 = 18230791) B18230791
theorem B8186123 : Blo 884570 8186123 := bstep (se 1 (by rfl) ⟨6139592, by rfl⟩ : syracuseStep 8186123 = 12279185) B12279185
theorem B20474171 : Blo 884570 20474171 := bstep (se 1 (by rfl) ⟨15355628, by rfl⟩ : syracuseStep 20474171 = 30711257) B30711257
theorem B7563739 : Blo 884570 7563739 := bstep (se 1 (by rfl) ⟨5672804, by rfl⟩ : syracuseStep 7563739 = 11345609) B11345609
theorem B7564013 : Blo 884570 7564013 := bstep (se 3 (by rfl) ⟨1418252, by rfl⟩ : syracuseStep 7564013 = 2836505) B2836505
theorem B3370319 : Blo 884570 3370319 := bstep (se 1 (by rfl) ⟨2527739, by rfl⟩ : syracuseStep 3370319 = 5055479) B5055479
theorem B1994111 : Blo 884570 1994111 := bstep (se 1 (by rfl) ⟨1495583, by rfl⟩ : syracuseStep 1994111 = 2991167) B2991167
theorem B6811361 : Blo 884570 6811361 := bstep (se 2 (by rfl) ⟨2554260, by rfl⟩ : syracuseStep 6811361 = 5108521) B5108521
theorem B1896539 : Blo 884570 1896539 := bstep (se 1 (by rfl) ⟨1422404, by rfl⟩ : syracuseStep 1896539 = 2844809) B2844809
theorem B1995047 : Blo 884570 1995047 := bstep (se 1 (by rfl) ⟨1496285, by rfl⟩ : syracuseStep 1995047 = 2992571) B2992571
theorem B17265581 : Blo 884570 17265581 := bstep (se 3 (by rfl) ⟨3237296, by rfl⟩ : syracuseStep 17265581 = 6474593) B6474593
theorem B3372475 : Blo 884570 3372475 := bstep (se 1 (by rfl) ⟨2529356, by rfl⟩ : syracuseStep 3372475 = 5058713) B5058713
theorem B1996667 : Blo 884570 1996667 := bstep (se 1 (by rfl) ⟨1497500, by rfl⟩ : syracuseStep 1996667 = 2995001) B2995001
theorem B4913531 : Blo 884570 4913531 := bstep (se 1 (by rfl) ⟨3685148, by rfl⟩ : syracuseStep 4913531 = 7370297) B7370297
theorem B4487561 : Blo 884570 4487561 := bstep (se 2 (by rfl) ⟨1682835, by rfl⟩ : syracuseStep 4487561 = 3365671) B3365671
theorem B1997243 : Blo 884570 1997243 := bstep (se 1 (by rfl) ⟨1497932, by rfl⟩ : syracuseStep 1997243 = 2995865) B2995865
theorem B19200563 : Blo 884570 19200563 := bstep (se 1 (by rfl) ⟨14400422, by rfl⟩ : syracuseStep 19200563 = 28800845) B28800845
theorem B3373751 : Blo 884570 3373751 := bstep (se 1 (by rfl) ⟨2530313, by rfl⟩ : syracuseStep 3373751 = 5060627) B5060627
theorem B415464389 : Blo 884570 415464389 := bstep (se 4 (by rfl) ⟨38949786, by rfl⟩ : syracuseStep 415464389 = 77899573) B77899573
theorem B7568387 : Blo 884570 7568387 := bstep (se 1 (by rfl) ⟨5676290, by rfl⟩ : syracuseStep 7568387 = 11352581) B11352581
theorem B1997945 : Blo 884570 1997945 := bstep (se 2 (by rfl) ⟨749229, by rfl⟩ : syracuseStep 1997945 = 1498459) B1498459
theorem B1998683 : Blo 884570 1998683 := bstep (se 1 (by rfl) ⟨1499012, by rfl⟩ : syracuseStep 1998683 = 2998025) B2998025
theorem B884671 : Blo 884570 884671 := bstep (se 1 (by rfl) ⟨663503, by rfl⟩ : syracuseStep 884671 = 1327007) B1327007
theorem B884731 : Blo 884570 884731 := bstep (se 1 (by rfl) ⟨663548, by rfl⟩ : syracuseStep 884731 = 1327097) B1327097
theorem B884767 : Blo 884570 884767 := bstep (se 1 (by rfl) ⟨663575, by rfl⟩ : syracuseStep 884767 = 1327151) B1327151
theorem B884783 : Blo 884570 884783 := bstep (se 1 (by rfl) ⟨663587, by rfl⟩ : syracuseStep 884783 = 1327175) B1327175
theorem B1998971 : Blo 884570 1998971 := bstep (se 1 (by rfl) ⟨1499228, by rfl⟩ : syracuseStep 1998971 = 2998457) B2998457
theorem B884903 : Blo 884570 884903 := bstep (se 1 (by rfl) ⟨663677, by rfl⟩ : syracuseStep 884903 = 1327355) B1327355
theorem B884987 : Blo 884570 884987 := bstep (se 1 (by rfl) ⟨663740, by rfl⟩ : syracuseStep 884987 = 1327481) B1327481
theorem B885095 : Blo 884570 885095 := bstep (se 1 (by rfl) ⟨663821, by rfl⟩ : syracuseStep 885095 = 1327643) B1327643
theorem B885183 : Blo 884570 885183 := bstep (se 1 (by rfl) ⟨663887, by rfl⟩ : syracuseStep 885183 = 1327775) B1327775
theorem B885215 : Blo 884570 885215 := bstep (se 1 (by rfl) ⟨663911, by rfl⟩ : syracuseStep 885215 = 1327823) B1327823
theorem B885295 : Blo 884570 885295 := bstep (se 1 (by rfl) ⟨663971, by rfl⟩ : syracuseStep 885295 = 1327943) B1327943
theorem B885339 : Blo 884570 885339 := bstep (se 1 (by rfl) ⟨664004, by rfl⟩ : syracuseStep 885339 = 1328009) B1328009
theorem B2524243 : Blo 884570 2524243 := bstep (se 1 (by rfl) ⟨1893182, by rfl⟩ : syracuseStep 2524243 = 3786365) B3786365
theorem B24249593 : Blo 884570 24249593 := bstep (se 2 (by rfl) ⟨9093597, by rfl⟩ : syracuseStep 24249593 = 18187195) B18187195
theorem B4261679 : Blo 884570 4261679 := bstep (se 1 (by rfl) ⟨3196259, by rfl⟩ : syracuseStep 4261679 = 6392519) B6392519
theorem B4261985 : Blo 884570 4261985 := bstep (se 2 (by rfl) ⟨1598244, by rfl⟩ : syracuseStep 4261985 = 3196489) B3196489
theorem B886951 : Blo 884570 886951 := bstep (se 1 (by rfl) ⟨665213, by rfl⟩ : syracuseStep 886951 = 1330427) B1330427
theorem B887231 : Blo 884570 887231 := bstep (se 1 (by rfl) ⟨665423, by rfl⟩ : syracuseStep 887231 = 1330847) B1330847
theorem B887451 : Blo 884570 887451 := bstep (se 1 (by rfl) ⟨665588, by rfl⟩ : syracuseStep 887451 = 1331177) B1331177
theorem B887487 : Blo 884570 887487 := bstep (se 1 (by rfl) ⟨665615, by rfl⟩ : syracuseStep 887487 = 1331231) B1331231
theorem B887839 : Blo 884570 887839 := bstep (se 1 (by rfl) ⟨665879, by rfl⟩ : syracuseStep 887839 = 1331759) B1331759
theorem B98339903 : Blo 884570 98339903 := bstep (se 1 (by rfl) ⟨73754927, by rfl⟩ : syracuseStep 98339903 = 147509855) B147509855
theorem B887963 : Blo 884570 887963 := bstep (se 1 (by rfl) ⟨665972, by rfl⟩ : syracuseStep 887963 = 1331945) B1331945
theorem B109186217 : Blo 884570 109186217 := bstep (se 2 (by rfl) ⟨40944831, by rfl⟩ : syracuseStep 109186217 = 81889663) B81889663
theorem B6065383 : Blo 884570 6065383 := bstep (se 1 (by rfl) ⟨4549037, by rfl⟩ : syracuseStep 6065383 = 9098075) B9098075
theorem B888059 : Blo 884570 888059 := bstep (se 1 (by rfl) ⟨666044, by rfl⟩ : syracuseStep 888059 = 1332089) B1332089
theorem B888527 : Blo 884570 888527 := bstep (se 1 (by rfl) ⟨666395, by rfl⟩ : syracuseStep 888527 = 1332791) B1332791
theorem B13635535 : Blo 884570 13635535 := bstep (se 1 (by rfl) ⟨10226651, by rfl⟩ : syracuseStep 13635535 = 20453303) B20453303
theorem B5051105 : Blo 884570 5051105 := bstep (se 2 (by rfl) ⟨1894164, by rfl⟩ : syracuseStep 5051105 = 3788329) B3788329
theorem B9114619 : Blo 884570 9114619 := bstep (se 1 (by rfl) ⟨6835964, by rfl⟩ : syracuseStep 9114619 = 13671929) B13671929
theorem B1513199 : Blo 884570 1513199 := bstep (se 1 (by rfl) ⟨1134899, by rfl⟩ : syracuseStep 1513199 = 2269799) B2269799
theorem B15177779 : Blo 884570 15177779 := bstep (se 1 (by rfl) ⟨11383334, by rfl⟩ : syracuseStep 15177779 = 22766669) B22766669
theorem B2562299 : Blo 884570 2562299 := bstep (se 1 (by rfl) ⟨1921724, by rfl⟩ : syracuseStep 2562299 = 3843449) B3843449
theorem B2988521 : Blo 884570 2988521 := bstep (se 2 (by rfl) ⟨1120695, by rfl⟩ : syracuseStep 2988521 = 2241391) B2241391
theorem B2988575 : Blo 884570 2988575 := bstep (se 1 (by rfl) ⟨2241431, by rfl⟩ : syracuseStep 2988575 = 4482863) B4482863
theorem B7183019 : Blo 884570 7183019 := bstep (se 1 (by rfl) ⟨5387264, by rfl⟩ : syracuseStep 7183019 = 10774529) B10774529
theorem B4496633 : Blo 884570 4496633 := bstep (se 2 (by rfl) ⟨1686237, by rfl⟩ : syracuseStep 4496633 = 3372475) B3372475
theorem B15147161 : Blo 884570 15147161 := bstep (se 2 (by rfl) ⟨5680185, by rfl⟩ : syracuseStep 15147161 = 11360371) B11360371
theorem B11510387 : Blo 884570 11510387 := bstep (se 1 (by rfl) ⟨8632790, by rfl⟩ : syracuseStep 11510387 = 17265581) B17265581
theorem B3416827 : Blo 884570 3416827 := bstep (se 1 (by rfl) ⟨2562620, by rfl⟩ : syracuseStep 3416827 = 5125241) B5125241
theorem B18162643 : Blo 884570 18162643 := bstep (se 1 (by rfl) ⟨13621982, by rfl⟩ : syracuseStep 18162643 = 27243965) B27243965
theorem B2991113 : Blo 884570 2991113 := bstep (se 2 (by rfl) ⟨1121667, by rfl⟩ : syracuseStep 2991113 = 2243335) B2243335
theorem B2991707 : Blo 884570 2991707 := bstep (se 1 (by rfl) ⟨2243780, by rfl⟩ : syracuseStep 2991707 = 4487561) B4487561
theorem B5057437 : Blo 884570 5057437 := bstep (se 3 (by rfl) ⟨948269, by rfl⟩ : syracuseStep 5057437 = 1896539) B1896539
theorem B5057711 : Blo 884570 5057711 := bstep (se 1 (by rfl) ⟨3793283, by rfl⟩ : syracuseStep 5057711 = 7586567) B7586567
theorem B2241371 : Blo 884570 2241371 := bstep (se 1 (by rfl) ⟨1681028, by rfl⟩ : syracuseStep 2241371 = 3362057) B3362057
theorem B3191993 : Blo 884570 3191993 := bstep (se 2 (by rfl) ⟨1196997, by rfl⟩ : syracuseStep 3191993 = 2393995) B2393995
theorem B2242313 : Blo 884570 2242313 := bstep (se 2 (by rfl) ⟨840867, by rfl⟩ : syracuseStep 2242313 = 1681735) B1681735
theorem B997159 : Blo 884570 997159 := bstep (se 1 (by rfl) ⟨747869, by rfl⟩ : syracuseStep 997159 = 1495739) B1495739
theorem B249083909 : Blo 884570 249083909 := bstep (se 4 (by rfl) ⟨23351616, by rfl⟩ : syracuseStep 249083909 = 46703233) B46703233
theorem B4864063 : Blo 884570 4864063 := bstep (se 1 (by rfl) ⟨3648047, by rfl⟩ : syracuseStep 4864063 = 7296095) B7296095
theorem B2242667 : Blo 884570 2242667 := bstep (se 1 (by rfl) ⟨1682000, by rfl⟩ : syracuseStep 2242667 = 3364001) B3364001
theorem B2242687 : Blo 884570 2242687 := bstep (se 1 (by rfl) ⟨1682015, by rfl⟩ : syracuseStep 2242687 = 3364031) B3364031
theorem B5126813 : Blo 884570 5126813 := bstep (se 3 (by rfl) ⟨961277, by rfl⟩ : syracuseStep 5126813 = 1922555) B1922555
theorem B998095 : Blo 884570 998095 := bstep (se 1 (by rfl) ⟨748571, by rfl⟩ : syracuseStep 998095 = 1497143) B1497143
theorem B2243497 : Blo 884570 2243497 := bstep (se 2 (by rfl) ⟨841311, by rfl⟩ : syracuseStep 2243497 = 1682623) B1682623
theorem B36453361 : Blo 884570 36453361 := bstep (se 2 (by rfl) ⟨13670010, by rfl⟩ : syracuseStep 36453361 = 27340021) B27340021
theorem B2243639 : Blo 884570 2243639 := bstep (se 1 (by rfl) ⟨1682729, by rfl⟩ : syracuseStep 2243639 = 3365459) B3365459
theorem B28720655 : Blo 884570 28720655 := bstep (se 1 (by rfl) ⟨21540491, by rfl⟩ : syracuseStep 28720655 = 43080983) B43080983
theorem B2997917 : Blo 884570 2997917 := bstep (se 3 (by rfl) ⟨562109, by rfl⟩ : syracuseStep 2997917 = 1124219) B1124219
theorem B2998241 : Blo 884570 2998241 := bstep (se 2 (by rfl) ⟨1124340, by rfl⟩ : syracuseStep 2998241 = 2248681) B2248681
theorem B1327145 : Blo 884570 1327145 := bstep (se 2 (by rfl) ⟨497679, by rfl⟩ : syracuseStep 1327145 = 995359) B995359
theorem B2244905 : Blo 884570 2244905 := bstep (se 2 (by rfl) ⟨841839, by rfl⟩ : syracuseStep 2244905 = 1683679) B1683679
theorem B1327595 : Blo 884570 1327595 := bstep (se 1 (by rfl) ⟨995696, by rfl⟩ : syracuseStep 1327595 = 1991393) B1991393
theorem B2245279 : Blo 884570 2245279 := bstep (se 1 (by rfl) ⟨1683959, by rfl⟩ : syracuseStep 2245279 = 3367919) B3367919
theorem B1327847 : Blo 884570 1327847 := bstep (se 1 (by rfl) ⟨995885, by rfl⟩ : syracuseStep 1327847 = 1991771) B1991771
theorem B2245583 : Blo 884570 2245583 := bstep (se 1 (by rfl) ⟨1684187, by rfl⟩ : syracuseStep 2245583 = 3368375) B3368375
theorem B1328393 : Blo 884570 1328393 := bstep (se 2 (by rfl) ⟨498147, by rfl⟩ : syracuseStep 1328393 = 996295) B996295
theorem B5686595 : Blo 884570 5686595 := bstep (se 1 (by rfl) ⟨4264946, by rfl⟩ : syracuseStep 5686595 = 8529893) B8529893
theorem B16205147 : Blo 884570 16205147 := bstep (se 1 (by rfl) ⟨12153860, by rfl⟩ : syracuseStep 16205147 = 24307721) B24307721
theorem B5457415 : Blo 884570 5457415 := bstep (se 1 (by rfl) ⟨4093061, by rfl⟩ : syracuseStep 5457415 = 8186123) B8186123
theorem B13649447 : Blo 884570 13649447 := bstep (se 1 (by rfl) ⟨10237085, by rfl⟩ : syracuseStep 13649447 = 20474171) B20474171
theorem B1328873 : Blo 884570 1328873 := bstep (se 2 (by rfl) ⟨498327, by rfl⟩ : syracuseStep 1328873 = 996655) B996655
theorem B4310921 : Blo 884570 4310921 := bstep (se 2 (by rfl) ⟨1616595, by rfl⟩ : syracuseStep 4310921 = 3233191) B3233191
theorem B6998057 : Blo 884570 6998057 := bstep (se 2 (by rfl) ⟨2624271, by rfl⟩ : syracuseStep 6998057 = 5248543) B5248543
theorem B2279567 : Blo 884570 2279567 := bstep (se 1 (by rfl) ⟨1709675, by rfl⟩ : syracuseStep 2279567 = 3419351) B3419351
theorem B2246879 : Blo 884570 2246879 := bstep (se 1 (by rfl) ⟨1685159, by rfl⟩ : syracuseStep 2246879 = 3370319) B3370319
theorem B1329407 : Blo 884570 1329407 := bstep (se 1 (by rfl) ⟨997055, by rfl⟩ : syracuseStep 1329407 = 1994111) B1994111
theorem B4540907 : Blo 884570 4540907 := bstep (se 1 (by rfl) ⟨3405680, by rfl⟩ : syracuseStep 4540907 = 6811361) B6811361
theorem B1330031 : Blo 884570 1330031 := bstep (se 1 (by rfl) ⟨997523, by rfl⟩ : syracuseStep 1330031 = 1995047) B1995047
theorem B137940083 : Blo 884570 137940083 := bstep (se 1 (by rfl) ⟨103455062, by rfl⟩ : syracuseStep 137940083 = 206910125) B206910125
theorem B1494335 : Blo 884570 1494335 := bstep (se 1 (by rfl) ⟨1120751, by rfl⟩ : syracuseStep 1494335 = 2241503) B2241503
theorem B1494767 : Blo 884570 1494767 := bstep (se 1 (by rfl) ⟨1121075, by rfl⟩ : syracuseStep 1494767 = 2242151) B2242151
theorem B1331111 : Blo 884570 1331111 := bstep (se 1 (by rfl) ⟨998333, by rfl⟩ : syracuseStep 1331111 = 1996667) B1996667
theorem B6737903 : Blo 884570 6737903 := bstep (se 1 (by rfl) ⟨5053427, by rfl⟩ : syracuseStep 6737903 = 10106855) B10106855
theorem B1331369 : Blo 884570 1331369 := bstep (se 2 (by rfl) ⟨499263, by rfl⟩ : syracuseStep 1331369 = 998527) B998527
theorem B1331495 : Blo 884570 1331495 := bstep (se 1 (by rfl) ⟨998621, by rfl⟩ : syracuseStep 1331495 = 1997243) B1997243
theorem B12800375 : Blo 884570 12800375 := bstep (se 1 (by rfl) ⟨9600281, by rfl⟩ : syracuseStep 12800375 = 19200563) B19200563
theorem B2249167 : Blo 884570 2249167 := bstep (se 1 (by rfl) ⟨1686875, by rfl⟩ : syracuseStep 2249167 = 3373751) B3373751
theorem B276976259 : Blo 884570 276976259 := bstep (se 1 (by rfl) ⟨207732194, by rfl⟩ : syracuseStep 276976259 = 415464389) B415464389
theorem B1331963 : Blo 884570 1331963 := bstep (se 1 (by rfl) ⟨998972, by rfl⟩ : syracuseStep 1331963 = 1997945) B1997945
theorem B3789935 : Blo 884570 3789935 := bstep (se 1 (by rfl) ⟨2842451, by rfl⟩ : syracuseStep 3789935 = 5684903) B5684903
theorem B1332455 : Blo 884570 1332455 := bstep (se 1 (by rfl) ⟨999341, by rfl⟩ : syracuseStep 1332455 = 1998683) B1998683
theorem B1332827 : Blo 884570 1332827 := bstep (se 1 (by rfl) ⟨999620, by rfl⟩ : syracuseStep 1332827 = 1999241) B1999241
theorem B9591635 : Blo 884570 9591635 := bstep (se 1 (by rfl) ⟨7193726, by rfl⟩ : syracuseStep 9591635 = 14387453) B14387453
theorem B7199597 : Blo 884570 7199597 := bstep (se 3 (by rfl) ⟨1349924, by rfl⟩ : syracuseStep 7199597 = 2699849) B2699849
theorem B9329627 : Blo 884570 9329627 := bstep (se 1 (by rfl) ⟨6997220, by rfl⟩ : syracuseStep 9329627 = 13994441) B13994441
theorem B3464329 : Blo 884570 3464329 := bstep (se 2 (by rfl) ⟨1299123, by rfl⟩ : syracuseStep 3464329 = 2598247) B2598247
theorem B1498729 : Blo 884570 1498729 := bstep (se 2 (by rfl) ⟨562023, by rfl⟩ : syracuseStep 1498729 = 1124047) B1124047
theorem B3792737 : Blo 884570 3792737 := bstep (se 2 (by rfl) ⟨1422276, by rfl⟩ : syracuseStep 3792737 = 2844553) B2844553
theorem B4546655 : Blo 884570 4546655 := bstep (se 1 (by rfl) ⟨3409991, by rfl⟩ : syracuseStep 4546655 = 6819983) B6819983
theorem B1990817 : Blo 884570 1990817 := bstep (se 2 (by rfl) ⟨746556, by rfl⟩ : syracuseStep 1990817 = 1493113) B1493113
theorem B3596831 : Blo 884570 3596831 := bstep (se 1 (by rfl) ⟨2697623, by rfl⟩ : syracuseStep 3596831 = 5395247) B5395247
theorem B10084985 : Blo 884570 10084985 := bstep (se 2 (by rfl) ⟨3781869, by rfl⟩ : syracuseStep 10084985 = 7563739) B7563739
theorem B8512283 : Blo 884570 8512283 := bstep (se 1 (by rfl) ⟨6384212, by rfl⟩ : syracuseStep 8512283 = 12768425) B12768425
theorem B1599167 : Blo 884570 1599167 := bstep (se 1 (by rfl) ⟨1199375, by rfl⟩ : syracuseStep 1599167 = 2398751) B2398751
theorem B1992923 : Blo 884570 1992923 := bstep (se 1 (by rfl) ⟨1494692, by rfl⟩ : syracuseStep 1992923 = 2989385) B2989385
theorem B2157263 : Blo 884570 2157263 := bstep (se 1 (by rfl) ⟨1617947, by rfl⟩ : syracuseStep 2157263 = 3235895) B3235895
theorem B1796987 : Blo 884570 1796987 := bstep (se 1 (by rfl) ⟨1347740, by rfl⟩ : syracuseStep 1796987 = 2695481) B2695481
theorem B1993697 : Blo 884570 1993697 := bstep (se 2 (by rfl) ⟨747636, by rfl⟩ : syracuseStep 1993697 = 1495273) B1495273
theorem B1993895 : Blo 884570 1993895 := bstep (se 1 (by rfl) ⟨1495421, by rfl⟩ : syracuseStep 1993895 = 2990843) B2990843
theorem B2125919 : Blo 884570 2125919 := bstep (se 1 (by rfl) ⟨1594439, by rfl⟩ : syracuseStep 2125919 = 3188879) B3188879
theorem B946399 : Blo 884570 946399 := bstep (se 1 (by rfl) ⟨709799, by rfl⟩ : syracuseStep 946399 = 1419599) B1419599
theorem B1994975 : Blo 884570 1994975 := bstep (se 1 (by rfl) ⟨1496231, by rfl⟩ : syracuseStep 1994975 = 2992463) B2992463
theorem B1995065 : Blo 884570 1995065 := bstep (se 2 (by rfl) ⟨748149, by rfl⟩ : syracuseStep 1995065 = 1496299) B1496299
theorem B7565723 : Blo 884570 7565723 := bstep (se 1 (by rfl) ⟨5674292, by rfl⟩ : syracuseStep 7565723 = 11348585) B11348585
theorem B5042675 : Blo 884570 5042675 := bstep (se 1 (by rfl) ⟨3782006, by rfl⟩ : syracuseStep 5042675 = 7564013) B7564013
theorem B1995263 : Blo 884570 1995263 := bstep (se 1 (by rfl) ⟨1496447, by rfl⟩ : syracuseStep 1995263 = 2992895) B2992895
theorem B13464797 : Blo 884570 13464797 := bstep (se 3 (by rfl) ⟨2524649, by rfl⟩ : syracuseStep 13464797 = 5049299) B5049299
theorem B9598463 : Blo 884570 9598463 := bstep (se 1 (by rfl) ⟨7198847, by rfl⟩ : syracuseStep 9598463 = 14397695) B14397695
theorem B15169031 : Blo 884570 15169031 := bstep (se 1 (by rfl) ⟨11376773, by rfl⟩ : syracuseStep 15169031 = 22753547) B22753547
theorem B1996361 : Blo 884570 1996361 := bstep (se 2 (by rfl) ⟨748635, by rfl⟩ : syracuseStep 1996361 = 1497271) B1497271
theorem B1997135 : Blo 884570 1997135 := bstep (se 1 (by rfl) ⟨1497851, by rfl⟩ : syracuseStep 1997135 = 2995703) B2995703
theorem B3275687 : Blo 884570 3275687 := bstep (se 1 (by rfl) ⟨2456765, by rfl⟩ : syracuseStep 3275687 = 4913531) B4913531
theorem B5045273 : Blo 884570 5045273 := bstep (se 2 (by rfl) ⟨1891977, by rfl⟩ : syracuseStep 5045273 = 3783955) B3783955
theorem B1997855 : Blo 884570 1997855 := bstep (se 1 (by rfl) ⟨1498391, by rfl⟩ : syracuseStep 1997855 = 2996783) B2996783
theorem B11500775 : Blo 884570 11500775 := bstep (se 1 (by rfl) ⟨8625581, by rfl⟩ : syracuseStep 11500775 = 17251163) B17251163
theorem B5045591 : Blo 884570 5045591 := bstep (se 1 (by rfl) ⟨3784193, by rfl⟩ : syracuseStep 5045591 = 7568387) B7568387
theorem B10255835 : Blo 884570 10255835 := bstep (se 1 (by rfl) ⟨7691876, by rfl⟩ : syracuseStep 10255835 = 15383753) B15383753
theorem B14384719 : Blo 884570 14384719 := bstep (se 1 (by rfl) ⟨10788539, by rfl⟩ : syracuseStep 14384719 = 21577079) B21577079
theorem B884607 : Blo 884570 884607 := bstep (se 1 (by rfl) ⟨663455, by rfl⟩ : syracuseStep 884607 = 1326911) B1326911
theorem B884763 : Blo 884570 884763 := bstep (se 1 (by rfl) ⟨663572, by rfl⟩ : syracuseStep 884763 = 1327145) B1327145
theorem B885063 : Blo 884570 885063 := bstep (se 1 (by rfl) ⟨663797, by rfl⟩ : syracuseStep 885063 = 1327595) B1327595
theorem B885231 : Blo 884570 885231 := bstep (se 1 (by rfl) ⟨663923, by rfl⟩ : syracuseStep 885231 = 1327847) B1327847
theorem B885595 : Blo 884570 885595 := bstep (se 1 (by rfl) ⟨664196, by rfl⟩ : syracuseStep 885595 = 1328393) B1328393
theorem B4555769 : Blo 884570 4555769 := bstep (se 2 (by rfl) ⟨1708413, by rfl⟩ : syracuseStep 4555769 = 3416827) B3416827
theorem B885915 : Blo 884570 885915 := bstep (se 1 (by rfl) ⟨664436, by rfl⟩ : syracuseStep 885915 = 1328873) B1328873
theorem B24216857 : Blo 884570 24216857 := bstep (se 2 (by rfl) ⟨9081321, by rfl⟩ : syracuseStep 24216857 = 18162643) B18162643
theorem B886271 : Blo 884570 886271 := bstep (se 1 (by rfl) ⟨664703, by rfl⟩ : syracuseStep 886271 = 1329407) B1329407
theorem B886687 : Blo 884570 886687 := bstep (se 1 (by rfl) ⟨665015, by rfl⟩ : syracuseStep 886687 = 1330031) B1330031
theorem B7276553 : Blo 884570 7276553 := bstep (se 2 (by rfl) ⟨2728707, by rfl⟩ : syracuseStep 7276553 = 5457415) B5457415
theorem B887407 : Blo 884570 887407 := bstep (se 1 (by rfl) ⟨665555, by rfl⟩ : syracuseStep 887407 = 1331111) B1331111
theorem B4491935 : Blo 884570 4491935 := bstep (se 1 (by rfl) ⟨3368951, by rfl⟩ : syracuseStep 4491935 = 6737903) B6737903
theorem B887579 : Blo 884570 887579 := bstep (se 1 (by rfl) ⟨665684, by rfl⟩ : syracuseStep 887579 = 1331369) B1331369
theorem B887663 : Blo 884570 887663 := bstep (se 1 (by rfl) ⟨665747, by rfl⟩ : syracuseStep 887663 = 1331495) B1331495
theorem B184650839 : Blo 884570 184650839 := bstep (se 1 (by rfl) ⟨138488129, by rfl⟩ : syracuseStep 184650839 = 276976259) B276976259
theorem B887975 : Blo 884570 887975 := bstep (se 1 (by rfl) ⟨665981, by rfl⟩ : syracuseStep 887975 = 1331963) B1331963
theorem B2526623 : Blo 884570 2526623 := bstep (se 1 (by rfl) ⟨1894967, by rfl⟩ : syracuseStep 2526623 = 3789935) B3789935
theorem B888303 : Blo 884570 888303 := bstep (se 1 (by rfl) ⟨666227, by rfl⟩ : syracuseStep 888303 = 1332455) B1332455
theorem B888551 : Blo 884570 888551 := bstep (se 1 (by rfl) ⟨666413, by rfl⟩ : syracuseStep 888551 = 1332827) B1332827
theorem B1708199 : Blo 884570 1708199 := bstep (se 1 (by rfl) ⟨1281149, by rfl⟩ : syracuseStep 1708199 = 2562299) B2562299
theorem B4264445 : Blo 884570 4264445 := bstep (se 3 (by rfl) ⟨799583, by rfl⟩ : syracuseStep 4264445 = 1599167) B1599167
theorem B6394423 : Blo 884570 6394423 := bstep (se 1 (by rfl) ⟨4795817, by rfl⟩ : syracuseStep 6394423 = 9591635) B9591635
theorem B4035197 : Blo 884570 4035197 := bstep (se 3 (by rfl) ⟨756599, by rfl⟩ : syracuseStep 4035197 = 1513199) B1513199
theorem B2528491 : Blo 884570 2528491 := bstep (se 1 (by rfl) ⟨1896368, by rfl⟩ : syracuseStep 2528491 = 3792737) B3792737
theorem B10098107 : Blo 884570 10098107 := bstep (se 1 (by rfl) ⟨7573580, by rfl⟩ : syracuseStep 10098107 = 15147161) B15147161
theorem B2397887 : Blo 884570 2397887 := bstep (se 1 (by rfl) ⟨1798415, by rfl⟩ : syracuseStep 2397887 = 3596831) B3596831
theorem B7673591 : Blo 884570 7673591 := bstep (se 1 (by rfl) ⟨5755193, by rfl⟩ : syracuseStep 7673591 = 11510387) B11510387
theorem B6723323 : Blo 884570 6723323 := bstep (se 1 (by rfl) ⟨5042492, by rfl⟩ : syracuseStep 6723323 = 10084985) B10084985
theorem B5674855 : Blo 884570 5674855 := bstep (se 1 (by rfl) ⟨4256141, by rfl⟩ : syracuseStep 5674855 = 8512283) B8512283
theorem B4791965 : Blo 884570 4791965 := bstep (se 3 (by rfl) ⟨898493, by rfl⟩ : syracuseStep 4791965 = 1796987) B1796987
theorem B24879005 : Blo 884570 24879005 := bstep (se 3 (by rfl) ⟨4664813, by rfl⟩ : syracuseStep 24879005 = 9329627) B9329627
theorem B1417279 : Blo 884570 1417279 := bstep (se 1 (by rfl) ⟨1062959, by rfl⟩ : syracuseStep 1417279 = 2125919) B2125919
theorem B2990249 : Blo 884570 2990249 := bstep (se 2 (by rfl) ⟨1121343, by rfl⟩ : syracuseStep 2990249 = 2242687) B2242687
theorem B6398975 : Blo 884570 6398975 := bstep (se 1 (by rfl) ⟨4799231, by rfl⟩ : syracuseStep 6398975 = 9598463) B9598463
theorem B2991329 : Blo 884570 2991329 := bstep (se 2 (by rfl) ⟨1121748, by rfl⟩ : syracuseStep 2991329 = 2243497) B2243497
theorem B48604481 : Blo 884570 48604481 := bstep (se 2 (by rfl) ⟨18226680, by rfl⟩ : syracuseStep 48604481 = 36453361) B36453361
theorem B3417875 : Blo 884570 3417875 := bstep (se 1 (by rfl) ⟨2563406, by rfl⟩ : syracuseStep 3417875 = 5126813) B5126813
theorem B19179625 : Blo 884570 19179625 := bstep (se 2 (by rfl) ⟨7192359, by rfl⟩ : syracuseStep 19179625 = 14384719) B14384719
theorem B19147103 : Blo 884570 19147103 := bstep (se 1 (by rfl) ⟨14360327, by rfl⟩ : syracuseStep 19147103 = 28720655) B28720655
theorem B16166395 : Blo 884570 16166395 := bstep (se 1 (by rfl) ⟨12124796, by rfl⟩ : syracuseStep 16166395 = 24249593) B24249593
theorem B2993705 : Blo 884570 2993705 := bstep (se 2 (by rfl) ⟨1122639, by rfl⟩ : syracuseStep 2993705 = 2245279) B2245279
theorem B4665371 : Blo 884570 4665371 := bstep (se 1 (by rfl) ⟨3499028, by rfl⟩ : syracuseStep 4665371 = 6998057) B6998057
theorem B1519711 : Blo 884570 1519711 := bstep (se 1 (by rfl) ⟨1139783, by rfl⟩ : syracuseStep 1519711 = 2279567) B2279567
theorem B91960055 : Blo 884570 91960055 := bstep (se 1 (by rfl) ⟨68970041, by rfl⟩ : syracuseStep 91960055 = 137940083) B137940083
theorem B72790811 : Blo 884570 72790811 := bstep (se 1 (by rfl) ⟨54593108, by rfl⟩ : syracuseStep 72790811 = 109186217) B109186217
theorem B996223 : Blo 884570 996223 := bstep (se 1 (by rfl) ⟨747167, by rfl⟩ : syracuseStep 996223 = 1494335) B1494335
theorem B996511 : Blo 884570 996511 := bstep (se 1 (by rfl) ⟨747383, by rfl⟩ : syracuseStep 996511 = 1494767) B1494767
theorem B8533583 : Blo 884570 8533583 := bstep (se 1 (by rfl) ⟨6400187, by rfl⟩ : syracuseStep 8533583 = 12800375) B12800375
theorem B4799731 : Blo 884570 4799731 := bstep (se 1 (by rfl) ⟨3599798, by rfl⟩ : syracuseStep 4799731 = 7199597) B7199597
theorem B2997755 : Blo 884570 2997755 := bstep (se 1 (by rfl) ⟨2248316, by rfl⟩ : syracuseStep 2997755 = 4496633) B4496633
theorem B3031103 : Blo 884570 3031103 := bstep (se 1 (by rfl) ⟨2273327, by rfl⟩ : syracuseStep 3031103 = 4546655) B4546655
theorem B1327211 : Blo 884570 1327211 := bstep (se 1 (by rfl) ⟨995408, by rfl⟩ : syracuseStep 1327211 = 1990817) B1990817
theorem B1261865 : Blo 884570 1261865 := bstep (se 2 (by rfl) ⟨473199, by rfl⟩ : syracuseStep 1261865 = 946399) B946399
theorem B2998889 : Blo 884570 2998889 := bstep (se 2 (by rfl) ⟨1124583, by rfl⟩ : syracuseStep 2998889 = 2249167) B2249167
theorem B12109085 : Blo 884570 12109085 := bstep (se 3 (by rfl) ⟨2270453, by rfl⟩ : syracuseStep 12109085 = 4540907) B4540907
theorem B1328615 : Blo 884570 1328615 := bstep (se 1 (by rfl) ⟨996461, by rfl⟩ : syracuseStep 1328615 = 1992923) B1992923
theorem B19154717 : Blo 884570 19154717 := bstep (se 3 (by rfl) ⟨3591509, by rfl⟩ : syracuseStep 19154717 = 7183019) B7183019
theorem B1329131 : Blo 884570 1329131 := bstep (se 1 (by rfl) ⟨996848, by rfl⟩ : syracuseStep 1329131 = 1993697) B1993697
theorem B1329263 : Blo 884570 1329263 := bstep (se 1 (by rfl) ⟨996947, by rfl⟩ : syracuseStep 1329263 = 1993895) B1993895
theorem B1329545 : Blo 884570 1329545 := bstep (se 2 (by rfl) ⟨498579, by rfl⟩ : syracuseStep 1329545 = 997159) B997159
theorem B1329983 : Blo 884570 1329983 := bstep (se 1 (by rfl) ⟨997487, by rfl⟩ : syracuseStep 1329983 = 1994975) B1994975
theorem B1330043 : Blo 884570 1330043 := bstep (se 1 (by rfl) ⟨997532, by rfl⟩ : syracuseStep 1330043 = 1995065) B1995065
theorem B3361783 : Blo 884570 3361783 := bstep (se 1 (by rfl) ⟨2521337, by rfl⟩ : syracuseStep 3361783 = 5042675) B5042675
theorem B1330175 : Blo 884570 1330175 := bstep (se 1 (by rfl) ⟨997631, by rfl⟩ : syracuseStep 1330175 = 1995263) B1995263
theorem B1494247 : Blo 884570 1494247 := bstep (se 1 (by rfl) ⟨1120685, by rfl⟩ : syracuseStep 1494247 = 2241371) B2241371
theorem B1330793 : Blo 884570 1330793 := bstep (se 2 (by rfl) ⟨499047, by rfl⟩ : syracuseStep 1330793 = 998095) B998095
theorem B10112687 : Blo 884570 10112687 := bstep (se 1 (by rfl) ⟨7584515, by rfl⟩ : syracuseStep 10112687 = 15169031) B15169031
theorem B1330907 : Blo 884570 1330907 := bstep (se 1 (by rfl) ⟨998180, by rfl⟩ : syracuseStep 1330907 = 1996361) B1996361
theorem B1494875 : Blo 884570 1494875 := bstep (se 1 (by rfl) ⟨1121156, by rfl⟩ : syracuseStep 1494875 = 2242313) B2242313
theorem B166055939 : Blo 884570 166055939 := bstep (se 1 (by rfl) ⟨124541954, by rfl⟩ : syracuseStep 166055939 = 249083909) B249083909
theorem B1495111 : Blo 884570 1495111 := bstep (se 1 (by rfl) ⟨1121333, by rfl⟩ : syracuseStep 1495111 = 2242667) B2242667
theorem B1331423 : Blo 884570 1331423 := bstep (se 1 (by rfl) ⟨998567, by rfl⟩ : syracuseStep 1331423 = 1997135) B1997135
theorem B2183791 : Blo 884570 2183791 := bstep (se 1 (by rfl) ⟨1637843, by rfl⟩ : syracuseStep 2183791 = 3275687) B3275687
theorem B3363515 : Blo 884570 3363515 := bstep (se 1 (by rfl) ⟨2522636, by rfl⟩ : syracuseStep 3363515 = 5045273) B5045273
theorem B1331903 : Blo 884570 1331903 := bstep (se 1 (by rfl) ⟨998927, by rfl⟩ : syracuseStep 1331903 = 1997855) B1997855
theorem B1495759 : Blo 884570 1495759 := bstep (se 1 (by rfl) ⟨1121819, by rfl⟩ : syracuseStep 1495759 = 2243639) B2243639
theorem B3363727 : Blo 884570 3363727 := bstep (se 1 (by rfl) ⟨2522795, by rfl⟩ : syracuseStep 3363727 = 5045591) B5045591
theorem B6837223 : Blo 884570 6837223 := bstep (se 1 (by rfl) ⟨5127917, by rfl⟩ : syracuseStep 6837223 = 10255835) B10255835
theorem B1332647 : Blo 884570 1332647 := bstep (se 1 (by rfl) ⟨999485, by rfl⟩ : syracuseStep 1332647 = 1998971) B1998971
theorem B1496603 : Blo 884570 1496603 := bstep (se 1 (by rfl) ⟨1122452, by rfl⟩ : syracuseStep 1496603 = 2244905) B2244905
theorem B1497055 : Blo 884570 1497055 := bstep (se 1 (by rfl) ⟨1122791, by rfl⟩ : syracuseStep 1497055 = 2245583) B2245583
theorem B3791063 : Blo 884570 3791063 := bstep (se 1 (by rfl) ⟨2843297, by rfl⟩ : syracuseStep 3791063 = 5686595) B5686595
theorem B10803431 : Blo 884570 10803431 := bstep (se 1 (by rfl) ⟨8102573, by rfl⟩ : syracuseStep 10803431 = 16205147) B16205147
theorem B9099631 : Blo 884570 9099631 := bstep (se 1 (by rfl) ⟨6824723, by rfl⟩ : syracuseStep 9099631 = 13649447) B13649447
theorem B2841119 : Blo 884570 2841119 := bstep (se 1 (by rfl) ⟨2130839, by rfl⟩ : syracuseStep 2841119 = 4261679) B4261679
theorem B2841323 : Blo 884570 2841323 := bstep (se 1 (by rfl) ⟨2130992, by rfl⟩ : syracuseStep 2841323 = 4261985) B4261985
theorem B3365657 : Blo 884570 3365657 := bstep (se 2 (by rfl) ⟨1262121, by rfl⟩ : syracuseStep 3365657 = 2524243) B2524243
theorem B1497919 : Blo 884570 1497919 := bstep (se 1 (by rfl) ⟨1123439, by rfl⟩ : syracuseStep 1497919 = 2246879) B2246879
theorem B65559935 : Blo 884570 65559935 := bstep (se 1 (by rfl) ⟨49169951, by rfl⟩ : syracuseStep 65559935 = 98339903) B98339903
theorem B3367403 : Blo 884570 3367403 := bstep (se 1 (by rfl) ⟨2525552, by rfl⟩ : syracuseStep 3367403 = 5051105) B5051105
theorem B35906125 : Blo 884570 35906125 := bstep (se 3 (by rfl) ⟨6732398, by rfl⟩ : syracuseStep 35906125 = 13464797) B13464797
theorem B6743249 : Blo 884570 6743249 := bstep (se 2 (by rfl) ⟨2528718, by rfl⟩ : syracuseStep 6743249 = 5057437) B5057437
theorem B10118519 : Blo 884570 10118519 := bstep (se 1 (by rfl) ⟨7588889, by rfl⟩ : syracuseStep 10118519 = 15177779) B15177779
theorem B8087177 : Blo 884570 8087177 := bstep (se 2 (by rfl) ⟨3032691, by rfl⟩ : syracuseStep 8087177 = 6065383) B6065383
theorem B1992347 : Blo 884570 1992347 := bstep (se 1 (by rfl) ⟨1494260, by rfl⟩ : syracuseStep 1992347 = 2988521) B2988521
theorem B1992383 : Blo 884570 1992383 := bstep (se 1 (by rfl) ⟨1494287, by rfl⟩ : syracuseStep 1992383 = 2988575) B2988575
theorem B11495789 : Blo 884570 11495789 := bstep (se 3 (by rfl) ⟨2155460, by rfl⟩ : syracuseStep 11495789 = 4310921) B4310921
theorem B18180713 : Blo 884570 18180713 := bstep (se 2 (by rfl) ⟨6817767, by rfl⟩ : syracuseStep 18180713 = 13635535) B13635535
theorem B1994075 : Blo 884570 1994075 := bstep (se 1 (by rfl) ⟨1495556, by rfl⟩ : syracuseStep 1994075 = 2991113) B2991113
theorem B1994471 : Blo 884570 1994471 := bstep (se 1 (by rfl) ⟨1495853, by rfl⟩ : syracuseStep 1994471 = 2991707) B2991707
theorem B12152825 : Blo 884570 12152825 := bstep (se 2 (by rfl) ⟨4557309, by rfl⟩ : syracuseStep 12152825 = 9114619) B9114619
theorem B1438175 : Blo 884570 1438175 := bstep (se 1 (by rfl) ⟨1078631, by rfl⟩ : syracuseStep 1438175 = 2157263) B2157263
theorem B3371807 : Blo 884570 3371807 := bstep (se 1 (by rfl) ⟨2528855, by rfl⟩ : syracuseStep 3371807 = 5057711) B5057711
theorem B6485417 : Blo 884570 6485417 := bstep (se 2 (by rfl) ⟨2432031, by rfl⟩ : syracuseStep 6485417 = 4864063) B4864063
theorem B5043815 : Blo 884570 5043815 := bstep (se 1 (by rfl) ⟨3782861, by rfl⟩ : syracuseStep 5043815 = 7565723) B7565723
theorem B2127995 : Blo 884570 2127995 := bstep (se 1 (by rfl) ⟨1595996, by rfl⟩ : syracuseStep 2127995 = 3191993) B3191993
theorem B4619105 : Blo 884570 4619105 := bstep (se 2 (by rfl) ⟨1732164, by rfl⟩ : syracuseStep 4619105 = 3464329) B3464329
theorem B1998305 : Blo 884570 1998305 := bstep (se 2 (by rfl) ⟨749364, by rfl⟩ : syracuseStep 1998305 = 1498729) B1498729
theorem B7667183 : Blo 884570 7667183 := bstep (se 1 (by rfl) ⟨5750387, by rfl⟩ : syracuseStep 7667183 = 11500775) B11500775
theorem B1998611 : Blo 884570 1998611 := bstep (se 1 (by rfl) ⟨1498958, by rfl⟩ : syracuseStep 1998611 = 2997917) B2997917
theorem B1998827 : Blo 884570 1998827 := bstep (se 1 (by rfl) ⟨1499120, by rfl⟩ : syracuseStep 1998827 = 2998241) B2998241
theorem B884807 : Blo 884570 884807 := bstep (se 1 (by rfl) ⟨663605, by rfl⟩ : syracuseStep 884807 = 1327211) B1327211
theorem B1999259 : Blo 884570 1999259 := bstep (se 1 (by rfl) ⟨1499444, by rfl⟩ : syracuseStep 1999259 = 2998889) B2998889
theorem B47874833 : Blo 884570 47874833 := bstep (se 2 (by rfl) ⟨17953062, by rfl⟩ : syracuseStep 47874833 = 35906125) B35906125
theorem B885743 : Blo 884570 885743 := bstep (se 1 (by rfl) ⟨664307, by rfl⟩ : syracuseStep 885743 = 1328615) B1328615
theorem B3835133 : Blo 884570 3835133 := bstep (se 3 (by rfl) ⟨719087, by rfl⟩ : syracuseStep 3835133 = 1438175) B1438175
theorem B886087 : Blo 884570 886087 := bstep (se 1 (by rfl) ⟨664565, by rfl⟩ : syracuseStep 886087 = 1329131) B1329131
theorem B11371853 : Blo 884570 11371853 := bstep (se 3 (by rfl) ⟨2132222, by rfl⟩ : syracuseStep 11371853 = 4264445) B4264445
theorem B4851035 : Blo 884570 4851035 := bstep (se 1 (by rfl) ⟨3638276, by rfl⟩ : syracuseStep 4851035 = 7276553) B7276553
theorem B886175 : Blo 884570 886175 := bstep (se 1 (by rfl) ⟨664631, by rfl⟩ : syracuseStep 886175 = 1329263) B1329263
theorem B886363 : Blo 884570 886363 := bstep (se 1 (by rfl) ⟨664772, by rfl⟩ : syracuseStep 886363 = 1329545) B1329545
theorem B886655 : Blo 884570 886655 := bstep (se 1 (by rfl) ⟨664991, by rfl⟩ : syracuseStep 886655 = 1329983) B1329983
theorem B886695 : Blo 884570 886695 := bstep (se 1 (by rfl) ⟨665021, by rfl⟩ : syracuseStep 886695 = 1330043) B1330043
theorem B886783 : Blo 884570 886783 := bstep (se 1 (by rfl) ⟨665087, by rfl⟩ : syracuseStep 886783 = 1330175) B1330175
theorem B887195 : Blo 884570 887195 := bstep (se 1 (by rfl) ⟨665396, by rfl⟩ : syracuseStep 887195 = 1330793) B1330793
theorem B887271 : Blo 884570 887271 := bstep (se 1 (by rfl) ⟨665453, by rfl⟩ : syracuseStep 887271 = 1330907) B1330907
theorem B887615 : Blo 884570 887615 := bstep (se 1 (by rfl) ⟨665711, by rfl⟩ : syracuseStep 887615 = 1331423) B1331423
theorem B2690131 : Blo 884570 2690131 := bstep (se 1 (by rfl) ⟨2017598, by rfl⟩ : syracuseStep 2690131 = 4035197) B4035197
theorem B887935 : Blo 884570 887935 := bstep (se 1 (by rfl) ⟨665951, by rfl⟩ : syracuseStep 887935 = 1331903) B1331903
theorem B888431 : Blo 884570 888431 := bstep (se 1 (by rfl) ⟨666323, by rfl⟩ : syracuseStep 888431 = 1332647) B1332647
theorem B5115727 : Blo 884570 5115727 := bstep (se 1 (by rfl) ⟨3836795, by rfl⟩ : syracuseStep 5115727 = 7673591) B7673591
theorem B2527375 : Blo 884570 2527375 := bstep (se 1 (by rfl) ⟨1895531, by rfl⟩ : syracuseStep 2527375 = 3791063) B3791063
theorem B16586003 : Blo 884570 16586003 := bstep (se 1 (by rfl) ⟨12439502, by rfl⟩ : syracuseStep 16586003 = 24879005) B24879005
theorem B4265983 : Blo 884570 4265983 := bstep (se 1 (by rfl) ⟨3199487, by rfl⟩ : syracuseStep 4265983 = 6398975) B6398975
theorem B8525897 : Blo 884570 8525897 := bstep (se 2 (by rfl) ⟨3197211, by rfl⟩ : syracuseStep 8525897 = 6394423) B6394423
theorem B4495499 : Blo 884570 4495499 := bstep (se 1 (by rfl) ⟨3371624, by rfl⟩ : syracuseStep 4495499 = 6743249) B6743249
theorem B9116297 : Blo 884570 9116297 := bstep (se 2 (by rfl) ⟨3418611, by rfl⟩ : syracuseStep 9116297 = 6837223) B6837223
theorem B7576861 : Blo 884570 7576861 := bstep (se 3 (by rfl) ⟨1420661, by rfl⟩ : syracuseStep 7576861 = 2841323) B2841323
theorem B8101883 : Blo 884570 8101883 := bstep (se 1 (by rfl) ⟨6076412, by rfl⟩ : syracuseStep 8101883 = 12152825) B12152825
theorem B12132841 : Blo 884570 12132841 := bstep (se 2 (by rfl) ⟨4549815, by rfl⟩ : syracuseStep 12132841 = 9099631) B9099631
theorem B1418663 : Blo 884570 1418663 := bstep (se 1 (by rfl) ⟨1063997, by rfl⟩ : syracuseStep 1418663 = 2127995) B2127995
theorem B6399641 : Blo 884570 6399641 := bstep (se 2 (by rfl) ⟨2399865, by rfl⟩ : syracuseStep 6399641 = 4799731) B4799731
theorem B8105125 : Blo 884570 8105125 := bstep (se 4 (by rfl) ⟨759855, by rfl⟩ : syracuseStep 8105125 = 1519711) B1519711
theorem B8072723 : Blo 884570 8072723 := bstep (se 1 (by rfl) ⟨6054542, by rfl⟩ : syracuseStep 8072723 = 12109085) B12109085
theorem B2994623 : Blo 884570 2994623 := bstep (se 1 (by rfl) ⟨2245967, by rfl⟩ : syracuseStep 2994623 = 4491935) B4491935
theorem B1684415 : Blo 884570 1684415 := bstep (se 1 (by rfl) ⟨1263311, by rfl⟩ : syracuseStep 1684415 = 2526623) B2526623
theorem B996583 : Blo 884570 996583 := bstep (se 1 (by rfl) ⟨747437, by rfl⟩ : syracuseStep 996583 = 1494875) B1494875
theorem B110703959 : Blo 884570 110703959 := bstep (se 1 (by rfl) ⟨83027969, by rfl⟩ : syracuseStep 110703959 = 166055939) B166055939
theorem B25572833 : Blo 884570 25572833 := bstep (se 2 (by rfl) ⟨9589812, by rfl⟩ : syracuseStep 25572833 = 19179625) B19179625
theorem B2242343 : Blo 884570 2242343 := bstep (se 1 (by rfl) ⟨1681757, by rfl⟩ : syracuseStep 2242343 = 3363515) B3363515
theorem B6732071 : Blo 884570 6732071 := bstep (se 1 (by rfl) ⟨5049053, by rfl⟩ : syracuseStep 6732071 = 10098107) B10098107
theorem B997735 : Blo 884570 997735 := bstep (se 1 (by rfl) ⟨748301, by rfl⟩ : syracuseStep 997735 = 1496603) B1496603
theorem B2243771 : Blo 884570 2243771 := bstep (se 1 (by rfl) ⟨1682828, by rfl⟩ : syracuseStep 2243771 = 3365657) B3365657
theorem B2244935 : Blo 884570 2244935 := bstep (se 1 (by rfl) ⟨1683701, by rfl⟩ : syracuseStep 2244935 = 3367403) B3367403
theorem B5391451 : Blo 884570 5391451 := bstep (se 1 (by rfl) ⟨4043588, by rfl⟩ : syracuseStep 5391451 = 8087177) B8087177
theorem B1328231 : Blo 884570 1328231 := bstep (se 1 (by rfl) ⟨996173, by rfl⟩ : syracuseStep 1328231 = 1992347) B1992347
theorem B1328255 : Blo 884570 1328255 := bstep (se 1 (by rfl) ⟨996191, by rfl⟩ : syracuseStep 1328255 = 1992383) B1992383
theorem B1328297 : Blo 884570 1328297 := bstep (se 2 (by rfl) ⟨498111, by rfl⟩ : syracuseStep 1328297 = 996223) B996223
theorem B2278583 : Blo 884570 2278583 := bstep (se 1 (by rfl) ⟨1708937, by rfl⟩ : syracuseStep 2278583 = 3417875) B3417875
theorem B1328681 : Blo 884570 1328681 := bstep (se 2 (by rfl) ⟨498255, by rfl⟩ : syracuseStep 1328681 = 996511) B996511
theorem B12764735 : Blo 884570 12764735 := bstep (se 1 (by rfl) ⟨9573551, by rfl⟩ : syracuseStep 12764735 = 19147103) B19147103
theorem B1329383 : Blo 884570 1329383 := bstep (se 1 (by rfl) ⟨997037, by rfl⟩ : syracuseStep 1329383 = 1994075) B1994075
theorem B1329647 : Blo 884570 1329647 := bstep (se 1 (by rfl) ⟨997235, by rfl⟩ : syracuseStep 1329647 = 1994471) B1994471
theorem B2247871 : Blo 884570 2247871 := bstep (se 1 (by rfl) ⟨1685903, by rfl⟩ : syracuseStep 2247871 = 3371807) B3371807
theorem B5689055 : Blo 884570 5689055 := bstep (se 1 (by rfl) ⟨4266791, by rfl⟩ : syracuseStep 5689055 = 8533583) B8533583
theorem B3362543 : Blo 884570 3362543 := bstep (se 1 (by rfl) ⟨2521907, by rfl⟩ : syracuseStep 3362543 = 5043815) B5043815
theorem B1332203 : Blo 884570 1332203 := bstep (se 1 (by rfl) ⟨999152, by rfl⟩ : syracuseStep 1332203 = 1998305) B1998305
theorem B1332407 : Blo 884570 1332407 := bstep (se 1 (by rfl) ⟨999305, by rfl⟩ : syracuseStep 1332407 = 1998611) B1998611
theorem B1332551 : Blo 884570 1332551 := bstep (se 1 (by rfl) ⟨999413, by rfl⟩ : syracuseStep 1332551 = 1998827) B1998827
theorem B2020735 : Blo 884570 2020735 := bstep (se 1 (by rfl) ⟨1515551, by rfl⟩ : syracuseStep 2020735 = 3031103) B3031103
theorem B12440989 : Blo 884570 12440989 := bstep (se 3 (by rfl) ⟨2332685, by rfl⟩ : syracuseStep 12440989 = 4665371) B4665371
theorem B1889705 : Blo 884570 1889705 := bstep (se 2 (by rfl) ⟨708639, by rfl⟩ : syracuseStep 1889705 = 1417279) B1417279
theorem B3364973 : Blo 884570 3364973 := bstep (se 3 (by rfl) ⟨630932, by rfl⟩ : syracuseStep 3364973 = 1261865) B1261865
theorem B16144571 : Blo 884570 16144571 := bstep (se 1 (by rfl) ⟨12108428, by rfl⟩ : syracuseStep 16144571 = 24216857) B24216857
theorem B12769811 : Blo 884570 12769811 := bstep (se 1 (by rfl) ⟨9577358, by rfl⟩ : syracuseStep 12769811 = 19154717) B19154717
theorem B123100559 : Blo 884570 123100559 := bstep (se 1 (by rfl) ⟨92325419, by rfl⟩ : syracuseStep 123100559 = 184650839) B184650839
theorem B6741791 : Blo 884570 6741791 := bstep (se 1 (by rfl) ⟨5056343, by rfl⟩ : syracuseStep 6741791 = 10112687) B10112687
theorem B12148717 : Blo 884570 12148717 := bstep (se 3 (by rfl) ⟨2277884, by rfl⟩ : syracuseStep 12148717 = 4555769) B4555769
theorem B1138799 : Blo 884570 1138799 := bstep (se 1 (by rfl) ⟨854099, by rfl⟩ : syracuseStep 1138799 = 1708199) B1708199
theorem B1598591 : Blo 884570 1598591 := bstep (se 1 (by rfl) ⟨1198943, by rfl⟩ : syracuseStep 1598591 = 2397887) B2397887
theorem B4482215 : Blo 884570 4482215 := bstep (se 1 (by rfl) ⟨3361661, by rfl⟩ : syracuseStep 4482215 = 6723323) B6723323
theorem B4482377 : Blo 884570 4482377 := bstep (se 2 (by rfl) ⟨1680891, by rfl⟩ : syracuseStep 4482377 = 3361783) B3361783
theorem B7202287 : Blo 884570 7202287 := bstep (se 1 (by rfl) ⟨5401715, by rfl⟩ : syracuseStep 7202287 = 10803431) B10803431
theorem B1992329 : Blo 884570 1992329 := bstep (se 2 (by rfl) ⟨747123, by rfl⟩ : syracuseStep 1992329 = 1494247) B1494247
theorem B1894079 : Blo 884570 1894079 := bstep (se 1 (by rfl) ⟨1420559, by rfl⟩ : syracuseStep 1894079 = 2841119) B2841119
theorem B21555193 : Blo 884570 21555193 := bstep (se 2 (by rfl) ⟨8083197, by rfl⟩ : syracuseStep 21555193 = 16166395) B16166395
theorem B43706623 : Blo 884570 43706623 := bstep (se 1 (by rfl) ⟨32779967, by rfl⟩ : syracuseStep 43706623 = 65559935) B65559935
theorem B1993481 : Blo 884570 1993481 := bstep (se 2 (by rfl) ⟨747555, by rfl⟩ : syracuseStep 1993481 = 1495111) B1495111
theorem B1993499 : Blo 884570 1993499 := bstep (se 1 (by rfl) ⟨1495124, by rfl⟩ : syracuseStep 1993499 = 2990249) B2990249
theorem B2911721 : Blo 884570 2911721 := bstep (se 2 (by rfl) ⟨1091895, by rfl⟩ : syracuseStep 2911721 = 2183791) B2183791
theorem B1994219 : Blo 884570 1994219 := bstep (se 1 (by rfl) ⟨1495664, by rfl⟩ : syracuseStep 1994219 = 2991329) B2991329
theorem B32402987 : Blo 884570 32402987 := bstep (se 1 (by rfl) ⟨24302240, by rfl⟩ : syracuseStep 32402987 = 48604481) B48604481
theorem B6745679 : Blo 884570 6745679 := bstep (se 1 (by rfl) ⟨5059259, by rfl⟩ : syracuseStep 6745679 = 10118519) B10118519
theorem B1994345 : Blo 884570 1994345 := bstep (se 2 (by rfl) ⟨747879, by rfl⟩ : syracuseStep 1994345 = 1495759) B1495759
theorem B4484969 : Blo 884570 4484969 := bstep (se 2 (by rfl) ⟨1681863, by rfl⟩ : syracuseStep 4484969 = 3363727) B3363727
theorem B7663859 : Blo 884570 7663859 := bstep (se 1 (by rfl) ⟨5747894, by rfl⟩ : syracuseStep 7663859 = 11495789) B11495789
theorem B3371321 : Blo 884570 3371321 := bstep (se 2 (by rfl) ⟨1264245, by rfl⟩ : syracuseStep 3371321 = 2528491) B2528491
theorem B12120475 : Blo 884570 12120475 := bstep (se 1 (by rfl) ⟨9090356, by rfl⟩ : syracuseStep 12120475 = 18180713) B18180713
theorem B1995803 : Blo 884570 1995803 := bstep (se 1 (by rfl) ⟨1496852, by rfl⟩ : syracuseStep 1995803 = 2993705) B2993705
theorem B7566473 : Blo 884570 7566473 := bstep (se 2 (by rfl) ⟨2837427, by rfl⟩ : syracuseStep 7566473 = 5674855) B5674855
theorem B1996073 : Blo 884570 1996073 := bstep (se 2 (by rfl) ⟨748527, by rfl⟩ : syracuseStep 1996073 = 1497055) B1497055
theorem B61306703 : Blo 884570 61306703 := bstep (se 1 (by rfl) ⟨45980027, by rfl⟩ : syracuseStep 61306703 = 91960055) B91960055
theorem B48527207 : Blo 884570 48527207 := bstep (se 1 (by rfl) ⟨36395405, by rfl⟩ : syracuseStep 48527207 = 72790811) B72790811
theorem B4323611 : Blo 884570 4323611 := bstep (se 1 (by rfl) ⟨3242708, by rfl⟩ : syracuseStep 4323611 = 6485417) B6485417
theorem B1997225 : Blo 884570 1997225 := bstep (se 2 (by rfl) ⟨748959, by rfl⟩ : syracuseStep 1997225 = 1497919) B1497919
theorem B12778573 : Blo 884570 12778573 := bstep (se 3 (by rfl) ⟨2395982, by rfl⟩ : syracuseStep 12778573 = 4791965) B4791965
theorem B3079403 : Blo 884570 3079403 := bstep (se 1 (by rfl) ⟨2309552, by rfl⟩ : syracuseStep 3079403 = 4619105) B4619105
theorem B5111455 : Blo 884570 5111455 := bstep (se 1 (by rfl) ⟨3833591, by rfl⟩ : syracuseStep 5111455 = 7667183) B7667183
theorem B1998503 : Blo 884570 1998503 := bstep (se 1 (by rfl) ⟨1498877, by rfl⟩ : syracuseStep 1998503 = 2997755) B2997755
theorem B31916555 : Blo 884570 31916555 := bstep (se 1 (by rfl) ⟨23937416, by rfl⟩ : syracuseStep 31916555 = 47874833) B47874833
theorem B885487 : Blo 884570 885487 := bstep (se 1 (by rfl) ⟨664115, by rfl⟩ : syracuseStep 885487 = 1328231) B1328231
theorem B885503 : Blo 884570 885503 := bstep (se 1 (by rfl) ⟨664127, by rfl⟩ : syracuseStep 885503 = 1328255) B1328255
theorem B885531 : Blo 884570 885531 := bstep (se 1 (by rfl) ⟨664148, by rfl⟩ : syracuseStep 885531 = 1328297) B1328297
theorem B2556755 : Blo 884570 2556755 := bstep (se 1 (by rfl) ⟨1917566, by rfl⟩ : syracuseStep 2556755 = 3835133) B3835133
theorem B885787 : Blo 884570 885787 := bstep (se 1 (by rfl) ⟨664340, by rfl⟩ : syracuseStep 885787 = 1328681) B1328681
theorem B886255 : Blo 884570 886255 := bstep (se 1 (by rfl) ⟨664691, by rfl⟩ : syracuseStep 886255 = 1329383) B1329383
theorem B886431 : Blo 884570 886431 := bstep (se 1 (by rfl) ⟨664823, by rfl⟩ : syracuseStep 886431 = 1329647) B1329647
theorem B9603049 : Blo 884570 9603049 := bstep (se 2 (by rfl) ⟨3601143, by rfl⟩ : syracuseStep 9603049 = 7202287) B7202287
theorem B4491773 : Blo 884570 4491773 := bstep (se 3 (by rfl) ⟨842207, by rfl⟩ : syracuseStep 4491773 = 1684415) B1684415
theorem B28740257 : Blo 884570 28740257 := bstep (se 2 (by rfl) ⟨10777596, by rfl⟩ : syracuseStep 28740257 = 21555193) B21555193
theorem B888135 : Blo 884570 888135 := bstep (se 1 (by rfl) ⟨666101, by rfl⟩ : syracuseStep 888135 = 1332203) B1332203
theorem B888271 : Blo 884570 888271 := bstep (se 1 (by rfl) ⟨666203, by rfl⟩ : syracuseStep 888271 = 1332407) B1332407
theorem B888367 : Blo 884570 888367 := bstep (se 1 (by rfl) ⟨666275, by rfl⟩ : syracuseStep 888367 = 1332551) B1332551
theorem B6820969 : Blo 884570 6820969 := bstep (se 2 (by rfl) ⟨2557863, by rfl⟩ : syracuseStep 6820969 = 5115727) B5115727
theorem B4494527 : Blo 884570 4494527 := bstep (se 1 (by rfl) ⟨3370895, by rfl⟩ : syracuseStep 4494527 = 6741791) B6741791
theorem B16160633 : Blo 884570 16160633 := bstep (se 2 (by rfl) ⟨6060237, by rfl⟩ : syracuseStep 16160633 = 12120475) B12120475
theorem B2988143 : Blo 884570 2988143 := bstep (se 1 (by rfl) ⟨2241107, by rfl⟩ : syracuseStep 2988143 = 4482215) B4482215
theorem B2988251 : Blo 884570 2988251 := bstep (se 1 (by rfl) ⟨2241188, by rfl⟩ : syracuseStep 2988251 = 4482377) B4482377
theorem B4266427 : Blo 884570 4266427 := bstep (se 1 (by rfl) ⟨3199820, by rfl⟩ : syracuseStep 4266427 = 6399641) B6399641
theorem B2694313 : Blo 884570 2694313 := bstep (se 2 (by rfl) ⟨1010367, by rfl⟩ : syracuseStep 2694313 = 2020735) B2020735
theorem B16587985 : Blo 884570 16587985 := bstep (se 2 (by rfl) ⟨6220494, by rfl⟩ : syracuseStep 16587985 = 12440989) B12440989
theorem B5381815 : Blo 884570 5381815 := bstep (se 1 (by rfl) ⟨4036361, by rfl⟩ : syracuseStep 5381815 = 8072723) B8072723
theorem B21601991 : Blo 884570 21601991 := bstep (se 1 (by rfl) ⟨16201493, by rfl⟩ : syracuseStep 21601991 = 32402987) B32402987
theorem B4497119 : Blo 884570 4497119 := bstep (se 1 (by rfl) ⟨3372839, by rfl⟩ : syracuseStep 4497119 = 6745679) B6745679
theorem B2989979 : Blo 884570 2989979 := bstep (se 1 (by rfl) ⟨2242484, by rfl⟩ : syracuseStep 2989979 = 4484969) B4484969
theorem B73802639 : Blo 884570 73802639 := bstep (se 1 (by rfl) ⟨55351979, by rfl⟩ : syracuseStep 73802639 = 110703959) B110703959
theorem B17048555 : Blo 884570 17048555 := bstep (se 1 (by rfl) ⟨12786416, by rfl⟩ : syracuseStep 17048555 = 25572833) B25572833
theorem B40871135 : Blo 884570 40871135 := bstep (se 1 (by rfl) ⟨30653351, by rfl⟩ : syracuseStep 40871135 = 61306703) B61306703
theorem B32351471 : Blo 884570 32351471 := bstep (se 1 (by rfl) ⟨24263603, by rfl⟩ : syracuseStep 32351471 = 48527207) B48527207
theorem B10102481 : Blo 884570 10102481 := bstep (se 2 (by rfl) ⟨3788430, by rfl⟩ : syracuseStep 10102481 = 7576861) B7576861
theorem B16198289 : Blo 884570 16198289 := bstep (se 2 (by rfl) ⟨6074358, by rfl⟩ : syracuseStep 16198289 = 12148717) B12148717
theorem B1519055 : Blo 884570 1519055 := bstep (se 1 (by rfl) ⟨1139291, by rfl⟩ : syracuseStep 1519055 = 2278583) B2278583
theorem B7581235 : Blo 884570 7581235 := bstep (se 1 (by rfl) ⟨5685926, by rfl⟩ : syracuseStep 7581235 = 11371853) B11371853
theorem B7188601 : Blo 884570 7188601 := bstep (se 2 (by rfl) ⟨2695725, by rfl⟩ : syracuseStep 7188601 = 5391451) B5391451
theorem B2241695 : Blo 884570 2241695 := bstep (se 1 (by rfl) ⟨1681271, by rfl⟩ : syracuseStep 2241695 = 3362543) B3362543
theorem B58275497 : Blo 884570 58275497 := bstep (se 2 (by rfl) ⟨21853311, by rfl⟩ : syracuseStep 58275497 = 43706623) B43706623
theorem B1259803 : Blo 884570 1259803 := bstep (se 1 (by rfl) ⟨944852, by rfl⟩ : syracuseStep 1259803 = 1889705) B1889705
theorem B5683931 : Blo 884570 5683931 := bstep (se 1 (by rfl) ⟨4262948, by rfl⟩ : syracuseStep 5683931 = 8525897) B8525897
theorem B2243315 : Blo 884570 2243315 := bstep (se 1 (by rfl) ⟨1682486, by rfl⟩ : syracuseStep 2243315 = 3364973) B3364973
theorem B2996999 : Blo 884570 2996999 := bstep (se 1 (by rfl) ⟨2247749, by rfl⟩ : syracuseStep 2996999 = 4495499) B4495499
theorem B3586841 : Blo 884570 3586841 := bstep (se 2 (by rfl) ⟨1345065, by rfl⟩ : syracuseStep 3586841 = 2690131) B2690131
theorem B10763047 : Blo 884570 10763047 := bstep (se 1 (by rfl) ⟨8072285, by rfl⟩ : syracuseStep 10763047 = 16144571) B16144571
theorem B2997161 : Blo 884570 2997161 := bstep (se 2 (by rfl) ⟨1123935, by rfl⟩ : syracuseStep 2997161 = 2247871) B2247871
theorem B6077531 : Blo 884570 6077531 := bstep (se 1 (by rfl) ⟨4558148, by rfl⟩ : syracuseStep 6077531 = 9116297) B9116297
theorem B82067039 : Blo 884570 82067039 := bstep (se 1 (by rfl) ⟨61550279, by rfl⟩ : syracuseStep 82067039 = 123100559) B123100559
theorem B1065727 : Blo 884570 1065727 := bstep (se 1 (by rfl) ⟨799295, by rfl⟩ : syracuseStep 1065727 = 1598591) B1598591
theorem B1328219 : Blo 884570 1328219 := bstep (se 1 (by rfl) ⟨996164, by rfl⟩ : syracuseStep 1328219 = 1992329) B1992329
theorem B1262719 : Blo 884570 1262719 := bstep (se 1 (by rfl) ⟨947039, by rfl⟩ : syracuseStep 1262719 = 1894079) B1894079
theorem B1328777 : Blo 884570 1328777 := bstep (se 2 (by rfl) ⟨498291, by rfl⟩ : syracuseStep 1328777 = 996583) B996583
theorem B1328987 : Blo 884570 1328987 := bstep (se 1 (by rfl) ⟨996740, by rfl⟩ : syracuseStep 1328987 = 1993481) B1993481
theorem B1328999 : Blo 884570 1328999 := bstep (se 1 (by rfl) ⟨996749, by rfl⟩ : syracuseStep 1328999 = 1993499) B1993499
theorem B1329479 : Blo 884570 1329479 := bstep (se 1 (by rfl) ⟨997109, by rfl⟩ : syracuseStep 1329479 = 1994219) B1994219
theorem B1329563 : Blo 884570 1329563 := bstep (se 1 (by rfl) ⟨997172, by rfl⟩ : syracuseStep 1329563 = 1994345) B1994345
theorem B5687977 : Blo 884570 5687977 := bstep (se 2 (by rfl) ⟨2132991, by rfl⟩ : syracuseStep 5687977 = 4265983) B4265983
theorem B2247547 : Blo 884570 2247547 := bstep (se 1 (by rfl) ⟨1685660, by rfl⟩ : syracuseStep 2247547 = 3371321) B3371321
theorem B1330313 : Blo 884570 1330313 := bstep (se 2 (by rfl) ⟨498867, by rfl⟩ : syracuseStep 1330313 = 997735) B997735
theorem B1330535 : Blo 884570 1330535 := bstep (se 1 (by rfl) ⟨997901, by rfl⟩ : syracuseStep 1330535 = 1995803) B1995803
theorem B1330715 : Blo 884570 1330715 := bstep (se 1 (by rfl) ⟨998036, by rfl⟩ : syracuseStep 1330715 = 1996073) B1996073
theorem B1494895 : Blo 884570 1494895 := bstep (se 1 (by rfl) ⟨1121171, by rfl⟩ : syracuseStep 1494895 = 2242343) B2242343
theorem B1331483 : Blo 884570 1331483 := bstep (se 1 (by rfl) ⟨998612, by rfl⟩ : syracuseStep 1331483 = 1997225) B1997225
theorem B1495847 : Blo 884570 1495847 := bstep (se 1 (by rfl) ⟨1121885, by rfl⟩ : syracuseStep 1495847 = 2243771) B2243771
theorem B2052935 : Blo 884570 2052935 := bstep (se 1 (by rfl) ⟨1539701, by rfl⟩ : syracuseStep 2052935 = 3079403) B3079403
theorem B1332335 : Blo 884570 1332335 := bstep (se 1 (by rfl) ⟨999251, by rfl⟩ : syracuseStep 1332335 = 1998503) B1998503
theorem B1496623 : Blo 884570 1496623 := bstep (se 1 (by rfl) ⟨1122467, by rfl⟩ : syracuseStep 1496623 = 2244935) B2244935
theorem B1332839 : Blo 884570 1332839 := bstep (se 1 (by rfl) ⟨999629, by rfl⟩ : syracuseStep 1332839 = 1999259) B1999259
theorem B3036797 : Blo 884570 3036797 := bstep (se 3 (by rfl) ⟨569399, by rfl⟩ : syracuseStep 3036797 = 1138799) B1138799
theorem B16177121 : Blo 884570 16177121 := bstep (se 2 (by rfl) ⟨6066420, by rfl⟩ : syracuseStep 16177121 = 12132841) B12132841
theorem B3234023 : Blo 884570 3234023 := bstep (se 1 (by rfl) ⟨2425517, by rfl⟩ : syracuseStep 3234023 = 4851035) B4851035
theorem B8509823 : Blo 884570 8509823 := bstep (se 1 (by rfl) ⟨6382367, by rfl⟩ : syracuseStep 8509823 = 12764735) B12764735
theorem B3792703 : Blo 884570 3792703 := bstep (se 1 (by rfl) ⟨2844527, by rfl⟩ : syracuseStep 3792703 = 5689055) B5689055
theorem B44229341 : Blo 884570 44229341 := bstep (se 3 (by rfl) ⟨8293001, by rfl⟩ : syracuseStep 44229341 = 16586003) B16586003
theorem B10806833 : Blo 884570 10806833 := bstep (se 2 (by rfl) ⟨4052562, by rfl⟩ : syracuseStep 10806833 = 8105125) B8105125
theorem B8513207 : Blo 884570 8513207 := bstep (se 1 (by rfl) ⟨6384905, by rfl⟩ : syracuseStep 8513207 = 12769811) B12769811
theorem B5401255 : Blo 884570 5401255 := bstep (se 1 (by rfl) ⟨4050941, by rfl⟩ : syracuseStep 5401255 = 8101883) B8101883
theorem B3369833 : Blo 884570 3369833 := bstep (se 2 (by rfl) ⟨1263687, by rfl⟩ : syracuseStep 3369833 = 2527375) B2527375
theorem B945775 : Blo 884570 945775 := bstep (se 1 (by rfl) ⟨709331, by rfl⟩ : syracuseStep 945775 = 1418663) B1418663
theorem B5109239 : Blo 884570 5109239 := bstep (se 1 (by rfl) ⟨3831929, by rfl⟩ : syracuseStep 5109239 = 7663859) B7663859
theorem B1996415 : Blo 884570 1996415 := bstep (se 1 (by rfl) ⟨1497311, by rfl⟩ : syracuseStep 1996415 = 2994623) B2994623
theorem B5044315 : Blo 884570 5044315 := bstep (se 1 (by rfl) ⟨3783236, by rfl⟩ : syracuseStep 5044315 = 7566473) B7566473
theorem B7764589 : Blo 884570 7764589 := bstep (se 3 (by rfl) ⟨1455860, by rfl⟩ : syracuseStep 7764589 = 2911721) B2911721
theorem B17038097 : Blo 884570 17038097 := bstep (se 2 (by rfl) ⟨6389286, by rfl⟩ : syracuseStep 17038097 = 12778573) B12778573
theorem B2882407 : Blo 884570 2882407 := bstep (se 1 (by rfl) ⟨2161805, by rfl⟩ : syracuseStep 2882407 = 4323611) B4323611
theorem B4488047 : Blo 884570 4488047 := bstep (se 1 (by rfl) ⟨3366035, by rfl⟩ : syracuseStep 4488047 = 6732071) B6732071
theorem B6815273 : Blo 884570 6815273 := bstep (se 2 (by rfl) ⟨2555727, by rfl⟩ : syracuseStep 6815273 = 5111455) B5111455
theorem B1704503 : Blo 884570 1704503 := bstep (se 1 (by rfl) ⟨1278377, by rfl⟩ : syracuseStep 1704503 = 2556755) B2556755
theorem B885479 : Blo 884570 885479 := bstep (se 1 (by rfl) ⟨664109, by rfl⟩ : syracuseStep 885479 = 1328219) B1328219
theorem B885851 : Blo 884570 885851 := bstep (se 1 (by rfl) ⟨664388, by rfl⟩ : syracuseStep 885851 = 1328777) B1328777
theorem B885991 : Blo 884570 885991 := bstep (se 1 (by rfl) ⟨664493, by rfl⟩ : syracuseStep 885991 = 1328987) B1328987
theorem B885999 : Blo 884570 885999 := bstep (se 1 (by rfl) ⟨664499, by rfl⟩ : syracuseStep 885999 = 1328999) B1328999
theorem B6718949 : Blo 884570 6718949 := bstep (se 4 (by rfl) ⟨629901, by rfl⟩ : syracuseStep 6718949 = 1259803) B1259803
theorem B886319 : Blo 884570 886319 := bstep (se 1 (by rfl) ⟨664739, by rfl⟩ : syracuseStep 886319 = 1329479) B1329479
theorem B886375 : Blo 884570 886375 := bstep (se 1 (by rfl) ⟨664781, by rfl⟩ : syracuseStep 886375 = 1329563) B1329563
theorem B886875 : Blo 884570 886875 := bstep (se 1 (by rfl) ⟨665156, by rfl⟩ : syracuseStep 886875 = 1330313) B1330313
theorem B887023 : Blo 884570 887023 := bstep (se 1 (by rfl) ⟨665267, by rfl⟩ : syracuseStep 887023 = 1330535) B1330535
theorem B887143 : Blo 884570 887143 := bstep (se 1 (by rfl) ⟨665357, by rfl⟩ : syracuseStep 887143 = 1330715) B1330715
theorem B887655 : Blo 884570 887655 := bstep (se 1 (by rfl) ⟨665741, by rfl⟩ : syracuseStep 887655 = 1331483) B1331483
theorem B888223 : Blo 884570 888223 := bstep (se 1 (by rfl) ⟨666167, by rfl⟩ : syracuseStep 888223 = 1332335) B1332335
theorem B888559 : Blo 884570 888559 := bstep (se 1 (by rfl) ⟨666419, by rfl⟩ : syracuseStep 888559 = 1332839) B1332839
theorem B10784747 : Blo 884570 10784747 := bstep (se 1 (by rfl) ⟨8088560, by rfl⟩ : syracuseStep 10784747 = 16177121) B16177121
theorem B5673215 : Blo 884570 5673215 := bstep (se 1 (by rfl) ⟨4254911, by rfl⟩ : syracuseStep 5673215 = 8509823) B8509823
theorem B21567647 : Blo 884570 21567647 := bstep (se 1 (by rfl) ⟨16175735, by rfl⟩ : syracuseStep 21567647 = 32351471) B32351471
theorem B5675471 : Blo 884570 5675471 := bstep (se 1 (by rfl) ⟨4256603, by rfl⟩ : syracuseStep 5675471 = 8513207) B8513207
theorem B6725753 : Blo 884570 6725753 := bstep (se 2 (by rfl) ⟨2522157, by rfl⟩ : syracuseStep 6725753 = 5044315) B5044315
theorem B3843209 : Blo 884570 3843209 := bstep (se 2 (by rfl) ⟨1441203, by rfl⟩ : syracuseStep 3843209 = 2882407) B2882407
theorem B2992031 : Blo 884570 2992031 := bstep (se 1 (by rfl) ⟨2244023, by rfl⟩ : syracuseStep 2992031 = 4488047) B4488047
theorem B5056937 : Blo 884570 5056937 := bstep (se 2 (by rfl) ⟨1896351, by rfl⟩ : syracuseStep 5056937 = 3792703) B3792703
theorem B21277703 : Blo 884570 21277703 := bstep (se 1 (by rfl) ⟨15958277, by rfl⟩ : syracuseStep 21277703 = 31916555) B31916555
theorem B2994515 : Blo 884570 2994515 := bstep (se 1 (by rfl) ⟨2245886, by rfl⟩ : syracuseStep 2994515 = 4491773) B4491773
theorem B997231 : Blo 884570 997231 := bstep (se 1 (by rfl) ⟨747923, by rfl⟩ : syracuseStep 997231 = 1495847) B1495847
theorem B2996351 : Blo 884570 2996351 := bstep (se 1 (by rfl) ⟨2247263, by rfl⟩ : syracuseStep 2996351 = 4494527) B4494527
theorem B7583969 : Blo 884570 7583969 := bstep (se 2 (by rfl) ⟨2843988, by rfl⟩ : syracuseStep 7583969 = 5687977) B5687977
theorem B2996729 : Blo 884570 2996729 := bstep (se 2 (by rfl) ⟨1123773, by rfl⟩ : syracuseStep 2996729 = 2247547) B2247547
theorem B5683877 : Blo 884570 5683877 := bstep (se 4 (by rfl) ⟨532863, by rfl⟩ : syracuseStep 5683877 = 1065727) B1065727
theorem B155401325 : Blo 884570 155401325 := bstep (se 3 (by rfl) ⟨29137748, by rfl⟩ : syracuseStep 155401325 = 58275497) B58275497
theorem B10108313 : Blo 884570 10108313 := bstep (se 2 (by rfl) ⟨3790617, by rfl⟩ : syracuseStep 10108313 = 7581235) B7581235
theorem B14401327 : Blo 884570 14401327 := bstep (se 1 (by rfl) ⟨10800995, by rfl⟩ : syracuseStep 14401327 = 21601991) B21601991
theorem B2998079 : Blo 884570 2998079 := bstep (se 1 (by rfl) ⟨2248559, by rfl⟩ : syracuseStep 2998079 = 4497119) B4497119
theorem B9584801 : Blo 884570 9584801 := bstep (se 2 (by rfl) ⟨3594300, by rfl⟩ : syracuseStep 9584801 = 7188601) B7188601
theorem B49201759 : Blo 884570 49201759 := bstep (se 1 (by rfl) ⟨36901319, by rfl⟩ : syracuseStep 49201759 = 73802639) B73802639
theorem B6734501 : Blo 884570 6734501 := bstep (se 4 (by rfl) ⟨631359, by rfl⟩ : syracuseStep 6734501 = 1262719) B1262719
theorem B27247423 : Blo 884570 27247423 := bstep (se 1 (by rfl) ⟨20435567, by rfl⟩ : syracuseStep 27247423 = 40871135) B40871135
theorem B14369669 : Blo 884570 14369669 := bstep (se 4 (by rfl) ⟨1347156, by rfl⟩ : syracuseStep 14369669 = 2694313) B2694313
theorem B6734987 : Blo 884570 6734987 := bstep (se 1 (by rfl) ⟨5051240, by rfl⟩ : syracuseStep 6734987 = 10102481) B10102481
theorem B9094625 : Blo 884570 9094625 := bstep (se 2 (by rfl) ⟨3410484, by rfl⟩ : syracuseStep 9094625 = 6820969) B6820969
theorem B10798859 : Blo 884570 10798859 := bstep (se 1 (by rfl) ⟨8099144, by rfl⟩ : syracuseStep 10798859 = 16198289) B16198289
theorem B2246555 : Blo 884570 2246555 := bstep (se 1 (by rfl) ⟨1684916, by rfl⟩ : syracuseStep 2246555 = 3369833) B3369833
theorem B16206749 : Blo 884570 16206749 := bstep (se 3 (by rfl) ⟨3038765, by rfl⟩ : syracuseStep 16206749 = 6077531) B6077531
theorem B5688569 : Blo 884570 5688569 := bstep (se 2 (by rfl) ⟨2133213, by rfl⟩ : syracuseStep 5688569 = 4266427) B4266427
theorem B1494463 : Blo 884570 1494463 := bstep (se 1 (by rfl) ⟨1120847, by rfl⟩ : syracuseStep 1494463 = 2241695) B2241695
theorem B1330943 : Blo 884570 1330943 := bstep (se 1 (by rfl) ⟨998207, by rfl⟩ : syracuseStep 1330943 = 1996415) B1996415
theorem B18174061 : Blo 884570 18174061 := bstep (se 3 (by rfl) ⟨3407636, by rfl⟩ : syracuseStep 18174061 = 6815273) B6815273
theorem B3789287 : Blo 884570 3789287 := bstep (se 1 (by rfl) ⟨2841965, by rfl⟩ : syracuseStep 3789287 = 5683931) B5683931
theorem B1495543 : Blo 884570 1495543 := bstep (se 1 (by rfl) ⟨1121657, by rfl⟩ : syracuseStep 1495543 = 2243315) B2243315
theorem B11358731 : Blo 884570 11358731 := bstep (se 1 (by rfl) ⟨8519048, by rfl⟩ : syracuseStep 11358731 = 17038097) B17038097
theorem B54711359 : Blo 884570 54711359 := bstep (se 1 (by rfl) ⟨41033519, by rfl⟩ : syracuseStep 54711359 = 82067039) B82067039
theorem B19160171 : Blo 884570 19160171 := bstep (se 1 (by rfl) ⟨14370128, by rfl⟩ : syracuseStep 19160171 = 28740257) B28740257
theorem B12804065 : Blo 884570 12804065 := bstep (se 2 (by rfl) ⟨4801524, by rfl⟩ : syracuseStep 12804065 = 9603049) B9603049
theorem B1368623 : Blo 884570 1368623 := bstep (se 1 (by rfl) ⟨1026467, by rfl⟩ : syracuseStep 1368623 = 2052935) B2052935
theorem B7201673 : Blo 884570 7201673 := bstep (se 2 (by rfl) ⟨2700627, by rfl⟩ : syracuseStep 7201673 = 5401255) B5401255
theorem B2024531 : Blo 884570 2024531 := bstep (se 1 (by rfl) ⟨1518398, by rfl⟩ : syracuseStep 2024531 = 3036797) B3036797
theorem B10773755 : Blo 884570 10773755 := bstep (se 1 (by rfl) ⟨8080316, by rfl⟩ : syracuseStep 10773755 = 16160633) B16160633
theorem B1992095 : Blo 884570 1992095 := bstep (se 1 (by rfl) ⟨1494071, by rfl⟩ : syracuseStep 1992095 = 2988143) B2988143
theorem B1992167 : Blo 884570 1992167 := bstep (se 1 (by rfl) ⟨1494125, by rfl⟩ : syracuseStep 1992167 = 2988251) B2988251
theorem B2156015 : Blo 884570 2156015 := bstep (se 1 (by rfl) ⟨1617011, by rfl⟩ : syracuseStep 2156015 = 3234023) B3234023
theorem B1993193 : Blo 884570 1993193 := bstep (se 2 (by rfl) ⟨747447, by rfl⟩ : syracuseStep 1993193 = 1494895) B1494895
theorem B1993319 : Blo 884570 1993319 := bstep (se 1 (by rfl) ⟨1494989, by rfl⟩ : syracuseStep 1993319 = 2989979) B2989979
theorem B29486227 : Blo 884570 29486227 := bstep (se 1 (by rfl) ⟨22114670, by rfl⟩ : syracuseStep 29486227 = 44229341) B44229341
theorem B11365703 : Blo 884570 11365703 := bstep (se 1 (by rfl) ⟨8524277, by rfl⟩ : syracuseStep 11365703 = 17048555) B17048555
theorem B7204555 : Blo 884570 7204555 := bstep (se 1 (by rfl) ⟨5403416, by rfl⟩ : syracuseStep 7204555 = 10806833) B10806833
theorem B1995497 : Blo 884570 1995497 := bstep (se 2 (by rfl) ⟨748311, by rfl⟩ : syracuseStep 1995497 = 1496623) B1496623
theorem B1012703 : Blo 884570 1012703 := bstep (se 1 (by rfl) ⟨759527, by rfl⟩ : syracuseStep 1012703 = 1519055) B1519055
theorem B5044133 : Blo 884570 5044133 := bstep (se 4 (by rfl) ⟨472887, by rfl⟩ : syracuseStep 5044133 = 945775) B945775
theorem B10352785 : Blo 884570 10352785 := bstep (se 2 (by rfl) ⟨3882294, by rfl⟩ : syracuseStep 10352785 = 7764589) B7764589
theorem B3406159 : Blo 884570 3406159 := bstep (se 1 (by rfl) ⟨2554619, by rfl⟩ : syracuseStep 3406159 = 5109239) B5109239
theorem B14350729 : Blo 884570 14350729 := bstep (se 2 (by rfl) ⟨5381523, by rfl⟩ : syracuseStep 14350729 = 10763047) B10763047
theorem B22117313 : Blo 884570 22117313 := bstep (se 2 (by rfl) ⟨8293992, by rfl⟩ : syracuseStep 22117313 = 16587985) B16587985
theorem B1997999 : Blo 884570 1997999 := bstep (se 1 (by rfl) ⟨1498499, by rfl⟩ : syracuseStep 1997999 = 2996999) B2996999
theorem B2391227 : Blo 884570 2391227 := bstep (se 1 (by rfl) ⟨1793420, by rfl⟩ : syracuseStep 2391227 = 3586841) B3586841
theorem B1998107 : Blo 884570 1998107 := bstep (se 1 (by rfl) ⟨1498580, by rfl⟩ : syracuseStep 1998107 = 2997161) B2997161
theorem B7175753 : Blo 884570 7175753 := bstep (se 2 (by rfl) ⟨2690907, by rfl⟩ : syracuseStep 7175753 = 5381815) B5381815
theorem B6389867 : Blo 884570 6389867 := bstep (se 1 (by rfl) ⟨4792400, by rfl⟩ : syracuseStep 6389867 = 9584801) B9584801
theorem B4489667 : Blo 884570 4489667 := bstep (se 1 (by rfl) ⟨3367250, by rfl⟩ : syracuseStep 4489667 = 6734501) B6734501
theorem B4489991 : Blo 884570 4489991 := bstep (se 1 (by rfl) ⟨3367493, by rfl⟩ : syracuseStep 4489991 = 6734987) B6734987
theorem B6063083 : Blo 884570 6063083 := bstep (se 1 (by rfl) ⟨4547312, by rfl⟩ : syracuseStep 6063083 = 9094625) B9094625
theorem B887295 : Blo 884570 887295 := bstep (se 1 (by rfl) ⟨665471, by rfl⟩ : syracuseStep 887295 = 1330943) B1330943
theorem B2526191 : Blo 884570 2526191 := bstep (se 1 (by rfl) ⟨1894643, by rfl⟩ : syracuseStep 2526191 = 3789287) B3789287
theorem B7572487 : Blo 884570 7572487 := bstep (se 1 (by rfl) ⟨5679365, by rfl⟩ : syracuseStep 7572487 = 11358731) B11358731
theorem B262409381 : Blo 884570 262409381 := bstep (se 4 (by rfl) ⟨24600879, by rfl⟩ : syracuseStep 262409381 = 49201759) B49201759
theorem B36474239 : Blo 884570 36474239 := bstep (se 1 (by rfl) ⟨27355679, by rfl⟩ : syracuseStep 36474239 = 54711359) B54711359
theorem B57513725 : Blo 884570 57513725 := bstep (se 3 (by rfl) ⟨10783823, by rfl⟩ : syracuseStep 57513725 = 21567647) B21567647
theorem B1349687 : Blo 884570 1349687 := bstep (se 1 (by rfl) ⟨1012265, by rfl⟩ : syracuseStep 1349687 = 2024531) B2024531
theorem B2562139 : Blo 884570 2562139 := bstep (se 1 (by rfl) ⟨1921604, by rfl⟩ : syracuseStep 2562139 = 3843209) B3843209
theorem B7182503 : Blo 884570 7182503 := bstep (se 1 (by rfl) ⟨5386877, by rfl⟩ : syracuseStep 7182503 = 10773755) B10773755
theorem B7577135 : Blo 884570 7577135 := bstep (se 1 (by rfl) ⟨5682851, by rfl⟩ : syracuseStep 7577135 = 11365703) B11365703
theorem B13803713 : Blo 884570 13803713 := bstep (se 2 (by rfl) ⟨5176392, by rfl⟩ : syracuseStep 13803713 = 10352785) B10352785
theorem B5055979 : Blo 884570 5055979 := bstep (se 1 (by rfl) ⟨3791984, by rfl⟩ : syracuseStep 5055979 = 7583969) B7583969
theorem B9579779 : Blo 884570 9579779 := bstep (se 1 (by rfl) ⟨7184834, by rfl⟩ : syracuseStep 9579779 = 14369669) B14369669
theorem B2700541 : Blo 884570 2700541 := bstep (se 3 (by rfl) ⟨506351, by rfl⟩ : syracuseStep 2700541 = 1012703) B1012703
theorem B7189831 : Blo 884570 7189831 := bstep (se 1 (by rfl) ⟨5392373, by rfl⟩ : syracuseStep 7189831 = 10784747) B10784747
theorem B3782143 : Blo 884570 3782143 := bstep (se 1 (by rfl) ⟨2836607, by rfl⟩ : syracuseStep 3782143 = 5673215) B5673215
theorem B5749373 : Blo 884570 5749373 := bstep (se 3 (by rfl) ⟨1078007, by rfl⟩ : syracuseStep 5749373 = 2156015) B2156015
theorem B3783647 : Blo 884570 3783647 := bstep (se 1 (by rfl) ⟨2837735, by rfl⟩ : syracuseStep 3783647 = 5675471) B5675471
theorem B8536043 : Blo 884570 8536043 := bstep (se 1 (by rfl) ⟨6402032, by rfl⟩ : syracuseStep 8536043 = 12804065) B12804065
theorem B24232081 : Blo 884570 24232081 := bstep (se 2 (by rfl) ⟨9087030, by rfl⟩ : syracuseStep 24232081 = 18174061) B18174061
theorem B4801115 : Blo 884570 4801115 := bstep (se 1 (by rfl) ⟨3600836, by rfl⟩ : syracuseStep 4801115 = 7201673) B7201673
theorem B1328063 : Blo 884570 1328063 := bstep (se 1 (by rfl) ⟨996047, by rfl⟩ : syracuseStep 1328063 = 1992095) B1992095
theorem B1328111 : Blo 884570 1328111 := bstep (se 1 (by rfl) ⟨996083, by rfl⟩ : syracuseStep 1328111 = 1992167) B1992167
theorem B1328795 : Blo 884570 1328795 := bstep (se 1 (by rfl) ⟨996596, by rfl⟩ : syracuseStep 1328795 = 1993193) B1993193
theorem B1328879 : Blo 884570 1328879 := bstep (se 1 (by rfl) ⟨996659, by rfl⟩ : syracuseStep 1328879 = 1993319) B1993319
theorem B1329641 : Blo 884570 1329641 := bstep (se 2 (by rfl) ⟨498615, by rfl⟩ : syracuseStep 1329641 = 997231) B997231
theorem B4541545 : Blo 884570 4541545 := bstep (se 2 (by rfl) ⟨1703079, by rfl⟩ : syracuseStep 4541545 = 3406159) B3406159
theorem B1330331 : Blo 884570 1330331 := bstep (se 1 (by rfl) ⟨997748, by rfl⟩ : syracuseStep 1330331 = 1995497) B1995497
theorem B38424293 : Blo 884570 38424293 := bstep (se 4 (by rfl) ⟨3602277, by rfl⟩ : syracuseStep 38424293 = 7204555) B7204555
theorem B3362755 : Blo 884570 3362755 := bstep (se 1 (by rfl) ⟨2522066, by rfl⟩ : syracuseStep 3362755 = 5044133) B5044133
theorem B3789251 : Blo 884570 3789251 := bstep (se 1 (by rfl) ⟨2841938, by rfl⟩ : syracuseStep 3789251 = 5683877) B5683877
theorem B103600883 : Blo 884570 103600883 := bstep (se 1 (by rfl) ⟨77700662, by rfl⟩ : syracuseStep 103600883 = 155401325) B155401325
theorem B1331999 : Blo 884570 1331999 := bstep (se 1 (by rfl) ⟨998999, by rfl⟩ : syracuseStep 1331999 = 1997999) B1997999
theorem B1594151 : Blo 884570 1594151 := bstep (se 1 (by rfl) ⟨1195613, by rfl⟩ : syracuseStep 1594151 = 2391227) B2391227
theorem B1332071 : Blo 884570 1332071 := bstep (se 1 (by rfl) ⟨999053, by rfl⟩ : syracuseStep 1332071 = 1998107) B1998107
theorem B6738875 : Blo 884570 6738875 := bstep (se 1 (by rfl) ⟨5054156, by rfl⟩ : syracuseStep 6738875 = 10108313) B10108313
theorem B4479299 : Blo 884570 4479299 := bstep (se 1 (by rfl) ⟨3359474, by rfl⟩ : syracuseStep 4479299 = 6718949) B6718949
theorem B36329897 : Blo 884570 36329897 := bstep (se 2 (by rfl) ⟨13623711, by rfl⟩ : syracuseStep 36329897 = 27247423) B27247423
theorem B7199239 : Blo 884570 7199239 := bstep (se 1 (by rfl) ⟨5399429, by rfl⟩ : syracuseStep 7199239 = 10798859) B10798859
theorem B1497703 : Blo 884570 1497703 := bstep (se 1 (by rfl) ⟨1123277, by rfl⟩ : syracuseStep 1497703 = 2246555) B2246555
theorem B4545341 : Blo 884570 4545341 := bstep (se 3 (by rfl) ⟨852251, by rfl⟩ : syracuseStep 4545341 = 1704503) B1704503
theorem B10804499 : Blo 884570 10804499 := bstep (se 1 (by rfl) ⟨8103374, by rfl⟩ : syracuseStep 10804499 = 16206749) B16206749
theorem B3792379 : Blo 884570 3792379 := bstep (se 1 (by rfl) ⟨2844284, by rfl⟩ : syracuseStep 3792379 = 5688569) B5688569
theorem B39314969 : Blo 884570 39314969 := bstep (se 2 (by rfl) ⟨14743113, by rfl⟩ : syracuseStep 39314969 = 29486227) B29486227
theorem B1992617 : Blo 884570 1992617 := bstep (se 2 (by rfl) ⟨747231, by rfl⟩ : syracuseStep 1992617 = 1494463) B1494463
theorem B12773447 : Blo 884570 12773447 := bstep (se 1 (by rfl) ⟨9580085, by rfl⟩ : syracuseStep 12773447 = 19160171) B19160171
theorem B4483835 : Blo 884570 4483835 := bstep (se 1 (by rfl) ⟨3362876, by rfl⟩ : syracuseStep 4483835 = 6725753) B6725753
theorem B912415 : Blo 884570 912415 := bstep (se 1 (by rfl) ⟨684311, by rfl⟩ : syracuseStep 912415 = 1368623) B1368623
theorem B1994057 : Blo 884570 1994057 := bstep (se 2 (by rfl) ⟨747771, by rfl⟩ : syracuseStep 1994057 = 1495543) B1495543
theorem B1994687 : Blo 884570 1994687 := bstep (se 1 (by rfl) ⟨1496015, by rfl⟩ : syracuseStep 1994687 = 2992031) B2992031
theorem B3371291 : Blo 884570 3371291 := bstep (se 1 (by rfl) ⟨2528468, by rfl⟩ : syracuseStep 3371291 = 5056937) B5056937
theorem B14185135 : Blo 884570 14185135 := bstep (se 1 (by rfl) ⟨10638851, by rfl⟩ : syracuseStep 14185135 = 21277703) B21277703
theorem B1996343 : Blo 884570 1996343 := bstep (se 1 (by rfl) ⟨1497257, by rfl⟩ : syracuseStep 1996343 = 2994515) B2994515
theorem B19134305 : Blo 884570 19134305 := bstep (se 2 (by rfl) ⟨7175364, by rfl⟩ : syracuseStep 19134305 = 14350729) B14350729
theorem B1997567 : Blo 884570 1997567 := bstep (se 1 (by rfl) ⟨1498175, by rfl⟩ : syracuseStep 1997567 = 2996351) B2996351
theorem B1997819 : Blo 884570 1997819 := bstep (se 1 (by rfl) ⟨1498364, by rfl⟩ : syracuseStep 1997819 = 2996729) B2996729
theorem B14744875 : Blo 884570 14744875 := bstep (se 1 (by rfl) ⟨11058656, by rfl⟩ : syracuseStep 14744875 = 22117313) B22117313
theorem B4783835 : Blo 884570 4783835 := bstep (se 1 (by rfl) ⟨3587876, by rfl⟩ : syracuseStep 4783835 = 7175753) B7175753
theorem B19201769 : Blo 884570 19201769 := bstep (se 2 (by rfl) ⟨7200663, by rfl⟩ : syracuseStep 19201769 = 14401327) B14401327
theorem B1998719 : Blo 884570 1998719 := bstep (se 1 (by rfl) ⟨1499039, by rfl⟩ : syracuseStep 1998719 = 2998079) B2998079
theorem B4259911 : Blo 884570 4259911 := bstep (se 1 (by rfl) ⟨3194933, by rfl⟩ : syracuseStep 4259911 = 6389867) B6389867
theorem B32309441 : Blo 884570 32309441 := bstep (se 2 (by rfl) ⟨12116040, by rfl⟩ : syracuseStep 32309441 = 24232081) B24232081
theorem B885375 : Blo 884570 885375 := bstep (se 1 (by rfl) ⟨664031, by rfl⟩ : syracuseStep 885375 = 1328063) B1328063
theorem B885407 : Blo 884570 885407 := bstep (se 1 (by rfl) ⟨664055, by rfl⟩ : syracuseStep 885407 = 1328111) B1328111
theorem B885863 : Blo 884570 885863 := bstep (se 1 (by rfl) ⟨664397, by rfl⟩ : syracuseStep 885863 = 1328795) B1328795
theorem B885919 : Blo 884570 885919 := bstep (se 1 (by rfl) ⟨664439, by rfl⟩ : syracuseStep 885919 = 1328879) B1328879
theorem B886427 : Blo 884570 886427 := bstep (se 1 (by rfl) ⟨664820, by rfl⟩ : syracuseStep 886427 = 1329641) B1329641
theorem B886887 : Blo 884570 886887 := bstep (se 1 (by rfl) ⟨665165, by rfl⟩ : syracuseStep 886887 = 1330331) B1330331
theorem B24316159 : Blo 884570 24316159 := bstep (se 1 (by rfl) ⟨18237119, by rfl⟩ : syracuseStep 24316159 = 36474239) B36474239
theorem B2526167 : Blo 884570 2526167 := bstep (se 1 (by rfl) ⟨1894625, by rfl⟩ : syracuseStep 2526167 = 3789251) B3789251
theorem B887999 : Blo 884570 887999 := bstep (se 1 (by rfl) ⟨665999, by rfl⟩ : syracuseStep 887999 = 1331999) B1331999
theorem B888047 : Blo 884570 888047 := bstep (se 1 (by rfl) ⟨666035, by rfl⟩ : syracuseStep 888047 = 1332071) B1332071
theorem B4492583 : Blo 884570 4492583 := bstep (se 1 (by rfl) ⟨3369437, by rfl⟩ : syracuseStep 4492583 = 6738875) B6738875
theorem B38342483 : Blo 884570 38342483 := bstep (se 1 (by rfl) ⟨28756862, by rfl⟩ : syracuseStep 38342483 = 57513725) B57513725
theorem B10096649 : Blo 884570 10096649 := bstep (se 2 (by rfl) ⟨3786243, by rfl⟩ : syracuseStep 10096649 = 7572487) B7572487
theorem B1216553 : Blo 884570 1216553 := bstep (se 2 (by rfl) ⟨456207, by rfl⟩ : syracuseStep 1216553 = 912415) B912415
theorem B4788335 : Blo 884570 4788335 := bstep (se 1 (by rfl) ⟨3591251, by rfl⟩ : syracuseStep 4788335 = 7182503) B7182503
theorem B2986199 : Blo 884570 2986199 := bstep (se 1 (by rfl) ⟨2239649, by rfl⟩ : syracuseStep 2986199 = 4479299) B4479299
theorem B24219931 : Blo 884570 24219931 := bstep (se 1 (by rfl) ⟨18164948, by rfl⟩ : syracuseStep 24219931 = 36329897) B36329897
theorem B5051423 : Blo 884570 5051423 := bstep (se 1 (by rfl) ⟨3788567, by rfl⟩ : syracuseStep 5051423 = 7577135) B7577135
theorem B18913513 : Blo 884570 18913513 := bstep (se 2 (by rfl) ⟨7092567, by rfl⟩ : syracuseStep 18913513 = 14185135) B14185135
theorem B2989223 : Blo 884570 2989223 := bstep (se 1 (by rfl) ⟨2241917, by rfl⟩ : syracuseStep 2989223 = 4483835) B4483835
theorem B3416185 : Blo 884570 3416185 := bstep (se 2 (by rfl) ⟨1281069, by rfl⟩ : syracuseStep 3416185 = 2562139) B2562139
theorem B12756203 : Blo 884570 12756203 := bstep (se 1 (by rfl) ⟨9567152, by rfl⟩ : syracuseStep 12756203 = 19134305) B19134305
theorem B5056505 : Blo 884570 5056505 := bstep (se 2 (by rfl) ⟨1896189, by rfl⟩ : syracuseStep 5056505 = 3792379) B3792379
theorem B3189223 : Blo 884570 3189223 := bstep (se 1 (by rfl) ⟨2391917, by rfl⟩ : syracuseStep 3189223 = 4783835) B4783835
theorem B2993111 : Blo 884570 2993111 := bstep (se 1 (by rfl) ⟨2244833, by rfl⟩ : syracuseStep 2993111 = 4489667) B4489667
theorem B2993327 : Blo 884570 2993327 := bstep (se 1 (by rfl) ⟨2244995, by rfl⟩ : syracuseStep 2993327 = 4489991) B4489991
theorem B4042055 : Blo 884570 4042055 := bstep (se 1 (by rfl) ⟨3031541, by rfl⟩ : syracuseStep 4042055 = 6063083) B6063083
theorem B1684127 : Blo 884570 1684127 := bstep (se 1 (by rfl) ⟨1263095, by rfl⟩ : syracuseStep 1684127 = 2526191) B2526191
theorem B1062767 : Blo 884570 1062767 := bstep (se 1 (by rfl) ⟨797075, by rfl⟩ : syracuseStep 1062767 = 1594151) B1594151
theorem B899791 : Blo 884570 899791 := bstep (se 1 (by rfl) ⟨674843, by rfl⟩ : syracuseStep 899791 = 1349687) B1349687
theorem B3030227 : Blo 884570 3030227 := bstep (se 1 (by rfl) ⟨2272670, by rfl⟩ : syracuseStep 3030227 = 4545341) B4545341
theorem B1328411 : Blo 884570 1328411 := bstep (se 1 (by rfl) ⟨996308, by rfl⟩ : syracuseStep 1328411 = 1992617) B1992617
theorem B9586441 : Blo 884570 9586441 := bstep (se 2 (by rfl) ⟨3594915, by rfl⟩ : syracuseStep 9586441 = 7189831) B7189831
theorem B1329371 : Blo 884570 1329371 := bstep (se 1 (by rfl) ⟨997028, by rfl⟩ : syracuseStep 1329371 = 1994057) B1994057
theorem B1329791 : Blo 884570 1329791 := bstep (se 1 (by rfl) ⟨997343, by rfl⟩ : syracuseStep 1329791 = 1994687) B1994687
theorem B2247527 : Blo 884570 2247527 := bstep (se 1 (by rfl) ⟨1685645, by rfl⟩ : syracuseStep 2247527 = 3371291) B3371291
theorem B1330895 : Blo 884570 1330895 := bstep (se 1 (by rfl) ⟨998171, by rfl⟩ : syracuseStep 1330895 = 1996343) B1996343
theorem B1331711 : Blo 884570 1331711 := bstep (se 1 (by rfl) ⟨998783, by rfl⟩ : syracuseStep 1331711 = 1997567) B1997567
theorem B1331879 : Blo 884570 1331879 := bstep (se 1 (by rfl) ⟨998909, by rfl⟩ : syracuseStep 1331879 = 1997819) B1997819
theorem B12801179 : Blo 884570 12801179 := bstep (se 1 (by rfl) ⟨9600884, by rfl⟩ : syracuseStep 12801179 = 19201769) B19201769
theorem B1332479 : Blo 884570 1332479 := bstep (se 1 (by rfl) ⟨999359, by rfl⟩ : syracuseStep 1332479 = 1998719) B1998719
theorem B5690695 : Blo 884570 5690695 := bstep (se 1 (by rfl) ⟨4268021, by rfl⟩ : syracuseStep 5690695 = 8536043) B8536043
theorem B3200743 : Blo 884570 3200743 := bstep (se 1 (by rfl) ⟨2400557, by rfl⟩ : syracuseStep 3200743 = 4801115) B4801115
theorem B6741305 : Blo 884570 6741305 := bstep (se 2 (by rfl) ⟨2527989, by rfl⟩ : syracuseStep 6741305 = 5055979) B5055979
theorem B174939587 : Blo 884570 174939587 := bstep (se 1 (by rfl) ⟨131204690, by rfl⟩ : syracuseStep 174939587 = 262409381) B262409381
theorem B25616195 : Blo 884570 25616195 := bstep (se 1 (by rfl) ⟨19212146, by rfl⟩ : syracuseStep 25616195 = 38424293) B38424293
theorem B69067255 : Blo 884570 69067255 := bstep (se 1 (by rfl) ⟨51800441, by rfl⟩ : syracuseStep 69067255 = 103600883) B103600883
theorem B6055393 : Blo 884570 6055393 := bstep (se 2 (by rfl) ⟨2270772, by rfl⟩ : syracuseStep 6055393 = 4541545) B4541545
theorem B7202999 : Blo 884570 7202999 := bstep (se 1 (by rfl) ⟨5402249, by rfl⟩ : syracuseStep 7202999 = 10804499) B10804499
theorem B4483673 : Blo 884570 4483673 := bstep (se 2 (by rfl) ⟨1681377, by rfl⟩ : syracuseStep 4483673 = 3362755) B3362755
theorem B9202475 : Blo 884570 9202475 := bstep (se 1 (by rfl) ⟨6901856, by rfl⟩ : syracuseStep 9202475 = 13803713) B13803713
theorem B26209979 : Blo 884570 26209979 := bstep (se 1 (by rfl) ⟨19657484, by rfl⟩ : syracuseStep 26209979 = 39314969) B39314969
theorem B8515631 : Blo 884570 8515631 := bstep (se 1 (by rfl) ⟨6386723, by rfl⟩ : syracuseStep 8515631 = 12773447) B12773447
theorem B3600721 : Blo 884570 3600721 := bstep (se 2 (by rfl) ⟨1350270, by rfl⟩ : syracuseStep 3600721 = 2700541) B2700541
theorem B5042857 : Blo 884570 5042857 := bstep (se 2 (by rfl) ⟨1891071, by rfl⟩ : syracuseStep 5042857 = 3782143) B3782143
theorem B6386519 : Blo 884570 6386519 := bstep (se 1 (by rfl) ⟨4789889, by rfl⟩ : syracuseStep 6386519 = 9579779) B9579779
theorem B9598985 : Blo 884570 9598985 := bstep (se 2 (by rfl) ⟨3599619, by rfl⟩ : syracuseStep 9598985 = 7199239) B7199239
theorem B1996937 : Blo 884570 1996937 := bstep (se 2 (by rfl) ⟨748851, by rfl⟩ : syracuseStep 1996937 = 1497703) B1497703
theorem B19659833 : Blo 884570 19659833 := bstep (se 2 (by rfl) ⟨7372437, by rfl⟩ : syracuseStep 19659833 = 14744875) B14744875
theorem B3832915 : Blo 884570 3832915 := bstep (se 1 (by rfl) ⟨2874686, by rfl⟩ : syracuseStep 3832915 = 5749373) B5749373
theorem B2522431 : Blo 884570 2522431 := bstep (se 1 (by rfl) ⟨1891823, by rfl⟩ : syracuseStep 2522431 = 3783647) B3783647
theorem B3244141 : Blo 884570 3244141 := bstep (se 3 (by rfl) ⟨608276, by rfl⟩ : syracuseStep 3244141 = 1216553) B1216553
theorem B4554913 : Blo 884570 4554913 := bstep (se 2 (by rfl) ⟨1708092, by rfl⟩ : syracuseStep 4554913 = 3416185) B3416185
theorem B885607 : Blo 884570 885607 := bstep (se 1 (by rfl) ⟨664205, by rfl⟩ : syracuseStep 885607 = 1328411) B1328411
theorem B886247 : Blo 884570 886247 := bstep (se 1 (by rfl) ⟨664685, by rfl⟩ : syracuseStep 886247 = 1329371) B1329371
theorem B886527 : Blo 884570 886527 := bstep (se 1 (by rfl) ⟨664895, by rfl⟩ : syracuseStep 886527 = 1329791) B1329791
theorem B12781921 : Blo 884570 12781921 := bstep (se 2 (by rfl) ⟨4793220, by rfl⟩ : syracuseStep 12781921 = 9586441) B9586441
theorem B887263 : Blo 884570 887263 := bstep (se 1 (by rfl) ⟨665447, by rfl⟩ : syracuseStep 887263 = 1330895) B1330895
theorem B17009189 : Blo 884570 17009189 := bstep (se 4 (by rfl) ⟨1594611, by rfl⟩ : syracuseStep 17009189 = 3189223) B3189223
theorem B25561655 : Blo 884570 25561655 := bstep (se 1 (by rfl) ⟨19171241, by rfl⟩ : syracuseStep 25561655 = 38342483) B38342483
theorem B887807 : Blo 884570 887807 := bstep (se 1 (by rfl) ⟨665855, by rfl⟩ : syracuseStep 887807 = 1331711) B1331711
theorem B887919 : Blo 884570 887919 := bstep (se 1 (by rfl) ⟨665939, by rfl⟩ : syracuseStep 887919 = 1331879) B1331879
theorem B888319 : Blo 884570 888319 := bstep (se 1 (by rfl) ⟨666239, by rfl⟩ : syracuseStep 888319 = 1332479) B1332479
theorem B4494203 : Blo 884570 4494203 := bstep (se 1 (by rfl) ⟨3370652, by rfl⟩ : syracuseStep 4494203 = 6741305) B6741305
theorem B116626391 : Blo 884570 116626391 := bstep (se 1 (by rfl) ⟨87469793, by rfl⟩ : syracuseStep 116626391 = 174939587) B174939587
theorem B17077463 : Blo 884570 17077463 := bstep (se 1 (by rfl) ⟨12808097, by rfl⟩ : syracuseStep 17077463 = 25616195) B25616195
theorem B6723809 : Blo 884570 6723809 := bstep (se 2 (by rfl) ⟨2521428, by rfl⟩ : syracuseStep 6723809 = 5042857) B5042857
theorem B2989115 : Blo 884570 2989115 := bstep (se 1 (by rfl) ⟨2241836, by rfl⟩ : syracuseStep 2989115 = 4483673) B4483673
theorem B6134983 : Blo 884570 6134983 := bstep (se 1 (by rfl) ⟨4601237, by rfl⟩ : syracuseStep 6134983 = 9202475) B9202475
theorem B2694703 : Blo 884570 2694703 := bstep (se 1 (by rfl) ⟨2021027, by rfl⟩ : syracuseStep 2694703 = 4042055) B4042055
theorem B4267657 : Blo 884570 4267657 := bstep (se 2 (by rfl) ⟨1600371, by rfl⟩ : syracuseStep 4267657 = 3200743) B3200743
theorem B17473319 : Blo 884570 17473319 := bstep (se 1 (by rfl) ⟨13104989, by rfl⟩ : syracuseStep 17473319 = 26209979) B26209979
theorem B5677087 : Blo 884570 5677087 := bstep (se 1 (by rfl) ⟨4257815, by rfl⟩ : syracuseStep 5677087 = 8515631) B8515631
theorem B1122751 : Blo 884570 1122751 := bstep (se 1 (by rfl) ⟨842063, by rfl⟩ : syracuseStep 1122751 = 1684127) B1684127
theorem B6399323 : Blo 884570 6399323 := bstep (se 1 (by rfl) ⟨4799492, by rfl⟩ : syracuseStep 6399323 = 9598985) B9598985
theorem B5679881 : Blo 884570 5679881 := bstep (se 2 (by rfl) ⟨2129955, by rfl⟩ : syracuseStep 5679881 = 4259911) B4259911
theorem B21539627 : Blo 884570 21539627 := bstep (se 1 (by rfl) ⟨16154720, by rfl⟩ : syracuseStep 21539627 = 32309441) B32309441
theorem B92089673 : Blo 884570 92089673 := bstep (se 2 (by rfl) ⟨34533627, by rfl⟩ : syracuseStep 92089673 = 69067255) B69067255
theorem B8073857 : Blo 884570 8073857 := bstep (se 2 (by rfl) ⟨3027696, by rfl⟩ : syracuseStep 8073857 = 6055393) B6055393
theorem B2995055 : Blo 884570 2995055 := bstep (se 1 (by rfl) ⟨2246291, by rfl⟩ : syracuseStep 2995055 = 4492583) B4492583
theorem B6731099 : Blo 884570 6731099 := bstep (se 1 (by rfl) ⟨5048324, by rfl⟩ : syracuseStep 6731099 = 10096649) B10096649
theorem B3192223 : Blo 884570 3192223 := bstep (se 1 (by rfl) ⟨2394167, by rfl⟩ : syracuseStep 3192223 = 4788335) B4788335
theorem B32421545 : Blo 884570 32421545 := bstep (se 2 (by rfl) ⟨12158079, by rfl⟩ : syracuseStep 32421545 = 24316159) B24316159
theorem B8534119 : Blo 884570 8534119 := bstep (se 1 (by rfl) ⟨6400589, by rfl⟩ : syracuseStep 8534119 = 12801179) B12801179
theorem B2834045 : Blo 884570 2834045 := bstep (se 3 (by rfl) ⟨531383, by rfl⟩ : syracuseStep 2834045 = 1062767) B1062767
theorem B32293241 : Blo 884570 32293241 := bstep (se 2 (by rfl) ⟨12109965, by rfl⟩ : syracuseStep 32293241 = 24219931) B24219931
theorem B4800961 : Blo 884570 4800961 := bstep (se 2 (by rfl) ⟨1800360, by rfl⟩ : syracuseStep 4800961 = 3600721) B3600721
theorem B8504135 : Blo 884570 8504135 := bstep (se 1 (by rfl) ⟨6378101, by rfl⟩ : syracuseStep 8504135 = 12756203) B12756203
theorem B4801999 : Blo 884570 4801999 := bstep (se 1 (by rfl) ⟨3601499, by rfl⟩ : syracuseStep 4801999 = 7202999) B7202999
theorem B7587593 : Blo 884570 7587593 := bstep (se 2 (by rfl) ⟨2845347, by rfl⟩ : syracuseStep 7587593 = 5690695) B5690695
theorem B6736445 : Blo 884570 6736445 := bstep (se 3 (by rfl) ⟨1263083, by rfl⟩ : syracuseStep 6736445 = 2526167) B2526167
theorem B25218017 : Blo 884570 25218017 := bstep (se 2 (by rfl) ⟨9456756, by rfl⟩ : syracuseStep 25218017 = 18913513) B18913513
theorem B1331291 : Blo 884570 1331291 := bstep (se 1 (by rfl) ⟨998468, by rfl⟩ : syracuseStep 1331291 = 1996937) B1996937
theorem B3363241 : Blo 884570 3363241 := bstep (se 2 (by rfl) ⟨1261215, by rfl⟩ : syracuseStep 3363241 = 2522431) B2522431
theorem B2020151 : Blo 884570 2020151 := bstep (se 1 (by rfl) ⟨1515113, by rfl⟩ : syracuseStep 2020151 = 3030227) B3030227
theorem B1498351 : Blo 884570 1498351 := bstep (se 1 (by rfl) ⟨1123763, by rfl⟩ : syracuseStep 1498351 = 2247527) B2247527
theorem B1990799 : Blo 884570 1990799 := bstep (se 1 (by rfl) ⟨1493099, by rfl⟩ : syracuseStep 1990799 = 2986199) B2986199
theorem B3367615 : Blo 884570 3367615 := bstep (se 1 (by rfl) ⟨2525711, by rfl⟩ : syracuseStep 3367615 = 5051423) B5051423
theorem B19195541 : Blo 884570 19195541 := bstep (se 6 (by rfl) ⟨449895, by rfl⟩ : syracuseStep 19195541 = 899791) B899791
theorem B1992815 : Blo 884570 1992815 := bstep (se 1 (by rfl) ⟨1494611, by rfl⟩ : syracuseStep 1992815 = 2989223) B2989223
theorem B3371003 : Blo 884570 3371003 := bstep (se 1 (by rfl) ⟨2528252, by rfl⟩ : syracuseStep 3371003 = 5056505) B5056505
theorem B1995407 : Blo 884570 1995407 := bstep (se 1 (by rfl) ⟨1496555, by rfl⟩ : syracuseStep 1995407 = 2993111) B2993111
theorem B1995551 : Blo 884570 1995551 := bstep (se 1 (by rfl) ⟨1496663, by rfl⟩ : syracuseStep 1995551 = 2993327) B2993327
theorem B4257679 : Blo 884570 4257679 := bstep (se 1 (by rfl) ⟨3193259, by rfl⟩ : syracuseStep 4257679 = 6386519) B6386519
theorem B5110553 : Blo 884570 5110553 := bstep (se 2 (by rfl) ⟨1916457, by rfl⟩ : syracuseStep 5110553 = 3832915) B3832915
theorem B13106555 : Blo 884570 13106555 := bstep (se 1 (by rfl) ⟨9829916, by rfl⟩ : syracuseStep 13106555 = 19659833) B19659833
theorem B7569449 : Blo 884570 7569449 := bstep (se 2 (by rfl) ⟨2838543, by rfl⟩ : syracuseStep 7569449 = 5677087) B5677087
theorem B4325521 : Blo 884570 4325521 := bstep (se 2 (by rfl) ⟨1622070, by rfl⟩ : syracuseStep 4325521 = 3244141) B3244141
theorem B21528827 : Blo 884570 21528827 := bstep (se 1 (by rfl) ⟨16146620, by rfl⟩ : syracuseStep 21528827 = 32293241) B32293241
theorem B5669423 : Blo 884570 5669423 := bstep (se 1 (by rfl) ⟨4252067, by rfl⟩ : syracuseStep 5669423 = 8504135) B8504135
theorem B4490153 : Blo 884570 4490153 := bstep (se 2 (by rfl) ⟨1683807, by rfl⟩ : syracuseStep 4490153 = 3367615) B3367615
theorem B21530285 : Blo 884570 21530285 := bstep (se 3 (by rfl) ⟨4036928, by rfl⟩ : syracuseStep 21530285 = 8073857) B8073857
theorem B11339459 : Blo 884570 11339459 := bstep (se 1 (by rfl) ⟨8504594, by rfl⟩ : syracuseStep 11339459 = 17009189) B17009189
theorem B17041103 : Blo 884570 17041103 := bstep (se 1 (by rfl) ⟨12780827, by rfl⟩ : syracuseStep 17041103 = 25561655) B25561655
theorem B4490963 : Blo 884570 4490963 := bstep (se 1 (by rfl) ⟨3368222, by rfl⟩ : syracuseStep 4490963 = 6736445) B6736445
theorem B16812011 : Blo 884570 16812011 := bstep (se 1 (by rfl) ⟨12609008, by rfl⟩ : syracuseStep 16812011 = 25218017) B25218017
theorem B887527 : Blo 884570 887527 := bstep (se 1 (by rfl) ⟨665645, by rfl⟩ : syracuseStep 887527 = 1331291) B1331291
theorem B17042561 : Blo 884570 17042561 := bstep (se 2 (by rfl) ⟨6390960, by rfl⟩ : syracuseStep 17042561 = 12781921) B12781921
theorem B4266215 : Blo 884570 4266215 := bstep (se 1 (by rfl) ⟨3199661, by rfl⟩ : syracuseStep 4266215 = 6399323) B6399323
theorem B14359751 : Blo 884570 14359751 := bstep (se 1 (by rfl) ⟨10769813, by rfl⟩ : syracuseStep 14359751 = 21539627) B21539627
theorem B5676905 : Blo 884570 5676905 := bstep (se 2 (by rfl) ⟨2128839, by rfl⟩ : syracuseStep 5676905 = 4257679) B4257679
theorem B11378825 : Blo 884570 11378825 := bstep (se 2 (by rfl) ⟨4267059, by rfl⟩ : syracuseStep 11378825 = 8534119) B8534119
theorem B6073217 : Blo 884570 6073217 := bstep (se 2 (by rfl) ⟨2277456, by rfl⟩ : syracuseStep 6073217 = 4554913) B4554913
theorem B6401281 : Blo 884570 6401281 := bstep (se 2 (by rfl) ⟨2400480, by rfl⟩ : syracuseStep 6401281 = 4800961) B4800961
theorem B5058395 : Blo 884570 5058395 := bstep (se 1 (by rfl) ⟨3793796, by rfl⟩ : syracuseStep 5058395 = 7587593) B7587593
theorem B6402665 : Blo 884570 6402665 := bstep (se 2 (by rfl) ⟨2400999, by rfl⟩ : syracuseStep 6402665 = 4801999) B4801999
theorem B5387069 : Blo 884570 5387069 := bstep (se 3 (by rfl) ⟨1010075, by rfl⟩ : syracuseStep 5387069 = 2020151) B2020151
theorem B2996135 : Blo 884570 2996135 := bstep (se 1 (by rfl) ⟨2247101, by rfl⟩ : syracuseStep 2996135 = 4494203) B4494203
theorem B11384975 : Blo 884570 11384975 := bstep (se 1 (by rfl) ⟨8538731, by rfl⟩ : syracuseStep 11384975 = 17077463) B17077463
theorem B11648879 : Blo 884570 11648879 := bstep (se 1 (by rfl) ⟨8736659, by rfl⟩ : syracuseStep 11648879 = 17473319) B17473319
theorem B1327199 : Blo 884570 1327199 := bstep (se 1 (by rfl) ⟨995399, by rfl⟩ : syracuseStep 1327199 = 1990799) B1990799
theorem B32719909 : Blo 884570 32719909 := bstep (se 4 (by rfl) ⟨3067491, by rfl⟩ : syracuseStep 32719909 = 6134983) B6134983
theorem B12797027 : Blo 884570 12797027 := bstep (se 1 (by rfl) ⟨9597770, by rfl⟩ : syracuseStep 12797027 = 19195541) B19195541
theorem B1328543 : Blo 884570 1328543 := bstep (se 1 (by rfl) ⟨996407, by rfl⟩ : syracuseStep 1328543 = 1992815) B1992815
theorem B3786587 : Blo 884570 3786587 := bstep (se 1 (by rfl) ⟨2839940, by rfl⟩ : syracuseStep 3786587 = 5679881) B5679881
theorem B61393115 : Blo 884570 61393115 := bstep (se 1 (by rfl) ⟨46044836, by rfl⟩ : syracuseStep 61393115 = 92089673) B92089673
theorem B2247335 : Blo 884570 2247335 := bstep (se 1 (by rfl) ⟨1685501, by rfl⟩ : syracuseStep 2247335 = 3371003) B3371003
theorem B1330271 : Blo 884570 1330271 := bstep (se 1 (by rfl) ⟨997703, by rfl⟩ : syracuseStep 1330271 = 1995407) B1995407
theorem B1330367 : Blo 884570 1330367 := bstep (se 1 (by rfl) ⟨997775, by rfl⟩ : syracuseStep 1330367 = 1995551) B1995551
theorem B21614363 : Blo 884570 21614363 := bstep (se 1 (by rfl) ⟨16210772, by rfl⟩ : syracuseStep 21614363 = 32421545) B32421545
theorem B3592937 : Blo 884570 3592937 := bstep (se 2 (by rfl) ⟨1347351, by rfl⟩ : syracuseStep 3592937 = 2694703) B2694703
theorem B5690209 : Blo 884570 5690209 := bstep (se 2 (by rfl) ⟨2133828, by rfl⟩ : syracuseStep 5690209 = 4267657) B4267657
theorem B8737703 : Blo 884570 8737703 := bstep (se 1 (by rfl) ⟨6553277, by rfl⟩ : syracuseStep 8737703 = 13106555) B13106555
theorem B1889363 : Blo 884570 1889363 := bstep (se 1 (by rfl) ⟨1417022, by rfl⟩ : syracuseStep 1889363 = 2834045) B2834045
theorem B1497001 : Blo 884570 1497001 := bstep (se 2 (by rfl) ⟨561375, by rfl⟩ : syracuseStep 1497001 = 1122751) B1122751
theorem B77750927 : Blo 884570 77750927 := bstep (se 1 (by rfl) ⟨58313195, by rfl⟩ : syracuseStep 77750927 = 116626391) B116626391
theorem B4482539 : Blo 884570 4482539 := bstep (se 1 (by rfl) ⟨3361904, by rfl⟩ : syracuseStep 4482539 = 6723809) B6723809
theorem B1992743 : Blo 884570 1992743 := bstep (se 1 (by rfl) ⟨1494557, by rfl⟩ : syracuseStep 1992743 = 2989115) B2989115
theorem B4484321 : Blo 884570 4484321 := bstep (se 2 (by rfl) ⟨1681620, by rfl⟩ : syracuseStep 4484321 = 3363241) B3363241
theorem B4256297 : Blo 884570 4256297 := bstep (se 2 (by rfl) ⟨1596111, by rfl⟩ : syracuseStep 4256297 = 3192223) B3192223
theorem B1996703 : Blo 884570 1996703 := bstep (se 1 (by rfl) ⟨1497527, by rfl⟩ : syracuseStep 1996703 = 2995055) B2995055
theorem B4487399 : Blo 884570 4487399 := bstep (se 1 (by rfl) ⟨3365549, by rfl⟩ : syracuseStep 4487399 = 6731099) B6731099
theorem B1997801 : Blo 884570 1997801 := bstep (se 2 (by rfl) ⟨749175, by rfl⟩ : syracuseStep 1997801 = 1498351) B1498351
theorem B3407035 : Blo 884570 3407035 := bstep (se 1 (by rfl) ⟨2555276, by rfl⟩ : syracuseStep 3407035 = 5110553) B5110553
theorem B5046299 : Blo 884570 5046299 := bstep (se 1 (by rfl) ⟨3784724, by rfl⟩ : syracuseStep 5046299 = 7569449) B7569449
theorem B884799 : Blo 884570 884799 := bstep (se 1 (by rfl) ⟨663599, by rfl⟩ : syracuseStep 884799 = 1327199) B1327199
theorem B14352551 : Blo 884570 14352551 := bstep (se 1 (by rfl) ⟨10764413, by rfl⟩ : syracuseStep 14352551 = 21528827) B21528827
theorem B5767361 : Blo 884570 5767361 := bstep (se 2 (by rfl) ⟨2162760, by rfl⟩ : syracuseStep 5767361 = 4325521) B4325521
theorem B885695 : Blo 884570 885695 := bstep (se 1 (by rfl) ⟨664271, by rfl⟩ : syracuseStep 885695 = 1328543) B1328543
theorem B14353523 : Blo 884570 14353523 := bstep (se 1 (by rfl) ⟨10765142, by rfl⟩ : syracuseStep 14353523 = 21530285) B21530285
theorem B2524391 : Blo 884570 2524391 := bstep (se 1 (by rfl) ⟨1893293, by rfl⟩ : syracuseStep 2524391 = 3786587) B3786587
theorem B11208007 : Blo 884570 11208007 := bstep (se 1 (by rfl) ⟨8406005, by rfl⟩ : syracuseStep 11208007 = 16812011) B16812011
theorem B40928743 : Blo 884570 40928743 := bstep (se 1 (by rfl) ⟨30696557, by rfl⟩ : syracuseStep 40928743 = 61393115) B61393115
theorem B17073773 : Blo 884570 17073773 := bstep (se 3 (by rfl) ⟨3201332, by rfl⟩ : syracuseStep 17073773 = 6402665) B6402665
theorem B886847 : Blo 884570 886847 := bstep (se 1 (by rfl) ⟨665135, by rfl⟩ : syracuseStep 886847 = 1330271) B1330271
theorem B886911 : Blo 884570 886911 := bstep (se 1 (by rfl) ⟨665183, by rfl⟩ : syracuseStep 886911 = 1330367) B1330367
theorem B9573167 : Blo 884570 9573167 := bstep (se 1 (by rfl) ⟨7179875, by rfl⟩ : syracuseStep 9573167 = 14359751) B14359751
theorem B2988359 : Blo 884570 2988359 := bstep (se 1 (by rfl) ⟨2241269, by rfl⟩ : syracuseStep 2988359 = 4482539) B4482539
theorem B2989547 : Blo 884570 2989547 := bstep (se 1 (by rfl) ⟨2242160, by rfl⟩ : syracuseStep 2989547 = 4484321) B4484321
theorem B2991599 : Blo 884570 2991599 := bstep (se 1 (by rfl) ⟨2243699, by rfl⟩ : syracuseStep 2991599 = 4487399) B4487399
theorem B3779615 : Blo 884570 3779615 := bstep (se 1 (by rfl) ⟨2834711, by rfl⟩ : syracuseStep 3779615 = 5669423) B5669423
theorem B2993435 : Blo 884570 2993435 := bstep (se 1 (by rfl) ⟨2245076, by rfl⟩ : syracuseStep 2993435 = 4490153) B4490153
theorem B8531351 : Blo 884570 8531351 := bstep (se 1 (by rfl) ⟨6398513, by rfl⟩ : syracuseStep 8531351 = 12797027) B12797027
theorem B2993975 : Blo 884570 2993975 := bstep (se 1 (by rfl) ⟨2245481, by rfl⟩ : syracuseStep 2993975 = 4490963) B4490963
theorem B43626545 : Blo 884570 43626545 := bstep (se 2 (by rfl) ⟨16359954, by rfl⟩ : syracuseStep 43626545 = 32719909) B32719909
theorem B9581165 : Blo 884570 9581165 := bstep (se 3 (by rfl) ⟨1796468, by rfl⟩ : syracuseStep 9581165 = 3592937) B3592937
theorem B8535041 : Blo 884570 8535041 := bstep (se 2 (by rfl) ⟨3200640, by rfl⟩ : syracuseStep 8535041 = 6401281) B6401281
theorem B7585883 : Blo 884570 7585883 := bstep (se 1 (by rfl) ⟨5689412, by rfl⟩ : syracuseStep 7585883 = 11378825) B11378825
theorem B7586945 : Blo 884570 7586945 := bstep (se 2 (by rfl) ⟨2845104, by rfl⟩ : syracuseStep 7586945 = 5690209) B5690209
theorem B1328495 : Blo 884570 1328495 := bstep (se 1 (by rfl) ⟨996371, by rfl⟩ : syracuseStep 1328495 = 1992743) B1992743
theorem B4048811 : Blo 884570 4048811 := bstep (se 1 (by rfl) ⟨3036608, by rfl⟩ : syracuseStep 4048811 = 6073217) B6073217
theorem B2837531 : Blo 884570 2837531 := bstep (se 1 (by rfl) ⟨2128148, by rfl⟩ : syracuseStep 2837531 = 4256297) B4256297
theorem B3591379 : Blo 884570 3591379 := bstep (se 1 (by rfl) ⟨2693534, by rfl⟩ : syracuseStep 3591379 = 5387069) B5387069
theorem B1331135 : Blo 884570 1331135 := bstep (se 1 (by rfl) ⟨998351, by rfl⟩ : syracuseStep 1331135 = 1996703) B1996703
theorem B7589983 : Blo 884570 7589983 := bstep (se 1 (by rfl) ⟨5692487, by rfl⟩ : syracuseStep 7589983 = 11384975) B11384975
theorem B4542713 : Blo 884570 4542713 := bstep (se 2 (by rfl) ⟨1703517, by rfl⟩ : syracuseStep 4542713 = 3407035) B3407035
theorem B1331867 : Blo 884570 1331867 := bstep (se 1 (by rfl) ⟨998900, by rfl⟩ : syracuseStep 1331867 = 1997801) B1997801
theorem B7559639 : Blo 884570 7559639 := bstep (se 1 (by rfl) ⟨5669729, by rfl⟩ : syracuseStep 7559639 = 11339459) B11339459
theorem B11360735 : Blo 884570 11360735 := bstep (se 1 (by rfl) ⟨8520551, by rfl⟩ : syracuseStep 11360735 = 17041103) B17041103
theorem B1498223 : Blo 884570 1498223 := bstep (se 1 (by rfl) ⟨1123667, by rfl⟩ : syracuseStep 1498223 = 2247335) B2247335
theorem B11361707 : Blo 884570 11361707 := bstep (se 1 (by rfl) ⟨8521280, by rfl⟩ : syracuseStep 11361707 = 17042561) B17042561
theorem B14409575 : Blo 884570 14409575 := bstep (se 1 (by rfl) ⟨10807181, by rfl⟩ : syracuseStep 14409575 = 21614363) B21614363
theorem B5038301 : Blo 884570 5038301 := bstep (se 3 (by rfl) ⟨944681, by rfl⟩ : syracuseStep 5038301 = 1889363) B1889363
theorem B5825135 : Blo 884570 5825135 := bstep (se 1 (by rfl) ⟨4368851, by rfl⟩ : syracuseStep 5825135 = 8737703) B8737703
theorem B2844143 : Blo 884570 2844143 := bstep (se 1 (by rfl) ⟨2133107, by rfl⟩ : syracuseStep 2844143 = 4266215) B4266215
theorem B51833951 : Blo 884570 51833951 := bstep (se 1 (by rfl) ⟨38875463, by rfl⟩ : syracuseStep 51833951 = 77750927) B77750927
theorem B1996001 : Blo 884570 1996001 := bstep (se 2 (by rfl) ⟨748500, by rfl⟩ : syracuseStep 1996001 = 1497001) B1497001
theorem B3372263 : Blo 884570 3372263 := bstep (se 1 (by rfl) ⟨2529197, by rfl⟩ : syracuseStep 3372263 = 5058395) B5058395
theorem B1997423 : Blo 884570 1997423 := bstep (se 1 (by rfl) ⟨1498067, by rfl⟩ : syracuseStep 1997423 = 2996135) B2996135
theorem B15138413 : Blo 884570 15138413 := bstep (se 3 (by rfl) ⟨2838452, by rfl⟩ : syracuseStep 15138413 = 5676905) B5676905
theorem B7765919 : Blo 884570 7765919 := bstep (se 1 (by rfl) ⟨5824439, by rfl⟩ : syracuseStep 7765919 = 11648879) B11648879
theorem B9568367 : Blo 884570 9568367 := bstep (se 1 (by rfl) ⟨7176275, by rfl⟩ : syracuseStep 9568367 = 14352551) B14352551
theorem B9569015 : Blo 884570 9569015 := bstep (se 1 (by rfl) ⟨7176761, by rfl⟩ : syracuseStep 9569015 = 14353523) B14353523
theorem B885663 : Blo 884570 885663 := bstep (se 1 (by rfl) ⟨664247, by rfl⟩ : syracuseStep 885663 = 1328495) B1328495
theorem B15533693 : Blo 884570 15533693 := bstep (se 3 (by rfl) ⟨2912567, by rfl⟩ : syracuseStep 15533693 = 5825135) B5825135
theorem B14944009 : Blo 884570 14944009 := bstep (se 2 (by rfl) ⟨5604003, by rfl⟩ : syracuseStep 14944009 = 11208007) B11208007
theorem B887423 : Blo 884570 887423 := bstep (se 1 (by rfl) ⟨665567, by rfl⟩ : syracuseStep 887423 = 1331135) B1331135
theorem B887911 : Blo 884570 887911 := bstep (se 1 (by rfl) ⟨665933, by rfl⟩ : syracuseStep 887911 = 1331867) B1331867
theorem B4788505 : Blo 884570 4788505 := bstep (se 2 (by rfl) ⟨1795689, by rfl⟩ : syracuseStep 4788505 = 3591379) B3591379
theorem B7573823 : Blo 884570 7573823 := bstep (se 1 (by rfl) ⟨5680367, by rfl⟩ : syracuseStep 7573823 = 11360735) B11360735
theorem B7574471 : Blo 884570 7574471 := bstep (se 1 (by rfl) ⟨5680853, by rfl⟩ : syracuseStep 7574471 = 11361707) B11361707
theorem B9606383 : Blo 884570 9606383 := bstep (se 1 (by rfl) ⟨7204787, by rfl⟩ : syracuseStep 9606383 = 14409575) B14409575
theorem B5057255 : Blo 884570 5057255 := bstep (se 1 (by rfl) ⟨3792941, by rfl⟩ : syracuseStep 5057255 = 7585883) B7585883
theorem B3844907 : Blo 884570 3844907 := bstep (se 1 (by rfl) ⟨2883680, by rfl⟩ : syracuseStep 3844907 = 5767361) B5767361
theorem B5057963 : Blo 884570 5057963 := bstep (se 1 (by rfl) ⟨3793472, by rfl⟩ : syracuseStep 5057963 = 7586945) B7586945
theorem B1682927 : Blo 884570 1682927 := bstep (se 1 (by rfl) ⟨1262195, by rfl⟩ : syracuseStep 1682927 = 2524391) B2524391
theorem B11382515 : Blo 884570 11382515 := bstep (se 1 (by rfl) ⟨8536886, by rfl⟩ : syracuseStep 11382515 = 17073773) B17073773
theorem B2699207 : Blo 884570 2699207 := bstep (se 1 (by rfl) ⟨2024405, by rfl⟩ : syracuseStep 2699207 = 4048811) B4048811
theorem B54571657 : Blo 884570 54571657 := bstep (se 2 (by rfl) ⟨20464371, by rfl⟩ : syracuseStep 54571657 = 40928743) B40928743
theorem B3028475 : Blo 884570 3028475 := bstep (se 1 (by rfl) ⟨2271356, by rfl⟩ : syracuseStep 3028475 = 4542713) B4542713
theorem B998815 : Blo 884570 998815 := bstep (se 1 (by rfl) ⟨749111, by rfl⟩ : syracuseStep 998815 = 1498223) B1498223
theorem B3358867 : Blo 884570 3358867 := bstep (se 1 (by rfl) ⟨2519150, by rfl⟩ : syracuseStep 3358867 = 5038301) B5038301
theorem B34555967 : Blo 884570 34555967 := bstep (se 1 (by rfl) ⟨25916975, by rfl⟩ : syracuseStep 34555967 = 51833951) B51833951
theorem B5687567 : Blo 884570 5687567 := bstep (se 1 (by rfl) ⟨4265675, by rfl⟩ : syracuseStep 5687567 = 8531351) B8531351
theorem B29084363 : Blo 884570 29084363 := bstep (se 1 (by rfl) ⟨21813272, by rfl⟩ : syracuseStep 29084363 = 43626545) B43626545
theorem B1330667 : Blo 884570 1330667 := bstep (se 1 (by rfl) ⟨998000, by rfl⟩ : syracuseStep 1330667 = 1996001) B1996001
theorem B2248175 : Blo 884570 2248175 := bstep (se 1 (by rfl) ⟨1686131, by rfl⟩ : syracuseStep 2248175 = 3372263) B3372263
theorem B1331615 : Blo 884570 1331615 := bstep (se 1 (by rfl) ⟨998711, by rfl⟩ : syracuseStep 1331615 = 1997423) B1997423
theorem B5690027 : Blo 884570 5690027 := bstep (se 1 (by rfl) ⟨4267520, by rfl⟩ : syracuseStep 5690027 = 8535041) B8535041
theorem B3364199 : Blo 884570 3364199 := bstep (se 1 (by rfl) ⟨2523149, by rfl⟩ : syracuseStep 3364199 = 5046299) B5046299
theorem B1891687 : Blo 884570 1891687 := bstep (se 1 (by rfl) ⟨1418765, by rfl⟩ : syracuseStep 1891687 = 2837531) B2837531
theorem B6382111 : Blo 884570 6382111 := bstep (se 1 (by rfl) ⟨4786583, by rfl⟩ : syracuseStep 6382111 = 9573167) B9573167
theorem B1992239 : Blo 884570 1992239 := bstep (se 1 (by rfl) ⟨1494179, by rfl⟩ : syracuseStep 1992239 = 2988359) B2988359
theorem B5039759 : Blo 884570 5039759 := bstep (se 1 (by rfl) ⟨3779819, by rfl⟩ : syracuseStep 5039759 = 7559639) B7559639
theorem B1993031 : Blo 884570 1993031 := bstep (se 1 (by rfl) ⟨1494773, by rfl⟩ : syracuseStep 1993031 = 2989547) B2989547
theorem B10119977 : Blo 884570 10119977 := bstep (se 2 (by rfl) ⟨3794991, by rfl⟩ : syracuseStep 10119977 = 7589983) B7589983
theorem B1994399 : Blo 884570 1994399 := bstep (se 1 (by rfl) ⟨1495799, by rfl⟩ : syracuseStep 1994399 = 2991599) B2991599
theorem B1896095 : Blo 884570 1896095 := bstep (se 1 (by rfl) ⟨1422071, by rfl⟩ : syracuseStep 1896095 = 2844143) B2844143
theorem B2519743 : Blo 884570 2519743 := bstep (se 1 (by rfl) ⟨1889807, by rfl⟩ : syracuseStep 2519743 = 3779615) B3779615
theorem B1995623 : Blo 884570 1995623 := bstep (se 1 (by rfl) ⟨1496717, by rfl⟩ : syracuseStep 1995623 = 2993435) B2993435
theorem B1995983 : Blo 884570 1995983 := bstep (se 1 (by rfl) ⟨1496987, by rfl⟩ : syracuseStep 1995983 = 2993975) B2993975
theorem B6387443 : Blo 884570 6387443 := bstep (se 1 (by rfl) ⟨4790582, by rfl⟩ : syracuseStep 6387443 = 9581165) B9581165
theorem B10092275 : Blo 884570 10092275 := bstep (se 1 (by rfl) ⟨7569206, by rfl⟩ : syracuseStep 10092275 = 15138413) B15138413
theorem B5177279 : Blo 884570 5177279 := bstep (se 1 (by rfl) ⟨3882959, by rfl⟩ : syracuseStep 5177279 = 7765919) B7765919
theorem B10355795 : Blo 884570 10355795 := bstep (se 1 (by rfl) ⟨7766846, by rfl⟩ : syracuseStep 10355795 = 15533693) B15533693
theorem B23037311 : Blo 884570 23037311 := bstep (se 1 (by rfl) ⟨17277983, by rfl⟩ : syracuseStep 23037311 = 34555967) B34555967
theorem B15173405 : Blo 884570 15173405 := bstep (se 3 (by rfl) ⟨2845013, by rfl⟩ : syracuseStep 15173405 = 5690027) B5690027
theorem B887111 : Blo 884570 887111 := bstep (se 1 (by rfl) ⟨665333, by rfl⟩ : syracuseStep 887111 = 1330667) B1330667
theorem B19925345 : Blo 884570 19925345 := bstep (se 2 (by rfl) ⟨7472004, by rfl⟩ : syracuseStep 19925345 = 14944009) B14944009
theorem B5049215 : Blo 884570 5049215 := bstep (se 1 (by rfl) ⟨3786911, by rfl⟩ : syracuseStep 5049215 = 7573823) B7573823
theorem B887743 : Blo 884570 887743 := bstep (se 1 (by rfl) ⟨665807, by rfl⟩ : syracuseStep 887743 = 1331615) B1331615
theorem B5049647 : Blo 884570 5049647 := bstep (se 1 (by rfl) ⟨3787235, by rfl⟩ : syracuseStep 5049647 = 7574471) B7574471
theorem B2563271 : Blo 884570 2563271 := bstep (se 1 (by rfl) ⟨1922453, by rfl⟩ : syracuseStep 2563271 = 3844907) B3844907
theorem B1121951 : Blo 884570 1121951 := bstep (se 1 (by rfl) ⟨841463, by rfl⟩ : syracuseStep 1121951 = 1682927) B1682927
theorem B5056253 : Blo 884570 5056253 := bstep (se 3 (by rfl) ⟨948047, by rfl⟩ : syracuseStep 5056253 = 1896095) B1896095
theorem B6728183 : Blo 884570 6728183 := bstep (se 1 (by rfl) ⟨5046137, by rfl⟩ : syracuseStep 6728183 = 10092275) B10092275
theorem B13806077 : Blo 884570 13806077 := bstep (se 3 (by rfl) ⟨2588639, by rfl⟩ : syracuseStep 13806077 = 5177279) B5177279
theorem B6404255 : Blo 884570 6404255 := bstep (se 1 (by rfl) ⟨4803191, by rfl⟩ : syracuseStep 6404255 = 9606383) B9606383
theorem B2242799 : Blo 884570 2242799 := bstep (se 1 (by rfl) ⟨1682099, by rfl⟩ : syracuseStep 2242799 = 3364199) B3364199
theorem B8075933 : Blo 884570 8075933 := bstep (se 3 (by rfl) ⟨1514237, by rfl⟩ : syracuseStep 8075933 = 3028475) B3028475
theorem B72762209 : Blo 884570 72762209 := bstep (se 2 (by rfl) ⟨27285828, by rfl⟩ : syracuseStep 72762209 = 54571657) B54571657
theorem B3359657 : Blo 884570 3359657 := bstep (se 2 (by rfl) ⟨1259871, by rfl⟩ : syracuseStep 3359657 = 2519743) B2519743
theorem B1328159 : Blo 884570 1328159 := bstep (se 1 (by rfl) ⟨996119, by rfl⟩ : syracuseStep 1328159 = 1992239) B1992239
theorem B3359839 : Blo 884570 3359839 := bstep (se 1 (by rfl) ⟨2519879, by rfl⟩ : syracuseStep 3359839 = 5039759) B5039759
theorem B1328687 : Blo 884570 1328687 := bstep (se 1 (by rfl) ⟨996515, by rfl⟩ : syracuseStep 1328687 = 1993031) B1993031
theorem B1329599 : Blo 884570 1329599 := bstep (se 1 (by rfl) ⟨997199, by rfl⟩ : syracuseStep 1329599 = 1994399) B1994399
theorem B7588343 : Blo 884570 7588343 := bstep (se 1 (by rfl) ⟨5691257, by rfl⟩ : syracuseStep 7588343 = 11382515) B11382515
theorem B1330415 : Blo 884570 1330415 := bstep (se 1 (by rfl) ⟨997811, by rfl⟩ : syracuseStep 1330415 = 1995623) B1995623
theorem B1330655 : Blo 884570 1330655 := bstep (se 1 (by rfl) ⟨997991, by rfl⟩ : syracuseStep 1330655 = 1995983) B1995983
theorem B1331753 : Blo 884570 1331753 := bstep (se 2 (by rfl) ⟨499407, by rfl⟩ : syracuseStep 1331753 = 998815) B998815
theorem B6378911 : Blo 884570 6378911 := bstep (se 1 (by rfl) ⟨4784183, by rfl⟩ : syracuseStep 6378911 = 9568367) B9568367
theorem B4478489 : Blo 884570 4478489 := bstep (se 2 (by rfl) ⟨1679433, by rfl⟩ : syracuseStep 4478489 = 3358867) B3358867
theorem B6379343 : Blo 884570 6379343 := bstep (se 1 (by rfl) ⟨4784507, by rfl⟩ : syracuseStep 6379343 = 9569015) B9569015
theorem B8509481 : Blo 884570 8509481 := bstep (se 2 (by rfl) ⟨3191055, by rfl⟩ : syracuseStep 8509481 = 6382111) B6382111
theorem B3791711 : Blo 884570 3791711 := bstep (se 1 (by rfl) ⟨2843783, by rfl⟩ : syracuseStep 3791711 = 5687567) B5687567
theorem B19389575 : Blo 884570 19389575 := bstep (se 1 (by rfl) ⟨14542181, by rfl⟩ : syracuseStep 19389575 = 29084363) B29084363
theorem B1498783 : Blo 884570 1498783 := bstep (se 1 (by rfl) ⟨1124087, by rfl⟩ : syracuseStep 1498783 = 2248175) B2248175
theorem B6384673 : Blo 884570 6384673 := bstep (se 2 (by rfl) ⟨2394252, by rfl⟩ : syracuseStep 6384673 = 4788505) B4788505
theorem B3371503 : Blo 884570 3371503 := bstep (se 1 (by rfl) ⟨2528627, by rfl⟩ : syracuseStep 3371503 = 5057255) B5057255
theorem B6746651 : Blo 884570 6746651 := bstep (se 1 (by rfl) ⟨5059988, by rfl⟩ : syracuseStep 6746651 = 10119977) B10119977
theorem B3371975 : Blo 884570 3371975 := bstep (se 1 (by rfl) ⟨2528981, by rfl⟩ : syracuseStep 3371975 = 5057963) B5057963
theorem B1799471 : Blo 884570 1799471 := bstep (se 1 (by rfl) ⟨1349603, by rfl⟩ : syracuseStep 1799471 = 2699207) B2699207
theorem B4258295 : Blo 884570 4258295 := bstep (se 1 (by rfl) ⟨3193721, by rfl⟩ : syracuseStep 4258295 = 6387443) B6387443
theorem B2522249 : Blo 884570 2522249 := bstep (se 2 (by rfl) ⟨945843, by rfl⟩ : syracuseStep 2522249 = 1891687) B1891687
theorem B885439 : Blo 884570 885439 := bstep (se 1 (by rfl) ⟨664079, by rfl⟩ : syracuseStep 885439 = 1328159) B1328159
theorem B885791 : Blo 884570 885791 := bstep (se 1 (by rfl) ⟨664343, by rfl⟩ : syracuseStep 885791 = 1328687) B1328687
theorem B886399 : Blo 884570 886399 := bstep (se 1 (by rfl) ⟨664799, by rfl⟩ : syracuseStep 886399 = 1329599) B1329599
theorem B886943 : Blo 884570 886943 := bstep (se 1 (by rfl) ⟨665207, by rfl⟩ : syracuseStep 886943 = 1330415) B1330415
theorem B887103 : Blo 884570 887103 := bstep (se 1 (by rfl) ⟨665327, by rfl⟩ : syracuseStep 887103 = 1330655) B1330655
theorem B887835 : Blo 884570 887835 := bstep (se 1 (by rfl) ⟨665876, by rfl⟩ : syracuseStep 887835 = 1331753) B1331753
theorem B2985659 : Blo 884570 2985659 := bstep (se 1 (by rfl) ⟨2239244, by rfl⟩ : syracuseStep 2985659 = 4478489) B4478489
theorem B5672987 : Blo 884570 5672987 := bstep (se 1 (by rfl) ⟨4254740, by rfl⟩ : syracuseStep 5672987 = 8509481) B8509481
theorem B1708847 : Blo 884570 1708847 := bstep (se 1 (by rfl) ⟨1281635, by rfl⟩ : syracuseStep 1708847 = 2563271) B2563271
theorem B34051589 : Blo 884570 34051589 := bstep (se 4 (by rfl) ⟨3192336, by rfl⟩ : syracuseStep 34051589 = 6384673) B6384673
theorem B4495337 : Blo 884570 4495337 := bstep (se 2 (by rfl) ⟨1685751, by rfl⟩ : syracuseStep 4495337 = 3371503) B3371503
theorem B4497767 : Blo 884570 4497767 := bstep (se 1 (by rfl) ⟨3373325, by rfl⟩ : syracuseStep 4497767 = 6746651) B6746651
theorem B4269503 : Blo 884570 4269503 := bstep (se 1 (by rfl) ⟨3202127, by rfl⟩ : syracuseStep 4269503 = 6404255) B6404255
theorem B2991869 : Blo 884570 2991869 := bstep (se 3 (by rfl) ⟨560975, by rfl⟩ : syracuseStep 2991869 = 1121951) B1121951
theorem B5383955 : Blo 884570 5383955 := bstep (se 1 (by rfl) ⟨4037966, by rfl⟩ : syracuseStep 5383955 = 8075933) B8075933
theorem B1681499 : Blo 884570 1681499 := bstep (se 1 (by rfl) ⟨1261124, by rfl⟩ : syracuseStep 1681499 = 2522249) B2522249
theorem B48508139 : Blo 884570 48508139 := bstep (se 1 (by rfl) ⟨36381104, by rfl⟩ : syracuseStep 48508139 = 72762209) B72762209
theorem B2239771 : Blo 884570 2239771 := bstep (se 1 (by rfl) ⟨1679828, by rfl⟩ : syracuseStep 2239771 = 3359657) B3359657
theorem B13283563 : Blo 884570 13283563 := bstep (se 1 (by rfl) ⟨9962672, by rfl⟩ : syracuseStep 13283563 = 19925345) B19925345
theorem B5058895 : Blo 884570 5058895 := bstep (se 1 (by rfl) ⟨3794171, by rfl⟩ : syracuseStep 5058895 = 7588343) B7588343
theorem B36816205 : Blo 884570 36816205 := bstep (se 3 (by rfl) ⟨6903038, by rfl⟩ : syracuseStep 36816205 = 13806077) B13806077
theorem B10111229 : Blo 884570 10111229 := bstep (se 3 (by rfl) ⟨1895855, by rfl⟩ : syracuseStep 10111229 = 3791711) B3791711
theorem B2247983 : Blo 884570 2247983 := bstep (se 1 (by rfl) ⟨1685987, by rfl⟩ : syracuseStep 2247983 = 3371975) B3371975
theorem B1199647 : Blo 884570 1199647 := bstep (se 1 (by rfl) ⟨899735, by rfl⟩ : syracuseStep 1199647 = 1799471) B1799471
theorem B1495199 : Blo 884570 1495199 := bstep (se 1 (by rfl) ⟨1121399, by rfl⟩ : syracuseStep 1495199 = 2242799) B2242799
theorem B2838863 : Blo 884570 2838863 := bstep (se 1 (by rfl) ⟨2129147, by rfl⟩ : syracuseStep 2838863 = 4258295) B4258295
theorem B6903863 : Blo 884570 6903863 := bstep (se 1 (by rfl) ⟨5177897, by rfl⟩ : syracuseStep 6903863 = 10355795) B10355795
theorem B10115603 : Blo 884570 10115603 := bstep (se 1 (by rfl) ⟨7586702, by rfl⟩ : syracuseStep 10115603 = 15173405) B15173405
theorem B4479785 : Blo 884570 4479785 := bstep (se 2 (by rfl) ⟨1679919, by rfl⟩ : syracuseStep 4479785 = 3359839) B3359839
theorem B3366143 : Blo 884570 3366143 := bstep (se 1 (by rfl) ⟨2524607, by rfl⟩ : syracuseStep 3366143 = 5049215) B5049215
theorem B3366431 : Blo 884570 3366431 := bstep (se 1 (by rfl) ⟨2524823, by rfl⟩ : syracuseStep 3366431 = 5049647) B5049647
theorem B4252607 : Blo 884570 4252607 := bstep (se 1 (by rfl) ⟨3189455, by rfl⟩ : syracuseStep 4252607 = 6378911) B6378911
theorem B61432829 : Blo 884570 61432829 := bstep (se 3 (by rfl) ⟨11518655, by rfl⟩ : syracuseStep 61432829 = 23037311) B23037311
theorem B4252895 : Blo 884570 4252895 := bstep (se 1 (by rfl) ⟨3189671, by rfl⟩ : syracuseStep 4252895 = 6379343) B6379343
theorem B3370835 : Blo 884570 3370835 := bstep (se 1 (by rfl) ⟨2528126, by rfl⟩ : syracuseStep 3370835 = 5056253) B5056253
theorem B4485455 : Blo 884570 4485455 := bstep (se 1 (by rfl) ⟨3364091, by rfl⟩ : syracuseStep 4485455 = 6728183) B6728183
theorem B51705533 : Blo 884570 51705533 := bstep (se 3 (by rfl) ⟨9694787, by rfl⟩ : syracuseStep 51705533 = 19389575) B19389575
theorem B1998377 : Blo 884570 1998377 := bstep (se 2 (by rfl) ⟨749391, by rfl⟩ : syracuseStep 1998377 = 1498783) B1498783
theorem B49088273 : Blo 884570 49088273 := bstep (se 2 (by rfl) ⟨18408102, by rfl⟩ : syracuseStep 49088273 = 36816205) B36816205
theorem B2986361 : Blo 884570 2986361 := bstep (se 2 (by rfl) ⟨1119885, by rfl⟩ : syracuseStep 2986361 = 2239771) B2239771
theorem B2986523 : Blo 884570 2986523 := bstep (se 1 (by rfl) ⟨2239892, by rfl⟩ : syracuseStep 2986523 = 4479785) B4479785
theorem B2990303 : Blo 884570 2990303 := bstep (se 1 (by rfl) ⟨2242727, by rfl⟩ : syracuseStep 2990303 = 4485455) B4485455
theorem B3781991 : Blo 884570 3781991 := bstep (se 1 (by rfl) ⟨2836493, by rfl⟩ : syracuseStep 3781991 = 5672987) B5672987
theorem B996799 : Blo 884570 996799 := bstep (se 1 (by rfl) ⟨747599, by rfl⟩ : syracuseStep 996799 = 1495199) B1495199
theorem B2996891 : Blo 884570 2996891 := bstep (se 1 (by rfl) ⟨2247668, by rfl⟩ : syracuseStep 2996891 = 4495337) B4495337
theorem B4602575 : Blo 884570 4602575 := bstep (se 1 (by rfl) ⟨3451931, by rfl⟩ : syracuseStep 4602575 = 6903863) B6903863
theorem B2244095 : Blo 884570 2244095 := bstep (se 1 (by rfl) ⟨1683071, by rfl⟩ : syracuseStep 2244095 = 3366143) B3366143
theorem B2244287 : Blo 884570 2244287 := bstep (se 1 (by rfl) ⟨1683215, by rfl⟩ : syracuseStep 2244287 = 3366431) B3366431
theorem B2998511 : Blo 884570 2998511 := bstep (se 1 (by rfl) ⟨2248883, by rfl⟩ : syracuseStep 2998511 = 4497767) B4497767
theorem B17711417 : Blo 884570 17711417 := bstep (se 2 (by rfl) ⟨6641781, by rfl⟩ : syracuseStep 17711417 = 13283563) B13283563
theorem B2835071 : Blo 884570 2835071 := bstep (se 1 (by rfl) ⟨2126303, by rfl⟩ : syracuseStep 2835071 = 4252607) B4252607
theorem B2835263 : Blo 884570 2835263 := bstep (se 1 (by rfl) ⟨2126447, by rfl⟩ : syracuseStep 2835263 = 4252895) B4252895
theorem B3589303 : Blo 884570 3589303 := bstep (se 1 (by rfl) ⟨2691977, by rfl⟩ : syracuseStep 3589303 = 5383955) B5383955
theorem B2247223 : Blo 884570 2247223 := bstep (se 1 (by rfl) ⟨1685417, by rfl⟩ : syracuseStep 2247223 = 3370835) B3370835
theorem B1332251 : Blo 884570 1332251 := bstep (se 1 (by rfl) ⟨999188, by rfl⟩ : syracuseStep 1332251 = 1998377) B1998377
theorem B6740819 : Blo 884570 6740819 := bstep (se 1 (by rfl) ⟨5055614, by rfl⟩ : syracuseStep 6740819 = 10111229) B10111229
theorem B1498655 : Blo 884570 1498655 := bstep (se 1 (by rfl) ⟨1123991, by rfl⟩ : syracuseStep 1498655 = 2247983) B2247983
theorem B1990439 : Blo 884570 1990439 := bstep (se 1 (by rfl) ⟨1492829, by rfl⟩ : syracuseStep 1990439 = 2985659) B2985659
theorem B1892575 : Blo 884570 1892575 := bstep (se 1 (by rfl) ⟨1419431, by rfl⟩ : syracuseStep 1892575 = 2838863) B2838863
theorem B1139231 : Blo 884570 1139231 := bstep (se 1 (by rfl) ⟨854423, by rfl⟩ : syracuseStep 1139231 = 1708847) B1708847
theorem B22701059 : Blo 884570 22701059 := bstep (se 1 (by rfl) ⟨17025794, by rfl⟩ : syracuseStep 22701059 = 34051589) B34051589
theorem B6743735 : Blo 884570 6743735 := bstep (se 1 (by rfl) ⟨5057801, by rfl⟩ : syracuseStep 6743735 = 10115603) B10115603
theorem B1599529 : Blo 884570 1599529 := bstep (se 2 (by rfl) ⟨599823, by rfl⟩ : syracuseStep 1599529 = 1199647) B1199647
theorem B4483997 : Blo 884570 4483997 := bstep (se 3 (by rfl) ⟨840749, by rfl⟩ : syracuseStep 4483997 = 1681499) B1681499
theorem B6745193 : Blo 884570 6745193 := bstep (se 2 (by rfl) ⟨2529447, by rfl⟩ : syracuseStep 6745193 = 5058895) B5058895
theorem B40955219 : Blo 884570 40955219 := bstep (se 1 (by rfl) ⟨30716414, by rfl⟩ : syracuseStep 40955219 = 61432829) B61432829
theorem B2846335 : Blo 884570 2846335 := bstep (se 1 (by rfl) ⟨2134751, by rfl⟩ : syracuseStep 2846335 = 4269503) B4269503
theorem B1994579 : Blo 884570 1994579 := bstep (se 1 (by rfl) ⟨1495934, by rfl⟩ : syracuseStep 1994579 = 2991869) B2991869
theorem B32338759 : Blo 884570 32338759 := bstep (se 1 (by rfl) ⟨24254069, by rfl⟩ : syracuseStep 32338759 = 48508139) B48508139
theorem B34470355 : Blo 884570 34470355 := bstep (se 1 (by rfl) ⟨25852766, by rfl⟩ : syracuseStep 34470355 = 51705533) B51705533
theorem B1999007 : Blo 884570 1999007 := bstep (se 1 (by rfl) ⟨1499255, by rfl⟩ : syracuseStep 1999007 = 2998511) B2998511
theorem B10093733 : Blo 884570 10093733 := bstep (se 4 (by rfl) ⟨946287, by rfl⟩ : syracuseStep 10093733 = 1892575) B1892575
theorem B4785737 : Blo 884570 4785737 := bstep (se 2 (by rfl) ⟨1794651, by rfl⟩ : syracuseStep 4785737 = 3589303) B3589303
theorem B2132705 : Blo 884570 2132705 := bstep (se 2 (by rfl) ⟨799764, by rfl⟩ : syracuseStep 2132705 = 1599529) B1599529
theorem B888167 : Blo 884570 888167 := bstep (se 1 (by rfl) ⟨666125, by rfl⟩ : syracuseStep 888167 = 1332251) B1332251
theorem B4493879 : Blo 884570 4493879 := bstep (se 1 (by rfl) ⟨3370409, by rfl⟩ : syracuseStep 4493879 = 6740819) B6740819
theorem B4495823 : Blo 884570 4495823 := bstep (se 1 (by rfl) ⟨3371867, by rfl⟩ : syracuseStep 4495823 = 6743735) B6743735
theorem B2989331 : Blo 884570 2989331 := bstep (se 1 (by rfl) ⟨2241998, by rfl⟩ : syracuseStep 2989331 = 4483997) B4483997
theorem B4496795 : Blo 884570 4496795 := bstep (se 1 (by rfl) ⟨3372596, by rfl⟩ : syracuseStep 4496795 = 6745193) B6745193
theorem B27303479 : Blo 884570 27303479 := bstep (se 1 (by rfl) ⟨20477609, by rfl⟩ : syracuseStep 27303479 = 40955219) B40955219
theorem B523608245 : Blo 884570 523608245 := bstep (se 5 (by rfl) ⟨24544136, by rfl⟩ : syracuseStep 523608245 = 49088273) B49088273
theorem B47230445 : Blo 884570 47230445 := bstep (se 3 (by rfl) ⟨8855708, by rfl⟩ : syracuseStep 47230445 = 17711417) B17711417
theorem B2996297 : Blo 884570 2996297 := bstep (se 2 (by rfl) ⟨1123611, by rfl⟩ : syracuseStep 2996297 = 2247223) B2247223
theorem B999103 : Blo 884570 999103 := bstep (se 1 (by rfl) ⟨749327, by rfl⟩ : syracuseStep 999103 = 1498655) B1498655
theorem B1326959 : Blo 884570 1326959 := bstep (se 1 (by rfl) ⟨995219, by rfl⟩ : syracuseStep 1326959 = 1990439) B1990439
theorem B1329065 : Blo 884570 1329065 := bstep (se 2 (by rfl) ⟨498399, by rfl⟩ : syracuseStep 1329065 = 996799) B996799
theorem B1329719 : Blo 884570 1329719 := bstep (se 1 (by rfl) ⟨997289, by rfl⟩ : syracuseStep 1329719 = 1994579) B1994579
theorem B45960473 : Blo 884570 45960473 := bstep (se 2 (by rfl) ⟨17235177, by rfl⟩ : syracuseStep 45960473 = 34470355) B34470355
theorem B3068383 : Blo 884570 3068383 := bstep (se 1 (by rfl) ⟨2301287, by rfl⟩ : syracuseStep 3068383 = 4602575) B4602575
theorem B1496063 : Blo 884570 1496063 := bstep (se 1 (by rfl) ⟨1122047, by rfl⟩ : syracuseStep 1496063 = 2244095) B2244095
theorem B1496191 : Blo 884570 1496191 := bstep (se 1 (by rfl) ⟨1122143, by rfl⟩ : syracuseStep 1496191 = 2244287) B2244287
theorem B1890047 : Blo 884570 1890047 := bstep (se 1 (by rfl) ⟨1417535, by rfl⟩ : syracuseStep 1890047 = 2835071) B2835071
theorem B3037949 : Blo 884570 3037949 := bstep (se 3 (by rfl) ⟨569615, by rfl⟩ : syracuseStep 3037949 = 1139231) B1139231
theorem B7560701 : Blo 884570 7560701 := bstep (se 3 (by rfl) ⟨1417631, by rfl⟩ : syracuseStep 7560701 = 2835263) B2835263
theorem B1990907 : Blo 884570 1990907 := bstep (se 1 (by rfl) ⟨1493180, by rfl⟩ : syracuseStep 1990907 = 2986361) B2986361
theorem B1991015 : Blo 884570 1991015 := bstep (se 1 (by rfl) ⟨1493261, by rfl⟩ : syracuseStep 1991015 = 2986523) B2986523
theorem B3795113 : Blo 884570 3795113 := bstep (se 2 (by rfl) ⟨1423167, by rfl⟩ : syracuseStep 3795113 = 2846335) B2846335
theorem B1993535 : Blo 884570 1993535 := bstep (se 1 (by rfl) ⟨1495151, by rfl⟩ : syracuseStep 1993535 = 2990303) B2990303
theorem B15134039 : Blo 884570 15134039 := bstep (se 1 (by rfl) ⟨11350529, by rfl⟩ : syracuseStep 15134039 = 22701059) B22701059
theorem B43118345 : Blo 884570 43118345 := bstep (se 2 (by rfl) ⟨16169379, by rfl⟩ : syracuseStep 43118345 = 32338759) B32338759
theorem B2521327 : Blo 884570 2521327 := bstep (se 1 (by rfl) ⟨1890995, by rfl⟩ : syracuseStep 2521327 = 3781991) B3781991
theorem B1997927 : Blo 884570 1997927 := bstep (se 1 (by rfl) ⟨1498445, by rfl⟩ : syracuseStep 1997927 = 2996891) B2996891
theorem B886043 : Blo 884570 886043 := bstep (se 1 (by rfl) ⟨664532, by rfl⟩ : syracuseStep 886043 = 1329065) B1329065
theorem B886479 : Blo 884570 886479 := bstep (se 1 (by rfl) ⟨664859, by rfl⟩ : syracuseStep 886479 = 1329719) B1329719
theorem B30640315 : Blo 884570 30640315 := bstep (se 1 (by rfl) ⟨22980236, by rfl⟩ : syracuseStep 30640315 = 45960473) B45960473
theorem B2530075 : Blo 884570 2530075 := bstep (se 1 (by rfl) ⟨1897556, by rfl⟩ : syracuseStep 2530075 = 3795113) B3795113
theorem B28745563 : Blo 884570 28745563 := bstep (se 1 (by rfl) ⟨21559172, by rfl⟩ : syracuseStep 28745563 = 43118345) B43118345
theorem B6729155 : Blo 884570 6729155 := bstep (se 1 (by rfl) ⟨5046866, by rfl⟩ : syracuseStep 6729155 = 10093733) B10093733
theorem B1421803 : Blo 884570 1421803 := bstep (se 1 (by rfl) ⟨1066352, by rfl⟩ : syracuseStep 1421803 = 2132705) B2132705
theorem B2995919 : Blo 884570 2995919 := bstep (se 1 (by rfl) ⟨2246939, by rfl⟩ : syracuseStep 2995919 = 4493879) B4493879
theorem B997375 : Blo 884570 997375 := bstep (se 1 (by rfl) ⟨748031, by rfl⟩ : syracuseStep 997375 = 1496063) B1496063
theorem B1260031 : Blo 884570 1260031 := bstep (se 1 (by rfl) ⟨945023, by rfl⟩ : syracuseStep 1260031 = 1890047) B1890047
theorem B12761965 : Blo 884570 12761965 := bstep (se 3 (by rfl) ⟨2392868, by rfl⟩ : syracuseStep 12761965 = 4785737) B4785737
theorem B2997215 : Blo 884570 2997215 := bstep (se 1 (by rfl) ⟨2247911, by rfl⟩ : syracuseStep 2997215 = 4495823) B4495823
theorem B2997863 : Blo 884570 2997863 := bstep (se 1 (by rfl) ⟨2248397, by rfl⟩ : syracuseStep 2997863 = 4496795) B4496795
theorem B18202319 : Blo 884570 18202319 := bstep (se 1 (by rfl) ⟨13651739, by rfl⟩ : syracuseStep 18202319 = 27303479) B27303479
theorem B1327271 : Blo 884570 1327271 := bstep (se 1 (by rfl) ⟨995453, by rfl⟩ : syracuseStep 1327271 = 1990907) B1990907
theorem B1327343 : Blo 884570 1327343 := bstep (se 1 (by rfl) ⟨995507, by rfl⟩ : syracuseStep 1327343 = 1991015) B1991015
theorem B1329023 : Blo 884570 1329023 := bstep (se 1 (by rfl) ⟨996767, by rfl⟩ : syracuseStep 1329023 = 1993535) B1993535
theorem B3361769 : Blo 884570 3361769 := bstep (se 2 (by rfl) ⟨1260663, by rfl⟩ : syracuseStep 3361769 = 2521327) B2521327
theorem B1331951 : Blo 884570 1331951 := bstep (se 1 (by rfl) ⟨998963, by rfl⟩ : syracuseStep 1331951 = 1997927) B1997927
theorem B1332137 : Blo 884570 1332137 := bstep (se 2 (by rfl) ⟨499551, by rfl⟩ : syracuseStep 1332137 = 999103) B999103
theorem B1332671 : Blo 884570 1332671 := bstep (se 1 (by rfl) ⟨999503, by rfl⟩ : syracuseStep 1332671 = 1999007) B1999007
theorem B2025299 : Blo 884570 2025299 := bstep (se 1 (by rfl) ⟨1518974, by rfl⟩ : syracuseStep 2025299 = 3037949) B3037949
theorem B1992887 : Blo 884570 1992887 := bstep (se 1 (by rfl) ⟨1494665, by rfl⟩ : syracuseStep 1992887 = 2989331) B2989331
theorem B5040467 : Blo 884570 5040467 := bstep (se 1 (by rfl) ⟨3780350, by rfl⟩ : syracuseStep 5040467 = 7560701) B7560701
theorem B349072163 : Blo 884570 349072163 := bstep (se 1 (by rfl) ⟨261804122, by rfl⟩ : syracuseStep 349072163 = 523608245) B523608245
theorem B4091177 : Blo 884570 4091177 := bstep (se 2 (by rfl) ⟨1534191, by rfl⟩ : syracuseStep 4091177 = 3068383) B3068383
theorem B1994921 : Blo 884570 1994921 := bstep (se 2 (by rfl) ⟨748095, by rfl⟩ : syracuseStep 1994921 = 1496191) B1496191
theorem B10089359 : Blo 884570 10089359 := bstep (se 1 (by rfl) ⟨7567019, by rfl⟩ : syracuseStep 10089359 = 15134039) B15134039
theorem B31486963 : Blo 884570 31486963 := bstep (se 1 (by rfl) ⟨23615222, by rfl⟩ : syracuseStep 31486963 = 47230445) B47230445
theorem B1997531 : Blo 884570 1997531 := bstep (se 1 (by rfl) ⟨1498148, by rfl⟩ : syracuseStep 1997531 = 2996297) B2996297
theorem B884639 : Blo 884570 884639 := bstep (se 1 (by rfl) ⟨663479, by rfl⟩ : syracuseStep 884639 = 1326959) B1326959
theorem B884847 : Blo 884570 884847 := bstep (se 1 (by rfl) ⟨663635, by rfl⟩ : syracuseStep 884847 = 1327271) B1327271
theorem B884895 : Blo 884570 884895 := bstep (se 1 (by rfl) ⟨663671, by rfl⟩ : syracuseStep 884895 = 1327343) B1327343
theorem B886015 : Blo 884570 886015 := bstep (se 1 (by rfl) ⟨664511, by rfl⟩ : syracuseStep 886015 = 1329023) B1329023
theorem B887967 : Blo 884570 887967 := bstep (se 1 (by rfl) ⟨665975, by rfl⟩ : syracuseStep 887967 = 1331951) B1331951
theorem B888091 : Blo 884570 888091 := bstep (se 1 (by rfl) ⟨666068, by rfl⟩ : syracuseStep 888091 = 1332137) B1332137
theorem B888447 : Blo 884570 888447 := bstep (se 1 (by rfl) ⟨666335, by rfl⟩ : syracuseStep 888447 = 1332671) B1332671
theorem B1350199 : Blo 884570 1350199 := bstep (se 1 (by rfl) ⟨1012649, by rfl⟩ : syracuseStep 1350199 = 2025299) B2025299
theorem B41982617 : Blo 884570 41982617 := bstep (se 2 (by rfl) ⟨15743481, by rfl⟩ : syracuseStep 41982617 = 31486963) B31486963
theorem B2727451 : Blo 884570 2727451 := bstep (se 1 (by rfl) ⟨2045588, by rfl⟩ : syracuseStep 2727451 = 4091177) B4091177
theorem B6726239 : Blo 884570 6726239 := bstep (se 1 (by rfl) ⟨5044679, by rfl⟩ : syracuseStep 6726239 = 10089359) B10089359
theorem B1680041 : Blo 884570 1680041 := bstep (se 2 (by rfl) ⟨630015, by rfl⟩ : syracuseStep 1680041 = 1260031) B1260031
theorem B17015953 : Blo 884570 17015953 := bstep (se 2 (by rfl) ⟨6380982, by rfl⟩ : syracuseStep 17015953 = 12761965) B12761965
theorem B12134879 : Blo 884570 12134879 := bstep (se 1 (by rfl) ⟨9101159, by rfl⟩ : syracuseStep 12134879 = 18202319) B18202319
theorem B2241179 : Blo 884570 2241179 := bstep (se 1 (by rfl) ⟨1680884, by rfl⟩ : syracuseStep 2241179 = 3361769) B3361769
theorem B1328591 : Blo 884570 1328591 := bstep (se 1 (by rfl) ⟨996443, by rfl⟩ : syracuseStep 1328591 = 1992887) B1992887
theorem B3360311 : Blo 884570 3360311 := bstep (se 1 (by rfl) ⟨2520233, by rfl⟩ : syracuseStep 3360311 = 5040467) B5040467
theorem B1329833 : Blo 884570 1329833 := bstep (se 2 (by rfl) ⟨498687, by rfl⟩ : syracuseStep 1329833 = 997375) B997375
theorem B1329947 : Blo 884570 1329947 := bstep (se 1 (by rfl) ⟨997460, by rfl⟩ : syracuseStep 1329947 = 1994921) B1994921
theorem B1331687 : Blo 884570 1331687 := bstep (se 1 (by rfl) ⟨998765, by rfl⟩ : syracuseStep 1331687 = 1997531) B1997531
theorem B38327417 : Blo 884570 38327417 := bstep (se 2 (by rfl) ⟨14372781, by rfl⟩ : syracuseStep 38327417 = 28745563) B28745563
theorem B40853753 : Blo 884570 40853753 := bstep (se 2 (by rfl) ⟨15320157, by rfl⟩ : syracuseStep 40853753 = 30640315) B30640315
theorem B1895737 : Blo 884570 1895737 := bstep (se 2 (by rfl) ⟨710901, by rfl⟩ : syracuseStep 1895737 = 1421803) B1421803
theorem B232714775 : Blo 884570 232714775 := bstep (se 1 (by rfl) ⟨174536081, by rfl⟩ : syracuseStep 232714775 = 349072163) B349072163
theorem B4486103 : Blo 884570 4486103 := bstep (se 1 (by rfl) ⟨3364577, by rfl⟩ : syracuseStep 4486103 = 6729155) B6729155
theorem B3373433 : Blo 884570 3373433 := bstep (se 2 (by rfl) ⟨1265037, by rfl⟩ : syracuseStep 3373433 = 2530075) B2530075
theorem B1997279 : Blo 884570 1997279 := bstep (se 1 (by rfl) ⟨1497959, by rfl⟩ : syracuseStep 1997279 = 2995919) B2995919
theorem B1998143 : Blo 884570 1998143 := bstep (se 1 (by rfl) ⟨1498607, by rfl⟩ : syracuseStep 1998143 = 2997215) B2997215
theorem B1998575 : Blo 884570 1998575 := bstep (se 1 (by rfl) ⟨1498931, by rfl⟩ : syracuseStep 1998575 = 2997863) B2997863
theorem B885727 : Blo 884570 885727 := bstep (se 1 (by rfl) ⟨664295, by rfl⟩ : syracuseStep 885727 = 1328591) B1328591
theorem B886555 : Blo 884570 886555 := bstep (se 1 (by rfl) ⟨664916, by rfl⟩ : syracuseStep 886555 = 1329833) B1329833
theorem B886631 : Blo 884570 886631 := bstep (se 1 (by rfl) ⟨664973, by rfl⟩ : syracuseStep 886631 = 1329947) B1329947
theorem B887791 : Blo 884570 887791 := bstep (se 1 (by rfl) ⟨665843, by rfl⟩ : syracuseStep 887791 = 1331687) B1331687
theorem B2527649 : Blo 884570 2527649 := bstep (se 2 (by rfl) ⟨947868, by rfl⟩ : syracuseStep 2527649 = 1895737) B1895737
theorem B27988411 : Blo 884570 27988411 := bstep (se 1 (by rfl) ⟨20991308, by rfl⟩ : syracuseStep 27988411 = 41982617) B41982617
theorem B27235835 : Blo 884570 27235835 := bstep (se 1 (by rfl) ⟨20426876, by rfl⟩ : syracuseStep 27235835 = 40853753) B40853753
theorem B2990735 : Blo 884570 2990735 := bstep (se 1 (by rfl) ⟨2243051, by rfl⟩ : syracuseStep 2990735 = 4486103) B4486103
theorem B2240207 : Blo 884570 2240207 := bstep (se 1 (by rfl) ⟨1680155, by rfl⟩ : syracuseStep 2240207 = 3360311) B3360311
theorem B22687937 : Blo 884570 22687937 := bstep (se 2 (by rfl) ⟨8507976, by rfl⟩ : syracuseStep 22687937 = 17015953) B17015953
theorem B155143183 : Blo 884570 155143183 := bstep (se 1 (by rfl) ⟨116357387, by rfl⟩ : syracuseStep 155143183 = 232714775) B232714775
theorem B1494119 : Blo 884570 1494119 := bstep (se 1 (by rfl) ⟨1120589, by rfl⟩ : syracuseStep 1494119 = 2241179) B2241179
theorem B2248955 : Blo 884570 2248955 := bstep (se 1 (by rfl) ⟨1686716, by rfl⟩ : syracuseStep 2248955 = 3373433) B3373433
theorem B1331519 : Blo 884570 1331519 := bstep (se 1 (by rfl) ⟨998639, by rfl⟩ : syracuseStep 1331519 = 1997279) B1997279
theorem B1332095 : Blo 884570 1332095 := bstep (se 1 (by rfl) ⟨999071, by rfl⟩ : syracuseStep 1332095 = 1998143) B1998143
theorem B1332383 : Blo 884570 1332383 := bstep (se 1 (by rfl) ⟨999287, by rfl⟩ : syracuseStep 1332383 = 1998575) B1998575
theorem B4480109 : Blo 884570 4480109 := bstep (se 3 (by rfl) ⟨840020, by rfl⟩ : syracuseStep 4480109 = 1680041) B1680041
theorem B7201061 : Blo 884570 7201061 := bstep (se 4 (by rfl) ⟨675099, by rfl⟩ : syracuseStep 7201061 = 1350199) B1350199
theorem B25551611 : Blo 884570 25551611 := bstep (se 1 (by rfl) ⟨19163708, by rfl⟩ : syracuseStep 25551611 = 38327417) B38327417
theorem B4484159 : Blo 884570 4484159 := bstep (se 1 (by rfl) ⟨3363119, by rfl⟩ : syracuseStep 4484159 = 6726239) B6726239
theorem B8089919 : Blo 884570 8089919 := bstep (se 1 (by rfl) ⟨6067439, by rfl⟩ : syracuseStep 8089919 = 12134879) B12134879
theorem B14546405 : Blo 884570 14546405 := bstep (se 4 (by rfl) ⟨1363725, by rfl⟩ : syracuseStep 14546405 = 2727451) B2727451
theorem B887679 : Blo 884570 887679 := bstep (se 1 (by rfl) ⟨665759, by rfl⟩ : syracuseStep 887679 = 1331519) B1331519
theorem B888063 : Blo 884570 888063 := bstep (se 1 (by rfl) ⟨666047, by rfl⟩ : syracuseStep 888063 = 1332095) B1332095
theorem B888255 : Blo 884570 888255 := bstep (se 1 (by rfl) ⟨666191, by rfl⟩ : syracuseStep 888255 = 1332383) B1332383
theorem B18157223 : Blo 884570 18157223 := bstep (se 1 (by rfl) ⟨13617917, by rfl⟩ : syracuseStep 18157223 = 27235835) B27235835
theorem B2986739 : Blo 884570 2986739 := bstep (se 1 (by rfl) ⟨2240054, by rfl⟩ : syracuseStep 2986739 = 4480109) B4480109
theorem B2989439 : Blo 884570 2989439 := bstep (se 1 (by rfl) ⟨2242079, by rfl⟩ : syracuseStep 2989439 = 4484159) B4484159
theorem B996079 : Blo 884570 996079 := bstep (se 1 (by rfl) ⟨747059, by rfl⟩ : syracuseStep 996079 = 1494119) B1494119
theorem B1685099 : Blo 884570 1685099 := bstep (se 1 (by rfl) ⟨1263824, by rfl⟩ : syracuseStep 1685099 = 2527649) B2527649
theorem B4800707 : Blo 884570 4800707 := bstep (se 1 (by rfl) ⟨3600530, by rfl⟩ : syracuseStep 4800707 = 7201061) B7201061
theorem B1493471 : Blo 884570 1493471 := bstep (se 1 (by rfl) ⟨1120103, by rfl⟩ : syracuseStep 1493471 = 2240207) B2240207
theorem B15125291 : Blo 884570 15125291 := bstep (se 1 (by rfl) ⟨11343968, by rfl⟩ : syracuseStep 15125291 = 22687937) B22687937
theorem B5393279 : Blo 884570 5393279 := bstep (se 1 (by rfl) ⟨4044959, by rfl⟩ : syracuseStep 5393279 = 8089919) B8089919
theorem B1499303 : Blo 884570 1499303 := bstep (se 1 (by rfl) ⟨1124477, by rfl⟩ : syracuseStep 1499303 = 2248955) B2248955
theorem B206857577 : Blo 884570 206857577 := bstep (se 2 (by rfl) ⟨77571591, by rfl⟩ : syracuseStep 206857577 = 155143183) B155143183
theorem B1993823 : Blo 884570 1993823 := bstep (se 1 (by rfl) ⟨1495367, by rfl⟩ : syracuseStep 1993823 = 2990735) B2990735
theorem B17034407 : Blo 884570 17034407 := bstep (se 1 (by rfl) ⟨12775805, by rfl⟩ : syracuseStep 17034407 = 25551611) B25551611
theorem B37317881 : Blo 884570 37317881 := bstep (se 2 (by rfl) ⟨13994205, by rfl⟩ : syracuseStep 37317881 = 27988411) B27988411
theorem B9697603 : Blo 884570 9697603 := bstep (se 1 (by rfl) ⟨7273202, by rfl⟩ : syracuseStep 9697603 = 14546405) B14546405
theorem B24878587 : Blo 884570 24878587 := bstep (se 1 (by rfl) ⟨18658940, by rfl⟩ : syracuseStep 24878587 = 37317881) B37317881
theorem B1123399 : Blo 884570 1123399 := bstep (se 1 (by rfl) ⟨842549, by rfl⟩ : syracuseStep 1123399 = 1685099) B1685099
theorem B995647 : Blo 884570 995647 := bstep (se 1 (by rfl) ⟨746735, by rfl⟩ : syracuseStep 995647 = 1493471) B1493471
theorem B12104815 : Blo 884570 12104815 := bstep (se 1 (by rfl) ⟨9078611, by rfl⟩ : syracuseStep 12104815 = 18157223) B18157223
theorem B999535 : Blo 884570 999535 := bstep (se 1 (by rfl) ⟨749651, by rfl⟩ : syracuseStep 999535 = 1499303) B1499303
theorem B137905051 : Blo 884570 137905051 := bstep (se 1 (by rfl) ⟨103428788, by rfl⟩ : syracuseStep 137905051 = 206857577) B206857577
theorem B1328105 : Blo 884570 1328105 := bstep (se 2 (by rfl) ⟨498039, by rfl⟩ : syracuseStep 1328105 = 996079) B996079
theorem B1329215 : Blo 884570 1329215 := bstep (se 1 (by rfl) ⟨996911, by rfl⟩ : syracuseStep 1329215 = 1993823) B1993823
theorem B11356271 : Blo 884570 11356271 := bstep (se 1 (by rfl) ⟨8517203, by rfl⟩ : syracuseStep 11356271 = 17034407) B17034407
theorem B12930137 : Blo 884570 12930137 := bstep (se 2 (by rfl) ⟨4848801, by rfl⟩ : syracuseStep 12930137 = 9697603) B9697603
theorem B3200471 : Blo 884570 3200471 := bstep (se 1 (by rfl) ⟨2400353, by rfl⟩ : syracuseStep 3200471 = 4800707) B4800707
theorem B10083527 : Blo 884570 10083527 := bstep (se 1 (by rfl) ⟨7562645, by rfl⟩ : syracuseStep 10083527 = 15125291) B15125291
theorem B3595519 : Blo 884570 3595519 := bstep (se 1 (by rfl) ⟨2696639, by rfl⟩ : syracuseStep 3595519 = 5393279) B5393279
theorem B1991159 : Blo 884570 1991159 := bstep (se 1 (by rfl) ⟨1493369, by rfl⟩ : syracuseStep 1991159 = 2986739) B2986739
theorem B1992959 : Blo 884570 1992959 := bstep (se 1 (by rfl) ⟨1494719, by rfl⟩ : syracuseStep 1992959 = 2989439) B2989439
theorem B885403 : Blo 884570 885403 := bstep (se 1 (by rfl) ⟨664052, by rfl⟩ : syracuseStep 885403 = 1328105) B1328105
theorem B886143 : Blo 884570 886143 := bstep (se 1 (by rfl) ⟨664607, by rfl⟩ : syracuseStep 886143 = 1329215) B1329215
theorem B7570847 : Blo 884570 7570847 := bstep (se 1 (by rfl) ⟨5678135, by rfl⟩ : syracuseStep 7570847 = 11356271) B11356271
theorem B8620091 : Blo 884570 8620091 := bstep (se 1 (by rfl) ⟨6465068, by rfl⟩ : syracuseStep 8620091 = 12930137) B12930137
theorem B2133647 : Blo 884570 2133647 := bstep (se 1 (by rfl) ⟨1600235, by rfl⟩ : syracuseStep 2133647 = 3200471) B3200471
theorem B6722351 : Blo 884570 6722351 := bstep (se 1 (by rfl) ⟨5041763, by rfl⟩ : syracuseStep 6722351 = 10083527) B10083527
theorem B4794025 : Blo 884570 4794025 := bstep (se 2 (by rfl) ⟨1797759, by rfl⟩ : syracuseStep 4794025 = 3595519) B3595519
theorem B33171449 : Blo 884570 33171449 := bstep (se 2 (by rfl) ⟨12439293, by rfl⟩ : syracuseStep 33171449 = 24878587) B24878587
theorem B183873401 : Blo 884570 183873401 := bstep (se 2 (by rfl) ⟨68952525, by rfl⟩ : syracuseStep 183873401 = 137905051) B137905051
theorem B1327439 : Blo 884570 1327439 := bstep (se 1 (by rfl) ⟨995579, by rfl⟩ : syracuseStep 1327439 = 1991159) B1991159
theorem B1327529 : Blo 884570 1327529 := bstep (se 2 (by rfl) ⟨497823, by rfl⟩ : syracuseStep 1327529 = 995647) B995647
theorem B16139753 : Blo 884570 16139753 := bstep (se 2 (by rfl) ⟨6052407, by rfl⟩ : syracuseStep 16139753 = 12104815) B12104815
theorem B1328639 : Blo 884570 1328639 := bstep (se 1 (by rfl) ⟨996479, by rfl⟩ : syracuseStep 1328639 = 1992959) B1992959
theorem B1332713 : Blo 884570 1332713 := bstep (se 2 (by rfl) ⟨499767, by rfl⟩ : syracuseStep 1332713 = 999535) B999535
theorem B1497865 : Blo 884570 1497865 := bstep (se 2 (by rfl) ⟨561699, by rfl⟩ : syracuseStep 1497865 = 1123399) B1123399
theorem B884959 : Blo 884570 884959 := bstep (se 1 (by rfl) ⟨663719, by rfl⟩ : syracuseStep 884959 = 1327439) B1327439
theorem B885019 : Blo 884570 885019 := bstep (se 1 (by rfl) ⟨663764, by rfl⟩ : syracuseStep 885019 = 1327529) B1327529
theorem B5047231 : Blo 884570 5047231 := bstep (se 1 (by rfl) ⟨3785423, by rfl⟩ : syracuseStep 5047231 = 7570847) B7570847
theorem B885759 : Blo 884570 885759 := bstep (se 1 (by rfl) ⟨664319, by rfl⟩ : syracuseStep 885759 = 1328639) B1328639
theorem B6392033 : Blo 884570 6392033 := bstep (se 2 (by rfl) ⟨2397012, by rfl⟩ : syracuseStep 6392033 = 4794025) B4794025
theorem B888475 : Blo 884570 888475 := bstep (se 1 (by rfl) ⟨666356, by rfl⟩ : syracuseStep 888475 = 1332713) B1332713
theorem B10759835 : Blo 884570 10759835 := bstep (se 1 (by rfl) ⟨8069876, by rfl⟩ : syracuseStep 10759835 = 16139753) B16139753
theorem B5746727 : Blo 884570 5746727 := bstep (se 1 (by rfl) ⟨4310045, by rfl⟩ : syracuseStep 5746727 = 8620091) B8620091
theorem B1422431 : Blo 884570 1422431 := bstep (se 1 (by rfl) ⟨1066823, by rfl⟩ : syracuseStep 1422431 = 2133647) B2133647
theorem B88457197 : Blo 884570 88457197 := bstep (se 3 (by rfl) ⟨16585724, by rfl⟩ : syracuseStep 88457197 = 33171449) B33171449
theorem B4481567 : Blo 884570 4481567 := bstep (se 1 (by rfl) ⟨3361175, by rfl⟩ : syracuseStep 4481567 = 6722351) B6722351
theorem B122582267 : Blo 884570 122582267 := bstep (se 1 (by rfl) ⟨91936700, by rfl⟩ : syracuseStep 122582267 = 183873401) B183873401
theorem B1997153 : Blo 884570 1997153 := bstep (se 2 (by rfl) ⟨748932, by rfl⟩ : syracuseStep 1997153 = 1497865) B1497865
theorem B4261355 : Blo 884570 4261355 := bstep (se 1 (by rfl) ⟨3196016, by rfl⟩ : syracuseStep 4261355 = 6392033) B6392033
theorem B2987711 : Blo 884570 2987711 := bstep (se 1 (by rfl) ⟨2240783, by rfl⟩ : syracuseStep 2987711 = 4481567) B4481567
theorem B117942929 : Blo 884570 117942929 := bstep (se 2 (by rfl) ⟨44228598, by rfl⟩ : syracuseStep 117942929 = 88457197) B88457197
theorem B6729641 : Blo 884570 6729641 := bstep (se 2 (by rfl) ⟨2523615, by rfl⟩ : syracuseStep 6729641 = 5047231) B5047231
theorem B1331435 : Blo 884570 1331435 := bstep (se 1 (by rfl) ⟨998576, by rfl⟩ : syracuseStep 1331435 = 1997153) B1997153
theorem B28692893 : Blo 884570 28692893 := bstep (se 3 (by rfl) ⟨5379917, by rfl⟩ : syracuseStep 28692893 = 10759835) B10759835
theorem B3831151 : Blo 884570 3831151 := bstep (se 1 (by rfl) ⟨2873363, by rfl⟩ : syracuseStep 3831151 = 5746727) B5746727
theorem B948287 : Blo 884570 948287 := bstep (se 1 (by rfl) ⟨711215, by rfl⟩ : syracuseStep 948287 = 1422431) B1422431
theorem B81721511 : Blo 884570 81721511 := bstep (se 1 (by rfl) ⟨61291133, by rfl⟩ : syracuseStep 81721511 = 122582267) B122582267
theorem B887623 : Blo 884570 887623 := bstep (se 1 (by rfl) ⟨665717, by rfl⟩ : syracuseStep 887623 = 1331435) B1331435
theorem B2528765 : Blo 884570 2528765 := bstep (se 3 (by rfl) ⟨474143, by rfl⟩ : syracuseStep 2528765 = 948287) B948287
theorem B78628619 : Blo 884570 78628619 := bstep (se 1 (by rfl) ⟨58971464, by rfl⟩ : syracuseStep 78628619 = 117942929) B117942929
theorem B54481007 : Blo 884570 54481007 := bstep (se 1 (by rfl) ⟨40860755, by rfl⟩ : syracuseStep 54481007 = 81721511) B81721511
theorem B2840903 : Blo 884570 2840903 := bstep (se 1 (by rfl) ⟨2130677, by rfl⟩ : syracuseStep 2840903 = 4261355) B4261355
theorem B19128595 : Blo 884570 19128595 := bstep (se 1 (by rfl) ⟨14346446, by rfl⟩ : syracuseStep 19128595 = 28692893) B28692893
theorem B1991807 : Blo 884570 1991807 := bstep (se 1 (by rfl) ⟨1493855, by rfl⟩ : syracuseStep 1991807 = 2987711) B2987711
theorem B5108201 : Blo 884570 5108201 := bstep (se 2 (by rfl) ⟨1915575, by rfl⟩ : syracuseStep 5108201 = 3831151) B3831151
theorem B4486427 : Blo 884570 4486427 := bstep (se 1 (by rfl) ⟨3364820, by rfl⟩ : syracuseStep 4486427 = 6729641) B6729641
theorem B2990951 : Blo 884570 2990951 := bstep (se 1 (by rfl) ⟨2243213, by rfl⟩ : syracuseStep 2990951 = 4486427) B4486427
theorem B25504793 : Blo 884570 25504793 := bstep (se 2 (by rfl) ⟨9564297, by rfl⟩ : syracuseStep 25504793 = 19128595) B19128595
theorem B36320671 : Blo 884570 36320671 := bstep (se 1 (by rfl) ⟨27240503, by rfl⟩ : syracuseStep 36320671 = 54481007) B54481007
theorem B1685843 : Blo 884570 1685843 := bstep (se 1 (by rfl) ⟨1264382, by rfl⟩ : syracuseStep 1685843 = 2528765) B2528765
theorem B1327871 : Blo 884570 1327871 := bstep (se 1 (by rfl) ⟨995903, by rfl⟩ : syracuseStep 1327871 = 1991807) B1991807
theorem B52419079 : Blo 884570 52419079 := bstep (se 1 (by rfl) ⟨39314309, by rfl⟩ : syracuseStep 52419079 = 78628619) B78628619
theorem B1893935 : Blo 884570 1893935 := bstep (se 1 (by rfl) ⟨1420451, by rfl⟩ : syracuseStep 1893935 = 2840903) B2840903
theorem B3405467 : Blo 884570 3405467 := bstep (se 1 (by rfl) ⟨2554100, by rfl⟩ : syracuseStep 3405467 = 5108201) B5108201
theorem B885247 : Blo 884570 885247 := bstep (se 1 (by rfl) ⟨663935, by rfl⟩ : syracuseStep 885247 = 1327871) B1327871
theorem B2270311 : Blo 884570 2270311 := bstep (se 1 (by rfl) ⟨1702733, by rfl⟩ : syracuseStep 2270311 = 3405467) B3405467
theorem B1123895 : Blo 884570 1123895 := bstep (se 1 (by rfl) ⟨842921, by rfl⟩ : syracuseStep 1123895 = 1685843) B1685843
theorem B1262623 : Blo 884570 1262623 := bstep (se 1 (by rfl) ⟨946967, by rfl⟩ : syracuseStep 1262623 = 1893935) B1893935
theorem B1993967 : Blo 884570 1993967 := bstep (se 1 (by rfl) ⟨1495475, by rfl⟩ : syracuseStep 1993967 = 2990951) B2990951
theorem B48427561 : Blo 884570 48427561 := bstep (se 2 (by rfl) ⟨18160335, by rfl⟩ : syracuseStep 48427561 = 36320671) B36320671
theorem B17003195 : Blo 884570 17003195 := bstep (se 1 (by rfl) ⟨12752396, by rfl⟩ : syracuseStep 17003195 = 25504793) B25504793
theorem B69892105 : Blo 884570 69892105 := bstep (se 2 (by rfl) ⟨26209539, by rfl⟩ : syracuseStep 69892105 = 52419079) B52419079
theorem B258280325 : Blo 884570 258280325 := bstep (se 4 (by rfl) ⟨24213780, by rfl⟩ : syracuseStep 258280325 = 48427561) B48427561
theorem B1683497 : Blo 884570 1683497 := bstep (se 2 (by rfl) ⟨631311, by rfl⟩ : syracuseStep 1683497 = 1262623) B1262623
theorem B2997053 : Blo 884570 2997053 := bstep (se 3 (by rfl) ⟨561947, by rfl⟩ : syracuseStep 2997053 = 1123895) B1123895
theorem B12108325 : Blo 884570 12108325 := bstep (se 4 (by rfl) ⟨1135155, by rfl⟩ : syracuseStep 12108325 = 2270311) B2270311
theorem B1329311 : Blo 884570 1329311 := bstep (se 1 (by rfl) ⟨996983, by rfl⟩ : syracuseStep 1329311 = 1993967) B1993967
theorem B93189473 : Blo 884570 93189473 := bstep (se 2 (by rfl) ⟨34946052, by rfl⟩ : syracuseStep 93189473 = 69892105) B69892105
theorem B11335463 : Blo 884570 11335463 := bstep (se 1 (by rfl) ⟨8501597, by rfl⟩ : syracuseStep 11335463 = 17003195) B17003195
theorem B886207 : Blo 884570 886207 := bstep (se 1 (by rfl) ⟨664655, by rfl⟩ : syracuseStep 886207 = 1329311) B1329311
theorem B1122331 : Blo 884570 1122331 := bstep (se 1 (by rfl) ⟨841748, by rfl⟩ : syracuseStep 1122331 = 1683497) B1683497
theorem B7556975 : Blo 884570 7556975 := bstep (se 1 (by rfl) ⟨5667731, by rfl⟩ : syracuseStep 7556975 = 11335463) B11335463
theorem B16144433 : Blo 884570 16144433 := bstep (se 2 (by rfl) ⟨6054162, by rfl⟩ : syracuseStep 16144433 = 12108325) B12108325
theorem B172186883 : Blo 884570 172186883 := bstep (se 1 (by rfl) ⟨129140162, by rfl⟩ : syracuseStep 172186883 = 258280325) B258280325
theorem B62126315 : Blo 884570 62126315 := bstep (se 1 (by rfl) ⟨46594736, by rfl⟩ : syracuseStep 62126315 = 93189473) B93189473
theorem B1998035 : Blo 884570 1998035 := bstep (se 1 (by rfl) ⟨1498526, by rfl⟩ : syracuseStep 1998035 = 2997053) B2997053
theorem B114791255 : Blo 884570 114791255 := bstep (se 1 (by rfl) ⟨86093441, by rfl⟩ : syracuseStep 114791255 = 172186883) B172186883
theorem B10762955 : Blo 884570 10762955 := bstep (se 1 (by rfl) ⟨8072216, by rfl⟩ : syracuseStep 10762955 = 16144433) B16144433
theorem B1332023 : Blo 884570 1332023 := bstep (se 1 (by rfl) ⟨999017, by rfl⟩ : syracuseStep 1332023 = 1998035) B1998035
theorem B1496441 : Blo 884570 1496441 := bstep (se 2 (by rfl) ⟨561165, by rfl⟩ : syracuseStep 1496441 = 1122331) B1122331
theorem B5037983 : Blo 884570 5037983 := bstep (se 1 (by rfl) ⟨3778487, by rfl⟩ : syracuseStep 5037983 = 7556975) B7556975
theorem B41417543 : Blo 884570 41417543 := bstep (se 1 (by rfl) ⟨31063157, by rfl⟩ : syracuseStep 41417543 = 62126315) B62126315
theorem B888015 : Blo 884570 888015 := bstep (se 1 (by rfl) ⟨666011, by rfl⟩ : syracuseStep 888015 = 1332023) B1332023
theorem B76527503 : Blo 884570 76527503 := bstep (se 1 (by rfl) ⟨57395627, by rfl⟩ : syracuseStep 76527503 = 114791255) B114791255
theorem B997627 : Blo 884570 997627 := bstep (se 1 (by rfl) ⟨748220, by rfl⟩ : syracuseStep 997627 = 1496441) B1496441
theorem B3358655 : Blo 884570 3358655 := bstep (se 1 (by rfl) ⟨2518991, by rfl⟩ : syracuseStep 3358655 = 5037983) B5037983
theorem B27611695 : Blo 884570 27611695 := bstep (se 1 (by rfl) ⟨20708771, by rfl⟩ : syracuseStep 27611695 = 41417543) B41417543
theorem B7175303 : Blo 884570 7175303 := bstep (se 1 (by rfl) ⟨5381477, by rfl⟩ : syracuseStep 7175303 = 10762955) B10762955
theorem B2239103 : Blo 884570 2239103 := bstep (se 1 (by rfl) ⟨1679327, by rfl⟩ : syracuseStep 2239103 = 3358655) B3358655
theorem B36815593 : Blo 884570 36815593 := bstep (se 2 (by rfl) ⟨13805847, by rfl⟩ : syracuseStep 36815593 = 27611695) B27611695
theorem B1330169 : Blo 884570 1330169 := bstep (se 2 (by rfl) ⟨498813, by rfl⟩ : syracuseStep 1330169 = 997627) B997627
theorem B51018335 : Blo 884570 51018335 := bstep (se 1 (by rfl) ⟨38263751, by rfl⟩ : syracuseStep 51018335 = 76527503) B76527503
theorem B4783535 : Blo 884570 4783535 := bstep (se 1 (by rfl) ⟨3587651, by rfl⟩ : syracuseStep 4783535 = 7175303) B7175303
theorem B49087457 : Blo 884570 49087457 := bstep (se 2 (by rfl) ⟨18407796, by rfl⟩ : syracuseStep 49087457 = 36815593) B36815593
theorem B886779 : Blo 884570 886779 := bstep (se 1 (by rfl) ⟨665084, by rfl⟩ : syracuseStep 886779 = 1330169) B1330169
theorem B3189023 : Blo 884570 3189023 := bstep (se 1 (by rfl) ⟨2391767, by rfl⟩ : syracuseStep 3189023 = 4783535) B4783535
theorem B1492735 : Blo 884570 1492735 := bstep (se 1 (by rfl) ⟨1119551, by rfl⟩ : syracuseStep 1492735 = 2239103) B2239103
theorem B34012223 : Blo 884570 34012223 := bstep (se 1 (by rfl) ⟨25509167, by rfl⟩ : syracuseStep 34012223 = 51018335) B51018335
theorem B32724971 : Blo 884570 32724971 := bstep (se 1 (by rfl) ⟨24543728, by rfl⟩ : syracuseStep 32724971 = 49087457) B49087457
theorem B1990313 : Blo 884570 1990313 := bstep (se 2 (by rfl) ⟨746367, by rfl⟩ : syracuseStep 1990313 = 1492735) B1492735
theorem B2126015 : Blo 884570 2126015 := bstep (se 1 (by rfl) ⟨1594511, by rfl⟩ : syracuseStep 2126015 = 3189023) B3189023
theorem B22674815 : Blo 884570 22674815 := bstep (se 1 (by rfl) ⟨17006111, by rfl⟩ : syracuseStep 22674815 = 34012223) B34012223
theorem B1417343 : Blo 884570 1417343 := bstep (se 1 (by rfl) ⟨1063007, by rfl⟩ : syracuseStep 1417343 = 2126015) B2126015
theorem B15116543 : Blo 884570 15116543 := bstep (se 1 (by rfl) ⟨11337407, by rfl⟩ : syracuseStep 15116543 = 22674815) B22674815
theorem B1326875 : Blo 884570 1326875 := bstep (se 1 (by rfl) ⟨995156, by rfl⟩ : syracuseStep 1326875 = 1990313) B1990313
theorem B21816647 : Blo 884570 21816647 := bstep (se 1 (by rfl) ⟨16362485, by rfl⟩ : syracuseStep 21816647 = 32724971) B32724971
theorem B3779581 : Blo 884570 3779581 := bstep (se 3 (by rfl) ⟨708671, by rfl⟩ : syracuseStep 3779581 = 1417343) B1417343
theorem B10077695 : Blo 884570 10077695 := bstep (se 1 (by rfl) ⟨7558271, by rfl⟩ : syracuseStep 10077695 = 15116543) B15116543
theorem B14544431 : Blo 884570 14544431 := bstep (se 1 (by rfl) ⟨10908323, by rfl⟩ : syracuseStep 14544431 = 21816647) B21816647
theorem B884583 : Blo 884570 884583 := bstep (se 1 (by rfl) ⟨663437, by rfl⟩ : syracuseStep 884583 = 1326875) B1326875
theorem B6718463 : Blo 884570 6718463 := bstep (se 1 (by rfl) ⟨5038847, by rfl⟩ : syracuseStep 6718463 = 10077695) B10077695
theorem B5039441 : Blo 884570 5039441 := bstep (se 2 (by rfl) ⟨1889790, by rfl⟩ : syracuseStep 5039441 = 3779581) B3779581
theorem B9696287 : Blo 884570 9696287 := bstep (se 1 (by rfl) ⟨7272215, by rfl⟩ : syracuseStep 9696287 = 14544431) B14544431
theorem B25856765 : Blo 884570 25856765 := bstep (se 3 (by rfl) ⟨4848143, by rfl⟩ : syracuseStep 25856765 = 9696287) B9696287
theorem B3359627 : Blo 884570 3359627 := bstep (se 1 (by rfl) ⟨2519720, by rfl⟩ : syracuseStep 3359627 = 5039441) B5039441
theorem B4478975 : Blo 884570 4478975 := bstep (se 1 (by rfl) ⟨3359231, by rfl⟩ : syracuseStep 4478975 = 6718463) B6718463
theorem B17237843 : Blo 884570 17237843 := bstep (se 1 (by rfl) ⟨12928382, by rfl⟩ : syracuseStep 17237843 = 25856765) B25856765
theorem B2985983 : Blo 884570 2985983 := bstep (se 1 (by rfl) ⟨2239487, by rfl⟩ : syracuseStep 2985983 = 4478975) B4478975
theorem B2239751 : Blo 884570 2239751 := bstep (se 1 (by rfl) ⟨1679813, by rfl⟩ : syracuseStep 2239751 = 3359627) B3359627
theorem B1493167 : Blo 884570 1493167 := bstep (se 1 (by rfl) ⟨1119875, by rfl⟩ : syracuseStep 1493167 = 2239751) B2239751
theorem B11491895 : Blo 884570 11491895 := bstep (se 1 (by rfl) ⟨8618921, by rfl⟩ : syracuseStep 11491895 = 17237843) B17237843
theorem B1990655 : Blo 884570 1990655 := bstep (se 1 (by rfl) ⟨1492991, by rfl⟩ : syracuseStep 1990655 = 2985983) B2985983
theorem B1327103 : Blo 884570 1327103 := bstep (se 1 (by rfl) ⟨995327, by rfl⟩ : syracuseStep 1327103 = 1990655) B1990655
theorem B1990889 : Blo 884570 1990889 := bstep (se 2 (by rfl) ⟨746583, by rfl⟩ : syracuseStep 1990889 = 1493167) B1493167
theorem B7661263 : Blo 884570 7661263 := bstep (se 1 (by rfl) ⟨5745947, by rfl⟩ : syracuseStep 7661263 = 11491895) B11491895
theorem B1327259 : Blo 884570 1327259 := bstep (se 1 (by rfl) ⟨995444, by rfl⟩ : syracuseStep 1327259 = 1990889) B1990889
theorem B10215017 : Blo 884570 10215017 := bstep (se 2 (by rfl) ⟨3830631, by rfl⟩ : syracuseStep 10215017 = 7661263) B7661263
theorem B884735 : Blo 884570 884735 := bstep (se 1 (by rfl) ⟨663551, by rfl⟩ : syracuseStep 884735 = 1327103) B1327103
theorem B884839 : Blo 884570 884839 := bstep (se 1 (by rfl) ⟨663629, by rfl⟩ : syracuseStep 884839 = 1327259) B1327259
theorem B6810011 : Blo 884570 6810011 := bstep (se 1 (by rfl) ⟨5107508, by rfl⟩ : syracuseStep 6810011 = 10215017) B10215017
theorem B4540007 : Blo 884570 4540007 := bstep (se 1 (by rfl) ⟨3405005, by rfl⟩ : syracuseStep 4540007 = 6810011) B6810011
theorem B12106685 : Blo 884570 12106685 := bstep (se 3 (by rfl) ⟨2270003, by rfl⟩ : syracuseStep 12106685 = 4540007) B4540007
theorem B8071123 : Blo 884570 8071123 := bstep (se 1 (by rfl) ⟨6053342, by rfl⟩ : syracuseStep 8071123 = 12106685) B12106685
theorem B10761497 : Blo 884570 10761497 := bstep (se 2 (by rfl) ⟨4035561, by rfl⟩ : syracuseStep 10761497 = 8071123) B8071123
theorem B7174331 : Blo 884570 7174331 := bstep (se 1 (by rfl) ⟨5380748, by rfl⟩ : syracuseStep 7174331 = 10761497) B10761497
theorem B4782887 : Blo 884570 4782887 := bstep (se 1 (by rfl) ⟨3587165, by rfl⟩ : syracuseStep 4782887 = 7174331) B7174331
theorem B3188591 : Blo 884570 3188591 := bstep (se 1 (by rfl) ⟨2391443, by rfl⟩ : syracuseStep 3188591 = 4782887) B4782887
theorem B2125727 : Blo 884570 2125727 := bstep (se 1 (by rfl) ⟨1594295, by rfl⟩ : syracuseStep 2125727 = 3188591) B3188591
theorem B1417151 : Blo 884570 1417151 := bstep (se 1 (by rfl) ⟨1062863, by rfl⟩ : syracuseStep 1417151 = 2125727) B2125727
theorem B944767 : Blo 884570 944767 := bstep (se 1 (by rfl) ⟨708575, by rfl⟩ : syracuseStep 944767 = 1417151) B1417151
theorem B5038757 : Blo 884570 5038757 := bstep (se 4 (by rfl) ⟨472383, by rfl⟩ : syracuseStep 5038757 = 944767) B944767
theorem B3359171 : Blo 884570 3359171 := bstep (se 1 (by rfl) ⟨2519378, by rfl⟩ : syracuseStep 3359171 = 5038757) B5038757
theorem B2239447 : Blo 884570 2239447 := bstep (se 1 (by rfl) ⟨1679585, by rfl⟩ : syracuseStep 2239447 = 3359171) B3359171
theorem B2985929 : Blo 884570 2985929 := bstep (se 2 (by rfl) ⟨1119723, by rfl⟩ : syracuseStep 2985929 = 2239447) B2239447
theorem B1990619 : Blo 884570 1990619 := bstep (se 1 (by rfl) ⟨1492964, by rfl⟩ : syracuseStep 1990619 = 2985929) B2985929
theorem B1327079 : Blo 884570 1327079 := bstep (se 1 (by rfl) ⟨995309, by rfl⟩ : syracuseStep 1327079 = 1990619) B1990619
theorem B884719 : Blo 884570 884719 := bstep (se 1 (by rfl) ⟨663539, by rfl⟩ : syracuseStep 884719 = 1327079) B1327079

theorem C0 (j : ℕ) (h1 : 221142 ≤ j) (h2 : j ≤ 221841) : Blo 884570 (4 * j + 3) := by
  interval_cases j
  · exact B884571
  · exact B884575
  · exact B884579
  · exact B884583
  · exact B884587
  · exact B884591
  · exact B884595
  · exact B884599
  · exact B884603
  · exact B884607
  · exact B884611
  · exact B884615
  · exact B884619
  · exact B884623
  · exact B884627
  · exact B884631
  · exact B884635
  · exact B884639
  · exact B884643
  · exact B884647
  · exact B884651
  · exact B884655
  · exact B884659
  · exact B884663
  · exact B884667
  · exact B884671
  · exact B884675
  · exact B884679
  · exact B884683
  · exact B884687
  · exact B884691
  · exact B884695
  · exact B884699
  · exact B884703
  · exact B884707
  · exact B884711
  · exact B884715
  · exact B884719
  · exact B884723
  · exact B884727
  · exact B884731
  · exact B884735
  · exact B884739
  · exact B884743
  · exact B884747
  · exact B884751
  · exact B884755
  · exact B884759
  · exact B884763
  · exact B884767
  · exact B884771
  · exact B884775
  · exact B884779
  · exact B884783
  · exact B884787
  · exact B884791
  · exact B884795
  · exact B884799
  · exact B884803
  · exact B884807
  · exact B884811
  · exact B884815
  · exact B884819
  · exact B884823
  · exact B884827
  · exact B884831
  · exact B884835
  · exact B884839
  · exact B884843
  · exact B884847
  · exact B884851
  · exact B884855
  · exact B884859
  · exact B884863
  · exact B884867
  · exact B884871
  · exact B884875
  · exact B884879
  · exact B884883
  · exact B884887
  · exact B884891
  · exact B884895
  · exact B884899
  · exact B884903
  · exact B884907
  · exact B884911
  · exact B884915
  · exact B884919
  · exact B884923
  · exact B884927
  · exact B884931
  · exact B884935
  · exact B884939
  · exact B884943
  · exact B884947
  · exact B884951
  · exact B884955
  · exact B884959
  · exact B884963
  · exact B884967
  · exact B884971
  · exact B884975
  · exact B884979
  · exact B884983
  · exact B884987
  · exact B884991
  · exact B884995
  · exact B884999
  · exact B885003
  · exact B885007
  · exact B885011
  · exact B885015
  · exact B885019
  · exact B885023
  · exact B885027
  · exact B885031
  · exact B885035
  · exact B885039
  · exact B885043
  · exact B885047
  · exact B885051
  · exact B885055
  · exact B885059
  · exact B885063
  · exact B885067
  · exact B885071
  · exact B885075
  · exact B885079
  · exact B885083
  · exact B885087
  · exact B885091
  · exact B885095
  · exact B885099
  · exact B885103
  · exact B885107
  · exact B885111
  · exact B885115
  · exact B885119
  · exact B885123
  · exact B885127
  · exact B885131
  · exact B885135
  · exact B885139
  · exact B885143
  · exact B885147
  · exact B885151
  · exact B885155
  · exact B885159
  · exact B885163
  · exact B885167
  · exact B885171
  · exact B885175
  · exact B885179
  · exact B885183
  · exact B885187
  · exact B885191
  · exact B885195
  · exact B885199
  · exact B885203
  · exact B885207
  · exact B885211
  · exact B885215
  · exact B885219
  · exact B885223
  · exact B885227
  · exact B885231
  · exact B885235
  · exact B885239
  · exact B885243
  · exact B885247
  · exact B885251
  · exact B885255
  · exact B885259
  · exact B885263
  · exact B885267
  · exact B885271
  · exact B885275
  · exact B885279
  · exact B885283
  · exact B885287
  · exact B885291
  · exact B885295
  · exact B885299
  · exact B885303
  · exact B885307
  · exact B885311
  · exact B885315
  · exact B885319
  · exact B885323
  · exact B885327
  · exact B885331
  · exact B885335
  · exact B885339
  · exact B885343
  · exact B885347
  · exact B885351
  · exact B885355
  · exact B885359
  · exact B885363
  · exact B885367
  · exact B885371
  · exact B885375
  · exact B885379
  · exact B885383
  · exact B885387
  · exact B885391
  · exact B885395
  · exact B885399
  · exact B885403
  · exact B885407
  · exact B885411
  · exact B885415
  · exact B885419
  · exact B885423
  · exact B885427
  · exact B885431
  · exact B885435
  · exact B885439
  · exact B885443
  · exact B885447
  · exact B885451
  · exact B885455
  · exact B885459
  · exact B885463
  · exact B885467
  · exact B885471
  · exact B885475
  · exact B885479
  · exact B885483
  · exact B885487
  · exact B885491
  · exact B885495
  · exact B885499
  · exact B885503
  · exact B885507
  · exact B885511
  · exact B885515
  · exact B885519
  · exact B885523
  · exact B885527
  · exact B885531
  · exact B885535
  · exact B885539
  · exact B885543
  · exact B885547
  · exact B885551
  · exact B885555
  · exact B885559
  · exact B885563
  · exact B885567
  · exact B885571
  · exact B885575
  · exact B885579
  · exact B885583
  · exact B885587
  · exact B885591
  · exact B885595
  · exact B885599
  · exact B885603
  · exact B885607
  · exact B885611
  · exact B885615
  · exact B885619
  · exact B885623
  · exact B885627
  · exact B885631
  · exact B885635
  · exact B885639
  · exact B885643
  · exact B885647
  · exact B885651
  · exact B885655
  · exact B885659
  · exact B885663
  · exact B885667
  · exact B885671
  · exact B885675
  · exact B885679
  · exact B885683
  · exact B885687
  · exact B885691
  · exact B885695
  · exact B885699
  · exact B885703
  · exact B885707
  · exact B885711
  · exact B885715
  · exact B885719
  · exact B885723
  · exact B885727
  · exact B885731
  · exact B885735
  · exact B885739
  · exact B885743
  · exact B885747
  · exact B885751
  · exact B885755
  · exact B885759
  · exact B885763
  · exact B885767
  · exact B885771
  · exact B885775
  · exact B885779
  · exact B885783
  · exact B885787
  · exact B885791
  · exact B885795
  · exact B885799
  · exact B885803
  · exact B885807
  · exact B885811
  · exact B885815
  · exact B885819
  · exact B885823
  · exact B885827
  · exact B885831
  · exact B885835
  · exact B885839
  · exact B885843
  · exact B885847
  · exact B885851
  · exact B885855
  · exact B885859
  · exact B885863
  · exact B885867
  · exact B885871
  · exact B885875
  · exact B885879
  · exact B885883
  · exact B885887
  · exact B885891
  · exact B885895
  · exact B885899
  · exact B885903
  · exact B885907
  · exact B885911
  · exact B885915
  · exact B885919
  · exact B885923
  · exact B885927
  · exact B885931
  · exact B885935
  · exact B885939
  · exact B885943
  · exact B885947
  · exact B885951
  · exact B885955
  · exact B885959
  · exact B885963
  · exact B885967
  · exact B885971
  · exact B885975
  · exact B885979
  · exact B885983
  · exact B885987
  · exact B885991
  · exact B885995
  · exact B885999
  · exact B886003
  · exact B886007
  · exact B886011
  · exact B886015
  · exact B886019
  · exact B886023
  · exact B886027
  · exact B886031
  · exact B886035
  · exact B886039
  · exact B886043
  · exact B886047
  · exact B886051
  · exact B886055
  · exact B886059
  · exact B886063
  · exact B886067
  · exact B886071
  · exact B886075
  · exact B886079
  · exact B886083
  · exact B886087
  · exact B886091
  · exact B886095
  · exact B886099
  · exact B886103
  · exact B886107
  · exact B886111
  · exact B886115
  · exact B886119
  · exact B886123
  · exact B886127
  · exact B886131
  · exact B886135
  · exact B886139
  · exact B886143
  · exact B886147
  · exact B886151
  · exact B886155
  · exact B886159
  · exact B886163
  · exact B886167
  · exact B886171
  · exact B886175
  · exact B886179
  · exact B886183
  · exact B886187
  · exact B886191
  · exact B886195
  · exact B886199
  · exact B886203
  · exact B886207
  · exact B886211
  · exact B886215
  · exact B886219
  · exact B886223
  · exact B886227
  · exact B886231
  · exact B886235
  · exact B886239
  · exact B886243
  · exact B886247
  · exact B886251
  · exact B886255
  · exact B886259
  · exact B886263
  · exact B886267
  · exact B886271
  · exact B886275
  · exact B886279
  · exact B886283
  · exact B886287
  · exact B886291
  · exact B886295
  · exact B886299
  · exact B886303
  · exact B886307
  · exact B886311
  · exact B886315
  · exact B886319
  · exact B886323
  · exact B886327
  · exact B886331
  · exact B886335
  · exact B886339
  · exact B886343
  · exact B886347
  · exact B886351
  · exact B886355
  · exact B886359
  · exact B886363
  · exact B886367
  · exact B886371
  · exact B886375
  · exact B886379
  · exact B886383
  · exact B886387
  · exact B886391
  · exact B886395
  · exact B886399
  · exact B886403
  · exact B886407
  · exact B886411
  · exact B886415
  · exact B886419
  · exact B886423
  · exact B886427
  · exact B886431
  · exact B886435
  · exact B886439
  · exact B886443
  · exact B886447
  · exact B886451
  · exact B886455
  · exact B886459
  · exact B886463
  · exact B886467
  · exact B886471
  · exact B886475
  · exact B886479
  · exact B886483
  · exact B886487
  · exact B886491
  · exact B886495
  · exact B886499
  · exact B886503
  · exact B886507
  · exact B886511
  · exact B886515
  · exact B886519
  · exact B886523
  · exact B886527
  · exact B886531
  · exact B886535
  · exact B886539
  · exact B886543
  · exact B886547
  · exact B886551
  · exact B886555
  · exact B886559
  · exact B886563
  · exact B886567
  · exact B886571
  · exact B886575
  · exact B886579
  · exact B886583
  · exact B886587
  · exact B886591
  · exact B886595
  · exact B886599
  · exact B886603
  · exact B886607
  · exact B886611
  · exact B886615
  · exact B886619
  · exact B886623
  · exact B886627
  · exact B886631
  · exact B886635
  · exact B886639
  · exact B886643
  · exact B886647
  · exact B886651
  · exact B886655
  · exact B886659
  · exact B886663
  · exact B886667
  · exact B886671
  · exact B886675
  · exact B886679
  · exact B886683
  · exact B886687
  · exact B886691
  · exact B886695
  · exact B886699
  · exact B886703
  · exact B886707
  · exact B886711
  · exact B886715
  · exact B886719
  · exact B886723
  · exact B886727
  · exact B886731
  · exact B886735
  · exact B886739
  · exact B886743
  · exact B886747
  · exact B886751
  · exact B886755
  · exact B886759
  · exact B886763
  · exact B886767
  · exact B886771
  · exact B886775
  · exact B886779
  · exact B886783
  · exact B886787
  · exact B886791
  · exact B886795
  · exact B886799
  · exact B886803
  · exact B886807
  · exact B886811
  · exact B886815
  · exact B886819
  · exact B886823
  · exact B886827
  · exact B886831
  · exact B886835
  · exact B886839
  · exact B886843
  · exact B886847
  · exact B886851
  · exact B886855
  · exact B886859
  · exact B886863
  · exact B886867
  · exact B886871
  · exact B886875
  · exact B886879
  · exact B886883
  · exact B886887
  · exact B886891
  · exact B886895
  · exact B886899
  · exact B886903
  · exact B886907
  · exact B886911
  · exact B886915
  · exact B886919
  · exact B886923
  · exact B886927
  · exact B886931
  · exact B886935
  · exact B886939
  · exact B886943
  · exact B886947
  · exact B886951
  · exact B886955
  · exact B886959
  · exact B886963
  · exact B886967
  · exact B886971
  · exact B886975
  · exact B886979
  · exact B886983
  · exact B886987
  · exact B886991
  · exact B886995
  · exact B886999
  · exact B887003
  · exact B887007
  · exact B887011
  · exact B887015
  · exact B887019
  · exact B887023
  · exact B887027
  · exact B887031
  · exact B887035
  · exact B887039
  · exact B887043
  · exact B887047
  · exact B887051
  · exact B887055
  · exact B887059
  · exact B887063
  · exact B887067
  · exact B887071
  · exact B887075
  · exact B887079
  · exact B887083
  · exact B887087
  · exact B887091
  · exact B887095
  · exact B887099
  · exact B887103
  · exact B887107
  · exact B887111
  · exact B887115
  · exact B887119
  · exact B887123
  · exact B887127
  · exact B887131
  · exact B887135
  · exact B887139
  · exact B887143
  · exact B887147
  · exact B887151
  · exact B887155
  · exact B887159
  · exact B887163
  · exact B887167
  · exact B887171
  · exact B887175
  · exact B887179
  · exact B887183
  · exact B887187
  · exact B887191
  · exact B887195
  · exact B887199
  · exact B887203
  · exact B887207
  · exact B887211
  · exact B887215
  · exact B887219
  · exact B887223
  · exact B887227
  · exact B887231
  · exact B887235
  · exact B887239
  · exact B887243
  · exact B887247
  · exact B887251
  · exact B887255
  · exact B887259
  · exact B887263
  · exact B887267
  · exact B887271
  · exact B887275
  · exact B887279
  · exact B887283
  · exact B887287
  · exact B887291
  · exact B887295
  · exact B887299
  · exact B887303
  · exact B887307
  · exact B887311
  · exact B887315
  · exact B887319
  · exact B887323
  · exact B887327
  · exact B887331
  · exact B887335
  · exact B887339
  · exact B887343
  · exact B887347
  · exact B887351
  · exact B887355
  · exact B887359
  · exact B887363
  · exact B887367

theorem C1 (j : ℕ) (h1 : 221842 ≤ j) (h2 : j ≤ 222141) : Blo 884570 (4 * j + 3) := by
  interval_cases j
  · exact B887371
  · exact B887375
  · exact B887379
  · exact B887383
  · exact B887387
  · exact B887391
  · exact B887395
  · exact B887399
  · exact B887403
  · exact B887407
  · exact B887411
  · exact B887415
  · exact B887419
  · exact B887423
  · exact B887427
  · exact B887431
  · exact B887435
  · exact B887439
  · exact B887443
  · exact B887447
  · exact B887451
  · exact B887455
  · exact B887459
  · exact B887463
  · exact B887467
  · exact B887471
  · exact B887475
  · exact B887479
  · exact B887483
  · exact B887487
  · exact B887491
  · exact B887495
  · exact B887499
  · exact B887503
  · exact B887507
  · exact B887511
  · exact B887515
  · exact B887519
  · exact B887523
  · exact B887527
  · exact B887531
  · exact B887535
  · exact B887539
  · exact B887543
  · exact B887547
  · exact B887551
  · exact B887555
  · exact B887559
  · exact B887563
  · exact B887567
  · exact B887571
  · exact B887575
  · exact B887579
  · exact B887583
  · exact B887587
  · exact B887591
  · exact B887595
  · exact B887599
  · exact B887603
  · exact B887607
  · exact B887611
  · exact B887615
  · exact B887619
  · exact B887623
  · exact B887627
  · exact B887631
  · exact B887635
  · exact B887639
  · exact B887643
  · exact B887647
  · exact B887651
  · exact B887655
  · exact B887659
  · exact B887663
  · exact B887667
  · exact B887671
  · exact B887675
  · exact B887679
  · exact B887683
  · exact B887687
  · exact B887691
  · exact B887695
  · exact B887699
  · exact B887703
  · exact B887707
  · exact B887711
  · exact B887715
  · exact B887719
  · exact B887723
  · exact B887727
  · exact B887731
  · exact B887735
  · exact B887739
  · exact B887743
  · exact B887747
  · exact B887751
  · exact B887755
  · exact B887759
  · exact B887763
  · exact B887767
  · exact B887771
  · exact B887775
  · exact B887779
  · exact B887783
  · exact B887787
  · exact B887791
  · exact B887795
  · exact B887799
  · exact B887803
  · exact B887807
  · exact B887811
  · exact B887815
  · exact B887819
  · exact B887823
  · exact B887827
  · exact B887831
  · exact B887835
  · exact B887839
  · exact B887843
  · exact B887847
  · exact B887851
  · exact B887855
  · exact B887859
  · exact B887863
  · exact B887867
  · exact B887871
  · exact B887875
  · exact B887879
  · exact B887883
  · exact B887887
  · exact B887891
  · exact B887895
  · exact B887899
  · exact B887903
  · exact B887907
  · exact B887911
  · exact B887915
  · exact B887919
  · exact B887923
  · exact B887927
  · exact B887931
  · exact B887935
  · exact B887939
  · exact B887943
  · exact B887947
  · exact B887951
  · exact B887955
  · exact B887959
  · exact B887963
  · exact B887967
  · exact B887971
  · exact B887975
  · exact B887979
  · exact B887983
  · exact B887987
  · exact B887991
  · exact B887995
  · exact B887999
  · exact B888003
  · exact B888007
  · exact B888011
  · exact B888015
  · exact B888019
  · exact B888023
  · exact B888027
  · exact B888031
  · exact B888035
  · exact B888039
  · exact B888043
  · exact B888047
  · exact B888051
  · exact B888055
  · exact B888059
  · exact B888063
  · exact B888067
  · exact B888071
  · exact B888075
  · exact B888079
  · exact B888083
  · exact B888087
  · exact B888091
  · exact B888095
  · exact B888099
  · exact B888103
  · exact B888107
  · exact B888111
  · exact B888115
  · exact B888119
  · exact B888123
  · exact B888127
  · exact B888131
  · exact B888135
  · exact B888139
  · exact B888143
  · exact B888147
  · exact B888151
  · exact B888155
  · exact B888159
  · exact B888163
  · exact B888167
  · exact B888171
  · exact B888175
  · exact B888179
  · exact B888183
  · exact B888187
  · exact B888191
  · exact B888195
  · exact B888199
  · exact B888203
  · exact B888207
  · exact B888211
  · exact B888215
  · exact B888219
  · exact B888223
  · exact B888227
  · exact B888231
  · exact B888235
  · exact B888239
  · exact B888243
  · exact B888247
  · exact B888251
  · exact B888255
  · exact B888259
  · exact B888263
  · exact B888267
  · exact B888271
  · exact B888275
  · exact B888279
  · exact B888283
  · exact B888287
  · exact B888291
  · exact B888295
  · exact B888299
  · exact B888303
  · exact B888307
  · exact B888311
  · exact B888315
  · exact B888319
  · exact B888323
  · exact B888327
  · exact B888331
  · exact B888335
  · exact B888339
  · exact B888343
  · exact B888347
  · exact B888351
  · exact B888355
  · exact B888359
  · exact B888363
  · exact B888367
  · exact B888371
  · exact B888375
  · exact B888379
  · exact B888383
  · exact B888387
  · exact B888391
  · exact B888395
  · exact B888399
  · exact B888403
  · exact B888407
  · exact B888411
  · exact B888415
  · exact B888419
  · exact B888423
  · exact B888427
  · exact B888431
  · exact B888435
  · exact B888439
  · exact B888443
  · exact B888447
  · exact B888451
  · exact B888455
  · exact B888459
  · exact B888463
  · exact B888467
  · exact B888471
  · exact B888475
  · exact B888479
  · exact B888483
  · exact B888487
  · exact B888491
  · exact B888495
  · exact B888499
  · exact B888503
  · exact B888507
  · exact B888511
  · exact B888515
  · exact B888519
  · exact B888523
  · exact B888527
  · exact B888531
  · exact B888535
  · exact B888539
  · exact B888543
  · exact B888547
  · exact B888551
  · exact B888555
  · exact B888559
  · exact B888563
  · exact B888567

theorem solution (m : ℕ) (hlo : 884570 ≤ m) (hhi : m ≤ 888570) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 221142 ≤ j := by omega
    have hj2 : j ≤ 222141 := by omega
    have hb : Blo 884570 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 221842 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
