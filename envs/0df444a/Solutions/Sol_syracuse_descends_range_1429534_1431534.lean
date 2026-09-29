-- Prove2me | solution 1 for syracuse_descends_range_1429534_1431534
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:41:54.402093+00:00
-- url     : https://prove2.me/submissions/cb7e6413-a01b-43ab-9e3d-bea61e65587c

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


theorem B3219461 : Blo 1429534 3219461 := bbase (se 4 (by rfl) ⟨301824, by rfl⟩ : syracuseStep 3219461 = 603649) (by norm_num)
theorem B1810441 : Blo 1429534 1810441 := bbase (se 2 (by rfl) ⟨678915, by rfl⟩ : syracuseStep 1810441 = 1357831) (by norm_num)
theorem B2146325 : Blo 1429534 2146325 := bbase (se 6 (by rfl) ⟨50304, by rfl⟩ : syracuseStep 2146325 = 100609) (by norm_num)
theorem B2146349 : Blo 1429534 2146349 := bbase (se 3 (by rfl) ⟨402440, by rfl⟩ : syracuseStep 2146349 = 804881) (by norm_num)
theorem B8257589 : Blo 1429534 8257589 := bbase (se 5 (by rfl) ⟨387074, by rfl⟩ : syracuseStep 8257589 = 774149) (by norm_num)
theorem B3620933 : Blo 1429534 3620933 := bbase (se 4 (by rfl) ⟨339462, by rfl⟩ : syracuseStep 3620933 = 678925) (by norm_num)
theorem B2146373 : Blo 1429534 2146373 := bbase (se 4 (by rfl) ⟨201222, by rfl⟩ : syracuseStep 2146373 = 402445) (by norm_num)
theorem B3219533 : Blo 1429534 3219533 := bbase (se 3 (by rfl) ⟨603662, by rfl⟩ : syracuseStep 3219533 = 1207325) (by norm_num)
theorem B2146397 : Blo 1429534 2146397 := bbase (se 3 (by rfl) ⟨402449, by rfl⟩ : syracuseStep 2146397 = 804899) (by norm_num)
theorem B6701173 : Blo 1429534 6701173 := bbase (se 5 (by rfl) ⟨314117, by rfl⟩ : syracuseStep 6701173 = 628235) (by norm_num)
theorem B2146421 : Blo 1429534 2146421 := bbase (se 5 (by rfl) ⟨100613, by rfl⟩ : syracuseStep 2146421 = 201227) (by norm_num)
theorem B2146445 : Blo 1429534 2146445 := bbase (se 3 (by rfl) ⟨402458, by rfl⟩ : syracuseStep 2146445 = 804917) (by norm_num)
theorem B5431445 : Blo 1429534 5431445 := bbase (se 6 (by rfl) ⟨127299, by rfl⟩ : syracuseStep 5431445 = 254599) (by norm_num)
theorem B3219605 : Blo 1429534 3219605 := bbase (se 6 (by rfl) ⟨75459, by rfl⟩ : syracuseStep 3219605 = 150919) (by norm_num)
theorem B2146469 : Blo 1429534 2146469 := bbase (se 4 (by rfl) ⟨201231, by rfl⟩ : syracuseStep 2146469 = 402463) (by norm_num)
theorem B5152949 : Blo 1429534 5152949 := bbase (se 5 (by rfl) ⟨241544, by rfl⟩ : syracuseStep 5152949 = 483089) (by norm_num)
theorem B1810613 : Blo 1429534 1810613 := bbase (se 5 (by rfl) ⟨84872, by rfl⟩ : syracuseStep 1810613 = 169745) (by norm_num)
theorem B2146493 : Blo 1429534 2146493 := bbase (se 3 (by rfl) ⟨402467, by rfl⟩ : syracuseStep 2146493 = 804935) (by norm_num)
theorem B2146517 : Blo 1429534 2146517 := bbase (se 7 (by rfl) ⟨25154, by rfl⟩ : syracuseStep 2146517 = 50309) (by norm_num)
theorem B3219677 : Blo 1429534 3219677 := bbase (se 3 (by rfl) ⟨603689, by rfl⟩ : syracuseStep 3219677 = 1207379) (by norm_num)
theorem B1810669 : Blo 1429534 1810669 := bbase (se 3 (by rfl) ⟨339500, by rfl⟩ : syracuseStep 1810669 = 679001) (by norm_num)
theorem B2146541 : Blo 1429534 2146541 := bbase (se 3 (by rfl) ⟨402476, by rfl⟩ : syracuseStep 2146541 = 804953) (by norm_num)
theorem B3621125 : Blo 1429534 3621125 := bbase (se 4 (by rfl) ⟨339480, by rfl⟩ : syracuseStep 3621125 = 678961) (by norm_num)
theorem B2146565 : Blo 1429534 2146565 := bbase (se 4 (by rfl) ⟨201240, by rfl⟩ : syracuseStep 2146565 = 402481) (by norm_num)
theorem B2146589 : Blo 1429534 2146589 := bbase (se 3 (by rfl) ⟨402485, by rfl⟩ : syracuseStep 2146589 = 804971) (by norm_num)
theorem B3219749 : Blo 1429534 3219749 := bbase (se 4 (by rfl) ⟨301851, by rfl⟩ : syracuseStep 3219749 = 603703) (by norm_num)
theorem B2146613 : Blo 1429534 2146613 := bbase (se 5 (by rfl) ⟨100622, by rfl⟩ : syracuseStep 2146613 = 201245) (by norm_num)
theorem B1548601 : Blo 1429534 1548601 := bbase (se 2 (by rfl) ⟨580725, by rfl⟩ : syracuseStep 1548601 = 1161451) (by norm_num)
theorem B6111557 : Blo 1429534 6111557 := bbase (se 4 (by rfl) ⟨572958, by rfl⟩ : syracuseStep 6111557 = 1145917) (by norm_num)
theorem B1810765 : Blo 1429534 1810765 := bbase (se 3 (by rfl) ⟨339518, by rfl⟩ : syracuseStep 1810765 = 679037) (by norm_num)
theorem B2146637 : Blo 1429534 2146637 := bbase (se 3 (by rfl) ⟨402494, by rfl⟩ : syracuseStep 2146637 = 804989) (by norm_num)
theorem B2146661 : Blo 1429534 2146661 := bbase (se 4 (by rfl) ⟨201249, by rfl⟩ : syracuseStep 2146661 = 402499) (by norm_num)
theorem B3219821 : Blo 1429534 3219821 := bbase (se 3 (by rfl) ⟨603716, by rfl⟩ : syracuseStep 3219821 = 1207433) (by norm_num)
theorem B2146685 : Blo 1429534 2146685 := bbase (se 3 (by rfl) ⟨402503, by rfl⟩ : syracuseStep 2146685 = 805007) (by norm_num)
theorem B4579733 : Blo 1429534 4579733 := bbase (se 6 (by rfl) ⟨107337, by rfl⟩ : syracuseStep 4579733 = 214675) (by norm_num)
theorem B4825493 : Blo 1429534 4825493 := bbase (se 6 (by rfl) ⟨113097, by rfl⟩ : syracuseStep 4825493 = 226195) (by norm_num)
theorem B2146709 : Blo 1429534 2146709 := bbase (se 6 (by rfl) ⟨50313, by rfl⟩ : syracuseStep 2146709 = 100627) (by norm_num)
theorem B2146733 : Blo 1429534 2146733 := bbase (se 3 (by rfl) ⟨402512, by rfl⟩ : syracuseStep 2146733 = 805025) (by norm_num)
theorem B3219893 : Blo 1429534 3219893 := bbase (se 5 (by rfl) ⟨150932, by rfl⟩ : syracuseStep 3219893 = 301865) (by norm_num)
theorem B2146757 : Blo 1429534 2146757 := bbase (se 4 (by rfl) ⟨201258, by rfl⟩ : syracuseStep 2146757 = 402517) (by norm_num)
theorem B1630681 : Blo 1429534 1630681 := bbase (se 2 (by rfl) ⟨611505, by rfl⟩ : syracuseStep 1630681 = 1223011) (by norm_num)
theorem B2146781 : Blo 1429534 2146781 := bbase (se 3 (by rfl) ⟨402521, by rfl⟩ : syracuseStep 2146781 = 805043) (by norm_num)
theorem B2146805 : Blo 1429534 2146805 := bbase (se 5 (by rfl) ⟨100631, by rfl⟩ : syracuseStep 2146805 = 201263) (by norm_num)
theorem B1810937 : Blo 1429534 1810937 := bbase (se 2 (by rfl) ⟨679101, by rfl⟩ : syracuseStep 1810937 = 1358203) (by norm_num)
theorem B3219965 : Blo 1429534 3219965 := bbase (se 3 (by rfl) ⟨603743, by rfl⟩ : syracuseStep 3219965 = 1207487) (by norm_num)
theorem B2146829 : Blo 1429534 2146829 := bbase (se 3 (by rfl) ⟨402530, by rfl⟩ : syracuseStep 2146829 = 805061) (by norm_num)
theorem B2146853 : Blo 1429534 2146853 := bbase (se 4 (by rfl) ⟨201267, by rfl⟩ : syracuseStep 2146853 = 402535) (by norm_num)
theorem B1810993 : Blo 1429534 1810993 := bbase (se 2 (by rfl) ⟨679122, by rfl⟩ : syracuseStep 1810993 = 1358245) (by norm_num)
theorem B2146877 : Blo 1429534 2146877 := bbase (se 3 (by rfl) ⟨402539, by rfl⟩ : syracuseStep 2146877 = 805079) (by norm_num)
theorem B3220037 : Blo 1429534 3220037 := bbase (se 4 (by rfl) ⟨301878, by rfl⟩ : syracuseStep 3220037 = 603757) (by norm_num)
theorem B2146901 : Blo 1429534 2146901 := bbase (se 8 (by rfl) ⟨12579, by rfl⟩ : syracuseStep 2146901 = 25159) (by norm_num)
theorem B3621469 : Blo 1429534 3621469 := bbase (se 3 (by rfl) ⟨679025, by rfl⟩ : syracuseStep 3621469 = 1358051) (by norm_num)
theorem B6111845 : Blo 1429534 6111845 := bbase (se 4 (by rfl) ⟨572985, by rfl⟩ : syracuseStep 6111845 = 1145971) (by norm_num)
theorem B2146925 : Blo 1429534 2146925 := bbase (se 3 (by rfl) ⟨402548, by rfl⟩ : syracuseStep 2146925 = 805097) (by norm_num)
theorem B2146949 : Blo 1429534 2146949 := bbase (se 4 (by rfl) ⟨201276, by rfl⟩ : syracuseStep 2146949 = 402553) (by norm_num)
theorem B3220109 : Blo 1429534 3220109 := bbase (se 3 (by rfl) ⟨603770, by rfl⟩ : syracuseStep 3220109 = 1207541) (by norm_num)
theorem B1811089 : Blo 1429534 1811089 := bbase (se 2 (by rfl) ⟨679158, by rfl⟩ : syracuseStep 1811089 = 1358317) (by norm_num)
theorem B2146973 : Blo 1429534 2146973 := bbase (se 3 (by rfl) ⟨402557, by rfl⟩ : syracuseStep 2146973 = 805115) (by norm_num)
theorem B2146997 : Blo 1429534 2146997 := bbase (se 5 (by rfl) ⟨100640, by rfl⟩ : syracuseStep 2146997 = 201281) (by norm_num)
theorem B3621581 : Blo 1429534 3621581 := bbase (se 3 (by rfl) ⟨679046, by rfl⟩ : syracuseStep 3621581 = 1358093) (by norm_num)
theorem B2147021 : Blo 1429534 2147021 := bbase (se 3 (by rfl) ⟨402566, by rfl⟩ : syracuseStep 2147021 = 805133) (by norm_num)
theorem B3220181 : Blo 1429534 3220181 := bbase (se 7 (by rfl) ⟨37736, by rfl⟩ : syracuseStep 3220181 = 75473) (by norm_num)
theorem B2147045 : Blo 1429534 2147045 := bbase (se 4 (by rfl) ⟨201285, by rfl⟩ : syracuseStep 2147045 = 402571) (by norm_num)
theorem B2147069 : Blo 1429534 2147069 := bbase (se 3 (by rfl) ⟨402575, by rfl⟩ : syracuseStep 2147069 = 805151) (by norm_num)
theorem B1835789 : Blo 1429534 1835789 := bbase (se 3 (by rfl) ⟨344210, by rfl⟩ : syracuseStep 1835789 = 688421) (by norm_num)
theorem B2147093 : Blo 1429534 2147093 := bbase (se 6 (by rfl) ⟨50322, by rfl⟩ : syracuseStep 2147093 = 100645) (by norm_num)
theorem B3220253 : Blo 1429534 3220253 := bbase (se 3 (by rfl) ⟨603797, by rfl⟩ : syracuseStep 3220253 = 1207595) (by norm_num)
theorem B7242533 : Blo 1429534 7242533 := bbase (se 4 (by rfl) ⟨678987, by rfl⟩ : syracuseStep 7242533 = 1357975) (by norm_num)
theorem B2147117 : Blo 1429534 2147117 := bbase (se 3 (by rfl) ⟨402584, by rfl⟩ : syracuseStep 2147117 = 805169) (by norm_num)
theorem B1811261 : Blo 1429534 1811261 := bbase (se 3 (by rfl) ⟨339611, by rfl⟩ : syracuseStep 1811261 = 679223) (by norm_num)
theorem B4825925 : Blo 1429534 4825925 := bbase (se 4 (by rfl) ⟨452430, by rfl⟩ : syracuseStep 4825925 = 904861) (by norm_num)
theorem B2147141 : Blo 1429534 2147141 := bbase (se 4 (by rfl) ⟨201294, by rfl⟩ : syracuseStep 2147141 = 402589) (by norm_num)
theorem B2900821 : Blo 1429534 2900821 := bbase (se 9 (by rfl) ⟨8498, by rfl⟩ : syracuseStep 2900821 = 16997) (by norm_num)
theorem B2147165 : Blo 1429534 2147165 := bbase (se 3 (by rfl) ⟨402593, by rfl⟩ : syracuseStep 2147165 = 805187) (by norm_num)
theorem B3220325 : Blo 1429534 3220325 := bbase (se 4 (by rfl) ⟨301905, by rfl⟩ : syracuseStep 3220325 = 603811) (by norm_num)
theorem B1811317 : Blo 1429534 1811317 := bbase (se 5 (by rfl) ⟨84905, by rfl⟩ : syracuseStep 1811317 = 169811) (by norm_num)
theorem B2147189 : Blo 1429534 2147189 := bbase (se 5 (by rfl) ⟨100649, by rfl⟩ : syracuseStep 2147189 = 201299) (by norm_num)
theorem B3621773 : Blo 1429534 3621773 := bbase (se 3 (by rfl) ⟨679082, by rfl⟩ : syracuseStep 3621773 = 1358165) (by norm_num)
theorem B2147213 : Blo 1429534 2147213 := bbase (se 3 (by rfl) ⟨402602, by rfl⟩ : syracuseStep 2147213 = 805205) (by norm_num)
theorem B2147237 : Blo 1429534 2147237 := bbase (se 4 (by rfl) ⟨201303, by rfl⟩ : syracuseStep 2147237 = 402607) (by norm_num)
theorem B3220397 : Blo 1429534 3220397 := bbase (se 3 (by rfl) ⟨603824, by rfl⟩ : syracuseStep 3220397 = 1207649) (by norm_num)
theorem B2147261 : Blo 1429534 2147261 := bbase (se 3 (by rfl) ⟨402611, by rfl⟩ : syracuseStep 2147261 = 805223) (by norm_num)
theorem B1811413 : Blo 1429534 1811413 := bbase (se 7 (by rfl) ⟨21227, by rfl⟩ : syracuseStep 1811413 = 42455) (by norm_num)
theorem B2147285 : Blo 1429534 2147285 := bbase (se 7 (by rfl) ⟨25163, by rfl⟩ : syracuseStep 2147285 = 50327) (by norm_num)
theorem B12215285 : Blo 1429534 12215285 := bbase (se 5 (by rfl) ⟨572591, by rfl⟩ : syracuseStep 12215285 = 1145183) (by norm_num)
theorem B3220469 : Blo 1429534 3220469 := bbase (se 5 (by rfl) ⟨150959, by rfl⟩ : syracuseStep 3220469 = 301919) (by norm_num)
theorem B3220541 : Blo 1429534 3220541 := bbase (se 3 (by rfl) ⟨603851, by rfl⟩ : syracuseStep 3220541 = 1207703) (by norm_num)
theorem B1811585 : Blo 1429534 1811585 := bbase (se 2 (by rfl) ⟨679344, by rfl⟩ : syracuseStep 1811585 = 1358689) (by norm_num)
theorem B3220613 : Blo 1429534 3220613 := bbase (se 4 (by rfl) ⟨301932, by rfl⟩ : syracuseStep 3220613 = 603865) (by norm_num)
theorem B1811641 : Blo 1429534 1811641 := bbase (se 2 (by rfl) ⟨679365, by rfl⟩ : syracuseStep 1811641 = 1358731) (by norm_num)
theorem B3220685 : Blo 1429534 3220685 := bbase (se 3 (by rfl) ⟨603878, by rfl⟩ : syracuseStep 3220685 = 1207757) (by norm_num)
theorem B3622117 : Blo 1429534 3622117 := bbase (se 4 (by rfl) ⟨339573, by rfl⟩ : syracuseStep 3622117 = 679147) (by norm_num)
theorem B4826357 : Blo 1429534 4826357 := bbase (se 5 (by rfl) ⟨226235, by rfl⟩ : syracuseStep 4826357 = 452471) (by norm_num)
theorem B1934605 : Blo 1429534 1934605 := bbase (se 3 (by rfl) ⟨362738, by rfl⟩ : syracuseStep 1934605 = 725477) (by norm_num)
theorem B3220757 : Blo 1429534 3220757 := bbase (se 6 (by rfl) ⟨75486, by rfl⟩ : syracuseStep 3220757 = 150973) (by norm_num)
theorem B1811737 : Blo 1429534 1811737 := bbase (se 2 (by rfl) ⟨679401, by rfl⟩ : syracuseStep 1811737 = 1358803) (by norm_num)
theorem B5432629 : Blo 1429534 5432629 := bbase (se 5 (by rfl) ⟨254654, by rfl⟩ : syracuseStep 5432629 = 509309) (by norm_num)
theorem B3622229 : Blo 1429534 3622229 := bbase (se 12 (by rfl) ⟨1326, by rfl⟩ : syracuseStep 3622229 = 2653) (by norm_num)
theorem B6112597 : Blo 1429534 6112597 := bbase (se 12 (by rfl) ⟨2238, by rfl⟩ : syracuseStep 6112597 = 4477) (by norm_num)
theorem B2901341 : Blo 1429534 2901341 := bbase (se 3 (by rfl) ⟨544001, by rfl⟩ : syracuseStep 2901341 = 1088003) (by norm_num)
theorem B3220829 : Blo 1429534 3220829 := bbase (se 3 (by rfl) ⟨603905, by rfl⟩ : syracuseStep 3220829 = 1207811) (by norm_num)
theorem B3220901 : Blo 1429534 3220901 := bbase (se 4 (by rfl) ⟨301959, by rfl⟩ : syracuseStep 3220901 = 603919) (by norm_num)
theorem B3057077 : Blo 1429534 3057077 := bbase (se 5 (by rfl) ⟨143300, by rfl⟩ : syracuseStep 3057077 = 286601) (by norm_num)
theorem B3622421 : Blo 1429534 3622421 := bbase (se 6 (by rfl) ⟨84900, by rfl⟩ : syracuseStep 3622421 = 169801) (by norm_num)
theorem B3671621 : Blo 1429534 3671621 := bbase (se 4 (by rfl) ⟨344214, by rfl⟩ : syracuseStep 3671621 = 688429) (by norm_num)
theorem B3057221 : Blo 1429534 3057221 := bbase (se 4 (by rfl) ⟨286614, by rfl⟩ : syracuseStep 3057221 = 573229) (by norm_num)
theorem B16287317 : Blo 1429534 16287317 := bbase (se 8 (by rfl) ⟨95433, by rfl⟩ : syracuseStep 16287317 = 190867) (by norm_num)
theorem B5432933 : Blo 1429534 5432933 := bbase (se 4 (by rfl) ⟨509337, by rfl⟩ : syracuseStep 5432933 = 1018675) (by norm_num)
theorem B4826789 : Blo 1429534 4826789 := bbase (se 4 (by rfl) ⟨452511, by rfl⟩ : syracuseStep 4826789 = 905023) (by norm_num)
theorem B6874789 : Blo 1429534 6874789 := bbase (se 4 (by rfl) ⟨644511, by rfl⟩ : syracuseStep 6874789 = 1289023) (by norm_num)
theorem B4351781 : Blo 1429534 4351781 := bbase (se 4 (by rfl) ⟨407979, by rfl⟩ : syracuseStep 4351781 = 815959) (by norm_num)
theorem B3868517 : Blo 1429534 3868517 := bbase (se 4 (by rfl) ⟨362673, by rfl⟩ : syracuseStep 3868517 = 725347) (by norm_num)
theorem B3622765 : Blo 1429534 3622765 := bbase (se 3 (by rfl) ⟨679268, by rfl⟩ : syracuseStep 3622765 = 1358537) (by norm_num)
theorem B1632209 : Blo 1429534 1632209 := bbase (se 2 (by rfl) ⟨612078, by rfl⟩ : syracuseStep 1632209 = 1224157) (by norm_num)
theorem B3622877 : Blo 1429534 3622877 := bbase (se 3 (by rfl) ⟨679289, by rfl⟩ : syracuseStep 3622877 = 1358579) (by norm_num)
theorem B10307573 : Blo 1429534 10307573 := bbase (se 5 (by rfl) ⟨483167, by rfl⟩ : syracuseStep 10307573 = 966335) (by norm_num)
theorem B6522869 : Blo 1429534 6522869 := bbase (se 5 (by rfl) ⟨305759, by rfl⟩ : syracuseStep 6522869 = 611519) (by norm_num)
theorem B7243829 : Blo 1429534 7243829 := bbase (se 5 (by rfl) ⟨339554, by rfl⟩ : syracuseStep 7243829 = 679109) (by norm_num)
theorem B6113333 : Blo 1429534 6113333 := bbase (se 5 (by rfl) ⟨286562, by rfl⟩ : syracuseStep 6113333 = 573125) (by norm_num)
theorem B8144981 : Blo 1429534 8144981 := bbase (se 8 (by rfl) ⟨47724, by rfl⟩ : syracuseStep 8144981 = 95449) (by norm_num)
theorem B4827221 : Blo 1429534 4827221 := bbase (se 8 (by rfl) ⟨28284, by rfl⟩ : syracuseStep 4827221 = 56569) (by norm_num)
theorem B3623069 : Blo 1429534 3623069 := bbase (se 3 (by rfl) ⟨679325, by rfl⟩ : syracuseStep 3623069 = 1358651) (by norm_num)
theorem B13224181 : Blo 1429534 13224181 := bbase (se 5 (by rfl) ⟨619883, by rfl⟩ : syracuseStep 13224181 = 1239767) (by norm_num)
theorem B3623413 : Blo 1429534 3623413 := bbase (se 5 (by rfl) ⟨169847, by rfl⟩ : syracuseStep 3623413 = 339695) (by norm_num)
theorem B4827653 : Blo 1429534 4827653 := bbase (se 4 (by rfl) ⟨452592, by rfl⟩ : syracuseStep 4827653 = 905185) (by norm_num)
theorem B1608241 : Blo 1429534 1608241 := bbase (se 2 (by rfl) ⟨603090, by rfl⟩ : syracuseStep 1608241 = 1206181) (by norm_num)
theorem B1608277 : Blo 1429534 1608277 := bbase (se 8 (by rfl) ⟨9423, by rfl⟩ : syracuseStep 1608277 = 18847) (by norm_num)
theorem B3623525 : Blo 1429534 3623525 := bbase (se 4 (by rfl) ⟨339705, by rfl⟩ : syracuseStep 3623525 = 679411) (by norm_num)
theorem B1608313 : Blo 1429534 1608313 := bbase (se 2 (by rfl) ⟨603117, by rfl⟩ : syracuseStep 1608313 = 1206235) (by norm_num)
theorem B13748885 : Blo 1429534 13748885 := bbase (se 6 (by rfl) ⟨322239, by rfl⟩ : syracuseStep 13748885 = 644479) (by norm_num)
theorem B1608349 : Blo 1429534 1608349 := bbase (se 3 (by rfl) ⟨301565, by rfl⟩ : syracuseStep 1608349 = 603131) (by norm_num)
theorem B13052597 : Blo 1429534 13052597 := bbase (se 5 (by rfl) ⟨611840, by rfl⟩ : syracuseStep 13052597 = 1223681) (by norm_num)
theorem B1608385 : Blo 1429534 1608385 := bbase (se 2 (by rfl) ⟨603144, by rfl⟩ : syracuseStep 1608385 = 1206289) (by norm_num)
theorem B1608421 : Blo 1429534 1608421 := bbase (se 4 (by rfl) ⟨150789, by rfl⟩ : syracuseStep 1608421 = 301579) (by norm_num)
theorem B4074245 : Blo 1429534 4074245 := bbase (se 4 (by rfl) ⟨381960, by rfl⟩ : syracuseStep 4074245 = 763921) (by norm_num)
theorem B1608457 : Blo 1429534 1608457 := bbase (se 2 (by rfl) ⟨603171, by rfl⟩ : syracuseStep 1608457 = 1206343) (by norm_num)
theorem B1608493 : Blo 1429534 1608493 := bbase (se 3 (by rfl) ⟨301592, by rfl⟩ : syracuseStep 1608493 = 603185) (by norm_num)
theorem B1608529 : Blo 1429534 1608529 := bbase (se 2 (by rfl) ⟨603198, by rfl⟩ : syracuseStep 1608529 = 1206397) (by norm_num)
theorem B1608565 : Blo 1429534 1608565 := bbase (se 5 (by rfl) ⟨75401, by rfl⟩ : syracuseStep 1608565 = 150803) (by norm_num)
theorem B2714485 : Blo 1429534 2714485 := bbase (se 5 (by rfl) ⟨127241, by rfl⟩ : syracuseStep 2714485 = 254483) (by norm_num)
theorem B1608601 : Blo 1429534 1608601 := bbase (se 2 (by rfl) ⟨603225, by rfl⟩ : syracuseStep 1608601 = 1206451) (by norm_num)
theorem B2173853 : Blo 1429534 2173853 := bbase (se 3 (by rfl) ⟨407597, by rfl⟩ : syracuseStep 2173853 = 815195) (by norm_num)
theorem B1526693 : Blo 1429534 1526693 := bbase (se 4 (by rfl) ⟨143127, by rfl⟩ : syracuseStep 1526693 = 286255) (by norm_num)
theorem B4828085 : Blo 1429534 4828085 := bbase (se 5 (by rfl) ⟨226316, by rfl⟩ : syracuseStep 4828085 = 452633) (by norm_num)
theorem B1608637 : Blo 1429534 1608637 := bbase (se 3 (by rfl) ⟨301619, by rfl⟩ : syracuseStep 1608637 = 603239) (by norm_num)
theorem B1608673 : Blo 1429534 1608673 := bbase (se 2 (by rfl) ⟨603252, by rfl⟩ : syracuseStep 1608673 = 1206505) (by norm_num)
theorem B2714629 : Blo 1429534 2714629 := bbase (se 4 (by rfl) ⟨254496, by rfl⟩ : syracuseStep 2714629 = 508993) (by norm_num)
theorem B1608709 : Blo 1429534 1608709 := bbase (se 4 (by rfl) ⟨150816, by rfl⟩ : syracuseStep 1608709 = 301633) (by norm_num)
theorem B1608745 : Blo 1429534 1608745 := bbase (se 2 (by rfl) ⟨603279, by rfl⟩ : syracuseStep 1608745 = 1206559) (by norm_num)
theorem B1608781 : Blo 1429534 1608781 := bbase (se 3 (by rfl) ⟨301646, by rfl⟩ : syracuseStep 1608781 = 603293) (by norm_num)
theorem B1608817 : Blo 1429534 1608817 := bbase (se 2 (by rfl) ⟨603306, by rfl⟩ : syracuseStep 1608817 = 1206613) (by norm_num)
theorem B1608853 : Blo 1429534 1608853 := bbase (se 6 (by rfl) ⟨37707, by rfl⟩ : syracuseStep 1608853 = 75415) (by norm_num)
theorem B2714789 : Blo 1429534 2714789 := bbase (se 4 (by rfl) ⟨254511, by rfl⟩ : syracuseStep 2714789 = 509023) (by norm_num)
theorem B1608889 : Blo 1429534 1608889 := bbase (se 2 (by rfl) ⟨603333, by rfl⟩ : syracuseStep 1608889 = 1206667) (by norm_num)
theorem B1608925 : Blo 1429534 1608925 := bbase (se 3 (by rfl) ⟨301673, by rfl⟩ : syracuseStep 1608925 = 603347) (by norm_num)
theorem B3140861 : Blo 1429534 3140861 := bbase (se 3 (by rfl) ⟨588911, by rfl⟩ : syracuseStep 3140861 = 1177823) (by norm_num)
theorem B1608961 : Blo 1429534 1608961 := bbase (se 2 (by rfl) ⟨603360, by rfl⟩ : syracuseStep 1608961 = 1206721) (by norm_num)
theorem B1608997 : Blo 1429534 1608997 := bbase (se 4 (by rfl) ⟨150843, by rfl⟩ : syracuseStep 1608997 = 301687) (by norm_num)
theorem B2714933 : Blo 1429534 2714933 := bbase (se 5 (by rfl) ⟨127262, by rfl⟩ : syracuseStep 2714933 = 254525) (by norm_num)
theorem B7245125 : Blo 1429534 7245125 := bbase (se 4 (by rfl) ⟨679230, by rfl⟩ : syracuseStep 7245125 = 1358461) (by norm_num)
theorem B1609033 : Blo 1429534 1609033 := bbase (se 2 (by rfl) ⟨603387, by rfl⟩ : syracuseStep 1609033 = 1206775) (by norm_num)
theorem B4582757 : Blo 1429534 4582757 := bbase (se 4 (by rfl) ⟨429633, by rfl⟩ : syracuseStep 4582757 = 859267) (by norm_num)
theorem B4828517 : Blo 1429534 4828517 := bbase (se 4 (by rfl) ⟨452673, by rfl⟩ : syracuseStep 4828517 = 905347) (by norm_num)
theorem B1609069 : Blo 1429534 1609069 := bbase (se 3 (by rfl) ⟨301700, by rfl⟩ : syracuseStep 1609069 = 603401) (by norm_num)
theorem B1609105 : Blo 1429534 1609105 := bbase (se 2 (by rfl) ⟨603414, by rfl⟩ : syracuseStep 1609105 = 1206829) (by norm_num)
theorem B6106549 : Blo 1429534 6106549 := bbase (se 5 (by rfl) ⟨286244, by rfl⟩ : syracuseStep 6106549 = 572489) (by norm_num)
theorem B1609141 : Blo 1429534 1609141 := bbase (se 5 (by rfl) ⟨75428, by rfl⟩ : syracuseStep 1609141 = 150857) (by norm_num)
theorem B5156293 : Blo 1429534 5156293 := bbase (se 4 (by rfl) ⟨483402, by rfl⟩ : syracuseStep 5156293 = 966805) (by norm_num)
theorem B1609177 : Blo 1429534 1609177 := bbase (se 2 (by rfl) ⟨603441, by rfl⟩ : syracuseStep 1609177 = 1206883) (by norm_num)
theorem B3141109 : Blo 1429534 3141109 := bbase (se 5 (by rfl) ⟨147239, by rfl⟩ : syracuseStep 3141109 = 294479) (by norm_num)
theorem B1609213 : Blo 1429534 1609213 := bbase (se 3 (by rfl) ⟨301727, by rfl⟩ : syracuseStep 1609213 = 603455) (by norm_num)
theorem B1609249 : Blo 1429534 1609249 := bbase (se 2 (by rfl) ⟨603468, by rfl⟩ : syracuseStep 1609249 = 1206937) (by norm_num)
theorem B1609285 : Blo 1429534 1609285 := bbase (se 4 (by rfl) ⟨150870, by rfl⟩ : syracuseStep 1609285 = 301741) (by norm_num)
theorem B2715221 : Blo 1429534 2715221 := bbase (se 8 (by rfl) ⟨15909, by rfl⟩ : syracuseStep 2715221 = 31819) (by norm_num)
theorem B1609321 : Blo 1429534 1609321 := bbase (se 2 (by rfl) ⟨603495, by rfl⟩ : syracuseStep 1609321 = 1206991) (by norm_num)
theorem B1609357 : Blo 1429534 1609357 := bbase (se 3 (by rfl) ⟨301754, by rfl⟩ : syracuseStep 1609357 = 603509) (by norm_num)
theorem B1527445 : Blo 1429534 1527445 := bbase (se 6 (by rfl) ⟨35799, by rfl⟩ : syracuseStep 1527445 = 71599) (by norm_num)
theorem B5435045 : Blo 1429534 5435045 := bbase (se 4 (by rfl) ⟨509535, by rfl⟩ : syracuseStep 5435045 = 1019071) (by norm_num)
theorem B1609393 : Blo 1429534 1609393 := bbase (se 2 (by rfl) ⟨603522, by rfl⟩ : syracuseStep 1609393 = 1207045) (by norm_num)
theorem B1609429 : Blo 1429534 1609429 := bbase (se 7 (by rfl) ⟨18860, by rfl⟩ : syracuseStep 1609429 = 37721) (by norm_num)
theorem B1527517 : Blo 1429534 1527517 := bbase (se 3 (by rfl) ⟨286409, by rfl⟩ : syracuseStep 1527517 = 572819) (by norm_num)
theorem B7237349 : Blo 1429534 7237349 := bbase (se 4 (by rfl) ⟨678501, by rfl⟩ : syracuseStep 7237349 = 1357003) (by norm_num)
theorem B2715373 : Blo 1429534 2715373 := bbase (se 3 (by rfl) ⟨509132, by rfl⟩ : syracuseStep 2715373 = 1018265) (by norm_num)
theorem B1609465 : Blo 1429534 1609465 := bbase (se 2 (by rfl) ⟨603549, by rfl⟩ : syracuseStep 1609465 = 1207099) (by norm_num)
theorem B4828949 : Blo 1429534 4828949 := bbase (se 6 (by rfl) ⟨113178, by rfl⟩ : syracuseStep 4828949 = 226357) (by norm_num)
theorem B1609501 : Blo 1429534 1609501 := bbase (se 3 (by rfl) ⟨301781, by rfl⟩ : syracuseStep 1609501 = 603563) (by norm_num)
theorem B7728949 : Blo 1429534 7728949 := bbase (se 5 (by rfl) ⟨362294, by rfl⟩ : syracuseStep 7728949 = 724589) (by norm_num)
theorem B1609537 : Blo 1429534 1609537 := bbase (se 2 (by rfl) ⟨603576, by rfl⟩ : syracuseStep 1609537 = 1207153) (by norm_num)
theorem B2412389 : Blo 1429534 2412389 := bbase (se 4 (by rfl) ⟨226161, by rfl⟩ : syracuseStep 2412389 = 452323) (by norm_num)
theorem B2322277 : Blo 1429534 2322277 := bbase (se 4 (by rfl) ⟨217713, by rfl⟩ : syracuseStep 2322277 = 435427) (by norm_num)
theorem B1609573 : Blo 1429534 1609573 := bbase (se 4 (by rfl) ⟨150897, by rfl⟩ : syracuseStep 1609573 = 301795) (by norm_num)
theorem B3305333 : Blo 1429534 3305333 := bbase (se 5 (by rfl) ⟨154937, by rfl⟩ : syracuseStep 3305333 = 309875) (by norm_num)
theorem B5156741 : Blo 1429534 5156741 := bbase (se 4 (by rfl) ⟨483444, by rfl⟩ : syracuseStep 5156741 = 966889) (by norm_num)
theorem B1609609 : Blo 1429534 1609609 := bbase (se 2 (by rfl) ⟨603603, by rfl⟩ : syracuseStep 1609609 = 1207207) (by norm_num)
theorem B1527697 : Blo 1429534 1527697 := bbase (se 2 (by rfl) ⟨572886, by rfl⟩ : syracuseStep 1527697 = 1145773) (by norm_num)
theorem B4075429 : Blo 1429534 4075429 := bbase (se 4 (by rfl) ⟨382071, by rfl⟩ : syracuseStep 4075429 = 764143) (by norm_num)
theorem B1609645 : Blo 1429534 1609645 := bbase (se 3 (by rfl) ⟨301808, by rfl⟩ : syracuseStep 1609645 = 603617) (by norm_num)
theorem B5435333 : Blo 1429534 5435333 := bbase (se 4 (by rfl) ⟨509562, by rfl⟩ : syracuseStep 5435333 = 1019125) (by norm_num)
theorem B1609681 : Blo 1429534 1609681 := bbase (se 2 (by rfl) ⟨603630, by rfl⟩ : syracuseStep 1609681 = 1207261) (by norm_num)
theorem B2412517 : Blo 1429534 2412517 := bbase (se 4 (by rfl) ⟨226173, by rfl⟩ : syracuseStep 2412517 = 452347) (by norm_num)
theorem B1609717 : Blo 1429534 1609717 := bbase (se 5 (by rfl) ⟨75455, by rfl⟩ : syracuseStep 1609717 = 150911) (by norm_num)
theorem B2576389 : Blo 1429534 2576389 := bbase (se 4 (by rfl) ⟨241536, by rfl⟩ : syracuseStep 2576389 = 483073) (by norm_num)
theorem B1609753 : Blo 1429534 1609753 := bbase (se 2 (by rfl) ⟨603657, by rfl⟩ : syracuseStep 1609753 = 1207315) (by norm_num)
theorem B2715677 : Blo 1429534 2715677 := bbase (se 3 (by rfl) ⟨509189, by rfl⟩ : syracuseStep 2715677 = 1018379) (by norm_num)
theorem B2617381 : Blo 1429534 2617381 := bbase (se 4 (by rfl) ⟨245379, by rfl⟩ : syracuseStep 2617381 = 490759) (by norm_num)
theorem B3436597 : Blo 1429534 3436597 := bbase (se 5 (by rfl) ⟨161090, by rfl⟩ : syracuseStep 3436597 = 322181) (by norm_num)
theorem B2412605 : Blo 1429534 2412605 := bbase (se 3 (by rfl) ⟨452363, by rfl⟩ : syracuseStep 2412605 = 904727) (by norm_num)
theorem B1609789 : Blo 1429534 1609789 := bbase (se 3 (by rfl) ⟨301835, by rfl⟩ : syracuseStep 1609789 = 603671) (by norm_num)
theorem B4075589 : Blo 1429534 4075589 := bbase (se 4 (by rfl) ⟨382086, by rfl⟩ : syracuseStep 4075589 = 764173) (by norm_num)
theorem B32206933 : Blo 1429534 32206933 := bbase (se 8 (by rfl) ⟨188712, by rfl⟩ : syracuseStep 32206933 = 377425) (by norm_num)
theorem B1609825 : Blo 1429534 1609825 := bbase (se 2 (by rfl) ⟨603684, by rfl⟩ : syracuseStep 1609825 = 1207369) (by norm_num)
theorem B1609861 : Blo 1429534 1609861 := bbase (se 4 (by rfl) ⟨150924, by rfl⟩ : syracuseStep 1609861 = 301849) (by norm_num)
theorem B1609897 : Blo 1429534 1609897 := bbase (se 2 (by rfl) ⟨603711, by rfl⟩ : syracuseStep 1609897 = 1207423) (by norm_num)
theorem B2412733 : Blo 1429534 2412733 := bbase (se 3 (by rfl) ⟨452387, by rfl⟩ : syracuseStep 2412733 = 904775) (by norm_num)
theorem B4829381 : Blo 1429534 4829381 := bbase (se 4 (by rfl) ⟨452754, by rfl⟩ : syracuseStep 4829381 = 905509) (by norm_num)
theorem B1609933 : Blo 1429534 1609933 := bbase (se 3 (by rfl) ⟨301862, by rfl⟩ : syracuseStep 1609933 = 603725) (by norm_num)
theorem B2576605 : Blo 1429534 2576605 := bbase (se 3 (by rfl) ⟨483113, by rfl⟩ : syracuseStep 2576605 = 966227) (by norm_num)
theorem B1609969 : Blo 1429534 1609969 := bbase (se 2 (by rfl) ⟨603738, by rfl⟩ : syracuseStep 1609969 = 1207477) (by norm_num)
theorem B2412821 : Blo 1429534 2412821 := bbase (se 6 (by rfl) ⟨56550, by rfl⟩ : syracuseStep 2412821 = 113101) (by norm_num)
theorem B1610005 : Blo 1429534 1610005 := bbase (se 6 (by rfl) ⟨37734, by rfl⟩ : syracuseStep 1610005 = 75469) (by norm_num)
theorem B4075829 : Blo 1429534 4075829 := bbase (se 5 (by rfl) ⟨191054, by rfl⟩ : syracuseStep 4075829 = 382109) (by norm_num)
theorem B1610041 : Blo 1429534 1610041 := bbase (se 2 (by rfl) ⟨603765, by rfl⟩ : syracuseStep 1610041 = 1207531) (by norm_num)
theorem B2036029 : Blo 1429534 2036029 := bbase (se 3 (by rfl) ⟨381755, by rfl⟩ : syracuseStep 2036029 = 763511) (by norm_num)
theorem B1528141 : Blo 1429534 1528141 := bbase (se 3 (by rfl) ⟨286526, by rfl⟩ : syracuseStep 1528141 = 573053) (by norm_num)
theorem B1610077 : Blo 1429534 1610077 := bbase (se 3 (by rfl) ⟨301889, by rfl⟩ : syracuseStep 1610077 = 603779) (by norm_num)
theorem B1610113 : Blo 1429534 1610113 := bbase (se 2 (by rfl) ⟨603792, by rfl⟩ : syracuseStep 1610113 = 1207585) (by norm_num)
theorem B2412949 : Blo 1429534 2412949 := bbase (se 6 (by rfl) ⟨56553, by rfl⟩ : syracuseStep 2412949 = 113107) (by norm_num)
theorem B2322845 : Blo 1429534 2322845 := bbase (se 3 (by rfl) ⟨435533, by rfl⟩ : syracuseStep 2322845 = 871067) (by norm_num)
theorem B1610149 : Blo 1429534 1610149 := bbase (se 4 (by rfl) ⟨150951, by rfl⟩ : syracuseStep 1610149 = 301903) (by norm_num)
theorem B1528265 : Blo 1429534 1528265 := bbase (se 2 (by rfl) ⟨573099, by rfl⟩ : syracuseStep 1528265 = 1146199) (by norm_num)
theorem B1610185 : Blo 1429534 1610185 := bbase (se 2 (by rfl) ⟨603819, by rfl⟩ : syracuseStep 1610185 = 1207639) (by norm_num)
theorem B7336421 : Blo 1429534 7336421 := bbase (se 4 (by rfl) ⟨687789, by rfl⟩ : syracuseStep 7336421 = 1375579) (by norm_num)
theorem B2413037 : Blo 1429534 2413037 := bbase (se 3 (by rfl) ⟨452444, by rfl⟩ : syracuseStep 2413037 = 904889) (by norm_num)
theorem B1610221 : Blo 1429534 1610221 := bbase (se 3 (by rfl) ⟨301916, by rfl⟩ : syracuseStep 1610221 = 603833) (by norm_num)
theorem B4076021 : Blo 1429534 4076021 := bbase (se 5 (by rfl) ⟨191063, by rfl⟩ : syracuseStep 4076021 = 382127) (by norm_num)
theorem B1610257 : Blo 1429534 1610257 := bbase (se 2 (by rfl) ⟨603846, by rfl⟩ : syracuseStep 1610257 = 1207693) (by norm_num)
theorem B1610293 : Blo 1429534 1610293 := bbase (se 5 (by rfl) ⟨75482, by rfl⟩ : syracuseStep 1610293 = 150965) (by norm_num)
theorem B7246421 : Blo 1429534 7246421 := bbase (se 8 (by rfl) ⟨42459, by rfl⟩ : syracuseStep 7246421 = 84919) (by norm_num)
theorem B1610329 : Blo 1429534 1610329 := bbase (se 2 (by rfl) ⟨603873, by rfl⟩ : syracuseStep 1610329 = 1207747) (by norm_num)
theorem B2290277 : Blo 1429534 2290277 := bbase (se 4 (by rfl) ⟨214713, by rfl⟩ : syracuseStep 2290277 = 429427) (by norm_num)
theorem B2413165 : Blo 1429534 2413165 := bbase (se 3 (by rfl) ⟨452468, by rfl⟩ : syracuseStep 2413165 = 904937) (by norm_num)
theorem B4829813 : Blo 1429534 4829813 := bbase (se 5 (by rfl) ⟨226397, by rfl⟩ : syracuseStep 4829813 = 452795) (by norm_num)
theorem B1610365 : Blo 1429534 1610365 := bbase (se 3 (by rfl) ⟨301943, by rfl⟩ : syracuseStep 1610365 = 603887) (by norm_num)
theorem B5796485 : Blo 1429534 5796485 := bbase (se 4 (by rfl) ⟨543420, by rfl⟩ : syracuseStep 5796485 = 1086841) (by norm_num)
theorem B1610401 : Blo 1429534 1610401 := bbase (se 2 (by rfl) ⟨603900, by rfl⟩ : syracuseStep 1610401 = 1207801) (by norm_num)
theorem B2323109 : Blo 1429534 2323109 := bbase (se 4 (by rfl) ⟨217791, by rfl⟩ : syracuseStep 2323109 = 435583) (by norm_num)
theorem B2175653 : Blo 1429534 2175653 := bbase (se 4 (by rfl) ⟨203967, by rfl⟩ : syracuseStep 2175653 = 407935) (by norm_num)
theorem B2413253 : Blo 1429534 2413253 := bbase (se 4 (by rfl) ⟨226242, by rfl⟩ : syracuseStep 2413253 = 452485) (by norm_num)
theorem B1528517 : Blo 1429534 1528517 := bbase (se 4 (by rfl) ⟨143298, by rfl⟩ : syracuseStep 1528517 = 286597) (by norm_num)
theorem B1610437 : Blo 1429534 1610437 := bbase (se 4 (by rfl) ⟨150978, by rfl⟩ : syracuseStep 1610437 = 301957) (by norm_num)
theorem B3437261 : Blo 1429534 3437261 := bbase (se 3 (by rfl) ⟨644486, by rfl⟩ : syracuseStep 3437261 = 1288973) (by norm_num)
theorem B6869717 : Blo 1429534 6869717 := bbase (se 7 (by rfl) ⟨80504, by rfl⟩ : syracuseStep 6869717 = 161009) (by norm_num)
theorem B7443173 : Blo 1429534 7443173 := bbase (se 4 (by rfl) ⟨697797, by rfl⟩ : syracuseStep 7443173 = 1395595) (by norm_num)
theorem B1610473 : Blo 1429534 1610473 := bbase (se 2 (by rfl) ⟨603927, by rfl⟩ : syracuseStep 1610473 = 1207855) (by norm_num)
theorem B10867445 : Blo 1429534 10867445 := bbase (se 5 (by rfl) ⟨509411, by rfl⟩ : syracuseStep 10867445 = 1018823) (by norm_num)
theorem B2716429 : Blo 1429534 2716429 := bbase (se 3 (by rfl) ⟨509330, by rfl⟩ : syracuseStep 2716429 = 1018661) (by norm_num)
theorem B12227381 : Blo 1429534 12227381 := bbase (se 5 (by rfl) ⟨573158, by rfl⟩ : syracuseStep 12227381 = 1146317) (by norm_num)
theorem B2413381 : Blo 1429534 2413381 := bbase (se 4 (by rfl) ⟨226254, by rfl⟩ : syracuseStep 2413381 = 452509) (by norm_num)
theorem B2036621 : Blo 1429534 2036621 := bbase (se 3 (by rfl) ⟨381866, by rfl⟩ : syracuseStep 2036621 = 763733) (by norm_num)
theorem B2413469 : Blo 1429534 2413469 := bbase (se 3 (by rfl) ⟨452525, by rfl⟩ : syracuseStep 2413469 = 905051) (by norm_num)
theorem B2716573 : Blo 1429534 2716573 := bbase (se 3 (by rfl) ⟨509357, by rfl⟩ : syracuseStep 2716573 = 1018715) (by norm_num)
theorem B2036701 : Blo 1429534 2036701 := bbase (se 3 (by rfl) ⟨381881, by rfl⟩ : syracuseStep 2036701 = 763763) (by norm_num)
theorem B2290661 : Blo 1429534 2290661 := bbase (se 4 (by rfl) ⟨214749, by rfl⟩ : syracuseStep 2290661 = 429499) (by norm_num)
theorem B3437549 : Blo 1429534 3437549 := bbase (se 3 (by rfl) ⟨644540, by rfl⟩ : syracuseStep 3437549 = 1289081) (by norm_num)
theorem B7238645 : Blo 1429534 7238645 := bbase (se 5 (by rfl) ⟨339311, by rfl⟩ : syracuseStep 7238645 = 678623) (by norm_num)
theorem B2413597 : Blo 1429534 2413597 := bbase (se 3 (by rfl) ⟨452549, by rfl⟩ : syracuseStep 2413597 = 905099) (by norm_num)
theorem B4830245 : Blo 1429534 4830245 := bbase (se 4 (by rfl) ⟨452835, by rfl⟩ : syracuseStep 4830245 = 905671) (by norm_num)
theorem B2716733 : Blo 1429534 2716733 := bbase (se 3 (by rfl) ⟨509387, by rfl⟩ : syracuseStep 2716733 = 1018775) (by norm_num)
theorem B2036821 : Blo 1429534 2036821 := bbase (se 8 (by rfl) ⟨11934, by rfl⟩ : syracuseStep 2036821 = 23869) (by norm_num)
theorem B2290789 : Blo 1429534 2290789 := bbase (se 4 (by rfl) ⟨214761, by rfl⟩ : syracuseStep 2290789 = 429523) (by norm_num)
theorem B2413685 : Blo 1429534 2413685 := bbase (se 5 (by rfl) ⟨113141, by rfl⟩ : syracuseStep 2413685 = 226283) (by norm_num)
theorem B3216509 : Blo 1429534 3216509 := bbase (se 3 (by rfl) ⟨603095, by rfl⟩ : syracuseStep 3216509 = 1206191) (by norm_num)
theorem B10859669 : Blo 1429534 10859669 := bbase (se 6 (by rfl) ⟨254523, by rfl⟩ : syracuseStep 10859669 = 509047) (by norm_num)
theorem B9163925 : Blo 1429534 9163925 := bbase (se 6 (by rfl) ⟨214779, by rfl⟩ : syracuseStep 9163925 = 429559) (by norm_num)
theorem B1569949 : Blo 1429534 1569949 := bbase (se 3 (by rfl) ⟨294365, by rfl⟩ : syracuseStep 1569949 = 588731) (by norm_num)
theorem B2036917 : Blo 1429534 2036917 := bbase (se 5 (by rfl) ⟨95480, by rfl⟩ : syracuseStep 2036917 = 190961) (by norm_num)
theorem B3216581 : Blo 1429534 3216581 := bbase (se 4 (by rfl) ⟨301554, by rfl⟩ : syracuseStep 3216581 = 603109) (by norm_num)
theorem B1717453 : Blo 1429534 1717453 := bbase (se 3 (by rfl) ⟨322022, by rfl⟩ : syracuseStep 1717453 = 644045) (by norm_num)
theorem B2716877 : Blo 1429534 2716877 := bbase (se 3 (by rfl) ⟨509414, by rfl⟩ : syracuseStep 2716877 = 1018829) (by norm_num)
theorem B2413813 : Blo 1429534 2413813 := bbase (se 5 (by rfl) ⟨113147, by rfl⟩ : syracuseStep 2413813 = 226295) (by norm_num)
theorem B3216653 : Blo 1429534 3216653 := bbase (se 3 (by rfl) ⟨603122, by rfl⟩ : syracuseStep 3216653 = 1206245) (by norm_num)
theorem B1766677 : Blo 1429534 1766677 := bbase (se 6 (by rfl) ⟨41406, by rfl⟩ : syracuseStep 1766677 = 82813) (by norm_num)
theorem B1717573 : Blo 1429534 1717573 := bbase (se 4 (by rfl) ⟨161022, by rfl⟩ : syracuseStep 1717573 = 322045) (by norm_num)
theorem B2413901 : Blo 1429534 2413901 := bbase (se 3 (by rfl) ⟨452606, by rfl⟩ : syracuseStep 2413901 = 905213) (by norm_num)
theorem B3216725 : Blo 1429534 3216725 := bbase (se 14 (by rfl) ⟨294, by rfl⟩ : syracuseStep 3216725 = 589) (by norm_num)
theorem B2446733 : Blo 1429534 2446733 := bbase (se 3 (by rfl) ⟨458762, by rfl⟩ : syracuseStep 2446733 = 917525) (by norm_num)
theorem B3216797 : Blo 1429534 3216797 := bbase (se 3 (by rfl) ⟨603149, by rfl⟩ : syracuseStep 3216797 = 1206299) (by norm_num)
theorem B2414029 : Blo 1429534 2414029 := bbase (se 3 (by rfl) ⟨452630, by rfl⟩ : syracuseStep 2414029 = 905261) (by norm_num)
theorem B4830677 : Blo 1429534 4830677 := bbase (se 7 (by rfl) ⟨56609, by rfl⟩ : syracuseStep 4830677 = 113219) (by norm_num)
theorem B3216869 : Blo 1429534 3216869 := bbase (se 4 (by rfl) ⟨301581, by rfl⟩ : syracuseStep 3216869 = 603163) (by norm_num)
theorem B2717165 : Blo 1429534 2717165 := bbase (se 3 (by rfl) ⟨509468, by rfl⟩ : syracuseStep 2717165 = 1018937) (by norm_num)
theorem B5428741 : Blo 1429534 5428741 := bbase (se 4 (by rfl) ⟨508944, by rfl⟩ : syracuseStep 5428741 = 1017889) (by norm_num)
theorem B5879317 : Blo 1429534 5879317 := bbase (se 6 (by rfl) ⟨137796, by rfl⟩ : syracuseStep 5879317 = 275593) (by norm_num)
theorem B2414117 : Blo 1429534 2414117 := bbase (se 4 (by rfl) ⟨226323, by rfl⟩ : syracuseStep 2414117 = 452647) (by norm_num)
theorem B3216941 : Blo 1429534 3216941 := bbase (se 3 (by rfl) ⟨603176, by rfl⟩ : syracuseStep 3216941 = 1206353) (by norm_num)
theorem B6878789 : Blo 1429534 6878789 := bbase (se 4 (by rfl) ⟨644886, by rfl⟩ : syracuseStep 6878789 = 1289773) (by norm_num)
theorem B1570405 : Blo 1429534 1570405 := bbase (se 4 (by rfl) ⟨147225, by rfl⟩ : syracuseStep 1570405 = 294451) (by norm_num)
theorem B3217013 : Blo 1429534 3217013 := bbase (se 5 (by rfl) ⟨150797, by rfl⟩ : syracuseStep 3217013 = 301595) (by norm_num)
theorem B3053189 : Blo 1429534 3053189 := bbase (se 4 (by rfl) ⟨286236, by rfl⟩ : syracuseStep 3053189 = 572473) (by norm_num)
theorem B2717317 : Blo 1429534 2717317 := bbase (se 4 (by rfl) ⟨254748, by rfl⟩ : syracuseStep 2717317 = 509497) (by norm_num)
theorem B2578061 : Blo 1429534 2578061 := bbase (se 3 (by rfl) ⟨483386, by rfl⟩ : syracuseStep 2578061 = 966773) (by norm_num)
theorem B2414245 : Blo 1429534 2414245 := bbase (se 4 (by rfl) ⟨226335, by rfl⟩ : syracuseStep 2414245 = 452671) (by norm_num)
theorem B2037413 : Blo 1429534 2037413 := bbase (se 4 (by rfl) ⟨191007, by rfl⟩ : syracuseStep 2037413 = 382015) (by norm_num)
theorem B3217085 : Blo 1429534 3217085 := bbase (se 3 (by rfl) ⟨603203, by rfl⟩ : syracuseStep 3217085 = 1206407) (by norm_num)
theorem B3618533 : Blo 1429534 3618533 := bbase (se 4 (by rfl) ⟨339237, by rfl⟩ : syracuseStep 3618533 = 678475) (by norm_num)
theorem B2414333 : Blo 1429534 2414333 := bbase (se 3 (by rfl) ⟨452687, by rfl⟩ : syracuseStep 2414333 = 905375) (by norm_num)
theorem B3217157 : Blo 1429534 3217157 := bbase (se 4 (by rfl) ⟨301608, by rfl⟩ : syracuseStep 3217157 = 603217) (by norm_num)
theorem B2578205 : Blo 1429534 2578205 := bbase (se 3 (by rfl) ⟨483413, by rfl⟩ : syracuseStep 2578205 = 966827) (by norm_num)
theorem B5429045 : Blo 1429534 5429045 := bbase (se 5 (by rfl) ⟨254486, by rfl⟩ : syracuseStep 5429045 = 508973) (by norm_num)
theorem B3217229 : Blo 1429534 3217229 := bbase (se 3 (by rfl) ⟨603230, by rfl⟩ : syracuseStep 3217229 = 1206461) (by norm_num)
theorem B2578277 : Blo 1429534 2578277 := bbase (se 4 (by rfl) ⟨241713, by rfl⟩ : syracuseStep 2578277 = 483427) (by norm_num)
theorem B2414461 : Blo 1429534 2414461 := bbase (se 3 (by rfl) ⟨452711, by rfl⟩ : syracuseStep 2414461 = 905423) (by norm_num)
theorem B4831109 : Blo 1429534 4831109 := bbase (se 4 (by rfl) ⟨452916, by rfl⟩ : syracuseStep 4831109 = 905833) (by norm_num)
theorem B3217301 : Blo 1429534 3217301 := bbase (se 6 (by rfl) ⟨75405, by rfl⟩ : syracuseStep 3217301 = 150811) (by norm_num)
theorem B2717621 : Blo 1429534 2717621 := bbase (se 5 (by rfl) ⟨127388, by rfl⟩ : syracuseStep 2717621 = 254777) (by norm_num)
theorem B10311637 : Blo 1429534 10311637 := bbase (se 7 (by rfl) ⟨120839, by rfl⟩ : syracuseStep 10311637 = 241679) (by norm_num)
theorem B2414549 : Blo 1429534 2414549 := bbase (se 7 (by rfl) ⟨28295, by rfl⟩ : syracuseStep 2414549 = 56591) (by norm_num)
theorem B3217373 : Blo 1429534 3217373 := bbase (se 3 (by rfl) ⟨603257, by rfl⟩ : syracuseStep 3217373 = 1206515) (by norm_num)
theorem B3217445 : Blo 1429534 3217445 := bbase (se 4 (by rfl) ⟨301635, by rfl⟩ : syracuseStep 3217445 = 603271) (by norm_num)
theorem B2144309 : Blo 1429534 2144309 := bbase (se 5 (by rfl) ⟨100514, by rfl⟩ : syracuseStep 2144309 = 201029) (by norm_num)
theorem B3618877 : Blo 1429534 3618877 := bbase (se 3 (by rfl) ⟨678539, by rfl⟩ : syracuseStep 3618877 = 1357079) (by norm_num)
theorem B2144333 : Blo 1429534 2144333 := bbase (se 3 (by rfl) ⟨402062, by rfl⟩ : syracuseStep 2144333 = 804125) (by norm_num)
theorem B2291789 : Blo 1429534 2291789 := bbase (se 3 (by rfl) ⟨429710, by rfl⟩ : syracuseStep 2291789 = 859421) (by norm_num)
theorem B2414677 : Blo 1429534 2414677 := bbase (se 8 (by rfl) ⟨14148, by rfl⟩ : syracuseStep 2414677 = 28297) (by norm_num)
theorem B2144357 : Blo 1429534 2144357 := bbase (se 4 (by rfl) ⟨201033, by rfl⟩ : syracuseStep 2144357 = 402067) (by norm_num)
theorem B3217517 : Blo 1429534 3217517 := bbase (se 3 (by rfl) ⟨603284, by rfl⟩ : syracuseStep 3217517 = 1206569) (by norm_num)
theorem B2144381 : Blo 1429534 2144381 := bbase (se 3 (by rfl) ⟨402071, by rfl⟩ : syracuseStep 2144381 = 804143) (by norm_num)
theorem B2144405 : Blo 1429534 2144405 := bbase (se 6 (by rfl) ⟨50259, by rfl⟩ : syracuseStep 2144405 = 100519) (by norm_num)
theorem B2144429 : Blo 1429534 2144429 := bbase (se 3 (by rfl) ⟨402080, by rfl⟩ : syracuseStep 2144429 = 804161) (by norm_num)
theorem B3618989 : Blo 1429534 3618989 := bbase (se 3 (by rfl) ⟨678560, by rfl⟩ : syracuseStep 3618989 = 1357121) (by norm_num)
theorem B2414765 : Blo 1429534 2414765 := bbase (se 3 (by rfl) ⟨452768, by rfl⟩ : syracuseStep 2414765 = 905537) (by norm_num)
theorem B3217589 : Blo 1429534 3217589 := bbase (se 5 (by rfl) ⟨150824, by rfl⟩ : syracuseStep 3217589 = 301649) (by norm_num)
theorem B2144453 : Blo 1429534 2144453 := bbase (se 4 (by rfl) ⟨201042, by rfl⟩ : syracuseStep 2144453 = 402085) (by norm_num)
theorem B2291917 : Blo 1429534 2291917 := bbase (se 3 (by rfl) ⟨429734, by rfl⟩ : syracuseStep 2291917 = 859469) (by norm_num)
theorem B2037965 : Blo 1429534 2037965 := bbase (se 3 (by rfl) ⟨382118, by rfl⟩ : syracuseStep 2037965 = 764237) (by norm_num)
theorem B24762581 : Blo 1429534 24762581 := bbase (se 7 (by rfl) ⟨290186, by rfl⟩ : syracuseStep 24762581 = 580373) (by norm_num)
theorem B2144477 : Blo 1429534 2144477 := bbase (se 3 (by rfl) ⟨402089, by rfl⟩ : syracuseStep 2144477 = 804179) (by norm_num)
theorem B2144501 : Blo 1429534 2144501 := bbase (se 5 (by rfl) ⟨100523, by rfl⟩ : syracuseStep 2144501 = 201047) (by norm_num)
theorem B3217661 : Blo 1429534 3217661 := bbase (se 3 (by rfl) ⟨603311, by rfl⟩ : syracuseStep 3217661 = 1206623) (by norm_num)
theorem B7239941 : Blo 1429534 7239941 := bbase (se 4 (by rfl) ⟨678744, by rfl⟩ : syracuseStep 7239941 = 1357489) (by norm_num)
theorem B2144525 : Blo 1429534 2144525 := bbase (se 3 (by rfl) ⟨402098, by rfl⟩ : syracuseStep 2144525 = 804197) (by norm_num)
theorem B2144549 : Blo 1429534 2144549 := bbase (se 4 (by rfl) ⟨201051, by rfl⟩ : syracuseStep 2144549 = 402103) (by norm_num)
theorem B2414893 : Blo 1429534 2414893 := bbase (se 3 (by rfl) ⟨452792, by rfl⟩ : syracuseStep 2414893 = 905585) (by norm_num)
theorem B2144573 : Blo 1429534 2144573 := bbase (se 3 (by rfl) ⟨402107, by rfl⟩ : syracuseStep 2144573 = 804215) (by norm_num)
theorem B3217733 : Blo 1429534 3217733 := bbase (se 4 (by rfl) ⟨301662, by rfl⟩ : syracuseStep 3217733 = 603325) (by norm_num)
theorem B2144597 : Blo 1429534 2144597 := bbase (se 10 (by rfl) ⟨3141, by rfl⟩ : syracuseStep 2144597 = 6283) (by norm_num)
theorem B2578781 : Blo 1429534 2578781 := bbase (se 3 (by rfl) ⟨483521, by rfl⟩ : syracuseStep 2578781 = 967043) (by norm_num)
theorem B2144621 : Blo 1429534 2144621 := bbase (se 3 (by rfl) ⟨402116, by rfl⟩ : syracuseStep 2144621 = 804233) (by norm_num)
theorem B3619181 : Blo 1429534 3619181 := bbase (se 3 (by rfl) ⟨678596, by rfl⟩ : syracuseStep 3619181 = 1357193) (by norm_num)
theorem B3053933 : Blo 1429534 3053933 := bbase (se 3 (by rfl) ⟨572612, by rfl⟩ : syracuseStep 3053933 = 1145225) (by norm_num)
theorem B9288053 : Blo 1429534 9288053 := bbase (se 5 (by rfl) ⟨435377, by rfl⟩ : syracuseStep 9288053 = 870755) (by norm_num)
theorem B1743229 : Blo 1429534 1743229 := bbase (se 3 (by rfl) ⟨326855, by rfl⟩ : syracuseStep 1743229 = 653711) (by norm_num)
theorem B2144645 : Blo 1429534 2144645 := bbase (se 4 (by rfl) ⟨201060, by rfl⟩ : syracuseStep 2144645 = 402121) (by norm_num)
theorem B2414981 : Blo 1429534 2414981 := bbase (se 4 (by rfl) ⟨226404, by rfl⟩ : syracuseStep 2414981 = 452809) (by norm_num)
theorem B3217805 : Blo 1429534 3217805 := bbase (se 3 (by rfl) ⟨603338, by rfl⟩ : syracuseStep 3217805 = 1206677) (by norm_num)
theorem B2144669 : Blo 1429534 2144669 := bbase (se 3 (by rfl) ⟨402125, by rfl⟩ : syracuseStep 2144669 = 804251) (by norm_num)
theorem B4897189 : Blo 1429534 4897189 := bbase (se 4 (by rfl) ⟨459111, by rfl⟩ : syracuseStep 4897189 = 918223) (by norm_num)
theorem B2144693 : Blo 1429534 2144693 := bbase (se 5 (by rfl) ⟨100532, by rfl⟩ : syracuseStep 2144693 = 201065) (by norm_num)
theorem B2144717 : Blo 1429534 2144717 := bbase (se 3 (by rfl) ⟨402134, by rfl⟩ : syracuseStep 2144717 = 804269) (by norm_num)
theorem B3217877 : Blo 1429534 3217877 := bbase (se 7 (by rfl) ⟨37709, by rfl⟩ : syracuseStep 3217877 = 75419) (by norm_num)
theorem B2144741 : Blo 1429534 2144741 := bbase (se 4 (by rfl) ⟨201069, by rfl⟩ : syracuseStep 2144741 = 402139) (by norm_num)
theorem B2144765 : Blo 1429534 2144765 := bbase (se 3 (by rfl) ⟨402143, by rfl⟩ : syracuseStep 2144765 = 804287) (by norm_num)
theorem B2415109 : Blo 1429534 2415109 := bbase (se 4 (by rfl) ⟨226416, by rfl⟩ : syracuseStep 2415109 = 452833) (by norm_num)
theorem B2144789 : Blo 1429534 2144789 := bbase (se 6 (by rfl) ⟨50268, by rfl⟩ : syracuseStep 2144789 = 100537) (by norm_num)
theorem B3217949 : Blo 1429534 3217949 := bbase (se 3 (by rfl) ⟨603365, by rfl⟩ : syracuseStep 3217949 = 1206731) (by norm_num)
theorem B2144813 : Blo 1429534 2144813 := bbase (se 3 (by rfl) ⟨402152, by rfl⟩ : syracuseStep 2144813 = 804305) (by norm_num)
theorem B2144837 : Blo 1429534 2144837 := bbase (se 4 (by rfl) ⟨201078, by rfl⟩ : syracuseStep 2144837 = 402157) (by norm_num)
theorem B2292301 : Blo 1429534 2292301 := bbase (se 3 (by rfl) ⟨429806, by rfl⟩ : syracuseStep 2292301 = 859613) (by norm_num)
theorem B18324053 : Blo 1429534 18324053 := bbase (se 8 (by rfl) ⟨107367, by rfl⟩ : syracuseStep 18324053 = 214735) (by norm_num)
theorem B2144861 : Blo 1429534 2144861 := bbase (se 3 (by rfl) ⟨402161, by rfl⟩ : syracuseStep 2144861 = 804323) (by norm_num)
theorem B2415197 : Blo 1429534 2415197 := bbase (se 3 (by rfl) ⟨452849, by rfl⟩ : syracuseStep 2415197 = 905699) (by norm_num)
theorem B3218021 : Blo 1429534 3218021 := bbase (se 4 (by rfl) ⟨301689, by rfl⟩ : syracuseStep 3218021 = 603379) (by norm_num)
theorem B2144885 : Blo 1429534 2144885 := bbase (se 5 (by rfl) ⟨100541, by rfl⟩ : syracuseStep 2144885 = 201083) (by norm_num)
theorem B2144909 : Blo 1429534 2144909 := bbase (se 3 (by rfl) ⟨402170, by rfl⟩ : syracuseStep 2144909 = 804341) (by norm_num)
theorem B2144933 : Blo 1429534 2144933 := bbase (se 4 (by rfl) ⟨201087, by rfl⟩ : syracuseStep 2144933 = 402175) (by norm_num)
theorem B3218093 : Blo 1429534 3218093 := bbase (se 3 (by rfl) ⟨603392, by rfl⟩ : syracuseStep 3218093 = 1206785) (by norm_num)
theorem B2144957 : Blo 1429534 2144957 := bbase (se 3 (by rfl) ⟨402179, by rfl⟩ : syracuseStep 2144957 = 804359) (by norm_num)
theorem B3619525 : Blo 1429534 3619525 := bbase (se 4 (by rfl) ⟨339330, by rfl⟩ : syracuseStep 3619525 = 678661) (by norm_num)
theorem B2144981 : Blo 1429534 2144981 := bbase (se 7 (by rfl) ⟨25136, by rfl⟩ : syracuseStep 2144981 = 50273) (by norm_num)
theorem B2415325 : Blo 1429534 2415325 := bbase (se 3 (by rfl) ⟨452873, by rfl⟩ : syracuseStep 2415325 = 905747) (by norm_num)
theorem B2145005 : Blo 1429534 2145005 := bbase (se 3 (by rfl) ⟨402188, by rfl⟩ : syracuseStep 2145005 = 804377) (by norm_num)
theorem B13744885 : Blo 1429534 13744885 := bbase (se 5 (by rfl) ⟨644291, by rfl⟩ : syracuseStep 13744885 = 1288583) (by norm_num)
theorem B3218165 : Blo 1429534 3218165 := bbase (se 5 (by rfl) ⟨150851, by rfl⟩ : syracuseStep 3218165 = 301703) (by norm_num)
theorem B2145029 : Blo 1429534 2145029 := bbase (se 4 (by rfl) ⟨201096, by rfl⟩ : syracuseStep 2145029 = 402193) (by norm_num)
theorem B23214869 : Blo 1429534 23214869 := bbase (se 6 (by rfl) ⟨544098, by rfl⟩ : syracuseStep 23214869 = 1088197) (by norm_num)
theorem B2145053 : Blo 1429534 2145053 := bbase (se 3 (by rfl) ⟨402197, by rfl⟩ : syracuseStep 2145053 = 804395) (by norm_num)
theorem B3619637 : Blo 1429534 3619637 := bbase (se 5 (by rfl) ⟨169670, by rfl⟩ : syracuseStep 3619637 = 339341) (by norm_num)
theorem B2145077 : Blo 1429534 2145077 := bbase (se 5 (by rfl) ⟨100550, by rfl⟩ : syracuseStep 2145077 = 201101) (by norm_num)
theorem B2415413 : Blo 1429534 2415413 := bbase (se 5 (by rfl) ⟨113222, by rfl⟩ : syracuseStep 2415413 = 226445) (by norm_num)
theorem B3218237 : Blo 1429534 3218237 := bbase (se 3 (by rfl) ⟨603419, by rfl⟩ : syracuseStep 3218237 = 1206839) (by norm_num)
theorem B2145101 : Blo 1429534 2145101 := bbase (se 3 (by rfl) ⟨402206, by rfl⟩ : syracuseStep 2145101 = 804413) (by norm_num)
theorem B2292557 : Blo 1429534 2292557 := bbase (se 3 (by rfl) ⟨429854, by rfl⟩ : syracuseStep 2292557 = 859709) (by norm_num)
theorem B74316629 : Blo 1429534 74316629 := bbase (se 9 (by rfl) ⟨217724, by rfl⟩ : syracuseStep 74316629 = 435449) (by norm_num)
theorem B2145125 : Blo 1429534 2145125 := bbase (se 4 (by rfl) ⟨201105, by rfl⟩ : syracuseStep 2145125 = 402211) (by norm_num)
theorem B1719149 : Blo 1429534 1719149 := bbase (se 3 (by rfl) ⟨322340, by rfl⟩ : syracuseStep 1719149 = 644681) (by norm_num)
theorem B2145149 : Blo 1429534 2145149 := bbase (se 3 (by rfl) ⟨402215, by rfl⟩ : syracuseStep 2145149 = 804431) (by norm_num)
theorem B3218309 : Blo 1429534 3218309 := bbase (se 4 (by rfl) ⟨301716, by rfl⟩ : syracuseStep 3218309 = 603433) (by norm_num)
theorem B2145173 : Blo 1429534 2145173 := bbase (se 6 (by rfl) ⟨50277, by rfl⟩ : syracuseStep 2145173 = 100555) (by norm_num)
theorem B1809317 : Blo 1429534 1809317 := bbase (se 4 (by rfl) ⟨169623, by rfl⟩ : syracuseStep 1809317 = 339247) (by norm_num)
theorem B2145197 : Blo 1429534 2145197 := bbase (se 3 (by rfl) ⟨402224, by rfl⟩ : syracuseStep 2145197 = 804449) (by norm_num)
theorem B2415541 : Blo 1429534 2415541 := bbase (se 5 (by rfl) ⟨113228, by rfl⟩ : syracuseStep 2415541 = 226457) (by norm_num)
theorem B2145221 : Blo 1429534 2145221 := bbase (se 4 (by rfl) ⟨201114, by rfl⟩ : syracuseStep 2145221 = 402229) (by norm_num)
theorem B3218381 : Blo 1429534 3218381 := bbase (se 3 (by rfl) ⟨603446, by rfl⟩ : syracuseStep 3218381 = 1206893) (by norm_num)
theorem B1809373 : Blo 1429534 1809373 := bbase (se 3 (by rfl) ⟨339257, by rfl⟩ : syracuseStep 1809373 = 678515) (by norm_num)
theorem B2145245 : Blo 1429534 2145245 := bbase (se 3 (by rfl) ⟨402233, by rfl⟩ : syracuseStep 2145245 = 804467) (by norm_num)
theorem B3619829 : Blo 1429534 3619829 := bbase (se 5 (by rfl) ⟨169679, by rfl⟩ : syracuseStep 3619829 = 339359) (by norm_num)
theorem B2145269 : Blo 1429534 2145269 := bbase (se 5 (by rfl) ⟨100559, by rfl⟩ : syracuseStep 2145269 = 201119) (by norm_num)
theorem B2145293 : Blo 1429534 2145293 := bbase (se 3 (by rfl) ⟨402242, by rfl⟩ : syracuseStep 2145293 = 804485) (by norm_num)
theorem B2415629 : Blo 1429534 2415629 := bbase (se 3 (by rfl) ⟨452930, by rfl⟩ : syracuseStep 2415629 = 905861) (by norm_num)
theorem B3218453 : Blo 1429534 3218453 := bbase (se 6 (by rfl) ⟨75432, by rfl⟩ : syracuseStep 3218453 = 150865) (by norm_num)
theorem B2145317 : Blo 1429534 2145317 := bbase (se 4 (by rfl) ⟨201123, by rfl⟩ : syracuseStep 2145317 = 402247) (by norm_num)
theorem B12213301 : Blo 1429534 12213301 := bbase (se 5 (by rfl) ⟨572498, by rfl⟩ : syracuseStep 12213301 = 1144997) (by norm_num)
theorem B1809469 : Blo 1429534 1809469 := bbase (se 3 (by rfl) ⟨339275, by rfl⟩ : syracuseStep 1809469 = 678551) (by norm_num)
theorem B2145341 : Blo 1429534 2145341 := bbase (se 3 (by rfl) ⟨402251, by rfl⟩ : syracuseStep 2145341 = 804503) (by norm_num)
theorem B2145365 : Blo 1429534 2145365 := bbase (se 8 (by rfl) ⟨12570, by rfl⟩ : syracuseStep 2145365 = 25141) (by norm_num)
theorem B3054685 : Blo 1429534 3054685 := bbase (se 3 (by rfl) ⟨572753, by rfl⟩ : syracuseStep 3054685 = 1145507) (by norm_num)
theorem B3218525 : Blo 1429534 3218525 := bbase (se 3 (by rfl) ⟨603473, by rfl⟩ : syracuseStep 3218525 = 1206947) (by norm_num)
theorem B2145389 : Blo 1429534 2145389 := bbase (se 3 (by rfl) ⟨402260, by rfl⟩ : syracuseStep 2145389 = 804521) (by norm_num)
theorem B2063485 : Blo 1429534 2063485 := bbase (se 3 (by rfl) ⟨386903, by rfl⟩ : syracuseStep 2063485 = 773807) (by norm_num)
theorem B3308669 : Blo 1429534 3308669 := bbase (se 3 (by rfl) ⟨620375, by rfl⟩ : syracuseStep 3308669 = 1240751) (by norm_num)
theorem B2145413 : Blo 1429534 2145413 := bbase (se 4 (by rfl) ⟨201132, by rfl⟩ : syracuseStep 2145413 = 402265) (by norm_num)
theorem B2145437 : Blo 1429534 2145437 := bbase (se 3 (by rfl) ⟨402269, by rfl⟩ : syracuseStep 2145437 = 804539) (by norm_num)
theorem B3218597 : Blo 1429534 3218597 := bbase (se 4 (by rfl) ⟨301743, by rfl⟩ : syracuseStep 3218597 = 603487) (by norm_num)
theorem B2145461 : Blo 1429534 2145461 := bbase (se 5 (by rfl) ⟨100568, by rfl⟩ : syracuseStep 2145461 = 201137) (by norm_num)
theorem B2145485 : Blo 1429534 2145485 := bbase (se 3 (by rfl) ⟨402278, by rfl⟩ : syracuseStep 2145485 = 804557) (by norm_num)
theorem B2145509 : Blo 1429534 2145509 := bbase (se 4 (by rfl) ⟨201141, by rfl⟩ : syracuseStep 2145509 = 402283) (by norm_num)
theorem B1809641 : Blo 1429534 1809641 := bbase (se 2 (by rfl) ⟨678615, by rfl⟩ : syracuseStep 1809641 = 1357231) (by norm_num)
theorem B3054829 : Blo 1429534 3054829 := bbase (se 3 (by rfl) ⟨572780, by rfl⟩ : syracuseStep 3054829 = 1145561) (by norm_num)
theorem B3218669 : Blo 1429534 3218669 := bbase (se 3 (by rfl) ⟨603500, by rfl⟩ : syracuseStep 3218669 = 1207001) (by norm_num)
theorem B2145533 : Blo 1429534 2145533 := bbase (se 3 (by rfl) ⟨402287, by rfl⟩ : syracuseStep 2145533 = 804575) (by norm_num)
theorem B2145557 : Blo 1429534 2145557 := bbase (se 6 (by rfl) ⟨50286, by rfl⟩ : syracuseStep 2145557 = 100573) (by norm_num)
theorem B1809697 : Blo 1429534 1809697 := bbase (se 2 (by rfl) ⟨678636, by rfl⟩ : syracuseStep 1809697 = 1357273) (by norm_num)
theorem B2145581 : Blo 1429534 2145581 := bbase (se 3 (by rfl) ⟨402296, by rfl⟩ : syracuseStep 2145581 = 804593) (by norm_num)
theorem B3218741 : Blo 1429534 3218741 := bbase (se 5 (by rfl) ⟨150878, by rfl⟩ : syracuseStep 3218741 = 301757) (by norm_num)
theorem B2235701 : Blo 1429534 2235701 := bbase (se 5 (by rfl) ⟨104798, by rfl⟩ : syracuseStep 2235701 = 209597) (by norm_num)
theorem B2145605 : Blo 1429534 2145605 := bbase (se 4 (by rfl) ⟨201150, by rfl⟩ : syracuseStep 2145605 = 402301) (by norm_num)
theorem B3620173 : Blo 1429534 3620173 := bbase (se 3 (by rfl) ⟨678782, by rfl⟩ : syracuseStep 3620173 = 1357565) (by norm_num)
theorem B2145629 : Blo 1429534 2145629 := bbase (se 3 (by rfl) ⟨402305, by rfl⟩ : syracuseStep 2145629 = 804611) (by norm_num)
theorem B2145653 : Blo 1429534 2145653 := bbase (se 5 (by rfl) ⟨100577, by rfl⟩ : syracuseStep 2145653 = 201155) (by norm_num)
theorem B3218813 : Blo 1429534 3218813 := bbase (se 3 (by rfl) ⟨603527, by rfl⟩ : syracuseStep 3218813 = 1207055) (by norm_num)
theorem B1809793 : Blo 1429534 1809793 := bbase (se 2 (by rfl) ⟨678672, by rfl⟩ : syracuseStep 1809793 = 1357345) (by norm_num)
theorem B2145677 : Blo 1429534 2145677 := bbase (se 3 (by rfl) ⟨402314, by rfl⟩ : syracuseStep 2145677 = 804629) (by norm_num)
theorem B2145701 : Blo 1429534 2145701 := bbase (se 4 (by rfl) ⟨201159, by rfl⟩ : syracuseStep 2145701 = 402319) (by norm_num)
theorem B3620285 : Blo 1429534 3620285 := bbase (se 3 (by rfl) ⟨678803, by rfl⟩ : syracuseStep 3620285 = 1357607) (by norm_num)
theorem B2145725 : Blo 1429534 2145725 := bbase (se 3 (by rfl) ⟨402323, by rfl⟩ : syracuseStep 2145725 = 804647) (by norm_num)
theorem B3218885 : Blo 1429534 3218885 := bbase (se 4 (by rfl) ⟨301770, by rfl⟩ : syracuseStep 3218885 = 603541) (by norm_num)
theorem B2145749 : Blo 1429534 2145749 := bbase (se 7 (by rfl) ⟨25145, by rfl⟩ : syracuseStep 2145749 = 50291) (by norm_num)
theorem B2145773 : Blo 1429534 2145773 := bbase (se 3 (by rfl) ⟨402332, by rfl⟩ : syracuseStep 2145773 = 804665) (by norm_num)
theorem B2145797 : Blo 1429534 2145797 := bbase (se 4 (by rfl) ⟨201168, by rfl⟩ : syracuseStep 2145797 = 402337) (by norm_num)
theorem B3218957 : Blo 1429534 3218957 := bbase (se 3 (by rfl) ⟨603554, by rfl⟩ : syracuseStep 3218957 = 1207109) (by norm_num)
theorem B6872597 : Blo 1429534 6872597 := bbase (se 6 (by rfl) ⟨161076, by rfl⟩ : syracuseStep 6872597 = 322153) (by norm_num)
theorem B7241237 : Blo 1429534 7241237 := bbase (se 6 (by rfl) ⟨169716, by rfl⟩ : syracuseStep 7241237 = 339433) (by norm_num)
theorem B2145821 : Blo 1429534 2145821 := bbase (se 3 (by rfl) ⟨402341, by rfl⟩ : syracuseStep 2145821 = 804683) (by norm_num)
theorem B1834537 : Blo 1429534 1834537 := bbase (se 2 (by rfl) ⟨687951, by rfl⟩ : syracuseStep 1834537 = 1375903) (by norm_num)
theorem B1809965 : Blo 1429534 1809965 := bbase (se 3 (by rfl) ⟨339368, by rfl⟩ : syracuseStep 1809965 = 678737) (by norm_num)
theorem B2145845 : Blo 1429534 2145845 := bbase (se 5 (by rfl) ⟨100586, by rfl⟩ : syracuseStep 2145845 = 201173) (by norm_num)
theorem B2145869 : Blo 1429534 2145869 := bbase (se 3 (by rfl) ⟨402350, by rfl⟩ : syracuseStep 2145869 = 804701) (by norm_num)
theorem B5504597 : Blo 1429534 5504597 := bbase (se 8 (by rfl) ⟨32253, by rfl⟩ : syracuseStep 5504597 = 64507) (by norm_num)
theorem B3219029 : Blo 1429534 3219029 := bbase (se 8 (by rfl) ⟨18861, by rfl⟩ : syracuseStep 3219029 = 37723) (by norm_num)
theorem B1810021 : Blo 1429534 1810021 := bbase (se 4 (by rfl) ⟨169689, by rfl⟩ : syracuseStep 1810021 = 339379) (by norm_num)
theorem B3055205 : Blo 1429534 3055205 := bbase (se 4 (by rfl) ⟨286425, by rfl⟩ : syracuseStep 3055205 = 572851) (by norm_num)
theorem B2145893 : Blo 1429534 2145893 := bbase (se 4 (by rfl) ⟨201177, by rfl⟩ : syracuseStep 2145893 = 402355) (by norm_num)
theorem B3096181 : Blo 1429534 3096181 := bbase (se 5 (by rfl) ⟨145133, by rfl⟩ : syracuseStep 3096181 = 290267) (by norm_num)
theorem B3620477 : Blo 1429534 3620477 := bbase (se 3 (by rfl) ⟨678839, by rfl⟩ : syracuseStep 3620477 = 1357679) (by norm_num)
theorem B2145917 : Blo 1429534 2145917 := bbase (se 3 (by rfl) ⟨402359, by rfl⟩ : syracuseStep 2145917 = 804719) (by norm_num)
theorem B2145941 : Blo 1429534 2145941 := bbase (se 6 (by rfl) ⟨50295, by rfl⟩ : syracuseStep 2145941 = 100591) (by norm_num)
theorem B3219101 : Blo 1429534 3219101 := bbase (se 3 (by rfl) ⟨603581, by rfl⟩ : syracuseStep 3219101 = 1207163) (by norm_num)
theorem B2145965 : Blo 1429534 2145965 := bbase (se 3 (by rfl) ⟨402368, by rfl⟩ : syracuseStep 2145965 = 804737) (by norm_num)
theorem B1810117 : Blo 1429534 1810117 := bbase (se 4 (by rfl) ⟨169698, by rfl⟩ : syracuseStep 1810117 = 339397) (by norm_num)
theorem B2145989 : Blo 1429534 2145989 := bbase (se 4 (by rfl) ⟨201186, by rfl⟩ : syracuseStep 2145989 = 402373) (by norm_num)
theorem B2146013 : Blo 1429534 2146013 := bbase (se 3 (by rfl) ⟨402377, by rfl⟩ : syracuseStep 2146013 = 804755) (by norm_num)
theorem B3219173 : Blo 1429534 3219173 := bbase (se 4 (by rfl) ⟨301797, by rfl⟩ : syracuseStep 3219173 = 603595) (by norm_num)
theorem B2752237 : Blo 1429534 2752237 := bbase (se 3 (by rfl) ⟨516044, by rfl⟩ : syracuseStep 2752237 = 1032089) (by norm_num)
theorem B2146037 : Blo 1429534 2146037 := bbase (se 5 (by rfl) ⟨100595, by rfl⟩ : syracuseStep 2146037 = 201191) (by norm_num)
theorem B1449721 : Blo 1429534 1449721 := bbase (se 2 (by rfl) ⟨543645, by rfl⟩ : syracuseStep 1449721 = 1087291) (by norm_num)
theorem B2146061 : Blo 1429534 2146061 := bbase (se 3 (by rfl) ⟨402386, by rfl⟩ : syracuseStep 2146061 = 804773) (by norm_num)
theorem B2146085 : Blo 1429534 2146085 := bbase (se 4 (by rfl) ⟨201195, by rfl⟩ : syracuseStep 2146085 = 402391) (by norm_num)
theorem B1548077 : Blo 1429534 1548077 := bbase (se 3 (by rfl) ⟨290264, by rfl⟩ : syracuseStep 1548077 = 580529) (by norm_num)
theorem B3219245 : Blo 1429534 3219245 := bbase (se 3 (by rfl) ⟨603608, by rfl⟩ : syracuseStep 3219245 = 1207217) (by norm_num)
theorem B4644661 : Blo 1429534 4644661 := bbase (se 5 (by rfl) ⟨217718, by rfl⟩ : syracuseStep 4644661 = 435437) (by norm_num)
theorem B2146109 : Blo 1429534 2146109 := bbase (se 3 (by rfl) ⟨402395, by rfl⟩ : syracuseStep 2146109 = 804791) (by norm_num)
theorem B2146133 : Blo 1429534 2146133 := bbase (se 9 (by rfl) ⟨6287, by rfl⟩ : syracuseStep 2146133 = 12575) (by norm_num)
theorem B2146157 : Blo 1429534 2146157 := bbase (se 3 (by rfl) ⟨402404, by rfl⟩ : syracuseStep 2146157 = 804809) (by norm_num)
theorem B1810289 : Blo 1429534 1810289 := bbase (se 2 (by rfl) ⟨678858, by rfl⟩ : syracuseStep 1810289 = 1357717) (by norm_num)
theorem B5431157 : Blo 1429534 5431157 := bbase (se 5 (by rfl) ⟨254585, by rfl⟩ : syracuseStep 5431157 = 509171) (by norm_num)
theorem B3219317 : Blo 1429534 3219317 := bbase (se 5 (by rfl) ⟨150905, by rfl⟩ : syracuseStep 3219317 = 301811) (by norm_num)
theorem B2146181 : Blo 1429534 2146181 := bbase (se 4 (by rfl) ⟨201204, by rfl⟩ : syracuseStep 2146181 = 402409) (by norm_num)
theorem B2146205 : Blo 1429534 2146205 := bbase (se 3 (by rfl) ⟨402413, by rfl⟩ : syracuseStep 2146205 = 804827) (by norm_num)
theorem B1810345 : Blo 1429534 1810345 := bbase (se 2 (by rfl) ⟨678879, by rfl⟩ : syracuseStep 1810345 = 1357759) (by norm_num)
theorem B3260341 : Blo 1429534 3260341 := bbase (se 5 (by rfl) ⟨152828, by rfl⟩ : syracuseStep 3260341 = 305657) (by norm_num)
theorem B2146229 : Blo 1429534 2146229 := bbase (se 5 (by rfl) ⟨100604, by rfl⟩ : syracuseStep 2146229 = 201209) (by norm_num)
theorem B3219389 : Blo 1429534 3219389 := bbase (se 3 (by rfl) ⟨603635, by rfl⟩ : syracuseStep 3219389 = 1207271) (by norm_num)
theorem B2146253 : Blo 1429534 2146253 := bbase (se 3 (by rfl) ⟨402422, by rfl⟩ : syracuseStep 2146253 = 804845) (by norm_num)
theorem B3620821 : Blo 1429534 3620821 := bbase (se 7 (by rfl) ⟨42431, by rfl⟩ : syracuseStep 3620821 = 84863) (by norm_num)
theorem B17399765 : Blo 1429534 17399765 := bbase (se 7 (by rfl) ⟨203903, by rfl⟩ : syracuseStep 17399765 = 407807) (by norm_num)
theorem B3055573 : Blo 1429534 3055573 := bbase (se 7 (by rfl) ⟨35807, by rfl⟩ : syracuseStep 3055573 = 71615) (by norm_num)
theorem B4825061 : Blo 1429534 4825061 := bbase (se 4 (by rfl) ⟨452349, by rfl⟩ : syracuseStep 4825061 = 904699) (by norm_num)
theorem B4071397 : Blo 1429534 4071397 := bbase (se 4 (by rfl) ⟨381693, by rfl⟩ : syracuseStep 4071397 = 763387) (by norm_num)
theorem B2146277 : Blo 1429534 2146277 := bbase (se 4 (by rfl) ⟨201213, by rfl⟩ : syracuseStep 2146277 = 402427) (by norm_num)
theorem B2146301 : Blo 1429534 2146301 := bbase (se 3 (by rfl) ⟨402431, by rfl⟩ : syracuseStep 2146301 = 804863) (by norm_num)
theorem B2146307 : Blo 1429534 2146307 := bstep (se 1 (by rfl) ⟨1609730, by rfl⟩ : syracuseStep 2146307 = 3219461) B3219461
theorem B1810451 : Blo 1429534 1810451 := bstep (se 1 (by rfl) ⟨1357838, by rfl⟩ : syracuseStep 1810451 = 2715677) B2715677
theorem B2146337 : Blo 1429534 2146337 := bstep (se 2 (by rfl) ⟨804876, by rfl⟩ : syracuseStep 2146337 = 1609753) B1609753
theorem B5505059 : Blo 1429534 5505059 := bstep (se 1 (by rfl) ⟨4128794, by rfl⟩ : syracuseStep 5505059 = 8257589) B8257589
theorem B3489841 : Blo 1429534 3489841 := bstep (se 2 (by rfl) ⟨1308690, by rfl⟩ : syracuseStep 3489841 = 2617381) B2617381
theorem B2146355 : Blo 1429534 2146355 := bstep (se 1 (by rfl) ⟨1609766, by rfl⟩ : syracuseStep 2146355 = 3219533) B3219533
theorem B4825169 : Blo 1429534 4825169 := bstep (se 2 (by rfl) ⟨1809438, by rfl⟩ : syracuseStep 4825169 = 3618877) B3618877
theorem B2146385 : Blo 1429534 2146385 := bstep (se 2 (by rfl) ⟨804894, by rfl⟩ : syracuseStep 2146385 = 1609789) B1609789
theorem B3620963 : Blo 1429534 3620963 := bstep (se 1 (by rfl) ⟨2715722, by rfl⟩ : syracuseStep 3620963 = 5431445) B5431445
theorem B2146403 : Blo 1429534 2146403 := bstep (se 1 (by rfl) ⟨1609802, by rfl⟩ : syracuseStep 2146403 = 3219605) B3219605
theorem B42942577 : Blo 1429534 42942577 := bstep (se 2 (by rfl) ⟨16103466, by rfl⟩ : syracuseStep 42942577 = 32206933) B32206933
theorem B3219569 : Blo 1429534 3219569 := bstep (se 2 (by rfl) ⟨1207338, by rfl⟩ : syracuseStep 3219569 = 2414677) B2414677
theorem B2146433 : Blo 1429534 2146433 := bstep (se 2 (by rfl) ⟨804912, by rfl⟩ : syracuseStep 2146433 = 1609825) B1609825
theorem B3219587 : Blo 1429534 3219587 := bstep (se 1 (by rfl) ⟨2414690, by rfl⟩ : syracuseStep 3219587 = 4829381) B4829381
theorem B2146451 : Blo 1429534 2146451 := bstep (se 1 (by rfl) ⟨1609838, by rfl⟩ : syracuseStep 2146451 = 3219677) B3219677
theorem B2146481 : Blo 1429534 2146481 := bstep (se 2 (by rfl) ⟨804930, by rfl⟩ : syracuseStep 2146481 = 1609861) B1609861
theorem B2146499 : Blo 1429534 2146499 := bstep (se 1 (by rfl) ⟨1609874, by rfl⟩ : syracuseStep 2146499 = 3219749) B3219749
theorem B2146529 : Blo 1429534 2146529 := bstep (se 2 (by rfl) ⟨804948, by rfl⟩ : syracuseStep 2146529 = 1609897) B1609897
theorem B2146547 : Blo 1429534 2146547 := bstep (se 1 (by rfl) ⟨1609910, by rfl⟩ : syracuseStep 2146547 = 3219821) B3219821
theorem B3055889 : Blo 1429534 3055889 := bstep (se 2 (by rfl) ⟨1145958, by rfl⟩ : syracuseStep 3055889 = 2291917) B2291917
theorem B2146577 : Blo 1429534 2146577 := bstep (se 2 (by rfl) ⟨804966, by rfl⟩ : syracuseStep 2146577 = 1609933) B1609933
theorem B1548563 : Blo 1429534 1548563 := bstep (se 1 (by rfl) ⟨1161422, by rfl⟩ : syracuseStep 1548563 = 2322845) B2322845
theorem B2146595 : Blo 1429534 2146595 := bstep (se 1 (by rfl) ⟨1609946, by rfl⟩ : syracuseStep 2146595 = 3219893) B3219893
theorem B2146625 : Blo 1429534 2146625 := bstep (se 2 (by rfl) ⟨804984, by rfl⟩ : syracuseStep 2146625 = 1609969) B1609969
theorem B4890947 : Blo 1429534 4890947 := bstep (se 1 (by rfl) ⟨3668210, by rfl⟩ : syracuseStep 4890947 = 7336421) B7336421
theorem B2146643 : Blo 1429534 2146643 := bstep (se 1 (by rfl) ⟨1609982, by rfl⟩ : syracuseStep 2146643 = 3219965) B3219965
theorem B2146673 : Blo 1429534 2146673 := bstep (se 2 (by rfl) ⟨805002, by rfl⟩ : syracuseStep 2146673 = 1610005) B1610005
theorem B2146691 : Blo 1429534 2146691 := bstep (se 1 (by rfl) ⟨1610018, by rfl⟩ : syracuseStep 2146691 = 3220037) B3220037
theorem B3219857 : Blo 1429534 3219857 := bstep (se 2 (by rfl) ⟨1207446, by rfl⟩ : syracuseStep 3219857 = 2414893) B2414893
theorem B2146721 : Blo 1429534 2146721 := bstep (se 2 (by rfl) ⟨805020, by rfl⟩ : syracuseStep 2146721 = 1610041) B1610041
theorem B3219875 : Blo 1429534 3219875 := bstep (se 1 (by rfl) ⟨2414906, by rfl⟩ : syracuseStep 3219875 = 4829813) B4829813
theorem B2146739 : Blo 1429534 2146739 := bstep (se 1 (by rfl) ⟨1610054, by rfl⟩ : syracuseStep 2146739 = 3220109) B3220109
theorem B1548739 : Blo 1429534 1548739 := bstep (se 1 (by rfl) ⟨1161554, by rfl⟩ : syracuseStep 1548739 = 2323109) B2323109
theorem B1450435 : Blo 1429534 1450435 := bstep (se 1 (by rfl) ⟨1087826, by rfl⟩ : syracuseStep 1450435 = 2175653) B2175653
theorem B2146769 : Blo 1429534 2146769 := bstep (se 2 (by rfl) ⟨805038, by rfl⟩ : syracuseStep 2146769 = 1610077) B1610077
theorem B4579811 : Blo 1429534 4579811 := bstep (se 1 (by rfl) ⟨3434858, by rfl⟩ : syracuseStep 4579811 = 6869717) B6869717
theorem B2146787 : Blo 1429534 2146787 := bstep (se 1 (by rfl) ⟨1610090, by rfl⟩ : syracuseStep 2146787 = 3220181) B3220181
theorem B2146817 : Blo 1429534 2146817 := bstep (se 2 (by rfl) ⟨805056, by rfl⟩ : syracuseStep 2146817 = 1610113) B1610113
theorem B2146835 : Blo 1429534 2146835 := bstep (se 1 (by rfl) ⟨1610126, by rfl⟩ : syracuseStep 2146835 = 3220253) B3220253
theorem B8151587 : Blo 1429534 8151587 := bstep (se 1 (by rfl) ⟨6113690, by rfl⟩ : syracuseStep 8151587 = 12227381) B12227381
theorem B2146865 : Blo 1429534 2146865 := bstep (se 2 (by rfl) ⟨805074, by rfl⟩ : syracuseStep 2146865 = 1610149) B1610149
theorem B6529585 : Blo 1429534 6529585 := bstep (se 2 (by rfl) ⟨2448594, by rfl⟩ : syracuseStep 6529585 = 4897189) B4897189
theorem B2146883 : Blo 1429534 2146883 := bstep (se 1 (by rfl) ⟨1610162, by rfl⟩ : syracuseStep 2146883 = 3220325) B3220325
theorem B2146913 : Blo 1429534 2146913 := bstep (se 2 (by rfl) ⟨805092, by rfl⟩ : syracuseStep 2146913 = 1610185) B1610185
theorem B4825709 : Blo 1429534 4825709 := bstep (se 3 (by rfl) ⟨904820, by rfl⟩ : syracuseStep 4825709 = 1809641) B1809641
theorem B2146931 : Blo 1429534 2146931 := bstep (se 1 (by rfl) ⟨1610198, by rfl⟩ : syracuseStep 2146931 = 3220397) B3220397
theorem B2146961 : Blo 1429534 2146961 := bstep (se 2 (by rfl) ⟨805110, by rfl⟩ : syracuseStep 2146961 = 1610221) B1610221
theorem B4825763 : Blo 1429534 4825763 := bstep (se 1 (by rfl) ⟨3619322, by rfl⟩ : syracuseStep 4825763 = 7238645) B7238645
theorem B8143523 : Blo 1429534 8143523 := bstep (se 1 (by rfl) ⟨6107642, by rfl⟩ : syracuseStep 8143523 = 12215285) B12215285
theorem B2146979 : Blo 1429534 2146979 := bstep (se 1 (by rfl) ⟨1610234, by rfl⟩ : syracuseStep 2146979 = 3220469) B3220469
theorem B3220145 : Blo 1429534 3220145 := bstep (se 2 (by rfl) ⟨1207554, by rfl⟩ : syracuseStep 3220145 = 2415109) B2415109
theorem B2147009 : Blo 1429534 2147009 := bstep (se 2 (by rfl) ⟨805128, by rfl⟩ : syracuseStep 2147009 = 1610257) B1610257
theorem B3220163 : Blo 1429534 3220163 := bstep (se 1 (by rfl) ⟨2415122, by rfl⟩ : syracuseStep 3220163 = 4830245) B4830245
theorem B1811155 : Blo 1429534 1811155 := bstep (se 1 (by rfl) ⟨1358366, by rfl⟩ : syracuseStep 1811155 = 2716733) B2716733
theorem B2147027 : Blo 1429534 2147027 := bstep (se 1 (by rfl) ⟨1610270, by rfl⟩ : syracuseStep 2147027 = 3220541) B3220541
theorem B2147057 : Blo 1429534 2147057 := bstep (se 2 (by rfl) ⟨805146, by rfl⟩ : syracuseStep 2147057 = 1610293) B1610293
theorem B2147075 : Blo 1429534 2147075 := bstep (se 1 (by rfl) ⟨1610306, by rfl⟩ : syracuseStep 2147075 = 3220613) B3220613
theorem B3056401 : Blo 1429534 3056401 := bstep (se 2 (by rfl) ⟨1146150, by rfl⟩ : syracuseStep 3056401 = 2292301) B2292301
theorem B2147105 : Blo 1429534 2147105 := bstep (se 2 (by rfl) ⟨805164, by rfl⟩ : syracuseStep 2147105 = 1610329) B1610329
theorem B1811251 : Blo 1429534 1811251 := bstep (se 1 (by rfl) ⟨1358438, by rfl⟩ : syracuseStep 1811251 = 2716877) B2716877
theorem B2147123 : Blo 1429534 2147123 := bstep (se 1 (by rfl) ⟨1610342, by rfl⟩ : syracuseStep 2147123 = 3220685) B3220685
theorem B8373061 : Blo 1429534 8373061 := bstep (se 4 (by rfl) ⟨784974, by rfl⟩ : syracuseStep 8373061 = 1569949) B1569949
theorem B2147153 : Blo 1429534 2147153 := bstep (se 2 (by rfl) ⟨805182, by rfl⟩ : syracuseStep 2147153 = 1610365) B1610365
theorem B2147171 : Blo 1429534 2147171 := bstep (se 1 (by rfl) ⟨1610378, by rfl⟩ : syracuseStep 2147171 = 3220757) B3220757
theorem B2147201 : Blo 1429534 2147201 := bstep (se 2 (by rfl) ⟨805200, by rfl⟩ : syracuseStep 2147201 = 1610401) B1610401
theorem B1934227 : Blo 1429534 1934227 := bstep (se 1 (by rfl) ⟨1450670, by rfl⟩ : syracuseStep 1934227 = 2901341) B2901341
theorem B2147219 : Blo 1429534 2147219 := bstep (se 1 (by rfl) ⟨1610414, by rfl⟩ : syracuseStep 2147219 = 3220829) B3220829
theorem B4826033 : Blo 1429534 4826033 := bstep (se 2 (by rfl) ⟨1809762, by rfl⟩ : syracuseStep 4826033 = 3619525) B3619525
theorem B2147249 : Blo 1429534 2147249 := bstep (se 2 (by rfl) ⟨805218, by rfl⟩ : syracuseStep 2147249 = 1610437) B1610437
theorem B2147267 : Blo 1429534 2147267 := bstep (se 1 (by rfl) ⟨1610450, by rfl⟩ : syracuseStep 2147267 = 3220901) B3220901
theorem B10863557 : Blo 1429534 10863557 := bstep (se 4 (by rfl) ⟨1018458, by rfl⟩ : syracuseStep 10863557 = 2036917) B2036917
theorem B3220433 : Blo 1429534 3220433 := bstep (se 2 (by rfl) ⟨1207662, by rfl⟩ : syracuseStep 3220433 = 2415325) B2415325
theorem B2147297 : Blo 1429534 2147297 := bstep (se 2 (by rfl) ⟨805236, by rfl⟩ : syracuseStep 2147297 = 1610473) B1610473
theorem B3220451 : Blo 1429534 3220451 := bstep (se 1 (by rfl) ⟨2415338, by rfl⟩ : syracuseStep 3220451 = 4830677) B4830677
theorem B18326513 : Blo 1429534 18326513 := bstep (se 2 (by rfl) ⟨6872442, by rfl⟩ : syracuseStep 18326513 = 13744885) B13744885
theorem B3621905 : Blo 1429534 3621905 := bstep (se 2 (by rfl) ⟨1358214, by rfl⟩ : syracuseStep 3621905 = 2716429) B2716429
theorem B3621955 : Blo 1429534 3621955 := bstep (se 1 (by rfl) ⟨2716466, by rfl⟩ : syracuseStep 3621955 = 5432933) B5432933
theorem B9159749 : Blo 1429534 9159749 := bstep (se 4 (by rfl) ⟨858726, by rfl⟩ : syracuseStep 9159749 = 1717453) B1717453
theorem B3867761 : Blo 1429534 3867761 := bstep (se 2 (by rfl) ⟨1450410, by rfl⟩ : syracuseStep 3867761 = 2900821) B2900821
theorem B2901187 : Blo 1429534 2901187 := bstep (se 1 (by rfl) ⟨2175890, by rfl⟩ : syracuseStep 2901187 = 4351781) B4351781
theorem B3622097 : Blo 1429534 3622097 := bstep (se 2 (by rfl) ⟨1358286, by rfl⟩ : syracuseStep 3622097 = 2716573) B2716573
theorem B3220721 : Blo 1429534 3220721 := bstep (se 2 (by rfl) ⟨1207770, by rfl⟩ : syracuseStep 3220721 = 2415541) B2415541
theorem B3220739 : Blo 1429534 3220739 := bstep (se 1 (by rfl) ⟨2415554, by rfl⟩ : syracuseStep 3220739 = 4831109) B4831109
theorem B1811747 : Blo 1429534 1811747 := bstep (se 1 (by rfl) ⟨1358810, by rfl⟩ : syracuseStep 1811747 = 2717621) B2717621
theorem B4826573 : Blo 1429534 4826573 := bstep (se 3 (by rfl) ⟨904982, by rfl⟩ : syracuseStep 4826573 = 1809965) B1809965
theorem B4072913 : Blo 1429534 4072913 := bstep (se 2 (by rfl) ⟨1527342, by rfl⟩ : syracuseStep 4072913 = 3054685) B3054685
theorem B16508387 : Blo 1429534 16508387 := bstep (se 1 (by rfl) ⟨12381290, by rfl⟩ : syracuseStep 16508387 = 24762581) B24762581
theorem B4826627 : Blo 1429534 4826627 := bstep (se 1 (by rfl) ⟨3619970, by rfl⟩ : syracuseStep 4826627 = 7239941) B7239941
theorem B8152589 : Blo 1429534 8152589 := bstep (se 3 (by rfl) ⟨1528610, by rfl⟩ : syracuseStep 8152589 = 3057221) B3057221
theorem B8259205 : Blo 1429534 8259205 := bstep (se 4 (by rfl) ⟨774300, by rfl⟩ : syracuseStep 8259205 = 1548601) B1548601
theorem B4073105 : Blo 1429534 4073105 := bstep (se 2 (by rfl) ⟨1527414, by rfl⟩ : syracuseStep 4073105 = 3054829) B3054829
theorem B12216035 : Blo 1429534 12216035 := bstep (se 1 (by rfl) ⟨9162026, by rfl⟩ : syracuseStep 12216035 = 18324053) B18324053
theorem B7243505 : Blo 1429534 7243505 := bstep (se 2 (by rfl) ⟨2716314, by rfl⟩ : syracuseStep 7243505 = 5432629) B5432629
theorem B5433101 : Blo 1429534 5433101 := bstep (se 3 (by rfl) ⟨1018706, by rfl⟩ : syracuseStep 5433101 = 2037413) B2037413
theorem B4826897 : Blo 1429534 4826897 := bstep (se 2 (by rfl) ⟨1810086, by rfl⟩ : syracuseStep 4826897 = 3620173) B3620173
theorem B15476579 : Blo 1429534 15476579 := bstep (se 1 (by rfl) ⟨11607434, by rfl⟩ : syracuseStep 15476579 = 23214869) B23214869
theorem B6875057 : Blo 1429534 6875057 := bstep (se 2 (by rfl) ⟨2578146, by rfl⟩ : syracuseStep 6875057 = 5156293) B5156293
theorem B2205779 : Blo 1429534 2205779 := bstep (se 1 (by rfl) ⟨1654334, by rfl⟩ : syracuseStep 2205779 = 3308669) B3308669
theorem B3623089 : Blo 1429534 3623089 := bstep (se 2 (by rfl) ⟨1358658, by rfl⟩ : syracuseStep 3623089 = 2717317) B2717317
theorem B17410229 : Blo 1429534 17410229 := bstep (se 5 (by rfl) ⟨816104, by rfl⟩ : syracuseStep 17410229 = 1632209) B1632209
theorem B6113485 : Blo 1429534 6113485 := bstep (se 3 (by rfl) ⟨1146278, by rfl⟩ : syracuseStep 6113485 = 2292557) B2292557
theorem B6875405 : Blo 1429534 6875405 := bstep (se 3 (by rfl) ⟨1289138, by rfl⟩ : syracuseStep 6875405 = 2578277) B2578277
theorem B10316045 : Blo 1429534 10316045 := bstep (se 3 (by rfl) ⟨1934258, by rfl⟩ : syracuseStep 10316045 = 3868517) B3868517
theorem B4827437 : Blo 1429534 4827437 := bstep (se 3 (by rfl) ⟨905144, by rfl⟩ : syracuseStep 4827437 = 1810289) B1810289
theorem B4581731 : Blo 1429534 4581731 := bstep (se 1 (by rfl) ⟨3436298, by rfl⟩ : syracuseStep 4581731 = 6872597) B6872597
theorem B4827491 : Blo 1429534 4827491 := bstep (se 1 (by rfl) ⟨3620618, by rfl⟩ : syracuseStep 4827491 = 7241237) B7241237
theorem B3623363 : Blo 1429534 3623363 := bstep (se 1 (by rfl) ⟨2717522, by rfl⟩ : syracuseStep 3623363 = 5435045) B5435045
theorem B5433905 : Blo 1429534 5433905 := bstep (se 2 (by rfl) ⟨2037714, by rfl⟩ : syracuseStep 5433905 = 4075429) B4075429
theorem B1608259 : Blo 1429534 1608259 := bstep (se 1 (by rfl) ⟨1206194, by rfl⟩ : syracuseStep 1608259 = 2412389) B2412389
theorem B4827761 : Blo 1429534 4827761 := bstep (se 2 (by rfl) ⟨1810410, by rfl⟩ : syracuseStep 4827761 = 3620821) B3620821
theorem B13748849 : Blo 1429534 13748849 := bstep (se 2 (by rfl) ⟨5155818, by rfl⟩ : syracuseStep 13748849 = 10311637) B10311637
theorem B4074097 : Blo 1429534 4074097 := bstep (se 2 (by rfl) ⟨1527786, by rfl⟩ : syracuseStep 4074097 = 3055573) B3055573
theorem B3623555 : Blo 1429534 3623555 := bstep (se 1 (by rfl) ⟨2717666, by rfl⟩ : syracuseStep 3623555 = 5435333) B5435333
theorem B3435185 : Blo 1429534 3435185 := bstep (se 2 (by rfl) ⟨1288194, by rfl⟩ : syracuseStep 3435185 = 2576389) B2576389
theorem B1608403 : Blo 1429534 1608403 := bstep (se 1 (by rfl) ⟨1206302, by rfl⟩ : syracuseStep 1608403 = 2412605) B2412605
theorem B3435299 : Blo 1429534 3435299 := bstep (se 1 (by rfl) ⟨2576474, by rfl⟩ : syracuseStep 3435299 = 5152949) B5152949
theorem B1608547 : Blo 1429534 1608547 := bstep (se 1 (by rfl) ⟨1206410, by rfl⟩ : syracuseStep 1608547 = 2412821) B2412821
theorem B4074371 : Blo 1429534 4074371 := bstep (se 1 (by rfl) ⟨3055778, by rfl⟩ : syracuseStep 4074371 = 6111557) B6111557
theorem B18328517 : Blo 1429534 18328517 := bstep (se 4 (by rfl) ⟨1718298, by rfl⟩ : syracuseStep 18328517 = 3436597) B3436597
theorem B3435473 : Blo 1429534 3435473 := bstep (se 2 (by rfl) ⟨1288302, by rfl⟩ : syracuseStep 3435473 = 2576605) B2576605
theorem B17632241 : Blo 1429534 17632241 := bstep (se 2 (by rfl) ⟨6612090, by rfl⟩ : syracuseStep 17632241 = 13224181) B13224181
theorem B1608691 : Blo 1429534 1608691 := bstep (se 1 (by rfl) ⟨1206518, by rfl⟩ : syracuseStep 1608691 = 2413037) B2413037
theorem B1526851 : Blo 1429534 1526851 := bstep (se 1 (by rfl) ⟨1145138, by rfl⟩ : syracuseStep 1526851 = 2290277) B2290277
theorem B4074563 : Blo 1429534 4074563 := bstep (se 1 (by rfl) ⟨3055922, by rfl⟩ : syracuseStep 4074563 = 6111845) B6111845
theorem B2714705 : Blo 1429534 2714705 := bstep (se 2 (by rfl) ⟨1018014, by rfl⟩ : syracuseStep 2714705 = 2036029) B2036029
theorem B1608835 : Blo 1429534 1608835 := bstep (se 1 (by rfl) ⟨1206626, by rfl⟩ : syracuseStep 1608835 = 2413253) B2413253
theorem B4828301 : Blo 1429534 4828301 := bstep (se 3 (by rfl) ⟨905306, by rfl⟩ : syracuseStep 4828301 = 1810613) B1810613
theorem B7244963 : Blo 1429534 7244963 := bstep (se 1 (by rfl) ⟨5433722, by rfl⟩ : syracuseStep 7244963 = 10867445) B10867445
theorem B4828355 : Blo 1429534 4828355 := bstep (se 1 (by rfl) ⟨3621266, by rfl⟩ : syracuseStep 4828355 = 7242533) B7242533
theorem B5434573 : Blo 1429534 5434573 := bstep (se 3 (by rfl) ⟨1018982, by rfl⟩ : syracuseStep 5434573 = 2037965) B2037965
theorem B1608979 : Blo 1429534 1608979 := bstep (se 1 (by rfl) ⟨1206734, by rfl⟩ : syracuseStep 1608979 = 2413469) B2413469
theorem B1527107 : Blo 1429534 1527107 := bstep (se 1 (by rfl) ⟨1145330, by rfl⟩ : syracuseStep 1527107 = 2290661) B2290661
theorem B1609123 : Blo 1429534 1609123 := bstep (se 1 (by rfl) ⟨1206842, by rfl⟩ : syracuseStep 1609123 = 2413685) B2413685
theorem B4828625 : Blo 1429534 4828625 := bstep (se 2 (by rfl) ⟨1810734, by rfl⟩ : syracuseStep 4828625 = 3621469) B3621469
theorem B1609267 : Blo 1429534 1609267 := bstep (se 1 (by rfl) ⟨1206950, by rfl⟩ : syracuseStep 1609267 = 2413901) B2413901
theorem B1609411 : Blo 1429534 1609411 := bstep (se 1 (by rfl) ⟨1207058, by rfl⟩ : syracuseStep 1609411 = 2414117) B2414117
theorem B6524621 : Blo 1429534 6524621 := bstep (se 3 (by rfl) ⟨1223366, by rfl⟩ : syracuseStep 6524621 = 2446733) B2446733
theorem B10858211 : Blo 1429534 10858211 := bstep (se 1 (by rfl) ⟨8143658, by rfl⟩ : syracuseStep 10858211 = 16287317) B16287317
theorem B2035459 : Blo 1429534 2035459 := bstep (se 1 (by rfl) ⟨1526594, by rfl⟩ : syracuseStep 2035459 = 3053189) B3053189
theorem B2412355 : Blo 1429534 2412355 := bstep (se 1 (by rfl) ⟨1809266, by rfl⟩ : syracuseStep 2412355 = 3618533) B3618533
theorem B8146757 : Blo 1429534 8146757 := bstep (se 4 (by rfl) ⟨763758, by rfl⟩ : syracuseStep 8146757 = 1527517) B1527517
theorem B1609555 : Blo 1429534 1609555 := bstep (se 1 (by rfl) ⟨1207166, by rfl⟩ : syracuseStep 1609555 = 2414333) B2414333
theorem B4075373 : Blo 1429534 4075373 := bstep (se 3 (by rfl) ⟨764132, by rfl⟩ : syracuseStep 4075373 = 1528265) B1528265
theorem B7245773 : Blo 1429534 7245773 := bstep (se 3 (by rfl) ⟨1358582, by rfl⟩ : syracuseStep 7245773 = 2717165) B2717165
theorem B2412497 : Blo 1429534 2412497 := bstep (se 2 (by rfl) ⟨904686, by rfl⟩ : syracuseStep 2412497 = 1809373) B1809373
theorem B2715601 : Blo 1429534 2715601 := bstep (se 2 (by rfl) ⟨1018350, by rfl⟩ : syracuseStep 2715601 = 2036701) B2036701
theorem B1609699 : Blo 1429534 1609699 := bstep (se 1 (by rfl) ⟨1207274, by rfl⟩ : syracuseStep 1609699 = 2414549) B2414549
theorem B4829165 : Blo 1429534 4829165 := bstep (se 3 (by rfl) ⟨905468, by rfl⟩ : syracuseStep 4829165 = 1810937) B1810937
theorem B1429539 : Blo 1429534 1429539 := bstep (se 1 (by rfl) ⟨1072154, by rfl⟩ : syracuseStep 1429539 = 2144309) B2144309
theorem B4829219 : Blo 1429534 4829219 := bstep (se 1 (by rfl) ⟨3621914, by rfl⟩ : syracuseStep 4829219 = 7243829) B7243829
theorem B4075555 : Blo 1429534 4075555 := bstep (se 1 (by rfl) ⟨3056666, by rfl⟩ : syracuseStep 4075555 = 6113333) B6113333
theorem B1429555 : Blo 1429534 1429555 := bstep (se 1 (by rfl) ⟨1072166, by rfl⟩ : syracuseStep 1429555 = 2144333) B2144333
theorem B1527859 : Blo 1429534 1527859 := bstep (se 1 (by rfl) ⟨1145894, by rfl⟩ : syracuseStep 1527859 = 2291789) B2291789
theorem B1429571 : Blo 1429534 1429571 := bstep (se 1 (by rfl) ⟨1072178, by rfl⟩ : syracuseStep 1429571 = 2144357) B2144357
theorem B2412625 : Blo 1429534 2412625 := bstep (se 2 (by rfl) ⟨904734, by rfl⟩ : syracuseStep 2412625 = 1809469) B1809469
theorem B1429587 : Blo 1429534 1429587 := bstep (se 1 (by rfl) ⟨1072190, by rfl⟩ : syracuseStep 1429587 = 2144381) B2144381
theorem B1429603 : Blo 1429534 1429603 := bstep (se 1 (by rfl) ⟨1072202, by rfl⟩ : syracuseStep 1429603 = 2144405) B2144405
theorem B2715761 : Blo 1429534 2715761 := bstep (se 2 (by rfl) ⟨1018410, by rfl⟩ : syracuseStep 2715761 = 2036821) B2036821
theorem B1429619 : Blo 1429534 1429619 := bstep (se 1 (by rfl) ⟨1072214, by rfl⟩ : syracuseStep 1429619 = 2144429) B2144429
theorem B2412659 : Blo 1429534 2412659 := bstep (se 1 (by rfl) ⟨1809494, by rfl⟩ : syracuseStep 2412659 = 3618989) B3618989
theorem B1609843 : Blo 1429534 1609843 := bstep (se 1 (by rfl) ⟨1207382, by rfl⟩ : syracuseStep 1609843 = 2414765) B2414765
theorem B1429635 : Blo 1429534 1429635 := bstep (se 1 (by rfl) ⟨1072226, by rfl⟩ : syracuseStep 1429635 = 2144453) B2144453
theorem B1429651 : Blo 1429534 1429651 := bstep (se 1 (by rfl) ⟨1072238, by rfl⟩ : syracuseStep 1429651 = 2144477) B2144477
theorem B1429667 : Blo 1429534 1429667 := bstep (se 1 (by rfl) ⟨1072250, by rfl⟩ : syracuseStep 1429667 = 2144501) B2144501
theorem B1429683 : Blo 1429534 1429683 := bstep (se 1 (by rfl) ⟨1072262, by rfl⟩ : syracuseStep 1429683 = 2144525) B2144525
theorem B1429699 : Blo 1429534 1429699 := bstep (se 1 (by rfl) ⟨1072274, by rfl⟩ : syracuseStep 1429699 = 2144549) B2144549
theorem B1429715 : Blo 1429534 1429715 := bstep (se 1 (by rfl) ⟨1072286, by rfl⟩ : syracuseStep 1429715 = 2144573) B2144573
theorem B1429731 : Blo 1429534 1429731 := bstep (se 1 (by rfl) ⟨1072298, by rfl⟩ : syracuseStep 1429731 = 2144597) B2144597
theorem B1429747 : Blo 1429534 1429747 := bstep (se 1 (by rfl) ⟨1072310, by rfl⟩ : syracuseStep 1429747 = 2144621) B2144621
theorem B2412787 : Blo 1429534 2412787 := bstep (se 1 (by rfl) ⟨1809590, by rfl⟩ : syracuseStep 2412787 = 3619181) B3619181
theorem B2035955 : Blo 1429534 2035955 := bstep (se 1 (by rfl) ⟨1526966, by rfl⟩ : syracuseStep 2035955 = 3053933) B3053933
theorem B1429763 : Blo 1429534 1429763 := bstep (se 1 (by rfl) ⟨1072322, by rfl⟩ : syracuseStep 1429763 = 2144645) B2144645
theorem B1609987 : Blo 1429534 1609987 := bstep (se 1 (by rfl) ⟨1207490, by rfl⟩ : syracuseStep 1609987 = 2414981) B2414981
theorem B8147213 : Blo 1429534 8147213 := bstep (se 3 (by rfl) ⟨1527602, by rfl⟩ : syracuseStep 8147213 = 3055205) B3055205
theorem B1429779 : Blo 1429534 1429779 := bstep (se 1 (by rfl) ⟨1072334, by rfl⟩ : syracuseStep 1429779 = 2144669) B2144669
theorem B1429795 : Blo 1429534 1429795 := bstep (se 1 (by rfl) ⟨1072346, by rfl⟩ : syracuseStep 1429795 = 2144693) B2144693
theorem B4829489 : Blo 1429534 4829489 := bstep (se 2 (by rfl) ⟨1811058, by rfl⟩ : syracuseStep 4829489 = 3622117) B3622117
theorem B1429811 : Blo 1429534 1429811 := bstep (se 1 (by rfl) ⟨1072358, by rfl⟩ : syracuseStep 1429811 = 2144717) B2144717
theorem B1429827 : Blo 1429534 1429827 := bstep (se 1 (by rfl) ⟨1072370, by rfl⟩ : syracuseStep 1429827 = 2144741) B2144741
theorem B1429843 : Blo 1429534 1429843 := bstep (se 1 (by rfl) ⟨1072382, by rfl⟩ : syracuseStep 1429843 = 2144765) B2144765
theorem B1429859 : Blo 1429534 1429859 := bstep (se 1 (by rfl) ⟨1072394, by rfl⟩ : syracuseStep 1429859 = 2144789) B2144789
theorem B2355569 : Blo 1429534 2355569 := bstep (se 2 (by rfl) ⟨883338, by rfl⟩ : syracuseStep 2355569 = 1766677) B1766677
theorem B1429875 : Blo 1429534 1429875 := bstep (se 1 (by rfl) ⟨1072406, by rfl⟩ : syracuseStep 1429875 = 2144813) B2144813
theorem B2412929 : Blo 1429534 2412929 := bstep (se 2 (by rfl) ⟨904848, by rfl⟩ : syracuseStep 2412929 = 1809697) B1809697
theorem B1429891 : Blo 1429534 1429891 := bstep (se 1 (by rfl) ⟨1072418, by rfl⟩ : syracuseStep 1429891 = 2144837) B2144837
theorem B1429907 : Blo 1429534 1429907 := bstep (se 1 (by rfl) ⟨1072430, by rfl⟩ : syracuseStep 1429907 = 2144861) B2144861
theorem B1610131 : Blo 1429534 1610131 := bstep (se 1 (by rfl) ⟨1207598, by rfl⟩ : syracuseStep 1610131 = 2415197) B2415197
theorem B1429923 : Blo 1429534 1429923 := bstep (se 1 (by rfl) ⟨1072442, by rfl⟩ : syracuseStep 1429923 = 2144885) B2144885
theorem B2290097 : Blo 1429534 2290097 := bstep (se 2 (by rfl) ⟨858786, by rfl⟩ : syracuseStep 2290097 = 1717573) B1717573
theorem B1429939 : Blo 1429534 1429939 := bstep (se 1 (by rfl) ⟨1072454, by rfl⟩ : syracuseStep 1429939 = 2144909) B2144909
theorem B1429955 : Blo 1429534 1429955 := bstep (se 1 (by rfl) ⟨1072466, by rfl⟩ : syracuseStep 1429955 = 2144933) B2144933
theorem B1429971 : Blo 1429534 1429971 := bstep (se 1 (by rfl) ⟨1072478, by rfl⟩ : syracuseStep 1429971 = 2144957) B2144957
theorem B1429987 : Blo 1429534 1429987 := bstep (se 1 (by rfl) ⟨1072490, by rfl⟩ : syracuseStep 1429987 = 2144981) B2144981
theorem B1430003 : Blo 1429534 1430003 := bstep (se 1 (by rfl) ⟨1072502, by rfl⟩ : syracuseStep 1430003 = 2145005) B2145005
theorem B2413057 : Blo 1429534 2413057 := bstep (se 2 (by rfl) ⟨904896, by rfl⟩ : syracuseStep 2413057 = 1809793) B1809793
theorem B1430019 : Blo 1429534 1430019 := bstep (se 1 (by rfl) ⟨1072514, by rfl⟩ : syracuseStep 1430019 = 2145029) B2145029
theorem B2716163 : Blo 1429534 2716163 := bstep (se 1 (by rfl) ⟨2037122, by rfl⟩ : syracuseStep 2716163 = 4074245) B4074245
theorem B4076045 : Blo 1429534 4076045 := bstep (se 3 (by rfl) ⟨764258, by rfl⟩ : syracuseStep 4076045 = 1528517) B1528517
theorem B1430035 : Blo 1429534 1430035 := bstep (se 1 (by rfl) ⟨1072526, by rfl⟩ : syracuseStep 1430035 = 2145053) B2145053
theorem B2413091 : Blo 1429534 2413091 := bstep (se 1 (by rfl) ⟨1809818, by rfl⟩ : syracuseStep 2413091 = 3619637) B3619637
theorem B1430051 : Blo 1429534 1430051 := bstep (se 1 (by rfl) ⟨1072538, by rfl⟩ : syracuseStep 1430051 = 2145077) B2145077
theorem B1610275 : Blo 1429534 1610275 := bstep (se 1 (by rfl) ⟨1207706, by rfl⟩ : syracuseStep 1610275 = 2415413) B2415413
theorem B1430067 : Blo 1429534 1430067 := bstep (se 1 (by rfl) ⟨1072550, by rfl⟩ : syracuseStep 1430067 = 2145101) B2145101
theorem B1430083 : Blo 1429534 1430083 := bstep (se 1 (by rfl) ⟨1072562, by rfl⟩ : syracuseStep 1430083 = 2145125) B2145125
theorem B1430099 : Blo 1429534 1430099 := bstep (se 1 (by rfl) ⟨1072574, by rfl⟩ : syracuseStep 1430099 = 2145149) B2145149
theorem B1430115 : Blo 1429534 1430115 := bstep (se 1 (by rfl) ⟨1072586, by rfl⟩ : syracuseStep 1430115 = 2145173) B2145173
theorem B1430131 : Blo 1429534 1430131 := bstep (se 1 (by rfl) ⟨1072598, by rfl⟩ : syracuseStep 1430131 = 2145197) B2145197
theorem B1430147 : Blo 1429534 1430147 := bstep (se 1 (by rfl) ⟨1072610, by rfl⟩ : syracuseStep 1430147 = 2145221) B2145221
theorem B1430163 : Blo 1429534 1430163 := bstep (se 1 (by rfl) ⟨1072622, by rfl⟩ : syracuseStep 1430163 = 2145245) B2145245
theorem B2413219 : Blo 1429534 2413219 := bstep (se 1 (by rfl) ⟨1809914, by rfl⟩ : syracuseStep 2413219 = 3619829) B3619829
theorem B1430179 : Blo 1429534 1430179 := bstep (se 1 (by rfl) ⟨1072634, by rfl⟩ : syracuseStep 1430179 = 2145269) B2145269
theorem B7238321 : Blo 1429534 7238321 := bstep (se 2 (by rfl) ⟨2714370, by rfl⟩ : syracuseStep 7238321 = 5428741) B5428741
theorem B1430195 : Blo 1429534 1430195 := bstep (se 1 (by rfl) ⟨1072646, by rfl⟩ : syracuseStep 1430195 = 2145293) B2145293
theorem B1610419 : Blo 1429534 1610419 := bstep (se 1 (by rfl) ⟨1207814, by rfl⟩ : syracuseStep 1610419 = 2415629) B2415629
theorem B1430211 : Blo 1429534 1430211 := bstep (se 1 (by rfl) ⟨1072658, by rfl⟩ : syracuseStep 1430211 = 2145317) B2145317
theorem B4895437 : Blo 1429534 4895437 := bstep (se 3 (by rfl) ⟨917894, by rfl⟩ : syracuseStep 4895437 = 1835789) B1835789
theorem B1430227 : Blo 1429534 1430227 := bstep (se 1 (by rfl) ⟨1072670, by rfl⟩ : syracuseStep 1430227 = 2145341) B2145341
theorem B2446049 : Blo 1429534 2446049 := bstep (se 2 (by rfl) ⟨917268, by rfl⟩ : syracuseStep 2446049 = 1834537) B1834537
theorem B1430243 : Blo 1429534 1430243 := bstep (se 1 (by rfl) ⟨1072682, by rfl⟩ : syracuseStep 1430243 = 2145365) B2145365
theorem B1430259 : Blo 1429534 1430259 := bstep (se 1 (by rfl) ⟨1072694, by rfl⟩ : syracuseStep 1430259 = 2145389) B2145389
theorem B1430275 : Blo 1429534 1430275 := bstep (se 1 (by rfl) ⟨1072706, by rfl⟩ : syracuseStep 1430275 = 2145413) B2145413
theorem B1430291 : Blo 1429534 1430291 := bstep (se 1 (by rfl) ⟨1072718, by rfl⟩ : syracuseStep 1430291 = 2145437) B2145437
theorem B1430307 : Blo 1429534 1430307 := bstep (se 1 (by rfl) ⟨1072730, by rfl⟩ : syracuseStep 1430307 = 2145461) B2145461
theorem B2413361 : Blo 1429534 2413361 := bstep (se 2 (by rfl) ⟨905010, by rfl⟩ : syracuseStep 2413361 = 1810021) B1810021
theorem B2093873 : Blo 1429534 2093873 := bstep (se 2 (by rfl) ⟨785202, by rfl⟩ : syracuseStep 2093873 = 1570405) B1570405
theorem B1430323 : Blo 1429534 1430323 := bstep (se 1 (by rfl) ⟨1072742, by rfl⟩ : syracuseStep 1430323 = 2145485) B2145485
theorem B1430339 : Blo 1429534 1430339 := bstep (se 1 (by rfl) ⟨1072754, by rfl⟩ : syracuseStep 1430339 = 2145509) B2145509
theorem B4830029 : Blo 1429534 4830029 := bstep (se 3 (by rfl) ⟨905630, by rfl⟩ : syracuseStep 4830029 = 1811261) B1811261
theorem B1430355 : Blo 1429534 1430355 := bstep (se 1 (by rfl) ⟨1072766, by rfl⟩ : syracuseStep 1430355 = 2145533) B2145533
theorem B1430371 : Blo 1429534 1430371 := bstep (se 1 (by rfl) ⟨1072778, by rfl⟩ : syracuseStep 1430371 = 2145557) B2145557
theorem B2036593 : Blo 1429534 2036593 := bstep (se 2 (by rfl) ⟨763722, by rfl⟩ : syracuseStep 2036593 = 1527445) B1527445
theorem B1430387 : Blo 1429534 1430387 := bstep (se 1 (by rfl) ⟨1072790, by rfl⟩ : syracuseStep 1430387 = 2145581) B2145581
theorem B1430403 : Blo 1429534 1430403 := bstep (se 1 (by rfl) ⟨1072802, by rfl⟩ : syracuseStep 1430403 = 2145605) B2145605
theorem B4830083 : Blo 1429534 4830083 := bstep (se 1 (by rfl) ⟨3622562, by rfl⟩ : syracuseStep 4830083 = 7245125) B7245125
theorem B1430419 : Blo 1429534 1430419 := bstep (se 1 (by rfl) ⟨1072814, by rfl⟩ : syracuseStep 1430419 = 2145629) B2145629
theorem B1430435 : Blo 1429534 1430435 := bstep (se 1 (by rfl) ⟨1072826, by rfl⟩ : syracuseStep 1430435 = 2145653) B2145653
theorem B2413489 : Blo 1429534 2413489 := bstep (se 2 (by rfl) ⟨905058, by rfl⟩ : syracuseStep 2413489 = 1810117) B1810117
theorem B1430451 : Blo 1429534 1430451 := bstep (se 1 (by rfl) ⟨1072838, by rfl⟩ : syracuseStep 1430451 = 2145677) B2145677
theorem B1430467 : Blo 1429534 1430467 := bstep (se 1 (by rfl) ⟨1072850, by rfl⟩ : syracuseStep 1430467 = 2145701) B2145701
theorem B4584397 : Blo 1429534 4584397 := bstep (se 3 (by rfl) ⟨859574, by rfl⟩ : syracuseStep 4584397 = 1719149) B1719149
theorem B2413523 : Blo 1429534 2413523 := bstep (se 1 (by rfl) ⟨1810142, by rfl⟩ : syracuseStep 2413523 = 3620285) B3620285
theorem B1430483 : Blo 1429534 1430483 := bstep (se 1 (by rfl) ⟨1072862, by rfl⟩ : syracuseStep 1430483 = 2145725) B2145725
theorem B1430499 : Blo 1429534 1430499 := bstep (se 1 (by rfl) ⟨1072874, by rfl⟩ : syracuseStep 1430499 = 2145749) B2145749
theorem B1430515 : Blo 1429534 1430515 := bstep (se 1 (by rfl) ⟨1072886, by rfl⟩ : syracuseStep 1430515 = 2145773) B2145773
theorem B1430531 : Blo 1429534 1430531 := bstep (se 1 (by rfl) ⟨1072898, by rfl⟩ : syracuseStep 1430531 = 2145797) B2145797
theorem B13751309 : Blo 1429534 13751309 := bstep (se 3 (by rfl) ⟨2578370, by rfl⟩ : syracuseStep 13751309 = 5156741) B5156741
theorem B1430547 : Blo 1429534 1430547 := bstep (se 1 (by rfl) ⟨1072910, by rfl⟩ : syracuseStep 1430547 = 2145821) B2145821
theorem B1430563 : Blo 1429534 1430563 := bstep (se 1 (by rfl) ⟨1072922, by rfl⟩ : syracuseStep 1430563 = 2145845) B2145845
theorem B1430579 : Blo 1429534 1430579 := bstep (se 1 (by rfl) ⟨1072934, by rfl⟩ : syracuseStep 1430579 = 2145869) B2145869
theorem B1430595 : Blo 1429534 1430595 := bstep (se 1 (by rfl) ⟨1072946, by rfl⟩ : syracuseStep 1430595 = 2145893) B2145893
theorem B2413651 : Blo 1429534 2413651 := bstep (se 1 (by rfl) ⟨1810238, by rfl⟩ : syracuseStep 2413651 = 3620477) B3620477
theorem B1430611 : Blo 1429534 1430611 := bstep (se 1 (by rfl) ⟨1072958, by rfl⟩ : syracuseStep 1430611 = 2145917) B2145917
theorem B1430627 : Blo 1429534 1430627 := bstep (se 1 (by rfl) ⟨1072970, by rfl⟩ : syracuseStep 1430627 = 2145941) B2145941
theorem B1430643 : Blo 1429534 1430643 := bstep (se 1 (by rfl) ⟨1072982, by rfl⟩ : syracuseStep 1430643 = 2145965) B2145965
theorem B1430659 : Blo 1429534 1430659 := bstep (se 1 (by rfl) ⟨1072994, by rfl⟩ : syracuseStep 1430659 = 2145989) B2145989
theorem B8696965 : Blo 1429534 8696965 := bstep (se 4 (by rfl) ⟨815340, by rfl⟩ : syracuseStep 8696965 = 1630681) B1630681
theorem B4830353 : Blo 1429534 4830353 := bstep (se 2 (by rfl) ⟨1811382, by rfl⟩ : syracuseStep 4830353 = 3622765) B3622765
theorem B1430675 : Blo 1429534 1430675 := bstep (se 1 (by rfl) ⟨1073006, by rfl⟩ : syracuseStep 1430675 = 2146013) B2146013
theorem B1430691 : Blo 1429534 1430691 := bstep (se 1 (by rfl) ⟨1073018, by rfl⟩ : syracuseStep 1430691 = 2146037) B2146037
theorem B1430707 : Blo 1429534 1430707 := bstep (se 1 (by rfl) ⟨1073030, by rfl⟩ : syracuseStep 1430707 = 2146061) B2146061
theorem B2036929 : Blo 1429534 2036929 := bstep (se 2 (by rfl) ⟨763848, by rfl⟩ : syracuseStep 2036929 = 1527697) B1527697
theorem B1430723 : Blo 1429534 1430723 := bstep (se 1 (by rfl) ⟨1073042, by rfl⟩ : syracuseStep 1430723 = 2146085) B2146085
theorem B1430739 : Blo 1429534 1430739 := bstep (se 1 (by rfl) ⟨1073054, by rfl⟩ : syracuseStep 1430739 = 2146109) B2146109
theorem B2413793 : Blo 1429534 2413793 := bstep (se 2 (by rfl) ⟨905172, by rfl⟩ : syracuseStep 2413793 = 1810345) B1810345
theorem B1430755 : Blo 1429534 1430755 := bstep (se 1 (by rfl) ⟨1073066, by rfl⟩ : syracuseStep 1430755 = 2146133) B2146133
theorem B4347121 : Blo 1429534 4347121 := bstep (se 2 (by rfl) ⟨1630170, by rfl⟩ : syracuseStep 4347121 = 3260341) B3260341
theorem B1430771 : Blo 1429534 1430771 := bstep (se 1 (by rfl) ⟨1073078, by rfl⟩ : syracuseStep 1430771 = 2146157) B2146157
theorem B1430787 : Blo 1429534 1430787 := bstep (se 1 (by rfl) ⟨1073090, by rfl⟩ : syracuseStep 1430787 = 2146181) B2146181
theorem B1430803 : Blo 1429534 1430803 := bstep (se 1 (by rfl) ⟨1073102, by rfl⟩ : syracuseStep 1430803 = 2146205) B2146205
theorem B1430819 : Blo 1429534 1430819 := bstep (se 1 (by rfl) ⟨1073114, by rfl⟩ : syracuseStep 1430819 = 2146229) B2146229
theorem B3216689 : Blo 1429534 3216689 := bstep (se 2 (by rfl) ⟨1206258, by rfl⟩ : syracuseStep 3216689 = 2412517) B2412517
theorem B5428529 : Blo 1429534 5428529 := bstep (se 2 (by rfl) ⟨2035698, by rfl⟩ : syracuseStep 5428529 = 4071397) B4071397
theorem B1430835 : Blo 1429534 1430835 := bstep (se 1 (by rfl) ⟨1073126, by rfl⟩ : syracuseStep 1430835 = 2146253) B2146253
theorem B33502517 : Blo 1429534 33502517 := bstep (se 5 (by rfl) ⟨1570430, by rfl⟩ : syracuseStep 33502517 = 3140861) B3140861
theorem B3216707 : Blo 1429534 3216707 := bstep (se 1 (by rfl) ⟨2412530, by rfl⟩ : syracuseStep 3216707 = 4825061) B4825061
theorem B1430851 : Blo 1429534 1430851 := bstep (se 1 (by rfl) ⟨1073138, by rfl⟩ : syracuseStep 1430851 = 2146277) B2146277
theorem B1430867 : Blo 1429534 1430867 := bstep (se 1 (by rfl) ⟨1073150, by rfl⟩ : syracuseStep 1430867 = 2146301) B2146301
theorem B2413921 : Blo 1429534 2413921 := bstep (se 2 (by rfl) ⟨905220, by rfl⟩ : syracuseStep 2413921 = 1810441) B1810441
theorem B1430883 : Blo 1429534 1430883 := bstep (se 1 (by rfl) ⟨1073162, by rfl⟩ : syracuseStep 1430883 = 2146325) B2146325
theorem B1430899 : Blo 1429534 1430899 := bstep (se 1 (by rfl) ⟨1073174, by rfl⟩ : syracuseStep 1430899 = 2146349) B2146349
theorem B2413955 : Blo 1429534 2413955 := bstep (se 1 (by rfl) ⟨1810466, by rfl⟩ : syracuseStep 2413955 = 3620933) B3620933
theorem B1430915 : Blo 1429534 1430915 := bstep (se 1 (by rfl) ⟨1073186, by rfl⟩ : syracuseStep 1430915 = 2146373) B2146373
theorem B2717059 : Blo 1429534 2717059 := bstep (se 1 (by rfl) ⟨2037794, by rfl⟩ : syracuseStep 2717059 = 4075589) B4075589
theorem B1430931 : Blo 1429534 1430931 := bstep (se 1 (by rfl) ⟨1073198, by rfl⟩ : syracuseStep 1430931 = 2146397) B2146397
theorem B1430947 : Blo 1429534 1430947 := bstep (se 1 (by rfl) ⟨1073210, by rfl⟩ : syracuseStep 1430947 = 2146421) B2146421
theorem B1430963 : Blo 1429534 1430963 := bstep (se 1 (by rfl) ⟨1073222, by rfl⟩ : syracuseStep 1430963 = 2146445) B2146445
theorem B1430979 : Blo 1429534 1430979 := bstep (se 1 (by rfl) ⟨1073234, by rfl⟩ : syracuseStep 1430979 = 2146469) B2146469
theorem B1430995 : Blo 1429534 1430995 := bstep (se 1 (by rfl) ⟨1073246, by rfl⟩ : syracuseStep 1430995 = 2146493) B2146493
theorem B1431011 : Blo 1429534 1431011 := bstep (se 1 (by rfl) ⟨1073258, by rfl⟩ : syracuseStep 1431011 = 2146517) B2146517
theorem B1431027 : Blo 1429534 1431027 := bstep (se 1 (by rfl) ⟨1073270, by rfl⟩ : syracuseStep 1431027 = 2146541) B2146541
theorem B2414083 : Blo 1429534 2414083 := bstep (se 1 (by rfl) ⟨1810562, by rfl⟩ : syracuseStep 2414083 = 3621125) B3621125
theorem B1431043 : Blo 1429534 1431043 := bstep (se 1 (by rfl) ⟨1073282, by rfl⟩ : syracuseStep 1431043 = 2146565) B2146565
theorem B1431059 : Blo 1429534 1431059 := bstep (se 1 (by rfl) ⟨1073294, by rfl⟩ : syracuseStep 1431059 = 2146589) B2146589
theorem B1431075 : Blo 1429534 1431075 := bstep (se 1 (by rfl) ⟨1073306, by rfl⟩ : syracuseStep 1431075 = 2146613) B2146613
theorem B2717219 : Blo 1429534 2717219 := bstep (se 1 (by rfl) ⟨2037914, by rfl⟩ : syracuseStep 2717219 = 4075829) B4075829
theorem B1431091 : Blo 1429534 1431091 := bstep (se 1 (by rfl) ⟨1073318, by rfl⟩ : syracuseStep 1431091 = 2146637) B2146637
theorem B1431107 : Blo 1429534 1431107 := bstep (se 1 (by rfl) ⟨1073330, by rfl⟩ : syracuseStep 1431107 = 2146661) B2146661
theorem B3216977 : Blo 1429534 3216977 := bstep (se 2 (by rfl) ⟨1206366, by rfl⟩ : syracuseStep 3216977 = 2412733) B2412733
theorem B1431123 : Blo 1429534 1431123 := bstep (se 1 (by rfl) ⟨1073342, by rfl⟩ : syracuseStep 1431123 = 2146685) B2146685
theorem B3053155 : Blo 1429534 3053155 := bstep (se 1 (by rfl) ⟨2289866, by rfl⟩ : syracuseStep 3053155 = 4579733) B4579733
theorem B3216995 : Blo 1429534 3216995 := bstep (se 1 (by rfl) ⟨2412746, by rfl⟩ : syracuseStep 3216995 = 4825493) B4825493
theorem B1431139 : Blo 1429534 1431139 := bstep (se 1 (by rfl) ⟨1073354, by rfl⟩ : syracuseStep 1431139 = 2146709) B2146709
theorem B1431155 : Blo 1429534 1431155 := bstep (se 1 (by rfl) ⟨1073366, by rfl⟩ : syracuseStep 1431155 = 2146733) B2146733
theorem B1431171 : Blo 1429534 1431171 := bstep (se 1 (by rfl) ⟨1073378, by rfl⟩ : syracuseStep 1431171 = 2146757) B2146757
theorem B2414225 : Blo 1429534 2414225 := bstep (se 2 (by rfl) ⟨905334, by rfl⟩ : syracuseStep 2414225 = 1810669) B1810669
theorem B1431187 : Blo 1429534 1431187 := bstep (se 1 (by rfl) ⟨1073390, by rfl⟩ : syracuseStep 1431187 = 2146781) B2146781
theorem B1431203 : Blo 1429534 1431203 := bstep (se 1 (by rfl) ⟨1073402, by rfl⟩ : syracuseStep 1431203 = 2146805) B2146805
theorem B4830893 : Blo 1429534 4830893 := bstep (se 3 (by rfl) ⟨905792, by rfl⟩ : syracuseStep 4830893 = 1811585) B1811585
theorem B1431219 : Blo 1429534 1431219 := bstep (se 1 (by rfl) ⟨1073414, by rfl⟩ : syracuseStep 1431219 = 2146829) B2146829
theorem B1431235 : Blo 1429534 1431235 := bstep (se 1 (by rfl) ⟨1073426, by rfl⟩ : syracuseStep 1431235 = 2146853) B2146853
theorem B1431251 : Blo 1429534 1431251 := bstep (se 1 (by rfl) ⟨1073438, by rfl⟩ : syracuseStep 1431251 = 2146877) B2146877
theorem B1431267 : Blo 1429534 1431267 := bstep (se 1 (by rfl) ⟨1073450, by rfl⟩ : syracuseStep 1431267 = 2146901) B2146901
theorem B4830947 : Blo 1429534 4830947 := bstep (se 1 (by rfl) ⟨3623210, by rfl⟩ : syracuseStep 4830947 = 7246421) B7246421
theorem B1431283 : Blo 1429534 1431283 := bstep (se 1 (by rfl) ⟨1073462, by rfl⟩ : syracuseStep 1431283 = 2146925) B2146925
theorem B3864323 : Blo 1429534 3864323 := bstep (se 1 (by rfl) ⟨2898242, by rfl⟩ : syracuseStep 3864323 = 5796485) B5796485
theorem B1431299 : Blo 1429534 1431299 := bstep (se 1 (by rfl) ⟨1073474, by rfl⟩ : syracuseStep 1431299 = 2146949) B2146949
theorem B2414353 : Blo 1429534 2414353 := bstep (se 2 (by rfl) ⟨905382, by rfl⟩ : syracuseStep 2414353 = 1810765) B1810765
theorem B2037521 : Blo 1429534 2037521 := bstep (se 2 (by rfl) ⟨764070, by rfl⟩ : syracuseStep 2037521 = 1528141) B1528141
theorem B1431315 : Blo 1429534 1431315 := bstep (se 1 (by rfl) ⟨1073486, by rfl⟩ : syracuseStep 1431315 = 2146973) B2146973
theorem B1431331 : Blo 1429534 1431331 := bstep (se 1 (by rfl) ⟨1073498, by rfl⟩ : syracuseStep 1431331 = 2146997) B2146997
theorem B2291507 : Blo 1429534 2291507 := bstep (se 1 (by rfl) ⟨1718630, by rfl⟩ : syracuseStep 2291507 = 3437261) B3437261
theorem B2414387 : Blo 1429534 2414387 := bstep (se 1 (by rfl) ⟨1810790, by rfl⟩ : syracuseStep 2414387 = 3621581) B3621581
theorem B16512821 : Blo 1429534 16512821 := bstep (se 5 (by rfl) ⟨774038, by rfl⟩ : syracuseStep 16512821 = 1548077) B1548077
theorem B1431347 : Blo 1429534 1431347 := bstep (se 1 (by rfl) ⟨1073510, by rfl⟩ : syracuseStep 1431347 = 2147021) B2147021
theorem B4962115 : Blo 1429534 4962115 := bstep (se 1 (by rfl) ⟨3721586, by rfl⟩ : syracuseStep 4962115 = 7443173) B7443173
theorem B1431363 : Blo 1429534 1431363 := bstep (se 1 (by rfl) ⟨1073522, by rfl⟩ : syracuseStep 1431363 = 2147045) B2147045
theorem B2324305 : Blo 1429534 2324305 := bstep (se 2 (by rfl) ⟨871614, by rfl⟩ : syracuseStep 2324305 = 1743229) B1743229
theorem B1431379 : Blo 1429534 1431379 := bstep (se 1 (by rfl) ⟨1073534, by rfl⟩ : syracuseStep 1431379 = 2147069) B2147069
theorem B1431395 : Blo 1429534 1431395 := bstep (se 1 (by rfl) ⟨1073546, by rfl⟩ : syracuseStep 1431395 = 2147093) B2147093
theorem B3217265 : Blo 1429534 3217265 := bstep (se 2 (by rfl) ⟨1206474, by rfl⟩ : syracuseStep 3217265 = 2412949) B2412949
theorem B1431411 : Blo 1429534 1431411 := bstep (se 1 (by rfl) ⟨1073558, by rfl⟩ : syracuseStep 1431411 = 2147117) B2147117
theorem B3217283 : Blo 1429534 3217283 := bstep (se 1 (by rfl) ⟨2412962, by rfl⟩ : syracuseStep 3217283 = 4825925) B4825925
theorem B1431427 : Blo 1429534 1431427 := bstep (se 1 (by rfl) ⟨1073570, by rfl⟩ : syracuseStep 1431427 = 2147141) B2147141
theorem B1431443 : Blo 1429534 1431443 := bstep (se 1 (by rfl) ⟨1073582, by rfl⟩ : syracuseStep 1431443 = 2147165) B2147165
theorem B1431459 : Blo 1429534 1431459 := bstep (se 1 (by rfl) ⟨1073594, by rfl⟩ : syracuseStep 1431459 = 2147189) B2147189
theorem B2414515 : Blo 1429534 2414515 := bstep (se 1 (by rfl) ⟨1810886, by rfl⟩ : syracuseStep 2414515 = 3621773) B3621773
theorem B1431475 : Blo 1429534 1431475 := bstep (se 1 (by rfl) ⟨1073606, by rfl⟩ : syracuseStep 1431475 = 2147213) B2147213
theorem B1431491 : Blo 1429534 1431491 := bstep (se 1 (by rfl) ⟨1073618, by rfl⟩ : syracuseStep 1431491 = 2147237) B2147237
theorem B35739589 : Blo 1429534 35739589 := bstep (se 4 (by rfl) ⟨3350586, by rfl⟩ : syracuseStep 35739589 = 6701173) B6701173
theorem B1431507 : Blo 1429534 1431507 := bstep (se 1 (by rfl) ⟨1073630, by rfl⟩ : syracuseStep 1431507 = 2147261) B2147261
theorem B1431523 : Blo 1429534 1431523 := bstep (se 1 (by rfl) ⟨1073642, by rfl⟩ : syracuseStep 1431523 = 2147285) B2147285
theorem B4831217 : Blo 1429534 4831217 := bstep (se 2 (by rfl) ⟨1811706, by rfl⟩ : syracuseStep 4831217 = 3623413) B3623413
theorem B2291699 : Blo 1429534 2291699 := bstep (se 1 (by rfl) ⟨1718774, by rfl⟩ : syracuseStep 2291699 = 3437549) B3437549
theorem B2144321 : Blo 1429534 2144321 := bstep (se 2 (by rfl) ⟨804120, by rfl⟩ : syracuseStep 2144321 = 1608241) B1608241
theorem B2414657 : Blo 1429534 2414657 := bstep (se 2 (by rfl) ⟨905496, by rfl⟩ : syracuseStep 2414657 = 1810993) B1810993
theorem B2144339 : Blo 1429534 2144339 := bstep (se 1 (by rfl) ⟨1608254, by rfl⟩ : syracuseStep 2144339 = 3216509) B3216509
theorem B7239779 : Blo 1429534 7239779 := bstep (se 1 (by rfl) ⟨5429834, by rfl⟩ : syracuseStep 7239779 = 10859669) B10859669
theorem B6109283 : Blo 1429534 6109283 := bstep (se 1 (by rfl) ⟨4581962, by rfl⟩ : syracuseStep 6109283 = 9163925) B9163925
theorem B2144369 : Blo 1429534 2144369 := bstep (se 2 (by rfl) ⟨804138, by rfl⟩ : syracuseStep 2144369 = 1608277) B1608277
theorem B2144387 : Blo 1429534 2144387 := bstep (se 1 (by rfl) ⟨1608290, by rfl⟩ : syracuseStep 2144387 = 3216581) B3216581
theorem B5961869 : Blo 1429534 5961869 := bstep (se 3 (by rfl) ⟨1117850, by rfl⟩ : syracuseStep 5961869 = 2235701) B2235701
theorem B3217553 : Blo 1429534 3217553 := bstep (se 2 (by rfl) ⟨1206582, by rfl⟩ : syracuseStep 3217553 = 2413165) B2413165
theorem B2144417 : Blo 1429534 2144417 := bstep (se 2 (by rfl) ⟨804156, by rfl⟩ : syracuseStep 2144417 = 1608313) B1608313
theorem B3217571 : Blo 1429534 3217571 := bstep (se 1 (by rfl) ⟨2413178, by rfl⟩ : syracuseStep 3217571 = 4826357) B4826357
theorem B2144435 : Blo 1429534 2144435 := bstep (se 1 (by rfl) ⟨1608326, by rfl⟩ : syracuseStep 2144435 = 3216653) B3216653
theorem B2414785 : Blo 1429534 2414785 := bstep (se 2 (by rfl) ⟨905544, by rfl⟩ : syracuseStep 2414785 = 1811089) B1811089
theorem B2144465 : Blo 1429534 2144465 := bstep (se 2 (by rfl) ⟨804174, by rfl⟩ : syracuseStep 2144465 = 1608349) B1608349
theorem B2144483 : Blo 1429534 2144483 := bstep (se 1 (by rfl) ⟨1608362, by rfl⟩ : syracuseStep 2144483 = 3216725) B3216725
theorem B2414819 : Blo 1429534 2414819 := bstep (se 1 (by rfl) ⟨1811114, by rfl⟩ : syracuseStep 2414819 = 3622229) B3622229
theorem B2144513 : Blo 1429534 2144513 := bstep (se 2 (by rfl) ⟨804192, by rfl⟩ : syracuseStep 2144513 = 1608385) B1608385
theorem B2144531 : Blo 1429534 2144531 := bstep (se 1 (by rfl) ⟨1608398, by rfl⟩ : syracuseStep 2144531 = 3216797) B3216797
theorem B2038051 : Blo 1429534 2038051 := bstep (se 1 (by rfl) ⟨1528538, by rfl⟩ : syracuseStep 2038051 = 3057077) B3057077
theorem B2144561 : Blo 1429534 2144561 := bstep (se 2 (by rfl) ⟨804210, by rfl⟩ : syracuseStep 2144561 = 1608421) B1608421
theorem B2144579 : Blo 1429534 2144579 := bstep (se 1 (by rfl) ⟨1608434, by rfl⟩ : syracuseStep 2144579 = 3216869) B3216869
theorem B2144609 : Blo 1429534 2144609 := bstep (se 2 (by rfl) ⟨804228, by rfl⟩ : syracuseStep 2144609 = 1608457) B1608457
theorem B2414947 : Blo 1429534 2414947 := bstep (se 1 (by rfl) ⟨1811210, by rfl⟩ : syracuseStep 2414947 = 3622421) B3622421
theorem B2144627 : Blo 1429534 2144627 := bstep (se 1 (by rfl) ⟨1608470, by rfl⟩ : syracuseStep 2144627 = 3216941) B3216941
theorem B2447747 : Blo 1429534 2447747 := bstep (se 1 (by rfl) ⟨1835810, by rfl⟩ : syracuseStep 2447747 = 3671621) B3671621
theorem B4585859 : Blo 1429534 4585859 := bstep (se 1 (by rfl) ⟨3439394, by rfl⟩ : syracuseStep 4585859 = 6878789) B6878789
theorem B2144657 : Blo 1429534 2144657 := bstep (se 2 (by rfl) ⟨804246, by rfl⟩ : syracuseStep 2144657 = 1608493) B1608493
theorem B2144675 : Blo 1429534 2144675 := bstep (se 1 (by rfl) ⟨1608506, by rfl⟩ : syracuseStep 2144675 = 3217013) B3217013
theorem B3217841 : Blo 1429534 3217841 := bstep (se 2 (by rfl) ⟨1206690, by rfl⟩ : syracuseStep 3217841 = 2413381) B2413381
theorem B1718707 : Blo 1429534 1718707 := bstep (se 1 (by rfl) ⟨1289030, by rfl⟩ : syracuseStep 1718707 = 2578061) B2578061
theorem B2144705 : Blo 1429534 2144705 := bstep (se 2 (by rfl) ⟨804264, by rfl⟩ : syracuseStep 2144705 = 1608529) B1608529
theorem B3217859 : Blo 1429534 3217859 := bstep (se 1 (by rfl) ⟨2413394, by rfl⟩ : syracuseStep 3217859 = 4826789) B4826789
theorem B2144723 : Blo 1429534 2144723 := bstep (se 1 (by rfl) ⟨1608542, by rfl⟩ : syracuseStep 2144723 = 3217085) B3217085
theorem B2144753 : Blo 1429534 2144753 := bstep (se 2 (by rfl) ⟨804282, by rfl⟩ : syracuseStep 2144753 = 1608565) B1608565
theorem B3619313 : Blo 1429534 3619313 := bstep (se 2 (by rfl) ⟨1357242, by rfl⟩ : syracuseStep 3619313 = 2714485) B2714485
theorem B2415089 : Blo 1429534 2415089 := bstep (se 2 (by rfl) ⟨905658, by rfl⟩ : syracuseStep 2415089 = 1811317) B1811317
theorem B2144771 : Blo 1429534 2144771 := bstep (se 1 (by rfl) ⟨1608578, by rfl⟩ : syracuseStep 2144771 = 3217157) B3217157
theorem B1718803 : Blo 1429534 1718803 := bstep (se 1 (by rfl) ⟨1289102, by rfl⟩ : syracuseStep 1718803 = 2578205) B2578205
theorem B2144801 : Blo 1429534 2144801 := bstep (se 2 (by rfl) ⟨804300, by rfl⟩ : syracuseStep 2144801 = 1608601) B1608601
theorem B3619363 : Blo 1429534 3619363 := bstep (se 1 (by rfl) ⟨2714522, by rfl⟩ : syracuseStep 3619363 = 5429045) B5429045
theorem B2144819 : Blo 1429534 2144819 := bstep (se 1 (by rfl) ⟨1608614, by rfl⟩ : syracuseStep 2144819 = 3217229) B3217229
theorem B14678597 : Blo 1429534 14678597 := bstep (se 4 (by rfl) ⟨1376118, by rfl⟩ : syracuseStep 14678597 = 2752237) B2752237
theorem B2144849 : Blo 1429534 2144849 := bstep (se 2 (by rfl) ⟨804318, by rfl⟩ : syracuseStep 2144849 = 1608637) B1608637
theorem B2144867 : Blo 1429534 2144867 := bstep (se 1 (by rfl) ⟨1608650, by rfl⟩ : syracuseStep 2144867 = 3217301) B3217301
theorem B2415217 : Blo 1429534 2415217 := bstep (se 2 (by rfl) ⟨905706, by rfl⟩ : syracuseStep 2415217 = 1811413) B1811413
theorem B2144897 : Blo 1429534 2144897 := bstep (se 2 (by rfl) ⟨804336, by rfl⟩ : syracuseStep 2144897 = 1608673) B1608673
theorem B7731845 : Blo 1429534 7731845 := bstep (se 4 (by rfl) ⟨724860, by rfl⟩ : syracuseStep 7731845 = 1449721) B1449721
theorem B10869389 : Blo 1429534 10869389 := bstep (se 3 (by rfl) ⟨2038010, by rfl⟩ : syracuseStep 10869389 = 4076021) B4076021
theorem B2144915 : Blo 1429534 2144915 := bstep (se 1 (by rfl) ⟨1608686, by rfl⟩ : syracuseStep 2144915 = 3217373) B3217373
theorem B2415251 : Blo 1429534 2415251 := bstep (se 1 (by rfl) ⟨1811438, by rfl⟩ : syracuseStep 2415251 = 3622877) B3622877
theorem B6871715 : Blo 1429534 6871715 := bstep (se 1 (by rfl) ⟨5153786, by rfl⟩ : syracuseStep 6871715 = 10307573) B10307573
theorem B4348579 : Blo 1429534 4348579 := bstep (se 1 (by rfl) ⟨3261434, by rfl⟩ : syracuseStep 4348579 = 6522869) B6522869
theorem B3619505 : Blo 1429534 3619505 := bstep (se 2 (by rfl) ⟨1357314, by rfl⟩ : syracuseStep 3619505 = 2714629) B2714629
theorem B2144945 : Blo 1429534 2144945 := bstep (se 2 (by rfl) ⟨804354, by rfl⟩ : syracuseStep 2144945 = 1608709) B1608709
theorem B2144963 : Blo 1429534 2144963 := bstep (se 1 (by rfl) ⟨1608722, by rfl⟩ : syracuseStep 2144963 = 3217445) B3217445
theorem B3218129 : Blo 1429534 3218129 := bstep (se 2 (by rfl) ⟨1206798, by rfl⟩ : syracuseStep 3218129 = 2413597) B2413597
theorem B2144993 : Blo 1429534 2144993 := bstep (se 2 (by rfl) ⟨804372, by rfl⟩ : syracuseStep 2144993 = 1608745) B1608745
theorem B5429987 : Blo 1429534 5429987 := bstep (se 1 (by rfl) ⟨4072490, by rfl⟩ : syracuseStep 5429987 = 8144981) B8144981
theorem B3218147 : Blo 1429534 3218147 := bstep (se 1 (by rfl) ⟨2413610, by rfl⟩ : syracuseStep 3218147 = 4827221) B4827221
theorem B16284401 : Blo 1429534 16284401 := bstep (se 2 (by rfl) ⟨6106650, by rfl⟩ : syracuseStep 16284401 = 12213301) B12213301
theorem B2145011 : Blo 1429534 2145011 := bstep (se 1 (by rfl) ⟨1608758, by rfl⟩ : syracuseStep 2145011 = 3217517) B3217517
theorem B2145041 : Blo 1429534 2145041 := bstep (se 2 (by rfl) ⟨804390, by rfl⟩ : syracuseStep 2145041 = 1608781) B1608781
theorem B2415379 : Blo 1429534 2415379 := bstep (se 1 (by rfl) ⟨1811534, by rfl⟩ : syracuseStep 2415379 = 3623069) B3623069
theorem B2145059 : Blo 1429534 2145059 := bstep (se 1 (by rfl) ⟨1608794, by rfl⟩ : syracuseStep 2145059 = 3217589) B3217589
theorem B3054385 : Blo 1429534 3054385 := bstep (se 2 (by rfl) ⟨1145394, by rfl⟩ : syracuseStep 3054385 = 2290789) B2290789
theorem B2145089 : Blo 1429534 2145089 := bstep (se 2 (by rfl) ⟨804408, by rfl⟩ : syracuseStep 2145089 = 1608817) B1608817
theorem B2751313 : Blo 1429534 2751313 := bstep (se 2 (by rfl) ⟨1031742, by rfl⟩ : syracuseStep 2751313 = 2063485) B2063485
theorem B2145107 : Blo 1429534 2145107 := bstep (se 1 (by rfl) ⟨1608830, by rfl⟩ : syracuseStep 2145107 = 3217661) B3217661
theorem B2145137 : Blo 1429534 2145137 := bstep (se 2 (by rfl) ⟨804426, by rfl⟩ : syracuseStep 2145137 = 1608853) B1608853
theorem B2145155 : Blo 1429534 2145155 := bstep (se 1 (by rfl) ⟨1608866, by rfl⟩ : syracuseStep 2145155 = 3217733) B3217733
theorem B7240589 : Blo 1429534 7240589 := bstep (se 3 (by rfl) ⟨1357610, by rfl⟩ : syracuseStep 7240589 = 2715221) B2715221
theorem B1719187 : Blo 1429534 1719187 := bstep (se 1 (by rfl) ⟨1289390, by rfl⟩ : syracuseStep 1719187 = 2578781) B2578781
theorem B2145185 : Blo 1429534 2145185 := bstep (se 2 (by rfl) ⟨804444, by rfl⟩ : syracuseStep 2145185 = 1608889) B1608889
theorem B2415521 : Blo 1429534 2415521 := bstep (se 2 (by rfl) ⟨905820, by rfl⟩ : syracuseStep 2415521 = 1811641) B1811641
theorem B6192035 : Blo 1429534 6192035 := bstep (se 1 (by rfl) ⟨4644026, by rfl⟩ : syracuseStep 6192035 = 9288053) B9288053
theorem B2145203 : Blo 1429534 2145203 := bstep (se 1 (by rfl) ⟨1608902, by rfl⟩ : syracuseStep 2145203 = 3217805) B3217805
theorem B2145233 : Blo 1429534 2145233 := bstep (se 2 (by rfl) ⟨804462, by rfl⟩ : syracuseStep 2145233 = 1608925) B1608925
theorem B2145251 : Blo 1429534 2145251 := bstep (se 1 (by rfl) ⟨1608938, by rfl⟩ : syracuseStep 2145251 = 3217877) B3217877
theorem B3218417 : Blo 1429534 3218417 := bstep (se 2 (by rfl) ⟨1206906, by rfl⟩ : syracuseStep 3218417 = 2413813) B2413813
theorem B2145281 : Blo 1429534 2145281 := bstep (se 2 (by rfl) ⟨804480, by rfl⟩ : syracuseStep 2145281 = 1608961) B1608961
theorem B3218435 : Blo 1429534 3218435 := bstep (se 1 (by rfl) ⟨2413826, by rfl⟩ : syracuseStep 3218435 = 4827653) B4827653
theorem B2579473 : Blo 1429534 2579473 := bstep (se 2 (by rfl) ⟨967302, by rfl⟩ : syracuseStep 2579473 = 1934605) B1934605
theorem B2145299 : Blo 1429534 2145299 := bstep (se 1 (by rfl) ⟨1608974, by rfl⟩ : syracuseStep 2145299 = 3217949) B3217949
theorem B2415649 : Blo 1429534 2415649 := bstep (se 2 (by rfl) ⟨905868, by rfl⟩ : syracuseStep 2415649 = 1811737) B1811737
theorem B2145329 : Blo 1429534 2145329 := bstep (se 2 (by rfl) ⟨804498, by rfl⟩ : syracuseStep 2145329 = 1608997) B1608997
theorem B2145347 : Blo 1429534 2145347 := bstep (se 1 (by rfl) ⟨1609010, by rfl⟩ : syracuseStep 2145347 = 3218021) B3218021
theorem B2415683 : Blo 1429534 2415683 := bstep (se 1 (by rfl) ⟨1811762, by rfl⟩ : syracuseStep 2415683 = 3623525) B3623525
theorem B2145377 : Blo 1429534 2145377 := bstep (se 2 (by rfl) ⟨804516, by rfl⟩ : syracuseStep 2145377 = 1609033) B1609033
theorem B9165923 : Blo 1429534 9165923 := bstep (se 1 (by rfl) ⟨6874442, by rfl⟩ : syracuseStep 9165923 = 13748885) B13748885
theorem B8150129 : Blo 1429534 8150129 := bstep (se 2 (by rfl) ⟨3056298, by rfl⟩ : syracuseStep 8150129 = 6112597) B6112597
theorem B2145395 : Blo 1429534 2145395 := bstep (se 1 (by rfl) ⟨1609046, by rfl⟩ : syracuseStep 2145395 = 3218093) B3218093
theorem B34806925 : Blo 1429534 34806925 := bstep (se 3 (by rfl) ⟨6526298, by rfl⟩ : syracuseStep 34806925 = 13052597) B13052597
theorem B2145425 : Blo 1429534 2145425 := bstep (se 2 (by rfl) ⟨804534, by rfl⟩ : syracuseStep 2145425 = 1609069) B1609069
theorem B2145443 : Blo 1429534 2145443 := bstep (se 1 (by rfl) ⟨1609082, by rfl⟩ : syracuseStep 2145443 = 3218165) B3218165
theorem B2145473 : Blo 1429534 2145473 := bstep (se 2 (by rfl) ⟨804552, by rfl⟩ : syracuseStep 2145473 = 1609105) B1609105
theorem B12385477 : Blo 1429534 12385477 := bstep (se 4 (by rfl) ⟨1161138, by rfl⟩ : syracuseStep 12385477 = 2322277) B2322277
theorem B2145491 : Blo 1429534 2145491 := bstep (se 1 (by rfl) ⟨1609118, by rfl⟩ : syracuseStep 2145491 = 3218237) B3218237
theorem B49544419 : Blo 1429534 49544419 := bstep (se 1 (by rfl) ⟨37158314, by rfl⟩ : syracuseStep 49544419 = 74316629) B74316629
theorem B8142065 : Blo 1429534 8142065 := bstep (se 2 (by rfl) ⟨3053274, by rfl⟩ : syracuseStep 8142065 = 6106549) B6106549
theorem B2145521 : Blo 1429534 2145521 := bstep (se 2 (by rfl) ⟨804570, by rfl⟩ : syracuseStep 2145521 = 1609141) B1609141
theorem B2145539 : Blo 1429534 2145539 := bstep (se 1 (by rfl) ⟨1609154, by rfl⟩ : syracuseStep 2145539 = 3218309) B3218309
theorem B3218705 : Blo 1429534 3218705 := bstep (se 2 (by rfl) ⟨1207014, by rfl⟩ : syracuseStep 3218705 = 2414029) B2414029
theorem B1449235 : Blo 1429534 1449235 := bstep (se 1 (by rfl) ⟨1086926, by rfl⟩ : syracuseStep 1449235 = 2173853) B2173853
theorem B2145569 : Blo 1429534 2145569 := bstep (se 2 (by rfl) ⟨804588, by rfl⟩ : syracuseStep 2145569 = 1609177) B1609177
theorem B3218723 : Blo 1429534 3218723 := bstep (se 1 (by rfl) ⟨2414042, by rfl⟩ : syracuseStep 3218723 = 4828085) B4828085
theorem B2145587 : Blo 1429534 2145587 := bstep (se 1 (by rfl) ⟨1609190, by rfl⟩ : syracuseStep 2145587 = 3218381) B3218381
theorem B2145617 : Blo 1429534 2145617 := bstep (se 2 (by rfl) ⟨804606, by rfl⟩ : syracuseStep 2145617 = 1609213) B1609213
theorem B2145635 : Blo 1429534 2145635 := bstep (se 1 (by rfl) ⟨1609226, by rfl⟩ : syracuseStep 2145635 = 3218453) B3218453
theorem B7839089 : Blo 1429534 7839089 := bstep (se 2 (by rfl) ⟨2939658, by rfl⟩ : syracuseStep 7839089 = 5879317) B5879317
theorem B2145665 : Blo 1429534 2145665 := bstep (se 2 (by rfl) ⟨804624, by rfl⟩ : syracuseStep 2145665 = 1609249) B1609249
theorem B2145683 : Blo 1429534 2145683 := bstep (se 1 (by rfl) ⟨1609262, by rfl⟩ : syracuseStep 2145683 = 3218525) B3218525
theorem B2145713 : Blo 1429534 2145713 := bstep (se 2 (by rfl) ⟨804642, by rfl⟩ : syracuseStep 2145713 = 1609285) B1609285
theorem B1809859 : Blo 1429534 1809859 := bstep (se 1 (by rfl) ⟨1357394, by rfl⟩ : syracuseStep 1809859 = 2714789) B2714789
theorem B2145731 : Blo 1429534 2145731 := bstep (se 1 (by rfl) ⟨1609298, by rfl⟩ : syracuseStep 2145731 = 3218597) B3218597
theorem B2145761 : Blo 1429534 2145761 := bstep (se 2 (by rfl) ⟨804660, by rfl⟩ : syracuseStep 2145761 = 1609321) B1609321
theorem B4128241 : Blo 1429534 4128241 := bstep (se 2 (by rfl) ⟨1548090, by rfl⟩ : syracuseStep 4128241 = 3096181) B3096181
theorem B2145779 : Blo 1429534 2145779 := bstep (se 1 (by rfl) ⟨1609334, by rfl⟩ : syracuseStep 2145779 = 3218669) B3218669
theorem B2145809 : Blo 1429534 2145809 := bstep (se 2 (by rfl) ⟨804678, by rfl⟩ : syracuseStep 2145809 = 1609357) B1609357
theorem B1809955 : Blo 1429534 1809955 := bstep (se 1 (by rfl) ⟨1357466, by rfl⟩ : syracuseStep 1809955 = 2714933) B2714933
theorem B2145827 : Blo 1429534 2145827 := bstep (se 1 (by rfl) ⟨1609370, by rfl⟩ : syracuseStep 2145827 = 3218741) B3218741
theorem B9166385 : Blo 1429534 9166385 := bstep (se 2 (by rfl) ⟨3437394, by rfl⟩ : syracuseStep 9166385 = 6874789) B6874789
theorem B3218993 : Blo 1429534 3218993 := bstep (se 2 (by rfl) ⟨1207122, by rfl⟩ : syracuseStep 3218993 = 2414245) B2414245
theorem B2145857 : Blo 1429534 2145857 := bstep (se 2 (by rfl) ⟨804696, by rfl⟩ : syracuseStep 2145857 = 1609393) B1609393
theorem B3055171 : Blo 1429534 3055171 := bstep (se 1 (by rfl) ⟨2291378, by rfl⟩ : syracuseStep 3055171 = 4582757) B4582757
theorem B3219011 : Blo 1429534 3219011 := bstep (se 1 (by rfl) ⟨2414258, by rfl⟩ : syracuseStep 3219011 = 4828517) B4828517
theorem B2145875 : Blo 1429534 2145875 := bstep (se 1 (by rfl) ⟨1609406, by rfl⟩ : syracuseStep 2145875 = 3218813) B3218813
theorem B2145905 : Blo 1429534 2145905 := bstep (se 2 (by rfl) ⟨804714, by rfl⟩ : syracuseStep 2145905 = 1609429) B1609429
theorem B2145923 : Blo 1429534 2145923 := bstep (se 1 (by rfl) ⟨1609442, by rfl⟩ : syracuseStep 2145923 = 3218885) B3218885
theorem B8814221 : Blo 1429534 8814221 := bstep (se 3 (by rfl) ⟨1652666, by rfl⟩ : syracuseStep 8814221 = 3305333) B3305333
theorem B3620497 : Blo 1429534 3620497 := bstep (se 2 (by rfl) ⟨1357686, by rfl⟩ : syracuseStep 3620497 = 2715373) B2715373
theorem B2145953 : Blo 1429534 2145953 := bstep (se 2 (by rfl) ⟨804732, by rfl⟩ : syracuseStep 2145953 = 1609465) B1609465
theorem B2145971 : Blo 1429534 2145971 := bstep (se 1 (by rfl) ⟨1609478, by rfl⟩ : syracuseStep 2145971 = 3218957) B3218957
theorem B5430989 : Blo 1429534 5430989 := bstep (se 3 (by rfl) ⟨1018310, by rfl⟩ : syracuseStep 5430989 = 2036621) B2036621
theorem B2146001 : Blo 1429534 2146001 := bstep (se 2 (by rfl) ⟨804750, by rfl⟩ : syracuseStep 2146001 = 1609501) B1609501
theorem B3669731 : Blo 1429534 3669731 := bstep (se 1 (by rfl) ⟨2752298, by rfl⟩ : syracuseStep 3669731 = 5504597) B5504597
theorem B2146019 : Blo 1429534 2146019 := bstep (se 1 (by rfl) ⟨1609514, by rfl⟩ : syracuseStep 2146019 = 3219029) B3219029
theorem B10305265 : Blo 1429534 10305265 := bstep (se 2 (by rfl) ⟨3864474, by rfl⟩ : syracuseStep 10305265 = 7728949) B7728949
theorem B6192881 : Blo 1429534 6192881 := bstep (se 2 (by rfl) ⟨2322330, by rfl⟩ : syracuseStep 6192881 = 4644661) B4644661
theorem B2146049 : Blo 1429534 2146049 := bstep (se 2 (by rfl) ⟨804768, by rfl⟩ : syracuseStep 2146049 = 1609537) B1609537
theorem B4824845 : Blo 1429534 4824845 := bstep (se 3 (by rfl) ⟨904658, by rfl⟩ : syracuseStep 4824845 = 1809317) B1809317
theorem B4071181 : Blo 1429534 4071181 := bstep (se 3 (by rfl) ⟨763346, by rfl⟩ : syracuseStep 4071181 = 1526693) B1526693
theorem B2146067 : Blo 1429534 2146067 := bstep (se 1 (by rfl) ⟨1609550, by rfl⟩ : syracuseStep 2146067 = 3219101) B3219101
theorem B2146097 : Blo 1429534 2146097 := bstep (se 2 (by rfl) ⟨804786, by rfl⟩ : syracuseStep 2146097 = 1609573) B1609573
theorem B4824899 : Blo 1429534 4824899 := bstep (se 1 (by rfl) ⟨3618674, by rfl⟩ : syracuseStep 4824899 = 7237349) B7237349
theorem B2146115 : Blo 1429534 2146115 := bstep (se 1 (by rfl) ⟨1609586, by rfl⟩ : syracuseStep 2146115 = 3219173) B3219173
theorem B3219281 : Blo 1429534 3219281 := bstep (se 2 (by rfl) ⟨1207230, by rfl⟩ : syracuseStep 3219281 = 2414461) B2414461
theorem B2146145 : Blo 1429534 2146145 := bstep (se 2 (by rfl) ⟨804804, by rfl⟩ : syracuseStep 2146145 = 1609609) B1609609
theorem B3219299 : Blo 1429534 3219299 := bstep (se 1 (by rfl) ⟨2414474, by rfl⟩ : syracuseStep 3219299 = 4828949) B4828949
theorem B2146163 : Blo 1429534 2146163 := bstep (se 1 (by rfl) ⟨1609622, by rfl⟩ : syracuseStep 2146163 = 3219245) B3219245
theorem B2146193 : Blo 1429534 2146193 := bstep (se 2 (by rfl) ⟨804822, by rfl⟩ : syracuseStep 2146193 = 1609645) B1609645
theorem B3620771 : Blo 1429534 3620771 := bstep (se 1 (by rfl) ⟨2715578, by rfl⟩ : syracuseStep 3620771 = 5431157) B5431157
theorem B2146211 : Blo 1429534 2146211 := bstep (se 1 (by rfl) ⟨1609658, by rfl⟩ : syracuseStep 2146211 = 3219317) B3219317
theorem B2146241 : Blo 1429534 2146241 := bstep (se 2 (by rfl) ⟨804840, by rfl⟩ : syracuseStep 2146241 = 1609681) B1609681
theorem B16752581 : Blo 1429534 16752581 := bstep (se 4 (by rfl) ⟨1570554, by rfl⟩ : syracuseStep 16752581 = 3141109) B3141109
theorem B2146259 : Blo 1429534 2146259 := bstep (se 1 (by rfl) ⟨1609694, by rfl⟩ : syracuseStep 2146259 = 3219389) B3219389
theorem B11599843 : Blo 1429534 11599843 := bstep (se 1 (by rfl) ⟨8699882, by rfl⟩ : syracuseStep 11599843 = 17399765) B17399765
theorem B2146289 : Blo 1429534 2146289 := bstep (se 2 (by rfl) ⟨804858, by rfl⟩ : syracuseStep 2146289 = 1609717) B1609717
theorem B3670039 : Blo 1429534 3670039 := bstep (se 1 (by rfl) ⟨2752529, by rfl⟩ : syracuseStep 3670039 = 5505059) B5505059
theorem B3219479 : Blo 1429534 3219479 := bstep (se 1 (by rfl) ⟨2414609, by rfl⟩ : syracuseStep 3219479 = 4829219) B4829219
theorem B4653121 : Blo 1429534 4653121 := bstep (se 2 (by rfl) ⟨1744920, by rfl⟩ : syracuseStep 4653121 = 3489841) B3489841
theorem B1810507 : Blo 1429534 1810507 := bstep (se 1 (by rfl) ⟨1357880, by rfl⟩ : syracuseStep 1810507 = 2715761) B2715761
theorem B2146379 : Blo 1429534 2146379 := bstep (se 1 (by rfl) ⟨1609784, by rfl⟩ : syracuseStep 2146379 = 3219569) B3219569
theorem B2146391 : Blo 1429534 2146391 := bstep (se 1 (by rfl) ⟨1609793, by rfl⟩ : syracuseStep 2146391 = 3219587) B3219587
theorem B2146457 : Blo 1429534 2146457 := bstep (se 2 (by rfl) ⟨804921, by rfl⟩ : syracuseStep 2146457 = 1609843) B1609843
theorem B5431475 : Blo 1429534 5431475 := bstep (se 1 (by rfl) ⟨4073606, by rfl⟩ : syracuseStep 5431475 = 8147213) B8147213
theorem B3219659 : Blo 1429534 3219659 := bstep (se 1 (by rfl) ⟨2414744, by rfl⟩ : syracuseStep 3219659 = 4829489) B4829489
theorem B5882077 : Blo 1429534 5882077 := bstep (se 3 (by rfl) ⟨1102889, by rfl⟩ : syracuseStep 5882077 = 2205779) B2205779
theorem B3219713 : Blo 1429534 3219713 := bstep (se 2 (by rfl) ⟨1207392, by rfl⟩ : syracuseStep 3219713 = 2414785) B2414785
theorem B2146571 : Blo 1429534 2146571 := bstep (se 1 (by rfl) ⟨1609928, by rfl⟩ : syracuseStep 2146571 = 3219857) B3219857
theorem B8151313 : Blo 1429534 8151313 := bstep (se 2 (by rfl) ⟨3056742, by rfl⟩ : syracuseStep 8151313 = 6113485) B6113485
theorem B2146583 : Blo 1429534 2146583 := bstep (se 1 (by rfl) ⟨1609937, by rfl⟩ : syracuseStep 2146583 = 3219875) B3219875
theorem B10314029 : Blo 1429534 10314029 := bstep (se 3 (by rfl) ⟨1933880, by rfl⟩ : syracuseStep 10314029 = 3867761) B3867761
theorem B1810775 : Blo 1429534 1810775 := bstep (se 1 (by rfl) ⟨1358081, by rfl⟩ : syracuseStep 1810775 = 2716163) B2716163
theorem B2146649 : Blo 1429534 2146649 := bstep (se 2 (by rfl) ⟨804993, by rfl⟩ : syracuseStep 2146649 = 1609987) B1609987
theorem B36675989 : Blo 1429534 36675989 := bstep (se 6 (by rfl) ⟨859593, by rfl⟩ : syracuseStep 36675989 = 1719187) B1719187
theorem B4825547 : Blo 1429534 4825547 := bstep (se 1 (by rfl) ⟨3619160, by rfl⟩ : syracuseStep 4825547 = 7238321) B7238321
theorem B2146763 : Blo 1429534 2146763 := bstep (se 1 (by rfl) ⟨1610072, by rfl⟩ : syracuseStep 2146763 = 3220145) B3220145
theorem B2146775 : Blo 1429534 2146775 := bstep (se 1 (by rfl) ⟨1610081, by rfl⟩ : syracuseStep 2146775 = 3220163) B3220163
theorem B3219929 : Blo 1429534 3219929 := bstep (se 2 (by rfl) ⟨1207473, by rfl⟩ : syracuseStep 3219929 = 2414947) B2414947
theorem B1630699 : Blo 1429534 1630699 := bstep (se 1 (by rfl) ⟨1223024, by rfl⟩ : syracuseStep 1630699 = 2446049) B2446049
theorem B2146841 : Blo 1429534 2146841 := bstep (se 2 (by rfl) ⟨805065, by rfl⟩ : syracuseStep 2146841 = 1610131) B1610131
theorem B3220019 : Blo 1429534 3220019 := bstep (se 1 (by rfl) ⟨2415014, by rfl⟩ : syracuseStep 3220019 = 4830029) B4830029
theorem B3220055 : Blo 1429534 3220055 := bstep (se 1 (by rfl) ⟨2415041, by rfl⟩ : syracuseStep 3220055 = 4830083) B4830083
theorem B1933913 : Blo 1429534 1933913 := bstep (se 2 (by rfl) ⟨725217, by rfl⟩ : syracuseStep 1933913 = 1450435) B1450435
theorem B7242371 : Blo 1429534 7242371 := bstep (se 1 (by rfl) ⟨5431778, by rfl⟩ : syracuseStep 7242371 = 10863557) B10863557
theorem B2146955 : Blo 1429534 2146955 := bstep (se 1 (by rfl) ⟨1610216, by rfl⟩ : syracuseStep 2146955 = 3220433) B3220433
theorem B2146967 : Blo 1429534 2146967 := bstep (se 1 (by rfl) ⟨1610225, by rfl⟩ : syracuseStep 2146967 = 3220451) B3220451
theorem B9167539 : Blo 1429534 9167539 := bstep (se 1 (by rfl) ⟨6875654, by rfl⟩ : syracuseStep 9167539 = 13751309) B13751309
theorem B27509453 : Blo 1429534 27509453 := bstep (se 3 (by rfl) ⟨5158022, by rfl⟩ : syracuseStep 27509453 = 10316045) B10316045
theorem B4825817 : Blo 1429534 4825817 := bstep (se 2 (by rfl) ⟨1809681, by rfl⟩ : syracuseStep 4825817 = 3619363) B3619363
theorem B2147033 : Blo 1429534 2147033 := bstep (se 2 (by rfl) ⟨805137, by rfl⟩ : syracuseStep 2147033 = 1610275) B1610275
theorem B4129501 : Blo 1429534 4129501 := bstep (se 3 (by rfl) ⟨774281, by rfl⟩ : syracuseStep 4129501 = 1548563) B1548563
theorem B3220235 : Blo 1429534 3220235 := bstep (se 1 (by rfl) ⟨2415176, by rfl⟩ : syracuseStep 3220235 = 4830353) B4830353
theorem B5432129 : Blo 1429534 5432129 := bstep (se 2 (by rfl) ⟨2037048, by rfl⟩ : syracuseStep 5432129 = 4074097) B4074097
theorem B3220289 : Blo 1429534 3220289 := bstep (se 2 (by rfl) ⟨1207608, by rfl⟩ : syracuseStep 3220289 = 2415217) B2415217
theorem B2147147 : Blo 1429534 2147147 := bstep (se 1 (by rfl) ⟨1610360, by rfl⟩ : syracuseStep 2147147 = 3220721) B3220721
theorem B2147159 : Blo 1429534 2147159 := bstep (se 1 (by rfl) ⟨1610369, by rfl⟩ : syracuseStep 2147159 = 3220739) B3220739
theorem B4072285 : Blo 1429534 4072285 := bstep (se 3 (by rfl) ⟨763553, by rfl⟩ : syracuseStep 4072285 = 1527107) B1527107
theorem B2147225 : Blo 1429534 2147225 := bstep (se 2 (by rfl) ⟨805209, by rfl⟩ : syracuseStep 2147225 = 1610419) B1610419
theorem B1811479 : Blo 1429534 1811479 := bstep (se 1 (by rfl) ⟨1358609, by rfl⟩ : syracuseStep 1811479 = 2717219) B2717219
theorem B3220505 : Blo 1429534 3220505 := bstep (se 2 (by rfl) ⟨1207689, by rfl⟩ : syracuseStep 3220505 = 2415379) B2415379
theorem B4072513 : Blo 1429534 4072513 := bstep (se 2 (by rfl) ⟨1527192, by rfl⟩ : syracuseStep 4072513 = 3054385) B3054385
theorem B3220595 : Blo 1429534 3220595 := bstep (se 1 (by rfl) ⟨2415446, by rfl⟩ : syracuseStep 3220595 = 4830893) B4830893
theorem B8144023 : Blo 1429534 8144023 := bstep (se 1 (by rfl) ⟨6108017, by rfl⟩ : syracuseStep 8144023 = 12216035) B12216035
theorem B3220631 : Blo 1429534 3220631 := bstep (se 1 (by rfl) ⟨2415473, by rfl⟩ : syracuseStep 3220631 = 4830947) B4830947
theorem B3622067 : Blo 1429534 3622067 := bstep (se 1 (by rfl) ⟨2716550, by rfl⟩ : syracuseStep 3622067 = 5433101) B5433101
theorem B6112529 : Blo 1429534 6112529 := bstep (se 2 (by rfl) ⟨2292198, by rfl⟩ : syracuseStep 6112529 = 4584397) B4584397
theorem B3220811 : Blo 1429534 3220811 := bstep (se 1 (by rfl) ⟨2415608, by rfl⟩ : syracuseStep 3220811 = 4831217) B4831217
theorem B10855781 : Blo 1429534 10855781 := bstep (se 4 (by rfl) ⟨1017729, by rfl⟩ : syracuseStep 10855781 = 2035459) B2035459
theorem B3220865 : Blo 1429534 3220865 := bstep (se 2 (by rfl) ⟨1207824, by rfl⟩ : syracuseStep 3220865 = 2415649) B2415649
theorem B4826519 : Blo 1429534 4826519 := bstep (se 1 (by rfl) ⟨3619889, by rfl⟩ : syracuseStep 4826519 = 7239779) B7239779
theorem B4072855 : Blo 1429534 4072855 := bstep (se 1 (by rfl) ⟨3054641, by rfl⟩ : syracuseStep 4072855 = 6109283) B6109283
theorem B3974579 : Blo 1429534 3974579 := bstep (se 1 (by rfl) ⟨2980934, by rfl⟩ : syracuseStep 3974579 = 5961869) B5961869
theorem B39142925 : Blo 1429534 39142925 := bstep (se 3 (by rfl) ⟨7339298, by rfl⟩ : syracuseStep 39142925 = 14678597) B14678597
theorem B46409233 : Blo 1429534 46409233 := bstep (se 2 (by rfl) ⟨17403462, by rfl⟩ : syracuseStep 46409233 = 34806925) B34806925
theorem B1631831 : Blo 1429534 1631831 := bstep (se 1 (by rfl) ⟨1223873, by rfl⟩ : syracuseStep 1631831 = 2447747) B2447747
theorem B3057239 : Blo 1429534 3057239 := bstep (se 1 (by rfl) ⟨2292929, by rfl⟩ : syracuseStep 3057239 = 4585859) B4585859
theorem B3868249 : Blo 1429534 3868249 := bstep (se 2 (by rfl) ⟨1450593, by rfl⟩ : syracuseStep 3868249 = 2901187) B2901187
theorem B3622603 : Blo 1429534 3622603 := bstep (se 1 (by rfl) ⟨2716952, by rfl⟩ : syracuseStep 3622603 = 5433905) B5433905
theorem B5154563 : Blo 1429534 5154563 := bstep (se 1 (by rfl) ⟨3865922, by rfl⟩ : syracuseStep 5154563 = 7731845) B7731845
theorem B12396293 : Blo 1429534 12396293 := bstep (se 4 (by rfl) ⟨1162152, by rfl⟩ : syracuseStep 12396293 = 2324305) B2324305
theorem B4581143 : Blo 1429534 4581143 := bstep (se 1 (by rfl) ⟨3435857, by rfl⟩ : syracuseStep 4581143 = 6871715) B6871715
theorem B10856267 : Blo 1429534 10856267 := bstep (se 1 (by rfl) ⟨8142200, by rfl⟩ : syracuseStep 10856267 = 16284401) B16284401
theorem B3622745 : Blo 1429534 3622745 := bstep (se 2 (by rfl) ⟨1358529, by rfl⟩ : syracuseStep 3622745 = 2717059) B2717059
theorem B4827059 : Blo 1429534 4827059 := bstep (se 1 (by rfl) ⟨3620294, by rfl⟩ : syracuseStep 4827059 = 7240589) B7240589
theorem B5433389 : Blo 1429534 5433389 := bstep (se 3 (by rfl) ⟨1018760, by rfl⟩ : syracuseStep 5433389 = 2037521) B2037521
theorem B5433419 : Blo 1429534 5433419 := bstep (se 1 (by rfl) ⟨4075064, by rfl⟩ : syracuseStep 5433419 = 8150129) B8150129
theorem B4073561 : Blo 1429534 4073561 := bstep (se 2 (by rfl) ⟨1527585, by rfl⟩ : syracuseStep 4073561 = 3055171) B3055171
theorem B11012273 : Blo 1429534 11012273 := bstep (se 2 (by rfl) ⟨4129602, by rfl⟩ : syracuseStep 11012273 = 8259205) B8259205
theorem B4827329 : Blo 1429534 4827329 := bstep (se 2 (by rfl) ⟨1810248, by rfl⟩ : syracuseStep 4827329 = 3620497) B3620497
theorem B13740353 : Blo 1429534 13740353 := bstep (se 2 (by rfl) ⟨5152632, by rfl⟩ : syracuseStep 13740353 = 10305265) B10305265
theorem B8259941 : Blo 1429534 8259941 := bstep (se 4 (by rfl) ⟨774369, by rfl⟩ : syracuseStep 8259941 = 1548739) B1548739
theorem B5876147 : Blo 1429534 5876147 := bstep (se 1 (by rfl) ⟨4407110, by rfl⟩ : syracuseStep 5876147 = 8814221) B8814221
theorem B9161261 : Blo 1429534 9161261 := bstep (se 3 (by rfl) ⟨1717736, by rfl⟩ : syracuseStep 9161261 = 3435473) B3435473
theorem B11168387 : Blo 1429534 11168387 := bstep (se 1 (by rfl) ⟨8376290, by rfl⟩ : syracuseStep 11168387 = 16752581) B16752581
theorem B1608331 : Blo 1429534 1608331 := bstep (se 1 (by rfl) ⟨1206248, by rfl⟩ : syracuseStep 1608331 = 2412497) B2412497
theorem B5434073 : Blo 1429534 5434073 := bstep (se 2 (by rfl) ⟨2037777, by rfl⟩ : syracuseStep 5434073 = 4075555) B4075555
theorem B4827869 : Blo 1429534 4827869 := bstep (se 3 (by rfl) ⟨905225, by rfl⟩ : syracuseStep 4827869 = 1810451) B1810451
theorem B1608439 : Blo 1429534 1608439 := bstep (se 1 (by rfl) ⟨1206329, by rfl⟩ : syracuseStep 1608439 = 2412659) B2412659
theorem B57256769 : Blo 1429534 57256769 := bstep (se 2 (by rfl) ⟨21471288, by rfl⟩ : syracuseStep 57256769 = 42942577) B42942577
theorem B10865501 : Blo 1429534 10865501 := bstep (se 3 (by rfl) ⟨2037281, by rfl⟩ : syracuseStep 10865501 = 4074563) B4074563
theorem B1608619 : Blo 1429534 1608619 := bstep (se 1 (by rfl) ⟨1206464, by rfl⟩ : syracuseStep 1608619 = 2412929) B2412929
theorem B1526731 : Blo 1429534 1526731 := bstep (se 1 (by rfl) ⟨1145048, by rfl⟩ : syracuseStep 1526731 = 2290097) B2290097
theorem B1608727 : Blo 1429534 1608727 := bstep (se 1 (by rfl) ⟨1206545, by rfl⟩ : syracuseStep 1608727 = 2413091) B2413091
theorem B5434391 : Blo 1429534 5434391 := bstep (se 1 (by rfl) ⟨4075793, by rfl⟩ : syracuseStep 5434391 = 8151587) B8151587
theorem B1608907 : Blo 1429534 1608907 := bstep (se 1 (by rfl) ⟨1206680, by rfl⟩ : syracuseStep 1608907 = 2413361) B2413361
theorem B1609015 : Blo 1429534 1609015 := bstep (se 1 (by rfl) ⟨1206761, by rfl⟩ : syracuseStep 1609015 = 2413523) B2413523
theorem B12217675 : Blo 1429534 12217675 := bstep (se 1 (by rfl) ⟨9163256, by rfl⟩ : syracuseStep 12217675 = 18326513) B18326513
theorem B52170101 : Blo 1429534 52170101 := bstep (se 5 (by rfl) ⟨2445473, by rfl⟩ : syracuseStep 52170101 = 4890947) B4890947
theorem B6106499 : Blo 1429534 6106499 := bstep (se 1 (by rfl) ⟨4579874, by rfl⟩ : syracuseStep 6106499 = 9159749) B9159749
theorem B1609195 : Blo 1429534 1609195 := bstep (se 1 (by rfl) ⟨1206896, by rfl⟩ : syracuseStep 1609195 = 2413793) B2413793
theorem B22335011 : Blo 1429534 22335011 := bstep (se 1 (by rfl) ⟨16751258, by rfl⟩ : syracuseStep 22335011 = 33502517) B33502517
theorem B1609303 : Blo 1429534 1609303 := bstep (se 1 (by rfl) ⟨1206977, by rfl⟩ : syracuseStep 1609303 = 2413955) B2413955
theorem B12217949 : Blo 1429534 12217949 := bstep (se 3 (by rfl) ⟨2290865, by rfl⟩ : syracuseStep 12217949 = 4581731) B4581731
theorem B2715275 : Blo 1429534 2715275 := bstep (se 1 (by rfl) ⟨2036456, by rfl⟩ : syracuseStep 2715275 = 4072913) B4072913
theorem B5435059 : Blo 1429534 5435059 := bstep (se 1 (by rfl) ⟨4076294, by rfl⟩ : syracuseStep 5435059 = 8152589) B8152589
theorem B4075201 : Blo 1429534 4075201 := bstep (se 2 (by rfl) ⟨1528200, by rfl⟩ : syracuseStep 4075201 = 3056401) B3056401
theorem B1609483 : Blo 1429534 1609483 := bstep (se 1 (by rfl) ⟨1207112, by rfl⟩ : syracuseStep 1609483 = 2414225) B2414225
theorem B2715457 : Blo 1429534 2715457 := bstep (se 2 (by rfl) ⟨1018296, by rfl⟩ : syracuseStep 2715457 = 2036593) B2036593
theorem B4829003 : Blo 1429534 4829003 := bstep (se 1 (by rfl) ⟨3621752, by rfl⟩ : syracuseStep 4829003 = 7243505) B7243505
theorem B2576215 : Blo 1429534 2576215 := bstep (se 1 (by rfl) ⟨1932161, by rfl⟩ : syracuseStep 2576215 = 3864323) B3864323
theorem B1527671 : Blo 1429534 1527671 := bstep (se 1 (by rfl) ⟨1145753, by rfl⟩ : syracuseStep 1527671 = 2291507) B2291507
theorem B1609591 : Blo 1429534 1609591 := bstep (se 1 (by rfl) ⟨1207193, by rfl⟩ : syracuseStep 1609591 = 2414387) B2414387
theorem B10317719 : Blo 1429534 10317719 := bstep (se 1 (by rfl) ⟨7738289, by rfl⟩ : syracuseStep 10317719 = 15476579) B15476579
theorem B1429547 : Blo 1429534 1429547 := bstep (se 1 (by rfl) ⟨1072160, by rfl⟩ : syracuseStep 1429547 = 2144321) B2144321
theorem B1609771 : Blo 1429534 1609771 := bstep (se 1 (by rfl) ⟨1207328, by rfl⟩ : syracuseStep 1609771 = 2414657) B2414657
theorem B1429559 : Blo 1429534 1429559 := bstep (se 1 (by rfl) ⟨1072169, by rfl⟩ : syracuseStep 1429559 = 2144339) B2144339
theorem B1429579 : Blo 1429534 1429579 := bstep (se 1 (by rfl) ⟨1072184, by rfl⟩ : syracuseStep 1429579 = 2144369) B2144369
theorem B1429591 : Blo 1429534 1429591 := bstep (se 1 (by rfl) ⟨1072193, by rfl⟩ : syracuseStep 1429591 = 2144387) B2144387
theorem B2035801 : Blo 1429534 2035801 := bstep (se 2 (by rfl) ⟨763425, by rfl⟩ : syracuseStep 2035801 = 1526851) B1526851
theorem B4829273 : Blo 1429534 4829273 := bstep (se 2 (by rfl) ⟨1810977, by rfl⟩ : syracuseStep 4829273 = 3621955) B3621955
theorem B7729253 : Blo 1429534 7729253 := bstep (se 4 (by rfl) ⟨724617, by rfl⟩ : syracuseStep 7729253 = 1449235) B1449235
theorem B1429611 : Blo 1429534 1429611 := bstep (se 1 (by rfl) ⟨1072208, by rfl⟩ : syracuseStep 1429611 = 2144417) B2144417
theorem B1429623 : Blo 1429534 1429623 := bstep (se 1 (by rfl) ⟨1072217, by rfl⟩ : syracuseStep 1429623 = 2144435) B2144435
theorem B1429643 : Blo 1429534 1429643 := bstep (se 1 (by rfl) ⟨1072232, by rfl⟩ : syracuseStep 1429643 = 2144465) B2144465
theorem B1429655 : Blo 1429534 1429655 := bstep (se 1 (by rfl) ⟨1072241, by rfl⟩ : syracuseStep 1429655 = 2144483) B2144483
theorem B1609879 : Blo 1429534 1609879 := bstep (se 1 (by rfl) ⟨1207409, by rfl⟩ : syracuseStep 1609879 = 2414819) B2414819
theorem B1429675 : Blo 1429534 1429675 := bstep (se 1 (by rfl) ⟨1072256, by rfl⟩ : syracuseStep 1429675 = 2144513) B2144513
theorem B11595953 : Blo 1429534 11595953 := bstep (se 2 (by rfl) ⟨4348482, by rfl⟩ : syracuseStep 11595953 = 8696965) B8696965
theorem B4583603 : Blo 1429534 4583603 := bstep (se 1 (by rfl) ⟨3437702, by rfl⟩ : syracuseStep 4583603 = 6875405) B6875405
theorem B1429687 : Blo 1429534 1429687 := bstep (se 1 (by rfl) ⟨1072265, by rfl⟩ : syracuseStep 1429687 = 2144531) B2144531
theorem B1429707 : Blo 1429534 1429707 := bstep (se 1 (by rfl) ⟨1072280, by rfl⟩ : syracuseStep 1429707 = 2144561) B2144561
theorem B1429719 : Blo 1429534 1429719 := bstep (se 1 (by rfl) ⟨1072289, by rfl⟩ : syracuseStep 1429719 = 2144579) B2144579
theorem B1429739 : Blo 1429534 1429739 := bstep (se 1 (by rfl) ⟨1072304, by rfl⟩ : syracuseStep 1429739 = 2144609) B2144609
theorem B1429751 : Blo 1429534 1429751 := bstep (se 1 (by rfl) ⟨1072313, by rfl⟩ : syracuseStep 1429751 = 2144627) B2144627
theorem B2715905 : Blo 1429534 2715905 := bstep (se 2 (by rfl) ⟨1018464, by rfl⟩ : syracuseStep 2715905 = 2036929) B2036929
theorem B1429771 : Blo 1429534 1429771 := bstep (se 1 (by rfl) ⟨1072328, by rfl⟩ : syracuseStep 1429771 = 2144657) B2144657
theorem B7246097 : Blo 1429534 7246097 := bstep (se 2 (by rfl) ⟨2717286, by rfl⟩ : syracuseStep 7246097 = 5434573) B5434573
theorem B1429783 : Blo 1429534 1429783 := bstep (se 1 (by rfl) ⟨1072337, by rfl⟩ : syracuseStep 1429783 = 2144675) B2144675
theorem B1429803 : Blo 1429534 1429803 := bstep (se 1 (by rfl) ⟨1072352, by rfl⟩ : syracuseStep 1429803 = 2144705) B2144705
theorem B1429815 : Blo 1429534 1429815 := bstep (se 1 (by rfl) ⟨1072361, by rfl⟩ : syracuseStep 1429815 = 2144723) B2144723
theorem B5796161 : Blo 1429534 5796161 := bstep (se 2 (by rfl) ⟨2173560, by rfl⟩ : syracuseStep 5796161 = 4347121) B4347121
theorem B1429835 : Blo 1429534 1429835 := bstep (se 1 (by rfl) ⟨1072376, by rfl⟩ : syracuseStep 1429835 = 2144753) B2144753
theorem B2412875 : Blo 1429534 2412875 := bstep (se 1 (by rfl) ⟨1809656, by rfl⟩ : syracuseStep 2412875 = 3619313) B3619313
theorem B1610059 : Blo 1429534 1610059 := bstep (se 1 (by rfl) ⟨1207544, by rfl⟩ : syracuseStep 1610059 = 2415089) B2415089
theorem B1429847 : Blo 1429534 1429847 := bstep (se 1 (by rfl) ⟨1072385, by rfl⟩ : syracuseStep 1429847 = 2144771) B2144771
theorem B1429867 : Blo 1429534 1429867 := bstep (se 1 (by rfl) ⟨1072400, by rfl⟩ : syracuseStep 1429867 = 2144801) B2144801
theorem B1429879 : Blo 1429534 1429879 := bstep (se 1 (by rfl) ⟨1072409, by rfl⟩ : syracuseStep 1429879 = 2144819) B2144819
theorem B1429899 : Blo 1429534 1429899 := bstep (se 1 (by rfl) ⟨1072424, by rfl⟩ : syracuseStep 1429899 = 2144849) B2144849
theorem B1429911 : Blo 1429534 1429911 := bstep (se 1 (by rfl) ⟨1072433, by rfl⟩ : syracuseStep 1429911 = 2144867) B2144867
theorem B1429931 : Blo 1429534 1429931 := bstep (se 1 (by rfl) ⟨1072448, by rfl⟩ : syracuseStep 1429931 = 2144897) B2144897
theorem B7246259 : Blo 1429534 7246259 := bstep (se 1 (by rfl) ⟨5434694, by rfl⟩ : syracuseStep 7246259 = 10869389) B10869389
theorem B1429943 : Blo 1429534 1429943 := bstep (se 1 (by rfl) ⟨1072457, by rfl⟩ : syracuseStep 1429943 = 2144915) B2144915
theorem B1610167 : Blo 1429534 1610167 := bstep (se 1 (by rfl) ⟨1207625, by rfl⟩ : syracuseStep 1610167 = 2415251) B2415251
theorem B2290123 : Blo 1429534 2290123 := bstep (se 1 (by rfl) ⟨1717592, by rfl⟩ : syracuseStep 2290123 = 3435185) B3435185
theorem B2413003 : Blo 1429534 2413003 := bstep (se 1 (by rfl) ⟨1809752, by rfl⟩ : syracuseStep 2413003 = 3619505) B3619505
theorem B1429963 : Blo 1429534 1429963 := bstep (se 1 (by rfl) ⟨1072472, by rfl⟩ : syracuseStep 1429963 = 2144945) B2144945
theorem B1429975 : Blo 1429534 1429975 := bstep (se 1 (by rfl) ⟨1072481, by rfl⟩ : syracuseStep 1429975 = 2144963) B2144963
theorem B1429995 : Blo 1429534 1429995 := bstep (se 1 (by rfl) ⟨1072496, by rfl⟩ : syracuseStep 1429995 = 2144993) B2144993
theorem B1430007 : Blo 1429534 1430007 := bstep (se 1 (by rfl) ⟨1072505, by rfl⟩ : syracuseStep 1430007 = 2145011) B2145011
theorem B1430027 : Blo 1429534 1430027 := bstep (se 1 (by rfl) ⟨1072520, by rfl⟩ : syracuseStep 1430027 = 2145041) B2145041
theorem B2290199 : Blo 1429534 2290199 := bstep (se 1 (by rfl) ⟨1717649, by rfl⟩ : syracuseStep 2290199 = 3435299) B3435299
theorem B1430039 : Blo 1429534 1430039 := bstep (se 1 (by rfl) ⟨1072529, by rfl⟩ : syracuseStep 1430039 = 2145059) B2145059
theorem B1430059 : Blo 1429534 1430059 := bstep (se 1 (by rfl) ⟨1072544, by rfl⟩ : syracuseStep 1430059 = 2145089) B2145089
theorem B1430071 : Blo 1429534 1430071 := bstep (se 1 (by rfl) ⟨1072553, by rfl⟩ : syracuseStep 1430071 = 2145107) B2145107
theorem B1430091 : Blo 1429534 1430091 := bstep (se 1 (by rfl) ⟨1072568, by rfl⟩ : syracuseStep 1430091 = 2145137) B2145137
theorem B1430103 : Blo 1429534 1430103 := bstep (se 1 (by rfl) ⟨1072577, by rfl⟩ : syracuseStep 1430103 = 2145155) B2145155
theorem B2716247 : Blo 1429534 2716247 := bstep (se 1 (by rfl) ⟨2037185, by rfl⟩ : syracuseStep 2716247 = 4074371) B4074371
theorem B2413145 : Blo 1429534 2413145 := bstep (se 2 (by rfl) ⟨904929, by rfl⟩ : syracuseStep 2413145 = 1809859) B1809859
theorem B1430123 : Blo 1429534 1430123 := bstep (se 1 (by rfl) ⟨1072592, by rfl⟩ : syracuseStep 1430123 = 2145185) B2145185
theorem B1610347 : Blo 1429534 1610347 := bstep (se 1 (by rfl) ⟨1207760, by rfl⟩ : syracuseStep 1610347 = 2415521) B2415521
theorem B1430135 : Blo 1429534 1430135 := bstep (se 1 (by rfl) ⟨1072601, by rfl⟩ : syracuseStep 1430135 = 2145203) B2145203
theorem B12219011 : Blo 1429534 12219011 := bstep (se 1 (by rfl) ⟨9164258, by rfl⟩ : syracuseStep 12219011 = 18328517) B18328517
theorem B1430155 : Blo 1429534 1430155 := bstep (se 1 (by rfl) ⟨1072616, by rfl⟩ : syracuseStep 1430155 = 2145233) B2145233
theorem B1430167 : Blo 1429534 1430167 := bstep (se 1 (by rfl) ⟨1072625, by rfl⟩ : syracuseStep 1430167 = 2145251) B2145251
theorem B1430187 : Blo 1429534 1430187 := bstep (se 1 (by rfl) ⟨1072640, by rfl⟩ : syracuseStep 1430187 = 2145281) B2145281
theorem B1430199 : Blo 1429534 1430199 := bstep (se 1 (by rfl) ⟨1072649, by rfl⟩ : syracuseStep 1430199 = 2145299) B2145299
theorem B1430219 : Blo 1429534 1430219 := bstep (se 1 (by rfl) ⟨1072664, by rfl⟩ : syracuseStep 1430219 = 2145329) B2145329
theorem B1430231 : Blo 1429534 1430231 := bstep (se 1 (by rfl) ⟨1072673, by rfl⟩ : syracuseStep 1430231 = 2145347) B2145347
theorem B1610455 : Blo 1429534 1610455 := bstep (se 1 (by rfl) ⟨1207841, by rfl⟩ : syracuseStep 1610455 = 2415683) B2415683
theorem B2413273 : Blo 1429534 2413273 := bstep (se 2 (by rfl) ⟨904977, by rfl⟩ : syracuseStep 2413273 = 1809955) B1809955
theorem B1430251 : Blo 1429534 1430251 := bstep (se 1 (by rfl) ⟨1072688, by rfl⟩ : syracuseStep 1430251 = 2145377) B2145377
theorem B1430263 : Blo 1429534 1430263 := bstep (se 1 (by rfl) ⟨1072697, by rfl⟩ : syracuseStep 1430263 = 2145395) B2145395
theorem B1430283 : Blo 1429534 1430283 := bstep (se 1 (by rfl) ⟨1072712, by rfl⟩ : syracuseStep 1430283 = 2145425) B2145425
theorem B1430295 : Blo 1429534 1430295 := bstep (se 1 (by rfl) ⟨1072721, by rfl⟩ : syracuseStep 1430295 = 2145443) B2145443
theorem B4829975 : Blo 1429534 4829975 := bstep (se 1 (by rfl) ⟨3622481, by rfl⟩ : syracuseStep 4829975 = 7244963) B7244963
theorem B1430315 : Blo 1429534 1430315 := bstep (se 1 (by rfl) ⟨1072736, by rfl⟩ : syracuseStep 1430315 = 2145473) B2145473
theorem B5583661 : Blo 1429534 5583661 := bstep (se 3 (by rfl) ⟨1046936, by rfl⟩ : syracuseStep 5583661 = 2093873) B2093873
theorem B1430327 : Blo 1429534 1430327 := bstep (se 1 (by rfl) ⟨1072745, by rfl⟩ : syracuseStep 1430327 = 2145491) B2145491
theorem B5428043 : Blo 1429534 5428043 := bstep (se 1 (by rfl) ⟨4071032, by rfl⟩ : syracuseStep 5428043 = 8142065) B8142065
theorem B1430347 : Blo 1429534 1430347 := bstep (se 1 (by rfl) ⟨1072760, by rfl⟩ : syracuseStep 1430347 = 2145521) B2145521
theorem B1430359 : Blo 1429534 1430359 := bstep (se 1 (by rfl) ⟨1072769, by rfl⟩ : syracuseStep 1430359 = 2145539) B2145539
theorem B1430379 : Blo 1429534 1430379 := bstep (se 1 (by rfl) ⟨1072784, by rfl⟩ : syracuseStep 1430379 = 2145569) B2145569
theorem B1430391 : Blo 1429534 1430391 := bstep (se 1 (by rfl) ⟨1072793, by rfl⟩ : syracuseStep 1430391 = 2145587) B2145587
theorem B1430411 : Blo 1429534 1430411 := bstep (se 1 (by rfl) ⟨1072808, by rfl⟩ : syracuseStep 1430411 = 2145617) B2145617
theorem B1430423 : Blo 1429534 1430423 := bstep (se 1 (by rfl) ⟨1072817, by rfl⟩ : syracuseStep 1430423 = 2145635) B2145635
theorem B1430443 : Blo 1429534 1430443 := bstep (se 1 (by rfl) ⟨1072832, by rfl⟩ : syracuseStep 1430443 = 2145665) B2145665
theorem B1430455 : Blo 1429534 1430455 := bstep (se 1 (by rfl) ⟨1072841, by rfl⟩ : syracuseStep 1430455 = 2145683) B2145683
theorem B1430475 : Blo 1429534 1430475 := bstep (se 1 (by rfl) ⟨1072856, by rfl⟩ : syracuseStep 1430475 = 2145713) B2145713
theorem B1430487 : Blo 1429534 1430487 := bstep (se 1 (by rfl) ⟨1072865, by rfl⟩ : syracuseStep 1430487 = 2145731) B2145731
theorem B1430507 : Blo 1429534 1430507 := bstep (se 1 (by rfl) ⟨1072880, by rfl⟩ : syracuseStep 1430507 = 2145761) B2145761
theorem B1430519 : Blo 1429534 1430519 := bstep (se 1 (by rfl) ⟨1072889, by rfl⟩ : syracuseStep 1430519 = 2145779) B2145779
theorem B1430539 : Blo 1429534 1430539 := bstep (se 1 (by rfl) ⟨1072904, by rfl⟩ : syracuseStep 1430539 = 2145809) B2145809
theorem B5428241 : Blo 1429534 5428241 := bstep (se 2 (by rfl) ⟨2035590, by rfl⟩ : syracuseStep 5428241 = 4071181) B4071181
theorem B1430551 : Blo 1429534 1430551 := bstep (se 1 (by rfl) ⟨1072913, by rfl⟩ : syracuseStep 1430551 = 2145827) B2145827
theorem B1430571 : Blo 1429534 1430571 := bstep (se 1 (by rfl) ⟨1072928, by rfl⟩ : syracuseStep 1430571 = 2145857) B2145857
theorem B1430583 : Blo 1429534 1430583 := bstep (se 1 (by rfl) ⟨1072937, by rfl⟩ : syracuseStep 1430583 = 2145875) B2145875
theorem B1430603 : Blo 1429534 1430603 := bstep (se 1 (by rfl) ⟨1072952, by rfl⟩ : syracuseStep 1430603 = 2145905) B2145905
theorem B1430615 : Blo 1429534 1430615 := bstep (se 1 (by rfl) ⟨1072961, by rfl⟩ : syracuseStep 1430615 = 2145923) B2145923
theorem B3216473 : Blo 1429534 3216473 := bstep (se 2 (by rfl) ⟨1206177, by rfl⟩ : syracuseStep 3216473 = 2412355) B2412355
theorem B6616153 : Blo 1429534 6616153 := bstep (se 2 (by rfl) ⟨2481057, by rfl⟩ : syracuseStep 6616153 = 4962115) B4962115
theorem B1430635 : Blo 1429534 1430635 := bstep (se 1 (by rfl) ⟨1072976, by rfl⟩ : syracuseStep 1430635 = 2145953) B2145953
theorem B1430647 : Blo 1429534 1430647 := bstep (se 1 (by rfl) ⟨1072985, by rfl⟩ : syracuseStep 1430647 = 2145971) B2145971
theorem B1430667 : Blo 1429534 1430667 := bstep (se 1 (by rfl) ⟨1073000, by rfl⟩ : syracuseStep 1430667 = 2146001) B2146001
theorem B7238807 : Blo 1429534 7238807 := bstep (se 1 (by rfl) ⟨5429105, by rfl⟩ : syracuseStep 7238807 = 10858211) B10858211
theorem B2446487 : Blo 1429534 2446487 := bstep (se 1 (by rfl) ⟨1834865, by rfl⟩ : syracuseStep 2446487 = 3669731) B3669731
theorem B1430679 : Blo 1429534 1430679 := bstep (se 1 (by rfl) ⟨1073009, by rfl⟩ : syracuseStep 1430679 = 2146019) B2146019
theorem B1430699 : Blo 1429534 1430699 := bstep (se 1 (by rfl) ⟨1073024, by rfl⟩ : syracuseStep 1430699 = 2146049) B2146049
theorem B3216563 : Blo 1429534 3216563 := bstep (se 1 (by rfl) ⟨2412422, by rfl⟩ : syracuseStep 3216563 = 4824845) B4824845
theorem B1430711 : Blo 1429534 1430711 := bstep (se 1 (by rfl) ⟨1073033, by rfl⟩ : syracuseStep 1430711 = 2146067) B2146067
theorem B1430731 : Blo 1429534 1430731 := bstep (se 1 (by rfl) ⟨1073048, by rfl⟩ : syracuseStep 1430731 = 2146097) B2146097
theorem B3216599 : Blo 1429534 3216599 := bstep (se 1 (by rfl) ⟨2412449, by rfl⟩ : syracuseStep 3216599 = 4824899) B4824899
theorem B1430743 : Blo 1429534 1430743 := bstep (se 1 (by rfl) ⟨1073057, by rfl⟩ : syracuseStep 1430743 = 2146115) B2146115
theorem B1430763 : Blo 1429534 1430763 := bstep (se 1 (by rfl) ⟨1073072, by rfl⟩ : syracuseStep 1430763 = 2146145) B2146145
theorem B2716915 : Blo 1429534 2716915 := bstep (se 1 (by rfl) ⟨2037686, by rfl⟩ : syracuseStep 2716915 = 4075373) B4075373
theorem B1430775 : Blo 1429534 1430775 := bstep (se 1 (by rfl) ⟨1073081, by rfl⟩ : syracuseStep 1430775 = 2146163) B2146163
theorem B1430795 : Blo 1429534 1430795 := bstep (se 1 (by rfl) ⟨1073096, by rfl⟩ : syracuseStep 1430795 = 2146193) B2146193
theorem B2413847 : Blo 1429534 2413847 := bstep (se 1 (by rfl) ⟨1810385, by rfl⟩ : syracuseStep 2413847 = 3620771) B3620771
theorem B1430807 : Blo 1429534 1430807 := bstep (se 1 (by rfl) ⟨1073105, by rfl⟩ : syracuseStep 1430807 = 2146211) B2146211
theorem B1430827 : Blo 1429534 1430827 := bstep (se 1 (by rfl) ⟨1073120, by rfl⟩ : syracuseStep 1430827 = 2146241) B2146241
theorem B4830515 : Blo 1429534 4830515 := bstep (se 1 (by rfl) ⟨3622886, by rfl⟩ : syracuseStep 4830515 = 7245773) B7245773
theorem B1430839 : Blo 1429534 1430839 := bstep (se 1 (by rfl) ⟨1073129, by rfl⟩ : syracuseStep 1430839 = 2146259) B2146259
theorem B1430859 : Blo 1429534 1430859 := bstep (se 1 (by rfl) ⟨1073144, by rfl⟩ : syracuseStep 1430859 = 2146289) B2146289
theorem B1430871 : Blo 1429534 1430871 := bstep (se 1 (by rfl) ⟨1073153, by rfl⟩ : syracuseStep 1430871 = 2146307) B2146307
theorem B1430891 : Blo 1429534 1430891 := bstep (se 1 (by rfl) ⟨1073168, by rfl⟩ : syracuseStep 1430891 = 2146337) B2146337
theorem B1430903 : Blo 1429534 1430903 := bstep (se 1 (by rfl) ⟨1073177, by rfl⟩ : syracuseStep 1430903 = 2146355) B2146355
theorem B3216779 : Blo 1429534 3216779 := bstep (se 1 (by rfl) ⟨2412584, by rfl⟩ : syracuseStep 3216779 = 4825169) B4825169
theorem B1430923 : Blo 1429534 1430923 := bstep (se 1 (by rfl) ⟨1073192, by rfl⟩ : syracuseStep 1430923 = 2146385) B2146385
theorem B2413975 : Blo 1429534 2413975 := bstep (se 1 (by rfl) ⟨1810481, by rfl⟩ : syracuseStep 2413975 = 3620963) B3620963
theorem B1430935 : Blo 1429534 1430935 := bstep (se 1 (by rfl) ⟨1073201, by rfl⟩ : syracuseStep 1430935 = 2146403) B2146403
theorem B2037145 : Blo 1429534 2037145 := bstep (se 2 (by rfl) ⟨763929, by rfl⟩ : syracuseStep 2037145 = 1527859) B1527859
theorem B1430955 : Blo 1429534 1430955 := bstep (se 1 (by rfl) ⟨1073216, by rfl⟩ : syracuseStep 1430955 = 2146433) B2146433
theorem B1430967 : Blo 1429534 1430967 := bstep (se 1 (by rfl) ⟨1073225, by rfl⟩ : syracuseStep 1430967 = 2146451) B2146451
theorem B3216833 : Blo 1429534 3216833 := bstep (se 2 (by rfl) ⟨1206312, by rfl⟩ : syracuseStep 3216833 = 2412625) B2412625
theorem B1430987 : Blo 1429534 1430987 := bstep (se 1 (by rfl) ⟨1073240, by rfl⟩ : syracuseStep 1430987 = 2146481) B2146481
theorem B1430999 : Blo 1429534 1430999 := bstep (se 1 (by rfl) ⟨1073249, by rfl⟩ : syracuseStep 1430999 = 2146499) B2146499
theorem B1431019 : Blo 1429534 1431019 := bstep (se 1 (by rfl) ⟨1073264, by rfl⟩ : syracuseStep 1431019 = 2146529) B2146529
theorem B1431031 : Blo 1429534 1431031 := bstep (se 1 (by rfl) ⟨1073273, by rfl⟩ : syracuseStep 1431031 = 2146547) B2146547
theorem B2037259 : Blo 1429534 2037259 := bstep (se 1 (by rfl) ⟨1527944, by rfl⟩ : syracuseStep 2037259 = 3055889) B3055889
theorem B1431051 : Blo 1429534 1431051 := bstep (se 1 (by rfl) ⟨1073288, by rfl⟩ : syracuseStep 1431051 = 2146577) B2146577
theorem B1431063 : Blo 1429534 1431063 := bstep (se 1 (by rfl) ⟨1073297, by rfl⟩ : syracuseStep 1431063 = 2146595) B2146595
theorem B1431083 : Blo 1429534 1431083 := bstep (se 1 (by rfl) ⟨1073312, by rfl⟩ : syracuseStep 1431083 = 2146625) B2146625
theorem B1431095 : Blo 1429534 1431095 := bstep (se 1 (by rfl) ⟨1073321, by rfl⟩ : syracuseStep 1431095 = 2146643) B2146643
theorem B4830785 : Blo 1429534 4830785 := bstep (se 2 (by rfl) ⟨1811544, by rfl⟩ : syracuseStep 4830785 = 3623089) B3623089
theorem B1431115 : Blo 1429534 1431115 := bstep (se 1 (by rfl) ⟨1073336, by rfl⟩ : syracuseStep 1431115 = 2146673) B2146673
theorem B1570379 : Blo 1429534 1570379 := bstep (se 1 (by rfl) ⟨1177784, by rfl⟩ : syracuseStep 1570379 = 2355569) B2355569
theorem B1431127 : Blo 1429534 1431127 := bstep (se 1 (by rfl) ⟨1073345, by rfl⟩ : syracuseStep 1431127 = 2146691) B2146691
theorem B1431147 : Blo 1429534 1431147 := bstep (se 1 (by rfl) ⟨1073360, by rfl⟩ : syracuseStep 1431147 = 2146721) B2146721
theorem B1431159 : Blo 1429534 1431159 := bstep (se 1 (by rfl) ⟨1073369, by rfl⟩ : syracuseStep 1431159 = 2146739) B2146739
theorem B1431179 : Blo 1429534 1431179 := bstep (se 1 (by rfl) ⟨1073384, by rfl⟩ : syracuseStep 1431179 = 2146769) B2146769
theorem B3053207 : Blo 1429534 3053207 := bstep (se 1 (by rfl) ⟨2289905, by rfl⟩ : syracuseStep 3053207 = 4579811) B4579811
theorem B1431191 : Blo 1429534 1431191 := bstep (se 1 (by rfl) ⟨1073393, by rfl⟩ : syracuseStep 1431191 = 2146787) B2146787
theorem B3217049 : Blo 1429534 3217049 := bstep (se 2 (by rfl) ⟨1206393, by rfl⟩ : syracuseStep 3217049 = 2412787) B2412787
theorem B1431211 : Blo 1429534 1431211 := bstep (se 1 (by rfl) ⟨1073408, by rfl⟩ : syracuseStep 1431211 = 2146817) B2146817
theorem B2717363 : Blo 1429534 2717363 := bstep (se 1 (by rfl) ⟨2038022, by rfl⟩ : syracuseStep 2717363 = 4076045) B4076045
theorem B1431223 : Blo 1429534 1431223 := bstep (se 1 (by rfl) ⟨1073417, by rfl⟩ : syracuseStep 1431223 = 2146835) B2146835
theorem B1431243 : Blo 1429534 1431243 := bstep (se 1 (by rfl) ⟨1073432, by rfl⟩ : syracuseStep 1431243 = 2146865) B2146865
theorem B1431255 : Blo 1429534 1431255 := bstep (se 1 (by rfl) ⟨1073441, by rfl⟩ : syracuseStep 1431255 = 2146883) B2146883
theorem B2717401 : Blo 1429534 2717401 := bstep (se 2 (by rfl) ⟨1019025, by rfl⟩ : syracuseStep 2717401 = 2038051) B2038051
theorem B1431275 : Blo 1429534 1431275 := bstep (se 1 (by rfl) ⟨1073456, by rfl⟩ : syracuseStep 1431275 = 2146913) B2146913
theorem B3217139 : Blo 1429534 3217139 := bstep (se 1 (by rfl) ⟨2412854, by rfl⟩ : syracuseStep 3217139 = 4825709) B4825709
theorem B1431287 : Blo 1429534 1431287 := bstep (se 1 (by rfl) ⟨1073465, by rfl⟩ : syracuseStep 1431287 = 2146931) B2146931
theorem B1431307 : Blo 1429534 1431307 := bstep (se 1 (by rfl) ⟨1073480, by rfl⟩ : syracuseStep 1431307 = 2146961) B2146961
theorem B3217175 : Blo 1429534 3217175 := bstep (se 1 (by rfl) ⟨2412881, by rfl⟩ : syracuseStep 3217175 = 4825763) B4825763
theorem B5429015 : Blo 1429534 5429015 := bstep (se 1 (by rfl) ⟨4071761, by rfl⟩ : syracuseStep 5429015 = 8143523) B8143523
theorem B1431319 : Blo 1429534 1431319 := bstep (se 1 (by rfl) ⟨1073489, by rfl⟩ : syracuseStep 1431319 = 2146979) B2146979
theorem B1431339 : Blo 1429534 1431339 := bstep (se 1 (by rfl) ⟨1073504, by rfl⟩ : syracuseStep 1431339 = 2147009) B2147009
theorem B1431351 : Blo 1429534 1431351 := bstep (se 1 (by rfl) ⟨1073513, by rfl⟩ : syracuseStep 1431351 = 2147027) B2147027
theorem B1431371 : Blo 1429534 1431371 := bstep (se 1 (by rfl) ⟨1073528, by rfl⟩ : syracuseStep 1431371 = 2147057) B2147057
theorem B1431383 : Blo 1429534 1431383 := bstep (se 1 (by rfl) ⟨1073537, by rfl⟩ : syracuseStep 1431383 = 2147075) B2147075
theorem B1431403 : Blo 1429534 1431403 := bstep (se 1 (by rfl) ⟨1073552, by rfl⟩ : syracuseStep 1431403 = 2147105) B2147105
theorem B1431415 : Blo 1429534 1431415 := bstep (se 1 (by rfl) ⟨1073561, by rfl⟩ : syracuseStep 1431415 = 2147123) B2147123
theorem B1431435 : Blo 1429534 1431435 := bstep (se 1 (by rfl) ⟨1073576, by rfl⟩ : syracuseStep 1431435 = 2147153) B2147153
theorem B1431447 : Blo 1429534 1431447 := bstep (se 1 (by rfl) ⟨1073585, by rfl⟩ : syracuseStep 1431447 = 2147171) B2147171
theorem B2291609 : Blo 1429534 2291609 := bstep (se 2 (by rfl) ⟨859353, by rfl⟩ : syracuseStep 2291609 = 1718707) B1718707
theorem B1431467 : Blo 1429534 1431467 := bstep (se 1 (by rfl) ⟨1073600, by rfl⟩ : syracuseStep 1431467 = 2147201) B2147201
theorem B1431479 : Blo 1429534 1431479 := bstep (se 1 (by rfl) ⟨1073609, by rfl⟩ : syracuseStep 1431479 = 2147219) B2147219
theorem B3217355 : Blo 1429534 3217355 := bstep (se 1 (by rfl) ⟨2413016, by rfl⟩ : syracuseStep 3217355 = 4826033) B4826033
theorem B1431499 : Blo 1429534 1431499 := bstep (se 1 (by rfl) ⟨1073624, by rfl⟩ : syracuseStep 1431499 = 2147249) B2147249
theorem B1431511 : Blo 1429534 1431511 := bstep (se 1 (by rfl) ⟨1073633, by rfl⟩ : syracuseStep 1431511 = 2147267) B2147267
theorem B5429213 : Blo 1429534 5429213 := bstep (se 3 (by rfl) ⟨1017977, by rfl⟩ : syracuseStep 5429213 = 2035955) B2035955
theorem B1431531 : Blo 1429534 1431531 := bstep (se 1 (by rfl) ⟨1073648, by rfl⟩ : syracuseStep 1431531 = 2147297) B2147297
theorem B3217409 : Blo 1429534 3217409 := bstep (se 2 (by rfl) ⟨1206528, by rfl⟩ : syracuseStep 3217409 = 2413057) B2413057
theorem B2414603 : Blo 1429534 2414603 := bstep (se 1 (by rfl) ⟨1810952, by rfl⟩ : syracuseStep 2414603 = 3621905) B3621905
theorem B2291737 : Blo 1429534 2291737 := bstep (se 2 (by rfl) ⟨859401, by rfl⟩ : syracuseStep 2291737 = 1718803) B1718803
theorem B8706113 : Blo 1429534 8706113 := bstep (se 2 (by rfl) ⟨3264792, by rfl⟩ : syracuseStep 8706113 = 6529585) B6529585
theorem B2144345 : Blo 1429534 2144345 := bstep (se 2 (by rfl) ⟨804129, by rfl⟩ : syracuseStep 2144345 = 1608259) B1608259
theorem B4831325 : Blo 1429534 4831325 := bstep (se 3 (by rfl) ⟨905873, by rfl⟩ : syracuseStep 4831325 = 1811747) B1811747
theorem B2414731 : Blo 1429534 2414731 := bstep (se 1 (by rfl) ⟨1811048, by rfl⟩ : syracuseStep 2414731 = 3622097) B3622097
theorem B2144459 : Blo 1429534 2144459 := bstep (se 1 (by rfl) ⟨1608344, by rfl⟩ : syracuseStep 2144459 = 3216689) B3216689
theorem B3619019 : Blo 1429534 3619019 := bstep (se 1 (by rfl) ⟨2714264, by rfl⟩ : syracuseStep 3619019 = 5428529) B5428529
theorem B2144471 : Blo 1429534 2144471 := bstep (se 1 (by rfl) ⟨1608353, by rfl⟩ : syracuseStep 2144471 = 3216707) B3216707
theorem B5798105 : Blo 1429534 5798105 := bstep (se 2 (by rfl) ⟨2174289, by rfl⟩ : syracuseStep 5798105 = 4348579) B4348579
theorem B3217625 : Blo 1429534 3217625 := bstep (se 2 (by rfl) ⟨1206609, by rfl⟩ : syracuseStep 3217625 = 2413219) B2413219
theorem B6527249 : Blo 1429534 6527249 := bstep (se 2 (by rfl) ⟨2447718, by rfl⟩ : syracuseStep 6527249 = 4895437) B4895437
theorem B2144537 : Blo 1429534 2144537 := bstep (se 2 (by rfl) ⟨804201, by rfl⟩ : syracuseStep 2144537 = 1608403) B1608403
theorem B2414873 : Blo 1429534 2414873 := bstep (se 2 (by rfl) ⟨905577, by rfl⟩ : syracuseStep 2414873 = 1811155) B1811155
theorem B3217715 : Blo 1429534 3217715 := bstep (se 1 (by rfl) ⟨2413286, by rfl⟩ : syracuseStep 3217715 = 4826573) B4826573
theorem B3217751 : Blo 1429534 3217751 := bstep (se 1 (by rfl) ⟨2413313, by rfl⟩ : syracuseStep 3217751 = 4826627) B4826627
theorem B2144651 : Blo 1429534 2144651 := bstep (se 1 (by rfl) ⟨1608488, by rfl⟩ : syracuseStep 2144651 = 3216977) B3216977
theorem B2144663 : Blo 1429534 2144663 := bstep (se 1 (by rfl) ⟨1608497, by rfl⟩ : syracuseStep 2144663 = 3216995) B3216995
theorem B2415001 : Blo 1429534 2415001 := bstep (se 2 (by rfl) ⟨905625, by rfl⟩ : syracuseStep 2415001 = 1811251) B1811251
theorem B11164081 : Blo 1429534 11164081 := bstep (se 2 (by rfl) ⟨4186530, by rfl⟩ : syracuseStep 11164081 = 8373061) B8373061
theorem B3668417 : Blo 1429534 3668417 := bstep (se 2 (by rfl) ⟨1375656, by rfl⟩ : syracuseStep 3668417 = 2751313) B2751313
theorem B2144729 : Blo 1429534 2144729 := bstep (se 2 (by rfl) ⟨804273, by rfl⟩ : syracuseStep 2144729 = 1608547) B1608547
theorem B3217931 : Blo 1429534 3217931 := bstep (se 1 (by rfl) ⟨2413448, by rfl⟩ : syracuseStep 3217931 = 4826897) B4826897
theorem B2578969 : Blo 1429534 2578969 := bstep (se 2 (by rfl) ⟨967113, by rfl⟩ : syracuseStep 2578969 = 1934227) B1934227
theorem B11008547 : Blo 1429534 11008547 := bstep (se 1 (by rfl) ⟨8256410, by rfl⟩ : syracuseStep 11008547 = 16512821) B16512821
theorem B3217985 : Blo 1429534 3217985 := bstep (se 2 (by rfl) ⟨1206744, by rfl⟩ : syracuseStep 3217985 = 2413489) B2413489
theorem B2144843 : Blo 1429534 2144843 := bstep (se 1 (by rfl) ⟨1608632, by rfl⟩ : syracuseStep 2144843 = 3217265) B3217265
theorem B2144855 : Blo 1429534 2144855 := bstep (se 1 (by rfl) ⟨1608641, by rfl⟩ : syracuseStep 2144855 = 3217283) B3217283
theorem B44022365 : Blo 1429534 44022365 := bstep (se 3 (by rfl) ⟨8254193, by rfl⟩ : syracuseStep 44022365 = 16508387) B16508387
theorem B2144921 : Blo 1429534 2144921 := bstep (se 2 (by rfl) ⟨804345, by rfl⟩ : syracuseStep 2144921 = 1608691) B1608691
theorem B3439297 : Blo 1429534 3439297 := bstep (se 2 (by rfl) ⟨1289736, by rfl⟩ : syracuseStep 3439297 = 2579473) B2579473
theorem B2145035 : Blo 1429534 2145035 := bstep (se 1 (by rfl) ⟨1608776, by rfl⟩ : syracuseStep 2145035 = 3217553) B3217553
theorem B2145047 : Blo 1429534 2145047 := bstep (se 1 (by rfl) ⟨1608785, by rfl⟩ : syracuseStep 2145047 = 3217571) B3217571
theorem B3218201 : Blo 1429534 3218201 := bstep (se 2 (by rfl) ⟨1206825, by rfl⟩ : syracuseStep 3218201 = 2413651) B2413651
theorem B11606819 : Blo 1429534 11606819 := bstep (se 1 (by rfl) ⟨8705114, by rfl⟩ : syracuseStep 11606819 = 17410229) B17410229
theorem B2145113 : Blo 1429534 2145113 := bstep (se 2 (by rfl) ⟨804417, by rfl⟩ : syracuseStep 2145113 = 1608835) B1608835
theorem B3218291 : Blo 1429534 3218291 := bstep (se 1 (by rfl) ⟨2413718, by rfl⟩ : syracuseStep 3218291 = 4827437) B4827437
theorem B3218327 : Blo 1429534 3218327 := bstep (se 1 (by rfl) ⟨2413745, by rfl⟩ : syracuseStep 3218327 = 4827491) B4827491
theorem B16513969 : Blo 1429534 16513969 := bstep (se 2 (by rfl) ⟨6192738, by rfl⟩ : syracuseStep 16513969 = 12385477) B12385477
theorem B2145227 : Blo 1429534 2145227 := bstep (se 1 (by rfl) ⟨1608920, by rfl⟩ : syracuseStep 2145227 = 3217841) B3217841
theorem B2145239 : Blo 1429534 2145239 := bstep (se 1 (by rfl) ⟨1608929, by rfl⟩ : syracuseStep 2145239 = 3217859) B3217859
theorem B66059225 : Blo 1429534 66059225 := bstep (se 2 (by rfl) ⟨24772209, by rfl⟩ : syracuseStep 66059225 = 49544419) B49544419
theorem B2415575 : Blo 1429534 2415575 := bstep (se 1 (by rfl) ⟨1811681, by rfl⟩ : syracuseStep 2415575 = 3623363) B3623363
theorem B2145305 : Blo 1429534 2145305 := bstep (se 2 (by rfl) ⟨804489, by rfl⟩ : syracuseStep 2145305 = 1608979) B1608979
theorem B10861613 : Blo 1429534 10861613 := bstep (se 3 (by rfl) ⟨2036552, by rfl⟩ : syracuseStep 10861613 = 4073105) B4073105
theorem B3218507 : Blo 1429534 3218507 := bstep (se 1 (by rfl) ⟨2413880, by rfl⟩ : syracuseStep 3218507 = 4827761) B4827761
theorem B9165899 : Blo 1429534 9165899 := bstep (se 1 (by rfl) ⟨6874424, by rfl⟩ : syracuseStep 9165899 = 13748849) B13748849
theorem B2415703 : Blo 1429534 2415703 := bstep (se 1 (by rfl) ⟨1811777, by rfl⟩ : syracuseStep 2415703 = 3623555) B3623555
theorem B3218561 : Blo 1429534 3218561 := bstep (se 2 (by rfl) ⟨1206960, by rfl⟩ : syracuseStep 3218561 = 2413921) B2413921
theorem B2145419 : Blo 1429534 2145419 := bstep (se 1 (by rfl) ⟨1609064, by rfl⟩ : syracuseStep 2145419 = 3218129) B3218129
theorem B3619991 : Blo 1429534 3619991 := bstep (se 1 (by rfl) ⟨2714993, by rfl⟩ : syracuseStep 3619991 = 5429987) B5429987
theorem B2145431 : Blo 1429534 2145431 := bstep (se 1 (by rfl) ⟨1609073, by rfl⟩ : syracuseStep 2145431 = 3218147) B3218147
theorem B2145497 : Blo 1429534 2145497 := bstep (se 2 (by rfl) ⟨804561, by rfl⟩ : syracuseStep 2145497 = 1609123) B1609123
theorem B4128023 : Blo 1429534 4128023 := bstep (se 1 (by rfl) ⟨3096017, by rfl⟩ : syracuseStep 4128023 = 6192035) B6192035
theorem B5504321 : Blo 1429534 5504321 := bstep (se 2 (by rfl) ⟨2064120, by rfl⟩ : syracuseStep 5504321 = 4128241) B4128241
theorem B11754827 : Blo 1429534 11754827 := bstep (se 1 (by rfl) ⟨8816120, by rfl⟩ : syracuseStep 11754827 = 17632241) B17632241
theorem B2145611 : Blo 1429534 2145611 := bstep (se 1 (by rfl) ⟨1609208, by rfl⟩ : syracuseStep 2145611 = 3218417) B3218417
theorem B2145623 : Blo 1429534 2145623 := bstep (se 1 (by rfl) ⟨1609217, by rfl⟩ : syracuseStep 2145623 = 3218435) B3218435
theorem B3218777 : Blo 1429534 3218777 := bstep (se 2 (by rfl) ⟨1207041, by rfl⟩ : syracuseStep 3218777 = 2414083) B2414083
theorem B1809803 : Blo 1429534 1809803 := bstep (se 1 (by rfl) ⟨1357352, by rfl⟩ : syracuseStep 1809803 = 2714705) B2714705
theorem B6110615 : Blo 1429534 6110615 := bstep (se 1 (by rfl) ⟨4582961, by rfl⟩ : syracuseStep 6110615 = 9165923) B9165923
theorem B2145689 : Blo 1429534 2145689 := bstep (se 2 (by rfl) ⟨804633, by rfl⟩ : syracuseStep 2145689 = 1609267) B1609267
theorem B3218867 : Blo 1429534 3218867 := bstep (se 1 (by rfl) ⟨2414150, by rfl⟩ : syracuseStep 3218867 = 4828301) B4828301
theorem B3218903 : Blo 1429534 3218903 := bstep (se 1 (by rfl) ⟨2414177, by rfl⟩ : syracuseStep 3218903 = 4828355) B4828355
theorem B4070873 : Blo 1429534 4070873 := bstep (se 2 (by rfl) ⟨1526577, by rfl⟩ : syracuseStep 4070873 = 3053155) B3053155
theorem B2145803 : Blo 1429534 2145803 := bstep (se 1 (by rfl) ⟨1609352, by rfl⟩ : syracuseStep 2145803 = 3218705) B3218705
theorem B2145815 : Blo 1429534 2145815 := bstep (se 1 (by rfl) ⟨1609361, by rfl⟩ : syracuseStep 2145815 = 3218723) B3218723
theorem B5226059 : Blo 1429534 5226059 := bstep (se 1 (by rfl) ⟨3919544, by rfl⟩ : syracuseStep 5226059 = 7839089) B7839089
theorem B2145881 : Blo 1429534 2145881 := bstep (se 2 (by rfl) ⟨804705, by rfl⟩ : syracuseStep 2145881 = 1609411) B1609411
theorem B3219083 : Blo 1429534 3219083 := bstep (se 1 (by rfl) ⟨2414312, by rfl⟩ : syracuseStep 3219083 = 4828625) B4828625
theorem B3219137 : Blo 1429534 3219137 := bstep (se 2 (by rfl) ⟨1207176, by rfl⟩ : syracuseStep 3219137 = 2414353) B2414353
theorem B6110923 : Blo 1429534 6110923 := bstep (se 1 (by rfl) ⟨4583192, by rfl⟩ : syracuseStep 6110923 = 9166385) B9166385
theorem B2145995 : Blo 1429534 2145995 := bstep (se 1 (by rfl) ⟨1609496, by rfl⟩ : syracuseStep 2145995 = 3218993) B3218993
theorem B2146007 : Blo 1429534 2146007 := bstep (se 1 (by rfl) ⟨1609505, by rfl⟩ : syracuseStep 2146007 = 3219011) B3219011
theorem B2146073 : Blo 1429534 2146073 := bstep (se 2 (by rfl) ⟨804777, by rfl⟩ : syracuseStep 2146073 = 1609555) B1609555
theorem B18333485 : Blo 1429534 18333485 := bstep (se 3 (by rfl) ⟨3437528, by rfl⟩ : syracuseStep 18333485 = 6875057) B6875057
theorem B3620659 : Blo 1429534 3620659 := bstep (se 1 (by rfl) ⟨2715494, by rfl⟩ : syracuseStep 3620659 = 5430989) B5430989
theorem B4349747 : Blo 1429534 4349747 := bstep (se 1 (by rfl) ⟨3262310, by rfl⟩ : syracuseStep 4349747 = 6524621) B6524621
theorem B4128587 : Blo 1429534 4128587 := bstep (se 1 (by rfl) ⟨3096440, by rfl⟩ : syracuseStep 4128587 = 6192881) B6192881
theorem B5431171 : Blo 1429534 5431171 := bstep (se 1 (by rfl) ⟨4073378, by rfl⟩ : syracuseStep 5431171 = 8146757) B8146757
theorem B2146187 : Blo 1429534 2146187 := bstep (se 1 (by rfl) ⟨1609640, by rfl⟩ : syracuseStep 2146187 = 3219281) B3219281
theorem B2146199 : Blo 1429534 2146199 := bstep (se 1 (by rfl) ⟨1609649, by rfl⟩ : syracuseStep 2146199 = 3219299) B3219299
theorem B3219353 : Blo 1429534 3219353 := bstep (se 2 (by rfl) ⟨1207257, by rfl⟩ : syracuseStep 3219353 = 2414515) B2414515
theorem B47652785 : Blo 1429534 47652785 := bstep (se 2 (by rfl) ⟨17869794, by rfl⟩ : syracuseStep 47652785 = 35739589) B35739589
theorem B3620801 : Blo 1429534 3620801 := bstep (se 2 (by rfl) ⟨1357800, by rfl⟩ : syracuseStep 3620801 = 2715601) B2715601
theorem B15466457 : Blo 1429534 15466457 := bstep (se 2 (by rfl) ⟨5799921, by rfl⟩ : syracuseStep 15466457 = 11599843) B11599843
theorem B2146265 : Blo 1429534 2146265 := bstep (se 2 (by rfl) ⟨804849, by rfl⟩ : syracuseStep 2146265 = 1609699) B1609699
theorem B6111197 : Blo 1429534 6111197 := bstep (se 3 (by rfl) ⟨1145849, by rfl⟩ : syracuseStep 6111197 = 2291699) B2291699
theorem B3219443 : Blo 1429534 3219443 := bstep (se 1 (by rfl) ⟨2414582, by rfl⟩ : syracuseStep 3219443 = 4829165) B4829165
theorem B2146319 : Blo 1429534 2146319 := bstep (se 1 (by rfl) ⟨1609739, by rfl⟩ : syracuseStep 2146319 = 3219479) B3219479
theorem B3055649 : Blo 1429534 3055649 := bstep (se 2 (by rfl) ⟨1145868, by rfl⟩ : syracuseStep 3055649 = 2291737) B2291737
theorem B2146361 : Blo 1429534 2146361 := bstep (se 2 (by rfl) ⟨804885, by rfl⟩ : syracuseStep 2146361 = 1609771) B1609771
theorem B3219515 : Blo 1429534 3219515 := bstep (se 1 (by rfl) ⟨2414636, by rfl⟩ : syracuseStep 3219515 = 4829273) B4829273
theorem B5152835 : Blo 1429534 5152835 := bstep (se 1 (by rfl) ⟨3864626, by rfl⟩ : syracuseStep 5152835 = 7729253) B7729253
theorem B3620983 : Blo 1429534 3620983 := bstep (se 1 (by rfl) ⟨2715737, by rfl⟩ : syracuseStep 3620983 = 5431475) B5431475
theorem B3055735 : Blo 1429534 3055735 := bstep (se 1 (by rfl) ⟨2291801, by rfl⟩ : syracuseStep 3055735 = 4583603) B4583603
theorem B2146439 : Blo 1429534 2146439 := bstep (se 1 (by rfl) ⟨1609829, by rfl⟩ : syracuseStep 2146439 = 3219659) B3219659
theorem B1810603 : Blo 1429534 1810603 := bstep (se 1 (by rfl) ⟨1357952, by rfl⟩ : syracuseStep 1810603 = 2715905) B2715905
theorem B2146475 : Blo 1429534 2146475 := bstep (se 1 (by rfl) ⟨1609856, by rfl⟩ : syracuseStep 2146475 = 3219713) B3219713
theorem B3219641 : Blo 1429534 3219641 := bstep (se 2 (by rfl) ⟨1207365, by rfl⟩ : syracuseStep 3219641 = 2414731) B2414731
theorem B2146505 : Blo 1429534 2146505 := bstep (se 2 (by rfl) ⟨804939, by rfl⟩ : syracuseStep 2146505 = 1609879) B1609879
theorem B24428789 : Blo 1429534 24428789 := bstep (se 5 (by rfl) ⟨1145099, by rfl⟩ : syracuseStep 24428789 = 2290199) B2290199
theorem B2146619 : Blo 1429534 2146619 := bstep (se 1 (by rfl) ⟨1609964, by rfl⟩ : syracuseStep 2146619 = 3219929) B3219929
theorem B2146679 : Blo 1429534 2146679 := bstep (se 1 (by rfl) ⟨1610009, by rfl⟩ : syracuseStep 2146679 = 3220019) B3220019
theorem B1810831 : Blo 1429534 1810831 := bstep (se 1 (by rfl) ⟨1358123, by rfl⟩ : syracuseStep 1810831 = 2716247) B2716247
theorem B2146703 : Blo 1429534 2146703 := bstep (se 1 (by rfl) ⟨1610027, by rfl⟩ : syracuseStep 2146703 = 3220055) B3220055
theorem B2146745 : Blo 1429534 2146745 := bstep (se 2 (by rfl) ⟨805029, by rfl⟩ : syracuseStep 2146745 = 1610059) B1610059
theorem B2146823 : Blo 1429534 2146823 := bstep (se 1 (by rfl) ⟨1610117, by rfl⟩ : syracuseStep 2146823 = 3220235) B3220235
theorem B3219983 : Blo 1429534 3219983 := bstep (se 1 (by rfl) ⟨2414987, by rfl⟩ : syracuseStep 3219983 = 4829975) B4829975
theorem B3220001 : Blo 1429534 3220001 := bstep (se 2 (by rfl) ⟨1207500, by rfl⟩ : syracuseStep 3220001 = 2415001) B2415001
theorem B3621419 : Blo 1429534 3621419 := bstep (se 1 (by rfl) ⟨2716064, by rfl⟩ : syracuseStep 3621419 = 5432129) B5432129
theorem B2146859 : Blo 1429534 2146859 := bstep (se 1 (by rfl) ⟨1610144, by rfl⟩ : syracuseStep 2146859 = 3220289) B3220289
theorem B14885441 : Blo 1429534 14885441 := bstep (se 2 (by rfl) ⟨5582040, by rfl⟩ : syracuseStep 14885441 = 11164081) B11164081
theorem B2146889 : Blo 1429534 2146889 := bstep (se 2 (by rfl) ⟨805083, by rfl⟩ : syracuseStep 2146889 = 1610167) B1610167
theorem B2147003 : Blo 1429534 2147003 := bstep (se 1 (by rfl) ⟨1610252, by rfl⟩ : syracuseStep 2147003 = 3220505) B3220505
theorem B2147063 : Blo 1429534 2147063 := bstep (se 1 (by rfl) ⟨1610297, by rfl⟩ : syracuseStep 2147063 = 3220595) B3220595
theorem B4825871 : Blo 1429534 4825871 := bstep (se 1 (by rfl) ⟨3619403, by rfl⟩ : syracuseStep 4825871 = 7238807) B7238807
theorem B1630991 : Blo 1429534 1630991 := bstep (se 1 (by rfl) ⟨1223243, by rfl⟩ : syracuseStep 1630991 = 2446487) B2446487
theorem B2147087 : Blo 1429534 2147087 := bstep (se 1 (by rfl) ⟨1610315, by rfl⟩ : syracuseStep 2147087 = 3220631) B3220631
theorem B2147129 : Blo 1429534 2147129 := bstep (se 2 (by rfl) ⟨805173, by rfl⟩ : syracuseStep 2147129 = 1610347) B1610347
theorem B3220343 : Blo 1429534 3220343 := bstep (se 1 (by rfl) ⟨2415257, by rfl⟩ : syracuseStep 3220343 = 4830515) B4830515
theorem B2147207 : Blo 1429534 2147207 := bstep (se 1 (by rfl) ⟨1610405, by rfl⟩ : syracuseStep 2147207 = 3220811) B3220811
theorem B12223385 : Blo 1429534 12223385 := bstep (se 2 (by rfl) ⟨4583769, by rfl⟩ : syracuseStep 12223385 = 9167539) B9167539
theorem B2147243 : Blo 1429534 2147243 := bstep (se 1 (by rfl) ⟨1610432, by rfl⟩ : syracuseStep 2147243 = 3220865) B3220865
theorem B2147273 : Blo 1429534 2147273 := bstep (se 2 (by rfl) ⟨805227, by rfl⟩ : syracuseStep 2147273 = 1610455) B1610455
theorem B5506001 : Blo 1429534 5506001 := bstep (se 2 (by rfl) ⟨2064750, by rfl⟩ : syracuseStep 5506001 = 4129501) B4129501
theorem B4826141 : Blo 1429534 4826141 := bstep (se 3 (by rfl) ⟨904901, by rfl⟩ : syracuseStep 4826141 = 1809803) B1809803
theorem B3220523 : Blo 1429534 3220523 := bstep (se 1 (by rfl) ⟨2415392, by rfl⟩ : syracuseStep 3220523 = 4830785) B4830785
theorem B1811575 : Blo 1429534 1811575 := bstep (se 1 (by rfl) ⟨1358681, by rfl⟩ : syracuseStep 1811575 = 2717363) B2717363
theorem B3622259 : Blo 1429534 3622259 := bstep (se 1 (by rfl) ⟨2716694, by rfl⟩ : syracuseStep 3622259 = 5433389) B5433389
theorem B3622279 : Blo 1429534 3622279 := bstep (se 1 (by rfl) ⟨2716709, by rfl⟩ : syracuseStep 3622279 = 5433419) B5433419
theorem B3220883 : Blo 1429534 3220883 := bstep (se 1 (by rfl) ⟨2415662, by rfl⟩ : syracuseStep 3220883 = 4831325) B4831325
theorem B3220937 : Blo 1429534 3220937 := bstep (se 2 (by rfl) ⟨1207851, by rfl⟩ : syracuseStep 3220937 = 2415703) B2415703
theorem B7341515 : Blo 1429534 7341515 := bstep (se 1 (by rfl) ⟨5506136, by rfl⟩ : syracuseStep 7341515 = 11012273) B11012273
theorem B2146295 : Blo 1429534 2146295 := bstep (se 1 (by rfl) ⟨1609721, by rfl⟩ : syracuseStep 2146295 = 3219443) B3219443
theorem B4351499 : Blo 1429534 4351499 := bstep (se 1 (by rfl) ⟨3263624, by rfl⟩ : syracuseStep 4351499 = 6527249) B6527249
theorem B13936157 : Blo 1429534 13936157 := bstep (se 3 (by rfl) ⟨2613029, by rfl⟩ : syracuseStep 13936157 = 5226059) B5226059
theorem B9160235 : Blo 1429534 9160235 := bstep (se 1 (by rfl) ⟨6870176, by rfl⟩ : syracuseStep 9160235 = 13740353) B13740353
theorem B5506627 : Blo 1429534 5506627 := bstep (se 1 (by rfl) ⟨4129970, by rfl⟩ : syracuseStep 5506627 = 8259941) B8259941
theorem B29779525 : Blo 1429534 29779525 := bstep (se 4 (by rfl) ⟨2791830, by rfl⟩ : syracuseStep 29779525 = 5583661) B5583661
theorem B3917431 : Blo 1429534 3917431 := bstep (se 1 (by rfl) ⟨2938073, by rfl⟩ : syracuseStep 3917431 = 5876147) B5876147
theorem B3622553 : Blo 1429534 3622553 := bstep (se 2 (by rfl) ⟨1358457, by rfl⟩ : syracuseStep 3622553 = 2716915) B2716915
theorem B13739813 : Blo 1429534 13739813 := bstep (se 4 (by rfl) ⟨1288107, by rfl⟩ : syracuseStep 13739813 = 2576215) B2576215
theorem B3622715 : Blo 1429534 3622715 := bstep (se 1 (by rfl) ⟨2717036, by rfl⟩ : syracuseStep 3622715 = 5434073) B5434073
theorem B7243667 : Blo 1429534 7243667 := bstep (se 1 (by rfl) ⟨5432750, by rfl⟩ : syracuseStep 7243667 = 10865501) B10865501
theorem B3622927 : Blo 1429534 3622927 := bstep (se 1 (by rfl) ⟨2717195, by rfl⟩ : syracuseStep 3622927 = 5434391) B5434391
theorem B30951517 : Blo 1429534 30951517 := bstep (se 3 (by rfl) ⟨5803409, by rfl⟩ : syracuseStep 30951517 = 11606819) B11606819
theorem B5433601 : Blo 1429534 5433601 := bstep (se 2 (by rfl) ⟨2037600, by rfl⟩ : syracuseStep 5433601 = 4075201) B4075201
theorem B4073743 : Blo 1429534 4073743 := bstep (se 1 (by rfl) ⟨3055307, by rfl⟩ : syracuseStep 4073743 = 6110615) B6110615
theorem B3623201 : Blo 1429534 3623201 := bstep (se 2 (by rfl) ⟨1358700, by rfl⟩ : syracuseStep 3623201 = 2717401) B2717401
theorem B2713915 : Blo 1429534 2713915 := bstep (se 1 (by rfl) ⟨2035436, by rfl⟩ : syracuseStep 2713915 = 4070873) B4070873
theorem B4073789 : Blo 1429534 4073789 := bstep (se 3 (by rfl) ⟨763835, by rfl⟩ : syracuseStep 4073789 = 1527671) B1527671
theorem B8145299 : Blo 1429534 8145299 := bstep (se 1 (by rfl) ⟨6108974, by rfl⟩ : syracuseStep 8145299 = 12217949) B12217949
theorem B4827545 : Blo 1429534 4827545 := bstep (se 2 (by rfl) ⟨1810329, by rfl⟩ : syracuseStep 4827545 = 3620659) B3620659
theorem B4074131 : Blo 1429534 4074131 := bstep (se 1 (by rfl) ⟨3055598, by rfl⟩ : syracuseStep 4074131 = 6111197) B6111197
theorem B4893385 : Blo 1429534 4893385 := bstep (se 2 (by rfl) ⟨1835019, by rfl⟩ : syracuseStep 4893385 = 3670039) B3670039
theorem B6204161 : Blo 1429534 6204161 := bstep (se 2 (by rfl) ⟨2326560, by rfl⟩ : syracuseStep 6204161 = 4653121) B4653121
theorem B2714401 : Blo 1429534 2714401 := bstep (se 2 (by rfl) ⟨1017900, by rfl⟩ : syracuseStep 2714401 = 2035801) B2035801
theorem B6876019 : Blo 1429534 6876019 := bstep (se 1 (by rfl) ⟨5157014, by rfl⟩ : syracuseStep 6876019 = 10314029) B10314029
theorem B1608583 : Blo 1429534 1608583 := bstep (se 1 (by rfl) ⟨1206437, by rfl⟩ : syracuseStep 1608583 = 2412875) B2412875
theorem B1608763 : Blo 1429534 1608763 := bstep (se 1 (by rfl) ⟨1206572, by rfl⟩ : syracuseStep 1608763 = 2413145) B2413145
theorem B8146007 : Blo 1429534 8146007 := bstep (se 1 (by rfl) ⟨6109505, by rfl⟩ : syracuseStep 8146007 = 12219011) B12219011
theorem B4828247 : Blo 1429534 4828247 := bstep (se 1 (by rfl) ⟨3621185, by rfl⟩ : syracuseStep 4828247 = 7242371) B7242371
theorem B4075019 : Blo 1429534 4075019 := bstep (se 1 (by rfl) ⟨3056264, by rfl⟩ : syracuseStep 4075019 = 6112529) B6112529
theorem B1609231 : Blo 1429534 1609231 := bstep (se 1 (by rfl) ⟨1206923, by rfl⟩ : syracuseStep 1609231 = 2413847) B2413847
theorem B4828733 : Blo 1429534 4828733 := bstep (se 3 (by rfl) ⟨905387, by rfl⟩ : syracuseStep 4828733 = 1810775) B1810775
theorem B7237187 : Blo 1429534 7237187 := bstep (se 1 (by rfl) ⟨5427890, by rfl⟩ : syracuseStep 7237187 = 10855781) B10855781
theorem B2649719 : Blo 1429534 2649719 := bstep (se 1 (by rfl) ⟨1987289, by rfl⟩ : syracuseStep 2649719 = 3974579) B3974579
theorem B26095283 : Blo 1429534 26095283 := bstep (se 1 (by rfl) ⟨19571462, by rfl⟩ : syracuseStep 26095283 = 39142925) B39142925
theorem B2035471 : Blo 1429534 2035471 := bstep (se 1 (by rfl) ⟨1526603, by rfl⟩ : syracuseStep 2035471 = 3053207) B3053207
theorem B31371077 : Blo 1429534 31371077 := bstep (se 4 (by rfl) ⟨2941038, by rfl⟩ : syracuseStep 31371077 = 5882077) B5882077
theorem B7237511 : Blo 1429534 7237511 := bstep (se 1 (by rfl) ⟨5428133, by rfl⟩ : syracuseStep 7237511 = 10856267) B10856267
theorem B1609735 : Blo 1429534 1609735 := bstep (se 1 (by rfl) ⟨1207301, by rfl⟩ : syracuseStep 1609735 = 2414603) B2414603
theorem B5804075 : Blo 1429534 5804075 := bstep (se 1 (by rfl) ⟨4353056, by rfl⟩ : syracuseStep 5804075 = 8706113) B8706113
theorem B1429563 : Blo 1429534 1429563 := bstep (se 1 (by rfl) ⟨1072172, by rfl⟩ : syracuseStep 1429563 = 2144345) B2144345
theorem B2715707 : Blo 1429534 2715707 := bstep (se 1 (by rfl) ⟨2036780, by rfl⟩ : syracuseStep 2715707 = 4073561) B4073561
theorem B1429639 : Blo 1429534 1429639 := bstep (se 1 (by rfl) ⟨1072229, by rfl⟩ : syracuseStep 1429639 = 2144459) B2144459
theorem B2412679 : Blo 1429534 2412679 := bstep (se 1 (by rfl) ⟨1809509, by rfl⟩ : syracuseStep 2412679 = 3619019) B3619019
theorem B1429647 : Blo 1429534 1429647 := bstep (se 1 (by rfl) ⟨1072235, by rfl⟩ : syracuseStep 1429647 = 2144471) B2144471
theorem B1429691 : Blo 1429534 1429691 := bstep (se 1 (by rfl) ⟨1072268, by rfl⟩ : syracuseStep 1429691 = 2144537) B2144537
theorem B1609915 : Blo 1429534 1609915 := bstep (se 1 (by rfl) ⟨1207436, by rfl⟩ : syracuseStep 1609915 = 2414873) B2414873
theorem B10858697 : Blo 1429534 10858697 := bstep (se 2 (by rfl) ⟨4072011, by rfl⟩ : syracuseStep 10858697 = 8144023) B8144023
theorem B5157101 : Blo 1429534 5157101 := bstep (se 3 (by rfl) ⟨966956, by rfl⟩ : syracuseStep 5157101 = 1933913) B1933913
theorem B1429767 : Blo 1429534 1429767 := bstep (se 1 (by rfl) ⟨1072325, by rfl⟩ : syracuseStep 1429767 = 2144651) B2144651
theorem B1429775 : Blo 1429534 1429775 := bstep (se 1 (by rfl) ⟨1072331, by rfl⟩ : syracuseStep 1429775 = 2144663) B2144663
theorem B2445611 : Blo 1429534 2445611 := bstep (se 1 (by rfl) ⟨1834208, by rfl⟩ : syracuseStep 2445611 = 3668417) B3668417
theorem B1429819 : Blo 1429534 1429819 := bstep (se 1 (by rfl) ⟨1072364, by rfl⟩ : syracuseStep 1429819 = 2144729) B2144729
theorem B6107507 : Blo 1429534 6107507 := bstep (se 1 (by rfl) ⟨4580630, by rfl⟩ : syracuseStep 6107507 = 9161261) B9161261
theorem B1429895 : Blo 1429534 1429895 := bstep (se 1 (by rfl) ⟨1072421, by rfl⟩ : syracuseStep 1429895 = 2144843) B2144843
theorem B1429903 : Blo 1429534 1429903 := bstep (se 1 (by rfl) ⟨1072427, by rfl⟩ : syracuseStep 1429903 = 2144855) B2144855
theorem B29348243 : Blo 1429534 29348243 := bstep (se 1 (by rfl) ⟨22011182, by rfl⟩ : syracuseStep 29348243 = 44022365) B44022365
theorem B16290233 : Blo 1429534 16290233 := bstep (se 2 (by rfl) ⟨6108837, by rfl⟩ : syracuseStep 16290233 = 12217675) B12217675
theorem B1429947 : Blo 1429534 1429947 := bstep (se 1 (by rfl) ⟨1072460, by rfl⟩ : syracuseStep 1429947 = 2144921) B2144921
theorem B1430023 : Blo 1429534 1430023 := bstep (se 1 (by rfl) ⟨1072517, by rfl⟩ : syracuseStep 1430023 = 2145035) B2145035
theorem B1430031 : Blo 1429534 1430031 := bstep (se 1 (by rfl) ⟨1072523, by rfl⟩ : syracuseStep 1430031 = 2145047) B2145047
theorem B2716193 : Blo 1429534 2716193 := bstep (se 2 (by rfl) ⟨1018572, by rfl⟩ : syracuseStep 2716193 = 2037145) B2037145
theorem B38171179 : Blo 1429534 38171179 := bstep (se 1 (by rfl) ⟨28628384, by rfl⟩ : syracuseStep 38171179 = 57256769) B57256769
theorem B1430075 : Blo 1429534 1430075 := bstep (se 1 (by rfl) ⟨1072556, by rfl⟩ : syracuseStep 1430075 = 2145113) B2145113
theorem B1430151 : Blo 1429534 1430151 := bstep (se 1 (by rfl) ⟨1072613, by rfl⟩ : syracuseStep 1430151 = 2145227) B2145227
theorem B1430159 : Blo 1429534 1430159 := bstep (se 1 (by rfl) ⟨1072619, by rfl⟩ : syracuseStep 1430159 = 2145239) B2145239
theorem B1610383 : Blo 1429534 1610383 := bstep (se 1 (by rfl) ⟨1207787, by rfl⟩ : syracuseStep 1610383 = 2415575) B2415575
theorem B2716345 : Blo 1429534 2716345 := bstep (se 2 (by rfl) ⟨1018629, by rfl⟩ : syracuseStep 2716345 = 2037259) B2037259
theorem B1430203 : Blo 1429534 1430203 := bstep (se 1 (by rfl) ⟨1072652, by rfl⟩ : syracuseStep 1430203 = 2145305) B2145305
theorem B61878977 : Blo 1429534 61878977 := bstep (se 2 (by rfl) ⟨23204616, by rfl⟩ : syracuseStep 61878977 = 46409233) B46409233
theorem B1430279 : Blo 1429534 1430279 := bstep (se 1 (by rfl) ⟨1072709, by rfl⟩ : syracuseStep 1430279 = 2145419) B2145419
theorem B2413327 : Blo 1429534 2413327 := bstep (se 1 (by rfl) ⟨1809995, by rfl⟩ : syracuseStep 2413327 = 3619991) B3619991
theorem B1430287 : Blo 1429534 1430287 := bstep (se 1 (by rfl) ⟨1072715, by rfl⟩ : syracuseStep 1430287 = 2145431) B2145431
theorem B5157665 : Blo 1429534 5157665 := bstep (se 2 (by rfl) ⟨1934124, by rfl⟩ : syracuseStep 5157665 = 3868249) B3868249
theorem B1430331 : Blo 1429534 1430331 := bstep (se 1 (by rfl) ⟨1072748, by rfl⟩ : syracuseStep 1430331 = 2145497) B2145497
theorem B7836551 : Blo 1429534 7836551 := bstep (se 1 (by rfl) ⟨5877413, by rfl⟩ : syracuseStep 7836551 = 11754827) B11754827
theorem B1430407 : Blo 1429534 1430407 := bstep (se 1 (by rfl) ⟨1072805, by rfl⟩ : syracuseStep 1430407 = 2145611) B2145611
theorem B1430415 : Blo 1429534 1430415 := bstep (se 1 (by rfl) ⟨1072811, by rfl⟩ : syracuseStep 1430415 = 2145623) B2145623
theorem B7246745 : Blo 1429534 7246745 := bstep (se 2 (by rfl) ⟨2717529, by rfl⟩ : syracuseStep 7246745 = 5435059) B5435059
theorem B34780067 : Blo 1429534 34780067 := bstep (se 1 (by rfl) ⟨26085050, by rfl⟩ : syracuseStep 34780067 = 52170101) B52170101
theorem B8147897 : Blo 1429534 8147897 := bstep (se 2 (by rfl) ⟨3055461, by rfl⟩ : syracuseStep 8147897 = 6110923) B6110923
theorem B4830137 : Blo 1429534 4830137 := bstep (se 2 (by rfl) ⟨1811301, by rfl⟩ : syracuseStep 4830137 = 3622603) B3622603
theorem B1430459 : Blo 1429534 1430459 := bstep (se 1 (by rfl) ⟨1072844, by rfl⟩ : syracuseStep 1430459 = 2145689) B2145689
theorem B1430535 : Blo 1429534 1430535 := bstep (se 1 (by rfl) ⟨1072901, by rfl⟩ : syracuseStep 1430535 = 2145803) B2145803
theorem B1430543 : Blo 1429534 1430543 := bstep (se 1 (by rfl) ⟨1072907, by rfl⟩ : syracuseStep 1430543 = 2145815) B2145815
theorem B14890007 : Blo 1429534 14890007 := bstep (se 1 (by rfl) ⟨11167505, by rfl⟩ : syracuseStep 14890007 = 22335011) B22335011
theorem B1430587 : Blo 1429534 1430587 := bstep (se 1 (by rfl) ⟨1072940, by rfl⟩ : syracuseStep 1430587 = 2145881) B2145881
theorem B27513917 : Blo 1429534 27513917 := bstep (se 3 (by rfl) ⟨5158859, by rfl⟩ : syracuseStep 27513917 = 10317719) B10317719
theorem B1430663 : Blo 1429534 1430663 := bstep (se 1 (by rfl) ⟨1072997, by rfl⟩ : syracuseStep 1430663 = 2145995) B2145995
theorem B1430671 : Blo 1429534 1430671 := bstep (se 1 (by rfl) ⟨1073003, by rfl⟩ : syracuseStep 1430671 = 2146007) B2146007
theorem B1430715 : Blo 1429534 1430715 := bstep (se 1 (by rfl) ⟨1073036, by rfl⟩ : syracuseStep 1430715 = 2146073) B2146073
theorem B8697061 : Blo 1429534 8697061 := bstep (se 4 (by rfl) ⟨815349, by rfl⟩ : syracuseStep 8697061 = 1630699) B1630699
theorem B1430791 : Blo 1429534 1430791 := bstep (se 1 (by rfl) ⟨1073093, by rfl⟩ : syracuseStep 1430791 = 2146187) B2146187
theorem B1430799 : Blo 1429534 1430799 := bstep (se 1 (by rfl) ⟨1073099, by rfl⟩ : syracuseStep 1430799 = 2146199) B2146199
theorem B2413867 : Blo 1429534 2413867 := bstep (se 1 (by rfl) ⟨1810400, by rfl⟩ : syracuseStep 2413867 = 3620801) B3620801
theorem B10310971 : Blo 1429534 10310971 := bstep (se 1 (by rfl) ⟨7733228, by rfl⟩ : syracuseStep 10310971 = 15466457) B15466457
theorem B1430843 : Blo 1429534 1430843 := bstep (se 1 (by rfl) ⟨1073132, by rfl⟩ : syracuseStep 1430843 = 2146265) B2146265
theorem B1430919 : Blo 1429534 1430919 := bstep (se 1 (by rfl) ⟨1073189, by rfl⟩ : syracuseStep 1430919 = 2146379) B2146379
theorem B1430927 : Blo 1429534 1430927 := bstep (se 1 (by rfl) ⟨1073195, by rfl⟩ : syracuseStep 1430927 = 2146391) B2146391
theorem B2414009 : Blo 1429534 2414009 := bstep (se 2 (by rfl) ⟨905253, by rfl⟩ : syracuseStep 2414009 = 1810507) B1810507
theorem B1430971 : Blo 1429534 1430971 := bstep (se 1 (by rfl) ⟨1073228, by rfl⟩ : syracuseStep 1430971 = 2146457) B2146457
theorem B7730635 : Blo 1429534 7730635 := bstep (se 1 (by rfl) ⟨5797976, by rfl⟩ : syracuseStep 7730635 = 11595953) B11595953
theorem B1431047 : Blo 1429534 1431047 := bstep (se 1 (by rfl) ⟨1073285, by rfl⟩ : syracuseStep 1431047 = 2146571) B2146571
theorem B4830731 : Blo 1429534 4830731 := bstep (se 1 (by rfl) ⟨3623048, by rfl⟩ : syracuseStep 4830731 = 7246097) B7246097
theorem B1431055 : Blo 1429534 1431055 := bstep (se 1 (by rfl) ⟨1073291, by rfl⟩ : syracuseStep 1431055 = 2146583) B2146583
theorem B3864107 : Blo 1429534 3864107 := bstep (se 1 (by rfl) ⟨2898080, by rfl⟩ : syracuseStep 3864107 = 5796161) B5796161
theorem B1431099 : Blo 1429534 1431099 := bstep (se 1 (by rfl) ⟨1073324, by rfl⟩ : syracuseStep 1431099 = 2146649) B2146649
theorem B24450659 : Blo 1429534 24450659 := bstep (se 1 (by rfl) ⟨18337994, by rfl⟩ : syracuseStep 24450659 = 36675989) B36675989
theorem B4830839 : Blo 1429534 4830839 := bstep (se 1 (by rfl) ⟨3623129, by rfl⟩ : syracuseStep 4830839 = 7246259) B7246259
theorem B3217031 : Blo 1429534 3217031 := bstep (se 1 (by rfl) ⟨2412773, by rfl⟩ : syracuseStep 3217031 = 4825547) B4825547
theorem B1431175 : Blo 1429534 1431175 := bstep (se 1 (by rfl) ⟨1073381, by rfl⟩ : syracuseStep 1431175 = 2146763) B2146763
theorem B1431183 : Blo 1429534 1431183 := bstep (se 1 (by rfl) ⟨1073387, by rfl⟩ : syracuseStep 1431183 = 2146775) B2146775
theorem B1431227 : Blo 1429534 1431227 := bstep (se 1 (by rfl) ⟨1073420, by rfl⟩ : syracuseStep 1431227 = 2146841) B2146841
theorem B10868417 : Blo 1429534 10868417 := bstep (se 2 (by rfl) ⟨4075656, by rfl⟩ : syracuseStep 10868417 = 8151313) B8151313
theorem B1431303 : Blo 1429534 1431303 := bstep (se 1 (by rfl) ⟨1073477, by rfl⟩ : syracuseStep 1431303 = 2146955) B2146955
theorem B1431311 : Blo 1429534 1431311 := bstep (se 1 (by rfl) ⟨1073483, by rfl⟩ : syracuseStep 1431311 = 2146967) B2146967
theorem B18339635 : Blo 1429534 18339635 := bstep (se 1 (by rfl) ⟨13754726, by rfl⟩ : syracuseStep 18339635 = 27509453) B27509453
theorem B3217211 : Blo 1429534 3217211 := bstep (se 1 (by rfl) ⟨2412908, by rfl⟩ : syracuseStep 3217211 = 4825817) B4825817
theorem B1431355 : Blo 1429534 1431355 := bstep (se 1 (by rfl) ⟨1073516, by rfl⟩ : syracuseStep 1431355 = 2147033) B2147033
theorem B3618695 : Blo 1429534 3618695 := bstep (se 1 (by rfl) ⟨2714021, by rfl⟩ : syracuseStep 3618695 = 5428043) B5428043
theorem B1431431 : Blo 1429534 1431431 := bstep (se 1 (by rfl) ⟨1073573, by rfl⟩ : syracuseStep 1431431 = 2147147) B2147147
theorem B1431439 : Blo 1429534 1431439 := bstep (se 1 (by rfl) ⟨1073579, by rfl⟩ : syracuseStep 1431439 = 2147159) B2147159
theorem B3053497 : Blo 1429534 3053497 := bstep (se 2 (by rfl) ⟨1145061, by rfl⟩ : syracuseStep 3053497 = 2290123) B2290123
theorem B3217337 : Blo 1429534 3217337 := bstep (se 2 (by rfl) ⟨1206501, by rfl⟩ : syracuseStep 3217337 = 2413003) B2413003
theorem B1431483 : Blo 1429534 1431483 := bstep (se 1 (by rfl) ⟨1073612, by rfl⟩ : syracuseStep 1431483 = 2147225) B2147225
theorem B3618827 : Blo 1429534 3618827 := bstep (se 1 (by rfl) ⟨2714120, by rfl⟩ : syracuseStep 3618827 = 5428241) B5428241
theorem B3438625 : Blo 1429534 3438625 := bstep (se 2 (by rfl) ⟨1289484, by rfl⟩ : syracuseStep 3438625 = 2578969) B2578969
theorem B2144315 : Blo 1429534 2144315 := bstep (se 1 (by rfl) ⟨1608236, by rfl⟩ : syracuseStep 2144315 = 3216473) B3216473
theorem B11008061 : Blo 1429534 11008061 := bstep (se 3 (by rfl) ⟨2064011, by rfl⟩ : syracuseStep 11008061 = 4128023) B4128023
theorem B16750709 : Blo 1429534 16750709 := bstep (se 5 (by rfl) ⟨785189, by rfl⟩ : syracuseStep 16750709 = 1570379) B1570379
theorem B2144375 : Blo 1429534 2144375 := bstep (se 1 (by rfl) ⟨1608281, by rfl⟩ : syracuseStep 2144375 = 3216563) B3216563
theorem B2414711 : Blo 1429534 2414711 := bstep (se 1 (by rfl) ⟨1811033, by rfl⟩ : syracuseStep 2414711 = 3622067) B3622067
theorem B2144399 : Blo 1429534 2144399 := bstep (se 1 (by rfl) ⟨1608299, by rfl⟩ : syracuseStep 2144399 = 3216599) B3216599
theorem B2144441 : Blo 1429534 2144441 := bstep (se 2 (by rfl) ⟨804165, by rfl⟩ : syracuseStep 2144441 = 1608331) B1608331
theorem B17406197 : Blo 1429534 17406197 := bstep (se 5 (by rfl) ⟨815915, by rfl⟩ : syracuseStep 17406197 = 1631831) B1631831
theorem B4585729 : Blo 1429534 4585729 := bstep (se 2 (by rfl) ⟨1719648, by rfl⟩ : syracuseStep 4585729 = 3439297) B3439297
theorem B2144519 : Blo 1429534 2144519 := bstep (se 1 (by rfl) ⟨1608389, by rfl⟩ : syracuseStep 2144519 = 3216779) B3216779
theorem B3217679 : Blo 1429534 3217679 := bstep (se 1 (by rfl) ⟨2413259, by rfl⟩ : syracuseStep 3217679 = 4826519) B4826519
theorem B3217697 : Blo 1429534 3217697 := bstep (se 2 (by rfl) ⟨1206636, by rfl⟩ : syracuseStep 3217697 = 2413273) B2413273
theorem B2144555 : Blo 1429534 2144555 := bstep (se 1 (by rfl) ⟨1608416, by rfl⟩ : syracuseStep 2144555 = 3216833) B3216833
theorem B2144585 : Blo 1429534 2144585 := bstep (se 2 (by rfl) ⟨804219, by rfl⟩ : syracuseStep 2144585 = 1608439) B1608439
theorem B2038159 : Blo 1429534 2038159 := bstep (se 1 (by rfl) ⟨1528619, by rfl⟩ : syracuseStep 2038159 = 3057239) B3057239
theorem B2144699 : Blo 1429534 2144699 := bstep (se 1 (by rfl) ⟨1608524, by rfl⟩ : syracuseStep 2144699 = 3217049) B3217049
theorem B5429713 : Blo 1429534 5429713 := bstep (se 2 (by rfl) ⟨2036142, by rfl⟩ : syracuseStep 5429713 = 4072285) B4072285
theorem B2144759 : Blo 1429534 2144759 := bstep (se 1 (by rfl) ⟨1608569, by rfl⟩ : syracuseStep 2144759 = 3217139) B3217139
theorem B8264195 : Blo 1429534 8264195 := bstep (se 1 (by rfl) ⟨6198146, by rfl⟩ : syracuseStep 8264195 = 12396293) B12396293
theorem B2144783 : Blo 1429534 2144783 := bstep (se 1 (by rfl) ⟨1608587, by rfl⟩ : syracuseStep 2144783 = 3217175) B3217175
theorem B3619343 : Blo 1429534 3619343 := bstep (se 1 (by rfl) ⟨2714507, by rfl⟩ : syracuseStep 3619343 = 5429015) B5429015
theorem B3054095 : Blo 1429534 3054095 := bstep (se 1 (by rfl) ⟨2290571, by rfl⟩ : syracuseStep 3054095 = 4581143) B4581143
theorem B2144825 : Blo 1429534 2144825 := bstep (se 2 (by rfl) ⟨804309, by rfl⟩ : syracuseStep 2144825 = 1608619) B1608619
theorem B2415163 : Blo 1429534 2415163 := bstep (se 1 (by rfl) ⟨1811372, by rfl⟩ : syracuseStep 2415163 = 3622745) B3622745
theorem B22018625 : Blo 1429534 22018625 := bstep (se 2 (by rfl) ⟨8256984, by rfl⟩ : syracuseStep 22018625 = 16513969) B16513969
theorem B3218039 : Blo 1429534 3218039 := bstep (se 1 (by rfl) ⟨2413529, by rfl⟩ : syracuseStep 3218039 = 4827059) B4827059
theorem B2144903 : Blo 1429534 2144903 := bstep (se 1 (by rfl) ⟨1608677, by rfl⟩ : syracuseStep 2144903 = 3217355) B3217355
theorem B3619475 : Blo 1429534 3619475 := bstep (se 1 (by rfl) ⟨2714606, by rfl⟩ : syracuseStep 3619475 = 5429213) B5429213
theorem B2144939 : Blo 1429534 2144939 := bstep (se 1 (by rfl) ⟨1608704, by rfl⟩ : syracuseStep 2144939 = 3217409) B3217409
theorem B2144969 : Blo 1429534 2144969 := bstep (se 2 (by rfl) ⟨804363, by rfl⟩ : syracuseStep 2144969 = 1608727) B1608727
theorem B2415305 : Blo 1429534 2415305 := bstep (se 2 (by rfl) ⟨905739, by rfl⟩ : syracuseStep 2415305 = 1811479) B1811479
theorem B5430017 : Blo 1429534 5430017 := bstep (se 2 (by rfl) ⟨2036256, by rfl⟩ : syracuseStep 5430017 = 4072513) B4072513
theorem B8821537 : Blo 1429534 8821537 := bstep (se 2 (by rfl) ⟨3308076, by rfl⟩ : syracuseStep 8821537 = 6616153) B6616153
theorem B3218219 : Blo 1429534 3218219 := bstep (se 1 (by rfl) ⟨2413664, by rfl⟩ : syracuseStep 3218219 = 4827329) B4827329
theorem B3865403 : Blo 1429534 3865403 := bstep (se 1 (by rfl) ⟨2899052, by rfl⟩ : syracuseStep 3865403 = 5798105) B5798105
theorem B2145083 : Blo 1429534 2145083 := bstep (se 1 (by rfl) ⟨1608812, by rfl⟩ : syracuseStep 2145083 = 3217625) B3217625
theorem B2145143 : Blo 1429534 2145143 := bstep (se 1 (by rfl) ⟨1608857, by rfl⟩ : syracuseStep 2145143 = 3217715) B3217715
theorem B2145167 : Blo 1429534 2145167 := bstep (se 1 (by rfl) ⟨1608875, by rfl⟩ : syracuseStep 2145167 = 3217751) B3217751
theorem B2145209 : Blo 1429534 2145209 := bstep (se 2 (by rfl) ⟨804453, by rfl⟩ : syracuseStep 2145209 = 1608907) B1608907
theorem B2145287 : Blo 1429534 2145287 := bstep (se 1 (by rfl) ⟨1608965, by rfl⟩ : syracuseStep 2145287 = 3217931) B3217931
theorem B7339031 : Blo 1429534 7339031 := bstep (se 1 (by rfl) ⟨5504273, by rfl⟩ : syracuseStep 7339031 = 11008547) B11008547
theorem B2145323 : Blo 1429534 2145323 := bstep (se 1 (by rfl) ⟨1608992, by rfl⟩ : syracuseStep 2145323 = 3217985) B3217985
theorem B2145353 : Blo 1429534 2145353 := bstep (se 2 (by rfl) ⟨804507, by rfl⟩ : syracuseStep 2145353 = 1609015) B1609015
theorem B7445591 : Blo 1429534 7445591 := bstep (se 1 (by rfl) ⟨5584193, by rfl⟩ : syracuseStep 7445591 = 11168387) B11168387
theorem B3218579 : Blo 1429534 3218579 := bstep (se 1 (by rfl) ⟨2413934, by rfl⟩ : syracuseStep 3218579 = 4827869) B4827869
theorem B2145467 : Blo 1429534 2145467 := bstep (se 1 (by rfl) ⟨1609100, by rfl⟩ : syracuseStep 2145467 = 3218201) B3218201
theorem B5430473 : Blo 1429534 5430473 := bstep (se 2 (by rfl) ⟨2036427, by rfl⟩ : syracuseStep 5430473 = 4072855) B4072855
theorem B3218633 : Blo 1429534 3218633 := bstep (se 2 (by rfl) ⟨1206987, by rfl⟩ : syracuseStep 3218633 = 2413975) B2413975
theorem B2145527 : Blo 1429534 2145527 := bstep (se 1 (by rfl) ⟨1609145, by rfl⟩ : syracuseStep 2145527 = 3218291) B3218291
theorem B2145551 : Blo 1429534 2145551 := bstep (se 1 (by rfl) ⟨1609163, by rfl⟩ : syracuseStep 2145551 = 3218327) B3218327
theorem B2145593 : Blo 1429534 2145593 := bstep (se 2 (by rfl) ⟨804597, by rfl⟩ : syracuseStep 2145593 = 1609195) B1609195
theorem B44039483 : Blo 1429534 44039483 := bstep (se 1 (by rfl) ⟨33029612, by rfl⟩ : syracuseStep 44039483 = 66059225) B66059225
theorem B13745501 : Blo 1429534 13745501 := bstep (se 3 (by rfl) ⟨2577281, by rfl⟩ : syracuseStep 13745501 = 5154563) B5154563
theorem B7241075 : Blo 1429534 7241075 := bstep (se 1 (by rfl) ⟨5430806, by rfl⟩ : syracuseStep 7241075 = 10861613) B10861613
theorem B2145671 : Blo 1429534 2145671 := bstep (se 1 (by rfl) ⟨1609253, by rfl⟩ : syracuseStep 2145671 = 3218507) B3218507
theorem B6110599 : Blo 1429534 6110599 := bstep (se 1 (by rfl) ⟨4582949, by rfl⟩ : syracuseStep 6110599 = 9165899) B9165899
theorem B2145707 : Blo 1429534 2145707 := bstep (se 1 (by rfl) ⟨1609280, by rfl⟩ : syracuseStep 2145707 = 3218561) B3218561
theorem B2145737 : Blo 1429534 2145737 := bstep (se 2 (by rfl) ⟨804651, by rfl⟩ : syracuseStep 2145737 = 1609303) B1609303
theorem B11599325 : Blo 1429534 11599325 := bstep (se 3 (by rfl) ⟨2174873, by rfl⟩ : syracuseStep 11599325 = 4349747) B4349747
theorem B3669547 : Blo 1429534 3669547 := bstep (se 1 (by rfl) ⟨2752160, by rfl⟩ : syracuseStep 3669547 = 5504321) B5504321
theorem B2145851 : Blo 1429534 2145851 := bstep (se 1 (by rfl) ⟨1609388, by rfl⟩ : syracuseStep 2145851 = 3218777) B3218777
theorem B4070999 : Blo 1429534 4070999 := bstep (se 1 (by rfl) ⟨3053249, by rfl⟩ : syracuseStep 4070999 = 6106499) B6106499
theorem B2145911 : Blo 1429534 2145911 := bstep (se 1 (by rfl) ⟨1609433, by rfl⟩ : syracuseStep 2145911 = 3218867) B3218867
theorem B2145935 : Blo 1429534 2145935 := bstep (se 1 (by rfl) ⟨1609451, by rfl⟩ : syracuseStep 2145935 = 3218903) B3218903
theorem B2145977 : Blo 1429534 2145977 := bstep (se 2 (by rfl) ⟨804741, by rfl⟩ : syracuseStep 2145977 = 1609483) B1609483
theorem B8142565 : Blo 1429534 8142565 := bstep (se 4 (by rfl) ⟨763365, by rfl⟩ : syracuseStep 8142565 = 1526731) B1526731
theorem B6110957 : Blo 1429534 6110957 := bstep (se 3 (by rfl) ⟨1145804, by rfl⟩ : syracuseStep 6110957 = 2291609) B2291609
theorem B3620609 : Blo 1429534 3620609 := bstep (se 2 (by rfl) ⟨1357728, by rfl⟩ : syracuseStep 3620609 = 2715457) B2715457
theorem B1810183 : Blo 1429534 1810183 := bstep (se 1 (by rfl) ⟨1357637, by rfl⟩ : syracuseStep 1810183 = 2715275) B2715275
theorem B2146055 : Blo 1429534 2146055 := bstep (se 1 (by rfl) ⟨1609541, by rfl⟩ : syracuseStep 2146055 = 3219083) B3219083
theorem B2146091 : Blo 1429534 2146091 := bstep (se 1 (by rfl) ⟨1609568, by rfl⟩ : syracuseStep 2146091 = 3219137) B3219137
theorem B2146121 : Blo 1429534 2146121 := bstep (se 2 (by rfl) ⟨804795, by rfl⟩ : syracuseStep 2146121 = 1609591) B1609591
theorem B7241561 : Blo 1429534 7241561 := bstep (se 2 (by rfl) ⟨2715585, by rfl⟩ : syracuseStep 7241561 = 5431171) B5431171
theorem B12222323 : Blo 1429534 12222323 := bstep (se 1 (by rfl) ⟨9166742, by rfl⟩ : syracuseStep 12222323 = 18333485) B18333485
theorem B2752391 : Blo 1429534 2752391 := bstep (se 1 (by rfl) ⟨2064293, by rfl⟩ : syracuseStep 2752391 = 4128587) B4128587
theorem B3219335 : Blo 1429534 3219335 := bstep (se 1 (by rfl) ⟨2414501, by rfl⟩ : syracuseStep 3219335 = 4829003) B4829003
theorem B2146235 : Blo 1429534 2146235 := bstep (se 1 (by rfl) ⟨1609676, by rfl⟩ : syracuseStep 2146235 = 3219353) B3219353
theorem B31768523 : Blo 1429534 31768523 := bstep (se 1 (by rfl) ⟨23826392, by rfl⟩ : syracuseStep 31768523 = 47652785) B47652785
theorem B2146313 : Blo 1429534 2146313 := bstep (se 2 (by rfl) ⟨804867, by rfl⟩ : syracuseStep 2146313 = 1609735) B1609735
theorem B2146343 : Blo 1429534 2146343 := bstep (se 1 (by rfl) ⟨1609757, by rfl⟩ : syracuseStep 2146343 = 3219515) B3219515
theorem B39706685 : Blo 1429534 39706685 := bstep (se 3 (by rfl) ⟨7445003, by rfl⟩ : syracuseStep 39706685 = 14890007) B14890007
theorem B2146427 : Blo 1429534 2146427 := bstep (se 1 (by rfl) ⟨1609820, by rfl⟩ : syracuseStep 2146427 = 3219641) B3219641
theorem B7241885 : Blo 1429534 7241885 := bstep (se 3 (by rfl) ⟨1357853, by rfl⟩ : syracuseStep 7241885 = 2715707) B2715707
theorem B16285859 : Blo 1429534 16285859 := bstep (se 1 (by rfl) ⟨12214394, by rfl⟩ : syracuseStep 16285859 = 24428789) B24428789
theorem B4071671 : Blo 1429534 4071671 := bstep (se 1 (by rfl) ⟨3053753, by rfl⟩ : syracuseStep 4071671 = 6107507) B6107507
theorem B2146553 : Blo 1429534 2146553 := bstep (se 2 (by rfl) ⟨804957, by rfl⟩ : syracuseStep 2146553 = 1609915) B1609915
theorem B2146655 : Blo 1429534 2146655 := bstep (se 1 (by rfl) ⟨1609991, by rfl⟩ : syracuseStep 2146655 = 3219983) B3219983
theorem B5431657 : Blo 1429534 5431657 := bstep (se 2 (by rfl) ⟨2036871, by rfl⟩ : syracuseStep 5431657 = 4073743) B4073743
theorem B2146667 : Blo 1429534 2146667 := bstep (se 1 (by rfl) ⟨1610000, by rfl⟩ : syracuseStep 2146667 = 3220001) B3220001
theorem B2146895 : Blo 1429534 2146895 := bstep (se 1 (by rfl) ⟨1610171, by rfl⟩ : syracuseStep 2146895 = 3220343) B3220343
theorem B5431931 : Blo 1429534 5431931 := bstep (se 1 (by rfl) ⟨4073948, by rfl⟩ : syracuseStep 5431931 = 8147897) B8147897
theorem B3220091 : Blo 1429534 3220091 := bstep (se 1 (by rfl) ⟨2415068, by rfl⟩ : syracuseStep 3220091 = 4830137) B4830137
theorem B3670667 : Blo 1429534 3670667 := bstep (se 1 (by rfl) ⟨2753000, by rfl⟩ : syracuseStep 3670667 = 5506001) B5506001
theorem B2147015 : Blo 1429534 2147015 := bstep (se 1 (by rfl) ⟨1610261, by rfl⟩ : syracuseStep 2147015 = 3220523) B3220523
theorem B18342611 : Blo 1429534 18342611 := bstep (se 1 (by rfl) ⟨13756958, by rfl⟩ : syracuseStep 18342611 = 27513917) B27513917
theorem B3220217 : Blo 1429534 3220217 := bstep (se 2 (by rfl) ⟨1207581, by rfl⟩ : syracuseStep 3220217 = 2415163) B2415163
theorem B6521629 : Blo 1429534 6521629 := bstep (se 3 (by rfl) ⟨1222805, by rfl⟩ : syracuseStep 6521629 = 2445611) B2445611
theorem B2147177 : Blo 1429534 2147177 := bstep (se 2 (by rfl) ⟨805191, by rfl⟩ : syracuseStep 2147177 = 1610383) B1610383
theorem B3621793 : Blo 1429534 3621793 := bstep (se 2 (by rfl) ⟨1358172, by rfl⟩ : syracuseStep 3621793 = 2716345) B2716345
theorem B2147255 : Blo 1429534 2147255 := bstep (se 1 (by rfl) ⟨1610441, by rfl⟩ : syracuseStep 2147255 = 3220883) B3220883
theorem B2147291 : Blo 1429534 2147291 := bstep (se 1 (by rfl) ⟨1610468, by rfl⟩ : syracuseStep 2147291 = 3220937) B3220937
theorem B2900999 : Blo 1429534 2900999 := bstep (se 1 (by rfl) ⟨2175749, by rfl⟩ : syracuseStep 2900999 = 4351499) B4351499
theorem B3220487 : Blo 1429534 3220487 := bstep (se 1 (by rfl) ⟨2415365, by rfl⟩ : syracuseStep 3220487 = 4830731) B4830731
theorem B9290771 : Blo 1429534 9290771 := bstep (se 1 (by rfl) ⟨6968078, by rfl⟩ : syracuseStep 9290771 = 13936157) B13936157
theorem B3220559 : Blo 1429534 3220559 := bstep (se 1 (by rfl) ⟨2415419, by rfl⟩ : syracuseStep 3220559 = 4830839) B4830839
theorem B9168025 : Blo 1429534 9168025 := bstep (se 2 (by rfl) ⟨3438009, by rfl⟩ : syracuseStep 9168025 = 6876019) B6876019
theorem B9159875 : Blo 1429534 9159875 := bstep (se 1 (by rfl) ⟨6869906, by rfl⟩ : syracuseStep 9159875 = 13739813) B13739813
theorem B46384325 : Blo 1429534 46384325 := bstep (se 4 (by rfl) ⟨4348530, by rfl⟩ : syracuseStep 46384325 = 8697061) B8697061
theorem B11167139 : Blo 1429534 11167139 := bstep (se 1 (by rfl) ⟨8375354, by rfl⟩ : syracuseStep 11167139 = 16750709) B16750709
theorem B7243181 : Blo 1429534 7243181 := bstep (se 3 (by rfl) ⟨1358096, by rfl⟩ : syracuseStep 7243181 = 2716193) B2716193
theorem B47048197 : Blo 1429534 47048197 := bstep (se 4 (by rfl) ⟨4410768, by rfl⟩ : syracuseStep 47048197 = 8821537) B8821537
theorem B13747961 : Blo 1429534 13747961 := bstep (se 2 (by rfl) ⟨5155485, by rfl⟩ : syracuseStep 13747961 = 10310971) B10310971
theorem B10307513 : Blo 1429534 10307513 := bstep (se 2 (by rfl) ⟨3865317, by rfl⟩ : syracuseStep 10307513 = 7730635) B7730635
theorem B4892687 : Blo 1429534 4892687 := bstep (se 1 (by rfl) ⟨3669515, by rfl⟩ : syracuseStep 4892687 = 7339031) B7339031
theorem B4892729 : Blo 1429534 4892729 := bstep (se 2 (by rfl) ⟨1834773, by rfl⟩ : syracuseStep 4892729 = 3669547) B3669547
theorem B7342169 : Blo 1429534 7342169 := bstep (se 2 (by rfl) ⟨2753313, by rfl⟩ : syracuseStep 7342169 = 5506627) B5506627
theorem B10307741 : Blo 1429534 10307741 := bstep (se 3 (by rfl) ⟨1932701, by rfl⟩ : syracuseStep 10307741 = 3865403) B3865403
theorem B4827383 : Blo 1429534 4827383 := bstep (se 1 (by rfl) ⟨3620537, by rfl⟩ : syracuseStep 4827383 = 7241075) B7241075
theorem B10856753 : Blo 1429534 10856753 := bstep (se 2 (by rfl) ⟨4071282, by rfl⟩ : syracuseStep 10856753 = 8142565) B8142565
theorem B2713961 : Blo 1429534 2713961 := bstep (se 2 (by rfl) ⟨1017735, by rfl⟩ : syracuseStep 2713961 = 2035471) B2035471
theorem B2713999 : Blo 1429534 2713999 := bstep (se 1 (by rfl) ⟨2035499, by rfl⟩ : syracuseStep 2713999 = 4070999) B4070999
theorem B4073971 : Blo 1429534 4073971 := bstep (se 1 (by rfl) ⟨3055478, by rfl⟩ : syracuseStep 4073971 = 6110957) B6110957
theorem B4827707 : Blo 1429534 4827707 := bstep (se 1 (by rfl) ⟨3620780, by rfl⟩ : syracuseStep 4827707 = 7241561) B7241561
theorem B21179015 : Blo 1429534 21179015 := bstep (se 1 (by rfl) ⟨15884261, by rfl⟩ : syracuseStep 21179015 = 31768523) B31768523
theorem B3869383 : Blo 1429534 3869383 := bstep (se 1 (by rfl) ⟨2902037, by rfl⟩ : syracuseStep 3869383 = 5804075) B5804075
theorem B3435223 : Blo 1429534 3435223 := bstep (se 1 (by rfl) ⟨2576417, by rfl⟩ : syracuseStep 3435223 = 5152835) B5152835
theorem B4827977 : Blo 1429534 4827977 := bstep (se 2 (by rfl) ⟨1810491, by rfl⟩ : syracuseStep 4827977 = 3620983) B3620983
theorem B4074313 : Blo 1429534 4074313 := bstep (se 2 (by rfl) ⟨1527867, by rfl⟩ : syracuseStep 4074313 = 3055735) B3055735
theorem B19565495 : Blo 1429534 19565495 := bstep (se 1 (by rfl) ⟨14674121, by rfl⟩ : syracuseStep 19565495 = 29348243) B29348243
theorem B7244801 : Blo 1429534 7244801 := bstep (se 2 (by rfl) ⟨2716800, by rfl⟩ : syracuseStep 7244801 = 5433601) B5433601
theorem B6114305 : Blo 1429534 6114305 := bstep (se 2 (by rfl) ⟨2292864, by rfl⟩ : syracuseStep 6114305 = 4585729) B4585729
theorem B9923627 : Blo 1429534 9923627 := bstep (se 1 (by rfl) ⟨7442720, by rfl⟩ : syracuseStep 9923627 = 14885441) B14885441
theorem B23186711 : Blo 1429534 23186711 := bstep (se 1 (by rfl) ⟨17390033, by rfl⟩ : syracuseStep 23186711 = 34780067) B34780067
theorem B6524513 : Blo 1429534 6524513 := bstep (se 2 (by rfl) ⟨2446692, by rfl⟩ : syracuseStep 6524513 = 4893385) B4893385
theorem B1609339 : Blo 1429534 1609339 := bstep (se 1 (by rfl) ⟨1207004, by rfl⟩ : syracuseStep 1609339 = 2414009) B2414009
theorem B4894343 : Blo 1429534 4894343 := bstep (se 1 (by rfl) ⟨3670757, by rfl⟩ : syracuseStep 4894343 = 7341515) B7341515
theorem B2576071 : Blo 1429534 2576071 := bstep (se 1 (by rfl) ⟨1932053, by rfl⟩ : syracuseStep 2576071 = 3864107) B3864107
theorem B6106823 : Blo 1429534 6106823 := bstep (se 1 (by rfl) ⟨4580117, by rfl⟩ : syracuseStep 6106823 = 9160235) B9160235
theorem B7245611 : Blo 1429534 7245611 := bstep (se 1 (by rfl) ⟨5434208, by rfl⟩ : syracuseStep 7245611 = 10868417) B10868417
theorem B12226423 : Blo 1429534 12226423 := bstep (se 1 (by rfl) ⟨9169817, by rfl⟩ : syracuseStep 12226423 = 18339635) B18339635
theorem B2412463 : Blo 1429534 2412463 := bstep (se 1 (by rfl) ⟨1809347, by rfl⟩ : syracuseStep 2412463 = 3618695) B3618695
theorem B4829111 : Blo 1429534 4829111 := bstep (se 1 (by rfl) ⟨3621833, by rfl⟩ : syracuseStep 4829111 = 7243667) B7243667
theorem B2412551 : Blo 1429534 2412551 := bstep (se 1 (by rfl) ⟨1809413, by rfl⟩ : syracuseStep 2412551 = 3618827) B3618827
theorem B1429543 : Blo 1429534 1429543 := bstep (se 1 (by rfl) ⟨1072157, by rfl⟩ : syracuseStep 1429543 = 2144315) B2144315
theorem B1429583 : Blo 1429534 1429583 := bstep (se 1 (by rfl) ⟨1072187, by rfl⟩ : syracuseStep 1429583 = 2144375) B2144375
theorem B1609807 : Blo 1429534 1609807 := bstep (se 1 (by rfl) ⟨1207355, by rfl⟩ : syracuseStep 1609807 = 2414711) B2414711
theorem B1429599 : Blo 1429534 1429599 := bstep (se 1 (by rfl) ⟨1072199, by rfl⟩ : syracuseStep 1429599 = 2144399) B2144399
theorem B1429627 : Blo 1429534 1429627 := bstep (se 1 (by rfl) ⟨1072220, by rfl⟩ : syracuseStep 1429627 = 2144441) B2144441
theorem B11604131 : Blo 1429534 11604131 := bstep (se 1 (by rfl) ⟨8703098, by rfl⟩ : syracuseStep 11604131 = 17406197) B17406197
theorem B1429679 : Blo 1429534 1429679 := bstep (se 1 (by rfl) ⟨1072259, by rfl⟩ : syracuseStep 1429679 = 2144519) B2144519
theorem B1429703 : Blo 1429534 1429703 := bstep (se 1 (by rfl) ⟨1072277, by rfl⟩ : syracuseStep 1429703 = 2144555) B2144555
theorem B2715859 : Blo 1429534 2715859 := bstep (se 1 (by rfl) ⟨2036894, by rfl⟩ : syracuseStep 2715859 = 4073789) B4073789
theorem B1429723 : Blo 1429534 1429723 := bstep (se 1 (by rfl) ⟨1072292, by rfl⟩ : syracuseStep 1429723 = 2144585) B2144585
theorem B1429799 : Blo 1429534 1429799 := bstep (se 1 (by rfl) ⟨1072349, by rfl⟩ : syracuseStep 1429799 = 2144699) B2144699
theorem B7065917 : Blo 1429534 7065917 := bstep (se 3 (by rfl) ⟨1324859, by rfl⟩ : syracuseStep 7065917 = 2649719) B2649719
theorem B1429839 : Blo 1429534 1429839 := bstep (se 1 (by rfl) ⟨1072379, by rfl⟩ : syracuseStep 1429839 = 2144759) B2144759
theorem B5509463 : Blo 1429534 5509463 := bstep (se 1 (by rfl) ⟨4132097, by rfl⟩ : syracuseStep 5509463 = 8264195) B8264195
theorem B1429855 : Blo 1429534 1429855 := bstep (se 1 (by rfl) ⟨1072391, by rfl⟩ : syracuseStep 1429855 = 2144783) B2144783
theorem B2412895 : Blo 1429534 2412895 := bstep (se 1 (by rfl) ⟨1809671, by rfl⟩ : syracuseStep 2412895 = 3619343) B3619343
theorem B2036063 : Blo 1429534 2036063 := bstep (se 1 (by rfl) ⟨1527047, by rfl⟩ : syracuseStep 2036063 = 3054095) B3054095
theorem B1429883 : Blo 1429534 1429883 := bstep (se 1 (by rfl) ⟨1072412, by rfl⟩ : syracuseStep 1429883 = 2144825) B2144825
theorem B1429935 : Blo 1429534 1429935 := bstep (se 1 (by rfl) ⟨1072451, by rfl⟩ : syracuseStep 1429935 = 2144903) B2144903
theorem B2412983 : Blo 1429534 2412983 := bstep (se 1 (by rfl) ⟨1809737, by rfl⟩ : syracuseStep 2412983 = 3619475) B3619475
theorem B2716087 : Blo 1429534 2716087 := bstep (se 1 (by rfl) ⟨2037065, by rfl⟩ : syracuseStep 2716087 = 4074131) B4074131
theorem B1429959 : Blo 1429534 1429959 := bstep (se 1 (by rfl) ⟨1072469, by rfl⟩ : syracuseStep 1429959 = 2144939) B2144939
theorem B1429979 : Blo 1429534 1429979 := bstep (se 1 (by rfl) ⟨1072484, by rfl⟩ : syracuseStep 1429979 = 2144969) B2144969
theorem B1610203 : Blo 1429534 1610203 := bstep (se 1 (by rfl) ⟨1207652, by rfl⟩ : syracuseStep 1610203 = 2415305) B2415305
theorem B8147465 : Blo 1429534 8147465 := bstep (se 2 (by rfl) ⟨3055299, by rfl⟩ : syracuseStep 8147465 = 6110599) B6110599
theorem B4829705 : Blo 1429534 4829705 := bstep (se 2 (by rfl) ⟨1811139, by rfl⟩ : syracuseStep 4829705 = 3622279) B3622279
theorem B1430055 : Blo 1429534 1430055 := bstep (se 1 (by rfl) ⟨1072541, by rfl⟩ : syracuseStep 1430055 = 2145083) B2145083
theorem B1430095 : Blo 1429534 1430095 := bstep (se 1 (by rfl) ⟨1072571, by rfl⟩ : syracuseStep 1430095 = 2145143) B2145143
theorem B1430111 : Blo 1429534 1430111 := bstep (se 1 (by rfl) ⟨1072583, by rfl⟩ : syracuseStep 1430111 = 2145167) B2145167
theorem B1430139 : Blo 1429534 1430139 := bstep (se 1 (by rfl) ⟨1072604, by rfl⟩ : syracuseStep 1430139 = 2145209) B2145209
theorem B1430191 : Blo 1429534 1430191 := bstep (se 1 (by rfl) ⟨1072643, by rfl⟩ : syracuseStep 1430191 = 2145287) B2145287
theorem B1430215 : Blo 1429534 1430215 := bstep (se 1 (by rfl) ⟨1072661, by rfl⟩ : syracuseStep 1430215 = 2145323) B2145323
theorem B1430235 : Blo 1429534 1430235 := bstep (se 1 (by rfl) ⟨1072676, by rfl⟩ : syracuseStep 1430235 = 2145353) B2145353
theorem B1430311 : Blo 1429534 1430311 := bstep (se 1 (by rfl) ⟨1072733, by rfl⟩ : syracuseStep 1430311 = 2145467) B2145467
theorem B5223241 : Blo 1429534 5223241 := bstep (se 2 (by rfl) ⟨1958715, by rfl⟩ : syracuseStep 5223241 = 3917431) B3917431
theorem B1430351 : Blo 1429534 1430351 := bstep (se 1 (by rfl) ⟨1072763, by rfl⟩ : syracuseStep 1430351 = 2145527) B2145527
theorem B1430367 : Blo 1429534 1430367 := bstep (se 1 (by rfl) ⟨1072775, by rfl⟩ : syracuseStep 1430367 = 2145551) B2145551
theorem B1430395 : Blo 1429534 1430395 := bstep (se 1 (by rfl) ⟨1072796, by rfl⟩ : syracuseStep 1430395 = 2145593) B2145593
theorem B9163667 : Blo 1429534 9163667 := bstep (se 1 (by rfl) ⟨6872750, by rfl⟩ : syracuseStep 9163667 = 13745501) B13745501
theorem B1430447 : Blo 1429534 1430447 := bstep (se 1 (by rfl) ⟨1072835, by rfl⟩ : syracuseStep 1430447 = 2145671) B2145671
theorem B1430471 : Blo 1429534 1430471 := bstep (se 1 (by rfl) ⟨1072853, by rfl⟩ : syracuseStep 1430471 = 2145707) B2145707
theorem B1430491 : Blo 1429534 1430491 := bstep (se 1 (by rfl) ⟨1072868, by rfl⟩ : syracuseStep 1430491 = 2145737) B2145737
theorem B2716679 : Blo 1429534 2716679 := bstep (se 1 (by rfl) ⟨2037509, by rfl⟩ : syracuseStep 2716679 = 4075019) B4075019
theorem B2413577 : Blo 1429534 2413577 := bstep (se 2 (by rfl) ⟨905091, by rfl⟩ : syracuseStep 2413577 = 1810183) B1810183
theorem B1430567 : Blo 1429534 1430567 := bstep (se 1 (by rfl) ⟨1072925, by rfl⟩ : syracuseStep 1430567 = 2145851) B2145851
theorem B1430607 : Blo 1429534 1430607 := bstep (se 1 (by rfl) ⟨1072955, by rfl⟩ : syracuseStep 1430607 = 2145911) B2145911
theorem B1430623 : Blo 1429534 1430623 := bstep (se 1 (by rfl) ⟨1072967, by rfl⟩ : syracuseStep 1430623 = 2145935) B2145935
theorem B17396855 : Blo 1429534 17396855 := bstep (se 1 (by rfl) ⟨13047641, by rfl⟩ : syracuseStep 17396855 = 26095283) B26095283
theorem B1430651 : Blo 1429534 1430651 := bstep (se 1 (by rfl) ⟨1072988, by rfl⟩ : syracuseStep 1430651 = 2145977) B2145977
theorem B2413739 : Blo 1429534 2413739 := bstep (se 1 (by rfl) ⟨1810304, by rfl⟩ : syracuseStep 2413739 = 3620609) B3620609
theorem B1430703 : Blo 1429534 1430703 := bstep (se 1 (by rfl) ⟨1073027, by rfl⟩ : syracuseStep 1430703 = 2146055) B2146055
theorem B1430727 : Blo 1429534 1430727 := bstep (se 1 (by rfl) ⟨1073045, by rfl⟩ : syracuseStep 1430727 = 2146091) B2146091
theorem B1430747 : Blo 1429534 1430747 := bstep (se 1 (by rfl) ⟨1073060, by rfl⟩ : syracuseStep 1430747 = 2146121) B2146121
theorem B8148215 : Blo 1429534 8148215 := bstep (se 1 (by rfl) ⟨6111161, by rfl⟩ : syracuseStep 8148215 = 12222323) B12222323
theorem B1430823 : Blo 1429534 1430823 := bstep (se 1 (by rfl) ⟨1073117, by rfl⟩ : syracuseStep 1430823 = 2146235) B2146235
theorem B1430863 : Blo 1429534 1430863 := bstep (se 1 (by rfl) ⟨1073147, by rfl⟩ : syracuseStep 1430863 = 2146295) B2146295
theorem B1430879 : Blo 1429534 1430879 := bstep (se 1 (by rfl) ⟨1073159, by rfl⟩ : syracuseStep 1430879 = 2146319) B2146319
theorem B4830569 : Blo 1429534 4830569 := bstep (se 2 (by rfl) ⟨1811463, by rfl⟩ : syracuseStep 4830569 = 3622927) B3622927
theorem B1430907 : Blo 1429534 1430907 := bstep (se 1 (by rfl) ⟨1073180, by rfl⟩ : syracuseStep 1430907 = 2146361) B2146361
theorem B4584833 : Blo 1429534 4584833 := bstep (se 2 (by rfl) ⟨1719312, by rfl⟩ : syracuseStep 4584833 = 3438625) B3438625
theorem B8148397 : Blo 1429534 8148397 := bstep (se 3 (by rfl) ⟨1527824, by rfl⟩ : syracuseStep 8148397 = 3055649) B3055649
theorem B1430959 : Blo 1429534 1430959 := bstep (se 1 (by rfl) ⟨1073219, by rfl⟩ : syracuseStep 1430959 = 2146439) B2146439
theorem B1430983 : Blo 1429534 1430983 := bstep (se 1 (by rfl) ⟨1073237, by rfl⟩ : syracuseStep 1430983 = 2146475) B2146475
theorem B41268689 : Blo 1429534 41268689 := bstep (se 2 (by rfl) ⟨15475758, by rfl⟩ : syracuseStep 41268689 = 30951517) B30951517
theorem B7239131 : Blo 1429534 7239131 := bstep (se 1 (by rfl) ⟨5429348, by rfl⟩ : syracuseStep 7239131 = 10858697) B10858697
theorem B1431003 : Blo 1429534 1431003 := bstep (se 1 (by rfl) ⟨1073252, by rfl⟩ : syracuseStep 1431003 = 2146505) B2146505
theorem B3438067 : Blo 1429534 3438067 := bstep (se 1 (by rfl) ⟨2578550, by rfl⟩ : syracuseStep 3438067 = 5157101) B5157101
theorem B3216905 : Blo 1429534 3216905 := bstep (se 2 (by rfl) ⟨1206339, by rfl⟩ : syracuseStep 3216905 = 2412679) B2412679
theorem B1431079 : Blo 1429534 1431079 := bstep (se 1 (by rfl) ⟨1073309, by rfl⟩ : syracuseStep 1431079 = 2146619) B2146619
theorem B2414137 : Blo 1429534 2414137 := bstep (se 2 (by rfl) ⟨905301, by rfl⟩ : syracuseStep 2414137 = 1810603) B1810603
theorem B1431119 : Blo 1429534 1431119 := bstep (se 1 (by rfl) ⟨1073339, by rfl⟩ : syracuseStep 1431119 = 2146679) B2146679
theorem B1431135 : Blo 1429534 1431135 := bstep (se 1 (by rfl) ⟨1073351, by rfl⟩ : syracuseStep 1431135 = 2146703) B2146703
theorem B10860155 : Blo 1429534 10860155 := bstep (se 1 (by rfl) ⟨8145116, by rfl⟩ : syracuseStep 10860155 = 16290233) B16290233
theorem B1431163 : Blo 1429534 1431163 := bstep (se 1 (by rfl) ⟨1073372, by rfl⟩ : syracuseStep 1431163 = 2146745) B2146745
theorem B1431215 : Blo 1429534 1431215 := bstep (se 1 (by rfl) ⟨1073411, by rfl⟩ : syracuseStep 1431215 = 2146823) B2146823
theorem B2414279 : Blo 1429534 2414279 := bstep (se 1 (by rfl) ⟨1810709, by rfl⟩ : syracuseStep 2414279 = 3621419) B3621419
theorem B1431239 : Blo 1429534 1431239 := bstep (se 1 (by rfl) ⟨1073429, by rfl⟩ : syracuseStep 1431239 = 2146859) B2146859
theorem B1431259 : Blo 1429534 1431259 := bstep (se 1 (by rfl) ⟨1073444, by rfl⟩ : syracuseStep 1431259 = 2146889) B2146889
theorem B3618553 : Blo 1429534 3618553 := bstep (se 2 (by rfl) ⟨1356957, by rfl⟩ : syracuseStep 3618553 = 2713915) B2713915
theorem B1431335 : Blo 1429534 1431335 := bstep (se 1 (by rfl) ⟨1073501, by rfl⟩ : syracuseStep 1431335 = 2147003) B2147003
theorem B41252651 : Blo 1429534 41252651 := bstep (se 1 (by rfl) ⟨30939488, by rfl⟩ : syracuseStep 41252651 = 61878977) B61878977
theorem B1431375 : Blo 1429534 1431375 := bstep (se 1 (by rfl) ⟨1073531, by rfl⟩ : syracuseStep 1431375 = 2147063) B2147063
theorem B3217247 : Blo 1429534 3217247 := bstep (se 1 (by rfl) ⟨2412935, by rfl⟩ : syracuseStep 3217247 = 4825871) B4825871
theorem B1431391 : Blo 1429534 1431391 := bstep (se 1 (by rfl) ⟨1073543, by rfl⟩ : syracuseStep 1431391 = 2147087) B2147087
theorem B2414441 : Blo 1429534 2414441 := bstep (se 2 (by rfl) ⟨905415, by rfl⟩ : syracuseStep 2414441 = 1810831) B1810831
theorem B3438443 : Blo 1429534 3438443 := bstep (se 1 (by rfl) ⟨2578832, by rfl⟩ : syracuseStep 3438443 = 5157665) B5157665
theorem B2717545 : Blo 1429534 2717545 := bstep (se 2 (by rfl) ⟨1019079, by rfl⟩ : syracuseStep 2717545 = 2038159) B2038159
theorem B1431419 : Blo 1429534 1431419 := bstep (se 1 (by rfl) ⟨1073564, by rfl⟩ : syracuseStep 1431419 = 2147129) B2147129
theorem B5224367 : Blo 1429534 5224367 := bstep (se 1 (by rfl) ⟨3918275, by rfl⟩ : syracuseStep 5224367 = 7836551) B7836551
theorem B1431471 : Blo 1429534 1431471 := bstep (se 1 (by rfl) ⟨1073603, by rfl⟩ : syracuseStep 1431471 = 2147207) B2147207
theorem B8148923 : Blo 1429534 8148923 := bstep (se 1 (by rfl) ⟨6111692, by rfl⟩ : syracuseStep 8148923 = 12223385) B12223385
theorem B4831163 : Blo 1429534 4831163 := bstep (se 1 (by rfl) ⟨3623372, by rfl⟩ : syracuseStep 4831163 = 7246745) B7246745
theorem B7239617 : Blo 1429534 7239617 := bstep (se 2 (by rfl) ⟨2714856, by rfl⟩ : syracuseStep 7239617 = 5429713) B5429713
theorem B1431495 : Blo 1429534 1431495 := bstep (se 1 (by rfl) ⟨1073621, by rfl⟩ : syracuseStep 1431495 = 2147243) B2147243
theorem B1431515 : Blo 1429534 1431515 := bstep (se 1 (by rfl) ⟨1073636, by rfl⟩ : syracuseStep 1431515 = 2147273) B2147273
theorem B3217427 : Blo 1429534 3217427 := bstep (se 1 (by rfl) ⟨2413070, by rfl⟩ : syracuseStep 3217427 = 4826141) B4826141
theorem B50894905 : Blo 1429534 50894905 := bstep (se 2 (by rfl) ⟨19085589, by rfl⟩ : syracuseStep 50894905 = 38171179) B38171179
theorem B2414839 : Blo 1429534 2414839 := bstep (se 1 (by rfl) ⟨1811129, by rfl⟩ : syracuseStep 2414839 = 3622259) B3622259
theorem B3217769 : Blo 1429534 3217769 := bstep (se 2 (by rfl) ⟨1206663, by rfl⟩ : syracuseStep 3217769 = 2413327) B2413327
theorem B3619201 : Blo 1429534 3619201 := bstep (se 2 (by rfl) ⟨1357200, by rfl⟩ : syracuseStep 3619201 = 2714401) B2714401
theorem B16300439 : Blo 1429534 16300439 := bstep (se 1 (by rfl) ⟨12225329, by rfl⟩ : syracuseStep 16300439 = 24450659) B24450659
theorem B2144687 : Blo 1429534 2144687 := bstep (se 1 (by rfl) ⟨1608515, by rfl⟩ : syracuseStep 2144687 = 3217031) B3217031
theorem B2415035 : Blo 1429534 2415035 := bstep (se 1 (by rfl) ⟨1811276, by rfl⟩ : syracuseStep 2415035 = 3622553) B3622553
theorem B2144777 : Blo 1429534 2144777 := bstep (se 2 (by rfl) ⟨804291, by rfl⟩ : syracuseStep 2144777 = 1608583) B1608583
theorem B2144807 : Blo 1429534 2144807 := bstep (se 1 (by rfl) ⟨1608605, by rfl⟩ : syracuseStep 2144807 = 3217211) B3217211
theorem B2415143 : Blo 1429534 2415143 := bstep (se 1 (by rfl) ⟨1811357, by rfl⟩ : syracuseStep 2415143 = 3622715) B3622715
theorem B2144891 : Blo 1429534 2144891 := bstep (se 1 (by rfl) ⟨1608668, by rfl⟩ : syracuseStep 2144891 = 3217337) B3217337
theorem B7338707 : Blo 1429534 7338707 := bstep (se 1 (by rfl) ⟨5504030, by rfl⟩ : syracuseStep 7338707 = 11008061) B11008061
theorem B2145017 : Blo 1429534 2145017 := bstep (se 2 (by rfl) ⟨804381, by rfl⟩ : syracuseStep 2145017 = 1608763) B1608763
theorem B2415433 : Blo 1429534 2415433 := bstep (se 2 (by rfl) ⟨905787, by rfl⟩ : syracuseStep 2415433 = 1811575) B1811575
theorem B2145119 : Blo 1429534 2145119 := bstep (se 1 (by rfl) ⟨1608839, by rfl⟩ : syracuseStep 2145119 = 3217679) B3217679
theorem B2145131 : Blo 1429534 2145131 := bstep (se 1 (by rfl) ⟨1608848, by rfl⟩ : syracuseStep 2145131 = 3217697) B3217697
theorem B2415467 : Blo 1429534 2415467 := bstep (se 1 (by rfl) ⟨1811600, by rfl⟩ : syracuseStep 2415467 = 3623201) B3623201
theorem B5430199 : Blo 1429534 5430199 := bstep (se 1 (by rfl) ⟨4072649, by rfl⟩ : syracuseStep 5430199 = 8145299) B8145299
theorem B3218363 : Blo 1429534 3218363 := bstep (se 1 (by rfl) ⟨2413772, by rfl⟩ : syracuseStep 3218363 = 4827545) B4827545
theorem B14679083 : Blo 1429534 14679083 := bstep (se 1 (by rfl) ⟨11009312, by rfl⟩ : syracuseStep 14679083 = 22018625) B22018625
theorem B3218489 : Blo 1429534 3218489 := bstep (se 2 (by rfl) ⟨1206933, by rfl⟩ : syracuseStep 3218489 = 2413867) B2413867
theorem B2145359 : Blo 1429534 2145359 := bstep (se 1 (by rfl) ⟨1609019, by rfl⟩ : syracuseStep 2145359 = 3218039) B3218039
theorem B4136107 : Blo 1429534 4136107 := bstep (se 1 (by rfl) ⟨3102080, by rfl⟩ : syracuseStep 4136107 = 6204161) B6204161
theorem B3620011 : Blo 1429534 3620011 := bstep (se 1 (by rfl) ⟨2715008, by rfl⟩ : syracuseStep 3620011 = 5430017) B5430017
theorem B2145479 : Blo 1429534 2145479 := bstep (se 1 (by rfl) ⟨1609109, by rfl⟩ : syracuseStep 2145479 = 3218219) B3218219
theorem B2145641 : Blo 1429534 2145641 := bstep (se 2 (by rfl) ⟨804615, by rfl⟩ : syracuseStep 2145641 = 1609231) B1609231
theorem B4349309 : Blo 1429534 4349309 := bstep (se 3 (by rfl) ⟨815495, by rfl⟩ : syracuseStep 4349309 = 1630991) B1630991
theorem B5430671 : Blo 1429534 5430671 := bstep (se 1 (by rfl) ⟨4073003, by rfl⟩ : syracuseStep 5430671 = 8146007) B8146007
theorem B3218831 : Blo 1429534 3218831 := bstep (se 1 (by rfl) ⟨2414123, by rfl⟩ : syracuseStep 3218831 = 4828247) B4828247
theorem B4963727 : Blo 1429534 4963727 := bstep (se 1 (by rfl) ⟨3722795, by rfl⟩ : syracuseStep 4963727 = 7445591) B7445591
theorem B39706033 : Blo 1429534 39706033 := bstep (se 2 (by rfl) ⟨14889762, by rfl⟩ : syracuseStep 39706033 = 29779525) B29779525
theorem B2145719 : Blo 1429534 2145719 := bstep (se 1 (by rfl) ⟨1609289, by rfl⟩ : syracuseStep 2145719 = 3218579) B3218579
theorem B3620315 : Blo 1429534 3620315 := bstep (se 1 (by rfl) ⟨2715236, by rfl⟩ : syracuseStep 3620315 = 5430473) B5430473
theorem B2145755 : Blo 1429534 2145755 := bstep (se 1 (by rfl) ⟨1609316, by rfl⟩ : syracuseStep 2145755 = 3218633) B3218633
theorem B29359655 : Blo 1429534 29359655 := bstep (se 1 (by rfl) ⟨22019741, by rfl⟩ : syracuseStep 29359655 = 44039483) B44039483
theorem B7732883 : Blo 1429534 7732883 := bstep (se 1 (by rfl) ⟨5799662, by rfl⟩ : syracuseStep 7732883 = 11599325) B11599325
theorem B7339709 : Blo 1429534 7339709 := bstep (se 3 (by rfl) ⟨1376195, by rfl⟩ : syracuseStep 7339709 = 2752391) B2752391
theorem B3219155 : Blo 1429534 3219155 := bstep (se 1 (by rfl) ⟨2414366, by rfl⟩ : syracuseStep 3219155 = 4828733) B4828733
theorem B4824791 : Blo 1429534 4824791 := bstep (se 1 (by rfl) ⟨3618593, by rfl⟩ : syracuseStep 4824791 = 7237187) B7237187
theorem B20914051 : Blo 1429534 20914051 := bstep (se 1 (by rfl) ⟨15685538, by rfl⟩ : syracuseStep 20914051 = 31371077) B31371077
theorem B4071329 : Blo 1429534 4071329 := bstep (se 2 (by rfl) ⟨1526748, by rfl⟩ : syracuseStep 4071329 = 3053497) B3053497
theorem B4825007 : Blo 1429534 4825007 := bstep (se 1 (by rfl) ⟨3618755, by rfl⟩ : syracuseStep 4825007 = 7237511) B7237511
theorem B2146223 : Blo 1429534 2146223 := bstep (se 1 (by rfl) ⟨1609667, by rfl⟩ : syracuseStep 2146223 = 3219335) B3219335
theorem B2146409 : Blo 1429534 2146409 := bstep (se 2 (by rfl) ⟨804903, by rfl⟩ : syracuseStep 2146409 = 1609807) B1609807
theorem B4710611 : Blo 1429534 4710611 := bstep (se 1 (by rfl) ⟨3532958, by rfl⟩ : syracuseStep 4710611 = 7065917) B7065917
theorem B19579117 : Blo 1429534 19579117 := bstep (se 3 (by rfl) ⟨3671084, by rfl⟩ : syracuseStep 19579117 = 7342169) B7342169
theorem B3621145 : Blo 1429534 3621145 := bstep (se 2 (by rfl) ⟨1357929, by rfl⟩ : syracuseStep 3621145 = 2715859) B2715859
theorem B3219785 : Blo 1429534 3219785 := bstep (se 2 (by rfl) ⟨1207419, by rfl⟩ : syracuseStep 3219785 = 2414839) B2414839
theorem B5431643 : Blo 1429534 5431643 := bstep (se 1 (by rfl) ⟨4073732, by rfl⟩ : syracuseStep 5431643 = 8147465) B8147465
theorem B3219803 : Blo 1429534 3219803 := bstep (se 1 (by rfl) ⟨2414852, by rfl⟩ : syracuseStep 3219803 = 4829705) B4829705
theorem B3621287 : Blo 1429534 3621287 := bstep (se 1 (by rfl) ⟨2715965, by rfl⟩ : syracuseStep 3621287 = 5431931) B5431931
theorem B2146727 : Blo 1429534 2146727 := bstep (se 1 (by rfl) ⟨1610045, by rfl⟩ : syracuseStep 2146727 = 3220091) B3220091
theorem B7242209 : Blo 1429534 7242209 := bstep (se 2 (by rfl) ⟨2715828, by rfl⟩ : syracuseStep 7242209 = 5431657) B5431657
theorem B2146811 : Blo 1429534 2146811 := bstep (se 1 (by rfl) ⟨1610108, by rfl⟩ : syracuseStep 2146811 = 3220217) B3220217
theorem B4825601 : Blo 1429534 4825601 := bstep (se 2 (by rfl) ⟨1809600, by rfl⟩ : syracuseStep 4825601 = 3619201) B3619201
theorem B3621449 : Blo 1429534 3621449 := bstep (se 2 (by rfl) ⟨1358043, by rfl⟩ : syracuseStep 3621449 = 2716087) B2716087
theorem B2146937 : Blo 1429534 2146937 := bstep (se 2 (by rfl) ⟨805101, by rfl⟩ : syracuseStep 2146937 = 1610203) B1610203
theorem B5431961 : Blo 1429534 5431961 := bstep (se 2 (by rfl) ⟨2036985, by rfl⟩ : syracuseStep 5431961 = 4073971) B4073971
theorem B1933999 : Blo 1429534 1933999 := bstep (se 1 (by rfl) ⟨1450499, by rfl⟩ : syracuseStep 1933999 = 2900999) B2900999
theorem B2146991 : Blo 1429534 2146991 := bstep (se 1 (by rfl) ⟨1610243, by rfl⟩ : syracuseStep 2146991 = 3220487) B3220487
theorem B6193847 : Blo 1429534 6193847 := bstep (se 1 (by rfl) ⟨4645385, by rfl⟩ : syracuseStep 6193847 = 9290771) B9290771
theorem B2147039 : Blo 1429534 2147039 := bstep (se 1 (by rfl) ⟨1610279, by rfl⟩ : syracuseStep 2147039 = 3220559) B3220559
theorem B5432143 : Blo 1429534 5432143 := bstep (se 1 (by rfl) ⟨4074107, by rfl⟩ : syracuseStep 5432143 = 8148215) B8148215
theorem B3220379 : Blo 1429534 3220379 := bstep (se 1 (by rfl) ⟨2415284, by rfl⟩ : syracuseStep 3220379 = 4830569) B4830569
theorem B3056555 : Blo 1429534 3056555 := bstep (se 1 (by rfl) ⟨2292416, by rfl⟩ : syracuseStep 3056555 = 4584833) B4584833
theorem B4580297 : Blo 1429534 4580297 := bstep (se 2 (by rfl) ⟨1717611, by rfl⟩ : syracuseStep 4580297 = 3435223) B3435223
theorem B4826087 : Blo 1429534 4826087 := bstep (se 1 (by rfl) ⟨3619565, by rfl⟩ : syracuseStep 4826087 = 7239131) B7239131
theorem B6964321 : Blo 1429534 6964321 := bstep (se 2 (by rfl) ⟨2611620, by rfl⟩ : syracuseStep 6964321 = 5223241) B5223241
theorem B5432417 : Blo 1429534 5432417 := bstep (se 2 (by rfl) ⟨2037156, by rfl⟩ : syracuseStep 5432417 = 4074313) B4074313
theorem B3220577 : Blo 1429534 3220577 := bstep (se 2 (by rfl) ⟨1207716, by rfl⟩ : syracuseStep 3220577 = 2415433) B2415433
theorem B27501767 : Blo 1429534 27501767 := bstep (se 1 (by rfl) ⟨20626325, by rfl⟩ : syracuseStep 27501767 = 41252651) B41252651
theorem B3482911 : Blo 1429534 3482911 := bstep (se 1 (by rfl) ⟨2612183, by rfl⟩ : syracuseStep 3482911 = 5224367) B5224367
theorem B5432615 : Blo 1429534 5432615 := bstep (se 1 (by rfl) ⟨4074461, by rfl⟩ : syracuseStep 5432615 = 8148923) B8148923
theorem B3220775 : Blo 1429534 3220775 := bstep (se 1 (by rfl) ⟨2415581, by rfl⟩ : syracuseStep 3220775 = 4831163) B4831163
theorem B4826411 : Blo 1429534 4826411 := bstep (se 1 (by rfl) ⟨3619808, by rfl⟩ : syracuseStep 4826411 = 7239617) B7239617
theorem B3261791 : Blo 1429534 3261791 := bstep (se 1 (by rfl) ⟨2446343, by rfl⟩ : syracuseStep 3261791 = 4892687) B4892687
theorem B12224033 : Blo 1429534 12224033 := bstep (se 2 (by rfl) ⟨4584012, by rfl⟩ : syracuseStep 12224033 = 9168025) B9168025
theorem B5514809 : Blo 1429534 5514809 := bstep (se 2 (by rfl) ⟨2068053, by rfl⟩ : syracuseStep 5514809 = 4136107) B4136107
theorem B4826681 : Blo 1429534 4826681 := bstep (se 2 (by rfl) ⟨1810005, by rfl⟩ : syracuseStep 4826681 = 3620011) B3620011
theorem B4892471 : Blo 1429534 4892471 := bstep (se 1 (by rfl) ⟨3669353, by rfl⟩ : syracuseStep 4892471 = 7338707) B7338707
theorem B10864529 : Blo 1429534 10864529 := bstep (se 2 (by rfl) ⟨4074198, by rfl⟩ : syracuseStep 10864529 = 8148397) B8148397
theorem B13043663 : Blo 1429534 13043663 := bstep (se 1 (by rfl) ⟨9782747, by rfl⟩ : syracuseStep 13043663 = 19565495) B19565495
theorem B3434761 : Blo 1429534 3434761 := bstep (se 2 (by rfl) ⟨1288035, by rfl⟩ : syracuseStep 3434761 = 2576071) B2576071
theorem B19573103 : Blo 1429534 19573103 := bstep (se 1 (by rfl) ⟨14679827, by rfl⟩ : syracuseStep 19573103 = 29359655) B29359655
theorem B3262895 : Blo 1429534 3262895 := bstep (se 1 (by rfl) ⟨2447171, by rfl⟩ : syracuseStep 3262895 = 4894343) B4894343
theorem B5155255 : Blo 1429534 5155255 := bstep (se 1 (by rfl) ⟨3866441, by rfl⟩ : syracuseStep 5155255 = 7732883) B7732883
theorem B4893139 : Blo 1429534 4893139 := bstep (se 1 (by rfl) ⟨3669854, by rfl⟩ : syracuseStep 4893139 = 7339709) B7339709
theorem B3623393 : Blo 1429534 3623393 := bstep (se 2 (by rfl) ⟨1358772, by rfl⟩ : syracuseStep 3623393 = 2717545) B2717545
theorem B2714219 : Blo 1429534 2714219 := bstep (se 1 (by rfl) ⟨2035664, by rfl⟩ : syracuseStep 2714219 = 4071329) B4071329
theorem B16304813 : Blo 1429534 16304813 := bstep (se 3 (by rfl) ⟨3057152, by rfl⟩ : syracuseStep 16304813 = 6114305) B6114305
theorem B1608367 : Blo 1429534 1608367 := bstep (se 1 (by rfl) ⟨1206275, by rfl⟩ : syracuseStep 1608367 = 2412551) B2412551
theorem B7244477 : Blo 1429534 7244477 := bstep (se 3 (by rfl) ⟨1358339, by rfl⟩ : syracuseStep 7244477 = 2716679) B2716679
theorem B26471123 : Blo 1429534 26471123 := bstep (se 1 (by rfl) ⟨19853342, by rfl⟩ : syracuseStep 26471123 = 39706685) B39706685
theorem B4827923 : Blo 1429534 4827923 := bstep (se 1 (by rfl) ⟨3620942, by rfl⟩ : syracuseStep 4827923 = 7241885) B7241885
theorem B10857239 : Blo 1429534 10857239 := bstep (se 1 (by rfl) ⟨8142929, by rfl⟩ : syracuseStep 10857239 = 16285859) B16285859
theorem B7736087 : Blo 1429534 7736087 := bstep (se 1 (by rfl) ⟨5802065, by rfl⟩ : syracuseStep 7736087 = 11604131) B11604131
theorem B2714447 : Blo 1429534 2714447 := bstep (se 1 (by rfl) ⟨2035835, by rfl⟩ : syracuseStep 2714447 = 4071671) B4071671
theorem B1608655 : Blo 1429534 1608655 := bstep (se 1 (by rfl) ⟨1206491, by rfl⟩ : syracuseStep 1608655 = 2412983) B2412983
theorem B27487309 : Blo 1429534 27487309 := bstep (se 3 (by rfl) ⟨5153870, by rfl⟩ : syracuseStep 27487309 = 10307741) B10307741
theorem B1609051 : Blo 1429534 1609051 := bstep (se 1 (by rfl) ⟨1206788, by rfl⟩ : syracuseStep 1609051 = 2413577) B2413577
theorem B1609159 : Blo 1429534 1609159 := bstep (se 1 (by rfl) ⟨1206869, by rfl⟩ : syracuseStep 1609159 = 2413739) B2413739
theorem B6106583 : Blo 1429534 6106583 := bstep (se 1 (by rfl) ⟨4579937, by rfl⟩ : syracuseStep 6106583 = 9159875) B9159875
theorem B14691901 : Blo 1429534 14691901 := bstep (se 3 (by rfl) ⟨2754731, by rfl⟩ : syracuseStep 14691901 = 5509463) B5509463
theorem B4828787 : Blo 1429534 4828787 := bstep (se 1 (by rfl) ⟨3621590, by rfl⟩ : syracuseStep 4828787 = 7243181) B7243181
theorem B27512459 : Blo 1429534 27512459 := bstep (se 1 (by rfl) ⟨20634344, by rfl⟩ : syracuseStep 27512459 = 41268689) B41268689
theorem B8695505 : Blo 1429534 8695505 := bstep (se 2 (by rfl) ⟨3260814, by rfl⟩ : syracuseStep 8695505 = 6521629) B6521629
theorem B1609519 : Blo 1429534 1609519 := bstep (se 1 (by rfl) ⟨1207139, by rfl⟩ : syracuseStep 1609519 = 2414279) B2414279
theorem B4829057 : Blo 1429534 4829057 := bstep (se 2 (by rfl) ⟨1810896, by rfl⟩ : syracuseStep 4829057 = 3621793) B3621793
theorem B1609627 : Blo 1429534 1609627 := bstep (se 1 (by rfl) ⟨1207220, by rfl⟩ : syracuseStep 1609627 = 2414441) B2414441
theorem B7237835 : Blo 1429534 7237835 := bstep (se 1 (by rfl) ⟨5428376, by rfl⟩ : syracuseStep 7237835 = 10856753) B10856753
theorem B10866959 : Blo 1429534 10866959 := bstep (se 1 (by rfl) ⟨8150219, by rfl⟩ : syracuseStep 10866959 = 16300439) B16300439
theorem B1429791 : Blo 1429534 1429791 := bstep (se 1 (by rfl) ⟨1072343, by rfl⟩ : syracuseStep 1429791 = 2144687) B2144687
theorem B1610023 : Blo 1429534 1610023 := bstep (se 1 (by rfl) ⟨1207517, by rfl⟩ : syracuseStep 1610023 = 2415035) B2415035
theorem B1429851 : Blo 1429534 1429851 := bstep (se 1 (by rfl) ⟨1072388, by rfl⟩ : syracuseStep 1429851 = 2144777) B2144777
theorem B1429871 : Blo 1429534 1429871 := bstep (se 1 (by rfl) ⟨1072403, by rfl⟩ : syracuseStep 1429871 = 2144807) B2144807
theorem B1610095 : Blo 1429534 1610095 := bstep (se 1 (by rfl) ⟨1207571, by rfl⟩ : syracuseStep 1610095 = 2415143) B2415143
theorem B1429927 : Blo 1429534 1429927 := bstep (se 1 (by rfl) ⟨1072445, by rfl⟩ : syracuseStep 1429927 = 2144891) B2144891
theorem B14119343 : Blo 1429534 14119343 := bstep (se 1 (by rfl) ⟨10589507, by rfl⟩ : syracuseStep 14119343 = 21179015) B21179015
theorem B1430011 : Blo 1429534 1430011 := bstep (se 1 (by rfl) ⟨1072508, by rfl⟩ : syracuseStep 1430011 = 2145017) B2145017
theorem B1430079 : Blo 1429534 1430079 := bstep (se 1 (by rfl) ⟨1072559, by rfl⟩ : syracuseStep 1430079 = 2145119) B2145119
theorem B52941377 : Blo 1429534 52941377 := bstep (se 2 (by rfl) ⟨19853016, by rfl⟩ : syracuseStep 52941377 = 39706033) B39706033
theorem B1430087 : Blo 1429534 1430087 := bstep (se 1 (by rfl) ⟨1072565, by rfl⟩ : syracuseStep 1430087 = 2145131) B2145131
theorem B1610311 : Blo 1429534 1610311 := bstep (se 1 (by rfl) ⟨1207733, by rfl⟩ : syracuseStep 1610311 = 2415467) B2415467
theorem B4584089 : Blo 1429534 4584089 := bstep (se 2 (by rfl) ⟨1719033, by rfl⟩ : syracuseStep 4584089 = 3438067) B3438067
theorem B4829867 : Blo 1429534 4829867 := bstep (se 1 (by rfl) ⟨3622400, by rfl⟩ : syracuseStep 4829867 = 7244801) B7244801
theorem B62730929 : Blo 1429534 62730929 := bstep (se 2 (by rfl) ⟨23524098, by rfl⟩ : syracuseStep 62730929 = 47048197) B47048197
theorem B9786055 : Blo 1429534 9786055 := bstep (se 1 (by rfl) ⟨7339541, by rfl⟩ : syracuseStep 9786055 = 14679083) B14679083
theorem B6615751 : Blo 1429534 6615751 := bstep (se 1 (by rfl) ⟨4961813, by rfl⟩ : syracuseStep 6615751 = 9923627) B9923627
theorem B1430239 : Blo 1429534 1430239 := bstep (se 1 (by rfl) ⟨1072679, by rfl⟩ : syracuseStep 1430239 = 2145359) B2145359
theorem B1430319 : Blo 1429534 1430319 := bstep (se 1 (by rfl) ⟨1072739, by rfl⟩ : syracuseStep 1430319 = 2145479) B2145479
theorem B1430427 : Blo 1429534 1430427 := bstep (se 1 (by rfl) ⟨1072820, by rfl⟩ : syracuseStep 1430427 = 2145641) B2145641
theorem B1430479 : Blo 1429534 1430479 := bstep (se 1 (by rfl) ⟨1072859, by rfl⟩ : syracuseStep 1430479 = 2145719) B2145719
theorem B2413543 : Blo 1429534 2413543 := bstep (se 1 (by rfl) ⟨1810157, by rfl⟩ : syracuseStep 2413543 = 3620315) B3620315
theorem B1430503 : Blo 1429534 1430503 := bstep (se 1 (by rfl) ⟨1072877, by rfl⟩ : syracuseStep 1430503 = 2145755) B2145755
theorem B3216527 : Blo 1429534 3216527 := bstep (se 1 (by rfl) ⟨2412395, by rfl⟩ : syracuseStep 3216527 = 4824791) B4824791
theorem B4830407 : Blo 1429534 4830407 := bstep (se 1 (by rfl) ⟨3622805, by rfl⟩ : syracuseStep 4830407 = 7245611) B7245611
theorem B3216617 : Blo 1429534 3216617 := bstep (se 2 (by rfl) ⟨1206231, by rfl⟩ : syracuseStep 3216617 = 2412463) B2412463
theorem B3216671 : Blo 1429534 3216671 := bstep (se 1 (by rfl) ⟨2412503, by rfl⟩ : syracuseStep 3216671 = 4825007) B4825007
theorem B1430815 : Blo 1429534 1430815 := bstep (se 1 (by rfl) ⟨1073111, by rfl⟩ : syracuseStep 1430815 = 2146223) B2146223
theorem B1430875 : Blo 1429534 1430875 := bstep (se 1 (by rfl) ⟨1073156, by rfl⟩ : syracuseStep 1430875 = 2146313) B2146313
theorem B1430895 : Blo 1429534 1430895 := bstep (se 1 (by rfl) ⟨1073171, by rfl⟩ : syracuseStep 1430895 = 2146343) B2146343
theorem B67859873 : Blo 1429534 67859873 := bstep (se 2 (by rfl) ⟨25447452, by rfl⟩ : syracuseStep 67859873 = 50894905) B50894905
theorem B1430951 : Blo 1429534 1430951 := bstep (se 1 (by rfl) ⟨1073213, by rfl⟩ : syracuseStep 1430951 = 2146427) B2146427
theorem B13047277 : Blo 1429534 13047277 := bstep (se 3 (by rfl) ⟨2446364, by rfl⟩ : syracuseStep 13047277 = 4892729) B4892729
theorem B1431035 : Blo 1429534 1431035 := bstep (se 1 (by rfl) ⟨1073276, by rfl⟩ : syracuseStep 1431035 = 2146553) B2146553
theorem B1431103 : Blo 1429534 1431103 := bstep (se 1 (by rfl) ⟨1073327, by rfl⟩ : syracuseStep 1431103 = 2146655) B2146655
theorem B1431111 : Blo 1429534 1431111 := bstep (se 1 (by rfl) ⟨1073333, by rfl⟩ : syracuseStep 1431111 = 2146667) B2146667
theorem B1431263 : Blo 1429534 1431263 := bstep (se 1 (by rfl) ⟨1073447, by rfl⟩ : syracuseStep 1431263 = 2146895) B2146895
theorem B2447111 : Blo 1429534 2447111 := bstep (se 1 (by rfl) ⟨1835333, by rfl⟩ : syracuseStep 2447111 = 3670667) B3670667
theorem B3217193 : Blo 1429534 3217193 := bstep (se 2 (by rfl) ⟨1206447, by rfl⟩ : syracuseStep 3217193 = 2412895) B2412895
theorem B1431343 : Blo 1429534 1431343 := bstep (se 1 (by rfl) ⟨1073507, by rfl⟩ : syracuseStep 1431343 = 2147015) B2147015
theorem B12228407 : Blo 1429534 12228407 := bstep (se 1 (by rfl) ⟨9171305, by rfl⟩ : syracuseStep 12228407 = 18342611) B18342611
theorem B3618665 : Blo 1429534 3618665 := bstep (se 2 (by rfl) ⟨1356999, by rfl⟩ : syracuseStep 3618665 = 2713999) B2713999
theorem B1431451 : Blo 1429534 1431451 := bstep (se 1 (by rfl) ⟨1073588, by rfl⟩ : syracuseStep 1431451 = 2147177) B2147177
theorem B6109111 : Blo 1429534 6109111 := bstep (se 1 (by rfl) ⟨4581833, by rfl⟩ : syracuseStep 6109111 = 9163667) B9163667
theorem B1431503 : Blo 1429534 1431503 := bstep (se 1 (by rfl) ⟨1073627, by rfl⟩ : syracuseStep 1431503 = 2147255) B2147255
theorem B1431527 : Blo 1429534 1431527 := bstep (se 1 (by rfl) ⟨1073645, by rfl⟩ : syracuseStep 1431527 = 2147291) B2147291
theorem B11597903 : Blo 1429534 11597903 := bstep (se 1 (by rfl) ⟨8698427, by rfl⟩ : syracuseStep 11597903 = 17396855) B17396855
theorem B30922883 : Blo 1429534 30922883 := bstep (se 1 (by rfl) ⟨23192162, by rfl⟩ : syracuseStep 30922883 = 46384325) B46384325
theorem B5429501 : Blo 1429534 5429501 := bstep (se 3 (by rfl) ⟨1018031, by rfl⟩ : syracuseStep 5429501 = 2036063) B2036063
theorem B5159177 : Blo 1429534 5159177 := bstep (se 2 (by rfl) ⟨1934691, by rfl⟩ : syracuseStep 5159177 = 3869383) B3869383
theorem B7444759 : Blo 1429534 7444759 := bstep (se 1 (by rfl) ⟨5583569, by rfl⟩ : syracuseStep 7444759 = 11167139) B11167139
theorem B11598157 : Blo 1429534 11598157 := bstep (se 3 (by rfl) ⟨2174654, by rfl⟩ : syracuseStep 11598157 = 4349309) B4349309
theorem B2144603 : Blo 1429534 2144603 := bstep (se 1 (by rfl) ⟨1608452, by rfl⟩ : syracuseStep 2144603 = 3216905) B3216905
theorem B13236605 : Blo 1429534 13236605 := bstep (se 3 (by rfl) ⟨2481863, by rfl⟩ : syracuseStep 13236605 = 4963727) B4963727
theorem B7240103 : Blo 1429534 7240103 := bstep (se 1 (by rfl) ⟨5430077, by rfl⟩ : syracuseStep 7240103 = 10860155) B10860155
theorem B9165307 : Blo 1429534 9165307 := bstep (se 1 (by rfl) ⟨6873980, by rfl⟩ : syracuseStep 9165307 = 13747961) B13747961
theorem B2144831 : Blo 1429534 2144831 := bstep (se 1 (by rfl) ⟨1608623, by rfl⟩ : syracuseStep 2144831 = 3217247) B3217247
theorem B2292295 : Blo 1429534 2292295 := bstep (se 1 (by rfl) ⟨1719221, by rfl⟩ : syracuseStep 2292295 = 3438443) B3438443
theorem B7240265 : Blo 1429534 7240265 := bstep (se 2 (by rfl) ⟨2715099, by rfl⟩ : syracuseStep 7240265 = 5430199) B5430199
theorem B6871675 : Blo 1429534 6871675 := bstep (se 1 (by rfl) ⟨5153756, by rfl⟩ : syracuseStep 6871675 = 10307513) B10307513
theorem B2144951 : Blo 1429534 2144951 := bstep (se 1 (by rfl) ⟨1608713, by rfl⟩ : syracuseStep 2144951 = 3217427) B3217427
theorem B3218255 : Blo 1429534 3218255 := bstep (se 1 (by rfl) ⟨2413691, by rfl⟩ : syracuseStep 3218255 = 4827383) B4827383
theorem B1809307 : Blo 1429534 1809307 := bstep (se 1 (by rfl) ⟨1356980, by rfl⟩ : syracuseStep 1809307 = 2713961) B2713961
theorem B2145179 : Blo 1429534 2145179 := bstep (se 1 (by rfl) ⟨1608884, by rfl⟩ : syracuseStep 2145179 = 3217769) B3217769
theorem B3218471 : Blo 1429534 3218471 := bstep (se 1 (by rfl) ⟨2413853, by rfl⟩ : syracuseStep 3218471 = 4827707) B4827707
theorem B3218651 : Blo 1429534 3218651 := bstep (se 1 (by rfl) ⟨2413988, by rfl⟩ : syracuseStep 3218651 = 4827977) B4827977
theorem B2145575 : Blo 1429534 2145575 := bstep (se 1 (by rfl) ⟨1609181, by rfl⟩ : syracuseStep 2145575 = 3218363) B3218363
theorem B2145659 : Blo 1429534 2145659 := bstep (se 1 (by rfl) ⟨1609244, by rfl⟩ : syracuseStep 2145659 = 3218489) B3218489
theorem B3218849 : Blo 1429534 3218849 := bstep (se 2 (by rfl) ⟨1207068, by rfl⟩ : syracuseStep 3218849 = 2414137) B2414137
theorem B2145785 : Blo 1429534 2145785 := bstep (se 2 (by rfl) ⟨804669, by rfl⟩ : syracuseStep 2145785 = 1609339) B1609339
theorem B15457807 : Blo 1429534 15457807 := bstep (se 1 (by rfl) ⟨11593355, by rfl⟩ : syracuseStep 15457807 = 23186711) B23186711
theorem B3620447 : Blo 1429534 3620447 := bstep (se 1 (by rfl) ⟨2715335, by rfl⟩ : syracuseStep 3620447 = 5430671) B5430671
theorem B2145887 : Blo 1429534 2145887 := bstep (se 1 (by rfl) ⟨1609415, by rfl⟩ : syracuseStep 2145887 = 3218831) B3218831
theorem B4824737 : Blo 1429534 4824737 := bstep (se 2 (by rfl) ⟨1809276, by rfl⟩ : syracuseStep 4824737 = 3618553) B3618553
theorem B4349675 : Blo 1429534 4349675 := bstep (se 1 (by rfl) ⟨3262256, by rfl⟩ : syracuseStep 4349675 = 6524513) B6524513
theorem B4071215 : Blo 1429534 4071215 := bstep (se 1 (by rfl) ⟨3053411, by rfl⟩ : syracuseStep 4071215 = 6106823) B6106823
theorem B2146103 : Blo 1429534 2146103 := bstep (se 1 (by rfl) ⟨1609577, by rfl⟩ : syracuseStep 2146103 = 3219155) B3219155
theorem B16301897 : Blo 1429534 16301897 := bstep (se 2 (by rfl) ⟨6113211, by rfl⟩ : syracuseStep 16301897 = 12226423) B12226423
theorem B27885401 : Blo 1429534 27885401 := bstep (se 2 (by rfl) ⟨10457025, by rfl⟩ : syracuseStep 27885401 = 20914051) B20914051
theorem B3219407 : Blo 1429534 3219407 := bstep (se 1 (by rfl) ⟨2414555, by rfl⟩ : syracuseStep 3219407 = 4829111) B4829111
theorem B4825223 : Blo 1429534 4825223 := bstep (se 1 (by rfl) ⟨3618917, by rfl⟩ : syracuseStep 4825223 = 7237835) B7237835
theorem B2146523 : Blo 1429534 2146523 := bstep (se 1 (by rfl) ⟨1609892, by rfl⟩ : syracuseStep 2146523 = 3219785) B3219785
theorem B3621095 : Blo 1429534 3621095 := bstep (se 1 (by rfl) ⟨2715821, by rfl⟩ : syracuseStep 3621095 = 5431643) B5431643
theorem B2146535 : Blo 1429534 2146535 := bstep (se 1 (by rfl) ⟨1609901, by rfl⟩ : syracuseStep 2146535 = 3219803) B3219803
theorem B9412895 : Blo 1429534 9412895 := bstep (se 1 (by rfl) ⟨7059671, by rfl⟩ : syracuseStep 9412895 = 14119343) B14119343
theorem B4579681 : Blo 1429534 4579681 := bstep (se 2 (by rfl) ⟨1717380, by rfl⟩ : syracuseStep 4579681 = 3434761) B3434761
theorem B2146697 : Blo 1429534 2146697 := bstep (se 2 (by rfl) ⟨805011, by rfl⟩ : syracuseStep 2146697 = 1610023) B1610023
theorem B3621307 : Blo 1429534 3621307 := bstep (se 1 (by rfl) ⟨2715980, by rfl⟩ : syracuseStep 3621307 = 5431961) B5431961
theorem B3056059 : Blo 1429534 3056059 := bstep (se 1 (by rfl) ⟨2292044, by rfl⟩ : syracuseStep 3056059 = 4584089) B4584089
theorem B3219911 : Blo 1429534 3219911 := bstep (se 1 (by rfl) ⟨2414933, by rfl⟩ : syracuseStep 3219911 = 4829867) B4829867
theorem B41820619 : Blo 1429534 41820619 := bstep (se 1 (by rfl) ⟨31365464, by rfl⟩ : syracuseStep 41820619 = 62730929) B62730929
theorem B4129231 : Blo 1429534 4129231 := bstep (se 1 (by rfl) ⟨3096923, by rfl⟩ : syracuseStep 4129231 = 6193847) B6193847
theorem B2146793 : Blo 1429534 2146793 := bstep (se 2 (by rfl) ⟨805047, by rfl⟩ : syracuseStep 2146793 = 1610095) B1610095
theorem B6873673 : Blo 1429534 6873673 := bstep (se 2 (by rfl) ⟨2577627, by rfl⟩ : syracuseStep 6873673 = 5155255) B5155255
theorem B2146919 : Blo 1429534 2146919 := bstep (se 1 (by rfl) ⟨1610189, by rfl⟩ : syracuseStep 2146919 = 3220379) B3220379
theorem B3621611 : Blo 1429534 3621611 := bstep (se 1 (by rfl) ⟨2716208, by rfl⟩ : syracuseStep 3621611 = 5432417) B5432417
theorem B2147051 : Blo 1429534 2147051 := bstep (se 1 (by rfl) ⟨1610288, by rfl⟩ : syracuseStep 2147051 = 3220577) B3220577
theorem B3056393 : Blo 1429534 3056393 := bstep (se 2 (by rfl) ⟨1146147, by rfl⟩ : syracuseStep 3056393 = 2292295) B2292295
theorem B2147081 : Blo 1429534 2147081 := bstep (se 2 (by rfl) ⟨805155, by rfl⟩ : syracuseStep 2147081 = 1610311) B1610311
theorem B18334511 : Blo 1429534 18334511 := bstep (se 1 (by rfl) ⟨13750883, by rfl⟩ : syracuseStep 18334511 = 27501767) B27501767
theorem B3220271 : Blo 1429534 3220271 := bstep (se 1 (by rfl) ⟨2415203, by rfl⟩ : syracuseStep 3220271 = 4830407) B4830407
theorem B3621743 : Blo 1429534 3621743 := bstep (se 1 (by rfl) ⟨2716307, by rfl⟩ : syracuseStep 3621743 = 5432615) B5432615
theorem B2147183 : Blo 1429534 2147183 := bstep (se 1 (by rfl) ⟨1610387, by rfl⟩ : syracuseStep 2147183 = 3220775) B3220775
theorem B7242857 : Blo 1429534 7242857 := bstep (se 2 (by rfl) ⟨2716071, by rfl⟩ : syracuseStep 7242857 = 5432143) B5432143
theorem B3261647 : Blo 1429534 3261647 := bstep (se 1 (by rfl) ⟨2446235, by rfl⟩ : syracuseStep 3261647 = 4892471) B4892471
theorem B8152271 : Blo 1429534 8152271 := bstep (se 1 (by rfl) ⟨6114203, by rfl⟩ : syracuseStep 8152271 = 12228407) B12228407
theorem B7243019 : Blo 1429534 7243019 := bstep (se 1 (by rfl) ⟨5432264, by rfl⟩ : syracuseStep 7243019 = 10864529) B10864529
theorem B8824403 : Blo 1429534 8824403 := bstep (se 1 (by rfl) ⟨6618302, by rfl⟩ : syracuseStep 8824403 = 13236605) B13236605
theorem B4826735 : Blo 1429534 4826735 := bstep (se 1 (by rfl) ⟨3620051, by rfl⟩ : syracuseStep 4826735 = 7240103) B7240103
theorem B4826843 : Blo 1429534 4826843 := bstep (se 1 (by rfl) ⟨3620132, by rfl⟩ : syracuseStep 4826843 = 7240265) B7240265
theorem B17647415 : Blo 1429534 17647415 := bstep (se 1 (by rfl) ⟨13235561, by rfl⟩ : syracuseStep 17647415 = 26471123) B26471123
theorem B19589201 : Blo 1429534 19589201 := bstep (se 2 (by rfl) ⟨7345950, by rfl⟩ : syracuseStep 19589201 = 14691901) B14691901
theorem B2714143 : Blo 1429534 2714143 := bstep (se 1 (by rfl) ⟨2035607, by rfl⟩ : syracuseStep 2714143 = 4071215) B4071215
theorem B18590267 : Blo 1429534 18590267 := bstep (se 1 (by rfl) ⟨13942700, by rfl⟩ : syracuseStep 18590267 = 27885401) B27885401
theorem B8145481 : Blo 1429534 8145481 := bstep (se 2 (by rfl) ⟨3054555, by rfl⟩ : syracuseStep 8145481 = 6109111) B6109111
theorem B3140407 : Blo 1429534 3140407 := bstep (se 1 (by rfl) ⟨2355305, by rfl⟩ : syracuseStep 3140407 = 4710611) B4710611
theorem B7244639 : Blo 1429534 7244639 := bstep (se 1 (by rfl) ⟨5433479, by rfl⟩ : syracuseStep 7244639 = 10866959) B10866959
theorem B4828139 : Blo 1429534 4828139 := bstep (se 1 (by rfl) ⟨3621104, by rfl⟩ : syracuseStep 4828139 = 7242209) B7242209
theorem B4828193 : Blo 1429534 4828193 := bstep (se 2 (by rfl) ⟨1810572, by rfl⟩ : syracuseStep 4828193 = 3621145) B3621145
theorem B35294251 : Blo 1429534 35294251 := bstep (se 1 (by rfl) ⟨26470688, by rfl⟩ : syracuseStep 35294251 = 52941377) B52941377
theorem B9162233 : Blo 1429534 9162233 := bstep (se 2 (by rfl) ⟨3435837, by rfl⟩ : syracuseStep 9162233 = 6871675) B6871675
theorem B45239915 : Blo 1429534 45239915 := bstep (se 1 (by rfl) ⟨33929936, by rfl⟩ : syracuseStep 45239915 = 67859873) B67859873
theorem B52194941 : Blo 1429534 52194941 := bstep (se 3 (by rfl) ⟨9786551, by rfl⟩ : syracuseStep 52194941 = 19573103) B19573103
theorem B41258645 : Blo 1429534 41258645 := bstep (se 6 (by rfl) ⟨966999, by rfl⟩ : syracuseStep 41258645 = 1933999) B1933999
theorem B2412409 : Blo 1429534 2412409 := bstep (se 2 (by rfl) ⟨904653, by rfl⟩ : syracuseStep 2412409 = 1809307) B1809307
theorem B2412443 : Blo 1429534 2412443 := bstep (se 1 (by rfl) ⟨1809332, by rfl⟩ : syracuseStep 2412443 = 3618665) B3618665
theorem B8695775 : Blo 1429534 8695775 := bstep (se 1 (by rfl) ⟨6521831, by rfl⟩ : syracuseStep 8695775 = 13043663) B13043663
theorem B20615255 : Blo 1429534 20615255 := bstep (se 1 (by rfl) ⟨15461441, by rfl⟩ : syracuseStep 20615255 = 30922883) B30922883
theorem B9285761 : Blo 1429534 9285761 := bstep (se 2 (by rfl) ⟨3482160, by rfl⟩ : syracuseStep 9285761 = 6964321) B6964321
theorem B1429735 : Blo 1429534 1429735 := bstep (se 1 (by rfl) ⟨1072301, by rfl⟩ : syracuseStep 1429735 = 2144603) B2144603
theorem B2175263 : Blo 1429534 2175263 := bstep (se 1 (by rfl) ⟨1631447, by rfl⟩ : syracuseStep 2175263 = 3262895) B3262895
theorem B1429887 : Blo 1429534 1429887 := bstep (se 1 (by rfl) ⟨1072415, by rfl⟩ : syracuseStep 1429887 = 2144831) B2144831
theorem B1429967 : Blo 1429534 1429967 := bstep (se 1 (by rfl) ⟨1072475, by rfl⟩ : syracuseStep 1429967 = 2144951) B2144951
theorem B4829651 : Blo 1429534 4829651 := bstep (se 1 (by rfl) ⟨3622238, by rfl⟩ : syracuseStep 4829651 = 7244477) B7244477
theorem B7238159 : Blo 1429534 7238159 := bstep (se 1 (by rfl) ⟨5428619, by rfl⟩ : syracuseStep 7238159 = 10857239) B10857239
theorem B5157391 : Blo 1429534 5157391 := bstep (se 1 (by rfl) ⟨3868043, by rfl⟩ : syracuseStep 5157391 = 7736087) B7736087
theorem B1430119 : Blo 1429534 1430119 := bstep (se 1 (by rfl) ⟨1072589, by rfl⟩ : syracuseStep 1430119 = 2145179) B2145179
theorem B17396369 : Blo 1429534 17396369 := bstep (se 2 (by rfl) ⟨6523638, by rfl⟩ : syracuseStep 17396369 = 13047277) B13047277
theorem B6525629 : Blo 1429534 6525629 := bstep (se 3 (by rfl) ⟨1223555, by rfl⟩ : syracuseStep 6525629 = 2447111) B2447111
theorem B1430383 : Blo 1429534 1430383 := bstep (se 1 (by rfl) ⟨1072787, by rfl⟩ : syracuseStep 1430383 = 2145575) B2145575
theorem B1430439 : Blo 1429534 1430439 := bstep (se 1 (by rfl) ⟨1072829, by rfl⟩ : syracuseStep 1430439 = 2145659) B2145659
theorem B1430523 : Blo 1429534 1430523 := bstep (se 1 (by rfl) ⟨1072892, by rfl⟩ : syracuseStep 1430523 = 2145785) B2145785
theorem B2413631 : Blo 1429534 2413631 := bstep (se 1 (by rfl) ⟨1810223, by rfl⟩ : syracuseStep 2413631 = 3620447) B3620447
theorem B1430591 : Blo 1429534 1430591 := bstep (se 1 (by rfl) ⟨1072943, by rfl⟩ : syracuseStep 1430591 = 2145887) B2145887
theorem B26096741 : Blo 1429534 26096741 := bstep (se 4 (by rfl) ⟨2446569, by rfl⟩ : syracuseStep 26096741 = 4893139) B4893139
theorem B3216491 : Blo 1429534 3216491 := bstep (se 1 (by rfl) ⟨2412368, by rfl⟩ : syracuseStep 3216491 = 4824737) B4824737
theorem B5797003 : Blo 1429534 5797003 := bstep (se 1 (by rfl) ⟨4347752, by rfl⟩ : syracuseStep 5797003 = 8695505) B8695505
theorem B1430735 : Blo 1429534 1430735 := bstep (se 1 (by rfl) ⟨1073051, by rfl⟩ : syracuseStep 1430735 = 2146103) B2146103
theorem B10867931 : Blo 1429534 10867931 := bstep (se 1 (by rfl) ⟨8150948, by rfl⟩ : syracuseStep 10867931 = 16301897) B16301897
theorem B1430939 : Blo 1429534 1430939 := bstep (se 1 (by rfl) ⟨1073204, by rfl⟩ : syracuseStep 1430939 = 2146409) B2146409
theorem B2414191 : Blo 1429534 2414191 := bstep (se 1 (by rfl) ⟨1810643, by rfl⟩ : syracuseStep 2414191 = 3621287) B3621287
theorem B1431151 : Blo 1429534 1431151 := bstep (se 1 (by rfl) ⟨1073363, by rfl⟩ : syracuseStep 1431151 = 2146727) B2146727
theorem B26105489 : Blo 1429534 26105489 := bstep (se 2 (by rfl) ⟨9789558, by rfl⟩ : syracuseStep 26105489 = 19579117) B19579117
theorem B1431207 : Blo 1429534 1431207 := bstep (se 1 (by rfl) ⟨1073405, by rfl⟩ : syracuseStep 1431207 = 2146811) B2146811
theorem B3217067 : Blo 1429534 3217067 := bstep (se 1 (by rfl) ⟨2412800, by rfl⟩ : syracuseStep 3217067 = 4825601) B4825601
theorem B9926345 : Blo 1429534 9926345 := bstep (se 2 (by rfl) ⟨3722379, by rfl⟩ : syracuseStep 9926345 = 7444759) B7444759
theorem B2414299 : Blo 1429534 2414299 := bstep (se 1 (by rfl) ⟨1810724, by rfl⟩ : syracuseStep 2414299 = 3621449) B3621449
theorem B1431291 : Blo 1429534 1431291 := bstep (se 1 (by rfl) ⟨1073468, by rfl⟩ : syracuseStep 1431291 = 2146937) B2146937
theorem B15464209 : Blo 1429534 15464209 := bstep (se 2 (by rfl) ⟨5799078, by rfl⟩ : syracuseStep 15464209 = 11598157) B11598157
theorem B1431327 : Blo 1429534 1431327 := bstep (se 1 (by rfl) ⟨1073495, by rfl⟩ : syracuseStep 1431327 = 2146991) B2146991
theorem B1431359 : Blo 1429534 1431359 := bstep (se 1 (by rfl) ⟨1073519, by rfl⟩ : syracuseStep 1431359 = 2147039) B2147039
theorem B58824629 : Blo 1429534 58824629 := bstep (se 5 (by rfl) ⟨2757404, by rfl⟩ : syracuseStep 58824629 = 5514809) B5514809
theorem B3053531 : Blo 1429534 3053531 := bstep (se 1 (by rfl) ⟨2290148, by rfl⟩ : syracuseStep 3053531 = 4580297) B4580297
theorem B3217391 : Blo 1429534 3217391 := bstep (se 1 (by rfl) ⟨2413043, by rfl⟩ : syracuseStep 3217391 = 4826087) B4826087
theorem B12220409 : Blo 1429534 12220409 := bstep (se 2 (by rfl) ⟨4582653, by rfl⟩ : syracuseStep 12220409 = 9165307) B9165307
theorem B2144351 : Blo 1429534 2144351 := bstep (se 1 (by rfl) ⟨1608263, by rfl⟩ : syracuseStep 2144351 = 3216527) B3216527
theorem B2144411 : Blo 1429534 2144411 := bstep (se 1 (by rfl) ⟨1608308, by rfl⟩ : syracuseStep 2144411 = 3216617) B3216617
theorem B2144447 : Blo 1429534 2144447 := bstep (se 1 (by rfl) ⟨1608335, by rfl⟩ : syracuseStep 2144447 = 3216671) B3216671
theorem B3217607 : Blo 1429534 3217607 := bstep (se 1 (by rfl) ⟨2413205, by rfl⟩ : syracuseStep 3217607 = 4826411) B4826411
theorem B2144489 : Blo 1429534 2144489 := bstep (se 2 (by rfl) ⟨804183, by rfl⟩ : syracuseStep 2144489 = 1608367) B1608367
theorem B8698109 : Blo 1429534 8698109 := bstep (se 3 (by rfl) ⟨1630895, by rfl⟩ : syracuseStep 8698109 = 3261791) B3261791
theorem B13048073 : Blo 1429534 13048073 := bstep (se 2 (by rfl) ⟨4893027, by rfl⟩ : syracuseStep 13048073 = 9786055) B9786055
theorem B8821001 : Blo 1429534 8821001 := bstep (se 2 (by rfl) ⟨3307875, by rfl⟩ : syracuseStep 8821001 = 6615751) B6615751
theorem B8149355 : Blo 1429534 8149355 := bstep (se 1 (by rfl) ⟨6112016, by rfl⟩ : syracuseStep 8149355 = 12224033) B12224033
theorem B3217787 : Blo 1429534 3217787 := bstep (se 1 (by rfl) ⟨2413340, by rfl⟩ : syracuseStep 3217787 = 4826681) B4826681
theorem B2144795 : Blo 1429534 2144795 := bstep (se 1 (by rfl) ⟨1608596, by rfl⟩ : syracuseStep 2144795 = 3217193) B3217193
theorem B2144873 : Blo 1429534 2144873 := bstep (se 2 (by rfl) ⟨804327, by rfl⟩ : syracuseStep 2144873 = 1608655) B1608655
theorem B3218057 : Blo 1429534 3218057 := bstep (se 2 (by rfl) ⟨1206771, by rfl⟩ : syracuseStep 3218057 = 2413543) B2413543
theorem B7731935 : Blo 1429534 7731935 := bstep (se 1 (by rfl) ⟨5798951, by rfl⟩ : syracuseStep 7731935 = 11597903) B11597903
theorem B36649745 : Blo 1429534 36649745 := bstep (se 2 (by rfl) ⟨13743654, by rfl⟩ : syracuseStep 36649745 = 27487309) B27487309
theorem B3619667 : Blo 1429534 3619667 := bstep (se 1 (by rfl) ⟨2714750, by rfl⟩ : syracuseStep 3619667 = 5429501) B5429501
theorem B3439451 : Blo 1429534 3439451 := bstep (se 1 (by rfl) ⟨2579588, by rfl⟩ : syracuseStep 3439451 = 5159177) B5159177
theorem B2415595 : Blo 1429534 2415595 := bstep (se 1 (by rfl) ⟨1811696, by rfl⟩ : syracuseStep 2415595 = 3623393) B3623393
theorem B4643881 : Blo 1429534 4643881 := bstep (se 2 (by rfl) ⟨1741455, by rfl⟩ : syracuseStep 4643881 = 3482911) B3482911
theorem B1809479 : Blo 1429534 1809479 := bstep (se 1 (by rfl) ⟨1357109, by rfl⟩ : syracuseStep 1809479 = 2714219) B2714219
theorem B10869875 : Blo 1429534 10869875 := bstep (se 1 (by rfl) ⟨8152406, by rfl⟩ : syracuseStep 10869875 = 16304813) B16304813
theorem B2145401 : Blo 1429534 2145401 := bstep (se 2 (by rfl) ⟨804525, by rfl⟩ : syracuseStep 2145401 = 1609051) B1609051
theorem B3218615 : Blo 1429534 3218615 := bstep (se 1 (by rfl) ⟨2413961, by rfl⟩ : syracuseStep 3218615 = 4827923) B4827923
theorem B1809631 : Blo 1429534 1809631 := bstep (se 1 (by rfl) ⟨1357223, by rfl⟩ : syracuseStep 1809631 = 2714447) B2714447
theorem B2145503 : Blo 1429534 2145503 := bstep (se 1 (by rfl) ⟨1609127, by rfl⟩ : syracuseStep 2145503 = 3218255) B3218255
theorem B2145545 : Blo 1429534 2145545 := bstep (se 2 (by rfl) ⟨804579, by rfl⟩ : syracuseStep 2145545 = 1609159) B1609159
theorem B20610409 : Blo 1429534 20610409 := bstep (se 2 (by rfl) ⟨7728903, by rfl⟩ : syracuseStep 20610409 = 15457807) B15457807
theorem B2145647 : Blo 1429534 2145647 := bstep (se 1 (by rfl) ⟨1609235, by rfl⟩ : syracuseStep 2145647 = 3218471) B3218471
theorem B2145767 : Blo 1429534 2145767 := bstep (se 1 (by rfl) ⟨1609325, by rfl⟩ : syracuseStep 2145767 = 3218651) B3218651
theorem B2145899 : Blo 1429534 2145899 := bstep (se 1 (by rfl) ⟨1609424, by rfl⟩ : syracuseStep 2145899 = 3218849) B3218849
theorem B4071055 : Blo 1429534 4071055 := bstep (se 1 (by rfl) ⟨3053291, by rfl⟩ : syracuseStep 4071055 = 6106583) B6106583
theorem B2146025 : Blo 1429534 2146025 := bstep (se 2 (by rfl) ⟨804759, by rfl⟩ : syracuseStep 2146025 = 1609519) B1609519
theorem B3219191 : Blo 1429534 3219191 := bstep (se 1 (by rfl) ⟨2414393, by rfl⟩ : syracuseStep 3219191 = 4828787) B4828787
theorem B18341639 : Blo 1429534 18341639 := bstep (se 1 (by rfl) ⟨13756229, by rfl⟩ : syracuseStep 18341639 = 27512459) B27512459
theorem B8150813 : Blo 1429534 8150813 := bstep (se 3 (by rfl) ⟨1528277, by rfl⟩ : syracuseStep 8150813 = 3056555) B3056555
theorem B2899783 : Blo 1429534 2899783 := bstep (se 1 (by rfl) ⟨2174837, by rfl⟩ : syracuseStep 2899783 = 4349675) B4349675
theorem B2146169 : Blo 1429534 2146169 := bstep (se 2 (by rfl) ⟨804813, by rfl⟩ : syracuseStep 2146169 = 1609627) B1609627
theorem B3219371 : Blo 1429534 3219371 := bstep (se 1 (by rfl) ⟨2414528, by rfl⟩ : syracuseStep 3219371 = 4829057) B4829057
theorem B2146271 : Blo 1429534 2146271 := bstep (se 1 (by rfl) ⟨1609703, by rfl⟩ : syracuseStep 2146271 = 3219407) B3219407
theorem B4825277 : Blo 1429534 4825277 := bstep (se 3 (by rfl) ⟨904739, by rfl⟩ : syracuseStep 4825277 = 1809479) B1809479
theorem B1450175 : Blo 1429534 1450175 := bstep (se 1 (by rfl) ⟨1087631, by rfl⟩ : syracuseStep 1450175 = 2175263) B2175263
theorem B2146607 : Blo 1429534 2146607 := bstep (se 1 (by rfl) ⟨1609955, by rfl⟩ : syracuseStep 2146607 = 3219911) B3219911
theorem B3219767 : Blo 1429534 3219767 := bstep (se 1 (by rfl) ⟨2414825, by rfl⟩ : syracuseStep 3219767 = 4829651) B4829651
theorem B4825439 : Blo 1429534 4825439 := bstep (se 1 (by rfl) ⟨3619079, by rfl⟩ : syracuseStep 4825439 = 7238159) B7238159
theorem B4350419 : Blo 1429534 4350419 := bstep (se 1 (by rfl) ⟨3262814, by rfl⟩ : syracuseStep 4350419 = 6525629) B6525629
theorem B12223007 : Blo 1429534 12223007 := bstep (se 1 (by rfl) ⟨9167255, by rfl⟩ : syracuseStep 12223007 = 18334511) B18334511
theorem B2146847 : Blo 1429534 2146847 := bstep (se 1 (by rfl) ⟨1610135, by rfl⟩ : syracuseStep 2146847 = 3220271) B3220271
theorem B5505641 : Blo 1429534 5505641 := bstep (se 2 (by rfl) ⟨2064615, by rfl⟩ : syracuseStep 5505641 = 4129231) B4129231
theorem B25101053 : Blo 1429534 25101053 := bstep (se 3 (by rfl) ⟨4706447, by rfl⟩ : syracuseStep 25101053 = 9412895) B9412895
theorem B4187209 : Blo 1429534 4187209 := bstep (se 2 (by rfl) ⟨1570203, by rfl⟩ : syracuseStep 4187209 = 3140407) B3140407
theorem B11764943 : Blo 1429534 11764943 := bstep (se 1 (by rfl) ⟨8823707, by rfl⟩ : syracuseStep 11764943 = 17647415) B17647415
theorem B39216419 : Blo 1429534 39216419 := bstep (se 1 (by rfl) ⟨29412314, by rfl⟩ : syracuseStep 39216419 = 58824629) B58824629
theorem B3220793 : Blo 1429534 3220793 := bstep (se 2 (by rfl) ⟨1207797, by rfl⟩ : syracuseStep 3220793 = 2415595) B2415595
theorem B13059467 : Blo 1429534 13059467 := bstep (se 1 (by rfl) ⟨9794600, by rfl⟩ : syracuseStep 13059467 = 19589201) B19589201
theorem B5432903 : Blo 1429534 5432903 := bstep (se 1 (by rfl) ⟨4074677, by rfl⟩ : syracuseStep 5432903 = 8149355) B8149355
theorem B5154623 : Blo 1429534 5154623 := bstep (se 1 (by rfl) ⟨3865967, by rfl⟩ : syracuseStep 5154623 = 7731935) B7731935
theorem B26470253 : Blo 1429534 26470253 := bstep (se 3 (by rfl) ⟨4963172, by rfl⟩ : syracuseStep 26470253 = 9926345) B9926345
theorem B5433875 : Blo 1429534 5433875 := bstep (se 1 (by rfl) ⟨4075406, by rfl⟩ : syracuseStep 5433875 = 8150813) B8150813
theorem B1608295 : Blo 1429534 1608295 := bstep (se 1 (by rfl) ⟨1206221, by rfl⟩ : syracuseStep 1608295 = 2412443) B2412443
theorem B24767365 : Blo 1429534 24767365 := bstep (se 4 (by rfl) ⟨2321940, by rfl⟩ : syracuseStep 24767365 = 4643881) B4643881
theorem B6106241 : Blo 1429534 6106241 := bstep (se 2 (by rfl) ⟨2289840, by rfl⟩ : syracuseStep 6106241 = 4579681) B4579681
theorem B4828409 : Blo 1429534 4828409 := bstep (se 2 (by rfl) ⟨1810653, by rfl⟩ : syracuseStep 4828409 = 3621307) B3621307
theorem B23194957 : Blo 1429534 23194957 := bstep (se 3 (by rfl) ⟨4349054, by rfl⟩ : syracuseStep 23194957 = 8698109) B8698109
theorem B6876521 : Blo 1429534 6876521 := bstep (se 2 (by rfl) ⟨2578695, by rfl⟩ : syracuseStep 6876521 = 5157391) B5157391
theorem B1609087 : Blo 1429534 1609087 := bstep (se 1 (by rfl) ⟨1206815, by rfl⟩ : syracuseStep 1609087 = 2413631) B2413631
theorem B4828571 : Blo 1429534 4828571 := bstep (se 1 (by rfl) ⟨3621428, by rfl⟩ : syracuseStep 4828571 = 7242857) B7242857
theorem B2174431 : Blo 1429534 2174431 := bstep (se 1 (by rfl) ⟨1630823, by rfl⟩ : syracuseStep 2174431 = 3261647) B3261647
theorem B5434847 : Blo 1429534 5434847 := bstep (se 1 (by rfl) ⟨4076135, by rfl⟩ : syracuseStep 5434847 = 8152271) B8152271
theorem B7245287 : Blo 1429534 7245287 := bstep (se 1 (by rfl) ⟨5433965, by rfl⟩ : syracuseStep 7245287 = 10867931) B10867931
theorem B4828679 : Blo 1429534 4828679 := bstep (se 1 (by rfl) ⟨3621509, by rfl⟩ : syracuseStep 4828679 = 7243019) B7243019
theorem B17403659 : Blo 1429534 17403659 := bstep (se 1 (by rfl) ⟨13052744, by rfl⟩ : syracuseStep 17403659 = 26105489) B26105489
theorem B2035687 : Blo 1429534 2035687 := bstep (se 1 (by rfl) ⟨1526765, by rfl⟩ : syracuseStep 2035687 = 3053531) B3053531
theorem B8146939 : Blo 1429534 8146939 := bstep (se 1 (by rfl) ⟨6110204, by rfl⟩ : syracuseStep 8146939 = 12220409) B12220409
theorem B47059001 : Blo 1429534 47059001 := bstep (se 2 (by rfl) ⟨17647125, by rfl⟩ : syracuseStep 47059001 = 35294251) B35294251
theorem B1429567 : Blo 1429534 1429567 := bstep (se 1 (by rfl) ⟨1072175, by rfl⟩ : syracuseStep 1429567 = 2144351) B2144351
theorem B1429607 : Blo 1429534 1429607 := bstep (se 1 (by rfl) ⟨1072205, by rfl⟩ : syracuseStep 1429607 = 2144411) B2144411
theorem B1429631 : Blo 1429534 1429631 := bstep (se 1 (by rfl) ⟨1072223, by rfl⟩ : syracuseStep 1429631 = 2144447) B2144447
theorem B1429659 : Blo 1429534 1429659 := bstep (se 1 (by rfl) ⟨1072244, by rfl⟩ : syracuseStep 1429659 = 2144489) B2144489
theorem B49574045 : Blo 1429534 49574045 := bstep (se 3 (by rfl) ⟨9295133, by rfl⟩ : syracuseStep 49574045 = 18590267) B18590267
theorem B7729337 : Blo 1429534 7729337 := bstep (se 2 (by rfl) ⟨2898501, by rfl⟩ : syracuseStep 7729337 = 5797003) B5797003
theorem B23531741 : Blo 1429534 23531741 := bstep (se 3 (by rfl) ⟨4412201, by rfl⟩ : syracuseStep 23531741 = 8824403) B8824403
theorem B120639773 : Blo 1429534 120639773 := bstep (se 3 (by rfl) ⟨22619957, by rfl⟩ : syracuseStep 120639773 = 45239915) B45239915
theorem B2412841 : Blo 1429534 2412841 := bstep (se 2 (by rfl) ⟨904815, by rfl⟩ : syracuseStep 2412841 = 1809631) B1809631
theorem B1429863 : Blo 1429534 1429863 := bstep (se 1 (by rfl) ⟨1072397, by rfl⟩ : syracuseStep 1429863 = 2144795) B2144795
theorem B1429915 : Blo 1429534 1429915 := bstep (se 1 (by rfl) ⟨1072436, by rfl⟩ : syracuseStep 1429915 = 2144873) B2144873
theorem B27480545 : Blo 1429534 27480545 := bstep (se 2 (by rfl) ⟨10305204, by rfl⟩ : syracuseStep 27480545 = 20610409) B20610409
theorem B24433163 : Blo 1429534 24433163 := bstep (se 1 (by rfl) ⟨18324872, by rfl⟩ : syracuseStep 24433163 = 36649745) B36649745
theorem B2413111 : Blo 1429534 2413111 := bstep (se 1 (by rfl) ⟨1809833, by rfl⟩ : syracuseStep 2413111 = 3619667) B3619667
theorem B4829759 : Blo 1429534 4829759 := bstep (se 1 (by rfl) ⟨3622319, by rfl⟩ : syracuseStep 4829759 = 7244639) B7244639
theorem B7246583 : Blo 1429534 7246583 := bstep (se 1 (by rfl) ⟨5434937, by rfl⟩ : syracuseStep 7246583 = 10869875) B10869875
theorem B1430267 : Blo 1429534 1430267 := bstep (se 1 (by rfl) ⟨1072700, by rfl⟩ : syracuseStep 1430267 = 2145401) B2145401
theorem B1430335 : Blo 1429534 1430335 := bstep (se 1 (by rfl) ⟨1072751, by rfl⟩ : syracuseStep 1430335 = 2145503) B2145503
theorem B1430363 : Blo 1429534 1430363 := bstep (se 1 (by rfl) ⟨1072772, by rfl⟩ : syracuseStep 1430363 = 2145545) B2145545
theorem B5428073 : Blo 1429534 5428073 := bstep (se 2 (by rfl) ⟨2035527, by rfl⟩ : syracuseStep 5428073 = 4071055) B4071055
theorem B1430431 : Blo 1429534 1430431 := bstep (se 1 (by rfl) ⟨1072823, by rfl⟩ : syracuseStep 1430431 = 2145647) B2145647
theorem B16298981 : Blo 1429534 16298981 := bstep (se 4 (by rfl) ⟨1528029, by rfl⟩ : syracuseStep 16298981 = 3056059) B3056059
theorem B1430511 : Blo 1429534 1430511 := bstep (se 1 (by rfl) ⟨1072883, by rfl⟩ : syracuseStep 1430511 = 2145767) B2145767
theorem B6108155 : Blo 1429534 6108155 := bstep (se 1 (by rfl) ⟨4581116, by rfl⟩ : syracuseStep 6108155 = 9162233) B9162233
theorem B1430599 : Blo 1429534 1430599 := bstep (se 1 (by rfl) ⟨1072949, by rfl⟩ : syracuseStep 1430599 = 2145899) B2145899
theorem B34796627 : Blo 1429534 34796627 := bstep (se 1 (by rfl) ⟨26097470, by rfl⟩ : syracuseStep 34796627 = 52194941) B52194941
theorem B27505763 : Blo 1429534 27505763 := bstep (se 1 (by rfl) ⟨20629322, by rfl⟩ : syracuseStep 27505763 = 41258645) B41258645
theorem B1430683 : Blo 1429534 1430683 := bstep (se 1 (by rfl) ⟨1073012, by rfl⟩ : syracuseStep 1430683 = 2146025) B2146025
theorem B3216545 : Blo 1429534 3216545 := bstep (se 2 (by rfl) ⟨1206204, by rfl⟩ : syracuseStep 3216545 = 2412409) B2412409
theorem B12227759 : Blo 1429534 12227759 := bstep (se 1 (by rfl) ⟨9170819, by rfl⟩ : syracuseStep 12227759 = 18341639) B18341639
theorem B1430779 : Blo 1429534 1430779 := bstep (se 1 (by rfl) ⟨1073084, by rfl⟩ : syracuseStep 1430779 = 2146169) B2146169
theorem B5797183 : Blo 1429534 5797183 := bstep (se 1 (by rfl) ⟨4347887, by rfl⟩ : syracuseStep 5797183 = 8695775) B8695775
theorem B1430847 : Blo 1429534 1430847 := bstep (se 1 (by rfl) ⟨1073135, by rfl⟩ : syracuseStep 1430847 = 2146271) B2146271
theorem B13743503 : Blo 1429534 13743503 := bstep (se 1 (by rfl) ⟨10307627, by rfl⟩ : syracuseStep 13743503 = 20615255) B20615255
theorem B6190507 : Blo 1429534 6190507 := bstep (se 1 (by rfl) ⟨4642880, by rfl⟩ : syracuseStep 6190507 = 9285761) B9285761
theorem B3216815 : Blo 1429534 3216815 := bstep (se 1 (by rfl) ⟨2412611, by rfl⟩ : syracuseStep 3216815 = 4825223) B4825223
theorem B1431015 : Blo 1429534 1431015 := bstep (se 1 (by rfl) ⟨1073261, by rfl⟩ : syracuseStep 1431015 = 2146523) B2146523
theorem B2414063 : Blo 1429534 2414063 := bstep (se 1 (by rfl) ⟨1810547, by rfl⟩ : syracuseStep 2414063 = 3621095) B3621095
theorem B1431023 : Blo 1429534 1431023 := bstep (se 1 (by rfl) ⟨1073267, by rfl⟩ : syracuseStep 1431023 = 2146535) B2146535
theorem B1431131 : Blo 1429534 1431131 := bstep (se 1 (by rfl) ⟨1073348, by rfl⟩ : syracuseStep 1431131 = 2146697) B2146697
theorem B1431195 : Blo 1429534 1431195 := bstep (se 1 (by rfl) ⟨1073396, by rfl⟩ : syracuseStep 1431195 = 2146793) B2146793
theorem B1431279 : Blo 1429534 1431279 := bstep (se 1 (by rfl) ⟨1073459, by rfl⟩ : syracuseStep 1431279 = 2146919) B2146919
theorem B11597579 : Blo 1429534 11597579 := bstep (se 1 (by rfl) ⟨8698184, by rfl⟩ : syracuseStep 11597579 = 17396369) B17396369
theorem B2414407 : Blo 1429534 2414407 := bstep (se 1 (by rfl) ⟨1810805, by rfl⟩ : syracuseStep 2414407 = 3621611) B3621611
theorem B1431367 : Blo 1429534 1431367 := bstep (se 1 (by rfl) ⟨1073525, by rfl⟩ : syracuseStep 1431367 = 2147051) B2147051
theorem B1431387 : Blo 1429534 1431387 := bstep (se 1 (by rfl) ⟨1073540, by rfl⟩ : syracuseStep 1431387 = 2147081) B2147081
theorem B2414495 : Blo 1429534 2414495 := bstep (se 1 (by rfl) ⟨1810871, by rfl⟩ : syracuseStep 2414495 = 3621743) B3621743
theorem B1431455 : Blo 1429534 1431455 := bstep (se 1 (by rfl) ⟨1073591, by rfl⟩ : syracuseStep 1431455 = 2147183) B2147183
theorem B55760825 : Blo 1429534 55760825 := bstep (se 2 (by rfl) ⟨20910309, by rfl⟩ : syracuseStep 55760825 = 41820619) B41820619
theorem B3618857 : Blo 1429534 3618857 := bstep (se 2 (by rfl) ⟨1357071, by rfl⟩ : syracuseStep 3618857 = 2714143) B2714143
theorem B17397827 : Blo 1429534 17397827 := bstep (se 1 (by rfl) ⟨13048370, by rfl⟩ : syracuseStep 17397827 = 26096741) B26096741
theorem B2144327 : Blo 1429534 2144327 := bstep (se 1 (by rfl) ⟨1608245, by rfl⟩ : syracuseStep 2144327 = 3216491) B3216491
theorem B10860641 : Blo 1429534 10860641 := bstep (se 2 (by rfl) ⟨4072740, by rfl⟩ : syracuseStep 10860641 = 8145481) B8145481
theorem B9164897 : Blo 1429534 9164897 := bstep (se 2 (by rfl) ⟨3436836, by rfl⟩ : syracuseStep 9164897 = 6873673) B6873673
theorem B3217823 : Blo 1429534 3217823 := bstep (se 1 (by rfl) ⟨2413367, by rfl⟩ : syracuseStep 3217823 = 4826735) B4826735
theorem B2144711 : Blo 1429534 2144711 := bstep (se 1 (by rfl) ⟨1608533, by rfl⟩ : syracuseStep 2144711 = 3217067) B3217067
theorem B3217895 : Blo 1429534 3217895 := bstep (se 1 (by rfl) ⟨2413421, by rfl⟩ : syracuseStep 3217895 = 4826843) B4826843
theorem B2144927 : Blo 1429534 2144927 := bstep (se 1 (by rfl) ⟨1608695, by rfl⟩ : syracuseStep 2144927 = 3217391) B3217391
theorem B2145071 : Blo 1429534 2145071 := bstep (se 1 (by rfl) ⟨1608803, by rfl⟩ : syracuseStep 2145071 = 3217607) B3217607
theorem B8698715 : Blo 1429534 8698715 := bstep (se 1 (by rfl) ⟨6524036, by rfl⟩ : syracuseStep 8698715 = 13048073) B13048073
theorem B5880667 : Blo 1429534 5880667 := bstep (se 1 (by rfl) ⟨4410500, by rfl⟩ : syracuseStep 5880667 = 8821001) B8821001
theorem B2145191 : Blo 1429534 2145191 := bstep (se 1 (by rfl) ⟨1608893, by rfl⟩ : syracuseStep 2145191 = 3217787) B3217787
theorem B2145371 : Blo 1429534 2145371 := bstep (se 1 (by rfl) ⟨1609028, by rfl⟩ : syracuseStep 2145371 = 3218057) B3218057
theorem B2292967 : Blo 1429534 2292967 := bstep (se 1 (by rfl) ⟨1719725, by rfl⟩ : syracuseStep 2292967 = 3439451) B3439451
theorem B3218759 : Blo 1429534 3218759 := bstep (se 1 (by rfl) ⟨2414069, by rfl⟩ : syracuseStep 3218759 = 4828139) B4828139
theorem B3218795 : Blo 1429534 3218795 := bstep (se 1 (by rfl) ⟨2414096, by rfl⟩ : syracuseStep 3218795 = 4828193) B4828193
theorem B8150381 : Blo 1429534 8150381 := bstep (se 3 (by rfl) ⟨1528196, by rfl⟩ : syracuseStep 8150381 = 3056393) B3056393
theorem B2145743 : Blo 1429534 2145743 := bstep (se 1 (by rfl) ⟨1609307, by rfl⟩ : syracuseStep 2145743 = 3218615) B3218615
theorem B3218921 : Blo 1429534 3218921 := bstep (se 2 (by rfl) ⟨1207095, by rfl⟩ : syracuseStep 3218921 = 2414191) B2414191
theorem B3219065 : Blo 1429534 3219065 := bstep (se 2 (by rfl) ⟨1207149, by rfl⟩ : syracuseStep 3219065 = 2414299) B2414299
theorem B20618945 : Blo 1429534 20618945 := bstep (se 2 (by rfl) ⟨7732104, by rfl⟩ : syracuseStep 20618945 = 15464209) B15464209
theorem B3866377 : Blo 1429534 3866377 := bstep (se 2 (by rfl) ⟨1449891, by rfl⟩ : syracuseStep 3866377 = 2899783) B2899783
theorem B2146127 : Blo 1429534 2146127 := bstep (se 1 (by rfl) ⟨1609595, by rfl⟩ : syracuseStep 2146127 = 3219191) B3219191
theorem B2146247 : Blo 1429534 2146247 := bstep (se 1 (by rfl) ⟨1609685, by rfl⟩ : syracuseStep 2146247 = 3219371) B3219371
theorem B5152891 : Blo 1429534 5152891 := bstep (se 1 (by rfl) ⟨3864668, by rfl⟩ : syracuseStep 5152891 = 7729337) B7729337
theorem B15687827 : Blo 1429534 15687827 := bstep (se 1 (by rfl) ⟨11765870, by rfl⟩ : syracuseStep 15687827 = 23531741) B23531741
theorem B2146511 : Blo 1429534 2146511 := bstep (se 1 (by rfl) ⟨1609883, by rfl⟩ : syracuseStep 2146511 = 3219767) B3219767
theorem B2900279 : Blo 1429534 2900279 := bstep (se 1 (by rfl) ⟨2175209, by rfl⟩ : syracuseStep 2900279 = 4350419) B4350419
theorem B3219839 : Blo 1429534 3219839 := bstep (se 1 (by rfl) ⟨2414879, by rfl⟩ : syracuseStep 3219839 = 4829759) B4829759
theorem B3670427 : Blo 1429534 3670427 := bstep (se 1 (by rfl) ⟨2752820, by rfl⟩ : syracuseStep 3670427 = 5505641) B5505641
theorem B4072103 : Blo 1429534 4072103 := bstep (se 1 (by rfl) ⟨3054077, by rfl⟩ : syracuseStep 4072103 = 6108155) B6108155
theorem B8151839 : Blo 1429534 8151839 := bstep (se 1 (by rfl) ⟨6113879, by rfl⟩ : syracuseStep 8151839 = 12227759) B12227759
theorem B2147195 : Blo 1429534 2147195 := bstep (se 1 (by rfl) ⟨1610396, by rfl⟩ : syracuseStep 2147195 = 3220793) B3220793
theorem B3621935 : Blo 1429534 3621935 := bstep (se 1 (by rfl) ⟨2716451, by rfl⟩ : syracuseStep 3621935 = 5432903) B5432903
theorem B7840889 : Blo 1429534 7840889 := bstep (se 2 (by rfl) ⟨2940333, by rfl⟩ : syracuseStep 7840889 = 5880667) B5880667
theorem B33023153 : Blo 1429534 33023153 := bstep (se 2 (by rfl) ⟨12383682, by rfl⟩ : syracuseStep 33023153 = 24767365) B24767365
theorem B17646835 : Blo 1429534 17646835 := bstep (se 1 (by rfl) ⟨13235126, by rfl⟩ : syracuseStep 17646835 = 26470253) B26470253
theorem B3622583 : Blo 1429534 3622583 := bstep (se 1 (by rfl) ⟨2716937, by rfl⟩ : syracuseStep 3622583 = 5433875) B5433875
theorem B30926609 : Blo 1429534 30926609 := bstep (se 2 (by rfl) ⟨11597478, by rfl⟩ : syracuseStep 30926609 = 23194957) B23194957
theorem B15468533 : Blo 1429534 15468533 := bstep (se 5 (by rfl) ⟨725087, by rfl⟩ : syracuseStep 15468533 = 1450175) B1450175
theorem B5433587 : Blo 1429534 5433587 := bstep (se 1 (by rfl) ⟨4075190, by rfl⟩ : syracuseStep 5433587 = 8150381) B8150381
theorem B3623231 : Blo 1429534 3623231 := bstep (se 1 (by rfl) ⟨2717423, by rfl⟩ : syracuseStep 3623231 = 5434847) B5434847
theorem B5155169 : Blo 1429534 5155169 := bstep (se 2 (by rfl) ⟨1933188, by rfl⟩ : syracuseStep 5155169 = 3866377) B3866377
theorem B148695533 : Blo 1429534 148695533 := bstep (se 3 (by rfl) ⟨27880412, by rfl⟩ : syracuseStep 148695533 = 55760825) B55760825
theorem B11602439 : Blo 1429534 11602439 := bstep (se 1 (by rfl) ⟨8701829, by rfl⟩ : syracuseStep 11602439 = 17403659) B17403659
theorem B2714249 : Blo 1429534 2714249 := bstep (se 2 (by rfl) ⟨1017843, by rfl⟩ : syracuseStep 2714249 = 2035687) B2035687
theorem B18320363 : Blo 1429534 18320363 := bstep (se 1 (by rfl) ⟨13740272, by rfl⟩ : syracuseStep 18320363 = 27480545) B27480545
theorem B16288775 : Blo 1429534 16288775 := bstep (se 1 (by rfl) ⟨12216581, by rfl⟩ : syracuseStep 16288775 = 24433163) B24433163
theorem B132197453 : Blo 1429534 132197453 := bstep (se 3 (by rfl) ⟨24787022, by rfl⟩ : syracuseStep 132197453 = 49574045) B49574045
theorem B10865987 : Blo 1429534 10865987 := bstep (se 1 (by rfl) ⟨8149490, by rfl⟩ : syracuseStep 10865987 = 16298981) B16298981
theorem B18337175 : Blo 1429534 18337175 := bstep (se 1 (by rfl) ⟨13752881, by rfl⟩ : syracuseStep 18337175 = 27505763) B27505763
theorem B7843295 : Blo 1429534 7843295 := bstep (se 1 (by rfl) ⟨5882471, by rfl⟩ : syracuseStep 7843295 = 11764943) B11764943
theorem B26144279 : Blo 1429534 26144279 := bstep (se 1 (by rfl) ⟨19608209, by rfl⟩ : syracuseStep 26144279 = 39216419) B39216419
theorem B9162335 : Blo 1429534 9162335 := bstep (se 1 (by rfl) ⟨6871751, by rfl⟩ : syracuseStep 9162335 = 13743503) B13743503
theorem B1609375 : Blo 1429534 1609375 := bstep (se 1 (by rfl) ⟨1207031, by rfl⟩ : syracuseStep 1609375 = 2414063) B2414063
theorem B3436415 : Blo 1429534 3436415 := bstep (se 1 (by rfl) ⟨2577311, by rfl⟩ : syracuseStep 3436415 = 5154623) B5154623
theorem B1609663 : Blo 1429534 1609663 := bstep (se 1 (by rfl) ⟨1207247, by rfl⟩ : syracuseStep 1609663 = 2414495) B2414495
theorem B2412571 : Blo 1429534 2412571 := bstep (se 1 (by rfl) ⟨1809428, by rfl⟩ : syracuseStep 2412571 = 3618857) B3618857
theorem B1429551 : Blo 1429534 1429551 := bstep (se 1 (by rfl) ⟨1072163, by rfl⟩ : syracuseStep 1429551 = 2144327) B2144327
theorem B5582945 : Blo 1429534 5582945 := bstep (se 2 (by rfl) ⟨2093604, by rfl⟩ : syracuseStep 5582945 = 4187209) B4187209
theorem B1429807 : Blo 1429534 1429807 := bstep (se 1 (by rfl) ⟨1072355, by rfl⟩ : syracuseStep 1429807 = 2144711) B2144711
theorem B7729577 : Blo 1429534 7729577 := bstep (se 2 (by rfl) ⟨2898591, by rfl⟩ : syracuseStep 7729577 = 5797183) B5797183
theorem B1429951 : Blo 1429534 1429951 := bstep (se 1 (by rfl) ⟨1072463, by rfl⟩ : syracuseStep 1429951 = 2144927) B2144927
theorem B1430047 : Blo 1429534 1430047 := bstep (se 1 (by rfl) ⟨1072535, by rfl⟩ : syracuseStep 1430047 = 2145071) B2145071
theorem B8254009 : Blo 1429534 8254009 := bstep (se 2 (by rfl) ⟨3095253, by rfl⟩ : syracuseStep 8254009 = 6190507) B6190507
theorem B1430127 : Blo 1429534 1430127 := bstep (se 1 (by rfl) ⟨1072595, by rfl⟩ : syracuseStep 1430127 = 2145191) B2145191
theorem B1430247 : Blo 1429534 1430247 := bstep (se 1 (by rfl) ⟨1072685, by rfl⟩ : syracuseStep 1430247 = 2145371) B2145371
theorem B4584347 : Blo 1429534 4584347 := bstep (se 1 (by rfl) ⟨3438260, by rfl⟩ : syracuseStep 4584347 = 6876521) B6876521
theorem B1430495 : Blo 1429534 1430495 := bstep (se 1 (by rfl) ⟨1072871, by rfl⟩ : syracuseStep 1430495 = 2145743) B2145743
theorem B4830191 : Blo 1429534 4830191 := bstep (se 1 (by rfl) ⟨3622643, by rfl⟩ : syracuseStep 4830191 = 7245287) B7245287
theorem B1430751 : Blo 1429534 1430751 := bstep (se 1 (by rfl) ⟨1073063, by rfl⟩ : syracuseStep 1430751 = 2146127) B2146127
theorem B1430831 : Blo 1429534 1430831 := bstep (se 1 (by rfl) ⟨1073123, by rfl⟩ : syracuseStep 1430831 = 2146247) B2146247
theorem B31372667 : Blo 1429534 31372667 := bstep (se 1 (by rfl) ⟨23529500, by rfl⟩ : syracuseStep 31372667 = 47059001) B47059001
theorem B3216851 : Blo 1429534 3216851 := bstep (se 1 (by rfl) ⟨2412638, by rfl⟩ : syracuseStep 3216851 = 4825277) B4825277
theorem B80426515 : Blo 1429534 80426515 := bstep (se 1 (by rfl) ⟨60319886, by rfl⟩ : syracuseStep 80426515 = 120639773) B120639773
theorem B1431071 : Blo 1429534 1431071 := bstep (se 1 (by rfl) ⟨1073303, by rfl⟩ : syracuseStep 1431071 = 2146607) B2146607
theorem B3216959 : Blo 1429534 3216959 := bstep (se 1 (by rfl) ⟨2412719, by rfl⟩ : syracuseStep 3216959 = 4825439) B4825439
theorem B8148671 : Blo 1429534 8148671 := bstep (se 1 (by rfl) ⟨6111503, by rfl⟩ : syracuseStep 8148671 = 12223007) B12223007
theorem B1431231 : Blo 1429534 1431231 := bstep (se 1 (by rfl) ⟨1073423, by rfl⟩ : syracuseStep 1431231 = 2146847) B2146847
theorem B3217121 : Blo 1429534 3217121 := bstep (se 2 (by rfl) ⟨1206420, by rfl⟩ : syracuseStep 3217121 = 2412841) B2412841
theorem B4831055 : Blo 1429534 4831055 := bstep (se 1 (by rfl) ⟨3623291, by rfl⟩ : syracuseStep 4831055 = 7246583) B7246583
theorem B16734035 : Blo 1429534 16734035 := bstep (se 1 (by rfl) ⟨12550526, by rfl⟩ : syracuseStep 16734035 = 25101053) B25101053
theorem B3618715 : Blo 1429534 3618715 := bstep (se 1 (by rfl) ⟨2714036, by rfl⟩ : syracuseStep 3618715 = 5428073) B5428073
theorem B23197751 : Blo 1429534 23197751 := bstep (se 1 (by rfl) ⟨17398313, by rfl⟩ : syracuseStep 23197751 = 34796627) B34796627
theorem B3217481 : Blo 1429534 3217481 := bstep (se 2 (by rfl) ⟨1206555, by rfl⟩ : syracuseStep 3217481 = 2413111) B2413111
theorem B2144363 : Blo 1429534 2144363 := bstep (se 1 (by rfl) ⟨1608272, by rfl⟩ : syracuseStep 2144363 = 3216545) B3216545
theorem B2144393 : Blo 1429534 2144393 := bstep (se 2 (by rfl) ⟨804147, by rfl⟩ : syracuseStep 2144393 = 1608295) B1608295
theorem B8706311 : Blo 1429534 8706311 := bstep (se 1 (by rfl) ⟨6529733, by rfl⟩ : syracuseStep 8706311 = 13059467) B13059467
theorem B2144543 : Blo 1429534 2144543 := bstep (se 1 (by rfl) ⟨1608407, by rfl⟩ : syracuseStep 2144543 = 3216815) B3216815
theorem B7731719 : Blo 1429534 7731719 := bstep (se 1 (by rfl) ⟨5798789, by rfl⟩ : syracuseStep 7731719 = 11597579) B11597579
theorem B12229157 : Blo 1429534 12229157 := bstep (se 4 (by rfl) ⟨1146483, by rfl⟩ : syracuseStep 12229157 = 2292967) B2292967
theorem B11598551 : Blo 1429534 11598551 := bstep (se 1 (by rfl) ⟨8698913, by rfl⟩ : syracuseStep 11598551 = 17397827) B17397827
theorem B7240427 : Blo 1429534 7240427 := bstep (se 1 (by rfl) ⟨5430320, by rfl⟩ : syracuseStep 7240427 = 10860641) B10860641
theorem B6109931 : Blo 1429534 6109931 := bstep (se 1 (by rfl) ⟨4582448, by rfl⟩ : syracuseStep 6109931 = 9164897) B9164897
theorem B2145215 : Blo 1429534 2145215 := bstep (se 1 (by rfl) ⟨1608911, by rfl⟩ : syracuseStep 2145215 = 3217823) B3217823
theorem B2145263 : Blo 1429534 2145263 := bstep (se 1 (by rfl) ⟨1608947, by rfl⟩ : syracuseStep 2145263 = 3217895) B3217895
theorem B2145449 : Blo 1429534 2145449 := bstep (se 2 (by rfl) ⟨804543, by rfl⟩ : syracuseStep 2145449 = 1609087) B1609087
theorem B5799143 : Blo 1429534 5799143 := bstep (se 1 (by rfl) ⟨4349357, by rfl⟩ : syracuseStep 5799143 = 8698715) B8698715
theorem B2899241 : Blo 1429534 2899241 := bstep (se 2 (by rfl) ⟨1087215, by rfl⟩ : syracuseStep 2899241 = 2174431) B2174431
theorem B4070827 : Blo 1429534 4070827 := bstep (se 1 (by rfl) ⟨3053120, by rfl⟩ : syracuseStep 4070827 = 6106241) B6106241
theorem B3218939 : Blo 1429534 3218939 := bstep (se 1 (by rfl) ⟨2414204, by rfl⟩ : syracuseStep 3218939 = 4828409) B4828409
theorem B2145839 : Blo 1429534 2145839 := bstep (se 1 (by rfl) ⟨1609379, by rfl⟩ : syracuseStep 2145839 = 3218759) B3218759
theorem B2145863 : Blo 1429534 2145863 := bstep (se 1 (by rfl) ⟨1609397, by rfl⟩ : syracuseStep 2145863 = 3218795) B3218795
theorem B3219047 : Blo 1429534 3219047 := bstep (se 1 (by rfl) ⟨2414285, by rfl⟩ : syracuseStep 3219047 = 4828571) B4828571
theorem B2145947 : Blo 1429534 2145947 := bstep (se 1 (by rfl) ⟨1609460, by rfl⟩ : syracuseStep 2145947 = 3218921) B3218921
theorem B3219119 : Blo 1429534 3219119 := bstep (se 1 (by rfl) ⟨2414339, by rfl⟩ : syracuseStep 3219119 = 4828679) B4828679
theorem B2146043 : Blo 1429534 2146043 := bstep (se 1 (by rfl) ⟨1609532, by rfl⟩ : syracuseStep 2146043 = 3219065) B3219065
theorem B3219209 : Blo 1429534 3219209 := bstep (se 2 (by rfl) ⟨1207203, by rfl⟩ : syracuseStep 3219209 = 2414407) B2414407
theorem B13745963 : Blo 1429534 13745963 := bstep (se 1 (by rfl) ⟨10309472, by rfl⟩ : syracuseStep 13745963 = 20618945) B20618945
theorem B10862585 : Blo 1429534 10862585 := bstep (se 2 (by rfl) ⟨4073469, by rfl⟩ : syracuseStep 10862585 = 8146939) B8146939
theorem B1933519 : Blo 1429534 1933519 := bstep (se 1 (by rfl) ⟨1450139, by rfl⟩ : syracuseStep 1933519 = 2900279) B2900279
theorem B2146559 : Blo 1429534 2146559 := bstep (se 1 (by rfl) ⟨1609919, by rfl⟩ : syracuseStep 2146559 = 3219839) B3219839
theorem B5153051 : Blo 1429534 5153051 := bstep (se 1 (by rfl) ⟨3864788, by rfl⟩ : syracuseStep 5153051 = 7729577) B7729577
theorem B3056231 : Blo 1429534 3056231 := bstep (se 1 (by rfl) ⟨2292173, by rfl⟩ : syracuseStep 3056231 = 4584347) B4584347
theorem B3220127 : Blo 1429534 3220127 := bstep (se 1 (by rfl) ⟨2415095, by rfl⟩ : syracuseStep 3220127 = 4830191) B4830191
theorem B5227259 : Blo 1429534 5227259 := bstep (se 1 (by rfl) ⟨3920444, by rfl⟩ : syracuseStep 5227259 = 7840889) B7840889
theorem B20915111 : Blo 1429534 20915111 := bstep (se 1 (by rfl) ⟨15686333, by rfl⟩ : syracuseStep 20915111 = 31372667) B31372667
theorem B13747117 : Blo 1429534 13747117 := bstep (se 3 (by rfl) ⟨2577584, by rfl⟩ : syracuseStep 13747117 = 5155169) B5155169
theorem B5432447 : Blo 1429534 5432447 := bstep (se 1 (by rfl) ⟨4074335, by rfl⟩ : syracuseStep 5432447 = 8148671) B8148671
theorem B3220703 : Blo 1429534 3220703 := bstep (se 1 (by rfl) ⟨2415527, by rfl⟩ : syracuseStep 3220703 = 4831055) B4831055
theorem B3622391 : Blo 1429534 3622391 := bstep (se 1 (by rfl) ⟨2716793, by rfl⟩ : syracuseStep 3622391 = 5433587) B5433587
theorem B23529113 : Blo 1429534 23529113 := bstep (se 2 (by rfl) ⟨8823417, by rfl⟩ : syracuseStep 23529113 = 17646835) B17646835
theorem B5154479 : Blo 1429534 5154479 := bstep (se 1 (by rfl) ⟨3865859, by rfl⟩ : syracuseStep 5154479 = 7731719) B7731719
theorem B7734959 : Blo 1429534 7734959 := bstep (se 1 (by rfl) ⟨5801219, by rfl⟩ : syracuseStep 7734959 = 11602439) B11602439
theorem B8152771 : Blo 1429534 8152771 := bstep (se 1 (by rfl) ⟨6114578, by rfl⟩ : syracuseStep 8152771 = 12229157) B12229157
theorem B4826951 : Blo 1429534 4826951 := bstep (se 1 (by rfl) ⟨3620213, by rfl⟩ : syracuseStep 4826951 = 7240427) B7240427
theorem B107235353 : Blo 1429534 107235353 := bstep (se 2 (by rfl) ⟨40213257, by rfl⟩ : syracuseStep 107235353 = 80426515) B80426515
theorem B88131635 : Blo 1429534 88131635 := bstep (se 1 (by rfl) ⟨66098726, by rfl⟩ : syracuseStep 88131635 = 132197453) B132197453
theorem B7243991 : Blo 1429534 7243991 := bstep (se 1 (by rfl) ⟨5432993, by rfl⟩ : syracuseStep 7243991 = 10865987) B10865987
theorem B12224783 : Blo 1429534 12224783 := bstep (se 1 (by rfl) ⟨9168587, by rfl⟩ : syracuseStep 12224783 = 18337175) B18337175
theorem B5228863 : Blo 1429534 5228863 := bstep (se 1 (by rfl) ⟨3921647, by rfl⟩ : syracuseStep 5228863 = 7843295) B7843295
theorem B3721963 : Blo 1429534 3721963 := bstep (se 1 (by rfl) ⟨2791472, by rfl⟩ : syracuseStep 3721963 = 5582945) B5582945
theorem B2714735 : Blo 1429534 2714735 := bstep (se 1 (by rfl) ⟨2036051, by rfl⟩ : syracuseStep 2714735 = 4072103) B4072103
theorem B5434559 : Blo 1429534 5434559 := bstep (se 1 (by rfl) ⟨4075919, by rfl⟩ : syracuseStep 5434559 = 8151839) B8151839
theorem B11005345 : Blo 1429534 11005345 := bstep (se 2 (by rfl) ⟨4127004, by rfl⟩ : syracuseStep 11005345 = 8254009) B8254009
theorem B22015435 : Blo 1429534 22015435 := bstep (se 1 (by rfl) ⟨16511576, by rfl⟩ : syracuseStep 22015435 = 33023153) B33023153
theorem B1429575 : Blo 1429534 1429575 := bstep (se 1 (by rfl) ⟨1072181, by rfl⟩ : syracuseStep 1429575 = 2144363) B2144363
theorem B1429595 : Blo 1429534 1429595 := bstep (se 1 (by rfl) ⟨1072196, by rfl⟩ : syracuseStep 1429595 = 2144393) B2144393
theorem B5804207 : Blo 1429534 5804207 := bstep (se 1 (by rfl) ⟨4353155, by rfl⟩ : syracuseStep 5804207 = 8706311) B8706311
theorem B1429695 : Blo 1429534 1429695 := bstep (se 1 (by rfl) ⟨1072271, by rfl⟩ : syracuseStep 1429695 = 2144543) B2144543
theorem B7237997 : Blo 1429534 7237997 := bstep (se 3 (by rfl) ⟨1357124, by rfl⟩ : syracuseStep 7237997 = 2714249) B2714249
theorem B5427769 : Blo 1429534 5427769 := bstep (se 2 (by rfl) ⟨2035413, by rfl⟩ : syracuseStep 5427769 = 4070827) B4070827
theorem B1430143 : Blo 1429534 1430143 := bstep (se 1 (by rfl) ⟨1072607, by rfl⟩ : syracuseStep 1430143 = 2145215) B2145215
theorem B1430175 : Blo 1429534 1430175 := bstep (se 1 (by rfl) ⟨1072631, by rfl⟩ : syracuseStep 1430175 = 2145263) B2145263
theorem B10859183 : Blo 1429534 10859183 := bstep (se 1 (by rfl) ⟨8144387, by rfl⟩ : syracuseStep 10859183 = 16288775) B16288775
theorem B1430299 : Blo 1429534 1430299 := bstep (se 1 (by rfl) ⟨1072724, by rfl⟩ : syracuseStep 1430299 = 2145449) B2145449
theorem B17429519 : Blo 1429534 17429519 := bstep (se 1 (by rfl) ⟨13072139, by rfl⟩ : syracuseStep 17429519 = 26144279) B26144279
theorem B1430559 : Blo 1429534 1430559 := bstep (se 1 (by rfl) ⟨1072919, by rfl⟩ : syracuseStep 1430559 = 2145839) B2145839
theorem B1430575 : Blo 1429534 1430575 := bstep (se 1 (by rfl) ⟨1072931, by rfl⟩ : syracuseStep 1430575 = 2145863) B2145863
theorem B6108223 : Blo 1429534 6108223 := bstep (se 1 (by rfl) ⟨4581167, by rfl⟩ : syracuseStep 6108223 = 9162335) B9162335
theorem B1430631 : Blo 1429534 1430631 := bstep (se 1 (by rfl) ⟨1072973, by rfl⟩ : syracuseStep 1430631 = 2145947) B2145947
theorem B1430695 : Blo 1429534 1430695 := bstep (se 1 (by rfl) ⟨1073021, by rfl⟩ : syracuseStep 1430695 = 2146043) B2146043
theorem B9163975 : Blo 1429534 9163975 := bstep (se 1 (by rfl) ⟨6872981, by rfl⟩ : syracuseStep 9163975 = 13745963) B13745963
theorem B2290943 : Blo 1429534 2290943 := bstep (se 1 (by rfl) ⟨1718207, by rfl⟩ : syracuseStep 2290943 = 3436415) B3436415
theorem B3216761 : Blo 1429534 3216761 := bstep (se 2 (by rfl) ⟨1206285, by rfl⟩ : syracuseStep 3216761 = 2412571) B2412571
theorem B10458551 : Blo 1429534 10458551 := bstep (se 1 (by rfl) ⟨7843913, by rfl⟩ : syracuseStep 10458551 = 15687827) B15687827
theorem B1431007 : Blo 1429534 1431007 := bstep (se 1 (by rfl) ⟨1073255, by rfl⟩ : syracuseStep 1431007 = 2146511) B2146511
theorem B6870521 : Blo 1429534 6870521 := bstep (se 2 (by rfl) ⟨2576445, by rfl⟩ : syracuseStep 6870521 = 5152891) B5152891
theorem B1431463 : Blo 1429534 1431463 := bstep (se 1 (by rfl) ⟨1073597, by rfl⟩ : syracuseStep 1431463 = 2147195) B2147195
theorem B2414623 : Blo 1429534 2414623 := bstep (se 1 (by rfl) ⟨1810967, by rfl⟩ : syracuseStep 2414623 = 3621935) B3621935
theorem B2144567 : Blo 1429534 2144567 := bstep (se 1 (by rfl) ⟨1608425, by rfl⟩ : syracuseStep 2144567 = 3216851) B3216851
theorem B2144639 : Blo 1429534 2144639 := bstep (se 1 (by rfl) ⟨1608479, by rfl⟩ : syracuseStep 2144639 = 3216959) B3216959
theorem B9787805 : Blo 1429534 9787805 := bstep (se 3 (by rfl) ⟨1835213, by rfl⟩ : syracuseStep 9787805 = 3670427) B3670427
theorem B2415055 : Blo 1429534 2415055 := bstep (se 1 (by rfl) ⟨1811291, by rfl⟩ : syracuseStep 2415055 = 3622583) B3622583
theorem B2144747 : Blo 1429534 2144747 := bstep (se 1 (by rfl) ⟨1608560, by rfl⟩ : syracuseStep 2144747 = 3217121) B3217121
theorem B20617739 : Blo 1429534 20617739 := bstep (se 1 (by rfl) ⟨15463304, by rfl⟩ : syracuseStep 20617739 = 30926609) B30926609
theorem B11156023 : Blo 1429534 11156023 := bstep (se 1 (by rfl) ⟨8367017, by rfl⟩ : syracuseStep 11156023 = 16734035) B16734035
theorem B10312355 : Blo 1429534 10312355 := bstep (se 1 (by rfl) ⟨7734266, by rfl⟩ : syracuseStep 10312355 = 15468533) B15468533
theorem B15465167 : Blo 1429534 15465167 := bstep (se 1 (by rfl) ⟨11598875, by rfl⟩ : syracuseStep 15465167 = 23197751) B23197751
theorem B2144987 : Blo 1429534 2144987 := bstep (se 1 (by rfl) ⟨1608740, by rfl⟩ : syracuseStep 2144987 = 3217481) B3217481
theorem B2415487 : Blo 1429534 2415487 := bstep (se 1 (by rfl) ⟨1811615, by rfl⟩ : syracuseStep 2415487 = 3623231) B3623231
theorem B99130355 : Blo 1429534 99130355 := bstep (se 1 (by rfl) ⟨74347766, by rfl⟩ : syracuseStep 99130355 = 148695533) B148695533
theorem B7732367 : Blo 1429534 7732367 := bstep (se 1 (by rfl) ⟨5799275, by rfl⟩ : syracuseStep 7732367 = 11598551) B11598551
theorem B16293149 : Blo 1429534 16293149 := bstep (se 3 (by rfl) ⟨3054965, by rfl⟩ : syracuseStep 16293149 = 6109931) B6109931
theorem B12213575 : Blo 1429534 12213575 := bstep (se 1 (by rfl) ⟨9160181, by rfl⟩ : syracuseStep 12213575 = 18320363) B18320363
theorem B3866095 : Blo 1429534 3866095 := bstep (se 1 (by rfl) ⟨2899571, by rfl⟩ : syracuseStep 3866095 = 5799143) B5799143
theorem B1932827 : Blo 1429534 1932827 := bstep (se 1 (by rfl) ⟨1449620, by rfl⟩ : syracuseStep 1932827 = 2899241) B2899241
theorem B2145833 : Blo 1429534 2145833 := bstep (se 2 (by rfl) ⟨804687, by rfl⟩ : syracuseStep 2145833 = 1609375) B1609375
theorem B2145959 : Blo 1429534 2145959 := bstep (se 1 (by rfl) ⟨1609469, by rfl⟩ : syracuseStep 2145959 = 3218939) B3218939
theorem B2146031 : Blo 1429534 2146031 := bstep (se 1 (by rfl) ⟨1609523, by rfl⟩ : syracuseStep 2146031 = 3219047) B3219047
theorem B2146079 : Blo 1429534 2146079 := bstep (se 1 (by rfl) ⟨1609559, by rfl⟩ : syracuseStep 2146079 = 3219119) B3219119
theorem B2146139 : Blo 1429534 2146139 := bstep (se 1 (by rfl) ⟨1609604, by rfl⟩ : syracuseStep 2146139 = 3219209) B3219209
theorem B4824953 : Blo 1429534 4824953 := bstep (se 2 (by rfl) ⟨1809357, by rfl⟩ : syracuseStep 4824953 = 3618715) B3618715
theorem B2146217 : Blo 1429534 2146217 := bstep (se 2 (by rfl) ⟨804831, by rfl⟩ : syracuseStep 2146217 = 1609663) B1609663
theorem B7241723 : Blo 1429534 7241723 := bstep (se 1 (by rfl) ⟨5431292, by rfl⟩ : syracuseStep 7241723 = 10862585) B10862585
theorem B3219497 : Blo 1429534 3219497 := bstep (se 2 (by rfl) ⟨1207311, by rfl⟩ : syracuseStep 3219497 = 2414623) B2414623
theorem B4825331 : Blo 1429534 4825331 := bstep (se 1 (by rfl) ⟨3618998, by rfl⟩ : syracuseStep 4825331 = 7237997) B7237997
theorem B2146751 : Blo 1429534 2146751 := bstep (se 1 (by rfl) ⟨1610063, by rfl⟩ : syracuseStep 2146751 = 3220127) B3220127
theorem B3220073 : Blo 1429534 3220073 := bstep (se 2 (by rfl) ⟨1207527, by rfl⟩ : syracuseStep 3220073 = 2415055) B2415055
theorem B13943407 : Blo 1429534 13943407 := bstep (se 1 (by rfl) ⟨10457555, by rfl⟩ : syracuseStep 13943407 = 20915111) B20915111
theorem B3621631 : Blo 1429534 3621631 := bstep (se 1 (by rfl) ⟨2716223, by rfl⟩ : syracuseStep 3621631 = 5432447) B5432447
theorem B2147135 : Blo 1429534 2147135 := bstep (se 1 (by rfl) ⟨1610351, by rfl⟩ : syracuseStep 2147135 = 3220703) B3220703
theorem B6972367 : Blo 1429534 6972367 := bstep (se 1 (by rfl) ⟨5229275, by rfl⟩ : syracuseStep 6972367 = 10458551) B10458551
theorem B3220649 : Blo 1429534 3220649 := bstep (se 2 (by rfl) ⟨1207743, by rfl⟩ : syracuseStep 3220649 = 2415487) B2415487
theorem B58754423 : Blo 1429534 58754423 := bstep (se 1 (by rfl) ⟨44065817, by rfl⟩ : syracuseStep 58754423 = 88131635) B88131635
theorem B5154205 : Blo 1429534 5154205 := bstep (se 3 (by rfl) ⟨966413, by rfl⟩ : syracuseStep 5154205 = 1932827) B1932827
theorem B8144297 : Blo 1429534 8144297 := bstep (se 2 (by rfl) ⟨3054111, by rfl⟩ : syracuseStep 8144297 = 6108223) B6108223
theorem B27887269 : Blo 1429534 27887269 := bstep (se 4 (by rfl) ⟨2614431, by rfl⟩ : syracuseStep 27887269 = 5228863) B5228863
theorem B6874903 : Blo 1429534 6874903 := bstep (se 1 (by rfl) ⟨5156177, by rfl⟩ : syracuseStep 6874903 = 10312355) B10312355
theorem B14673793 : Blo 1429534 14673793 := bstep (se 2 (by rfl) ⟨5502672, by rfl⟩ : syracuseStep 14673793 = 11005345) B11005345
theorem B29353913 : Blo 1429534 29353913 := bstep (se 2 (by rfl) ⟨11007717, by rfl⟩ : syracuseStep 29353913 = 22015435) B22015435
theorem B66086903 : Blo 1429534 66086903 := bstep (se 1 (by rfl) ⟨49565177, by rfl⟩ : syracuseStep 66086903 = 99130355) B99130355
theorem B5154911 : Blo 1429534 5154911 := bstep (se 1 (by rfl) ⟨3866183, by rfl⟩ : syracuseStep 5154911 = 7732367) B7732367
theorem B3623039 : Blo 1429534 3623039 := bstep (se 1 (by rfl) ⟨2717279, by rfl⟩ : syracuseStep 3623039 = 5434559) B5434559
theorem B55757429 : Blo 1429534 55757429 := bstep (se 5 (by rfl) ⟨2613629, by rfl⟩ : syracuseStep 55757429 = 5227259) B5227259
theorem B4827815 : Blo 1429534 4827815 := bstep (se 1 (by rfl) ⟨3620861, by rfl⟩ : syracuseStep 4827815 = 7241723) B7241723
theorem B3869471 : Blo 1429534 3869471 := bstep (se 1 (by rfl) ⟨2902103, by rfl⟩ : syracuseStep 3869471 = 5804207) B5804207
theorem B3435367 : Blo 1429534 3435367 := bstep (se 1 (by rfl) ⟨2576525, by rfl⟩ : syracuseStep 3435367 = 5153051) B5153051
theorem B7237025 : Blo 1429534 7237025 := bstep (se 2 (by rfl) ⟨2713884, by rfl⟩ : syracuseStep 7237025 = 5427769) B5427769
theorem B3436319 : Blo 1429534 3436319 := bstep (se 1 (by rfl) ⟨2577239, by rfl⟩ : syracuseStep 3436319 = 5154479) B5154479
theorem B5156639 : Blo 1429534 5156639 := bstep (se 1 (by rfl) ⟨3867479, by rfl⟩ : syracuseStep 5156639 = 7734959) B7734959
theorem B18329489 : Blo 1429534 18329489 := bstep (se 2 (by rfl) ⟨6873558, by rfl⟩ : syracuseStep 18329489 = 13747117) B13747117
theorem B18321389 : Blo 1429534 18321389 := bstep (se 3 (by rfl) ⟨3435260, by rfl⟩ : syracuseStep 18321389 = 6870521) B6870521
theorem B4829327 : Blo 1429534 4829327 := bstep (se 1 (by rfl) ⟨3621995, by rfl⟩ : syracuseStep 4829327 = 7243991) B7243991
theorem B1429711 : Blo 1429534 1429711 := bstep (se 1 (by rfl) ⟨1072283, by rfl⟩ : syracuseStep 1429711 = 2144567) B2144567
theorem B1429759 : Blo 1429534 1429759 := bstep (se 1 (by rfl) ⟨1072319, by rfl⟩ : syracuseStep 1429759 = 2144639) B2144639
theorem B12218633 : Blo 1429534 12218633 := bstep (se 2 (by rfl) ⟨4581987, by rfl⟩ : syracuseStep 12218633 = 9163975) B9163975
theorem B6525203 : Blo 1429534 6525203 := bstep (se 1 (by rfl) ⟨4893902, by rfl⟩ : syracuseStep 6525203 = 9787805) B9787805
theorem B1429831 : Blo 1429534 1429831 := bstep (se 1 (by rfl) ⟨1072373, by rfl⟩ : syracuseStep 1429831 = 2144747) B2144747
theorem B10310111 : Blo 1429534 10310111 := bstep (se 1 (by rfl) ⟨7732583, by rfl⟩ : syracuseStep 10310111 = 15465167) B15465167
theorem B1429991 : Blo 1429534 1429991 := bstep (se 1 (by rfl) ⟨1072493, by rfl⟩ : syracuseStep 1429991 = 2144987) B2144987
theorem B1430555 : Blo 1429534 1430555 := bstep (se 1 (by rfl) ⟨1072916, by rfl⟩ : syracuseStep 1430555 = 2145833) B2145833
theorem B1430639 : Blo 1429534 1430639 := bstep (se 1 (by rfl) ⟨1072979, by rfl⟩ : syracuseStep 1430639 = 2145959) B2145959
theorem B1430687 : Blo 1429534 1430687 := bstep (se 1 (by rfl) ⟨1073015, by rfl⟩ : syracuseStep 1430687 = 2146031) B2146031
theorem B1430719 : Blo 1429534 1430719 := bstep (se 1 (by rfl) ⟨1073039, by rfl⟩ : syracuseStep 1430719 = 2146079) B2146079
theorem B1430759 : Blo 1429534 1430759 := bstep (se 1 (by rfl) ⟨1073069, by rfl⟩ : syracuseStep 1430759 = 2146139) B2146139
theorem B3216635 : Blo 1429534 3216635 := bstep (se 1 (by rfl) ⟨2412476, by rfl⟩ : syracuseStep 3216635 = 4824953) B4824953
theorem B1430811 : Blo 1429534 1430811 := bstep (se 1 (by rfl) ⟨1073108, by rfl⟩ : syracuseStep 1430811 = 2146217) B2146217
theorem B46478717 : Blo 1429534 46478717 := bstep (se 3 (by rfl) ⟨8714759, by rfl⟩ : syracuseStep 46478717 = 17429519) B17429519
theorem B1431039 : Blo 1429534 1431039 := bstep (se 1 (by rfl) ⟨1073279, by rfl⟩ : syracuseStep 1431039 = 2146559) B2146559
theorem B2578025 : Blo 1429534 2578025 := bstep (se 2 (by rfl) ⟨966759, by rfl⟩ : syracuseStep 2578025 = 1933519) B1933519
theorem B7239293 : Blo 1429534 7239293 := bstep (se 3 (by rfl) ⟨1357367, by rfl⟩ : syracuseStep 7239293 = 2714735) B2714735
theorem B2037487 : Blo 1429534 2037487 := bstep (se 1 (by rfl) ⟨1528115, by rfl⟩ : syracuseStep 2037487 = 3056231) B3056231
theorem B7239455 : Blo 1429534 7239455 := bstep (se 1 (by rfl) ⟨5429591, by rfl⟩ : syracuseStep 7239455 = 10859183) B10859183
theorem B6109181 : Blo 1429534 6109181 := bstep (se 3 (by rfl) ⟨1145471, by rfl⟩ : syracuseStep 6109181 = 2290943) B2290943
theorem B14874697 : Blo 1429534 14874697 := bstep (se 2 (by rfl) ⟨5578011, by rfl⟩ : syracuseStep 14874697 = 11156023) B11156023
theorem B2144507 : Blo 1429534 2144507 := bstep (se 1 (by rfl) ⟨1608380, by rfl⟩ : syracuseStep 2144507 = 3216761) B3216761
theorem B4962617 : Blo 1429534 4962617 := bstep (se 2 (by rfl) ⟨1860981, by rfl⟩ : syracuseStep 4962617 = 3721963) B3721963
theorem B2414927 : Blo 1429534 2414927 := bstep (se 1 (by rfl) ⟨1811195, by rfl⟩ : syracuseStep 2414927 = 3622391) B3622391
theorem B15686075 : Blo 1429534 15686075 := bstep (se 1 (by rfl) ⟨11764556, by rfl⟩ : syracuseStep 15686075 = 23529113) B23529113
theorem B3217967 : Blo 1429534 3217967 := bstep (se 1 (by rfl) ⟨2413475, by rfl⟩ : syracuseStep 3217967 = 4826951) B4826951
theorem B71490235 : Blo 1429534 71490235 := bstep (se 1 (by rfl) ⟨53617676, by rfl⟩ : syracuseStep 71490235 = 107235353) B107235353
theorem B8149855 : Blo 1429534 8149855 := bstep (se 1 (by rfl) ⟨6112391, by rfl⟩ : syracuseStep 8149855 = 12224783) B12224783
theorem B13745159 : Blo 1429534 13745159 := bstep (se 1 (by rfl) ⟨10308869, by rfl⟩ : syracuseStep 13745159 = 20617739) B20617739
theorem B10862099 : Blo 1429534 10862099 := bstep (se 1 (by rfl) ⟨8146574, by rfl⟩ : syracuseStep 10862099 = 16293149) B16293149
theorem B8142383 : Blo 1429534 8142383 := bstep (se 1 (by rfl) ⟨6106787, by rfl⟩ : syracuseStep 8142383 = 12213575) B12213575
theorem B10870361 : Blo 1429534 10870361 := bstep (se 2 (by rfl) ⟨4076385, by rfl⟩ : syracuseStep 10870361 = 8152771) B8152771
theorem B20619173 : Blo 1429534 20619173 := bstep (se 4 (by rfl) ⟨1933047, by rfl⟩ : syracuseStep 20619173 = 3866095) B3866095
theorem B2146331 : Blo 1429534 2146331 := bstep (se 1 (by rfl) ⟨1609748, by rfl⟩ : syracuseStep 2146331 = 3219497) B3219497
theorem B3219551 : Blo 1429534 3219551 := bstep (se 1 (by rfl) ⟨2414663, by rfl⟩ : syracuseStep 3219551 = 4829327) B4829327
theorem B6873407 : Blo 1429534 6873407 := bstep (se 1 (by rfl) ⟨5155055, by rfl⟩ : syracuseStep 6873407 = 10310111) B10310111
theorem B79331717 : Blo 1429534 79331717 := bstep (se 4 (by rfl) ⟨7437348, by rfl⟩ : syracuseStep 79331717 = 14874697) B14874697
theorem B2146715 : Blo 1429534 2146715 := bstep (se 1 (by rfl) ⟨1610036, by rfl⟩ : syracuseStep 2146715 = 3220073) B3220073
theorem B2147099 : Blo 1429534 2147099 := bstep (se 1 (by rfl) ⟨1610324, by rfl⟩ : syracuseStep 2147099 = 3220649) B3220649
theorem B4826195 : Blo 1429534 4826195 := bstep (se 1 (by rfl) ⟨3619646, by rfl⟩ : syracuseStep 4826195 = 7239293) B7239293
theorem B4580489 : Blo 1429534 4580489 := bstep (se 2 (by rfl) ⟨1717683, by rfl⟩ : syracuseStep 4580489 = 3435367) B3435367
theorem B41829533 : Blo 1429534 41829533 := bstep (se 3 (by rfl) ⟨7843037, by rfl⟩ : syracuseStep 41829533 = 15686075) B15686075
theorem B4826303 : Blo 1429534 4826303 := bstep (se 1 (by rfl) ⟨3619727, by rfl⟩ : syracuseStep 4826303 = 7239455) B7239455
theorem B44057935 : Blo 1429534 44057935 := bstep (se 1 (by rfl) ⟨33043451, by rfl⟩ : syracuseStep 44057935 = 66086903) B66086903
theorem B4072787 : Blo 1429534 4072787 := bstep (se 1 (by rfl) ⟨3054590, by rfl⟩ : syracuseStep 4072787 = 6109181) B6109181
theorem B6874733 : Blo 1429534 6874733 := bstep (se 3 (by rfl) ⟨1289012, by rfl⟩ : syracuseStep 6874733 = 2578025) B2578025
theorem B19565057 : Blo 1429534 19565057 := bstep (se 2 (by rfl) ⟨7336896, by rfl⟩ : syracuseStep 19565057 = 14673793) B14673793
theorem B8145755 : Blo 1429534 8145755 := bstep (se 1 (by rfl) ⟨6109316, by rfl⟩ : syracuseStep 8145755 = 12218633) B12218633
theorem B69602165 : Blo 1429534 69602165 := bstep (se 5 (by rfl) ⟨3262601, by rfl⟩ : syracuseStep 69602165 = 6525203) B6525203
theorem B18591209 : Blo 1429534 18591209 := bstep (se 2 (by rfl) ⟨6971703, by rfl⟩ : syracuseStep 18591209 = 13943407) B13943407
theorem B39169615 : Blo 1429534 39169615 := bstep (se 1 (by rfl) ⟨29377211, by rfl⟩ : syracuseStep 39169615 = 58754423) B58754423
theorem B30985811 : Blo 1429534 30985811 := bstep (se 1 (by rfl) ⟨23239358, by rfl⟩ : syracuseStep 30985811 = 46478717) B46478717
theorem B4828841 : Blo 1429534 4828841 := bstep (se 2 (by rfl) ⟨1810815, by rfl⟩ : syracuseStep 4828841 = 3621631) B3621631
theorem B10866473 : Blo 1429534 10866473 := bstep (se 2 (by rfl) ⟨4074927, by rfl⟩ : syracuseStep 10866473 = 8149855) B8149855
theorem B3436607 : Blo 1429534 3436607 := bstep (se 1 (by rfl) ⟨2577455, by rfl⟩ : syracuseStep 3436607 = 5154911) B5154911
theorem B1429671 : Blo 1429534 1429671 := bstep (se 1 (by rfl) ⟨1072253, by rfl⟩ : syracuseStep 1429671 = 2144507) B2144507
theorem B1609951 : Blo 1429534 1609951 := bstep (se 1 (by rfl) ⟨1207463, by rfl⟩ : syracuseStep 1609951 = 2414927) B2414927
theorem B37171619 : Blo 1429534 37171619 := bstep (se 1 (by rfl) ⟨27878714, by rfl⟩ : syracuseStep 37171619 = 55757429) B55757429
theorem B9163439 : Blo 1429534 9163439 := bstep (se 1 (by rfl) ⟨6872579, by rfl⟩ : syracuseStep 9163439 = 13745159) B13745159
theorem B2716649 : Blo 1429534 2716649 := bstep (se 2 (by rfl) ⟨1018743, by rfl⟩ : syracuseStep 2716649 = 2037487) B2037487
theorem B5428255 : Blo 1429534 5428255 := bstep (se 1 (by rfl) ⟨4071191, by rfl⟩ : syracuseStep 5428255 = 8142383) B8142383
theorem B7246907 : Blo 1429534 7246907 := bstep (se 1 (by rfl) ⟨5435180, by rfl⟩ : syracuseStep 7246907 = 10870361) B10870361
theorem B2290879 : Blo 1429534 2290879 := bstep (se 1 (by rfl) ⟨1718159, by rfl⟩ : syracuseStep 2290879 = 3436319) B3436319
theorem B3437759 : Blo 1429534 3437759 := bstep (se 1 (by rfl) ⟨2578319, by rfl⟩ : syracuseStep 3437759 = 5156639) B5156639
theorem B12219659 : Blo 1429534 12219659 := bstep (se 1 (by rfl) ⟨9164744, by rfl⟩ : syracuseStep 12219659 = 18329489) B18329489
theorem B3216887 : Blo 1429534 3216887 := bstep (se 1 (by rfl) ⟨2412665, by rfl⟩ : syracuseStep 3216887 = 4825331) B4825331
theorem B1431167 : Blo 1429534 1431167 := bstep (se 1 (by rfl) ⟨1073375, by rfl⟩ : syracuseStep 1431167 = 2146751) B2146751
theorem B1431423 : Blo 1429534 1431423 := bstep (se 1 (by rfl) ⟨1073567, by rfl⟩ : syracuseStep 1431423 = 2147135) B2147135
theorem B2144423 : Blo 1429534 2144423 := bstep (se 1 (by rfl) ⟨1608317, by rfl⟩ : syracuseStep 2144423 = 3216635) B3216635
theorem B95320313 : Blo 1429534 95320313 := bstep (se 2 (by rfl) ⟨35745117, by rfl⟩ : syracuseStep 95320313 = 71490235) B71490235
theorem B5429531 : Blo 1429534 5429531 := bstep (se 1 (by rfl) ⟨4072148, by rfl⟩ : syracuseStep 5429531 = 8144297) B8144297
theorem B9296489 : Blo 1429534 9296489 := bstep (se 2 (by rfl) ⟨3486183, by rfl⟩ : syracuseStep 9296489 = 6972367) B6972367
theorem B19569275 : Blo 1429534 19569275 := bstep (se 1 (by rfl) ⟨14676956, by rfl⟩ : syracuseStep 19569275 = 29353913) B29353913
theorem B2415359 : Blo 1429534 2415359 := bstep (se 1 (by rfl) ⟨1811519, by rfl⟩ : syracuseStep 2415359 = 3623039) B3623039
theorem B3308411 : Blo 1429534 3308411 := bstep (se 1 (by rfl) ⟨2481308, by rfl⟩ : syracuseStep 3308411 = 4962617) B4962617
theorem B2145311 : Blo 1429534 2145311 := bstep (se 1 (by rfl) ⟨1608983, by rfl⟩ : syracuseStep 2145311 = 3217967) B3217967
theorem B3218543 : Blo 1429534 3218543 := bstep (se 1 (by rfl) ⟨2413907, by rfl⟩ : syracuseStep 3218543 = 4827815) B4827815
theorem B2579647 : Blo 1429534 2579647 := bstep (se 1 (by rfl) ⟨1934735, by rfl⟩ : syracuseStep 2579647 = 3869471) B3869471
theorem B6872273 : Blo 1429534 6872273 := bstep (se 2 (by rfl) ⟨2577102, by rfl⟩ : syracuseStep 6872273 = 5154205) B5154205
theorem B37183025 : Blo 1429534 37183025 := bstep (se 2 (by rfl) ⟨13943634, by rfl⟩ : syracuseStep 37183025 = 27887269) B27887269
theorem B4824683 : Blo 1429534 4824683 := bstep (se 1 (by rfl) ⟨3618512, by rfl⟩ : syracuseStep 4824683 = 7237025) B7237025
theorem B7241399 : Blo 1429534 7241399 := bstep (se 1 (by rfl) ⟨5431049, by rfl⟩ : syracuseStep 7241399 = 10862099) B10862099
theorem B9166537 : Blo 1429534 9166537 := bstep (se 2 (by rfl) ⟨3437451, by rfl⟩ : syracuseStep 9166537 = 6874903) B6874903
theorem B13746115 : Blo 1429534 13746115 := bstep (se 1 (by rfl) ⟨10309586, by rfl⟩ : syracuseStep 13746115 = 20619173) B20619173
theorem B12214259 : Blo 1429534 12214259 := bstep (se 1 (by rfl) ⟨9160694, by rfl⟩ : syracuseStep 12214259 = 18321389) B18321389
theorem B2146367 : Blo 1429534 2146367 := bstep (se 1 (by rfl) ⟨1609775, by rfl⟩ : syracuseStep 2146367 = 3219551) B3219551
theorem B52887811 : Blo 1429534 52887811 := bstep (se 1 (by rfl) ⟨39665858, by rfl⟩ : syracuseStep 52887811 = 79331717) B79331717
theorem B24781079 : Blo 1429534 24781079 := bstep (se 1 (by rfl) ⟨18585809, by rfl⟩ : syracuseStep 24781079 = 37171619) B37171619
theorem B2146601 : Blo 1429534 2146601 := bstep (se 2 (by rfl) ⟨804975, by rfl⟩ : syracuseStep 2146601 = 1609951) B1609951
theorem B12214637 : Blo 1429534 12214637 := bstep (se 3 (by rfl) ⟨2290244, by rfl⟩ : syracuseStep 12214637 = 4580489) B4580489
theorem B9167357 : Blo 1429534 9167357 := bstep (se 3 (by rfl) ⟨1718879, by rfl⟩ : syracuseStep 9167357 = 3437759) B3437759
theorem B1811099 : Blo 1429534 1811099 := bstep (se 1 (by rfl) ⟨1358324, by rfl⟩ : syracuseStep 1811099 = 2716649) B2716649
theorem B27886355 : Blo 1429534 27886355 := bstep (se 1 (by rfl) ⟨20914766, by rfl⟩ : syracuseStep 27886355 = 41829533) B41829533
theorem B63546875 : Blo 1429534 63546875 := bstep (se 1 (by rfl) ⟨47660156, by rfl⟩ : syracuseStep 63546875 = 95320313) B95320313
theorem B24790637 : Blo 1429534 24790637 := bstep (se 3 (by rfl) ⟨4648244, by rfl⟩ : syracuseStep 24790637 = 9296489) B9296489
theorem B13043371 : Blo 1429534 13043371 := bstep (se 1 (by rfl) ⟨9782528, by rfl⟩ : syracuseStep 13043371 = 19565057) B19565057
theorem B46401443 : Blo 1429534 46401443 := bstep (se 1 (by rfl) ⟨34801082, by rfl⟩ : syracuseStep 46401443 = 69602165) B69602165
theorem B2205607 : Blo 1429534 2205607 := bstep (se 1 (by rfl) ⟨1654205, by rfl⟩ : syracuseStep 2205607 = 3308411) B3308411
theorem B52226153 : Blo 1429534 52226153 := bstep (se 2 (by rfl) ⟨19584807, by rfl⟩ : syracuseStep 52226153 = 39169615) B39169615
theorem B4581515 : Blo 1429534 4581515 := bstep (se 1 (by rfl) ⟨3436136, by rfl⟩ : syracuseStep 4581515 = 6872273) B6872273
theorem B4827599 : Blo 1429534 4827599 := bstep (se 1 (by rfl) ⟨3620699, by rfl⟩ : syracuseStep 4827599 = 7241399) B7241399
theorem B7244315 : Blo 1429534 7244315 := bstep (se 1 (by rfl) ⟨5433236, by rfl⟩ : syracuseStep 7244315 = 10866473) B10866473
theorem B18328153 : Blo 1429534 18328153 := bstep (se 2 (by rfl) ⟨6873057, by rfl⟩ : syracuseStep 18328153 = 13746115) B13746115
theorem B4582271 : Blo 1429534 4582271 := bstep (se 1 (by rfl) ⟨3436703, by rfl⟩ : syracuseStep 4582271 = 6873407) B6873407
theorem B8146439 : Blo 1429534 8146439 := bstep (se 1 (by rfl) ⟨6109829, by rfl⟩ : syracuseStep 8146439 = 12219659) B12219659
theorem B2715191 : Blo 1429534 2715191 := bstep (se 1 (by rfl) ⟨2036393, by rfl⟩ : syracuseStep 2715191 = 4072787) B4072787
theorem B4583155 : Blo 1429534 4583155 := bstep (se 1 (by rfl) ⟨3437366, by rfl⟩ : syracuseStep 4583155 = 6874733) B6874733
theorem B7237673 : Blo 1429534 7237673 := bstep (se 2 (by rfl) ⟨2714127, by rfl⟩ : syracuseStep 7237673 = 5428255) B5428255
theorem B1429615 : Blo 1429534 1429615 := bstep (se 1 (by rfl) ⟨1072211, by rfl⟩ : syracuseStep 1429615 = 2144423) B2144423
theorem B234975653 : Blo 1429534 234975653 := bstep (se 4 (by rfl) ⟨22028967, by rfl⟩ : syracuseStep 234975653 = 44057935) B44057935
theorem B13046183 : Blo 1429534 13046183 := bstep (se 1 (by rfl) ⟨9784637, by rfl⟩ : syracuseStep 13046183 = 19569275) B19569275
theorem B1610239 : Blo 1429534 1610239 := bstep (se 1 (by rfl) ⟨1207679, by rfl⟩ : syracuseStep 1610239 = 2415359) B2415359
theorem B1430207 : Blo 1429534 1430207 := bstep (se 1 (by rfl) ⟨1072655, by rfl⟩ : syracuseStep 1430207 = 2145311) B2145311
theorem B20657207 : Blo 1429534 20657207 := bstep (se 1 (by rfl) ⟨15492905, by rfl⟩ : syracuseStep 20657207 = 30985811) B30985811
theorem B3216455 : Blo 1429534 3216455 := bstep (se 1 (by rfl) ⟨2412341, by rfl⟩ : syracuseStep 3216455 = 4824683) B4824683
theorem B1430887 : Blo 1429534 1430887 := bstep (se 1 (by rfl) ⟨1073165, by rfl⟩ : syracuseStep 1430887 = 2146331) B2146331
theorem B2291071 : Blo 1429534 2291071 := bstep (se 1 (by rfl) ⟨1718303, by rfl⟩ : syracuseStep 2291071 = 3436607) B3436607
theorem B1431143 : Blo 1429534 1431143 := bstep (se 1 (by rfl) ⟨1073357, by rfl⟩ : syracuseStep 1431143 = 2146715) B2146715
theorem B6108959 : Blo 1429534 6108959 := bstep (se 1 (by rfl) ⟨4581719, by rfl⟩ : syracuseStep 6108959 = 9163439) B9163439
theorem B1431399 : Blo 1429534 1431399 := bstep (se 1 (by rfl) ⟨1073549, by rfl⟩ : syracuseStep 1431399 = 2147099) B2147099
theorem B4831271 : Blo 1429534 4831271 := bstep (se 1 (by rfl) ⟨3623453, by rfl⟩ : syracuseStep 4831271 = 7246907) B7246907
theorem B3217463 : Blo 1429534 3217463 := bstep (se 1 (by rfl) ⟨2413097, by rfl⟩ : syracuseStep 3217463 = 4826195) B4826195
theorem B3217535 : Blo 1429534 3217535 := bstep (se 1 (by rfl) ⟨2413151, by rfl⟩ : syracuseStep 3217535 = 4826303) B4826303
theorem B2144591 : Blo 1429534 2144591 := bstep (se 1 (by rfl) ⟨1608443, by rfl⟩ : syracuseStep 2144591 = 3216887) B3216887
theorem B3619687 : Blo 1429534 3619687 := bstep (se 1 (by rfl) ⟨2714765, by rfl⟩ : syracuseStep 3619687 = 5429531) B5429531
theorem B3054505 : Blo 1429534 3054505 := bstep (se 2 (by rfl) ⟨1145439, by rfl⟩ : syracuseStep 3054505 = 2290879) B2290879
theorem B3439529 : Blo 1429534 3439529 := bstep (se 2 (by rfl) ⟨1289823, by rfl⟩ : syracuseStep 3439529 = 2579647) B2579647
theorem B5430503 : Blo 1429534 5430503 := bstep (se 1 (by rfl) ⟨4072877, by rfl⟩ : syracuseStep 5430503 = 8145755) B8145755
theorem B2145695 : Blo 1429534 2145695 := bstep (se 1 (by rfl) ⟨1609271, by rfl⟩ : syracuseStep 2145695 = 3218543) B3218543
theorem B12222049 : Blo 1429534 12222049 := bstep (se 2 (by rfl) ⟨4583268, by rfl⟩ : syracuseStep 12222049 = 9166537) B9166537
theorem B12394139 : Blo 1429534 12394139 := bstep (se 1 (by rfl) ⟨9295604, by rfl⟩ : syracuseStep 12394139 = 18591209) B18591209
theorem B24788683 : Blo 1429534 24788683 := bstep (se 1 (by rfl) ⟨18591512, by rfl⟩ : syracuseStep 24788683 = 37183025) B37183025
theorem B3219227 : Blo 1429534 3219227 := bstep (se 1 (by rfl) ⟨2414420, by rfl⟩ : syracuseStep 3219227 = 4828841) B4828841
theorem B8142839 : Blo 1429534 8142839 := bstep (se 1 (by rfl) ⟨6107129, by rfl⟩ : syracuseStep 8142839 = 12214259) B12214259
theorem B4825115 : Blo 1429534 4825115 := bstep (se 1 (by rfl) ⟨3618836, by rfl⟩ : syracuseStep 4825115 = 7237673) B7237673
theorem B8143091 : Blo 1429534 8143091 := bstep (se 1 (by rfl) ⟨6107318, by rfl⟩ : syracuseStep 8143091 = 12214637) B12214637
theorem B70517081 : Blo 1429534 70517081 := bstep (se 2 (by rfl) ⟨26443905, by rfl⟩ : syracuseStep 70517081 = 52887811) B52887811
theorem B2146985 : Blo 1429534 2146985 := bstep (se 2 (by rfl) ⟨805119, by rfl⟩ : syracuseStep 2146985 = 1610239) B1610239
theorem B13771471 : Blo 1429534 13771471 := bstep (se 1 (by rfl) ⟨10328603, by rfl⟩ : syracuseStep 13771471 = 20657207) B20657207
theorem B24437537 : Blo 1429534 24437537 := bstep (se 2 (by rfl) ⟨9164076, by rfl⟩ : syracuseStep 24437537 = 18328153) B18328153
theorem B4826249 : Blo 1429534 4826249 := bstep (se 2 (by rfl) ⟨1809843, by rfl⟩ : syracuseStep 4826249 = 3619687) B3619687
theorem B4072639 : Blo 1429534 4072639 := bstep (se 1 (by rfl) ⟨3054479, by rfl⟩ : syracuseStep 4072639 = 6108959) B6108959
theorem B4072673 : Blo 1429534 4072673 := bstep (se 2 (by rfl) ⟨1527252, by rfl⟩ : syracuseStep 4072673 = 3054505) B3054505
theorem B30934295 : Blo 1429534 30934295 := bstep (se 1 (by rfl) ⟨23200721, by rfl⟩ : syracuseStep 30934295 = 46401443) B46401443
theorem B24446285 : Blo 1429534 24446285 := bstep (se 3 (by rfl) ⟨4583678, by rfl⟩ : syracuseStep 24446285 = 9167357) B9167357
theorem B3220847 : Blo 1429534 3220847 := bstep (se 1 (by rfl) ⟨2415635, by rfl⟩ : syracuseStep 3220847 = 4831271) B4831271
theorem B34817435 : Blo 1429534 34817435 := bstep (se 1 (by rfl) ⟨26113076, by rfl⟩ : syracuseStep 34817435 = 52226153) B52226153
theorem B132204149 : Blo 1429534 132204149 := bstep (se 5 (by rfl) ⟨6197069, by rfl⟩ : syracuseStep 132204149 = 12394139) B12394139
theorem B16296065 : Blo 1429534 16296065 := bstep (se 2 (by rfl) ⟨6111024, by rfl⟩ : syracuseStep 16296065 = 12222049) B12222049
theorem B156650435 : Blo 1429534 156650435 := bstep (se 1 (by rfl) ⟨117487826, by rfl⟩ : syracuseStep 156650435 = 234975653) B234975653
theorem B18590903 : Blo 1429534 18590903 := bstep (se 1 (by rfl) ⟨13943177, by rfl⟩ : syracuseStep 18590903 = 27886355) B27886355
theorem B42364583 : Blo 1429534 42364583 := bstep (se 1 (by rfl) ⟨31773437, by rfl⟩ : syracuseStep 42364583 = 63546875) B63546875
theorem B16527091 : Blo 1429534 16527091 := bstep (se 1 (by rfl) ⟨12395318, by rfl⟩ : syracuseStep 16527091 = 24790637) B24790637
theorem B1429727 : Blo 1429534 1429727 := bstep (se 1 (by rfl) ⟨1072295, by rfl⟩ : syracuseStep 1429727 = 2144591) B2144591
theorem B4829543 : Blo 1429534 4829543 := bstep (se 1 (by rfl) ⟨3622157, by rfl⟩ : syracuseStep 4829543 = 7244315) B7244315
theorem B4829597 : Blo 1429534 4829597 := bstep (se 3 (by rfl) ⟨905549, by rfl⟩ : syracuseStep 4829597 = 1811099) B1811099
theorem B33051577 : Blo 1429534 33051577 := bstep (se 2 (by rfl) ⟨12394341, by rfl⟩ : syracuseStep 33051577 = 24788683) B24788683
theorem B1430463 : Blo 1429534 1430463 := bstep (se 1 (by rfl) ⟨1072847, by rfl⟩ : syracuseStep 1430463 = 2145695) B2145695
theorem B5428559 : Blo 1429534 5428559 := bstep (se 1 (by rfl) ⟨4071419, by rfl⟩ : syracuseStep 5428559 = 8142839) B8142839
theorem B1430911 : Blo 1429534 1430911 := bstep (se 1 (by rfl) ⟨1073183, by rfl⟩ : syracuseStep 1430911 = 2146367) B2146367
theorem B16520719 : Blo 1429534 16520719 := bstep (se 1 (by rfl) ⟨12390539, by rfl⟩ : syracuseStep 16520719 = 24781079) B24781079
theorem B1431067 : Blo 1429534 1431067 := bstep (se 1 (by rfl) ⟨1073300, by rfl⟩ : syracuseStep 1431067 = 2146601) B2146601
theorem B8697455 : Blo 1429534 8697455 := bstep (se 1 (by rfl) ⟨6523091, by rfl⟩ : syracuseStep 8697455 = 13046183) B13046183
theorem B2144303 : Blo 1429534 2144303 := bstep (se 1 (by rfl) ⟨1608227, by rfl⟩ : syracuseStep 2144303 = 3216455) B3216455
theorem B2144975 : Blo 1429534 2144975 := bstep (se 1 (by rfl) ⟨1608731, by rfl⟩ : syracuseStep 2144975 = 3217463) B3217463
theorem B2145023 : Blo 1429534 2145023 := bstep (se 1 (by rfl) ⟨1608767, by rfl⟩ : syracuseStep 2145023 = 3217535) B3217535
theorem B3054343 : Blo 1429534 3054343 := bstep (se 1 (by rfl) ⟨2290757, by rfl⟩ : syracuseStep 3054343 = 4581515) B4581515
theorem B3218399 : Blo 1429534 3218399 := bstep (se 1 (by rfl) ⟨2413799, by rfl⟩ : syracuseStep 3218399 = 4827599) B4827599
theorem B3054761 : Blo 1429534 3054761 := bstep (se 2 (by rfl) ⟨1145535, by rfl⟩ : syracuseStep 3054761 = 2291071) B2291071
theorem B3054847 : Blo 1429534 3054847 := bstep (se 1 (by rfl) ⟨2291135, by rfl⟩ : syracuseStep 3054847 = 4582271) B4582271
theorem B2293019 : Blo 1429534 2293019 := bstep (se 1 (by rfl) ⟨1719764, by rfl⟩ : syracuseStep 2293019 = 3439529) B3439529
theorem B3620335 : Blo 1429534 3620335 := bstep (se 1 (by rfl) ⟨2715251, by rfl⟩ : syracuseStep 3620335 = 5430503) B5430503
theorem B17391161 : Blo 1429534 17391161 := bstep (se 2 (by rfl) ⟨6521685, by rfl⟩ : syracuseStep 17391161 = 13043371) B13043371
theorem B6110873 : Blo 1429534 6110873 := bstep (se 2 (by rfl) ⟨2291577, by rfl⟩ : syracuseStep 6110873 = 4583155) B4583155
theorem B5430959 : Blo 1429534 5430959 := bstep (se 1 (by rfl) ⟨4073219, by rfl⟩ : syracuseStep 5430959 = 8146439) B8146439
theorem B1810127 : Blo 1429534 1810127 := bstep (se 1 (by rfl) ⟨1357595, by rfl⟩ : syracuseStep 1810127 = 2715191) B2715191
theorem B2146151 : Blo 1429534 2146151 := bstep (se 1 (by rfl) ⟨1609613, by rfl⟩ : syracuseStep 2146151 = 3219227) B3219227
theorem B2940809 : Blo 1429534 2940809 := bstep (se 2 (by rfl) ⟨1102803, by rfl⟩ : syracuseStep 2940809 = 2205607) B2205607
theorem B3219695 : Blo 1429534 3219695 := bstep (se 1 (by rfl) ⟨2414771, by rfl⟩ : syracuseStep 3219695 = 4829543) B4829543
theorem B3219731 : Blo 1429534 3219731 := bstep (se 1 (by rfl) ⟨2414798, by rfl⟩ : syracuseStep 3219731 = 4829597) B4829597
theorem B2147231 : Blo 1429534 2147231 := bstep (se 1 (by rfl) ⟨1610423, by rfl⟩ : syracuseStep 2147231 = 3220847) B3220847
theorem B4072457 : Blo 1429534 4072457 := bstep (se 2 (by rfl) ⟨1527171, by rfl⟩ : syracuseStep 4072457 = 3054343) B3054343
theorem B10864043 : Blo 1429534 10864043 := bstep (se 1 (by rfl) ⟨8148032, by rfl⟩ : syracuseStep 10864043 = 16296065) B16296065
theorem B31368629 : Blo 1429534 31368629 := bstep (se 5 (by rfl) ⟨1470404, by rfl⟩ : syracuseStep 31368629 = 2940809) B2940809
theorem B4073129 : Blo 1429534 4073129 := bstep (se 2 (by rfl) ⟨1527423, by rfl⟩ : syracuseStep 4073129 = 3054847) B3054847
theorem B4827005 : Blo 1429534 4827005 := bstep (se 3 (by rfl) ⟨905063, by rfl⟩ : syracuseStep 4827005 = 1810127) B1810127
theorem B104433623 : Blo 1429534 104433623 := bstep (se 1 (by rfl) ⟨78325217, by rfl⟩ : syracuseStep 104433623 = 156650435) B156650435
theorem B4827113 : Blo 1429534 4827113 := bstep (se 2 (by rfl) ⟨1810167, by rfl⟩ : syracuseStep 4827113 = 3620335) B3620335
theorem B11594107 : Blo 1429534 11594107 := bstep (se 1 (by rfl) ⟨8695580, by rfl⟩ : syracuseStep 11594107 = 17391161) B17391161
theorem B4073915 : Blo 1429534 4073915 := bstep (se 1 (by rfl) ⟨3055436, by rfl⟩ : syracuseStep 4073915 = 6110873) B6110873
theorem B2715115 : Blo 1429534 2715115 := bstep (se 1 (by rfl) ⟨2036336, by rfl⟩ : syracuseStep 2715115 = 4072673) B4072673
theorem B20622863 : Blo 1429534 20622863 := bstep (se 1 (by rfl) ⟨15467147, by rfl⟩ : syracuseStep 20622863 = 30934295) B30934295
theorem B16297523 : Blo 1429534 16297523 := bstep (se 1 (by rfl) ⟨12223142, by rfl⟩ : syracuseStep 16297523 = 24446285) B24446285
theorem B23211623 : Blo 1429534 23211623 := bstep (se 1 (by rfl) ⟨17408717, by rfl⟩ : syracuseStep 23211623 = 34817435) B34817435
theorem B18361961 : Blo 1429534 18361961 := bstep (se 2 (by rfl) ⟨6885735, by rfl⟩ : syracuseStep 18361961 = 13771471) B13771471
theorem B44068769 : Blo 1429534 44068769 := bstep (se 2 (by rfl) ⟨16525788, by rfl⟩ : syracuseStep 44068769 = 33051577) B33051577
theorem B1429535 : Blo 1429534 1429535 := bstep (se 1 (by rfl) ⟨1072151, by rfl⟩ : syracuseStep 1429535 = 2144303) B2144303
theorem B1429983 : Blo 1429534 1429983 := bstep (se 1 (by rfl) ⟨1072487, by rfl⟩ : syracuseStep 1429983 = 2144975) B2144975
theorem B1430015 : Blo 1429534 1430015 := bstep (se 1 (by rfl) ⟨1072511, by rfl⟩ : syracuseStep 1430015 = 2145023) B2145023
theorem B2036507 : Blo 1429534 2036507 := bstep (se 1 (by rfl) ⟨1527380, by rfl⟩ : syracuseStep 2036507 = 3054761) B3054761
theorem B1528679 : Blo 1429534 1528679 := bstep (se 1 (by rfl) ⟨1146509, by rfl⟩ : syracuseStep 1528679 = 2293019) B2293019
theorem B28243055 : Blo 1429534 28243055 := bstep (se 1 (by rfl) ⟨21182291, by rfl⟩ : syracuseStep 28243055 = 42364583) B42364583
theorem B1430767 : Blo 1429534 1430767 := bstep (se 1 (by rfl) ⟨1073075, by rfl⟩ : syracuseStep 1430767 = 2146151) B2146151
theorem B3216743 : Blo 1429534 3216743 := bstep (se 1 (by rfl) ⟨2412557, by rfl⟩ : syracuseStep 3216743 = 4825115) B4825115
theorem B5428727 : Blo 1429534 5428727 := bstep (se 1 (by rfl) ⟨4071545, by rfl⟩ : syracuseStep 5428727 = 8143091) B8143091
theorem B47011387 : Blo 1429534 47011387 := bstep (se 1 (by rfl) ⟨35258540, by rfl⟩ : syracuseStep 47011387 = 70517081) B70517081
theorem B1431323 : Blo 1429534 1431323 := bstep (se 1 (by rfl) ⟨1073492, by rfl⟩ : syracuseStep 1431323 = 2146985) B2146985
theorem B16291691 : Blo 1429534 16291691 := bstep (se 1 (by rfl) ⟨12218768, by rfl⟩ : syracuseStep 16291691 = 24437537) B24437537
theorem B3217499 : Blo 1429534 3217499 := bstep (se 1 (by rfl) ⟨2413124, by rfl⟩ : syracuseStep 3217499 = 4826249) B4826249
theorem B3619039 : Blo 1429534 3619039 := bstep (se 1 (by rfl) ⟨2714279, by rfl⟩ : syracuseStep 3619039 = 5428559) B5428559
theorem B5798303 : Blo 1429534 5798303 := bstep (se 1 (by rfl) ⟨4348727, by rfl⟩ : syracuseStep 5798303 = 8697455) B8697455
theorem B88136099 : Blo 1429534 88136099 := bstep (se 1 (by rfl) ⟨66102074, by rfl⟩ : syracuseStep 88136099 = 132204149) B132204149
theorem B5430185 : Blo 1429534 5430185 := bstep (se 2 (by rfl) ⟨2036319, by rfl⟩ : syracuseStep 5430185 = 4072639) B4072639
theorem B2145599 : Blo 1429534 2145599 := bstep (se 1 (by rfl) ⟨1609199, by rfl⟩ : syracuseStep 2145599 = 3218399) B3218399
theorem B22027625 : Blo 1429534 22027625 := bstep (se 2 (by rfl) ⟨8260359, by rfl⟩ : syracuseStep 22027625 = 16520719) B16520719
theorem B12393935 : Blo 1429534 12393935 := bstep (se 1 (by rfl) ⟨9295451, by rfl⟩ : syracuseStep 12393935 = 18590903) B18590903
theorem B22036121 : Blo 1429534 22036121 := bstep (se 2 (by rfl) ⟨8263545, by rfl⟩ : syracuseStep 22036121 = 16527091) B16527091
theorem B3620639 : Blo 1429534 3620639 := bstep (se 1 (by rfl) ⟨2715479, by rfl⟩ : syracuseStep 3620639 = 5430959) B5430959
theorem B2146463 : Blo 1429534 2146463 := bstep (se 1 (by rfl) ⟨1609847, by rfl⟩ : syracuseStep 2146463 = 3219695) B3219695
theorem B2146487 : Blo 1429534 2146487 := bstep (se 1 (by rfl) ⟨1609865, by rfl⟩ : syracuseStep 2146487 = 3219731) B3219731
theorem B4825385 : Blo 1429534 4825385 := bstep (se 2 (by rfl) ⟨1809519, by rfl⟩ : syracuseStep 4825385 = 3619039) B3619039
theorem B15458809 : Blo 1429534 15458809 := bstep (se 2 (by rfl) ⟨5797053, by rfl⟩ : syracuseStep 15458809 = 11594107) B11594107
theorem B7242695 : Blo 1429534 7242695 := bstep (se 1 (by rfl) ⟨5432021, by rfl⟩ : syracuseStep 7242695 = 10864043) B10864043
theorem B54994301 : Blo 1429534 54994301 := bstep (se 3 (by rfl) ⟨10311431, by rfl⟩ : syracuseStep 54994301 = 20622863) B20622863
theorem B10865015 : Blo 1429534 10865015 := bstep (se 1 (by rfl) ⟨8148761, by rfl⟩ : syracuseStep 10865015 = 16297523) B16297523
theorem B12241307 : Blo 1429534 12241307 := bstep (se 1 (by rfl) ⟨9180980, by rfl⟩ : syracuseStep 12241307 = 18361961) B18361961
theorem B14690747 : Blo 1429534 14690747 := bstep (se 1 (by rfl) ⟨11018060, by rfl⟩ : syracuseStep 14690747 = 22036121) B22036121
theorem B29379179 : Blo 1429534 29379179 := bstep (se 1 (by rfl) ⟨22034384, by rfl⟩ : syracuseStep 29379179 = 44068769) B44068769
theorem B2714971 : Blo 1429534 2714971 := bstep (se 1 (by rfl) ⟨2036228, by rfl⟩ : syracuseStep 2714971 = 4072457) B4072457
theorem B18828703 : Blo 1429534 18828703 := bstep (se 1 (by rfl) ⟨14121527, by rfl⟩ : syracuseStep 18828703 = 28243055) B28243055
theorem B2715419 : Blo 1429534 2715419 := bstep (se 1 (by rfl) ⟨2036564, by rfl⟩ : syracuseStep 2715419 = 4073129) B4073129
theorem B58757399 : Blo 1429534 58757399 := bstep (se 1 (by rfl) ⟨44068049, by rfl⟩ : syracuseStep 58757399 = 88136099) B88136099
theorem B2715943 : Blo 1429534 2715943 := bstep (se 1 (by rfl) ⟨2036957, by rfl⟩ : syracuseStep 2715943 = 4073915) B4073915
theorem B62681849 : Blo 1429534 62681849 := bstep (se 2 (by rfl) ⟨23505693, by rfl⟩ : syracuseStep 62681849 = 47011387) B47011387
theorem B1430399 : Blo 1429534 1430399 := bstep (se 1 (by rfl) ⟨1072799, by rfl⟩ : syracuseStep 1430399 = 2145599) B2145599
theorem B14685083 : Blo 1429534 14685083 := bstep (se 1 (by rfl) ⟨11013812, by rfl⟩ : syracuseStep 14685083 = 22027625) B22027625
theorem B4076477 : Blo 1429534 4076477 := bstep (se 3 (by rfl) ⟨764339, by rfl⟩ : syracuseStep 4076477 = 1528679) B1528679
theorem B8262623 : Blo 1429534 8262623 := bstep (se 1 (by rfl) ⟨6196967, by rfl⟩ : syracuseStep 8262623 = 12393935) B12393935
theorem B2413759 : Blo 1429534 2413759 := bstep (se 1 (by rfl) ⟨1810319, by rfl⟩ : syracuseStep 2413759 = 3620639) B3620639
theorem B1431487 : Blo 1429534 1431487 := bstep (se 1 (by rfl) ⟨1073615, by rfl⟩ : syracuseStep 1431487 = 2147231) B2147231
theorem B2144495 : Blo 1429534 2144495 := bstep (se 1 (by rfl) ⟨1608371, by rfl⟩ : syracuseStep 2144495 = 3216743) B3216743
theorem B20912419 : Blo 1429534 20912419 := bstep (se 1 (by rfl) ⟨15684314, by rfl⟩ : syracuseStep 20912419 = 31368629) B31368629
theorem B3619151 : Blo 1429534 3619151 := bstep (se 1 (by rfl) ⟨2714363, by rfl⟩ : syracuseStep 3619151 = 5428727) B5428727
theorem B10861127 : Blo 1429534 10861127 := bstep (se 1 (by rfl) ⟨8145845, by rfl⟩ : syracuseStep 10861127 = 16291691) B16291691
theorem B3218003 : Blo 1429534 3218003 := bstep (se 1 (by rfl) ⟨2413502, by rfl⟩ : syracuseStep 3218003 = 4827005) B4827005
theorem B69622415 : Blo 1429534 69622415 := bstep (se 1 (by rfl) ⟨52216811, by rfl⟩ : syracuseStep 69622415 = 104433623) B104433623
theorem B3218075 : Blo 1429534 3218075 := bstep (se 1 (by rfl) ⟨2413556, by rfl⟩ : syracuseStep 3218075 = 4827113) B4827113
theorem B2144999 : Blo 1429534 2144999 := bstep (se 1 (by rfl) ⟨1608749, by rfl⟩ : syracuseStep 2144999 = 3217499) B3217499
theorem B3865535 : Blo 1429534 3865535 := bstep (se 1 (by rfl) ⟨2899151, by rfl⟩ : syracuseStep 3865535 = 5798303) B5798303
theorem B3620123 : Blo 1429534 3620123 := bstep (se 1 (by rfl) ⟨2715092, by rfl⟩ : syracuseStep 3620123 = 5430185) B5430185
theorem B3620153 : Blo 1429534 3620153 := bstep (se 2 (by rfl) ⟨1357557, by rfl⟩ : syracuseStep 3620153 = 2715115) B2715115
theorem B5430685 : Blo 1429534 5430685 := bstep (se 3 (by rfl) ⟨1018253, by rfl⟩ : syracuseStep 5430685 = 2036507) B2036507
theorem B15474415 : Blo 1429534 15474415 := bstep (se 1 (by rfl) ⟨11605811, by rfl⟩ : syracuseStep 15474415 = 23211623) B23211623
theorem B3621257 : Blo 1429534 3621257 := bstep (se 2 (by rfl) ⟨1357971, by rfl⟩ : syracuseStep 3621257 = 2715943) B2715943
theorem B41787899 : Blo 1429534 41787899 := bstep (se 1 (by rfl) ⟨31340924, by rfl⟩ : syracuseStep 41787899 = 62681849) B62681849
theorem B9790055 : Blo 1429534 9790055 := bstep (se 1 (by rfl) ⟨7342541, by rfl⟩ : syracuseStep 9790055 = 14685083) B14685083
theorem B20611745 : Blo 1429534 20611745 := bstep (se 2 (by rfl) ⟨7729404, by rfl⟩ : syracuseStep 20611745 = 15458809) B15458809
theorem B7243343 : Blo 1429534 7243343 := bstep (se 1 (by rfl) ⟨5432507, by rfl⟩ : syracuseStep 7243343 = 10865015) B10865015
theorem B8160871 : Blo 1429534 8160871 := bstep (se 1 (by rfl) ⟨6120653, by rfl⟩ : syracuseStep 8160871 = 12241307) B12241307
theorem B100419749 : Blo 1429534 100419749 := bstep (se 4 (by rfl) ⟨9414351, by rfl⟩ : syracuseStep 100419749 = 18828703) B18828703
theorem B4828463 : Blo 1429534 4828463 := bstep (se 1 (by rfl) ⟨3621347, by rfl⟩ : syracuseStep 4828463 = 7242695) B7242695
theorem B5508415 : Blo 1429534 5508415 := bstep (se 1 (by rfl) ⟨4131311, by rfl⟩ : syracuseStep 5508415 = 8262623) B8262623
theorem B36662867 : Blo 1429534 36662867 := bstep (se 1 (by rfl) ⟨27497150, by rfl⟩ : syracuseStep 36662867 = 54994301) B54994301
theorem B1429663 : Blo 1429534 1429663 := bstep (se 1 (by rfl) ⟨1072247, by rfl⟩ : syracuseStep 1429663 = 2144495) B2144495
theorem B2412767 : Blo 1429534 2412767 := bstep (se 1 (by rfl) ⟨1809575, by rfl⟩ : syracuseStep 2412767 = 3619151) B3619151
theorem B9793831 : Blo 1429534 9793831 := bstep (se 1 (by rfl) ⟨7345373, by rfl⟩ : syracuseStep 9793831 = 14690747) B14690747
theorem B1429999 : Blo 1429534 1429999 := bstep (se 1 (by rfl) ⟨1072499, by rfl⟩ : syracuseStep 1429999 = 2144999) B2144999
theorem B2577023 : Blo 1429534 2577023 := bstep (se 1 (by rfl) ⟨1932767, by rfl⟩ : syracuseStep 2577023 = 3865535) B3865535
theorem B2413415 : Blo 1429534 2413415 := bstep (se 1 (by rfl) ⟨1810061, by rfl⟩ : syracuseStep 2413415 = 3620123) B3620123
theorem B2413435 : Blo 1429534 2413435 := bstep (se 1 (by rfl) ⟨1810076, by rfl⟩ : syracuseStep 2413435 = 3620153) B3620153
theorem B20632553 : Blo 1429534 20632553 := bstep (se 2 (by rfl) ⟨7737207, by rfl⟩ : syracuseStep 20632553 = 15474415) B15474415
theorem B1430975 : Blo 1429534 1430975 := bstep (se 1 (by rfl) ⟨1073231, by rfl⟩ : syracuseStep 1430975 = 2146463) B2146463
theorem B1430991 : Blo 1429534 1430991 := bstep (se 1 (by rfl) ⟨1073243, by rfl⟩ : syracuseStep 1430991 = 2146487) B2146487
theorem B39171599 : Blo 1429534 39171599 := bstep (se 1 (by rfl) ⟨29378699, by rfl⟩ : syracuseStep 39171599 = 58757399) B58757399
theorem B3216923 : Blo 1429534 3216923 := bstep (se 1 (by rfl) ⟨2412692, by rfl⟩ : syracuseStep 3216923 = 4825385) B4825385
theorem B27883225 : Blo 1429534 27883225 := bstep (se 2 (by rfl) ⟨10456209, by rfl⟩ : syracuseStep 27883225 = 20912419) B20912419
theorem B2717651 : Blo 1429534 2717651 := bstep (se 1 (by rfl) ⟨2038238, by rfl⟩ : syracuseStep 2717651 = 4076477) B4076477
theorem B3218345 : Blo 1429534 3218345 := bstep (se 2 (by rfl) ⟨1206879, by rfl⟩ : syracuseStep 3218345 = 2413759) B2413759
theorem B7240751 : Blo 1429534 7240751 := bstep (se 1 (by rfl) ⟨5430563, by rfl⟩ : syracuseStep 7240751 = 10861127) B10861127
theorem B2145335 : Blo 1429534 2145335 := bstep (se 1 (by rfl) ⟨1609001, by rfl⟩ : syracuseStep 2145335 = 3218003) B3218003
theorem B19586119 : Blo 1429534 19586119 := bstep (se 1 (by rfl) ⟨14689589, by rfl⟩ : syracuseStep 19586119 = 29379179) B29379179
theorem B46414943 : Blo 1429534 46414943 := bstep (se 1 (by rfl) ⟨34811207, by rfl⟩ : syracuseStep 46414943 = 69622415) B69622415
theorem B2145383 : Blo 1429534 2145383 := bstep (se 1 (by rfl) ⟨1609037, by rfl⟩ : syracuseStep 2145383 = 3218075) B3218075
theorem B3619961 : Blo 1429534 3619961 := bstep (se 2 (by rfl) ⟨1357485, by rfl⟩ : syracuseStep 3619961 = 2714971) B2714971
theorem B7240913 : Blo 1429534 7240913 := bstep (se 2 (by rfl) ⟨2715342, by rfl⟩ : syracuseStep 7240913 = 5430685) B5430685
theorem B1810279 : Blo 1429534 1810279 := bstep (se 1 (by rfl) ⟨1357709, by rfl⟩ : syracuseStep 1810279 = 2715419) B2715419
theorem B13058441 : Blo 1429534 13058441 := bstep (se 2 (by rfl) ⟨4896915, by rfl⟩ : syracuseStep 13058441 = 9793831) B9793831
theorem B13755035 : Blo 1429534 13755035 := bstep (se 1 (by rfl) ⟨10316276, by rfl⟩ : syracuseStep 13755035 = 20632553) B20632553
theorem B66946499 : Blo 1429534 66946499 := bstep (se 1 (by rfl) ⟨50209874, by rfl⟩ : syracuseStep 66946499 = 100419749) B100419749
theorem B29378213 : Blo 1429534 29378213 := bstep (se 4 (by rfl) ⟨2754207, by rfl⟩ : syracuseStep 29378213 = 5508415) B5508415
theorem B4827167 : Blo 1429534 4827167 := bstep (se 1 (by rfl) ⟨3620375, by rfl⟩ : syracuseStep 4827167 = 7240751) B7240751
theorem B30943295 : Blo 1429534 30943295 := bstep (se 1 (by rfl) ⟨23207471, by rfl⟩ : syracuseStep 30943295 = 46414943) B46414943
theorem B10881161 : Blo 1429534 10881161 := bstep (se 2 (by rfl) ⟨4080435, by rfl⟩ : syracuseStep 10881161 = 8160871) B8160871
theorem B4827275 : Blo 1429534 4827275 := bstep (se 1 (by rfl) ⟨3620456, by rfl⟩ : syracuseStep 4827275 = 7240913) B7240913
theorem B37177633 : Blo 1429534 37177633 := bstep (se 2 (by rfl) ⟨13941612, by rfl⟩ : syracuseStep 37177633 = 27883225) B27883225
theorem B1608511 : Blo 1429534 1608511 := bstep (se 1 (by rfl) ⟨1206383, by rfl⟩ : syracuseStep 1608511 = 2412767) B2412767
theorem B13741163 : Blo 1429534 13741163 := bstep (se 1 (by rfl) ⟨10305872, by rfl⟩ : syracuseStep 13741163 = 20611745) B20611745
theorem B1608943 : Blo 1429534 1608943 := bstep (se 1 (by rfl) ⟨1206707, by rfl⟩ : syracuseStep 1608943 = 2413415) B2413415
theorem B4828895 : Blo 1429534 4828895 := bstep (se 1 (by rfl) ⟨3621671, by rfl⟩ : syracuseStep 4828895 = 7243343) B7243343
theorem B1430223 : Blo 1429534 1430223 := bstep (se 1 (by rfl) ⟨1072667, by rfl⟩ : syracuseStep 1430223 = 2145335) B2145335
theorem B1430255 : Blo 1429534 1430255 := bstep (se 1 (by rfl) ⟨1072691, by rfl⟩ : syracuseStep 1430255 = 2145383) B2145383
theorem B2413307 : Blo 1429534 2413307 := bstep (se 1 (by rfl) ⟨1809980, by rfl⟩ : syracuseStep 2413307 = 3619961) B3619961
theorem B24441911 : Blo 1429534 24441911 := bstep (se 1 (by rfl) ⟨18331433, by rfl⟩ : syracuseStep 24441911 = 36662867) B36662867
theorem B2413705 : Blo 1429534 2413705 := bstep (se 2 (by rfl) ⟨905139, by rfl⟩ : syracuseStep 2413705 = 1810279) B1810279
theorem B7247069 : Blo 1429534 7247069 := bstep (se 3 (by rfl) ⟨1358825, by rfl⟩ : syracuseStep 7247069 = 2717651) B2717651
theorem B2414171 : Blo 1429534 2414171 := bstep (se 1 (by rfl) ⟨1810628, by rfl⟩ : syracuseStep 2414171 = 3621257) B3621257
theorem B27858599 : Blo 1429534 27858599 := bstep (se 1 (by rfl) ⟨20893949, by rfl⟩ : syracuseStep 27858599 = 41787899) B41787899
theorem B6526703 : Blo 1429534 6526703 := bstep (se 1 (by rfl) ⟨4895027, by rfl⟩ : syracuseStep 6526703 = 9790055) B9790055
theorem B1718015 : Blo 1429534 1718015 := bstep (se 1 (by rfl) ⟨1288511, by rfl⟩ : syracuseStep 1718015 = 2577023) B2577023
theorem B26114399 : Blo 1429534 26114399 := bstep (se 1 (by rfl) ⟨19585799, by rfl⟩ : syracuseStep 26114399 = 39171599) B39171599
theorem B2144615 : Blo 1429534 2144615 := bstep (se 1 (by rfl) ⟨1608461, by rfl⟩ : syracuseStep 2144615 = 3216923) B3216923
theorem B3217913 : Blo 1429534 3217913 := bstep (se 2 (by rfl) ⟨1206717, by rfl⟩ : syracuseStep 3217913 = 2413435) B2413435
theorem B26114825 : Blo 1429534 26114825 := bstep (se 2 (by rfl) ⟨9793059, by rfl⟩ : syracuseStep 26114825 = 19586119) B19586119
theorem B2145563 : Blo 1429534 2145563 := bstep (se 1 (by rfl) ⟨1609172, by rfl⟩ : syracuseStep 2145563 = 3218345) B3218345
theorem B3218975 : Blo 1429534 3218975 := bstep (se 1 (by rfl) ⟨2414231, by rfl⟩ : syracuseStep 3218975 = 4828463) B4828463
theorem B49570177 : Blo 1429534 49570177 := bstep (se 2 (by rfl) ⟨18588816, by rfl⟩ : syracuseStep 49570177 = 37177633) B37177633
theorem B16294607 : Blo 1429534 16294607 := bstep (se 1 (by rfl) ⟨12220955, by rfl⟩ : syracuseStep 16294607 = 24441911) B24441911
theorem B44630999 : Blo 1429534 44630999 := bstep (se 1 (by rfl) ⟨33473249, by rfl⟩ : syracuseStep 44630999 = 66946499) B66946499
theorem B18572399 : Blo 1429534 18572399 := bstep (se 1 (by rfl) ⟨13929299, by rfl⟩ : syracuseStep 18572399 = 27858599) B27858599
theorem B20628863 : Blo 1429534 20628863 := bstep (se 1 (by rfl) ⟨15471647, by rfl⟩ : syracuseStep 20628863 = 30943295) B30943295
theorem B17409599 : Blo 1429534 17409599 := bstep (se 1 (by rfl) ⟨13057199, by rfl⟩ : syracuseStep 17409599 = 26114399) B26114399
theorem B4581373 : Blo 1429534 4581373 := bstep (se 3 (by rfl) ⟨859007, by rfl⟩ : syracuseStep 4581373 = 1718015) B1718015
theorem B9160775 : Blo 1429534 9160775 := bstep (se 1 (by rfl) ⟨6870581, by rfl⟩ : syracuseStep 9160775 = 13741163) B13741163
theorem B9170023 : Blo 1429534 9170023 := bstep (se 1 (by rfl) ⟨6877517, by rfl⟩ : syracuseStep 9170023 = 13755035) B13755035
theorem B1608871 : Blo 1429534 1608871 := bstep (se 1 (by rfl) ⟨1206653, by rfl⟩ : syracuseStep 1608871 = 2413307) B2413307
theorem B1609447 : Blo 1429534 1609447 := bstep (se 1 (by rfl) ⟨1207085, by rfl⟩ : syracuseStep 1609447 = 2414171) B2414171
theorem B7254107 : Blo 1429534 7254107 := bstep (se 1 (by rfl) ⟨5440580, by rfl⟩ : syracuseStep 7254107 = 10881161) B10881161
theorem B1429743 : Blo 1429534 1429743 := bstep (se 1 (by rfl) ⟨1072307, by rfl⟩ : syracuseStep 1429743 = 2144615) B2144615
theorem B17404541 : Blo 1429534 17404541 := bstep (se 3 (by rfl) ⟨3263351, by rfl⟩ : syracuseStep 17404541 = 6526703) B6526703
theorem B1430375 : Blo 1429534 1430375 := bstep (se 1 (by rfl) ⟨1072781, by rfl⟩ : syracuseStep 1430375 = 2145563) B2145563
theorem B8705627 : Blo 1429534 8705627 := bstep (se 1 (by rfl) ⟨6529220, by rfl⟩ : syracuseStep 8705627 = 13058441) B13058441
theorem B4831379 : Blo 1429534 4831379 := bstep (se 1 (by rfl) ⟨3623534, by rfl⟩ : syracuseStep 4831379 = 7247069) B7247069
theorem B2144681 : Blo 1429534 2144681 := bstep (se 2 (by rfl) ⟨804255, by rfl⟩ : syracuseStep 2144681 = 1608511) B1608511
theorem B19585475 : Blo 1429534 19585475 := bstep (se 1 (by rfl) ⟨14689106, by rfl⟩ : syracuseStep 19585475 = 29378213) B29378213
theorem B3218111 : Blo 1429534 3218111 := bstep (se 1 (by rfl) ⟨2413583, by rfl⟩ : syracuseStep 3218111 = 4827167) B4827167
theorem B3218183 : Blo 1429534 3218183 := bstep (se 1 (by rfl) ⟨2413637, by rfl⟩ : syracuseStep 3218183 = 4827275) B4827275
theorem B3218273 : Blo 1429534 3218273 := bstep (se 2 (by rfl) ⟨1206852, by rfl⟩ : syracuseStep 3218273 = 2413705) B2413705
theorem B2145257 : Blo 1429534 2145257 := bstep (se 2 (by rfl) ⟨804471, by rfl⟩ : syracuseStep 2145257 = 1608943) B1608943
theorem B2145275 : Blo 1429534 2145275 := bstep (se 1 (by rfl) ⟨1608956, by rfl⟩ : syracuseStep 2145275 = 3217913) B3217913
theorem B69639533 : Blo 1429534 69639533 := bstep (se 3 (by rfl) ⟨13057412, by rfl⟩ : syracuseStep 69639533 = 26114825) B26114825
theorem B2145983 : Blo 1429534 2145983 := bstep (se 1 (by rfl) ⟨1609487, by rfl⟩ : syracuseStep 2145983 = 3218975) B3218975
theorem B3219263 : Blo 1429534 3219263 := bstep (se 1 (by rfl) ⟨2414447, by rfl⟩ : syracuseStep 3219263 = 4828895) B4828895
theorem B10863071 : Blo 1429534 10863071 := bstep (se 1 (by rfl) ⟨8147303, by rfl⟩ : syracuseStep 10863071 = 16294607) B16294607
theorem B66093569 : Blo 1429534 66093569 := bstep (se 2 (by rfl) ⟨24785088, by rfl⟩ : syracuseStep 66093569 = 49570177) B49570177
theorem B29753999 : Blo 1429534 29753999 := bstep (se 1 (by rfl) ⟨22315499, by rfl⟩ : syracuseStep 29753999 = 44630999) B44630999
theorem B3220919 : Blo 1429534 3220919 := bstep (se 1 (by rfl) ⟨2415689, by rfl⟩ : syracuseStep 3220919 = 4831379) B4831379
theorem B46426355 : Blo 1429534 46426355 := bstep (se 1 (by rfl) ⟨34819766, by rfl⟩ : syracuseStep 46426355 = 69639533) B69639533
theorem B4836071 : Blo 1429534 4836071 := bstep (se 1 (by rfl) ⟨3627053, by rfl⟩ : syracuseStep 4836071 = 7254107) B7254107
theorem B11603027 : Blo 1429534 11603027 := bstep (se 1 (by rfl) ⟨8702270, by rfl⟩ : syracuseStep 11603027 = 17404541) B17404541
theorem B12381599 : Blo 1429534 12381599 := bstep (se 1 (by rfl) ⟨9286199, by rfl⟩ : syracuseStep 12381599 = 18572399) B18572399
theorem B5803751 : Blo 1429534 5803751 := bstep (se 1 (by rfl) ⟨4352813, by rfl⟩ : syracuseStep 5803751 = 8705627) B8705627
theorem B6107183 : Blo 1429534 6107183 := bstep (se 1 (by rfl) ⟨4580387, by rfl⟩ : syracuseStep 6107183 = 9160775) B9160775
theorem B12226697 : Blo 1429534 12226697 := bstep (se 2 (by rfl) ⟨4585011, by rfl⟩ : syracuseStep 12226697 = 9170023) B9170023
theorem B1429787 : Blo 1429534 1429787 := bstep (se 1 (by rfl) ⟨1072340, by rfl⟩ : syracuseStep 1429787 = 2144681) B2144681
theorem B1430171 : Blo 1429534 1430171 := bstep (se 1 (by rfl) ⟨1072628, by rfl⟩ : syracuseStep 1430171 = 2145257) B2145257
theorem B1430183 : Blo 1429534 1430183 := bstep (se 1 (by rfl) ⟨1072637, by rfl⟩ : syracuseStep 1430183 = 2145275) B2145275
theorem B1430655 : Blo 1429534 1430655 := bstep (se 1 (by rfl) ⟨1072991, by rfl⟩ : syracuseStep 1430655 = 2145983) B2145983
theorem B6108497 : Blo 1429534 6108497 := bstep (se 2 (by rfl) ⟨2290686, by rfl⟩ : syracuseStep 6108497 = 4581373) B4581373
theorem B13752575 : Blo 1429534 13752575 := bstep (se 1 (by rfl) ⟨10314431, by rfl⟩ : syracuseStep 13752575 = 20628863) B20628863
theorem B11606399 : Blo 1429534 11606399 := bstep (se 1 (by rfl) ⟨8704799, by rfl⟩ : syracuseStep 11606399 = 17409599) B17409599
theorem B2145161 : Blo 1429534 2145161 := bstep (se 2 (by rfl) ⟨804435, by rfl⟩ : syracuseStep 2145161 = 1608871) B1608871
theorem B13056983 : Blo 1429534 13056983 := bstep (se 1 (by rfl) ⟨9792737, by rfl⟩ : syracuseStep 13056983 = 19585475) B19585475
theorem B2145407 : Blo 1429534 2145407 := bstep (se 1 (by rfl) ⟨1609055, by rfl⟩ : syracuseStep 2145407 = 3218111) B3218111
theorem B2145455 : Blo 1429534 2145455 := bstep (se 1 (by rfl) ⟨1609091, by rfl⟩ : syracuseStep 2145455 = 3218183) B3218183
theorem B2145515 : Blo 1429534 2145515 := bstep (se 1 (by rfl) ⟨1609136, by rfl⟩ : syracuseStep 2145515 = 3218273) B3218273
theorem B2145929 : Blo 1429534 2145929 := bstep (se 2 (by rfl) ⟨804723, by rfl⟩ : syracuseStep 2145929 = 1609447) B1609447
theorem B2146175 : Blo 1429534 2146175 := bstep (se 1 (by rfl) ⟨1609631, by rfl⟩ : syracuseStep 2146175 = 3219263) B3219263
theorem B4071455 : Blo 1429534 4071455 := bstep (se 1 (by rfl) ⟨3053591, by rfl⟩ : syracuseStep 4071455 = 6107183) B6107183
theorem B8151131 : Blo 1429534 8151131 := bstep (se 1 (by rfl) ⟨6113348, by rfl⟩ : syracuseStep 8151131 = 12226697) B12226697
theorem B7242047 : Blo 1429534 7242047 := bstep (se 1 (by rfl) ⟨5431535, by rfl⟩ : syracuseStep 7242047 = 10863071) B10863071
theorem B4072331 : Blo 1429534 4072331 := bstep (se 1 (by rfl) ⟨3054248, by rfl⟩ : syracuseStep 4072331 = 6108497) B6108497
theorem B2147279 : Blo 1429534 2147279 := bstep (se 1 (by rfl) ⟨1610459, by rfl⟩ : syracuseStep 2147279 = 3220919) B3220919
theorem B30950903 : Blo 1429534 30950903 := bstep (se 1 (by rfl) ⟨23213177, by rfl⟩ : syracuseStep 30950903 = 46426355) B46426355
theorem B9168383 : Blo 1429534 9168383 := bstep (se 1 (by rfl) ⟨6876287, by rfl⟩ : syracuseStep 9168383 = 13752575) B13752575
theorem B12896189 : Blo 1429534 12896189 := bstep (se 3 (by rfl) ⟨2418035, by rfl⟩ : syracuseStep 12896189 = 4836071) B4836071
theorem B15476669 : Blo 1429534 15476669 := bstep (se 3 (by rfl) ⟨2901875, by rfl⟩ : syracuseStep 15476669 = 5803751) B5803751
theorem B7735351 : Blo 1429534 7735351 := bstep (se 1 (by rfl) ⟨5801513, by rfl⟩ : syracuseStep 7735351 = 11603027) B11603027
theorem B19835999 : Blo 1429534 19835999 := bstep (se 1 (by rfl) ⟨14876999, by rfl⟩ : syracuseStep 19835999 = 29753999) B29753999
theorem B7737599 : Blo 1429534 7737599 := bstep (se 1 (by rfl) ⟨5803199, by rfl⟩ : syracuseStep 7737599 = 11606399) B11606399
theorem B1430107 : Blo 1429534 1430107 := bstep (se 1 (by rfl) ⟨1072580, by rfl⟩ : syracuseStep 1430107 = 2145161) B2145161
theorem B8704655 : Blo 1429534 8704655 := bstep (se 1 (by rfl) ⟨6528491, by rfl⟩ : syracuseStep 8704655 = 13056983) B13056983
theorem B1430271 : Blo 1429534 1430271 := bstep (se 1 (by rfl) ⟨1072703, by rfl⟩ : syracuseStep 1430271 = 2145407) B2145407
theorem B1430303 : Blo 1429534 1430303 := bstep (se 1 (by rfl) ⟨1072727, by rfl⟩ : syracuseStep 1430303 = 2145455) B2145455
theorem B1430343 : Blo 1429534 1430343 := bstep (se 1 (by rfl) ⟨1072757, by rfl⟩ : syracuseStep 1430343 = 2145515) B2145515
theorem B8254399 : Blo 1429534 8254399 := bstep (se 1 (by rfl) ⟨6190799, by rfl⟩ : syracuseStep 8254399 = 12381599) B12381599
theorem B1430619 : Blo 1429534 1430619 := bstep (se 1 (by rfl) ⟨1072964, by rfl⟩ : syracuseStep 1430619 = 2145929) B2145929
theorem B1430783 : Blo 1429534 1430783 := bstep (se 1 (by rfl) ⟨1073087, by rfl⟩ : syracuseStep 1430783 = 2146175) B2146175
theorem B44062379 : Blo 1429534 44062379 := bstep (se 1 (by rfl) ⟨33046784, by rfl⟩ : syracuseStep 44062379 = 66093569) B66093569
theorem B10313801 : Blo 1429534 10313801 := bstep (se 2 (by rfl) ⟨3867675, by rfl⟩ : syracuseStep 10313801 = 7735351) B7735351
theorem B6112255 : Blo 1429534 6112255 := bstep (se 1 (by rfl) ⟨4584191, by rfl⟩ : syracuseStep 6112255 = 9168383) B9168383
theorem B13223999 : Blo 1429534 13223999 := bstep (se 1 (by rfl) ⟨9917999, by rfl⟩ : syracuseStep 13223999 = 19835999) B19835999
theorem B2714303 : Blo 1429534 2714303 := bstep (se 1 (by rfl) ⟨2035727, by rfl⟩ : syracuseStep 2714303 = 4071455) B4071455
theorem B5434087 : Blo 1429534 5434087 := bstep (se 1 (by rfl) ⟨4075565, by rfl⟩ : syracuseStep 5434087 = 8151131) B8151131
theorem B4828031 : Blo 1429534 4828031 := bstep (se 1 (by rfl) ⟨3621023, by rfl⟩ : syracuseStep 4828031 = 7242047) B7242047
theorem B5803103 : Blo 1429534 5803103 := bstep (se 1 (by rfl) ⟨4352327, by rfl⟩ : syracuseStep 5803103 = 8704655) B8704655
theorem B2714887 : Blo 1429534 2714887 := bstep (se 1 (by rfl) ⟨2036165, by rfl⟩ : syracuseStep 2714887 = 4072331) B4072331
theorem B11005865 : Blo 1429534 11005865 := bstep (se 2 (by rfl) ⟨4127199, by rfl⟩ : syracuseStep 11005865 = 8254399) B8254399
theorem B8597459 : Blo 1429534 8597459 := bstep (se 1 (by rfl) ⟨6448094, by rfl⟩ : syracuseStep 8597459 = 12896189) B12896189
theorem B10317779 : Blo 1429534 10317779 := bstep (se 1 (by rfl) ⟨7738334, by rfl⟩ : syracuseStep 10317779 = 15476669) B15476669
theorem B5158399 : Blo 1429534 5158399 := bstep (se 1 (by rfl) ⟨3868799, by rfl⟩ : syracuseStep 5158399 = 7737599) B7737599
theorem B1431519 : Blo 1429534 1431519 := bstep (se 1 (by rfl) ⟨1073639, by rfl⟩ : syracuseStep 1431519 = 2147279) B2147279
theorem B20633935 : Blo 1429534 20633935 := bstep (se 1 (by rfl) ⟨15475451, by rfl⟩ : syracuseStep 20633935 = 30950903) B30950903
theorem B29374919 : Blo 1429534 29374919 := bstep (se 1 (by rfl) ⟨22031189, by rfl⟩ : syracuseStep 29374919 = 44062379) B44062379
theorem B8815999 : Blo 1429534 8815999 := bstep (se 1 (by rfl) ⟨6611999, by rfl⟩ : syracuseStep 8815999 = 13223999) B13223999
theorem B3868735 : Blo 1429534 3868735 := bstep (se 1 (by rfl) ⟨2901551, by rfl⟩ : syracuseStep 3868735 = 5803103) B5803103
theorem B6875867 : Blo 1429534 6875867 := bstep (se 1 (by rfl) ⟨5156900, by rfl⟩ : syracuseStep 6875867 = 10313801) B10313801
theorem B27511913 : Blo 1429534 27511913 := bstep (se 2 (by rfl) ⟨10316967, by rfl⟩ : syracuseStep 27511913 = 20633935) B20633935
theorem B7245449 : Blo 1429534 7245449 := bstep (se 2 (by rfl) ⟨2717043, by rfl⟩ : syracuseStep 7245449 = 5434087) B5434087
theorem B19583279 : Blo 1429534 19583279 := bstep (se 1 (by rfl) ⟨14687459, by rfl⟩ : syracuseStep 19583279 = 29374919) B29374919
theorem B6877865 : Blo 1429534 6877865 := bstep (se 2 (by rfl) ⟨2579199, by rfl⟩ : syracuseStep 6877865 = 5158399) B5158399
theorem B22926557 : Blo 1429534 22926557 := bstep (se 3 (by rfl) ⟨4298729, by rfl⟩ : syracuseStep 22926557 = 8597459) B8597459
theorem B7337243 : Blo 1429534 7337243 := bstep (se 1 (by rfl) ⟨5502932, by rfl⟩ : syracuseStep 7337243 = 11005865) B11005865
theorem B6878519 : Blo 1429534 6878519 := bstep (se 1 (by rfl) ⟨5158889, by rfl⟩ : syracuseStep 6878519 = 10317779) B10317779
theorem B8149673 : Blo 1429534 8149673 := bstep (se 2 (by rfl) ⟨3056127, by rfl⟩ : syracuseStep 8149673 = 6112255) B6112255
theorem B3619849 : Blo 1429534 3619849 := bstep (se 2 (by rfl) ⟨1357443, by rfl⟩ : syracuseStep 3619849 = 2714887) B2714887
theorem B1809535 : Blo 1429534 1809535 := bstep (se 1 (by rfl) ⟨1357151, by rfl⟩ : syracuseStep 1809535 = 2714303) B2714303
theorem B3218687 : Blo 1429534 3218687 := bstep (se 1 (by rfl) ⟨2414015, by rfl⟩ : syracuseStep 3218687 = 4828031) B4828031
theorem B4826465 : Blo 1429534 4826465 := bstep (se 2 (by rfl) ⟨1809924, by rfl⟩ : syracuseStep 4826465 = 3619849) B3619849
theorem B5433115 : Blo 1429534 5433115 := bstep (se 1 (by rfl) ⟨4074836, by rfl⟩ : syracuseStep 5433115 = 8149673) B8149673
theorem B19565981 : Blo 1429534 19565981 := bstep (se 3 (by rfl) ⟨3668621, by rfl⟩ : syracuseStep 19565981 = 7337243) B7337243
theorem B2412713 : Blo 1429534 2412713 := bstep (se 2 (by rfl) ⟨904767, by rfl⟩ : syracuseStep 2412713 = 1809535) B1809535
theorem B4583911 : Blo 1429534 4583911 := bstep (se 1 (by rfl) ⟨3437933, by rfl⟩ : syracuseStep 4583911 = 6875867) B6875867
theorem B4830299 : Blo 1429534 4830299 := bstep (se 1 (by rfl) ⟨3622724, by rfl⟩ : syracuseStep 4830299 = 7245449) B7245449
theorem B5158313 : Blo 1429534 5158313 := bstep (se 2 (by rfl) ⟨1934367, by rfl⟩ : syracuseStep 5158313 = 3868735) B3868735
theorem B13055519 : Blo 1429534 13055519 := bstep (se 1 (by rfl) ⟨9791639, by rfl⟩ : syracuseStep 13055519 = 19583279) B19583279
theorem B4585243 : Blo 1429534 4585243 := bstep (se 1 (by rfl) ⟨3438932, by rfl⟩ : syracuseStep 4585243 = 6877865) B6877865
theorem B15284371 : Blo 1429534 15284371 := bstep (se 1 (by rfl) ⟨11463278, by rfl⟩ : syracuseStep 15284371 = 22926557) B22926557
theorem B4585679 : Blo 1429534 4585679 := bstep (se 1 (by rfl) ⟨3439259, by rfl⟩ : syracuseStep 4585679 = 6878519) B6878519
theorem B11754665 : Blo 1429534 11754665 := bstep (se 2 (by rfl) ⟨4407999, by rfl⟩ : syracuseStep 11754665 = 8815999) B8815999
theorem B18341275 : Blo 1429534 18341275 := bstep (se 1 (by rfl) ⟨13755956, by rfl⟩ : syracuseStep 18341275 = 27511913) B27511913
theorem B2145791 : Blo 1429534 2145791 := bstep (se 1 (by rfl) ⟨1609343, by rfl⟩ : syracuseStep 2145791 = 3218687) B3218687
theorem B6111881 : Blo 1429534 6111881 := bstep (se 2 (by rfl) ⟨2291955, by rfl⟩ : syracuseStep 6111881 = 4583911) B4583911
theorem B3220199 : Blo 1429534 3220199 := bstep (se 1 (by rfl) ⟨2415149, by rfl⟩ : syracuseStep 3220199 = 4830299) B4830299
theorem B3057119 : Blo 1429534 3057119 := bstep (se 1 (by rfl) ⟨2292839, by rfl⟩ : syracuseStep 3057119 = 4585679) B4585679
theorem B24455033 : Blo 1429534 24455033 := bstep (se 2 (by rfl) ⟨9170637, by rfl⟩ : syracuseStep 24455033 = 18341275) B18341275
theorem B13043987 : Blo 1429534 13043987 := bstep (se 1 (by rfl) ⟨9782990, by rfl⟩ : syracuseStep 13043987 = 19565981) B19565981
theorem B7244153 : Blo 1429534 7244153 := bstep (se 2 (by rfl) ⟨2716557, by rfl⟩ : syracuseStep 7244153 = 5433115) B5433115
theorem B6113657 : Blo 1429534 6113657 := bstep (se 2 (by rfl) ⟨2292621, by rfl⟩ : syracuseStep 6113657 = 4585243) B4585243
theorem B1608475 : Blo 1429534 1608475 := bstep (se 1 (by rfl) ⟨1206356, by rfl⟩ : syracuseStep 1608475 = 2412713) B2412713
theorem B7836443 : Blo 1429534 7836443 := bstep (se 1 (by rfl) ⟨5877332, by rfl⟩ : syracuseStep 7836443 = 11754665) B11754665
theorem B1430527 : Blo 1429534 1430527 := bstep (se 1 (by rfl) ⟨1072895, by rfl⟩ : syracuseStep 1430527 = 2145791) B2145791
theorem B20379161 : Blo 1429534 20379161 := bstep (se 2 (by rfl) ⟨7642185, by rfl⟩ : syracuseStep 20379161 = 15284371) B15284371
theorem B3217643 : Blo 1429534 3217643 := bstep (se 1 (by rfl) ⟨2413232, by rfl⟩ : syracuseStep 3217643 = 4826465) B4826465
theorem B3438875 : Blo 1429534 3438875 := bstep (se 1 (by rfl) ⟨2579156, by rfl⟩ : syracuseStep 3438875 = 5158313) B5158313
theorem B34814717 : Blo 1429534 34814717 := bstep (se 3 (by rfl) ⟨6527759, by rfl⟩ : syracuseStep 34814717 = 13055519) B13055519
theorem B2146799 : Blo 1429534 2146799 := bstep (se 1 (by rfl) ⟨1610099, by rfl⟩ : syracuseStep 2146799 = 3220199) B3220199
theorem B16303355 : Blo 1429534 16303355 := bstep (se 1 (by rfl) ⟨12227516, by rfl⟩ : syracuseStep 16303355 = 24455033) B24455033
theorem B23209811 : Blo 1429534 23209811 := bstep (se 1 (by rfl) ⟨17407358, by rfl⟩ : syracuseStep 23209811 = 34814717) B34814717
theorem B4074587 : Blo 1429534 4074587 := bstep (se 1 (by rfl) ⟨3055940, by rfl⟩ : syracuseStep 4074587 = 6111881) B6111881
theorem B9170333 : Blo 1429534 9170333 := bstep (se 3 (by rfl) ⟨1719437, by rfl⟩ : syracuseStep 9170333 = 3438875) B3438875
theorem B8695991 : Blo 1429534 8695991 := bstep (se 1 (by rfl) ⟨6521993, by rfl⟩ : syracuseStep 8695991 = 13043987) B13043987
theorem B4829435 : Blo 1429534 4829435 := bstep (se 1 (by rfl) ⟨3622076, by rfl⟩ : syracuseStep 4829435 = 7244153) B7244153
theorem B4075771 : Blo 1429534 4075771 := bstep (se 1 (by rfl) ⟨3056828, by rfl⟩ : syracuseStep 4075771 = 6113657) B6113657
theorem B5224295 : Blo 1429534 5224295 := bstep (se 1 (by rfl) ⟨3918221, by rfl⟩ : syracuseStep 5224295 = 7836443) B7836443
theorem B2038079 : Blo 1429534 2038079 := bstep (se 1 (by rfl) ⟨1528559, by rfl⟩ : syracuseStep 2038079 = 3057119) B3057119
theorem B2144633 : Blo 1429534 2144633 := bstep (se 2 (by rfl) ⟨804237, by rfl⟩ : syracuseStep 2144633 = 1608475) B1608475
theorem B54344429 : Blo 1429534 54344429 := bstep (se 3 (by rfl) ⟨10189580, by rfl⟩ : syracuseStep 54344429 = 20379161) B20379161
theorem B2145095 : Blo 1429534 2145095 := bstep (se 1 (by rfl) ⟨1608821, by rfl⟩ : syracuseStep 2145095 = 3217643) B3217643
theorem B3219623 : Blo 1429534 3219623 := bstep (se 1 (by rfl) ⟨2414717, by rfl⟩ : syracuseStep 3219623 = 4829435) B4829435
theorem B6113555 : Blo 1429534 6113555 := bstep (se 1 (by rfl) ⟨4585166, by rfl⟩ : syracuseStep 6113555 = 9170333) B9170333
theorem B5434361 : Blo 1429534 5434361 := bstep (se 2 (by rfl) ⟨2037885, by rfl⟩ : syracuseStep 5434361 = 4075771) B4075771
theorem B5434877 : Blo 1429534 5434877 := bstep (se 3 (by rfl) ⟨1019039, by rfl⟩ : syracuseStep 5434877 = 2038079) B2038079
theorem B1429755 : Blo 1429534 1429755 := bstep (se 1 (by rfl) ⟨1072316, by rfl⟩ : syracuseStep 1429755 = 2144633) B2144633
theorem B36229619 : Blo 1429534 36229619 := bstep (se 1 (by rfl) ⟨27172214, by rfl⟩ : syracuseStep 36229619 = 54344429) B54344429
theorem B1430063 : Blo 1429534 1430063 := bstep (se 1 (by rfl) ⟨1072547, by rfl⟩ : syracuseStep 1430063 = 2145095) B2145095
theorem B2716391 : Blo 1429534 2716391 := bstep (se 1 (by rfl) ⟨2037293, by rfl⟩ : syracuseStep 2716391 = 4074587) B4074587
theorem B13931453 : Blo 1429534 13931453 := bstep (se 3 (by rfl) ⟨2612147, by rfl⟩ : syracuseStep 13931453 = 5224295) B5224295
theorem B5797327 : Blo 1429534 5797327 := bstep (se 1 (by rfl) ⟨4347995, by rfl⟩ : syracuseStep 5797327 = 8695991) B8695991
theorem B1431199 : Blo 1429534 1431199 := bstep (se 1 (by rfl) ⟨1073399, by rfl⟩ : syracuseStep 1431199 = 2146799) B2146799
theorem B10868903 : Blo 1429534 10868903 := bstep (se 1 (by rfl) ⟨8151677, by rfl⟩ : syracuseStep 10868903 = 16303355) B16303355
theorem B15473207 : Blo 1429534 15473207 := bstep (se 1 (by rfl) ⟨11604905, by rfl⟩ : syracuseStep 15473207 = 23209811) B23209811
theorem B2146415 : Blo 1429534 2146415 := bstep (se 1 (by rfl) ⟨1609811, by rfl⟩ : syracuseStep 2146415 = 3219623) B3219623
theorem B1810927 : Blo 1429534 1810927 := bstep (se 1 (by rfl) ⟨1358195, by rfl⟩ : syracuseStep 1810927 = 2716391) B2716391
theorem B10315471 : Blo 1429534 10315471 := bstep (se 1 (by rfl) ⟨7736603, by rfl⟩ : syracuseStep 10315471 = 15473207) B15473207
theorem B3622907 : Blo 1429534 3622907 := bstep (se 1 (by rfl) ⟨2717180, by rfl⟩ : syracuseStep 3622907 = 5434361) B5434361
theorem B3623251 : Blo 1429534 3623251 := bstep (se 1 (by rfl) ⟨2717438, by rfl⟩ : syracuseStep 3623251 = 5434877) B5434877
theorem B24153079 : Blo 1429534 24153079 := bstep (se 1 (by rfl) ⟨18114809, by rfl⟩ : syracuseStep 24153079 = 36229619) B36229619
theorem B7245935 : Blo 1429534 7245935 := bstep (se 1 (by rfl) ⟨5434451, by rfl⟩ : syracuseStep 7245935 = 10868903) B10868903
theorem B4075703 : Blo 1429534 4075703 := bstep (se 1 (by rfl) ⟨3056777, by rfl⟩ : syracuseStep 4075703 = 6113555) B6113555
theorem B7729769 : Blo 1429534 7729769 := bstep (se 2 (by rfl) ⟨2898663, by rfl⟩ : syracuseStep 7729769 = 5797327) B5797327
theorem B9287635 : Blo 1429534 9287635 := bstep (se 1 (by rfl) ⟨6965726, by rfl⟩ : syracuseStep 9287635 = 13931453) B13931453
theorem B32204105 : Blo 1429534 32204105 := bstep (se 2 (by rfl) ⟨12076539, by rfl⟩ : syracuseStep 32204105 = 24153079) B24153079
theorem B20612717 : Blo 1429534 20612717 := bstep (se 3 (by rfl) ⟨3864884, by rfl⟩ : syracuseStep 20612717 = 7729769) B7729769
theorem B12383513 : Blo 1429534 12383513 := bstep (se 2 (by rfl) ⟨4643817, by rfl⟩ : syracuseStep 12383513 = 9287635) B9287635
theorem B1430943 : Blo 1429534 1430943 := bstep (se 1 (by rfl) ⟨1073207, by rfl⟩ : syracuseStep 1430943 = 2146415) B2146415
theorem B4830623 : Blo 1429534 4830623 := bstep (se 1 (by rfl) ⟨3622967, by rfl⟩ : syracuseStep 4830623 = 7245935) B7245935
theorem B2717135 : Blo 1429534 2717135 := bstep (se 1 (by rfl) ⟨2037851, by rfl⟩ : syracuseStep 2717135 = 4075703) B4075703
theorem B4831001 : Blo 1429534 4831001 := bstep (se 2 (by rfl) ⟨1811625, by rfl⟩ : syracuseStep 4831001 = 3623251) B3623251
theorem B2414569 : Blo 1429534 2414569 := bstep (se 2 (by rfl) ⟨905463, by rfl⟩ : syracuseStep 2414569 = 1810927) B1810927
theorem B2415271 : Blo 1429534 2415271 := bstep (se 1 (by rfl) ⟨1811453, by rfl⟩ : syracuseStep 2415271 = 3622907) B3622907
theorem B13753961 : Blo 1429534 13753961 := bstep (se 2 (by rfl) ⟨5157735, by rfl⟩ : syracuseStep 13753961 = 10315471) B10315471
theorem B3220361 : Blo 1429534 3220361 := bstep (se 2 (by rfl) ⟨1207635, by rfl⟩ : syracuseStep 3220361 = 2415271) B2415271
theorem B3220415 : Blo 1429534 3220415 := bstep (se 1 (by rfl) ⟨2415311, by rfl⟩ : syracuseStep 3220415 = 4830623) B4830623
theorem B1811423 : Blo 1429534 1811423 := bstep (se 1 (by rfl) ⟨1358567, by rfl⟩ : syracuseStep 1811423 = 2717135) B2717135
theorem B3220667 : Blo 1429534 3220667 := bstep (se 1 (by rfl) ⟨2415500, by rfl⟩ : syracuseStep 3220667 = 4831001) B4831001
theorem B9169307 : Blo 1429534 9169307 := bstep (se 1 (by rfl) ⟨6876980, by rfl⟩ : syracuseStep 9169307 = 13753961) B13753961
theorem B13741811 : Blo 1429534 13741811 := bstep (se 1 (by rfl) ⟨10306358, by rfl⟩ : syracuseStep 13741811 = 20612717) B20612717
theorem B8255675 : Blo 1429534 8255675 := bstep (se 1 (by rfl) ⟨6191756, by rfl⟩ : syracuseStep 8255675 = 12383513) B12383513
theorem B21469403 : Blo 1429534 21469403 := bstep (se 1 (by rfl) ⟨16102052, by rfl⟩ : syracuseStep 21469403 = 32204105) B32204105
theorem B3219425 : Blo 1429534 3219425 := bstep (se 2 (by rfl) ⟨1207284, by rfl⟩ : syracuseStep 3219425 = 2414569) B2414569
theorem B2146907 : Blo 1429534 2146907 := bstep (se 1 (by rfl) ⟨1610180, by rfl⟩ : syracuseStep 2146907 = 3220361) B3220361
theorem B2146943 : Blo 1429534 2146943 := bstep (se 1 (by rfl) ⟨1610207, by rfl⟩ : syracuseStep 2146943 = 3220415) B3220415
theorem B2147111 : Blo 1429534 2147111 := bstep (se 1 (by rfl) ⟨1610333, by rfl⟩ : syracuseStep 2147111 = 3220667) B3220667
theorem B14312935 : Blo 1429534 14312935 := bstep (se 1 (by rfl) ⟨10734701, by rfl⟩ : syracuseStep 14312935 = 21469403) B21469403
theorem B6112871 : Blo 1429534 6112871 := bstep (se 1 (by rfl) ⟨4584653, by rfl⟩ : syracuseStep 6112871 = 9169307) B9169307
theorem B9161207 : Blo 1429534 9161207 := bstep (se 1 (by rfl) ⟨6870905, by rfl⟩ : syracuseStep 9161207 = 13741811) B13741811
theorem B4830461 : Blo 1429534 4830461 := bstep (se 3 (by rfl) ⟨905711, by rfl⟩ : syracuseStep 4830461 = 1811423) B1811423
theorem B5503783 : Blo 1429534 5503783 := bstep (se 1 (by rfl) ⟨4127837, by rfl⟩ : syracuseStep 5503783 = 8255675) B8255675
theorem B2146283 : Blo 1429534 2146283 := bstep (se 1 (by rfl) ⟨1609712, by rfl⟩ : syracuseStep 2146283 = 3219425) B3219425
theorem B3220307 : Blo 1429534 3220307 := bstep (se 1 (by rfl) ⟨2415230, by rfl⟩ : syracuseStep 3220307 = 4830461) B4830461
theorem B76335653 : Blo 1429534 76335653 := bstep (se 4 (by rfl) ⟨7156467, by rfl⟩ : syracuseStep 76335653 = 14312935) B14312935
theorem B4075247 : Blo 1429534 4075247 := bstep (se 1 (by rfl) ⟨3056435, by rfl⟩ : syracuseStep 4075247 = 6112871) B6112871
theorem B6107471 : Blo 1429534 6107471 := bstep (se 1 (by rfl) ⟨4580603, by rfl⟩ : syracuseStep 6107471 = 9161207) B9161207
theorem B1430855 : Blo 1429534 1430855 := bstep (se 1 (by rfl) ⟨1073141, by rfl⟩ : syracuseStep 1430855 = 2146283) B2146283
theorem B1431271 : Blo 1429534 1431271 := bstep (se 1 (by rfl) ⟨1073453, by rfl⟩ : syracuseStep 1431271 = 2146907) B2146907
theorem B1431295 : Blo 1429534 1431295 := bstep (se 1 (by rfl) ⟨1073471, by rfl⟩ : syracuseStep 1431295 = 2146943) B2146943
theorem B1431407 : Blo 1429534 1431407 := bstep (se 1 (by rfl) ⟨1073555, by rfl⟩ : syracuseStep 1431407 = 2147111) B2147111
theorem B7338377 : Blo 1429534 7338377 := bstep (se 2 (by rfl) ⟨2751891, by rfl⟩ : syracuseStep 7338377 = 5503783) B5503783
theorem B4071647 : Blo 1429534 4071647 := bstep (se 1 (by rfl) ⟨3053735, by rfl⟩ : syracuseStep 4071647 = 6107471) B6107471
theorem B2146871 : Blo 1429534 2146871 := bstep (se 1 (by rfl) ⟨1610153, by rfl⟩ : syracuseStep 2146871 = 3220307) B3220307
theorem B4892251 : Blo 1429534 4892251 := bstep (se 1 (by rfl) ⟨3669188, by rfl⟩ : syracuseStep 4892251 = 7338377) B7338377
theorem B2716831 : Blo 1429534 2716831 := bstep (se 1 (by rfl) ⟨2037623, by rfl⟩ : syracuseStep 2716831 = 4075247) B4075247
theorem B203561741 : Blo 1429534 203561741 := bstep (se 3 (by rfl) ⟨38167826, by rfl⟩ : syracuseStep 203561741 = 76335653) B76335653
theorem B3622441 : Blo 1429534 3622441 := bstep (se 2 (by rfl) ⟨1358415, by rfl⟩ : syracuseStep 3622441 = 2716831) B2716831
theorem B6523001 : Blo 1429534 6523001 := bstep (se 2 (by rfl) ⟨2446125, by rfl⟩ : syracuseStep 6523001 = 4892251) B4892251
theorem B10857725 : Blo 1429534 10857725 := bstep (se 3 (by rfl) ⟨2035823, by rfl⟩ : syracuseStep 10857725 = 4071647) B4071647
theorem B1431247 : Blo 1429534 1431247 := bstep (se 1 (by rfl) ⟨1073435, by rfl⟩ : syracuseStep 1431247 = 2146871) B2146871
theorem B135707827 : Blo 1429534 135707827 := bstep (se 1 (by rfl) ⟨101780870, by rfl⟩ : syracuseStep 135707827 = 203561741) B203561741
theorem B4829921 : Blo 1429534 4829921 := bstep (se 2 (by rfl) ⟨1811220, by rfl⟩ : syracuseStep 4829921 = 3622441) B3622441
theorem B7238483 : Blo 1429534 7238483 := bstep (se 1 (by rfl) ⟨5428862, by rfl⟩ : syracuseStep 7238483 = 10857725) B10857725
theorem B4348667 : Blo 1429534 4348667 := bstep (se 1 (by rfl) ⟨3261500, by rfl⟩ : syracuseStep 4348667 = 6523001) B6523001
theorem B180943769 : Blo 1429534 180943769 := bstep (se 2 (by rfl) ⟨67853913, by rfl⟩ : syracuseStep 180943769 = 135707827) B135707827
theorem B3219947 : Blo 1429534 3219947 := bstep (se 1 (by rfl) ⟨2414960, by rfl⟩ : syracuseStep 3219947 = 4829921) B4829921
theorem B4825655 : Blo 1429534 4825655 := bstep (se 1 (by rfl) ⟨3619241, by rfl⟩ : syracuseStep 4825655 = 7238483) B7238483
theorem B120629179 : Blo 1429534 120629179 := bstep (se 1 (by rfl) ⟨90471884, by rfl⟩ : syracuseStep 120629179 = 180943769) B180943769
theorem B11596445 : Blo 1429534 11596445 := bstep (se 3 (by rfl) ⟨2174333, by rfl⟩ : syracuseStep 11596445 = 4348667) B4348667
theorem B2146631 : Blo 1429534 2146631 := bstep (se 1 (by rfl) ⟨1609973, by rfl⟩ : syracuseStep 2146631 = 3219947) B3219947
theorem B643355621 : Blo 1429534 643355621 := bstep (se 4 (by rfl) ⟨60314589, by rfl⟩ : syracuseStep 643355621 = 120629179) B120629179
theorem B3217103 : Blo 1429534 3217103 := bstep (se 1 (by rfl) ⟨2412827, by rfl⟩ : syracuseStep 3217103 = 4825655) B4825655
theorem B7730963 : Blo 1429534 7730963 := bstep (se 1 (by rfl) ⟨5798222, by rfl⟩ : syracuseStep 7730963 = 11596445) B11596445
theorem B5153975 : Blo 1429534 5153975 := bstep (se 1 (by rfl) ⟨3865481, by rfl⟩ : syracuseStep 5153975 = 7730963) B7730963
theorem B428903747 : Blo 1429534 428903747 := bstep (se 1 (by rfl) ⟨321677810, by rfl⟩ : syracuseStep 428903747 = 643355621) B643355621
theorem B1431087 : Blo 1429534 1431087 := bstep (se 1 (by rfl) ⟨1073315, by rfl⟩ : syracuseStep 1431087 = 2146631) B2146631
theorem B2144735 : Blo 1429534 2144735 := bstep (se 1 (by rfl) ⟨1608551, by rfl⟩ : syracuseStep 2144735 = 3217103) B3217103
theorem B285935831 : Blo 1429534 285935831 := bstep (se 1 (by rfl) ⟨214451873, by rfl⟩ : syracuseStep 285935831 = 428903747) B428903747
theorem B3435983 : Blo 1429534 3435983 := bstep (se 1 (by rfl) ⟨2576987, by rfl⟩ : syracuseStep 3435983 = 5153975) B5153975
theorem B1429823 : Blo 1429534 1429823 := bstep (se 1 (by rfl) ⟨1072367, by rfl⟩ : syracuseStep 1429823 = 2144735) B2144735
theorem B190623887 : Blo 1429534 190623887 := bstep (se 1 (by rfl) ⟨142967915, by rfl⟩ : syracuseStep 190623887 = 285935831) B285935831
theorem B2290655 : Blo 1429534 2290655 := bstep (se 1 (by rfl) ⟨1717991, by rfl⟩ : syracuseStep 2290655 = 3435983) B3435983
theorem B127082591 : Blo 1429534 127082591 := bstep (se 1 (by rfl) ⟨95311943, by rfl⟩ : syracuseStep 127082591 = 190623887) B190623887
theorem B1527103 : Blo 1429534 1527103 := bstep (se 1 (by rfl) ⟨1145327, by rfl⟩ : syracuseStep 1527103 = 2290655) B2290655
theorem B84721727 : Blo 1429534 84721727 := bstep (se 1 (by rfl) ⟨63541295, by rfl⟩ : syracuseStep 84721727 = 127082591) B127082591
theorem B8144549 : Blo 1429534 8144549 := bstep (se 4 (by rfl) ⟨763551, by rfl⟩ : syracuseStep 8144549 = 1527103) B1527103
theorem B56481151 : Blo 1429534 56481151 := bstep (se 1 (by rfl) ⟨42360863, by rfl⟩ : syracuseStep 56481151 = 84721727) B84721727
theorem B5429699 : Blo 1429534 5429699 := bstep (se 1 (by rfl) ⟨4072274, by rfl⟩ : syracuseStep 5429699 = 8144549) B8144549
theorem B3619799 : Blo 1429534 3619799 := bstep (se 1 (by rfl) ⟨2714849, by rfl⟩ : syracuseStep 3619799 = 5429699) B5429699
theorem B75308201 : Blo 1429534 75308201 := bstep (se 2 (by rfl) ⟨28240575, by rfl⟩ : syracuseStep 75308201 = 56481151) B56481151
theorem B2413199 : Blo 1429534 2413199 := bstep (se 1 (by rfl) ⟨1809899, by rfl⟩ : syracuseStep 2413199 = 3619799) B3619799
theorem B50205467 : Blo 1429534 50205467 := bstep (se 1 (by rfl) ⟨37654100, by rfl⟩ : syracuseStep 50205467 = 75308201) B75308201
theorem B1608799 : Blo 1429534 1608799 := bstep (se 1 (by rfl) ⟨1206599, by rfl⟩ : syracuseStep 1608799 = 2413199) B2413199
theorem B133881245 : Blo 1429534 133881245 := bstep (se 3 (by rfl) ⟨25102733, by rfl⟩ : syracuseStep 133881245 = 50205467) B50205467
theorem B89254163 : Blo 1429534 89254163 := bstep (se 1 (by rfl) ⟨66940622, by rfl⟩ : syracuseStep 89254163 = 133881245) B133881245
theorem B2145065 : Blo 1429534 2145065 := bstep (se 2 (by rfl) ⟨804399, by rfl⟩ : syracuseStep 2145065 = 1608799) B1608799
theorem B59502775 : Blo 1429534 59502775 := bstep (se 1 (by rfl) ⟨44627081, by rfl⟩ : syracuseStep 59502775 = 89254163) B89254163
theorem B1430043 : Blo 1429534 1430043 := bstep (se 1 (by rfl) ⟨1072532, by rfl⟩ : syracuseStep 1430043 = 2145065) B2145065
theorem B79337033 : Blo 1429534 79337033 := bstep (se 2 (by rfl) ⟨29751387, by rfl⟩ : syracuseStep 79337033 = 59502775) B59502775
theorem B52891355 : Blo 1429534 52891355 := bstep (se 1 (by rfl) ⟨39668516, by rfl⟩ : syracuseStep 52891355 = 79337033) B79337033
theorem B35260903 : Blo 1429534 35260903 := bstep (se 1 (by rfl) ⟨26445677, by rfl⟩ : syracuseStep 35260903 = 52891355) B52891355
theorem B188058149 : Blo 1429534 188058149 := bstep (se 4 (by rfl) ⟨17630451, by rfl⟩ : syracuseStep 188058149 = 35260903) B35260903
theorem B125372099 : Blo 1429534 125372099 := bstep (se 1 (by rfl) ⟨94029074, by rfl⟩ : syracuseStep 125372099 = 188058149) B188058149
theorem B83581399 : Blo 1429534 83581399 := bstep (se 1 (by rfl) ⟨62686049, by rfl⟩ : syracuseStep 83581399 = 125372099) B125372099
theorem B111441865 : Blo 1429534 111441865 := bstep (se 2 (by rfl) ⟨41790699, by rfl⟩ : syracuseStep 111441865 = 83581399) B83581399
theorem B148589153 : Blo 1429534 148589153 := bstep (se 2 (by rfl) ⟨55720932, by rfl⟩ : syracuseStep 148589153 = 111441865) B111441865
theorem B99059435 : Blo 1429534 99059435 := bstep (se 1 (by rfl) ⟨74294576, by rfl⟩ : syracuseStep 99059435 = 148589153) B148589153
theorem B66039623 : Blo 1429534 66039623 := bstep (se 1 (by rfl) ⟨49529717, by rfl⟩ : syracuseStep 66039623 = 99059435) B99059435
theorem B44026415 : Blo 1429534 44026415 := bstep (se 1 (by rfl) ⟨33019811, by rfl⟩ : syracuseStep 44026415 = 66039623) B66039623
theorem B29350943 : Blo 1429534 29350943 := bstep (se 1 (by rfl) ⟨22013207, by rfl⟩ : syracuseStep 29350943 = 44026415) B44026415
theorem B19567295 : Blo 1429534 19567295 := bstep (se 1 (by rfl) ⟨14675471, by rfl⟩ : syracuseStep 19567295 = 29350943) B29350943
theorem B13044863 : Blo 1429534 13044863 := bstep (se 1 (by rfl) ⟨9783647, by rfl⟩ : syracuseStep 13044863 = 19567295) B19567295
theorem B8696575 : Blo 1429534 8696575 := bstep (se 1 (by rfl) ⟨6522431, by rfl⟩ : syracuseStep 8696575 = 13044863) B13044863
theorem B11595433 : Blo 1429534 11595433 := bstep (se 2 (by rfl) ⟨4348287, by rfl⟩ : syracuseStep 11595433 = 8696575) B8696575
theorem B15460577 : Blo 1429534 15460577 := bstep (se 2 (by rfl) ⟨5797716, by rfl⟩ : syracuseStep 15460577 = 11595433) B11595433
theorem B10307051 : Blo 1429534 10307051 := bstep (se 1 (by rfl) ⟨7730288, by rfl⟩ : syracuseStep 10307051 = 15460577) B15460577
theorem B6871367 : Blo 1429534 6871367 := bstep (se 1 (by rfl) ⟨5153525, by rfl⟩ : syracuseStep 6871367 = 10307051) B10307051
theorem B4580911 : Blo 1429534 4580911 := bstep (se 1 (by rfl) ⟨3435683, by rfl⟩ : syracuseStep 4580911 = 6871367) B6871367
theorem B6107881 : Blo 1429534 6107881 := bstep (se 2 (by rfl) ⟨2290455, by rfl⟩ : syracuseStep 6107881 = 4580911) B4580911
theorem B8143841 : Blo 1429534 8143841 := bstep (se 2 (by rfl) ⟨3053940, by rfl⟩ : syracuseStep 8143841 = 6107881) B6107881
theorem B5429227 : Blo 1429534 5429227 := bstep (se 1 (by rfl) ⟨4071920, by rfl⟩ : syracuseStep 5429227 = 8143841) B8143841
theorem B7238969 : Blo 1429534 7238969 := bstep (se 2 (by rfl) ⟨2714613, by rfl⟩ : syracuseStep 7238969 = 5429227) B5429227
theorem B4825979 : Blo 1429534 4825979 := bstep (se 1 (by rfl) ⟨3619484, by rfl⟩ : syracuseStep 4825979 = 7238969) B7238969
theorem B3217319 : Blo 1429534 3217319 := bstep (se 1 (by rfl) ⟨2412989, by rfl⟩ : syracuseStep 3217319 = 4825979) B4825979
theorem B2144879 : Blo 1429534 2144879 := bstep (se 1 (by rfl) ⟨1608659, by rfl⟩ : syracuseStep 2144879 = 3217319) B3217319
theorem B1429919 : Blo 1429534 1429919 := bstep (se 1 (by rfl) ⟨1072439, by rfl⟩ : syracuseStep 1429919 = 2144879) B2144879

theorem C0 (j : ℕ) (h1 : 357383 ≤ j) (h2 : j ≤ 357882) : Blo 1429534 (4 * j + 3) := by
  interval_cases j
  · exact B1429535
  · exact B1429539
  · exact B1429543
  · exact B1429547
  · exact B1429551
  · exact B1429555
  · exact B1429559
  · exact B1429563
  · exact B1429567
  · exact B1429571
  · exact B1429575
  · exact B1429579
  · exact B1429583
  · exact B1429587
  · exact B1429591
  · exact B1429595
  · exact B1429599
  · exact B1429603
  · exact B1429607
  · exact B1429611
  · exact B1429615
  · exact B1429619
  · exact B1429623
  · exact B1429627
  · exact B1429631
  · exact B1429635
  · exact B1429639
  · exact B1429643
  · exact B1429647
  · exact B1429651
  · exact B1429655
  · exact B1429659
  · exact B1429663
  · exact B1429667
  · exact B1429671
  · exact B1429675
  · exact B1429679
  · exact B1429683
  · exact B1429687
  · exact B1429691
  · exact B1429695
  · exact B1429699
  · exact B1429703
  · exact B1429707
  · exact B1429711
  · exact B1429715
  · exact B1429719
  · exact B1429723
  · exact B1429727
  · exact B1429731
  · exact B1429735
  · exact B1429739
  · exact B1429743
  · exact B1429747
  · exact B1429751
  · exact B1429755
  · exact B1429759
  · exact B1429763
  · exact B1429767
  · exact B1429771
  · exact B1429775
  · exact B1429779
  · exact B1429783
  · exact B1429787
  · exact B1429791
  · exact B1429795
  · exact B1429799
  · exact B1429803
  · exact B1429807
  · exact B1429811
  · exact B1429815
  · exact B1429819
  · exact B1429823
  · exact B1429827
  · exact B1429831
  · exact B1429835
  · exact B1429839
  · exact B1429843
  · exact B1429847
  · exact B1429851
  · exact B1429855
  · exact B1429859
  · exact B1429863
  · exact B1429867
  · exact B1429871
  · exact B1429875
  · exact B1429879
  · exact B1429883
  · exact B1429887
  · exact B1429891
  · exact B1429895
  · exact B1429899
  · exact B1429903
  · exact B1429907
  · exact B1429911
  · exact B1429915
  · exact B1429919
  · exact B1429923
  · exact B1429927
  · exact B1429931
  · exact B1429935
  · exact B1429939
  · exact B1429943
  · exact B1429947
  · exact B1429951
  · exact B1429955
  · exact B1429959
  · exact B1429963
  · exact B1429967
  · exact B1429971
  · exact B1429975
  · exact B1429979
  · exact B1429983
  · exact B1429987
  · exact B1429991
  · exact B1429995
  · exact B1429999
  · exact B1430003
  · exact B1430007
  · exact B1430011
  · exact B1430015
  · exact B1430019
  · exact B1430023
  · exact B1430027
  · exact B1430031
  · exact B1430035
  · exact B1430039
  · exact B1430043
  · exact B1430047
  · exact B1430051
  · exact B1430055
  · exact B1430059
  · exact B1430063
  · exact B1430067
  · exact B1430071
  · exact B1430075
  · exact B1430079
  · exact B1430083
  · exact B1430087
  · exact B1430091
  · exact B1430095
  · exact B1430099
  · exact B1430103
  · exact B1430107
  · exact B1430111
  · exact B1430115
  · exact B1430119
  · exact B1430123
  · exact B1430127
  · exact B1430131
  · exact B1430135
  · exact B1430139
  · exact B1430143
  · exact B1430147
  · exact B1430151
  · exact B1430155
  · exact B1430159
  · exact B1430163
  · exact B1430167
  · exact B1430171
  · exact B1430175
  · exact B1430179
  · exact B1430183
  · exact B1430187
  · exact B1430191
  · exact B1430195
  · exact B1430199
  · exact B1430203
  · exact B1430207
  · exact B1430211
  · exact B1430215
  · exact B1430219
  · exact B1430223
  · exact B1430227
  · exact B1430231
  · exact B1430235
  · exact B1430239
  · exact B1430243
  · exact B1430247
  · exact B1430251
  · exact B1430255
  · exact B1430259
  · exact B1430263
  · exact B1430267
  · exact B1430271
  · exact B1430275
  · exact B1430279
  · exact B1430283
  · exact B1430287
  · exact B1430291
  · exact B1430295
  · exact B1430299
  · exact B1430303
  · exact B1430307
  · exact B1430311
  · exact B1430315
  · exact B1430319
  · exact B1430323
  · exact B1430327
  · exact B1430331
  · exact B1430335
  · exact B1430339
  · exact B1430343
  · exact B1430347
  · exact B1430351
  · exact B1430355
  · exact B1430359
  · exact B1430363
  · exact B1430367
  · exact B1430371
  · exact B1430375
  · exact B1430379
  · exact B1430383
  · exact B1430387
  · exact B1430391
  · exact B1430395
  · exact B1430399
  · exact B1430403
  · exact B1430407
  · exact B1430411
  · exact B1430415
  · exact B1430419
  · exact B1430423
  · exact B1430427
  · exact B1430431
  · exact B1430435
  · exact B1430439
  · exact B1430443
  · exact B1430447
  · exact B1430451
  · exact B1430455
  · exact B1430459
  · exact B1430463
  · exact B1430467
  · exact B1430471
  · exact B1430475
  · exact B1430479
  · exact B1430483
  · exact B1430487
  · exact B1430491
  · exact B1430495
  · exact B1430499
  · exact B1430503
  · exact B1430507
  · exact B1430511
  · exact B1430515
  · exact B1430519
  · exact B1430523
  · exact B1430527
  · exact B1430531
  · exact B1430535
  · exact B1430539
  · exact B1430543
  · exact B1430547
  · exact B1430551
  · exact B1430555
  · exact B1430559
  · exact B1430563
  · exact B1430567
  · exact B1430571
  · exact B1430575
  · exact B1430579
  · exact B1430583
  · exact B1430587
  · exact B1430591
  · exact B1430595
  · exact B1430599
  · exact B1430603
  · exact B1430607
  · exact B1430611
  · exact B1430615
  · exact B1430619
  · exact B1430623
  · exact B1430627
  · exact B1430631
  · exact B1430635
  · exact B1430639
  · exact B1430643
  · exact B1430647
  · exact B1430651
  · exact B1430655
  · exact B1430659
  · exact B1430663
  · exact B1430667
  · exact B1430671
  · exact B1430675
  · exact B1430679
  · exact B1430683
  · exact B1430687
  · exact B1430691
  · exact B1430695
  · exact B1430699
  · exact B1430703
  · exact B1430707
  · exact B1430711
  · exact B1430715
  · exact B1430719
  · exact B1430723
  · exact B1430727
  · exact B1430731
  · exact B1430735
  · exact B1430739
  · exact B1430743
  · exact B1430747
  · exact B1430751
  · exact B1430755
  · exact B1430759
  · exact B1430763
  · exact B1430767
  · exact B1430771
  · exact B1430775
  · exact B1430779
  · exact B1430783
  · exact B1430787
  · exact B1430791
  · exact B1430795
  · exact B1430799
  · exact B1430803
  · exact B1430807
  · exact B1430811
  · exact B1430815
  · exact B1430819
  · exact B1430823
  · exact B1430827
  · exact B1430831
  · exact B1430835
  · exact B1430839
  · exact B1430843
  · exact B1430847
  · exact B1430851
  · exact B1430855
  · exact B1430859
  · exact B1430863
  · exact B1430867
  · exact B1430871
  · exact B1430875
  · exact B1430879
  · exact B1430883
  · exact B1430887
  · exact B1430891
  · exact B1430895
  · exact B1430899
  · exact B1430903
  · exact B1430907
  · exact B1430911
  · exact B1430915
  · exact B1430919
  · exact B1430923
  · exact B1430927
  · exact B1430931
  · exact B1430935
  · exact B1430939
  · exact B1430943
  · exact B1430947
  · exact B1430951
  · exact B1430955
  · exact B1430959
  · exact B1430963
  · exact B1430967
  · exact B1430971
  · exact B1430975
  · exact B1430979
  · exact B1430983
  · exact B1430987
  · exact B1430991
  · exact B1430995
  · exact B1430999
  · exact B1431003
  · exact B1431007
  · exact B1431011
  · exact B1431015
  · exact B1431019
  · exact B1431023
  · exact B1431027
  · exact B1431031
  · exact B1431035
  · exact B1431039
  · exact B1431043
  · exact B1431047
  · exact B1431051
  · exact B1431055
  · exact B1431059
  · exact B1431063
  · exact B1431067
  · exact B1431071
  · exact B1431075
  · exact B1431079
  · exact B1431083
  · exact B1431087
  · exact B1431091
  · exact B1431095
  · exact B1431099
  · exact B1431103
  · exact B1431107
  · exact B1431111
  · exact B1431115
  · exact B1431119
  · exact B1431123
  · exact B1431127
  · exact B1431131
  · exact B1431135
  · exact B1431139
  · exact B1431143
  · exact B1431147
  · exact B1431151
  · exact B1431155
  · exact B1431159
  · exact B1431163
  · exact B1431167
  · exact B1431171
  · exact B1431175
  · exact B1431179
  · exact B1431183
  · exact B1431187
  · exact B1431191
  · exact B1431195
  · exact B1431199
  · exact B1431203
  · exact B1431207
  · exact B1431211
  · exact B1431215
  · exact B1431219
  · exact B1431223
  · exact B1431227
  · exact B1431231
  · exact B1431235
  · exact B1431239
  · exact B1431243
  · exact B1431247
  · exact B1431251
  · exact B1431255
  · exact B1431259
  · exact B1431263
  · exact B1431267
  · exact B1431271
  · exact B1431275
  · exact B1431279
  · exact B1431283
  · exact B1431287
  · exact B1431291
  · exact B1431295
  · exact B1431299
  · exact B1431303
  · exact B1431307
  · exact B1431311
  · exact B1431315
  · exact B1431319
  · exact B1431323
  · exact B1431327
  · exact B1431331
  · exact B1431335
  · exact B1431339
  · exact B1431343
  · exact B1431347
  · exact B1431351
  · exact B1431355
  · exact B1431359
  · exact B1431363
  · exact B1431367
  · exact B1431371
  · exact B1431375
  · exact B1431379
  · exact B1431383
  · exact B1431387
  · exact B1431391
  · exact B1431395
  · exact B1431399
  · exact B1431403
  · exact B1431407
  · exact B1431411
  · exact B1431415
  · exact B1431419
  · exact B1431423
  · exact B1431427
  · exact B1431431
  · exact B1431435
  · exact B1431439
  · exact B1431443
  · exact B1431447
  · exact B1431451
  · exact B1431455
  · exact B1431459
  · exact B1431463
  · exact B1431467
  · exact B1431471
  · exact B1431475
  · exact B1431479
  · exact B1431483
  · exact B1431487
  · exact B1431491
  · exact B1431495
  · exact B1431499
  · exact B1431503
  · exact B1431507
  · exact B1431511
  · exact B1431515
  · exact B1431519
  · exact B1431523
  · exact B1431527
  · exact B1431531

theorem solution (m : ℕ) (hlo : 1429534 ≤ m) (hhi : m ≤ 1431534) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 357383 ≤ j := by omega
    have hj2 : j ≤ 357882 := by omega
    have hb : Blo 1429534 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
