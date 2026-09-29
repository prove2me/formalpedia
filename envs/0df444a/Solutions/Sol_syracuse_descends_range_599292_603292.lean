-- Prove2me | solution 1 for syracuse_descends_range_599292_603292
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:28.522317+00:00
-- url     : https://prove2.me/submissions/c541d490-7d2f-4cfb-a235-35146f6d0c99

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


theorem B1015861 : Blo 599292 1015861 := bbase (se 5 (by rfl) ⟨47618, by rfl⟩ : syracuseStep 1015861 = 95237) (by norm_num)
theorem B2031749 : Blo 599292 2031749 := bbase (se 4 (by rfl) ⟨190476, by rfl⟩ : syracuseStep 2031749 = 380953) (by norm_num)
theorem B1015949 : Blo 599292 1015949 := bbase (se 3 (by rfl) ⟨190490, by rfl⟩ : syracuseStep 1015949 = 380981) (by norm_num)
theorem B2162933 : Blo 599292 2162933 := bbase (se 5 (by rfl) ⟨101387, by rfl⟩ : syracuseStep 2162933 = 202775) (by norm_num)
theorem B1016077 : Blo 599292 1016077 := bbase (se 3 (by rfl) ⟨190514, by rfl⟩ : syracuseStep 1016077 = 381029) (by norm_num)
theorem B5144917 : Blo 599292 5144917 := bbase (se 10 (by rfl) ⟨7536, by rfl⟩ : syracuseStep 5144917 = 15073) (by norm_num)
theorem B1016165 : Blo 599292 1016165 := bbase (se 4 (by rfl) ⟨95265, by rfl⟩ : syracuseStep 1016165 = 190531) (by norm_num)
theorem B1016293 : Blo 599292 1016293 := bbase (se 4 (by rfl) ⟨95277, by rfl⟩ : syracuseStep 1016293 = 190555) (by norm_num)
theorem B2032181 : Blo 599292 2032181 := bbase (se 5 (by rfl) ⟨95258, by rfl⟩ : syracuseStep 2032181 = 190517) (by norm_num)
theorem B1016381 : Blo 599292 1016381 := bbase (se 3 (by rfl) ⟨190571, by rfl⟩ : syracuseStep 1016381 = 381143) (by norm_num)
theorem B721477 : Blo 599292 721477 := bbase (se 4 (by rfl) ⟨67638, by rfl⟩ : syracuseStep 721477 = 135277) (by norm_num)
theorem B1016509 : Blo 599292 1016509 := bbase (se 3 (by rfl) ⟨190595, by rfl⟩ : syracuseStep 1016509 = 381191) (by norm_num)
theorem B1442549 : Blo 599292 1442549 := bbase (se 5 (by rfl) ⟨67619, by rfl⟩ : syracuseStep 1442549 = 135239) (by norm_num)
theorem B1016597 : Blo 599292 1016597 := bbase (se 6 (by rfl) ⟨23826, by rfl⟩ : syracuseStep 1016597 = 47653) (by norm_num)
theorem B721693 : Blo 599292 721693 := bbase (se 3 (by rfl) ⟨135317, by rfl⟩ : syracuseStep 721693 = 270635) (by norm_num)
theorem B2163509 : Blo 599292 2163509 := bbase (se 5 (by rfl) ⟨101414, by rfl⟩ : syracuseStep 2163509 = 202829) (by norm_num)
theorem B1082173 : Blo 599292 1082173 := bbase (se 3 (by rfl) ⟨202907, by rfl⟩ : syracuseStep 1082173 = 405815) (by norm_num)
theorem B1540949 : Blo 599292 1540949 := bbase (se 9 (by rfl) ⟨4514, by rfl⟩ : syracuseStep 1540949 = 9029) (by norm_num)
theorem B1016725 : Blo 599292 1016725 := bbase (se 6 (by rfl) ⟨23829, by rfl⟩ : syracuseStep 1016725 = 47659) (by norm_num)
theorem B2032613 : Blo 599292 2032613 := bbase (se 4 (by rfl) ⟨190557, by rfl⟩ : syracuseStep 2032613 = 381115) (by norm_num)
theorem B1016813 : Blo 599292 1016813 := bbase (se 3 (by rfl) ⟨190652, by rfl⟩ : syracuseStep 1016813 = 381305) (by norm_num)
theorem B1016941 : Blo 599292 1016941 := bbase (se 3 (by rfl) ⟨190676, by rfl⟩ : syracuseStep 1016941 = 381353) (by norm_num)
theorem B1017029 : Blo 599292 1017029 := bbase (se 4 (by rfl) ⟨95346, by rfl⟩ : syracuseStep 1017029 = 190693) (by norm_num)
theorem B3048677 : Blo 599292 3048677 := bbase (se 4 (by rfl) ⟨285813, by rfl⟩ : syracuseStep 3048677 = 571627) (by norm_num)
theorem B1017157 : Blo 599292 1017157 := bbase (se 4 (by rfl) ⟨95358, by rfl⟩ : syracuseStep 1017157 = 190717) (by norm_num)
theorem B2033045 : Blo 599292 2033045 := bbase (se 6 (by rfl) ⟨47649, by rfl⟩ : syracuseStep 2033045 = 95299) (by norm_num)
theorem B1017245 : Blo 599292 1017245 := bbase (se 3 (by rfl) ⟨190733, by rfl⟩ : syracuseStep 1017245 = 381467) (by norm_num)
theorem B853517 : Blo 599292 853517 := bbase (se 3 (by rfl) ⟨160034, by rfl⟩ : syracuseStep 853517 = 320069) (by norm_num)
theorem B1017373 : Blo 599292 1017373 := bbase (se 3 (by rfl) ⟨190757, by rfl⟩ : syracuseStep 1017373 = 381515) (by norm_num)
theorem B1017461 : Blo 599292 1017461 := bbase (se 5 (by rfl) ⟨47693, by rfl⟩ : syracuseStep 1017461 = 95387) (by norm_num)
theorem B24610517 : Blo 599292 24610517 := bbase (se 7 (by rfl) ⟨288404, by rfl⟩ : syracuseStep 24610517 = 576809) (by norm_num)
theorem B1017589 : Blo 599292 1017589 := bbase (se 5 (by rfl) ⟨47699, by rfl⟩ : syracuseStep 1017589 = 95399) (by norm_num)
theorem B2033477 : Blo 599292 2033477 := bbase (se 4 (by rfl) ⟨190638, by rfl⟩ : syracuseStep 2033477 = 381277) (by norm_num)
theorem B1017677 : Blo 599292 1017677 := bbase (se 3 (by rfl) ⟨190814, by rfl⟩ : syracuseStep 1017677 = 381629) (by norm_num)
theorem B1017805 : Blo 599292 1017805 := bbase (se 3 (by rfl) ⟨190838, by rfl⟩ : syracuseStep 1017805 = 381677) (by norm_num)
theorem B1017893 : Blo 599292 1017893 := bbase (se 4 (by rfl) ⟨95427, by rfl⟩ : syracuseStep 1017893 = 190855) (by norm_num)
theorem B1280045 : Blo 599292 1280045 := bbase (se 3 (by rfl) ⟨240008, by rfl⟩ : syracuseStep 1280045 = 480017) (by norm_num)
theorem B854069 : Blo 599292 854069 := bbase (se 5 (by rfl) ⟨40034, by rfl⟩ : syracuseStep 854069 = 80069) (by norm_num)
theorem B1083557 : Blo 599292 1083557 := bbase (se 4 (by rfl) ⟨101583, by rfl⟩ : syracuseStep 1083557 = 203167) (by norm_num)
theorem B1018021 : Blo 599292 1018021 := bbase (se 4 (by rfl) ⟨95439, by rfl⟩ : syracuseStep 1018021 = 190879) (by norm_num)
theorem B2033909 : Blo 599292 2033909 := bbase (se 5 (by rfl) ⟨95339, by rfl⟩ : syracuseStep 2033909 = 190679) (by norm_num)
theorem B5146901 : Blo 599292 5146901 := bbase (se 6 (by rfl) ⟨120630, by rfl⟩ : syracuseStep 5146901 = 241261) (by norm_num)
theorem B2165093 : Blo 599292 2165093 := bbase (se 4 (by rfl) ⟨202977, by rfl⟩ : syracuseStep 2165093 = 405955) (by norm_num)
theorem B1083773 : Blo 599292 1083773 := bbase (se 3 (by rfl) ⟨203207, by rfl⟩ : syracuseStep 1083773 = 406415) (by norm_num)
theorem B723389 : Blo 599292 723389 := bbase (se 3 (by rfl) ⟨135635, by rfl⟩ : syracuseStep 723389 = 271271) (by norm_num)
theorem B3049973 : Blo 599292 3049973 := bbase (se 5 (by rfl) ⟨142967, by rfl⟩ : syracuseStep 3049973 = 285935) (by norm_num)
theorem B1280549 : Blo 599292 1280549 := bbase (se 4 (by rfl) ⟨120051, by rfl⟩ : syracuseStep 1280549 = 240103) (by norm_num)
theorem B1280557 : Blo 599292 1280557 := bbase (se 3 (by rfl) ⟨240104, by rfl⟩ : syracuseStep 1280557 = 480209) (by norm_num)
theorem B2165381 : Blo 599292 2165381 := bbase (se 4 (by rfl) ⟨203004, by rfl⟩ : syracuseStep 2165381 = 406009) (by norm_num)
theorem B723601 : Blo 599292 723601 := bbase (se 2 (by rfl) ⟨271350, by rfl⟩ : syracuseStep 723601 = 542701) (by norm_num)
theorem B2034341 : Blo 599292 2034341 := bbase (se 4 (by rfl) ⟨190719, by rfl⟩ : syracuseStep 2034341 = 381439) (by norm_num)
theorem B1215157 : Blo 599292 1215157 := bbase (se 5 (by rfl) ⟨56960, by rfl⟩ : syracuseStep 1215157 = 113921) (by norm_num)
theorem B723745 : Blo 599292 723745 := bbase (se 2 (by rfl) ⟨271404, by rfl⟩ : syracuseStep 723745 = 542809) (by norm_num)
theorem B854821 : Blo 599292 854821 := bbase (se 4 (by rfl) ⟨80139, by rfl⟩ : syracuseStep 854821 = 160279) (by norm_num)
theorem B1444645 : Blo 599292 1444645 := bbase (se 4 (by rfl) ⟨135435, by rfl⟩ : syracuseStep 1444645 = 270871) (by norm_num)
theorem B3083093 : Blo 599292 3083093 := bbase (se 9 (by rfl) ⟨9032, by rfl⟩ : syracuseStep 3083093 = 18065) (by norm_num)
theorem B2034773 : Blo 599292 2034773 := bbase (se 8 (by rfl) ⟨11922, by rfl⟩ : syracuseStep 2034773 = 23845) (by norm_num)
theorem B1084853 : Blo 599292 1084853 := bbase (se 5 (by rfl) ⟨50852, by rfl⟩ : syracuseStep 1084853 = 101705) (by norm_num)
theorem B1445357 : Blo 599292 1445357 := bbase (se 3 (by rfl) ⟨271004, by rfl⟩ : syracuseStep 1445357 = 542009) (by norm_num)
theorem B2035205 : Blo 599292 2035205 := bbase (se 4 (by rfl) ⟨190800, by rfl⟩ : syracuseStep 2035205 = 381601) (by norm_num)
theorem B855613 : Blo 599292 855613 := bbase (se 3 (by rfl) ⟨160427, by rfl⟩ : syracuseStep 855613 = 320855) (by norm_num)
theorem B1707637 : Blo 599292 1707637 := bbase (se 5 (by rfl) ⟨80045, by rfl⟩ : syracuseStep 1707637 = 160091) (by norm_num)
theorem B1412725 : Blo 599292 1412725 := bbase (se 5 (by rfl) ⟨66221, by rfl⟩ : syracuseStep 1412725 = 132443) (by norm_num)
theorem B1281685 : Blo 599292 1281685 := bbase (se 6 (by rfl) ⟨30039, by rfl⟩ : syracuseStep 1281685 = 60079) (by norm_num)
theorem B1085077 : Blo 599292 1085077 := bbase (se 6 (by rfl) ⟨25431, by rfl⟩ : syracuseStep 1085077 = 50863) (by norm_num)
theorem B3051269 : Blo 599292 3051269 := bbase (se 4 (by rfl) ⟨286056, by rfl⟩ : syracuseStep 3051269 = 572113) (by norm_num)
theorem B1707797 : Blo 599292 1707797 := bbase (se 6 (by rfl) ⟨40026, by rfl⟩ : syracuseStep 1707797 = 80053) (by norm_num)
theorem B1543981 : Blo 599292 1543981 := bbase (se 3 (by rfl) ⟨289496, by rfl⟩ : syracuseStep 1543981 = 578993) (by norm_num)
theorem B1216309 : Blo 599292 1216309 := bbase (se 5 (by rfl) ⟨57014, by rfl⟩ : syracuseStep 1216309 = 114029) (by norm_num)
theorem B1445741 : Blo 599292 1445741 := bbase (se 3 (by rfl) ⟨271076, by rfl⟩ : syracuseStep 1445741 = 542153) (by norm_num)
theorem B855949 : Blo 599292 855949 := bbase (se 3 (by rfl) ⟨160490, by rfl⟩ : syracuseStep 855949 = 320981) (by norm_num)
theorem B2035637 : Blo 599292 2035637 := bbase (se 5 (by rfl) ⟨95420, by rfl⟩ : syracuseStep 2035637 = 190841) (by norm_num)
theorem B1708037 : Blo 599292 1708037 := bbase (se 4 (by rfl) ⟨160128, by rfl⟩ : syracuseStep 1708037 = 320257) (by norm_num)
theorem B1282061 : Blo 599292 1282061 := bbase (se 3 (by rfl) ⟨240386, by rfl⟩ : syracuseStep 1282061 = 480773) (by norm_num)
theorem B856165 : Blo 599292 856165 := bbase (se 4 (by rfl) ⟨80265, by rfl⟩ : syracuseStep 856165 = 160531) (by norm_num)
theorem B1446029 : Blo 599292 1446029 := bbase (se 3 (by rfl) ⟨271130, by rfl⟩ : syracuseStep 1446029 = 542261) (by norm_num)
theorem B1708229 : Blo 599292 1708229 := bbase (se 4 (by rfl) ⟨160146, by rfl⟩ : syracuseStep 1708229 = 320293) (by norm_num)
theorem B19501397 : Blo 599292 19501397 := bbase (se 10 (by rfl) ⟨28566, by rfl⟩ : syracuseStep 19501397 = 57133) (by norm_num)
theorem B2036069 : Blo 599292 2036069 := bbase (se 4 (by rfl) ⟨190881, by rfl⟩ : syracuseStep 2036069 = 381763) (by norm_num)
theorem B856541 : Blo 599292 856541 := bbase (se 3 (by rfl) ⟨160601, by rfl⟩ : syracuseStep 856541 = 321203) (by norm_num)
theorem B2200069 : Blo 599292 2200069 := bbase (se 4 (by rfl) ⟨206256, by rfl⟩ : syracuseStep 2200069 = 412513) (by norm_num)
theorem B9277973 : Blo 599292 9277973 := bbase (se 6 (by rfl) ⟨217452, by rfl⟩ : syracuseStep 9277973 = 434905) (by norm_num)
theorem B2888405 : Blo 599292 2888405 := bbase (se 7 (by rfl) ⟨33848, by rfl⟩ : syracuseStep 2888405 = 67697) (by norm_num)
theorem B758585 : Blo 599292 758585 := bbase (se 2 (by rfl) ⟨284469, by rfl⟩ : syracuseStep 758585 = 568939) (by norm_num)
theorem B758641 : Blo 599292 758641 := bbase (se 2 (by rfl) ⟨284490, by rfl⟩ : syracuseStep 758641 = 568981) (by norm_num)
theorem B1348469 : Blo 599292 1348469 := bbase (se 5 (by rfl) ⟨63209, by rfl⟩ : syracuseStep 1348469 = 126419) (by norm_num)
theorem B1348541 : Blo 599292 1348541 := bbase (se 3 (by rfl) ⟨252851, by rfl⟩ : syracuseStep 1348541 = 505703) (by norm_num)
theorem B758737 : Blo 599292 758737 := bbase (se 2 (by rfl) ⟨284526, by rfl⟩ : syracuseStep 758737 = 569053) (by norm_num)
theorem B1086461 : Blo 599292 1086461 := bbase (se 3 (by rfl) ⟨203711, by rfl⟩ : syracuseStep 1086461 = 407423) (by norm_num)
theorem B1348613 : Blo 599292 1348613 := bbase (se 4 (by rfl) ⟨126432, by rfl⟩ : syracuseStep 1348613 = 252865) (by norm_num)
theorem B3052565 : Blo 599292 3052565 := bbase (se 6 (by rfl) ⟨71544, by rfl⟩ : syracuseStep 3052565 = 143089) (by norm_num)
theorem B2430005 : Blo 599292 2430005 := bbase (se 5 (by rfl) ⟨113906, by rfl⟩ : syracuseStep 2430005 = 227813) (by norm_num)
theorem B1348685 : Blo 599292 1348685 := bbase (se 3 (by rfl) ⟨252878, by rfl⟩ : syracuseStep 1348685 = 505757) (by norm_num)
theorem B1545301 : Blo 599292 1545301 := bbase (se 8 (by rfl) ⟨9054, by rfl⟩ : syracuseStep 1545301 = 18109) (by norm_num)
theorem B758909 : Blo 599292 758909 := bbase (se 3 (by rfl) ⟨142295, by rfl⟩ : syracuseStep 758909 = 284591) (by norm_num)
theorem B1348757 : Blo 599292 1348757 := bbase (se 6 (by rfl) ⟨31611, by rfl⟩ : syracuseStep 1348757 = 63223) (by norm_num)
theorem B1709221 : Blo 599292 1709221 := bbase (se 4 (by rfl) ⟨160239, by rfl⟩ : syracuseStep 1709221 = 320479) (by norm_num)
theorem B758965 : Blo 599292 758965 := bbase (se 5 (by rfl) ⟨35576, by rfl⟩ : syracuseStep 758965 = 71153) (by norm_num)
theorem B1348829 : Blo 599292 1348829 := bbase (se 3 (by rfl) ⟨252905, by rfl⟩ : syracuseStep 1348829 = 505811) (by norm_num)
theorem B759061 : Blo 599292 759061 := bbase (se 6 (by rfl) ⟨17790, by rfl⟩ : syracuseStep 759061 = 35581) (by norm_num)
theorem B1348901 : Blo 599292 1348901 := bbase (se 4 (by rfl) ⟨126459, by rfl⟩ : syracuseStep 1348901 = 252919) (by norm_num)
theorem B2168149 : Blo 599292 2168149 := bbase (se 14 (by rfl) ⟨198, by rfl⟩ : syracuseStep 2168149 = 397) (by norm_num)
theorem B1348973 : Blo 599292 1348973 := bbase (se 3 (by rfl) ⟨252932, by rfl⟩ : syracuseStep 1348973 = 505865) (by norm_num)
theorem B1349045 : Blo 599292 1349045 := bbase (se 5 (by rfl) ⟨63236, by rfl⟩ : syracuseStep 1349045 = 126473) (by norm_num)
theorem B759233 : Blo 599292 759233 := bbase (se 2 (by rfl) ⟨284712, by rfl⟩ : syracuseStep 759233 = 569425) (by norm_num)
theorem B2168309 : Blo 599292 2168309 := bbase (se 5 (by rfl) ⟨101639, by rfl⟩ : syracuseStep 2168309 = 203279) (by norm_num)
theorem B759289 : Blo 599292 759289 := bbase (se 2 (by rfl) ⟨284733, by rfl⟩ : syracuseStep 759289 = 569467) (by norm_num)
theorem B1349117 : Blo 599292 1349117 := bbase (se 3 (by rfl) ⟨252959, by rfl⟩ : syracuseStep 1349117 = 505919) (by norm_num)
theorem B1218053 : Blo 599292 1218053 := bbase (se 4 (by rfl) ⟨114192, by rfl⟩ : syracuseStep 1218053 = 228385) (by norm_num)
theorem B1349189 : Blo 599292 1349189 := bbase (se 4 (by rfl) ⟨126486, by rfl⟩ : syracuseStep 1349189 = 252973) (by norm_num)
theorem B1218125 : Blo 599292 1218125 := bbase (se 3 (by rfl) ⟨228398, by rfl⟩ : syracuseStep 1218125 = 456797) (by norm_num)
theorem B759385 : Blo 599292 759385 := bbase (se 2 (by rfl) ⟨284769, by rfl⟩ : syracuseStep 759385 = 569539) (by norm_num)
theorem B1283701 : Blo 599292 1283701 := bbase (se 5 (by rfl) ⟨60173, by rfl⟩ : syracuseStep 1283701 = 120347) (by norm_num)
theorem B1349261 : Blo 599292 1349261 := bbase (se 3 (by rfl) ⟨252986, by rfl⟩ : syracuseStep 1349261 = 505973) (by norm_num)
theorem B1349333 : Blo 599292 1349333 := bbase (se 7 (by rfl) ⟨15812, by rfl⟩ : syracuseStep 1349333 = 31625) (by norm_num)
theorem B2561797 : Blo 599292 2561797 := bbase (se 4 (by rfl) ⟨240168, by rfl⟩ : syracuseStep 2561797 = 480337) (by norm_num)
theorem B759557 : Blo 599292 759557 := bbase (se 4 (by rfl) ⟨71208, by rfl⟩ : syracuseStep 759557 = 142417) (by norm_num)
theorem B1349405 : Blo 599292 1349405 := bbase (se 3 (by rfl) ⟨253013, by rfl⟩ : syracuseStep 1349405 = 506027) (by norm_num)
theorem B759613 : Blo 599292 759613 := bbase (se 3 (by rfl) ⟨142427, by rfl⟩ : syracuseStep 759613 = 284855) (by norm_num)
theorem B1349477 : Blo 599292 1349477 := bbase (se 4 (by rfl) ⟨126513, by rfl⟩ : syracuseStep 1349477 = 253027) (by norm_num)
theorem B857965 : Blo 599292 857965 := bbase (se 3 (by rfl) ⟨160868, by rfl⟩ : syracuseStep 857965 = 321737) (by norm_num)
theorem B759709 : Blo 599292 759709 := bbase (se 3 (by rfl) ⟨142445, by rfl⟩ : syracuseStep 759709 = 284891) (by norm_num)
theorem B1349549 : Blo 599292 1349549 := bbase (se 3 (by rfl) ⟨253040, by rfl⟩ : syracuseStep 1349549 = 506081) (by norm_num)
theorem B1349621 : Blo 599292 1349621 := bbase (se 5 (by rfl) ⟨63263, by rfl⟩ : syracuseStep 1349621 = 126527) (by norm_num)
theorem B1349693 : Blo 599292 1349693 := bbase (se 3 (by rfl) ⟨253067, by rfl⟩ : syracuseStep 1349693 = 506135) (by norm_num)
theorem B759881 : Blo 599292 759881 := bbase (se 2 (by rfl) ⟨284955, by rfl⟩ : syracuseStep 759881 = 569911) (by norm_num)
theorem B759937 : Blo 599292 759937 := bbase (se 2 (by rfl) ⟨284976, by rfl⟩ : syracuseStep 759937 = 569953) (by norm_num)
theorem B1349765 : Blo 599292 1349765 := bbase (se 4 (by rfl) ⟨126540, by rfl⟩ : syracuseStep 1349765 = 253081) (by norm_num)
theorem B1349837 : Blo 599292 1349837 := bbase (se 3 (by rfl) ⟨253094, by rfl⟩ : syracuseStep 1349837 = 506189) (by norm_num)
theorem B4561109 : Blo 599292 4561109 := bbase (se 7 (by rfl) ⟨53450, by rfl⟩ : syracuseStep 4561109 = 106901) (by norm_num)
theorem B760033 : Blo 599292 760033 := bbase (se 2 (by rfl) ⟨285012, by rfl⟩ : syracuseStep 760033 = 570025) (by norm_num)
theorem B1710325 : Blo 599292 1710325 := bbase (se 5 (by rfl) ⟨80171, by rfl⟩ : syracuseStep 1710325 = 160343) (by norm_num)
theorem B1349909 : Blo 599292 1349909 := bbase (se 6 (by rfl) ⟨31638, by rfl⟩ : syracuseStep 1349909 = 63277) (by norm_num)
theorem B3053861 : Blo 599292 3053861 := bbase (se 4 (by rfl) ⟨286299, by rfl⟩ : syracuseStep 3053861 = 572599) (by norm_num)
theorem B1349981 : Blo 599292 1349981 := bbase (se 3 (by rfl) ⟨253121, by rfl⟩ : syracuseStep 1349981 = 506243) (by norm_num)
theorem B760205 : Blo 599292 760205 := bbase (se 3 (by rfl) ⟨142538, by rfl⟩ : syracuseStep 760205 = 285077) (by norm_num)
theorem B1350053 : Blo 599292 1350053 := bbase (se 4 (by rfl) ⟨126567, by rfl⟩ : syracuseStep 1350053 = 253135) (by norm_num)
theorem B858557 : Blo 599292 858557 := bbase (se 3 (by rfl) ⟨160979, by rfl⟩ : syracuseStep 858557 = 321959) (by norm_num)
theorem B760261 : Blo 599292 760261 := bbase (se 4 (by rfl) ⟨71274, by rfl⟩ : syracuseStep 760261 = 142549) (by norm_num)
theorem B1350125 : Blo 599292 1350125 := bbase (se 3 (by rfl) ⟨253148, by rfl⟩ : syracuseStep 1350125 = 506297) (by norm_num)
theorem B1284589 : Blo 599292 1284589 := bbase (se 3 (by rfl) ⟨240860, by rfl⟩ : syracuseStep 1284589 = 481721) (by norm_num)
theorem B858637 : Blo 599292 858637 := bbase (se 3 (by rfl) ⟨160994, by rfl⟩ : syracuseStep 858637 = 321989) (by norm_num)
theorem B760357 : Blo 599292 760357 := bbase (se 4 (by rfl) ⟨71283, by rfl⟩ : syracuseStep 760357 = 142567) (by norm_num)
theorem B1350197 : Blo 599292 1350197 := bbase (se 5 (by rfl) ⟨63290, by rfl⟩ : syracuseStep 1350197 = 126581) (by norm_num)
theorem B1350269 : Blo 599292 1350269 := bbase (se 3 (by rfl) ⟨253175, by rfl⟩ : syracuseStep 1350269 = 506351) (by norm_num)
theorem B858757 : Blo 599292 858757 := bbase (se 4 (by rfl) ⟨80508, by rfl⟩ : syracuseStep 858757 = 161017) (by norm_num)
theorem B5872277 : Blo 599292 5872277 := bbase (se 6 (by rfl) ⟨137631, by rfl⟩ : syracuseStep 5872277 = 275263) (by norm_num)
theorem B1350341 : Blo 599292 1350341 := bbase (se 4 (by rfl) ⟨126594, by rfl⟩ : syracuseStep 1350341 = 253189) (by norm_num)
theorem B760529 : Blo 599292 760529 := bbase (se 2 (by rfl) ⟨285198, by rfl⟩ : syracuseStep 760529 = 570397) (by norm_num)
theorem B858853 : Blo 599292 858853 := bbase (se 4 (by rfl) ⟨80517, by rfl⟩ : syracuseStep 858853 = 161035) (by norm_num)
theorem B760585 : Blo 599292 760585 := bbase (se 2 (by rfl) ⟨285219, by rfl⟩ : syracuseStep 760585 = 570439) (by norm_num)
theorem B1350413 : Blo 599292 1350413 := bbase (se 3 (by rfl) ⟨253202, by rfl⟩ : syracuseStep 1350413 = 506405) (by norm_num)
theorem B3119957 : Blo 599292 3119957 := bbase (se 9 (by rfl) ⟨9140, by rfl⟩ : syracuseStep 3119957 = 18281) (by norm_num)
theorem B1350485 : Blo 599292 1350485 := bbase (se 9 (by rfl) ⟨3956, by rfl⟩ : syracuseStep 1350485 = 7913) (by norm_num)
theorem B760681 : Blo 599292 760681 := bbase (se 2 (by rfl) ⟨285255, by rfl⟩ : syracuseStep 760681 = 570511) (by norm_num)
theorem B1350557 : Blo 599292 1350557 := bbase (se 3 (by rfl) ⟨253229, by rfl⟩ : syracuseStep 1350557 = 506459) (by norm_num)
theorem B1285085 : Blo 599292 1285085 := bbase (se 3 (by rfl) ⟨240953, by rfl⟩ : syracuseStep 1285085 = 481907) (by norm_num)
theorem B1350629 : Blo 599292 1350629 := bbase (se 4 (by rfl) ⟨126621, by rfl⟩ : syracuseStep 1350629 = 253243) (by norm_num)
theorem B760853 : Blo 599292 760853 := bbase (se 6 (by rfl) ⟨17832, by rfl⟩ : syracuseStep 760853 = 35665) (by norm_num)
theorem B1350701 : Blo 599292 1350701 := bbase (se 3 (by rfl) ⟨253256, by rfl⟩ : syracuseStep 1350701 = 506513) (by norm_num)
theorem B760909 : Blo 599292 760909 := bbase (se 3 (by rfl) ⟨142670, by rfl⟩ : syracuseStep 760909 = 285341) (by norm_num)
theorem B1350773 : Blo 599292 1350773 := bbase (se 5 (by rfl) ⟨63317, by rfl⟩ : syracuseStep 1350773 = 126635) (by norm_num)
theorem B1449085 : Blo 599292 1449085 := bbase (se 3 (by rfl) ⟨271703, by rfl⟩ : syracuseStep 1449085 = 543407) (by norm_num)
theorem B761005 : Blo 599292 761005 := bbase (se 3 (by rfl) ⟨142688, by rfl⟩ : syracuseStep 761005 = 285377) (by norm_num)
theorem B1350845 : Blo 599292 1350845 := bbase (se 3 (by rfl) ⟨253283, by rfl⟩ : syracuseStep 1350845 = 506567) (by norm_num)
theorem B2563285 : Blo 599292 2563285 := bbase (se 7 (by rfl) ⟨30038, by rfl⟩ : syracuseStep 2563285 = 60077) (by norm_num)
theorem B2563301 : Blo 599292 2563301 := bbase (se 4 (by rfl) ⟨240309, by rfl⟩ : syracuseStep 2563301 = 480619) (by norm_num)
theorem B1350917 : Blo 599292 1350917 := bbase (se 4 (by rfl) ⟨126648, by rfl⟩ : syracuseStep 1350917 = 253297) (by norm_num)
theorem B1350989 : Blo 599292 1350989 := bbase (se 3 (by rfl) ⟨253310, by rfl⟩ : syracuseStep 1350989 = 506621) (by norm_num)
theorem B761177 : Blo 599292 761177 := bbase (se 2 (by rfl) ⟨285441, by rfl⟩ : syracuseStep 761177 = 570883) (by norm_num)
theorem B761233 : Blo 599292 761233 := bbase (se 2 (by rfl) ⟨285462, by rfl⟩ : syracuseStep 761233 = 570925) (by norm_num)
theorem B1351061 : Blo 599292 1351061 := bbase (se 6 (by rfl) ⟨31665, by rfl⟩ : syracuseStep 1351061 = 63331) (by norm_num)
theorem B2891173 : Blo 599292 2891173 := bbase (se 4 (by rfl) ⟨271047, by rfl⟩ : syracuseStep 2891173 = 542095) (by norm_num)
theorem B5774773 : Blo 599292 5774773 := bbase (se 5 (by rfl) ⟨270692, by rfl⟩ : syracuseStep 5774773 = 541385) (by norm_num)
theorem B1351133 : Blo 599292 1351133 := bbase (se 3 (by rfl) ⟨253337, by rfl⟩ : syracuseStep 1351133 = 506675) (by norm_num)
theorem B761329 : Blo 599292 761329 := bbase (se 2 (by rfl) ⟨285498, by rfl⟩ : syracuseStep 761329 = 570997) (by norm_num)
theorem B1351205 : Blo 599292 1351205 := bbase (se 4 (by rfl) ⟨126675, by rfl⟩ : syracuseStep 1351205 = 253351) (by norm_num)
theorem B1351277 : Blo 599292 1351277 := bbase (se 3 (by rfl) ⟨253364, by rfl⟩ : syracuseStep 1351277 = 506729) (by norm_num)
theorem B761501 : Blo 599292 761501 := bbase (se 3 (by rfl) ⟨142781, by rfl⟩ : syracuseStep 761501 = 285563) (by norm_num)
theorem B1351349 : Blo 599292 1351349 := bbase (se 5 (by rfl) ⟨63344, by rfl⟩ : syracuseStep 1351349 = 126689) (by norm_num)
theorem B1711829 : Blo 599292 1711829 := bbase (se 7 (by rfl) ⟨20060, by rfl⟩ : syracuseStep 1711829 = 40121) (by norm_num)
theorem B761557 : Blo 599292 761557 := bbase (se 7 (by rfl) ⟨8924, by rfl⟩ : syracuseStep 761557 = 17849) (by norm_num)
theorem B1351421 : Blo 599292 1351421 := bbase (se 3 (by rfl) ⟨253391, by rfl⟩ : syracuseStep 1351421 = 506783) (by norm_num)
theorem B761653 : Blo 599292 761653 := bbase (se 5 (by rfl) ⟨35702, by rfl⟩ : syracuseStep 761653 = 71405) (by norm_num)
theorem B1285949 : Blo 599292 1285949 := bbase (se 3 (by rfl) ⟨241115, by rfl⟩ : syracuseStep 1285949 = 482231) (by norm_num)
theorem B1351493 : Blo 599292 1351493 := bbase (se 4 (by rfl) ⟨126702, by rfl⟩ : syracuseStep 1351493 = 253405) (by norm_num)
theorem B1351565 : Blo 599292 1351565 := bbase (se 3 (by rfl) ⟨253418, by rfl⟩ : syracuseStep 1351565 = 506837) (by norm_num)
theorem B1220525 : Blo 599292 1220525 := bbase (se 3 (by rfl) ⟨228848, by rfl⟩ : syracuseStep 1220525 = 457697) (by norm_num)
theorem B1286093 : Blo 599292 1286093 := bbase (se 3 (by rfl) ⟨241142, by rfl⟩ : syracuseStep 1286093 = 482285) (by norm_num)
theorem B1351637 : Blo 599292 1351637 := bbase (se 7 (by rfl) ⟨15839, by rfl⟩ : syracuseStep 1351637 = 31679) (by norm_num)
theorem B761825 : Blo 599292 761825 := bbase (se 2 (by rfl) ⟨285684, by rfl⟩ : syracuseStep 761825 = 571369) (by norm_num)
theorem B761881 : Blo 599292 761881 := bbase (se 2 (by rfl) ⟨285705, by rfl⟩ : syracuseStep 761881 = 571411) (by norm_num)
theorem B1351709 : Blo 599292 1351709 := bbase (se 3 (by rfl) ⟨253445, by rfl⟩ : syracuseStep 1351709 = 506891) (by norm_num)
theorem B1351781 : Blo 599292 1351781 := bbase (se 4 (by rfl) ⟨126729, by rfl⟩ : syracuseStep 1351781 = 253459) (by norm_num)
theorem B761977 : Blo 599292 761977 := bbase (se 2 (by rfl) ⟨285741, by rfl⟩ : syracuseStep 761977 = 571483) (by norm_num)
theorem B1351853 : Blo 599292 1351853 := bbase (se 3 (by rfl) ⟨253472, by rfl⟩ : syracuseStep 1351853 = 506945) (by norm_num)
theorem B1351925 : Blo 599292 1351925 := bbase (se 5 (by rfl) ⟨63371, by rfl⟩ : syracuseStep 1351925 = 126743) (by norm_num)
theorem B762149 : Blo 599292 762149 := bbase (se 4 (by rfl) ⟨71451, by rfl⟩ : syracuseStep 762149 = 142903) (by norm_num)
theorem B1351997 : Blo 599292 1351997 := bbase (se 3 (by rfl) ⟨253499, by rfl⟩ : syracuseStep 1351997 = 506999) (by norm_num)
theorem B1155421 : Blo 599292 1155421 := bbase (se 3 (by rfl) ⟨216641, by rfl⟩ : syracuseStep 1155421 = 433283) (by norm_num)
theorem B762205 : Blo 599292 762205 := bbase (se 3 (by rfl) ⟨142913, by rfl⟩ : syracuseStep 762205 = 285827) (by norm_num)
theorem B1352069 : Blo 599292 1352069 := bbase (se 4 (by rfl) ⟨126756, by rfl⟩ : syracuseStep 1352069 = 253513) (by norm_num)
theorem B762301 : Blo 599292 762301 := bbase (se 3 (by rfl) ⟨142931, by rfl⟩ : syracuseStep 762301 = 285863) (by norm_num)
theorem B1352141 : Blo 599292 1352141 := bbase (se 3 (by rfl) ⟨253526, by rfl⟩ : syracuseStep 1352141 = 507053) (by norm_num)
theorem B1155589 : Blo 599292 1155589 := bbase (se 4 (by rfl) ⟨108336, by rfl⟩ : syracuseStep 1155589 = 216673) (by norm_num)
theorem B1352213 : Blo 599292 1352213 := bbase (se 6 (by rfl) ⟨31692, by rfl⟩ : syracuseStep 1352213 = 63385) (by norm_num)
theorem B39428693 : Blo 599292 39428693 := bbase (se 8 (by rfl) ⟨231027, by rfl⟩ : syracuseStep 39428693 = 462055) (by norm_num)
theorem B1352285 : Blo 599292 1352285 := bbase (se 3 (by rfl) ⟨253553, by rfl⟩ : syracuseStep 1352285 = 507107) (by norm_num)
theorem B762473 : Blo 599292 762473 := bbase (se 2 (by rfl) ⟨285927, by rfl⟩ : syracuseStep 762473 = 571855) (by norm_num)
theorem B2433653 : Blo 599292 2433653 := bbase (se 5 (by rfl) ⟨114077, by rfl⟩ : syracuseStep 2433653 = 228155) (by norm_num)
theorem B762529 : Blo 599292 762529 := bbase (se 2 (by rfl) ⟨285948, by rfl⟩ : syracuseStep 762529 = 571897) (by norm_num)
theorem B1352357 : Blo 599292 1352357 := bbase (se 4 (by rfl) ⟨126783, by rfl⟩ : syracuseStep 1352357 = 253567) (by norm_num)
theorem B1286837 : Blo 599292 1286837 := bbase (se 5 (by rfl) ⟨60320, by rfl⟩ : syracuseStep 1286837 = 120641) (by norm_num)
theorem B1352429 : Blo 599292 1352429 := bbase (se 3 (by rfl) ⟨253580, by rfl⟩ : syracuseStep 1352429 = 507161) (by norm_num)
theorem B762625 : Blo 599292 762625 := bbase (se 2 (by rfl) ⟨285984, by rfl⟩ : syracuseStep 762625 = 571969) (by norm_num)
theorem B5481269 : Blo 599292 5481269 := bbase (se 5 (by rfl) ⟨256934, by rfl⟩ : syracuseStep 5481269 = 513869) (by norm_num)
theorem B1352501 : Blo 599292 1352501 := bbase (se 5 (by rfl) ⟨63398, by rfl⟩ : syracuseStep 1352501 = 126797) (by norm_num)
theorem B1352573 : Blo 599292 1352573 := bbase (se 3 (by rfl) ⟨253607, by rfl⟩ : syracuseStep 1352573 = 507215) (by norm_num)
theorem B762797 : Blo 599292 762797 := bbase (se 3 (by rfl) ⟨143024, by rfl⟩ : syracuseStep 762797 = 286049) (by norm_num)
theorem B1352645 : Blo 599292 1352645 := bbase (se 4 (by rfl) ⟨126810, by rfl⟩ : syracuseStep 1352645 = 253621) (by norm_num)
theorem B762853 : Blo 599292 762853 := bbase (se 4 (by rfl) ⟨71517, by rfl⟩ : syracuseStep 762853 = 143035) (by norm_num)
theorem B1352717 : Blo 599292 1352717 := bbase (se 3 (by rfl) ⟨253634, by rfl⟩ : syracuseStep 1352717 = 507269) (by norm_num)
theorem B762949 : Blo 599292 762949 := bbase (se 4 (by rfl) ⟨71526, by rfl⟩ : syracuseStep 762949 = 143053) (by norm_num)
theorem B1352789 : Blo 599292 1352789 := bbase (se 8 (by rfl) ⟨7926, by rfl⟩ : syracuseStep 1352789 = 15853) (by norm_num)
theorem B4891765 : Blo 599292 4891765 := bbase (se 5 (by rfl) ⟨229301, by rfl⟩ : syracuseStep 4891765 = 458603) (by norm_num)
theorem B3286165 : Blo 599292 3286165 := bbase (se 6 (by rfl) ⟨77019, by rfl⟩ : syracuseStep 3286165 = 154039) (by norm_num)
theorem B1352861 : Blo 599292 1352861 := bbase (se 3 (by rfl) ⟨253661, by rfl⟩ : syracuseStep 1352861 = 507323) (by norm_num)
theorem B1352933 : Blo 599292 1352933 := bbase (se 4 (by rfl) ⟨126837, by rfl⟩ : syracuseStep 1352933 = 253675) (by norm_num)
theorem B763121 : Blo 599292 763121 := bbase (se 2 (by rfl) ⟨286170, by rfl⟩ : syracuseStep 763121 = 572341) (by norm_num)
theorem B1713413 : Blo 599292 1713413 := bbase (se 4 (by rfl) ⟨160632, by rfl⟩ : syracuseStep 1713413 = 321265) (by norm_num)
theorem B763177 : Blo 599292 763177 := bbase (se 2 (by rfl) ⟨286191, by rfl⟩ : syracuseStep 763177 = 572383) (by norm_num)
theorem B1353005 : Blo 599292 1353005 := bbase (se 3 (by rfl) ⟨253688, by rfl⟩ : syracuseStep 1353005 = 507377) (by norm_num)
theorem B3417461 : Blo 599292 3417461 := bbase (se 5 (by rfl) ⟨160193, by rfl⟩ : syracuseStep 3417461 = 320387) (by norm_num)
theorem B1353077 : Blo 599292 1353077 := bbase (se 5 (by rfl) ⟨63425, by rfl⟩ : syracuseStep 1353077 = 126851) (by norm_num)
theorem B763273 : Blo 599292 763273 := bbase (se 2 (by rfl) ⟨286227, by rfl⟩ : syracuseStep 763273 = 572455) (by norm_num)
theorem B1287589 : Blo 599292 1287589 := bbase (se 4 (by rfl) ⟨120711, by rfl⟩ : syracuseStep 1287589 = 241423) (by norm_num)
theorem B2565557 : Blo 599292 2565557 := bbase (se 5 (by rfl) ⟨120260, by rfl⟩ : syracuseStep 2565557 = 240521) (by norm_num)
theorem B4335029 : Blo 599292 4335029 := bbase (se 5 (by rfl) ⟨203204, by rfl⟩ : syracuseStep 4335029 = 406409) (by norm_num)
theorem B1353149 : Blo 599292 1353149 := bbase (se 3 (by rfl) ⟨253715, by rfl⟩ : syracuseStep 1353149 = 507431) (by norm_num)
theorem B1353221 : Blo 599292 1353221 := bbase (se 4 (by rfl) ⟨126864, by rfl⟩ : syracuseStep 1353221 = 253729) (by norm_num)
theorem B1517069 : Blo 599292 1517069 := bbase (se 3 (by rfl) ⟨284450, by rfl⟩ : syracuseStep 1517069 = 568901) (by norm_num)
theorem B1287733 : Blo 599292 1287733 := bbase (se 5 (by rfl) ⟨60362, by rfl⟩ : syracuseStep 1287733 = 120725) (by norm_num)
theorem B763445 : Blo 599292 763445 := bbase (se 5 (by rfl) ⟨35786, by rfl⟩ : syracuseStep 763445 = 71573) (by norm_num)
theorem B1353293 : Blo 599292 1353293 := bbase (se 3 (by rfl) ⟨253742, by rfl⟩ : syracuseStep 1353293 = 507485) (by norm_num)
theorem B763501 : Blo 599292 763501 := bbase (se 3 (by rfl) ⟨143156, by rfl⟩ : syracuseStep 763501 = 286313) (by norm_num)
theorem B1353365 : Blo 599292 1353365 := bbase (se 6 (by rfl) ⟨31719, by rfl⟩ : syracuseStep 1353365 = 63439) (by norm_num)
theorem B1353437 : Blo 599292 1353437 := bbase (se 3 (by rfl) ⟨253769, by rfl⟩ : syracuseStep 1353437 = 507539) (by norm_num)
theorem B1353509 : Blo 599292 1353509 := bbase (se 4 (by rfl) ⟨126891, by rfl⟩ : syracuseStep 1353509 = 253783) (by norm_num)
theorem B960341 : Blo 599292 960341 := bbase (se 9 (by rfl) ⟨2813, by rfl⟩ : syracuseStep 960341 = 5627) (by norm_num)
theorem B1517413 : Blo 599292 1517413 := bbase (se 4 (by rfl) ⟨142257, by rfl⟩ : syracuseStep 1517413 = 284515) (by norm_num)
theorem B1353581 : Blo 599292 1353581 := bbase (se 3 (by rfl) ⟨253796, by rfl⟩ : syracuseStep 1353581 = 507593) (by norm_num)
theorem B1714085 : Blo 599292 1714085 := bbase (se 4 (by rfl) ⟨160695, by rfl⟩ : syracuseStep 1714085 = 321391) (by norm_num)
theorem B1288109 : Blo 599292 1288109 := bbase (se 3 (by rfl) ⟨241520, by rfl⟩ : syracuseStep 1288109 = 483041) (by norm_num)
theorem B1353653 : Blo 599292 1353653 := bbase (se 5 (by rfl) ⟨63452, by rfl⟩ : syracuseStep 1353653 = 126905) (by norm_num)
theorem B1517525 : Blo 599292 1517525 := bbase (se 7 (by rfl) ⟨17783, by rfl⟩ : syracuseStep 1517525 = 35567) (by norm_num)
theorem B1353725 : Blo 599292 1353725 := bbase (se 3 (by rfl) ⟨253823, by rfl⟩ : syracuseStep 1353725 = 507647) (by norm_num)
theorem B1353797 : Blo 599292 1353797 := bbase (se 4 (by rfl) ⟨126918, by rfl⟩ : syracuseStep 1353797 = 253837) (by norm_num)
theorem B1353869 : Blo 599292 1353869 := bbase (se 3 (by rfl) ⟨253850, by rfl⟩ : syracuseStep 1353869 = 507701) (by norm_num)
theorem B1517717 : Blo 599292 1517717 := bbase (se 6 (by rfl) ⟨35571, by rfl⟩ : syracuseStep 1517717 = 71143) (by norm_num)
theorem B1353941 : Blo 599292 1353941 := bbase (se 7 (by rfl) ⟨15866, by rfl⟩ : syracuseStep 1353941 = 31733) (by norm_num)
theorem B1222901 : Blo 599292 1222901 := bbase (se 5 (by rfl) ⟨57323, by rfl⟩ : syracuseStep 1222901 = 114647) (by norm_num)
theorem B1354013 : Blo 599292 1354013 := bbase (se 3 (by rfl) ⟨253877, by rfl⟩ : syracuseStep 1354013 = 507755) (by norm_num)
theorem B1288477 : Blo 599292 1288477 := bbase (se 3 (by rfl) ⟨241589, by rfl⟩ : syracuseStep 1288477 = 483179) (by norm_num)
theorem B3909941 : Blo 599292 3909941 := bbase (se 5 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 3909941 = 366557) (by norm_num)
theorem B1714517 : Blo 599292 1714517 := bbase (se 10 (by rfl) ⟨2511, by rfl⟩ : syracuseStep 1714517 = 5023) (by norm_num)
theorem B1354085 : Blo 599292 1354085 := bbase (se 4 (by rfl) ⟨126945, by rfl⟩ : syracuseStep 1354085 = 253891) (by norm_num)
theorem B960893 : Blo 599292 960893 := bbase (se 3 (by rfl) ⟨180167, by rfl⟩ : syracuseStep 960893 = 360335) (by norm_num)
theorem B960925 : Blo 599292 960925 := bbase (se 3 (by rfl) ⟨180173, by rfl⟩ : syracuseStep 960925 = 360347) (by norm_num)
theorem B1354157 : Blo 599292 1354157 := bbase (se 3 (by rfl) ⟨253904, by rfl⟩ : syracuseStep 1354157 = 507809) (by norm_num)
theorem B731605 : Blo 599292 731605 := bbase (se 7 (by rfl) ⟨8573, by rfl⟩ : syracuseStep 731605 = 17147) (by norm_num)
theorem B1518061 : Blo 599292 1518061 := bbase (se 3 (by rfl) ⟨284636, by rfl⟩ : syracuseStep 1518061 = 569273) (by norm_num)
theorem B1354229 : Blo 599292 1354229 := bbase (se 5 (by rfl) ⟨63479, by rfl⟩ : syracuseStep 1354229 = 126959) (by norm_num)
theorem B3418645 : Blo 599292 3418645 := bbase (se 6 (by rfl) ⟨80124, by rfl⟩ : syracuseStep 3418645 = 160249) (by norm_num)
theorem B1354301 : Blo 599292 1354301 := bbase (se 3 (by rfl) ⟨253931, by rfl⟩ : syracuseStep 1354301 = 507863) (by norm_num)
theorem B1518173 : Blo 599292 1518173 := bbase (se 3 (by rfl) ⟨284657, by rfl⟩ : syracuseStep 1518173 = 569315) (by norm_num)
theorem B1354373 : Blo 599292 1354373 := bbase (se 4 (by rfl) ⟨126972, by rfl⟩ : syracuseStep 1354373 = 253945) (by norm_num)
theorem B1354445 : Blo 599292 1354445 := bbase (se 3 (by rfl) ⟨253958, by rfl⟩ : syracuseStep 1354445 = 507917) (by norm_num)
theorem B1354517 : Blo 599292 1354517 := bbase (se 6 (by rfl) ⟨31746, by rfl⟩ : syracuseStep 1354517 = 63493) (by norm_num)
theorem B1518365 : Blo 599292 1518365 := bbase (se 3 (by rfl) ⟨284693, by rfl⟩ : syracuseStep 1518365 = 569387) (by norm_num)
theorem B1354589 : Blo 599292 1354589 := bbase (se 3 (by rfl) ⟨253985, by rfl⟩ : syracuseStep 1354589 = 507971) (by norm_num)
theorem B4107125 : Blo 599292 4107125 := bbase (se 5 (by rfl) ⟨192521, by rfl⟩ : syracuseStep 4107125 = 385043) (by norm_num)
theorem B1354661 : Blo 599292 1354661 := bbase (se 4 (by rfl) ⟨126999, by rfl⟩ : syracuseStep 1354661 = 253999) (by norm_num)
theorem B1158085 : Blo 599292 1158085 := bbase (se 4 (by rfl) ⟨108570, by rfl⟩ : syracuseStep 1158085 = 217141) (by norm_num)
theorem B1354733 : Blo 599292 1354733 := bbase (se 3 (by rfl) ⟨254012, by rfl⟩ : syracuseStep 1354733 = 508025) (by norm_num)
theorem B1354805 : Blo 599292 1354805 := bbase (se 5 (by rfl) ⟨63506, by rfl⟩ : syracuseStep 1354805 = 127013) (by norm_num)
theorem B1715269 : Blo 599292 1715269 := bbase (se 4 (by rfl) ⟨160806, by rfl⟩ : syracuseStep 1715269 = 321613) (by norm_num)
theorem B1518709 : Blo 599292 1518709 := bbase (se 5 (by rfl) ⟨71189, by rfl⟩ : syracuseStep 1518709 = 142379) (by norm_num)
theorem B1354877 : Blo 599292 1354877 := bbase (se 3 (by rfl) ⟨254039, by rfl⟩ : syracuseStep 1354877 = 508079) (by norm_num)
theorem B1354949 : Blo 599292 1354949 := bbase (se 4 (by rfl) ⟨127026, by rfl⟩ : syracuseStep 1354949 = 254053) (by norm_num)
theorem B1518821 : Blo 599292 1518821 := bbase (se 4 (by rfl) ⟨142389, by rfl⟩ : syracuseStep 1518821 = 284779) (by norm_num)
theorem B1355021 : Blo 599292 1355021 := bbase (se 3 (by rfl) ⟨254066, by rfl⟩ : syracuseStep 1355021 = 508133) (by norm_num)
theorem B961853 : Blo 599292 961853 := bbase (se 3 (by rfl) ⟨180347, by rfl⟩ : syracuseStep 961853 = 360695) (by norm_num)
theorem B1355093 : Blo 599292 1355093 := bbase (se 11 (by rfl) ⟨992, by rfl⟩ : syracuseStep 1355093 = 1985) (by norm_num)
theorem B1355165 : Blo 599292 1355165 := bbase (se 3 (by rfl) ⟨254093, by rfl⟩ : syracuseStep 1355165 = 508187) (by norm_num)
theorem B1519013 : Blo 599292 1519013 := bbase (se 4 (by rfl) ⟨142407, by rfl⟩ : syracuseStep 1519013 = 284815) (by norm_num)
theorem B1355237 : Blo 599292 1355237 := bbase (se 4 (by rfl) ⟨127053, by rfl⟩ : syracuseStep 1355237 = 254107) (by norm_num)
theorem B1355309 : Blo 599292 1355309 := bbase (se 3 (by rfl) ⟨254120, by rfl⟩ : syracuseStep 1355309 = 508241) (by norm_num)
theorem B1355381 : Blo 599292 1355381 := bbase (se 5 (by rfl) ⟨63533, by rfl⟩ : syracuseStep 1355381 = 127067) (by norm_num)
theorem B1355453 : Blo 599292 1355453 := bbase (se 3 (by rfl) ⟨254147, by rfl⟩ : syracuseStep 1355453 = 508295) (by norm_num)
theorem B634601 : Blo 599292 634601 := bbase (se 2 (by rfl) ⟨237975, by rfl⟩ : syracuseStep 634601 = 475951) (by norm_num)
theorem B1519357 : Blo 599292 1519357 := bbase (se 3 (by rfl) ⟨284879, by rfl⟩ : syracuseStep 1519357 = 569759) (by norm_num)
theorem B1355525 : Blo 599292 1355525 := bbase (se 4 (by rfl) ⟨127080, by rfl⟩ : syracuseStep 1355525 = 254161) (by norm_num)
theorem B1355597 : Blo 599292 1355597 := bbase (se 3 (by rfl) ⟨254174, by rfl⟩ : syracuseStep 1355597 = 508349) (by norm_num)
theorem B1519469 : Blo 599292 1519469 := bbase (se 3 (by rfl) ⟨284900, by rfl⟩ : syracuseStep 1519469 = 569801) (by norm_num)
theorem B1027957 : Blo 599292 1027957 := bbase (se 5 (by rfl) ⟨48185, by rfl⟩ : syracuseStep 1027957 = 96371) (by norm_num)
theorem B2895749 : Blo 599292 2895749 := bbase (se 4 (by rfl) ⟨271476, by rfl⟩ : syracuseStep 2895749 = 542953) (by norm_num)
theorem B1355669 : Blo 599292 1355669 := bbase (se 6 (by rfl) ⟨31773, by rfl⟩ : syracuseStep 1355669 = 63547) (by norm_num)
theorem B1355741 : Blo 599292 1355741 := bbase (se 3 (by rfl) ⟨254201, by rfl⟩ : syracuseStep 1355741 = 508403) (by norm_num)
theorem B962533 : Blo 599292 962533 := bbase (se 4 (by rfl) ⟨90237, by rfl⟩ : syracuseStep 962533 = 180475) (by norm_num)
theorem B962597 : Blo 599292 962597 := bbase (se 4 (by rfl) ⟨90243, by rfl⟩ : syracuseStep 962597 = 180487) (by norm_num)
theorem B1355813 : Blo 599292 1355813 := bbase (se 4 (by rfl) ⟨127107, by rfl⟩ : syracuseStep 1355813 = 254215) (by norm_num)
theorem B1519661 : Blo 599292 1519661 := bbase (se 3 (by rfl) ⟨284936, by rfl⟩ : syracuseStep 1519661 = 569873) (by norm_num)
theorem B1355885 : Blo 599292 1355885 := bbase (se 3 (by rfl) ⟨254228, by rfl⟩ : syracuseStep 1355885 = 508457) (by norm_num)
theorem B1355957 : Blo 599292 1355957 := bbase (se 5 (by rfl) ⟨63560, by rfl⟩ : syracuseStep 1355957 = 127121) (by norm_num)
theorem B1356029 : Blo 599292 1356029 := bbase (se 3 (by rfl) ⟨254255, by rfl⟩ : syracuseStep 1356029 = 508511) (by norm_num)
theorem B1356101 : Blo 599292 1356101 := bbase (se 4 (by rfl) ⟨127134, by rfl⟩ : syracuseStep 1356101 = 254269) (by norm_num)
theorem B1520005 : Blo 599292 1520005 := bbase (se 4 (by rfl) ⟨142500, by rfl⟩ : syracuseStep 1520005 = 285001) (by norm_num)
theorem B1356173 : Blo 599292 1356173 := bbase (se 3 (by rfl) ⟨254282, by rfl⟩ : syracuseStep 1356173 = 508565) (by norm_num)
theorem B2306501 : Blo 599292 2306501 := bbase (se 4 (by rfl) ⟨216234, by rfl⟩ : syracuseStep 2306501 = 432469) (by norm_num)
theorem B3420629 : Blo 599292 3420629 := bbase (se 7 (by rfl) ⟨40085, by rfl⟩ : syracuseStep 3420629 = 80171) (by norm_num)
theorem B1356245 : Blo 599292 1356245 := bbase (se 7 (by rfl) ⟨15893, by rfl⟩ : syracuseStep 1356245 = 31787) (by norm_num)
theorem B1520117 : Blo 599292 1520117 := bbase (se 5 (by rfl) ⟨71255, by rfl⟩ : syracuseStep 1520117 = 142511) (by norm_num)
theorem B3650069 : Blo 599292 3650069 := bbase (se 6 (by rfl) ⟨85548, by rfl⟩ : syracuseStep 3650069 = 171097) (by norm_num)
theorem B9777685 : Blo 599292 9777685 := bbase (se 6 (by rfl) ⟨229164, by rfl⟩ : syracuseStep 9777685 = 458329) (by norm_num)
theorem B1356317 : Blo 599292 1356317 := bbase (se 3 (by rfl) ⟨254309, by rfl⟩ : syracuseStep 1356317 = 508619) (by norm_num)
theorem B1356389 : Blo 599292 1356389 := bbase (se 4 (by rfl) ⟨127161, by rfl⟩ : syracuseStep 1356389 = 254323) (by norm_num)
theorem B1356461 : Blo 599292 1356461 := bbase (se 3 (by rfl) ⟨254336, by rfl⟩ : syracuseStep 1356461 = 508673) (by norm_num)
theorem B4108981 : Blo 599292 4108981 := bbase (se 5 (by rfl) ⟨192608, by rfl⟩ : syracuseStep 4108981 = 385217) (by norm_num)
theorem B1520309 : Blo 599292 1520309 := bbase (se 5 (by rfl) ⟨71264, by rfl⟩ : syracuseStep 1520309 = 142529) (by norm_num)
theorem B1356533 : Blo 599292 1356533 := bbase (se 5 (by rfl) ⟨63587, by rfl⟩ : syracuseStep 1356533 = 127175) (by norm_num)
theorem B1356605 : Blo 599292 1356605 := bbase (se 3 (by rfl) ⟨254363, by rfl⟩ : syracuseStep 1356605 = 508727) (by norm_num)
theorem B1192781 : Blo 599292 1192781 := bbase (se 3 (by rfl) ⟨223646, by rfl⟩ : syracuseStep 1192781 = 447293) (by norm_num)
theorem B1356677 : Blo 599292 1356677 := bbase (se 4 (by rfl) ⟨127188, by rfl⟩ : syracuseStep 1356677 = 254377) (by norm_num)
theorem B1160101 : Blo 599292 1160101 := bbase (se 4 (by rfl) ⟨108759, by rfl⟩ : syracuseStep 1160101 = 217519) (by norm_num)
theorem B1356749 : Blo 599292 1356749 := bbase (se 3 (by rfl) ⟨254390, by rfl⟩ : syracuseStep 1356749 = 508781) (by norm_num)
theorem B1520653 : Blo 599292 1520653 := bbase (se 3 (by rfl) ⟨285122, by rfl⟩ : syracuseStep 1520653 = 570245) (by norm_num)
theorem B1356821 : Blo 599292 1356821 := bbase (se 6 (by rfl) ⟨31800, by rfl⟩ : syracuseStep 1356821 = 63601) (by norm_num)
theorem B1356893 : Blo 599292 1356893 := bbase (se 3 (by rfl) ⟨254417, by rfl⟩ : syracuseStep 1356893 = 508835) (by norm_num)
theorem B1520765 : Blo 599292 1520765 := bbase (se 3 (by rfl) ⟨285143, by rfl⟩ : syracuseStep 1520765 = 570287) (by norm_num)
theorem B2438309 : Blo 599292 2438309 := bbase (se 4 (by rfl) ⟨228591, by rfl⟩ : syracuseStep 2438309 = 457183) (by norm_num)
theorem B1356965 : Blo 599292 1356965 := bbase (se 4 (by rfl) ⟨127215, by rfl⟩ : syracuseStep 1356965 = 254431) (by norm_num)
theorem B1357037 : Blo 599292 1357037 := bbase (se 3 (by rfl) ⟨254444, by rfl⟩ : syracuseStep 1357037 = 508889) (by norm_num)
theorem B1357109 : Blo 599292 1357109 := bbase (se 5 (by rfl) ⟨63614, by rfl⟩ : syracuseStep 1357109 = 127229) (by norm_num)
theorem B1520957 : Blo 599292 1520957 := bbase (se 3 (by rfl) ⟨285179, by rfl⟩ : syracuseStep 1520957 = 570359) (by norm_num)
theorem B963917 : Blo 599292 963917 := bbase (se 3 (by rfl) ⟨180734, by rfl⟩ : syracuseStep 963917 = 361469) (by norm_num)
theorem B2569589 : Blo 599292 2569589 := bbase (se 5 (by rfl) ⟨120449, by rfl⟩ : syracuseStep 2569589 = 240899) (by norm_num)
theorem B1357181 : Blo 599292 1357181 := bbase (se 3 (by rfl) ⟨254471, by rfl⟩ : syracuseStep 1357181 = 508943) (by norm_num)
theorem B1357253 : Blo 599292 1357253 := bbase (se 4 (by rfl) ⟨127242, by rfl⟩ : syracuseStep 1357253 = 254485) (by norm_num)
theorem B964109 : Blo 599292 964109 := bbase (se 3 (by rfl) ⟨180770, by rfl⟩ : syracuseStep 964109 = 361541) (by norm_num)
theorem B1357325 : Blo 599292 1357325 := bbase (se 3 (by rfl) ⟨254498, by rfl⟩ : syracuseStep 1357325 = 508997) (by norm_num)
theorem B1357397 : Blo 599292 1357397 := bbase (se 8 (by rfl) ⟨7953, by rfl⟩ : syracuseStep 1357397 = 15907) (by norm_num)
theorem B1390189 : Blo 599292 1390189 := bbase (se 3 (by rfl) ⟨260660, by rfl⟩ : syracuseStep 1390189 = 521321) (by norm_num)
theorem B964237 : Blo 599292 964237 := bbase (se 3 (by rfl) ⟨180794, by rfl⟩ : syracuseStep 964237 = 361589) (by norm_num)
theorem B5125781 : Blo 599292 5125781 := bbase (se 6 (by rfl) ⟨120135, by rfl⟩ : syracuseStep 5125781 = 240271) (by norm_num)
theorem B1521301 : Blo 599292 1521301 := bbase (se 6 (by rfl) ⟨35655, by rfl⟩ : syracuseStep 1521301 = 71311) (by norm_num)
theorem B3847925 : Blo 599292 3847925 := bbase (se 5 (by rfl) ⟨180371, by rfl⟩ : syracuseStep 3847925 = 360743) (by norm_num)
theorem B1521413 : Blo 599292 1521413 := bbase (se 4 (by rfl) ⟨142632, by rfl⟩ : syracuseStep 1521413 = 285265) (by norm_num)
theorem B4568885 : Blo 599292 4568885 := bbase (se 5 (by rfl) ⟨214166, by rfl⟩ : syracuseStep 4568885 = 428333) (by norm_num)
theorem B898949 : Blo 599292 898949 := bbase (se 4 (by rfl) ⟨84276, by rfl⟩ : syracuseStep 898949 = 168553) (by norm_num)
theorem B898973 : Blo 599292 898973 := bbase (se 3 (by rfl) ⟨168557, by rfl⟩ : syracuseStep 898973 = 337115) (by norm_num)
theorem B898997 : Blo 599292 898997 := bbase (se 5 (by rfl) ⟨42140, by rfl⟩ : syracuseStep 898997 = 84281) (by norm_num)
theorem B1521605 : Blo 599292 1521605 := bbase (se 4 (by rfl) ⟨142650, by rfl⟩ : syracuseStep 1521605 = 285301) (by norm_num)
theorem B899021 : Blo 599292 899021 := bbase (se 3 (by rfl) ⟨168566, by rfl⟩ : syracuseStep 899021 = 337133) (by norm_num)
theorem B6862805 : Blo 599292 6862805 := bbase (se 7 (by rfl) ⟨80423, by rfl⟩ : syracuseStep 6862805 = 160847) (by norm_num)
theorem B899045 : Blo 599292 899045 := bbase (se 4 (by rfl) ⟨84285, by rfl⟩ : syracuseStep 899045 = 168571) (by norm_num)
theorem B899069 : Blo 599292 899069 := bbase (se 3 (by rfl) ⟨168575, by rfl⟩ : syracuseStep 899069 = 337151) (by norm_num)
theorem B899093 : Blo 599292 899093 := bbase (se 6 (by rfl) ⟨21072, by rfl⟩ : syracuseStep 899093 = 42145) (by norm_num)
theorem B899117 : Blo 599292 899117 := bbase (se 3 (by rfl) ⟨168584, by rfl⟩ : syracuseStep 899117 = 337169) (by norm_num)
theorem B899141 : Blo 599292 899141 := bbase (se 4 (by rfl) ⟨84294, by rfl⟩ : syracuseStep 899141 = 168589) (by norm_num)
theorem B899165 : Blo 599292 899165 := bbase (se 3 (by rfl) ⟨168593, by rfl⟩ : syracuseStep 899165 = 337187) (by norm_num)
theorem B899189 : Blo 599292 899189 := bbase (se 5 (by rfl) ⟨42149, by rfl⟩ : syracuseStep 899189 = 84299) (by norm_num)
theorem B1620101 : Blo 599292 1620101 := bbase (se 4 (by rfl) ⟨151884, by rfl⟩ : syracuseStep 1620101 = 303769) (by norm_num)
theorem B899213 : Blo 599292 899213 := bbase (se 3 (by rfl) ⟨168602, by rfl⟩ : syracuseStep 899213 = 337205) (by norm_num)
theorem B899237 : Blo 599292 899237 := bbase (se 4 (by rfl) ⟨84303, by rfl⟩ : syracuseStep 899237 = 168607) (by norm_num)
theorem B899261 : Blo 599292 899261 := bbase (se 3 (by rfl) ⟨168611, by rfl⟩ : syracuseStep 899261 = 337223) (by norm_num)
theorem B899285 : Blo 599292 899285 := bbase (se 7 (by rfl) ⟨10538, by rfl⟩ : syracuseStep 899285 = 21077) (by norm_num)
theorem B899309 : Blo 599292 899309 := bbase (se 3 (by rfl) ⟨168620, by rfl⟩ : syracuseStep 899309 = 337241) (by norm_num)
theorem B2275573 : Blo 599292 2275573 := bbase (se 5 (by rfl) ⟨106667, by rfl⟩ : syracuseStep 2275573 = 213335) (by norm_num)
theorem B899333 : Blo 599292 899333 := bbase (se 4 (by rfl) ⟨84312, by rfl⟩ : syracuseStep 899333 = 168625) (by norm_num)
theorem B964877 : Blo 599292 964877 := bbase (se 3 (by rfl) ⟨180914, by rfl⟩ : syracuseStep 964877 = 361829) (by norm_num)
theorem B899357 : Blo 599292 899357 := bbase (se 3 (by rfl) ⟨168629, by rfl⟩ : syracuseStep 899357 = 337259) (by norm_num)
theorem B1521949 : Blo 599292 1521949 := bbase (se 3 (by rfl) ⟨285365, by rfl⟩ : syracuseStep 1521949 = 570731) (by norm_num)
theorem B899381 : Blo 599292 899381 := bbase (se 5 (by rfl) ⟨42158, by rfl⟩ : syracuseStep 899381 = 84317) (by norm_num)
theorem B899405 : Blo 599292 899405 := bbase (se 3 (by rfl) ⟨168638, by rfl⟩ : syracuseStep 899405 = 337277) (by norm_num)
theorem B899429 : Blo 599292 899429 := bbase (se 4 (by rfl) ⟨84321, by rfl⟩ : syracuseStep 899429 = 168643) (by norm_num)
theorem B899453 : Blo 599292 899453 := bbase (se 3 (by rfl) ⟨168647, by rfl⟩ : syracuseStep 899453 = 337295) (by norm_num)
theorem B1522061 : Blo 599292 1522061 := bbase (se 3 (by rfl) ⟨285386, by rfl⟩ : syracuseStep 1522061 = 570773) (by norm_num)
theorem B899477 : Blo 599292 899477 := bbase (se 6 (by rfl) ⟨21081, by rfl⟩ : syracuseStep 899477 = 42163) (by norm_num)
theorem B899501 : Blo 599292 899501 := bbase (se 3 (by rfl) ⟨168656, by rfl⟩ : syracuseStep 899501 = 337313) (by norm_num)
theorem B899525 : Blo 599292 899525 := bbase (se 4 (by rfl) ⟨84330, by rfl⟩ : syracuseStep 899525 = 168661) (by norm_num)
theorem B899549 : Blo 599292 899549 := bbase (se 3 (by rfl) ⟨168665, by rfl⟩ : syracuseStep 899549 = 337331) (by norm_num)
theorem B899573 : Blo 599292 899573 := bbase (se 5 (by rfl) ⟨42167, by rfl⟩ : syracuseStep 899573 = 84335) (by norm_num)
theorem B899597 : Blo 599292 899597 := bbase (se 3 (by rfl) ⟨168674, by rfl⟩ : syracuseStep 899597 = 337349) (by norm_num)
theorem B2275877 : Blo 599292 2275877 := bbase (se 4 (by rfl) ⟨213363, by rfl⟩ : syracuseStep 2275877 = 426727) (by norm_num)
theorem B899621 : Blo 599292 899621 := bbase (se 4 (by rfl) ⟨84339, by rfl⟩ : syracuseStep 899621 = 168679) (by norm_num)
theorem B1620533 : Blo 599292 1620533 := bbase (se 5 (by rfl) ⟨75962, by rfl⟩ : syracuseStep 1620533 = 151925) (by norm_num)
theorem B899645 : Blo 599292 899645 := bbase (se 3 (by rfl) ⟨168683, by rfl⟩ : syracuseStep 899645 = 337367) (by norm_num)
theorem B1522253 : Blo 599292 1522253 := bbase (se 3 (by rfl) ⟨285422, by rfl⟩ : syracuseStep 1522253 = 570845) (by norm_num)
theorem B899669 : Blo 599292 899669 := bbase (se 8 (by rfl) ⟨5271, by rfl⟩ : syracuseStep 899669 = 10543) (by norm_num)
theorem B2964053 : Blo 599292 2964053 := bbase (se 8 (by rfl) ⟨17367, by rfl⟩ : syracuseStep 2964053 = 34735) (by norm_num)
theorem B899693 : Blo 599292 899693 := bbase (se 3 (by rfl) ⟨168692, by rfl⟩ : syracuseStep 899693 = 337385) (by norm_num)
theorem B3422837 : Blo 599292 3422837 := bbase (se 5 (by rfl) ⟨160445, by rfl⟩ : syracuseStep 3422837 = 320891) (by norm_num)
theorem B899717 : Blo 599292 899717 := bbase (se 4 (by rfl) ⟨84348, by rfl⟩ : syracuseStep 899717 = 168697) (by norm_num)
theorem B899741 : Blo 599292 899741 := bbase (se 3 (by rfl) ⟨168701, by rfl⟩ : syracuseStep 899741 = 337403) (by norm_num)
theorem B899765 : Blo 599292 899765 := bbase (se 5 (by rfl) ⟨42176, by rfl⟩ : syracuseStep 899765 = 84353) (by norm_num)
theorem B899789 : Blo 599292 899789 := bbase (se 3 (by rfl) ⟨168710, by rfl⟩ : syracuseStep 899789 = 337421) (by norm_num)
theorem B965333 : Blo 599292 965333 := bbase (se 7 (by rfl) ⟨11312, by rfl⟩ : syracuseStep 965333 = 22625) (by norm_num)
theorem B899813 : Blo 599292 899813 := bbase (se 4 (by rfl) ⟨84357, by rfl⟩ : syracuseStep 899813 = 168715) (by norm_num)
theorem B899837 : Blo 599292 899837 := bbase (se 3 (by rfl) ⟨168719, by rfl⟩ : syracuseStep 899837 = 337439) (by norm_num)
theorem B899861 : Blo 599292 899861 := bbase (se 6 (by rfl) ⟨21090, by rfl⟩ : syracuseStep 899861 = 42181) (by norm_num)
theorem B899885 : Blo 599292 899885 := bbase (se 3 (by rfl) ⟨168728, by rfl⟩ : syracuseStep 899885 = 337457) (by norm_num)
theorem B899909 : Blo 599292 899909 := bbase (se 4 (by rfl) ⟨84366, by rfl⟩ : syracuseStep 899909 = 168733) (by norm_num)
theorem B899933 : Blo 599292 899933 := bbase (se 3 (by rfl) ⟨168737, by rfl⟩ : syracuseStep 899933 = 337475) (by norm_num)
theorem B899957 : Blo 599292 899957 := bbase (se 5 (by rfl) ⟨42185, by rfl⟩ : syracuseStep 899957 = 84371) (by norm_num)
theorem B899981 : Blo 599292 899981 := bbase (se 3 (by rfl) ⟨168746, by rfl⟩ : syracuseStep 899981 = 337493) (by norm_num)
theorem B1620901 : Blo 599292 1620901 := bbase (se 4 (by rfl) ⟨151959, by rfl⟩ : syracuseStep 1620901 = 303919) (by norm_num)
theorem B900005 : Blo 599292 900005 := bbase (se 4 (by rfl) ⟨84375, by rfl⟩ : syracuseStep 900005 = 168751) (by norm_num)
theorem B1522597 : Blo 599292 1522597 := bbase (se 4 (by rfl) ⟨142743, by rfl⟩ : syracuseStep 1522597 = 285487) (by norm_num)
theorem B1031077 : Blo 599292 1031077 := bbase (se 4 (by rfl) ⟨96663, by rfl⟩ : syracuseStep 1031077 = 193327) (by norm_num)
theorem B965557 : Blo 599292 965557 := bbase (se 5 (by rfl) ⟨45260, by rfl⟩ : syracuseStep 965557 = 90521) (by norm_num)
theorem B900029 : Blo 599292 900029 := bbase (se 3 (by rfl) ⟨168755, by rfl⟩ : syracuseStep 900029 = 337511) (by norm_num)
theorem B900053 : Blo 599292 900053 := bbase (se 7 (by rfl) ⟨10547, by rfl⟩ : syracuseStep 900053 = 21095) (by norm_num)
theorem B900077 : Blo 599292 900077 := bbase (se 3 (by rfl) ⟨168764, by rfl⟩ : syracuseStep 900077 = 337529) (by norm_num)
theorem B965621 : Blo 599292 965621 := bbase (se 5 (by rfl) ⟨45263, by rfl⟩ : syracuseStep 965621 = 90527) (by norm_num)
theorem B900101 : Blo 599292 900101 := bbase (se 4 (by rfl) ⟨84384, by rfl⟩ : syracuseStep 900101 = 168769) (by norm_num)
theorem B1522709 : Blo 599292 1522709 := bbase (se 6 (by rfl) ⟨35688, by rfl⟩ : syracuseStep 1522709 = 71377) (by norm_num)
theorem B900125 : Blo 599292 900125 := bbase (se 3 (by rfl) ⟨168773, by rfl⟩ : syracuseStep 900125 = 337547) (by norm_num)
theorem B900149 : Blo 599292 900149 := bbase (se 5 (by rfl) ⟨42194, by rfl⟩ : syracuseStep 900149 = 84389) (by norm_num)
theorem B900173 : Blo 599292 900173 := bbase (se 3 (by rfl) ⟨168782, by rfl⟩ : syracuseStep 900173 = 337565) (by norm_num)
theorem B900197 : Blo 599292 900197 := bbase (se 4 (by rfl) ⟨84393, by rfl⟩ : syracuseStep 900197 = 168787) (by norm_num)
theorem B2571365 : Blo 599292 2571365 := bbase (se 4 (by rfl) ⟨241065, by rfl⟩ : syracuseStep 2571365 = 482131) (by norm_num)
theorem B965749 : Blo 599292 965749 := bbase (se 5 (by rfl) ⟨45269, by rfl⟩ : syracuseStep 965749 = 90539) (by norm_num)
theorem B900221 : Blo 599292 900221 := bbase (se 3 (by rfl) ⟨168791, by rfl⟩ : syracuseStep 900221 = 337583) (by norm_num)
theorem B900245 : Blo 599292 900245 := bbase (se 6 (by rfl) ⟨21099, by rfl⟩ : syracuseStep 900245 = 42199) (by norm_num)
theorem B900269 : Blo 599292 900269 := bbase (se 3 (by rfl) ⟨168800, by rfl⟩ : syracuseStep 900269 = 337601) (by norm_num)
theorem B900293 : Blo 599292 900293 := bbase (se 4 (by rfl) ⟨84402, by rfl⟩ : syracuseStep 900293 = 168805) (by norm_num)
theorem B1522901 : Blo 599292 1522901 := bbase (se 7 (by rfl) ⟨17846, by rfl⟩ : syracuseStep 1522901 = 35693) (by norm_num)
theorem B900317 : Blo 599292 900317 := bbase (se 3 (by rfl) ⟨168809, by rfl⟩ : syracuseStep 900317 = 337619) (by norm_num)
theorem B900341 : Blo 599292 900341 := bbase (se 5 (by rfl) ⟨42203, by rfl⟩ : syracuseStep 900341 = 84407) (by norm_num)
theorem B900365 : Blo 599292 900365 := bbase (se 3 (by rfl) ⟨168818, by rfl⟩ : syracuseStep 900365 = 337637) (by norm_num)
theorem B900389 : Blo 599292 900389 := bbase (se 4 (by rfl) ⟨84411, by rfl⟩ : syracuseStep 900389 = 168823) (by norm_num)
theorem B900413 : Blo 599292 900413 := bbase (se 3 (by rfl) ⟨168827, by rfl⟩ : syracuseStep 900413 = 337655) (by norm_num)
theorem B900437 : Blo 599292 900437 := bbase (se 11 (by rfl) ⟨659, by rfl⟩ : syracuseStep 900437 = 1319) (by norm_num)
theorem B900461 : Blo 599292 900461 := bbase (se 3 (by rfl) ⟨168836, by rfl⟩ : syracuseStep 900461 = 337673) (by norm_num)
theorem B900485 : Blo 599292 900485 := bbase (se 4 (by rfl) ⟨84420, by rfl⟩ : syracuseStep 900485 = 168841) (by norm_num)
theorem B900509 : Blo 599292 900509 := bbase (se 3 (by rfl) ⟨168845, by rfl⟩ : syracuseStep 900509 = 337691) (by norm_num)
theorem B2735525 : Blo 599292 2735525 := bbase (se 4 (by rfl) ⟨256455, by rfl⟩ : syracuseStep 2735525 = 512911) (by norm_num)
theorem B900533 : Blo 599292 900533 := bbase (se 5 (by rfl) ⟨42212, by rfl⟩ : syracuseStep 900533 = 84425) (by norm_num)
theorem B900557 : Blo 599292 900557 := bbase (se 3 (by rfl) ⟨168854, by rfl⟩ : syracuseStep 900557 = 337709) (by norm_num)
theorem B900581 : Blo 599292 900581 := bbase (se 4 (by rfl) ⟨84429, by rfl⟩ : syracuseStep 900581 = 168859) (by norm_num)
theorem B900605 : Blo 599292 900605 := bbase (se 3 (by rfl) ⟨168863, by rfl⟩ : syracuseStep 900605 = 337727) (by norm_num)
theorem B900629 : Blo 599292 900629 := bbase (se 6 (by rfl) ⟨21108, by rfl⟩ : syracuseStep 900629 = 42217) (by norm_num)
theorem B900653 : Blo 599292 900653 := bbase (se 3 (by rfl) ⟨168872, by rfl⟩ : syracuseStep 900653 = 337745) (by norm_num)
theorem B1523245 : Blo 599292 1523245 := bbase (se 3 (by rfl) ⟨285608, by rfl⟩ : syracuseStep 1523245 = 571217) (by norm_num)
theorem B900677 : Blo 599292 900677 := bbase (se 4 (by rfl) ⟨84438, by rfl⟩ : syracuseStep 900677 = 168877) (by norm_num)
theorem B900701 : Blo 599292 900701 := bbase (se 3 (by rfl) ⟨168881, by rfl⟩ : syracuseStep 900701 = 337763) (by norm_num)
theorem B2637413 : Blo 599292 2637413 := bbase (se 4 (by rfl) ⟨247257, by rfl⟩ : syracuseStep 2637413 = 494515) (by norm_num)
theorem B900725 : Blo 599292 900725 := bbase (se 5 (by rfl) ⟨42221, by rfl⟩ : syracuseStep 900725 = 84443) (by norm_num)
theorem B900749 : Blo 599292 900749 := bbase (se 3 (by rfl) ⟨168890, by rfl⟩ : syracuseStep 900749 = 337781) (by norm_num)
theorem B1523357 : Blo 599292 1523357 := bbase (se 3 (by rfl) ⟨285629, by rfl⟩ : syracuseStep 1523357 = 571259) (by norm_num)
theorem B1031837 : Blo 599292 1031837 := bbase (se 3 (by rfl) ⟨193469, by rfl⟩ : syracuseStep 1031837 = 386939) (by norm_num)
theorem B900773 : Blo 599292 900773 := bbase (se 4 (by rfl) ⟨84447, by rfl⟩ : syracuseStep 900773 = 168895) (by norm_num)
theorem B900797 : Blo 599292 900797 := bbase (se 3 (by rfl) ⟨168899, by rfl⟩ : syracuseStep 900797 = 337799) (by norm_num)
theorem B900821 : Blo 599292 900821 := bbase (se 7 (by rfl) ⟨10556, by rfl⟩ : syracuseStep 900821 = 21113) (by norm_num)
theorem B900845 : Blo 599292 900845 := bbase (se 3 (by rfl) ⟨168908, by rfl⟩ : syracuseStep 900845 = 337817) (by norm_num)
theorem B900869 : Blo 599292 900869 := bbase (se 4 (by rfl) ⟨84456, by rfl⟩ : syracuseStep 900869 = 168913) (by norm_num)
theorem B900893 : Blo 599292 900893 := bbase (se 3 (by rfl) ⟨168917, by rfl⟩ : syracuseStep 900893 = 337835) (by norm_num)
theorem B900917 : Blo 599292 900917 := bbase (se 5 (by rfl) ⟨42230, by rfl⟩ : syracuseStep 900917 = 84461) (by norm_num)
theorem B900941 : Blo 599292 900941 := bbase (se 3 (by rfl) ⟨168926, by rfl⟩ : syracuseStep 900941 = 337853) (by norm_num)
theorem B1523549 : Blo 599292 1523549 := bbase (se 3 (by rfl) ⟨285665, by rfl⟩ : syracuseStep 1523549 = 571331) (by norm_num)
theorem B900965 : Blo 599292 900965 := bbase (se 4 (by rfl) ⟨84465, by rfl⟩ : syracuseStep 900965 = 168931) (by norm_num)
theorem B900989 : Blo 599292 900989 := bbase (se 3 (by rfl) ⟨168935, by rfl⟩ : syracuseStep 900989 = 337871) (by norm_num)
theorem B901013 : Blo 599292 901013 := bbase (se 6 (by rfl) ⟨21117, by rfl⟩ : syracuseStep 901013 = 42235) (by norm_num)
theorem B901037 : Blo 599292 901037 := bbase (se 3 (by rfl) ⟨168944, by rfl⟩ : syracuseStep 901037 = 337889) (by norm_num)
theorem B901061 : Blo 599292 901061 := bbase (se 4 (by rfl) ⟨84474, by rfl⟩ : syracuseStep 901061 = 168949) (by norm_num)
theorem B11583445 : Blo 599292 11583445 := bbase (se 7 (by rfl) ⟨135743, by rfl⟩ : syracuseStep 11583445 = 271487) (by norm_num)
theorem B901085 : Blo 599292 901085 := bbase (se 3 (by rfl) ⟨168953, by rfl⟩ : syracuseStep 901085 = 337907) (by norm_num)
theorem B901109 : Blo 599292 901109 := bbase (se 5 (by rfl) ⟨42239, by rfl⟩ : syracuseStep 901109 = 84479) (by norm_num)
theorem B901133 : Blo 599292 901133 := bbase (se 3 (by rfl) ⟨168962, by rfl⟩ : syracuseStep 901133 = 337925) (by norm_num)
theorem B901157 : Blo 599292 901157 := bbase (se 4 (by rfl) ⟨84483, by rfl⟩ : syracuseStep 901157 = 168967) (by norm_num)
theorem B901181 : Blo 599292 901181 := bbase (se 3 (by rfl) ⟨168971, by rfl⟩ : syracuseStep 901181 = 337943) (by norm_num)
theorem B2572357 : Blo 599292 2572357 := bbase (se 4 (by rfl) ⟨241158, by rfl⟩ : syracuseStep 2572357 = 482317) (by norm_num)
theorem B901205 : Blo 599292 901205 := bbase (se 8 (by rfl) ⟨5280, by rfl⟩ : syracuseStep 901205 = 10561) (by norm_num)
theorem B901229 : Blo 599292 901229 := bbase (se 3 (by rfl) ⟨168980, by rfl⟩ : syracuseStep 901229 = 337961) (by norm_num)
theorem B901253 : Blo 599292 901253 := bbase (se 4 (by rfl) ⟨84492, by rfl⟩ : syracuseStep 901253 = 168985) (by norm_num)
theorem B901277 : Blo 599292 901277 := bbase (se 3 (by rfl) ⟨168989, by rfl⟩ : syracuseStep 901277 = 337979) (by norm_num)
theorem B901301 : Blo 599292 901301 := bbase (se 5 (by rfl) ⟨42248, by rfl⟩ : syracuseStep 901301 = 84497) (by norm_num)
theorem B1523893 : Blo 599292 1523893 := bbase (se 5 (by rfl) ⟨71432, by rfl⟩ : syracuseStep 1523893 = 142865) (by norm_num)
theorem B901325 : Blo 599292 901325 := bbase (se 3 (by rfl) ⟨168998, by rfl⟩ : syracuseStep 901325 = 337997) (by norm_num)
theorem B901349 : Blo 599292 901349 := bbase (se 4 (by rfl) ⟨84501, by rfl⟩ : syracuseStep 901349 = 169003) (by norm_num)
theorem B901373 : Blo 599292 901373 := bbase (se 3 (by rfl) ⟨169007, by rfl⟩ : syracuseStep 901373 = 338015) (by norm_num)
theorem B901397 : Blo 599292 901397 := bbase (se 6 (by rfl) ⟨21126, by rfl⟩ : syracuseStep 901397 = 42253) (by norm_num)
theorem B1524005 : Blo 599292 1524005 := bbase (se 4 (by rfl) ⟨142875, by rfl⟩ : syracuseStep 1524005 = 285751) (by norm_num)
theorem B901421 : Blo 599292 901421 := bbase (se 3 (by rfl) ⟨169016, by rfl⟩ : syracuseStep 901421 = 338033) (by norm_num)
theorem B2736437 : Blo 599292 2736437 := bbase (se 5 (by rfl) ⟨128270, by rfl⟩ : syracuseStep 2736437 = 256541) (by norm_num)
theorem B901445 : Blo 599292 901445 := bbase (se 4 (by rfl) ⟨84510, by rfl⟩ : syracuseStep 901445 = 169021) (by norm_num)
theorem B901469 : Blo 599292 901469 := bbase (se 3 (by rfl) ⟨169025, by rfl⟩ : syracuseStep 901469 = 338051) (by norm_num)
theorem B901493 : Blo 599292 901493 := bbase (se 5 (by rfl) ⟨42257, by rfl⟩ : syracuseStep 901493 = 84515) (by norm_num)
theorem B901517 : Blo 599292 901517 := bbase (se 3 (by rfl) ⟨169034, by rfl⟩ : syracuseStep 901517 = 338069) (by norm_num)
theorem B901541 : Blo 599292 901541 := bbase (se 4 (by rfl) ⟨84519, by rfl⟩ : syracuseStep 901541 = 169039) (by norm_num)
theorem B901565 : Blo 599292 901565 := bbase (se 3 (by rfl) ⟨169043, by rfl⟩ : syracuseStep 901565 = 338087) (by norm_num)
theorem B10961365 : Blo 599292 10961365 := bbase (se 7 (by rfl) ⟨128453, by rfl⟩ : syracuseStep 10961365 = 256907) (by norm_num)
theorem B901589 : Blo 599292 901589 := bbase (se 7 (by rfl) ⟨10565, by rfl⟩ : syracuseStep 901589 = 21131) (by norm_num)
theorem B1524197 : Blo 599292 1524197 := bbase (se 4 (by rfl) ⟨142893, by rfl⟩ : syracuseStep 1524197 = 285787) (by norm_num)
theorem B901613 : Blo 599292 901613 := bbase (se 3 (by rfl) ⟨169052, by rfl⟩ : syracuseStep 901613 = 338105) (by norm_num)
theorem B901637 : Blo 599292 901637 := bbase (se 4 (by rfl) ⟨84528, by rfl⟩ : syracuseStep 901637 = 169057) (by norm_num)
theorem B901661 : Blo 599292 901661 := bbase (se 3 (by rfl) ⟨169061, by rfl⟩ : syracuseStep 901661 = 338123) (by norm_num)
theorem B5128757 : Blo 599292 5128757 := bbase (se 5 (by rfl) ⟨240410, by rfl⟩ : syracuseStep 5128757 = 480821) (by norm_num)
theorem B901685 : Blo 599292 901685 := bbase (se 5 (by rfl) ⟨42266, by rfl⟩ : syracuseStep 901685 = 84533) (by norm_num)
theorem B2114117 : Blo 599292 2114117 := bbase (se 4 (by rfl) ⟨198198, by rfl⟩ : syracuseStep 2114117 = 396397) (by norm_num)
theorem B901709 : Blo 599292 901709 := bbase (se 3 (by rfl) ⟨169070, by rfl⟩ : syracuseStep 901709 = 338141) (by norm_num)
theorem B2277989 : Blo 599292 2277989 := bbase (se 4 (by rfl) ⟨213561, by rfl⟩ : syracuseStep 2277989 = 427123) (by norm_num)
theorem B901733 : Blo 599292 901733 := bbase (se 4 (by rfl) ⟨84537, by rfl⟩ : syracuseStep 901733 = 169075) (by norm_num)
theorem B901757 : Blo 599292 901757 := bbase (se 3 (by rfl) ⟨169079, by rfl⟩ : syracuseStep 901757 = 338159) (by norm_num)
theorem B901781 : Blo 599292 901781 := bbase (se 6 (by rfl) ⟨21135, by rfl⟩ : syracuseStep 901781 = 42271) (by norm_num)
theorem B901805 : Blo 599292 901805 := bbase (se 3 (by rfl) ⟨169088, by rfl⟩ : syracuseStep 901805 = 338177) (by norm_num)
theorem B901829 : Blo 599292 901829 := bbase (se 4 (by rfl) ⟨84546, by rfl⟩ : syracuseStep 901829 = 169093) (by norm_num)
theorem B901853 : Blo 599292 901853 := bbase (se 3 (by rfl) ⟨169097, by rfl⟩ : syracuseStep 901853 = 338195) (by norm_num)
theorem B901877 : Blo 599292 901877 := bbase (se 5 (by rfl) ⟨42275, by rfl⟩ : syracuseStep 901877 = 84551) (by norm_num)
theorem B901901 : Blo 599292 901901 := bbase (se 3 (by rfl) ⟨169106, by rfl⟩ : syracuseStep 901901 = 338213) (by norm_num)
theorem B901925 : Blo 599292 901925 := bbase (se 4 (by rfl) ⟨84555, by rfl⟩ : syracuseStep 901925 = 169111) (by norm_num)
theorem B1393453 : Blo 599292 1393453 := bbase (se 3 (by rfl) ⟨261272, by rfl⟩ : syracuseStep 1393453 = 522545) (by norm_num)
theorem B901949 : Blo 599292 901949 := bbase (se 3 (by rfl) ⟨169115, by rfl⟩ : syracuseStep 901949 = 338231) (by norm_num)
theorem B1524541 : Blo 599292 1524541 := bbase (se 3 (by rfl) ⟨285851, by rfl⟩ : syracuseStep 1524541 = 571703) (by norm_num)
theorem B901973 : Blo 599292 901973 := bbase (se 9 (by rfl) ⟨2642, by rfl⟩ : syracuseStep 901973 = 5285) (by norm_num)
theorem B901997 : Blo 599292 901997 := bbase (se 3 (by rfl) ⟨169124, by rfl⟩ : syracuseStep 901997 = 338249) (by norm_num)
theorem B2278277 : Blo 599292 2278277 := bbase (se 4 (by rfl) ⟨213588, by rfl⟩ : syracuseStep 2278277 = 427177) (by norm_num)
theorem B902021 : Blo 599292 902021 := bbase (se 4 (by rfl) ⟨84564, by rfl⟩ : syracuseStep 902021 = 169129) (by norm_num)
theorem B902045 : Blo 599292 902045 := bbase (se 3 (by rfl) ⟨169133, by rfl⟩ : syracuseStep 902045 = 338267) (by norm_num)
theorem B1524653 : Blo 599292 1524653 := bbase (se 3 (by rfl) ⟨285872, by rfl⟩ : syracuseStep 1524653 = 571745) (by norm_num)
theorem B902069 : Blo 599292 902069 := bbase (se 5 (by rfl) ⟨42284, by rfl⟩ : syracuseStep 902069 = 84569) (by norm_num)
theorem B902093 : Blo 599292 902093 := bbase (se 3 (by rfl) ⟨169142, by rfl⟩ : syracuseStep 902093 = 338285) (by norm_num)
theorem B836573 : Blo 599292 836573 := bbase (se 3 (by rfl) ⟨156857, by rfl⟩ : syracuseStep 836573 = 313715) (by norm_num)
theorem B902117 : Blo 599292 902117 := bbase (se 4 (by rfl) ⟨84573, by rfl⟩ : syracuseStep 902117 = 169147) (by norm_num)
theorem B902141 : Blo 599292 902141 := bbase (se 3 (by rfl) ⟨169151, by rfl⟩ : syracuseStep 902141 = 338303) (by norm_num)
theorem B902165 : Blo 599292 902165 := bbase (se 6 (by rfl) ⟨21144, by rfl⟩ : syracuseStep 902165 = 42289) (by norm_num)
theorem B902189 : Blo 599292 902189 := bbase (se 3 (by rfl) ⟨169160, by rfl⟩ : syracuseStep 902189 = 338321) (by norm_num)
theorem B902213 : Blo 599292 902213 := bbase (se 4 (by rfl) ⟨84582, by rfl⟩ : syracuseStep 902213 = 169165) (by norm_num)
theorem B902237 : Blo 599292 902237 := bbase (se 3 (by rfl) ⟨169169, by rfl⟩ : syracuseStep 902237 = 338339) (by norm_num)
theorem B1524845 : Blo 599292 1524845 := bbase (se 3 (by rfl) ⟨285908, by rfl⟩ : syracuseStep 1524845 = 571817) (by norm_num)
theorem B902261 : Blo 599292 902261 := bbase (se 5 (by rfl) ⟨42293, by rfl⟩ : syracuseStep 902261 = 84587) (by norm_num)
theorem B902285 : Blo 599292 902285 := bbase (se 3 (by rfl) ⟨169178, by rfl⟩ : syracuseStep 902285 = 338357) (by norm_num)
theorem B902309 : Blo 599292 902309 := bbase (se 4 (by rfl) ⟨84591, by rfl⟩ : syracuseStep 902309 = 169183) (by norm_num)
theorem B902333 : Blo 599292 902333 := bbase (se 3 (by rfl) ⟨169187, by rfl⟩ : syracuseStep 902333 = 338375) (by norm_num)
theorem B771277 : Blo 599292 771277 := bbase (se 3 (by rfl) ⟨144614, by rfl⟩ : syracuseStep 771277 = 289229) (by norm_num)
theorem B902357 : Blo 599292 902357 := bbase (se 7 (by rfl) ⟨10574, by rfl⟩ : syracuseStep 902357 = 21149) (by norm_num)
theorem B902381 : Blo 599292 902381 := bbase (se 3 (by rfl) ⟨169196, by rfl⟩ : syracuseStep 902381 = 338393) (by norm_num)
theorem B902405 : Blo 599292 902405 := bbase (se 4 (by rfl) ⟨84600, by rfl⟩ : syracuseStep 902405 = 169201) (by norm_num)
theorem B902429 : Blo 599292 902429 := bbase (se 3 (by rfl) ⟨169205, by rfl⟩ : syracuseStep 902429 = 338411) (by norm_num)
theorem B902453 : Blo 599292 902453 := bbase (se 5 (by rfl) ⟨42302, by rfl⟩ : syracuseStep 902453 = 84605) (by norm_num)
theorem B902477 : Blo 599292 902477 := bbase (se 3 (by rfl) ⟨169214, by rfl⟩ : syracuseStep 902477 = 338429) (by norm_num)
theorem B902501 : Blo 599292 902501 := bbase (se 4 (by rfl) ⟨84609, by rfl⟩ : syracuseStep 902501 = 169219) (by norm_num)
theorem B902525 : Blo 599292 902525 := bbase (se 3 (by rfl) ⟨169223, by rfl⟩ : syracuseStep 902525 = 338447) (by norm_num)
theorem B902549 : Blo 599292 902549 := bbase (se 6 (by rfl) ⟨21153, by rfl⟩ : syracuseStep 902549 = 42307) (by norm_num)
theorem B902573 : Blo 599292 902573 := bbase (se 3 (by rfl) ⟨169232, by rfl⟩ : syracuseStep 902573 = 338465) (by norm_num)
theorem B902597 : Blo 599292 902597 := bbase (se 4 (by rfl) ⟨84618, by rfl⟩ : syracuseStep 902597 = 169237) (by norm_num)
theorem B1525189 : Blo 599292 1525189 := bbase (se 4 (by rfl) ⟨142986, by rfl⟩ : syracuseStep 1525189 = 285973) (by norm_num)
theorem B607709 : Blo 599292 607709 := bbase (se 3 (by rfl) ⟨113945, by rfl⟩ : syracuseStep 607709 = 227891) (by norm_num)
theorem B902621 : Blo 599292 902621 := bbase (se 3 (by rfl) ⟨169241, by rfl⟩ : syracuseStep 902621 = 338483) (by norm_num)
theorem B902645 : Blo 599292 902645 := bbase (se 5 (by rfl) ⟨42311, by rfl⟩ : syracuseStep 902645 = 84623) (by norm_num)
theorem B902669 : Blo 599292 902669 := bbase (se 3 (by rfl) ⟨169250, by rfl⟩ : syracuseStep 902669 = 338501) (by norm_num)
theorem B902693 : Blo 599292 902693 := bbase (se 4 (by rfl) ⟨84627, by rfl⟩ : syracuseStep 902693 = 169255) (by norm_num)
theorem B1525301 : Blo 599292 1525301 := bbase (se 5 (by rfl) ⟨71498, by rfl⟩ : syracuseStep 1525301 = 142997) (by norm_num)
theorem B902717 : Blo 599292 902717 := bbase (se 3 (by rfl) ⟨169259, by rfl⟩ : syracuseStep 902717 = 338519) (by norm_num)
theorem B1099333 : Blo 599292 1099333 := bbase (se 4 (by rfl) ⟨103062, by rfl⟩ : syracuseStep 1099333 = 206125) (by norm_num)
theorem B902741 : Blo 599292 902741 := bbase (se 8 (by rfl) ⟨5289, by rfl⟩ : syracuseStep 902741 = 10579) (by norm_num)
theorem B2475605 : Blo 599292 2475605 := bbase (se 8 (by rfl) ⟨14505, by rfl⟩ : syracuseStep 2475605 = 29011) (by norm_num)
theorem B902765 : Blo 599292 902765 := bbase (se 3 (by rfl) ⟨169268, by rfl⟩ : syracuseStep 902765 = 338537) (by norm_num)
theorem B902789 : Blo 599292 902789 := bbase (se 4 (by rfl) ⟨84636, by rfl⟩ : syracuseStep 902789 = 169273) (by norm_num)
theorem B902813 : Blo 599292 902813 := bbase (se 3 (by rfl) ⟨169277, by rfl⟩ : syracuseStep 902813 = 338555) (by norm_num)
theorem B902837 : Blo 599292 902837 := bbase (se 5 (by rfl) ⟨42320, by rfl⟩ : syracuseStep 902837 = 84641) (by norm_num)
theorem B902861 : Blo 599292 902861 := bbase (se 3 (by rfl) ⟨169286, by rfl⟩ : syracuseStep 902861 = 338573) (by norm_num)
theorem B902885 : Blo 599292 902885 := bbase (se 4 (by rfl) ⟨84645, by rfl⟩ : syracuseStep 902885 = 169291) (by norm_num)
theorem B640757 : Blo 599292 640757 := bbase (se 5 (by rfl) ⟨30035, by rfl⟩ : syracuseStep 640757 = 60071) (by norm_num)
theorem B1525493 : Blo 599292 1525493 := bbase (se 5 (by rfl) ⟨71507, by rfl⟩ : syracuseStep 1525493 = 143015) (by norm_num)
theorem B902909 : Blo 599292 902909 := bbase (se 3 (by rfl) ⟨169295, by rfl⟩ : syracuseStep 902909 = 338591) (by norm_num)
theorem B902933 : Blo 599292 902933 := bbase (se 6 (by rfl) ⟨21162, by rfl⟩ : syracuseStep 902933 = 42325) (by norm_num)
theorem B902957 : Blo 599292 902957 := bbase (se 3 (by rfl) ⟨169304, by rfl⟩ : syracuseStep 902957 = 338609) (by norm_num)
theorem B902981 : Blo 599292 902981 := bbase (se 4 (by rfl) ⟨84654, by rfl⟩ : syracuseStep 902981 = 169309) (by norm_num)
theorem B903005 : Blo 599292 903005 := bbase (se 3 (by rfl) ⟨169313, by rfl⟩ : syracuseStep 903005 = 338627) (by norm_num)
theorem B903029 : Blo 599292 903029 := bbase (se 5 (by rfl) ⟨42329, by rfl⟩ : syracuseStep 903029 = 84659) (by norm_num)
theorem B903053 : Blo 599292 903053 := bbase (se 3 (by rfl) ⟨169322, by rfl⟩ : syracuseStep 903053 = 338645) (by norm_num)
theorem B903077 : Blo 599292 903077 := bbase (se 4 (by rfl) ⟨84663, by rfl⟩ : syracuseStep 903077 = 169327) (by norm_num)
theorem B903101 : Blo 599292 903101 := bbase (se 3 (by rfl) ⟨169331, by rfl⟩ : syracuseStep 903101 = 338663) (by norm_num)
theorem B903125 : Blo 599292 903125 := bbase (se 7 (by rfl) ⟨10583, by rfl⟩ : syracuseStep 903125 = 21167) (by norm_num)
theorem B903149 : Blo 599292 903149 := bbase (se 3 (by rfl) ⟨169340, by rfl⟩ : syracuseStep 903149 = 338681) (by norm_num)
theorem B903173 : Blo 599292 903173 := bbase (se 4 (by rfl) ⟨84672, by rfl⟩ : syracuseStep 903173 = 169345) (by norm_num)
theorem B903197 : Blo 599292 903197 := bbase (se 3 (by rfl) ⟨169349, by rfl⟩ : syracuseStep 903197 = 338699) (by norm_num)
theorem B2279461 : Blo 599292 2279461 := bbase (se 4 (by rfl) ⟨213699, by rfl⟩ : syracuseStep 2279461 = 427399) (by norm_num)
theorem B3655733 : Blo 599292 3655733 := bbase (se 5 (by rfl) ⟨171362, by rfl⟩ : syracuseStep 3655733 = 342725) (by norm_num)
theorem B903221 : Blo 599292 903221 := bbase (se 5 (by rfl) ⟨42338, by rfl⟩ : syracuseStep 903221 = 84677) (by norm_num)
theorem B903245 : Blo 599292 903245 := bbase (se 3 (by rfl) ⟨169358, by rfl⟩ : syracuseStep 903245 = 338717) (by norm_num)
theorem B1525837 : Blo 599292 1525837 := bbase (se 3 (by rfl) ⟨286094, by rfl⟩ : syracuseStep 1525837 = 572189) (by norm_num)
theorem B608357 : Blo 599292 608357 := bbase (se 4 (by rfl) ⟨57033, by rfl⟩ : syracuseStep 608357 = 114067) (by norm_num)
theorem B903269 : Blo 599292 903269 := bbase (se 4 (by rfl) ⟨84681, by rfl⟩ : syracuseStep 903269 = 169363) (by norm_num)
theorem B608365 : Blo 599292 608365 := bbase (se 3 (by rfl) ⟨114068, by rfl⟩ : syracuseStep 608365 = 228137) (by norm_num)
theorem B903293 : Blo 599292 903293 := bbase (se 3 (by rfl) ⟨169367, by rfl⟩ : syracuseStep 903293 = 338735) (by norm_num)
theorem B903317 : Blo 599292 903317 := bbase (se 6 (by rfl) ⟨21171, by rfl⟩ : syracuseStep 903317 = 42343) (by norm_num)
theorem B4638869 : Blo 599292 4638869 := bbase (se 6 (by rfl) ⟨108723, by rfl⟩ : syracuseStep 4638869 = 217447) (by norm_num)
theorem B903341 : Blo 599292 903341 := bbase (se 3 (by rfl) ⟨169376, by rfl⟩ : syracuseStep 903341 = 338753) (by norm_num)
theorem B641201 : Blo 599292 641201 := bbase (se 2 (by rfl) ⟨240450, by rfl⟩ : syracuseStep 641201 = 480901) (by norm_num)
theorem B1525949 : Blo 599292 1525949 := bbase (se 3 (by rfl) ⟨286115, by rfl⟩ : syracuseStep 1525949 = 572231) (by norm_num)
theorem B903365 : Blo 599292 903365 := bbase (se 4 (by rfl) ⟨84690, by rfl⟩ : syracuseStep 903365 = 169381) (by norm_num)
theorem B903389 : Blo 599292 903389 := bbase (se 3 (by rfl) ⟨169385, by rfl⟩ : syracuseStep 903389 = 338771) (by norm_num)
theorem B903413 : Blo 599292 903413 := bbase (se 5 (by rfl) ⟨42347, by rfl⟩ : syracuseStep 903413 = 84695) (by norm_num)
theorem B903437 : Blo 599292 903437 := bbase (se 3 (by rfl) ⟨169394, by rfl⟩ : syracuseStep 903437 = 338789) (by norm_num)
theorem B903461 : Blo 599292 903461 := bbase (se 4 (by rfl) ⟨84699, by rfl⟩ : syracuseStep 903461 = 169399) (by norm_num)
theorem B903485 : Blo 599292 903485 := bbase (se 3 (by rfl) ⟨169403, by rfl⟩ : syracuseStep 903485 = 338807) (by norm_num)
theorem B2279765 : Blo 599292 2279765 := bbase (se 10 (by rfl) ⟨3339, by rfl⟩ : syracuseStep 2279765 = 6679) (by norm_num)
theorem B903509 : Blo 599292 903509 := bbase (se 10 (by rfl) ⟨1323, by rfl⟩ : syracuseStep 903509 = 2647) (by norm_num)
theorem B772445 : Blo 599292 772445 := bbase (se 3 (by rfl) ⟨144833, by rfl⟩ : syracuseStep 772445 = 289667) (by norm_num)
theorem B903533 : Blo 599292 903533 := bbase (se 3 (by rfl) ⟨169412, by rfl⟩ : syracuseStep 903533 = 338825) (by norm_num)
theorem B1526141 : Blo 599292 1526141 := bbase (se 3 (by rfl) ⟨286151, by rfl⟩ : syracuseStep 1526141 = 572303) (by norm_num)
theorem B903557 : Blo 599292 903557 := bbase (se 4 (by rfl) ⟨84708, by rfl⟩ : syracuseStep 903557 = 169417) (by norm_num)
theorem B903581 : Blo 599292 903581 := bbase (se 3 (by rfl) ⟨169421, by rfl⟩ : syracuseStep 903581 = 338843) (by norm_num)
theorem B641449 : Blo 599292 641449 := bbase (se 2 (by rfl) ⟨240543, by rfl⟩ : syracuseStep 641449 = 481087) (by norm_num)
theorem B674221 : Blo 599292 674221 := bbase (se 3 (by rfl) ⟨126416, by rfl⟩ : syracuseStep 674221 = 252833) (by norm_num)
theorem B903605 : Blo 599292 903605 := bbase (se 5 (by rfl) ⟨42356, by rfl⟩ : syracuseStep 903605 = 84713) (by norm_num)
theorem B903629 : Blo 599292 903629 := bbase (se 3 (by rfl) ⟨169430, by rfl⟩ : syracuseStep 903629 = 338861) (by norm_num)
theorem B674257 : Blo 599292 674257 := bbase (se 2 (by rfl) ⟨252846, by rfl⟩ : syracuseStep 674257 = 505693) (by norm_num)
theorem B903653 : Blo 599292 903653 := bbase (se 4 (by rfl) ⟨84717, by rfl⟩ : syracuseStep 903653 = 169435) (by norm_num)
theorem B674293 : Blo 599292 674293 := bbase (se 5 (by rfl) ⟨31607, by rfl⟩ : syracuseStep 674293 = 63215) (by norm_num)
theorem B903677 : Blo 599292 903677 := bbase (se 3 (by rfl) ⟨169439, by rfl⟩ : syracuseStep 903677 = 338879) (by norm_num)
theorem B2476565 : Blo 599292 2476565 := bbase (se 6 (by rfl) ⟨58044, by rfl⟩ : syracuseStep 2476565 = 116089) (by norm_num)
theorem B903701 : Blo 599292 903701 := bbase (se 6 (by rfl) ⟨21180, by rfl⟩ : syracuseStep 903701 = 42361) (by norm_num)
theorem B674329 : Blo 599292 674329 := bbase (se 2 (by rfl) ⟨252873, by rfl⟩ : syracuseStep 674329 = 505747) (by norm_num)
theorem B903725 : Blo 599292 903725 := bbase (se 3 (by rfl) ⟨169448, by rfl⟩ : syracuseStep 903725 = 338897) (by norm_num)
theorem B674365 : Blo 599292 674365 := bbase (se 3 (by rfl) ⟨126443, by rfl⟩ : syracuseStep 674365 = 252887) (by norm_num)
theorem B903749 : Blo 599292 903749 := bbase (se 4 (by rfl) ⟨84726, by rfl⟩ : syracuseStep 903749 = 169453) (by norm_num)
theorem B903773 : Blo 599292 903773 := bbase (se 3 (by rfl) ⟨169457, by rfl⟩ : syracuseStep 903773 = 338915) (by norm_num)
theorem B674401 : Blo 599292 674401 := bbase (se 2 (by rfl) ⟨252900, by rfl⟩ : syracuseStep 674401 = 505801) (by norm_num)
theorem B903797 : Blo 599292 903797 := bbase (se 5 (by rfl) ⟨42365, by rfl⟩ : syracuseStep 903797 = 84731) (by norm_num)
theorem B674437 : Blo 599292 674437 := bbase (se 4 (by rfl) ⟨63228, by rfl⟩ : syracuseStep 674437 = 126457) (by norm_num)
theorem B903821 : Blo 599292 903821 := bbase (se 3 (by rfl) ⟨169466, by rfl⟩ : syracuseStep 903821 = 338933) (by norm_num)
theorem B903845 : Blo 599292 903845 := bbase (se 4 (by rfl) ⟨84735, by rfl⟩ : syracuseStep 903845 = 169471) (by norm_num)
theorem B674473 : Blo 599292 674473 := bbase (se 2 (by rfl) ⟨252927, by rfl⟩ : syracuseStep 674473 = 505855) (by norm_num)
theorem B608941 : Blo 599292 608941 := bbase (se 3 (by rfl) ⟨114176, by rfl⟩ : syracuseStep 608941 = 228353) (by norm_num)
theorem B903869 : Blo 599292 903869 := bbase (se 3 (by rfl) ⟨169475, by rfl⟩ : syracuseStep 903869 = 338951) (by norm_num)
theorem B674509 : Blo 599292 674509 := bbase (se 3 (by rfl) ⟨126470, by rfl⟩ : syracuseStep 674509 = 252941) (by norm_num)
theorem B903893 : Blo 599292 903893 := bbase (se 7 (by rfl) ⟨10592, by rfl⟩ : syracuseStep 903893 = 21185) (by norm_num)
theorem B1526485 : Blo 599292 1526485 := bbase (se 7 (by rfl) ⟨17888, by rfl⟩ : syracuseStep 1526485 = 35777) (by norm_num)
theorem B903917 : Blo 599292 903917 := bbase (se 3 (by rfl) ⟨169484, by rfl⟩ : syracuseStep 903917 = 338969) (by norm_num)
theorem B674545 : Blo 599292 674545 := bbase (se 2 (by rfl) ⟨252954, by rfl⟩ : syracuseStep 674545 = 505909) (by norm_num)
theorem B903941 : Blo 599292 903941 := bbase (se 4 (by rfl) ⟨84744, by rfl⟩ : syracuseStep 903941 = 169489) (by norm_num)
theorem B674581 : Blo 599292 674581 := bbase (se 6 (by rfl) ⟨15810, by rfl⟩ : syracuseStep 674581 = 31621) (by norm_num)
theorem B903965 : Blo 599292 903965 := bbase (se 3 (by rfl) ⟨169493, by rfl⟩ : syracuseStep 903965 = 338987) (by norm_num)
theorem B903989 : Blo 599292 903989 := bbase (se 5 (by rfl) ⟨42374, by rfl⟩ : syracuseStep 903989 = 84749) (by norm_num)
theorem B674617 : Blo 599292 674617 := bbase (se 2 (by rfl) ⟨252981, by rfl⟩ : syracuseStep 674617 = 505963) (by norm_num)
theorem B1526597 : Blo 599292 1526597 := bbase (se 4 (by rfl) ⟨143118, by rfl⟩ : syracuseStep 1526597 = 286237) (by norm_num)
theorem B904013 : Blo 599292 904013 := bbase (se 3 (by rfl) ⟨169502, by rfl⟩ : syracuseStep 904013 = 339005) (by norm_num)
theorem B641881 : Blo 599292 641881 := bbase (se 2 (by rfl) ⟨240705, by rfl⟩ : syracuseStep 641881 = 481411) (by norm_num)
theorem B674653 : Blo 599292 674653 := bbase (se 3 (by rfl) ⟨126497, by rfl⟩ : syracuseStep 674653 = 252995) (by norm_num)
theorem B904037 : Blo 599292 904037 := bbase (se 4 (by rfl) ⟨84753, by rfl⟩ : syracuseStep 904037 = 169507) (by norm_num)
theorem B904061 : Blo 599292 904061 := bbase (se 3 (by rfl) ⟨169511, by rfl⟩ : syracuseStep 904061 = 339023) (by norm_num)
theorem B674689 : Blo 599292 674689 := bbase (se 2 (by rfl) ⟨253008, by rfl⟩ : syracuseStep 674689 = 506017) (by norm_num)
theorem B904085 : Blo 599292 904085 := bbase (se 6 (by rfl) ⟨21189, by rfl⟩ : syracuseStep 904085 = 42379) (by norm_num)
theorem B773021 : Blo 599292 773021 := bbase (se 3 (by rfl) ⟨144941, by rfl⟩ : syracuseStep 773021 = 289883) (by norm_num)
theorem B641953 : Blo 599292 641953 := bbase (se 2 (by rfl) ⟨240732, by rfl⟩ : syracuseStep 641953 = 481465) (by norm_num)
theorem B674725 : Blo 599292 674725 := bbase (se 4 (by rfl) ⟨63255, by rfl⟩ : syracuseStep 674725 = 126511) (by norm_num)
theorem B904109 : Blo 599292 904109 := bbase (se 3 (by rfl) ⟨169520, by rfl⟩ : syracuseStep 904109 = 339041) (by norm_num)
theorem B904133 : Blo 599292 904133 := bbase (se 4 (by rfl) ⟨84762, by rfl⟩ : syracuseStep 904133 = 169525) (by norm_num)
theorem B674761 : Blo 599292 674761 := bbase (se 2 (by rfl) ⟨253035, by rfl⟩ : syracuseStep 674761 = 506071) (by norm_num)
theorem B904157 : Blo 599292 904157 := bbase (se 3 (by rfl) ⟨169529, by rfl⟩ : syracuseStep 904157 = 339059) (by norm_num)
theorem B674797 : Blo 599292 674797 := bbase (se 3 (by rfl) ⟨126524, by rfl⟩ : syracuseStep 674797 = 253049) (by norm_num)
theorem B904181 : Blo 599292 904181 := bbase (se 5 (by rfl) ⟨42383, by rfl⟩ : syracuseStep 904181 = 84767) (by norm_num)
theorem B1526789 : Blo 599292 1526789 := bbase (se 4 (by rfl) ⟨143136, by rfl⟩ : syracuseStep 1526789 = 286273) (by norm_num)
theorem B904205 : Blo 599292 904205 := bbase (se 3 (by rfl) ⟨169538, by rfl⟩ : syracuseStep 904205 = 339077) (by norm_num)
theorem B674833 : Blo 599292 674833 := bbase (se 2 (by rfl) ⟨253062, by rfl⟩ : syracuseStep 674833 = 506125) (by norm_num)
theorem B904229 : Blo 599292 904229 := bbase (se 4 (by rfl) ⟨84771, by rfl⟩ : syracuseStep 904229 = 169543) (by norm_num)
theorem B674869 : Blo 599292 674869 := bbase (se 5 (by rfl) ⟨31634, by rfl⟩ : syracuseStep 674869 = 63269) (by norm_num)
theorem B904253 : Blo 599292 904253 := bbase (se 3 (by rfl) ⟨169547, by rfl⟩ : syracuseStep 904253 = 339095) (by norm_num)
theorem B904277 : Blo 599292 904277 := bbase (se 8 (by rfl) ⟨5298, by rfl⟩ : syracuseStep 904277 = 10597) (by norm_num)
theorem B674905 : Blo 599292 674905 := bbase (se 2 (by rfl) ⟨253089, by rfl⟩ : syracuseStep 674905 = 506179) (by norm_num)
theorem B904301 : Blo 599292 904301 := bbase (se 3 (by rfl) ⟨169556, by rfl⟩ : syracuseStep 904301 = 339113) (by norm_num)
theorem B674941 : Blo 599292 674941 := bbase (se 3 (by rfl) ⟨126551, by rfl⟩ : syracuseStep 674941 = 253103) (by norm_num)
theorem B904325 : Blo 599292 904325 := bbase (se 4 (by rfl) ⟨84780, by rfl⟩ : syracuseStep 904325 = 169561) (by norm_num)
theorem B904349 : Blo 599292 904349 := bbase (se 3 (by rfl) ⟨169565, by rfl⟩ : syracuseStep 904349 = 339131) (by norm_num)
theorem B674977 : Blo 599292 674977 := bbase (se 2 (by rfl) ⟨253116, by rfl⟩ : syracuseStep 674977 = 506233) (by norm_num)
theorem B904373 : Blo 599292 904373 := bbase (se 5 (by rfl) ⟨42392, by rfl⟩ : syracuseStep 904373 = 84785) (by norm_num)
theorem B675013 : Blo 599292 675013 := bbase (se 4 (by rfl) ⟨63282, by rfl⟩ : syracuseStep 675013 = 126565) (by norm_num)
theorem B904397 : Blo 599292 904397 := bbase (se 3 (by rfl) ⟨169574, by rfl⟩ : syracuseStep 904397 = 339149) (by norm_num)
theorem B904421 : Blo 599292 904421 := bbase (se 4 (by rfl) ⟨84789, by rfl⟩ : syracuseStep 904421 = 169579) (by norm_num)
theorem B675049 : Blo 599292 675049 := bbase (se 2 (by rfl) ⟨253143, by rfl⟩ : syracuseStep 675049 = 506287) (by norm_num)
theorem B904445 : Blo 599292 904445 := bbase (se 3 (by rfl) ⟨169583, by rfl⟩ : syracuseStep 904445 = 339167) (by norm_num)
theorem B675085 : Blo 599292 675085 := bbase (se 3 (by rfl) ⟨126578, by rfl⟩ : syracuseStep 675085 = 253157) (by norm_num)
theorem B642325 : Blo 599292 642325 := bbase (se 6 (by rfl) ⟨15054, by rfl⟩ : syracuseStep 642325 = 30109) (by norm_num)
theorem B904469 : Blo 599292 904469 := bbase (se 6 (by rfl) ⟨21198, by rfl⟩ : syracuseStep 904469 = 42397) (by norm_num)
theorem B904493 : Blo 599292 904493 := bbase (se 3 (by rfl) ⟨169592, by rfl⟩ : syracuseStep 904493 = 339185) (by norm_num)
theorem B675121 : Blo 599292 675121 := bbase (se 2 (by rfl) ⟨253170, by rfl⟩ : syracuseStep 675121 = 506341) (by norm_num)
theorem B3034421 : Blo 599292 3034421 := bbase (se 5 (by rfl) ⟨142238, by rfl⟩ : syracuseStep 3034421 = 284477) (by norm_num)
theorem B904517 : Blo 599292 904517 := bbase (se 4 (by rfl) ⟨84798, by rfl⟩ : syracuseStep 904517 = 169597) (by norm_num)
theorem B675157 : Blo 599292 675157 := bbase (se 11 (by rfl) ⟨494, by rfl⟩ : syracuseStep 675157 = 989) (by norm_num)
theorem B904541 : Blo 599292 904541 := bbase (se 3 (by rfl) ⟨169601, by rfl⟩ : syracuseStep 904541 = 339203) (by norm_num)
theorem B904565 : Blo 599292 904565 := bbase (se 5 (by rfl) ⟨42401, by rfl⟩ : syracuseStep 904565 = 84803) (by norm_num)
theorem B675193 : Blo 599292 675193 := bbase (se 2 (by rfl) ⟨253197, by rfl⟩ : syracuseStep 675193 = 506395) (by norm_num)
theorem B904589 : Blo 599292 904589 := bbase (se 3 (by rfl) ⟨169610, by rfl⟩ : syracuseStep 904589 = 339221) (by norm_num)
theorem B675229 : Blo 599292 675229 := bbase (se 3 (by rfl) ⟨126605, by rfl⟩ : syracuseStep 675229 = 253211) (by norm_num)
theorem B904613 : Blo 599292 904613 := bbase (se 4 (by rfl) ⟨84807, by rfl⟩ : syracuseStep 904613 = 169615) (by norm_num)
theorem B904637 : Blo 599292 904637 := bbase (se 3 (by rfl) ⟨169619, by rfl⟩ : syracuseStep 904637 = 339239) (by norm_num)
theorem B675265 : Blo 599292 675265 := bbase (se 2 (by rfl) ⟨253224, by rfl⟩ : syracuseStep 675265 = 506449) (by norm_num)
theorem B904661 : Blo 599292 904661 := bbase (se 7 (by rfl) ⟨10601, by rfl⟩ : syracuseStep 904661 = 21203) (by norm_num)
theorem B675301 : Blo 599292 675301 := bbase (se 4 (by rfl) ⟨63309, by rfl⟩ : syracuseStep 675301 = 126619) (by norm_num)
theorem B904685 : Blo 599292 904685 := bbase (se 3 (by rfl) ⟨169628, by rfl⟩ : syracuseStep 904685 = 339257) (by norm_num)
theorem B1560053 : Blo 599292 1560053 := bbase (se 5 (by rfl) ⟨73127, by rfl⟩ : syracuseStep 1560053 = 146255) (by norm_num)
theorem B904709 : Blo 599292 904709 := bbase (se 4 (by rfl) ⟨84816, by rfl⟩ : syracuseStep 904709 = 169633) (by norm_num)
theorem B675337 : Blo 599292 675337 := bbase (se 2 (by rfl) ⟨253251, by rfl⟩ : syracuseStep 675337 = 506503) (by norm_num)
theorem B904733 : Blo 599292 904733 := bbase (se 3 (by rfl) ⟨169637, by rfl⟩ : syracuseStep 904733 = 339275) (by norm_num)
theorem B675373 : Blo 599292 675373 := bbase (se 3 (by rfl) ⟨126632, by rfl⟩ : syracuseStep 675373 = 253265) (by norm_num)
theorem B773677 : Blo 599292 773677 := bbase (se 3 (by rfl) ⟨145064, by rfl⟩ : syracuseStep 773677 = 290129) (by norm_num)
theorem B904757 : Blo 599292 904757 := bbase (se 5 (by rfl) ⟨42410, by rfl⟩ : syracuseStep 904757 = 84821) (by norm_num)
theorem B1920581 : Blo 599292 1920581 := bbase (se 4 (by rfl) ⟨180054, by rfl⟩ : syracuseStep 1920581 = 360109) (by norm_num)
theorem B904781 : Blo 599292 904781 := bbase (se 3 (by rfl) ⟨169646, by rfl⟩ : syracuseStep 904781 = 339293) (by norm_num)
theorem B675409 : Blo 599292 675409 := bbase (se 2 (by rfl) ⟨253278, by rfl⟩ : syracuseStep 675409 = 506557) (by norm_num)
theorem B904805 : Blo 599292 904805 := bbase (se 4 (by rfl) ⟨84825, by rfl⟩ : syracuseStep 904805 = 169651) (by norm_num)
theorem B675445 : Blo 599292 675445 := bbase (se 5 (by rfl) ⟨31661, by rfl⟩ : syracuseStep 675445 = 63323) (by norm_num)
theorem B904829 : Blo 599292 904829 := bbase (se 3 (by rfl) ⟨169655, by rfl⟩ : syracuseStep 904829 = 339311) (by norm_num)
theorem B642701 : Blo 599292 642701 := bbase (se 3 (by rfl) ⟨120506, by rfl⟩ : syracuseStep 642701 = 241013) (by norm_num)
theorem B3853973 : Blo 599292 3853973 := bbase (se 6 (by rfl) ⟨90327, by rfl⟩ : syracuseStep 3853973 = 180655) (by norm_num)
theorem B904853 : Blo 599292 904853 := bbase (se 6 (by rfl) ⟨21207, by rfl⟩ : syracuseStep 904853 = 42415) (by norm_num)
theorem B675481 : Blo 599292 675481 := bbase (se 2 (by rfl) ⟨253305, by rfl⟩ : syracuseStep 675481 = 506611) (by norm_num)
theorem B2608805 : Blo 599292 2608805 := bbase (se 4 (by rfl) ⟨244575, by rfl⟩ : syracuseStep 2608805 = 489151) (by norm_num)
theorem B904877 : Blo 599292 904877 := bbase (se 3 (by rfl) ⟨169664, by rfl⟩ : syracuseStep 904877 = 339329) (by norm_num)
theorem B675517 : Blo 599292 675517 := bbase (se 3 (by rfl) ⟨126659, by rfl⟩ : syracuseStep 675517 = 253319) (by norm_num)
theorem B904901 : Blo 599292 904901 := bbase (se 4 (by rfl) ⟨84834, by rfl⟩ : syracuseStep 904901 = 169669) (by norm_num)
theorem B642773 : Blo 599292 642773 := bbase (se 7 (by rfl) ⟨7532, by rfl⟩ : syracuseStep 642773 = 15065) (by norm_num)
theorem B904925 : Blo 599292 904925 := bbase (se 3 (by rfl) ⟨169673, by rfl⟩ : syracuseStep 904925 = 339347) (by norm_num)
theorem B675553 : Blo 599292 675553 := bbase (se 2 (by rfl) ⟨253332, by rfl⟩ : syracuseStep 675553 = 506665) (by norm_num)
theorem B675589 : Blo 599292 675589 := bbase (se 4 (by rfl) ⟨63336, by rfl⟩ : syracuseStep 675589 = 126673) (by norm_num)
theorem B675625 : Blo 599292 675625 := bbase (se 2 (by rfl) ⟨253359, by rfl⟩ : syracuseStep 675625 = 506719) (by norm_num)
theorem B1953589 : Blo 599292 1953589 := bbase (se 5 (by rfl) ⟨91574, by rfl⟩ : syracuseStep 1953589 = 183149) (by norm_num)
theorem B675661 : Blo 599292 675661 := bbase (se 3 (by rfl) ⟨126686, by rfl⟩ : syracuseStep 675661 = 253373) (by norm_num)
theorem B675697 : Blo 599292 675697 := bbase (se 2 (by rfl) ⟨253386, by rfl⟩ : syracuseStep 675697 = 506773) (by norm_num)
theorem B642961 : Blo 599292 642961 := bbase (se 2 (by rfl) ⟨241110, by rfl⟩ : syracuseStep 642961 = 482221) (by norm_num)
theorem B675733 : Blo 599292 675733 := bbase (se 6 (by rfl) ⟨15837, by rfl⟩ : syracuseStep 675733 = 31675) (by norm_num)
theorem B675769 : Blo 599292 675769 := bbase (se 2 (by rfl) ⟨253413, by rfl⟩ : syracuseStep 675769 = 506827) (by norm_num)
theorem B675805 : Blo 599292 675805 := bbase (se 3 (by rfl) ⟨126713, by rfl⟩ : syracuseStep 675805 = 253427) (by norm_num)
theorem B675841 : Blo 599292 675841 := bbase (se 2 (by rfl) ⟨253440, by rfl⟩ : syracuseStep 675841 = 506881) (by norm_num)
theorem B8802325 : Blo 599292 8802325 := bbase (se 6 (by rfl) ⟨206304, by rfl⟩ : syracuseStep 8802325 = 412609) (by norm_num)
theorem B675877 : Blo 599292 675877 := bbase (se 4 (by rfl) ⟨63363, by rfl⟩ : syracuseStep 675877 = 126727) (by norm_num)
theorem B675913 : Blo 599292 675913 := bbase (se 2 (by rfl) ⟨253467, by rfl⟩ : syracuseStep 675913 = 506935) (by norm_num)
theorem B643145 : Blo 599292 643145 := bbase (se 2 (by rfl) ⟨241179, by rfl⟩ : syracuseStep 643145 = 482359) (by norm_num)
theorem B675949 : Blo 599292 675949 := bbase (se 3 (by rfl) ⟨126740, by rfl⟩ : syracuseStep 675949 = 253481) (by norm_num)
theorem B610421 : Blo 599292 610421 := bbase (se 5 (by rfl) ⟨28613, by rfl⟩ : syracuseStep 610421 = 57227) (by norm_num)
theorem B675985 : Blo 599292 675985 := bbase (se 2 (by rfl) ⟨253494, by rfl⟩ : syracuseStep 675985 = 506989) (by norm_num)
theorem B676021 : Blo 599292 676021 := bbase (se 5 (by rfl) ⟨31688, by rfl⟩ : syracuseStep 676021 = 63377) (by norm_num)
theorem B676057 : Blo 599292 676057 := bbase (se 2 (by rfl) ⟨253521, by rfl⟩ : syracuseStep 676057 = 507043) (by norm_num)
theorem B676093 : Blo 599292 676093 := bbase (se 3 (by rfl) ⟨126767, by rfl⟩ : syracuseStep 676093 = 253535) (by norm_num)
theorem B676129 : Blo 599292 676129 := bbase (se 2 (by rfl) ⟨253548, by rfl⟩ : syracuseStep 676129 = 507097) (by norm_num)
theorem B676165 : Blo 599292 676165 := bbase (se 4 (by rfl) ⟨63390, by rfl⟩ : syracuseStep 676165 = 126781) (by norm_num)
theorem B676201 : Blo 599292 676201 := bbase (se 2 (by rfl) ⟨253575, by rfl⟩ : syracuseStep 676201 = 507151) (by norm_num)
theorem B676237 : Blo 599292 676237 := bbase (se 3 (by rfl) ⟨126794, by rfl⟩ : syracuseStep 676237 = 253589) (by norm_num)
theorem B2281877 : Blo 599292 2281877 := bbase (se 6 (by rfl) ⟨53481, by rfl⟩ : syracuseStep 2281877 = 106963) (by norm_num)
theorem B676273 : Blo 599292 676273 := bbase (se 2 (by rfl) ⟨253602, by rfl⟩ : syracuseStep 676273 = 507205) (by norm_num)
theorem B1921477 : Blo 599292 1921477 := bbase (se 4 (by rfl) ⟨180138, by rfl⟩ : syracuseStep 1921477 = 360277) (by norm_num)
theorem B676309 : Blo 599292 676309 := bbase (se 7 (by rfl) ⟨7925, by rfl⟩ : syracuseStep 676309 = 15851) (by norm_num)
theorem B676345 : Blo 599292 676345 := bbase (se 2 (by rfl) ⟨253629, by rfl⟩ : syracuseStep 676345 = 507259) (by norm_num)
theorem B4346389 : Blo 599292 4346389 := bbase (se 6 (by rfl) ⟨101868, by rfl⟩ : syracuseStep 4346389 = 203737) (by norm_num)
theorem B676381 : Blo 599292 676381 := bbase (se 3 (by rfl) ⟨126821, by rfl⟩ : syracuseStep 676381 = 253643) (by norm_num)
theorem B676417 : Blo 599292 676417 := bbase (se 2 (by rfl) ⟨253656, by rfl⟩ : syracuseStep 676417 = 507313) (by norm_num)
theorem B3035717 : Blo 599292 3035717 := bbase (se 4 (by rfl) ⟨284598, by rfl⟩ : syracuseStep 3035717 = 569197) (by norm_num)
theorem B676453 : Blo 599292 676453 := bbase (se 4 (by rfl) ⟨63417, by rfl⟩ : syracuseStep 676453 = 126835) (by norm_num)
theorem B676489 : Blo 599292 676489 := bbase (se 2 (by rfl) ⟨253683, by rfl⟩ : syracuseStep 676489 = 507367) (by norm_num)
theorem B676525 : Blo 599292 676525 := bbase (se 3 (by rfl) ⟨126848, by rfl⟩ : syracuseStep 676525 = 253697) (by norm_num)
theorem B2282165 : Blo 599292 2282165 := bbase (se 5 (by rfl) ⟨106976, by rfl⟩ : syracuseStep 2282165 = 213953) (by norm_num)
theorem B676561 : Blo 599292 676561 := bbase (se 2 (by rfl) ⟨253710, by rfl⟩ : syracuseStep 676561 = 507421) (by norm_num)
theorem B676597 : Blo 599292 676597 := bbase (se 5 (by rfl) ⟨31715, by rfl⟩ : syracuseStep 676597 = 63431) (by norm_num)
theorem B676633 : Blo 599292 676633 := bbase (se 2 (by rfl) ⟨253737, by rfl⟩ : syracuseStep 676633 = 507475) (by norm_num)
theorem B4117301 : Blo 599292 4117301 := bbase (se 5 (by rfl) ⟨192998, by rfl⟩ : syracuseStep 4117301 = 385997) (by norm_num)
theorem B643897 : Blo 599292 643897 := bbase (se 2 (by rfl) ⟨241461, by rfl⟩ : syracuseStep 643897 = 482923) (by norm_num)
theorem B676669 : Blo 599292 676669 := bbase (se 3 (by rfl) ⟨126875, by rfl⟩ : syracuseStep 676669 = 253751) (by norm_num)
theorem B676705 : Blo 599292 676705 := bbase (se 2 (by rfl) ⟨253764, by rfl⟩ : syracuseStep 676705 = 507529) (by norm_num)
theorem B643969 : Blo 599292 643969 := bbase (se 2 (by rfl) ⟨241488, by rfl⟩ : syracuseStep 643969 = 482977) (by norm_num)
theorem B676741 : Blo 599292 676741 := bbase (se 4 (by rfl) ⟨63444, by rfl⟩ : syracuseStep 676741 = 126889) (by norm_num)
theorem B676777 : Blo 599292 676777 := bbase (se 2 (by rfl) ⟨253791, by rfl⟩ : syracuseStep 676777 = 507583) (by norm_num)
theorem B676813 : Blo 599292 676813 := bbase (se 3 (by rfl) ⟨126902, by rfl⟩ : syracuseStep 676813 = 253805) (by norm_num)
theorem B676849 : Blo 599292 676849 := bbase (se 2 (by rfl) ⟨253818, by rfl⟩ : syracuseStep 676849 = 507637) (by norm_num)
theorem B676885 : Blo 599292 676885 := bbase (se 6 (by rfl) ⟨15864, by rfl⟩ : syracuseStep 676885 = 31729) (by norm_num)
theorem B611365 : Blo 599292 611365 := bbase (se 4 (by rfl) ⟨57315, by rfl⟩ : syracuseStep 611365 = 114631) (by norm_num)
theorem B644149 : Blo 599292 644149 := bbase (se 5 (by rfl) ⟨30194, by rfl⟩ : syracuseStep 644149 = 60389) (by norm_num)
theorem B676921 : Blo 599292 676921 := bbase (se 2 (by rfl) ⟨253845, by rfl⟩ : syracuseStep 676921 = 507691) (by norm_num)
theorem B676957 : Blo 599292 676957 := bbase (se 3 (by rfl) ⟨126929, by rfl⟩ : syracuseStep 676957 = 253859) (by norm_num)
theorem B676993 : Blo 599292 676993 := bbase (se 2 (by rfl) ⟨253872, by rfl⟩ : syracuseStep 676993 = 507745) (by norm_num)
theorem B677029 : Blo 599292 677029 := bbase (se 4 (by rfl) ⟨63471, by rfl⟩ : syracuseStep 677029 = 126943) (by norm_num)
theorem B677065 : Blo 599292 677065 := bbase (se 2 (by rfl) ⟨253899, by rfl⟩ : syracuseStep 677065 = 507799) (by norm_num)
theorem B677101 : Blo 599292 677101 := bbase (se 3 (by rfl) ⟨126956, by rfl⟩ : syracuseStep 677101 = 253913) (by norm_num)
theorem B677137 : Blo 599292 677137 := bbase (se 2 (by rfl) ⟨253926, by rfl⟩ : syracuseStep 677137 = 507853) (by norm_num)
theorem B677173 : Blo 599292 677173 := bbase (se 5 (by rfl) ⟨31742, by rfl⟩ : syracuseStep 677173 = 63485) (by norm_num)
theorem B677209 : Blo 599292 677209 := bbase (se 2 (by rfl) ⟨253953, by rfl⟩ : syracuseStep 677209 = 507907) (by norm_num)
theorem B677245 : Blo 599292 677245 := bbase (se 3 (by rfl) ⟨126983, by rfl⟩ : syracuseStep 677245 = 253967) (by norm_num)
theorem B4576661 : Blo 599292 4576661 := bbase (se 6 (by rfl) ⟨107265, by rfl⟩ : syracuseStep 4576661 = 214531) (by norm_num)
theorem B677281 : Blo 599292 677281 := bbase (se 2 (by rfl) ⟨253980, by rfl⟩ : syracuseStep 677281 = 507961) (by norm_num)
theorem B677317 : Blo 599292 677317 := bbase (se 4 (by rfl) ⟨63498, by rfl⟩ : syracuseStep 677317 = 126997) (by norm_num)
theorem B677353 : Blo 599292 677353 := bbase (se 2 (by rfl) ⟨254007, by rfl⟩ : syracuseStep 677353 = 508015) (by norm_num)
theorem B677389 : Blo 599292 677389 := bbase (se 3 (by rfl) ⟨127010, by rfl⟩ : syracuseStep 677389 = 254021) (by norm_num)
theorem B2053669 : Blo 599292 2053669 := bbase (se 4 (by rfl) ⟨192531, by rfl⟩ : syracuseStep 2053669 = 385063) (by norm_num)
theorem B677425 : Blo 599292 677425 := bbase (se 2 (by rfl) ⟨254034, by rfl⟩ : syracuseStep 677425 = 508069) (by norm_num)
theorem B677461 : Blo 599292 677461 := bbase (se 8 (by rfl) ⟨3969, by rfl⟩ : syracuseStep 677461 = 7939) (by norm_num)
theorem B677497 : Blo 599292 677497 := bbase (se 2 (by rfl) ⟨254061, by rfl⟩ : syracuseStep 677497 = 508123) (by norm_num)
theorem B677533 : Blo 599292 677533 := bbase (se 3 (by rfl) ⟨127037, by rfl⟩ : syracuseStep 677533 = 254075) (by norm_num)
theorem B677569 : Blo 599292 677569 := bbase (se 2 (by rfl) ⟨254088, by rfl⟩ : syracuseStep 677569 = 508177) (by norm_num)
theorem B677605 : Blo 599292 677605 := bbase (se 4 (by rfl) ⟨63525, by rfl⟩ : syracuseStep 677605 = 127051) (by norm_num)
theorem B677641 : Blo 599292 677641 := bbase (se 2 (by rfl) ⟨254115, by rfl⟩ : syracuseStep 677641 = 508231) (by norm_num)
theorem B677677 : Blo 599292 677677 := bbase (se 3 (by rfl) ⟨127064, by rfl⟩ : syracuseStep 677677 = 254129) (by norm_num)
theorem B677713 : Blo 599292 677713 := bbase (se 2 (by rfl) ⟨254142, by rfl⟩ : syracuseStep 677713 = 508285) (by norm_num)
theorem B13850453 : Blo 599292 13850453 := bbase (se 9 (by rfl) ⟨40577, by rfl⟩ : syracuseStep 13850453 = 81155) (by norm_num)
theorem B3037013 : Blo 599292 3037013 := bbase (se 9 (by rfl) ⟨8897, by rfl⟩ : syracuseStep 3037013 = 17795) (by norm_num)
theorem B2053973 : Blo 599292 2053973 := bbase (se 9 (by rfl) ⟨6017, by rfl⟩ : syracuseStep 2053973 = 12035) (by norm_num)
theorem B2283349 : Blo 599292 2283349 := bbase (se 9 (by rfl) ⟨6689, by rfl⟩ : syracuseStep 2283349 = 13379) (by norm_num)
theorem B1464173 : Blo 599292 1464173 := bbase (se 3 (by rfl) ⟨274532, by rfl⟩ : syracuseStep 1464173 = 549065) (by norm_num)
theorem B677749 : Blo 599292 677749 := bbase (se 5 (by rfl) ⟨31769, by rfl⟩ : syracuseStep 677749 = 63539) (by norm_num)
theorem B677785 : Blo 599292 677785 := bbase (se 2 (by rfl) ⟨254169, by rfl⟩ : syracuseStep 677785 = 508339) (by norm_num)
theorem B677821 : Blo 599292 677821 := bbase (se 3 (by rfl) ⟨127091, by rfl⟩ : syracuseStep 677821 = 254183) (by norm_num)
theorem B677857 : Blo 599292 677857 := bbase (se 2 (by rfl) ⟨254196, by rfl⟩ : syracuseStep 677857 = 508393) (by norm_num)
theorem B677893 : Blo 599292 677893 := bbase (se 4 (by rfl) ⟨63552, by rfl⟩ : syracuseStep 677893 = 127105) (by norm_num)
theorem B677929 : Blo 599292 677929 := bbase (se 2 (by rfl) ⟨254223, by rfl⟩ : syracuseStep 677929 = 508447) (by norm_num)
theorem B677965 : Blo 599292 677965 := bbase (se 3 (by rfl) ⟨127118, by rfl⟩ : syracuseStep 677965 = 254237) (by norm_num)
theorem B678001 : Blo 599292 678001 := bbase (se 2 (by rfl) ⟨254250, by rfl⟩ : syracuseStep 678001 = 508501) (by norm_num)
theorem B4642933 : Blo 599292 4642933 := bbase (se 5 (by rfl) ⟨217637, by rfl⟩ : syracuseStep 4642933 = 435275) (by norm_num)
theorem B2283653 : Blo 599292 2283653 := bbase (se 4 (by rfl) ⟨214092, by rfl⟩ : syracuseStep 2283653 = 428185) (by norm_num)
theorem B678037 : Blo 599292 678037 := bbase (se 6 (by rfl) ⟨15891, by rfl⟩ : syracuseStep 678037 = 31783) (by norm_num)
theorem B678073 : Blo 599292 678073 := bbase (se 2 (by rfl) ⟨254277, by rfl⟩ : syracuseStep 678073 = 508555) (by norm_num)
theorem B678109 : Blo 599292 678109 := bbase (se 3 (by rfl) ⟨127145, by rfl⟩ : syracuseStep 678109 = 254291) (by norm_num)
theorem B678145 : Blo 599292 678145 := bbase (se 2 (by rfl) ⟨254304, by rfl⟩ : syracuseStep 678145 = 508609) (by norm_num)
theorem B678181 : Blo 599292 678181 := bbase (se 4 (by rfl) ⟨63579, by rfl⟩ : syracuseStep 678181 = 127159) (by norm_num)
theorem B678217 : Blo 599292 678217 := bbase (se 2 (by rfl) ⟨254331, by rfl⟩ : syracuseStep 678217 = 508663) (by norm_num)
theorem B678253 : Blo 599292 678253 := bbase (se 3 (by rfl) ⟨127172, by rfl⟩ : syracuseStep 678253 = 254345) (by norm_num)
theorem B678289 : Blo 599292 678289 := bbase (se 2 (by rfl) ⟨254358, by rfl⟩ : syracuseStep 678289 = 508717) (by norm_num)
theorem B678325 : Blo 599292 678325 := bbase (se 5 (by rfl) ⟨31796, by rfl⟩ : syracuseStep 678325 = 63593) (by norm_num)
theorem B678361 : Blo 599292 678361 := bbase (se 2 (by rfl) ⟨254385, by rfl⟩ : syracuseStep 678361 = 508771) (by norm_num)
theorem B678397 : Blo 599292 678397 := bbase (se 3 (by rfl) ⟨127199, by rfl⟩ : syracuseStep 678397 = 254399) (by norm_num)
theorem B678433 : Blo 599292 678433 := bbase (se 2 (by rfl) ⟨254412, by rfl⟩ : syracuseStep 678433 = 508825) (by norm_num)
theorem B4872757 : Blo 599292 4872757 := bbase (se 5 (by rfl) ⟨228410, by rfl⟩ : syracuseStep 4872757 = 456821) (by norm_num)
theorem B678469 : Blo 599292 678469 := bbase (se 4 (by rfl) ⟨63606, by rfl⟩ : syracuseStep 678469 = 127213) (by norm_num)
theorem B2775653 : Blo 599292 2775653 := bbase (se 4 (by rfl) ⟨260217, by rfl⟩ : syracuseStep 2775653 = 520435) (by norm_num)
theorem B678505 : Blo 599292 678505 := bbase (se 2 (by rfl) ⟨254439, by rfl⟩ : syracuseStep 678505 = 508879) (by norm_num)
theorem B678541 : Blo 599292 678541 := bbase (se 3 (by rfl) ⟨127226, by rfl⟩ : syracuseStep 678541 = 254453) (by norm_num)
theorem B1628837 : Blo 599292 1628837 := bbase (se 4 (by rfl) ⟨152703, by rfl⟩ : syracuseStep 1628837 = 305407) (by norm_num)
theorem B678577 : Blo 599292 678577 := bbase (se 2 (by rfl) ⟨254466, by rfl⟩ : syracuseStep 678577 = 508933) (by norm_num)
theorem B678613 : Blo 599292 678613 := bbase (se 7 (by rfl) ⟨7952, by rfl⟩ : syracuseStep 678613 = 15905) (by norm_num)
theorem B678649 : Blo 599292 678649 := bbase (se 2 (by rfl) ⟨254493, by rfl⟩ : syracuseStep 678649 = 508987) (by norm_num)
theorem B678685 : Blo 599292 678685 := bbase (se 3 (by rfl) ⟨127253, by rfl⟩ : syracuseStep 678685 = 254507) (by norm_num)
theorem B1629173 : Blo 599292 1629173 := bbase (se 5 (by rfl) ⟨76367, by rfl⟩ : syracuseStep 1629173 = 152735) (by norm_num)
theorem B3038309 : Blo 599292 3038309 := bbase (se 4 (by rfl) ⟨284841, by rfl⟩ : syracuseStep 3038309 = 569683) (by norm_num)
theorem B2382965 : Blo 599292 2382965 := bbase (se 5 (by rfl) ⟨111701, by rfl⟩ : syracuseStep 2382965 = 223403) (by norm_num)
theorem B1236125 : Blo 599292 1236125 := bbase (se 3 (by rfl) ⟨231773, by rfl⟩ : syracuseStep 1236125 = 463547) (by norm_num)
theorem B1137901 : Blo 599292 1137901 := bbase (se 3 (by rfl) ⟨213356, by rfl⟩ : syracuseStep 1137901 = 426713) (by norm_num)
theorem B974069 : Blo 599292 974069 := bbase (se 5 (by rfl) ⟨45659, by rfl⟩ : syracuseStep 974069 = 91319) (by norm_num)
theorem B2022677 : Blo 599292 2022677 := bbase (se 6 (by rfl) ⟨47406, by rfl⟩ : syracuseStep 2022677 = 94813) (by norm_num)
theorem B1924373 : Blo 599292 1924373 := bbase (se 6 (by rfl) ⟨45102, by rfl⟩ : syracuseStep 1924373 = 90205) (by norm_num)
theorem B15621461 : Blo 599292 15621461 := bbase (se 11 (by rfl) ⟨11441, by rfl⟩ : syracuseStep 15621461 = 22883) (by norm_num)
theorem B1138045 : Blo 599292 1138045 := bbase (se 3 (by rfl) ⟨213383, by rfl⟩ : syracuseStep 1138045 = 426767) (by norm_num)
theorem B1138205 : Blo 599292 1138205 := bbase (se 3 (by rfl) ⟨213413, by rfl⟩ : syracuseStep 1138205 = 426827) (by norm_num)
theorem B2252405 : Blo 599292 2252405 := bbase (se 5 (by rfl) ⟨105581, by rfl⟩ : syracuseStep 2252405 = 211163) (by norm_num)
theorem B1138349 : Blo 599292 1138349 := bbase (se 3 (by rfl) ⟨213440, by rfl⟩ : syracuseStep 1138349 = 426881) (by norm_num)
theorem B2088629 : Blo 599292 2088629 := bbase (se 5 (by rfl) ⟨97904, by rfl⟩ : syracuseStep 2088629 = 195809) (by norm_num)
theorem B2023109 : Blo 599292 2023109 := bbase (se 4 (by rfl) ⟨189666, by rfl⟩ : syracuseStep 2023109 = 379333) (by norm_num)
theorem B1138637 : Blo 599292 1138637 := bbase (se 3 (by rfl) ⟨213494, by rfl⟩ : syracuseStep 1138637 = 426989) (by norm_num)
theorem B1138789 : Blo 599292 1138789 := bbase (se 4 (by rfl) ⟨106761, by rfl⟩ : syracuseStep 1138789 = 213523) (by norm_num)
theorem B2023541 : Blo 599292 2023541 := bbase (se 5 (by rfl) ⟨94853, by rfl⟩ : syracuseStep 2023541 = 189707) (by norm_num)
theorem B2285765 : Blo 599292 2285765 := bbase (se 4 (by rfl) ⟨214290, by rfl⟩ : syracuseStep 2285765 = 428581) (by norm_num)
theorem B811229 : Blo 599292 811229 := bbase (se 3 (by rfl) ⟨152105, by rfl⟩ : syracuseStep 811229 = 304211) (by norm_num)
theorem B3432725 : Blo 599292 3432725 := bbase (se 6 (by rfl) ⟨80454, by rfl⟩ : syracuseStep 3432725 = 160909) (by norm_num)
theorem B3039605 : Blo 599292 3039605 := bbase (se 5 (by rfl) ⟨142481, by rfl⟩ : syracuseStep 3039605 = 284963) (by norm_num)
theorem B1139093 : Blo 599292 1139093 := bbase (se 6 (by rfl) ⟨26697, by rfl⟩ : syracuseStep 1139093 = 53395) (by norm_num)
theorem B2286053 : Blo 599292 2286053 := bbase (se 4 (by rfl) ⟨214317, by rfl⟩ : syracuseStep 2286053 = 428635) (by norm_num)
theorem B975341 : Blo 599292 975341 := bbase (se 3 (by rfl) ⟨182876, by rfl⟩ : syracuseStep 975341 = 365753) (by norm_num)
theorem B2023973 : Blo 599292 2023973 := bbase (se 4 (by rfl) ⟨189747, by rfl⟩ : syracuseStep 2023973 = 379495) (by norm_num)
theorem B4875157 : Blo 599292 4875157 := bbase (se 6 (by rfl) ⟨114261, by rfl⟩ : syracuseStep 4875157 = 228523) (by norm_num)
theorem B2024405 : Blo 599292 2024405 := bbase (se 7 (by rfl) ⟨23723, by rfl⟩ : syracuseStep 2024405 = 47447) (by norm_num)
theorem B10937429 : Blo 599292 10937429 := bbase (se 8 (by rfl) ⟨64086, by rfl⟩ : syracuseStep 10937429 = 128173) (by norm_num)
theorem B1139845 : Blo 599292 1139845 := bbase (se 4 (by rfl) ⟨106860, by rfl⟩ : syracuseStep 1139845 = 213721) (by norm_num)
theorem B1139989 : Blo 599292 1139989 := bbase (se 6 (by rfl) ⟨26718, by rfl⟩ : syracuseStep 1139989 = 53437) (by norm_num)
theorem B2024837 : Blo 599292 2024837 := bbase (se 4 (by rfl) ⟨189828, by rfl⟩ : syracuseStep 2024837 = 379657) (by norm_num)
theorem B1140149 : Blo 599292 1140149 := bbase (se 5 (by rfl) ⟨53444, by rfl⟩ : syracuseStep 1140149 = 106889) (by norm_num)
theorem B1926629 : Blo 599292 1926629 := bbase (se 4 (by rfl) ⟨180621, by rfl⟩ : syracuseStep 1926629 = 361243) (by norm_num)
theorem B812597 : Blo 599292 812597 := bbase (se 5 (by rfl) ⟨38090, by rfl⟩ : syracuseStep 812597 = 76181) (by norm_num)
theorem B1140293 : Blo 599292 1140293 := bbase (se 4 (by rfl) ⟨106902, by rfl⟩ : syracuseStep 1140293 = 213805) (by norm_num)
theorem B1828453 : Blo 599292 1828453 := bbase (se 4 (by rfl) ⟨171417, by rfl⟩ : syracuseStep 1828453 = 342835) (by norm_num)
theorem B3040901 : Blo 599292 3040901 := bbase (se 4 (by rfl) ⟨285084, by rfl⟩ : syracuseStep 3040901 = 570169) (by norm_num)
theorem B2287237 : Blo 599292 2287237 := bbase (se 4 (by rfl) ⟨214428, by rfl⟩ : syracuseStep 2287237 = 428857) (by norm_num)
theorem B2025269 : Blo 599292 2025269 := bbase (se 5 (by rfl) ⟨94934, by rfl⟩ : syracuseStep 2025269 = 189869) (by norm_num)
theorem B1140581 : Blo 599292 1140581 := bbase (se 4 (by rfl) ⟨106929, by rfl⟩ : syracuseStep 1140581 = 213859) (by norm_num)
theorem B2287541 : Blo 599292 2287541 := bbase (se 5 (by rfl) ⟨107228, by rfl⟩ : syracuseStep 2287541 = 214457) (by norm_num)
theorem B1140733 : Blo 599292 1140733 := bbase (se 3 (by rfl) ⟨213887, by rfl⟩ : syracuseStep 1140733 = 427775) (by norm_num)
theorem B2025701 : Blo 599292 2025701 := bbase (se 4 (by rfl) ⟨189909, by rfl⟩ : syracuseStep 2025701 = 379819) (by norm_num)
theorem B1927397 : Blo 599292 1927397 := bbase (se 4 (by rfl) ⟨180693, by rfl⟩ : syracuseStep 1927397 = 361387) (by norm_num)
theorem B1141037 : Blo 599292 1141037 := bbase (se 3 (by rfl) ⟨213944, by rfl⟩ : syracuseStep 1141037 = 427889) (by norm_num)
theorem B4811093 : Blo 599292 4811093 := bbase (se 10 (by rfl) ⟨7047, by rfl⟩ : syracuseStep 4811093 = 14095) (by norm_num)
theorem B911837 : Blo 599292 911837 := bbase (se 3 (by rfl) ⟨170969, by rfl⟩ : syracuseStep 911837 = 341939) (by norm_num)
theorem B2026133 : Blo 599292 2026133 := bbase (se 6 (by rfl) ⟨47487, by rfl⟩ : syracuseStep 2026133 = 94975) (by norm_num)
theorem B1927909 : Blo 599292 1927909 := bbase (se 4 (by rfl) ⟨180741, by rfl⟩ : syracuseStep 1927909 = 361483) (by norm_num)
theorem B3042197 : Blo 599292 3042197 := bbase (se 6 (by rfl) ⟨71301, by rfl⟩ : syracuseStep 3042197 = 142603) (by norm_num)
theorem B813997 : Blo 599292 813997 := bbase (se 3 (by rfl) ⟨152624, by rfl⟩ : syracuseStep 813997 = 305249) (by norm_num)
theorem B1141789 : Blo 599292 1141789 := bbase (se 3 (by rfl) ⟨214085, by rfl⟩ : syracuseStep 1141789 = 428171) (by norm_num)
theorem B2026565 : Blo 599292 2026565 := bbase (se 4 (by rfl) ⟨189990, by rfl⟩ : syracuseStep 2026565 = 379981) (by norm_num)
theorem B1141933 : Blo 599292 1141933 := bbase (se 3 (by rfl) ⟨214112, by rfl⟩ : syracuseStep 1141933 = 428225) (by norm_num)
theorem B1142093 : Blo 599292 1142093 := bbase (se 3 (by rfl) ⟨214142, by rfl⟩ : syracuseStep 1142093 = 428285) (by norm_num)
theorem B1371485 : Blo 599292 1371485 := bbase (se 3 (by rfl) ⟨257153, by rfl⟩ : syracuseStep 1371485 = 514307) (by norm_num)
theorem B716149 : Blo 599292 716149 := bbase (se 5 (by rfl) ⟨33569, by rfl⟩ : syracuseStep 716149 = 67139) (by norm_num)
theorem B1142237 : Blo 599292 1142237 := bbase (se 3 (by rfl) ⟨214169, by rfl⟩ : syracuseStep 1142237 = 428339) (by norm_num)
theorem B2026997 : Blo 599292 2026997 := bbase (se 5 (by rfl) ⟨95015, by rfl⟩ : syracuseStep 2026997 = 190031) (by norm_num)
theorem B1830485 : Blo 599292 1830485 := bbase (se 8 (by rfl) ⟨10725, by rfl⟩ : syracuseStep 1830485 = 21451) (by norm_num)
theorem B1011325 : Blo 599292 1011325 := bbase (se 3 (by rfl) ⟨189623, by rfl⟩ : syracuseStep 1011325 = 379247) (by norm_num)
theorem B1011413 : Blo 599292 1011413 := bbase (se 7 (by rfl) ⟨11852, by rfl⟩ : syracuseStep 1011413 = 23705) (by norm_num)
theorem B1142525 : Blo 599292 1142525 := bbase (se 3 (by rfl) ⟨214223, by rfl⟩ : syracuseStep 1142525 = 428447) (by norm_num)
theorem B1011541 : Blo 599292 1011541 := bbase (se 9 (by rfl) ⟨2963, by rfl⟩ : syracuseStep 1011541 = 5927) (by norm_num)
theorem B1142677 : Blo 599292 1142677 := bbase (se 6 (by rfl) ⟨26781, by rfl⟩ : syracuseStep 1142677 = 53563) (by norm_num)
theorem B2027429 : Blo 599292 2027429 := bbase (se 4 (by rfl) ⟨190071, by rfl⟩ : syracuseStep 2027429 = 380143) (by norm_num)
theorem B1011629 : Blo 599292 1011629 := bbase (se 3 (by rfl) ⟨189680, by rfl⟩ : syracuseStep 1011629 = 379361) (by norm_num)
theorem B2289653 : Blo 599292 2289653 := bbase (se 5 (by rfl) ⟨107327, by rfl⟩ : syracuseStep 2289653 = 214655) (by norm_num)
theorem B1011757 : Blo 599292 1011757 := bbase (se 3 (by rfl) ⟨189704, by rfl⟩ : syracuseStep 1011757 = 379409) (by norm_num)
theorem B684137 : Blo 599292 684137 := bbase (se 2 (by rfl) ⟨256551, by rfl⟩ : syracuseStep 684137 = 513103) (by norm_num)
theorem B1011845 : Blo 599292 1011845 := bbase (se 4 (by rfl) ⟨94860, by rfl⟩ : syracuseStep 1011845 = 189721) (by norm_num)
theorem B3043493 : Blo 599292 3043493 := bbase (se 4 (by rfl) ⟨285327, by rfl⟩ : syracuseStep 3043493 = 570655) (by norm_num)
theorem B1142981 : Blo 599292 1142981 := bbase (se 4 (by rfl) ⟨107154, by rfl⟩ : syracuseStep 1142981 = 214309) (by norm_num)
theorem B1011973 : Blo 599292 1011973 := bbase (se 4 (by rfl) ⟨94872, by rfl⟩ : syracuseStep 1011973 = 189745) (by norm_num)
theorem B2289941 : Blo 599292 2289941 := bbase (se 6 (by rfl) ⟨53670, by rfl⟩ : syracuseStep 2289941 = 107341) (by norm_num)
theorem B2027861 : Blo 599292 2027861 := bbase (se 10 (by rfl) ⟨2970, by rfl⟩ : syracuseStep 2027861 = 5941) (by norm_num)
theorem B1012061 : Blo 599292 1012061 := bbase (se 3 (by rfl) ⟨189761, by rfl⟩ : syracuseStep 1012061 = 379523) (by norm_num)
theorem B913837 : Blo 599292 913837 := bbase (se 3 (by rfl) ⟨171344, by rfl⟩ : syracuseStep 913837 = 342689) (by norm_num)
theorem B1929653 : Blo 599292 1929653 := bbase (se 5 (by rfl) ⟨90452, by rfl⟩ : syracuseStep 1929653 = 180905) (by norm_num)
theorem B1012189 : Blo 599292 1012189 := bbase (se 3 (by rfl) ⟨189785, by rfl⟩ : syracuseStep 1012189 = 379571) (by norm_num)
theorem B1372717 : Blo 599292 1372717 := bbase (se 3 (by rfl) ⟨257384, by rfl⟩ : syracuseStep 1372717 = 514769) (by norm_num)
theorem B1012277 : Blo 599292 1012277 := bbase (se 5 (by rfl) ⟨47450, by rfl⟩ : syracuseStep 1012277 = 94901) (by norm_num)
theorem B1929845 : Blo 599292 1929845 := bbase (se 5 (by rfl) ⟨90461, by rfl⟩ : syracuseStep 1929845 = 180923) (by norm_num)
theorem B1012405 : Blo 599292 1012405 := bbase (se 5 (by rfl) ⟨47456, by rfl⟩ : syracuseStep 1012405 = 94913) (by norm_num)
theorem B2028293 : Blo 599292 2028293 := bbase (se 4 (by rfl) ⟨190152, by rfl⟩ : syracuseStep 2028293 = 380305) (by norm_num)
theorem B1012493 : Blo 599292 1012493 := bbase (se 3 (by rfl) ⟨189842, by rfl⟩ : syracuseStep 1012493 = 379685) (by norm_num)
theorem B1012621 : Blo 599292 1012621 := bbase (se 3 (by rfl) ⟨189866, by rfl⟩ : syracuseStep 1012621 = 379733) (by norm_num)
theorem B684973 : Blo 599292 684973 := bbase (se 3 (by rfl) ⟨128432, by rfl⟩ : syracuseStep 684973 = 256865) (by norm_num)
theorem B1143733 : Blo 599292 1143733 := bbase (se 5 (by rfl) ⟨53612, by rfl⟩ : syracuseStep 1143733 = 107225) (by norm_num)
theorem B2880485 : Blo 599292 2880485 := bbase (se 4 (by rfl) ⟨270045, by rfl⟩ : syracuseStep 2880485 = 540091) (by norm_num)
theorem B1012709 : Blo 599292 1012709 := bbase (se 4 (by rfl) ⟨94941, by rfl⟩ : syracuseStep 1012709 = 189883) (by norm_num)
theorem B1831909 : Blo 599292 1831909 := bbase (se 4 (by rfl) ⟨171741, by rfl⟩ : syracuseStep 1831909 = 343483) (by norm_num)
theorem B5796917 : Blo 599292 5796917 := bbase (se 5 (by rfl) ⟨271730, by rfl⟩ : syracuseStep 5796917 = 543461) (by norm_num)
theorem B1143877 : Blo 599292 1143877 := bbase (se 4 (by rfl) ⟨107238, by rfl⟩ : syracuseStep 1143877 = 214477) (by norm_num)
theorem B1012837 : Blo 599292 1012837 := bbase (se 4 (by rfl) ⟨94953, by rfl⟩ : syracuseStep 1012837 = 189907) (by norm_num)
theorem B2028725 : Blo 599292 2028725 := bbase (se 5 (by rfl) ⟨95096, by rfl⟩ : syracuseStep 2028725 = 190193) (by norm_num)
theorem B1012925 : Blo 599292 1012925 := bbase (se 3 (by rfl) ⟨189923, by rfl⟩ : syracuseStep 1012925 = 379847) (by norm_num)
theorem B1144037 : Blo 599292 1144037 := bbase (se 4 (by rfl) ⟨107253, by rfl⟩ : syracuseStep 1144037 = 214507) (by norm_num)
theorem B3241237 : Blo 599292 3241237 := bbase (se 6 (by rfl) ⟨75966, by rfl⟩ : syracuseStep 3241237 = 151933) (by norm_num)
theorem B1013053 : Blo 599292 1013053 := bbase (se 3 (by rfl) ⟨189947, by rfl⟩ : syracuseStep 1013053 = 379895) (by norm_num)
theorem B1144181 : Blo 599292 1144181 := bbase (se 5 (by rfl) ⟨53633, by rfl⟩ : syracuseStep 1144181 = 107267) (by norm_num)
theorem B1013141 : Blo 599292 1013141 := bbase (se 6 (by rfl) ⟨23745, by rfl⟩ : syracuseStep 1013141 = 47491) (by norm_num)
theorem B3044789 : Blo 599292 3044789 := bbase (se 5 (by rfl) ⟨142724, by rfl⟩ : syracuseStep 3044789 = 285449) (by norm_num)
theorem B1013269 : Blo 599292 1013269 := bbase (se 6 (by rfl) ⟨23748, by rfl⟩ : syracuseStep 1013269 = 47497) (by norm_num)
theorem B685633 : Blo 599292 685633 := bbase (se 2 (by rfl) ⟨257112, by rfl⟩ : syracuseStep 685633 = 514225) (by norm_num)
theorem B2029157 : Blo 599292 2029157 := bbase (se 4 (by rfl) ⟨190233, by rfl⟩ : syracuseStep 2029157 = 380467) (by norm_num)
theorem B1013357 : Blo 599292 1013357 := bbase (se 3 (by rfl) ⟨190004, by rfl⟩ : syracuseStep 1013357 = 380009) (by norm_num)
theorem B1144469 : Blo 599292 1144469 := bbase (se 6 (by rfl) ⟨26823, by rfl⟩ : syracuseStep 1144469 = 53647) (by norm_num)
theorem B915101 : Blo 599292 915101 := bbase (se 3 (by rfl) ⟨171581, by rfl⟩ : syracuseStep 915101 = 343163) (by norm_num)
theorem B1013485 : Blo 599292 1013485 := bbase (se 3 (by rfl) ⟨190028, by rfl⟩ : syracuseStep 1013485 = 380057) (by norm_num)
theorem B1144621 : Blo 599292 1144621 := bbase (se 3 (by rfl) ⟨214616, by rfl⟩ : syracuseStep 1144621 = 429233) (by norm_num)
theorem B1013573 : Blo 599292 1013573 := bbase (se 4 (by rfl) ⟨95022, by rfl⟩ : syracuseStep 1013573 = 190045) (by norm_num)
theorem B1013701 : Blo 599292 1013701 := bbase (se 4 (by rfl) ⟨95034, by rfl⟩ : syracuseStep 1013701 = 190069) (by norm_num)
theorem B2029589 : Blo 599292 2029589 := bbase (se 6 (by rfl) ⟨47568, by rfl⟩ : syracuseStep 2029589 = 95137) (by norm_num)
theorem B1013789 : Blo 599292 1013789 := bbase (se 3 (by rfl) ⟨190085, by rfl⟩ : syracuseStep 1013789 = 380171) (by norm_num)
theorem B1144925 : Blo 599292 1144925 := bbase (se 3 (by rfl) ⟨214673, by rfl⟩ : syracuseStep 1144925 = 429347) (by norm_num)
theorem B915565 : Blo 599292 915565 := bbase (se 3 (by rfl) ⟨171668, by rfl⟩ : syracuseStep 915565 = 343337) (by norm_num)
theorem B1013917 : Blo 599292 1013917 := bbase (se 3 (by rfl) ⟨190109, by rfl⟩ : syracuseStep 1013917 = 380219) (by norm_num)
theorem B1014005 : Blo 599292 1014005 := bbase (se 5 (by rfl) ⟨47531, by rfl⟩ : syracuseStep 1014005 = 95063) (by norm_num)
theorem B2193685 : Blo 599292 2193685 := bbase (se 6 (by rfl) ⟨51414, by rfl⟩ : syracuseStep 2193685 = 102829) (by norm_num)
theorem B1440109 : Blo 599292 1440109 := bbase (se 3 (by rfl) ⟨270020, by rfl⟩ : syracuseStep 1440109 = 540041) (by norm_num)
theorem B1014133 : Blo 599292 1014133 := bbase (se 5 (by rfl) ⟨47537, by rfl⟩ : syracuseStep 1014133 = 95075) (by norm_num)
theorem B2030021 : Blo 599292 2030021 := bbase (se 4 (by rfl) ⟨190314, by rfl⟩ : syracuseStep 2030021 = 380629) (by norm_num)
theorem B1374661 : Blo 599292 1374661 := bbase (se 4 (by rfl) ⟨128874, by rfl⟩ : syracuseStep 1374661 = 257749) (by norm_num)
theorem B1014221 : Blo 599292 1014221 := bbase (se 3 (by rfl) ⟨190166, by rfl⟩ : syracuseStep 1014221 = 380333) (by norm_num)
theorem B1735141 : Blo 599292 1735141 := bbase (se 4 (by rfl) ⟨162669, by rfl⟩ : syracuseStep 1735141 = 325339) (by norm_num)
theorem B2882101 : Blo 599292 2882101 := bbase (se 5 (by rfl) ⟨135098, by rfl⟩ : syracuseStep 2882101 = 270197) (by norm_num)
theorem B1014349 : Blo 599292 1014349 := bbase (se 3 (by rfl) ⟨190190, by rfl⟩ : syracuseStep 1014349 = 380381) (by norm_num)
theorem B686701 : Blo 599292 686701 := bbase (se 3 (by rfl) ⟨128756, by rfl⟩ : syracuseStep 686701 = 257513) (by norm_num)
theorem B4553333 : Blo 599292 4553333 := bbase (se 5 (by rfl) ⟨213437, by rfl⟩ : syracuseStep 4553333 = 426875) (by norm_num)
theorem B1014437 : Blo 599292 1014437 := bbase (se 4 (by rfl) ⟨95103, by rfl⟩ : syracuseStep 1014437 = 190207) (by norm_num)
theorem B3046085 : Blo 599292 3046085 := bbase (se 4 (by rfl) ⟨285570, by rfl⟩ : syracuseStep 3046085 = 571141) (by norm_num)
theorem B1014565 : Blo 599292 1014565 := bbase (se 4 (by rfl) ⟨95115, by rfl⟩ : syracuseStep 1014565 = 190231) (by norm_num)
theorem B2030453 : Blo 599292 2030453 := bbase (se 5 (by rfl) ⟨95177, by rfl⟩ : syracuseStep 2030453 = 190355) (by norm_num)
theorem B1014653 : Blo 599292 1014653 := bbase (se 3 (by rfl) ⟨190247, by rfl⟩ : syracuseStep 1014653 = 380495) (by norm_num)
theorem B1014781 : Blo 599292 1014781 := bbase (se 3 (by rfl) ⟨190271, by rfl⟩ : syracuseStep 1014781 = 380543) (by norm_num)
theorem B1440773 : Blo 599292 1440773 := bbase (se 4 (by rfl) ⟨135072, by rfl⟩ : syracuseStep 1440773 = 270145) (by norm_num)
theorem B1014869 : Blo 599292 1014869 := bbase (se 8 (by rfl) ⟨5946, by rfl⟩ : syracuseStep 1014869 = 11893) (by norm_num)
theorem B1014997 : Blo 599292 1014997 := bbase (se 7 (by rfl) ⟨11894, by rfl⟩ : syracuseStep 1014997 = 23789) (by norm_num)
theorem B2030885 : Blo 599292 2030885 := bbase (se 4 (by rfl) ⟨190395, by rfl⟩ : syracuseStep 2030885 = 380791) (by norm_num)
theorem B1015085 : Blo 599292 1015085 := bbase (se 3 (by rfl) ⟨190328, by rfl⟩ : syracuseStep 1015085 = 380657) (by norm_num)
theorem B687421 : Blo 599292 687421 := bbase (se 3 (by rfl) ⟨128891, by rfl⟩ : syracuseStep 687421 = 257783) (by norm_num)
theorem B916853 : Blo 599292 916853 := bbase (se 5 (by rfl) ⟨42977, by rfl⟩ : syracuseStep 916853 = 85955) (by norm_num)
theorem B1375645 : Blo 599292 1375645 := bbase (se 3 (by rfl) ⟨257933, by rfl⟩ : syracuseStep 1375645 = 515867) (by norm_num)
theorem B1015213 : Blo 599292 1015213 := bbase (se 3 (by rfl) ⟨190352, by rfl⟩ : syracuseStep 1015213 = 380705) (by norm_num)
theorem B8224213 : Blo 599292 8224213 := bbase (se 7 (by rfl) ⟨96377, by rfl⟩ : syracuseStep 8224213 = 192755) (by norm_num)
theorem B687577 : Blo 599292 687577 := bbase (se 2 (by rfl) ⟨257841, by rfl⟩ : syracuseStep 687577 = 515683) (by norm_num)
theorem B1015301 : Blo 599292 1015301 := bbase (se 4 (by rfl) ⟨95184, by rfl⟩ : syracuseStep 1015301 = 190369) (by norm_num)
theorem B1375829 : Blo 599292 1375829 := bbase (se 8 (by rfl) ⟨8061, by rfl⟩ : syracuseStep 1375829 = 16123) (by norm_num)
theorem B1015429 : Blo 599292 1015429 := bbase (se 4 (by rfl) ⟨95196, by rfl⟩ : syracuseStep 1015429 = 190393) (by norm_num)
theorem B2031317 : Blo 599292 2031317 := bbase (se 7 (by rfl) ⟨23804, by rfl⟩ : syracuseStep 2031317 = 47609) (by norm_num)
theorem B1015517 : Blo 599292 1015517 := bbase (se 3 (by rfl) ⟨190409, by rfl⟩ : syracuseStep 1015517 = 380819) (by norm_num)
theorem B1015645 : Blo 599292 1015645 := bbase (se 3 (by rfl) ⟨190433, by rfl⟩ : syracuseStep 1015645 = 380867) (by norm_num)
theorem B1539965 : Blo 599292 1539965 := bbase (se 3 (by rfl) ⟨288743, by rfl⟩ : syracuseStep 1539965 = 577487) (by norm_num)
theorem B720785 : Blo 599292 720785 := bbase (se 2 (by rfl) ⟨270294, by rfl⟩ : syracuseStep 720785 = 540589) (by norm_num)
theorem B1015733 : Blo 599292 1015733 := bbase (se 5 (by rfl) ⟨47612, by rfl⟩ : syracuseStep 1015733 = 95225) (by norm_num)
theorem B3243989 : Blo 599292 3243989 := bbase (se 7 (by rfl) ⟨38015, by rfl⟩ : syracuseStep 3243989 = 76031) (by norm_num)
theorem B3047381 : Blo 599292 3047381 := bbase (se 7 (by rfl) ⟨35711, by rfl⟩ : syracuseStep 3047381 = 71423) (by norm_num)
theorem B1015841 : Blo 599292 1015841 := bstep (se 2 (by rfl) ⟨380940, by rfl⟩ : syracuseStep 1015841 = 761881) B761881
theorem B1015969 : Blo 599292 1015969 := bstep (se 2 (by rfl) ⟨380988, by rfl⟩ : syracuseStep 1015969 = 761977) B761977
theorem B1441955 : Blo 599292 1441955 := bstep (se 1 (by rfl) ⟨1081466, by rfl⟩ : syracuseStep 1441955 = 2162933) B2162933
theorem B1016003 : Blo 599292 1016003 := bstep (se 1 (by rfl) ⟨762002, by rfl⟩ : syracuseStep 1016003 = 1524005) B1524005
theorem B2031857 : Blo 599292 2031857 := bstep (se 2 (by rfl) ⟨761946, by rfl⟩ : syracuseStep 2031857 = 1523893) B1523893
theorem B1016131 : Blo 599292 1016131 := bstep (se 1 (by rfl) ⟨762098, by rfl⟩ : syracuseStep 1016131 = 1524197) B1524197
theorem B1409411 : Blo 599292 1409411 := bstep (se 1 (by rfl) ⟨1057058, by rfl⟩ : syracuseStep 1409411 = 2114117) B2114117
theorem B1540561 : Blo 599292 1540561 := bstep (se 2 (by rfl) ⟨577710, by rfl⟩ : syracuseStep 1540561 = 1155421) B1155421
theorem B1016273 : Blo 599292 1016273 := bstep (se 2 (by rfl) ⟨381102, by rfl⟩ : syracuseStep 1016273 = 762205) B762205
theorem B4555277 : Blo 599292 4555277 := bstep (se 3 (by rfl) ⟨854114, by rfl⟩ : syracuseStep 4555277 = 1708229) B1708229
theorem B1442339 : Blo 599292 1442339 := bstep (se 1 (by rfl) ⟨1081754, by rfl⟩ : syracuseStep 1442339 = 2163509) B2163509
theorem B2163277 : Blo 599292 2163277 := bstep (se 3 (by rfl) ⟨405614, by rfl⟩ : syracuseStep 2163277 = 811229) B811229
theorem B1016401 : Blo 599292 1016401 := bstep (se 2 (by rfl) ⟨381150, by rfl⟩ : syracuseStep 1016401 = 762301) B762301
theorem B14615153 : Blo 599292 14615153 := bstep (se 2 (by rfl) ⟨5480682, by rfl⟩ : syracuseStep 14615153 = 10961365) B10961365
theorem B1016435 : Blo 599292 1016435 := bstep (se 1 (by rfl) ⟨762326, by rfl⟩ : syracuseStep 1016435 = 1524653) B1524653
theorem B1016563 : Blo 599292 1016563 := bstep (se 1 (by rfl) ⟨762422, by rfl⟩ : syracuseStep 1016563 = 1524845) B1524845
theorem B2032397 : Blo 599292 2032397 := bstep (se 3 (by rfl) ⟨381074, by rfl⟩ : syracuseStep 2032397 = 762149) B762149
theorem B2032451 : Blo 599292 2032451 := bstep (se 1 (by rfl) ⟨1524338, by rfl⟩ : syracuseStep 2032451 = 3048677) B3048677
theorem B1016705 : Blo 599292 1016705 := bstep (se 2 (by rfl) ⟨381264, by rfl⟩ : syracuseStep 1016705 = 762529) B762529
theorem B1016833 : Blo 599292 1016833 := bstep (se 2 (by rfl) ⟨381312, by rfl⟩ : syracuseStep 1016833 = 762625) B762625
theorem B1016867 : Blo 599292 1016867 := bstep (se 1 (by rfl) ⟨762650, by rfl⟩ : syracuseStep 1016867 = 1525301) B1525301
theorem B1442897 : Blo 599292 1442897 := bstep (se 2 (by rfl) ⟨541086, by rfl⟩ : syracuseStep 1442897 = 1082173) B1082173
theorem B2032721 : Blo 599292 2032721 := bstep (se 2 (by rfl) ⟨762270, by rfl⟩ : syracuseStep 2032721 = 1524541) B1524541
theorem B1016995 : Blo 599292 1016995 := bstep (se 1 (by rfl) ⟨762746, by rfl⟩ : syracuseStep 1016995 = 1525493) B1525493
theorem B1017137 : Blo 599292 1017137 := bstep (se 2 (by rfl) ⟨381426, by rfl⟩ : syracuseStep 1017137 = 762853) B762853
theorem B853363 : Blo 599292 853363 := bstep (se 1 (by rfl) ⟨640022, by rfl⟩ : syracuseStep 853363 = 1280045) B1280045
theorem B9733517 : Blo 599292 9733517 := bstep (se 3 (by rfl) ⟨1825034, by rfl⟩ : syracuseStep 9733517 = 3650069) B3650069
theorem B1017265 : Blo 599292 1017265 := bstep (se 2 (by rfl) ⟨381474, by rfl⟩ : syracuseStep 1017265 = 762949) B762949
theorem B722371 : Blo 599292 722371 := bstep (se 1 (by rfl) ⟨541778, by rfl⟩ : syracuseStep 722371 = 1083557) B1083557
theorem B11699653 : Blo 599292 11699653 := bstep (se 4 (by rfl) ⟨1096842, by rfl⟩ : syracuseStep 11699653 = 2193685) B2193685
theorem B1017299 : Blo 599292 1017299 := bstep (se 1 (by rfl) ⟨762974, by rfl⟩ : syracuseStep 1017299 = 1525949) B1525949
theorem B6522353 : Blo 599292 6522353 := bstep (se 2 (by rfl) ⟨2445882, by rfl⟩ : syracuseStep 6522353 = 4891765) B4891765
theorem B1443395 : Blo 599292 1443395 := bstep (se 1 (by rfl) ⟨1082546, by rfl⟩ : syracuseStep 1443395 = 2165093) B2165093
theorem B722515 : Blo 599292 722515 := bstep (se 1 (by rfl) ⟨541886, by rfl⟩ : syracuseStep 722515 = 1083773) B1083773
theorem B1017427 : Blo 599292 1017427 := bstep (se 1 (by rfl) ⟨763070, by rfl⟩ : syracuseStep 1017427 = 1526141) B1526141
theorem B2033261 : Blo 599292 2033261 := bstep (se 3 (by rfl) ⟨381236, by rfl⟩ : syracuseStep 2033261 = 762473) B762473
theorem B5146253 : Blo 599292 5146253 := bstep (se 3 (by rfl) ⟨964922, by rfl⟩ : syracuseStep 5146253 = 1929845) B1929845
theorem B2033315 : Blo 599292 2033315 := bstep (se 1 (by rfl) ⟨1524986, by rfl⟩ : syracuseStep 2033315 = 3049973) B3049973
theorem B1017569 : Blo 599292 1017569 := bstep (se 2 (by rfl) ⟨381588, by rfl⟩ : syracuseStep 1017569 = 763177) B763177
theorem B1443587 : Blo 599292 1443587 := bstep (se 1 (by rfl) ⟨1082690, by rfl⟩ : syracuseStep 1443587 = 2165381) B2165381
theorem B1017697 : Blo 599292 1017697 := bstep (se 2 (by rfl) ⟨381636, by rfl⟩ : syracuseStep 1017697 = 763273) B763273
theorem B1017731 : Blo 599292 1017731 := bstep (se 1 (by rfl) ⟨763298, by rfl⟩ : syracuseStep 1017731 = 1526597) B1526597
theorem B2033585 : Blo 599292 2033585 := bstep (se 2 (by rfl) ⟨762594, by rfl⟩ : syracuseStep 2033585 = 1525189) B1525189
theorem B1017859 : Blo 599292 1017859 := bstep (se 1 (by rfl) ⟨763394, by rfl⟩ : syracuseStep 1017859 = 1526789) B1526789
theorem B1018001 : Blo 599292 1018001 := bstep (se 2 (by rfl) ⟨381750, by rfl⟩ : syracuseStep 1018001 = 763501) B763501
theorem B3049649 : Blo 599292 3049649 := bstep (se 2 (by rfl) ⟨1143618, by rfl⟩ : syracuseStep 3049649 = 2287237) B2287237
theorem B1280387 : Blo 599292 1280387 := bstep (se 1 (by rfl) ⟨960290, by rfl⟩ : syracuseStep 1280387 = 1920581) B1920581
theorem B2034125 : Blo 599292 2034125 := bstep (se 3 (by rfl) ⟨381398, by rfl⟩ : syracuseStep 2034125 = 762797) B762797
theorem B2034179 : Blo 599292 2034179 := bstep (se 1 (by rfl) ⟨1525634, by rfl⟩ : syracuseStep 2034179 = 3051269) B3051269
theorem B6851141 : Blo 599292 6851141 := bstep (se 4 (by rfl) ⟨642294, by rfl⟩ : syracuseStep 6851141 = 1284589) B1284589
theorem B2230861 : Blo 599292 2230861 := bstep (se 3 (by rfl) ⟨418286, by rfl⟩ : syracuseStep 2230861 = 836573) B836573
theorem B854707 : Blo 599292 854707 := bstep (se 1 (by rfl) ⟨641030, by rfl⟩ : syracuseStep 854707 = 1282061) B1282061
theorem B6163141 : Blo 599292 6163141 := bstep (se 4 (by rfl) ⟨577794, by rfl⟩ : syracuseStep 6163141 = 1155589) B1155589
theorem B2034449 : Blo 599292 2034449 := bstep (se 2 (by rfl) ⟨762918, by rfl⟩ : syracuseStep 2034449 = 1525837) B1525837
theorem B10292021 : Blo 599292 10292021 := bstep (se 5 (by rfl) ⟨482438, by rfl⟩ : syracuseStep 10292021 = 964877) B964877
theorem B1281233 : Blo 599292 1281233 := bstep (se 2 (by rfl) ⟨480462, by rfl⟩ : syracuseStep 1281233 = 960925) B960925
theorem B2034989 : Blo 599292 2034989 := bstep (se 3 (by rfl) ⟨381560, by rfl⟩ : syracuseStep 2034989 = 763121) B763121
theorem B724307 : Blo 599292 724307 := bstep (se 1 (by rfl) ⟨543230, by rfl⟩ : syracuseStep 724307 = 1086461) B1086461
theorem B2035043 : Blo 599292 2035043 := bstep (se 1 (by rfl) ⟨1526282, by rfl⟩ : syracuseStep 2035043 = 3052565) B3052565
theorem B4558193 : Blo 599292 4558193 := bstep (se 2 (by rfl) ⟨1709322, by rfl⟩ : syracuseStep 4558193 = 3418645) B3418645
theorem B1707409 : Blo 599292 1707409 := bstep (se 2 (by rfl) ⟨640278, by rfl⟩ : syracuseStep 1707409 = 1280557) B1280557
theorem B3247685 : Blo 599292 3247685 := bstep (se 4 (by rfl) ⟨304470, by rfl⟩ : syracuseStep 3247685 = 608941) B608941
theorem B3051107 : Blo 599292 3051107 := bstep (se 1 (by rfl) ⟨2288330, by rfl⟩ : syracuseStep 3051107 = 4576661) B4576661
theorem B2035313 : Blo 599292 2035313 := bstep (se 2 (by rfl) ⟨763242, by rfl⟩ : syracuseStep 2035313 = 1526485) B1526485
theorem B1445539 : Blo 599292 1445539 := bstep (se 1 (by rfl) ⟨1084154, by rfl⟩ : syracuseStep 1445539 = 2168309) B2168309
theorem B855841 : Blo 599292 855841 := bstep (se 2 (by rfl) ⟨320940, by rfl⟩ : syracuseStep 855841 = 641881) B641881
theorem B855937 : Blo 599292 855937 := bstep (se 2 (by rfl) ⟨320976, by rfl⟩ : syracuseStep 855937 = 641953) B641953
theorem B1085329 : Blo 599292 1085329 := bstep (se 2 (by rfl) ⟨406998, by rfl⟩ : syracuseStep 1085329 = 813997) B813997
theorem B1544113 : Blo 599292 1544113 := bstep (se 2 (by rfl) ⟨579042, by rfl⟩ : syracuseStep 1544113 = 1158085) B1158085
theorem B2166925 : Blo 599292 2166925 := bstep (se 3 (by rfl) ⟨406298, by rfl⟩ : syracuseStep 2166925 = 812597) B812597
theorem B2035853 : Blo 599292 2035853 := bstep (se 3 (by rfl) ⟨381722, by rfl⟩ : syracuseStep 2035853 = 763445) B763445
theorem B2035907 : Blo 599292 2035907 := bstep (se 1 (by rfl) ⟨1526930, by rfl⟩ : syracuseStep 2035907 = 3053861) B3053861
theorem B3248333 : Blo 599292 3248333 := bstep (se 3 (by rfl) ⟨609062, by rfl⟩ : syracuseStep 3248333 = 1218125) B1218125
theorem B856433 : Blo 599292 856433 := bstep (se 2 (by rfl) ⟨321162, by rfl⟩ : syracuseStep 856433 = 642325) B642325
theorem B3051917 : Blo 599292 3051917 := bstep (se 3 (by rfl) ⟨572234, by rfl⟩ : syracuseStep 3051917 = 1144469) B1144469
theorem B1085891 : Blo 599292 1085891 := bstep (se 1 (by rfl) ⟨814418, by rfl⟩ : syracuseStep 1085891 = 1628837) B1628837
theorem B954865 : Blo 599292 954865 := bstep (se 2 (by rfl) ⟨358074, by rfl⟩ : syracuseStep 954865 = 716149) B716149
theorem B1708685 : Blo 599292 1708685 := bstep (se 3 (by rfl) ⟨320378, by rfl⟩ : syracuseStep 1708685 = 640757) B640757
theorem B1708867 : Blo 599292 1708867 := bstep (se 1 (by rfl) ⟨1281650, by rfl⟩ : syracuseStep 1708867 = 2563301) B2563301
theorem B1348433 : Blo 599292 1348433 := bstep (se 2 (by rfl) ⟨505662, by rfl⟩ : syracuseStep 1348433 = 1011325) B1011325
theorem B1348451 : Blo 599292 1348451 := bstep (se 1 (by rfl) ⟨1011338, by rfl⟩ : syracuseStep 1348451 = 2022677) B2022677
theorem B1282915 : Blo 599292 1282915 := bstep (se 1 (by rfl) ⟨962186, by rfl⟩ : syracuseStep 1282915 = 1924373) B1924373
theorem B1708913 : Blo 599292 1708913 := bstep (se 2 (by rfl) ⟨640842, by rfl⟩ : syracuseStep 1708913 = 1281685) B1281685
theorem B1446769 : Blo 599292 1446769 := bstep (se 2 (by rfl) ⟨542538, by rfl⟩ : syracuseStep 1446769 = 1085077) B1085077
theorem B2560909 : Blo 599292 2560909 := bstep (se 3 (by rfl) ⟨480170, by rfl⟩ : syracuseStep 2560909 = 960341) B960341
theorem B758803 : Blo 599292 758803 := bstep (se 1 (by rfl) ⟨569102, by rfl⟩ : syracuseStep 758803 = 1138205) B1138205
theorem B1348721 : Blo 599292 1348721 := bstep (se 2 (by rfl) ⟨505770, by rfl⟩ : syracuseStep 1348721 = 1011541) B1011541
theorem B758899 : Blo 599292 758899 := bstep (se 1 (by rfl) ⟨569174, by rfl⟩ : syracuseStep 758899 = 1138349) B1138349
theorem B1348739 : Blo 599292 1348739 := bstep (se 1 (by rfl) ⟨1011554, by rfl⟩ : syracuseStep 1348739 = 2023109) B2023109
theorem B857299 : Blo 599292 857299 := bstep (se 1 (by rfl) ⟨642974, by rfl⟩ : syracuseStep 857299 = 1285949) B1285949
theorem B1283377 : Blo 599292 1283377 := bstep (se 2 (by rfl) ⟨481266, by rfl⟩ : syracuseStep 1283377 = 962533) B962533
theorem B857395 : Blo 599292 857395 := bstep (se 1 (by rfl) ⟨643046, by rfl⟩ : syracuseStep 857395 = 1286093) B1286093
theorem B11736433 : Blo 599292 11736433 := bstep (se 2 (by rfl) ⟨4401162, by rfl⟩ : syracuseStep 11736433 = 8802325) B8802325
theorem B1349009 : Blo 599292 1349009 := bstep (se 2 (by rfl) ⟨505878, by rfl⟩ : syracuseStep 1349009 = 1011757) B1011757
theorem B1349027 : Blo 599292 1349027 := bstep (se 1 (by rfl) ⟨1011770, by rfl⟩ : syracuseStep 1349027 = 2023541) B2023541
theorem B759395 : Blo 599292 759395 := bstep (se 1 (by rfl) ⟨569546, by rfl⟩ : syracuseStep 759395 = 1139093) B1139093
theorem B1349297 : Blo 599292 1349297 := bstep (se 2 (by rfl) ⟨505986, by rfl⟩ : syracuseStep 1349297 = 1011973) B1011973
theorem B1349315 : Blo 599292 1349315 := bstep (se 1 (by rfl) ⟨1011986, by rfl⟩ : syracuseStep 1349315 = 2023973) B2023973
theorem B26285795 : Blo 599292 26285795 := bstep (se 1 (by rfl) ⟨19714346, by rfl⟩ : syracuseStep 26285795 = 39428693) B39428693
theorem B857891 : Blo 599292 857891 := bstep (se 1 (by rfl) ⟨643418, by rfl⟩ : syracuseStep 857891 = 1286837) B1286837
theorem B1218449 : Blo 599292 1218449 := bstep (se 2 (by rfl) ⟨456918, by rfl⟩ : syracuseStep 1218449 = 913837) B913837
theorem B2561969 : Blo 599292 2561969 := bstep (se 2 (by rfl) ⟨960738, by rfl⟩ : syracuseStep 2561969 = 1921477) B1921477
theorem B1349585 : Blo 599292 1349585 := bstep (se 2 (by rfl) ⟨506094, by rfl⟩ : syracuseStep 1349585 = 1012189) B1012189
theorem B1349603 : Blo 599292 1349603 := bstep (se 1 (by rfl) ⟨1012202, by rfl⟩ : syracuseStep 1349603 = 2024405) B2024405
theorem B1349873 : Blo 599292 1349873 := bstep (se 2 (by rfl) ⟨506202, by rfl⟩ : syracuseStep 1349873 = 1012405) B1012405
theorem B5478641 : Blo 599292 5478641 := bstep (se 2 (by rfl) ⟨2054490, by rfl⟩ : syracuseStep 5478641 = 4108981) B4108981
theorem B1349891 : Blo 599292 1349891 := bstep (se 1 (by rfl) ⟨1012418, by rfl⟩ : syracuseStep 1349891 = 2024837) B2024837
theorem B760099 : Blo 599292 760099 := bstep (se 1 (by rfl) ⟨570074, by rfl⟩ : syracuseStep 760099 = 1140149) B1140149
theorem B1710371 : Blo 599292 1710371 := bstep (se 1 (by rfl) ⟨1282778, by rfl⟩ : syracuseStep 1710371 = 2565557) B2565557
theorem B2890019 : Blo 599292 2890019 := bstep (se 1 (by rfl) ⟨2167514, by rfl⟩ : syracuseStep 2890019 = 4335029) B4335029
theorem B1284419 : Blo 599292 1284419 := bstep (se 1 (by rfl) ⟨963314, by rfl⟩ : syracuseStep 1284419 = 1926629) B1926629
theorem B760195 : Blo 599292 760195 := bstep (se 1 (by rfl) ⟨570146, by rfl⟩ : syracuseStep 760195 = 1140293) B1140293
theorem B858529 : Blo 599292 858529 := bstep (se 2 (by rfl) ⟨321948, by rfl⟩ : syracuseStep 858529 = 643897) B643897
theorem B1350161 : Blo 599292 1350161 := bstep (se 2 (by rfl) ⟨506310, by rfl⟩ : syracuseStep 1350161 = 1012621) B1012621
theorem B1350179 : Blo 599292 1350179 := bstep (se 1 (by rfl) ⟨1012634, by rfl⟩ : syracuseStep 1350179 = 2025269) B2025269
theorem B2431565 : Blo 599292 2431565 := bstep (se 3 (by rfl) ⟨455918, by rfl⟩ : syracuseStep 2431565 = 911837) B911837
theorem B858865 : Blo 599292 858865 := bstep (se 2 (by rfl) ⟨322074, by rfl⟩ : syracuseStep 858865 = 644149) B644149
theorem B3414797 : Blo 599292 3414797 := bstep (se 3 (by rfl) ⟨640274, by rfl⟩ : syracuseStep 3414797 = 1280549) B1280549
theorem B1350449 : Blo 599292 1350449 := bstep (se 2 (by rfl) ⟨506418, by rfl⟩ : syracuseStep 1350449 = 1012837) B1012837
theorem B1350467 : Blo 599292 1350467 := bstep (se 1 (by rfl) ⟨1012850, by rfl⟩ : syracuseStep 1350467 = 2025701) B2025701
theorem B1284931 : Blo 599292 1284931 := bstep (se 1 (by rfl) ⟨963698, by rfl⟩ : syracuseStep 1284931 = 1927397) B1927397
theorem B760691 : Blo 599292 760691 := bstep (se 1 (by rfl) ⟨570518, by rfl⟩ : syracuseStep 760691 = 1141037) B1141037
theorem B1350737 : Blo 599292 1350737 := bstep (se 2 (by rfl) ⟨506526, by rfl⟩ : syracuseStep 1350737 = 1013053) B1013053
theorem B1350755 : Blo 599292 1350755 := bstep (se 1 (by rfl) ⟨1013066, by rfl⟩ : syracuseStep 1350755 = 2026133) B2026133
theorem B2890865 : Blo 599292 2890865 := bstep (se 2 (by rfl) ⟨1084074, by rfl⟩ : syracuseStep 2890865 = 2168149) B2168149
theorem B1351025 : Blo 599292 1351025 := bstep (se 2 (by rfl) ⟨506634, by rfl⟩ : syracuseStep 1351025 = 1013269) B1013269
theorem B1351043 : Blo 599292 1351043 := bstep (se 1 (by rfl) ⟨1013282, by rfl⟩ : syracuseStep 1351043 = 2026565) B2026565
theorem B1711601 : Blo 599292 1711601 := bstep (se 2 (by rfl) ⟨641850, by rfl⟩ : syracuseStep 1711601 = 1283701) B1283701
theorem B1285649 : Blo 599292 1285649 := bstep (se 2 (by rfl) ⟨482118, by rfl⟩ : syracuseStep 1285649 = 964237) B964237
theorem B761395 : Blo 599292 761395 := bstep (se 1 (by rfl) ⟨571046, by rfl⟩ : syracuseStep 761395 = 1142093) B1142093
theorem B1351313 : Blo 599292 1351313 := bstep (se 2 (by rfl) ⟨506742, by rfl⟩ : syracuseStep 1351313 = 1013485) B1013485
theorem B761491 : Blo 599292 761491 := bstep (se 1 (by rfl) ⟨571118, by rfl⟩ : syracuseStep 761491 = 1142237) B1142237
theorem B1351331 : Blo 599292 1351331 := bstep (se 1 (by rfl) ⟨1013498, by rfl⟩ : syracuseStep 1351331 = 2026997) B2026997
theorem B3415729 : Blo 599292 3415729 := bstep (se 2 (by rfl) ⟨1280898, by rfl⟩ : syracuseStep 3415729 = 2561797) B2561797
theorem B1351601 : Blo 599292 1351601 := bstep (se 2 (by rfl) ⟨506850, by rfl⟩ : syracuseStep 1351601 = 1013701) B1013701
theorem B1351619 : Blo 599292 1351619 := bstep (se 1 (by rfl) ⟨1013714, by rfl⟩ : syracuseStep 1351619 = 2027429) B2027429
theorem B761987 : Blo 599292 761987 := bstep (se 1 (by rfl) ⟨571490, by rfl⟩ : syracuseStep 761987 = 1142981) B1142981
theorem B1220753 : Blo 599292 1220753 := bstep (se 2 (by rfl) ⟨457782, by rfl⟩ : syracuseStep 1220753 = 915565) B915565
theorem B1351889 : Blo 599292 1351889 := bstep (se 2 (by rfl) ⟨506958, by rfl⟩ : syracuseStep 1351889 = 1013917) B1013917
theorem B1351907 : Blo 599292 1351907 := bstep (se 1 (by rfl) ⟨1013930, by rfl⟩ : syracuseStep 1351907 = 2027861) B2027861
theorem B6856973 : Blo 599292 6856973 := bstep (se 3 (by rfl) ⟨1285682, by rfl⟩ : syracuseStep 6856973 = 2571365) B2571365
theorem B1286435 : Blo 599292 1286435 := bstep (se 1 (by rfl) ⟨964826, by rfl⟩ : syracuseStep 1286435 = 1929653) B1929653
theorem B1352177 : Blo 599292 1352177 := bstep (se 2 (by rfl) ⟨507066, by rfl⟩ : syracuseStep 1352177 = 1014133) B1014133
theorem B1352195 : Blo 599292 1352195 := bstep (se 1 (by rfl) ⟨1014146, by rfl⟩ : syracuseStep 1352195 = 2028293) B2028293
theorem B795187 : Blo 599292 795187 := bstep (se 1 (by rfl) ⟨596390, by rfl⟩ : syracuseStep 795187 = 1192781) B1192781
theorem B3842801 : Blo 599292 3842801 := bstep (se 2 (by rfl) ⟨1441050, by rfl⟩ : syracuseStep 3842801 = 2882101) B2882101
theorem B6497009 : Blo 599292 6497009 := bstep (se 2 (by rfl) ⟨2436378, by rfl⟩ : syracuseStep 6497009 = 4872757) B4872757
theorem B1352465 : Blo 599292 1352465 := bstep (se 2 (by rfl) ⟨507174, by rfl⟩ : syracuseStep 1352465 = 1014349) B1014349
theorem B1352483 : Blo 599292 1352483 := bstep (se 1 (by rfl) ⟨1014362, by rfl⟩ : syracuseStep 1352483 = 2028725) B2028725
theorem B762691 : Blo 599292 762691 := bstep (se 1 (by rfl) ⟨572018, by rfl⟩ : syracuseStep 762691 = 1144037) B1144037
theorem B2564941 : Blo 599292 2564941 := bstep (se 3 (by rfl) ⟨480926, by rfl⟩ : syracuseStep 2564941 = 961853) B961853
theorem B1713059 : Blo 599292 1713059 := bstep (se 1 (by rfl) ⟨1284794, by rfl⟩ : syracuseStep 1713059 = 2569589) B2569589
theorem B762787 : Blo 599292 762787 := bstep (se 1 (by rfl) ⟨572090, by rfl⟩ : syracuseStep 762787 = 1144181) B1144181
theorem B1352753 : Blo 599292 1352753 := bstep (se 2 (by rfl) ⟨507282, by rfl⟩ : syracuseStep 1352753 = 1014565) B1014565
theorem B1352771 : Blo 599292 1352771 := bstep (se 1 (by rfl) ⟨1014578, by rfl⟩ : syracuseStep 1352771 = 2029157) B2029157
theorem B3417187 : Blo 599292 3417187 := bstep (se 1 (by rfl) ⟨2562890, by rfl⟩ : syracuseStep 3417187 = 5125781) B5125781
theorem B2892941 : Blo 599292 2892941 := bstep (se 3 (by rfl) ⟨542426, by rfl⟩ : syracuseStep 2892941 = 1084853) B1084853
theorem B2565283 : Blo 599292 2565283 := bstep (se 1 (by rfl) ⟨1923962, by rfl⟩ : syracuseStep 2565283 = 3847925) B3847925
theorem B1287409 : Blo 599292 1287409 := bstep (se 2 (by rfl) ⟨482778, by rfl⟩ : syracuseStep 1287409 = 965557) B965557
theorem B599299 : Blo 599292 599299 := bstep (se 1 (by rfl) ⟨449474, by rfl⟩ : syracuseStep 599299 = 898949) B898949
theorem B599315 : Blo 599292 599315 := bstep (se 1 (by rfl) ⟨449486, by rfl⟩ : syracuseStep 599315 = 898973) B898973
theorem B599331 : Blo 599292 599331 := bstep (se 1 (by rfl) ⟨449498, by rfl⟩ : syracuseStep 599331 = 898997) B898997
theorem B599347 : Blo 599292 599347 := bstep (se 1 (by rfl) ⟨449510, by rfl⟩ : syracuseStep 599347 = 899021) B899021
theorem B599363 : Blo 599292 599363 := bstep (se 1 (by rfl) ⟨449522, by rfl⟩ : syracuseStep 599363 = 899045) B899045
theorem B1353041 : Blo 599292 1353041 := bstep (se 2 (by rfl) ⟨507390, by rfl⟩ : syracuseStep 1353041 = 1014781) B1014781
theorem B599379 : Blo 599292 599379 := bstep (se 1 (by rfl) ⟨449534, by rfl⟩ : syracuseStep 599379 = 899069) B899069
theorem B599395 : Blo 599292 599395 := bstep (se 1 (by rfl) ⟨449546, by rfl⟩ : syracuseStep 599395 = 899093) B899093
theorem B1353059 : Blo 599292 1353059 := bstep (se 1 (by rfl) ⟨1014794, by rfl⟩ : syracuseStep 1353059 = 2029589) B2029589
theorem B599411 : Blo 599292 599411 := bstep (se 1 (by rfl) ⟨449558, by rfl⟩ : syracuseStep 599411 = 899117) B899117
theorem B599427 : Blo 599292 599427 := bstep (se 1 (by rfl) ⟨449570, by rfl⟩ : syracuseStep 599427 = 899141) B899141
theorem B599443 : Blo 599292 599443 := bstep (se 1 (by rfl) ⟨449582, by rfl⟩ : syracuseStep 599443 = 899165) B899165
theorem B763283 : Blo 599292 763283 := bstep (se 1 (by rfl) ⟨572462, by rfl⟩ : syracuseStep 763283 = 1144925) B1144925
theorem B599459 : Blo 599292 599459 := bstep (se 1 (by rfl) ⟨449594, by rfl⟩ : syracuseStep 599459 = 899189) B899189
theorem B599475 : Blo 599292 599475 := bstep (se 1 (by rfl) ⟨449606, by rfl⟩ : syracuseStep 599475 = 899213) B899213
theorem B599491 : Blo 599292 599491 := bstep (se 1 (by rfl) ⟨449618, by rfl⟩ : syracuseStep 599491 = 899237) B899237
theorem B599507 : Blo 599292 599507 := bstep (se 1 (by rfl) ⟨449630, by rfl⟩ : syracuseStep 599507 = 899261) B899261
theorem B599523 : Blo 599292 599523 := bstep (se 1 (by rfl) ⟨449642, by rfl⟩ : syracuseStep 599523 = 899285) B899285
theorem B1287665 : Blo 599292 1287665 := bstep (se 2 (by rfl) ⟨482874, by rfl⟩ : syracuseStep 1287665 = 965749) B965749
theorem B599539 : Blo 599292 599539 := bstep (se 1 (by rfl) ⟨449654, by rfl⟩ : syracuseStep 599539 = 899309) B899309
theorem B599555 : Blo 599292 599555 := bstep (se 1 (by rfl) ⟨449666, by rfl⟩ : syracuseStep 599555 = 899333) B899333
theorem B599571 : Blo 599292 599571 := bstep (se 1 (by rfl) ⟨449678, by rfl⟩ : syracuseStep 599571 = 899357) B899357
theorem B599587 : Blo 599292 599587 := bstep (se 1 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 599587 = 899381) B899381
theorem B599603 : Blo 599292 599603 := bstep (se 1 (by rfl) ⟨449702, by rfl⟩ : syracuseStep 599603 = 899405) B899405
theorem B599619 : Blo 599292 599619 := bstep (se 1 (by rfl) ⟨449714, by rfl⟩ : syracuseStep 599619 = 899429) B899429
theorem B599635 : Blo 599292 599635 := bstep (se 1 (by rfl) ⟨449726, by rfl⟩ : syracuseStep 599635 = 899453) B899453
theorem B599651 : Blo 599292 599651 := bstep (se 1 (by rfl) ⟨449738, by rfl⟩ : syracuseStep 599651 = 899477) B899477
theorem B3417713 : Blo 599292 3417713 := bstep (se 2 (by rfl) ⟨1281642, by rfl⟩ : syracuseStep 3417713 = 2563285) B2563285
theorem B1353329 : Blo 599292 1353329 := bstep (se 2 (by rfl) ⟨507498, by rfl⟩ : syracuseStep 1353329 = 1014997) B1014997
theorem B599667 : Blo 599292 599667 := bstep (se 1 (by rfl) ⟨449750, by rfl⟩ : syracuseStep 599667 = 899501) B899501
theorem B599683 : Blo 599292 599683 := bstep (se 1 (by rfl) ⟨449762, by rfl⟩ : syracuseStep 599683 = 899525) B899525
theorem B1353347 : Blo 599292 1353347 := bstep (se 1 (by rfl) ⟨1015010, by rfl⟩ : syracuseStep 1353347 = 2030021) B2030021
theorem B6006413 : Blo 599292 6006413 := bstep (se 3 (by rfl) ⟨1126202, by rfl⟩ : syracuseStep 6006413 = 2252405) B2252405
theorem B1517201 : Blo 599292 1517201 := bstep (se 2 (by rfl) ⟨568950, by rfl⟩ : syracuseStep 1517201 = 1137901) B1137901
theorem B599699 : Blo 599292 599699 := bstep (se 1 (by rfl) ⟨449774, by rfl⟩ : syracuseStep 599699 = 899549) B899549
theorem B599715 : Blo 599292 599715 := bstep (se 1 (by rfl) ⟨449786, by rfl⟩ : syracuseStep 599715 = 899573) B899573
theorem B599731 : Blo 599292 599731 := bstep (se 1 (by rfl) ⟨449798, by rfl⟩ : syracuseStep 599731 = 899597) B899597
theorem B1517251 : Blo 599292 1517251 := bstep (se 1 (by rfl) ⟨1137938, by rfl⟩ : syracuseStep 1517251 = 2275877) B2275877
theorem B599747 : Blo 599292 599747 := bstep (se 1 (by rfl) ⟨449810, by rfl⟩ : syracuseStep 599747 = 899621) B899621
theorem B1713869 : Blo 599292 1713869 := bstep (se 3 (by rfl) ⟨321350, by rfl⟩ : syracuseStep 1713869 = 642701) B642701
theorem B599763 : Blo 599292 599763 := bstep (se 1 (by rfl) ⟨449822, by rfl⟩ : syracuseStep 599763 = 899645) B899645
theorem B599779 : Blo 599292 599779 := bstep (se 1 (by rfl) ⟨449834, by rfl⟩ : syracuseStep 599779 = 899669) B899669
theorem B1976035 : Blo 599292 1976035 := bstep (se 1 (by rfl) ⟨1482026, by rfl⟩ : syracuseStep 1976035 = 2964053) B2964053
theorem B599795 : Blo 599292 599795 := bstep (se 1 (by rfl) ⟨449846, by rfl⟩ : syracuseStep 599795 = 899693) B899693
theorem B599811 : Blo 599292 599811 := bstep (se 1 (by rfl) ⟨449858, by rfl⟩ : syracuseStep 599811 = 899717) B899717
theorem B6956813 : Blo 599292 6956813 := bstep (se 3 (by rfl) ⟨1304402, by rfl⟩ : syracuseStep 6956813 = 2608805) B2608805
theorem B599827 : Blo 599292 599827 := bstep (se 1 (by rfl) ⟨449870, by rfl⟩ : syracuseStep 599827 = 899741) B899741
theorem B599843 : Blo 599292 599843 := bstep (se 1 (by rfl) ⟨449882, by rfl⟩ : syracuseStep 599843 = 899765) B899765
theorem B599859 : Blo 599292 599859 := bstep (se 1 (by rfl) ⟨449894, by rfl⟩ : syracuseStep 599859 = 899789) B899789
theorem B599875 : Blo 599292 599875 := bstep (se 1 (by rfl) ⟨449906, by rfl⟩ : syracuseStep 599875 = 899813) B899813
theorem B1517393 : Blo 599292 1517393 := bstep (se 2 (by rfl) ⟨569022, by rfl⟩ : syracuseStep 1517393 = 1138045) B1138045
theorem B599891 : Blo 599292 599891 := bstep (se 1 (by rfl) ⟨449918, by rfl⟩ : syracuseStep 599891 = 899837) B899837
theorem B599907 : Blo 599292 599907 := bstep (se 1 (by rfl) ⟨449930, by rfl⟩ : syracuseStep 599907 = 899861) B899861
theorem B599923 : Blo 599292 599923 := bstep (se 1 (by rfl) ⟨449942, by rfl⟩ : syracuseStep 599923 = 899885) B899885
theorem B599939 : Blo 599292 599939 := bstep (se 1 (by rfl) ⟨449954, by rfl⟩ : syracuseStep 599939 = 899909) B899909
theorem B1714061 : Blo 599292 1714061 := bstep (se 3 (by rfl) ⟨321386, by rfl⟩ : syracuseStep 1714061 = 642773) B642773
theorem B1353617 : Blo 599292 1353617 := bstep (se 2 (by rfl) ⟨507606, by rfl⟩ : syracuseStep 1353617 = 1015213) B1015213
theorem B599955 : Blo 599292 599955 := bstep (se 1 (by rfl) ⟨449966, by rfl⟩ : syracuseStep 599955 = 899933) B899933
theorem B599971 : Blo 599292 599971 := bstep (se 1 (by rfl) ⟨449978, by rfl⟩ : syracuseStep 599971 = 899957) B899957
theorem B1353635 : Blo 599292 1353635 := bstep (se 1 (by rfl) ⟨1015226, by rfl⟩ : syracuseStep 1353635 = 2030453) B2030453
theorem B599987 : Blo 599292 599987 := bstep (se 1 (by rfl) ⟨449990, by rfl⟩ : syracuseStep 599987 = 899981) B899981
theorem B600003 : Blo 599292 600003 := bstep (se 1 (by rfl) ⟨450002, by rfl⟩ : syracuseStep 600003 = 900005) B900005
theorem B600019 : Blo 599292 600019 := bstep (se 1 (by rfl) ⟨450014, by rfl⟩ : syracuseStep 600019 = 900029) B900029
theorem B600035 : Blo 599292 600035 := bstep (se 1 (by rfl) ⟨450026, by rfl⟩ : syracuseStep 600035 = 900053) B900053
theorem B600051 : Blo 599292 600051 := bstep (se 1 (by rfl) ⟨450038, by rfl⟩ : syracuseStep 600051 = 900077) B900077
theorem B960515 : Blo 599292 960515 := bstep (se 1 (by rfl) ⟨720386, by rfl⟩ : syracuseStep 960515 = 1440773) B1440773
theorem B600067 : Blo 599292 600067 := bstep (se 1 (by rfl) ⟨450050, by rfl⟩ : syracuseStep 600067 = 900101) B900101
theorem B600083 : Blo 599292 600083 := bstep (se 1 (by rfl) ⟨450062, by rfl⟩ : syracuseStep 600083 = 900125) B900125
theorem B600099 : Blo 599292 600099 := bstep (se 1 (by rfl) ⟨450074, by rfl⟩ : syracuseStep 600099 = 900149) B900149
theorem B600115 : Blo 599292 600115 := bstep (se 1 (by rfl) ⟨450086, by rfl⟩ : syracuseStep 600115 = 900173) B900173
theorem B600131 : Blo 599292 600131 := bstep (se 1 (by rfl) ⟨450098, by rfl⟩ : syracuseStep 600131 = 900197) B900197
theorem B600147 : Blo 599292 600147 := bstep (se 1 (by rfl) ⟨450110, by rfl⟩ : syracuseStep 600147 = 900221) B900221
theorem B600163 : Blo 599292 600163 := bstep (se 1 (by rfl) ⟨450122, by rfl⟩ : syracuseStep 600163 = 900245) B900245
theorem B600179 : Blo 599292 600179 := bstep (se 1 (by rfl) ⟨450134, by rfl⟩ : syracuseStep 600179 = 900269) B900269
theorem B600195 : Blo 599292 600195 := bstep (se 1 (by rfl) ⟨450146, by rfl⟩ : syracuseStep 600195 = 900293) B900293
theorem B600211 : Blo 599292 600211 := bstep (se 1 (by rfl) ⟨450158, by rfl⟩ : syracuseStep 600211 = 900317) B900317
theorem B600227 : Blo 599292 600227 := bstep (se 1 (by rfl) ⟨450170, by rfl⟩ : syracuseStep 600227 = 900341) B900341
theorem B1353905 : Blo 599292 1353905 := bstep (se 2 (by rfl) ⟨507714, by rfl⟩ : syracuseStep 1353905 = 1015429) B1015429
theorem B600243 : Blo 599292 600243 := bstep (se 1 (by rfl) ⟨450182, by rfl⟩ : syracuseStep 600243 = 900365) B900365
theorem B600259 : Blo 599292 600259 := bstep (se 1 (by rfl) ⟨450194, by rfl⟩ : syracuseStep 600259 = 900389) B900389
theorem B1353923 : Blo 599292 1353923 := bstep (se 1 (by rfl) ⟨1015442, by rfl⟩ : syracuseStep 1353923 = 2030885) B2030885
theorem B600275 : Blo 599292 600275 := bstep (se 1 (by rfl) ⟨450206, by rfl⟩ : syracuseStep 600275 = 900413) B900413
theorem B600291 : Blo 599292 600291 := bstep (se 1 (by rfl) ⟨450218, by rfl⟩ : syracuseStep 600291 = 900437) B900437
theorem B600307 : Blo 599292 600307 := bstep (se 1 (by rfl) ⟨450230, by rfl⟩ : syracuseStep 600307 = 900461) B900461
theorem B600323 : Blo 599292 600323 := bstep (se 1 (by rfl) ⟨450242, by rfl⟩ : syracuseStep 600323 = 900485) B900485
theorem B600339 : Blo 599292 600339 := bstep (se 1 (by rfl) ⟨450254, by rfl⟩ : syracuseStep 600339 = 900509) B900509
theorem B600355 : Blo 599292 600355 := bstep (se 1 (by rfl) ⟨450266, by rfl⟩ : syracuseStep 600355 = 900533) B900533
theorem B600371 : Blo 599292 600371 := bstep (se 1 (by rfl) ⟨450278, by rfl⟩ : syracuseStep 600371 = 900557) B900557
theorem B600387 : Blo 599292 600387 := bstep (se 1 (by rfl) ⟨450290, by rfl⟩ : syracuseStep 600387 = 900581) B900581
theorem B600403 : Blo 599292 600403 := bstep (se 1 (by rfl) ⟨450302, by rfl⟩ : syracuseStep 600403 = 900605) B900605
theorem B600419 : Blo 599292 600419 := bstep (se 1 (by rfl) ⟨450314, by rfl⟩ : syracuseStep 600419 = 900629) B900629
theorem B600435 : Blo 599292 600435 := bstep (se 1 (by rfl) ⟨450326, by rfl⟩ : syracuseStep 600435 = 900653) B900653
theorem B600451 : Blo 599292 600451 := bstep (se 1 (by rfl) ⟨450338, by rfl⟩ : syracuseStep 600451 = 900677) B900677
theorem B600467 : Blo 599292 600467 := bstep (se 1 (by rfl) ⟨450350, by rfl⟩ : syracuseStep 600467 = 900701) B900701
theorem B600483 : Blo 599292 600483 := bstep (se 1 (by rfl) ⟨450362, by rfl⟩ : syracuseStep 600483 = 900725) B900725
theorem B600499 : Blo 599292 600499 := bstep (se 1 (by rfl) ⟨450374, by rfl⟩ : syracuseStep 600499 = 900749) B900749
theorem B600515 : Blo 599292 600515 := bstep (se 1 (by rfl) ⟨450386, by rfl⟩ : syracuseStep 600515 = 900773) B900773
theorem B1354193 : Blo 599292 1354193 := bstep (se 2 (by rfl) ⟨507822, by rfl⟩ : syracuseStep 1354193 = 1015645) B1015645
theorem B600531 : Blo 599292 600531 := bstep (se 1 (by rfl) ⟨450398, by rfl⟩ : syracuseStep 600531 = 900797) B900797
theorem B600547 : Blo 599292 600547 := bstep (se 1 (by rfl) ⟨450410, by rfl⟩ : syracuseStep 600547 = 900821) B900821
theorem B1354211 : Blo 599292 1354211 := bstep (se 1 (by rfl) ⟨1015658, by rfl⟩ : syracuseStep 1354211 = 2031317) B2031317
theorem B600563 : Blo 599292 600563 := bstep (se 1 (by rfl) ⟨450422, by rfl⟩ : syracuseStep 600563 = 900845) B900845
theorem B600579 : Blo 599292 600579 := bstep (se 1 (by rfl) ⟨450434, by rfl⟩ : syracuseStep 600579 = 900869) B900869
theorem B600595 : Blo 599292 600595 := bstep (se 1 (by rfl) ⟨450446, by rfl⟩ : syracuseStep 600595 = 900893) B900893
theorem B600611 : Blo 599292 600611 := bstep (se 1 (by rfl) ⟨450458, by rfl⟩ : syracuseStep 600611 = 900917) B900917
theorem B600627 : Blo 599292 600627 := bstep (se 1 (by rfl) ⟨450470, by rfl⟩ : syracuseStep 600627 = 900941) B900941
theorem B600643 : Blo 599292 600643 := bstep (se 1 (by rfl) ⟨450482, by rfl⟩ : syracuseStep 600643 = 900965) B900965
theorem B1026643 : Blo 599292 1026643 := bstep (se 1 (by rfl) ⟨769982, by rfl⟩ : syracuseStep 1026643 = 1539965) B1539965
theorem B600659 : Blo 599292 600659 := bstep (se 1 (by rfl) ⟨450494, by rfl⟩ : syracuseStep 600659 = 900989) B900989
theorem B600675 : Blo 599292 600675 := bstep (se 1 (by rfl) ⟨450506, by rfl⟩ : syracuseStep 600675 = 901013) B901013
theorem B15444593 : Blo 599292 15444593 := bstep (se 2 (by rfl) ⟨5791722, by rfl⟩ : syracuseStep 15444593 = 11583445) B11583445
theorem B600691 : Blo 599292 600691 := bstep (se 1 (by rfl) ⟨450518, by rfl⟩ : syracuseStep 600691 = 901037) B901037
theorem B600707 : Blo 599292 600707 := bstep (se 1 (by rfl) ⟨450530, by rfl⟩ : syracuseStep 600707 = 901061) B901061
theorem B600723 : Blo 599292 600723 := bstep (se 1 (by rfl) ⟨450542, by rfl⟩ : syracuseStep 600723 = 901085) B901085
theorem B600739 : Blo 599292 600739 := bstep (se 1 (by rfl) ⟨450554, by rfl⟩ : syracuseStep 600739 = 901109) B901109
theorem B600755 : Blo 599292 600755 := bstep (se 1 (by rfl) ⟨450566, by rfl⟩ : syracuseStep 600755 = 901133) B901133
theorem B600771 : Blo 599292 600771 := bstep (se 1 (by rfl) ⟨450578, by rfl⟩ : syracuseStep 600771 = 901157) B901157
theorem B600787 : Blo 599292 600787 := bstep (se 1 (by rfl) ⟨450590, by rfl⟩ : syracuseStep 600787 = 901181) B901181
theorem B600803 : Blo 599292 600803 := bstep (se 1 (by rfl) ⟨450602, by rfl⟩ : syracuseStep 600803 = 901205) B901205
theorem B1354481 : Blo 599292 1354481 := bstep (se 2 (by rfl) ⟨507930, by rfl⟩ : syracuseStep 1354481 = 1015861) B1015861
theorem B600819 : Blo 599292 600819 := bstep (se 1 (by rfl) ⟨450614, by rfl⟩ : syracuseStep 600819 = 901229) B901229
theorem B600835 : Blo 599292 600835 := bstep (se 1 (by rfl) ⟨450626, by rfl⟩ : syracuseStep 600835 = 901253) B901253
theorem B1354499 : Blo 599292 1354499 := bstep (se 1 (by rfl) ⟨1015874, by rfl⟩ : syracuseStep 1354499 = 2031749) B2031749
theorem B600851 : Blo 599292 600851 := bstep (se 1 (by rfl) ⟨450638, by rfl⟩ : syracuseStep 600851 = 901277) B901277
theorem B600867 : Blo 599292 600867 := bstep (se 1 (by rfl) ⟨450650, by rfl⟩ : syracuseStep 600867 = 901301) B901301
theorem B1518385 : Blo 599292 1518385 := bstep (se 2 (by rfl) ⟨569394, by rfl⟩ : syracuseStep 1518385 = 1138789) B1138789
theorem B600883 : Blo 599292 600883 := bstep (se 1 (by rfl) ⟨450662, by rfl⟩ : syracuseStep 600883 = 901325) B901325
theorem B600899 : Blo 599292 600899 := bstep (se 1 (by rfl) ⟨450674, by rfl⟩ : syracuseStep 600899 = 901349) B901349
theorem B600915 : Blo 599292 600915 := bstep (se 1 (by rfl) ⟨450686, by rfl⟩ : syracuseStep 600915 = 901373) B901373
theorem B600931 : Blo 599292 600931 := bstep (se 1 (by rfl) ⟨450698, by rfl⟩ : syracuseStep 600931 = 901397) B901397
theorem B1715053 : Blo 599292 1715053 := bstep (se 3 (by rfl) ⟨321572, by rfl⟩ : syracuseStep 1715053 = 643145) B643145
theorem B600947 : Blo 599292 600947 := bstep (se 1 (by rfl) ⟨450710, by rfl⟩ : syracuseStep 600947 = 901421) B901421
theorem B600963 : Blo 599292 600963 := bstep (se 1 (by rfl) ⟨450722, by rfl⟩ : syracuseStep 600963 = 901445) B901445
theorem B600979 : Blo 599292 600979 := bstep (se 1 (by rfl) ⟨450734, by rfl⟩ : syracuseStep 600979 = 901469) B901469
theorem B600995 : Blo 599292 600995 := bstep (se 1 (by rfl) ⟨450746, by rfl⟩ : syracuseStep 600995 = 901493) B901493
theorem B601011 : Blo 599292 601011 := bstep (se 1 (by rfl) ⟨450758, by rfl⟩ : syracuseStep 601011 = 901517) B901517
theorem B601027 : Blo 599292 601027 := bstep (se 1 (by rfl) ⟨450770, by rfl⟩ : syracuseStep 601027 = 901541) B901541
theorem B601043 : Blo 599292 601043 := bstep (se 1 (by rfl) ⟨450782, by rfl⟩ : syracuseStep 601043 = 901565) B901565
theorem B601059 : Blo 599292 601059 := bstep (se 1 (by rfl) ⟨450794, by rfl⟩ : syracuseStep 601059 = 901589) B901589
theorem B601075 : Blo 599292 601075 := bstep (se 1 (by rfl) ⟨450806, by rfl⟩ : syracuseStep 601075 = 901613) B901613
theorem B601091 : Blo 599292 601091 := bstep (se 1 (by rfl) ⟨450818, by rfl⟩ : syracuseStep 601091 = 901637) B901637
theorem B1354769 : Blo 599292 1354769 := bstep (se 2 (by rfl) ⟨508038, by rfl⟩ : syracuseStep 1354769 = 1016077) B1016077
theorem B601107 : Blo 599292 601107 := bstep (se 1 (by rfl) ⟨450830, by rfl⟩ : syracuseStep 601107 = 901661) B901661
theorem B3419171 : Blo 599292 3419171 := bstep (se 1 (by rfl) ⟨2564378, by rfl⟩ : syracuseStep 3419171 = 5128757) B5128757
theorem B601123 : Blo 599292 601123 := bstep (se 1 (by rfl) ⟨450842, by rfl⟩ : syracuseStep 601123 = 901685) B901685
theorem B1354787 : Blo 599292 1354787 := bstep (se 1 (by rfl) ⟨1016090, by rfl⟩ : syracuseStep 1354787 = 2032181) B2032181
theorem B601139 : Blo 599292 601139 := bstep (se 1 (by rfl) ⟨450854, by rfl⟩ : syracuseStep 601139 = 901709) B901709
theorem B1518659 : Blo 599292 1518659 := bstep (se 1 (by rfl) ⟨1138994, by rfl⟩ : syracuseStep 1518659 = 2277989) B2277989
theorem B601155 : Blo 599292 601155 := bstep (se 1 (by rfl) ⟨450866, by rfl⟩ : syracuseStep 601155 = 901733) B901733
theorem B601171 : Blo 599292 601171 := bstep (se 1 (by rfl) ⟨450878, by rfl⟩ : syracuseStep 601171 = 901757) B901757
theorem B601187 : Blo 599292 601187 := bstep (se 1 (by rfl) ⟨450890, by rfl⟩ : syracuseStep 601187 = 901781) B901781
theorem B6859889 : Blo 599292 6859889 := bstep (se 2 (by rfl) ⟨2572458, by rfl⟩ : syracuseStep 6859889 = 5144917) B5144917
theorem B601203 : Blo 599292 601203 := bstep (se 1 (by rfl) ⟨450902, by rfl⟩ : syracuseStep 601203 = 901805) B901805
theorem B601219 : Blo 599292 601219 := bstep (se 1 (by rfl) ⟨450914, by rfl⟩ : syracuseStep 601219 = 901829) B901829
theorem B601235 : Blo 599292 601235 := bstep (se 1 (by rfl) ⟨450926, by rfl⟩ : syracuseStep 601235 = 901853) B901853
theorem B601251 : Blo 599292 601251 := bstep (se 1 (by rfl) ⟨450938, by rfl⟩ : syracuseStep 601251 = 901877) B901877
theorem B601267 : Blo 599292 601267 := bstep (se 1 (by rfl) ⟨450950, by rfl⟩ : syracuseStep 601267 = 901901) B901901
theorem B601283 : Blo 599292 601283 := bstep (se 1 (by rfl) ⟨450962, by rfl⟩ : syracuseStep 601283 = 901925) B901925
theorem B601299 : Blo 599292 601299 := bstep (se 1 (by rfl) ⟨450974, by rfl⟩ : syracuseStep 601299 = 901949) B901949
theorem B601315 : Blo 599292 601315 := bstep (se 1 (by rfl) ⟨450986, by rfl⟩ : syracuseStep 601315 = 901973) B901973
theorem B601331 : Blo 599292 601331 := bstep (se 1 (by rfl) ⟨450998, by rfl⟩ : syracuseStep 601331 = 901997) B901997
theorem B1518851 : Blo 599292 1518851 := bstep (se 1 (by rfl) ⟨1139138, by rfl⟩ : syracuseStep 1518851 = 2278277) B2278277
theorem B601347 : Blo 599292 601347 := bstep (se 1 (by rfl) ⟨451010, by rfl⟩ : syracuseStep 601347 = 902021) B902021
theorem B601363 : Blo 599292 601363 := bstep (se 1 (by rfl) ⟨451022, by rfl⟩ : syracuseStep 601363 = 902045) B902045
theorem B601379 : Blo 599292 601379 := bstep (se 1 (by rfl) ⟨451034, by rfl⟩ : syracuseStep 601379 = 902069) B902069
theorem B1355057 : Blo 599292 1355057 := bstep (se 2 (by rfl) ⟨508146, by rfl⟩ : syracuseStep 1355057 = 1016293) B1016293
theorem B601395 : Blo 599292 601395 := bstep (se 1 (by rfl) ⟨451046, by rfl⟩ : syracuseStep 601395 = 902093) B902093
theorem B601411 : Blo 599292 601411 := bstep (se 1 (by rfl) ⟨451058, by rfl⟩ : syracuseStep 601411 = 902117) B902117
theorem B1355075 : Blo 599292 1355075 := bstep (se 1 (by rfl) ⟨1016306, by rfl⟩ : syracuseStep 1355075 = 2032613) B2032613
theorem B601427 : Blo 599292 601427 := bstep (se 1 (by rfl) ⟨451070, by rfl⟩ : syracuseStep 601427 = 902141) B902141
theorem B601443 : Blo 599292 601443 := bstep (se 1 (by rfl) ⟨451082, by rfl⟩ : syracuseStep 601443 = 902165) B902165
theorem B601459 : Blo 599292 601459 := bstep (se 1 (by rfl) ⟨451094, by rfl⟩ : syracuseStep 601459 = 902189) B902189
theorem B601475 : Blo 599292 601475 := bstep (se 1 (by rfl) ⟨451106, by rfl⟩ : syracuseStep 601475 = 902213) B902213
theorem B601491 : Blo 599292 601491 := bstep (se 1 (by rfl) ⟨451118, by rfl⟩ : syracuseStep 601491 = 902237) B902237
theorem B601507 : Blo 599292 601507 := bstep (se 1 (by rfl) ⟨451130, by rfl⟩ : syracuseStep 601507 = 902261) B902261
theorem B961969 : Blo 599292 961969 := bstep (se 2 (by rfl) ⟨360738, by rfl⟩ : syracuseStep 961969 = 721477) B721477
theorem B601523 : Blo 599292 601523 := bstep (se 1 (by rfl) ⟨451142, by rfl⟩ : syracuseStep 601523 = 902285) B902285
theorem B601539 : Blo 599292 601539 := bstep (se 1 (by rfl) ⟨451154, by rfl⟩ : syracuseStep 601539 = 902309) B902309
theorem B601555 : Blo 599292 601555 := bstep (se 1 (by rfl) ⟨451166, by rfl⟩ : syracuseStep 601555 = 902333) B902333
theorem B601571 : Blo 599292 601571 := bstep (se 1 (by rfl) ⟨451178, by rfl⟩ : syracuseStep 601571 = 902357) B902357
theorem B601587 : Blo 599292 601587 := bstep (se 1 (by rfl) ⟨451190, by rfl⟩ : syracuseStep 601587 = 902381) B902381
theorem B601603 : Blo 599292 601603 := bstep (se 1 (by rfl) ⟨451202, by rfl⟩ : syracuseStep 601603 = 902405) B902405
theorem B601619 : Blo 599292 601619 := bstep (se 1 (by rfl) ⟨451214, by rfl⟩ : syracuseStep 601619 = 902429) B902429
theorem B601635 : Blo 599292 601635 := bstep (se 1 (by rfl) ⟨451226, by rfl⟩ : syracuseStep 601635 = 902453) B902453
theorem B601651 : Blo 599292 601651 := bstep (se 1 (by rfl) ⟨451238, by rfl⟩ : syracuseStep 601651 = 902477) B902477
theorem B601667 : Blo 599292 601667 := bstep (se 1 (by rfl) ⟨451250, by rfl⟩ : syracuseStep 601667 = 902501) B902501
theorem B1355345 : Blo 599292 1355345 := bstep (se 2 (by rfl) ⟨508254, by rfl⟩ : syracuseStep 1355345 = 1016509) B1016509
theorem B601683 : Blo 599292 601683 := bstep (se 1 (by rfl) ⟨451262, by rfl⟩ : syracuseStep 601683 = 902525) B902525
theorem B601699 : Blo 599292 601699 := bstep (se 1 (by rfl) ⟨451274, by rfl⟩ : syracuseStep 601699 = 902549) B902549
theorem B1355363 : Blo 599292 1355363 := bstep (se 1 (by rfl) ⟨1016522, by rfl⟩ : syracuseStep 1355363 = 2033045) B2033045
theorem B601715 : Blo 599292 601715 := bstep (se 1 (by rfl) ⟨451286, by rfl⟩ : syracuseStep 601715 = 902573) B902573
theorem B601731 : Blo 599292 601731 := bstep (se 1 (by rfl) ⟨451298, by rfl⟩ : syracuseStep 601731 = 902597) B902597
theorem B601747 : Blo 599292 601747 := bstep (se 1 (by rfl) ⟨451310, by rfl⟩ : syracuseStep 601747 = 902621) B902621
theorem B601763 : Blo 599292 601763 := bstep (se 1 (by rfl) ⟨451322, by rfl⟩ : syracuseStep 601763 = 902645) B902645
theorem B601779 : Blo 599292 601779 := bstep (se 1 (by rfl) ⟨451334, by rfl⟩ : syracuseStep 601779 = 902669) B902669
theorem B601795 : Blo 599292 601795 := bstep (se 1 (by rfl) ⟨451346, by rfl⟩ : syracuseStep 601795 = 902693) B902693
theorem B601811 : Blo 599292 601811 := bstep (se 1 (by rfl) ⟨451358, by rfl⟩ : syracuseStep 601811 = 902717) B902717
theorem B601827 : Blo 599292 601827 := bstep (se 1 (by rfl) ⟨451370, by rfl⟩ : syracuseStep 601827 = 902741) B902741
theorem B1650403 : Blo 599292 1650403 := bstep (se 1 (by rfl) ⟨1237802, by rfl⟩ : syracuseStep 1650403 = 2475605) B2475605
theorem B601843 : Blo 599292 601843 := bstep (se 1 (by rfl) ⟨451382, by rfl⟩ : syracuseStep 601843 = 902765) B902765
theorem B601859 : Blo 599292 601859 := bstep (se 1 (by rfl) ⟨451394, by rfl⟩ : syracuseStep 601859 = 902789) B902789
theorem B601875 : Blo 599292 601875 := bstep (se 1 (by rfl) ⟨451406, by rfl⟩ : syracuseStep 601875 = 902813) B902813
theorem B601891 : Blo 599292 601891 := bstep (se 1 (by rfl) ⟨451418, by rfl⟩ : syracuseStep 601891 = 902837) B902837
theorem B601907 : Blo 599292 601907 := bstep (se 1 (by rfl) ⟨451430, by rfl⟩ : syracuseStep 601907 = 902861) B902861
theorem B601923 : Blo 599292 601923 := bstep (se 1 (by rfl) ⟨451442, by rfl⟩ : syracuseStep 601923 = 902885) B902885
theorem B601939 : Blo 599292 601939 := bstep (se 1 (by rfl) ⟨451454, by rfl⟩ : syracuseStep 601939 = 902909) B902909
theorem B601955 : Blo 599292 601955 := bstep (se 1 (by rfl) ⟨451466, by rfl⟩ : syracuseStep 601955 = 902933) B902933
theorem B6500209 : Blo 599292 6500209 := bstep (se 2 (by rfl) ⟨2437578, by rfl⟩ : syracuseStep 6500209 = 4875157) B4875157
theorem B1355633 : Blo 599292 1355633 := bstep (se 2 (by rfl) ⟨508362, by rfl⟩ : syracuseStep 1355633 = 1016725) B1016725
theorem B601971 : Blo 599292 601971 := bstep (se 1 (by rfl) ⟨451478, by rfl⟩ : syracuseStep 601971 = 902957) B902957
theorem B601987 : Blo 599292 601987 := bstep (se 1 (by rfl) ⟨451490, by rfl⟩ : syracuseStep 601987 = 902981) B902981
theorem B1355651 : Blo 599292 1355651 := bstep (se 1 (by rfl) ⟨1016738, by rfl⟩ : syracuseStep 1355651 = 2033477) B2033477
theorem B602003 : Blo 599292 602003 := bstep (se 1 (by rfl) ⟨451502, by rfl⟩ : syracuseStep 602003 = 903005) B903005
theorem B602019 : Blo 599292 602019 := bstep (se 1 (by rfl) ⟨451514, by rfl⟩ : syracuseStep 602019 = 903029) B903029
theorem B602035 : Blo 599292 602035 := bstep (se 1 (by rfl) ⟨451526, by rfl⟩ : syracuseStep 602035 = 903053) B903053
theorem B602051 : Blo 599292 602051 := bstep (se 1 (by rfl) ⟨451538, by rfl⟩ : syracuseStep 602051 = 903077) B903077
theorem B2600909 : Blo 599292 2600909 := bstep (se 3 (by rfl) ⟨487670, by rfl⟩ : syracuseStep 2600909 = 975341) B975341
theorem B602067 : Blo 599292 602067 := bstep (se 1 (by rfl) ⟨451550, by rfl⟩ : syracuseStep 602067 = 903101) B903101
theorem B602083 : Blo 599292 602083 := bstep (se 1 (by rfl) ⟨451562, by rfl⟩ : syracuseStep 602083 = 903125) B903125
theorem B602099 : Blo 599292 602099 := bstep (se 1 (by rfl) ⟨451574, by rfl⟩ : syracuseStep 602099 = 903149) B903149
theorem B602115 : Blo 599292 602115 := bstep (se 1 (by rfl) ⟨451586, by rfl⟩ : syracuseStep 602115 = 903173) B903173
theorem B602131 : Blo 599292 602131 := bstep (se 1 (by rfl) ⟨451598, by rfl⟩ : syracuseStep 602131 = 903197) B903197
theorem B602147 : Blo 599292 602147 := bstep (se 1 (by rfl) ⟨451610, by rfl⟩ : syracuseStep 602147 = 903221) B903221
theorem B602163 : Blo 599292 602163 := bstep (se 1 (by rfl) ⟨451622, by rfl⟩ : syracuseStep 602163 = 903245) B903245
theorem B602179 : Blo 599292 602179 := bstep (se 1 (by rfl) ⟨451634, by rfl⟩ : syracuseStep 602179 = 903269) B903269
theorem B602195 : Blo 599292 602195 := bstep (se 1 (by rfl) ⟨451646, by rfl⟩ : syracuseStep 602195 = 903293) B903293
theorem B602211 : Blo 599292 602211 := bstep (se 1 (by rfl) ⟨451658, by rfl⟩ : syracuseStep 602211 = 903317) B903317
theorem B3092579 : Blo 599292 3092579 := bstep (se 1 (by rfl) ⟨2319434, by rfl⟩ : syracuseStep 3092579 = 4638869) B4638869
theorem B602227 : Blo 599292 602227 := bstep (se 1 (by rfl) ⟨451670, by rfl⟩ : syracuseStep 602227 = 903341) B903341
theorem B602243 : Blo 599292 602243 := bstep (se 1 (by rfl) ⟨451682, by rfl⟩ : syracuseStep 602243 = 903365) B903365
theorem B1355921 : Blo 599292 1355921 := bstep (se 2 (by rfl) ⟨508470, by rfl⟩ : syracuseStep 1355921 = 1016941) B1016941
theorem B602259 : Blo 599292 602259 := bstep (se 1 (by rfl) ⟨451694, by rfl⟩ : syracuseStep 602259 = 903389) B903389
theorem B602275 : Blo 599292 602275 := bstep (se 1 (by rfl) ⟨451706, by rfl⟩ : syracuseStep 602275 = 903413) B903413
theorem B1355939 : Blo 599292 1355939 := bstep (se 1 (by rfl) ⟨1016954, by rfl⟩ : syracuseStep 1355939 = 2033909) B2033909
theorem B1519793 : Blo 599292 1519793 := bstep (se 2 (by rfl) ⟨569922, by rfl⟩ : syracuseStep 1519793 = 1139845) B1139845
theorem B602291 : Blo 599292 602291 := bstep (se 1 (by rfl) ⟨451718, by rfl⟩ : syracuseStep 602291 = 903437) B903437
theorem B602307 : Blo 599292 602307 := bstep (se 1 (by rfl) ⟨451730, by rfl⟩ : syracuseStep 602307 = 903461) B903461
theorem B602323 : Blo 599292 602323 := bstep (se 1 (by rfl) ⟨451742, by rfl⟩ : syracuseStep 602323 = 903485) B903485
theorem B1519843 : Blo 599292 1519843 := bstep (se 1 (by rfl) ⟨1139882, by rfl⟩ : syracuseStep 1519843 = 2279765) B2279765
theorem B602339 : Blo 599292 602339 := bstep (se 1 (by rfl) ⟨451754, by rfl⟩ : syracuseStep 602339 = 903509) B903509
theorem B602355 : Blo 599292 602355 := bstep (se 1 (by rfl) ⟨451766, by rfl⟩ : syracuseStep 602355 = 903533) B903533
theorem B602371 : Blo 599292 602371 := bstep (se 1 (by rfl) ⟨451778, by rfl⟩ : syracuseStep 602371 = 903557) B903557
theorem B1028369 : Blo 599292 1028369 := bstep (se 2 (by rfl) ⟨385638, by rfl⟩ : syracuseStep 1028369 = 771277) B771277
theorem B602387 : Blo 599292 602387 := bstep (se 1 (by rfl) ⟨451790, by rfl⟩ : syracuseStep 602387 = 903581) B903581
theorem B602403 : Blo 599292 602403 := bstep (se 1 (by rfl) ⟨451802, by rfl⟩ : syracuseStep 602403 = 903605) B903605
theorem B602419 : Blo 599292 602419 := bstep (se 1 (by rfl) ⟨451814, by rfl⟩ : syracuseStep 602419 = 903629) B903629
theorem B602435 : Blo 599292 602435 := bstep (se 1 (by rfl) ⟨451826, by rfl⟩ : syracuseStep 602435 = 903653) B903653
theorem B602451 : Blo 599292 602451 := bstep (se 1 (by rfl) ⟨451838, by rfl⟩ : syracuseStep 602451 = 903677) B903677
theorem B1651043 : Blo 599292 1651043 := bstep (se 1 (by rfl) ⟨1238282, by rfl⟩ : syracuseStep 1651043 = 2476565) B2476565
theorem B602467 : Blo 599292 602467 := bstep (se 1 (by rfl) ⟨451850, by rfl⟩ : syracuseStep 602467 = 903701) B903701
theorem B1519985 : Blo 599292 1519985 := bstep (se 2 (by rfl) ⟨569994, by rfl⟩ : syracuseStep 1519985 = 1139989) B1139989
theorem B602483 : Blo 599292 602483 := bstep (se 1 (by rfl) ⟨451862, by rfl⟩ : syracuseStep 602483 = 903725) B903725
theorem B602499 : Blo 599292 602499 := bstep (se 1 (by rfl) ⟨451874, by rfl⟩ : syracuseStep 602499 = 903749) B903749
theorem B602515 : Blo 599292 602515 := bstep (se 1 (by rfl) ⟨451886, by rfl⟩ : syracuseStep 602515 = 903773) B903773
theorem B602531 : Blo 599292 602531 := bstep (se 1 (by rfl) ⟨451898, by rfl⟩ : syracuseStep 602531 = 903797) B903797
theorem B1356209 : Blo 599292 1356209 := bstep (se 2 (by rfl) ⟨508578, by rfl⟩ : syracuseStep 1356209 = 1017157) B1017157
theorem B602547 : Blo 599292 602547 := bstep (se 1 (by rfl) ⟨451910, by rfl⟩ : syracuseStep 602547 = 903821) B903821
theorem B602563 : Blo 599292 602563 := bstep (se 1 (by rfl) ⟨451922, by rfl⟩ : syracuseStep 602563 = 903845) B903845
theorem B1356227 : Blo 599292 1356227 := bstep (se 1 (by rfl) ⟨1017170, by rfl⟩ : syracuseStep 1356227 = 2034341) B2034341
theorem B602579 : Blo 599292 602579 := bstep (se 1 (by rfl) ⟨451934, by rfl⟩ : syracuseStep 602579 = 903869) B903869
theorem B602595 : Blo 599292 602595 := bstep (se 1 (by rfl) ⟨451946, by rfl⟩ : syracuseStep 602595 = 903893) B903893
theorem B602611 : Blo 599292 602611 := bstep (se 1 (by rfl) ⟨451958, by rfl⟩ : syracuseStep 602611 = 903917) B903917
theorem B602627 : Blo 599292 602627 := bstep (se 1 (by rfl) ⟨451970, by rfl⟩ : syracuseStep 602627 = 903941) B903941
theorem B602643 : Blo 599292 602643 := bstep (se 1 (by rfl) ⟨451982, by rfl⟩ : syracuseStep 602643 = 903965) B903965
theorem B602659 : Blo 599292 602659 := bstep (se 1 (by rfl) ⟨451994, by rfl⟩ : syracuseStep 602659 = 903989) B903989
theorem B1716785 : Blo 599292 1716785 := bstep (se 2 (by rfl) ⟨643794, by rfl⟩ : syracuseStep 1716785 = 1287589) B1287589
theorem B602675 : Blo 599292 602675 := bstep (se 1 (by rfl) ⟨452006, by rfl⟩ : syracuseStep 602675 = 904013) B904013
theorem B602691 : Blo 599292 602691 := bstep (se 1 (by rfl) ⟨452018, by rfl⟩ : syracuseStep 602691 = 904037) B904037
theorem B602707 : Blo 599292 602707 := bstep (se 1 (by rfl) ⟨452030, by rfl⟩ : syracuseStep 602707 = 904061) B904061
theorem B602723 : Blo 599292 602723 := bstep (se 1 (by rfl) ⟨452042, by rfl⟩ : syracuseStep 602723 = 904085) B904085
theorem B602739 : Blo 599292 602739 := bstep (se 1 (by rfl) ⟨452054, by rfl⟩ : syracuseStep 602739 = 904109) B904109
theorem B602755 : Blo 599292 602755 := bstep (se 1 (by rfl) ⟨452066, by rfl⟩ : syracuseStep 602755 = 904133) B904133
theorem B3846797 : Blo 599292 3846797 := bstep (se 3 (by rfl) ⟨721274, by rfl⟩ : syracuseStep 3846797 = 1442549) B1442549
theorem B602771 : Blo 599292 602771 := bstep (se 1 (by rfl) ⟨452078, by rfl⟩ : syracuseStep 602771 = 904157) B904157
theorem B602787 : Blo 599292 602787 := bstep (se 1 (by rfl) ⟨452090, by rfl⟩ : syracuseStep 602787 = 904181) B904181
theorem B602803 : Blo 599292 602803 := bstep (se 1 (by rfl) ⟨452102, by rfl⟩ : syracuseStep 602803 = 904205) B904205
theorem B602819 : Blo 599292 602819 := bstep (se 1 (by rfl) ⟨452114, by rfl⟩ : syracuseStep 602819 = 904229) B904229
theorem B1356497 : Blo 599292 1356497 := bstep (se 2 (by rfl) ⟨508686, by rfl⟩ : syracuseStep 1356497 = 1017373) B1017373
theorem B602835 : Blo 599292 602835 := bstep (se 1 (by rfl) ⟨452126, by rfl⟩ : syracuseStep 602835 = 904253) B904253
theorem B602851 : Blo 599292 602851 := bstep (se 1 (by rfl) ⟨452138, by rfl⟩ : syracuseStep 602851 = 904277) B904277
theorem B1356515 : Blo 599292 1356515 := bstep (se 1 (by rfl) ⟨1017386, by rfl⟩ : syracuseStep 1356515 = 2034773) B2034773
theorem B1716977 : Blo 599292 1716977 := bstep (se 2 (by rfl) ⟨643866, by rfl⟩ : syracuseStep 1716977 = 1287733) B1287733
theorem B602867 : Blo 599292 602867 := bstep (se 1 (by rfl) ⟨452150, by rfl⟩ : syracuseStep 602867 = 904301) B904301
theorem B602883 : Blo 599292 602883 := bstep (se 1 (by rfl) ⟨452162, by rfl⟩ : syracuseStep 602883 = 904325) B904325
theorem B602899 : Blo 599292 602899 := bstep (se 1 (by rfl) ⟨452174, by rfl⟩ : syracuseStep 602899 = 904349) B904349
theorem B602915 : Blo 599292 602915 := bstep (se 1 (by rfl) ⟨452186, by rfl⟩ : syracuseStep 602915 = 904373) B904373
theorem B2437937 : Blo 599292 2437937 := bstep (se 2 (by rfl) ⟨914226, by rfl⟩ : syracuseStep 2437937 = 1828453) B1828453
theorem B602931 : Blo 599292 602931 := bstep (se 1 (by rfl) ⟨452198, by rfl⟩ : syracuseStep 602931 = 904397) B904397
theorem B602947 : Blo 599292 602947 := bstep (se 1 (by rfl) ⟨452210, by rfl⟩ : syracuseStep 602947 = 904421) B904421
theorem B602963 : Blo 599292 602963 := bstep (se 1 (by rfl) ⟨452222, by rfl⟩ : syracuseStep 602963 = 904445) B904445
theorem B602979 : Blo 599292 602979 := bstep (se 1 (by rfl) ⟨452234, by rfl⟩ : syracuseStep 602979 = 904469) B904469
theorem B602995 : Blo 599292 602995 := bstep (se 1 (by rfl) ⟨452246, by rfl⟩ : syracuseStep 602995 = 904493) B904493
theorem B603011 : Blo 599292 603011 := bstep (se 1 (by rfl) ⟨452258, by rfl⟩ : syracuseStep 603011 = 904517) B904517
theorem B3421061 : Blo 599292 3421061 := bstep (se 4 (by rfl) ⟨320724, by rfl⟩ : syracuseStep 3421061 = 641449) B641449
theorem B4109197 : Blo 599292 4109197 := bstep (se 3 (by rfl) ⟨770474, by rfl⟩ : syracuseStep 4109197 = 1540949) B1540949
theorem B603027 : Blo 599292 603027 := bstep (se 1 (by rfl) ⟨452270, by rfl⟩ : syracuseStep 603027 = 904541) B904541
theorem B603043 : Blo 599292 603043 := bstep (se 1 (by rfl) ⟨452282, by rfl⟩ : syracuseStep 603043 = 904565) B904565
theorem B603059 : Blo 599292 603059 := bstep (se 1 (by rfl) ⟨452294, by rfl⟩ : syracuseStep 603059 = 904589) B904589
theorem B603075 : Blo 599292 603075 := bstep (se 1 (by rfl) ⟨452306, by rfl⟩ : syracuseStep 603075 = 904613) B904613
theorem B603091 : Blo 599292 603091 := bstep (se 1 (by rfl) ⟨452318, by rfl⟩ : syracuseStep 603091 = 904637) B904637
theorem B603107 : Blo 599292 603107 := bstep (se 1 (by rfl) ⟨452330, by rfl⟩ : syracuseStep 603107 = 904661) B904661
theorem B1356785 : Blo 599292 1356785 := bstep (se 2 (by rfl) ⟨508794, by rfl⟩ : syracuseStep 1356785 = 1017589) B1017589
theorem B963571 : Blo 599292 963571 := bstep (se 1 (by rfl) ⟨722678, by rfl⟩ : syracuseStep 963571 = 1445357) B1445357
theorem B603123 : Blo 599292 603123 := bstep (se 1 (by rfl) ⟨452342, by rfl⟩ : syracuseStep 603123 = 904685) B904685
theorem B1356803 : Blo 599292 1356803 := bstep (se 1 (by rfl) ⟨1017602, by rfl⟩ : syracuseStep 1356803 = 2035205) B2035205
theorem B603139 : Blo 599292 603139 := bstep (se 1 (by rfl) ⟨452354, by rfl⟩ : syracuseStep 603139 = 904709) B904709
theorem B603155 : Blo 599292 603155 := bstep (se 1 (by rfl) ⟨452366, by rfl⟩ : syracuseStep 603155 = 904733) B904733
theorem B603171 : Blo 599292 603171 := bstep (se 1 (by rfl) ⟨452378, by rfl⟩ : syracuseStep 603171 = 904757) B904757
theorem B603187 : Blo 599292 603187 := bstep (se 1 (by rfl) ⟨452390, by rfl⟩ : syracuseStep 603187 = 904781) B904781
theorem B603203 : Blo 599292 603203 := bstep (se 1 (by rfl) ⟨452402, by rfl⟩ : syracuseStep 603203 = 904805) B904805
theorem B603219 : Blo 599292 603219 := bstep (se 1 (by rfl) ⟨452414, by rfl⟩ : syracuseStep 603219 = 904829) B904829
theorem B2569315 : Blo 599292 2569315 := bstep (se 1 (by rfl) ⟨1926986, by rfl⟩ : syracuseStep 2569315 = 3853973) B3853973
theorem B603235 : Blo 599292 603235 := bstep (se 1 (by rfl) ⟨452426, by rfl⟩ : syracuseStep 603235 = 904853) B904853
theorem B603251 : Blo 599292 603251 := bstep (se 1 (by rfl) ⟨452438, by rfl⟩ : syracuseStep 603251 = 904877) B904877
theorem B603267 : Blo 599292 603267 := bstep (se 1 (by rfl) ⟨452450, by rfl⟩ : syracuseStep 603267 = 904901) B904901
theorem B603283 : Blo 599292 603283 := bstep (se 1 (by rfl) ⟨452462, by rfl⟩ : syracuseStep 603283 = 904925) B904925
theorem B963827 : Blo 599292 963827 := bstep (se 1 (by rfl) ⟨722870, by rfl⟩ : syracuseStep 963827 = 1445741) B1445741
theorem B1357073 : Blo 599292 1357073 := bstep (se 2 (by rfl) ⟨508902, by rfl⟩ : syracuseStep 1357073 = 1017805) B1017805
theorem B1357091 : Blo 599292 1357091 := bstep (se 1 (by rfl) ⟨1017818, by rfl⟩ : syracuseStep 1357091 = 2035637) B2035637
theorem B1520977 : Blo 599292 1520977 := bstep (se 2 (by rfl) ⟨570366, by rfl⟩ : syracuseStep 1520977 = 1140733) B1140733
theorem B964019 : Blo 599292 964019 := bstep (se 1 (by rfl) ⟨723014, by rfl⟩ : syracuseStep 964019 = 1446029) B1446029
theorem B1357361 : Blo 599292 1357361 := bstep (se 2 (by rfl) ⟨509010, by rfl⟩ : syracuseStep 1357361 = 1018021) B1018021
theorem B1357379 : Blo 599292 1357379 := bstep (se 1 (by rfl) ⟨1018034, by rfl⟩ : syracuseStep 1357379 = 2036069) B2036069
theorem B1521251 : Blo 599292 1521251 := bstep (se 1 (by rfl) ⟨1140938, by rfl⟩ : syracuseStep 1521251 = 2281877) B2281877
theorem B1717969 : Blo 599292 1717969 := bstep (se 2 (by rfl) ⟨644238, by rfl⟩ : syracuseStep 1717969 = 1288477) B1288477
theorem B6502157 : Blo 599292 6502157 := bstep (se 3 (by rfl) ⟨1219154, by rfl⟩ : syracuseStep 6502157 = 2438309) B2438309
theorem B1521443 : Blo 599292 1521443 := bstep (se 1 (by rfl) ⟨1141082, by rfl⟩ : syracuseStep 1521443 = 2282165) B2282165
theorem B898961 : Blo 599292 898961 := bstep (se 2 (by rfl) ⟨337110, by rfl⟩ : syracuseStep 898961 = 674221) B674221
theorem B898979 : Blo 599292 898979 := bstep (se 1 (by rfl) ⟨674234, by rfl⟩ : syracuseStep 898979 = 1348469) B1348469
theorem B899009 : Blo 599292 899009 := bstep (se 2 (by rfl) ⟨337128, by rfl⟩ : syracuseStep 899009 = 674257) B674257
theorem B899027 : Blo 599292 899027 := bstep (se 1 (by rfl) ⟨674270, by rfl⟩ : syracuseStep 899027 = 1348541) B1348541
theorem B899057 : Blo 599292 899057 := bstep (se 2 (by rfl) ⟨337146, by rfl⟩ : syracuseStep 899057 = 674293) B674293
theorem B899075 : Blo 599292 899075 := bstep (se 1 (by rfl) ⟨674306, by rfl⟩ : syracuseStep 899075 = 1348613) B1348613
theorem B899105 : Blo 599292 899105 := bstep (se 2 (by rfl) ⟨337164, by rfl⟩ : syracuseStep 899105 = 674329) B674329
theorem B899123 : Blo 599292 899123 := bstep (se 1 (by rfl) ⟨674342, by rfl⟩ : syracuseStep 899123 = 1348685) B1348685
theorem B899153 : Blo 599292 899153 := bstep (se 2 (by rfl) ⟨337182, by rfl⟩ : syracuseStep 899153 = 674365) B674365
theorem B899171 : Blo 599292 899171 := bstep (se 1 (by rfl) ⟨674378, by rfl⟩ : syracuseStep 899171 = 1348757) B1348757
theorem B899201 : Blo 599292 899201 := bstep (se 2 (by rfl) ⟨337200, by rfl⟩ : syracuseStep 899201 = 674401) B674401
theorem B899219 : Blo 599292 899219 := bstep (se 1 (by rfl) ⟨674414, by rfl⟩ : syracuseStep 899219 = 1348829) B1348829
theorem B899249 : Blo 599292 899249 := bstep (se 2 (by rfl) ⟨337218, by rfl⟩ : syracuseStep 899249 = 674437) B674437
theorem B964801 : Blo 599292 964801 := bstep (se 2 (by rfl) ⟨361800, by rfl⟩ : syracuseStep 964801 = 723601) B723601
theorem B899267 : Blo 599292 899267 := bstep (se 1 (by rfl) ⟨674450, by rfl⟩ : syracuseStep 899267 = 1348901) B1348901
theorem B899297 : Blo 599292 899297 := bstep (se 2 (by rfl) ⟨337236, by rfl⟩ : syracuseStep 899297 = 674473) B674473
theorem B1620209 : Blo 599292 1620209 := bstep (se 2 (by rfl) ⟨607578, by rfl⟩ : syracuseStep 1620209 = 1215157) B1215157
theorem B899315 : Blo 599292 899315 := bstep (se 1 (by rfl) ⟨674486, by rfl⟩ : syracuseStep 899315 = 1348973) B1348973
theorem B899345 : Blo 599292 899345 := bstep (se 2 (by rfl) ⟨337254, by rfl⟩ : syracuseStep 899345 = 674509) B674509
theorem B899363 : Blo 599292 899363 := bstep (se 1 (by rfl) ⟨674522, by rfl⟩ : syracuseStep 899363 = 1349045) B1349045
theorem B2570545 : Blo 599292 2570545 := bstep (se 2 (by rfl) ⟨963954, by rfl⟩ : syracuseStep 2570545 = 1927909) B1927909
theorem B899393 : Blo 599292 899393 := bstep (se 2 (by rfl) ⟨337272, by rfl⟩ : syracuseStep 899393 = 674545) B674545
theorem B899411 : Blo 599292 899411 := bstep (se 1 (by rfl) ⟨674558, by rfl⟩ : syracuseStep 899411 = 1349117) B1349117
theorem B899441 : Blo 599292 899441 := bstep (se 2 (by rfl) ⟨337290, by rfl⟩ : syracuseStep 899441 = 674581) B674581
theorem B899459 : Blo 599292 899459 := bstep (se 1 (by rfl) ⟨674594, by rfl⟩ : syracuseStep 899459 = 1349189) B1349189
theorem B899489 : Blo 599292 899489 := bstep (se 2 (by rfl) ⟨337308, by rfl⟩ : syracuseStep 899489 = 674617) B674617
theorem B899507 : Blo 599292 899507 := bstep (se 1 (by rfl) ⟨674630, by rfl⟩ : syracuseStep 899507 = 1349261) B1349261
theorem B899537 : Blo 599292 899537 := bstep (se 2 (by rfl) ⟨337326, by rfl⟩ : syracuseStep 899537 = 674653) B674653
theorem B899555 : Blo 599292 899555 := bstep (se 1 (by rfl) ⟨674666, by rfl⟩ : syracuseStep 899555 = 1349333) B1349333
theorem B899585 : Blo 599292 899585 := bstep (se 2 (by rfl) ⟨337344, by rfl⟩ : syracuseStep 899585 = 674689) B674689
theorem B899603 : Blo 599292 899603 := bstep (se 1 (by rfl) ⟨674702, by rfl⟩ : syracuseStep 899603 = 1349405) B1349405
theorem B899633 : Blo 599292 899633 := bstep (se 2 (by rfl) ⟨337362, by rfl⟩ : syracuseStep 899633 = 674725) B674725
theorem B899651 : Blo 599292 899651 := bstep (se 1 (by rfl) ⟨674738, by rfl⟩ : syracuseStep 899651 = 1349477) B1349477
theorem B1620557 : Blo 599292 1620557 := bstep (se 3 (by rfl) ⟨303854, by rfl⟩ : syracuseStep 1620557 = 607709) B607709
theorem B899681 : Blo 599292 899681 := bstep (se 2 (by rfl) ⟨337380, by rfl⟩ : syracuseStep 899681 = 674761) B674761
theorem B899699 : Blo 599292 899699 := bstep (se 1 (by rfl) ⟨674774, by rfl⟩ : syracuseStep 899699 = 1349549) B1349549
theorem B899729 : Blo 599292 899729 := bstep (se 2 (by rfl) ⟨337398, by rfl⟩ : syracuseStep 899729 = 674797) B674797
theorem B899747 : Blo 599292 899747 := bstep (se 1 (by rfl) ⟨674810, by rfl⟩ : syracuseStep 899747 = 1349621) B1349621
theorem B899777 : Blo 599292 899777 := bstep (se 2 (by rfl) ⟨337416, by rfl⟩ : syracuseStep 899777 = 674833) B674833
theorem B2276045 : Blo 599292 2276045 := bstep (se 3 (by rfl) ⟨426758, by rfl⟩ : syracuseStep 2276045 = 853517) B853517
theorem B1522385 : Blo 599292 1522385 := bstep (se 2 (by rfl) ⟨570894, by rfl⟩ : syracuseStep 1522385 = 1141789) B1141789
theorem B899795 : Blo 599292 899795 := bstep (se 1 (by rfl) ⟨674846, by rfl⟩ : syracuseStep 899795 = 1349693) B1349693
theorem B899825 : Blo 599292 899825 := bstep (se 2 (by rfl) ⟨337434, by rfl⟩ : syracuseStep 899825 = 674869) B674869
theorem B899843 : Blo 599292 899843 := bstep (se 1 (by rfl) ⟨674882, by rfl⟩ : syracuseStep 899843 = 1349765) B1349765
theorem B1522435 : Blo 599292 1522435 := bstep (se 1 (by rfl) ⟨1141826, by rfl⟩ : syracuseStep 1522435 = 2283653) B2283653
theorem B899873 : Blo 599292 899873 := bstep (se 2 (by rfl) ⟨337452, by rfl⟩ : syracuseStep 899873 = 674905) B674905
theorem B899891 : Blo 599292 899891 := bstep (se 1 (by rfl) ⟨674918, by rfl⟩ : syracuseStep 899891 = 1349837) B1349837
theorem B3849029 : Blo 599292 3849029 := bstep (se 4 (by rfl) ⟨360846, by rfl⟩ : syracuseStep 3849029 = 721693) B721693
theorem B899921 : Blo 599292 899921 := bstep (se 2 (by rfl) ⟨337470, by rfl⟩ : syracuseStep 899921 = 674941) B674941
theorem B899939 : Blo 599292 899939 := bstep (se 1 (by rfl) ⟨674954, by rfl⟩ : syracuseStep 899939 = 1349909) B1349909
theorem B899969 : Blo 599292 899969 := bstep (se 2 (by rfl) ⟨337488, by rfl⟩ : syracuseStep 899969 = 674977) B674977
theorem B1522577 : Blo 599292 1522577 := bstep (se 2 (by rfl) ⟨570966, by rfl⟩ : syracuseStep 1522577 = 1141933) B1141933
theorem B899987 : Blo 599292 899987 := bstep (se 1 (by rfl) ⟨674990, by rfl⟩ : syracuseStep 899987 = 1349981) B1349981
theorem B900017 : Blo 599292 900017 := bstep (se 2 (by rfl) ⟨337506, by rfl⟩ : syracuseStep 900017 = 675013) B675013
theorem B900035 : Blo 599292 900035 := bstep (se 1 (by rfl) ⟨675026, by rfl⟩ : syracuseStep 900035 = 1350053) B1350053
theorem B900065 : Blo 599292 900065 := bstep (se 2 (by rfl) ⟨337524, by rfl⟩ : syracuseStep 900065 = 675049) B675049
theorem B900083 : Blo 599292 900083 := bstep (se 1 (by rfl) ⟨675062, by rfl⟩ : syracuseStep 900083 = 1350125) B1350125
theorem B900113 : Blo 599292 900113 := bstep (se 2 (by rfl) ⟨337542, by rfl⟩ : syracuseStep 900113 = 675085) B675085
theorem B900131 : Blo 599292 900131 := bstep (se 1 (by rfl) ⟨675098, by rfl⟩ : syracuseStep 900131 = 1350197) B1350197
theorem B900161 : Blo 599292 900161 := bstep (se 2 (by rfl) ⟨337560, by rfl⟩ : syracuseStep 900161 = 675121) B675121
theorem B1850435 : Blo 599292 1850435 := bstep (se 1 (by rfl) ⟨1387826, by rfl⟩ : syracuseStep 1850435 = 2775653) B2775653
theorem B900179 : Blo 599292 900179 := bstep (se 1 (by rfl) ⟨675134, by rfl⟩ : syracuseStep 900179 = 1350269) B1350269
theorem B3914851 : Blo 599292 3914851 := bstep (se 1 (by rfl) ⟨2936138, by rfl⟩ : syracuseStep 3914851 = 5872277) B5872277
theorem B900209 : Blo 599292 900209 := bstep (se 2 (by rfl) ⟨337578, by rfl⟩ : syracuseStep 900209 = 675157) B675157
theorem B900227 : Blo 599292 900227 := bstep (se 1 (by rfl) ⟨675170, by rfl⟩ : syracuseStep 900227 = 1350341) B1350341
theorem B900257 : Blo 599292 900257 := bstep (se 2 (by rfl) ⟨337596, by rfl⟩ : syracuseStep 900257 = 675193) B675193
theorem B900275 : Blo 599292 900275 := bstep (se 1 (by rfl) ⟨675206, by rfl⟩ : syracuseStep 900275 = 1350413) B1350413
theorem B900305 : Blo 599292 900305 := bstep (se 2 (by rfl) ⟨337614, by rfl⟩ : syracuseStep 900305 = 675229) B675229
theorem B2079971 : Blo 599292 2079971 := bstep (se 1 (by rfl) ⟨1559978, by rfl⟩ : syracuseStep 2079971 = 3119957) B3119957
theorem B900323 : Blo 599292 900323 := bstep (se 1 (by rfl) ⟨675242, by rfl⟩ : syracuseStep 900323 = 1350485) B1350485
theorem B900353 : Blo 599292 900353 := bstep (se 2 (by rfl) ⟨337632, by rfl⟩ : syracuseStep 900353 = 675265) B675265
theorem B900371 : Blo 599292 900371 := bstep (se 1 (by rfl) ⟨675278, by rfl⟩ : syracuseStep 900371 = 1350557) B1350557
theorem B900401 : Blo 599292 900401 := bstep (se 2 (by rfl) ⟨337650, by rfl⟩ : syracuseStep 900401 = 675301) B675301
theorem B900419 : Blo 599292 900419 := bstep (se 1 (by rfl) ⟨675314, by rfl⟩ : syracuseStep 900419 = 1350629) B1350629
theorem B900449 : Blo 599292 900449 := bstep (se 2 (by rfl) ⟨337668, by rfl⟩ : syracuseStep 900449 = 675337) B675337
theorem B900467 : Blo 599292 900467 := bstep (se 1 (by rfl) ⟨675350, by rfl⟩ : syracuseStep 900467 = 1350701) B1350701
theorem B900497 : Blo 599292 900497 := bstep (se 2 (by rfl) ⟨337686, by rfl⟩ : syracuseStep 900497 = 675373) B675373
theorem B900515 : Blo 599292 900515 := bstep (se 1 (by rfl) ⟨675386, by rfl⟩ : syracuseStep 900515 = 1350773) B1350773
theorem B1588643 : Blo 599292 1588643 := bstep (se 1 (by rfl) ⟨1191482, by rfl⟩ : syracuseStep 1588643 = 2382965) B2382965
theorem B900545 : Blo 599292 900545 := bstep (se 2 (by rfl) ⟨337704, by rfl⟩ : syracuseStep 900545 = 675409) B675409
theorem B900563 : Blo 599292 900563 := bstep (se 1 (by rfl) ⟨675422, by rfl⟩ : syracuseStep 900563 = 1350845) B1350845
theorem B2276849 : Blo 599292 2276849 := bstep (se 2 (by rfl) ⟨853818, by rfl⟩ : syracuseStep 2276849 = 1707637) B1707637
theorem B900593 : Blo 599292 900593 := bstep (se 2 (by rfl) ⟨337722, by rfl⟩ : syracuseStep 900593 = 675445) B675445
theorem B1883633 : Blo 599292 1883633 := bstep (se 2 (by rfl) ⟨706362, by rfl⟩ : syracuseStep 1883633 = 1412725) B1412725
theorem B900611 : Blo 599292 900611 := bstep (se 1 (by rfl) ⟨675458, by rfl⟩ : syracuseStep 900611 = 1350917) B1350917
theorem B900641 : Blo 599292 900641 := bstep (se 2 (by rfl) ⟨337740, by rfl⟩ : syracuseStep 900641 = 675481) B675481
theorem B900659 : Blo 599292 900659 := bstep (se 1 (by rfl) ⟨675494, by rfl⟩ : syracuseStep 900659 = 1350989) B1350989
theorem B900689 : Blo 599292 900689 := bstep (se 2 (by rfl) ⟨337758, by rfl⟩ : syracuseStep 900689 = 675517) B675517
theorem B900707 : Blo 599292 900707 := bstep (se 1 (by rfl) ⟨675530, by rfl⟩ : syracuseStep 900707 = 1351061) B1351061
theorem B900737 : Blo 599292 900737 := bstep (se 2 (by rfl) ⟨337776, by rfl⟩ : syracuseStep 900737 = 675553) B675553
theorem B900755 : Blo 599292 900755 := bstep (se 1 (by rfl) ⟨675566, by rfl⟩ : syracuseStep 900755 = 1351133) B1351133
theorem B900785 : Blo 599292 900785 := bstep (se 2 (by rfl) ⟨337794, by rfl⟩ : syracuseStep 900785 = 675589) B675589
theorem B900803 : Blo 599292 900803 := bstep (se 1 (by rfl) ⟨675602, by rfl⟩ : syracuseStep 900803 = 1351205) B1351205
theorem B900833 : Blo 599292 900833 := bstep (se 2 (by rfl) ⟨337812, by rfl⟩ : syracuseStep 900833 = 675625) B675625
theorem B1621745 : Blo 599292 1621745 := bstep (se 2 (by rfl) ⟨608154, by rfl⟩ : syracuseStep 1621745 = 1216309) B1216309
theorem B900851 : Blo 599292 900851 := bstep (se 1 (by rfl) ⟨675638, by rfl⟩ : syracuseStep 900851 = 1351277) B1351277
theorem B900881 : Blo 599292 900881 := bstep (se 2 (by rfl) ⟨337830, by rfl⟩ : syracuseStep 900881 = 675661) B675661
theorem B900899 : Blo 599292 900899 := bstep (se 1 (by rfl) ⟨675674, by rfl⟩ : syracuseStep 900899 = 1351349) B1351349
theorem B1392419 : Blo 599292 1392419 := bstep (se 1 (by rfl) ⟨1044314, by rfl⟩ : syracuseStep 1392419 = 2088629) B2088629
theorem B900929 : Blo 599292 900929 := bstep (se 2 (by rfl) ⟨337848, by rfl⟩ : syracuseStep 900929 = 675697) B675697
theorem B900947 : Blo 599292 900947 := bstep (se 1 (by rfl) ⟨675710, by rfl⟩ : syracuseStep 900947 = 1351421) B1351421
theorem B900977 : Blo 599292 900977 := bstep (se 2 (by rfl) ⟨337866, by rfl⟩ : syracuseStep 900977 = 675733) B675733
theorem B1523569 : Blo 599292 1523569 := bstep (se 2 (by rfl) ⟨571338, by rfl⟩ : syracuseStep 1523569 = 1142677) B1142677
theorem B900995 : Blo 599292 900995 := bstep (se 1 (by rfl) ⟨675746, by rfl⟩ : syracuseStep 900995 = 1351493) B1351493
theorem B901025 : Blo 599292 901025 := bstep (se 2 (by rfl) ⟨337884, by rfl⟩ : syracuseStep 901025 = 675769) B675769
theorem B901043 : Blo 599292 901043 := bstep (se 1 (by rfl) ⟨675782, by rfl⟩ : syracuseStep 901043 = 1351565) B1351565
theorem B901073 : Blo 599292 901073 := bstep (se 2 (by rfl) ⟨337902, by rfl⟩ : syracuseStep 901073 = 675805) B675805
theorem B901091 : Blo 599292 901091 := bstep (se 1 (by rfl) ⟨675818, by rfl⟩ : syracuseStep 901091 = 1351637) B1351637
theorem B901121 : Blo 599292 901121 := bstep (se 2 (by rfl) ⟨337920, by rfl⟩ : syracuseStep 901121 = 675841) B675841
theorem B901139 : Blo 599292 901139 := bstep (se 1 (by rfl) ⟨675854, by rfl⟩ : syracuseStep 901139 = 1351709) B1351709
theorem B901169 : Blo 599292 901169 := bstep (se 2 (by rfl) ⟨337938, by rfl⟩ : syracuseStep 901169 = 675877) B675877
theorem B901187 : Blo 599292 901187 := bstep (se 1 (by rfl) ⟨675890, by rfl⟩ : syracuseStep 901187 = 1351781) B1351781
theorem B901217 : Blo 599292 901217 := bstep (se 2 (by rfl) ⟨337956, by rfl⟩ : syracuseStep 901217 = 675913) B675913
theorem B901235 : Blo 599292 901235 := bstep (se 1 (by rfl) ⟨675926, by rfl⟩ : syracuseStep 901235 = 1351853) B1351853
theorem B1523843 : Blo 599292 1523843 := bstep (se 1 (by rfl) ⟨1142882, by rfl⟩ : syracuseStep 1523843 = 2285765) B2285765
theorem B2277517 : Blo 599292 2277517 := bstep (se 3 (by rfl) ⟨427034, by rfl⟩ : syracuseStep 2277517 = 854069) B854069
theorem B9748621 : Blo 599292 9748621 := bstep (se 3 (by rfl) ⟨1827866, by rfl⟩ : syracuseStep 9748621 = 3655733) B3655733
theorem B901265 : Blo 599292 901265 := bstep (se 2 (by rfl) ⟨337974, by rfl⟩ : syracuseStep 901265 = 675949) B675949
theorem B901283 : Blo 599292 901283 := bstep (se 1 (by rfl) ⟨675962, by rfl⟩ : syracuseStep 901283 = 1351925) B1351925
theorem B901313 : Blo 599292 901313 := bstep (se 2 (by rfl) ⟨337992, by rfl⟩ : syracuseStep 901313 = 675985) B675985
theorem B901331 : Blo 599292 901331 := bstep (se 1 (by rfl) ⟨675998, by rfl⟩ : syracuseStep 901331 = 1351997) B1351997
theorem B901361 : Blo 599292 901361 := bstep (se 2 (by rfl) ⟨338010, by rfl⟩ : syracuseStep 901361 = 676021) B676021
theorem B901379 : Blo 599292 901379 := bstep (se 1 (by rfl) ⟨676034, by rfl⟩ : syracuseStep 901379 = 1352069) B1352069
theorem B1622285 : Blo 599292 1622285 := bstep (se 3 (by rfl) ⟨304178, by rfl⟩ : syracuseStep 1622285 = 608357) B608357
theorem B901409 : Blo 599292 901409 := bstep (se 2 (by rfl) ⟨338028, by rfl⟩ : syracuseStep 901409 = 676057) B676057
theorem B901427 : Blo 599292 901427 := bstep (se 1 (by rfl) ⟨676070, by rfl⟩ : syracuseStep 901427 = 1352141) B1352141
theorem B1524035 : Blo 599292 1524035 := bstep (se 1 (by rfl) ⟨1143026, by rfl⟩ : syracuseStep 1524035 = 2286053) B2286053
theorem B901457 : Blo 599292 901457 := bstep (se 2 (by rfl) ⟨338046, by rfl⟩ : syracuseStep 901457 = 676093) B676093
theorem B901475 : Blo 599292 901475 := bstep (se 1 (by rfl) ⟨676106, by rfl⟩ : syracuseStep 901475 = 1352213) B1352213
theorem B901505 : Blo 599292 901505 := bstep (se 2 (by rfl) ⟨338064, by rfl⟩ : syracuseStep 901505 = 676129) B676129
theorem B901523 : Blo 599292 901523 := bstep (se 1 (by rfl) ⟨676142, by rfl⟩ : syracuseStep 901523 = 1352285) B1352285
theorem B1622435 : Blo 599292 1622435 := bstep (se 1 (by rfl) ⟨1216826, by rfl⟩ : syracuseStep 1622435 = 2433653) B2433653
theorem B901553 : Blo 599292 901553 := bstep (se 2 (by rfl) ⟨338082, by rfl⟩ : syracuseStep 901553 = 676165) B676165
theorem B901571 : Blo 599292 901571 := bstep (se 1 (by rfl) ⟨676178, by rfl⟩ : syracuseStep 901571 = 1352357) B1352357
theorem B901601 : Blo 599292 901601 := bstep (se 2 (by rfl) ⟨338100, by rfl⟩ : syracuseStep 901601 = 676201) B676201
theorem B901619 : Blo 599292 901619 := bstep (se 1 (by rfl) ⟨676214, by rfl⟩ : syracuseStep 901619 = 1352429) B1352429
theorem B901649 : Blo 599292 901649 := bstep (se 2 (by rfl) ⟨338118, by rfl⟩ : syracuseStep 901649 = 676237) B676237
theorem B3654179 : Blo 599292 3654179 := bstep (se 1 (by rfl) ⟨2740634, by rfl⟩ : syracuseStep 3654179 = 5481269) B5481269
theorem B901667 : Blo 599292 901667 := bstep (se 1 (by rfl) ⟨676250, by rfl⟩ : syracuseStep 901667 = 1352501) B1352501
theorem B901697 : Blo 599292 901697 := bstep (se 2 (by rfl) ⟨338136, by rfl⟩ : syracuseStep 901697 = 676273) B676273
theorem B901715 : Blo 599292 901715 := bstep (se 1 (by rfl) ⟨676286, by rfl⟩ : syracuseStep 901715 = 1352573) B1352573
theorem B901745 : Blo 599292 901745 := bstep (se 2 (by rfl) ⟨338154, by rfl⟩ : syracuseStep 901745 = 676309) B676309
theorem B901763 : Blo 599292 901763 := bstep (se 1 (by rfl) ⟨676322, by rfl⟩ : syracuseStep 901763 = 1352645) B1352645
theorem B901793 : Blo 599292 901793 := bstep (se 2 (by rfl) ⟨338172, by rfl⟩ : syracuseStep 901793 = 676345) B676345
theorem B2933425 : Blo 599292 2933425 := bstep (se 2 (by rfl) ⟨1100034, by rfl⟩ : syracuseStep 2933425 = 2200069) B2200069
theorem B901811 : Blo 599292 901811 := bstep (se 1 (by rfl) ⟨676358, by rfl⟩ : syracuseStep 901811 = 1352717) B1352717
theorem B901841 : Blo 599292 901841 := bstep (se 2 (by rfl) ⟨338190, by rfl⟩ : syracuseStep 901841 = 676381) B676381
theorem B7291619 : Blo 599292 7291619 := bstep (se 1 (by rfl) ⟨5468714, by rfl⟩ : syracuseStep 7291619 = 10937429) B10937429
theorem B901859 : Blo 599292 901859 := bstep (se 1 (by rfl) ⟨676394, by rfl⟩ : syracuseStep 901859 = 1352789) B1352789
theorem B901889 : Blo 599292 901889 := bstep (se 2 (by rfl) ⟨338208, by rfl⟩ : syracuseStep 901889 = 676417) B676417
theorem B901907 : Blo 599292 901907 := bstep (se 1 (by rfl) ⟨676430, by rfl⟩ : syracuseStep 901907 = 1352861) B1352861
theorem B901937 : Blo 599292 901937 := bstep (se 2 (by rfl) ⟨338226, by rfl⟩ : syracuseStep 901937 = 676453) B676453
theorem B901955 : Blo 599292 901955 := bstep (se 1 (by rfl) ⟨676466, by rfl⟩ : syracuseStep 901955 = 1352933) B1352933
theorem B901985 : Blo 599292 901985 := bstep (se 2 (by rfl) ⟨338244, by rfl⟩ : syracuseStep 901985 = 676489) B676489
theorem B902003 : Blo 599292 902003 := bstep (se 1 (by rfl) ⟨676502, by rfl⟩ : syracuseStep 902003 = 1353005) B1353005
theorem B902033 : Blo 599292 902033 := bstep (se 2 (by rfl) ⟨338262, by rfl⟩ : syracuseStep 902033 = 676525) B676525
theorem B2278307 : Blo 599292 2278307 := bstep (se 1 (by rfl) ⟨1708730, by rfl⟩ : syracuseStep 2278307 = 3417461) B3417461
theorem B902051 : Blo 599292 902051 := bstep (se 1 (by rfl) ⟨676538, by rfl⟩ : syracuseStep 902051 = 1353077) B1353077
theorem B902081 : Blo 599292 902081 := bstep (se 2 (by rfl) ⟨338280, by rfl⟩ : syracuseStep 902081 = 676561) B676561
theorem B902099 : Blo 599292 902099 := bstep (se 1 (by rfl) ⟨676574, by rfl⟩ : syracuseStep 902099 = 1353149) B1353149
theorem B902129 : Blo 599292 902129 := bstep (se 2 (by rfl) ⟨338298, by rfl⟩ : syracuseStep 902129 = 676597) B676597
theorem B902147 : Blo 599292 902147 := bstep (se 1 (by rfl) ⟨676610, by rfl⟩ : syracuseStep 902147 = 1353221) B1353221
theorem B902177 : Blo 599292 902177 := bstep (se 2 (by rfl) ⟨338316, by rfl⟩ : syracuseStep 902177 = 676633) B676633
theorem B902195 : Blo 599292 902195 := bstep (se 1 (by rfl) ⟨676646, by rfl⟩ : syracuseStep 902195 = 1353293) B1353293
theorem B902225 : Blo 599292 902225 := bstep (se 2 (by rfl) ⟨338334, by rfl⟩ : syracuseStep 902225 = 676669) B676669
theorem B902243 : Blo 599292 902243 := bstep (se 1 (by rfl) ⟨676682, by rfl⟩ : syracuseStep 902243 = 1353365) B1353365
theorem B902273 : Blo 599292 902273 := bstep (se 2 (by rfl) ⟨338352, by rfl⟩ : syracuseStep 902273 = 676705) B676705
theorem B902291 : Blo 599292 902291 := bstep (se 1 (by rfl) ⟨676718, by rfl⟩ : syracuseStep 902291 = 1353437) B1353437
theorem B902321 : Blo 599292 902321 := bstep (se 2 (by rfl) ⟨338370, by rfl⟩ : syracuseStep 902321 = 676741) B676741
theorem B902339 : Blo 599292 902339 := bstep (se 1 (by rfl) ⟨676754, by rfl⟩ : syracuseStep 902339 = 1353509) B1353509
theorem B902369 : Blo 599292 902369 := bstep (se 2 (by rfl) ⟨338388, by rfl⟩ : syracuseStep 902369 = 676777) B676777
theorem B1524977 : Blo 599292 1524977 := bstep (se 2 (by rfl) ⟨571866, by rfl⟩ : syracuseStep 1524977 = 1143733) B1143733
theorem B902387 : Blo 599292 902387 := bstep (se 1 (by rfl) ⟨676790, by rfl⟩ : syracuseStep 902387 = 1353581) B1353581
theorem B902417 : Blo 599292 902417 := bstep (se 2 (by rfl) ⟨338406, by rfl⟩ : syracuseStep 902417 = 676813) B676813
theorem B902435 : Blo 599292 902435 := bstep (se 1 (by rfl) ⟨676826, by rfl⟩ : syracuseStep 902435 = 1353653) B1353653
theorem B1525027 : Blo 599292 1525027 := bstep (se 1 (by rfl) ⟨1143770, by rfl⟩ : syracuseStep 1525027 = 2287541) B2287541
theorem B2442545 : Blo 599292 2442545 := bstep (se 2 (by rfl) ⟨915954, by rfl⟩ : syracuseStep 2442545 = 1831909) B1831909
theorem B902465 : Blo 599292 902465 := bstep (se 2 (by rfl) ⟨338424, by rfl⟩ : syracuseStep 902465 = 676849) B676849
theorem B902483 : Blo 599292 902483 := bstep (se 1 (by rfl) ⟨676862, by rfl⟩ : syracuseStep 902483 = 1353725) B1353725
theorem B902513 : Blo 599292 902513 := bstep (se 2 (by rfl) ⟨338442, by rfl⟩ : syracuseStep 902513 = 676885) B676885
theorem B902531 : Blo 599292 902531 := bstep (se 1 (by rfl) ⟨676898, by rfl⟩ : syracuseStep 902531 = 1353797) B1353797
theorem B902561 : Blo 599292 902561 := bstep (se 2 (by rfl) ⟨338460, by rfl⟩ : syracuseStep 902561 = 676921) B676921
theorem B1525169 : Blo 599292 1525169 := bstep (se 2 (by rfl) ⟨571938, by rfl⟩ : syracuseStep 1525169 = 1143877) B1143877
theorem B902579 : Blo 599292 902579 := bstep (se 1 (by rfl) ⟨676934, by rfl⟩ : syracuseStep 902579 = 1353869) B1353869
theorem B902609 : Blo 599292 902609 := bstep (se 2 (by rfl) ⟨338478, by rfl⟩ : syracuseStep 902609 = 676957) B676957
theorem B902627 : Blo 599292 902627 := bstep (se 1 (by rfl) ⟨676970, by rfl⟩ : syracuseStep 902627 = 1353941) B1353941
theorem B902657 : Blo 599292 902657 := bstep (se 2 (by rfl) ⟨338496, by rfl⟩ : syracuseStep 902657 = 676993) B676993
theorem B902675 : Blo 599292 902675 := bstep (se 1 (by rfl) ⟨677006, by rfl⟩ : syracuseStep 902675 = 1354013) B1354013
theorem B2606627 : Blo 599292 2606627 := bstep (se 1 (by rfl) ⟨1954970, by rfl⟩ : syracuseStep 2606627 = 3909941) B3909941
theorem B2278961 : Blo 599292 2278961 := bstep (se 2 (by rfl) ⟨854610, by rfl⟩ : syracuseStep 2278961 = 1709221) B1709221
theorem B902705 : Blo 599292 902705 := bstep (se 2 (by rfl) ⟨338514, by rfl⟩ : syracuseStep 902705 = 677029) B677029
theorem B902723 : Blo 599292 902723 := bstep (se 1 (by rfl) ⟨677042, by rfl⟩ : syracuseStep 902723 = 1354085) B1354085
theorem B640595 : Blo 599292 640595 := bstep (se 1 (by rfl) ⟨480446, by rfl⟩ : syracuseStep 640595 = 960893) B960893
theorem B902753 : Blo 599292 902753 := bstep (se 2 (by rfl) ⟨338532, by rfl⟩ : syracuseStep 902753 = 677065) B677065
theorem B902771 : Blo 599292 902771 := bstep (se 1 (by rfl) ⟨677078, by rfl⟩ : syracuseStep 902771 = 1354157) B1354157
theorem B902801 : Blo 599292 902801 := bstep (se 2 (by rfl) ⟨338550, by rfl⟩ : syracuseStep 902801 = 677101) B677101
theorem B902819 : Blo 599292 902819 := bstep (se 1 (by rfl) ⟨677114, by rfl⟩ : syracuseStep 902819 = 1354229) B1354229
theorem B902849 : Blo 599292 902849 := bstep (se 2 (by rfl) ⟨338568, by rfl⟩ : syracuseStep 902849 = 677137) B677137
theorem B902867 : Blo 599292 902867 := bstep (se 1 (by rfl) ⟨677150, by rfl⟩ : syracuseStep 902867 = 1354301) B1354301
theorem B902897 : Blo 599292 902897 := bstep (se 2 (by rfl) ⟨338586, by rfl⟩ : syracuseStep 902897 = 677173) B677173
theorem B902915 : Blo 599292 902915 := bstep (se 1 (by rfl) ⟨677186, by rfl⟩ : syracuseStep 902915 = 1354373) B1354373
theorem B902945 : Blo 599292 902945 := bstep (se 2 (by rfl) ⟨338604, by rfl⟩ : syracuseStep 902945 = 677209) B677209
theorem B902963 : Blo 599292 902963 := bstep (se 1 (by rfl) ⟨677222, by rfl⟩ : syracuseStep 902963 = 1354445) B1354445
theorem B902993 : Blo 599292 902993 := bstep (se 2 (by rfl) ⟨338622, by rfl⟩ : syracuseStep 902993 = 677245) B677245
theorem B903011 : Blo 599292 903011 := bstep (se 1 (by rfl) ⟨677258, by rfl⟩ : syracuseStep 903011 = 1354517) B1354517
theorem B903041 : Blo 599292 903041 := bstep (se 2 (by rfl) ⟨338640, by rfl⟩ : syracuseStep 903041 = 677281) B677281
theorem B903059 : Blo 599292 903059 := bstep (se 1 (by rfl) ⟨677294, by rfl⟩ : syracuseStep 903059 = 1354589) B1354589
theorem B2738083 : Blo 599292 2738083 := bstep (se 1 (by rfl) ⟨2053562, by rfl⟩ : syracuseStep 2738083 = 4107125) B4107125
theorem B903089 : Blo 599292 903089 := bstep (se 2 (by rfl) ⟨338658, by rfl⟩ : syracuseStep 903089 = 677317) B677317
theorem B903107 : Blo 599292 903107 := bstep (se 1 (by rfl) ⟨677330, by rfl⟩ : syracuseStep 903107 = 1354661) B1354661
theorem B903137 : Blo 599292 903137 := bstep (se 2 (by rfl) ⟨338676, by rfl⟩ : syracuseStep 903137 = 677353) B677353
theorem B903155 : Blo 599292 903155 := bstep (se 1 (by rfl) ⟨677366, by rfl⟩ : syracuseStep 903155 = 1354733) B1354733
theorem B903185 : Blo 599292 903185 := bstep (se 2 (by rfl) ⟨338694, by rfl⟩ : syracuseStep 903185 = 677389) B677389
theorem B903203 : Blo 599292 903203 := bstep (se 1 (by rfl) ⟨677402, by rfl⟩ : syracuseStep 903203 = 1354805) B1354805
theorem B2738225 : Blo 599292 2738225 := bstep (se 2 (by rfl) ⟨1026834, by rfl⟩ : syracuseStep 2738225 = 2053669) B2053669
theorem B903233 : Blo 599292 903233 := bstep (se 2 (by rfl) ⟨338712, by rfl⟩ : syracuseStep 903233 = 677425) B677425
theorem B903251 : Blo 599292 903251 := bstep (se 1 (by rfl) ⟨677438, by rfl⟩ : syracuseStep 903251 = 1354877) B1354877
theorem B903281 : Blo 599292 903281 := bstep (se 2 (by rfl) ⟨338730, by rfl⟩ : syracuseStep 903281 = 677461) B677461
theorem B903299 : Blo 599292 903299 := bstep (se 1 (by rfl) ⟨677474, by rfl⟩ : syracuseStep 903299 = 1354949) B1354949
theorem B1853585 : Blo 599292 1853585 := bstep (se 2 (by rfl) ⟨695094, by rfl⟩ : syracuseStep 1853585 = 1390189) B1390189
theorem B903329 : Blo 599292 903329 := bstep (se 2 (by rfl) ⟨338748, by rfl⟩ : syracuseStep 903329 = 677497) B677497
theorem B903347 : Blo 599292 903347 := bstep (se 1 (by rfl) ⟨677510, by rfl⟩ : syracuseStep 903347 = 1355021) B1355021
theorem B903377 : Blo 599292 903377 := bstep (se 2 (by rfl) ⟨338766, by rfl⟩ : syracuseStep 903377 = 677533) B677533
theorem B903395 : Blo 599292 903395 := bstep (se 1 (by rfl) ⟨677546, by rfl⟩ : syracuseStep 903395 = 1355093) B1355093
theorem B903425 : Blo 599292 903425 := bstep (se 2 (by rfl) ⟨338784, by rfl⟩ : syracuseStep 903425 = 677569) B677569
theorem B903443 : Blo 599292 903443 := bstep (se 1 (by rfl) ⟨677582, by rfl⟩ : syracuseStep 903443 = 1355165) B1355165
theorem B903473 : Blo 599292 903473 := bstep (se 2 (by rfl) ⟨338802, by rfl⟩ : syracuseStep 903473 = 677605) B677605
theorem B903491 : Blo 599292 903491 := bstep (se 1 (by rfl) ⟨677618, by rfl⟩ : syracuseStep 903491 = 1355237) B1355237
theorem B903521 : Blo 599292 903521 := bstep (se 2 (by rfl) ⟨338820, by rfl⟩ : syracuseStep 903521 = 677641) B677641
theorem B903539 : Blo 599292 903539 := bstep (se 1 (by rfl) ⟨677654, by rfl⟩ : syracuseStep 903539 = 1355309) B1355309
theorem B903569 : Blo 599292 903569 := bstep (se 2 (by rfl) ⟨338838, by rfl⟩ : syracuseStep 903569 = 677677) B677677
theorem B1526161 : Blo 599292 1526161 := bstep (se 2 (by rfl) ⟨572310, by rfl⟩ : syracuseStep 1526161 = 1144621) B1144621
theorem B903587 : Blo 599292 903587 := bstep (se 1 (by rfl) ⟨677690, by rfl⟩ : syracuseStep 903587 = 1355381) B1355381
theorem B903617 : Blo 599292 903617 := bstep (se 2 (by rfl) ⟨338856, by rfl⟩ : syracuseStep 903617 = 677713) B677713
theorem B903635 : Blo 599292 903635 := bstep (se 1 (by rfl) ⟨677726, by rfl⟩ : syracuseStep 903635 = 1355453) B1355453
theorem B674275 : Blo 599292 674275 := bstep (se 1 (by rfl) ⟨505706, by rfl⟩ : syracuseStep 674275 = 1011413) B1011413
theorem B903665 : Blo 599292 903665 := bstep (se 2 (by rfl) ⟨338874, by rfl⟩ : syracuseStep 903665 = 677749) B677749
theorem B903683 : Blo 599292 903683 := bstep (se 1 (by rfl) ⟨677762, by rfl⟩ : syracuseStep 903683 = 1355525) B1355525
theorem B903713 : Blo 599292 903713 := bstep (se 2 (by rfl) ⟨338892, by rfl⟩ : syracuseStep 903713 = 677785) B677785
theorem B903731 : Blo 599292 903731 := bstep (se 1 (by rfl) ⟨677798, by rfl⟩ : syracuseStep 903731 = 1355597) B1355597
theorem B3426893 : Blo 599292 3426893 := bstep (se 3 (by rfl) ⟨642542, by rfl⟩ : syracuseStep 3426893 = 1285085) B1285085
theorem B903761 : Blo 599292 903761 := bstep (se 2 (by rfl) ⟨338910, by rfl⟩ : syracuseStep 903761 = 677821) B677821
theorem B903779 : Blo 599292 903779 := bstep (se 1 (by rfl) ⟨677834, by rfl⟩ : syracuseStep 903779 = 1355669) B1355669
theorem B674419 : Blo 599292 674419 := bstep (se 1 (by rfl) ⟨505814, by rfl⟩ : syracuseStep 674419 = 1011629) B1011629
theorem B903809 : Blo 599292 903809 := bstep (se 2 (by rfl) ⟨338928, by rfl⟩ : syracuseStep 903809 = 677857) B677857
theorem B4344461 : Blo 599292 4344461 := bstep (se 3 (by rfl) ⟨814586, by rfl⟩ : syracuseStep 4344461 = 1629173) B1629173
theorem B2574989 : Blo 599292 2574989 := bstep (se 3 (by rfl) ⟨482810, by rfl⟩ : syracuseStep 2574989 = 965621) B965621
theorem B903827 : Blo 599292 903827 := bstep (se 1 (by rfl) ⟨677870, by rfl⟩ : syracuseStep 903827 = 1355741) B1355741
theorem B1526435 : Blo 599292 1526435 := bstep (se 1 (by rfl) ⟨1144826, by rfl⟩ : syracuseStep 1526435 = 2289653) B2289653
theorem B903857 : Blo 599292 903857 := bstep (se 2 (by rfl) ⟨338946, by rfl⟩ : syracuseStep 903857 = 677893) B677893
theorem B641731 : Blo 599292 641731 := bstep (se 1 (by rfl) ⟨481298, by rfl⟩ : syracuseStep 641731 = 962597) B962597
theorem B903875 : Blo 599292 903875 := bstep (se 1 (by rfl) ⟨677906, by rfl⟩ : syracuseStep 903875 = 1355813) B1355813
theorem B903905 : Blo 599292 903905 := bstep (se 2 (by rfl) ⟨338964, by rfl⟩ : syracuseStep 903905 = 677929) B677929
theorem B903923 : Blo 599292 903923 := bstep (se 1 (by rfl) ⟨677942, by rfl⟩ : syracuseStep 903923 = 1355885) B1355885
theorem B674563 : Blo 599292 674563 := bstep (se 1 (by rfl) ⟨505922, by rfl⟩ : syracuseStep 674563 = 1011845) B1011845
theorem B903953 : Blo 599292 903953 := bstep (se 2 (by rfl) ⟨338982, by rfl⟩ : syracuseStep 903953 = 677965) B677965
theorem B903971 : Blo 599292 903971 := bstep (se 1 (by rfl) ⟨677978, by rfl⟩ : syracuseStep 903971 = 1355957) B1355957
theorem B904001 : Blo 599292 904001 := bstep (se 2 (by rfl) ⟨339000, by rfl⟩ : syracuseStep 904001 = 678001) B678001
theorem B904019 : Blo 599292 904019 := bstep (se 1 (by rfl) ⟨678014, by rfl⟩ : syracuseStep 904019 = 1356029) B1356029
theorem B1526627 : Blo 599292 1526627 := bstep (se 1 (by rfl) ⟨1144970, by rfl⟩ : syracuseStep 1526627 = 2289941) B2289941
theorem B904049 : Blo 599292 904049 := bstep (se 2 (by rfl) ⟨339018, by rfl⟩ : syracuseStep 904049 = 678037) B678037
theorem B904067 : Blo 599292 904067 := bstep (se 1 (by rfl) ⟨678050, by rfl⟩ : syracuseStep 904067 = 1356101) B1356101
theorem B674707 : Blo 599292 674707 := bstep (se 1 (by rfl) ⟨506030, by rfl⟩ : syracuseStep 674707 = 1012061) B1012061
theorem B904097 : Blo 599292 904097 := bstep (se 2 (by rfl) ⟨339036, by rfl⟩ : syracuseStep 904097 = 678073) B678073
theorem B904115 : Blo 599292 904115 := bstep (se 1 (by rfl) ⟨678086, by rfl⟩ : syracuseStep 904115 = 1356173) B1356173
theorem B904145 : Blo 599292 904145 := bstep (se 2 (by rfl) ⟨339054, by rfl⟩ : syracuseStep 904145 = 678109) B678109
theorem B2280419 : Blo 599292 2280419 := bstep (se 1 (by rfl) ⟨1710314, by rfl⟩ : syracuseStep 2280419 = 3420629) B3420629
theorem B904163 : Blo 599292 904163 := bstep (se 1 (by rfl) ⟨678122, by rfl⟩ : syracuseStep 904163 = 1356245) B1356245
theorem B3034097 : Blo 599292 3034097 := bstep (se 2 (by rfl) ⟨1137786, by rfl⟩ : syracuseStep 3034097 = 2275573) B2275573
theorem B2280433 : Blo 599292 2280433 := bstep (se 2 (by rfl) ⟨855162, by rfl⟩ : syracuseStep 2280433 = 1710325) B1710325
theorem B904193 : Blo 599292 904193 := bstep (se 2 (by rfl) ⟨339072, by rfl⟩ : syracuseStep 904193 = 678145) B678145
theorem B904211 : Blo 599292 904211 := bstep (se 1 (by rfl) ⟨678158, by rfl⟩ : syracuseStep 904211 = 1356317) B1356317
theorem B674851 : Blo 599292 674851 := bstep (se 1 (by rfl) ⟨506138, by rfl⟩ : syracuseStep 674851 = 1012277) B1012277
theorem B904241 : Blo 599292 904241 := bstep (se 2 (by rfl) ⟨339090, by rfl⟩ : syracuseStep 904241 = 678181) B678181
theorem B904259 : Blo 599292 904259 := bstep (se 1 (by rfl) ⟨678194, by rfl⟩ : syracuseStep 904259 = 1356389) B1356389
theorem B3296333 : Blo 599292 3296333 := bstep (se 3 (by rfl) ⟨618062, by rfl⟩ : syracuseStep 3296333 = 1236125) B1236125
theorem B904289 : Blo 599292 904289 := bstep (se 2 (by rfl) ⟨339108, by rfl⟩ : syracuseStep 904289 = 678217) B678217
theorem B904307 : Blo 599292 904307 := bstep (se 1 (by rfl) ⟨678230, by rfl⟩ : syracuseStep 904307 = 1356461) B1356461
theorem B1920145 : Blo 599292 1920145 := bstep (se 2 (by rfl) ⟨720054, by rfl⟩ : syracuseStep 1920145 = 1440109) B1440109
theorem B904337 : Blo 599292 904337 := bstep (se 2 (by rfl) ⟨339126, by rfl⟩ : syracuseStep 904337 = 678253) B678253
theorem B904355 : Blo 599292 904355 := bstep (se 1 (by rfl) ⟨678266, by rfl⟩ : syracuseStep 904355 = 1356533) B1356533
theorem B674995 : Blo 599292 674995 := bstep (se 1 (by rfl) ⟨506246, by rfl⟩ : syracuseStep 674995 = 1012493) B1012493
theorem B904385 : Blo 599292 904385 := bstep (se 2 (by rfl) ⟨339144, by rfl⟩ : syracuseStep 904385 = 678289) B678289
theorem B904403 : Blo 599292 904403 := bstep (se 1 (by rfl) ⟨678302, by rfl⟩ : syracuseStep 904403 = 1356605) B1356605
theorem B904433 : Blo 599292 904433 := bstep (se 2 (by rfl) ⟨339162, by rfl⟩ : syracuseStep 904433 = 678325) B678325
theorem B904451 : Blo 599292 904451 := bstep (se 1 (by rfl) ⟨678338, by rfl⟩ : syracuseStep 904451 = 1356677) B1356677
theorem B904481 : Blo 599292 904481 := bstep (se 2 (by rfl) ⟨339180, by rfl⟩ : syracuseStep 904481 = 678361) B678361
theorem B2313521 : Blo 599292 2313521 := bstep (se 2 (by rfl) ⟨867570, by rfl⟩ : syracuseStep 2313521 = 1735141) B1735141
theorem B904499 : Blo 599292 904499 := bstep (se 1 (by rfl) ⟨678374, by rfl⟩ : syracuseStep 904499 = 1356749) B1356749
theorem B1920323 : Blo 599292 1920323 := bstep (se 1 (by rfl) ⟨1440242, by rfl⟩ : syracuseStep 1920323 = 2880485) B2880485
theorem B675139 : Blo 599292 675139 := bstep (se 1 (by rfl) ⟨506354, by rfl⟩ : syracuseStep 675139 = 1012709) B1012709
theorem B904529 : Blo 599292 904529 := bstep (se 2 (by rfl) ⟨339198, by rfl⟩ : syracuseStep 904529 = 678397) B678397
theorem B904547 : Blo 599292 904547 := bstep (se 1 (by rfl) ⟨678410, by rfl⟩ : syracuseStep 904547 = 1356821) B1356821
theorem B904577 : Blo 599292 904577 := bstep (se 2 (by rfl) ⟨339216, by rfl⟩ : syracuseStep 904577 = 678433) B678433
theorem B904595 : Blo 599292 904595 := bstep (se 1 (by rfl) ⟨678446, by rfl⟩ : syracuseStep 904595 = 1356893) B1356893
theorem B904625 : Blo 599292 904625 := bstep (se 2 (by rfl) ⟨339234, by rfl⟩ : syracuseStep 904625 = 678469) B678469
theorem B904643 : Blo 599292 904643 := bstep (se 1 (by rfl) ⟨678482, by rfl⟩ : syracuseStep 904643 = 1356965) B1356965
theorem B675283 : Blo 599292 675283 := bstep (se 1 (by rfl) ⟨506462, by rfl⟩ : syracuseStep 675283 = 1012925) B1012925
theorem B904673 : Blo 599292 904673 := bstep (se 2 (by rfl) ⟨339252, by rfl⟩ : syracuseStep 904673 = 678505) B678505
theorem B904691 : Blo 599292 904691 := bstep (se 1 (by rfl) ⟨678518, by rfl⟩ : syracuseStep 904691 = 1357037) B1357037
theorem B904721 : Blo 599292 904721 := bstep (se 2 (by rfl) ⟨339270, by rfl⟩ : syracuseStep 904721 = 678541) B678541
theorem B904739 : Blo 599292 904739 := bstep (se 1 (by rfl) ⟨678554, by rfl⟩ : syracuseStep 904739 = 1357109) B1357109
theorem B642611 : Blo 599292 642611 := bstep (se 1 (by rfl) ⟨481958, by rfl⟩ : syracuseStep 642611 = 963917) B963917
theorem B904769 : Blo 599292 904769 := bstep (se 2 (by rfl) ⟨339288, by rfl⟩ : syracuseStep 904769 = 678577) B678577
theorem B904787 : Blo 599292 904787 := bstep (se 1 (by rfl) ⟨678590, by rfl⟩ : syracuseStep 904787 = 1357181) B1357181
theorem B675427 : Blo 599292 675427 := bstep (se 1 (by rfl) ⟨506570, by rfl⟩ : syracuseStep 675427 = 1013141) B1013141
theorem B904817 : Blo 599292 904817 := bstep (se 2 (by rfl) ⟨339306, by rfl⟩ : syracuseStep 904817 = 678613) B678613
theorem B904835 : Blo 599292 904835 := bstep (se 1 (by rfl) ⟨678626, by rfl⟩ : syracuseStep 904835 = 1357253) B1357253
theorem B2444941 : Blo 599292 2444941 := bstep (se 3 (by rfl) ⟨458426, by rfl⟩ : syracuseStep 2444941 = 916853) B916853
theorem B904865 : Blo 599292 904865 := bstep (se 2 (by rfl) ⟨339324, by rfl⟩ : syracuseStep 904865 = 678649) B678649
theorem B642739 : Blo 599292 642739 := bstep (se 1 (by rfl) ⟨482054, by rfl⟩ : syracuseStep 642739 = 964109) B964109
theorem B904883 : Blo 599292 904883 := bstep (se 1 (by rfl) ⟨678662, by rfl⟩ : syracuseStep 904883 = 1357325) B1357325
theorem B904913 : Blo 599292 904913 := bstep (se 2 (by rfl) ⟨339342, by rfl⟩ : syracuseStep 904913 = 678685) B678685
theorem B904931 : Blo 599292 904931 := bstep (se 1 (by rfl) ⟨678698, by rfl⟩ : syracuseStep 904931 = 1357397) B1357397
theorem B675571 : Blo 599292 675571 := bstep (se 1 (by rfl) ⟨506678, by rfl⟩ : syracuseStep 675571 = 1013357) B1013357
theorem B675715 : Blo 599292 675715 := bstep (se 1 (by rfl) ⟨506786, by rfl⟩ : syracuseStep 675715 = 1013573) B1013573
theorem B4575203 : Blo 599292 4575203 := bstep (se 1 (by rfl) ⟨3431402, by rfl⟩ : syracuseStep 4575203 = 6862805) B6862805
theorem B675859 : Blo 599292 675859 := bstep (se 1 (by rfl) ⟨506894, by rfl⟩ : syracuseStep 675859 = 1013789) B1013789
theorem B676003 : Blo 599292 676003 := bstep (se 1 (by rfl) ⟨507002, by rfl⟩ : syracuseStep 676003 = 1014005) B1014005
theorem B676147 : Blo 599292 676147 := bstep (se 1 (by rfl) ⟨507110, by rfl⟩ : syracuseStep 676147 = 1014221) B1014221
theorem B3035555 : Blo 599292 3035555 := bstep (se 1 (by rfl) ⟨2276666, by rfl⟩ : syracuseStep 3035555 = 4553333) B4553333
theorem B2281891 : Blo 599292 2281891 := bstep (se 1 (by rfl) ⟨1711418, by rfl⟩ : syracuseStep 2281891 = 3422837) B3422837
theorem B676291 : Blo 599292 676291 := bstep (se 1 (by rfl) ⟨507218, by rfl⟩ : syracuseStep 676291 = 1014437) B1014437
theorem B643555 : Blo 599292 643555 := bstep (se 1 (by rfl) ⟨482666, by rfl⟩ : syracuseStep 643555 = 965333) B965333
theorem B3854897 : Blo 599292 3854897 := bstep (se 2 (by rfl) ⟨1445586, by rfl⟩ : syracuseStep 3854897 = 2891173) B2891173
theorem B676435 : Blo 599292 676435 := bstep (se 1 (by rfl) ⟨507326, by rfl⟩ : syracuseStep 676435 = 1014653) B1014653
theorem B1692269 : Blo 599292 1692269 := bstep (se 3 (by rfl) ⟨317300, by rfl⟩ : syracuseStep 1692269 = 634601) B634601
theorem B10965617 : Blo 599292 10965617 := bstep (se 2 (by rfl) ⟨4112106, by rfl⟩ : syracuseStep 10965617 = 8224213) B8224213
theorem B676579 : Blo 599292 676579 := bstep (se 1 (by rfl) ⟨507434, by rfl⟩ : syracuseStep 676579 = 1014869) B1014869
theorem B3429125 : Blo 599292 3429125 := bstep (se 4 (by rfl) ⟨321480, by rfl⟩ : syracuseStep 3429125 = 642961) B642961
theorem B676723 : Blo 599292 676723 := bstep (se 1 (by rfl) ⟨507542, by rfl⟩ : syracuseStep 676723 = 1015085) B1015085
theorem B1823683 : Blo 599292 1823683 := bstep (se 1 (by rfl) ⟨1367762, by rfl⟩ : syracuseStep 1823683 = 2735525) B2735525
theorem B676867 : Blo 599292 676867 := bstep (se 1 (by rfl) ⟨507650, by rfl⟩ : syracuseStep 676867 = 1015301) B1015301
theorem B1922093 : Blo 599292 1922093 := bstep (se 3 (by rfl) ⟨360392, by rfl⟩ : syracuseStep 1922093 = 720785) B720785
theorem B1758275 : Blo 599292 1758275 := bstep (se 1 (by rfl) ⟨1318706, by rfl⟩ : syracuseStep 1758275 = 2637413) B2637413
theorem B677011 : Blo 599292 677011 := bstep (se 1 (by rfl) ⟨507758, by rfl⟩ : syracuseStep 677011 = 1015517) B1015517
theorem B3036365 : Blo 599292 3036365 := bstep (se 3 (by rfl) ⟨569318, by rfl⟩ : syracuseStep 3036365 = 1138637) B1138637
theorem B677155 : Blo 599292 677155 := bstep (se 1 (by rfl) ⟨507866, by rfl⟩ : syracuseStep 677155 = 1015733) B1015733
theorem B3429809 : Blo 599292 3429809 := bstep (se 2 (by rfl) ⟨1286178, by rfl⟩ : syracuseStep 3429809 = 2572357) B2572357
theorem B677299 : Blo 599292 677299 := bstep (se 1 (by rfl) ⟨507974, by rfl⟩ : syracuseStep 677299 = 1015949) B1015949
theorem B677443 : Blo 599292 677443 := bstep (se 1 (by rfl) ⟨508082, by rfl⟩ : syracuseStep 677443 = 1016165) B1016165
theorem B1824365 : Blo 599292 1824365 := bstep (se 3 (by rfl) ⟨342068, by rfl⟩ : syracuseStep 1824365 = 684137) B684137
theorem B1627789 : Blo 599292 1627789 := bstep (se 3 (by rfl) ⟨305210, by rfl⟩ : syracuseStep 1627789 = 610421) B610421
theorem B677587 : Blo 599292 677587 := bstep (se 1 (by rfl) ⟨508190, by rfl⟩ : syracuseStep 677587 = 1016381) B1016381
theorem B677731 : Blo 599292 677731 := bstep (se 1 (by rfl) ⟨508298, by rfl⟩ : syracuseStep 677731 = 1016597) B1016597
theorem B677875 : Blo 599292 677875 := bstep (se 1 (by rfl) ⟨508406, by rfl⟩ : syracuseStep 677875 = 1016813) B1016813
theorem B678019 : Blo 599292 678019 := bstep (se 1 (by rfl) ⟨508514, by rfl⟩ : syracuseStep 678019 = 1017029) B1017029
theorem B7297165 : Blo 599292 7297165 := bstep (se 3 (by rfl) ⟨1368218, by rfl⟩ : syracuseStep 7297165 = 2736437) B2736437
theorem B678163 : Blo 599292 678163 := bstep (se 1 (by rfl) ⟨508622, by rfl⟩ : syracuseStep 678163 = 1017245) B1017245
theorem B1857937 : Blo 599292 1857937 := bstep (se 2 (by rfl) ⟨696726, by rfl⟩ : syracuseStep 1857937 = 1393453) B1393453
theorem B678307 : Blo 599292 678307 := bstep (se 1 (by rfl) ⟨508730, by rfl⟩ : syracuseStep 678307 = 1017461) B1017461
theorem B16407011 : Blo 599292 16407011 := bstep (se 1 (by rfl) ⟨12305258, by rfl⟩ : syracuseStep 16407011 = 24610517) B24610517
theorem B678451 : Blo 599292 678451 := bstep (se 1 (by rfl) ⟨508838, by rfl⟩ : syracuseStep 678451 = 1017677) B1017677
theorem B2284109 : Blo 599292 2284109 := bstep (se 3 (by rfl) ⟨428270, by rfl⟩ : syracuseStep 2284109 = 856541) B856541
theorem B678595 : Blo 599292 678595 := bstep (se 1 (by rfl) ⟨508946, by rfl⟩ : syracuseStep 678595 = 1017893) B1017893
theorem B3431267 : Blo 599292 3431267 := bstep (se 1 (by rfl) ⟨2573450, by rfl⟩ : syracuseStep 3431267 = 5146901) B5146901
theorem B4381553 : Blo 599292 4381553 := bstep (se 2 (by rfl) ⟨1643082, by rfl⟩ : syracuseStep 4381553 = 3286165) B3286165
theorem B6839477 : Blo 599292 6839477 := bstep (se 5 (by rfl) ⟨320600, by rfl⟩ : syracuseStep 6839477 = 641201) B641201
theorem B2055395 : Blo 599292 2055395 := bstep (se 1 (by rfl) ⟨1541546, by rfl⟩ : syracuseStep 2055395 = 3083093) B3083093
theorem B1465777 : Blo 599292 1465777 := bstep (se 2 (by rfl) ⟨549666, by rfl⟩ : syracuseStep 1465777 = 1099333) B1099333
theorem B2022893 : Blo 599292 2022893 := bstep (se 3 (by rfl) ⟨379292, by rfl⟩ : syracuseStep 2022893 = 758585) B758585
theorem B2022947 : Blo 599292 2022947 := bstep (se 1 (by rfl) ⟨1517210, by rfl⟩ : syracuseStep 2022947 = 3034421) B3034421
theorem B1040035 : Blo 599292 1040035 := bstep (se 1 (by rfl) ⟨780026, by rfl⟩ : syracuseStep 1040035 = 1560053) B1560053
theorem B2023217 : Blo 599292 2023217 := bstep (se 2 (by rfl) ⟨758706, by rfl⟩ : syracuseStep 2023217 = 1517413) B1517413
theorem B1138531 : Blo 599292 1138531 := bstep (se 1 (by rfl) ⟨853898, by rfl⟩ : syracuseStep 1138531 = 1707797) B1707797
theorem B1138691 : Blo 599292 1138691 := bstep (se 1 (by rfl) ⟨854018, by rfl⟩ : syracuseStep 1138691 = 1708037) B1708037
theorem B3039281 : Blo 599292 3039281 := bstep (se 2 (by rfl) ⟨1139730, by rfl⟩ : syracuseStep 3039281 = 2279461) B2279461
theorem B6480013 : Blo 599292 6480013 := bstep (se 3 (by rfl) ⟨1215002, by rfl⟩ : syracuseStep 6480013 = 2430005) B2430005
theorem B811153 : Blo 599292 811153 := bstep (se 2 (by rfl) ⟨304182, by rfl⟩ : syracuseStep 811153 = 608365) B608365
theorem B13000931 : Blo 599292 13000931 := bstep (se 1 (by rfl) ⟨9750698, by rfl⟩ : syracuseStep 13000931 = 19501397) B19501397
theorem B2023757 : Blo 599292 2023757 := bstep (se 3 (by rfl) ⟨379454, by rfl⟩ : syracuseStep 2023757 = 758909) B758909
theorem B6185315 : Blo 599292 6185315 := bstep (se 1 (by rfl) ⟨4638986, by rfl⟩ : syracuseStep 6185315 = 9277973) B9277973
theorem B2023811 : Blo 599292 2023811 := bstep (se 1 (by rfl) ⟨1517858, by rfl⟩ : syracuseStep 2023811 = 3035717) B3035717
theorem B1925603 : Blo 599292 1925603 := bstep (se 1 (by rfl) ⟨1444202, by rfl⟩ : syracuseStep 1925603 = 2888405) B2888405
theorem B2744867 : Blo 599292 2744867 := bstep (se 1 (by rfl) ⟨2058650, by rfl⟩ : syracuseStep 2744867 = 4117301) B4117301
theorem B3662405 : Blo 599292 3662405 := bstep (se 4 (by rfl) ⟨343350, by rfl⟩ : syracuseStep 3662405 = 686701) B686701
theorem B975473 : Blo 599292 975473 := bstep (se 2 (by rfl) ⟨365802, by rfl⟩ : syracuseStep 975473 = 731605) B731605
theorem B2024081 : Blo 599292 2024081 := bstep (se 2 (by rfl) ⟨759030, by rfl⟩ : syracuseStep 2024081 = 1518061) B1518061
theorem B812035 : Blo 599292 812035 := bstep (se 1 (by rfl) ⟨609026, by rfl⟩ : syracuseStep 812035 = 1218053) B1218053
theorem B1139761 : Blo 599292 1139761 := bstep (se 2 (by rfl) ⟨427410, by rfl⟩ : syracuseStep 1139761 = 854821) B854821
theorem B1926193 : Blo 599292 1926193 := bstep (se 2 (by rfl) ⟨722322, by rfl⟩ : syracuseStep 1926193 = 1444645) B1444645
theorem B2024621 : Blo 599292 2024621 := bstep (se 3 (by rfl) ⟨379616, by rfl⟩ : syracuseStep 2024621 = 759233) B759233
theorem B4580549 : Blo 599292 4580549 := bstep (se 4 (by rfl) ⟨429426, by rfl⟩ : syracuseStep 4580549 = 858853) B858853
theorem B9233635 : Blo 599292 9233635 := bstep (se 1 (by rfl) ⟨6925226, by rfl⟩ : syracuseStep 9233635 = 13850453) B13850453
theorem B2024675 : Blo 599292 2024675 := bstep (se 1 (by rfl) ⟨1518506, by rfl⟩ : syracuseStep 2024675 = 3037013) B3037013
theorem B1369315 : Blo 599292 1369315 := bstep (se 1 (by rfl) ⟨1026986, by rfl⟩ : syracuseStep 1369315 = 2053973) B2053973
theorem B976115 : Blo 599292 976115 := bstep (se 1 (by rfl) ⟨732086, by rfl⟩ : syracuseStep 976115 = 1464173) B1464173
theorem B2287025 : Blo 599292 2287025 := bstep (se 2 (by rfl) ⟨857634, by rfl⟩ : syracuseStep 2287025 = 1715269) B1715269
theorem B3040739 : Blo 599292 3040739 := bstep (se 1 (by rfl) ⟨2280554, by rfl⟩ : syracuseStep 3040739 = 4561109) B4561109
theorem B2024945 : Blo 599292 2024945 := bstep (se 2 (by rfl) ⟨759354, by rfl⟩ : syracuseStep 2024945 = 1518709) B1518709
theorem B3859973 : Blo 599292 3859973 := bstep (se 4 (by rfl) ⟨361872, by rfl⟩ : syracuseStep 3859973 = 723745) B723745
theorem B3434501 : Blo 599292 3434501 := bstep (se 4 (by rfl) ⟨321984, by rfl⟩ : syracuseStep 3434501 = 643969) B643969
theorem B2025485 : Blo 599292 2025485 := bstep (se 3 (by rfl) ⟨379778, by rfl⟩ : syracuseStep 2025485 = 759557) B759557
theorem B2025539 : Blo 599292 2025539 := bstep (se 1 (by rfl) ⟨1519154, by rfl⟩ : syracuseStep 2025539 = 3038309) B3038309
theorem B1140817 : Blo 599292 1140817 := bstep (se 2 (by rfl) ⟨427806, by rfl⟩ : syracuseStep 1140817 = 855613) B855613
theorem B649379 : Blo 599292 649379 := bstep (se 1 (by rfl) ⟨487034, by rfl⟩ : syracuseStep 649379 = 974069) B974069
theorem B6187205 : Blo 599292 6187205 := bstep (se 4 (by rfl) ⟨580050, by rfl⟩ : syracuseStep 6187205 = 1160101) B1160101
theorem B10414307 : Blo 599292 10414307 := bstep (se 1 (by rfl) ⟨7810730, by rfl⟩ : syracuseStep 10414307 = 15621461) B15621461
theorem B3041549 : Blo 599292 3041549 := bstep (se 3 (by rfl) ⟨570290, by rfl⟩ : syracuseStep 3041549 = 1140581) B1140581
theorem B2025809 : Blo 599292 2025809 := bstep (se 2 (by rfl) ⟨759678, by rfl⟩ : syracuseStep 2025809 = 1519357) B1519357
theorem B2058641 : Blo 599292 2058641 := bstep (se 2 (by rfl) ⟨771990, by rfl⟩ : syracuseStep 2058641 = 1543981) B1543981
theorem B3434957 : Blo 599292 3434957 := bstep (se 3 (by rfl) ⟨644054, by rfl⟩ : syracuseStep 3434957 = 1288109) B1288109
theorem B1141219 : Blo 599292 1141219 := bstep (se 1 (by rfl) ⟨855914, by rfl⟩ : syracuseStep 1141219 = 1711829) B1711829
theorem B1370609 : Blo 599292 1370609 := bstep (se 2 (by rfl) ⟨513978, by rfl⟩ : syracuseStep 1370609 = 1027957) B1027957
theorem B1141265 : Blo 599292 1141265 := bstep (se 2 (by rfl) ⟨427974, by rfl⟩ : syracuseStep 1141265 = 855949) B855949
theorem B813683 : Blo 599292 813683 := bstep (se 1 (by rfl) ⟨610262, by rfl⟩ : syracuseStep 813683 = 1220525) B1220525
theorem B1141553 : Blo 599292 1141553 := bstep (se 2 (by rfl) ⟨428082, by rfl⟩ : syracuseStep 1141553 = 856165) B856165
theorem B2288483 : Blo 599292 2288483 := bstep (se 1 (by rfl) ⟨1716362, by rfl⟩ : syracuseStep 2288483 = 3432725) B3432725
theorem B2026349 : Blo 599292 2026349 := bstep (se 3 (by rfl) ⟨379940, by rfl⟩ : syracuseStep 2026349 = 759881) B759881
theorem B2026403 : Blo 599292 2026403 := bstep (se 1 (by rfl) ⟨1519802, by rfl⟩ : syracuseStep 2026403 = 3039605) B3039605
theorem B2026673 : Blo 599292 2026673 := bstep (se 2 (by rfl) ⟨760002, by rfl⟩ : syracuseStep 2026673 = 1520005) B1520005
theorem B13036913 : Blo 599292 13036913 := bstep (se 2 (by rfl) ⟨4888842, by rfl⟩ : syracuseStep 13036913 = 9777685) B9777685
theorem B5795185 : Blo 599292 5795185 := bstep (se 2 (by rfl) ⟨2173194, by rfl⟩ : syracuseStep 5795185 = 4346389) B4346389
theorem B1830289 : Blo 599292 1830289 := bstep (se 2 (by rfl) ⟨686358, by rfl⟩ : syracuseStep 1830289 = 1372717) B1372717
theorem B1142275 : Blo 599292 1142275 := bstep (se 1 (by rfl) ⟨856706, by rfl⟩ : syracuseStep 1142275 = 1713413) B1713413
theorem B2059853 : Blo 599292 2059853 := bstep (se 3 (by rfl) ⟨386222, by rfl⟩ : syracuseStep 2059853 = 772445) B772445
theorem B1011379 : Blo 599292 1011379 := bstep (se 1 (by rfl) ⟨758534, by rfl⟩ : syracuseStep 1011379 = 1517069) B1517069
theorem B2027213 : Blo 599292 2027213 := bstep (se 3 (by rfl) ⟨380102, by rfl⟩ : syracuseStep 2027213 = 760205) B760205
theorem B2027267 : Blo 599292 2027267 := bstep (se 1 (by rfl) ⟨1520450, by rfl⟩ : syracuseStep 2027267 = 3040901) B3040901
theorem B41676565 : Blo 599292 41676565 := bstep (se 6 (by rfl) ⟨976794, by rfl⟩ : syracuseStep 41676565 = 1953589) B1953589
theorem B1011521 : Blo 599292 1011521 := bstep (se 2 (by rfl) ⟨379320, by rfl⟩ : syracuseStep 1011521 = 758641) B758641
theorem B1929037 : Blo 599292 1929037 := bstep (se 3 (by rfl) ⟨361694, by rfl⟩ : syracuseStep 1929037 = 723389) B723389
theorem B2289485 : Blo 599292 2289485 := bstep (se 3 (by rfl) ⟨429278, by rfl⟩ : syracuseStep 2289485 = 858557) B858557
theorem B913297 : Blo 599292 913297 := bstep (se 2 (by rfl) ⟨342486, by rfl⟩ : syracuseStep 913297 = 684973) B684973
theorem B1011649 : Blo 599292 1011649 := bstep (se 2 (by rfl) ⟨379368, by rfl⟩ : syracuseStep 1011649 = 758737) B758737
theorem B1142723 : Blo 599292 1142723 := bstep (se 1 (by rfl) ⟨857042, by rfl⟩ : syracuseStep 1142723 = 1714085) B1714085
theorem B1011683 : Blo 599292 1011683 := bstep (se 1 (by rfl) ⟨758762, by rfl⟩ : syracuseStep 1011683 = 1517525) B1517525
theorem B2027537 : Blo 599292 2027537 := bstep (se 2 (by rfl) ⟨760326, by rfl⟩ : syracuseStep 2027537 = 1520653) B1520653
theorem B815153 : Blo 599292 815153 := bstep (se 2 (by rfl) ⟨305682, by rfl⟩ : syracuseStep 815153 = 611365) B611365
theorem B1011811 : Blo 599292 1011811 := bstep (se 1 (by rfl) ⟨758858, by rfl⟩ : syracuseStep 1011811 = 1517717) B1517717
theorem B2060401 : Blo 599292 2060401 := bstep (se 2 (by rfl) ⟨772650, by rfl⟩ : syracuseStep 2060401 = 1545301) B1545301
theorem B4321421 : Blo 599292 4321421 := bstep (se 3 (by rfl) ⟨810266, by rfl⟩ : syracuseStep 4321421 = 1620533) B1620533
theorem B815267 : Blo 599292 815267 := bstep (se 1 (by rfl) ⟨611450, by rfl⟩ : syracuseStep 815267 = 1222901) B1222901
theorem B3207395 : Blo 599292 3207395 := bstep (se 1 (by rfl) ⟨2405546, by rfl⟩ : syracuseStep 3207395 = 4811093) B4811093
theorem B1143011 : Blo 599292 1143011 := bstep (se 1 (by rfl) ⟨857258, by rfl⟩ : syracuseStep 1143011 = 1714517) B1714517
theorem B1011953 : Blo 599292 1011953 := bstep (se 2 (by rfl) ⟨379482, by rfl⟩ : syracuseStep 1011953 = 758965) B758965
theorem B9761077 : Blo 599292 9761077 := bstep (se 5 (by rfl) ⟨457550, by rfl⟩ : syracuseStep 9761077 = 915101) B915101
theorem B4321649 : Blo 599292 4321649 := bstep (se 2 (by rfl) ⟨1620618, by rfl⟩ : syracuseStep 4321649 = 3241237) B3241237
theorem B1012081 : Blo 599292 1012081 := bstep (se 2 (by rfl) ⟨379530, by rfl⟩ : syracuseStep 1012081 = 759061) B759061
theorem B1012115 : Blo 599292 1012115 := bstep (se 1 (by rfl) ⟨759086, by rfl⟩ : syracuseStep 1012115 = 1518173) B1518173
theorem B1012243 : Blo 599292 1012243 := bstep (se 1 (by rfl) ⟨759182, by rfl⟩ : syracuseStep 1012243 = 1518365) B1518365
theorem B2028077 : Blo 599292 2028077 := bstep (se 3 (by rfl) ⟨380264, by rfl⟩ : syracuseStep 2028077 = 760529) B760529
theorem B2028131 : Blo 599292 2028131 := bstep (se 1 (by rfl) ⟨1521098, by rfl⟩ : syracuseStep 2028131 = 3042197) B3042197
theorem B1012385 : Blo 599292 1012385 := bstep (se 2 (by rfl) ⟨379644, by rfl⟩ : syracuseStep 1012385 = 759289) B759289
theorem B914177 : Blo 599292 914177 := bstep (se 2 (by rfl) ⟨342816, by rfl⟩ : syracuseStep 914177 = 685633) B685633
theorem B1012513 : Blo 599292 1012513 := bstep (se 2 (by rfl) ⟨379692, by rfl⟩ : syracuseStep 1012513 = 759385) B759385
theorem B1012547 : Blo 599292 1012547 := bstep (se 1 (by rfl) ⟨759410, by rfl⟩ : syracuseStep 1012547 = 1518821) B1518821
theorem B2028401 : Blo 599292 2028401 := bstep (se 2 (by rfl) ⟨760650, by rfl⟩ : syracuseStep 2028401 = 1521301) B1521301
theorem B914323 : Blo 599292 914323 := bstep (se 1 (by rfl) ⟨685742, by rfl⟩ : syracuseStep 914323 = 1371485) B1371485
theorem B1012675 : Blo 599292 1012675 := bstep (se 1 (by rfl) ⟨759506, by rfl⟩ : syracuseStep 1012675 = 1519013) B1519013
theorem B2061389 : Blo 599292 2061389 := bstep (se 3 (by rfl) ⟨386510, by rfl⟩ : syracuseStep 2061389 = 773021) B773021
theorem B1012817 : Blo 599292 1012817 := bstep (se 2 (by rfl) ⟨379806, by rfl⟩ : syracuseStep 1012817 = 759613) B759613
theorem B3044465 : Blo 599292 3044465 := bstep (se 2 (by rfl) ⟨1141674, by rfl⟩ : syracuseStep 3044465 = 2283349) B2283349
theorem B1143953 : Blo 599292 1143953 := bstep (se 2 (by rfl) ⟨428982, by rfl⟩ : syracuseStep 1143953 = 857965) B857965
theorem B1012945 : Blo 599292 1012945 := bstep (se 2 (by rfl) ⟨379854, by rfl⟩ : syracuseStep 1012945 = 759709) B759709
theorem B1012979 : Blo 599292 1012979 := bstep (se 1 (by rfl) ⟨759734, by rfl⟩ : syracuseStep 1012979 = 1519469) B1519469
theorem B1930499 : Blo 599292 1930499 := bstep (se 1 (by rfl) ⟨1447874, by rfl⟩ : syracuseStep 1930499 = 2895749) B2895749
theorem B1013107 : Blo 599292 1013107 := bstep (se 1 (by rfl) ⟨759830, by rfl⟩ : syracuseStep 1013107 = 1519661) B1519661
theorem B2028941 : Blo 599292 2028941 := bstep (se 3 (by rfl) ⟨380426, by rfl⟩ : syracuseStep 2028941 = 760853) B760853
theorem B2028995 : Blo 599292 2028995 := bstep (se 1 (by rfl) ⟨1521746, by rfl⟩ : syracuseStep 2028995 = 3043493) B3043493
theorem B6190577 : Blo 599292 6190577 := bstep (se 2 (by rfl) ⟨2321466, by rfl⟩ : syracuseStep 6190577 = 4642933) B4642933
theorem B1013249 : Blo 599292 1013249 := bstep (se 2 (by rfl) ⟨379968, by rfl⟩ : syracuseStep 1013249 = 759937) B759937
theorem B4126277 : Blo 599292 4126277 := bstep (se 4 (by rfl) ⟨386838, by rfl⟩ : syracuseStep 4126277 = 773677) B773677
theorem B1013377 : Blo 599292 1013377 := bstep (se 2 (by rfl) ⟨380016, by rfl⟩ : syracuseStep 1013377 = 760033) B760033
theorem B1537667 : Blo 599292 1537667 := bstep (se 1 (by rfl) ⟨1153250, by rfl⟩ : syracuseStep 1537667 = 2306501) B2306501
theorem B1013411 : Blo 599292 1013411 := bstep (se 1 (by rfl) ⟨760058, by rfl⟩ : syracuseStep 1013411 = 1520117) B1520117
theorem B2029265 : Blo 599292 2029265 := bstep (se 2 (by rfl) ⟨760974, by rfl⟩ : syracuseStep 2029265 = 1521949) B1521949
theorem B1013539 : Blo 599292 1013539 := bstep (se 1 (by rfl) ⟨760154, by rfl⟩ : syracuseStep 1013539 = 1520309) B1520309
theorem B1013681 : Blo 599292 1013681 := bstep (se 2 (by rfl) ⟨380130, by rfl⟩ : syracuseStep 1013681 = 760261) B760261
theorem B1832881 : Blo 599292 1832881 := bstep (se 2 (by rfl) ⟨687330, by rfl⟩ : syracuseStep 1832881 = 1374661) B1374661
theorem B1144849 : Blo 599292 1144849 := bstep (se 2 (by rfl) ⟨429318, by rfl⟩ : syracuseStep 1144849 = 858637) B858637
theorem B3864611 : Blo 599292 3864611 := bstep (se 1 (by rfl) ⟨2898458, by rfl⟩ : syracuseStep 3864611 = 5796917) B5796917
theorem B1013809 : Blo 599292 1013809 := bstep (se 2 (by rfl) ⟨380178, by rfl⟩ : syracuseStep 1013809 = 760357) B760357
theorem B1013843 : Blo 599292 1013843 := bstep (se 1 (by rfl) ⟨760382, by rfl⟩ : syracuseStep 1013843 = 1520765) B1520765
theorem B1145009 : Blo 599292 1145009 := bstep (se 2 (by rfl) ⟨429378, by rfl⟩ : syracuseStep 1145009 = 858757) B858757
theorem B1013971 : Blo 599292 1013971 := bstep (se 1 (by rfl) ⟨760478, by rfl⟩ : syracuseStep 1013971 = 1520957) B1520957
theorem B2029805 : Blo 599292 2029805 := bstep (se 3 (by rfl) ⟨380588, by rfl⟩ : syracuseStep 2029805 = 761177) B761177
theorem B2029859 : Blo 599292 2029859 := bstep (se 1 (by rfl) ⟨1522394, by rfl⟩ : syracuseStep 2029859 = 3044789) B3044789
theorem B1014113 : Blo 599292 1014113 := bstep (se 2 (by rfl) ⟨380292, by rfl⟩ : syracuseStep 1014113 = 760585) B760585
theorem B1014241 : Blo 599292 1014241 := bstep (se 2 (by rfl) ⟨380340, by rfl⟩ : syracuseStep 1014241 = 760681) B760681
theorem B1014275 : Blo 599292 1014275 := bstep (se 1 (by rfl) ⟨760706, by rfl⟩ : syracuseStep 1014275 = 1521413) B1521413
theorem B3045923 : Blo 599292 3045923 := bstep (se 1 (by rfl) ⟨2284442, by rfl⟩ : syracuseStep 3045923 = 4568885) B4568885
theorem B2161201 : Blo 599292 2161201 := bstep (se 2 (by rfl) ⟨810450, by rfl⟩ : syracuseStep 2161201 = 1620901) B1620901
theorem B2030129 : Blo 599292 2030129 := bstep (se 2 (by rfl) ⟨761298, by rfl⟩ : syracuseStep 2030129 = 1522597) B1522597
theorem B1374769 : Blo 599292 1374769 := bstep (se 2 (by rfl) ⟨515538, by rfl⟩ : syracuseStep 1374769 = 1031077) B1031077
theorem B1014403 : Blo 599292 1014403 := bstep (se 1 (by rfl) ⟨760802, by rfl⟩ : syracuseStep 1014403 = 1521605) B1521605
theorem B1080067 : Blo 599292 1080067 := bstep (se 1 (by rfl) ⟨810050, by rfl⟩ : syracuseStep 1080067 = 1620101) B1620101
theorem B1014545 : Blo 599292 1014545 := bstep (se 2 (by rfl) ⟨380454, by rfl⟩ : syracuseStep 1014545 = 760909) B760909
theorem B1932113 : Blo 599292 1932113 := bstep (se 2 (by rfl) ⟨724542, by rfl⟩ : syracuseStep 1932113 = 1449085) B1449085
theorem B4881293 : Blo 599292 4881293 := bstep (se 3 (by rfl) ⟨915242, by rfl⟩ : syracuseStep 4881293 = 1830485) B1830485
theorem B1014673 : Blo 599292 1014673 := bstep (se 2 (by rfl) ⟨380502, by rfl⟩ : syracuseStep 1014673 = 761005) B761005
theorem B1014707 : Blo 599292 1014707 := bstep (se 1 (by rfl) ⟨761030, by rfl⟩ : syracuseStep 1014707 = 1522061) B1522061
theorem B1014835 : Blo 599292 1014835 := bstep (se 1 (by rfl) ⟨761126, by rfl⟩ : syracuseStep 1014835 = 1522253) B1522253
theorem B2030669 : Blo 599292 2030669 := bstep (se 3 (by rfl) ⟨380750, by rfl⟩ : syracuseStep 2030669 = 761501) B761501
theorem B2751565 : Blo 599292 2751565 := bstep (se 3 (by rfl) ⟨515918, by rfl⟩ : syracuseStep 2751565 = 1031837) B1031837
theorem B916561 : Blo 599292 916561 := bstep (se 2 (by rfl) ⟨343710, by rfl⟩ : syracuseStep 916561 = 687421) B687421
theorem B2030723 : Blo 599292 2030723 := bstep (se 1 (by rfl) ⟨1523042, by rfl⟩ : syracuseStep 2030723 = 3046085) B3046085
theorem B1014977 : Blo 599292 1014977 := bstep (se 2 (by rfl) ⟨380616, by rfl⟩ : syracuseStep 1014977 = 761233) B761233
theorem B1834193 : Blo 599292 1834193 := bstep (se 2 (by rfl) ⟨687822, by rfl⟩ : syracuseStep 1834193 = 1375645) B1375645
theorem B7699697 : Blo 599292 7699697 := bstep (se 2 (by rfl) ⟨2887386, by rfl⟩ : syracuseStep 7699697 = 5774773) B5774773
theorem B916769 : Blo 599292 916769 := bstep (se 2 (by rfl) ⟨343788, by rfl⟩ : syracuseStep 916769 = 687577) B687577
theorem B1015105 : Blo 599292 1015105 := bstep (se 2 (by rfl) ⟨380664, by rfl⟩ : syracuseStep 1015105 = 761329) B761329
theorem B3046733 : Blo 599292 3046733 := bstep (se 3 (by rfl) ⟨571262, by rfl⟩ : syracuseStep 3046733 = 1142525) B1142525
theorem B1015139 : Blo 599292 1015139 := bstep (se 1 (by rfl) ⟨761354, by rfl⟩ : syracuseStep 1015139 = 1522709) B1522709
theorem B2030993 : Blo 599292 2030993 := bstep (se 2 (by rfl) ⟨761622, by rfl⟩ : syracuseStep 2030993 = 1523245) B1523245
theorem B1015267 : Blo 599292 1015267 := bstep (se 1 (by rfl) ⟨761450, by rfl⟩ : syracuseStep 1015267 = 1522901) B1522901
theorem B1015409 : Blo 599292 1015409 := bstep (se 2 (by rfl) ⟨380778, by rfl⟩ : syracuseStep 1015409 = 761557) B761557
theorem B917219 : Blo 599292 917219 := bstep (se 1 (by rfl) ⟨687914, by rfl⟩ : syracuseStep 917219 = 1375829) B1375829
theorem B1015537 : Blo 599292 1015537 := bstep (se 2 (by rfl) ⟨380826, by rfl⟩ : syracuseStep 1015537 = 761653) B761653
theorem B1015571 : Blo 599292 1015571 := bstep (se 1 (by rfl) ⟨761678, by rfl⟩ : syracuseStep 1015571 = 1523357) B1523357
theorem B1015699 : Blo 599292 1015699 := bstep (se 1 (by rfl) ⟨761774, by rfl⟩ : syracuseStep 1015699 = 1523549) B1523549
theorem B2031533 : Blo 599292 2031533 := bstep (se 3 (by rfl) ⟨380912, by rfl⟩ : syracuseStep 2031533 = 761825) B761825
theorem B2162659 : Blo 599292 2162659 := bstep (se 1 (by rfl) ⟨1621994, by rfl⟩ : syracuseStep 2162659 = 3243989) B3243989
theorem B2031587 : Blo 599292 2031587 := bstep (se 1 (by rfl) ⟨1523690, by rfl⟩ : syracuseStep 2031587 = 3047381) B3047381
theorem B1015895 : Blo 599292 1015895 := bstep (se 1 (by rfl) ⟨761921, by rfl⟩ : syracuseStep 1015895 = 1523843) B1523843
theorem B1081523 : Blo 599292 1081523 := bstep (se 1 (by rfl) ⟨811142, by rfl⟩ : syracuseStep 1081523 = 1622285) B1622285
theorem B1016023 : Blo 599292 1016023 := bstep (se 1 (by rfl) ⟨762017, by rfl⟩ : syracuseStep 1016023 = 1524035) B1524035
theorem B2031965 : Blo 599292 2031965 := bstep (se 3 (by rfl) ⟨380993, by rfl⟩ : syracuseStep 2031965 = 761987) B761987
theorem B8553053 : Blo 599292 8553053 := bstep (se 3 (by rfl) ⟨1603697, by rfl⟩ : syracuseStep 8553053 = 3207395) B3207395
theorem B3048029 : Blo 599292 3048029 := bstep (se 3 (by rfl) ⟨571505, by rfl⟩ : syracuseStep 3048029 = 1143011) B1143011
theorem B4326149 : Blo 599292 4326149 := bstep (se 4 (by rfl) ⟨405576, by rfl⟩ : syracuseStep 4326149 = 811153) B811153
theorem B2884369 : Blo 599292 2884369 := bstep (se 2 (by rfl) ⟨1081638, by rfl⟩ : syracuseStep 2884369 = 2163277) B2163277
theorem B1016651 : Blo 599292 1016651 := bstep (se 1 (by rfl) ⟨762488, by rfl⟩ : syracuseStep 1016651 = 1524977) B1524977
theorem B6489011 : Blo 599292 6489011 := bstep (se 1 (by rfl) ⟨4866758, by rfl⟩ : syracuseStep 6489011 = 9733517) B9733517
theorem B1016779 : Blo 599292 1016779 := bstep (se 1 (by rfl) ⟨762584, by rfl⟩ : syracuseStep 1016779 = 1525169) B1525169
theorem B1016921 : Blo 599292 1016921 := bstep (se 2 (by rfl) ⟨381345, by rfl⟩ : syracuseStep 1016921 = 762691) B762691
theorem B1017049 : Blo 599292 1017049 := bstep (se 2 (by rfl) ⟨381393, by rfl⟩ : syracuseStep 1017049 = 762787) B762787
theorem B2033099 : Blo 599292 2033099 := bstep (se 1 (by rfl) ⟨1524824, by rfl⟩ : syracuseStep 2033099 = 3049649) B3049649
theorem B4556249 : Blo 599292 4556249 := bstep (se 2 (by rfl) ⟨1708593, by rfl⟩ : syracuseStep 4556249 = 3417187) B3417187
theorem B853591 : Blo 599292 853591 := bstep (se 1 (by rfl) ⟨640193, by rfl⟩ : syracuseStep 853591 = 1280387) B1280387
theorem B2033369 : Blo 599292 2033369 := bstep (se 2 (by rfl) ⟨762513, by rfl⟩ : syracuseStep 2033369 = 1525027) B1525027
theorem B1017623 : Blo 599292 1017623 := bstep (se 1 (by rfl) ⟨763217, by rfl⟩ : syracuseStep 1017623 = 1526435) B1526435
theorem B1017751 : Blo 599292 1017751 := bstep (se 1 (by rfl) ⟨763313, by rfl⟩ : syracuseStep 1017751 = 1526627) B1526627
theorem B15599537 : Blo 599292 15599537 := bstep (se 2 (by rfl) ⟨5849826, by rfl⟩ : syracuseStep 15599537 = 11699653) B11699653
theorem B854155 : Blo 599292 854155 := bstep (se 1 (by rfl) ⟨640616, by rfl⟩ : syracuseStep 854155 = 1281233) B1281233
theorem B1542347 : Blo 599292 1542347 := bstep (se 1 (by rfl) ⟨1156760, by rfl⟩ : syracuseStep 1542347 = 2313521) B2313521
theorem B1280215 : Blo 599292 1280215 := bstep (se 1 (by rfl) ⟨960161, by rfl⟩ : syracuseStep 1280215 = 1920323) B1920323
theorem B2165123 : Blo 599292 2165123 := bstep (se 1 (by rfl) ⟨1623842, by rfl⟩ : syracuseStep 2165123 = 3247685) B3247685
theorem B2034071 : Blo 599292 2034071 := bstep (se 1 (by rfl) ⟨1525553, by rfl⟩ : syracuseStep 2034071 = 3051107) B3051107
theorem B3050135 : Blo 599292 3050135 := bstep (se 1 (by rfl) ⟨2287601, by rfl⟩ : syracuseStep 3050135 = 4575203) B4575203
theorem B2165555 : Blo 599292 2165555 := bstep (se 1 (by rfl) ⟨1624166, by rfl⟩ : syracuseStep 2165555 = 3248333) B3248333
theorem B2034611 : Blo 599292 2034611 := bstep (se 1 (by rfl) ⟨1525958, by rfl⟩ : syracuseStep 2034611 = 3051917) B3051917
theorem B7310411 : Blo 599292 7310411 := bstep (se 1 (by rfl) ⟨5482808, by rfl⟩ : syracuseStep 7310411 = 10965617) B10965617
theorem B2034881 : Blo 599292 2034881 := bstep (se 2 (by rfl) ⟨763080, by rfl⟩ : syracuseStep 2034881 = 1526161) B1526161
theorem B1281395 : Blo 599292 1281395 := bstep (se 1 (by rfl) ⟨961046, by rfl⟩ : syracuseStep 1281395 = 1922093) B1922093
theorem B855641 : Blo 599292 855641 := bstep (se 2 (by rfl) ⟨320865, by rfl⟩ : syracuseStep 855641 = 641731) B641731
theorem B2035421 : Blo 599292 2035421 := bstep (se 3 (by rfl) ⟨381641, by rfl⟩ : syracuseStep 2035421 = 763283) B763283
theorem B1216243 : Blo 599292 1216243 := bstep (se 1 (by rfl) ⟨912182, by rfl⟩ : syracuseStep 1216243 = 1824365) B1824365
theorem B1707979 : Blo 599292 1707979 := bstep (se 1 (by rfl) ⟨1280984, by rfl⟩ : syracuseStep 1707979 = 2561969) B2561969
theorem B6951005 : Blo 599292 6951005 := bstep (se 3 (by rfl) ⟨1303313, by rfl⟩ : syracuseStep 6951005 = 2606627) B2606627
theorem B2560193 : Blo 599292 2560193 := bstep (se 2 (by rfl) ⟨960072, by rfl⟩ : syracuseStep 2560193 = 1920145) B1920145
theorem B856279 : Blo 599292 856279 := bstep (se 1 (by rfl) ⟨642209, by rfl⟩ : syracuseStep 856279 = 1284419) B1284419
theorem B1708253 : Blo 599292 1708253 := bstep (se 3 (by rfl) ⟨320297, by rfl⟩ : syracuseStep 1708253 = 640595) B640595
theorem B17305973 : Blo 599292 17305973 := bstep (se 5 (by rfl) ⟨811217, by rfl⟩ : syracuseStep 17305973 = 1622435) B1622435
theorem B1282625 : Blo 599292 1282625 := bstep (se 2 (by rfl) ⟨480984, by rfl⟩ : syracuseStep 1282625 = 961969) B961969
theorem B2921035 : Blo 599292 2921035 := bstep (se 1 (by rfl) ⟨2190776, by rfl⟩ : syracuseStep 2921035 = 4381553) B4381553
theorem B18551501 : Blo 599292 18551501 := bstep (se 3 (by rfl) ⟨3478406, by rfl⟩ : syracuseStep 18551501 = 6956813) B6956813
theorem B4559651 : Blo 599292 4559651 := bstep (se 1 (by rfl) ⟨3419738, by rfl⟩ : syracuseStep 4559651 = 6839477) B6839477
theorem B1348505 : Blo 599292 1348505 := bstep (se 2 (by rfl) ⟨505689, by rfl⟩ : syracuseStep 1348505 = 1011379) B1011379
theorem B856985 : Blo 599292 856985 := bstep (se 2 (by rfl) ⟨321369, by rfl⟩ : syracuseStep 856985 = 642739) B642739
theorem B2200537 : Blo 599292 2200537 := bstep (se 2 (by rfl) ⟨825201, by rfl⟩ : syracuseStep 2200537 = 1650403) B1650403
theorem B1348595 : Blo 599292 1348595 := bstep (se 1 (by rfl) ⟨1011446, by rfl⟩ : syracuseStep 1348595 = 2022893) B2022893
theorem B857099 : Blo 599292 857099 := bstep (se 1 (by rfl) ⟨642824, by rfl⟩ : syracuseStep 857099 = 1285649) B1285649
theorem B1348631 : Blo 599292 1348631 := bstep (se 1 (by rfl) ⟨1011473, by rfl⟩ : syracuseStep 1348631 = 2022947) B2022947
theorem B20092085 : Blo 599292 20092085 := bstep (se 5 (by rfl) ⟨941816, by rfl⟩ : syracuseStep 20092085 = 1883633) B1883633
theorem B1217729 : Blo 599292 1217729 := bstep (se 2 (by rfl) ⟨456648, by rfl⟩ : syracuseStep 1217729 = 913297) B913297
theorem B1348811 : Blo 599292 1348811 := bstep (se 1 (by rfl) ⟨1011608, by rfl⟩ : syracuseStep 1348811 = 2023217) B2023217
theorem B1348865 : Blo 599292 1348865 := bstep (se 2 (by rfl) ⟨505824, by rfl⟩ : syracuseStep 1348865 = 1011649) B1011649
theorem B759127 : Blo 599292 759127 := bstep (se 1 (by rfl) ⟨569345, by rfl⟩ : syracuseStep 759127 = 1138691) B1138691
theorem B4330853 : Blo 599292 4330853 := bstep (se 4 (by rfl) ⟨406017, by rfl⟩ : syracuseStep 4330853 = 812035) B812035
theorem B1349081 : Blo 599292 1349081 := bstep (se 2 (by rfl) ⟨505905, by rfl⟩ : syracuseStep 1349081 = 1011811) B1011811
theorem B2889233 : Blo 599292 2889233 := bstep (se 2 (by rfl) ⟨1083462, by rfl⟩ : syracuseStep 2889233 = 2166925) B2166925
theorem B857623 : Blo 599292 857623 := bstep (se 1 (by rfl) ⟨643217, by rfl⟩ : syracuseStep 857623 = 1286435) B1286435
theorem B1349171 : Blo 599292 1349171 := bstep (se 1 (by rfl) ⟨1011878, by rfl⟩ : syracuseStep 1349171 = 2023757) B2023757
theorem B1349207 : Blo 599292 1349207 := bstep (se 1 (by rfl) ⟨1011905, by rfl⟩ : syracuseStep 1349207 = 2023811) B2023811
theorem B1283735 : Blo 599292 1283735 := bstep (se 1 (by rfl) ⟨962801, by rfl⟩ : syracuseStep 1283735 = 1925603) B1925603
theorem B13014769 : Blo 599292 13014769 := bstep (se 2 (by rfl) ⟨4880538, by rfl⟩ : syracuseStep 13014769 = 9761077) B9761077
theorem B4888325 : Blo 599292 4888325 := bstep (se 4 (by rfl) ⟨458280, by rfl⟩ : syracuseStep 4888325 = 916561) B916561
theorem B1349387 : Blo 599292 1349387 := bstep (se 1 (by rfl) ⟨1012040, by rfl⟩ : syracuseStep 1349387 = 2024081) B2024081
theorem B1349441 : Blo 599292 1349441 := bstep (se 2 (by rfl) ⟨506040, by rfl⟩ : syracuseStep 1349441 = 1012081) B1012081
theorem B2561867 : Blo 599292 2561867 := bstep (se 1 (by rfl) ⟨1921400, by rfl⟩ : syracuseStep 2561867 = 3842801) B3842801
theorem B4331339 : Blo 599292 4331339 := bstep (se 1 (by rfl) ⟨3248504, by rfl⟩ : syracuseStep 4331339 = 6497009) B6497009
theorem B1349657 : Blo 599292 1349657 := bstep (se 2 (by rfl) ⟨506121, by rfl⟩ : syracuseStep 1349657 = 1012243) B1012243
theorem B1349747 : Blo 599292 1349747 := bstep (se 1 (by rfl) ⟨1012310, by rfl⟩ : syracuseStep 1349747 = 2024621) B2024621
theorem B3053699 : Blo 599292 3053699 := bstep (se 1 (by rfl) ⟨2290274, by rfl⟩ : syracuseStep 3053699 = 4580549) B4580549
theorem B1349783 : Blo 599292 1349783 := bstep (se 1 (by rfl) ⟨1012337, by rfl⟩ : syracuseStep 1349783 = 2024675) B2024675
theorem B1349963 : Blo 599292 1349963 := bstep (se 1 (by rfl) ⟨1012472, by rfl⟩ : syracuseStep 1349963 = 2024945) B2024945
theorem B858443 : Blo 599292 858443 := bstep (se 1 (by rfl) ⟨643832, by rfl⟩ : syracuseStep 858443 = 1287665) B1287665
theorem B1350017 : Blo 599292 1350017 := bstep (se 2 (by rfl) ⟨506256, by rfl⟩ : syracuseStep 1350017 = 1012513) B1012513
theorem B4004275 : Blo 599292 4004275 := bstep (se 1 (by rfl) ⟨3003206, by rfl⟩ : syracuseStep 4004275 = 6006413) B6006413
theorem B1710553 : Blo 599292 1710553 := bstep (se 2 (by rfl) ⟨641457, by rfl⟩ : syracuseStep 1710553 = 1282915) B1282915
theorem B3414545 : Blo 599292 3414545 := bstep (se 2 (by rfl) ⟨1280454, by rfl⟩ : syracuseStep 3414545 = 2560909) B2560909
theorem B5478929 : Blo 599292 5478929 := bstep (se 2 (by rfl) ⟨2054598, by rfl⟩ : syracuseStep 5478929 = 4109197) B4109197
theorem B1219097 : Blo 599292 1219097 := bstep (se 2 (by rfl) ⟨457161, by rfl⟩ : syracuseStep 1219097 = 914323) B914323
theorem B2431577 : Blo 599292 2431577 := bstep (se 2 (by rfl) ⟨911841, by rfl⟩ : syracuseStep 2431577 = 1823683) B1823683
theorem B1350233 : Blo 599292 1350233 := bstep (se 2 (by rfl) ⟨506337, by rfl⟩ : syracuseStep 1350233 = 1012675) B1012675
theorem B1284761 : Blo 599292 1284761 := bstep (se 2 (by rfl) ⟨481785, by rfl⟩ : syracuseStep 1284761 = 963571) B963571
theorem B1350323 : Blo 599292 1350323 := bstep (se 1 (by rfl) ⟨1012742, by rfl⟩ : syracuseStep 1350323 = 2025485) B2025485
theorem B1350359 : Blo 599292 1350359 := bstep (se 1 (by rfl) ⟨1012769, by rfl⟩ : syracuseStep 1350359 = 2025539) B2025539
theorem B1350539 : Blo 599292 1350539 := bstep (se 1 (by rfl) ⟨1012904, by rfl⟩ : syracuseStep 1350539 = 2025809) B2025809
theorem B1350593 : Blo 599292 1350593 := bstep (se 2 (by rfl) ⟨506472, by rfl⟩ : syracuseStep 1350593 = 1012945) B1012945
theorem B2169821 : Blo 599292 2169821 := bstep (se 3 (by rfl) ⟨406841, by rfl⟩ : syracuseStep 2169821 = 813683) B813683
theorem B760843 : Blo 599292 760843 := bstep (se 1 (by rfl) ⟨570632, by rfl⟩ : syracuseStep 760843 = 1141265) B1141265
theorem B1711169 : Blo 599292 1711169 := bstep (se 2 (by rfl) ⟨641688, by rfl⟩ : syracuseStep 1711169 = 1283377) B1283377
theorem B10296395 : Blo 599292 10296395 := bstep (se 1 (by rfl) ⟨7722296, by rfl⟩ : syracuseStep 10296395 = 15444593) B15444593
theorem B1350809 : Blo 599292 1350809 := bstep (se 2 (by rfl) ⟨506553, by rfl⟩ : syracuseStep 1350809 = 1013107) B1013107
theorem B1350899 : Blo 599292 1350899 := bstep (se 1 (by rfl) ⟨1013174, by rfl⟩ : syracuseStep 1350899 = 2026349) B2026349
theorem B62594309 : Blo 599292 62594309 := bstep (se 4 (by rfl) ⟨5868216, by rfl⟩ : syracuseStep 62594309 = 11736433) B11736433
theorem B1350935 : Blo 599292 1350935 := bstep (se 1 (by rfl) ⟨1013201, by rfl⟩ : syracuseStep 1350935 = 2026403) B2026403
theorem B1351115 : Blo 599292 1351115 := bstep (se 1 (by rfl) ⟨1013336, by rfl⟩ : syracuseStep 1351115 = 2026673) B2026673
theorem B1351169 : Blo 599292 1351169 := bstep (se 2 (by rfl) ⟨506688, by rfl⟩ : syracuseStep 1351169 = 1013377) B1013377
theorem B2170385 : Blo 599292 2170385 := bstep (se 2 (by rfl) ⟨813894, by rfl⟩ : syracuseStep 2170385 = 1627789) B1627789
theorem B8691275 : Blo 599292 8691275 := bstep (se 1 (by rfl) ⟨6518456, by rfl⟩ : syracuseStep 8691275 = 13036913) B13036913
theorem B1351385 : Blo 599292 1351385 := bstep (se 2 (by rfl) ⟨506769, by rfl⟩ : syracuseStep 1351385 = 1013539) B1013539
theorem B1351475 : Blo 599292 1351475 := bstep (se 1 (by rfl) ⟨1013606, by rfl⟩ : syracuseStep 1351475 = 2027213) B2027213
theorem B1351511 : Blo 599292 1351511 := bstep (se 1 (by rfl) ⟨1013633, by rfl⟩ : syracuseStep 1351511 = 2027267) B2027267
theorem B761815 : Blo 599292 761815 := bstep (se 1 (by rfl) ⟨571361, by rfl⟩ : syracuseStep 761815 = 1142723) B1142723
theorem B1351691 : Blo 599292 1351691 := bstep (se 1 (by rfl) ⟨1013768, by rfl⟩ : syracuseStep 1351691 = 2027537) B2027537
theorem B1351745 : Blo 599292 1351745 := bstep (se 2 (by rfl) ⟨506904, by rfl⟩ : syracuseStep 1351745 = 1013809) B1013809
theorem B8790221 : Blo 599292 8790221 := bstep (se 3 (by rfl) ⟨1648166, by rfl⟩ : syracuseStep 8790221 = 3296333) B3296333
theorem B1286401 : Blo 599292 1286401 := bstep (se 2 (by rfl) ⟨482400, by rfl⟩ : syracuseStep 1286401 = 964801) B964801
theorem B1351961 : Blo 599292 1351961 := bstep (se 2 (by rfl) ⟨506985, by rfl⟩ : syracuseStep 1351961 = 1013971) B1013971
theorem B1352051 : Blo 599292 1352051 := bstep (se 1 (by rfl) ⟨1014038, by rfl⟩ : syracuseStep 1352051 = 2028077) B2028077
theorem B1352087 : Blo 599292 1352087 := bstep (se 1 (by rfl) ⟨1014065, by rfl⟩ : syracuseStep 1352087 = 2028131) B2028131
theorem B2564531 : Blo 599292 2564531 := bstep (se 1 (by rfl) ⟨1923398, by rfl⟩ : syracuseStep 2564531 = 3846797) B3846797
theorem B1352267 : Blo 599292 1352267 := bstep (se 1 (by rfl) ⟨1014200, by rfl⟩ : syracuseStep 1352267 = 2028401) B2028401
theorem B1352321 : Blo 599292 1352321 := bstep (se 2 (by rfl) ⟨507120, by rfl⟩ : syracuseStep 1352321 = 1014241) B1014241
theorem B762635 : Blo 599292 762635 := bstep (se 1 (by rfl) ⟨571976, by rfl⟩ : syracuseStep 762635 = 1143953) B1143953
theorem B1286999 : Blo 599292 1286999 := bstep (se 1 (by rfl) ⟨965249, by rfl⟩ : syracuseStep 1286999 = 1930499) B1930499
theorem B1352537 : Blo 599292 1352537 := bstep (se 2 (by rfl) ⟨507201, by rfl⟩ : syracuseStep 1352537 = 1014403) B1014403
theorem B1352627 : Blo 599292 1352627 := bstep (se 1 (by rfl) ⟨1014470, by rfl⟩ : syracuseStep 1352627 = 2028941) B2028941
theorem B1352663 : Blo 599292 1352663 := bstep (se 1 (by rfl) ⟨1014497, by rfl⟩ : syracuseStep 1352663 = 2028995) B2028995
theorem B1025111 : Blo 599292 1025111 := bstep (se 1 (by rfl) ⟨768833, by rfl⟩ : syracuseStep 1025111 = 1537667) B1537667
theorem B1713241 : Blo 599292 1713241 := bstep (se 2 (by rfl) ⟨642465, by rfl⟩ : syracuseStep 1713241 = 1284931) B1284931
theorem B1352843 : Blo 599292 1352843 := bstep (se 1 (by rfl) ⟨1014632, by rfl⟩ : syracuseStep 1352843 = 2029265) B2029265
theorem B4334771 : Blo 599292 4334771 := bstep (se 1 (by rfl) ⟨3251078, by rfl⟩ : syracuseStep 4334771 = 6502157) B6502157
theorem B1352897 : Blo 599292 1352897 := bstep (se 2 (by rfl) ⟨507336, by rfl⟩ : syracuseStep 1352897 = 1014673) B1014673
theorem B599307 : Blo 599292 599307 := bstep (se 1 (by rfl) ⟨449480, by rfl⟩ : syracuseStep 599307 = 898961) B898961
theorem B599319 : Blo 599292 599319 := bstep (se 1 (by rfl) ⟨449489, by rfl⟩ : syracuseStep 599319 = 898979) B898979
theorem B599339 : Blo 599292 599339 := bstep (se 1 (by rfl) ⟨449504, by rfl⟩ : syracuseStep 599339 = 899009) B899009
theorem B599351 : Blo 599292 599351 := bstep (se 1 (by rfl) ⟨449513, by rfl⟩ : syracuseStep 599351 = 899027) B899027
theorem B599371 : Blo 599292 599371 := bstep (se 1 (by rfl) ⟨449528, by rfl⟩ : syracuseStep 599371 = 899057) B899057
theorem B599383 : Blo 599292 599383 := bstep (se 1 (by rfl) ⟨449537, by rfl⟩ : syracuseStep 599383 = 899075) B899075
theorem B599403 : Blo 599292 599403 := bstep (se 1 (by rfl) ⟨449552, by rfl⟩ : syracuseStep 599403 = 899105) B899105
theorem B599415 : Blo 599292 599415 := bstep (se 1 (by rfl) ⟨449561, by rfl⟩ : syracuseStep 599415 = 899123) B899123
theorem B599435 : Blo 599292 599435 := bstep (se 1 (by rfl) ⟨449576, by rfl⟩ : syracuseStep 599435 = 899153) B899153
theorem B599447 : Blo 599292 599447 := bstep (se 1 (by rfl) ⟨449585, by rfl⟩ : syracuseStep 599447 = 899171) B899171
theorem B1353113 : Blo 599292 1353113 := bstep (se 2 (by rfl) ⟨507417, by rfl⟩ : syracuseStep 1353113 = 1014835) B1014835
theorem B599467 : Blo 599292 599467 := bstep (se 1 (by rfl) ⟨449600, by rfl⟩ : syracuseStep 599467 = 899201) B899201
theorem B599479 : Blo 599292 599479 := bstep (se 1 (by rfl) ⟨449609, by rfl⟩ : syracuseStep 599479 = 899219) B899219
theorem B599499 : Blo 599292 599499 := bstep (se 1 (by rfl) ⟨449624, by rfl⟩ : syracuseStep 599499 = 899249) B899249
theorem B763339 : Blo 599292 763339 := bstep (se 1 (by rfl) ⟨572504, by rfl⟩ : syracuseStep 763339 = 1145009) B1145009
theorem B599511 : Blo 599292 599511 := bstep (se 1 (by rfl) ⟨449633, by rfl⟩ : syracuseStep 599511 = 899267) B899267
theorem B5219801 : Blo 599292 5219801 := bstep (se 2 (by rfl) ⟨1957425, by rfl⟩ : syracuseStep 5219801 = 3914851) B3914851
theorem B1713629 : Blo 599292 1713629 := bstep (se 3 (by rfl) ⟨321305, by rfl⟩ : syracuseStep 1713629 = 642611) B642611
theorem B599531 : Blo 599292 599531 := bstep (se 1 (by rfl) ⟨449648, by rfl⟩ : syracuseStep 599531 = 899297) B899297
theorem B1353203 : Blo 599292 1353203 := bstep (se 1 (by rfl) ⟨1014902, by rfl⟩ : syracuseStep 1353203 = 2029805) B2029805
theorem B599543 : Blo 599292 599543 := bstep (se 1 (by rfl) ⟨449657, by rfl⟩ : syracuseStep 599543 = 899315) B899315
theorem B599563 : Blo 599292 599563 := bstep (se 1 (by rfl) ⟨449672, by rfl⟩ : syracuseStep 599563 = 899345) B899345
theorem B599575 : Blo 599292 599575 := bstep (se 1 (by rfl) ⟨449681, by rfl⟩ : syracuseStep 599575 = 899363) B899363
theorem B1353239 : Blo 599292 1353239 := bstep (se 1 (by rfl) ⟨1014929, by rfl⟩ : syracuseStep 1353239 = 2029859) B2029859
theorem B599595 : Blo 599292 599595 := bstep (se 1 (by rfl) ⟨449696, by rfl⟩ : syracuseStep 599595 = 899393) B899393
theorem B599607 : Blo 599292 599607 := bstep (se 1 (by rfl) ⟨449705, by rfl⟩ : syracuseStep 599607 = 899411) B899411
theorem B599627 : Blo 599292 599627 := bstep (se 1 (by rfl) ⟨449720, by rfl⟩ : syracuseStep 599627 = 899441) B899441
theorem B599639 : Blo 599292 599639 := bstep (se 1 (by rfl) ⟨449729, by rfl⟩ : syracuseStep 599639 = 899459) B899459
theorem B599659 : Blo 599292 599659 := bstep (se 1 (by rfl) ⟨449744, by rfl⟩ : syracuseStep 599659 = 899489) B899489
theorem B599671 : Blo 599292 599671 := bstep (se 1 (by rfl) ⟨449753, by rfl⟩ : syracuseStep 599671 = 899507) B899507
theorem B599691 : Blo 599292 599691 := bstep (se 1 (by rfl) ⟨449768, by rfl⟩ : syracuseStep 599691 = 899537) B899537
theorem B599703 : Blo 599292 599703 := bstep (se 1 (by rfl) ⟨449777, by rfl⟩ : syracuseStep 599703 = 899555) B899555
theorem B599723 : Blo 599292 599723 := bstep (se 1 (by rfl) ⟨449792, by rfl⟩ : syracuseStep 599723 = 899585) B899585
theorem B599735 : Blo 599292 599735 := bstep (se 1 (by rfl) ⟨449801, by rfl⟩ : syracuseStep 599735 = 899603) B899603
theorem B599755 : Blo 599292 599755 := bstep (se 1 (by rfl) ⟨449816, by rfl⟩ : syracuseStep 599755 = 899633) B899633
theorem B1353419 : Blo 599292 1353419 := bstep (se 1 (by rfl) ⟨1015064, by rfl⟩ : syracuseStep 1353419 = 2030129) B2030129
theorem B599767 : Blo 599292 599767 := bstep (se 1 (by rfl) ⟨449825, by rfl⟩ : syracuseStep 599767 = 899651) B899651
theorem B599787 : Blo 599292 599787 := bstep (se 1 (by rfl) ⟨449840, by rfl⟩ : syracuseStep 599787 = 899681) B899681
theorem B599799 : Blo 599292 599799 := bstep (se 1 (by rfl) ⟨449849, by rfl⟩ : syracuseStep 599799 = 899699) B899699
theorem B1353473 : Blo 599292 1353473 := bstep (se 2 (by rfl) ⟨507552, by rfl⟩ : syracuseStep 1353473 = 1015105) B1015105
theorem B599819 : Blo 599292 599819 := bstep (se 1 (by rfl) ⟨449864, by rfl⟩ : syracuseStep 599819 = 899729) B899729
theorem B599831 : Blo 599292 599831 := bstep (se 1 (by rfl) ⟨449873, by rfl⟩ : syracuseStep 599831 = 899747) B899747
theorem B599851 : Blo 599292 599851 := bstep (se 1 (by rfl) ⟨449888, by rfl⟩ : syracuseStep 599851 = 899777) B899777
theorem B1517363 : Blo 599292 1517363 := bstep (se 1 (by rfl) ⟨1138022, by rfl⟩ : syracuseStep 1517363 = 2276045) B2276045
theorem B599863 : Blo 599292 599863 := bstep (se 1 (by rfl) ⟨449897, by rfl⟩ : syracuseStep 599863 = 899795) B899795
theorem B599883 : Blo 599292 599883 := bstep (se 1 (by rfl) ⟨449912, by rfl⟩ : syracuseStep 599883 = 899825) B899825
theorem B599895 : Blo 599292 599895 := bstep (se 1 (by rfl) ⟨449921, by rfl⟩ : syracuseStep 599895 = 899843) B899843
theorem B599915 : Blo 599292 599915 := bstep (se 1 (by rfl) ⟨449936, by rfl⟩ : syracuseStep 599915 = 899873) B899873
theorem B599927 : Blo 599292 599927 := bstep (se 1 (by rfl) ⟨449945, by rfl⟩ : syracuseStep 599927 = 899891) B899891
theorem B2566019 : Blo 599292 2566019 := bstep (se 1 (by rfl) ⟨1924514, by rfl⟩ : syracuseStep 2566019 = 3849029) B3849029
theorem B599947 : Blo 599292 599947 := bstep (se 1 (by rfl) ⟨449960, by rfl⟩ : syracuseStep 599947 = 899921) B899921
theorem B1288075 : Blo 599292 1288075 := bstep (se 1 (by rfl) ⟨966056, by rfl⟩ : syracuseStep 1288075 = 1932113) B1932113
theorem B599959 : Blo 599292 599959 := bstep (se 1 (by rfl) ⟨449969, by rfl⟩ : syracuseStep 599959 = 899939) B899939
theorem B599979 : Blo 599292 599979 := bstep (se 1 (by rfl) ⟨449984, by rfl⟩ : syracuseStep 599979 = 899969) B899969
theorem B3254195 : Blo 599292 3254195 := bstep (se 1 (by rfl) ⟨2440646, by rfl⟩ : syracuseStep 3254195 = 4881293) B4881293
theorem B599991 : Blo 599292 599991 := bstep (se 1 (by rfl) ⟨449993, by rfl⟩ : syracuseStep 599991 = 899987) B899987
theorem B600011 : Blo 599292 600011 := bstep (se 1 (by rfl) ⟨450008, by rfl⟩ : syracuseStep 600011 = 900017) B900017
theorem B600023 : Blo 599292 600023 := bstep (se 1 (by rfl) ⟨450017, by rfl⟩ : syracuseStep 600023 = 900035) B900035
theorem B1353689 : Blo 599292 1353689 := bstep (se 2 (by rfl) ⟨507633, by rfl⟩ : syracuseStep 1353689 = 1015267) B1015267
theorem B600043 : Blo 599292 600043 := bstep (se 1 (by rfl) ⟨450032, by rfl⟩ : syracuseStep 600043 = 900065) B900065
theorem B600055 : Blo 599292 600055 := bstep (se 1 (by rfl) ⟨450041, by rfl⟩ : syracuseStep 600055 = 900083) B900083
theorem B4564997 : Blo 599292 4564997 := bstep (se 4 (by rfl) ⟨427968, by rfl⟩ : syracuseStep 4564997 = 855937) B855937
theorem B600075 : Blo 599292 600075 := bstep (se 1 (by rfl) ⟨450056, by rfl⟩ : syracuseStep 600075 = 900113) B900113
theorem B600087 : Blo 599292 600087 := bstep (se 1 (by rfl) ⟨450065, by rfl⟩ : syracuseStep 600087 = 900131) B900131
theorem B600107 : Blo 599292 600107 := bstep (se 1 (by rfl) ⟨450080, by rfl⟩ : syracuseStep 600107 = 900161) B900161
theorem B1353779 : Blo 599292 1353779 := bstep (se 1 (by rfl) ⟨1015334, by rfl⟩ : syracuseStep 1353779 = 2030669) B2030669
theorem B600119 : Blo 599292 600119 := bstep (se 1 (by rfl) ⟨450089, by rfl⟩ : syracuseStep 600119 = 900179) B900179
theorem B600139 : Blo 599292 600139 := bstep (se 1 (by rfl) ⟨450104, by rfl⟩ : syracuseStep 600139 = 900209) B900209
theorem B600151 : Blo 599292 600151 := bstep (se 1 (by rfl) ⟨450113, by rfl⟩ : syracuseStep 600151 = 900227) B900227
theorem B1353815 : Blo 599292 1353815 := bstep (se 1 (by rfl) ⟨1015361, by rfl⟩ : syracuseStep 1353815 = 2030723) B2030723
theorem B600171 : Blo 599292 600171 := bstep (se 1 (by rfl) ⟨450128, by rfl⟩ : syracuseStep 600171 = 900257) B900257
theorem B600183 : Blo 599292 600183 := bstep (se 1 (by rfl) ⟨450137, by rfl⟩ : syracuseStep 600183 = 900275) B900275
theorem B600203 : Blo 599292 600203 := bstep (se 1 (by rfl) ⟨450152, by rfl⟩ : syracuseStep 600203 = 900305) B900305
theorem B1222795 : Blo 599292 1222795 := bstep (se 1 (by rfl) ⟨917096, by rfl⟩ : syracuseStep 1222795 = 1834193) B1834193
theorem B1386647 : Blo 599292 1386647 := bstep (se 1 (by rfl) ⟨1039985, by rfl⟩ : syracuseStep 1386647 = 2079971) B2079971
theorem B600215 : Blo 599292 600215 := bstep (se 1 (by rfl) ⟨450161, by rfl⟩ : syracuseStep 600215 = 900323) B900323
theorem B600235 : Blo 599292 600235 := bstep (se 1 (by rfl) ⟨450176, by rfl⟩ : syracuseStep 600235 = 900353) B900353
theorem B600247 : Blo 599292 600247 := bstep (se 1 (by rfl) ⟨450185, by rfl⟩ : syracuseStep 600247 = 900371) B900371
theorem B600267 : Blo 599292 600267 := bstep (se 1 (by rfl) ⟨450200, by rfl⟩ : syracuseStep 600267 = 900401) B900401
theorem B600279 : Blo 599292 600279 := bstep (se 1 (by rfl) ⟨450209, by rfl⟩ : syracuseStep 600279 = 900419) B900419
theorem B1386713 : Blo 599292 1386713 := bstep (se 2 (by rfl) ⟨520017, by rfl⟩ : syracuseStep 1386713 = 1040035) B1040035
theorem B600299 : Blo 599292 600299 := bstep (se 1 (by rfl) ⟨450224, by rfl⟩ : syracuseStep 600299 = 900449) B900449
theorem B600311 : Blo 599292 600311 := bstep (se 1 (by rfl) ⟨450233, by rfl⟩ : syracuseStep 600311 = 900467) B900467
theorem B600331 : Blo 599292 600331 := bstep (se 1 (by rfl) ⟨450248, by rfl⟩ : syracuseStep 600331 = 900497) B900497
theorem B1353995 : Blo 599292 1353995 := bstep (se 1 (by rfl) ⟨1015496, by rfl⟩ : syracuseStep 1353995 = 2030993) B2030993
theorem B600343 : Blo 599292 600343 := bstep (se 1 (by rfl) ⟨450257, by rfl⟩ : syracuseStep 600343 = 900515) B900515
theorem B1059095 : Blo 599292 1059095 := bstep (se 1 (by rfl) ⟨794321, by rfl⟩ : syracuseStep 1059095 = 1588643) B1588643
theorem B600363 : Blo 599292 600363 := bstep (se 1 (by rfl) ⟨450272, by rfl⟩ : syracuseStep 600363 = 900545) B900545
theorem B600375 : Blo 599292 600375 := bstep (se 1 (by rfl) ⟨450281, by rfl⟩ : syracuseStep 600375 = 900563) B900563
theorem B1354049 : Blo 599292 1354049 := bstep (se 2 (by rfl) ⟨507768, by rfl⟩ : syracuseStep 1354049 = 1015537) B1015537
theorem B1517899 : Blo 599292 1517899 := bstep (se 1 (by rfl) ⟨1138424, by rfl⟩ : syracuseStep 1517899 = 2276849) B2276849
theorem B600395 : Blo 599292 600395 := bstep (se 1 (by rfl) ⟨450296, by rfl⟩ : syracuseStep 600395 = 900593) B900593
theorem B600407 : Blo 599292 600407 := bstep (se 1 (by rfl) ⟨450305, by rfl⟩ : syracuseStep 600407 = 900611) B900611
theorem B600427 : Blo 599292 600427 := bstep (se 1 (by rfl) ⟨450320, by rfl⟩ : syracuseStep 600427 = 900641) B900641
theorem B600439 : Blo 599292 600439 := bstep (se 1 (by rfl) ⟨450329, by rfl⟩ : syracuseStep 600439 = 900659) B900659
theorem B600459 : Blo 599292 600459 := bstep (se 1 (by rfl) ⟨450344, by rfl⟩ : syracuseStep 600459 = 900689) B900689
theorem B600471 : Blo 599292 600471 := bstep (se 1 (by rfl) ⟨450353, by rfl⟩ : syracuseStep 600471 = 900707) B900707
theorem B600491 : Blo 599292 600491 := bstep (se 1 (by rfl) ⟨450368, by rfl⟩ : syracuseStep 600491 = 900737) B900737
theorem B600503 : Blo 599292 600503 := bstep (se 1 (by rfl) ⟨450377, by rfl⟩ : syracuseStep 600503 = 900755) B900755
theorem B600523 : Blo 599292 600523 := bstep (se 1 (by rfl) ⟨450392, by rfl⟩ : syracuseStep 600523 = 900785) B900785
theorem B600535 : Blo 599292 600535 := bstep (se 1 (by rfl) ⟨450401, by rfl⟩ : syracuseStep 600535 = 900803) B900803
theorem B1518041 : Blo 599292 1518041 := bstep (se 2 (by rfl) ⟨569265, by rfl⟩ : syracuseStep 1518041 = 1138531) B1138531
theorem B600555 : Blo 599292 600555 := bstep (se 1 (by rfl) ⟨450416, by rfl⟩ : syracuseStep 600555 = 900833) B900833
theorem B600567 : Blo 599292 600567 := bstep (se 1 (by rfl) ⟨450425, by rfl⟩ : syracuseStep 600567 = 900851) B900851
theorem B600587 : Blo 599292 600587 := bstep (se 1 (by rfl) ⟨450440, by rfl⟩ : syracuseStep 600587 = 900881) B900881
theorem B600599 : Blo 599292 600599 := bstep (se 1 (by rfl) ⟨450449, by rfl⟩ : syracuseStep 600599 = 900899) B900899
theorem B928279 : Blo 599292 928279 := bstep (se 1 (by rfl) ⟨696209, by rfl⟩ : syracuseStep 928279 = 1392419) B1392419
theorem B1354265 : Blo 599292 1354265 := bstep (se 2 (by rfl) ⟨507849, by rfl⟩ : syracuseStep 1354265 = 1015699) B1015699
theorem B600619 : Blo 599292 600619 := bstep (se 1 (by rfl) ⟨450464, by rfl⟩ : syracuseStep 600619 = 900929) B900929
theorem B600631 : Blo 599292 600631 := bstep (se 1 (by rfl) ⟨450473, by rfl⟩ : syracuseStep 600631 = 900947) B900947
theorem B600651 : Blo 599292 600651 := bstep (se 1 (by rfl) ⟨450488, by rfl⟩ : syracuseStep 600651 = 900977) B900977
theorem B600663 : Blo 599292 600663 := bstep (se 1 (by rfl) ⟨450497, by rfl⟩ : syracuseStep 600663 = 900995) B900995
theorem B600683 : Blo 599292 600683 := bstep (se 1 (by rfl) ⟨450512, by rfl⟩ : syracuseStep 600683 = 901025) B901025
theorem B1354355 : Blo 599292 1354355 := bstep (se 1 (by rfl) ⟨1015766, by rfl⟩ : syracuseStep 1354355 = 2031533) B2031533
theorem B600695 : Blo 599292 600695 := bstep (se 1 (by rfl) ⟨450521, by rfl⟩ : syracuseStep 600695 = 901043) B901043
theorem B600715 : Blo 599292 600715 := bstep (se 1 (by rfl) ⟨450536, by rfl⟩ : syracuseStep 600715 = 901073) B901073
theorem B600727 : Blo 599292 600727 := bstep (se 1 (by rfl) ⟨450545, by rfl⟩ : syracuseStep 600727 = 901091) B901091
theorem B1354391 : Blo 599292 1354391 := bstep (se 1 (by rfl) ⟨1015793, by rfl⟩ : syracuseStep 1354391 = 2031587) B2031587
theorem B600747 : Blo 599292 600747 := bstep (se 1 (by rfl) ⟨450560, by rfl⟩ : syracuseStep 600747 = 901121) B901121
theorem B600759 : Blo 599292 600759 := bstep (se 1 (by rfl) ⟨450569, by rfl⟩ : syracuseStep 600759 = 901139) B901139
theorem B600779 : Blo 599292 600779 := bstep (se 1 (by rfl) ⟨450584, by rfl⟩ : syracuseStep 600779 = 901169) B901169
theorem B600791 : Blo 599292 600791 := bstep (se 1 (by rfl) ⟨450593, by rfl⟩ : syracuseStep 600791 = 901187) B901187
theorem B600811 : Blo 599292 600811 := bstep (se 1 (by rfl) ⟨450608, by rfl⟩ : syracuseStep 600811 = 901217) B901217
theorem B600823 : Blo 599292 600823 := bstep (se 1 (by rfl) ⟨450617, by rfl⟩ : syracuseStep 600823 = 901235) B901235
theorem B600843 : Blo 599292 600843 := bstep (se 1 (by rfl) ⟨450632, by rfl⟩ : syracuseStep 600843 = 901265) B901265
theorem B961303 : Blo 599292 961303 := bstep (se 1 (by rfl) ⟨720977, by rfl⟩ : syracuseStep 961303 = 1441955) B1441955
theorem B600855 : Blo 599292 600855 := bstep (se 1 (by rfl) ⟨450641, by rfl⟩ : syracuseStep 600855 = 901283) B901283
theorem B600875 : Blo 599292 600875 := bstep (se 1 (by rfl) ⟨450656, by rfl⟩ : syracuseStep 600875 = 901313) B901313
theorem B600887 : Blo 599292 600887 := bstep (se 1 (by rfl) ⟨450665, by rfl⟩ : syracuseStep 600887 = 901331) B901331
theorem B600907 : Blo 599292 600907 := bstep (se 1 (by rfl) ⟨450680, by rfl⟩ : syracuseStep 600907 = 901361) B901361
theorem B1354571 : Blo 599292 1354571 := bstep (se 1 (by rfl) ⟨1015928, by rfl⟩ : syracuseStep 1354571 = 2031857) B2031857
theorem B600919 : Blo 599292 600919 := bstep (se 1 (by rfl) ⟨450689, by rfl⟩ : syracuseStep 600919 = 901379) B901379
theorem B600939 : Blo 599292 600939 := bstep (se 1 (by rfl) ⟨450704, by rfl⟩ : syracuseStep 600939 = 901409) B901409
theorem B600951 : Blo 599292 600951 := bstep (se 1 (by rfl) ⟨450713, by rfl⟩ : syracuseStep 600951 = 901427) B901427
theorem B1354625 : Blo 599292 1354625 := bstep (se 2 (by rfl) ⟨507984, by rfl⟩ : syracuseStep 1354625 = 1015969) B1015969
theorem B600971 : Blo 599292 600971 := bstep (se 1 (by rfl) ⟨450728, by rfl⟩ : syracuseStep 600971 = 901457) B901457
theorem B600983 : Blo 599292 600983 := bstep (se 1 (by rfl) ⟨450737, by rfl⟩ : syracuseStep 600983 = 901475) B901475
theorem B601003 : Blo 599292 601003 := bstep (se 1 (by rfl) ⟨450752, by rfl⟩ : syracuseStep 601003 = 901505) B901505
theorem B601015 : Blo 599292 601015 := bstep (se 1 (by rfl) ⟨450761, by rfl⟩ : syracuseStep 601015 = 901523) B901523
theorem B601035 : Blo 599292 601035 := bstep (se 1 (by rfl) ⟨450776, by rfl⟩ : syracuseStep 601035 = 901553) B901553
theorem B601047 : Blo 599292 601047 := bstep (se 1 (by rfl) ⟨450785, by rfl⟩ : syracuseStep 601047 = 901571) B901571
theorem B601067 : Blo 599292 601067 := bstep (se 1 (by rfl) ⟨450800, by rfl⟩ : syracuseStep 601067 = 901601) B901601
theorem B601079 : Blo 599292 601079 := bstep (se 1 (by rfl) ⟨450809, by rfl⟩ : syracuseStep 601079 = 901619) B901619
theorem B601099 : Blo 599292 601099 := bstep (se 1 (by rfl) ⟨450824, by rfl⟩ : syracuseStep 601099 = 901649) B901649
theorem B961559 : Blo 599292 961559 := bstep (se 1 (by rfl) ⟨721169, by rfl⟩ : syracuseStep 961559 = 1442339) B1442339
theorem B2436119 : Blo 599292 2436119 := bstep (se 1 (by rfl) ⟨1827089, by rfl⟩ : syracuseStep 2436119 = 3654179) B3654179
theorem B601111 : Blo 599292 601111 := bstep (se 1 (by rfl) ⟨450833, by rfl⟩ : syracuseStep 601111 = 901667) B901667
theorem B601131 : Blo 599292 601131 := bstep (se 1 (by rfl) ⟨450848, by rfl⟩ : syracuseStep 601131 = 901697) B901697
theorem B601143 : Blo 599292 601143 := bstep (se 1 (by rfl) ⟨450857, by rfl⟩ : syracuseStep 601143 = 901715) B901715
theorem B9743435 : Blo 599292 9743435 := bstep (se 1 (by rfl) ⟨7307576, by rfl⟩ : syracuseStep 9743435 = 14615153) B14615153
theorem B601163 : Blo 599292 601163 := bstep (se 1 (by rfl) ⟨450872, by rfl⟩ : syracuseStep 601163 = 901745) B901745
theorem B601175 : Blo 599292 601175 := bstep (se 1 (by rfl) ⟨450881, by rfl⟩ : syracuseStep 601175 = 901763) B901763
theorem B1354841 : Blo 599292 1354841 := bstep (se 2 (by rfl) ⟨508065, by rfl⟩ : syracuseStep 1354841 = 1016131) B1016131
theorem B2174045 : Blo 599292 2174045 := bstep (se 3 (by rfl) ⟨407633, by rfl⟩ : syracuseStep 2174045 = 815267) B815267
theorem B601195 : Blo 599292 601195 := bstep (se 1 (by rfl) ⟨450896, by rfl⟩ : syracuseStep 601195 = 901793) B901793
theorem B601207 : Blo 599292 601207 := bstep (se 1 (by rfl) ⟨450905, by rfl⟩ : syracuseStep 601207 = 901811) B901811
theorem B601227 : Blo 599292 601227 := bstep (se 1 (by rfl) ⟨450920, by rfl⟩ : syracuseStep 601227 = 901841) B901841
theorem B4861079 : Blo 599292 4861079 := bstep (se 1 (by rfl) ⟨3645809, by rfl⟩ : syracuseStep 4861079 = 7291619) B7291619
theorem B601239 : Blo 599292 601239 := bstep (se 1 (by rfl) ⟨450929, by rfl⟩ : syracuseStep 601239 = 901859) B901859
theorem B601259 : Blo 599292 601259 := bstep (se 1 (by rfl) ⟨450944, by rfl⟩ : syracuseStep 601259 = 901889) B901889
theorem B1354931 : Blo 599292 1354931 := bstep (se 1 (by rfl) ⟨1016198, by rfl⟩ : syracuseStep 1354931 = 2032397) B2032397
theorem B8694965 : Blo 599292 8694965 := bstep (se 5 (by rfl) ⟨407576, by rfl⟩ : syracuseStep 8694965 = 815153) B815153
theorem B601271 : Blo 599292 601271 := bstep (se 1 (by rfl) ⟨450953, by rfl⟩ : syracuseStep 601271 = 901907) B901907
theorem B601291 : Blo 599292 601291 := bstep (se 1 (by rfl) ⟨450968, by rfl⟩ : syracuseStep 601291 = 901937) B901937
theorem B601303 : Blo 599292 601303 := bstep (se 1 (by rfl) ⟨450977, by rfl⟩ : syracuseStep 601303 = 901955) B901955
theorem B1354967 : Blo 599292 1354967 := bstep (se 1 (by rfl) ⟨1016225, by rfl⟩ : syracuseStep 1354967 = 2032451) B2032451
theorem B601323 : Blo 599292 601323 := bstep (se 1 (by rfl) ⟨450992, by rfl⟩ : syracuseStep 601323 = 901985) B901985
theorem B601335 : Blo 599292 601335 := bstep (se 1 (by rfl) ⟨451001, by rfl⟩ : syracuseStep 601335 = 902003) B902003
theorem B601355 : Blo 599292 601355 := bstep (se 1 (by rfl) ⟨451016, by rfl⟩ : syracuseStep 601355 = 902033) B902033
theorem B1518871 : Blo 599292 1518871 := bstep (se 1 (by rfl) ⟨1139153, by rfl⟩ : syracuseStep 1518871 = 2278307) B2278307
theorem B601367 : Blo 599292 601367 := bstep (se 1 (by rfl) ⟨451025, by rfl⟩ : syracuseStep 601367 = 902051) B902051
theorem B601387 : Blo 599292 601387 := bstep (se 1 (by rfl) ⟨451040, by rfl⟩ : syracuseStep 601387 = 902081) B902081
theorem B601399 : Blo 599292 601399 := bstep (se 1 (by rfl) ⟨451049, by rfl⟩ : syracuseStep 601399 = 902099) B902099
theorem B601419 : Blo 599292 601419 := bstep (se 1 (by rfl) ⟨451064, by rfl⟩ : syracuseStep 601419 = 902129) B902129
theorem B601431 : Blo 599292 601431 := bstep (se 1 (by rfl) ⟨451073, by rfl⟩ : syracuseStep 601431 = 902147) B902147
theorem B601451 : Blo 599292 601451 := bstep (se 1 (by rfl) ⟨451088, by rfl⟩ : syracuseStep 601451 = 902177) B902177
theorem B601463 : Blo 599292 601463 := bstep (se 1 (by rfl) ⟨451097, by rfl⟩ : syracuseStep 601463 = 902195) B902195
theorem B961931 : Blo 599292 961931 := bstep (se 1 (by rfl) ⟨721448, by rfl⟩ : syracuseStep 961931 = 1442897) B1442897
theorem B601483 : Blo 599292 601483 := bstep (se 1 (by rfl) ⟨451112, by rfl⟩ : syracuseStep 601483 = 902225) B902225
theorem B1355147 : Blo 599292 1355147 := bstep (se 1 (by rfl) ⟨1016360, by rfl⟩ : syracuseStep 1355147 = 2032721) B2032721
theorem B601495 : Blo 599292 601495 := bstep (se 1 (by rfl) ⟨451121, by rfl⟩ : syracuseStep 601495 = 902243) B902243
theorem B1060249 : Blo 599292 1060249 := bstep (se 2 (by rfl) ⟨397593, by rfl⟩ : syracuseStep 1060249 = 795187) B795187
theorem B601515 : Blo 599292 601515 := bstep (se 1 (by rfl) ⟨451136, by rfl⟩ : syracuseStep 601515 = 902273) B902273
theorem B601527 : Blo 599292 601527 := bstep (se 1 (by rfl) ⟨451145, by rfl⟩ : syracuseStep 601527 = 902291) B902291
theorem B1355201 : Blo 599292 1355201 := bstep (se 2 (by rfl) ⟨508200, by rfl⟩ : syracuseStep 1355201 = 1016401) B1016401
theorem B601547 : Blo 599292 601547 := bstep (se 1 (by rfl) ⟨451160, by rfl⟩ : syracuseStep 601547 = 902321) B902321
theorem B601559 : Blo 599292 601559 := bstep (se 1 (by rfl) ⟨451169, by rfl⟩ : syracuseStep 601559 = 902339) B902339
theorem B601579 : Blo 599292 601579 := bstep (se 1 (by rfl) ⟨451184, by rfl⟩ : syracuseStep 601579 = 902369) B902369
theorem B601591 : Blo 599292 601591 := bstep (se 1 (by rfl) ⟨451193, by rfl⟩ : syracuseStep 601591 = 902387) B902387
theorem B601611 : Blo 599292 601611 := bstep (se 1 (by rfl) ⟨451208, by rfl⟩ : syracuseStep 601611 = 902417) B902417
theorem B601623 : Blo 599292 601623 := bstep (se 1 (by rfl) ⟨451217, by rfl⟩ : syracuseStep 601623 = 902435) B902435
theorem B601643 : Blo 599292 601643 := bstep (se 1 (by rfl) ⟨451232, by rfl⟩ : syracuseStep 601643 = 902465) B902465
theorem B601655 : Blo 599292 601655 := bstep (se 1 (by rfl) ⟨451241, by rfl⟩ : syracuseStep 601655 = 902483) B902483
theorem B601675 : Blo 599292 601675 := bstep (se 1 (by rfl) ⟨451256, by rfl⟩ : syracuseStep 601675 = 902513) B902513
theorem B601687 : Blo 599292 601687 := bstep (se 1 (by rfl) ⟨451265, by rfl⟩ : syracuseStep 601687 = 902531) B902531
theorem B4402781 : Blo 599292 4402781 := bstep (se 3 (by rfl) ⟨825521, by rfl⟩ : syracuseStep 4402781 = 1651043) B1651043
theorem B601707 : Blo 599292 601707 := bstep (se 1 (by rfl) ⟨451280, by rfl⟩ : syracuseStep 601707 = 902561) B902561
theorem B601719 : Blo 599292 601719 := bstep (se 1 (by rfl) ⟨451289, by rfl⟩ : syracuseStep 601719 = 902579) B902579
theorem B601739 : Blo 599292 601739 := bstep (se 1 (by rfl) ⟨451304, by rfl⟩ : syracuseStep 601739 = 902609) B902609
theorem B601751 : Blo 599292 601751 := bstep (se 1 (by rfl) ⟨451313, by rfl⟩ : syracuseStep 601751 = 902627) B902627
theorem B1355417 : Blo 599292 1355417 := bstep (se 2 (by rfl) ⟨508281, by rfl⟩ : syracuseStep 1355417 = 1016563) B1016563
theorem B601771 : Blo 599292 601771 := bstep (se 1 (by rfl) ⟨451328, by rfl⟩ : syracuseStep 601771 = 902657) B902657
theorem B601783 : Blo 599292 601783 := bstep (se 1 (by rfl) ⟨451337, by rfl⟩ : syracuseStep 601783 = 902675) B902675
theorem B1519307 : Blo 599292 1519307 := bstep (se 1 (by rfl) ⟨1139480, by rfl⟩ : syracuseStep 1519307 = 2278961) B2278961
theorem B601803 : Blo 599292 601803 := bstep (se 1 (by rfl) ⟨451352, by rfl⟩ : syracuseStep 601803 = 902705) B902705
theorem B962263 : Blo 599292 962263 := bstep (se 1 (by rfl) ⟨721697, by rfl⟩ : syracuseStep 962263 = 1443395) B1443395
theorem B601815 : Blo 599292 601815 := bstep (se 1 (by rfl) ⟨451361, by rfl⟩ : syracuseStep 601815 = 902723) B902723
theorem B601835 : Blo 599292 601835 := bstep (se 1 (by rfl) ⟨451376, by rfl⟩ : syracuseStep 601835 = 902753) B902753
theorem B1355507 : Blo 599292 1355507 := bstep (se 1 (by rfl) ⟨1016630, by rfl⟩ : syracuseStep 1355507 = 2033261) B2033261
theorem B601847 : Blo 599292 601847 := bstep (se 1 (by rfl) ⟨451385, by rfl⟩ : syracuseStep 601847 = 902771) B902771
theorem B601867 : Blo 599292 601867 := bstep (se 1 (by rfl) ⟨451400, by rfl⟩ : syracuseStep 601867 = 902801) B902801
theorem B3419921 : Blo 599292 3419921 := bstep (se 2 (by rfl) ⟨1282470, by rfl⟩ : syracuseStep 3419921 = 2564941) B2564941
theorem B601879 : Blo 599292 601879 := bstep (se 1 (by rfl) ⟨451409, by rfl⟩ : syracuseStep 601879 = 902819) B902819
theorem B1355543 : Blo 599292 1355543 := bstep (se 1 (by rfl) ⟨1016657, by rfl⟩ : syracuseStep 1355543 = 2033315) B2033315
theorem B601899 : Blo 599292 601899 := bstep (se 1 (by rfl) ⟨451424, by rfl⟩ : syracuseStep 601899 = 902849) B902849
theorem B601911 : Blo 599292 601911 := bstep (se 1 (by rfl) ⟨451433, by rfl⟩ : syracuseStep 601911 = 902867) B902867
theorem B601931 : Blo 599292 601931 := bstep (se 1 (by rfl) ⟨451448, by rfl⟩ : syracuseStep 601931 = 902897) B902897
theorem B601943 : Blo 599292 601943 := bstep (se 1 (by rfl) ⟨451457, by rfl⟩ : syracuseStep 601943 = 902915) B902915
theorem B2895709 : Blo 599292 2895709 := bstep (se 3 (by rfl) ⟨542945, by rfl⟩ : syracuseStep 2895709 = 1085891) B1085891
theorem B601963 : Blo 599292 601963 := bstep (se 1 (by rfl) ⟨451472, by rfl⟩ : syracuseStep 601963 = 902945) B902945
theorem B601975 : Blo 599292 601975 := bstep (se 1 (by rfl) ⟨451481, by rfl⟩ : syracuseStep 601975 = 902963) B902963
theorem B601995 : Blo 599292 601995 := bstep (se 1 (by rfl) ⟨451496, by rfl⟩ : syracuseStep 601995 = 902993) B902993
theorem B602007 : Blo 599292 602007 := bstep (se 1 (by rfl) ⟨451505, by rfl⟩ : syracuseStep 602007 = 903011) B903011
theorem B602027 : Blo 599292 602027 := bstep (se 1 (by rfl) ⟨451520, by rfl⟩ : syracuseStep 602027 = 903041) B903041
theorem B602039 : Blo 599292 602039 := bstep (se 1 (by rfl) ⟨451529, by rfl⟩ : syracuseStep 602039 = 903059) B903059
theorem B602059 : Blo 599292 602059 := bstep (se 1 (by rfl) ⟨451544, by rfl⟩ : syracuseStep 602059 = 903089) B903089
theorem B1355723 : Blo 599292 1355723 := bstep (se 1 (by rfl) ⟨1016792, by rfl⟩ : syracuseStep 1355723 = 2033585) B2033585
theorem B602071 : Blo 599292 602071 := bstep (se 1 (by rfl) ⟨451553, by rfl⟩ : syracuseStep 602071 = 903107) B903107
theorem B602091 : Blo 599292 602091 := bstep (se 1 (by rfl) ⟨451568, by rfl⟩ : syracuseStep 602091 = 903137) B903137
theorem B602103 : Blo 599292 602103 := bstep (se 1 (by rfl) ⟨451577, by rfl⟩ : syracuseStep 602103 = 903155) B903155
theorem B1355777 : Blo 599292 1355777 := bstep (se 2 (by rfl) ⟨508416, by rfl⟩ : syracuseStep 1355777 = 1016833) B1016833
theorem B602123 : Blo 599292 602123 := bstep (se 1 (by rfl) ⟨451592, by rfl⟩ : syracuseStep 602123 = 903185) B903185
theorem B602135 : Blo 599292 602135 := bstep (se 1 (by rfl) ⟨451601, by rfl⟩ : syracuseStep 602135 = 903203) B903203
theorem B602155 : Blo 599292 602155 := bstep (se 1 (by rfl) ⟨451616, by rfl⟩ : syracuseStep 602155 = 903233) B903233
theorem B602167 : Blo 599292 602167 := bstep (se 1 (by rfl) ⟨451625, by rfl⟩ : syracuseStep 602167 = 903251) B903251
theorem B1519681 : Blo 599292 1519681 := bstep (se 2 (by rfl) ⟨569880, by rfl⟩ : syracuseStep 1519681 = 1139761) B1139761
theorem B2568257 : Blo 599292 2568257 := bstep (se 2 (by rfl) ⟨963096, by rfl⟩ : syracuseStep 2568257 = 1926193) B1926193
theorem B602187 : Blo 599292 602187 := bstep (se 1 (by rfl) ⟨451640, by rfl⟩ : syracuseStep 602187 = 903281) B903281
theorem B602199 : Blo 599292 602199 := bstep (se 1 (by rfl) ⟨451649, by rfl⟩ : syracuseStep 602199 = 903299) B903299
theorem B7319645 : Blo 599292 7319645 := bstep (se 3 (by rfl) ⟨1372433, by rfl⟩ : syracuseStep 7319645 = 2744867) B2744867
theorem B602219 : Blo 599292 602219 := bstep (se 1 (by rfl) ⟨451664, by rfl⟩ : syracuseStep 602219 = 903329) B903329
theorem B602231 : Blo 599292 602231 := bstep (se 1 (by rfl) ⟨451673, by rfl⟩ : syracuseStep 602231 = 903347) B903347
theorem B602251 : Blo 599292 602251 := bstep (se 1 (by rfl) ⟨451688, by rfl⟩ : syracuseStep 602251 = 903377) B903377
theorem B602263 : Blo 599292 602263 := bstep (se 1 (by rfl) ⟨451697, by rfl⟩ : syracuseStep 602263 = 903395) B903395
theorem B602283 : Blo 599292 602283 := bstep (se 1 (by rfl) ⟨451712, by rfl⟩ : syracuseStep 602283 = 903425) B903425
theorem B602295 : Blo 599292 602295 := bstep (se 1 (by rfl) ⟨451721, by rfl⟩ : syracuseStep 602295 = 903443) B903443
theorem B602315 : Blo 599292 602315 := bstep (se 1 (by rfl) ⟨451736, by rfl⟩ : syracuseStep 602315 = 903473) B903473
theorem B602327 : Blo 599292 602327 := bstep (se 1 (by rfl) ⟨451745, by rfl⟩ : syracuseStep 602327 = 903491) B903491
theorem B3420377 : Blo 599292 3420377 := bstep (se 2 (by rfl) ⟨1282641, by rfl⟩ : syracuseStep 3420377 = 2565283) B2565283
theorem B1355993 : Blo 599292 1355993 := bstep (se 2 (by rfl) ⟨508497, by rfl⟩ : syracuseStep 1355993 = 1016995) B1016995
theorem B602347 : Blo 599292 602347 := bstep (se 1 (by rfl) ⟨451760, by rfl⟩ : syracuseStep 602347 = 903521) B903521
theorem B602359 : Blo 599292 602359 := bstep (se 1 (by rfl) ⟨451769, by rfl⟩ : syracuseStep 602359 = 903539) B903539
theorem B602379 : Blo 599292 602379 := bstep (se 1 (by rfl) ⟨451784, by rfl⟩ : syracuseStep 602379 = 903569) B903569
theorem B602391 : Blo 599292 602391 := bstep (se 1 (by rfl) ⟨451793, by rfl⟩ : syracuseStep 602391 = 903587) B903587
theorem B602411 : Blo 599292 602411 := bstep (se 1 (by rfl) ⟨451808, by rfl⟩ : syracuseStep 602411 = 903617) B903617
theorem B1356083 : Blo 599292 1356083 := bstep (se 1 (by rfl) ⟨1017062, by rfl⟩ : syracuseStep 1356083 = 2034125) B2034125
theorem B602423 : Blo 599292 602423 := bstep (se 1 (by rfl) ⟨451817, by rfl⟩ : syracuseStep 602423 = 903635) B903635
theorem B1716545 : Blo 599292 1716545 := bstep (se 2 (by rfl) ⟨643704, by rfl⟩ : syracuseStep 1716545 = 1287409) B1287409
theorem B602443 : Blo 599292 602443 := bstep (se 1 (by rfl) ⟨451832, by rfl⟩ : syracuseStep 602443 = 903665) B903665
theorem B602455 : Blo 599292 602455 := bstep (se 1 (by rfl) ⟨451841, by rfl⟩ : syracuseStep 602455 = 903683) B903683
theorem B1356119 : Blo 599292 1356119 := bstep (se 1 (by rfl) ⟨1017089, by rfl⟩ : syracuseStep 1356119 = 2034179) B2034179
theorem B602475 : Blo 599292 602475 := bstep (se 1 (by rfl) ⟨451856, by rfl⟩ : syracuseStep 602475 = 903713) B903713
theorem B602487 : Blo 599292 602487 := bstep (se 1 (by rfl) ⟨451865, by rfl⟩ : syracuseStep 602487 = 903731) B903731
theorem B4567427 : Blo 599292 4567427 := bstep (se 1 (by rfl) ⟨3425570, by rfl⟩ : syracuseStep 4567427 = 6851141) B6851141
theorem B602507 : Blo 599292 602507 := bstep (se 1 (by rfl) ⟨451880, by rfl⟩ : syracuseStep 602507 = 903761) B903761
theorem B602519 : Blo 599292 602519 := bstep (se 1 (by rfl) ⟨451889, by rfl⟩ : syracuseStep 602519 = 903779) B903779
theorem B602539 : Blo 599292 602539 := bstep (se 1 (by rfl) ⟨451904, by rfl⟩ : syracuseStep 602539 = 903809) B903809
theorem B2896307 : Blo 599292 2896307 := bstep (se 1 (by rfl) ⟨2172230, by rfl⟩ : syracuseStep 2896307 = 4344461) B4344461
theorem B1716659 : Blo 599292 1716659 := bstep (se 1 (by rfl) ⟨1287494, by rfl⟩ : syracuseStep 1716659 = 2574989) B2574989
theorem B602551 : Blo 599292 602551 := bstep (se 1 (by rfl) ⟨451913, by rfl⟩ : syracuseStep 602551 = 903827) B903827
theorem B602571 : Blo 599292 602571 := bstep (se 1 (by rfl) ⟨451928, by rfl⟩ : syracuseStep 602571 = 903857) B903857
theorem B602583 : Blo 599292 602583 := bstep (se 1 (by rfl) ⟨451937, by rfl⟩ : syracuseStep 602583 = 903875) B903875
theorem B602603 : Blo 599292 602603 := bstep (se 1 (by rfl) ⟨451952, by rfl⟩ : syracuseStep 602603 = 903905) B903905
theorem B602615 : Blo 599292 602615 := bstep (se 1 (by rfl) ⟨451961, by rfl⟩ : syracuseStep 602615 = 903923) B903923
theorem B602635 : Blo 599292 602635 := bstep (se 1 (by rfl) ⟨451976, by rfl⟩ : syracuseStep 602635 = 903953) B903953
theorem B1356299 : Blo 599292 1356299 := bstep (se 1 (by rfl) ⟨1017224, by rfl⟩ : syracuseStep 1356299 = 2034449) B2034449
theorem B602647 : Blo 599292 602647 := bstep (se 1 (by rfl) ⟨451985, by rfl⟩ : syracuseStep 602647 = 903971) B903971
theorem B6861347 : Blo 599292 6861347 := bstep (se 1 (by rfl) ⟨5146010, by rfl⟩ : syracuseStep 6861347 = 10292021) B10292021
theorem B602667 : Blo 599292 602667 := bstep (se 1 (by rfl) ⟨452000, by rfl⟩ : syracuseStep 602667 = 904001) B904001
theorem B602679 : Blo 599292 602679 := bstep (se 1 (by rfl) ⟨452009, by rfl⟩ : syracuseStep 602679 = 904019) B904019
theorem B1356353 : Blo 599292 1356353 := bstep (se 2 (by rfl) ⟨508632, by rfl⟩ : syracuseStep 1356353 = 1017265) B1017265
theorem B602699 : Blo 599292 602699 := bstep (se 1 (by rfl) ⟨452024, by rfl⟩ : syracuseStep 602699 = 904049) B904049
theorem B602711 : Blo 599292 602711 := bstep (se 1 (by rfl) ⟨452033, by rfl⟩ : syracuseStep 602711 = 904067) B904067
theorem B963161 : Blo 599292 963161 := bstep (se 2 (by rfl) ⟨361185, by rfl⟩ : syracuseStep 963161 = 722371) B722371
theorem B602731 : Blo 599292 602731 := bstep (se 1 (by rfl) ⟨452048, by rfl⟩ : syracuseStep 602731 = 904097) B904097
theorem B602743 : Blo 599292 602743 := bstep (se 1 (by rfl) ⟨452057, by rfl⟩ : syracuseStep 602743 = 904115) B904115
theorem B602763 : Blo 599292 602763 := bstep (se 1 (by rfl) ⟨452072, by rfl⟩ : syracuseStep 602763 = 904145) B904145
theorem B1520279 : Blo 599292 1520279 := bstep (se 1 (by rfl) ⟨1140209, by rfl⟩ : syracuseStep 1520279 = 2280419) B2280419
theorem B602775 : Blo 599292 602775 := bstep (se 1 (by rfl) ⟨452081, by rfl⟩ : syracuseStep 602775 = 904163) B904163
theorem B602795 : Blo 599292 602795 := bstep (se 1 (by rfl) ⟨452096, by rfl⟩ : syracuseStep 602795 = 904193) B904193
theorem B2437805 : Blo 599292 2437805 := bstep (se 3 (by rfl) ⟨457088, by rfl⟩ : syracuseStep 2437805 = 914177) B914177
theorem B602807 : Blo 599292 602807 := bstep (se 1 (by rfl) ⟨452105, by rfl⟩ : syracuseStep 602807 = 904211) B904211
theorem B602827 : Blo 599292 602827 := bstep (se 1 (by rfl) ⟨452120, by rfl⟩ : syracuseStep 602827 = 904241) B904241
theorem B602839 : Blo 599292 602839 := bstep (se 1 (by rfl) ⟨452129, by rfl⟩ : syracuseStep 602839 = 904259) B904259
theorem B602859 : Blo 599292 602859 := bstep (se 1 (by rfl) ⟨452144, by rfl⟩ : syracuseStep 602859 = 904289) B904289
theorem B602871 : Blo 599292 602871 := bstep (se 1 (by rfl) ⟨452153, by rfl⟩ : syracuseStep 602871 = 904307) B904307
theorem B602891 : Blo 599292 602891 := bstep (se 1 (by rfl) ⟨452168, by rfl⟩ : syracuseStep 602891 = 904337) B904337
theorem B602903 : Blo 599292 602903 := bstep (se 1 (by rfl) ⟨452177, by rfl⟩ : syracuseStep 602903 = 904355) B904355
theorem B963353 : Blo 599292 963353 := bstep (se 2 (by rfl) ⟨361257, by rfl⟩ : syracuseStep 963353 = 722515) B722515
theorem B1356569 : Blo 599292 1356569 := bstep (se 2 (by rfl) ⟨508713, by rfl⟩ : syracuseStep 1356569 = 1017427) B1017427
theorem B602923 : Blo 599292 602923 := bstep (se 1 (by rfl) ⟨452192, by rfl⟩ : syracuseStep 602923 = 904385) B904385
theorem B602935 : Blo 599292 602935 := bstep (se 1 (by rfl) ⟨452201, by rfl⟩ : syracuseStep 602935 = 904403) B904403
theorem B602955 : Blo 599292 602955 := bstep (se 1 (by rfl) ⟨452216, by rfl⟩ : syracuseStep 602955 = 904433) B904433
theorem B602967 : Blo 599292 602967 := bstep (se 1 (by rfl) ⟨452225, by rfl⟩ : syracuseStep 602967 = 904451) B904451
theorem B602987 : Blo 599292 602987 := bstep (se 1 (by rfl) ⟨452240, by rfl⟩ : syracuseStep 602987 = 904481) B904481
theorem B1356659 : Blo 599292 1356659 := bstep (se 1 (by rfl) ⟨1017494, by rfl⟩ : syracuseStep 1356659 = 2034989) B2034989
theorem B602999 : Blo 599292 602999 := bstep (se 1 (by rfl) ⟨452249, by rfl⟩ : syracuseStep 602999 = 904499) B904499
theorem B603019 : Blo 599292 603019 := bstep (se 1 (by rfl) ⟨452264, by rfl⟩ : syracuseStep 603019 = 904529) B904529
theorem B1356695 : Blo 599292 1356695 := bstep (se 1 (by rfl) ⟨1017521, by rfl⟩ : syracuseStep 1356695 = 2035043) B2035043
theorem B603031 : Blo 599292 603031 := bstep (se 1 (by rfl) ⟨452273, by rfl⟩ : syracuseStep 603031 = 904547) B904547
theorem B603051 : Blo 599292 603051 := bstep (se 1 (by rfl) ⟨452288, by rfl⟩ : syracuseStep 603051 = 904577) B904577
theorem B603063 : Blo 599292 603063 := bstep (se 1 (by rfl) ⟨452297, by rfl⟩ : syracuseStep 603063 = 904595) B904595
theorem B603083 : Blo 599292 603083 := bstep (se 1 (by rfl) ⟨452312, by rfl⟩ : syracuseStep 603083 = 904625) B904625
theorem B603095 : Blo 599292 603095 := bstep (se 1 (by rfl) ⟨452321, by rfl⟩ : syracuseStep 603095 = 904643) B904643
theorem B2634713 : Blo 599292 2634713 := bstep (se 2 (by rfl) ⟨988017, by rfl⟩ : syracuseStep 2634713 = 1976035) B1976035
theorem B603115 : Blo 599292 603115 := bstep (se 1 (by rfl) ⟨452336, by rfl⟩ : syracuseStep 603115 = 904673) B904673
theorem B603127 : Blo 599292 603127 := bstep (se 1 (by rfl) ⟨452345, by rfl⟩ : syracuseStep 603127 = 904691) B904691
theorem B603147 : Blo 599292 603147 := bstep (se 1 (by rfl) ⟨452360, by rfl⟩ : syracuseStep 603147 = 904721) B904721
theorem B603159 : Blo 599292 603159 := bstep (se 1 (by rfl) ⟨452369, by rfl⟩ : syracuseStep 603159 = 904739) B904739
theorem B603179 : Blo 599292 603179 := bstep (se 1 (by rfl) ⟨452384, by rfl⟩ : syracuseStep 603179 = 904769) B904769
theorem B603191 : Blo 599292 603191 := bstep (se 1 (by rfl) ⟨452393, by rfl⟩ : syracuseStep 603191 = 904787) B904787
theorem B1356875 : Blo 599292 1356875 := bstep (se 1 (by rfl) ⟨1017656, by rfl⟩ : syracuseStep 1356875 = 2035313) B2035313
theorem B603211 : Blo 599292 603211 := bstep (se 1 (by rfl) ⟨452408, by rfl⟩ : syracuseStep 603211 = 904817) B904817
theorem B603223 : Blo 599292 603223 := bstep (se 1 (by rfl) ⟨452417, by rfl⟩ : syracuseStep 603223 = 904835) B904835
theorem B603243 : Blo 599292 603243 := bstep (se 1 (by rfl) ⟨452432, by rfl⟩ : syracuseStep 603243 = 904865) B904865
theorem B603255 : Blo 599292 603255 := bstep (se 1 (by rfl) ⟨452441, by rfl⟩ : syracuseStep 603255 = 904883) B904883
theorem B1356929 : Blo 599292 1356929 := bstep (se 2 (by rfl) ⟨508848, by rfl⟩ : syracuseStep 1356929 = 1017697) B1017697
theorem B603275 : Blo 599292 603275 := bstep (se 1 (by rfl) ⟨452456, by rfl⟩ : syracuseStep 603275 = 904913) B904913
theorem B603287 : Blo 599292 603287 := bstep (se 1 (by rfl) ⟨452465, by rfl⟩ : syracuseStep 603287 = 904931) B904931
theorem B3650777 : Blo 599292 3650777 := bstep (se 2 (by rfl) ⟨1369041, by rfl⟩ : syracuseStep 3650777 = 2738083) B2738083
theorem B1357145 : Blo 599292 1357145 := bstep (se 2 (by rfl) ⟨508929, by rfl⟩ : syracuseStep 1357145 = 1017859) B1017859
theorem B1357235 : Blo 599292 1357235 := bstep (se 1 (by rfl) ⟨1017926, by rfl⟩ : syracuseStep 1357235 = 2035853) B2035853
theorem B1521089 : Blo 599292 1521089 := bstep (se 2 (by rfl) ⟨570408, by rfl⟩ : syracuseStep 1521089 = 1140817) B1140817
theorem B1357271 : Blo 599292 1357271 := bstep (se 1 (by rfl) ⟨1017953, by rfl⟩ : syracuseStep 1357271 = 2035907) B2035907
theorem B2569931 : Blo 599292 2569931 := bstep (se 1 (by rfl) ⟨1927448, by rfl⟩ : syracuseStep 2569931 = 3854897) B3854897
theorem B1128179 : Blo 599292 1128179 := bstep (se 1 (by rfl) ⟨846134, by rfl⟩ : syracuseStep 1128179 = 1692269) B1692269
theorem B898955 : Blo 599292 898955 := bstep (se 1 (by rfl) ⟨674216, by rfl⟩ : syracuseStep 898955 = 1348433) B1348433
theorem B898967 : Blo 599292 898967 := bstep (se 1 (by rfl) ⟨674225, by rfl⟩ : syracuseStep 898967 = 1348451) B1348451
theorem B899033 : Blo 599292 899033 := bstep (se 2 (by rfl) ⟨337137, by rfl⟩ : syracuseStep 899033 = 674275) B674275
theorem B1521625 : Blo 599292 1521625 := bstep (se 2 (by rfl) ⟨570609, by rfl⟩ : syracuseStep 1521625 = 1141219) B1141219
theorem B899147 : Blo 599292 899147 := bstep (se 1 (by rfl) ⟨674360, by rfl⟩ : syracuseStep 899147 = 1348721) B1348721
theorem B899159 : Blo 599292 899159 := bstep (se 1 (by rfl) ⟨674369, by rfl⟩ : syracuseStep 899159 = 1348739) B1348739
theorem B899225 : Blo 599292 899225 := bstep (se 2 (by rfl) ⟨337209, by rfl⟩ : syracuseStep 899225 = 674419) B674419
theorem B15644933 : Blo 599292 15644933 := bstep (se 4 (by rfl) ⟨1466712, by rfl⟩ : syracuseStep 15644933 = 2933425) B2933425
theorem B899339 : Blo 599292 899339 := bstep (se 1 (by rfl) ⟨674504, by rfl⟩ : syracuseStep 899339 = 1349009) B1349009
theorem B899351 : Blo 599292 899351 := bstep (se 1 (by rfl) ⟨674513, by rfl⟩ : syracuseStep 899351 = 1349027) B1349027
theorem B899417 : Blo 599292 899417 := bstep (se 2 (by rfl) ⟨337281, by rfl⟩ : syracuseStep 899417 = 674563) B674563
theorem B899531 : Blo 599292 899531 := bstep (se 1 (by rfl) ⟨674648, by rfl⟩ : syracuseStep 899531 = 1349297) B1349297
theorem B899543 : Blo 599292 899543 := bstep (se 1 (by rfl) ⟨674657, by rfl⟩ : syracuseStep 899543 = 1349315) B1349315
theorem B2570717 : Blo 599292 2570717 := bstep (se 3 (by rfl) ⟨482009, by rfl⟩ : syracuseStep 2570717 = 964019) B964019
theorem B899609 : Blo 599292 899609 := bstep (se 2 (by rfl) ⟨337353, by rfl⟩ : syracuseStep 899609 = 674707) B674707
theorem B899723 : Blo 599292 899723 := bstep (se 1 (by rfl) ⟨674792, by rfl⟩ : syracuseStep 899723 = 1349585) B1349585
theorem B899735 : Blo 599292 899735 := bstep (se 1 (by rfl) ⟨674801, by rfl⟩ : syracuseStep 899735 = 1349603) B1349603
theorem B899801 : Blo 599292 899801 := bstep (se 2 (by rfl) ⟨337425, by rfl⟩ : syracuseStep 899801 = 674851) B674851
theorem B899915 : Blo 599292 899915 := bstep (se 1 (by rfl) ⟨674936, by rfl⟩ : syracuseStep 899915 = 1349873) B1349873
theorem B3652427 : Blo 599292 3652427 := bstep (se 1 (by rfl) ⟨2739320, by rfl⟩ : syracuseStep 3652427 = 5478641) B5478641
theorem B899927 : Blo 599292 899927 := bstep (se 1 (by rfl) ⟨674945, by rfl⟩ : syracuseStep 899927 = 1349891) B1349891
theorem B899993 : Blo 599292 899993 := bstep (se 2 (by rfl) ⟨337497, by rfl⟩ : syracuseStep 899993 = 674995) B674995
theorem B900107 : Blo 599292 900107 := bstep (se 1 (by rfl) ⟨675080, by rfl⟩ : syracuseStep 900107 = 1350161) B1350161
theorem B900119 : Blo 599292 900119 := bstep (se 1 (by rfl) ⟨675089, by rfl⟩ : syracuseStep 900119 = 1350179) B1350179
theorem B1621043 : Blo 599292 1621043 := bstep (se 1 (by rfl) ⟨1215782, by rfl⟩ : syracuseStep 1621043 = 2431565) B2431565
theorem B1522739 : Blo 599292 1522739 := bstep (se 1 (by rfl) ⟨1142054, by rfl⟩ : syracuseStep 1522739 = 2284109) B2284109
theorem B900185 : Blo 599292 900185 := bstep (se 2 (by rfl) ⟨337569, by rfl⟩ : syracuseStep 900185 = 675139) B675139
theorem B2276531 : Blo 599292 2276531 := bstep (se 1 (by rfl) ⟨1707398, by rfl⟩ : syracuseStep 2276531 = 3414797) B3414797
theorem B2276545 : Blo 599292 2276545 := bstep (se 2 (by rfl) ⟨853704, by rfl⟩ : syracuseStep 2276545 = 1707409) B1707409
theorem B2440385 : Blo 599292 2440385 := bstep (se 2 (by rfl) ⟨915144, by rfl⟩ : syracuseStep 2440385 = 1830289) B1830289
theorem B900299 : Blo 599292 900299 := bstep (se 1 (by rfl) ⟨675224, by rfl⟩ : syracuseStep 900299 = 1350449) B1350449
theorem B900311 : Blo 599292 900311 := bstep (se 1 (by rfl) ⟨675233, by rfl⟩ : syracuseStep 900311 = 1350467) B1350467
theorem B900377 : Blo 599292 900377 := bstep (se 2 (by rfl) ⟨337641, by rfl⟩ : syracuseStep 900377 = 675283) B675283
theorem B1523033 : Blo 599292 1523033 := bstep (se 2 (by rfl) ⟨571137, by rfl⟩ : syracuseStep 1523033 = 1142275) B1142275
theorem B3849565 : Blo 599292 3849565 := bstep (se 3 (by rfl) ⟨721793, by rfl⟩ : syracuseStep 3849565 = 1443587) B1443587
theorem B900491 : Blo 599292 900491 := bstep (se 1 (by rfl) ⟨675368, by rfl⟩ : syracuseStep 900491 = 1350737) B1350737
theorem B900503 : Blo 599292 900503 := bstep (se 1 (by rfl) ⟨675377, by rfl⟩ : syracuseStep 900503 = 1350755) B1350755
theorem B900569 : Blo 599292 900569 := bstep (se 2 (by rfl) ⟨337713, by rfl⟩ : syracuseStep 900569 = 675427) B675427
theorem B3259921 : Blo 599292 3259921 := bstep (se 2 (by rfl) ⟨1222470, by rfl⟩ : syracuseStep 3259921 = 2444941) B2444941
theorem B900683 : Blo 599292 900683 := bstep (se 1 (by rfl) ⟨675512, by rfl⟩ : syracuseStep 900683 = 1351025) B1351025
theorem B900695 : Blo 599292 900695 := bstep (se 1 (by rfl) ⟨675521, by rfl⟩ : syracuseStep 900695 = 1351043) B1351043
theorem B900761 : Blo 599292 900761 := bstep (se 2 (by rfl) ⟨337785, by rfl⟩ : syracuseStep 900761 = 675571) B675571
theorem B4570829 : Blo 599292 4570829 := bstep (se 3 (by rfl) ⟨857030, by rfl⟩ : syracuseStep 4570829 = 1714061) B1714061
theorem B900875 : Blo 599292 900875 := bstep (se 1 (by rfl) ⟨675656, by rfl⟩ : syracuseStep 900875 = 1351313) B1351313
theorem B2572049 : Blo 599292 2572049 := bstep (se 2 (by rfl) ⟨964518, by rfl⟩ : syracuseStep 2572049 = 1929037) B1929037
theorem B900887 : Blo 599292 900887 := bstep (se 1 (by rfl) ⟨675665, by rfl⟩ : syracuseStep 900887 = 1351331) B1351331
theorem B8666945 : Blo 599292 8666945 := bstep (se 2 (by rfl) ⟨3250104, by rfl⟩ : syracuseStep 8666945 = 6500209) B6500209
theorem B900953 : Blo 599292 900953 := bstep (se 2 (by rfl) ⟨337857, by rfl⟩ : syracuseStep 900953 = 675715) B675715
theorem B901067 : Blo 599292 901067 := bstep (se 1 (by rfl) ⟨675800, by rfl⟩ : syracuseStep 901067 = 1351601) B1351601
theorem B901079 : Blo 599292 901079 := bstep (se 1 (by rfl) ⟨675809, by rfl⟩ : syracuseStep 901079 = 1351619) B1351619
theorem B901145 : Blo 599292 901145 := bstep (se 2 (by rfl) ⟨337929, by rfl⟩ : syracuseStep 901145 = 675859) B675859
theorem B901259 : Blo 599292 901259 := bstep (se 1 (by rfl) ⟨675944, by rfl⟩ : syracuseStep 901259 = 1351889) B1351889
theorem B901271 : Blo 599292 901271 := bstep (se 1 (by rfl) ⟨675953, by rfl⟩ : syracuseStep 901271 = 1351907) B1351907
theorem B8667287 : Blo 599292 8667287 := bstep (se 1 (by rfl) ⟨6500465, by rfl⟩ : syracuseStep 8667287 = 13000931) B13000931
theorem B4571315 : Blo 599292 4571315 := bstep (se 1 (by rfl) ⟨3428486, by rfl⟩ : syracuseStep 4571315 = 6856973) B6856973
theorem B901337 : Blo 599292 901337 := bstep (se 2 (by rfl) ⟨338001, by rfl⟩ : syracuseStep 901337 = 676003) B676003
theorem B901451 : Blo 599292 901451 := bstep (se 1 (by rfl) ⟨676088, by rfl⟩ : syracuseStep 901451 = 1352177) B1352177
theorem B901463 : Blo 599292 901463 := bstep (se 1 (by rfl) ⟨676097, by rfl⟩ : syracuseStep 901463 = 1352195) B1352195
theorem B2441603 : Blo 599292 2441603 := bstep (se 1 (by rfl) ⟨1831202, by rfl⟩ : syracuseStep 2441603 = 3662405) B3662405
theorem B901529 : Blo 599292 901529 := bstep (se 2 (by rfl) ⟨338073, by rfl⟩ : syracuseStep 901529 = 676147) B676147
theorem B901643 : Blo 599292 901643 := bstep (se 1 (by rfl) ⟨676232, by rfl⟩ : syracuseStep 901643 = 1352465) B1352465
theorem B901655 : Blo 599292 901655 := bstep (se 1 (by rfl) ⟨676241, by rfl⟩ : syracuseStep 901655 = 1352483) B1352483
theorem B901721 : Blo 599292 901721 := bstep (se 2 (by rfl) ⟨338145, by rfl⟩ : syracuseStep 901721 = 676291) B676291
theorem B901835 : Blo 599292 901835 := bstep (se 1 (by rfl) ⟨676376, by rfl⟩ : syracuseStep 901835 = 1352753) B1352753
theorem B79086293 : Blo 599292 79086293 := bstep (se 7 (by rfl) ⟨926792, by rfl⟩ : syracuseStep 79086293 = 1853585) B1853585
theorem B901847 : Blo 599292 901847 := bstep (se 1 (by rfl) ⟨676385, by rfl⟩ : syracuseStep 901847 = 1352771) B1352771
theorem B901913 : Blo 599292 901913 := bstep (se 2 (by rfl) ⟨338217, by rfl⟩ : syracuseStep 901913 = 676435) B676435
theorem B902027 : Blo 599292 902027 := bstep (se 1 (by rfl) ⟨676520, by rfl⟩ : syracuseStep 902027 = 1353041) B1353041
theorem B902039 : Blo 599292 902039 := bstep (se 1 (by rfl) ⟨676529, by rfl⟩ : syracuseStep 902039 = 1353059) B1353059
theorem B1524683 : Blo 599292 1524683 := bstep (se 1 (by rfl) ⟨1143512, by rfl⟩ : syracuseStep 1524683 = 2287025) B2287025
theorem B902105 : Blo 599292 902105 := bstep (se 2 (by rfl) ⟨338289, by rfl⟩ : syracuseStep 902105 = 676579) B676579
theorem B2573315 : Blo 599292 2573315 := bstep (se 1 (by rfl) ⟨1929986, by rfl⟩ : syracuseStep 2573315 = 3859973) B3859973
theorem B2278475 : Blo 599292 2278475 := bstep (se 1 (by rfl) ⟨1708856, by rfl⟩ : syracuseStep 2278475 = 3417713) B3417713
theorem B902219 : Blo 599292 902219 := bstep (se 1 (by rfl) ⟨676664, by rfl⟩ : syracuseStep 902219 = 1353329) B1353329
theorem B902231 : Blo 599292 902231 := bstep (se 1 (by rfl) ⟨676673, by rfl⟩ : syracuseStep 902231 = 1353347) B1353347
theorem B2278489 : Blo 599292 2278489 := bstep (se 2 (by rfl) ⟨854433, by rfl⟩ : syracuseStep 2278489 = 1708867) B1708867
theorem B902297 : Blo 599292 902297 := bstep (se 2 (by rfl) ⟨338361, by rfl⟩ : syracuseStep 902297 = 676723) B676723
theorem B902411 : Blo 599292 902411 := bstep (se 1 (by rfl) ⟨676808, by rfl⟩ : syracuseStep 902411 = 1353617) B1353617
theorem B902423 : Blo 599292 902423 := bstep (se 1 (by rfl) ⟨676817, by rfl⟩ : syracuseStep 902423 = 1353635) B1353635
theorem B640343 : Blo 599292 640343 := bstep (se 1 (by rfl) ⟨480257, by rfl⟩ : syracuseStep 640343 = 960515) B960515
theorem B902489 : Blo 599292 902489 := bstep (se 2 (by rfl) ⟨338433, by rfl⟩ : syracuseStep 902489 = 676867) B676867
theorem B902603 : Blo 599292 902603 := bstep (se 1 (by rfl) ⟨676952, by rfl⟩ : syracuseStep 902603 = 1353905) B1353905
theorem B902615 : Blo 599292 902615 := bstep (se 1 (by rfl) ⟨676961, by rfl⟩ : syracuseStep 902615 = 1353923) B1353923
theorem B3425753 : Blo 599292 3425753 := bstep (se 2 (by rfl) ⟨1284657, by rfl⟩ : syracuseStep 3425753 = 2569315) B2569315
theorem B902681 : Blo 599292 902681 := bstep (se 2 (by rfl) ⟨338505, by rfl⟩ : syracuseStep 902681 = 677011) B677011
theorem B4572773 : Blo 599292 4572773 := bstep (se 4 (by rfl) ⟨428697, by rfl⟩ : syracuseStep 4572773 = 857395) B857395
theorem B902795 : Blo 599292 902795 := bstep (se 1 (by rfl) ⟨677096, by rfl⟩ : syracuseStep 902795 = 1354193) B1354193
theorem B902807 : Blo 599292 902807 := bstep (se 1 (by rfl) ⟨677105, by rfl⟩ : syracuseStep 902807 = 1354211) B1354211
theorem B902873 : Blo 599292 902873 := bstep (se 2 (by rfl) ⟨338577, by rfl⟩ : syracuseStep 902873 = 677155) B677155
theorem B902987 : Blo 599292 902987 := bstep (se 1 (by rfl) ⟨677240, by rfl⟩ : syracuseStep 902987 = 1354481) B1354481
theorem B902999 : Blo 599292 902999 := bstep (se 1 (by rfl) ⟨677249, by rfl⟩ : syracuseStep 902999 = 1354499) B1354499
theorem B1525655 : Blo 599292 1525655 := bstep (se 1 (by rfl) ⟨1144241, by rfl⟩ : syracuseStep 1525655 = 2288483) B2288483
theorem B903065 : Blo 599292 903065 := bstep (se 2 (by rfl) ⟨338649, by rfl⟩ : syracuseStep 903065 = 677299) B677299
theorem B903179 : Blo 599292 903179 := bstep (se 1 (by rfl) ⟨677384, by rfl⟩ : syracuseStep 903179 = 1354769) B1354769
theorem B2279447 : Blo 599292 2279447 := bstep (se 1 (by rfl) ⟨1709585, by rfl⟩ : syracuseStep 2279447 = 3419171) B3419171
theorem B903191 : Blo 599292 903191 := bstep (se 1 (by rfl) ⟨677393, by rfl⟩ : syracuseStep 903191 = 1354787) B1354787
theorem B4573259 : Blo 599292 4573259 := bstep (se 1 (by rfl) ⟨3429944, by rfl⟩ : syracuseStep 4573259 = 6859889) B6859889
theorem B903257 : Blo 599292 903257 := bstep (se 2 (by rfl) ⟨338721, by rfl⟩ : syracuseStep 903257 = 677443) B677443
theorem B903371 : Blo 599292 903371 := bstep (se 1 (by rfl) ⟨677528, by rfl⟩ : syracuseStep 903371 = 1355057) B1355057
theorem B903383 : Blo 599292 903383 := bstep (se 1 (by rfl) ⟨677537, by rfl⟩ : syracuseStep 903383 = 1355075) B1355075
theorem B7817477 : Blo 599292 7817477 := bstep (se 4 (by rfl) ⟨732888, by rfl⟩ : syracuseStep 7817477 = 1465777) B1465777
theorem B903449 : Blo 599292 903449 := bstep (se 2 (by rfl) ⟨338793, by rfl⟩ : syracuseStep 903449 = 677587) B677587
theorem B903563 : Blo 599292 903563 := bstep (se 1 (by rfl) ⟨677672, by rfl⟩ : syracuseStep 903563 = 1355345) B1355345
theorem B903575 : Blo 599292 903575 := bstep (se 1 (by rfl) ⟨677681, by rfl⟩ : syracuseStep 903575 = 1355363) B1355363
theorem B903641 : Blo 599292 903641 := bstep (se 2 (by rfl) ⟨338865, by rfl⟩ : syracuseStep 903641 = 677731) B677731
theorem B674347 : Blo 599292 674347 := bstep (se 1 (by rfl) ⟨505760, by rfl⟩ : syracuseStep 674347 = 1011521) B1011521
theorem B1526323 : Blo 599292 1526323 := bstep (se 1 (by rfl) ⟨1144742, by rfl⟩ : syracuseStep 1526323 = 2289485) B2289485
theorem B2443841 : Blo 599292 2443841 := bstep (se 2 (by rfl) ⟨916440, by rfl⟩ : syracuseStep 2443841 = 1832881) B1832881
theorem B903755 : Blo 599292 903755 := bstep (se 1 (by rfl) ⟨677816, by rfl⟩ : syracuseStep 903755 = 1355633) B1355633
theorem B903767 : Blo 599292 903767 := bstep (se 1 (by rfl) ⟨677825, by rfl⟩ : syracuseStep 903767 = 1355651) B1355651
theorem B674455 : Blo 599292 674455 := bstep (se 1 (by rfl) ⟨505841, by rfl⟩ : syracuseStep 674455 = 1011683) B1011683
theorem B903833 : Blo 599292 903833 := bstep (se 2 (by rfl) ⟨338937, by rfl⟩ : syracuseStep 903833 = 677875) B677875
theorem B1526465 : Blo 599292 1526465 := bstep (se 2 (by rfl) ⟨572424, by rfl⟩ : syracuseStep 1526465 = 1144849) B1144849
theorem B903947 : Blo 599292 903947 := bstep (se 1 (by rfl) ⟨677960, by rfl⟩ : syracuseStep 903947 = 1355921) B1355921
theorem B903959 : Blo 599292 903959 := bstep (se 1 (by rfl) ⟨677969, by rfl⟩ : syracuseStep 903959 = 1355939) B1355939
theorem B674635 : Blo 599292 674635 := bstep (se 1 (by rfl) ⟨505976, by rfl⟩ : syracuseStep 674635 = 1011953) B1011953
theorem B904025 : Blo 599292 904025 := bstep (se 2 (by rfl) ⟨339009, by rfl⟩ : syracuseStep 904025 = 678019) B678019
theorem B674743 : Blo 599292 674743 := bstep (se 1 (by rfl) ⟨506057, by rfl⟩ : syracuseStep 674743 = 1012115) B1012115
theorem B904139 : Blo 599292 904139 := bstep (se 1 (by rfl) ⟨678104, by rfl⟩ : syracuseStep 904139 = 1356209) B1356209
theorem B904151 : Blo 599292 904151 := bstep (se 1 (by rfl) ⟨678113, by rfl⟩ : syracuseStep 904151 = 1356227) B1356227
theorem B904217 : Blo 599292 904217 := bstep (se 2 (by rfl) ⟨339081, by rfl⟩ : syracuseStep 904217 = 678163) B678163
theorem B3427393 : Blo 599292 3427393 := bstep (se 2 (by rfl) ⟨1285272, by rfl⟩ : syracuseStep 3427393 = 2570545) B2570545
theorem B674923 : Blo 599292 674923 := bstep (se 1 (by rfl) ⟨506192, by rfl⟩ : syracuseStep 674923 = 1012385) B1012385
theorem B904331 : Blo 599292 904331 := bstep (se 1 (by rfl) ⟨678248, by rfl⟩ : syracuseStep 904331 = 1356497) B1356497
theorem B904343 : Blo 599292 904343 := bstep (se 1 (by rfl) ⟨678257, by rfl⟩ : syracuseStep 904343 = 1356515) B1356515
theorem B2477249 : Blo 599292 2477249 := bstep (se 2 (by rfl) ⟨928968, by rfl⟩ : syracuseStep 2477249 = 1857937) B1857937
theorem B1625291 : Blo 599292 1625291 := bstep (se 1 (by rfl) ⟨1218968, by rfl⟩ : syracuseStep 1625291 = 2437937) B2437937
theorem B675031 : Blo 599292 675031 := bstep (se 1 (by rfl) ⟨506273, by rfl⟩ : syracuseStep 675031 = 1012547) B1012547
theorem B904409 : Blo 599292 904409 := bstep (se 2 (by rfl) ⟨339153, by rfl⟩ : syracuseStep 904409 = 678307) B678307
theorem B2280707 : Blo 599292 2280707 := bstep (se 1 (by rfl) ⟨1710530, by rfl⟩ : syracuseStep 2280707 = 3421061) B3421061
theorem B904523 : Blo 599292 904523 := bstep (se 1 (by rfl) ⟨678392, by rfl⟩ : syracuseStep 904523 = 1356785) B1356785
theorem B904535 : Blo 599292 904535 := bstep (se 1 (by rfl) ⟨678401, by rfl⟩ : syracuseStep 904535 = 1356803) B1356803
theorem B675211 : Blo 599292 675211 := bstep (se 1 (by rfl) ⟨506408, by rfl⟩ : syracuseStep 675211 = 1012817) B1012817
theorem B904601 : Blo 599292 904601 := bstep (se 2 (by rfl) ⟨339225, by rfl⟩ : syracuseStep 904601 = 678451) B678451
theorem B2444717 : Blo 599292 2444717 := bstep (se 3 (by rfl) ⟨458384, by rfl⟩ : syracuseStep 2444717 = 916769) B916769
theorem B675319 : Blo 599292 675319 := bstep (se 1 (by rfl) ⟨506489, by rfl⟩ : syracuseStep 675319 = 1012979) B1012979
theorem B642551 : Blo 599292 642551 := bstep (se 1 (by rfl) ⟨481913, by rfl⟩ : syracuseStep 642551 = 963827) B963827
theorem B904715 : Blo 599292 904715 := bstep (se 1 (by rfl) ⟨678536, by rfl⟩ : syracuseStep 904715 = 1357073) B1357073
theorem B904727 : Blo 599292 904727 := bstep (se 1 (by rfl) ⟨678545, by rfl⟩ : syracuseStep 904727 = 1357091) B1357091
theorem B904793 : Blo 599292 904793 := bstep (se 2 (by rfl) ⟨339297, by rfl⟩ : syracuseStep 904793 = 678595) B678595
theorem B675499 : Blo 599292 675499 := bstep (se 1 (by rfl) ⟨506624, by rfl⟩ : syracuseStep 675499 = 1013249) B1013249
theorem B904907 : Blo 599292 904907 := bstep (se 1 (by rfl) ⟨678680, by rfl⟩ : syracuseStep 904907 = 1357361) B1357361
theorem B904919 : Blo 599292 904919 := bstep (se 1 (by rfl) ⟨678689, by rfl⟩ : syracuseStep 904919 = 1357379) B1357379
theorem B675607 : Blo 599292 675607 := bstep (se 1 (by rfl) ⟨506705, by rfl⟩ : syracuseStep 675607 = 1013411) B1013411
theorem B675787 : Blo 599292 675787 := bstep (se 1 (by rfl) ⟨506840, by rfl⟩ : syracuseStep 675787 = 1013681) B1013681
theorem B2576407 : Blo 599292 2576407 := bstep (se 1 (by rfl) ⟨1932305, by rfl⟩ : syracuseStep 2576407 = 3864611) B3864611
theorem B675895 : Blo 599292 675895 := bstep (se 1 (by rfl) ⟨506921, by rfl⟩ : syracuseStep 675895 = 1013843) B1013843
theorem B5492941 : Blo 599292 5492941 := bstep (se 3 (by rfl) ⟨1029926, by rfl⟩ : syracuseStep 5492941 = 2059853) B2059853
theorem B676075 : Blo 599292 676075 := bstep (se 1 (by rfl) ⟨507056, by rfl⟩ : syracuseStep 676075 = 1014113) B1014113
theorem B676183 : Blo 599292 676183 := bstep (se 1 (by rfl) ⟨507137, by rfl⟩ : syracuseStep 676183 = 1014275) B1014275
theorem B676363 : Blo 599292 676363 := bstep (se 1 (by rfl) ⟨507272, by rfl⟩ : syracuseStep 676363 = 1014545) B1014545
theorem B676471 : Blo 599292 676471 := bstep (se 1 (by rfl) ⟨507353, by rfl⟩ : syracuseStep 676471 = 1014707) B1014707
theorem B1233623 : Blo 599292 1233623 := bstep (se 1 (by rfl) ⟨925217, by rfl⟩ : syracuseStep 1233623 = 1850435) B1850435
theorem B5788421 : Blo 599292 5788421 := bstep (se 4 (by rfl) ⟨542664, by rfl⟩ : syracuseStep 5788421 = 1085329) B1085329
theorem B676651 : Blo 599292 676651 := bstep (se 1 (by rfl) ⟨507488, by rfl⟩ : syracuseStep 676651 = 1014977) B1014977
theorem B5133131 : Blo 599292 5133131 := bstep (se 1 (by rfl) ⟨3849848, by rfl⟩ : syracuseStep 5133131 = 7699697) B7699697
theorem B676759 : Blo 599292 676759 := bstep (se 1 (by rfl) ⟨507569, by rfl⟩ : syracuseStep 676759 = 1015139) B1015139
theorem B676939 : Blo 599292 676939 := bstep (se 1 (by rfl) ⟨507704, by rfl⟩ : syracuseStep 676939 = 1015409) B1015409
theorem B611479 : Blo 599292 611479 := bstep (se 1 (by rfl) ⟨458609, by rfl⟩ : syracuseStep 611479 = 917219) B917219
theorem B677047 : Blo 599292 677047 := bstep (se 1 (by rfl) ⟨507785, by rfl⟩ : syracuseStep 677047 = 1015571) B1015571
theorem B677227 : Blo 599292 677227 := bstep (se 1 (by rfl) ⟨507920, by rfl⟩ : syracuseStep 677227 = 1015841) B1015841
theorem B677335 : Blo 599292 677335 := bstep (se 1 (by rfl) ⟨508001, by rfl⟩ : syracuseStep 677335 = 1016003) B1016003
theorem B8640017 : Blo 599292 8640017 := bstep (se 2 (by rfl) ⟨3240006, by rfl⟩ : syracuseStep 8640017 = 6480013) B6480013
theorem B3036689 : Blo 599292 3036689 := bstep (se 2 (by rfl) ⟨1138758, by rfl⟩ : syracuseStep 3036689 = 2277517) B2277517
theorem B12998161 : Blo 599292 12998161 := bstep (se 2 (by rfl) ⟨4874310, by rfl⟩ : syracuseStep 12998161 = 9748621) B9748621
theorem B939607 : Blo 599292 939607 := bstep (se 1 (by rfl) ⟨704705, by rfl⟩ : syracuseStep 939607 = 1409411) B1409411
theorem B677515 : Blo 599292 677515 := bstep (se 1 (by rfl) ⟨508136, by rfl⟩ : syracuseStep 677515 = 1016273) B1016273
theorem B3036851 : Blo 599292 3036851 := bstep (se 1 (by rfl) ⟨2277638, by rfl⟩ : syracuseStep 3036851 = 4555277) B4555277
theorem B677623 : Blo 599292 677623 := bstep (se 1 (by rfl) ⟨508217, by rfl⟩ : syracuseStep 677623 = 1016435) B1016435
theorem B677803 : Blo 599292 677803 := bstep (se 1 (by rfl) ⟨508352, by rfl⟩ : syracuseStep 677803 = 1016705) B1016705
theorem B2054081 : Blo 599292 2054081 := bstep (se 2 (by rfl) ⟨770280, by rfl⟩ : syracuseStep 2054081 = 1540561) B1540561
theorem B677911 : Blo 599292 677911 := bstep (se 1 (by rfl) ⟨508433, by rfl⟩ : syracuseStep 677911 = 1016867) B1016867
theorem B1628363 : Blo 599292 1628363 := bstep (se 1 (by rfl) ⟨1221272, by rfl⟩ : syracuseStep 1628363 = 2442545) B2442545
theorem B678091 : Blo 599292 678091 := bstep (se 1 (by rfl) ⟨508568, by rfl⟩ : syracuseStep 678091 = 1017137) B1017137
theorem B2283821 : Blo 599292 2283821 := bstep (se 3 (by rfl) ⟨428216, by rfl⟩ : syracuseStep 2283821 = 856433) B856433
theorem B678199 : Blo 599292 678199 := bstep (se 1 (by rfl) ⟨508649, by rfl⟩ : syracuseStep 678199 = 1017299) B1017299
theorem B4348235 : Blo 599292 4348235 := bstep (se 1 (by rfl) ⟨3261176, by rfl⟩ : syracuseStep 4348235 = 6522353) B6522353
theorem B3430835 : Blo 599292 3430835 := bstep (se 1 (by rfl) ⟨2573126, by rfl⟩ : syracuseStep 3430835 = 5146253) B5146253
theorem B678379 : Blo 599292 678379 := bstep (se 1 (by rfl) ⟨508784, by rfl⟩ : syracuseStep 678379 = 1017569) B1017569
theorem B678487 : Blo 599292 678487 := bstep (se 1 (by rfl) ⟨508865, by rfl⟩ : syracuseStep 678487 = 1017731) B1017731
theorem B678667 : Blo 599292 678667 := bstep (se 1 (by rfl) ⟨509000, by rfl⟩ : syracuseStep 678667 = 1018001) B1018001
theorem B12311513 : Blo 599292 12311513 := bstep (se 2 (by rfl) ⟨4616817, by rfl⟩ : syracuseStep 12311513 = 9233635) B9233635
theorem B1825753 : Blo 599292 1825753 := bstep (se 2 (by rfl) ⟨684657, by rfl⟩ : syracuseStep 1825753 = 1369315) B1369315
theorem B2284595 : Blo 599292 2284595 := bstep (se 1 (by rfl) ⟨1713446, by rfl⟩ : syracuseStep 2284595 = 3426893) B3426893
theorem B1137817 : Blo 599292 1137817 := bstep (se 2 (by rfl) ⟨426681, by rfl⟩ : syracuseStep 1137817 = 853363) B853363
theorem B4578605 : Blo 599292 4578605 := bstep (se 3 (by rfl) ⟨858488, by rfl⟩ : syracuseStep 4578605 = 1716977) B1716977
theorem B2022731 : Blo 599292 2022731 := bstep (se 1 (by rfl) ⟨1517048, by rfl⟩ : syracuseStep 2022731 = 3034097) B3034097
theorem B3038795 : Blo 599292 3038795 := bstep (se 1 (by rfl) ⟨2279096, by rfl⟩ : syracuseStep 3038795 = 4558193) B4558193
theorem B2023001 : Blo 599292 2023001 := bstep (se 2 (by rfl) ⟨758625, by rfl⟩ : syracuseStep 2023001 = 1517251) B1517251
theorem B3432293 : Blo 599292 3432293 := bstep (se 4 (by rfl) ⟨321777, by rfl⟩ : syracuseStep 3432293 = 643555) B643555
theorem B2023703 : Blo 599292 2023703 := bstep (se 1 (by rfl) ⟨1517777, by rfl⟩ : syracuseStep 2023703 = 3035555) B3035555
theorem B1139123 : Blo 599292 1139123 := bstep (se 1 (by rfl) ⟨854342, by rfl⟩ : syracuseStep 1139123 = 1708685) B1708685
theorem B2286083 : Blo 599292 2286083 := bstep (se 1 (by rfl) ⟨1714562, by rfl⟩ : syracuseStep 2286083 = 3429125) B3429125
theorem B1139275 : Blo 599292 1139275 := bstep (se 1 (by rfl) ⟨854456, by rfl⟩ : syracuseStep 1139275 = 1708913) B1708913
theorem B1172183 : Blo 599292 1172183 := bstep (se 1 (by rfl) ⟨879137, by rfl⟩ : syracuseStep 1172183 = 1758275) B1758275
theorem B2974481 : Blo 599292 2974481 := bstep (se 2 (by rfl) ⟨1115430, by rfl⟩ : syracuseStep 2974481 = 2230861) B2230861
theorem B1368857 : Blo 599292 1368857 := bstep (se 2 (by rfl) ⟨513321, by rfl⟩ : syracuseStep 1368857 = 1026643) B1026643
theorem B2024243 : Blo 599292 2024243 := bstep (se 1 (by rfl) ⟨1518182, by rfl⟩ : syracuseStep 2024243 = 3036365) B3036365
theorem B7725941 : Blo 599292 7725941 := bstep (se 5 (by rfl) ⟨362153, by rfl⟩ : syracuseStep 7725941 = 724307) B724307
theorem B1139609 : Blo 599292 1139609 := bstep (se 2 (by rfl) ⟨427353, by rfl⟩ : syracuseStep 1139609 = 854707) B854707
theorem B8217521 : Blo 599292 8217521 := bstep (se 2 (by rfl) ⟨3081570, by rfl⟩ : syracuseStep 8217521 = 6163141) B6163141
theorem B2286539 : Blo 599292 2286539 := bstep (se 1 (by rfl) ⟨1714904, by rfl⟩ : syracuseStep 2286539 = 3429809) B3429809
theorem B2024513 : Blo 599292 2024513 := bstep (se 2 (by rfl) ⟨759192, by rfl⟩ : syracuseStep 2024513 = 1518385) B1518385
theorem B2286737 : Blo 599292 2286737 := bstep (se 2 (by rfl) ⟨857526, by rfl⟩ : syracuseStep 2286737 = 1715053) B1715053
theorem B17523863 : Blo 599292 17523863 := bstep (se 1 (by rfl) ⟨13142897, by rfl⟩ : syracuseStep 17523863 = 26285795) B26285795
theorem B812299 : Blo 599292 812299 := bstep (se 1 (by rfl) ⟨609224, by rfl⟩ : syracuseStep 812299 = 1218449) B1218449
theorem B3040577 : Blo 599292 3040577 := bstep (se 2 (by rfl) ⟨1140216, by rfl⟩ : syracuseStep 3040577 = 2280433) B2280433
theorem B1140247 : Blo 599292 1140247 := bstep (se 1 (by rfl) ⟨855185, by rfl⟩ : syracuseStep 1140247 = 1710371) B1710371
theorem B1926679 : Blo 599292 1926679 := bstep (se 1 (by rfl) ⟨1445009, by rfl⟩ : syracuseStep 1926679 = 2890019) B2890019
theorem B2025053 : Blo 599292 2025053 := bstep (se 3 (by rfl) ⟨379697, by rfl⟩ : syracuseStep 2025053 = 759395) B759395
theorem B10938007 : Blo 599292 10938007 := bstep (se 1 (by rfl) ⟨8203505, by rfl⟩ : syracuseStep 10938007 = 16407011) B16407011
theorem B7726913 : Blo 599292 7726913 := bstep (se 2 (by rfl) ⟨2897592, by rfl⟩ : syracuseStep 7726913 = 5795185) B5795185
theorem B2287511 : Blo 599292 2287511 := bstep (se 1 (by rfl) ⟨1715633, by rfl⟩ : syracuseStep 2287511 = 3431267) B3431267
theorem B1927243 : Blo 599292 1927243 := bstep (se 1 (by rfl) ⟨1445432, by rfl⟩ : syracuseStep 1927243 = 2890865) B2890865
theorem B2287709 : Blo 599292 2287709 := bstep (se 3 (by rfl) ⟨428945, by rfl⟩ : syracuseStep 2287709 = 857891) B857891
theorem B1370263 : Blo 599292 1370263 := bstep (se 1 (by rfl) ⟨1027697, by rfl⟩ : syracuseStep 1370263 = 2055395) B2055395
theorem B1927385 : Blo 599292 1927385 := bstep (se 2 (by rfl) ⟨722769, by rfl⟩ : syracuseStep 1927385 = 1445539) B1445539
theorem B1141067 : Blo 599292 1141067 := bstep (se 1 (by rfl) ⟨855800, by rfl⟩ : syracuseStep 1141067 = 1711601) B1711601
theorem B55568753 : Blo 599292 55568753 := bstep (se 2 (by rfl) ⟨20838282, by rfl⟩ : syracuseStep 55568753 = 41676565) B41676565
theorem B1141121 : Blo 599292 1141121 := bstep (se 2 (by rfl) ⟨427920, by rfl⟩ : syracuseStep 1141121 = 855841) B855841
theorem B2058817 : Blo 599292 2058817 := bstep (se 2 (by rfl) ⟨772056, by rfl⟩ : syracuseStep 2058817 = 1544113) B1544113
theorem B2026187 : Blo 599292 2026187 := bstep (se 1 (by rfl) ⟨1519640, by rfl⟩ : syracuseStep 2026187 = 3039281) B3039281
theorem B813835 : Blo 599292 813835 := bstep (se 1 (by rfl) ⟨610376, by rfl⟩ : syracuseStep 813835 = 1220753) B1220753
theorem B7301933 : Blo 599292 7301933 := bstep (se 3 (by rfl) ⟨1369112, by rfl⟩ : syracuseStep 7301933 = 2738225) B2738225
theorem B2747201 : Blo 599292 2747201 := bstep (se 2 (by rfl) ⟨1030200, by rfl⟩ : syracuseStep 2747201 = 2060401) B2060401
theorem B4123543 : Blo 599292 4123543 := bstep (se 1 (by rfl) ⟨3092657, by rfl⟩ : syracuseStep 4123543 = 6185315) B6185315
theorem B2026457 : Blo 599292 2026457 := bstep (se 2 (by rfl) ⟨759921, by rfl⟩ : syracuseStep 2026457 = 1519843) B1519843
theorem B650315 : Blo 599292 650315 := bstep (se 1 (by rfl) ⟨487736, by rfl⟩ : syracuseStep 650315 = 975473) B975473
theorem B1731677 : Blo 599292 1731677 := bstep (se 3 (by rfl) ⟨324689, by rfl⟩ : syracuseStep 1731677 = 649379) B649379
theorem B3042521 : Blo 599292 3042521 := bstep (se 2 (by rfl) ⟨1140945, by rfl⟩ : syracuseStep 3042521 = 2281891) B2281891
theorem B1142039 : Blo 599292 1142039 := bstep (se 1 (by rfl) ⟨856529, by rfl⟩ : syracuseStep 1142039 = 1713059) B1713059
theorem B1273153 : Blo 599292 1273153 := bstep (se 2 (by rfl) ⟨477432, by rfl⟩ : syracuseStep 1273153 = 954865) B954865
theorem B1928627 : Blo 599292 1928627 := bstep (se 1 (by rfl) ⟨1446470, by rfl⟩ : syracuseStep 1928627 = 2892941) B2892941
theorem B650743 : Blo 599292 650743 := bstep (se 1 (by rfl) ⟨488057, by rfl⟩ : syracuseStep 650743 = 976115) B976115
theorem B2027159 : Blo 599292 2027159 := bstep (se 1 (by rfl) ⟨1520369, by rfl⟩ : syracuseStep 2027159 = 3040739) B3040739
theorem B1011467 : Blo 599292 1011467 := bstep (se 1 (by rfl) ⟨758600, by rfl⟩ : syracuseStep 1011467 = 1517201) B1517201
theorem B1142579 : Blo 599292 1142579 := bstep (se 1 (by rfl) ⟨856934, by rfl⟩ : syracuseStep 1142579 = 1713869) B1713869
theorem B1929025 : Blo 599292 1929025 := bstep (se 2 (by rfl) ⟨723384, by rfl⟩ : syracuseStep 1929025 = 1446769) B1446769
theorem B1011595 : Blo 599292 1011595 := bstep (se 1 (by rfl) ⟨758696, by rfl⟩ : syracuseStep 1011595 = 1517393) B1517393
theorem B2289667 : Blo 599292 2289667 := bstep (se 1 (by rfl) ⟨1717250, by rfl⟩ : syracuseStep 2289667 = 3434501) B3434501
theorem B1011737 : Blo 599292 1011737 := bstep (se 2 (by rfl) ⟨379401, by rfl⟩ : syracuseStep 1011737 = 758803) B758803
theorem B4124803 : Blo 599292 4124803 := bstep (se 1 (by rfl) ⟨3093602, by rfl⟩ : syracuseStep 4124803 = 6187205) B6187205
theorem B6942871 : Blo 599292 6942871 := bstep (se 1 (by rfl) ⟨5207153, by rfl⟩ : syracuseStep 6942871 = 10414307) B10414307
theorem B1011865 : Blo 599292 1011865 := bstep (se 2 (by rfl) ⟨379449, by rfl⟩ : syracuseStep 1011865 = 758899) B758899
theorem B2027699 : Blo 599292 2027699 := bstep (se 1 (by rfl) ⟨1520774, by rfl⟩ : syracuseStep 2027699 = 3041549) B3041549
theorem B1372427 : Blo 599292 1372427 := bstep (se 1 (by rfl) ⟨1029320, by rfl⟩ : syracuseStep 1372427 = 2058641) B2058641
theorem B1143065 : Blo 599292 1143065 := bstep (se 2 (by rfl) ⟨428649, by rfl⟩ : syracuseStep 1143065 = 857299) B857299
theorem B2289971 : Blo 599292 2289971 := bstep (se 1 (by rfl) ⟨1717478, by rfl⟩ : syracuseStep 2289971 = 3434957) B3434957
theorem B913739 : Blo 599292 913739 := bstep (se 1 (by rfl) ⟨685304, by rfl⟩ : syracuseStep 913739 = 1370609) B1370609
theorem B2027969 : Blo 599292 2027969 := bstep (se 2 (by rfl) ⟨760488, by rfl⟩ : syracuseStep 2027969 = 1520977) B1520977
theorem B1012439 : Blo 599292 1012439 := bstep (se 1 (by rfl) ⟨759329, by rfl⟩ : syracuseStep 1012439 = 1518659) B1518659
theorem B3044141 : Blo 599292 3044141 := bstep (se 3 (by rfl) ⟨570776, by rfl⟩ : syracuseStep 3044141 = 1141553) B1141553
theorem B1012567 : Blo 599292 1012567 := bstep (se 1 (by rfl) ⟨759425, by rfl⟩ : syracuseStep 1012567 = 1518851) B1518851
theorem B2290625 : Blo 599292 2290625 := bstep (se 2 (by rfl) ⟨858984, by rfl⟩ : syracuseStep 2290625 = 1717969) B1717969
theorem B2028509 : Blo 599292 2028509 := bstep (se 3 (by rfl) ⟨380345, by rfl⟩ : syracuseStep 2028509 = 760691) B760691
theorem B1733939 : Blo 599292 1733939 := bstep (se 1 (by rfl) ⟨1300454, by rfl⟩ : syracuseStep 1733939 = 2600909) B2600909
theorem B2061719 : Blo 599292 2061719 := bstep (se 1 (by rfl) ⟨1546289, by rfl⟩ : syracuseStep 2061719 = 3092579) B3092579
theorem B2880947 : Blo 599292 2880947 := bstep (se 1 (by rfl) ⟨2160710, by rfl⟩ : syracuseStep 2880947 = 4321421) B4321421
theorem B1013195 : Blo 599292 1013195 := bstep (se 1 (by rfl) ⟨759896, by rfl⟩ : syracuseStep 1013195 = 1519793) B1519793
theorem B685579 : Blo 599292 685579 := bstep (se 1 (by rfl) ⟨514184, by rfl⟩ : syracuseStep 685579 = 1028369) B1028369
theorem B9729553 : Blo 599292 9729553 := bstep (se 2 (by rfl) ⟨3648582, by rfl⟩ : syracuseStep 9729553 = 7297165) B7297165
theorem B2881099 : Blo 599292 2881099 := bstep (se 1 (by rfl) ⟨2160824, by rfl⟩ : syracuseStep 2881099 = 4321649) B4321649
theorem B1013323 : Blo 599292 1013323 := bstep (se 1 (by rfl) ⟨759992, by rfl⟩ : syracuseStep 1013323 = 1519985) B1519985
theorem B1144523 : Blo 599292 1144523 := bstep (se 1 (by rfl) ⟨858392, by rfl⟩ : syracuseStep 1144523 = 1716785) B1716785
theorem B1013465 : Blo 599292 1013465 := bstep (se 2 (by rfl) ⟨380049, by rfl⟩ : syracuseStep 1013465 = 760099) B760099
theorem B1013593 : Blo 599292 1013593 := bstep (se 2 (by rfl) ⟨380097, by rfl⟩ : syracuseStep 1013593 = 760195) B760195
theorem B1144705 : Blo 599292 1144705 := bstep (se 2 (by rfl) ⟨429264, by rfl⟩ : syracuseStep 1144705 = 858529) B858529
theorem B1374259 : Blo 599292 1374259 := bstep (se 1 (by rfl) ⟨1030694, by rfl⟩ : syracuseStep 1374259 = 2061389) B2061389
theorem B2881601 : Blo 599292 2881601 := bstep (se 2 (by rfl) ⟨1080600, by rfl⟩ : syracuseStep 2881601 = 2161201) B2161201
theorem B1833025 : Blo 599292 1833025 := bstep (se 2 (by rfl) ⟨687384, by rfl⟩ : syracuseStep 1833025 = 1374769) B1374769
theorem B2029643 : Blo 599292 2029643 := bstep (se 1 (by rfl) ⟨1522232, by rfl⟩ : syracuseStep 2029643 = 3044465) B3044465
theorem B1145153 : Blo 599292 1145153 := bstep (se 2 (by rfl) ⟨429432, by rfl⟩ : syracuseStep 1145153 = 858865) B858865
theorem B4127051 : Blo 599292 4127051 := bstep (se 1 (by rfl) ⟨3095288, by rfl⟩ : syracuseStep 4127051 = 6190577) B6190577
theorem B1440089 : Blo 599292 1440089 := bstep (se 2 (by rfl) ⟨540033, by rfl⟩ : syracuseStep 1440089 = 1080067) B1080067
theorem B2029913 : Blo 599292 2029913 := bstep (se 2 (by rfl) ⟨761217, by rfl⟩ : syracuseStep 2029913 = 1522435) B1522435
theorem B2750851 : Blo 599292 2750851 := bstep (se 1 (by rfl) ⟨2063138, by rfl⟩ : syracuseStep 2750851 = 4126277) B4126277
theorem B1014167 : Blo 599292 1014167 := bstep (se 1 (by rfl) ⟨760625, by rfl⟩ : syracuseStep 1014167 = 1521251) B1521251
theorem B1014295 : Blo 599292 1014295 := bstep (se 1 (by rfl) ⟨760721, by rfl⟩ : syracuseStep 1014295 = 1521443) B1521443
theorem B3668753 : Blo 599292 3668753 := bstep (se 2 (by rfl) ⟨1375782, by rfl⟩ : syracuseStep 3668753 = 2751565) B2751565
theorem B1080139 : Blo 599292 1080139 := bstep (se 1 (by rfl) ⟨810104, by rfl⟩ : syracuseStep 1080139 = 1620209) B1620209
theorem B2030615 : Blo 599292 2030615 := bstep (se 1 (by rfl) ⟨1522961, by rfl⟩ : syracuseStep 2030615 = 3045923) B3045923
theorem B1080371 : Blo 599292 1080371 := bstep (se 1 (by rfl) ⟨810278, by rfl⟩ : syracuseStep 1080371 = 1620557) B1620557
theorem B1014923 : Blo 599292 1014923 := bstep (se 1 (by rfl) ⟨761192, by rfl⟩ : syracuseStep 1014923 = 1522385) B1522385
theorem B1015051 : Blo 599292 1015051 := bstep (se 1 (by rfl) ⟨761288, by rfl⟩ : syracuseStep 1015051 = 1522577) B1522577
theorem B1015193 : Blo 599292 1015193 := bstep (se 2 (by rfl) ⟨380697, by rfl⟩ : syracuseStep 1015193 = 761395) B761395
theorem B1015321 : Blo 599292 1015321 := bstep (se 2 (by rfl) ⟨380745, by rfl⟩ : syracuseStep 1015321 = 761491) B761491
theorem B2031155 : Blo 599292 2031155 := bstep (se 1 (by rfl) ⟨1523366, by rfl⟩ : syracuseStep 2031155 = 3046733) B3046733
theorem B4554305 : Blo 599292 4554305 := bstep (se 2 (by rfl) ⟨1707864, by rfl⟩ : syracuseStep 4554305 = 3415729) B3415729
theorem B2031425 : Blo 599292 2031425 := bstep (se 2 (by rfl) ⟨761784, by rfl⟩ : syracuseStep 2031425 = 1523569) B1523569
theorem B1081163 : Blo 599292 1081163 := bstep (se 1 (by rfl) ⟨810872, by rfl⟩ : syracuseStep 1081163 = 1621745) B1621745
theorem B2883545 : Blo 599292 2883545 := bstep (se 2 (by rfl) ⟨1081329, by rfl⟩ : syracuseStep 2883545 = 2162659) B2162659
theorem B3047543 : Blo 599292 3047543 := bstep (se 1 (by rfl) ⟨2285657, by rfl⟩ : syracuseStep 3047543 = 4571315) B4571315
theorem B2032019 : Blo 599292 2032019 := bstep (se 1 (by rfl) ⟨1524014, by rfl⟩ : syracuseStep 2032019 = 3048029) B3048029
theorem B2884061 : Blo 599292 2884061 := bstep (se 3 (by rfl) ⟨540761, by rfl⟩ : syracuseStep 2884061 = 1081523) B1081523
theorem B52724195 : Blo 599292 52724195 := bstep (se 1 (by rfl) ⟨39543146, by rfl⟩ : syracuseStep 52724195 = 79086293) B79086293
theorem B2884099 : Blo 599292 2884099 := bstep (se 1 (by rfl) ⟨2163074, by rfl⟩ : syracuseStep 2884099 = 4326149) B4326149
theorem B4326007 : Blo 599292 4326007 := bstep (se 1 (by rfl) ⟨3244505, by rfl⟩ : syracuseStep 4326007 = 6489011) B6489011
theorem B1016455 : Blo 599292 1016455 := bstep (se 1 (by rfl) ⟨762341, by rfl⟩ : syracuseStep 1016455 = 1524683) B1524683
theorem B6521573 : Blo 599292 6521573 := bstep (se 4 (by rfl) ⟨611397, by rfl⟩ : syracuseStep 6521573 = 1222795) B1222795
theorem B3048515 : Blo 599292 3048515 := bstep (se 1 (by rfl) ⟨2286386, by rfl⟩ : syracuseStep 3048515 = 4572773) B4572773
theorem B29295685 : Blo 599292 29295685 := bstep (se 4 (by rfl) ⟨2746470, by rfl⟩ : syracuseStep 29295685 = 5492941) B5492941
theorem B1017103 : Blo 599292 1017103 := bstep (se 1 (by rfl) ⟨762827, by rfl⟩ : syracuseStep 1017103 = 1525655) B1525655
theorem B3048839 : Blo 599292 3048839 := bstep (se 1 (by rfl) ⟨2286629, by rfl⟩ : syracuseStep 3048839 = 4573259) B4573259
theorem B22808141 : Blo 599292 22808141 := bstep (se 3 (by rfl) ⟨4276526, by rfl⟩ : syracuseStep 22808141 = 8553053) B8553053
theorem B1443415 : Blo 599292 1443415 := bstep (se 1 (by rfl) ⟨1082561, by rfl⟩ : syracuseStep 1443415 = 2165123) B2165123
theorem B1083065 : Blo 599292 1083065 := bstep (se 2 (by rfl) ⟨406149, by rfl⟩ : syracuseStep 1083065 = 812299) B812299
theorem B2033423 : Blo 599292 2033423 := bstep (se 1 (by rfl) ⟨1525067, by rfl⟩ : syracuseStep 2033423 = 3050135) B3050135
theorem B1017643 : Blo 599292 1017643 := bstep (se 1 (by rfl) ⟨763232, by rfl⟩ : syracuseStep 1017643 = 1526465) B1526465
theorem B1443703 : Blo 599292 1443703 := bstep (se 1 (by rfl) ⟨1082777, by rfl⟩ : syracuseStep 1443703 = 2165555) B2165555
theorem B1017785 : Blo 599292 1017785 := bstep (se 2 (by rfl) ⟨381669, by rfl⟩ : syracuseStep 1017785 = 763339) B763339
theorem B2033693 : Blo 599292 2033693 := bstep (se 3 (by rfl) ⟨381317, by rfl⟩ : syracuseStep 2033693 = 762635) B762635
theorem B1083527 : Blo 599292 1083527 := bstep (se 1 (by rfl) ⟨812645, by rfl⟩ : syracuseStep 1083527 = 1625291) B1625291
theorem B854263 : Blo 599292 854263 := bstep (se 1 (by rfl) ⟨640697, by rfl⟩ : syracuseStep 854263 = 1281395) B1281395
theorem B4950821 : Blo 599292 4950821 := bstep (se 4 (by rfl) ⟨464139, by rfl⟩ : syracuseStep 4950821 = 928279) B928279
theorem B1706795 : Blo 599292 1706795 := bstep (se 1 (by rfl) ⟨1280096, by rfl⟩ : syracuseStep 1706795 = 2560193) B2560193
theorem B11537315 : Blo 599292 11537315 := bstep (se 1 (by rfl) ⟨8652986, by rfl⟩ : syracuseStep 11537315 = 17305973) B17305973
theorem B855083 : Blo 599292 855083 := bstep (se 1 (by rfl) ⟨641312, by rfl⟩ : syracuseStep 855083 = 1282625) B1282625
theorem B822415 : Blo 599292 822415 := bstep (se 1 (by rfl) ⟨616811, by rfl⟩ : syracuseStep 822415 = 1233623) B1233623
theorem B2035097 : Blo 599292 2035097 := bstep (se 2 (by rfl) ⟨763161, by rfl⟩ : syracuseStep 2035097 = 1526323) B1526323
theorem B1707581 : Blo 599292 1707581 := bstep (se 3 (by rfl) ⟨320171, by rfl⟩ : syracuseStep 1707581 = 640343) B640343
theorem B2887235 : Blo 599292 2887235 := bstep (se 1 (by rfl) ⟨2165426, by rfl⟩ : syracuseStep 2887235 = 4330853) B4330853
theorem B1085113 : Blo 599292 1085113 := bstep (se 2 (by rfl) ⟨406917, by rfl⟩ : syracuseStep 1085113 = 813835) B813835
theorem B1281737 : Blo 599292 1281737 := bstep (se 2 (by rfl) ⟨480651, by rfl⟩ : syracuseStep 1281737 = 961303) B961303
theorem B1707911 : Blo 599292 1707911 := bstep (se 1 (by rfl) ⟨1280933, by rfl⟩ : syracuseStep 1707911 = 2561867) B2561867
theorem B2887559 : Blo 599292 2887559 := bstep (se 1 (by rfl) ⟨2165669, by rfl⟩ : syracuseStep 2887559 = 4331339) B4331339
theorem B2035799 : Blo 599292 2035799 := bstep (se 1 (by rfl) ⟨1526849, by rfl⟩ : syracuseStep 2035799 = 3053699) B3053699
theorem B1085575 : Blo 599292 1085575 := bstep (se 1 (by rfl) ⟨814181, by rfl⟩ : syracuseStep 1085575 = 1628363) B1628363
theorem B856507 : Blo 599292 856507 := bstep (se 1 (by rfl) ⟨642380, by rfl⟩ : syracuseStep 856507 = 1284761) B1284761
theorem B1413665 : Blo 599292 1413665 := bstep (se 2 (by rfl) ⟨530124, by rfl⟩ : syracuseStep 1413665 = 1060249) B1060249
theorem B1446547 : Blo 599292 1446547 := bstep (se 1 (by rfl) ⟨1084910, by rfl⟩ : syracuseStep 1446547 = 2169821) B2169821
theorem B3052403 : Blo 599292 3052403 := bstep (se 1 (by rfl) ⟨2289302, by rfl⟩ : syracuseStep 3052403 = 4578605) B4578605
theorem B1348487 : Blo 599292 1348487 := bstep (se 1 (by rfl) ⟨1011365, by rfl⟩ : syracuseStep 1348487 = 2022731) B2022731
theorem B1446923 : Blo 599292 1446923 := bstep (se 1 (by rfl) ⟨1085192, by rfl⟩ : syracuseStep 1446923 = 2170385) B2170385
theorem B1348667 : Blo 599292 1348667 := bstep (se 1 (by rfl) ⟨1011500, by rfl⟩ : syracuseStep 1348667 = 2023001) B2023001
theorem B1348793 : Blo 599292 1348793 := bstep (se 2 (by rfl) ⟨505797, by rfl⟩ : syracuseStep 1348793 = 1011595) B1011595
theorem B3052889 : Blo 599292 3052889 := bstep (se 2 (by rfl) ⟨1144833, by rfl⟩ : syracuseStep 3052889 = 2289667) B2289667
theorem B1349135 : Blo 599292 1349135 := bstep (se 1 (by rfl) ⟨1011851, by rfl⟩ : syracuseStep 1349135 = 2023703) B2023703
theorem B1349153 : Blo 599292 1349153 := bstep (se 2 (by rfl) ⟨505932, by rfl⟩ : syracuseStep 1349153 = 1011865) B1011865
theorem B1709687 : Blo 599292 1709687 := bstep (se 1 (by rfl) ⟨1282265, by rfl⟩ : syracuseStep 1709687 = 2564531) B2564531
theorem B1349495 : Blo 599292 1349495 := bstep (se 1 (by rfl) ⟨1012121, by rfl⟩ : syracuseStep 1349495 = 2024243) B2024243
theorem B857999 : Blo 599292 857999 := bstep (se 1 (by rfl) ⟨643499, by rfl⟩ : syracuseStep 857999 = 1286999) B1286999
theorem B5150627 : Blo 599292 5150627 := bstep (se 1 (by rfl) ⟨3862970, by rfl⟩ : syracuseStep 5150627 = 7725941) B7725941
theorem B5478347 : Blo 599292 5478347 := bstep (se 1 (by rfl) ⟨4108760, by rfl⟩ : syracuseStep 5478347 = 8217521) B8217521
theorem B20846605 : Blo 599292 20846605 := bstep (se 3 (by rfl) ⟨3908738, by rfl⟩ : syracuseStep 20846605 = 7817477) B7817477
theorem B1349675 : Blo 599292 1349675 := bstep (se 1 (by rfl) ⟨1012256, by rfl⟩ : syracuseStep 1349675 = 2024513) B2024513
theorem B2889847 : Blo 599292 2889847 := bstep (se 1 (by rfl) ⟨2167385, by rfl⟩ : syracuseStep 2889847 = 4334771) B4334771
theorem B3479867 : Blo 599292 3479867 := bstep (se 1 (by rfl) ⟨2609900, by rfl⟩ : syracuseStep 3479867 = 5219801) B5219801
theorem B1350035 : Blo 599292 1350035 := bstep (se 1 (by rfl) ⟨1012526, by rfl⟩ : syracuseStep 1350035 = 2025053) B2025053
theorem B1350089 : Blo 599292 1350089 := bstep (se 2 (by rfl) ⟨506283, by rfl⟩ : syracuseStep 1350089 = 1012567) B1012567
theorem B5151275 : Blo 599292 5151275 := bstep (se 1 (by rfl) ⟨3863456, by rfl⟩ : syracuseStep 5151275 = 7726913) B7726913
theorem B1710679 : Blo 599292 1710679 := bstep (se 1 (by rfl) ⟨1283009, by rfl⟩ : syracuseStep 1710679 = 2566019) B2566019
theorem B2169463 : Blo 599292 2169463 := bstep (se 1 (by rfl) ⟨1627097, by rfl⟩ : syracuseStep 2169463 = 3254195) B3254195
theorem B3250925 : Blo 599292 3250925 := bstep (se 3 (by rfl) ⟨609548, by rfl⟩ : syracuseStep 3250925 = 1219097) B1219097
theorem B924431 : Blo 599292 924431 := bstep (se 1 (by rfl) ⟨693323, by rfl⟩ : syracuseStep 924431 = 1386647) B1386647
theorem B924475 : Blo 599292 924475 := bstep (se 1 (by rfl) ⟨693356, by rfl⟩ : syracuseStep 924475 = 1386713) B1386713
theorem B1284923 : Blo 599292 1284923 := bstep (se 1 (by rfl) ⟨963692, by rfl⟩ : syracuseStep 1284923 = 1927385) B1927385
theorem B760747 : Blo 599292 760747 := bstep (se 1 (by rfl) ⟨570560, by rfl⟩ : syracuseStep 760747 = 1141121) B1141121
theorem B1350791 : Blo 599292 1350791 := bstep (se 1 (by rfl) ⟨1013093, by rfl⟩ : syracuseStep 1350791 = 2026187) B2026187
theorem B1350971 : Blo 599292 1350971 := bstep (se 1 (by rfl) ⟨1013228, by rfl⟩ : syracuseStep 1350971 = 2026457) B2026457
theorem B6495623 : Blo 599292 6495623 := bstep (se 1 (by rfl) ⟨4871717, by rfl⟩ : syracuseStep 6495623 = 9743435) B9743435
theorem B1351097 : Blo 599292 1351097 := bstep (se 2 (by rfl) ⟨506661, by rfl⟩ : syracuseStep 1351097 = 1013323) B1013323
theorem B1285751 : Blo 599292 1285751 := bstep (se 1 (by rfl) ⟨964313, by rfl⟩ : syracuseStep 1285751 = 1928627) B1928627
theorem B1351439 : Blo 599292 1351439 := bstep (se 1 (by rfl) ⟨1013579, by rfl⟩ : syracuseStep 1351439 = 2027159) B2027159
theorem B1351457 : Blo 599292 1351457 := bstep (se 2 (by rfl) ⟨506796, by rfl⟩ : syracuseStep 1351457 = 1013593) B1013593
theorem B761719 : Blo 599292 761719 := bstep (se 1 (by rfl) ⟨571289, by rfl⟩ : syracuseStep 761719 = 1142579) B1142579
theorem B1712171 : Blo 599292 1712171 := bstep (se 1 (by rfl) ⟨1284128, by rfl⟩ : syracuseStep 1712171 = 2568257) B2568257
theorem B1351799 : Blo 599292 1351799 := bstep (se 1 (by rfl) ⟨1013849, by rfl⟩ : syracuseStep 1351799 = 2027699) B2027699
theorem B762043 : Blo 599292 762043 := bstep (se 1 (by rfl) ⟨571532, by rfl⟩ : syracuseStep 762043 = 1143065) B1143065
theorem B1351979 : Blo 599292 1351979 := bstep (se 1 (by rfl) ⟨1013984, by rfl⟩ : syracuseStep 1351979 = 2027969) B2027969
theorem B1352339 : Blo 599292 1352339 := bstep (se 1 (by rfl) ⟨1014254, by rfl⟩ : syracuseStep 1352339 = 2028509) B2028509
theorem B29303477 : Blo 599292 29303477 := bstep (se 5 (by rfl) ⟨1373600, by rfl⟩ : syracuseStep 29303477 = 2747201) B2747201
theorem B1352393 : Blo 599292 1352393 := bstep (se 2 (by rfl) ⟨507147, by rfl⟩ : syracuseStep 1352393 = 1014295) B1014295
theorem B58336037 : Blo 599292 58336037 := bstep (se 4 (by rfl) ⟨5469003, by rfl⟩ : syracuseStep 58336037 = 10938007) B10938007
theorem B2433851 : Blo 599292 2433851 := bstep (se 1 (by rfl) ⟨1825388, by rfl⟩ : syracuseStep 2433851 = 3650777) B3650777
theorem B1155959 : Blo 599292 1155959 := bstep (se 1 (by rfl) ⟨866969, by rfl⟩ : syracuseStep 1155959 = 1733939) B1733939
theorem B1713287 : Blo 599292 1713287 := bstep (se 1 (by rfl) ⟨1284965, by rfl⟩ : syracuseStep 1713287 = 2569931) B2569931
theorem B763015 : Blo 599292 763015 := bstep (se 1 (by rfl) ⟨572261, by rfl⟩ : syracuseStep 763015 = 1144523) B1144523
theorem B599303 : Blo 599292 599303 := bstep (se 1 (by rfl) ⟨449477, by rfl⟩ : syracuseStep 599303 = 898955) B898955
theorem B599311 : Blo 599292 599311 := bstep (se 1 (by rfl) ⟨449483, by rfl⟩ : syracuseStep 599311 = 898967) B898967
theorem B2434337 : Blo 599292 2434337 := bstep (se 2 (by rfl) ⟨912876, by rfl⟩ : syracuseStep 2434337 = 1825753) B1825753
theorem B599355 : Blo 599292 599355 := bstep (se 1 (by rfl) ⟨449516, by rfl⟩ : syracuseStep 599355 = 899033) B899033
theorem B1713469 : Blo 599292 1713469 := bstep (se 3 (by rfl) ⟨321275, by rfl⟩ : syracuseStep 1713469 = 642551) B642551
theorem B599431 : Blo 599292 599431 := bstep (se 1 (by rfl) ⟨449573, by rfl⟩ : syracuseStep 599431 = 899147) B899147
theorem B1353095 : Blo 599292 1353095 := bstep (se 1 (by rfl) ⟨1014821, by rfl⟩ : syracuseStep 1353095 = 2029643) B2029643
theorem B599439 : Blo 599292 599439 := bstep (se 1 (by rfl) ⟨449579, by rfl⟩ : syracuseStep 599439 = 899159) B899159
theorem B599483 : Blo 599292 599483 := bstep (se 1 (by rfl) ⟨449612, by rfl⟩ : syracuseStep 599483 = 899225) B899225
theorem B10429955 : Blo 599292 10429955 := bstep (se 1 (by rfl) ⟨7822466, by rfl⟩ : syracuseStep 10429955 = 15644933) B15644933
theorem B599559 : Blo 599292 599559 := bstep (se 1 (by rfl) ⟨449669, by rfl⟩ : syracuseStep 599559 = 899339) B899339
theorem B599567 : Blo 599292 599567 := bstep (se 1 (by rfl) ⟨449675, by rfl⟩ : syracuseStep 599567 = 899351) B899351
theorem B1517089 : Blo 599292 1517089 := bstep (se 2 (by rfl) ⟨568908, by rfl⟩ : syracuseStep 1517089 = 1137817) B1137817
theorem B763435 : Blo 599292 763435 := bstep (se 1 (by rfl) ⟨572576, by rfl⟩ : syracuseStep 763435 = 1145153) B1145153
theorem B960059 : Blo 599292 960059 := bstep (se 1 (by rfl) ⟨720044, by rfl⟩ : syracuseStep 960059 = 1440089) B1440089
theorem B599611 : Blo 599292 599611 := bstep (se 1 (by rfl) ⟨449708, by rfl⟩ : syracuseStep 599611 = 899417) B899417
theorem B1353275 : Blo 599292 1353275 := bstep (se 1 (by rfl) ⟨1014956, by rfl⟩ : syracuseStep 1353275 = 2029913) B2029913
theorem B599687 : Blo 599292 599687 := bstep (se 1 (by rfl) ⟨449765, by rfl⟩ : syracuseStep 599687 = 899531) B899531
theorem B599695 : Blo 599292 599695 := bstep (se 1 (by rfl) ⟨449771, by rfl⟩ : syracuseStep 599695 = 899543) B899543
theorem B1713811 : Blo 599292 1713811 := bstep (se 1 (by rfl) ⟨1285358, by rfl⟩ : syracuseStep 1713811 = 2570717) B2570717
theorem B1353401 : Blo 599292 1353401 := bstep (se 2 (by rfl) ⟨507525, by rfl⟩ : syracuseStep 1353401 = 1015051) B1015051
theorem B599739 : Blo 599292 599739 := bstep (se 1 (by rfl) ⟨449804, by rfl⟩ : syracuseStep 599739 = 899609) B899609
theorem B599815 : Blo 599292 599815 := bstep (se 1 (by rfl) ⟨449861, by rfl⟩ : syracuseStep 599815 = 899723) B899723
theorem B599823 : Blo 599292 599823 := bstep (se 1 (by rfl) ⟨449867, by rfl⟩ : syracuseStep 599823 = 899735) B899735
theorem B599867 : Blo 599292 599867 := bstep (se 1 (by rfl) ⟨449900, by rfl⟩ : syracuseStep 599867 = 899801) B899801
theorem B599943 : Blo 599292 599943 := bstep (se 1 (by rfl) ⟨449957, by rfl⟩ : syracuseStep 599943 = 899915) B899915
theorem B2434951 : Blo 599292 2434951 := bstep (se 1 (by rfl) ⟨1826213, by rfl⟩ : syracuseStep 2434951 = 3652427) B3652427
theorem B599951 : Blo 599292 599951 := bstep (se 1 (by rfl) ⟨449963, by rfl⟩ : syracuseStep 599951 = 899927) B899927
theorem B599995 : Blo 599292 599995 := bstep (se 1 (by rfl) ⟨449996, by rfl⟩ : syracuseStep 599995 = 899993) B899993
theorem B600071 : Blo 599292 600071 := bstep (se 1 (by rfl) ⟨450053, by rfl⟩ : syracuseStep 600071 = 900107) B900107
theorem B600079 : Blo 599292 600079 := bstep (se 1 (by rfl) ⟨450059, by rfl⟩ : syracuseStep 600079 = 900119) B900119
theorem B1353743 : Blo 599292 1353743 := bstep (se 1 (by rfl) ⟨1015307, by rfl⟩ : syracuseStep 1353743 = 2030615) B2030615
theorem B1353761 : Blo 599292 1353761 := bstep (se 2 (by rfl) ⟨507660, by rfl⟩ : syracuseStep 1353761 = 1015321) B1015321
theorem B600123 : Blo 599292 600123 := bstep (se 1 (by rfl) ⟨450092, by rfl⟩ : syracuseStep 600123 = 900185) B900185
theorem B1517687 : Blo 599292 1517687 := bstep (se 1 (by rfl) ⟨1138265, by rfl⟩ : syracuseStep 1517687 = 2276531) B2276531
theorem B600199 : Blo 599292 600199 := bstep (se 1 (by rfl) ⟨450149, by rfl⟩ : syracuseStep 600199 = 900299) B900299
theorem B600207 : Blo 599292 600207 := bstep (se 1 (by rfl) ⟨450155, by rfl⟩ : syracuseStep 600207 = 900311) B900311
theorem B600251 : Blo 599292 600251 := bstep (se 1 (by rfl) ⟨450188, by rfl⟩ : syracuseStep 600251 = 900377) B900377
theorem B600327 : Blo 599292 600327 := bstep (se 1 (by rfl) ⟨450245, by rfl⟩ : syracuseStep 600327 = 900491) B900491
theorem B600335 : Blo 599292 600335 := bstep (se 1 (by rfl) ⟨450251, by rfl⟩ : syracuseStep 600335 = 900503) B900503
theorem B600379 : Blo 599292 600379 := bstep (se 1 (by rfl) ⟨450284, by rfl⟩ : syracuseStep 600379 = 900569) B900569
theorem B1354103 : Blo 599292 1354103 := bstep (se 1 (by rfl) ⟨1015577, by rfl⟩ : syracuseStep 1354103 = 2031155) B2031155
theorem B600455 : Blo 599292 600455 := bstep (se 1 (by rfl) ⟨450341, by rfl⟩ : syracuseStep 600455 = 900683) B900683
theorem B600463 : Blo 599292 600463 := bstep (se 1 (by rfl) ⟨450347, by rfl⟩ : syracuseStep 600463 = 900695) B900695
theorem B600507 : Blo 599292 600507 := bstep (se 1 (by rfl) ⟨450380, by rfl⟩ : syracuseStep 600507 = 900761) B900761
theorem B600583 : Blo 599292 600583 := bstep (se 1 (by rfl) ⟨450437, by rfl⟩ : syracuseStep 600583 = 900875) B900875
theorem B1714699 : Blo 599292 1714699 := bstep (se 1 (by rfl) ⟨1286024, by rfl⟩ : syracuseStep 1714699 = 2572049) B2572049
theorem B600591 : Blo 599292 600591 := bstep (se 1 (by rfl) ⟨450443, by rfl⟩ : syracuseStep 600591 = 900887) B900887
theorem B5777963 : Blo 599292 5777963 := bstep (se 1 (by rfl) ⟨4333472, by rfl⟩ : syracuseStep 5777963 = 8666945) B8666945
theorem B1354283 : Blo 599292 1354283 := bstep (se 1 (by rfl) ⟨1015712, by rfl⟩ : syracuseStep 1354283 = 2031425) B2031425
theorem B600635 : Blo 599292 600635 := bstep (se 1 (by rfl) ⟨450476, by rfl⟩ : syracuseStep 600635 = 900953) B900953
theorem B600711 : Blo 599292 600711 := bstep (se 1 (by rfl) ⟨450533, by rfl⟩ : syracuseStep 600711 = 901067) B901067
theorem B600719 : Blo 599292 600719 := bstep (se 1 (by rfl) ⟨450539, by rfl⟩ : syracuseStep 600719 = 901079) B901079
theorem B600763 : Blo 599292 600763 := bstep (se 1 (by rfl) ⟨450572, by rfl⟩ : syracuseStep 600763 = 901145) B901145
theorem B600839 : Blo 599292 600839 := bstep (se 1 (by rfl) ⟨450629, by rfl⟩ : syracuseStep 600839 = 901259) B901259
theorem B600847 : Blo 599292 600847 := bstep (se 1 (by rfl) ⟨450635, by rfl⟩ : syracuseStep 600847 = 901271) B901271
theorem B5778191 : Blo 599292 5778191 := bstep (se 1 (by rfl) ⟨4333643, by rfl⟩ : syracuseStep 5778191 = 8667287) B8667287
theorem B600891 : Blo 599292 600891 := bstep (se 1 (by rfl) ⟨450668, by rfl⟩ : syracuseStep 600891 = 901337) B901337
theorem B600967 : Blo 599292 600967 := bstep (se 1 (by rfl) ⟨450725, by rfl⟩ : syracuseStep 600967 = 901451) B901451
theorem B600975 : Blo 599292 600975 := bstep (se 1 (by rfl) ⟨450731, by rfl⟩ : syracuseStep 600975 = 901463) B901463
theorem B1354643 : Blo 599292 1354643 := bstep (se 1 (by rfl) ⟨1015982, by rfl⟩ : syracuseStep 1354643 = 2031965) B2031965
theorem B601019 : Blo 599292 601019 := bstep (se 1 (by rfl) ⟨450764, by rfl⟩ : syracuseStep 601019 = 901529) B901529
theorem B1354697 : Blo 599292 1354697 := bstep (se 2 (by rfl) ⟨508011, by rfl⟩ : syracuseStep 1354697 = 1016023) B1016023
theorem B1715201 : Blo 599292 1715201 := bstep (se 2 (by rfl) ⟨643200, by rfl⟩ : syracuseStep 1715201 = 1286401) B1286401
theorem B601095 : Blo 599292 601095 := bstep (se 1 (by rfl) ⟨450821, by rfl⟩ : syracuseStep 601095 = 901643) B901643
theorem B601103 : Blo 599292 601103 := bstep (se 1 (by rfl) ⟨450827, by rfl⟩ : syracuseStep 601103 = 901655) B901655
theorem B601147 : Blo 599292 601147 := bstep (se 1 (by rfl) ⟨450860, by rfl⟩ : syracuseStep 601147 = 901721) B901721
theorem B601223 : Blo 599292 601223 := bstep (se 1 (by rfl) ⟨450917, by rfl⟩ : syracuseStep 601223 = 901835) B901835
theorem B601231 : Blo 599292 601231 := bstep (se 1 (by rfl) ⟨450923, by rfl⟩ : syracuseStep 601231 = 901847) B901847
theorem B601275 : Blo 599292 601275 := bstep (se 1 (by rfl) ⟨450956, by rfl⟩ : syracuseStep 601275 = 901913) B901913
theorem B601351 : Blo 599292 601351 := bstep (se 1 (by rfl) ⟨451013, by rfl⟩ : syracuseStep 601351 = 902027) B902027
theorem B601359 : Blo 599292 601359 := bstep (se 1 (by rfl) ⟨451019, by rfl⟩ : syracuseStep 601359 = 902039) B902039
theorem B601403 : Blo 599292 601403 := bstep (se 1 (by rfl) ⟨451052, by rfl⟩ : syracuseStep 601403 = 902105) B902105
theorem B1715543 : Blo 599292 1715543 := bstep (se 1 (by rfl) ⟨1286657, by rfl⟩ : syracuseStep 1715543 = 2573315) B2573315
theorem B1518983 : Blo 599292 1518983 := bstep (se 1 (by rfl) ⟨1139237, by rfl⟩ : syracuseStep 1518983 = 2278475) B2278475
theorem B601479 : Blo 599292 601479 := bstep (se 1 (by rfl) ⟨451109, by rfl⟩ : syracuseStep 601479 = 902219) B902219
theorem B601487 : Blo 599292 601487 := bstep (se 1 (by rfl) ⟨451115, by rfl⟩ : syracuseStep 601487 = 902231) B902231
theorem B1519033 : Blo 599292 1519033 := bstep (se 2 (by rfl) ⟨569637, by rfl⟩ : syracuseStep 1519033 = 1139275) B1139275
theorem B601531 : Blo 599292 601531 := bstep (se 1 (by rfl) ⟨451148, by rfl⟩ : syracuseStep 601531 = 902297) B902297
theorem B601607 : Blo 599292 601607 := bstep (se 1 (by rfl) ⟨451205, by rfl⟩ : syracuseStep 601607 = 902411) B902411
theorem B601615 : Blo 599292 601615 := bstep (se 1 (by rfl) ⟨451211, by rfl⟩ : syracuseStep 601615 = 902423) B902423
theorem B2436637 : Blo 599292 2436637 := bstep (se 3 (by rfl) ⟨456869, by rfl⟩ : syracuseStep 2436637 = 913739) B913739
theorem B601659 : Blo 599292 601659 := bstep (se 1 (by rfl) ⟨451244, by rfl⟩ : syracuseStep 601659 = 902489) B902489
theorem B601735 : Blo 599292 601735 := bstep (se 1 (by rfl) ⟨451301, by rfl⟩ : syracuseStep 601735 = 902603) B902603
theorem B1355399 : Blo 599292 1355399 := bstep (se 1 (by rfl) ⟨1016549, by rfl⟩ : syracuseStep 1355399 = 2033099) B2033099
theorem B601743 : Blo 599292 601743 := bstep (se 1 (by rfl) ⟨451307, by rfl⟩ : syracuseStep 601743 = 902615) B902615
theorem B601787 : Blo 599292 601787 := bstep (se 1 (by rfl) ⟨451340, by rfl⟩ : syracuseStep 601787 = 902681) B902681
theorem B3845825 : Blo 599292 3845825 := bstep (se 2 (by rfl) ⟨1442184, by rfl⟩ : syracuseStep 3845825 = 2884369) B2884369
theorem B601863 : Blo 599292 601863 := bstep (se 1 (by rfl) ⟨451397, by rfl⟩ : syracuseStep 601863 = 902795) B902795
theorem B601871 : Blo 599292 601871 := bstep (se 1 (by rfl) ⟨451403, by rfl⟩ : syracuseStep 601871 = 902807) B902807
theorem B6827813 : Blo 599292 6827813 := bstep (se 4 (by rfl) ⟨640107, by rfl⟩ : syracuseStep 6827813 = 1280215) B1280215
theorem B601915 : Blo 599292 601915 := bstep (se 1 (by rfl) ⟨451436, by rfl⟩ : syracuseStep 601915 = 902873) B902873
theorem B1355579 : Blo 599292 1355579 := bstep (se 1 (by rfl) ⟨1016684, by rfl⟩ : syracuseStep 1355579 = 2033369) B2033369
theorem B601991 : Blo 599292 601991 := bstep (se 1 (by rfl) ⟨451493, by rfl⟩ : syracuseStep 601991 = 902987) B902987
theorem B601999 : Blo 599292 601999 := bstep (se 1 (by rfl) ⟨451499, by rfl⟩ : syracuseStep 601999 = 902999) B902999
theorem B1355705 : Blo 599292 1355705 := bstep (se 2 (by rfl) ⟨508389, by rfl⟩ : syracuseStep 1355705 = 1016779) B1016779
theorem B602043 : Blo 599292 602043 := bstep (se 1 (by rfl) ⟨451532, by rfl⟩ : syracuseStep 602043 = 903065) B903065
theorem B10399691 : Blo 599292 10399691 := bstep (se 1 (by rfl) ⟨7799768, by rfl⟩ : syracuseStep 10399691 = 15599537) B15599537
theorem B602119 : Blo 599292 602119 := bstep (se 1 (by rfl) ⟨451589, by rfl⟩ : syracuseStep 602119 = 903179) B903179
theorem B1519631 : Blo 599292 1519631 := bstep (se 1 (by rfl) ⟨1139723, by rfl⟩ : syracuseStep 1519631 = 2279447) B2279447
theorem B602127 : Blo 599292 602127 := bstep (se 1 (by rfl) ⟨451595, by rfl⟩ : syracuseStep 602127 = 903191) B903191
theorem B602171 : Blo 599292 602171 := bstep (se 1 (by rfl) ⟨451628, by rfl⟩ : syracuseStep 602171 = 903257) B903257
theorem B1028231 : Blo 599292 1028231 := bstep (se 1 (by rfl) ⟨771173, by rfl⟩ : syracuseStep 1028231 = 1542347) B1542347
theorem B602247 : Blo 599292 602247 := bstep (se 1 (by rfl) ⟨451685, by rfl⟩ : syracuseStep 602247 = 903371) B903371
theorem B602255 : Blo 599292 602255 := bstep (se 1 (by rfl) ⟨451691, by rfl⟩ : syracuseStep 602255 = 903383) B903383
theorem B602299 : Blo 599292 602299 := bstep (se 1 (by rfl) ⟨451724, by rfl⟩ : syracuseStep 602299 = 903449) B903449
theorem B602375 : Blo 599292 602375 := bstep (se 1 (by rfl) ⟨451781, by rfl⟩ : syracuseStep 602375 = 903563) B903563
theorem B602383 : Blo 599292 602383 := bstep (se 1 (by rfl) ⟨451787, by rfl⟩ : syracuseStep 602383 = 903575) B903575
theorem B1356047 : Blo 599292 1356047 := bstep (se 1 (by rfl) ⟨1017035, by rfl⟩ : syracuseStep 1356047 = 2034071) B2034071
theorem B1356065 : Blo 599292 1356065 := bstep (se 2 (by rfl) ⟨508524, by rfl⟩ : syracuseStep 1356065 = 1017049) B1017049
theorem B602427 : Blo 599292 602427 := bstep (se 1 (by rfl) ⟨451820, by rfl⟩ : syracuseStep 602427 = 903641) B903641
theorem B602503 : Blo 599292 602503 := bstep (se 1 (by rfl) ⟨451877, by rfl⟩ : syracuseStep 602503 = 903755) B903755
theorem B602511 : Blo 599292 602511 := bstep (se 1 (by rfl) ⟨451883, by rfl⟩ : syracuseStep 602511 = 903767) B903767
theorem B602555 : Blo 599292 602555 := bstep (se 1 (by rfl) ⟨451916, by rfl⟩ : syracuseStep 602555 = 903833) B903833
theorem B602631 : Blo 599292 602631 := bstep (se 1 (by rfl) ⟨451973, by rfl⟩ : syracuseStep 602631 = 903947) B903947
theorem B602639 : Blo 599292 602639 := bstep (se 1 (by rfl) ⟨451979, by rfl⟩ : syracuseStep 602639 = 903959) B903959
theorem B602683 : Blo 599292 602683 := bstep (se 1 (by rfl) ⟨452012, by rfl⟩ : syracuseStep 602683 = 904025) B904025
theorem B1356407 : Blo 599292 1356407 := bstep (se 1 (by rfl) ⟨1017305, by rfl⟩ : syracuseStep 1356407 = 2034611) B2034611
theorem B602759 : Blo 599292 602759 := bstep (se 1 (by rfl) ⟨452069, by rfl⟩ : syracuseStep 602759 = 904139) B904139
theorem B602767 : Blo 599292 602767 := bstep (se 1 (by rfl) ⟨452075, by rfl⟩ : syracuseStep 602767 = 904151) B904151
theorem B602811 : Blo 599292 602811 := bstep (se 1 (by rfl) ⟨452108, by rfl⟩ : syracuseStep 602811 = 904217) B904217
theorem B1520329 : Blo 599292 1520329 := bstep (se 2 (by rfl) ⟨570123, by rfl⟩ : syracuseStep 1520329 = 1140247) B1140247
theorem B2568905 : Blo 599292 2568905 := bstep (se 2 (by rfl) ⟨963339, by rfl⟩ : syracuseStep 2568905 = 1926679) B1926679
theorem B3650285 : Blo 599292 3650285 := bstep (se 3 (by rfl) ⟨684428, by rfl⟩ : syracuseStep 3650285 = 1368857) B1368857
theorem B2568941 : Blo 599292 2568941 := bstep (se 3 (by rfl) ⟨481676, by rfl⟩ : syracuseStep 2568941 = 963353) B963353
theorem B602887 : Blo 599292 602887 := bstep (se 1 (by rfl) ⟨452165, by rfl⟩ : syracuseStep 602887 = 904331) B904331
theorem B602895 : Blo 599292 602895 := bstep (se 1 (by rfl) ⟨452171, by rfl⟩ : syracuseStep 602895 = 904343) B904343
theorem B1651499 : Blo 599292 1651499 := bstep (se 1 (by rfl) ⟨1238624, by rfl⟩ : syracuseStep 1651499 = 2477249) B2477249
theorem B1356587 : Blo 599292 1356587 := bstep (se 1 (by rfl) ⟨1017440, by rfl⟩ : syracuseStep 1356587 = 2034881) B2034881
theorem B602939 : Blo 599292 602939 := bstep (se 1 (by rfl) ⟨452204, by rfl⟩ : syracuseStep 602939 = 904409) B904409
theorem B1520471 : Blo 599292 1520471 := bstep (se 1 (by rfl) ⟨1140353, by rfl⟩ : syracuseStep 1520471 = 2280707) B2280707
theorem B603015 : Blo 599292 603015 := bstep (se 1 (by rfl) ⟨452261, by rfl⟩ : syracuseStep 603015 = 904523) B904523
theorem B603023 : Blo 599292 603023 := bstep (se 1 (by rfl) ⟨452267, by rfl⟩ : syracuseStep 603023 = 904535) B904535
theorem B603067 : Blo 599292 603067 := bstep (se 1 (by rfl) ⟨452300, by rfl⟩ : syracuseStep 603067 = 904601) B904601
theorem B603143 : Blo 599292 603143 := bstep (se 1 (by rfl) ⟨452357, by rfl⟩ : syracuseStep 603143 = 904715) B904715
theorem B603151 : Blo 599292 603151 := bstep (se 1 (by rfl) ⟨452363, by rfl⟩ : syracuseStep 603151 = 904727) B904727
theorem B603195 : Blo 599292 603195 := bstep (se 1 (by rfl) ⟨452396, by rfl⟩ : syracuseStep 603195 = 904793) B904793
theorem B603271 : Blo 599292 603271 := bstep (se 1 (by rfl) ⟨452453, by rfl⟩ : syracuseStep 603271 = 904907) B904907
theorem B603279 : Blo 599292 603279 := bstep (se 1 (by rfl) ⟨452459, by rfl⟩ : syracuseStep 603279 = 904919) B904919
theorem B1356947 : Blo 599292 1356947 := bstep (se 1 (by rfl) ⟨1017710, by rfl⟩ : syracuseStep 1356947 = 2035421) B2035421
theorem B1717433 : Blo 599292 1717433 := bstep (se 2 (by rfl) ⟨644037, by rfl⟩ : syracuseStep 1717433 = 1288075) B1288075
theorem B1357001 : Blo 599292 1357001 := bstep (se 2 (by rfl) ⟨508875, by rfl⟩ : syracuseStep 1357001 = 1017751) B1017751
theorem B4634003 : Blo 599292 4634003 := bstep (se 1 (by rfl) ⟨3475502, by rfl⟩ : syracuseStep 4634003 = 6951005) B6951005
theorem B2569657 : Blo 599292 2569657 := bstep (se 2 (by rfl) ⟨963621, by rfl⟩ : syracuseStep 2569657 = 1927243) B1927243
theorem B12367667 : Blo 599292 12367667 := bstep (se 1 (by rfl) ⟨9275750, by rfl⟩ : syracuseStep 12367667 = 18551501) B18551501
theorem B3422087 : Blo 599292 3422087 := bstep (se 1 (by rfl) ⟨2566565, by rfl⟩ : syracuseStep 3422087 = 5133131) B5133131
theorem B899003 : Blo 599292 899003 := bstep (se 1 (by rfl) ⟨674252, by rfl⟩ : syracuseStep 899003 = 1348505) B1348505
theorem B899063 : Blo 599292 899063 := bstep (se 1 (by rfl) ⟨674297, by rfl⟩ : syracuseStep 899063 = 1348595) B1348595
theorem B899087 : Blo 599292 899087 := bstep (se 1 (by rfl) ⟨674315, by rfl⟩ : syracuseStep 899087 = 1348631) B1348631
theorem B899129 : Blo 599292 899129 := bstep (se 2 (by rfl) ⟨337173, by rfl⟩ : syracuseStep 899129 = 674347) B674347
theorem B899207 : Blo 599292 899207 := bstep (se 1 (by rfl) ⟨674405, by rfl⟩ : syracuseStep 899207 = 1348811) B1348811
theorem B899243 : Blo 599292 899243 := bstep (se 1 (by rfl) ⟨674432, by rfl⟩ : syracuseStep 899243 = 1348865) B1348865
theorem B899273 : Blo 599292 899273 := bstep (se 2 (by rfl) ⟨337227, by rfl⟩ : syracuseStep 899273 = 674455) B674455
theorem B899387 : Blo 599292 899387 := bstep (se 1 (by rfl) ⟨674540, by rfl⟩ : syracuseStep 899387 = 1349081) B1349081
theorem B899447 : Blo 599292 899447 := bstep (se 1 (by rfl) ⟨674585, by rfl⟩ : syracuseStep 899447 = 1349171) B1349171
theorem B899471 : Blo 599292 899471 := bstep (se 1 (by rfl) ⟨674603, by rfl⟩ : syracuseStep 899471 = 1349207) B1349207
theorem B899513 : Blo 599292 899513 := bstep (se 2 (by rfl) ⟨337317, by rfl⟩ : syracuseStep 899513 = 674635) B674635
theorem B3258883 : Blo 599292 3258883 := bstep (se 1 (by rfl) ⟨2444162, by rfl⟩ : syracuseStep 3258883 = 4888325) B4888325
theorem B899591 : Blo 599292 899591 := bstep (se 1 (by rfl) ⟨674693, by rfl⟩ : syracuseStep 899591 = 1349387) B1349387
theorem B899627 : Blo 599292 899627 := bstep (se 1 (by rfl) ⟨674720, by rfl⟩ : syracuseStep 899627 = 1349441) B1349441
theorem B899657 : Blo 599292 899657 := bstep (se 2 (by rfl) ⟨337371, by rfl⟩ : syracuseStep 899657 = 674743) B674743
theorem B899771 : Blo 599292 899771 := bstep (se 1 (by rfl) ⟨674828, by rfl⟩ : syracuseStep 899771 = 1349657) B1349657
theorem B899831 : Blo 599292 899831 := bstep (se 1 (by rfl) ⟨674873, by rfl⟩ : syracuseStep 899831 = 1349747) B1349747
theorem B4569857 : Blo 599292 4569857 := bstep (se 2 (by rfl) ⟨1713696, by rfl⟩ : syracuseStep 4569857 = 3427393) B3427393
theorem B899855 : Blo 599292 899855 := bstep (se 1 (by rfl) ⟨674891, by rfl⟩ : syracuseStep 899855 = 1349783) B1349783
theorem B899897 : Blo 599292 899897 := bstep (se 2 (by rfl) ⟨337461, by rfl⟩ : syracuseStep 899897 = 674923) B674923
theorem B1522547 : Blo 599292 1522547 := bstep (se 1 (by rfl) ⟨1141910, by rfl⟩ : syracuseStep 1522547 = 2283821) B2283821
theorem B899975 : Blo 599292 899975 := bstep (se 1 (by rfl) ⟨674981, by rfl⟩ : syracuseStep 899975 = 1349963) B1349963
theorem B2898823 : Blo 599292 2898823 := bstep (se 1 (by rfl) ⟨2174117, by rfl⟩ : syracuseStep 2898823 = 4348235) B4348235
theorem B900011 : Blo 599292 900011 := bstep (se 1 (by rfl) ⟨675008, by rfl⟩ : syracuseStep 900011 = 1350017) B1350017
theorem B900041 : Blo 599292 900041 := bstep (se 2 (by rfl) ⟨337515, by rfl⟩ : syracuseStep 900041 = 675031) B675031
theorem B2276363 : Blo 599292 2276363 := bstep (se 1 (by rfl) ⟨1707272, by rfl⟩ : syracuseStep 2276363 = 3414545) B3414545
theorem B3652619 : Blo 599292 3652619 := bstep (se 1 (by rfl) ⟨2739464, by rfl⟩ : syracuseStep 3652619 = 5478929) B5478929
theorem B900155 : Blo 599292 900155 := bstep (se 1 (by rfl) ⟨675116, by rfl⟩ : syracuseStep 900155 = 1350233) B1350233
theorem B3423293 : Blo 599292 3423293 := bstep (se 3 (by rfl) ⟨641867, by rfl⟩ : syracuseStep 3423293 = 1283735) B1283735
theorem B900215 : Blo 599292 900215 := bstep (se 1 (by rfl) ⟨675161, by rfl⟩ : syracuseStep 900215 = 1350323) B1350323
theorem B900239 : Blo 599292 900239 := bstep (se 1 (by rfl) ⟨675179, by rfl⟩ : syracuseStep 900239 = 1350359) B1350359
theorem B900281 : Blo 599292 900281 := bstep (se 2 (by rfl) ⟨337605, by rfl⟩ : syracuseStep 900281 = 675211) B675211
theorem B900359 : Blo 599292 900359 := bstep (se 1 (by rfl) ⟨675269, by rfl⟩ : syracuseStep 900359 = 1350539) B1350539
theorem B900395 : Blo 599292 900395 := bstep (se 1 (by rfl) ⟨675296, by rfl⟩ : syracuseStep 900395 = 1350593) B1350593
theorem B8207675 : Blo 599292 8207675 := bstep (se 1 (by rfl) ⟨6155756, by rfl⟩ : syracuseStep 8207675 = 12311513) B12311513
theorem B900425 : Blo 599292 900425 := bstep (se 2 (by rfl) ⟨337659, by rfl⟩ : syracuseStep 900425 = 675319) B675319
theorem B1523063 : Blo 599292 1523063 := bstep (se 1 (by rfl) ⟨1142297, by rfl⟩ : syracuseStep 1523063 = 2284595) B2284595
theorem B6864263 : Blo 599292 6864263 := bstep (se 1 (by rfl) ⟨5148197, by rfl⟩ : syracuseStep 6864263 = 10296395) B10296395
theorem B900539 : Blo 599292 900539 := bstep (se 1 (by rfl) ⟨675404, by rfl⟩ : syracuseStep 900539 = 1350809) B1350809
theorem B900599 : Blo 599292 900599 := bstep (se 1 (by rfl) ⟨675449, by rfl⟩ : syracuseStep 900599 = 1350899) B1350899
theorem B41729539 : Blo 599292 41729539 := bstep (se 1 (by rfl) ⟨31297154, by rfl⟩ : syracuseStep 41729539 = 62594309) B62594309
theorem B900623 : Blo 599292 900623 := bstep (se 1 (by rfl) ⟨675467, by rfl⟩ : syracuseStep 900623 = 1350935) B1350935
theorem B900665 : Blo 599292 900665 := bstep (se 2 (by rfl) ⟨337749, by rfl⟩ : syracuseStep 900665 = 675499) B675499
theorem B900743 : Blo 599292 900743 := bstep (se 1 (by rfl) ⟨675557, by rfl⟩ : syracuseStep 900743 = 1351115) B1351115
theorem B1621657 : Blo 599292 1621657 := bstep (se 2 (by rfl) ⟨608121, by rfl⟩ : syracuseStep 1621657 = 1216243) B1216243
theorem B900779 : Blo 599292 900779 := bstep (se 1 (by rfl) ⟨675584, by rfl⟩ : syracuseStep 900779 = 1351169) B1351169
theorem B900809 : Blo 599292 900809 := bstep (se 2 (by rfl) ⟨337803, by rfl⟩ : syracuseStep 900809 = 675607) B675607
theorem B2572033 : Blo 599292 2572033 := bstep (se 2 (by rfl) ⟨964512, by rfl⟩ : syracuseStep 2572033 = 1929025) B1929025
theorem B900923 : Blo 599292 900923 := bstep (se 1 (by rfl) ⟨675692, by rfl⟩ : syracuseStep 900923 = 1351385) B1351385
theorem B900983 : Blo 599292 900983 := bstep (se 1 (by rfl) ⟨675737, by rfl⟩ : syracuseStep 900983 = 1351475) B1351475
theorem B901007 : Blo 599292 901007 := bstep (se 1 (by rfl) ⟨675755, by rfl⟩ : syracuseStep 901007 = 1351511) B1351511
theorem B2277305 : Blo 599292 2277305 := bstep (se 2 (by rfl) ⟨853989, by rfl⟩ : syracuseStep 2277305 = 1707979) B1707979
theorem B901049 : Blo 599292 901049 := bstep (se 2 (by rfl) ⟨337893, by rfl⟩ : syracuseStep 901049 = 675787) B675787
theorem B901127 : Blo 599292 901127 := bstep (se 1 (by rfl) ⟨675845, by rfl⟩ : syracuseStep 901127 = 1351691) B1351691
theorem B901163 : Blo 599292 901163 := bstep (se 1 (by rfl) ⟨675872, by rfl⟩ : syracuseStep 901163 = 1351745) B1351745
theorem B901193 : Blo 599292 901193 := bstep (se 2 (by rfl) ⟨337947, by rfl⟩ : syracuseStep 901193 = 675895) B675895
theorem B901307 : Blo 599292 901307 := bstep (se 1 (by rfl) ⟨675980, by rfl⟩ : syracuseStep 901307 = 1351961) B1351961
theorem B9257161 : Blo 599292 9257161 := bstep (se 2 (by rfl) ⟨3471435, by rfl⟩ : syracuseStep 9257161 = 6942871) B6942871
theorem B901367 : Blo 599292 901367 := bstep (se 1 (by rfl) ⟨676025, by rfl⟩ : syracuseStep 901367 = 1352051) B1352051
theorem B901391 : Blo 599292 901391 := bstep (se 1 (by rfl) ⟨676043, by rfl⟩ : syracuseStep 901391 = 1352087) B1352087
theorem B901433 : Blo 599292 901433 := bstep (se 2 (by rfl) ⟨338037, by rfl⟩ : syracuseStep 901433 = 676075) B676075
theorem B1524055 : Blo 599292 1524055 := bstep (se 1 (by rfl) ⟨1143041, by rfl⟩ : syracuseStep 1524055 = 2286083) B2286083
theorem B901511 : Blo 599292 901511 := bstep (se 1 (by rfl) ⟨676133, by rfl⟩ : syracuseStep 901511 = 1352267) B1352267
theorem B901547 : Blo 599292 901547 := bstep (se 1 (by rfl) ⟨676160, by rfl⟩ : syracuseStep 901547 = 1352321) B1352321
theorem B901577 : Blo 599292 901577 := bstep (se 2 (by rfl) ⟨338091, by rfl⟩ : syracuseStep 901577 = 676183) B676183
theorem B1982987 : Blo 599292 1982987 := bstep (se 1 (by rfl) ⟨1487240, by rfl⟩ : syracuseStep 1982987 = 2974481) B2974481
theorem B901691 : Blo 599292 901691 := bstep (se 1 (by rfl) ⟨676268, by rfl⟩ : syracuseStep 901691 = 1352537) B1352537
theorem B901751 : Blo 599292 901751 := bstep (se 1 (by rfl) ⟨676313, by rfl⟩ : syracuseStep 901751 = 1352627) B1352627
theorem B1524359 : Blo 599292 1524359 := bstep (se 1 (by rfl) ⟨1143269, by rfl⟩ : syracuseStep 1524359 = 2286539) B2286539
theorem B901775 : Blo 599292 901775 := bstep (se 1 (by rfl) ⟨676331, by rfl⟩ : syracuseStep 901775 = 1352663) B1352663
theorem B901817 : Blo 599292 901817 := bstep (se 2 (by rfl) ⟨338181, by rfl⟩ : syracuseStep 901817 = 676363) B676363
theorem B901895 : Blo 599292 901895 := bstep (se 1 (by rfl) ⟨676421, by rfl⟩ : syracuseStep 901895 = 1352843) B1352843
theorem B1524491 : Blo 599292 1524491 := bstep (se 1 (by rfl) ⟨1143368, by rfl⟩ : syracuseStep 1524491 = 2286737) B2286737
theorem B11682575 : Blo 599292 11682575 := bstep (se 1 (by rfl) ⟨8761931, by rfl⟩ : syracuseStep 11682575 = 17523863) B17523863
theorem B3261221 : Blo 599292 3261221 := bstep (se 4 (by rfl) ⟨305739, by rfl⟩ : syracuseStep 3261221 = 611479) B611479
theorem B901931 : Blo 599292 901931 := bstep (se 1 (by rfl) ⟨676448, by rfl⟩ : syracuseStep 901931 = 1352897) B1352897
theorem B901961 : Blo 599292 901961 := bstep (se 2 (by rfl) ⟨338235, by rfl⟩ : syracuseStep 901961 = 676471) B676471
theorem B902075 : Blo 599292 902075 := bstep (se 1 (by rfl) ⟨676556, by rfl⟩ : syracuseStep 902075 = 1353113) B1353113
theorem B902135 : Blo 599292 902135 := bstep (se 1 (by rfl) ⟨676601, by rfl⟩ : syracuseStep 902135 = 1353203) B1353203
theorem B902159 : Blo 599292 902159 := bstep (se 1 (by rfl) ⟨676619, by rfl⟩ : syracuseStep 902159 = 1353239) B1353239
theorem B902201 : Blo 599292 902201 := bstep (se 2 (by rfl) ⟨338325, by rfl⟩ : syracuseStep 902201 = 676651) B676651
theorem B902279 : Blo 599292 902279 := bstep (se 1 (by rfl) ⟨676709, by rfl⟩ : syracuseStep 902279 = 1353419) B1353419
theorem B902315 : Blo 599292 902315 := bstep (se 1 (by rfl) ⟨676736, by rfl⟩ : syracuseStep 902315 = 1353473) B1353473
theorem B902345 : Blo 599292 902345 := bstep (se 2 (by rfl) ⟨338379, by rfl⟩ : syracuseStep 902345 = 676759) B676759
theorem B1525007 : Blo 599292 1525007 := bstep (se 1 (by rfl) ⟨1143755, by rfl⟩ : syracuseStep 1525007 = 2287511) B2287511
theorem B2934049 : Blo 599292 2934049 := bstep (se 2 (by rfl) ⟨1100268, by rfl⟩ : syracuseStep 2934049 = 2200537) B2200537
theorem B902459 : Blo 599292 902459 := bstep (se 1 (by rfl) ⟨676844, by rfl⟩ : syracuseStep 902459 = 1353689) B1353689
theorem B902519 : Blo 599292 902519 := bstep (se 1 (by rfl) ⟨676889, by rfl⟩ : syracuseStep 902519 = 1353779) B1353779
theorem B902543 : Blo 599292 902543 := bstep (se 1 (by rfl) ⟨676907, by rfl⟩ : syracuseStep 902543 = 1353815) B1353815
theorem B1525139 : Blo 599292 1525139 := bstep (se 1 (by rfl) ⟨1143854, by rfl⟩ : syracuseStep 1525139 = 2287709) B2287709
theorem B902585 : Blo 599292 902585 := bstep (se 2 (by rfl) ⟨338469, by rfl⟩ : syracuseStep 902585 = 676939) B676939
theorem B902663 : Blo 599292 902663 := bstep (se 1 (by rfl) ⟨676997, by rfl⟩ : syracuseStep 902663 = 1353995) B1353995
theorem B706063 : Blo 599292 706063 := bstep (se 1 (by rfl) ⟨529547, by rfl⟩ : syracuseStep 706063 = 1059095) B1059095
theorem B902699 : Blo 599292 902699 := bstep (se 1 (by rfl) ⟨677024, by rfl⟩ : syracuseStep 902699 = 1354049) B1354049
theorem B902729 : Blo 599292 902729 := bstep (se 2 (by rfl) ⟨338523, by rfl⟩ : syracuseStep 902729 = 677047) B677047
theorem B37045835 : Blo 599292 37045835 := bstep (se 1 (by rfl) ⟨27784376, by rfl⟩ : syracuseStep 37045835 = 55568753) B55568753
theorem B902843 : Blo 599292 902843 := bstep (se 1 (by rfl) ⟨677132, by rfl⟩ : syracuseStep 902843 = 1354265) B1354265
theorem B902903 : Blo 599292 902903 := bstep (se 1 (by rfl) ⟨677177, by rfl⟩ : syracuseStep 902903 = 1354355) B1354355
theorem B902927 : Blo 599292 902927 := bstep (se 1 (by rfl) ⟨677195, by rfl⟩ : syracuseStep 902927 = 1354391) B1354391
theorem B902969 : Blo 599292 902969 := bstep (se 2 (by rfl) ⟨338613, by rfl⟩ : syracuseStep 902969 = 677227) B677227
theorem B4867955 : Blo 599292 4867955 := bstep (se 1 (by rfl) ⟨3650966, by rfl⟩ : syracuseStep 4867955 = 7301933) B7301933
theorem B903047 : Blo 599292 903047 := bstep (se 1 (by rfl) ⟨677285, by rfl⟩ : syracuseStep 903047 = 1354571) B1354571
theorem B903083 : Blo 599292 903083 := bstep (se 1 (by rfl) ⟨677312, by rfl⟩ : syracuseStep 903083 = 1354625) B1354625
theorem B903113 : Blo 599292 903113 := bstep (se 2 (by rfl) ⟨338667, by rfl⟩ : syracuseStep 903113 = 677335) B677335
theorem B641039 : Blo 599292 641039 := bstep (se 1 (by rfl) ⟨480779, by rfl⟩ : syracuseStep 641039 = 961559) B961559
theorem B1624079 : Blo 599292 1624079 := bstep (se 1 (by rfl) ⟨1218059, by rfl⟩ : syracuseStep 1624079 = 2436119) B2436119
theorem B9783341 : Blo 599292 9783341 := bstep (se 3 (by rfl) ⟨1834376, by rfl⟩ : syracuseStep 9783341 = 3668753) B3668753
theorem B903227 : Blo 599292 903227 := bstep (se 1 (by rfl) ⟨677420, by rfl⟩ : syracuseStep 903227 = 1354841) B1354841
theorem B903287 : Blo 599292 903287 := bstep (se 1 (by rfl) ⟨677465, by rfl⟩ : syracuseStep 903287 = 1354931) B1354931
theorem B903311 : Blo 599292 903311 := bstep (se 1 (by rfl) ⟨677483, by rfl⟩ : syracuseStep 903311 = 1354967) B1354967
theorem B903353 : Blo 599292 903353 := bstep (se 2 (by rfl) ⟨338757, by rfl⟩ : syracuseStep 903353 = 677515) B677515
theorem B12503285 : Blo 599292 12503285 := bstep (se 5 (by rfl) ⟨586091, by rfl⟩ : syracuseStep 12503285 = 1172183) B1172183
theorem B641287 : Blo 599292 641287 := bstep (se 1 (by rfl) ⟨480965, by rfl⟩ : syracuseStep 641287 = 961931) B961931
theorem B903431 : Blo 599292 903431 := bstep (se 1 (by rfl) ⟨677573, by rfl⟩ : syracuseStep 903431 = 1355147) B1355147
theorem B903467 : Blo 599292 903467 := bstep (se 1 (by rfl) ⟨677600, by rfl⟩ : syracuseStep 903467 = 1355201) B1355201
theorem B17353025 : Blo 599292 17353025 := bstep (se 2 (by rfl) ⟨6507384, by rfl⟩ : syracuseStep 17353025 = 13014769) B13014769
theorem B903497 : Blo 599292 903497 := bstep (se 2 (by rfl) ⟨338811, by rfl⟩ : syracuseStep 903497 = 677623) B677623
theorem B2935187 : Blo 599292 2935187 := bstep (se 1 (by rfl) ⟨2201390, by rfl⟩ : syracuseStep 2935187 = 4402781) B4402781
theorem B903611 : Blo 599292 903611 := bstep (se 1 (by rfl) ⟨677708, by rfl⟩ : syracuseStep 903611 = 1355417) B1355417
theorem B903671 : Blo 599292 903671 := bstep (se 1 (by rfl) ⟨677753, by rfl⟩ : syracuseStep 903671 = 1355507) B1355507
theorem B1526273 : Blo 599292 1526273 := bstep (se 2 (by rfl) ⟨572352, by rfl⟩ : syracuseStep 1526273 = 1144705) B1144705
theorem B674311 : Blo 599292 674311 := bstep (se 1 (by rfl) ⟨505733, by rfl⟩ : syracuseStep 674311 = 1011467) B1011467
theorem B2279947 : Blo 599292 2279947 := bstep (se 1 (by rfl) ⟨1709960, by rfl⟩ : syracuseStep 2279947 = 3419921) B3419921
theorem B903695 : Blo 599292 903695 := bstep (se 1 (by rfl) ⟨677771, by rfl⟩ : syracuseStep 903695 = 1355543) B1355543
theorem B903737 : Blo 599292 903737 := bstep (se 2 (by rfl) ⟨338901, by rfl⟩ : syracuseStep 903737 = 677803) B677803
theorem B903815 : Blo 599292 903815 := bstep (se 1 (by rfl) ⟨677861, by rfl⟩ : syracuseStep 903815 = 1355723) B1355723
theorem B903851 : Blo 599292 903851 := bstep (se 1 (by rfl) ⟨677888, by rfl⟩ : syracuseStep 903851 = 1355777) B1355777
theorem B674491 : Blo 599292 674491 := bstep (se 1 (by rfl) ⟨505868, by rfl⟩ : syracuseStep 674491 = 1011737) B1011737
theorem B903881 : Blo 599292 903881 := bstep (se 2 (by rfl) ⟨338955, by rfl⟩ : syracuseStep 903881 = 677911) B677911
theorem B2444033 : Blo 599292 2444033 := bstep (se 2 (by rfl) ⟨916512, by rfl⟩ : syracuseStep 2444033 = 1833025) B1833025
theorem B2280251 : Blo 599292 2280251 := bstep (se 1 (by rfl) ⟨1710188, by rfl⟩ : syracuseStep 2280251 = 3420377) B3420377
theorem B903995 : Blo 599292 903995 := bstep (se 1 (by rfl) ⟨677996, by rfl⟩ : syracuseStep 903995 = 1355993) B1355993
theorem B904055 : Blo 599292 904055 := bstep (se 1 (by rfl) ⟨678041, by rfl⟩ : syracuseStep 904055 = 1356083) B1356083
theorem B1526647 : Blo 599292 1526647 := bstep (se 1 (by rfl) ⟨1144985, by rfl⟩ : syracuseStep 1526647 = 2289971) B2289971
theorem B904079 : Blo 599292 904079 := bstep (se 1 (by rfl) ⟨678059, by rfl⟩ : syracuseStep 904079 = 1356119) B1356119
theorem B904121 : Blo 599292 904121 := bstep (se 2 (by rfl) ⟨339045, by rfl⟩ : syracuseStep 904121 = 678091) B678091
theorem B904199 : Blo 599292 904199 := bstep (se 1 (by rfl) ⟨678149, by rfl⟩ : syracuseStep 904199 = 1356299) B1356299
theorem B4574231 : Blo 599292 4574231 := bstep (se 1 (by rfl) ⟨3430673, by rfl⟩ : syracuseStep 4574231 = 6861347) B6861347
theorem B904235 : Blo 599292 904235 := bstep (se 1 (by rfl) ⟨678176, by rfl⟩ : syracuseStep 904235 = 1356353) B1356353
theorem B642107 : Blo 599292 642107 := bstep (se 1 (by rfl) ⟨481580, by rfl⟩ : syracuseStep 642107 = 963161) B963161
theorem B904265 : Blo 599292 904265 := bstep (se 2 (by rfl) ⟨339099, by rfl⟩ : syracuseStep 904265 = 678199) B678199
theorem B1625203 : Blo 599292 1625203 := bstep (se 1 (by rfl) ⟨1218902, by rfl⟩ : syracuseStep 1625203 = 2437805) B2437805
theorem B23186573 : Blo 599292 23186573 := bstep (se 3 (by rfl) ⟨4347482, by rfl⟩ : syracuseStep 23186573 = 8694965) B8694965
theorem B674959 : Blo 599292 674959 := bstep (se 1 (by rfl) ⟨506219, by rfl⟩ : syracuseStep 674959 = 1012439) B1012439
theorem B904379 : Blo 599292 904379 := bstep (se 1 (by rfl) ⟨678284, by rfl⟩ : syracuseStep 904379 = 1356569) B1356569
theorem B904439 : Blo 599292 904439 := bstep (se 1 (by rfl) ⟨678329, by rfl⟩ : syracuseStep 904439 = 1356659) B1356659
theorem B904463 : Blo 599292 904463 := bstep (se 1 (by rfl) ⟨678347, by rfl⟩ : syracuseStep 904463 = 1356695) B1356695
theorem B2280737 : Blo 599292 2280737 := bstep (se 2 (by rfl) ⟨855276, by rfl⟩ : syracuseStep 2280737 = 1710553) B1710553
theorem B1527083 : Blo 599292 1527083 := bstep (se 1 (by rfl) ⟨1145312, by rfl⟩ : syracuseStep 1527083 = 2290625) B2290625
theorem B904505 : Blo 599292 904505 := bstep (se 2 (by rfl) ⟨339189, by rfl⟩ : syracuseStep 904505 = 678379) B678379
theorem B1756475 : Blo 599292 1756475 := bstep (se 1 (by rfl) ⟨1317356, by rfl⟩ : syracuseStep 1756475 = 2634713) B2634713
theorem B904583 : Blo 599292 904583 := bstep (se 1 (by rfl) ⟨678437, by rfl⟩ : syracuseStep 904583 = 1356875) B1356875
theorem B904619 : Blo 599292 904619 := bstep (se 1 (by rfl) ⟨678464, by rfl⟩ : syracuseStep 904619 = 1356929) B1356929
theorem B904649 : Blo 599292 904649 := bstep (se 2 (by rfl) ⟨339243, by rfl⟩ : syracuseStep 904649 = 678487) B678487
theorem B904763 : Blo 599292 904763 := bstep (se 1 (by rfl) ⟨678572, by rfl⟩ : syracuseStep 904763 = 1357145) B1357145
theorem B1920631 : Blo 599292 1920631 := bstep (se 1 (by rfl) ⟨1440473, by rfl⟩ : syracuseStep 1920631 = 2880947) B2880947
theorem B904823 : Blo 599292 904823 := bstep (se 1 (by rfl) ⟨678617, by rfl⟩ : syracuseStep 904823 = 1357235) B1357235
theorem B675463 : Blo 599292 675463 := bstep (se 1 (by rfl) ⟨506597, by rfl⟩ : syracuseStep 675463 = 1013195) B1013195
theorem B904847 : Blo 599292 904847 := bstep (se 1 (by rfl) ⟨678635, by rfl⟩ : syracuseStep 904847 = 1357271) B1357271
theorem B904889 : Blo 599292 904889 := bstep (se 2 (by rfl) ⟨339333, by rfl⟩ : syracuseStep 904889 = 678667) B678667
theorem B5132069 : Blo 599292 5132069 := bstep (se 4 (by rfl) ⟨481131, by rfl⟩ : syracuseStep 5132069 = 962263) B962263
theorem B675643 : Blo 599292 675643 := bstep (se 1 (by rfl) ⟨506732, by rfl⟩ : syracuseStep 675643 = 1013465) B1013465
theorem B1921067 : Blo 599292 1921067 := bstep (se 1 (by rfl) ⟨1440800, by rfl⟩ : syracuseStep 1921067 = 2881601) B2881601
theorem B2281709 : Blo 599292 2281709 := bstep (se 3 (by rfl) ⟨427820, by rfl⟩ : syracuseStep 2281709 = 855641) B855641
theorem B3035393 : Blo 599292 3035393 := bstep (se 2 (by rfl) ⟨1138272, by rfl⟩ : syracuseStep 3035393 = 2276545) B2276545
theorem B676111 : Blo 599292 676111 := bstep (se 1 (by rfl) ⟨507083, by rfl⟩ : syracuseStep 676111 = 1014167) B1014167
theorem B5132753 : Blo 599292 5132753 := bstep (se 2 (by rfl) ⟨1924782, by rfl⟩ : syracuseStep 5132753 = 3849565) B3849565
theorem B4346561 : Blo 599292 4346561 := bstep (se 2 (by rfl) ⟨1629960, by rfl⟩ : syracuseStep 4346561 = 3259921) B3259921
theorem B676615 : Blo 599292 676615 := bstep (se 1 (by rfl) ⟨507461, by rfl⟩ : syracuseStep 676615 = 1014923) B1014923
theorem B1626923 : Blo 599292 1626923 := bstep (se 1 (by rfl) ⟨1220192, by rfl⟩ : syracuseStep 1626923 = 2440385) B2440385
theorem B676795 : Blo 599292 676795 := bstep (se 1 (by rfl) ⟨507596, by rfl⟩ : syracuseStep 676795 = 1015193) B1015193
theorem B3036203 : Blo 599292 3036203 := bstep (se 1 (by rfl) ⟨2277152, by rfl⟩ : syracuseStep 3036203 = 4554305) B4554305
theorem B1922363 : Blo 599292 1922363 := bstep (se 1 (by rfl) ⟨1441772, by rfl⟩ : syracuseStep 1922363 = 2883545) B2883545
theorem B677263 : Blo 599292 677263 := bstep (se 1 (by rfl) ⟨507947, by rfl⟩ : syracuseStep 677263 = 1015895) B1015895
theorem B677767 : Blo 599292 677767 := bstep (se 1 (by rfl) ⟨508325, by rfl⟩ : syracuseStep 677767 = 1016651) B1016651
theorem B677947 : Blo 599292 677947 := bstep (se 1 (by rfl) ⟨508460, by rfl⟩ : syracuseStep 677947 = 1016921) B1016921
theorem B3037499 : Blo 599292 3037499 := bstep (se 1 (by rfl) ⟨2278124, by rfl⟩ : syracuseStep 3037499 = 4556249) B4556249
theorem B2283835 : Blo 599292 2283835 := bstep (se 1 (by rfl) ⟨1712876, by rfl⟩ : syracuseStep 2283835 = 3425753) B3425753
theorem B6510941 : Blo 599292 6510941 := bstep (se 3 (by rfl) ⟨1220801, by rfl⟩ : syracuseStep 6510941 = 2441603) B2441603
theorem B3037661 : Blo 599292 3037661 := bstep (se 3 (by rfl) ⟨569561, by rfl⟩ : syracuseStep 3037661 = 1139123) B1139123
theorem B678415 : Blo 599292 678415 := bstep (se 1 (by rfl) ⟨508811, by rfl⟩ : syracuseStep 678415 = 1017623) B1017623
theorem B3037985 : Blo 599292 3037985 := bstep (se 2 (by rfl) ⟨1139244, by rfl⟩ : syracuseStep 3037985 = 2278489) B2278489
theorem B2284321 : Blo 599292 2284321 := bstep (se 2 (by rfl) ⟨856620, by rfl⟩ : syracuseStep 2284321 = 1713241) B1713241
theorem B1629227 : Blo 599292 1629227 := bstep (se 1 (by rfl) ⟨1221920, by rfl⟩ : syracuseStep 1629227 = 2443841) B2443841
theorem B4873607 : Blo 599292 4873607 := bstep (se 1 (by rfl) ⟨3655205, by rfl⟩ : syracuseStep 4873607 = 7310411) B7310411
theorem B1138121 : Blo 599292 1138121 := bstep (se 2 (by rfl) ⟨426795, by rfl⟩ : syracuseStep 1138121 = 853591) B853591
theorem B1629811 : Blo 599292 1629811 := bstep (se 1 (by rfl) ⟨1222358, by rfl⟩ : syracuseStep 1629811 = 2444717) B2444717
theorem B3038957 : Blo 599292 3038957 := bstep (se 3 (by rfl) ⟨569804, by rfl⟩ : syracuseStep 3038957 = 1139609) B1139609
theorem B2285293 : Blo 599292 2285293 := bstep (se 3 (by rfl) ⟨428492, by rfl⟩ : syracuseStep 2285293 = 856985) B856985
theorem B2285597 : Blo 599292 2285597 := bstep (se 3 (by rfl) ⟨428549, by rfl⟩ : syracuseStep 2285597 = 857099) B857099
theorem B1138835 : Blo 599292 1138835 := bstep (se 1 (by rfl) ⟨854126, by rfl⟩ : syracuseStep 1138835 = 1708253) B1708253
theorem B1138873 : Blo 599292 1138873 := bstep (se 2 (by rfl) ⟨427077, by rfl⟩ : syracuseStep 1138873 = 854155) B854155
theorem B1827017 : Blo 599292 1827017 := bstep (se 2 (by rfl) ⟨685131, by rfl⟩ : syracuseStep 1827017 = 1370263) B1370263
theorem B2023865 : Blo 599292 2023865 := bstep (se 2 (by rfl) ⟨758949, by rfl⟩ : syracuseStep 2023865 = 1517899) B1517899
theorem B3858947 : Blo 599292 3858947 := bstep (se 1 (by rfl) ⟨2894210, by rfl⟩ : syracuseStep 3858947 = 5788421) B5788421
theorem B3039767 : Blo 599292 3039767 := bstep (se 1 (by rfl) ⟨2279825, by rfl⟩ : syracuseStep 3039767 = 4559651) B4559651
theorem B2745089 : Blo 599292 2745089 := bstep (se 2 (by rfl) ⟨1029408, by rfl⟩ : syracuseStep 2745089 = 2058817) B2058817
theorem B13394723 : Blo 599292 13394723 := bstep (se 1 (by rfl) ⟨10046042, by rfl⟩ : syracuseStep 13394723 = 20092085) B20092085
theorem B811819 : Blo 599292 811819 := bstep (se 1 (by rfl) ⟨608864, by rfl⟩ : syracuseStep 811819 = 1217729) B1217729
theorem B5760011 : Blo 599292 5760011 := bstep (se 1 (by rfl) ⟨4320008, by rfl⟩ : syracuseStep 5760011 = 8640017) B8640017
theorem B2024459 : Blo 599292 2024459 := bstep (se 1 (by rfl) ⟨1518344, by rfl⟩ : syracuseStep 2024459 = 3036689) B3036689
theorem B1926155 : Blo 599292 1926155 := bstep (se 1 (by rfl) ⟨1444616, by rfl⟩ : syracuseStep 1926155 = 2889233) B2889233
theorem B2024567 : Blo 599292 2024567 := bstep (se 1 (by rfl) ⟨1518425, by rfl⟩ : syracuseStep 2024567 = 3036851) B3036851
theorem B5498057 : Blo 599292 5498057 := bstep (se 2 (by rfl) ⟨2061771, by rfl⟩ : syracuseStep 5498057 = 4123543) B4123543
theorem B1369387 : Blo 599292 1369387 := bstep (se 1 (by rfl) ⟨1027040, by rfl⟩ : syracuseStep 1369387 = 2054081) B2054081
theorem B2287223 : Blo 599292 2287223 := bstep (se 1 (by rfl) ⟨1715417, by rfl⟩ : syracuseStep 2287223 = 3430835) B3430835
theorem B2025161 : Blo 599292 2025161 := bstep (se 2 (by rfl) ⟨759435, by rfl⟩ : syracuseStep 2025161 = 1518871) B1518871
theorem B1697537 : Blo 599292 1697537 := bstep (se 2 (by rfl) ⟨636576, by rfl⟩ : syracuseStep 1697537 = 1273153) B1273153
theorem B3008477 : Blo 599292 3008477 := bstep (se 3 (by rfl) ⟨564089, by rfl⟩ : syracuseStep 3008477 = 1128179) B1128179
theorem B1140779 : Blo 599292 1140779 := bstep (se 1 (by rfl) ⟨855584, by rfl⟩ : syracuseStep 1140779 = 1711169) B1711169
theorem B2025863 : Blo 599292 2025863 := bstep (se 1 (by rfl) ⟨1519397, by rfl⟩ : syracuseStep 2025863 = 3038795) B3038795
theorem B5794183 : Blo 599292 5794183 := bstep (se 1 (by rfl) ⟨4345637, by rfl⟩ : syracuseStep 5794183 = 8691275) B8691275
theorem B3860945 : Blo 599292 3860945 := bstep (se 2 (by rfl) ⟨1447854, by rfl⟩ : syracuseStep 3860945 = 2895709) B2895709
theorem B2288195 : Blo 599292 2288195 := bstep (se 1 (by rfl) ⟨1716146, by rfl⟩ : syracuseStep 2288195 = 3432293) B3432293
theorem B3435209 : Blo 599292 3435209 := bstep (se 2 (by rfl) ⟨1288203, by rfl⟩ : syracuseStep 3435209 = 2576407) B2576407
theorem B2026241 : Blo 599292 2026241 := bstep (se 2 (by rfl) ⟨759840, by rfl⟩ : syracuseStep 2026241 = 1519681) B1519681
theorem B5860147 : Blo 599292 5860147 := bstep (se 1 (by rfl) ⟨4395110, by rfl⟩ : syracuseStep 5860147 = 8790221) B8790221
theorem B5499737 : Blo 599292 5499737 := bstep (se 2 (by rfl) ⟨2062401, by rfl⟩ : syracuseStep 5499737 = 4124803) B4124803
theorem B1141705 : Blo 599292 1141705 := bstep (se 2 (by rfl) ⟨428139, by rfl⟩ : syracuseStep 1141705 = 856279) B856279
theorem B683407 : Blo 599292 683407 := bstep (se 1 (by rfl) ⟨512555, by rfl⟩ : syracuseStep 683407 = 1025111) B1025111
theorem B3894713 : Blo 599292 3894713 := bstep (se 2 (by rfl) ⟨1460517, by rfl⟩ : syracuseStep 3894713 = 2921035) B2921035
theorem B3042845 : Blo 599292 3042845 := bstep (se 3 (by rfl) ⟨570533, by rfl⟩ : syracuseStep 3042845 = 1141067) B1141067
theorem B2289181 : Blo 599292 2289181 := bstep (se 3 (by rfl) ⟨429221, by rfl⟩ : syracuseStep 2289181 = 858443) B858443
theorem B2027051 : Blo 599292 2027051 := bstep (se 1 (by rfl) ⟨1520288, by rfl⟩ : syracuseStep 2027051 = 3040577) B3040577
theorem B1142419 : Blo 599292 1142419 := bstep (se 1 (by rfl) ⟨856814, by rfl⟩ : syracuseStep 1142419 = 1713629) B1713629
theorem B1011575 : Blo 599292 1011575 := bstep (se 1 (by rfl) ⟨758681, by rfl⟩ : syracuseStep 1011575 = 1517363) B1517363
theorem B3043331 : Blo 599292 3043331 := bstep (se 1 (by rfl) ⟨2282498, by rfl⟩ : syracuseStep 3043331 = 4564997) B4564997
theorem B6484205 : Blo 599292 6484205 := bstep (se 3 (by rfl) ⟨1215788, by rfl⟩ : syracuseStep 6484205 = 2431577) B2431577
theorem B1012027 : Blo 599292 1012027 := bstep (se 1 (by rfl) ⟨759020, by rfl⟩ : syracuseStep 1012027 = 1518041) B1518041
theorem B1012169 : Blo 599292 1012169 := bstep (se 2 (by rfl) ⟨379563, by rfl⟩ : syracuseStep 1012169 = 759127) B759127
theorem B914105 : Blo 599292 914105 := bstep (se 2 (by rfl) ⟨342789, by rfl⟩ : syracuseStep 914105 = 685579) B685579
theorem B12972737 : Blo 599292 12972737 := bstep (se 2 (by rfl) ⟨4864776, by rfl⟩ : syracuseStep 12972737 = 9729553) B9729553
theorem B17330881 : Blo 599292 17330881 := bstep (se 2 (by rfl) ⟨6499080, by rfl⟩ : syracuseStep 17330881 = 12998161) B12998161
theorem B1143497 : Blo 599292 1143497 := bstep (se 2 (by rfl) ⟨428811, by rfl⟩ : syracuseStep 1143497 = 857623) B857623
theorem B3240719 : Blo 599292 3240719 := bstep (se 1 (by rfl) ⟨2430539, by rfl⟩ : syracuseStep 3240719 = 4861079) B4861079
theorem B2028347 : Blo 599292 2028347 := bstep (se 1 (by rfl) ⟨1521260, by rfl⟩ : syracuseStep 2028347 = 3042521) B3042521
theorem B1012871 : Blo 599292 1012871 := bstep (se 1 (by rfl) ⟨759653, by rfl⟩ : syracuseStep 1012871 = 1519307) B1519307
theorem B2028833 : Blo 599292 2028833 := bstep (se 2 (by rfl) ⟨760812, by rfl⟩ : syracuseStep 2028833 = 1521625) B1521625
theorem B3470629 : Blo 599292 3470629 := bstep (se 4 (by rfl) ⟨325371, by rfl⟩ : syracuseStep 3470629 = 650743) B650743
theorem B4879763 : Blo 599292 4879763 := bstep (se 1 (by rfl) ⟨3659822, by rfl⟩ : syracuseStep 4879763 = 7319645) B7319645
theorem B1832345 : Blo 599292 1832345 := bstep (se 2 (by rfl) ⟨687129, by rfl⟩ : syracuseStep 1832345 = 1374259) B1374259
theorem B914951 : Blo 599292 914951 := bstep (se 1 (by rfl) ⟨686213, by rfl⟩ : syracuseStep 914951 = 1372427) B1372427
theorem B1734173 : Blo 599292 1734173 := bstep (se 3 (by rfl) ⟨325157, by rfl⟩ : syracuseStep 1734173 = 650315) B650315
theorem B1144363 : Blo 599292 1144363 := bstep (se 1 (by rfl) ⟨858272, by rfl⟩ : syracuseStep 1144363 = 1716545) B1716545
theorem B4617805 : Blo 599292 4617805 := bstep (se 3 (by rfl) ⟨865838, by rfl⟩ : syracuseStep 4617805 = 1731677) B1731677
theorem B5797453 : Blo 599292 5797453 := bstep (se 3 (by rfl) ⟨1087022, by rfl⟩ : syracuseStep 5797453 = 2174045) B2174045
theorem B3044951 : Blo 599292 3044951 := bstep (se 1 (by rfl) ⟨2283713, by rfl⟩ : syracuseStep 3044951 = 4567427) B4567427
theorem B1930871 : Blo 599292 1930871 := bstep (se 1 (by rfl) ⟨1448153, by rfl⟩ : syracuseStep 1930871 = 2896307) B2896307
theorem B1144439 : Blo 599292 1144439 := bstep (se 1 (by rfl) ⟨858329, by rfl⟩ : syracuseStep 1144439 = 1716659) B1716659
theorem B15365861 : Blo 599292 15365861 := bstep (se 4 (by rfl) ⟨1440549, by rfl⟩ : syracuseStep 15365861 = 2881099) B2881099
theorem B1013519 : Blo 599292 1013519 := bstep (se 1 (by rfl) ⟨760139, by rfl⟩ : syracuseStep 1013519 = 1520279) B1520279
theorem B5011237 : Blo 599292 5011237 := bstep (se 4 (by rfl) ⟨469803, by rfl⟩ : syracuseStep 5011237 = 939607) B939607
theorem B3667801 : Blo 599292 3667801 := bstep (se 2 (by rfl) ⟨1375425, by rfl⟩ : syracuseStep 3667801 = 2750851) B2750851
theorem B2029427 : Blo 599292 2029427 := bstep (se 1 (by rfl) ⟨1522070, by rfl⟩ : syracuseStep 2029427 = 3044141) B3044141
theorem B5339033 : Blo 599292 5339033 := bstep (se 2 (by rfl) ⟨2002137, by rfl⟩ : syracuseStep 5339033 = 4004275) B4004275
theorem B3045437 : Blo 599292 3045437 := bstep (se 3 (by rfl) ⟨571019, by rfl⟩ : syracuseStep 3045437 = 1142039) B1142039
theorem B1374479 : Blo 599292 1374479 := bstep (se 1 (by rfl) ⟨1030859, by rfl⟩ : syracuseStep 1374479 = 2061719) B2061719
theorem B1014059 : Blo 599292 1014059 := bstep (se 1 (by rfl) ⟨760544, by rfl⟩ : syracuseStep 1014059 = 1521089) B1521089
theorem B1440185 : Blo 599292 1440185 := bstep (se 2 (by rfl) ⟨540069, by rfl⟩ : syracuseStep 1440185 = 1080139) B1080139
theorem B1014457 : Blo 599292 1014457 := bstep (se 2 (by rfl) ⟨380421, by rfl⟩ : syracuseStep 1014457 = 760843) B760843
theorem B2751367 : Blo 599292 2751367 := bstep (se 1 (by rfl) ⟨2063525, by rfl⟩ : syracuseStep 2751367 = 4127051) B4127051
theorem B720247 : Blo 599292 720247 := bstep (se 1 (by rfl) ⟨540185, by rfl⟩ : syracuseStep 720247 = 1080371) B1080371
theorem B1080695 : Blo 599292 1080695 := bstep (se 1 (by rfl) ⟨810521, by rfl⟩ : syracuseStep 1080695 = 1621043) B1621043
theorem B1015159 : Blo 599292 1015159 := bstep (se 1 (by rfl) ⟨761369, by rfl⟩ : syracuseStep 1015159 = 1522739) B1522739
theorem B1015355 : Blo 599292 1015355 := bstep (se 1 (by rfl) ⟨761516, by rfl⟩ : syracuseStep 1015355 = 1523033) B1523033
theorem B3047219 : Blo 599292 3047219 := bstep (se 1 (by rfl) ⟨2285414, by rfl⟩ : syracuseStep 3047219 = 4570829) B4570829
theorem B720775 : Blo 599292 720775 := bstep (se 1 (by rfl) ⟨540581, by rfl⟩ : syracuseStep 720775 = 1081163) B1081163
theorem B1015753 : Blo 599292 1015753 := bstep (se 2 (by rfl) ⟨380907, by rfl⟩ : syracuseStep 1015753 = 761815) B761815
theorem B2031695 : Blo 599292 2031695 := bstep (se 1 (by rfl) ⟨1523771, by rfl⟩ : syracuseStep 2031695 = 3047543) B3047543
theorem B38961269 : Blo 599292 38961269 := bstep (se 5 (by rfl) ⟨1826309, by rfl⟩ : syracuseStep 38961269 = 3652619) B3652619
theorem B1016057 : Blo 599292 1016057 := bstep (se 2 (by rfl) ⟨381021, by rfl⟩ : syracuseStep 1016057 = 762043) B762043
theorem B1016239 : Blo 599292 1016239 := bstep (se 1 (by rfl) ⟨762179, by rfl⟩ : syracuseStep 1016239 = 1524359) B1524359
theorem B2032073 : Blo 599292 2032073 := bstep (se 2 (by rfl) ⟨762027, by rfl⟩ : syracuseStep 2032073 = 1524055) B1524055
theorem B1016327 : Blo 599292 1016327 := bstep (se 1 (by rfl) ⟨762245, by rfl⟩ : syracuseStep 1016327 = 1524491) B1524491
theorem B2032343 : Blo 599292 2032343 := bstep (se 1 (by rfl) ⟨1524257, by rfl⟩ : syracuseStep 2032343 = 3048515) B3048515
theorem B5768009 : Blo 599292 5768009 := bstep (se 2 (by rfl) ⟨2163003, by rfl⟩ : syracuseStep 5768009 = 4326007) B4326007
theorem B1016671 : Blo 599292 1016671 := bstep (se 1 (by rfl) ⟨762503, by rfl⟩ : syracuseStep 1016671 = 1525007) B1525007
theorem B2032559 : Blo 599292 2032559 := bstep (se 1 (by rfl) ⟨1524419, by rfl⟩ : syracuseStep 2032559 = 3048839) B3048839
theorem B1016759 : Blo 599292 1016759 := bstep (se 1 (by rfl) ⟨762569, by rfl⟩ : syracuseStep 1016759 = 1525139) B1525139
theorem B15205427 : Blo 599292 15205427 := bstep (se 1 (by rfl) ⟨11404070, by rfl⟩ : syracuseStep 15205427 = 22808141) B22808141
theorem B1082425 : Blo 599292 1082425 := bstep (se 2 (by rfl) ⟨405909, by rfl⟩ : syracuseStep 1082425 = 811819) B811819
theorem B3245303 : Blo 599292 3245303 := bstep (se 1 (by rfl) ⟨2433977, by rfl⟩ : syracuseStep 3245303 = 4867955) B4867955
theorem B1082719 : Blo 599292 1082719 := bstep (se 1 (by rfl) ⟨812039, by rfl⟩ : syracuseStep 1082719 = 1624079) B1624079
theorem B6522227 : Blo 599292 6522227 := bstep (se 1 (by rfl) ⟨4891670, by rfl⟩ : syracuseStep 6522227 = 9783341) B9783341
theorem B722351 : Blo 599292 722351 := bstep (se 1 (by rfl) ⟨541763, by rfl⟩ : syracuseStep 722351 = 1083527) B1083527
theorem B39060913 : Blo 599292 39060913 := bstep (se 2 (by rfl) ⟨14647842, by rfl⟩ : syracuseStep 39060913 = 29295685) B29295685
theorem B1017353 : Blo 599292 1017353 := bstep (se 2 (by rfl) ⟨381507, by rfl⟩ : syracuseStep 1017353 = 763015) B763015
theorem B11568683 : Blo 599292 11568683 := bstep (se 1 (by rfl) ⟨8676512, by rfl⟩ : syracuseStep 11568683 = 17353025) B17353025
theorem B1017515 : Blo 599292 1017515 := bstep (se 1 (by rfl) ⟨763136, by rfl⟩ : syracuseStep 1017515 = 1526273) B1526273
theorem B3049325 : Blo 599292 3049325 := bstep (se 3 (by rfl) ⟨571748, by rfl⟩ : syracuseStep 3049325 = 1143497) B1143497
theorem B9734093 : Blo 599292 9734093 := bstep (se 3 (by rfl) ⟨1825142, by rfl⟩ : syracuseStep 9734093 = 3650285) B3650285
theorem B3049487 : Blo 599292 3049487 := bstep (se 1 (by rfl) ⟨2287115, by rfl⟩ : syracuseStep 3049487 = 4574231) B4574231
theorem B1017913 : Blo 599292 1017913 := bstep (se 2 (by rfl) ⟨381717, by rfl⟩ : syracuseStep 1017913 = 763435) B763435
theorem B35719261 : Blo 599292 35719261 := bstep (se 3 (by rfl) ⟨6697361, by rfl⟩ : syracuseStep 35719261 = 13394723) B13394723
theorem B1018055 : Blo 599292 1018055 := bstep (se 1 (by rfl) ⟨763541, by rfl⟩ : syracuseStep 1018055 = 1527083) B1527083
theorem B854491 : Blo 599292 854491 := bstep (se 1 (by rfl) ⟨640868, by rfl⟩ : syracuseStep 854491 = 1281737) B1281737
theorem B1280711 : Blo 599292 1280711 := bstep (se 1 (by rfl) ⟨960533, by rfl⟩ : syracuseStep 1280711 = 1921067) B1921067
theorem B855049 : Blo 599292 855049 := bstep (se 2 (by rfl) ⟨320643, by rfl⟩ : syracuseStep 855049 = 641287) B641287
theorem B2034935 : Blo 599292 2034935 := bstep (se 1 (by rfl) ⟨1526201, by rfl⟩ : syracuseStep 2034935 = 3052403) B3052403
theorem B1281575 : Blo 599292 1281575 := bstep (se 1 (by rfl) ⟨961181, by rfl⟩ : syracuseStep 1281575 = 1922363) B1922363
theorem B2035259 : Blo 599292 2035259 := bstep (se 1 (by rfl) ⟨1526444, by rfl⟩ : syracuseStep 2035259 = 3052889) B3052889
theorem B2035529 : Blo 599292 2035529 := bstep (se 2 (by rfl) ⟨763323, by rfl⟩ : syracuseStep 2035529 = 1526647) B1526647
theorem B2560157 : Blo 599292 2560157 := bstep (se 3 (by rfl) ⟨480029, by rfl⟩ : syracuseStep 2560157 = 960059) B960059
theorem B4559165 : Blo 599292 4559165 := bstep (se 3 (by rfl) ⟨854843, by rfl⟩ : syracuseStep 4559165 = 1709687) B1709687
theorem B2888173 : Blo 599292 2888173 := bstep (se 3 (by rfl) ⟨541532, by rfl⟩ : syracuseStep 2888173 = 1083065) B1083065
theorem B2167283 : Blo 599292 2167283 := bstep (se 1 (by rfl) ⟨1625462, by rfl⟩ : syracuseStep 2167283 = 3250925) B3250925
theorem B4526765 : Blo 599292 4526765 := bstep (se 3 (by rfl) ⟨848768, by rfl⟩ : syracuseStep 4526765 = 1697537) B1697537
theorem B1086151 : Blo 599292 1086151 := bstep (se 1 (by rfl) ⟨814613, by rfl⟩ : syracuseStep 1086151 = 1629227) B1629227
theorem B3248849 : Blo 599292 3248849 := bstep (se 2 (by rfl) ⟨1218318, by rfl⟩ : syracuseStep 3248849 = 2436637) B2436637
theorem B3052241 : Blo 599292 3052241 := bstep (se 2 (by rfl) ⟨1144590, by rfl⟩ : syracuseStep 3052241 = 2289181) B2289181
theorem B2560841 : Blo 599292 2560841 := bstep (se 2 (by rfl) ⟨960315, by rfl⟩ : syracuseStep 2560841 = 1920631) B1920631
theorem B1446817 : Blo 599292 1446817 := bstep (se 2 (by rfl) ⟨542556, by rfl⟩ : syracuseStep 1446817 = 1085113) B1085113
theorem B4330415 : Blo 599292 4330415 := bstep (se 1 (by rfl) ⟨3247811, by rfl⟩ : syracuseStep 4330415 = 6495623) B6495623
theorem B3249071 : Blo 599292 3249071 := bstep (se 1 (by rfl) ⟨2436803, by rfl⟩ : syracuseStep 3249071 = 4873607) B4873607
theorem B758747 : Blo 599292 758747 := bstep (se 1 (by rfl) ⟨569060, by rfl⟩ : syracuseStep 758747 = 1138121) B1138121
theorem B1709437 : Blo 599292 1709437 := bstep (se 3 (by rfl) ⟨320519, by rfl⟩ : syracuseStep 1709437 = 641039) B641039
theorem B759223 : Blo 599292 759223 := bstep (se 1 (by rfl) ⟨569417, by rfl⟩ : syracuseStep 759223 = 1138835) B1138835
theorem B1218011 : Blo 599292 1218011 := bstep (se 1 (by rfl) ⟨913508, by rfl⟩ : syracuseStep 1218011 = 1827017) B1827017
theorem B1447433 : Blo 599292 1447433 := bstep (se 2 (by rfl) ⟨542787, by rfl⟩ : syracuseStep 1447433 = 1085575) B1085575
theorem B1349243 : Blo 599292 1349243 := bstep (se 1 (by rfl) ⟨1011932, by rfl⟩ : syracuseStep 1349243 = 2023865) B2023865
theorem B1349369 : Blo 599292 1349369 := bstep (se 2 (by rfl) ⟨506013, by rfl⟩ : syracuseStep 1349369 = 1012027) B1012027
theorem B19535651 : Blo 599292 19535651 := bstep (se 1 (by rfl) ⟨14651738, by rfl⟩ : syracuseStep 19535651 = 29303477) B29303477
theorem B3840007 : Blo 599292 3840007 := bstep (se 1 (by rfl) ⟨2880005, by rfl⟩ : syracuseStep 3840007 = 5760011) B5760011
theorem B1349639 : Blo 599292 1349639 := bstep (se 1 (by rfl) ⟨1012229, by rfl⟩ : syracuseStep 1349639 = 2024459) B2024459
theorem B1284103 : Blo 599292 1284103 := bstep (se 1 (by rfl) ⟨963077, by rfl⟩ : syracuseStep 1284103 = 1926155) B1926155
theorem B1349711 : Blo 599292 1349711 := bstep (se 1 (by rfl) ⟨1012283, by rfl⟩ : syracuseStep 1349711 = 2024567) B2024567
theorem B23107841 : Blo 599292 23107841 := bstep (se 2 (by rfl) ⟨8665440, by rfl⟩ : syracuseStep 23107841 = 17330881) B17330881
theorem B6953303 : Blo 599292 6953303 := bstep (se 1 (by rfl) ⟨5214977, by rfl⟩ : syracuseStep 6953303 = 10429955) B10429955
theorem B1350107 : Blo 599292 1350107 := bstep (se 1 (by rfl) ⟨1012580, by rfl⟩ : syracuseStep 1350107 = 2025161) B2025161
theorem B3840493 : Blo 599292 3840493 := bstep (se 3 (by rfl) ⟨720092, by rfl⟩ : syracuseStep 3840493 = 1440185) B1440185
theorem B2005651 : Blo 599292 2005651 := bstep (se 1 (by rfl) ⟨1504238, by rfl⟩ : syracuseStep 2005651 = 3008477) B3008477
theorem B760519 : Blo 599292 760519 := bstep (se 1 (by rfl) ⟨570389, by rfl⟩ : syracuseStep 760519 = 1140779) B1140779
theorem B1350575 : Blo 599292 1350575 := bstep (se 1 (by rfl) ⟨1012931, by rfl⟩ : syracuseStep 1350575 = 2025863) B2025863
theorem B4627505 : Blo 599292 4627505 := bstep (se 2 (by rfl) ⟨1735314, by rfl⟩ : syracuseStep 4627505 = 3470629) B3470629
theorem B1350827 : Blo 599292 1350827 := bstep (se 1 (by rfl) ⟨1013120, by rfl⟩ : syracuseStep 1350827 = 2026241) B2026241
theorem B2465149 : Blo 599292 2465149 := bstep (se 3 (by rfl) ⟨462215, by rfl⟩ : syracuseStep 2465149 = 924431) B924431
theorem B3644837 : Blo 599292 3644837 := bstep (se 4 (by rfl) ⟨341703, by rfl⟩ : syracuseStep 3644837 = 683407) B683407
theorem B2596475 : Blo 599292 2596475 := bstep (se 1 (by rfl) ⟨1947356, by rfl⟩ : syracuseStep 2596475 = 3894713) B3894713
theorem B1351367 : Blo 599292 1351367 := bstep (se 1 (by rfl) ⟨1013525, by rfl⟩ : syracuseStep 1351367 = 2027051) B2027051
theorem B4890401 : Blo 599292 4890401 := bstep (se 2 (by rfl) ⟨1833900, by rfl⟩ : syracuseStep 4890401 = 3667801) B3667801
theorem B2563883 : Blo 599292 2563883 := bstep (se 1 (by rfl) ⟨1922912, by rfl⟩ : syracuseStep 2563883 = 3845825) B3845825
theorem B27795473 : Blo 599292 27795473 := bstep (se 2 (by rfl) ⟨10423302, by rfl⟩ : syracuseStep 27795473 = 20846605) B20846605
theorem B1712285 : Blo 599292 1712285 := bstep (se 3 (by rfl) ⟨321053, by rfl⟩ : syracuseStep 1712285 = 642107) B642107
theorem B1712603 : Blo 599292 1712603 := bstep (se 1 (by rfl) ⟨1284452, by rfl⟩ : syracuseStep 1712603 = 2568905) B2568905
theorem B1712627 : Blo 599292 1712627 := bstep (se 1 (by rfl) ⟨1284470, by rfl⟩ : syracuseStep 1712627 = 2568941) B2568941
theorem B1352231 : Blo 599292 1352231 := bstep (se 1 (by rfl) ⟨1014173, by rfl⟩ : syracuseStep 1352231 = 2028347) B2028347
theorem B2892617 : Blo 599292 2892617 := bstep (se 2 (by rfl) ⟨1084731, by rfl⟩ : syracuseStep 2892617 = 2169463) B2169463
theorem B1352555 : Blo 599292 1352555 := bstep (se 1 (by rfl) ⟨1014416, by rfl⟩ : syracuseStep 1352555 = 2028833) B2028833
theorem B1352609 : Blo 599292 1352609 := bstep (se 2 (by rfl) ⟨507228, by rfl⟩ : syracuseStep 1352609 = 1014457) B1014457
theorem B3253175 : Blo 599292 3253175 := bstep (se 1 (by rfl) ⟨2439881, by rfl⟩ : syracuseStep 3253175 = 4879763) B4879763
theorem B3089335 : Blo 599292 3089335 := bstep (se 1 (by rfl) ⟨2317001, by rfl⟩ : syracuseStep 3089335 = 4634003) B4634003
theorem B1221563 : Blo 599292 1221563 := bstep (se 1 (by rfl) ⟨916172, by rfl⟩ : syracuseStep 1221563 = 1832345) B1832345
theorem B1156115 : Blo 599292 1156115 := bstep (se 1 (by rfl) ⟨867086, by rfl⟩ : syracuseStep 1156115 = 1734173) B1734173
theorem B1287247 : Blo 599292 1287247 := bstep (se 1 (by rfl) ⟨965435, by rfl⟩ : syracuseStep 1287247 = 1930871) B1930871
theorem B762959 : Blo 599292 762959 := bstep (se 1 (by rfl) ⟨572219, by rfl⟩ : syracuseStep 762959 = 1144439) B1144439
theorem B1352951 : Blo 599292 1352951 := bstep (se 1 (by rfl) ⟨1014713, by rfl⟩ : syracuseStep 1352951 = 2029427) B2029427
theorem B599335 : Blo 599292 599335 := bstep (se 1 (by rfl) ⟨449501, by rfl⟩ : syracuseStep 599335 = 899003) B899003
theorem B599375 : Blo 599292 599375 := bstep (se 1 (by rfl) ⟨449531, by rfl⟩ : syracuseStep 599375 = 899063) B899063
theorem B599391 : Blo 599292 599391 := bstep (se 1 (by rfl) ⟨449543, by rfl⟩ : syracuseStep 599391 = 899087) B899087
theorem B599419 : Blo 599292 599419 := bstep (se 1 (by rfl) ⟨449564, by rfl⟩ : syracuseStep 599419 = 899129) B899129
theorem B599471 : Blo 599292 599471 := bstep (se 1 (by rfl) ⟨449603, by rfl⟩ : syracuseStep 599471 = 899207) B899207
theorem B599495 : Blo 599292 599495 := bstep (se 1 (by rfl) ⟨449621, by rfl⟩ : syracuseStep 599495 = 899243) B899243
theorem B599515 : Blo 599292 599515 := bstep (se 1 (by rfl) ⟨449636, by rfl⟩ : syracuseStep 599515 = 899273) B899273
theorem B599591 : Blo 599292 599591 := bstep (se 1 (by rfl) ⟨449693, by rfl⟩ : syracuseStep 599591 = 899387) B899387
theorem B599631 : Blo 599292 599631 := bstep (se 1 (by rfl) ⟨449723, by rfl⟩ : syracuseStep 599631 = 899447) B899447
theorem B599647 : Blo 599292 599647 := bstep (se 1 (by rfl) ⟨449735, by rfl⟩ : syracuseStep 599647 = 899471) B899471
theorem B599675 : Blo 599292 599675 := bstep (se 1 (by rfl) ⟨449756, by rfl⟩ : syracuseStep 599675 = 899513) B899513
theorem B599727 : Blo 599292 599727 := bstep (se 1 (by rfl) ⟨449795, by rfl⟩ : syracuseStep 599727 = 899591) B899591
theorem B599751 : Blo 599292 599751 := bstep (se 1 (by rfl) ⟨449813, by rfl⟩ : syracuseStep 599751 = 899627) B899627
theorem B599771 : Blo 599292 599771 := bstep (se 1 (by rfl) ⟨449828, by rfl⟩ : syracuseStep 599771 = 899657) B899657
theorem B599847 : Blo 599292 599847 := bstep (se 1 (by rfl) ⟨449885, by rfl⟩ : syracuseStep 599847 = 899771) B899771
theorem B960329 : Blo 599292 960329 := bstep (se 2 (by rfl) ⟨360123, by rfl⟩ : syracuseStep 960329 = 720247) B720247
theorem B1353545 : Blo 599292 1353545 := bstep (se 2 (by rfl) ⟨507579, by rfl⟩ : syracuseStep 1353545 = 1015159) B1015159
theorem B599887 : Blo 599292 599887 := bstep (se 1 (by rfl) ⟨449915, by rfl⟩ : syracuseStep 599887 = 899831) B899831
theorem B599903 : Blo 599292 599903 := bstep (se 1 (by rfl) ⟨449927, by rfl⟩ : syracuseStep 599903 = 899855) B899855
theorem B599931 : Blo 599292 599931 := bstep (se 1 (by rfl) ⟨449948, by rfl⟩ : syracuseStep 599931 = 899897) B899897
theorem B599983 : Blo 599292 599983 := bstep (se 1 (by rfl) ⟨449987, by rfl⟩ : syracuseStep 599983 = 899975) B899975
theorem B600007 : Blo 599292 600007 := bstep (se 1 (by rfl) ⟨450005, by rfl⟩ : syracuseStep 600007 = 900011) B900011
theorem B600027 : Blo 599292 600027 := bstep (se 1 (by rfl) ⟨450020, by rfl⟩ : syracuseStep 600027 = 900041) B900041
theorem B1517575 : Blo 599292 1517575 := bstep (se 1 (by rfl) ⟨1138181, by rfl⟩ : syracuseStep 1517575 = 2276363) B2276363
theorem B12986405 : Blo 599292 12986405 := bstep (se 4 (by rfl) ⟨1217475, by rfl⟩ : syracuseStep 12986405 = 2434951) B2434951
theorem B600103 : Blo 599292 600103 := bstep (se 1 (by rfl) ⟨450077, by rfl⟩ : syracuseStep 600103 = 900155) B900155
theorem B600143 : Blo 599292 600143 := bstep (se 1 (by rfl) ⟨450107, by rfl⟩ : syracuseStep 600143 = 900215) B900215
theorem B600159 : Blo 599292 600159 := bstep (se 1 (by rfl) ⟨450119, by rfl⟩ : syracuseStep 600159 = 900239) B900239
theorem B600187 : Blo 599292 600187 := bstep (se 1 (by rfl) ⟨450140, by rfl⟩ : syracuseStep 600187 = 900281) B900281
theorem B2173081 : Blo 599292 2173081 := bstep (se 2 (by rfl) ⟨814905, by rfl⟩ : syracuseStep 2173081 = 1629811) B1629811
theorem B600239 : Blo 599292 600239 := bstep (se 1 (by rfl) ⟨450179, by rfl⟩ : syracuseStep 600239 = 900359) B900359
theorem B600263 : Blo 599292 600263 := bstep (se 1 (by rfl) ⟨450197, by rfl⟩ : syracuseStep 600263 = 900395) B900395
theorem B600283 : Blo 599292 600283 := bstep (se 1 (by rfl) ⟨450212, by rfl⟩ : syracuseStep 600283 = 900425) B900425
theorem B600359 : Blo 599292 600359 := bstep (se 1 (by rfl) ⟨450269, by rfl⟩ : syracuseStep 600359 = 900539) B900539
theorem B600399 : Blo 599292 600399 := bstep (se 1 (by rfl) ⟨450299, by rfl⟩ : syracuseStep 600399 = 900599) B900599
theorem B600415 : Blo 599292 600415 := bstep (se 1 (by rfl) ⟨450311, by rfl⟩ : syracuseStep 600415 = 900623) B900623
theorem B600443 : Blo 599292 600443 := bstep (se 1 (by rfl) ⟨450332, by rfl⟩ : syracuseStep 600443 = 900665) B900665
theorem B600495 : Blo 599292 600495 := bstep (se 1 (by rfl) ⟨450371, by rfl⟩ : syracuseStep 600495 = 900743) B900743
theorem B600519 : Blo 599292 600519 := bstep (se 1 (by rfl) ⟨450389, by rfl⟩ : syracuseStep 600519 = 900779) B900779
theorem B600539 : Blo 599292 600539 := bstep (se 1 (by rfl) ⟨450404, by rfl⟩ : syracuseStep 600539 = 900809) B900809
theorem B961033 : Blo 599292 961033 := bstep (se 2 (by rfl) ⟨360387, by rfl⟩ : syracuseStep 961033 = 720775) B720775
theorem B600615 : Blo 599292 600615 := bstep (se 1 (by rfl) ⟨450461, by rfl⟩ : syracuseStep 600615 = 900923) B900923
theorem B600655 : Blo 599292 600655 := bstep (se 1 (by rfl) ⟨450491, by rfl⟩ : syracuseStep 600655 = 900983) B900983
theorem B600671 : Blo 599292 600671 := bstep (se 1 (by rfl) ⟨450503, by rfl⟩ : syracuseStep 600671 = 901007) B901007
theorem B1354337 : Blo 599292 1354337 := bstep (se 2 (by rfl) ⟨507876, by rfl⟩ : syracuseStep 1354337 = 1015753) B1015753
theorem B1518203 : Blo 599292 1518203 := bstep (se 1 (by rfl) ⟨1138652, by rfl⟩ : syracuseStep 1518203 = 2277305) B2277305
theorem B600699 : Blo 599292 600699 := bstep (se 1 (by rfl) ⟨450524, by rfl⟩ : syracuseStep 600699 = 901049) B901049
theorem B600751 : Blo 599292 600751 := bstep (se 1 (by rfl) ⟨450563, by rfl⟩ : syracuseStep 600751 = 901127) B901127
theorem B600775 : Blo 599292 600775 := bstep (se 1 (by rfl) ⟨450581, by rfl⟩ : syracuseStep 600775 = 901163) B901163
theorem B600795 : Blo 599292 600795 := bstep (se 1 (by rfl) ⟨450596, by rfl⟩ : syracuseStep 600795 = 901193) B901193
theorem B600871 : Blo 599292 600871 := bstep (se 1 (by rfl) ⟨450653, by rfl⟩ : syracuseStep 600871 = 901307) B901307
theorem B600911 : Blo 599292 600911 := bstep (se 1 (by rfl) ⟨450683, by rfl⟩ : syracuseStep 600911 = 901367) B901367
theorem B600927 : Blo 599292 600927 := bstep (se 1 (by rfl) ⟨450695, by rfl⟩ : syracuseStep 600927 = 901391) B901391
theorem B600955 : Blo 599292 600955 := bstep (se 1 (by rfl) ⟨450716, by rfl⟩ : syracuseStep 600955 = 901433) B901433
theorem B1518497 : Blo 599292 1518497 := bstep (se 2 (by rfl) ⟨569436, by rfl⟩ : syracuseStep 1518497 = 1138873) B1138873
theorem B601007 : Blo 599292 601007 := bstep (se 1 (by rfl) ⟨450755, by rfl⟩ : syracuseStep 601007 = 901511) B901511
theorem B1354679 : Blo 599292 1354679 := bstep (se 1 (by rfl) ⟨1016009, by rfl⟩ : syracuseStep 1354679 = 2032019) B2032019
theorem B601031 : Blo 599292 601031 := bstep (se 1 (by rfl) ⟨450773, by rfl⟩ : syracuseStep 601031 = 901547) B901547
theorem B601051 : Blo 599292 601051 := bstep (se 1 (by rfl) ⟨450788, by rfl⟩ : syracuseStep 601051 = 901577) B901577
theorem B1321991 : Blo 599292 1321991 := bstep (se 1 (by rfl) ⟨991493, by rfl⟩ : syracuseStep 1321991 = 1982987) B1982987
theorem B601127 : Blo 599292 601127 := bstep (se 1 (by rfl) ⟨450845, by rfl⟩ : syracuseStep 601127 = 901691) B901691
theorem B601167 : Blo 599292 601167 := bstep (se 1 (by rfl) ⟨450875, by rfl⟩ : syracuseStep 601167 = 901751) B901751
theorem B601183 : Blo 599292 601183 := bstep (se 1 (by rfl) ⟨450887, by rfl⟩ : syracuseStep 601183 = 901775) B901775
theorem B601211 : Blo 599292 601211 := bstep (se 1 (by rfl) ⟨450908, by rfl⟩ : syracuseStep 601211 = 901817) B901817
theorem B601263 : Blo 599292 601263 := bstep (se 1 (by rfl) ⟨450947, by rfl⟩ : syracuseStep 601263 = 901895) B901895
theorem B2174147 : Blo 599292 2174147 := bstep (se 1 (by rfl) ⟨1630610, by rfl⟩ : syracuseStep 2174147 = 3261221) B3261221
theorem B601287 : Blo 599292 601287 := bstep (se 1 (by rfl) ⟨450965, by rfl⟩ : syracuseStep 601287 = 901931) B901931
theorem B601307 : Blo 599292 601307 := bstep (se 1 (by rfl) ⟨450980, by rfl⟩ : syracuseStep 601307 = 901961) B901961
theorem B601383 : Blo 599292 601383 := bstep (se 1 (by rfl) ⟨451037, by rfl⟩ : syracuseStep 601383 = 902075) B902075
theorem B601423 : Blo 599292 601423 := bstep (se 1 (by rfl) ⟨451067, by rfl⟩ : syracuseStep 601423 = 902135) B902135
theorem B3845465 : Blo 599292 3845465 := bstep (se 2 (by rfl) ⟨1442049, by rfl⟩ : syracuseStep 3845465 = 2884099) B2884099
theorem B601439 : Blo 599292 601439 := bstep (se 1 (by rfl) ⟨451079, by rfl⟩ : syracuseStep 601439 = 902159) B902159
theorem B601467 : Blo 599292 601467 := bstep (se 1 (by rfl) ⟨451100, by rfl⟩ : syracuseStep 601467 = 902201) B902201
theorem B601519 : Blo 599292 601519 := bstep (se 1 (by rfl) ⟨451139, by rfl⟩ : syracuseStep 601519 = 902279) B902279
theorem B601543 : Blo 599292 601543 := bstep (se 1 (by rfl) ⟨451157, by rfl⟩ : syracuseStep 601543 = 902315) B902315
theorem B601563 : Blo 599292 601563 := bstep (se 1 (by rfl) ⟨451172, by rfl⟩ : syracuseStep 601563 = 902345) B902345
theorem B1355273 : Blo 599292 1355273 := bstep (se 2 (by rfl) ⟨508227, by rfl⟩ : syracuseStep 1355273 = 1016455) B1016455
theorem B601639 : Blo 599292 601639 := bstep (se 1 (by rfl) ⟨451229, by rfl⟩ : syracuseStep 601639 = 902459) B902459
theorem B601679 : Blo 599292 601679 := bstep (se 1 (by rfl) ⟨451259, by rfl⟩ : syracuseStep 601679 = 902519) B902519
theorem B601695 : Blo 599292 601695 := bstep (se 1 (by rfl) ⟨451271, by rfl⟩ : syracuseStep 601695 = 902543) B902543
theorem B601723 : Blo 599292 601723 := bstep (se 1 (by rfl) ⟨451292, by rfl⟩ : syracuseStep 601723 = 902585) B902585
theorem B601775 : Blo 599292 601775 := bstep (se 1 (by rfl) ⟨451331, by rfl⟩ : syracuseStep 601775 = 902663) B902663
theorem B601799 : Blo 599292 601799 := bstep (se 1 (by rfl) ⟨451349, by rfl⟩ : syracuseStep 601799 = 902699) B902699
theorem B601819 : Blo 599292 601819 := bstep (se 1 (by rfl) ⟨451364, by rfl⟩ : syracuseStep 601819 = 902729) B902729
theorem B601895 : Blo 599292 601895 := bstep (se 1 (by rfl) ⟨451421, by rfl⟩ : syracuseStep 601895 = 902843) B902843
theorem B601935 : Blo 599292 601935 := bstep (se 1 (by rfl) ⟨451451, by rfl⟩ : syracuseStep 601935 = 902903) B902903
theorem B601951 : Blo 599292 601951 := bstep (se 1 (by rfl) ⟨451463, by rfl⟩ : syracuseStep 601951 = 902927) B902927
theorem B1355615 : Blo 599292 1355615 := bstep (se 1 (by rfl) ⟨1016711, by rfl⟩ : syracuseStep 1355615 = 2033423) B2033423
theorem B601979 : Blo 599292 601979 := bstep (se 1 (by rfl) ⟨451484, by rfl⟩ : syracuseStep 601979 = 902969) B902969
theorem B602031 : Blo 599292 602031 := bstep (se 1 (by rfl) ⟨451523, by rfl⟩ : syracuseStep 602031 = 903047) B903047
theorem B602055 : Blo 599292 602055 := bstep (se 1 (by rfl) ⟨451541, by rfl⟩ : syracuseStep 602055 = 903083) B903083
theorem B602075 : Blo 599292 602075 := bstep (se 1 (by rfl) ⟨451556, by rfl⟩ : syracuseStep 602075 = 903113) B903113
theorem B1355795 : Blo 599292 1355795 := bstep (se 1 (by rfl) ⟨1016846, by rfl⟩ : syracuseStep 1355795 = 2033693) B2033693
theorem B602151 : Blo 599292 602151 := bstep (se 1 (by rfl) ⟨451613, by rfl⟩ : syracuseStep 602151 = 903227) B903227
theorem B602191 : Blo 599292 602191 := bstep (se 1 (by rfl) ⟨451643, by rfl⟩ : syracuseStep 602191 = 903287) B903287
theorem B602207 : Blo 599292 602207 := bstep (se 1 (by rfl) ⟨451655, by rfl⟩ : syracuseStep 602207 = 903311) B903311
theorem B602235 : Blo 599292 602235 := bstep (se 1 (by rfl) ⟨451676, by rfl⟩ : syracuseStep 602235 = 903353) B903353
theorem B8335523 : Blo 599292 8335523 := bstep (se 1 (by rfl) ⟨6251642, by rfl⟩ : syracuseStep 8335523 = 12503285) B12503285
theorem B602287 : Blo 599292 602287 := bstep (se 1 (by rfl) ⟨451715, by rfl⟩ : syracuseStep 602287 = 903431) B903431
theorem B602311 : Blo 599292 602311 := bstep (se 1 (by rfl) ⟨451733, by rfl⟩ : syracuseStep 602311 = 903467) B903467
theorem B602331 : Blo 599292 602331 := bstep (se 1 (by rfl) ⟨451748, by rfl⟩ : syracuseStep 602331 = 903497) B903497
theorem B602407 : Blo 599292 602407 := bstep (se 1 (by rfl) ⟨451805, by rfl⟩ : syracuseStep 602407 = 903611) B903611
theorem B602447 : Blo 599292 602447 := bstep (se 1 (by rfl) ⟨451835, by rfl⟩ : syracuseStep 602447 = 903671) B903671
theorem B602463 : Blo 599292 602463 := bstep (se 1 (by rfl) ⟨451847, by rfl⟩ : syracuseStep 602463 = 903695) B903695
theorem B1356137 : Blo 599292 1356137 := bstep (se 2 (by rfl) ⟨508551, by rfl⟩ : syracuseStep 1356137 = 1017103) B1017103
theorem B602491 : Blo 599292 602491 := bstep (se 1 (by rfl) ⟨451868, by rfl⟩ : syracuseStep 602491 = 903737) B903737
theorem B3912065 : Blo 599292 3912065 := bstep (se 2 (by rfl) ⟨1467024, by rfl⟩ : syracuseStep 3912065 = 2934049) B2934049
theorem B602543 : Blo 599292 602543 := bstep (se 1 (by rfl) ⟨451907, by rfl⟩ : syracuseStep 602543 = 903815) B903815
theorem B602567 : Blo 599292 602567 := bstep (se 1 (by rfl) ⟨451925, by rfl⟩ : syracuseStep 602567 = 903851) B903851
theorem B602587 : Blo 599292 602587 := bstep (se 1 (by rfl) ⟨451940, by rfl⟩ : syracuseStep 602587 = 903881) B903881
theorem B2437613 : Blo 599292 2437613 := bstep (se 3 (by rfl) ⟨457052, by rfl⟩ : syracuseStep 2437613 = 914105) B914105
theorem B1520167 : Blo 599292 1520167 := bstep (se 1 (by rfl) ⟨1140125, by rfl⟩ : syracuseStep 1520167 = 2280251) B2280251
theorem B602663 : Blo 599292 602663 := bstep (se 1 (by rfl) ⟨451997, by rfl⟩ : syracuseStep 602663 = 903995) B903995
theorem B602703 : Blo 599292 602703 := bstep (se 1 (by rfl) ⟨452027, by rfl⟩ : syracuseStep 602703 = 904055) B904055
theorem B602719 : Blo 599292 602719 := bstep (se 1 (by rfl) ⟨452039, by rfl⟩ : syracuseStep 602719 = 904079) B904079
theorem B602747 : Blo 599292 602747 := bstep (se 1 (by rfl) ⟨452060, by rfl⟩ : syracuseStep 602747 = 904121) B904121
theorem B602799 : Blo 599292 602799 := bstep (se 1 (by rfl) ⟨452099, by rfl⟩ : syracuseStep 602799 = 904199) B904199
theorem B602823 : Blo 599292 602823 := bstep (se 1 (by rfl) ⟨452117, by rfl⟩ : syracuseStep 602823 = 904235) B904235
theorem B602843 : Blo 599292 602843 := bstep (se 1 (by rfl) ⟨452132, by rfl⟩ : syracuseStep 602843 = 904265) B904265
theorem B4338461 : Blo 599292 4338461 := bstep (se 3 (by rfl) ⟨813461, by rfl⟩ : syracuseStep 4338461 = 1626923) B1626923
theorem B602919 : Blo 599292 602919 := bstep (se 1 (by rfl) ⟨452189, by rfl⟩ : syracuseStep 602919 = 904379) B904379
theorem B602959 : Blo 599292 602959 := bstep (se 1 (by rfl) ⟨452219, by rfl⟩ : syracuseStep 602959 = 904439) B904439
theorem B602975 : Blo 599292 602975 := bstep (se 1 (by rfl) ⟨452231, by rfl⟩ : syracuseStep 602975 = 904463) B904463
theorem B1520491 : Blo 599292 1520491 := bstep (se 1 (by rfl) ⟨1140368, by rfl⟩ : syracuseStep 1520491 = 2280737) B2280737
theorem B603003 : Blo 599292 603003 := bstep (se 1 (by rfl) ⟨452252, by rfl⟩ : syracuseStep 603003 = 904505) B904505
theorem B603055 : Blo 599292 603055 := bstep (se 1 (by rfl) ⟨452291, by rfl⟩ : syracuseStep 603055 = 904583) B904583
theorem B1356731 : Blo 599292 1356731 := bstep (se 1 (by rfl) ⟨1017548, by rfl⟩ : syracuseStep 1356731 = 2035097) B2035097
theorem B603079 : Blo 599292 603079 := bstep (se 1 (by rfl) ⟨452309, by rfl⟩ : syracuseStep 603079 = 904619) B904619
theorem B603099 : Blo 599292 603099 := bstep (se 1 (by rfl) ⟨452324, by rfl⟩ : syracuseStep 603099 = 904649) B904649
theorem B603175 : Blo 599292 603175 := bstep (se 1 (by rfl) ⟨452381, by rfl⟩ : syracuseStep 603175 = 904763) B904763
theorem B1356857 : Blo 599292 1356857 := bstep (se 2 (by rfl) ⟨508821, by rfl⟩ : syracuseStep 1356857 = 1017643) B1017643
theorem B603215 : Blo 599292 603215 := bstep (se 1 (by rfl) ⟨452411, by rfl⟩ : syracuseStep 603215 = 904823) B904823
theorem B603231 : Blo 599292 603231 := bstep (se 1 (by rfl) ⟨452423, by rfl⟩ : syracuseStep 603231 = 904847) B904847
theorem B603259 : Blo 599292 603259 := bstep (se 1 (by rfl) ⟨452444, by rfl⟩ : syracuseStep 603259 = 904889) B904889
theorem B3421379 : Blo 599292 3421379 := bstep (se 1 (by rfl) ⟨2566034, by rfl⟩ : syracuseStep 3421379 = 5132069) B5132069
theorem B1357199 : Blo 599292 1357199 := bstep (se 1 (by rfl) ⟨1017899, by rfl⟩ : syracuseStep 1357199 = 2035799) B2035799
theorem B1521139 : Blo 599292 1521139 := bstep (se 1 (by rfl) ⟨1140854, by rfl⟩ : syracuseStep 1521139 = 2281709) B2281709
theorem B3421835 : Blo 599292 3421835 := bstep (se 1 (by rfl) ⟨2566376, by rfl⟩ : syracuseStep 3421835 = 5132753) B5132753
theorem B2897707 : Blo 599292 2897707 := bstep (se 1 (by rfl) ⟨2173280, by rfl⟩ : syracuseStep 2897707 = 4346561) B4346561
theorem B898991 : Blo 599292 898991 := bstep (se 1 (by rfl) ⟨674243, by rfl⟩ : syracuseStep 898991 = 1348487) B1348487
theorem B899081 : Blo 599292 899081 := bstep (se 2 (by rfl) ⟨337155, by rfl⟩ : syracuseStep 899081 = 674311) B674311
theorem B899111 : Blo 599292 899111 := bstep (se 1 (by rfl) ⟨674333, by rfl⟩ : syracuseStep 899111 = 1348667) B1348667
theorem B899195 : Blo 599292 899195 := bstep (se 1 (by rfl) ⟨674396, by rfl⟩ : syracuseStep 899195 = 1348793) B1348793
theorem B899321 : Blo 599292 899321 := bstep (se 2 (by rfl) ⟨337245, by rfl⟩ : syracuseStep 899321 = 674491) B674491
theorem B899423 : Blo 599292 899423 := bstep (se 1 (by rfl) ⟨674567, by rfl⟩ : syracuseStep 899423 = 1349135) B1349135
theorem B899435 : Blo 599292 899435 := bstep (se 1 (by rfl) ⟨674576, by rfl⟩ : syracuseStep 899435 = 1349153) B1349153
theorem B7813529 : Blo 599292 7813529 := bstep (se 2 (by rfl) ⟨2930073, by rfl⟩ : syracuseStep 7813529 = 5860147) B5860147
theorem B899663 : Blo 599292 899663 := bstep (se 1 (by rfl) ⟨674747, by rfl⟩ : syracuseStep 899663 = 1349495) B1349495
theorem B1522273 : Blo 599292 1522273 := bstep (se 2 (by rfl) ⟨570852, by rfl⟩ : syracuseStep 1522273 = 1141705) B1141705
theorem B3652231 : Blo 599292 3652231 := bstep (se 1 (by rfl) ⟨2739173, by rfl⟩ : syracuseStep 3652231 = 5478347) B5478347
theorem B899783 : Blo 599292 899783 := bstep (se 1 (by rfl) ⟨674837, by rfl⟩ : syracuseStep 899783 = 1349675) B1349675
theorem B899945 : Blo 599292 899945 := bstep (se 2 (by rfl) ⟨337479, by rfl⟩ : syracuseStep 899945 = 674959) B674959
theorem B1096553 : Blo 599292 1096553 := bstep (se 2 (by rfl) ⟨411207, by rfl⟩ : syracuseStep 1096553 = 822415) B822415
theorem B4340627 : Blo 599292 4340627 := bstep (se 1 (by rfl) ⟨3255470, by rfl⟩ : syracuseStep 4340627 = 6510941) B6510941
theorem B900023 : Blo 599292 900023 := bstep (se 1 (by rfl) ⟨675017, by rfl⟩ : syracuseStep 900023 = 1350035) B1350035
theorem B900059 : Blo 599292 900059 := bstep (se 1 (by rfl) ⟨675044, by rfl⟩ : syracuseStep 900059 = 1350089) B1350089
theorem B900527 : Blo 599292 900527 := bstep (se 1 (by rfl) ⟨675395, by rfl⟩ : syracuseStep 900527 = 1350791) B1350791
theorem B900617 : Blo 599292 900617 := bstep (se 2 (by rfl) ⟨337731, by rfl⟩ : syracuseStep 900617 = 675463) B675463
theorem B1523225 : Blo 599292 1523225 := bstep (se 2 (by rfl) ⟨571209, by rfl⟩ : syracuseStep 1523225 = 1142419) B1142419
theorem B900647 : Blo 599292 900647 := bstep (se 1 (by rfl) ⟨675485, by rfl⟩ : syracuseStep 900647 = 1350971) B1350971
theorem B900731 : Blo 599292 900731 := bstep (se 1 (by rfl) ⟨675548, by rfl⟩ : syracuseStep 900731 = 1351097) B1351097
theorem B900857 : Blo 599292 900857 := bstep (se 2 (by rfl) ⟨337821, by rfl⟩ : syracuseStep 900857 = 675643) B675643
theorem B900959 : Blo 599292 900959 := bstep (se 1 (by rfl) ⟨675719, by rfl⟩ : syracuseStep 900959 = 1351439) B1351439
theorem B900971 : Blo 599292 900971 := bstep (se 1 (by rfl) ⟨675728, by rfl⟩ : syracuseStep 900971 = 1351457) B1351457
theorem B1523731 : Blo 599292 1523731 := bstep (se 1 (by rfl) ⟨1142798, by rfl⟩ : syracuseStep 1523731 = 2285597) B2285597
theorem B901199 : Blo 599292 901199 := bstep (se 1 (by rfl) ⟨675899, by rfl⟩ : syracuseStep 901199 = 1351799) B1351799
theorem B901319 : Blo 599292 901319 := bstep (se 1 (by rfl) ⟨675989, by rfl⟩ : syracuseStep 901319 = 1351979) B1351979
theorem B2572631 : Blo 599292 2572631 := bstep (se 1 (by rfl) ⟨1929473, by rfl⟩ : syracuseStep 2572631 = 3858947) B3858947
theorem B901481 : Blo 599292 901481 := bstep (se 2 (by rfl) ⟨338055, by rfl⟩ : syracuseStep 901481 = 676111) B676111
theorem B901559 : Blo 599292 901559 := bstep (se 1 (by rfl) ⟨676169, by rfl⟩ : syracuseStep 901559 = 1352339) B1352339
theorem B901595 : Blo 599292 901595 := bstep (se 1 (by rfl) ⟨676196, by rfl⟩ : syracuseStep 901595 = 1352393) B1352393
theorem B1622567 : Blo 599292 1622567 := bstep (se 1 (by rfl) ⟨1216925, by rfl⟩ : syracuseStep 1622567 = 2433851) B2433851
theorem B770639 : Blo 599292 770639 := bstep (se 1 (by rfl) ⟨577979, by rfl⟩ : syracuseStep 770639 = 1155959) B1155959
theorem B8667749 : Blo 599292 8667749 := bstep (se 4 (by rfl) ⟨812601, by rfl⟩ : syracuseStep 8667749 = 1625203) B1625203
theorem B1622891 : Blo 599292 1622891 := bstep (se 1 (by rfl) ⟨1217168, by rfl⟩ : syracuseStep 1622891 = 2434337) B2434337
theorem B902063 : Blo 599292 902063 := bstep (se 1 (by rfl) ⟨676547, by rfl⟩ : syracuseStep 902063 = 1353095) B1353095
theorem B902153 : Blo 599292 902153 := bstep (se 2 (by rfl) ⟨338307, by rfl⟩ : syracuseStep 902153 = 676615) B676615
theorem B902183 : Blo 599292 902183 := bstep (se 1 (by rfl) ⟨676637, by rfl⟩ : syracuseStep 902183 = 1353275) B1353275
theorem B1524815 : Blo 599292 1524815 := bstep (se 1 (by rfl) ⟨1143611, by rfl⟩ : syracuseStep 1524815 = 2287223) B2287223
theorem B902267 : Blo 599292 902267 := bstep (se 1 (by rfl) ⟨676700, by rfl⟩ : syracuseStep 902267 = 1353401) B1353401
theorem B902393 : Blo 599292 902393 := bstep (se 2 (by rfl) ⟨338397, by rfl⟩ : syracuseStep 902393 = 676795) B676795
theorem B902495 : Blo 599292 902495 := bstep (se 1 (by rfl) ⟨676871, by rfl⟩ : syracuseStep 902495 = 1353743) B1353743
theorem B902507 : Blo 599292 902507 := bstep (se 1 (by rfl) ⟨676880, by rfl⟩ : syracuseStep 902507 = 1353761) B1353761
theorem B902735 : Blo 599292 902735 := bstep (se 1 (by rfl) ⟨677051, by rfl⟩ : syracuseStep 902735 = 1354103) B1354103
theorem B2573963 : Blo 599292 2573963 := bstep (se 1 (by rfl) ⟨1930472, by rfl⟩ : syracuseStep 2573963 = 3860945) B3860945
theorem B3851975 : Blo 599292 3851975 := bstep (se 1 (by rfl) ⟨2888981, by rfl⟩ : syracuseStep 3851975 = 5777963) B5777963
theorem B902855 : Blo 599292 902855 := bstep (se 1 (by rfl) ⟨677141, by rfl⟩ : syracuseStep 902855 = 1354283) B1354283
theorem B1525463 : Blo 599292 1525463 := bstep (se 1 (by rfl) ⟨1144097, by rfl⟩ : syracuseStep 1525463 = 2288195) B2288195
theorem B3852127 : Blo 599292 3852127 := bstep (se 1 (by rfl) ⟨2889095, by rfl⟩ : syracuseStep 3852127 = 5778191) B5778191
theorem B903017 : Blo 599292 903017 := bstep (se 2 (by rfl) ⟨338631, by rfl⟩ : syracuseStep 903017 = 677263) B677263
theorem B3426209 : Blo 599292 3426209 := bstep (se 2 (by rfl) ⟨1284828, by rfl⟩ : syracuseStep 3426209 = 2569657) B2569657
theorem B903095 : Blo 599292 903095 := bstep (se 1 (by rfl) ⟨677321, by rfl⟩ : syracuseStep 903095 = 1354643) B1354643
theorem B903131 : Blo 599292 903131 := bstep (se 1 (by rfl) ⟨677348, by rfl⟩ : syracuseStep 903131 = 1354697) B1354697
theorem B1525817 : Blo 599292 1525817 := bstep (se 2 (by rfl) ⟨572181, by rfl⟩ : syracuseStep 1525817 = 1144363) B1144363
theorem B3426461 : Blo 599292 3426461 := bstep (se 3 (by rfl) ⟨642461, by rfl⟩ : syracuseStep 3426461 = 1284923) B1284923
theorem B903599 : Blo 599292 903599 := bstep (se 1 (by rfl) ⟨677699, by rfl⟩ : syracuseStep 903599 = 1355399) B1355399
theorem B903689 : Blo 599292 903689 := bstep (se 2 (by rfl) ⟨338883, by rfl⟩ : syracuseStep 903689 = 677767) B677767
theorem B903719 : Blo 599292 903719 := bstep (se 1 (by rfl) ⟨677789, by rfl⟩ : syracuseStep 903719 = 1355579) B1355579
theorem B674383 : Blo 599292 674383 := bstep (se 1 (by rfl) ⟨505787, by rfl⟩ : syracuseStep 674383 = 1011575) B1011575
theorem B903803 : Blo 599292 903803 := bstep (se 1 (by rfl) ⟨677852, by rfl⟩ : syracuseStep 903803 = 1355705) B1355705
theorem B6933127 : Blo 599292 6933127 := bstep (se 1 (by rfl) ⟨5199845, by rfl⟩ : syracuseStep 6933127 = 10399691) B10399691
theorem B903929 : Blo 599292 903929 := bstep (se 2 (by rfl) ⟨338973, by rfl⟩ : syracuseStep 903929 = 677947) B677947
theorem B2280221 : Blo 599292 2280221 := bstep (se 3 (by rfl) ⟨427541, by rfl⟩ : syracuseStep 2280221 = 855083) B855083
theorem B3853129 : Blo 599292 3853129 := bstep (se 2 (by rfl) ⟨1444923, by rfl⟩ : syracuseStep 3853129 = 2889847) B2889847
theorem B904031 : Blo 599292 904031 := bstep (se 1 (by rfl) ⟨678023, by rfl⟩ : syracuseStep 904031 = 1356047) B1356047
theorem B904043 : Blo 599292 904043 := bstep (se 1 (by rfl) ⟨678032, by rfl⟩ : syracuseStep 904043 = 1356065) B1356065
theorem B674779 : Blo 599292 674779 := bstep (se 1 (by rfl) ⟨506084, by rfl⟩ : syracuseStep 674779 = 1012169) B1012169
theorem B904271 : Blo 599292 904271 := bstep (se 1 (by rfl) ⟨678203, by rfl⟩ : syracuseStep 904271 = 1356407) B1356407
theorem B1100999 : Blo 599292 1100999 := bstep (se 1 (by rfl) ⟨825749, by rfl⟩ : syracuseStep 1100999 = 1651499) B1651499
theorem B904391 : Blo 599292 904391 := bstep (se 1 (by rfl) ⟨678293, by rfl⟩ : syracuseStep 904391 = 1356587) B1356587
theorem B4345177 : Blo 599292 4345177 := bstep (se 2 (by rfl) ⟨1629441, by rfl⟩ : syracuseStep 4345177 = 3258883) B3258883
theorem B904553 : Blo 599292 904553 := bstep (se 2 (by rfl) ⟨339207, by rfl⟩ : syracuseStep 904553 = 678415) B678415
theorem B675247 : Blo 599292 675247 := bstep (se 1 (by rfl) ⟨506435, by rfl⟩ : syracuseStep 675247 = 1012871) B1012871
theorem B904631 : Blo 599292 904631 := bstep (se 1 (by rfl) ⟨678473, by rfl⟩ : syracuseStep 904631 = 1356947) B1356947
theorem B2280905 : Blo 599292 2280905 := bstep (se 2 (by rfl) ⟨855339, by rfl⟩ : syracuseStep 2280905 = 1710679) B1710679
theorem B904667 : Blo 599292 904667 := bstep (se 1 (by rfl) ⟨678500, by rfl⟩ : syracuseStep 904667 = 1357001) B1357001
theorem B609967 : Blo 599292 609967 := bstep (se 1 (by rfl) ⟨457475, by rfl⟩ : syracuseStep 609967 = 914951) B914951
theorem B1232633 : Blo 599292 1232633 := bstep (se 2 (by rfl) ⟨462237, by rfl⟩ : syracuseStep 1232633 = 924475) B924475
theorem B10243907 : Blo 599292 10243907 := bstep (se 1 (by rfl) ⟨7682930, by rfl⟩ : syracuseStep 10243907 = 15365861) B15365861
theorem B675679 : Blo 599292 675679 := bstep (se 1 (by rfl) ⟨506759, by rfl⟩ : syracuseStep 675679 = 1013519) B1013519
theorem B8245111 : Blo 599292 8245111 := bstep (se 1 (by rfl) ⟨6183833, by rfl⟩ : syracuseStep 8245111 = 12367667) B12367667
theorem B2281391 : Blo 599292 2281391 := bstep (se 1 (by rfl) ⟨1711043, by rfl⟩ : syracuseStep 2281391 = 3422087) B3422087
theorem B3559355 : Blo 599292 3559355 := bstep (se 1 (by rfl) ⟨2669516, by rfl⟩ : syracuseStep 3559355 = 5339033) B5339033
theorem B26726597 : Blo 599292 26726597 := bstep (se 4 (by rfl) ⟨2505618, by rfl⟩ : syracuseStep 26726597 = 5011237) B5011237
theorem B676039 : Blo 599292 676039 := bstep (se 1 (by rfl) ⟨507029, by rfl⟩ : syracuseStep 676039 = 1014059) B1014059
theorem B3428669 : Blo 599292 3428669 := bstep (se 3 (by rfl) ⟨642875, by rfl⟩ : syracuseStep 3428669 = 1285751) B1285751
theorem B2282195 : Blo 599292 2282195 := bstep (se 1 (by rfl) ⟨1711646, by rfl⟩ : syracuseStep 2282195 = 3423293) B3423293
theorem B4576175 : Blo 599292 4576175 := bstep (se 1 (by rfl) ⟨3432131, by rfl⟩ : syracuseStep 4576175 = 6864263) B6864263
theorem B3429377 : Blo 599292 3429377 := bstep (se 2 (by rfl) ⟨1286016, by rfl⟩ : syracuseStep 3429377 = 2572033) B2572033
theorem B676903 : Blo 599292 676903 := bstep (se 1 (by rfl) ⟨507677, by rfl⟩ : syracuseStep 676903 = 1015355) B1015355
theorem B12342881 : Blo 599292 12342881 := bstep (se 2 (by rfl) ⟨4628580, by rfl⟩ : syracuseStep 12342881 = 9257161) B9257161
theorem B1922707 : Blo 599292 1922707 := bstep (se 1 (by rfl) ⟨1442030, by rfl⟩ : syracuseStep 1922707 = 2884061) B2884061
theorem B35149463 : Blo 599292 35149463 := bstep (se 1 (by rfl) ⟨26362097, by rfl⟩ : syracuseStep 35149463 = 52724195) B52724195
theorem B4347715 : Blo 599292 4347715 := bstep (se 1 (by rfl) ⟨3260786, by rfl⟩ : syracuseStep 4347715 = 6521573) B6521573
theorem B7788383 : Blo 599292 7788383 := bstep (se 1 (by rfl) ⟨5841287, by rfl⟩ : syracuseStep 7788383 = 11682575) B11682575
theorem B24697223 : Blo 599292 24697223 := bstep (se 1 (by rfl) ⟨18522917, by rfl⟩ : syracuseStep 24697223 = 37045835) B37045835
theorem B678523 : Blo 599292 678523 := bstep (se 1 (by rfl) ⟨508892, by rfl⟩ : syracuseStep 678523 = 1017785) B1017785
theorem B1956791 : Blo 599292 1956791 := bstep (se 1 (by rfl) ⟨1467593, by rfl⟩ : syracuseStep 1956791 = 2935187) B2935187
theorem B1825849 : Blo 599292 1825849 := bstep (se 2 (by rfl) ⟨684693, by rfl⟩ : syracuseStep 1825849 = 1369387) B1369387
theorem B2284625 : Blo 599292 2284625 := bstep (se 2 (by rfl) ⟨856734, by rfl⟩ : syracuseStep 2284625 = 1713469) B1713469
theorem B1137863 : Blo 599292 1137863 := bstep (se 1 (by rfl) ⟨853397, by rfl⟩ : syracuseStep 1137863 = 1706795) B1706795
theorem B7691543 : Blo 599292 7691543 := bstep (se 1 (by rfl) ⟨5768657, by rfl⟩ : syracuseStep 7691543 = 11537315) B11537315
theorem B941417 : Blo 599292 941417 := bstep (se 2 (by rfl) ⟨353031, by rfl⟩ : syracuseStep 941417 = 706063) B706063
theorem B2022785 : Blo 599292 2022785 := bstep (se 2 (by rfl) ⟨758544, by rfl⟩ : syracuseStep 2022785 = 1517089) B1517089
theorem B15457715 : Blo 599292 15457715 := bstep (se 1 (by rfl) ⟨11593286, by rfl⟩ : syracuseStep 15457715 = 23186573) B23186573
theorem B1924553 : Blo 599292 1924553 := bstep (se 2 (by rfl) ⟨721707, by rfl⟩ : syracuseStep 1924553 = 1443415) B1443415
theorem B2285081 : Blo 599292 2285081 := bstep (se 2 (by rfl) ⟨856905, by rfl⟩ : syracuseStep 2285081 = 1713811) B1713811
theorem B1170983 : Blo 599292 1170983 := bstep (se 1 (by rfl) ⟨878237, by rfl⟩ : syracuseStep 1170983 = 1756475) B1756475
theorem B1138387 : Blo 599292 1138387 := bstep (se 1 (by rfl) ⟨853790, by rfl⟩ : syracuseStep 1138387 = 1707581) B1707581
theorem B1924823 : Blo 599292 1924823 := bstep (se 1 (by rfl) ⟨1443617, by rfl⟩ : syracuseStep 1924823 = 2887235) B2887235
theorem B1924937 : Blo 599292 1924937 := bstep (se 2 (by rfl) ⟨721851, by rfl⟩ : syracuseStep 1924937 = 1443703) B1443703
theorem B1138607 : Blo 599292 1138607 := bstep (se 1 (by rfl) ⟨853955, by rfl⟩ : syracuseStep 1138607 = 1707911) B1707911
theorem B1925039 : Blo 599292 1925039 := bstep (se 1 (by rfl) ⟨1443779, by rfl⟩ : syracuseStep 1925039 = 2887559) B2887559
theorem B3858461 : Blo 599292 3858461 := bstep (se 3 (by rfl) ⟨723461, by rfl⟩ : syracuseStep 3858461 = 1446923) B1446923
theorem B2023595 : Blo 599292 2023595 := bstep (se 1 (by rfl) ⟨1517696, by rfl⟩ : syracuseStep 2023595 = 3035393) B3035393
theorem B1139017 : Blo 599292 1139017 := bstep (se 2 (by rfl) ⟨427131, by rfl⟩ : syracuseStep 1139017 = 854263) B854263
theorem B942443 : Blo 599292 942443 := bstep (se 1 (by rfl) ⟨706832, by rfl⟩ : syracuseStep 942443 = 1413665) B1413665
theorem B7725577 : Blo 599292 7725577 := bstep (se 2 (by rfl) ⟨2897091, by rfl⟩ : syracuseStep 7725577 = 5794183) B5794183
theorem B3039929 : Blo 599292 3039929 := bstep (se 2 (by rfl) ⟨1139973, by rfl⟩ : syracuseStep 3039929 = 2279947) B2279947
theorem B2286265 : Blo 599292 2286265 := bstep (se 2 (by rfl) ⟨857349, by rfl⟩ : syracuseStep 2286265 = 1714699) B1714699
theorem B2024135 : Blo 599292 2024135 := bstep (se 1 (by rfl) ⟨1518101, by rfl⟩ : syracuseStep 2024135 = 3036203) B3036203
theorem B3433751 : Blo 599292 3433751 := bstep (se 1 (by rfl) ⟨2575313, by rfl⟩ : syracuseStep 3433751 = 5150627) B5150627
theorem B2024999 : Blo 599292 2024999 := bstep (se 1 (by rfl) ⟨1518749, by rfl⟩ : syracuseStep 2024999 = 3037499) B3037499
theorem B2319911 : Blo 599292 2319911 := bstep (se 1 (by rfl) ⟨1739933, by rfl⟩ : syracuseStep 2319911 = 3479867) B3479867
theorem B2025107 : Blo 599292 2025107 := bstep (se 1 (by rfl) ⟨1518830, by rfl⟩ : syracuseStep 2025107 = 3037661) B3037661
theorem B3434183 : Blo 599292 3434183 := bstep (se 1 (by rfl) ⟨2575637, by rfl⟩ : syracuseStep 3434183 = 5151275) B5151275
theorem B2025323 : Blo 599292 2025323 := bstep (se 1 (by rfl) ⟨1518992, by rfl⟩ : syracuseStep 2025323 = 3037985) B3037985
theorem B2025377 : Blo 599292 2025377 := bstep (se 2 (by rfl) ⟨759516, by rfl⟩ : syracuseStep 2025377 = 1519033) B1519033
theorem B2287997 : Blo 599292 2287997 := bstep (se 3 (by rfl) ⟨428999, by rfl⟩ : syracuseStep 2287997 = 857999) B857999
theorem B2025971 : Blo 599292 2025971 := bstep (se 1 (by rfl) ⟨1519478, by rfl⟩ : syracuseStep 2025971 = 3038957) B3038957
theorem B1141447 : Blo 599292 1141447 := bstep (se 1 (by rfl) ⟨856085, by rfl⟩ : syracuseStep 1141447 = 1712171) B1712171
theorem B2026511 : Blo 599292 2026511 := bstep (se 1 (by rfl) ⟨1519883, by rfl⟩ : syracuseStep 2026511 = 3039767) B3039767
theorem B1830059 : Blo 599292 1830059 := bstep (se 1 (by rfl) ⟨1372544, by rfl⟩ : syracuseStep 1830059 = 2745089) B2745089
theorem B38890691 : Blo 599292 38890691 := bstep (se 1 (by rfl) ⟨29168018, by rfl⟩ : syracuseStep 38890691 = 58336037) B58336037
theorem B1142009 : Blo 599292 1142009 := bstep (se 2 (by rfl) ⟨428253, by rfl⟩ : syracuseStep 1142009 = 856507) B856507
theorem B1142191 : Blo 599292 1142191 := bstep (se 1 (by rfl) ⟨856643, by rfl⟩ : syracuseStep 1142191 = 1713287) B1713287
theorem B3665371 : Blo 599292 3665371 := bstep (se 1 (by rfl) ⟨2749028, by rfl⟩ : syracuseStep 3665371 = 5498057) B5498057
theorem B1928729 : Blo 599292 1928729 := bstep (se 2 (by rfl) ⟨723273, by rfl⟩ : syracuseStep 1928729 = 1446547) B1446547
theorem B2027105 : Blo 599292 2027105 := bstep (se 2 (by rfl) ⟨760164, by rfl⟩ : syracuseStep 2027105 = 1520329) B1520329
theorem B1011791 : Blo 599292 1011791 := bstep (se 1 (by rfl) ⟨758843, by rfl⟩ : syracuseStep 1011791 = 1517687) B1517687
theorem B2290139 : Blo 599292 2290139 := bstep (se 1 (by rfl) ⟨1717604, by rfl⟩ : syracuseStep 2290139 = 3435209) B3435209
theorem B3666491 : Blo 599292 3666491 := bstep (se 1 (by rfl) ⟨2749868, by rfl⟩ : syracuseStep 3666491 = 5499737) B5499737
theorem B1143467 : Blo 599292 1143467 := bstep (se 1 (by rfl) ⟨857600, by rfl⟩ : syracuseStep 1143467 = 1715201) B1715201
theorem B6517421 : Blo 599292 6517421 := bstep (se 3 (by rfl) ⟨1222016, by rfl⟩ : syracuseStep 6517421 = 2444033) B2444033
theorem B13202189 : Blo 599292 13202189 := bstep (se 3 (by rfl) ⟨2475410, by rfl⟩ : syracuseStep 13202189 = 4950821) B4950821
theorem B6157073 : Blo 599292 6157073 := bstep (se 2 (by rfl) ⟨2308902, by rfl⟩ : syracuseStep 6157073 = 4617805) B4617805
theorem B7729937 : Blo 599292 7729937 := bstep (se 2 (by rfl) ⟨2898726, by rfl⟩ : syracuseStep 7729937 = 5797453) B5797453
theorem B1143695 : Blo 599292 1143695 := bstep (se 1 (by rfl) ⟨857771, by rfl⟩ : syracuseStep 1143695 = 1715543) B1715543
theorem B1012655 : Blo 599292 1012655 := bstep (se 1 (by rfl) ⟨759491, by rfl⟩ : syracuseStep 1012655 = 1518983) B1518983
theorem B2028563 : Blo 599292 2028563 := bstep (se 1 (by rfl) ⟨1521422, by rfl⟩ : syracuseStep 2028563 = 3042845) B3042845
theorem B4551875 : Blo 599292 4551875 := bstep (se 1 (by rfl) ⟨3413906, by rfl⟩ : syracuseStep 4551875 = 6827813) B6827813
theorem B2028887 : Blo 599292 2028887 := bstep (se 1 (by rfl) ⟨1521665, by rfl⟩ : syracuseStep 2028887 = 3043331) B3043331
theorem B1013087 : Blo 599292 1013087 := bstep (se 1 (by rfl) ⟨759815, by rfl⟩ : syracuseStep 1013087 = 1519631) B1519631
theorem B685487 : Blo 599292 685487 := bstep (se 1 (by rfl) ⟨514115, by rfl⟩ : syracuseStep 685487 = 1028231) B1028231
theorem B4322803 : Blo 599292 4322803 := bstep (se 1 (by rfl) ⟨3242102, by rfl⟩ : syracuseStep 4322803 = 6484205) B6484205
theorem B3045113 : Blo 599292 3045113 := bstep (se 2 (by rfl) ⟨1141917, by rfl⟩ : syracuseStep 3045113 = 2283835) B2283835
theorem B8648491 : Blo 599292 8648491 := bstep (se 1 (by rfl) ⟨6486368, by rfl⟩ : syracuseStep 8648491 = 12972737) B12972737
theorem B2160479 : Blo 599292 2160479 := bstep (se 1 (by rfl) ⟨1620359, by rfl⟩ : syracuseStep 2160479 = 3240719) B3240719
theorem B1013647 : Blo 599292 1013647 := bstep (se 1 (by rfl) ⟨760235, by rfl⟩ : syracuseStep 1013647 = 1520471) B1520471
theorem B1144955 : Blo 599292 1144955 := bstep (se 1 (by rfl) ⟨858716, by rfl⟩ : syracuseStep 1144955 = 1717433) B1717433
theorem B3045761 : Blo 599292 3045761 := bstep (se 2 (by rfl) ⟨1142160, by rfl⟩ : syracuseStep 3045761 = 2284321) B2284321
theorem B2029967 : Blo 599292 2029967 := bstep (se 1 (by rfl) ⟨1522475, by rfl⟩ : syracuseStep 2029967 = 3044951) B3044951
theorem B3668489 : Blo 599292 3668489 := bstep (se 2 (by rfl) ⟨1375683, by rfl⟩ : syracuseStep 3668489 = 2751367) B2751367
theorem B3865097 : Blo 599292 3865097 := bstep (se 2 (by rfl) ⟨1449411, by rfl⟩ : syracuseStep 3865097 = 2898823) B2898823
theorem B1014329 : Blo 599292 1014329 := bstep (se 2 (by rfl) ⟨380373, by rfl⟩ : syracuseStep 1014329 = 760747) B760747
theorem B2030291 : Blo 599292 2030291 := bstep (se 1 (by rfl) ⟨1522718, by rfl⟩ : syracuseStep 2030291 = 3045437) B3045437
theorem B916319 : Blo 599292 916319 := bstep (se 1 (by rfl) ⟨687239, by rfl⟩ : syracuseStep 916319 = 1374479) B1374479
theorem B3046571 : Blo 599292 3046571 := bstep (se 1 (by rfl) ⟨2284928, by rfl⟩ : syracuseStep 3046571 = 4569857) B4569857
theorem B1015031 : Blo 599292 1015031 := bstep (se 1 (by rfl) ⟨761273, by rfl⟩ : syracuseStep 1015031 = 1522547) B1522547
theorem B55639385 : Blo 599292 55639385 := bstep (se 2 (by rfl) ⟨20864769, by rfl⟩ : syracuseStep 55639385 = 41729539) B41729539
theorem B2162209 : Blo 599292 2162209 := bstep (se 2 (by rfl) ⟨810828, by rfl⟩ : syracuseStep 2162209 = 1621657) B1621657
theorem B5471783 : Blo 599292 5471783 := bstep (se 1 (by rfl) ⟨4103837, by rfl⟩ : syracuseStep 5471783 = 8207675) B8207675
theorem B720463 : Blo 599292 720463 := bstep (se 1 (by rfl) ⟨540347, by rfl⟩ : syracuseStep 720463 = 1080695) B1080695
theorem B1015375 : Blo 599292 1015375 := bstep (se 1 (by rfl) ⟨761531, by rfl⟩ : syracuseStep 1015375 = 1523063) B1523063
theorem B3047057 : Blo 599292 3047057 := bstep (se 2 (by rfl) ⟨1142646, by rfl⟩ : syracuseStep 3047057 = 2285293) B2285293
theorem B1015625 : Blo 599292 1015625 := bstep (se 2 (by rfl) ⟨380859, by rfl⟩ : syracuseStep 1015625 = 761719) B761719
theorem B2031479 : Blo 599292 2031479 := bstep (se 1 (by rfl) ⟨1523609, by rfl⟩ : syracuseStep 2031479 = 3047219) B3047219
theorem B2031641 : Blo 599292 2031641 := bstep (se 2 (by rfl) ⟨761865, by rfl⟩ : syracuseStep 2031641 = 1523731) B1523731
theorem B1081711 : Blo 599292 1081711 := bstep (se 1 (by rfl) ⟨811283, by rfl⟩ : syracuseStep 1081711 = 1622567) B1622567
theorem B1081927 : Blo 599292 1081927 := bstep (se 1 (by rfl) ⟨811445, by rfl⟩ : syracuseStep 1081927 = 1622891) B1622891
theorem B1016543 : Blo 599292 1016543 := bstep (se 1 (by rfl) ⟨762407, by rfl⟩ : syracuseStep 1016543 = 1524815) B1524815
theorem B3048353 : Blo 599292 3048353 := bstep (se 2 (by rfl) ⟨1143132, by rfl⟩ : syracuseStep 3048353 = 2286265) B2286265
theorem B1016975 : Blo 599292 1016975 := bstep (se 1 (by rfl) ⟨762731, by rfl⟩ : syracuseStep 1016975 = 1525463) B1525463
theorem B2032883 : Blo 599292 2032883 := bstep (se 1 (by rfl) ⟨1524662, by rfl⟩ : syracuseStep 2032883 = 3049325) B3049325
theorem B6489395 : Blo 599292 6489395 := bstep (se 1 (by rfl) ⟨4867046, by rfl⟩ : syracuseStep 6489395 = 9734093) B9734093
theorem B2032991 : Blo 599292 2032991 := bstep (se 1 (by rfl) ⟨1524743, by rfl⟩ : syracuseStep 2032991 = 3049487) B3049487
theorem B1017211 : Blo 599292 1017211 := bstep (se 1 (by rfl) ⟨762908, by rfl⟩ : syracuseStep 1017211 = 1525817) B1525817
theorem B1443233 : Blo 599292 1443233 := bstep (se 2 (by rfl) ⟨541212, by rfl⟩ : syracuseStep 1443233 = 1082425) B1082425
theorem B1443625 : Blo 599292 1443625 := bstep (se 2 (by rfl) ⟨541359, by rfl⟩ : syracuseStep 1443625 = 1082719) B1082719
theorem B11569229 : Blo 599292 11569229 := bstep (se 3 (by rfl) ⟨2169230, by rfl⟩ : syracuseStep 11569229 = 4338461) B4338461
theorem B854383 : Blo 599292 854383 := bstep (se 1 (by rfl) ⟨640787, by rfl⟩ : syracuseStep 854383 = 1281575) B1281575
theorem B821755 : Blo 599292 821755 := bstep (se 1 (by rfl) ⟨616316, by rfl⟩ : syracuseStep 821755 = 1232633) B1232633
theorem B1706771 : Blo 599292 1706771 := bstep (se 1 (by rfl) ⟨1280078, by rfl⟩ : syracuseStep 1706771 = 2560157) B2560157
theorem B2034557 : Blo 599292 2034557 := bstep (se 3 (by rfl) ⟨381479, by rfl⟩ : syracuseStep 2034557 = 762959) B762959
theorem B3017843 : Blo 599292 3017843 := bstep (se 1 (by rfl) ⟨2263382, by rfl⟩ : syracuseStep 3017843 = 4526765) B4526765
theorem B2034827 : Blo 599292 2034827 := bstep (se 1 (by rfl) ⟨1526120, by rfl⟩ : syracuseStep 2034827 = 3052241) B3052241
theorem B1707227 : Blo 599292 1707227 := bstep (se 1 (by rfl) ⟨1280420, by rfl⟩ : syracuseStep 1707227 = 2560841) B2560841
theorem B2886943 : Blo 599292 2886943 := bstep (se 1 (by rfl) ⟨2165207, by rfl⟩ : syracuseStep 2886943 = 4330415) B4330415
theorem B2166047 : Blo 599292 2166047 := bstep (se 1 (by rfl) ⟨1624535, by rfl⟩ : syracuseStep 2166047 = 3249071) B3249071
theorem B3050783 : Blo 599292 3050783 := bstep (se 1 (by rfl) ⟨2288087, by rfl⟩ : syracuseStep 3050783 = 4576175) B4576175
theorem B8654141 : Blo 599292 8654141 := bstep (se 3 (by rfl) ⟨1622651, by rfl⟩ : syracuseStep 8654141 = 3245303) B3245303
theorem B1281377 : Blo 599292 1281377 := bstep (se 2 (by rfl) ⟨480516, by rfl⟩ : syracuseStep 1281377 = 961033) B961033
theorem B9244169 : Blo 599292 9244169 := bstep (se 2 (by rfl) ⟨3466563, by rfl⟩ : syracuseStep 9244169 = 6933127) B6933127
theorem B8228587 : Blo 599292 8228587 := bstep (se 1 (by rfl) ⟨6171440, by rfl⟩ : syracuseStep 8228587 = 12342881) B12342881
theorem B23432975 : Blo 599292 23432975 := bstep (se 1 (by rfl) ⟨17574731, by rfl⟩ : syracuseStep 23432975 = 35149463) B35149463
theorem B3248029 : Blo 599292 3248029 := bstep (se 3 (by rfl) ⟨609005, by rfl⟩ : syracuseStep 3248029 = 1218011) B1218011
theorem B15405227 : Blo 599292 15405227 := bstep (se 1 (by rfl) ⟨11553920, by rfl⟩ : syracuseStep 15405227 = 23107841) B23107841
theorem B4887161 : Blo 599292 4887161 := bstep (se 2 (by rfl) ⟨1832685, by rfl⟩ : syracuseStep 4887161 = 3665371) B3665371
theorem B3085003 : Blo 599292 3085003 := bstep (se 1 (by rfl) ⟨2313752, by rfl⟩ : syracuseStep 3085003 = 4627505) B4627505
theorem B758575 : Blo 599292 758575 := bstep (se 1 (by rfl) ⟨568931, by rfl⟩ : syracuseStep 758575 = 1137863) B1137863
theorem B1348523 : Blo 599292 1348523 := bstep (se 1 (by rfl) ⟨1011392, by rfl⟩ : syracuseStep 1348523 = 2022785) B2022785
theorem B2429891 : Blo 599292 2429891 := bstep (se 1 (by rfl) ⟨1822418, by rfl⟩ : syracuseStep 2429891 = 3644837) B3644837
theorem B1283035 : Blo 599292 1283035 := bstep (se 1 (by rfl) ⟨962276, by rfl⟩ : syracuseStep 1283035 = 1924553) B1924553
theorem B1283215 : Blo 599292 1283215 := bstep (se 1 (by rfl) ⟨962411, by rfl⟩ : syracuseStep 1283215 = 1924823) B1924823
theorem B1709255 : Blo 599292 1709255 := bstep (se 1 (by rfl) ⟨1281941, by rfl⟩ : syracuseStep 1709255 = 2563883) B2563883
theorem B1283291 : Blo 599292 1283291 := bstep (se 1 (by rfl) ⟨962468, by rfl⟩ : syracuseStep 1283291 = 1924937) B1924937
theorem B759071 : Blo 599292 759071 := bstep (se 1 (by rfl) ⟨569303, by rfl⟩ : syracuseStep 759071 = 1138607) B1138607
theorem B1283359 : Blo 599292 1283359 := bstep (se 1 (by rfl) ⟨962519, by rfl⟩ : syracuseStep 1283359 = 1925039) B1925039
theorem B1349063 : Blo 599292 1349063 := bstep (se 1 (by rfl) ⟨1011797, by rfl⟩ : syracuseStep 1349063 = 2023595) B2023595
theorem B628295 : Blo 599292 628295 := bstep (se 1 (by rfl) ⟨471221, by rfl⟩ : syracuseStep 628295 = 942443) B942443
theorem B3053213 : Blo 599292 3053213 := bstep (se 3 (by rfl) ⟨572477, by rfl⟩ : syracuseStep 3053213 = 1144955) B1144955
theorem B1349423 : Blo 599292 1349423 := bstep (se 1 (by rfl) ⟨1012067, by rfl⟩ : syracuseStep 1349423 = 2024135) B2024135
theorem B2168783 : Blo 599292 2168783 := bstep (se 1 (by rfl) ⟨1626587, by rfl⟩ : syracuseStep 2168783 = 3253175) B3253175
theorem B1448201 : Blo 599292 1448201 := bstep (se 2 (by rfl) ⟨543075, by rfl⟩ : syracuseStep 1448201 = 1086151) B1086151
theorem B1349999 : Blo 599292 1349999 := bstep (se 1 (by rfl) ⟨1012499, by rfl⟩ : syracuseStep 1349999 = 2024999) B2024999
theorem B1546607 : Blo 599292 1546607 := bstep (se 1 (by rfl) ⟨1159955, by rfl⟩ : syracuseStep 1546607 = 2319911) B2319911
theorem B1350071 : Blo 599292 1350071 := bstep (se 1 (by rfl) ⟨1012553, by rfl⟩ : syracuseStep 1350071 = 2025107) B2025107
theorem B1350215 : Blo 599292 1350215 := bstep (se 1 (by rfl) ⟨1012661, by rfl⟩ : syracuseStep 1350215 = 2025323) B2025323
theorem B1350251 : Blo 599292 1350251 := bstep (se 1 (by rfl) ⟨1012688, by rfl⟩ : syracuseStep 1350251 = 2025377) B2025377
theorem B8657603 : Blo 599292 8657603 := bstep (se 1 (by rfl) ⟨6493202, by rfl⟩ : syracuseStep 8657603 = 12986405) B12986405
theorem B1350647 : Blo 599292 1350647 := bstep (se 1 (by rfl) ⟨1012985, by rfl⟩ : syracuseStep 1350647 = 2025971) B2025971
theorem B3415229 : Blo 599292 3415229 := bstep (se 3 (by rfl) ⟨640355, by rfl⟩ : syracuseStep 3415229 = 1280711) B1280711
theorem B1351007 : Blo 599292 1351007 := bstep (se 1 (by rfl) ⟨1013255, by rfl⟩ : syracuseStep 1351007 = 2026511) B2026511
theorem B1220039 : Blo 599292 1220039 := bstep (se 1 (by rfl) ⟨915029, by rfl⟩ : syracuseStep 1220039 = 1830059) B1830059
theorem B25927127 : Blo 599292 25927127 := bstep (se 1 (by rfl) ⟨19445345, by rfl⟩ : syracuseStep 25927127 = 38890691) B38890691
theorem B1449431 : Blo 599292 1449431 := bstep (se 1 (by rfl) ⟨1087073, by rfl⟩ : syracuseStep 1449431 = 2174147) B2174147
theorem B761339 : Blo 599292 761339 := bstep (se 1 (by rfl) ⟨571004, by rfl⟩ : syracuseStep 761339 = 1142009) B1142009
theorem B2563609 : Blo 599292 2563609 := bstep (se 2 (by rfl) ⟨961353, by rfl⟩ : syracuseStep 2563609 = 1922707) B1922707
theorem B2563643 : Blo 599292 2563643 := bstep (se 1 (by rfl) ⟨1922732, by rfl⟩ : syracuseStep 2563643 = 3845465) B3845465
theorem B1351403 : Blo 599292 1351403 := bstep (se 1 (by rfl) ⟨1013552, by rfl⟩ : syracuseStep 1351403 = 2027105) B2027105
theorem B1351529 : Blo 599292 1351529 := bstep (se 2 (by rfl) ⟨506823, by rfl⟩ : syracuseStep 1351529 = 1013647) B1013647
theorem B5120009 : Blo 599292 5120009 := bstep (se 2 (by rfl) ⟨1920003, by rfl⟩ : syracuseStep 5120009 = 3840007) B3840007
theorem B1712137 : Blo 599292 1712137 := bstep (se 2 (by rfl) ⟨642051, by rfl⟩ : syracuseStep 1712137 = 1284103) B1284103
theorem B762311 : Blo 599292 762311 := bstep (se 1 (by rfl) ⟨571733, by rfl⟩ : syracuseStep 762311 = 1143467) B1143467
theorem B4104715 : Blo 599292 4104715 := bstep (se 1 (by rfl) ⟨3078536, by rfl⟩ : syracuseStep 4104715 = 6157073) B6157073
theorem B5153291 : Blo 599292 5153291 := bstep (se 1 (by rfl) ⟨3864968, by rfl⟩ : syracuseStep 5153291 = 7729937) B7729937
theorem B762463 : Blo 599292 762463 := bstep (se 1 (by rfl) ⟨571847, by rfl⟩ : syracuseStep 762463 = 1143695) B1143695
theorem B5120657 : Blo 599292 5120657 := bstep (se 2 (by rfl) ⟨1920246, by rfl⟩ : syracuseStep 5120657 = 3840493) B3840493
theorem B1352375 : Blo 599292 1352375 := bstep (se 1 (by rfl) ⟨1014281, by rfl⟩ : syracuseStep 1352375 = 2028563) B2028563
theorem B1352591 : Blo 599292 1352591 := bstep (se 1 (by rfl) ⟨1014443, by rfl⟩ : syracuseStep 1352591 = 2028887) B2028887
theorem B599327 : Blo 599292 599327 := bstep (se 1 (by rfl) ⟨449495, by rfl⟩ : syracuseStep 599327 = 898991) B898991
theorem B599387 : Blo 599292 599387 := bstep (se 1 (by rfl) ⟨449540, by rfl⟩ : syracuseStep 599387 = 899081) B899081
theorem B599407 : Blo 599292 599407 := bstep (se 1 (by rfl) ⟨449555, by rfl⟩ : syracuseStep 599407 = 899111) B899111
theorem B2434465 : Blo 599292 2434465 := bstep (se 2 (by rfl) ⟨912924, by rfl⟩ : syracuseStep 2434465 = 1825849) B1825849
theorem B599463 : Blo 599292 599463 := bstep (se 1 (by rfl) ⟨449597, by rfl⟩ : syracuseStep 599463 = 899195) B899195
theorem B3122621 : Blo 599292 3122621 := bstep (se 3 (by rfl) ⟨585491, by rfl⟩ : syracuseStep 3122621 = 1170983) B1170983
theorem B599547 : Blo 599292 599547 := bstep (se 1 (by rfl) ⟨449660, by rfl⟩ : syracuseStep 599547 = 899321) B899321
theorem B599615 : Blo 599292 599615 := bstep (se 1 (by rfl) ⟨449711, by rfl⟩ : syracuseStep 599615 = 899423) B899423
theorem B599623 : Blo 599292 599623 := bstep (se 1 (by rfl) ⟨449717, by rfl⟩ : syracuseStep 599623 = 899435) B899435
theorem B1353311 : Blo 599292 1353311 := bstep (se 1 (by rfl) ⟨1014983, by rfl⟩ : syracuseStep 1353311 = 2029967) B2029967
theorem B599775 : Blo 599292 599775 := bstep (se 1 (by rfl) ⟨449831, by rfl⟩ : syracuseStep 599775 = 899663) B899663
theorem B599855 : Blo 599292 599855 := bstep (se 1 (by rfl) ⟨449891, by rfl⟩ : syracuseStep 599855 = 899783) B899783
theorem B1353527 : Blo 599292 1353527 := bstep (se 1 (by rfl) ⟨1015145, by rfl⟩ : syracuseStep 1353527 = 2030291) B2030291
theorem B3286865 : Blo 599292 3286865 := bstep (se 2 (by rfl) ⟨1232574, by rfl⟩ : syracuseStep 3286865 = 2465149) B2465149
theorem B599963 : Blo 599292 599963 := bstep (se 1 (by rfl) ⟨449972, by rfl⟩ : syracuseStep 599963 = 899945) B899945
theorem B731035 : Blo 599292 731035 := bstep (se 1 (by rfl) ⟨548276, by rfl⟩ : syracuseStep 731035 = 1096553) B1096553
theorem B2893751 : Blo 599292 2893751 := bstep (se 1 (by rfl) ⟨2170313, by rfl⟩ : syracuseStep 2893751 = 4340627) B4340627
theorem B600015 : Blo 599292 600015 := bstep (se 1 (by rfl) ⟨450011, by rfl⟩ : syracuseStep 600015 = 900023) B900023
theorem B600039 : Blo 599292 600039 := bstep (se 1 (by rfl) ⟨450029, by rfl⟩ : syracuseStep 600039 = 900059) B900059
theorem B960617 : Blo 599292 960617 := bstep (se 2 (by rfl) ⟨360231, by rfl⟩ : syracuseStep 960617 = 720463) B720463
theorem B1353833 : Blo 599292 1353833 := bstep (se 2 (by rfl) ⟨507687, by rfl⟩ : syracuseStep 1353833 = 1015375) B1015375
theorem B1517849 : Blo 599292 1517849 := bstep (se 2 (by rfl) ⟨569193, by rfl⟩ : syracuseStep 1517849 = 1138387) B1138387
theorem B600351 : Blo 599292 600351 := bstep (se 1 (by rfl) ⟨450263, by rfl⟩ : syracuseStep 600351 = 900527) B900527
theorem B600411 : Blo 599292 600411 := bstep (se 1 (by rfl) ⟨450308, by rfl⟩ : syracuseStep 600411 = 900617) B900617
theorem B3647855 : Blo 599292 3647855 := bstep (se 1 (by rfl) ⟨2735891, by rfl⟩ : syracuseStep 3647855 = 5471783) B5471783
theorem B600431 : Blo 599292 600431 := bstep (se 1 (by rfl) ⟨450323, by rfl⟩ : syracuseStep 600431 = 900647) B900647
theorem B600487 : Blo 599292 600487 := bstep (se 1 (by rfl) ⟨450365, by rfl⟩ : syracuseStep 600487 = 900731) B900731
theorem B600571 : Blo 599292 600571 := bstep (se 1 (by rfl) ⟨450428, by rfl⟩ : syracuseStep 600571 = 900857) B900857
theorem B600639 : Blo 599292 600639 := bstep (se 1 (by rfl) ⟨450479, by rfl⟩ : syracuseStep 600639 = 900959) B900959
theorem B600647 : Blo 599292 600647 := bstep (se 1 (by rfl) ⟨450485, by rfl⟩ : syracuseStep 600647 = 900971) B900971
theorem B1354319 : Blo 599292 1354319 := bstep (se 1 (by rfl) ⟨1015739, by rfl⟩ : syracuseStep 1354319 = 2031479) B2031479
theorem B600799 : Blo 599292 600799 := bstep (se 1 (by rfl) ⟨450599, by rfl⟩ : syracuseStep 600799 = 901199) B901199
theorem B1354463 : Blo 599292 1354463 := bstep (se 1 (by rfl) ⟨1015847, by rfl⟩ : syracuseStep 1354463 = 2031695) B2031695
theorem B600879 : Blo 599292 600879 := bstep (se 1 (by rfl) ⟨450659, by rfl⟩ : syracuseStep 600879 = 901319) B901319
theorem B1715087 : Blo 599292 1715087 := bstep (se 1 (by rfl) ⟨1286315, by rfl⟩ : syracuseStep 1715087 = 2572631) B2572631
theorem B600987 : Blo 599292 600987 := bstep (se 1 (by rfl) ⟨450740, by rfl⟩ : syracuseStep 600987 = 901481) B901481
theorem B601039 : Blo 599292 601039 := bstep (se 1 (by rfl) ⟨450779, by rfl⟩ : syracuseStep 601039 = 901559) B901559
theorem B1354715 : Blo 599292 1354715 := bstep (se 1 (by rfl) ⟨1016036, by rfl⟩ : syracuseStep 1354715 = 2032073) B2032073
theorem B601063 : Blo 599292 601063 := bstep (se 1 (by rfl) ⟨450797, by rfl⟩ : syracuseStep 601063 = 901595) B901595
theorem B5778499 : Blo 599292 5778499 := bstep (se 1 (by rfl) ⟨4333874, by rfl⟩ : syracuseStep 5778499 = 8667749) B8667749
theorem B1518689 : Blo 599292 1518689 := bstep (se 2 (by rfl) ⟨569508, by rfl⟩ : syracuseStep 1518689 = 1139017) B1139017
theorem B1354895 : Blo 599292 1354895 := bstep (se 1 (by rfl) ⟨1016171, by rfl⟩ : syracuseStep 1354895 = 2032343) B2032343
theorem B3845339 : Blo 599292 3845339 := bstep (se 1 (by rfl) ⟨2884004, by rfl⟩ : syracuseStep 3845339 = 5768009) B5768009
theorem B1354985 : Blo 599292 1354985 := bstep (se 2 (by rfl) ⟨508119, by rfl⟩ : syracuseStep 1354985 = 1016239) B1016239
theorem B601375 : Blo 599292 601375 := bstep (se 1 (by rfl) ⟨451031, by rfl⟩ : syracuseStep 601375 = 902063) B902063
theorem B1355039 : Blo 599292 1355039 := bstep (se 1 (by rfl) ⟨1016279, by rfl⟩ : syracuseStep 1355039 = 2032559) B2032559
theorem B601435 : Blo 599292 601435 := bstep (se 1 (by rfl) ⟨451076, by rfl⟩ : syracuseStep 601435 = 902153) B902153
theorem B10300769 : Blo 599292 10300769 := bstep (se 2 (by rfl) ⟨3862788, by rfl⟩ : syracuseStep 10300769 = 7725577) B7725577
theorem B601455 : Blo 599292 601455 := bstep (se 1 (by rfl) ⟨451091, by rfl⟩ : syracuseStep 601455 = 902183) B902183
theorem B10136951 : Blo 599292 10136951 := bstep (se 1 (by rfl) ⟨7602713, by rfl⟩ : syracuseStep 10136951 = 15205427) B15205427
theorem B601511 : Blo 599292 601511 := bstep (se 1 (by rfl) ⟨451133, by rfl⟩ : syracuseStep 601511 = 902267) B902267
theorem B601595 : Blo 599292 601595 := bstep (se 1 (by rfl) ⟨451196, by rfl⟩ : syracuseStep 601595 = 902393) B902393
theorem B601663 : Blo 599292 601663 := bstep (se 1 (by rfl) ⟨451247, by rfl⟩ : syracuseStep 601663 = 902495) B902495
theorem B601671 : Blo 599292 601671 := bstep (se 1 (by rfl) ⟨451253, by rfl⟩ : syracuseStep 601671 = 902507) B902507
theorem B7712455 : Blo 599292 7712455 := bstep (se 1 (by rfl) ⟨5784341, by rfl⟩ : syracuseStep 7712455 = 11568683) B11568683
theorem B601823 : Blo 599292 601823 := bstep (se 1 (by rfl) ⟨451367, by rfl⟩ : syracuseStep 601823 = 902735) B902735
theorem B1715975 : Blo 599292 1715975 := bstep (se 1 (by rfl) ⟨1286981, by rfl⟩ : syracuseStep 1715975 = 2573963) B2573963
theorem B1355561 : Blo 599292 1355561 := bstep (se 2 (by rfl) ⟨508335, by rfl⟩ : syracuseStep 1355561 = 1016671) B1016671
theorem B2567983 : Blo 599292 2567983 := bstep (se 1 (by rfl) ⟨1925987, by rfl⟩ : syracuseStep 2567983 = 3851975) B3851975
theorem B601903 : Blo 599292 601903 := bstep (se 1 (by rfl) ⟨451427, by rfl⟩ : syracuseStep 601903 = 902855) B902855
theorem B602011 : Blo 599292 602011 := bstep (se 1 (by rfl) ⟨451508, by rfl⟩ : syracuseStep 602011 = 903017) B903017
theorem B4566941 : Blo 599292 4566941 := bstep (se 3 (by rfl) ⟨856301, by rfl⟩ : syracuseStep 4566941 = 1712603) B1712603
theorem B602063 : Blo 599292 602063 := bstep (se 1 (by rfl) ⟨451547, by rfl⟩ : syracuseStep 602063 = 903095) B903095
theorem B5779421 : Blo 599292 5779421 := bstep (se 3 (by rfl) ⟨1083641, by rfl⟩ : syracuseStep 5779421 = 2167283) B2167283
theorem B602087 : Blo 599292 602087 := bstep (se 1 (by rfl) ⟨451565, by rfl⟩ : syracuseStep 602087 = 903131) B903131
theorem B1716329 : Blo 599292 1716329 := bstep (se 2 (by rfl) ⟨643623, by rfl⟩ : syracuseStep 1716329 = 1287247) B1287247
theorem B602399 : Blo 599292 602399 := bstep (se 1 (by rfl) ⟨451799, by rfl⟩ : syracuseStep 602399 = 903599) B903599
theorem B602459 : Blo 599292 602459 := bstep (se 1 (by rfl) ⟨451844, by rfl⟩ : syracuseStep 602459 = 903689) B903689
theorem B602479 : Blo 599292 602479 := bstep (se 1 (by rfl) ⟨451859, by rfl⟩ : syracuseStep 602479 = 903719) B903719
theorem B602535 : Blo 599292 602535 := bstep (se 1 (by rfl) ⟨451901, by rfl⟩ : syracuseStep 602535 = 903803) B903803
theorem B602619 : Blo 599292 602619 := bstep (se 1 (by rfl) ⟨451964, by rfl⟩ : syracuseStep 602619 = 903929) B903929
theorem B1520147 : Blo 599292 1520147 := bstep (se 1 (by rfl) ⟨1140110, by rfl⟩ : syracuseStep 1520147 = 2280221) B2280221
theorem B8663597 : Blo 599292 8663597 := bstep (se 3 (by rfl) ⟨1624424, by rfl⟩ : syracuseStep 8663597 = 3248849) B3248849
theorem B602687 : Blo 599292 602687 := bstep (se 1 (by rfl) ⟨452015, by rfl⟩ : syracuseStep 602687 = 904031) B904031
theorem B52081217 : Blo 599292 52081217 := bstep (se 2 (by rfl) ⟨19530456, by rfl⟩ : syracuseStep 52081217 = 39060913) B39060913
theorem B602695 : Blo 599292 602695 := bstep (se 1 (by rfl) ⟨452021, by rfl⟩ : syracuseStep 602695 = 904043) B904043
theorem B602847 : Blo 599292 602847 := bstep (se 1 (by rfl) ⟨452135, by rfl⟩ : syracuseStep 602847 = 904271) B904271
theorem B602927 : Blo 599292 602927 := bstep (se 1 (by rfl) ⟨452195, by rfl⟩ : syracuseStep 602927 = 904391) B904391
theorem B1356623 : Blo 599292 1356623 := bstep (se 1 (by rfl) ⟨1017467, by rfl⟩ : syracuseStep 1356623 = 2034935) B2034935
theorem B603035 : Blo 599292 603035 := bstep (se 1 (by rfl) ⟨452276, by rfl⟩ : syracuseStep 603035 = 904553) B904553
theorem B603087 : Blo 599292 603087 := bstep (se 1 (by rfl) ⟨452315, by rfl⟩ : syracuseStep 603087 = 904631) B904631
theorem B1520603 : Blo 599292 1520603 := bstep (se 1 (by rfl) ⟨1140452, by rfl⟩ : syracuseStep 1520603 = 2280905) B2280905
theorem B603111 : Blo 599292 603111 := bstep (se 1 (by rfl) ⟨452333, by rfl⟩ : syracuseStep 603111 = 904667) B904667
theorem B1356839 : Blo 599292 1356839 := bstep (se 1 (by rfl) ⟨1017629, by rfl⟩ : syracuseStep 1356839 = 2035259) B2035259
theorem B6829271 : Blo 599292 6829271 := bstep (se 1 (by rfl) ⟨5121953, by rfl⟩ : syracuseStep 6829271 = 10243907) B10243907
theorem B1357019 : Blo 599292 1357019 := bstep (se 1 (by rfl) ⟨1017764, by rfl⟩ : syracuseStep 1357019 = 2035529) B2035529
theorem B1520927 : Blo 599292 1520927 := bstep (se 1 (by rfl) ⟨1140695, by rfl⟩ : syracuseStep 1520927 = 2281391) B2281391
theorem B2372903 : Blo 599292 2372903 := bstep (se 1 (by rfl) ⟨1779677, by rfl⟩ : syracuseStep 2372903 = 3559355) B3559355
theorem B1357217 : Blo 599292 1357217 := bstep (se 2 (by rfl) ⟨508956, by rfl⟩ : syracuseStep 1357217 = 1017913) B1017913
theorem B2897441 : Blo 599292 2897441 := bstep (se 2 (by rfl) ⟨1086540, by rfl⟩ : syracuseStep 2897441 = 2173081) B2173081
theorem B1521463 : Blo 599292 1521463 := bstep (se 1 (by rfl) ⟨1141097, by rfl⟩ : syracuseStep 1521463 = 2282195) B2282195
theorem B899177 : Blo 599292 899177 := bstep (se 2 (by rfl) ⟨337191, by rfl⟩ : syracuseStep 899177 = 674383) B674383
theorem B1521929 : Blo 599292 1521929 := bstep (se 2 (by rfl) ⟨570723, by rfl⟩ : syracuseStep 1521929 = 1141447) B1141447
theorem B964955 : Blo 599292 964955 := bstep (se 1 (by rfl) ⟨723716, by rfl⟩ : syracuseStep 964955 = 1447433) B1447433
theorem B899495 : Blo 599292 899495 := bstep (se 1 (by rfl) ⟨674621, by rfl⟩ : syracuseStep 899495 = 1349243) B1349243
theorem B10041781 : Blo 599292 10041781 := bstep (se 5 (by rfl) ⟨470708, by rfl⟩ : syracuseStep 10041781 = 941417) B941417
theorem B899579 : Blo 599292 899579 := bstep (se 1 (by rfl) ⟨674684, by rfl⟩ : syracuseStep 899579 = 1349369) B1349369
theorem B13023767 : Blo 599292 13023767 := bstep (se 1 (by rfl) ⟨9767825, by rfl⟩ : syracuseStep 13023767 = 19535651) B19535651
theorem B5192255 : Blo 599292 5192255 := bstep (se 1 (by rfl) ⟨3894191, by rfl⟩ : syracuseStep 5192255 = 7788383) B7788383
theorem B899705 : Blo 599292 899705 := bstep (se 2 (by rfl) ⟨337389, by rfl⟩ : syracuseStep 899705 = 674779) B674779
theorem B899759 : Blo 599292 899759 := bstep (se 1 (by rfl) ⟨674819, by rfl⟩ : syracuseStep 899759 = 1349639) B1349639
theorem B899807 : Blo 599292 899807 := bstep (se 1 (by rfl) ⟨674855, by rfl⟩ : syracuseStep 899807 = 1349711) B1349711
theorem B4635535 : Blo 599292 4635535 := bstep (se 1 (by rfl) ⟨3476651, by rfl⟩ : syracuseStep 4635535 = 6953303) B6953303
theorem B16464815 : Blo 599292 16464815 := bstep (se 1 (by rfl) ⟨12348611, by rfl⟩ : syracuseStep 16464815 = 24697223) B24697223
theorem B900071 : Blo 599292 900071 := bstep (se 1 (by rfl) ⟨675053, by rfl⟩ : syracuseStep 900071 = 1350107) B1350107
theorem B900329 : Blo 599292 900329 := bstep (se 2 (by rfl) ⟨337623, by rfl⟩ : syracuseStep 900329 = 675247) B675247
theorem B1522921 : Blo 599292 1522921 := bstep (se 2 (by rfl) ⟨571095, by rfl⟩ : syracuseStep 1522921 = 1142191) B1142191
theorem B900383 : Blo 599292 900383 := bstep (se 1 (by rfl) ⟨675287, by rfl⟩ : syracuseStep 900383 = 1350575) B1350575
theorem B1523083 : Blo 599292 1523083 := bstep (se 1 (by rfl) ⟨1142312, by rfl⟩ : syracuseStep 1523083 = 2284625) B2284625
theorem B900551 : Blo 599292 900551 := bstep (se 1 (by rfl) ⟨675413, by rfl⟩ : syracuseStep 900551 = 1350827) B1350827
theorem B5127695 : Blo 599292 5127695 := bstep (se 1 (by rfl) ⟨3845771, by rfl⟩ : syracuseStep 5127695 = 7691543) B7691543
theorem B10305143 : Blo 599292 10305143 := bstep (se 1 (by rfl) ⟨7728857, by rfl⟩ : syracuseStep 10305143 = 15457715) B15457715
theorem B1523387 : Blo 599292 1523387 := bstep (se 1 (by rfl) ⟨1142540, by rfl⟩ : syracuseStep 1523387 = 2285081) B2285081
theorem B900905 : Blo 599292 900905 := bstep (se 2 (by rfl) ⟨337839, by rfl⟩ : syracuseStep 900905 = 675679) B675679
theorem B900911 : Blo 599292 900911 := bstep (se 1 (by rfl) ⟨675683, by rfl⟩ : syracuseStep 900911 = 1351367) B1351367
theorem B10993481 : Blo 599292 10993481 := bstep (se 2 (by rfl) ⟨4122555, by rfl⟩ : syracuseStep 10993481 = 8245111) B8245111
theorem B3260267 : Blo 599292 3260267 := bstep (se 1 (by rfl) ⟨2445200, by rfl⟩ : syracuseStep 3260267 = 4890401) B4890401
theorem B18530315 : Blo 599292 18530315 := bstep (se 1 (by rfl) ⟨13897736, by rfl⟩ : syracuseStep 18530315 = 27795473) B27795473
theorem B2572307 : Blo 599292 2572307 := bstep (se 1 (by rfl) ⟨1929230, by rfl⟩ : syracuseStep 2572307 = 3858461) B3858461
theorem B901385 : Blo 599292 901385 := bstep (se 2 (by rfl) ⟨338019, by rfl⟩ : syracuseStep 901385 = 676039) B676039
theorem B901487 : Blo 599292 901487 := bstep (se 1 (by rfl) ⟨676115, by rfl⟩ : syracuseStep 901487 = 1352231) B1352231
theorem B901703 : Blo 599292 901703 := bstep (se 1 (by rfl) ⟨676277, by rfl⟩ : syracuseStep 901703 = 1352555) B1352555
theorem B901739 : Blo 599292 901739 := bstep (se 1 (by rfl) ⟨676304, by rfl⟩ : syracuseStep 901739 = 1352609) B1352609
theorem B3850897 : Blo 599292 3850897 := bstep (se 2 (by rfl) ⟨1444086, by rfl⟩ : syracuseStep 3850897 = 2888173) B2888173
theorem B770743 : Blo 599292 770743 := bstep (se 1 (by rfl) ⟨578057, by rfl⟩ : syracuseStep 770743 = 1156115) B1156115
theorem B901967 : Blo 599292 901967 := bstep (se 1 (by rfl) ⟨676475, by rfl⟩ : syracuseStep 901967 = 1352951) B1352951
theorem B640219 : Blo 599292 640219 := bstep (se 1 (by rfl) ⟨480164, by rfl⟩ : syracuseStep 640219 = 960329) B960329
theorem B902363 : Blo 599292 902363 := bstep (se 1 (by rfl) ⟨676772, by rfl⟩ : syracuseStep 902363 = 1353545) B1353545
theorem B902537 : Blo 599292 902537 := bstep (se 2 (by rfl) ⟨338451, by rfl⟩ : syracuseStep 902537 = 676903) B676903
theorem B1525331 : Blo 599292 1525331 := bstep (se 1 (by rfl) ⟨1143998, by rfl⟩ : syracuseStep 1525331 = 2287997) B2287997
theorem B902891 : Blo 599292 902891 := bstep (se 1 (by rfl) ⟨677168, by rfl⟩ : syracuseStep 902891 = 1354337) B1354337
theorem B2279249 : Blo 599292 2279249 := bstep (se 2 (by rfl) ⟨854718, by rfl⟩ : syracuseStep 2279249 = 1709437) B1709437
theorem B903119 : Blo 599292 903119 := bstep (se 1 (by rfl) ⟨677339, by rfl⟩ : syracuseStep 903119 = 1354679) B1354679
theorem B2443517 : Blo 599292 2443517 := bstep (se 3 (by rfl) ⟨458159, by rfl⟩ : syracuseStep 2443517 = 916319) B916319
theorem B903515 : Blo 599292 903515 := bstep (se 1 (by rfl) ⟨677636, by rfl⟩ : syracuseStep 903515 = 1355273) B1355273
theorem B903743 : Blo 599292 903743 := bstep (se 1 (by rfl) ⟨677807, by rfl⟩ : syracuseStep 903743 = 1355615) B1355615
theorem B903863 : Blo 599292 903863 := bstep (se 1 (by rfl) ⟨677897, by rfl⟩ : syracuseStep 903863 = 1355795) B1355795
theorem B674527 : Blo 599292 674527 := bstep (se 1 (by rfl) ⟨505895, by rfl⟩ : syracuseStep 674527 = 1011791) B1011791
theorem B5557015 : Blo 599292 5557015 := bstep (se 1 (by rfl) ⟨4167761, by rfl⟩ : syracuseStep 5557015 = 8335523) B8335523
theorem B904091 : Blo 599292 904091 := bstep (se 1 (by rfl) ⟨678068, by rfl⟩ : syracuseStep 904091 = 1356137) B1356137
theorem B2608043 : Blo 599292 2608043 := bstep (se 1 (by rfl) ⟨1956032, by rfl⟩ : syracuseStep 2608043 = 3912065) B3912065
theorem B1526759 : Blo 599292 1526759 := bstep (se 1 (by rfl) ⟨1145069, by rfl⟩ : syracuseStep 1526759 = 2290139) B2290139
theorem B1625075 : Blo 599292 1625075 := bstep (se 1 (by rfl) ⟨1218806, by rfl⟩ : syracuseStep 1625075 = 2437613) B2437613
theorem B2444327 : Blo 599292 2444327 := bstep (se 1 (by rfl) ⟨1833245, by rfl⟩ : syracuseStep 2444327 = 3666491) B3666491
theorem B4344947 : Blo 599292 4344947 := bstep (se 1 (by rfl) ⟨3258710, by rfl⟩ : syracuseStep 4344947 = 6517421) B6517421
theorem B8801459 : Blo 599292 8801459 := bstep (se 1 (by rfl) ⟨6601094, by rfl⟩ : syracuseStep 8801459 = 13202189) B13202189
theorem B2935997 : Blo 599292 2935997 := bstep (se 3 (by rfl) ⟨550499, by rfl⟩ : syracuseStep 2935997 = 1100999) B1100999
theorem B675103 : Blo 599292 675103 := bstep (se 1 (by rfl) ⟨506327, by rfl⟩ : syracuseStep 675103 = 1012655) B1012655
theorem B904487 : Blo 599292 904487 := bstep (se 1 (by rfl) ⟨678365, by rfl⟩ : syracuseStep 904487 = 1356731) B1356731
theorem B904571 : Blo 599292 904571 := bstep (se 1 (by rfl) ⟨678428, by rfl⟩ : syracuseStep 904571 = 1356857) B1356857
theorem B3034583 : Blo 599292 3034583 := bstep (se 1 (by rfl) ⟨2275937, by rfl⟩ : syracuseStep 3034583 = 4551875) B4551875
theorem B2280919 : Blo 599292 2280919 := bstep (se 1 (by rfl) ⟨1710689, by rfl⟩ : syracuseStep 2280919 = 3421379) B3421379
theorem B904697 : Blo 599292 904697 := bstep (se 2 (by rfl) ⟨339261, by rfl⟩ : syracuseStep 904697 = 678523) B678523
theorem B4869641 : Blo 599292 4869641 := bstep (se 2 (by rfl) ⟨1826115, by rfl⟩ : syracuseStep 4869641 = 3652231) B3652231
theorem B2674201 : Blo 599292 2674201 := bstep (se 2 (by rfl) ⟨1002825, by rfl⟩ : syracuseStep 2674201 = 2005651) B2005651
theorem B675391 : Blo 599292 675391 := bstep (se 1 (by rfl) ⟨506543, by rfl⟩ : syracuseStep 675391 = 1013087) B1013087
theorem B904799 : Blo 599292 904799 := bstep (se 1 (by rfl) ⟨678599, by rfl⟩ : syracuseStep 904799 = 1357199) B1357199
theorem B2281223 : Blo 599292 2281223 := bstep (se 1 (by rfl) ⟨1710917, by rfl⟩ : syracuseStep 2281223 = 3421835) B3421835
theorem B2445659 : Blo 599292 2445659 := bstep (se 1 (by rfl) ⟨1834244, by rfl⟩ : syracuseStep 2445659 = 3668489) B3668489
theorem B2576731 : Blo 599292 2576731 := bstep (se 1 (by rfl) ⟨1932548, by rfl⟩ : syracuseStep 2576731 = 3865097) B3865097
theorem B676219 : Blo 599292 676219 := bstep (se 1 (by rfl) ⟨507164, by rfl⟩ : syracuseStep 676219 = 1014329) B1014329
theorem B676687 : Blo 599292 676687 := bstep (se 1 (by rfl) ⟨507515, by rfl⟩ : syracuseStep 676687 = 1015031) B1015031
theorem B677083 : Blo 599292 677083 := bstep (se 1 (by rfl) ⟨507812, by rfl⟩ : syracuseStep 677083 = 1015625) B1015625
theorem B25974179 : Blo 599292 25974179 := bstep (se 1 (by rfl) ⟨19480634, by rfl⟩ : syracuseStep 25974179 = 38961269) B38961269
theorem B677371 : Blo 599292 677371 := bstep (se 1 (by rfl) ⟨508028, by rfl⟩ : syracuseStep 677371 = 1016057) B1016057
theorem B677551 : Blo 599292 677551 := bstep (se 1 (by rfl) ⟨508163, by rfl⟩ : syracuseStep 677551 = 1016327) B1016327
theorem B190502725 : Blo 599292 190502725 := bstep (se 4 (by rfl) ⟨17859630, by rfl⟩ : syracuseStep 190502725 = 35719261) B35719261
theorem B677839 : Blo 599292 677839 := bstep (se 1 (by rfl) ⟨508379, by rfl⟩ : syracuseStep 677839 = 1016759) B1016759
theorem B4348151 : Blo 599292 4348151 := bstep (se 1 (by rfl) ⟨3261113, by rfl⟩ : syracuseStep 4348151 = 6522227) B6522227
theorem B678235 : Blo 599292 678235 := bstep (se 1 (by rfl) ⟨508676, by rfl⟩ : syracuseStep 678235 = 1017353) B1017353
theorem B678343 : Blo 599292 678343 := bstep (se 1 (by rfl) ⟨508757, by rfl⟩ : syracuseStep 678343 = 1017515) B1017515
theorem B4119113 : Blo 599292 4119113 := bstep (se 2 (by rfl) ⟨1544667, by rfl⟩ : syracuseStep 4119113 = 3089335) B3089335
theorem B2284139 : Blo 599292 2284139 := bstep (se 1 (by rfl) ⟨1713104, by rfl⟩ : syracuseStep 2284139 = 3426209) B3426209
theorem B2284307 : Blo 599292 2284307 := bstep (se 1 (by rfl) ⟨1713230, by rfl⟩ : syracuseStep 2284307 = 3426461) B3426461
theorem B678703 : Blo 599292 678703 := bstep (se 1 (by rfl) ⟨509027, by rfl⟩ : syracuseStep 678703 = 1018055) B1018055
theorem B5136169 : Blo 599292 5136169 := bstep (se 2 (by rfl) ⟨1926063, by rfl⟩ : syracuseStep 5136169 = 3852127) B3852127
theorem B2023325 : Blo 599292 2023325 := bstep (se 3 (by rfl) ⟨379373, by rfl⟩ : syracuseStep 2023325 = 758747) B758747
theorem B2023433 : Blo 599292 2023433 := bstep (se 2 (by rfl) ⟨758787, by rfl⟩ : syracuseStep 2023433 = 1517575) B1517575
theorem B17817731 : Blo 599292 17817731 := bstep (se 1 (by rfl) ⟨13363298, by rfl⟩ : syracuseStep 17817731 = 26726597) B26726597
theorem B3039443 : Blo 599292 3039443 := bstep (se 1 (by rfl) ⟨2279582, by rfl⟩ : syracuseStep 3039443 = 4559165) B4559165
theorem B2285779 : Blo 599292 2285779 := bstep (se 1 (by rfl) ⟨1714334, by rfl⟩ : syracuseStep 2285779 = 3428669) B3428669
theorem B1139321 : Blo 599292 1139321 := bstep (se 2 (by rfl) ⟨427245, by rfl⟩ : syracuseStep 1139321 = 854491) B854491
theorem B2286251 : Blo 599292 2286251 := bstep (se 1 (by rfl) ⟨1714688, by rfl⟩ : syracuseStep 2286251 = 3429377) B3429377
theorem B5137505 : Blo 599292 5137505 := bstep (se 2 (by rfl) ⟨1926564, by rfl⟩ : syracuseStep 5137505 = 3853129) B3853129
theorem B1827965 : Blo 599292 1827965 := bstep (se 3 (by rfl) ⟨342743, by rfl⟩ : syracuseStep 1827965 = 685487) B685487
theorem B1926269 : Blo 599292 1926269 := bstep (se 3 (by rfl) ⟨361175, by rfl⟩ : syracuseStep 1926269 = 722351) B722351
theorem B1140065 : Blo 599292 1140065 := bstep (se 2 (by rfl) ⟨427524, by rfl⟩ : syracuseStep 1140065 = 855049) B855049
theorem B5793569 : Blo 599292 5793569 := bstep (se 2 (by rfl) ⟨2172588, by rfl⟩ : syracuseStep 5793569 = 4345177) B4345177
theorem B1304527 : Blo 599292 1304527 := bstep (se 1 (by rfl) ⟨978395, by rfl⟩ : syracuseStep 1304527 = 1956791) B1956791
theorem B813289 : Blo 599292 813289 := bstep (se 2 (by rfl) ⟨304983, by rfl⟩ : syracuseStep 813289 = 609967) B609967
theorem B5761277 : Blo 599292 5761277 := bstep (se 3 (by rfl) ⟨1080239, by rfl⟩ : syracuseStep 5761277 = 2160479) B2160479
theorem B1730983 : Blo 599292 1730983 := bstep (se 1 (by rfl) ⟨1298237, by rfl⟩ : syracuseStep 1730983 = 2596475) B2596475
theorem B1141523 : Blo 599292 1141523 := bstep (se 1 (by rfl) ⟨856142, by rfl⟩ : syracuseStep 1141523 = 1712285) B1712285
theorem B1141751 : Blo 599292 1141751 := bstep (se 1 (by rfl) ⟨856313, by rfl⟩ : syracuseStep 1141751 = 1712627) B1712627
theorem B2026619 : Blo 599292 2026619 := bstep (se 1 (by rfl) ⟨1519964, by rfl⟩ : syracuseStep 2026619 = 3039929) B3039929
theorem B1928411 : Blo 599292 1928411 := bstep (se 1 (by rfl) ⟨1446308, by rfl⟩ : syracuseStep 1928411 = 2892617) B2892617
theorem B814375 : Blo 599292 814375 := bstep (se 1 (by rfl) ⟨610781, by rfl⟩ : syracuseStep 814375 = 1221563) B1221563
theorem B2026889 : Blo 599292 2026889 := bstep (se 2 (by rfl) ⟨760083, by rfl⟩ : syracuseStep 2026889 = 1520167) B1520167
theorem B8220149 : Blo 599292 8220149 := bstep (se 5 (by rfl) ⟨385319, by rfl⟩ : syracuseStep 8220149 = 770639) B770639
theorem B2289167 : Blo 599292 2289167 := bstep (se 1 (by rfl) ⟨1716875, by rfl⟩ : syracuseStep 2289167 = 3433751) B3433751
theorem B2289455 : Blo 599292 2289455 := bstep (se 1 (by rfl) ⟨1717091, by rfl⟩ : syracuseStep 2289455 = 3434183) B3434183
theorem B2027321 : Blo 599292 2027321 := bstep (se 2 (by rfl) ⟨760245, by rfl⟩ : syracuseStep 2027321 = 1520491) B1520491
theorem B1929089 : Blo 599292 1929089 := bstep (se 2 (by rfl) ⟨723408, by rfl⟩ : syracuseStep 1929089 = 1446817) B1446817
theorem B1012135 : Blo 599292 1012135 := bstep (se 1 (by rfl) ⟨759101, by rfl⟩ : syracuseStep 1012135 = 1518203) B1518203
theorem B1012297 : Blo 599292 1012297 := bstep (se 2 (by rfl) ⟨379611, by rfl⟩ : syracuseStep 1012297 = 759223) B759223
theorem B1012331 : Blo 599292 1012331 := bstep (se 1 (by rfl) ⟨759248, by rfl⟩ : syracuseStep 1012331 = 1518497) B1518497
theorem B5763737 : Blo 599292 5763737 := bstep (se 2 (by rfl) ⟨2161401, by rfl⟩ : syracuseStep 5763737 = 4322803) B4322803
theorem B2028185 : Blo 599292 2028185 := bstep (se 2 (by rfl) ⟨760569, by rfl⟩ : syracuseStep 2028185 = 1521139) B1521139
theorem B881327 : Blo 599292 881327 := bstep (se 1 (by rfl) ⟨660995, by rfl⟩ : syracuseStep 881327 = 1321991) B1321991
theorem B11531321 : Blo 599292 11531321 := bstep (se 2 (by rfl) ⟨4324245, by rfl⟩ : syracuseStep 11531321 = 8648491) B8648491
theorem B3863609 : Blo 599292 3863609 := bstep (se 2 (by rfl) ⟨1448853, by rfl⟩ : syracuseStep 3863609 = 2897707) B2897707
theorem B5796953 : Blo 599292 5796953 := bstep (se 2 (by rfl) ⟨2173857, by rfl⟩ : syracuseStep 5796953 = 4347715) B4347715
theorem B2029697 : Blo 599292 2029697 := bstep (se 2 (by rfl) ⟨761136, by rfl⟩ : syracuseStep 2029697 = 1522273) B1522273
theorem B1014025 : Blo 599292 1014025 := bstep (se 2 (by rfl) ⟨380259, by rfl⟩ : syracuseStep 1014025 = 760519) B760519
theorem B2030075 : Blo 599292 2030075 := bstep (se 1 (by rfl) ⟨1522556, by rfl⟩ : syracuseStep 2030075 = 3045113) B3045113
theorem B5143277 : Blo 599292 5143277 := bstep (se 3 (by rfl) ⟨964364, by rfl⟩ : syracuseStep 5143277 = 1928729) B1928729
theorem B2030507 : Blo 599292 2030507 := bstep (se 1 (by rfl) ⟨1522880, by rfl⟩ : syracuseStep 2030507 = 3045761) B3045761
theorem B5209019 : Blo 599292 5209019 := bstep (se 1 (by rfl) ⟨3906764, by rfl⟩ : syracuseStep 5209019 = 7813529) B7813529
theorem B2882945 : Blo 599292 2882945 := bstep (se 2 (by rfl) ⟨1081104, by rfl⟩ : syracuseStep 2882945 = 2162209) B2162209
theorem B2031047 : Blo 599292 2031047 := bstep (se 1 (by rfl) ⟨1523285, by rfl⟩ : syracuseStep 2031047 = 3046571) B3046571
theorem B37092923 : Blo 599292 37092923 := bstep (se 1 (by rfl) ⟨27819692, by rfl⟩ : syracuseStep 37092923 = 55639385) B55639385
theorem B1015483 : Blo 599292 1015483 := bstep (se 1 (by rfl) ⟨761612, by rfl⟩ : syracuseStep 1015483 = 1523225) B1523225
theorem B2031371 : Blo 599292 2031371 := bstep (se 1 (by rfl) ⟨1523528, by rfl⟩ : syracuseStep 2031371 = 3047057) B3047057
theorem B12353543 : Blo 599292 12353543 := bstep (se 1 (by rfl) ⟨9265157, by rfl⟩ : syracuseStep 12353543 = 18530315) B18530315
theorem B3047705 : Blo 599292 3047705 := bstep (se 2 (by rfl) ⟨1142889, by rfl⟩ : syracuseStep 3047705 = 2285779) B2285779
theorem B1442281 : Blo 599292 1442281 := bstep (se 2 (by rfl) ⟨540855, by rfl⟩ : syracuseStep 1442281 = 1081711) B1081711
theorem B2032235 : Blo 599292 2032235 := bstep (se 1 (by rfl) ⟨1524176, by rfl⟩ : syracuseStep 2032235 = 3048353) B3048353
theorem B5472953 : Blo 599292 5472953 := bstep (se 2 (by rfl) ⟨2052357, by rfl⟩ : syracuseStep 5472953 = 4104715) B4104715
theorem B1016617 : Blo 599292 1016617 := bstep (se 2 (by rfl) ⟨381231, by rfl⟩ : syracuseStep 1016617 = 762463) B762463
theorem B4326263 : Blo 599292 4326263 := bstep (se 1 (by rfl) ⟨3244697, by rfl⟩ : syracuseStep 4326263 = 6489395) B6489395
theorem B1016887 : Blo 599292 1016887 := bstep (se 1 (by rfl) ⟨762665, by rfl⟩ : syracuseStep 1016887 = 1525331) B1525331
theorem B2032829 : Blo 599292 2032829 := bstep (se 3 (by rfl) ⟨381155, by rfl⟩ : syracuseStep 2032829 = 762311) B762311
theorem B853625 : Blo 599292 853625 := bstep (se 2 (by rfl) ⟨320109, by rfl⟩ : syracuseStep 853625 = 640219) B640219
theorem B3245953 : Blo 599292 3245953 := bstep (se 2 (by rfl) ⟨1217232, by rfl⟩ : syracuseStep 3245953 = 2434465) B2434465
theorem B1017839 : Blo 599292 1017839 := bstep (se 1 (by rfl) ⟨763379, by rfl⟩ : syracuseStep 1017839 = 1526759) B1526759
theorem B1083383 : Blo 599292 1083383 := bstep (se 1 (by rfl) ⟨812537, by rfl⟩ : syracuseStep 1083383 = 1625075) B1625075
theorem B5867639 : Blo 599292 5867639 := bstep (se 1 (by rfl) ⟨4400729, by rfl⟩ : syracuseStep 5867639 = 8801459) B8801459
theorem B1444031 : Blo 599292 1444031 := bstep (se 1 (by rfl) ⟨1083023, by rfl⟩ : syracuseStep 1444031 = 2166047) B2166047
theorem B2033855 : Blo 599292 2033855 := bstep (se 1 (by rfl) ⟨1525391, by rfl⟩ : syracuseStep 2033855 = 3050783) B3050783
theorem B5769427 : Blo 599292 5769427 := bstep (se 1 (by rfl) ⟨4327070, by rfl⟩ : syracuseStep 5769427 = 8654141) B8654141
theorem B6162779 : Blo 599292 6162779 := bstep (se 1 (by rfl) ⟨4622084, by rfl⟩ : syracuseStep 6162779 = 9244169) B9244169
theorem B3246427 : Blo 599292 3246427 := bstep (se 1 (by rfl) ⟨2434820, by rfl⟩ : syracuseStep 3246427 = 4869641) B4869641
theorem B1084385 : Blo 599292 1084385 := bstep (se 2 (by rfl) ⟨406644, by rfl⟩ : syracuseStep 1084385 = 813289) B813289
theorem B5770277 : Blo 599292 5770277 := bstep (se 4 (by rfl) ⟨540963, by rfl⟩ : syracuseStep 5770277 = 1081927) B1081927
theorem B855527 : Blo 599292 855527 := bstep (se 1 (by rfl) ⟨641645, by rfl⟩ : syracuseStep 855527 = 1283291) B1283291
theorem B2035475 : Blo 599292 2035475 := bstep (se 1 (by rfl) ⟨1526606, by rfl⟩ : syracuseStep 2035475 = 3053213) B3053213
theorem B1445855 : Blo 599292 1445855 := bstep (se 1 (by rfl) ⟨1084391, by rfl⟩ : syracuseStep 1445855 = 2168783) B2168783
theorem B7704665 : Blo 599292 7704665 := bstep (se 2 (by rfl) ⟨2889249, by rfl⟩ : syracuseStep 7704665 = 5778499) B5778499
theorem B1675453 : Blo 599292 1675453 := bstep (se 3 (by rfl) ⟨314147, by rfl⟩ : syracuseStep 1675453 = 628295) B628295
theorem B1085833 : Blo 599292 1085833 := bstep (se 2 (by rfl) ⟨407187, by rfl⟩ : syracuseStep 1085833 = 814375) B814375
theorem B5771735 : Blo 599292 5771735 := bstep (se 1 (by rfl) ⟨4328801, by rfl⟩ : syracuseStep 5771735 = 8657603) B8657603
theorem B1709095 : Blo 599292 1709095 := bstep (se 1 (by rfl) ⟨1281821, by rfl⟩ : syracuseStep 1709095 = 2563643) B2563643
theorem B4330705 : Blo 599292 4330705 := bstep (se 2 (by rfl) ⟨1624014, by rfl⟩ : syracuseStep 4330705 = 3248029) B3248029
theorem B1348883 : Blo 599292 1348883 := bstep (se 1 (by rfl) ⟨1011662, by rfl⟩ : syracuseStep 1348883 = 2023325) B2023325
theorem B3413339 : Blo 599292 3413339 := bstep (se 1 (by rfl) ⟨2560004, by rfl⟩ : syracuseStep 3413339 = 5120009) B5120009
theorem B1348955 : Blo 599292 1348955 := bstep (se 1 (by rfl) ⟨1011716, by rfl⟩ : syracuseStep 1348955 = 2023433) B2023433
theorem B2561645 : Blo 599292 2561645 := bstep (se 3 (by rfl) ⟨480308, by rfl⟩ : syracuseStep 2561645 = 960617) B960617
theorem B759547 : Blo 599292 759547 := bstep (se 1 (by rfl) ⟨569660, by rfl⟩ : syracuseStep 759547 = 1139321) B1139321
theorem B3413771 : Blo 599292 3413771 := bstep (se 1 (by rfl) ⟨2560328, by rfl⟩ : syracuseStep 3413771 = 5120657) B5120657
theorem B1349513 : Blo 599292 1349513 := bstep (se 2 (by rfl) ⟨506067, by rfl⟩ : syracuseStep 1349513 = 1012135) B1012135
theorem B1284179 : Blo 599292 1284179 := bstep (se 1 (by rfl) ⟨963134, by rfl⟩ : syracuseStep 1284179 = 1926269) B1926269
theorem B1349729 : Blo 599292 1349729 := bstep (se 2 (by rfl) ⟨506148, by rfl⟩ : syracuseStep 1349729 = 1012297) B1012297
theorem B760043 : Blo 599292 760043 := bstep (se 1 (by rfl) ⟨570032, by rfl⟩ : syracuseStep 760043 = 1140065) B1140065
theorem B1710713 : Blo 599292 1710713 := bstep (se 2 (by rfl) ⟨641517, by rfl⟩ : syracuseStep 1710713 = 1283035) B1283035
theorem B3840851 : Blo 599292 3840851 := bstep (se 1 (by rfl) ⟨2880638, by rfl⟩ : syracuseStep 3840851 = 5761277) B5761277
theorem B1710953 : Blo 599292 1710953 := bstep (se 2 (by rfl) ⟨641607, by rfl⟩ : syracuseStep 1710953 = 1283215) B1283215
theorem B2431903 : Blo 599292 2431903 := bstep (se 1 (by rfl) ⟨1823927, by rfl⟩ : syracuseStep 2431903 = 3647855) B3647855
theorem B1711145 : Blo 599292 1711145 := bstep (se 2 (by rfl) ⟨641679, by rfl⟩ : syracuseStep 1711145 = 1283359) B1283359
theorem B761015 : Blo 599292 761015 := bstep (se 1 (by rfl) ⟨570761, by rfl⟩ : syracuseStep 761015 = 1141523) B1141523
theorem B761167 : Blo 599292 761167 := bstep (se 1 (by rfl) ⟨570875, by rfl⟩ : syracuseStep 761167 = 1141751) B1141751
theorem B1351079 : Blo 599292 1351079 := bstep (se 1 (by rfl) ⟨1013309, by rfl⟩ : syracuseStep 1351079 = 2026619) B2026619
theorem B2563559 : Blo 599292 2563559 := bstep (se 1 (by rfl) ⟨1922669, by rfl⟩ : syracuseStep 2563559 = 3845339) B3845339
theorem B1285607 : Blo 599292 1285607 := bstep (se 1 (by rfl) ⟨964205, by rfl⟩ : syracuseStep 1285607 = 1928411) B1928411
theorem B6757967 : Blo 599292 6757967 := bstep (se 1 (by rfl) ⟨5068475, by rfl⟩ : syracuseStep 6757967 = 10136951) B10136951
theorem B1351259 : Blo 599292 1351259 := bstep (se 1 (by rfl) ⟨1013444, by rfl⟩ : syracuseStep 1351259 = 2026889) B2026889
theorem B5480099 : Blo 599292 5480099 := bstep (se 1 (by rfl) ⟨4110074, by rfl⟩ : syracuseStep 5480099 = 8220149) B8220149
theorem B6954781 : Blo 599292 6954781 := bstep (se 3 (by rfl) ⟨1304021, by rfl⟩ : syracuseStep 6954781 = 2608043) B2608043
theorem B1351547 : Blo 599292 1351547 := bstep (se 1 (by rfl) ⟨1013660, by rfl⟩ : syracuseStep 1351547 = 2027321) B2027321
theorem B1286059 : Blo 599292 1286059 := bstep (se 1 (by rfl) ⟨964544, by rfl⟩ : syracuseStep 1286059 = 1929089) B1929089
theorem B1352033 : Blo 599292 1352033 := bstep (se 2 (by rfl) ⟨507012, by rfl⟩ : syracuseStep 1352033 = 1014025) B1014025
theorem B5775731 : Blo 599292 5775731 := bstep (se 1 (by rfl) ⟨4331798, by rfl⟩ : syracuseStep 5775731 = 8663597) B8663597
theorem B3842491 : Blo 599292 3842491 := bstep (se 1 (by rfl) ⟨2881868, by rfl⟩ : syracuseStep 3842491 = 5763737) B5763737
theorem B1352123 : Blo 599292 1352123 := bstep (se 1 (by rfl) ⟨1014092, by rfl⟩ : syracuseStep 1352123 = 2028185) B2028185
theorem B1581935 : Blo 599292 1581935 := bstep (se 1 (by rfl) ⟨1186451, by rfl⟩ : syracuseStep 1581935 = 2372903) B2372903
theorem B3417005 : Blo 599292 3417005 := bstep (se 3 (by rfl) ⟨640688, by rfl⟩ : syracuseStep 3417005 = 1281377) B1281377
theorem B599451 : Blo 599292 599451 := bstep (se 1 (by rfl) ⟨449588, by rfl⟩ : syracuseStep 599451 = 899177) B899177
theorem B1353131 : Blo 599292 1353131 := bstep (se 1 (by rfl) ⟨1014848, by rfl⟩ : syracuseStep 1353131 = 2029697) B2029697
theorem B599663 : Blo 599292 599663 := bstep (se 1 (by rfl) ⟨449747, by rfl⟩ : syracuseStep 599663 = 899495) B899495
theorem B27829909 : Blo 599292 27829909 := bstep (se 6 (by rfl) ⟨652263, by rfl⟩ : syracuseStep 27829909 = 1304527) B1304527
theorem B599719 : Blo 599292 599719 := bstep (se 1 (by rfl) ⟨449789, by rfl⟩ : syracuseStep 599719 = 899579) B899579
theorem B1353383 : Blo 599292 1353383 := bstep (se 1 (by rfl) ⟨1015037, by rfl⟩ : syracuseStep 1353383 = 2030075) B2030075
theorem B599803 : Blo 599292 599803 := bstep (se 1 (by rfl) ⟨449852, by rfl⟩ : syracuseStep 599803 = 899705) B899705
theorem B599839 : Blo 599292 599839 := bstep (se 1 (by rfl) ⟨449879, by rfl⟩ : syracuseStep 599839 = 899759) B899759
theorem B599871 : Blo 599292 599871 := bstep (se 1 (by rfl) ⟨449903, by rfl⟩ : syracuseStep 599871 = 899807) B899807
theorem B1353671 : Blo 599292 1353671 := bstep (se 1 (by rfl) ⟨1015253, by rfl⟩ : syracuseStep 1353671 = 2030507) B2030507
theorem B600047 : Blo 599292 600047 := bstep (se 1 (by rfl) ⟨450035, by rfl⟩ : syracuseStep 600047 = 900071) B900071
theorem B3418145 : Blo 599292 3418145 := bstep (se 2 (by rfl) ⟨1281804, by rfl⟩ : syracuseStep 3418145 = 2563609) B2563609
theorem B600219 : Blo 599292 600219 := bstep (se 1 (by rfl) ⟨450164, by rfl⟩ : syracuseStep 600219 = 900329) B900329
theorem B600255 : Blo 599292 600255 := bstep (se 1 (by rfl) ⟨450191, by rfl⟩ : syracuseStep 600255 = 900383) B900383
theorem B1353977 : Blo 599292 1353977 := bstep (se 2 (by rfl) ⟨507741, by rfl⟩ : syracuseStep 1353977 = 1015483) B1015483
theorem B600367 : Blo 599292 600367 := bstep (se 1 (by rfl) ⟨450275, by rfl⟩ : syracuseStep 600367 = 900551) B900551
theorem B1354031 : Blo 599292 1354031 := bstep (se 1 (by rfl) ⟨1015523, by rfl⟩ : syracuseStep 1354031 = 2031047) B2031047
theorem B3418463 : Blo 599292 3418463 := bstep (se 1 (by rfl) ⟨2563847, by rfl⟩ : syracuseStep 3418463 = 5127695) B5127695
theorem B1354247 : Blo 599292 1354247 := bstep (se 1 (by rfl) ⟨1015685, by rfl⟩ : syracuseStep 1354247 = 2031371) B2031371
theorem B600603 : Blo 599292 600603 := bstep (se 1 (by rfl) ⟨450452, by rfl⟩ : syracuseStep 600603 = 900905) B900905
theorem B600607 : Blo 599292 600607 := bstep (se 1 (by rfl) ⟨450455, by rfl⟩ : syracuseStep 600607 = 900911) B900911
theorem B2173511 : Blo 599292 2173511 := bstep (se 1 (by rfl) ⟨1630133, by rfl⟩ : syracuseStep 2173511 = 3260267) B3260267
theorem B1714871 : Blo 599292 1714871 := bstep (se 1 (by rfl) ⟨1286153, by rfl⟩ : syracuseStep 1714871 = 2572307) B2572307
theorem B1354427 : Blo 599292 1354427 := bstep (se 1 (by rfl) ⟨1015820, by rfl⟩ : syracuseStep 1354427 = 2031641) B2031641
theorem B600923 : Blo 599292 600923 := bstep (se 1 (by rfl) ⟨450692, by rfl⟩ : syracuseStep 600923 = 901385) B901385
theorem B600991 : Blo 599292 600991 := bstep (se 1 (by rfl) ⟨450743, by rfl⟩ : syracuseStep 600991 = 901487) B901487
theorem B601135 : Blo 599292 601135 := bstep (se 1 (by rfl) ⟨450851, by rfl⟩ : syracuseStep 601135 = 901703) B901703
theorem B601159 : Blo 599292 601159 := bstep (se 1 (by rfl) ⟨450869, by rfl⟩ : syracuseStep 601159 = 901739) B901739
theorem B601311 : Blo 599292 601311 := bstep (se 1 (by rfl) ⟨450983, by rfl⟩ : syracuseStep 601311 = 901967) B901967
theorem B601575 : Blo 599292 601575 := bstep (se 1 (by rfl) ⟨451181, by rfl⟩ : syracuseStep 601575 = 902363) B902363
theorem B1355255 : Blo 599292 1355255 := bstep (se 1 (by rfl) ⟨1016441, by rfl⟩ : syracuseStep 1355255 = 2032883) B2032883
theorem B1355327 : Blo 599292 1355327 := bstep (se 1 (by rfl) ⟨1016495, by rfl⟩ : syracuseStep 1355327 = 2032991) B2032991
theorem B1027657 : Blo 599292 1027657 := bstep (se 2 (by rfl) ⟨385371, by rfl⟩ : syracuseStep 1027657 = 770743) B770743
theorem B601691 : Blo 599292 601691 := bstep (se 1 (by rfl) ⟨451268, by rfl⟩ : syracuseStep 601691 = 902537) B902537
theorem B962155 : Blo 599292 962155 := bstep (se 1 (by rfl) ⟨721616, by rfl⟩ : syracuseStep 962155 = 1443233) B1443233
theorem B601927 : Blo 599292 601927 := bstep (se 1 (by rfl) ⟨451445, by rfl⟩ : syracuseStep 601927 = 902891) B902891
theorem B1519499 : Blo 599292 1519499 := bstep (se 1 (by rfl) ⟨1139624, by rfl⟩ : syracuseStep 1519499 = 2279249) B2279249
theorem B602079 : Blo 599292 602079 := bstep (se 1 (by rfl) ⟨451559, by rfl⟩ : syracuseStep 602079 = 903119) B903119
theorem B7712819 : Blo 599292 7712819 := bstep (se 1 (by rfl) ⟨5784614, by rfl⟩ : syracuseStep 7712819 = 11569229) B11569229
theorem B602343 : Blo 599292 602343 := bstep (se 1 (by rfl) ⟨451757, by rfl⟩ : syracuseStep 602343 = 903515) B903515
theorem B602495 : Blo 599292 602495 := bstep (se 1 (by rfl) ⟨451871, by rfl⟩ : syracuseStep 602495 = 903743) B903743
theorem B602575 : Blo 599292 602575 := bstep (se 1 (by rfl) ⟨451931, by rfl⟩ : syracuseStep 602575 = 903863) B903863
theorem B1356281 : Blo 599292 1356281 := bstep (se 2 (by rfl) ⟨508605, by rfl⟩ : syracuseStep 1356281 = 1017211) B1017211
theorem B1356371 : Blo 599292 1356371 := bstep (se 1 (by rfl) ⟨1017278, by rfl⟩ : syracuseStep 1356371 = 2034557) B2034557
theorem B602727 : Blo 599292 602727 := bstep (se 1 (by rfl) ⟨452045, by rfl⟩ : syracuseStep 602727 = 904091) B904091
theorem B2011895 : Blo 599292 2011895 := bstep (se 1 (by rfl) ⟨1508921, by rfl⟩ : syracuseStep 2011895 = 3017843) B3017843
theorem B2896631 : Blo 599292 2896631 := bstep (se 1 (by rfl) ⟨2172473, by rfl⟩ : syracuseStep 2896631 = 4344947) B4344947
theorem B1356551 : Blo 599292 1356551 := bstep (se 1 (by rfl) ⟨1017413, by rfl⟩ : syracuseStep 1356551 = 2034827) B2034827
theorem B602991 : Blo 599292 602991 := bstep (se 1 (by rfl) ⟨452243, by rfl⟩ : syracuseStep 602991 = 904487) B904487
theorem B603047 : Blo 599292 603047 := bstep (se 1 (by rfl) ⟨452285, by rfl⟩ : syracuseStep 603047 = 904571) B904571
theorem B603131 : Blo 599292 603131 := bstep (se 1 (by rfl) ⟨452348, by rfl⟩ : syracuseStep 603131 = 904697) B904697
theorem B603199 : Blo 599292 603199 := bstep (se 1 (by rfl) ⟨452399, by rfl⟩ : syracuseStep 603199 = 904799) B904799
theorem B1520815 : Blo 599292 1520815 := bstep (se 1 (by rfl) ⟨1140611, by rfl⟩ : syracuseStep 1520815 = 2281223) B2281223
theorem B10270151 : Blo 599292 10270151 := bstep (se 1 (by rfl) ⟨7702613, by rfl⟩ : syracuseStep 10270151 = 15405227) B15405227
theorem B3258107 : Blo 599292 3258107 := bstep (se 1 (by rfl) ⟨2443580, by rfl⟩ : syracuseStep 3258107 = 4887161) B4887161
theorem B2307977 : Blo 599292 2307977 := bstep (se 2 (by rfl) ⟨865491, by rfl⟩ : syracuseStep 2307977 = 1730983) B1730983
theorem B899015 : Blo 599292 899015 := bstep (se 1 (by rfl) ⟨674261, by rfl⟩ : syracuseStep 899015 = 1348523) B1348523
theorem B1619927 : Blo 599292 1619927 := bstep (se 1 (by rfl) ⟨1214945, by rfl⟩ : syracuseStep 1619927 = 2429891) B2429891
theorem B17316119 : Blo 599292 17316119 := bstep (se 1 (by rfl) ⟨12987089, by rfl⟩ : syracuseStep 17316119 = 25974179) B25974179
theorem B899369 : Blo 599292 899369 := bstep (se 2 (by rfl) ⟨337263, by rfl⟩ : syracuseStep 899369 = 674527) B674527
theorem B899375 : Blo 599292 899375 := bstep (se 1 (by rfl) ⟨674531, by rfl⟩ : syracuseStep 899375 = 1349063) B1349063
theorem B899615 : Blo 599292 899615 := bstep (se 1 (by rfl) ⟨674711, by rfl⟩ : syracuseStep 899615 = 1349423) B1349423
theorem B29637413 : Blo 599292 29637413 := bstep (se 4 (by rfl) ⟨2778507, by rfl⟩ : syracuseStep 29637413 = 5557015) B5557015
theorem B2898767 : Blo 599292 2898767 := bstep (se 1 (by rfl) ⟨2174075, by rfl⟩ : syracuseStep 2898767 = 4348151) B4348151
theorem B965467 : Blo 599292 965467 := bstep (se 1 (by rfl) ⟨724100, by rfl⟩ : syracuseStep 965467 = 1448201) B1448201
theorem B899999 : Blo 599292 899999 := bstep (se 1 (by rfl) ⟨674999, by rfl⟩ : syracuseStep 899999 = 1349999) B1349999
theorem B1031071 : Blo 599292 1031071 := bstep (se 1 (by rfl) ⟨773303, by rfl⟩ : syracuseStep 1031071 = 1546607) B1546607
theorem B900047 : Blo 599292 900047 := bstep (se 1 (by rfl) ⟨675035, by rfl⟩ : syracuseStep 900047 = 1350071) B1350071
theorem B900137 : Blo 599292 900137 := bstep (se 2 (by rfl) ⟨337551, by rfl⟩ : syracuseStep 900137 = 675103) B675103
theorem B3849257 : Blo 599292 3849257 := bstep (se 2 (by rfl) ⟨1443471, by rfl⟩ : syracuseStep 3849257 = 2886943) B2886943
theorem B900143 : Blo 599292 900143 := bstep (se 1 (by rfl) ⟨675107, by rfl⟩ : syracuseStep 900143 = 1350215) B1350215
theorem B900167 : Blo 599292 900167 := bstep (se 1 (by rfl) ⟨675125, by rfl⟩ : syracuseStep 900167 = 1350251) B1350251
theorem B1522759 : Blo 599292 1522759 := bstep (se 1 (by rfl) ⟨1142069, by rfl⟩ : syracuseStep 1522759 = 2284139) B2284139
theorem B1522871 : Blo 599292 1522871 := bstep (se 1 (by rfl) ⟨1142153, by rfl⟩ : syracuseStep 1522871 = 2284307) B2284307
theorem B900431 : Blo 599292 900431 := bstep (se 1 (by rfl) ⟨675323, by rfl⟩ : syracuseStep 900431 = 1350647) B1350647
theorem B900521 : Blo 599292 900521 := bstep (se 2 (by rfl) ⟨337695, by rfl⟩ : syracuseStep 900521 = 675391) B675391
theorem B2276819 : Blo 599292 2276819 := bstep (se 1 (by rfl) ⟨1707614, by rfl⟩ : syracuseStep 2276819 = 3415229) B3415229
theorem B8764973 : Blo 599292 8764973 := bstep (se 3 (by rfl) ⟨1643432, by rfl⟩ : syracuseStep 8764973 = 3286865) B3286865
theorem B900671 : Blo 599292 900671 := bstep (se 1 (by rfl) ⟨675503, by rfl⟩ : syracuseStep 900671 = 1351007) B1351007
theorem B17284751 : Blo 599292 17284751 := bstep (se 1 (by rfl) ⟨12963563, by rfl⟩ : syracuseStep 17284751 = 25927127) B25927127
theorem B966287 : Blo 599292 966287 := bstep (se 1 (by rfl) ⟨724715, by rfl⟩ : syracuseStep 966287 = 1449431) B1449431
theorem B3423977 : Blo 599292 3423977 := bstep (se 2 (by rfl) ⟨1283991, by rfl⟩ : syracuseStep 3423977 = 2567983) B2567983
theorem B900935 : Blo 599292 900935 := bstep (se 1 (by rfl) ⟨675701, by rfl⟩ : syracuseStep 900935 = 1351403) B1351403
theorem B901019 : Blo 599292 901019 := bstep (se 1 (by rfl) ⟨675764, by rfl⟩ : syracuseStep 901019 = 1351529) B1351529
theorem B11878487 : Blo 599292 11878487 := bstep (se 1 (by rfl) ⟨8908865, by rfl⟩ : syracuseStep 11878487 = 17817731) B17817731
theorem B1524167 : Blo 599292 1524167 := bstep (se 1 (by rfl) ⟨1143125, by rfl⟩ : syracuseStep 1524167 = 2286251) B2286251
theorem B901583 : Blo 599292 901583 := bstep (se 1 (by rfl) ⟨676187, by rfl⟩ : syracuseStep 901583 = 1352375) B1352375
theorem B901625 : Blo 599292 901625 := bstep (se 2 (by rfl) ⟨338109, by rfl⟩ : syracuseStep 901625 = 676219) B676219
theorem B901727 : Blo 599292 901727 := bstep (se 1 (by rfl) ⟨676295, by rfl⟩ : syracuseStep 901727 = 1352591) B1352591
theorem B3425003 : Blo 599292 3425003 := bstep (se 1 (by rfl) ⟨2568752, by rfl⟩ : syracuseStep 3425003 = 5137505) B5137505
theorem B4113337 : Blo 599292 4113337 := bstep (se 2 (by rfl) ⟨1542501, by rfl⟩ : syracuseStep 4113337 = 3085003) B3085003
theorem B2081747 : Blo 599292 2081747 := bstep (se 1 (by rfl) ⟨1561310, by rfl⟩ : syracuseStep 2081747 = 3122621) B3122621
theorem B902207 : Blo 599292 902207 := bstep (se 1 (by rfl) ⟨676655, by rfl⟩ : syracuseStep 902207 = 1353311) B1353311
theorem B902249 : Blo 599292 902249 := bstep (se 2 (by rfl) ⟨338343, by rfl⟩ : syracuseStep 902249 = 676687) B676687
theorem B902351 : Blo 599292 902351 := bstep (se 1 (by rfl) ⟨676763, by rfl⟩ : syracuseStep 902351 = 1353527) B1353527
theorem B902555 : Blo 599292 902555 := bstep (se 1 (by rfl) ⟨676916, by rfl⟩ : syracuseStep 902555 = 1353833) B1353833
theorem B902777 : Blo 599292 902777 := bstep (se 2 (by rfl) ⟨338541, by rfl⟩ : syracuseStep 902777 = 677083) B677083
theorem B902879 : Blo 599292 902879 := bstep (se 1 (by rfl) ⟨677159, by rfl⟩ : syracuseStep 902879 = 1354319) B1354319
theorem B902975 : Blo 599292 902975 := bstep (se 1 (by rfl) ⟨677231, by rfl⟩ : syracuseStep 902975 = 1354463) B1354463
theorem B903143 : Blo 599292 903143 := bstep (se 1 (by rfl) ⟨677357, by rfl⟩ : syracuseStep 903143 = 1354715) B1354715
theorem B903161 : Blo 599292 903161 := bstep (se 2 (by rfl) ⟨338685, by rfl⟩ : syracuseStep 903161 = 677371) B677371
theorem B903263 : Blo 599292 903263 := bstep (se 1 (by rfl) ⟨677447, by rfl⟩ : syracuseStep 903263 = 1354895) B1354895
theorem B903323 : Blo 599292 903323 := bstep (se 1 (by rfl) ⟨677492, by rfl⟩ : syracuseStep 903323 = 1354985) B1354985
theorem B903359 : Blo 599292 903359 := bstep (se 1 (by rfl) ⟨677519, by rfl⟩ : syracuseStep 903359 = 1355039) B1355039
theorem B903401 : Blo 599292 903401 := bstep (se 2 (by rfl) ⟨338775, by rfl⟩ : syracuseStep 903401 = 677551) B677551
theorem B6867179 : Blo 599292 6867179 := bstep (se 1 (by rfl) ⟨5150384, by rfl⟩ : syracuseStep 6867179 = 10300769) B10300769
theorem B1526111 : Blo 599292 1526111 := bstep (se 1 (by rfl) ⟨1144583, by rfl⟩ : syracuseStep 1526111 = 2289167) B2289167
theorem B254003633 : Blo 599292 254003633 := bstep (se 2 (by rfl) ⟨95251362, by rfl⟩ : syracuseStep 254003633 = 190502725) B190502725
theorem B903707 : Blo 599292 903707 := bstep (se 1 (by rfl) ⟨677780, by rfl⟩ : syracuseStep 903707 = 1355561) B1355561
theorem B1526303 : Blo 599292 1526303 := bstep (se 1 (by rfl) ⟨1144727, by rfl⟩ : syracuseStep 1526303 = 2289455) B2289455
theorem B903785 : Blo 599292 903785 := bstep (se 2 (by rfl) ⟨338919, by rfl⟩ : syracuseStep 903785 = 677839) B677839
theorem B3852947 : Blo 599292 3852947 := bstep (se 1 (by rfl) ⟨2889710, by rfl⟩ : syracuseStep 3852947 = 5779421) B5779421
theorem B34720811 : Blo 599292 34720811 := bstep (se 1 (by rfl) ⟨26040608, by rfl⟩ : syracuseStep 34720811 = 52081217) B52081217
theorem B674887 : Blo 599292 674887 := bstep (se 1 (by rfl) ⟨506165, by rfl⟩ : syracuseStep 674887 = 1012331) B1012331
theorem B904313 : Blo 599292 904313 := bstep (se 2 (by rfl) ⟨339117, by rfl⟩ : syracuseStep 904313 = 678235) B678235
theorem B904415 : Blo 599292 904415 := bstep (se 1 (by rfl) ⟨678311, by rfl⟩ : syracuseStep 904415 = 1356623) B1356623
theorem B13389041 : Blo 599292 13389041 := bstep (se 2 (by rfl) ⟨5020890, by rfl⟩ : syracuseStep 13389041 = 10041781) B10041781
theorem B904457 : Blo 599292 904457 := bstep (se 2 (by rfl) ⟨339171, by rfl⟩ : syracuseStep 904457 = 678343) B678343
theorem B904559 : Blo 599292 904559 := bstep (se 1 (by rfl) ⟨678419, by rfl⟩ : syracuseStep 904559 = 1356839) B1356839
theorem B7687547 : Blo 599292 7687547 := bstep (se 1 (by rfl) ⟨5765660, by rfl⟩ : syracuseStep 7687547 = 11531321) B11531321
theorem B2575739 : Blo 599292 2575739 := bstep (se 1 (by rfl) ⟨1931804, by rfl⟩ : syracuseStep 2575739 = 3863609) B3863609
theorem B904679 : Blo 599292 904679 := bstep (se 1 (by rfl) ⟨678509, by rfl⟩ : syracuseStep 904679 = 1357019) B1357019
theorem B904811 : Blo 599292 904811 := bstep (se 1 (by rfl) ⟨678608, by rfl⟩ : syracuseStep 904811 = 1357217) B1357217
theorem B904937 : Blo 599292 904937 := bstep (se 2 (by rfl) ⟨339351, by rfl⟩ : syracuseStep 904937 = 678703) B678703
theorem B6180713 : Blo 599292 6180713 := bstep (se 2 (by rfl) ⟨2317767, by rfl⟩ : syracuseStep 6180713 = 4635535) B4635535
theorem B643303 : Blo 599292 643303 := bstep (se 1 (by rfl) ⟨482477, by rfl⟩ : syracuseStep 643303 = 964955) B964955
theorem B3461503 : Blo 599292 3461503 := bstep (se 1 (by rfl) ⟨2596127, by rfl⟩ : syracuseStep 3461503 = 5192255) B5192255
theorem B3428851 : Blo 599292 3428851 := bstep (se 1 (by rfl) ⟨2571638, by rfl⟩ : syracuseStep 3428851 = 5143277) B5143277
theorem B1921963 : Blo 599292 1921963 := bstep (se 1 (by rfl) ⟨1441472, by rfl⟩ : syracuseStep 1921963 = 2882945) B2882945
theorem B24728615 : Blo 599292 24728615 := bstep (se 1 (by rfl) ⟨18546461, by rfl⟩ : syracuseStep 24728615 = 37092923) B37092923
theorem B6870095 : Blo 599292 6870095 := bstep (se 1 (by rfl) ⟨5152571, by rfl⟩ : syracuseStep 6870095 = 10305143) B10305143
theorem B7328987 : Blo 599292 7328987 := bstep (se 1 (by rfl) ⟨5496740, by rfl⟩ : syracuseStep 7328987 = 10993481) B10993481
theorem B2282849 : Blo 599292 2282849 := bstep (se 2 (by rfl) ⟨856068, by rfl⟩ : syracuseStep 2282849 = 1712137) B1712137
theorem B677695 : Blo 599292 677695 := bstep (se 1 (by rfl) ⟨508271, by rfl⟩ : syracuseStep 677695 = 1016543) B1016543
theorem B677983 : Blo 599292 677983 := bstep (se 1 (by rfl) ⟨508487, by rfl⟩ : syracuseStep 677983 = 1016975) B1016975
theorem B5134529 : Blo 599292 5134529 := bstep (se 2 (by rfl) ⟨1925448, by rfl⟩ : syracuseStep 5134529 = 3850897) B3850897
theorem B1629011 : Blo 599292 1629011 := bstep (se 1 (by rfl) ⟨1221758, by rfl⟩ : syracuseStep 1629011 = 2443517) B2443517
theorem B2350205 : Blo 599292 2350205 := bstep (se 3 (by rfl) ⟨440663, by rfl⟩ : syracuseStep 2350205 = 881327) B881327
theorem B1629551 : Blo 599292 1629551 := bstep (se 1 (by rfl) ⟨1222163, by rfl⟩ : syracuseStep 1629551 = 2444327) B2444327
theorem B1957331 : Blo 599292 1957331 := bstep (se 1 (by rfl) ⟨1467998, by rfl⟩ : syracuseStep 1957331 = 2935997) B2935997
theorem B1138151 : Blo 599292 1138151 := bstep (se 1 (by rfl) ⟨853613, by rfl⟩ : syracuseStep 1138151 = 1707227) B1707227
theorem B2023055 : Blo 599292 2023055 := bstep (se 1 (by rfl) ⟨1517291, by rfl⟩ : syracuseStep 2023055 = 3034583) B3034583
theorem B15621983 : Blo 599292 15621983 := bstep (se 1 (by rfl) ⟨11716487, by rfl⟩ : syracuseStep 15621983 = 23432975) B23432975
theorem B4382693 : Blo 599292 4382693 := bstep (se 4 (by rfl) ⟨410877, by rfl⟩ : syracuseStep 4382693 = 821755) B821755
theorem B1630439 : Blo 599292 1630439 := bstep (se 1 (by rfl) ⟨1222829, by rfl⟩ : syracuseStep 1630439 = 2445659) B2445659
theorem B4874573 : Blo 599292 4874573 := bstep (se 3 (by rfl) ⟨913982, by rfl⟩ : syracuseStep 4874573 = 1827965) B1827965
theorem B1139177 : Blo 599292 1139177 := bstep (se 2 (by rfl) ⟨427191, by rfl⟩ : syracuseStep 1139177 = 854383) B854383
theorem B2024189 : Blo 599292 2024189 := bstep (se 3 (by rfl) ⟨379535, by rfl⟩ : syracuseStep 2024189 = 759071) B759071
theorem B1139503 : Blo 599292 1139503 := bstep (se 1 (by rfl) ⟨854627, by rfl⟩ : syracuseStep 1139503 = 1709255) B1709255
theorem B2746075 : Blo 599292 2746075 := bstep (se 1 (by rfl) ⟨2059556, by rfl⟩ : syracuseStep 2746075 = 4119113) B4119113
theorem B3041225 : Blo 599292 3041225 := bstep (se 2 (by rfl) ⟨1140459, by rfl⟩ : syracuseStep 3041225 = 2280919) B2280919
theorem B3565601 : Blo 599292 3565601 := bstep (se 2 (by rfl) ⟨1337100, by rfl⟩ : syracuseStep 3565601 = 2674201) B2674201
theorem B10283273 : Blo 599292 10283273 := bstep (se 2 (by rfl) ⟨3856227, by rfl⟩ : syracuseStep 10283273 = 7712455) B7712455
theorem B813359 : Blo 599292 813359 := bstep (se 1 (by rfl) ⟨610019, by rfl⟩ : syracuseStep 813359 = 1220039) B1220039
theorem B10971449 : Blo 599292 10971449 := bstep (se 2 (by rfl) ⟨4114293, by rfl⟩ : syracuseStep 10971449 = 8228587) B8228587
theorem B2026295 : Blo 599292 2026295 := bstep (se 1 (by rfl) ⟨1519721, by rfl⟩ : syracuseStep 2026295 = 3039443) B3039443
theorem B3435527 : Blo 599292 3435527 := bstep (se 1 (by rfl) ⟨2576645, by rfl⟩ : syracuseStep 3435527 = 5153291) B5153291
theorem B3435641 : Blo 599292 3435641 := bstep (se 2 (by rfl) ⟨1288365, by rfl⟩ : syracuseStep 3435641 = 2576731) B2576731
theorem B1011433 : Blo 599292 1011433 := bstep (se 2 (by rfl) ⟨379287, by rfl⟩ : syracuseStep 1011433 = 758575) B758575
theorem B3862379 : Blo 599292 3862379 := bstep (se 1 (by rfl) ⟨2896784, by rfl⟩ : syracuseStep 3862379 = 5793569) B5793569
theorem B1929167 : Blo 599292 1929167 := bstep (se 1 (by rfl) ⟨1446875, by rfl⟩ : syracuseStep 1929167 = 2893751) B2893751
theorem B1011899 : Blo 599292 1011899 := bstep (se 1 (by rfl) ⟨758924, by rfl⟩ : syracuseStep 1011899 = 1517849) B1517849
theorem B1143391 : Blo 599292 1143391 := bstep (se 1 (by rfl) ⟨857543, by rfl⟩ : syracuseStep 1143391 = 1715087) B1715087
theorem B4551389 : Blo 599292 4551389 := bstep (se 3 (by rfl) ⟨853385, by rfl⟩ : syracuseStep 4551389 = 1706771) B1706771
theorem B1012459 : Blo 599292 1012459 := bstep (se 1 (by rfl) ⟨759344, by rfl⟩ : syracuseStep 1012459 = 1518689) B1518689
theorem B2028617 : Blo 599292 2028617 := bstep (se 2 (by rfl) ⟨760731, by rfl⟩ : syracuseStep 2028617 = 1521463) B1521463
theorem B1143983 : Blo 599292 1143983 := bstep (se 1 (by rfl) ⟨857987, by rfl⟩ : syracuseStep 1143983 = 1715975) B1715975
theorem B3044627 : Blo 599292 3044627 := bstep (se 1 (by rfl) ⟨2283470, by rfl⟩ : syracuseStep 3044627 = 4566941) B4566941
theorem B1144219 : Blo 599292 1144219 := bstep (se 1 (by rfl) ⟨858164, by rfl⟩ : syracuseStep 1144219 = 1716329) B1716329
theorem B1013431 : Blo 599292 1013431 := bstep (se 1 (by rfl) ⟨760073, by rfl⟩ : syracuseStep 1013431 = 1520147) B1520147
theorem B1013735 : Blo 599292 1013735 := bstep (se 1 (by rfl) ⟨760301, by rfl⟩ : syracuseStep 1013735 = 1520603) B1520603
theorem B3864635 : Blo 599292 3864635 := bstep (se 1 (by rfl) ⟨2898476, by rfl⟩ : syracuseStep 3864635 = 5796953) B5796953
theorem B4552847 : Blo 599292 4552847 := bstep (se 1 (by rfl) ⟨3414635, by rfl⟩ : syracuseStep 4552847 = 6829271) B6829271
theorem B1013951 : Blo 599292 1013951 := bstep (se 1 (by rfl) ⟨760463, by rfl⟩ : syracuseStep 1013951 = 1520927) B1520927
theorem B1931627 : Blo 599292 1931627 := bstep (se 1 (by rfl) ⟨1448720, by rfl⟩ : syracuseStep 1931627 = 2897441) B2897441
theorem B2030237 : Blo 599292 2030237 := bstep (se 3 (by rfl) ⟨380669, by rfl⟩ : syracuseStep 2030237 = 761339) B761339
theorem B1014619 : Blo 599292 1014619 := bstep (se 1 (by rfl) ⟨760964, by rfl⟩ : syracuseStep 1014619 = 1521929) B1521929
theorem B7699333 : Blo 599292 7699333 := bstep (se 4 (by rfl) ⟨721812, by rfl⟩ : syracuseStep 7699333 = 1443625) B1443625
theorem B2030561 : Blo 599292 2030561 := bstep (se 2 (by rfl) ⟨761460, by rfl⟩ : syracuseStep 2030561 = 1522921) B1522921
theorem B8682511 : Blo 599292 8682511 := bstep (se 1 (by rfl) ⟨6511883, by rfl⟩ : syracuseStep 8682511 = 13023767) B13023767
theorem B2030777 : Blo 599292 2030777 := bstep (se 2 (by rfl) ⟨761541, by rfl⟩ : syracuseStep 2030777 = 1523083) B1523083
theorem B10976543 : Blo 599292 10976543 := bstep (se 1 (by rfl) ⟨8232407, by rfl⟩ : syracuseStep 10976543 = 16464815) B16464815
theorem B3472679 : Blo 599292 3472679 := bstep (se 1 (by rfl) ⟨2604509, by rfl⟩ : syracuseStep 3472679 = 5209019) B5209019
theorem B3898853 : Blo 599292 3898853 := bstep (se 4 (by rfl) ⟨365517, by rfl⟩ : syracuseStep 3898853 = 731035) B731035
theorem B6848225 : Blo 599292 6848225 := bstep (se 2 (by rfl) ⟨2568084, by rfl⟩ : syracuseStep 6848225 = 5136169) B5136169
theorem B1015591 : Blo 599292 1015591 := bstep (se 1 (by rfl) ⟨761693, by rfl⟩ : syracuseStep 1015591 = 1523387) B1523387
theorem B2031803 : Blo 599292 2031803 := bstep (se 1 (by rfl) ⟨1523852, by rfl⟩ : syracuseStep 2031803 = 3047705) B3047705
theorem B1016111 : Blo 599292 1016111 := bstep (se 1 (by rfl) ⟨762083, by rfl⟩ : syracuseStep 1016111 = 1524167) B1524167
theorem B2884175 : Blo 599292 2884175 := bstep (se 1 (by rfl) ⟨2163131, by rfl⟩ : syracuseStep 2884175 = 4326263) B4326263
theorem B722255 : Blo 599292 722255 := bstep (se 1 (by rfl) ⟨541691, by rfl⟩ : syracuseStep 722255 = 1083383) B1083383
theorem B1017407 : Blo 599292 1017407 := bstep (se 1 (by rfl) ⟨763055, by rfl⟩ : syracuseStep 1017407 = 1526111) B1526111
theorem B1017535 : Blo 599292 1017535 := bstep (se 1 (by rfl) ⟨763151, by rfl⟩ : syracuseStep 1017535 = 1526303) B1526303
theorem B4327937 : Blo 599292 4327937 := bstep (se 2 (by rfl) ⟨1622976, by rfl⟩ : syracuseStep 4327937 = 3245953) B3245953
theorem B4328569 : Blo 599292 4328569 := bstep (se 2 (by rfl) ⟨1623213, by rfl⟩ : syracuseStep 4328569 = 3246427) B3246427
theorem B3050621 : Blo 599292 3050621 := bstep (se 3 (by rfl) ⟨571991, by rfl⟩ : syracuseStep 3050621 = 1143983) B1143983
theorem B16485743 : Blo 599292 16485743 := bstep (se 1 (by rfl) ⟨12364307, by rfl⟩ : syracuseStep 16485743 = 24728615) B24728615
theorem B4885991 : Blo 599292 4885991 := bstep (se 1 (by rfl) ⟨3664493, by rfl⟩ : syracuseStep 4885991 = 7328987) B7328987
theorem B1707763 : Blo 599292 1707763 := bstep (se 1 (by rfl) ⟨1280822, by rfl⟩ : syracuseStep 1707763 = 2561645) B2561645
theorem B2560567 : Blo 599292 2560567 := bstep (se 1 (by rfl) ⟨1920425, by rfl⟩ : syracuseStep 2560567 = 3840851) B3840851
theorem B1086007 : Blo 599292 1086007 := bstep (se 1 (by rfl) ⟨814505, by rfl⟩ : syracuseStep 1086007 = 1629011) B1629011
theorem B1282873 : Blo 599292 1282873 := bstep (se 2 (by rfl) ⟨481077, by rfl⟩ : syracuseStep 1282873 = 962155) B962155
theorem B1086367 : Blo 599292 1086367 := bstep (se 1 (by rfl) ⟨814775, by rfl⟩ : syracuseStep 1086367 = 1629551) B1629551
theorem B1348577 : Blo 599292 1348577 := bstep (se 2 (by rfl) ⟨505716, by rfl⟩ : syracuseStep 1348577 = 1011433) B1011433
theorem B1709039 : Blo 599292 1709039 := bstep (se 1 (by rfl) ⟨1281779, by rfl⟩ : syracuseStep 1709039 = 2563559) B2563559
theorem B857071 : Blo 599292 857071 := bstep (se 1 (by rfl) ⟨642803, by rfl⟩ : syracuseStep 857071 = 1285607) B1285607
theorem B1348703 : Blo 599292 1348703 := bstep (se 1 (by rfl) ⟨1011527, by rfl⟩ : syracuseStep 1348703 = 2023055) B2023055
theorem B2921795 : Blo 599292 2921795 := bstep (se 1 (by rfl) ⟨2191346, by rfl⟩ : syracuseStep 2921795 = 4382693) B4382693
theorem B1086959 : Blo 599292 1086959 := bstep (se 1 (by rfl) ⟨815219, by rfl⟩ : syracuseStep 1086959 = 1630439) B1630439
theorem B3249715 : Blo 599292 3249715 := bstep (se 1 (by rfl) ⟨2437286, by rfl⟩ : syracuseStep 3249715 = 4874573) B4874573
theorem B2233937 : Blo 599292 2233937 := bstep (se 2 (by rfl) ⟨837726, by rfl⟩ : syracuseStep 2233937 = 1675453) B1675453
theorem B857737 : Blo 599292 857737 := bstep (se 2 (by rfl) ⟨321651, by rfl⟩ : syracuseStep 857737 = 643303) B643303
theorem B759451 : Blo 599292 759451 := bstep (se 1 (by rfl) ⟨569588, by rfl⟩ : syracuseStep 759451 = 1139177) B1139177
theorem B1349459 : Blo 599292 1349459 := bstep (se 1 (by rfl) ⟨1012094, by rfl⟩ : syracuseStep 1349459 = 2024189) B2024189
theorem B1447777 : Blo 599292 1447777 := bstep (se 2 (by rfl) ⟨542916, by rfl⟩ : syracuseStep 1447777 = 1085833) B1085833
theorem B2168957 : Blo 599292 2168957 := bstep (se 3 (by rfl) ⟨406679, by rfl⟩ : syracuseStep 2168957 = 813359) B813359
theorem B1349945 : Blo 599292 1349945 := bstep (se 2 (by rfl) ⟨506229, by rfl⟩ : syracuseStep 1349945 = 1012459) B1012459
theorem B2562617 : Blo 599292 2562617 := bstep (se 2 (by rfl) ⟨960981, by rfl⟩ : syracuseStep 2562617 = 1921963) B1921963
theorem B6855515 : Blo 599292 6855515 := bstep (se 1 (by rfl) ⟨5141636, by rfl⟩ : syracuseStep 6855515 = 10283273) B10283273
theorem B7314299 : Blo 599292 7314299 := bstep (se 1 (by rfl) ⟨5485724, by rfl⟩ : syracuseStep 7314299 = 10971449) B10971449
theorem B5774273 : Blo 599292 5774273 := bstep (se 2 (by rfl) ⟨2165352, by rfl⟩ : syracuseStep 5774273 = 4330705) B4330705
theorem B1350863 : Blo 599292 1350863 := bstep (se 1 (by rfl) ⟨1013147, by rfl⟩ : syracuseStep 1350863 = 2026295) B2026295
theorem B1351241 : Blo 599292 1351241 := bstep (se 2 (by rfl) ⟨506715, by rfl⟩ : syracuseStep 1351241 = 1013431) B1013431
theorem B2891693 : Blo 599292 2891693 := bstep (se 3 (by rfl) ⟨542192, by rfl⟩ : syracuseStep 2891693 = 1084385) B1084385
theorem B1286111 : Blo 599292 1286111 := bstep (se 1 (by rfl) ⟨964583, by rfl⟩ : syracuseStep 1286111 = 1929167) B1929167
theorem B4563053 : Blo 599292 4563053 := bstep (se 3 (by rfl) ⟨855572, by rfl⟩ : syracuseStep 4563053 = 1711145) B1711145
theorem B1352411 : Blo 599292 1352411 := bstep (se 1 (by rfl) ⟨1014308, by rfl⟩ : syracuseStep 1352411 = 2028617) B2028617
theorem B1352825 : Blo 599292 1352825 := bstep (se 2 (by rfl) ⟨507309, by rfl⟩ : syracuseStep 1352825 = 1014619) B1014619
theorem B1287289 : Blo 599292 1287289 := bstep (se 2 (by rfl) ⟨482733, by rfl⟩ : syracuseStep 1287289 = 965467) B965467
theorem B2172071 : Blo 599292 2172071 := bstep (se 1 (by rfl) ⟨1629053, by rfl⟩ : syracuseStep 2172071 = 3258107) B3258107
theorem B10265777 : Blo 599292 10265777 := bstep (se 2 (by rfl) ⟨3849666, by rfl⟩ : syracuseStep 10265777 = 7699333) B7699333
theorem B5219549 : Blo 599292 5219549 := bstep (se 3 (by rfl) ⟨978665, by rfl⟩ : syracuseStep 5219549 = 1957331) B1957331
theorem B599343 : Blo 599292 599343 := bstep (se 1 (by rfl) ⟨449507, by rfl⟩ : syracuseStep 599343 = 899015) B899015
theorem B11576681 : Blo 599292 11576681 := bstep (se 2 (by rfl) ⟨4341255, by rfl⟩ : syracuseStep 11576681 = 8682511) B8682511
theorem B11544079 : Blo 599292 11544079 := bstep (se 1 (by rfl) ⟨8658059, by rfl⟩ : syracuseStep 11544079 = 17316119) B17316119
theorem B599579 : Blo 599292 599579 := bstep (se 1 (by rfl) ⟨449684, by rfl⟩ : syracuseStep 599579 = 899369) B899369
theorem B599583 : Blo 599292 599583 := bstep (se 1 (by rfl) ⟨449687, by rfl⟩ : syracuseStep 599583 = 899375) B899375
theorem B1287751 : Blo 599292 1287751 := bstep (se 1 (by rfl) ⟨965813, by rfl⟩ : syracuseStep 1287751 = 1931627) B1931627
theorem B599743 : Blo 599292 599743 := bstep (se 1 (by rfl) ⟨449807, by rfl⟩ : syracuseStep 599743 = 899615) B899615
theorem B1353491 : Blo 599292 1353491 := bstep (se 1 (by rfl) ⟨1015118, by rfl⟩ : syracuseStep 1353491 = 2030237) B2030237
theorem B599999 : Blo 599292 599999 := bstep (se 1 (by rfl) ⟨449999, by rfl⟩ : syracuseStep 599999 = 899999) B899999
theorem B600031 : Blo 599292 600031 := bstep (se 1 (by rfl) ⟨450023, by rfl⟩ : syracuseStep 600031 = 900047) B900047
theorem B1353707 : Blo 599292 1353707 := bstep (se 1 (by rfl) ⟨1015280, by rfl⟩ : syracuseStep 1353707 = 2030561) B2030561
theorem B600091 : Blo 599292 600091 := bstep (se 1 (by rfl) ⟨450068, by rfl⟩ : syracuseStep 600091 = 900137) B900137
theorem B2566171 : Blo 599292 2566171 := bstep (se 1 (by rfl) ⟨1924628, by rfl⟩ : syracuseStep 2566171 = 3849257) B3849257
theorem B600095 : Blo 599292 600095 := bstep (se 1 (by rfl) ⟨450071, by rfl⟩ : syracuseStep 600095 = 900143) B900143
theorem B600111 : Blo 599292 600111 := bstep (se 1 (by rfl) ⟨450083, by rfl⟩ : syracuseStep 600111 = 900167) B900167
theorem B1353851 : Blo 599292 1353851 := bstep (se 1 (by rfl) ⟨1015388, by rfl⟩ : syracuseStep 1353851 = 2030777) B2030777
theorem B7317695 : Blo 599292 7317695 := bstep (se 1 (by rfl) ⟨5488271, by rfl⟩ : syracuseStep 7317695 = 10976543) B10976543
theorem B600287 : Blo 599292 600287 := bstep (se 1 (by rfl) ⟨450215, by rfl⟩ : syracuseStep 600287 = 900431) B900431
theorem B600347 : Blo 599292 600347 := bstep (se 1 (by rfl) ⟨450260, by rfl⟩ : syracuseStep 600347 = 900521) B900521
theorem B1517879 : Blo 599292 1517879 := bstep (se 1 (by rfl) ⟨1138409, by rfl⟩ : syracuseStep 1517879 = 2276819) B2276819
theorem B2599235 : Blo 599292 2599235 := bstep (se 1 (by rfl) ⟨1949426, by rfl⟩ : syracuseStep 2599235 = 3898853) B3898853
theorem B5843315 : Blo 599292 5843315 := bstep (se 1 (by rfl) ⟨4382486, by rfl⟩ : syracuseStep 5843315 = 8764973) B8764973
theorem B600447 : Blo 599292 600447 := bstep (se 1 (by rfl) ⟨450335, by rfl⟩ : syracuseStep 600447 = 900671) B900671
theorem B1354121 : Blo 599292 1354121 := bstep (se 2 (by rfl) ⟨507795, by rfl⟩ : syracuseStep 1354121 = 1015591) B1015591
theorem B4565483 : Blo 599292 4565483 := bstep (se 1 (by rfl) ⟨3424112, by rfl⟩ : syracuseStep 4565483 = 6848225) B6848225
theorem B600623 : Blo 599292 600623 := bstep (se 1 (by rfl) ⟨450467, by rfl⟩ : syracuseStep 600623 = 900935) B900935
theorem B1714745 : Blo 599292 1714745 := bstep (se 2 (by rfl) ⟨643029, by rfl⟩ : syracuseStep 1714745 = 1286059) B1286059
theorem B600679 : Blo 599292 600679 := bstep (se 1 (by rfl) ⟨450509, by rfl⟩ : syracuseStep 600679 = 901019) B901019
theorem B8235695 : Blo 599292 8235695 := bstep (se 1 (by rfl) ⟨6176771, by rfl⟩ : syracuseStep 8235695 = 12353543) B12353543
theorem B601055 : Blo 599292 601055 := bstep (se 1 (by rfl) ⟨450791, by rfl⟩ : syracuseStep 601055 = 901583) B901583
theorem B601083 : Blo 599292 601083 := bstep (se 1 (by rfl) ⟨450812, by rfl⟩ : syracuseStep 601083 = 901625) B901625
theorem B601151 : Blo 599292 601151 := bstep (se 1 (by rfl) ⟨450863, by rfl⟩ : syracuseStep 601151 = 901727) B901727
theorem B1354823 : Blo 599292 1354823 := bstep (se 1 (by rfl) ⟨1016117, by rfl⟩ : syracuseStep 1354823 = 2032235) B2032235
theorem B3648635 : Blo 599292 3648635 := bstep (se 1 (by rfl) ⟨2736476, by rfl⟩ : syracuseStep 3648635 = 5472953) B5472953
theorem B5123321 : Blo 599292 5123321 := bstep (se 2 (by rfl) ⟨1921245, by rfl⟩ : syracuseStep 5123321 = 3842491) B3842491
theorem B601471 : Blo 599292 601471 := bstep (se 1 (by rfl) ⟨451103, by rfl⟩ : syracuseStep 601471 = 902207) B902207
theorem B601499 : Blo 599292 601499 := bstep (se 1 (by rfl) ⟨451124, by rfl⟩ : syracuseStep 601499 = 902249) B902249
theorem B1355219 : Blo 599292 1355219 := bstep (se 1 (by rfl) ⟨1016414, by rfl⟩ : syracuseStep 1355219 = 2032829) B2032829
theorem B601567 : Blo 599292 601567 := bstep (se 1 (by rfl) ⟨451175, by rfl⟩ : syracuseStep 601567 = 902351) B902351
theorem B601703 : Blo 599292 601703 := bstep (se 1 (by rfl) ⟨451277, by rfl⟩ : syracuseStep 601703 = 902555) B902555
theorem B1355489 : Blo 599292 1355489 := bstep (se 2 (by rfl) ⟨508308, by rfl⟩ : syracuseStep 1355489 = 1016617) B1016617
theorem B1519337 : Blo 599292 1519337 := bstep (se 2 (by rfl) ⟨569751, by rfl⟩ : syracuseStep 1519337 = 1139503) B1139503
theorem B601851 : Blo 599292 601851 := bstep (se 1 (by rfl) ⟨451388, by rfl⟩ : syracuseStep 601851 = 902777) B902777
theorem B601919 : Blo 599292 601919 := bstep (se 1 (by rfl) ⟨451439, by rfl⟩ : syracuseStep 601919 = 902879) B902879
theorem B601983 : Blo 599292 601983 := bstep (se 1 (by rfl) ⟨451487, by rfl⟩ : syracuseStep 601983 = 902975) B902975
theorem B5484449 : Blo 599292 5484449 := bstep (se 2 (by rfl) ⟨2056668, by rfl⟩ : syracuseStep 5484449 = 4113337) B4113337
theorem B602095 : Blo 599292 602095 := bstep (se 1 (by rfl) ⟨451571, by rfl⟩ : syracuseStep 602095 = 903143) B903143
theorem B602107 : Blo 599292 602107 := bstep (se 1 (by rfl) ⟨451580, by rfl⟩ : syracuseStep 602107 = 903161) B903161
theorem B602175 : Blo 599292 602175 := bstep (se 1 (by rfl) ⟨451631, by rfl⟩ : syracuseStep 602175 = 903263) B903263
theorem B1355849 : Blo 599292 1355849 := bstep (se 2 (by rfl) ⟨508443, by rfl⟩ : syracuseStep 1355849 = 1016887) B1016887
theorem B3911759 : Blo 599292 3911759 := bstep (se 1 (by rfl) ⟨2933819, by rfl⟩ : syracuseStep 3911759 = 5867639) B5867639
theorem B602215 : Blo 599292 602215 := bstep (se 1 (by rfl) ⟨451661, by rfl⟩ : syracuseStep 602215 = 903323) B903323
theorem B962687 : Blo 599292 962687 := bstep (se 1 (by rfl) ⟨722015, by rfl⟩ : syracuseStep 962687 = 1444031) B1444031
theorem B602239 : Blo 599292 602239 := bstep (se 1 (by rfl) ⟨451679, by rfl⟩ : syracuseStep 602239 = 903359) B903359
theorem B1355903 : Blo 599292 1355903 := bstep (se 1 (by rfl) ⟨1016927, by rfl⟩ : syracuseStep 1355903 = 2033855) B2033855
theorem B602267 : Blo 599292 602267 := bstep (se 1 (by rfl) ⟨451700, by rfl⟩ : syracuseStep 602267 = 903401) B903401
theorem B4108519 : Blo 599292 4108519 := bstep (se 1 (by rfl) ⟨3081389, by rfl⟩ : syracuseStep 4108519 = 6162779) B6162779
theorem B602471 : Blo 599292 602471 := bstep (se 1 (by rfl) ⟨451853, by rfl⟩ : syracuseStep 602471 = 903707) B903707
theorem B602523 : Blo 599292 602523 := bstep (se 1 (by rfl) ⟨451892, by rfl⟩ : syracuseStep 602523 = 903785) B903785
theorem B3846851 : Blo 599292 3846851 := bstep (se 1 (by rfl) ⟨2885138, by rfl⟩ : syracuseStep 3846851 = 5770277) B5770277
theorem B23147207 : Blo 599292 23147207 := bstep (se 1 (by rfl) ⟨17360405, by rfl⟩ : syracuseStep 23147207 = 34720811) B34720811
theorem B602875 : Blo 599292 602875 := bstep (se 1 (by rfl) ⟨452156, by rfl⟩ : syracuseStep 602875 = 904313) B904313
theorem B602943 : Blo 599292 602943 := bstep (se 1 (by rfl) ⟨452207, by rfl⟩ : syracuseStep 602943 = 904415) B904415
theorem B8926027 : Blo 599292 8926027 := bstep (se 1 (by rfl) ⟨6694520, by rfl⟩ : syracuseStep 8926027 = 13389041) B13389041
theorem B602971 : Blo 599292 602971 := bstep (se 1 (by rfl) ⟨452228, by rfl⟩ : syracuseStep 602971 = 904457) B904457
theorem B37106545 : Blo 599292 37106545 := bstep (se 2 (by rfl) ⟨13914954, by rfl⟩ : syracuseStep 37106545 = 27829909) B27829909
theorem B603039 : Blo 599292 603039 := bstep (se 1 (by rfl) ⟨452279, by rfl⟩ : syracuseStep 603039 = 904559) B904559
theorem B5125031 : Blo 599292 5125031 := bstep (se 1 (by rfl) ⟨3843773, by rfl⟩ : syracuseStep 5125031 = 7687547) B7687547
theorem B603119 : Blo 599292 603119 := bstep (se 1 (by rfl) ⟨452339, by rfl⟩ : syracuseStep 603119 = 904679) B904679
theorem B603207 : Blo 599292 603207 := bstep (se 1 (by rfl) ⟨452405, by rfl⟩ : syracuseStep 603207 = 904811) B904811
theorem B603291 : Blo 599292 603291 := bstep (se 1 (by rfl) ⟨452468, by rfl⟩ : syracuseStep 603291 = 904937) B904937
theorem B1356983 : Blo 599292 1356983 := bstep (se 1 (by rfl) ⟨1017737, by rfl⟩ : syracuseStep 1356983 = 2035475) B2035475
theorem B5551325 : Blo 599292 5551325 := bstep (se 3 (by rfl) ⟨1040873, by rfl⟩ : syracuseStep 5551325 = 2081747) B2081747
theorem B3847823 : Blo 599292 3847823 := bstep (se 1 (by rfl) ⟨2885867, by rfl⟩ : syracuseStep 3847823 = 5771735) B5771735
theorem B899255 : Blo 599292 899255 := bstep (se 1 (by rfl) ⟨674441, by rfl⟩ : syracuseStep 899255 = 1348883) B1348883
theorem B2275559 : Blo 599292 2275559 := bstep (se 1 (by rfl) ⟨1706669, by rfl⟩ : syracuseStep 2275559 = 3413339) B3413339
theorem B899303 : Blo 599292 899303 := bstep (se 1 (by rfl) ⟨674477, by rfl⟩ : syracuseStep 899303 = 1348955) B1348955
theorem B1521899 : Blo 599292 1521899 := bstep (se 1 (by rfl) ⟨1141424, by rfl⟩ : syracuseStep 1521899 = 2282849) B2282849
theorem B2275847 : Blo 599292 2275847 := bstep (se 1 (by rfl) ⟨1706885, by rfl⟩ : syracuseStep 2275847 = 3413771) B3413771
theorem B899675 : Blo 599292 899675 := bstep (se 1 (by rfl) ⟨674756, by rfl⟩ : syracuseStep 899675 = 1349513) B1349513
theorem B899819 : Blo 599292 899819 := bstep (se 1 (by rfl) ⟨674864, by rfl⟩ : syracuseStep 899819 = 1349729) B1349729
theorem B899849 : Blo 599292 899849 := bstep (se 2 (by rfl) ⟨337443, by rfl⟩ : syracuseStep 899849 = 674887) B674887
theorem B3423019 : Blo 599292 3423019 := bstep (se 1 (by rfl) ⟨2567264, by rfl⟩ : syracuseStep 3423019 = 5134529) B5134529
theorem B2276333 : Blo 599292 2276333 := bstep (se 3 (by rfl) ⟨426812, by rfl⟩ : syracuseStep 2276333 = 853625) B853625
theorem B900719 : Blo 599292 900719 := bstep (se 1 (by rfl) ⟨675539, by rfl⟩ : syracuseStep 900719 = 1351079) B1351079
theorem B4505311 : Blo 599292 4505311 := bstep (se 1 (by rfl) ⟨3378983, by rfl⟩ : syracuseStep 4505311 = 6757967) B6757967
theorem B900839 : Blo 599292 900839 := bstep (se 1 (by rfl) ⟨675629, by rfl⟩ : syracuseStep 900839 = 1351259) B1351259
theorem B3653399 : Blo 599292 3653399 := bstep (se 1 (by rfl) ⟨2740049, by rfl⟩ : syracuseStep 3653399 = 5480099) B5480099
theorem B901031 : Blo 599292 901031 := bstep (se 1 (by rfl) ⟨675773, by rfl⟩ : syracuseStep 901031 = 1351547) B1351547
theorem B3424477 : Blo 599292 3424477 := bstep (se 3 (by rfl) ⟨642089, by rfl⟩ : syracuseStep 3424477 = 1284179) B1284179
theorem B901355 : Blo 599292 901355 := bstep (se 1 (by rfl) ⟨676016, by rfl⟩ : syracuseStep 901355 = 1352033) B1352033
theorem B3850487 : Blo 599292 3850487 := bstep (se 1 (by rfl) ⟨2887865, by rfl⟩ : syracuseStep 3850487 = 5775731) B5775731
theorem B901415 : Blo 599292 901415 := bstep (se 1 (by rfl) ⟨676061, by rfl⟩ : syracuseStep 901415 = 1352123) B1352123
theorem B2278003 : Blo 599292 2278003 := bstep (se 1 (by rfl) ⟨1708502, by rfl⟩ : syracuseStep 2278003 = 3417005) B3417005
theorem B4571801 : Blo 599292 4571801 := bstep (se 2 (by rfl) ⟨1714425, by rfl⟩ : syracuseStep 4571801 = 3428851) B3428851
theorem B1524521 : Blo 599292 1524521 := bstep (se 2 (by rfl) ⟨571695, by rfl⟩ : syracuseStep 1524521 = 1143391) B1143391
theorem B902087 : Blo 599292 902087 := bstep (se 1 (by rfl) ⟨676565, by rfl⟩ : syracuseStep 902087 = 1353131) B1353131
theorem B902255 : Blo 599292 902255 := bstep (se 1 (by rfl) ⟨676691, by rfl⟩ : syracuseStep 902255 = 1353383) B1353383
theorem B902447 : Blo 599292 902447 := bstep (se 1 (by rfl) ⟨676835, by rfl⟩ : syracuseStep 902447 = 1353671) B1353671
theorem B2278763 : Blo 599292 2278763 := bstep (se 1 (by rfl) ⟨1709072, by rfl⟩ : syracuseStep 2278763 = 3418145) B3418145
theorem B2377067 : Blo 599292 2377067 := bstep (se 1 (by rfl) ⟨1782800, by rfl⟩ : syracuseStep 2377067 = 3565601) B3565601
theorem B2278793 : Blo 599292 2278793 := bstep (se 2 (by rfl) ⟨854547, by rfl⟩ : syracuseStep 2278793 = 1709095) B1709095
theorem B902651 : Blo 599292 902651 := bstep (se 1 (by rfl) ⟨676988, by rfl⟩ : syracuseStep 902651 = 1353977) B1353977
theorem B902687 : Blo 599292 902687 := bstep (se 1 (by rfl) ⟨677015, by rfl⟩ : syracuseStep 902687 = 1354031) B1354031
theorem B2278975 : Blo 599292 2278975 := bstep (se 1 (by rfl) ⟨1709231, by rfl⟩ : syracuseStep 2278975 = 3418463) B3418463
theorem B902831 : Blo 599292 902831 := bstep (se 1 (by rfl) ⟨677123, by rfl⟩ : syracuseStep 902831 = 1354247) B1354247
theorem B10274525 : Blo 599292 10274525 := bstep (se 3 (by rfl) ⟨1926473, by rfl⟩ : syracuseStep 10274525 = 3852947) B3852947
theorem B902951 : Blo 599292 902951 := bstep (se 1 (by rfl) ⟨677213, by rfl⟩ : syracuseStep 902951 = 1354427) B1354427
theorem B1525625 : Blo 599292 1525625 := bstep (se 2 (by rfl) ⟨572109, by rfl⟩ : syracuseStep 1525625 = 1144219) B1144219
theorem B903503 : Blo 599292 903503 := bstep (se 1 (by rfl) ⟨677627, by rfl⟩ : syracuseStep 903503 = 1355255) B1355255
theorem B903551 : Blo 599292 903551 := bstep (se 1 (by rfl) ⟨677663, by rfl⟩ : syracuseStep 903551 = 1355327) B1355327
theorem B903593 : Blo 599292 903593 := bstep (se 2 (by rfl) ⟨338847, by rfl⟩ : syracuseStep 903593 = 677695) B677695
theorem B2574919 : Blo 599292 2574919 := bstep (se 1 (by rfl) ⟨1931189, by rfl⟩ : syracuseStep 2574919 = 3862379) B3862379
theorem B674599 : Blo 599292 674599 := bstep (se 1 (by rfl) ⟨505949, by rfl⟩ : syracuseStep 674599 = 1011899) B1011899
theorem B903977 : Blo 599292 903977 := bstep (se 2 (by rfl) ⟨338991, by rfl⟩ : syracuseStep 903977 = 677983) B677983
theorem B904187 : Blo 599292 904187 := bstep (se 1 (by rfl) ⟨678140, by rfl⟩ : syracuseStep 904187 = 1356281) B1356281
theorem B904247 : Blo 599292 904247 := bstep (se 1 (by rfl) ⟨678185, by rfl⟩ : syracuseStep 904247 = 1356371) B1356371
theorem B3034259 : Blo 599292 3034259 := bstep (se 1 (by rfl) ⟨2275694, by rfl⟩ : syracuseStep 3034259 = 4551389) B4551389
theorem B904367 : Blo 599292 904367 := bstep (se 1 (by rfl) ⟨678275, by rfl⟩ : syracuseStep 904367 = 1356551) B1356551
theorem B9260477 : Blo 599292 9260477 := bstep (se 3 (by rfl) ⟨1736339, by rfl⟩ : syracuseStep 9260477 = 3472679) B3472679
theorem B6868637 : Blo 599292 6868637 := bstep (se 3 (by rfl) ⟨1287869, by rfl⟩ : syracuseStep 6868637 = 2575739) B2575739
theorem B3035069 : Blo 599292 3035069 := bstep (se 3 (by rfl) ⟨569075, by rfl⟩ : syracuseStep 3035069 = 1138151) B1138151
theorem B2281405 : Blo 599292 2281405 := bstep (se 3 (by rfl) ⟨427763, by rfl⟩ : syracuseStep 2281405 = 855527) B855527
theorem B675823 : Blo 599292 675823 := bstep (se 1 (by rfl) ⟨506867, by rfl⟩ : syracuseStep 675823 = 1013735) B1013735
theorem B2576423 : Blo 599292 2576423 := bstep (se 1 (by rfl) ⟨1932317, by rfl⟩ : syracuseStep 2576423 = 3864635) B3864635
theorem B3035231 : Blo 599292 3035231 := bstep (se 1 (by rfl) ⟨2276423, by rfl⟩ : syracuseStep 3035231 = 4552847) B4552847
theorem B675967 : Blo 599292 675967 := bstep (se 1 (by rfl) ⟨506975, by rfl⟩ : syracuseStep 675967 = 1013951) B1013951
theorem B2576765 : Blo 599292 2576765 := bstep (se 3 (by rfl) ⟨483143, by rfl⟩ : syracuseStep 2576765 = 966287) B966287
theorem B11523167 : Blo 599292 11523167 := bstep (se 1 (by rfl) ⟨8642375, by rfl⟩ : syracuseStep 11523167 = 17284751) B17284751
theorem B2282651 : Blo 599292 2282651 := bstep (se 1 (by rfl) ⟨1711988, by rfl⟩ : syracuseStep 2282651 = 3423977) B3423977
theorem B3855613 : Blo 599292 3855613 := bstep (se 3 (by rfl) ⟨722927, by rfl⟩ : syracuseStep 3855613 = 1445855) B1445855
theorem B7918991 : Blo 599292 7918991 := bstep (se 1 (by rfl) ⟨5939243, by rfl⟩ : syracuseStep 7918991 = 11878487) B11878487
theorem B2283335 : Blo 599292 2283335 := bstep (se 1 (by rfl) ⟨1712501, by rfl⟩ : syracuseStep 2283335 = 3425003) B3425003
theorem B1923041 : Blo 599292 1923041 := bstep (se 2 (by rfl) ⟨721140, by rfl⟩ : syracuseStep 1923041 = 1442281) B1442281
theorem B678559 : Blo 599292 678559 := bstep (se 1 (by rfl) ⟨508919, by rfl⟩ : syracuseStep 678559 = 1017839) B1017839
theorem B4578119 : Blo 599292 4578119 := bstep (se 1 (by rfl) ⟨3433589, by rfl⟩ : syracuseStep 4578119 = 6867179) B6867179
theorem B169335755 : Blo 599292 169335755 := bstep (se 1 (by rfl) ⟨127001816, by rfl⟩ : syracuseStep 169335755 = 254003633) B254003633
theorem B3661433 : Blo 599292 3661433 := bstep (se 2 (by rfl) ⟨1373037, by rfl⟩ : syracuseStep 3661433 = 2746075) B2746075
theorem B4218493 : Blo 599292 4218493 := bstep (se 3 (by rfl) ⟨790967, by rfl⟩ : syracuseStep 4218493 = 1581935) B1581935
theorem B4120475 : Blo 599292 4120475 := bstep (se 1 (by rfl) ⟨3090356, by rfl⟩ : syracuseStep 4120475 = 6180713) B6180713
theorem B5136443 : Blo 599292 5136443 := bstep (se 1 (by rfl) ⟨3852332, by rfl⟩ : syracuseStep 5136443 = 7704665) B7704665
theorem B7692569 : Blo 599292 7692569 := bstep (se 2 (by rfl) ⟨2884713, by rfl⟩ : syracuseStep 7692569 = 5769427) B5769427
theorem B4580063 : Blo 599292 4580063 := bstep (se 1 (by rfl) ⟨3435047, by rfl⟩ : syracuseStep 4580063 = 6870095) B6870095
theorem B1140475 : Blo 599292 1140475 := bstep (se 1 (by rfl) ⟨855356, by rfl⟩ : syracuseStep 1140475 = 1710713) B1710713
theorem B1140635 : Blo 599292 1140635 := bstep (se 1 (by rfl) ⟨855476, by rfl⟩ : syracuseStep 1140635 = 1710953) B1710953
theorem B1566803 : Blo 599292 1566803 := bstep (se 1 (by rfl) ⟨1175102, by rfl⟩ : syracuseStep 1566803 = 2350205) B2350205
theorem B1370209 : Blo 599292 1370209 := bstep (se 2 (by rfl) ⟨513828, by rfl⟩ : syracuseStep 1370209 = 1027657) B1027657
theorem B10414655 : Blo 599292 10414655 := bstep (se 1 (by rfl) ⟨7810991, by rfl⟩ : syracuseStep 10414655 = 15621983) B15621983
theorem B4615337 : Blo 599292 4615337 := bstep (se 2 (by rfl) ⟨1730751, by rfl⟩ : syracuseStep 4615337 = 3461503) B3461503
theorem B2026781 : Blo 599292 2026781 := bstep (se 3 (by rfl) ⟨380021, by rfl⟩ : syracuseStep 2026781 = 760043) B760043
theorem B2027483 : Blo 599292 2027483 := bstep (se 1 (by rfl) ⟨1520612, by rfl⟩ : syracuseStep 2027483 = 3041225) B3041225
theorem B5796029 : Blo 599292 5796029 := bstep (se 3 (by rfl) ⟨1086755, by rfl⟩ : syracuseStep 5796029 = 2173511) B2173511
theorem B2027753 : Blo 599292 2027753 := bstep (se 2 (by rfl) ⟨760407, by rfl⟩ : syracuseStep 2027753 = 1520815) B1520815
theorem B1143247 : Blo 599292 1143247 := bstep (se 1 (by rfl) ⟨857435, by rfl⟩ : syracuseStep 1143247 = 1714871) B1714871
theorem B2290351 : Blo 599292 2290351 := bstep (se 1 (by rfl) ⟨1717763, by rfl⟩ : syracuseStep 2290351 = 3435527) B3435527
theorem B2290427 : Blo 599292 2290427 := bstep (se 1 (by rfl) ⟨1717820, by rfl⟩ : syracuseStep 2290427 = 3435641) B3435641
theorem B1012729 : Blo 599292 1012729 := bstep (se 2 (by rfl) ⟨379773, by rfl⟩ : syracuseStep 1012729 = 759547) B759547
theorem B1012999 : Blo 599292 1012999 := bstep (se 1 (by rfl) ⟨759749, by rfl⟩ : syracuseStep 1012999 = 1519499) B1519499
theorem B5141879 : Blo 599292 5141879 := bstep (se 1 (by rfl) ⟨3856409, by rfl⟩ : syracuseStep 5141879 = 7712819) B7712819
theorem B2029373 : Blo 599292 2029373 := bstep (se 3 (by rfl) ⟨380507, by rfl⟩ : syracuseStep 2029373 = 761015) B761015
theorem B1341263 : Blo 599292 1341263 := bstep (se 1 (by rfl) ⟨1005947, by rfl⟩ : syracuseStep 1341263 = 2011895) B2011895
theorem B1931087 : Blo 599292 1931087 := bstep (se 1 (by rfl) ⟨1448315, by rfl⟩ : syracuseStep 1931087 = 2896631) B2896631
theorem B2029751 : Blo 599292 2029751 := bstep (se 1 (by rfl) ⟨1522313, by rfl⟩ : syracuseStep 2029751 = 3044627) B3044627
theorem B6846767 : Blo 599292 6846767 := bstep (se 1 (by rfl) ⟨5135075, by rfl⟩ : syracuseStep 6846767 = 10270151) B10270151
theorem B3242537 : Blo 599292 3242537 := bstep (se 2 (by rfl) ⟨1215951, by rfl⟩ : syracuseStep 3242537 = 2431903) B2431903
theorem B1374761 : Blo 599292 1374761 := bstep (se 2 (by rfl) ⟨515535, by rfl⟩ : syracuseStep 1374761 = 1031071) B1031071
theorem B1538651 : Blo 599292 1538651 := bstep (se 1 (by rfl) ⟨1153988, by rfl⟩ : syracuseStep 1538651 = 2307977) B2307977
theorem B1079951 : Blo 599292 1079951 := bstep (se 1 (by rfl) ⟨809963, by rfl⟩ : syracuseStep 1079951 = 1619927) B1619927
theorem B2030345 : Blo 599292 2030345 := bstep (se 2 (by rfl) ⟨761379, by rfl⟩ : syracuseStep 2030345 = 1522759) B1522759
theorem B1014889 : Blo 599292 1014889 := bstep (se 2 (by rfl) ⟨380583, by rfl⟩ : syracuseStep 1014889 = 761167) B761167
theorem B19758275 : Blo 599292 19758275 := bstep (se 1 (by rfl) ⟨14818706, by rfl⟩ : syracuseStep 19758275 = 29637413) B29637413
theorem B1932511 : Blo 599292 1932511 := bstep (se 1 (by rfl) ⟨1449383, by rfl⟩ : syracuseStep 1932511 = 2898767) B2898767
theorem B1015247 : Blo 599292 1015247 := bstep (se 1 (by rfl) ⟨761435, by rfl⟩ : syracuseStep 1015247 = 1522871) B1522871
theorem B9273041 : Blo 599292 9273041 := bstep (se 2 (by rfl) ⟨3477390, by rfl⟩ : syracuseStep 9273041 = 6954781) B6954781
theorem B3047867 : Blo 599292 3047867 := bstep (se 1 (by rfl) ⟨2285900, by rfl⟩ : syracuseStep 3047867 = 4571801) B4571801
theorem B1016347 : Blo 599292 1016347 := bstep (se 1 (by rfl) ⟨762260, by rfl⟩ : syracuseStep 1016347 = 1524521) B1524521
theorem B6849683 : Blo 599292 6849683 := bstep (se 1 (by rfl) ⟨5137262, by rfl⟩ : syracuseStep 6849683 = 10274525) B10274525
theorem B1017083 : Blo 599292 1017083 := bstep (se 1 (by rfl) ⟨762812, by rfl⟩ : syracuseStep 1017083 = 1525625) B1525625
theorem B2885291 : Blo 599292 2885291 := bstep (se 1 (by rfl) ⟨2163968, by rfl⟩ : syracuseStep 2885291 = 4327937) B4327937
theorem B2033747 : Blo 599292 2033747 := bstep (se 1 (by rfl) ⟨1525310, by rfl⟩ : syracuseStep 2033747 = 3050621) B3050621
theorem B5279327 : Blo 599292 5279327 := bstep (se 1 (by rfl) ⟨3959495, by rfl⟩ : syracuseStep 5279327 = 7918991) B7918991
theorem B724639 : Blo 599292 724639 := bstep (se 1 (by rfl) ⟨543479, by rfl⟩ : syracuseStep 724639 = 1086959) B1086959
theorem B1282027 : Blo 599292 1282027 := bstep (se 1 (by rfl) ⟨961520, by rfl⟩ : syracuseStep 1282027 = 1923041) B1923041
theorem B5771425 : Blo 599292 5771425 := bstep (se 2 (by rfl) ⟨2164284, by rfl⟩ : syracuseStep 5771425 = 4328569) B4328569
theorem B3052079 : Blo 599292 3052079 := bstep (se 1 (by rfl) ⟨2289059, by rfl⟩ : syracuseStep 3052079 = 4578119) B4578119
theorem B112890503 : Blo 599292 112890503 := bstep (se 1 (by rfl) ⟨84667877, by rfl⟩ : syracuseStep 112890503 = 169335755) B169335755
theorem B5149565 : Blo 599292 5149565 := bstep (se 3 (by rfl) ⟨965543, by rfl⟩ : syracuseStep 5149565 = 1931087) B1931087
theorem B857407 : Blo 599292 857407 := bstep (se 1 (by rfl) ⟨643055, by rfl⟩ : syracuseStep 857407 = 1286111) B1286111
theorem B5478025 : Blo 599292 5478025 := bstep (se 2 (by rfl) ⟨2054259, by rfl⟩ : syracuseStep 5478025 = 4108519) B4108519
theorem B3053375 : Blo 599292 3053375 := bstep (se 1 (by rfl) ⟨2290031, by rfl⟩ : syracuseStep 3053375 = 4580063) B4580063
theorem B3414089 : Blo 599292 3414089 := bstep (se 2 (by rfl) ⟨1280283, by rfl⟩ : syracuseStep 3414089 = 2560567) B2560567
theorem B1448009 : Blo 599292 1448009 := bstep (se 2 (by rfl) ⟨543003, by rfl⟩ : syracuseStep 1448009 = 1086007) B1086007
theorem B1448047 : Blo 599292 1448047 := bstep (se 1 (by rfl) ⟨1086035, by rfl⟩ : syracuseStep 1448047 = 2172071) B2172071
theorem B3479699 : Blo 599292 3479699 := bstep (se 1 (by rfl) ⟨2609774, by rfl⟩ : syracuseStep 3479699 = 5219549) B5219549
theorem B3053801 : Blo 599292 3053801 := bstep (se 2 (by rfl) ⟨1145175, by rfl⟩ : syracuseStep 3053801 = 2290351) B2290351
theorem B1710497 : Blo 599292 1710497 := bstep (se 2 (by rfl) ⟨641436, by rfl⟩ : syracuseStep 1710497 = 1282873) B1282873
theorem B1448489 : Blo 599292 1448489 := bstep (se 2 (by rfl) ⟨543183, by rfl⟩ : syracuseStep 1448489 = 1086367) B1086367
theorem B760423 : Blo 599292 760423 := bstep (se 1 (by rfl) ⟨570317, by rfl⟩ : syracuseStep 760423 = 1140635) B1140635
theorem B1350305 : Blo 599292 1350305 := bstep (se 2 (by rfl) ⟨506364, by rfl⟩ : syracuseStep 1350305 = 1012729) B1012729
theorem B1350665 : Blo 599292 1350665 := bstep (se 2 (by rfl) ⟨506499, by rfl⟩ : syracuseStep 1350665 = 1012999) B1012999
theorem B21961853 : Blo 599292 21961853 := bstep (se 3 (by rfl) ⟨4117847, by rfl⟩ : syracuseStep 21961853 = 8235695) B8235695
theorem B4332953 : Blo 599292 4332953 := bstep (se 2 (by rfl) ⟨1624857, by rfl⟩ : syracuseStep 4332953 = 3249715) B3249715
theorem B2432423 : Blo 599292 2432423 := bstep (se 1 (by rfl) ⟨1824317, by rfl⟩ : syracuseStep 2432423 = 3648635) B3648635
theorem B3415547 : Blo 599292 3415547 := bstep (se 1 (by rfl) ⟨2561660, by rfl⟩ : syracuseStep 3415547 = 5123321) B5123321
theorem B1351187 : Blo 599292 1351187 := bstep (se 1 (by rfl) ⟨1013390, by rfl⟩ : syracuseStep 1351187 = 2026781) B2026781
theorem B1351655 : Blo 599292 1351655 := bstep (se 1 (by rfl) ⟨1013741, by rfl⟩ : syracuseStep 1351655 = 2027483) B2027483
theorem B1351835 : Blo 599292 1351835 := bstep (se 1 (by rfl) ⟨1013876, by rfl⟩ : syracuseStep 1351835 = 2027753) B2027753
theorem B2564567 : Blo 599292 2564567 := bstep (se 1 (by rfl) ⟨1923425, by rfl⟩ : syracuseStep 2564567 = 3846851) B3846851
theorem B3416687 : Blo 599292 3416687 := bstep (se 1 (by rfl) ⟨2562515, by rfl⟩ : syracuseStep 3416687 = 5125031) B5125031
theorem B4564025 : Blo 599292 4564025 := bstep (se 2 (by rfl) ⟨1711509, by rfl⟩ : syracuseStep 4564025 = 3423019) B3423019
theorem B2565215 : Blo 599292 2565215 := bstep (se 1 (by rfl) ⟨1923911, by rfl⟩ : syracuseStep 2565215 = 3847823) B3847823
theorem B1352915 : Blo 599292 1352915 := bstep (se 1 (by rfl) ⟨1014686, by rfl⟩ : syracuseStep 1352915 = 2029373) B2029373
theorem B894175 : Blo 599292 894175 := bstep (se 1 (by rfl) ⟨670631, by rfl⟩ : syracuseStep 894175 = 1341263) B1341263
theorem B599503 : Blo 599292 599503 := bstep (se 1 (by rfl) ⟨449627, by rfl⟩ : syracuseStep 599503 = 899255) B899255
theorem B1353167 : Blo 599292 1353167 := bstep (se 1 (by rfl) ⟨1014875, by rfl⟩ : syracuseStep 1353167 = 2029751) B2029751
theorem B1353185 : Blo 599292 1353185 := bstep (se 2 (by rfl) ⟨507444, by rfl⟩ : syracuseStep 1353185 = 1014889) B1014889
theorem B1517039 : Blo 599292 1517039 := bstep (se 1 (by rfl) ⟨1137779, by rfl⟩ : syracuseStep 1517039 = 2275559) B2275559
theorem B599535 : Blo 599292 599535 := bstep (se 1 (by rfl) ⟨449651, by rfl⟩ : syracuseStep 599535 = 899303) B899303
theorem B4564511 : Blo 599292 4564511 := bstep (se 1 (by rfl) ⟨3423383, by rfl⟩ : syracuseStep 4564511 = 6846767) B6846767
theorem B1517231 : Blo 599292 1517231 := bstep (se 1 (by rfl) ⟨1137923, by rfl⟩ : syracuseStep 1517231 = 2275847) B2275847
theorem B1025767 : Blo 599292 1025767 := bstep (se 1 (by rfl) ⟨769325, by rfl⟩ : syracuseStep 1025767 = 1538651) B1538651
theorem B599783 : Blo 599292 599783 := bstep (se 1 (by rfl) ⟨449837, by rfl⟩ : syracuseStep 599783 = 899675) B899675
theorem B599879 : Blo 599292 599879 := bstep (se 1 (by rfl) ⟨449909, by rfl⟩ : syracuseStep 599879 = 899819) B899819
theorem B599899 : Blo 599292 599899 := bstep (se 1 (by rfl) ⟨449924, by rfl⟩ : syracuseStep 599899 = 899849) B899849
theorem B1353563 : Blo 599292 1353563 := bstep (se 1 (by rfl) ⟨1015172, by rfl⟩ : syracuseStep 1353563 = 2030345) B2030345
theorem B1517555 : Blo 599292 1517555 := bstep (se 1 (by rfl) ⟨1138166, by rfl⟩ : syracuseStep 1517555 = 2276333) B2276333
theorem B6007081 : Blo 599292 6007081 := bstep (se 2 (by rfl) ⟨2252655, by rfl⟩ : syracuseStep 6007081 = 4505311) B4505311
theorem B10987933 : Blo 599292 10987933 := bstep (se 3 (by rfl) ⟨2060237, by rfl⟩ : syracuseStep 10987933 = 4120475) B4120475
theorem B600479 : Blo 599292 600479 := bstep (se 1 (by rfl) ⟨450359, by rfl⟩ : syracuseStep 600479 = 900719) B900719
theorem B600559 : Blo 599292 600559 := bstep (se 1 (by rfl) ⟨450419, by rfl⟩ : syracuseStep 600559 = 900839) B900839
theorem B2435599 : Blo 599292 2435599 := bstep (se 1 (by rfl) ⟨1826699, by rfl⟩ : syracuseStep 2435599 = 3653399) B3653399
theorem B600687 : Blo 599292 600687 := bstep (se 1 (by rfl) ⟨450515, by rfl⟩ : syracuseStep 600687 = 901031) B901031
theorem B1354535 : Blo 599292 1354535 := bstep (se 1 (by rfl) ⟨1015901, by rfl⟩ : syracuseStep 1354535 = 2031803) B2031803
theorem B600903 : Blo 599292 600903 := bstep (se 1 (by rfl) ⟨450677, by rfl⟩ : syracuseStep 600903 = 901355) B901355
theorem B2566991 : Blo 599292 2566991 := bstep (se 1 (by rfl) ⟨1925243, by rfl⟩ : syracuseStep 2566991 = 3850487) B3850487
theorem B600943 : Blo 599292 600943 := bstep (se 1 (by rfl) ⟨450707, by rfl⟩ : syracuseStep 600943 = 901415) B901415
theorem B4565969 : Blo 599292 4565969 := bstep (se 2 (by rfl) ⟨1712238, by rfl⟩ : syracuseStep 4565969 = 3424477) B3424477
theorem B601391 : Blo 599292 601391 := bstep (se 1 (by rfl) ⟨451043, by rfl⟩ : syracuseStep 601391 = 902087) B902087
theorem B601503 : Blo 599292 601503 := bstep (se 1 (by rfl) ⟨451127, by rfl⟩ : syracuseStep 601503 = 902255) B902255
theorem B601631 : Blo 599292 601631 := bstep (se 1 (by rfl) ⟨451223, by rfl⟩ : syracuseStep 601631 = 902447) B902447
theorem B1519175 : Blo 599292 1519175 := bstep (se 1 (by rfl) ⟨1139381, by rfl⟩ : syracuseStep 1519175 = 2278763) B2278763
theorem B1519195 : Blo 599292 1519195 := bstep (se 1 (by rfl) ⟨1139396, by rfl⟩ : syracuseStep 1519195 = 2278793) B2278793
theorem B601767 : Blo 599292 601767 := bstep (se 1 (by rfl) ⟨451325, by rfl⟩ : syracuseStep 601767 = 902651) B902651
theorem B601791 : Blo 599292 601791 := bstep (se 1 (by rfl) ⟨451343, by rfl⟩ : syracuseStep 601791 = 902687) B902687
theorem B601887 : Blo 599292 601887 := bstep (se 1 (by rfl) ⟨451415, by rfl⟩ : syracuseStep 601887 = 902831) B902831
theorem B601967 : Blo 599292 601967 := bstep (se 1 (by rfl) ⟨451475, by rfl⟩ : syracuseStep 601967 = 902951) B902951
theorem B1716385 : Blo 599292 1716385 := bstep (se 2 (by rfl) ⟨643644, by rfl⟩ : syracuseStep 1716385 = 1287289) B1287289
theorem B602335 : Blo 599292 602335 := bstep (se 1 (by rfl) ⟨451751, by rfl⟩ : syracuseStep 602335 = 903503) B903503
theorem B602367 : Blo 599292 602367 := bstep (se 1 (by rfl) ⟨451775, by rfl⟩ : syracuseStep 602367 = 903551) B903551
theorem B602395 : Blo 599292 602395 := bstep (se 1 (by rfl) ⟨451796, by rfl⟩ : syracuseStep 602395 = 903593) B903593
theorem B602651 : Blo 599292 602651 := bstep (se 1 (by rfl) ⟨451988, by rfl⟩ : syracuseStep 602651 = 903977) B903977
theorem B602791 : Blo 599292 602791 := bstep (se 1 (by rfl) ⟨452093, by rfl⟩ : syracuseStep 602791 = 904187) B904187
theorem B602831 : Blo 599292 602831 := bstep (se 1 (by rfl) ⟨452123, by rfl⟩ : syracuseStep 602831 = 904247) B904247
theorem B1717001 : Blo 599292 1717001 := bstep (se 2 (by rfl) ⟨643875, by rfl⟩ : syracuseStep 1717001 = 1287751) B1287751
theorem B602911 : Blo 599292 602911 := bstep (se 1 (by rfl) ⟨452183, by rfl⟩ : syracuseStep 602911 = 904367) B904367
theorem B10990495 : Blo 599292 10990495 := bstep (se 1 (by rfl) ⟨8242871, by rfl⟩ : syracuseStep 10990495 = 16485743) B16485743
theorem B1356713 : Blo 599292 1356713 := bstep (se 2 (by rfl) ⟨508767, by rfl⟩ : syracuseStep 1356713 = 1017535) B1017535
theorem B6173651 : Blo 599292 6173651 := bstep (se 1 (by rfl) ⟨4630238, by rfl⟩ : syracuseStep 6173651 = 9260477) B9260477
theorem B3257327 : Blo 599292 3257327 := bstep (se 1 (by rfl) ⟨2442995, by rfl⟩ : syracuseStep 3257327 = 4885991) B4885991
theorem B1520633 : Blo 599292 1520633 := bstep (se 2 (by rfl) ⟨570237, by rfl⟩ : syracuseStep 1520633 = 1140475) B1140475
theorem B1717615 : Blo 599292 1717615 := bstep (se 1 (by rfl) ⟨1288211, by rfl⟩ : syracuseStep 1717615 = 2576423) B2576423
theorem B3421561 : Blo 599292 3421561 := bstep (se 2 (by rfl) ⟨1283085, by rfl⟩ : syracuseStep 3421561 = 2566171) B2566171
theorem B1717843 : Blo 599292 1717843 := bstep (se 1 (by rfl) ⟨1288382, by rfl⟩ : syracuseStep 1717843 = 2576765) B2576765
theorem B899051 : Blo 599292 899051 := bstep (se 1 (by rfl) ⟨674288, by rfl⟩ : syracuseStep 899051 = 1348577) B1348577
theorem B899135 : Blo 599292 899135 := bstep (se 1 (by rfl) ⟨674351, by rfl⟩ : syracuseStep 899135 = 1348703) B1348703
theorem B7682111 : Blo 599292 7682111 := bstep (se 1 (by rfl) ⟨5761583, by rfl⟩ : syracuseStep 7682111 = 11523167) B11523167
theorem B1521767 : Blo 599292 1521767 := bstep (se 1 (by rfl) ⟨1141325, by rfl⟩ : syracuseStep 1521767 = 2282651) B2282651
theorem B1947863 : Blo 599292 1947863 := bstep (se 1 (by rfl) ⟨1460897, by rfl⟩ : syracuseStep 1947863 = 2921795) B2921795
theorem B6338845 : Blo 599292 6338845 := bstep (se 3 (by rfl) ⟨1188533, by rfl⟩ : syracuseStep 6338845 = 2377067) B2377067
theorem B899465 : Blo 599292 899465 := bstep (se 2 (by rfl) ⟨337299, by rfl⟩ : syracuseStep 899465 = 674599) B674599
theorem B1489291 : Blo 599292 1489291 := bstep (se 1 (by rfl) ⟨1116968, by rfl⟩ : syracuseStep 1489291 = 2233937) B2233937
theorem B1522223 : Blo 599292 1522223 := bstep (se 1 (by rfl) ⟨1141667, by rfl⟩ : syracuseStep 1522223 = 2283335) B2283335
theorem B899639 : Blo 599292 899639 := bstep (se 1 (by rfl) ⟨674729, by rfl⟩ : syracuseStep 899639 = 1349459) B1349459
theorem B899963 : Blo 599292 899963 := bstep (se 1 (by rfl) ⟨674972, by rfl⟩ : syracuseStep 899963 = 1349945) B1349945
theorem B4570343 : Blo 599292 4570343 := bstep (se 1 (by rfl) ⟨3427757, by rfl⟩ : syracuseStep 4570343 = 6855515) B6855515
theorem B3849515 : Blo 599292 3849515 := bstep (se 1 (by rfl) ⟨2887136, by rfl⟩ : syracuseStep 3849515 = 5774273) B5774273
theorem B900575 : Blo 599292 900575 := bstep (se 1 (by rfl) ⟨675431, by rfl⟩ : syracuseStep 900575 = 1350863) B1350863
theorem B2277017 : Blo 599292 2277017 := bstep (se 2 (by rfl) ⟨853881, by rfl⟩ : syracuseStep 2277017 = 1707763) B1707763
theorem B900827 : Blo 599292 900827 := bstep (se 1 (by rfl) ⟨675620, by rfl⟩ : syracuseStep 900827 = 1351241) B1351241
theorem B2440955 : Blo 599292 2440955 := bstep (se 1 (by rfl) ⟨1830716, by rfl⟩ : syracuseStep 2440955 = 3661433) B3661433
theorem B901097 : Blo 599292 901097 := bstep (se 2 (by rfl) ⟨337911, by rfl⟩ : syracuseStep 901097 = 675823) B675823
theorem B3424295 : Blo 599292 3424295 := bstep (se 1 (by rfl) ⟨2568221, by rfl⟩ : syracuseStep 3424295 = 5136443) B5136443
theorem B901289 : Blo 599292 901289 := bstep (se 2 (by rfl) ⟨337983, by rfl⟩ : syracuseStep 901289 = 675967) B675967
theorem B5128379 : Blo 599292 5128379 := bstep (se 1 (by rfl) ⟨3846284, by rfl⟩ : syracuseStep 5128379 = 7692569) B7692569
theorem B5783885 : Blo 599292 5783885 := bstep (se 3 (by rfl) ⟨1084478, by rfl⟩ : syracuseStep 5783885 = 2168957) B2168957
theorem B901607 : Blo 599292 901607 := bstep (se 1 (by rfl) ⟨676205, by rfl⟩ : syracuseStep 901607 = 1352411) B1352411
theorem B1524329 : Blo 599292 1524329 := bstep (se 2 (by rfl) ⟨571623, by rfl⟩ : syracuseStep 1524329 = 1143247) B1143247
theorem B901883 : Blo 599292 901883 := bstep (se 1 (by rfl) ⟨676412, by rfl⟩ : syracuseStep 901883 = 1352825) B1352825
theorem B7717787 : Blo 599292 7717787 := bstep (se 1 (by rfl) ⟨5788340, by rfl⟩ : syracuseStep 7717787 = 11576681) B11576681
theorem B902327 : Blo 599292 902327 := bstep (se 1 (by rfl) ⟨676745, by rfl⟩ : syracuseStep 902327 = 1353491) B1353491
theorem B902471 : Blo 599292 902471 := bstep (se 1 (by rfl) ⟨676853, by rfl⟩ : syracuseStep 902471 = 1353707) B1353707
theorem B902567 : Blo 599292 902567 := bstep (se 1 (by rfl) ⟨676925, by rfl⟩ : syracuseStep 902567 = 1353851) B1353851
theorem B6833645 : Blo 599292 6833645 := bstep (se 3 (by rfl) ⟨1281308, by rfl⟩ : syracuseStep 6833645 = 2562617) B2562617
theorem B902747 : Blo 599292 902747 := bstep (se 1 (by rfl) ⟨677060, by rfl⟩ : syracuseStep 902747 = 1354121) B1354121
theorem B903215 : Blo 599292 903215 := bstep (se 1 (by rfl) ⟨677411, by rfl⟩ : syracuseStep 903215 = 1354823) B1354823
theorem B903479 : Blo 599292 903479 := bstep (se 1 (by rfl) ⟨677609, by rfl⟩ : syracuseStep 903479 = 1355219) B1355219
theorem B903659 : Blo 599292 903659 := bstep (se 1 (by rfl) ⟨677744, by rfl⟩ : syracuseStep 903659 = 1355489) B1355489
theorem B3656299 : Blo 599292 3656299 := bstep (se 1 (by rfl) ⟨2742224, by rfl⟩ : syracuseStep 3656299 = 5484449) B5484449
theorem B903899 : Blo 599292 903899 := bstep (se 1 (by rfl) ⟨677924, by rfl⟩ : syracuseStep 903899 = 1355849) B1355849
theorem B2607839 : Blo 599292 2607839 := bstep (se 1 (by rfl) ⟨1955879, by rfl⟩ : syracuseStep 2607839 = 3911759) B3911759
theorem B641791 : Blo 599292 641791 := bstep (se 1 (by rfl) ⟨481343, by rfl⟩ : syracuseStep 641791 = 962687) B962687
theorem B903935 : Blo 599292 903935 := bstep (se 1 (by rfl) ⟨677951, by rfl⟩ : syracuseStep 903935 = 1355903) B1355903
theorem B12307565 : Blo 599292 12307565 := bstep (se 3 (by rfl) ⟨2307668, by rfl⟩ : syracuseStep 12307565 = 4615337) B4615337
theorem B1526951 : Blo 599292 1526951 := bstep (se 1 (by rfl) ⟨1145213, by rfl⟩ : syracuseStep 1526951 = 2290427) B2290427
theorem B904655 : Blo 599292 904655 := bstep (se 1 (by rfl) ⟨678491, by rfl⟩ : syracuseStep 904655 = 1356983) B1356983
theorem B904745 : Blo 599292 904745 := bstep (se 2 (by rfl) ⟨339279, by rfl⟩ : syracuseStep 904745 = 678559) B678559
theorem B3427919 : Blo 599292 3427919 := bstep (se 1 (by rfl) ⟨2570939, by rfl⟩ : syracuseStep 3427919 = 5141879) B5141879
theorem B2576681 : Blo 599292 2576681 := bstep (se 2 (by rfl) ⟨966255, by rfl⟩ : syracuseStep 2576681 = 1932511) B1932511
theorem B7721477 : Blo 599292 7721477 := bstep (se 4 (by rfl) ⟨723888, by rfl⟩ : syracuseStep 7721477 = 1447777) B1447777
theorem B5624657 : Blo 599292 5624657 := bstep (se 2 (by rfl) ⟨2109246, by rfl⟩ : syracuseStep 5624657 = 4218493) B4218493
theorem B676831 : Blo 599292 676831 := bstep (se 1 (by rfl) ⟨507623, by rfl⟩ : syracuseStep 676831 = 1015247) B1015247
theorem B6182027 : Blo 599292 6182027 := bstep (se 1 (by rfl) ⟨4636520, by rfl⟩ : syracuseStep 6182027 = 9273041) B9273041
theorem B677407 : Blo 599292 677407 := bstep (se 1 (by rfl) ⟨508055, by rfl⟩ : syracuseStep 677407 = 1016111) B1016111
theorem B1922783 : Blo 599292 1922783 := bstep (se 1 (by rfl) ⟨1442087, by rfl⟩ : syracuseStep 1922783 = 2884175) B2884175
theorem B3037337 : Blo 599292 3037337 := bstep (se 2 (by rfl) ⟨1139001, by rfl⟩ : syracuseStep 3037337 = 2278003) B2278003
theorem B678271 : Blo 599292 678271 := bstep (se 1 (by rfl) ⟨508703, by rfl⟩ : syracuseStep 678271 = 1017407) B1017407
theorem B15392105 : Blo 599292 15392105 := bstep (se 2 (by rfl) ⟨5772039, by rfl⟩ : syracuseStep 15392105 = 11544079) B11544079
theorem B3038633 : Blo 599292 3038633 := bstep (se 2 (by rfl) ⟨1139487, by rfl⟩ : syracuseStep 3038633 = 2278975) B2278975
theorem B2022839 : Blo 599292 2022839 := bstep (se 1 (by rfl) ⟨1517129, by rfl⟩ : syracuseStep 2022839 = 3034259) B3034259
theorem B4579091 : Blo 599292 4579091 := bstep (se 1 (by rfl) ⟨3434318, by rfl⟩ : syracuseStep 4579091 = 6868637) B6868637
theorem B2023379 : Blo 599292 2023379 := bstep (se 1 (by rfl) ⟨1517534, by rfl⟩ : syracuseStep 2023379 = 3035069) B3035069
theorem B2023487 : Blo 599292 2023487 := bstep (se 1 (by rfl) ⟨1517615, by rfl⟩ : syracuseStep 2023487 = 3035231) B3035231
theorem B1826945 : Blo 599292 1826945 := bstep (se 2 (by rfl) ⟨685104, by rfl⟩ : syracuseStep 1826945 = 1370209) B1370209
theorem B1139359 : Blo 599292 1139359 := bstep (se 1 (by rfl) ⟨854519, by rfl⟩ : syracuseStep 1139359 = 1709039) B1709039
theorem B3433225 : Blo 599292 3433225 := bstep (se 2 (by rfl) ⟨1287459, by rfl⟩ : syracuseStep 3433225 = 2574919) B2574919
theorem B1926013 : Blo 599292 1926013 := bstep (se 3 (by rfl) ⟨361127, by rfl⟩ : syracuseStep 1926013 = 722255) B722255
theorem B47605477 : Blo 599292 47605477 := bstep (se 4 (by rfl) ⟨4463013, by rfl⟩ : syracuseStep 47605477 = 8926027) B8926027
theorem B4876199 : Blo 599292 4876199 := bstep (se 1 (by rfl) ⟨3657149, by rfl⟩ : syracuseStep 4876199 = 7314299) B7314299
theorem B3041873 : Blo 599292 3041873 := bstep (se 2 (by rfl) ⟨1140702, by rfl⟩ : syracuseStep 3041873 = 2281405) B2281405
theorem B1927795 : Blo 599292 1927795 := bstep (se 1 (by rfl) ⟨1445846, by rfl⟩ : syracuseStep 1927795 = 2891693) B2891693
theorem B3042035 : Blo 599292 3042035 := bstep (se 1 (by rfl) ⟨2281526, by rfl⟩ : syracuseStep 3042035 = 4563053) B4563053
theorem B6843851 : Blo 599292 6843851 := bstep (se 1 (by rfl) ⟨5132888, by rfl⟩ : syracuseStep 6843851 = 10265777) B10265777
theorem B49475393 : Blo 599292 49475393 := bstep (se 2 (by rfl) ⟨18553272, by rfl⟩ : syracuseStep 49475393 = 37106545) B37106545
theorem B1142761 : Blo 599292 1142761 := bstep (se 2 (by rfl) ⟨428535, by rfl⟩ : syracuseStep 1142761 = 857071) B857071
theorem B1044535 : Blo 599292 1044535 := bstep (se 1 (by rfl) ⟨783401, by rfl⟩ : syracuseStep 1044535 = 1566803) B1566803
theorem B4878463 : Blo 599292 4878463 := bstep (se 1 (by rfl) ⟨3658847, by rfl⟩ : syracuseStep 4878463 = 7317695) B7317695
theorem B1011919 : Blo 599292 1011919 := bstep (se 1 (by rfl) ⟨758939, by rfl⟩ : syracuseStep 1011919 = 1517879) B1517879
theorem B1732823 : Blo 599292 1732823 := bstep (se 1 (by rfl) ⟨1299617, by rfl⟩ : syracuseStep 1732823 = 2599235) B2599235
theorem B3895543 : Blo 599292 3895543 := bstep (se 1 (by rfl) ⟨2921657, by rfl⟩ : syracuseStep 3895543 = 5843315) B5843315
theorem B3043655 : Blo 599292 3043655 := bstep (se 1 (by rfl) ⟨2282741, by rfl⟩ : syracuseStep 3043655 = 4565483) B4565483
theorem B5140817 : Blo 599292 5140817 := bstep (se 2 (by rfl) ⟨1927806, by rfl⟩ : syracuseStep 5140817 = 3855613) B3855613
theorem B1143163 : Blo 599292 1143163 := bstep (se 1 (by rfl) ⟨857372, by rfl⟩ : syracuseStep 1143163 = 1714745) B1714745
theorem B2879869 : Blo 599292 2879869 := bstep (se 3 (by rfl) ⟨539975, by rfl⟩ : syracuseStep 2879869 = 1079951) B1079951
theorem B6943103 : Blo 599292 6943103 := bstep (se 1 (by rfl) ⟨5207327, by rfl⟩ : syracuseStep 6943103 = 10414655) B10414655
theorem B1143649 : Blo 599292 1143649 := bstep (se 2 (by rfl) ⟨428868, by rfl⟩ : syracuseStep 1143649 = 857737) B857737
theorem B1012601 : Blo 599292 1012601 := bstep (se 2 (by rfl) ⟨379725, by rfl⟩ : syracuseStep 1012601 = 759451) B759451
theorem B1012891 : Blo 599292 1012891 := bstep (se 1 (by rfl) ⟨759668, by rfl⟩ : syracuseStep 1012891 = 1519337) B1519337
theorem B3864019 : Blo 599292 3864019 := bstep (se 1 (by rfl) ⟨2898014, by rfl⟩ : syracuseStep 3864019 = 5796029) B5796029
theorem B15431471 : Blo 599292 15431471 := bstep (se 1 (by rfl) ⟨11573603, by rfl⟩ : syracuseStep 15431471 = 23147207) B23147207
theorem B3700883 : Blo 599292 3700883 := bstep (se 1 (by rfl) ⟨2775662, by rfl⟩ : syracuseStep 3700883 = 5551325) B5551325
theorem B1014599 : Blo 599292 1014599 := bstep (se 1 (by rfl) ⟨760949, by rfl⟩ : syracuseStep 1014599 = 1521899) B1521899
theorem B2161691 : Blo 599292 2161691 := bstep (se 1 (by rfl) ⟨1621268, by rfl⟩ : syracuseStep 2161691 = 3242537) B3242537
theorem B916507 : Blo 599292 916507 := bstep (se 1 (by rfl) ⟨687380, by rfl⟩ : syracuseStep 916507 = 1374761) B1374761
theorem B13172183 : Blo 599292 13172183 := bstep (se 1 (by rfl) ⟨9879137, by rfl⟩ : syracuseStep 13172183 = 19758275) B19758275
theorem B2031911 : Blo 599292 2031911 := bstep (se 1 (by rfl) ⟨1523933, by rfl⟩ : syracuseStep 2031911 = 3047867) B3047867
theorem B1016219 : Blo 599292 1016219 := bstep (se 1 (by rfl) ⟨762164, by rfl⟩ : syracuseStep 1016219 = 1524329) B1524329
theorem B5145191 : Blo 599292 5145191 := bstep (se 1 (by rfl) ⟨3858893, by rfl⟩ : syracuseStep 5145191 = 7717787) B7717787
theorem B4555763 : Blo 599292 4555763 := bstep (se 1 (by rfl) ⟨3416822, by rfl⟩ : syracuseStep 4555763 = 6833645) B6833645
theorem B1738559 : Blo 599292 1738559 := bstep (se 1 (by rfl) ⟨1303919, by rfl⟩ : syracuseStep 1738559 = 2607839) B2607839
theorem B1017967 : Blo 599292 1017967 := bstep (se 1 (by rfl) ⟨763475, by rfl⟩ : syracuseStep 1017967 = 1526951) B1526951
theorem B63473969 : Blo 599292 63473969 := bstep (se 2 (by rfl) ⟨23802738, by rfl⟩ : syracuseStep 63473969 = 47605477) B47605477
theorem B5147651 : Blo 599292 5147651 := bstep (se 1 (by rfl) ⟨3860738, by rfl⟩ : syracuseStep 5147651 = 7721477) B7721477
theorem B2034719 : Blo 599292 2034719 := bstep (se 1 (by rfl) ⟨1526039, by rfl⟩ : syracuseStep 2034719 = 3052079) B3052079
theorem B14650577 : Blo 599292 14650577 := bstep (se 2 (by rfl) ⟨5493966, by rfl⟩ : syracuseStep 14650577 = 10987933) B10987933
theorem B3247465 : Blo 599292 3247465 := bstep (se 2 (by rfl) ⟨1217799, by rfl⟩ : syracuseStep 3247465 = 2435599) B2435599
theorem B855721 : Blo 599292 855721 := bstep (se 2 (by rfl) ⟨320895, by rfl⟩ : syracuseStep 855721 = 641791) B641791
theorem B2035583 : Blo 599292 2035583 := bstep (se 1 (by rfl) ⟨1526687, by rfl⟩ : syracuseStep 2035583 = 3053375) B3053375
theorem B2035867 : Blo 599292 2035867 := bstep (se 1 (by rfl) ⟨1526900, by rfl⟩ : syracuseStep 2035867 = 3053801) B3053801
theorem B19075733 : Blo 599292 19075733 := bstep (se 6 (by rfl) ⟨447087, by rfl⟩ : syracuseStep 19075733 = 894175) B894175
theorem B10261403 : Blo 599292 10261403 := bstep (se 1 (by rfl) ⟨7696052, by rfl⟩ : syracuseStep 10261403 = 15392105) B15392105
theorem B2888635 : Blo 599292 2888635 := bstep (se 1 (by rfl) ⟨2166476, by rfl⟩ : syracuseStep 2888635 = 4332953) B4332953
theorem B1348559 : Blo 599292 1348559 := bstep (se 1 (by rfl) ⟨1011419, by rfl⟩ : syracuseStep 1348559 = 2022839) B2022839
theorem B3052727 : Blo 599292 3052727 := bstep (se 1 (by rfl) ⟨2289545, by rfl⟩ : syracuseStep 3052727 = 4579091) B4579091
theorem B1348919 : Blo 599292 1348919 := bstep (se 1 (by rfl) ⟨1011689, by rfl⟩ : syracuseStep 1348919 = 2023379) B2023379
theorem B1709369 : Blo 599292 1709369 := bstep (se 2 (by rfl) ⟨641013, by rfl⟩ : syracuseStep 1709369 = 1282027) B1282027
theorem B1348991 : Blo 599292 1348991 := bstep (se 1 (by rfl) ⟨1011743, by rfl⟩ : syracuseStep 1348991 = 2023487) B2023487
theorem B1217963 : Blo 599292 1217963 := bstep (se 1 (by rfl) ⟨913472, by rfl⟩ : syracuseStep 1217963 = 1826945) B1826945
theorem B1349225 : Blo 599292 1349225 := bstep (se 2 (by rfl) ⟨505959, by rfl⟩ : syracuseStep 1349225 = 1011919) B1011919
theorem B1709711 : Blo 599292 1709711 := bstep (se 1 (by rfl) ⟨1282283, by rfl⟩ : syracuseStep 1709711 = 2564567) B2564567
theorem B9279197 : Blo 599292 9279197 := bstep (se 3 (by rfl) ⟨1739849, by rfl⟩ : syracuseStep 9279197 = 3479699) B3479699
theorem B3839825 : Blo 599292 3839825 := bstep (se 2 (by rfl) ⟨1439934, by rfl⟩ : syracuseStep 3839825 = 2879869) B2879869
theorem B1710143 : Blo 599292 1710143 := bstep (se 1 (by rfl) ⟨1282607, by rfl⟩ : syracuseStep 1710143 = 2565215) B2565215
theorem B14653993 : Blo 599292 14653993 := bstep (se 2 (by rfl) ⟨5495247, by rfl⟩ : syracuseStep 14653993 = 10990495) B10990495
theorem B3250799 : Blo 599292 3250799 := bstep (se 1 (by rfl) ⟨2438099, by rfl⟩ : syracuseStep 3250799 = 4876199) B4876199
theorem B1350521 : Blo 599292 1350521 := bstep (se 2 (by rfl) ⟨506445, by rfl⟩ : syracuseStep 1350521 = 1012891) B1012891
theorem B4562081 : Blo 599292 4562081 := bstep (se 2 (by rfl) ⟨1710780, by rfl⟩ : syracuseStep 4562081 = 3421561) B3421561
theorem B5152025 : Blo 599292 5152025 := bstep (se 2 (by rfl) ⟨1932009, by rfl⟩ : syracuseStep 5152025 = 3864019) B3864019
theorem B4562567 : Blo 599292 4562567 := bstep (se 1 (by rfl) ⟨3421925, by rfl⟩ : syracuseStep 4562567 = 6843851) B6843851
theorem B1155215 : Blo 599292 1155215 := bstep (se 1 (by rfl) ⟨866411, by rfl⟩ : syracuseStep 1155215 = 1732823) B1732823
theorem B4628735 : Blo 599292 4628735 := bstep (se 1 (by rfl) ⟨3471551, by rfl⟩ : syracuseStep 4628735 = 6943103) B6943103
theorem B2171551 : Blo 599292 2171551 := bstep (se 1 (by rfl) ⟨1628663, by rfl⟩ : syracuseStep 2171551 = 3257327) B3257327
theorem B599367 : Blo 599292 599367 := bstep (se 1 (by rfl) ⟨449525, by rfl⟩ : syracuseStep 599367 = 899051) B899051
theorem B1222009 : Blo 599292 1222009 := bstep (se 2 (by rfl) ⟨458253, by rfl⟩ : syracuseStep 1222009 = 916507) B916507
theorem B599423 : Blo 599292 599423 := bstep (se 1 (by rfl) ⟨449567, by rfl⟩ : syracuseStep 599423 = 899135) B899135
theorem B5121407 : Blo 599292 5121407 := bstep (se 1 (by rfl) ⟨3841055, by rfl⟩ : syracuseStep 5121407 = 7682111) B7682111
theorem B2467255 : Blo 599292 2467255 := bstep (se 1 (by rfl) ⟨1850441, by rfl⟩ : syracuseStep 2467255 = 3700883) B3700883
theorem B599643 : Blo 599292 599643 := bstep (se 1 (by rfl) ⟨449732, by rfl⟩ : syracuseStep 599643 = 899465) B899465
theorem B599759 : Blo 599292 599759 := bstep (se 1 (by rfl) ⟨449819, by rfl⟩ : syracuseStep 599759 = 899639) B899639
theorem B599975 : Blo 599292 599975 := bstep (se 1 (by rfl) ⟨449981, by rfl⟩ : syracuseStep 599975 = 899963) B899963
theorem B2566343 : Blo 599292 2566343 := bstep (se 1 (by rfl) ⟨1924757, by rfl⟩ : syracuseStep 2566343 = 3849515) B3849515
theorem B600383 : Blo 599292 600383 := bstep (se 1 (by rfl) ⟨450287, by rfl⟩ : syracuseStep 600383 = 900575) B900575
theorem B1518011 : Blo 599292 1518011 := bstep (se 1 (by rfl) ⟨1138508, by rfl⟩ : syracuseStep 1518011 = 2277017) B2277017
theorem B600551 : Blo 599292 600551 := bstep (se 1 (by rfl) ⟨450413, by rfl⟩ : syracuseStep 600551 = 900827) B900827
theorem B600731 : Blo 599292 600731 := bstep (se 1 (by rfl) ⟨450548, by rfl⟩ : syracuseStep 600731 = 901097) B901097
theorem B600859 : Blo 599292 600859 := bstep (se 1 (by rfl) ⟨450644, by rfl⟩ : syracuseStep 600859 = 901289) B901289
theorem B3418919 : Blo 599292 3418919 := bstep (se 1 (by rfl) ⟨2564189, by rfl⟩ : syracuseStep 3418919 = 5128379) B5128379
theorem B601071 : Blo 599292 601071 := bstep (se 1 (by rfl) ⟨450803, by rfl⟩ : syracuseStep 601071 = 901607) B901607
theorem B601255 : Blo 599292 601255 := bstep (se 1 (by rfl) ⟨450941, by rfl⟩ : syracuseStep 601255 = 901883) B901883
theorem B1355129 : Blo 599292 1355129 := bstep (se 2 (by rfl) ⟨508173, by rfl⟩ : syracuseStep 1355129 = 1016347) B1016347
theorem B4566455 : Blo 599292 4566455 := bstep (se 1 (by rfl) ⟨3424841, by rfl⟩ : syracuseStep 4566455 = 6849683) B6849683
theorem B601551 : Blo 599292 601551 := bstep (se 1 (by rfl) ⟨451163, by rfl⟩ : syracuseStep 601551 = 902327) B902327
theorem B1519145 : Blo 599292 1519145 := bstep (se 2 (by rfl) ⟨569679, by rfl⟩ : syracuseStep 1519145 = 1139359) B1139359
theorem B601647 : Blo 599292 601647 := bstep (se 1 (by rfl) ⟨451235, by rfl⟩ : syracuseStep 601647 = 902471) B902471
theorem B601711 : Blo 599292 601711 := bstep (se 1 (by rfl) ⟨451283, by rfl⟩ : syracuseStep 601711 = 902567) B902567
theorem B601831 : Blo 599292 601831 := bstep (se 1 (by rfl) ⟨451373, by rfl⟩ : syracuseStep 601831 = 902747) B902747
theorem B2568017 : Blo 599292 2568017 := bstep (se 2 (by rfl) ⟨963006, by rfl⟩ : syracuseStep 2568017 = 1926013) B1926013
theorem B602143 : Blo 599292 602143 := bstep (se 1 (by rfl) ⟨451607, by rfl⟩ : syracuseStep 602143 = 903215) B903215
theorem B1355831 : Blo 599292 1355831 := bstep (se 1 (by rfl) ⟨1016873, by rfl⟩ : syracuseStep 1355831 = 2033747) B2033747
theorem B602319 : Blo 599292 602319 := bstep (se 1 (by rfl) ⟨451739, by rfl⟩ : syracuseStep 602319 = 903479) B903479
theorem B602439 : Blo 599292 602439 := bstep (se 1 (by rfl) ⟨451829, by rfl⟩ : syracuseStep 602439 = 903659) B903659
theorem B602599 : Blo 599292 602599 := bstep (se 1 (by rfl) ⟨451949, by rfl⟩ : syracuseStep 602599 = 903899) B903899
theorem B602623 : Blo 599292 602623 := bstep (se 1 (by rfl) ⟨451967, by rfl⟩ : syracuseStep 602623 = 903935) B903935
theorem B603103 : Blo 599292 603103 := bstep (se 1 (by rfl) ⟨452327, by rfl⟩ : syracuseStep 603103 = 904655) B904655
theorem B603163 : Blo 599292 603163 := bstep (se 1 (by rfl) ⟨452372, by rfl⟩ : syracuseStep 603163 = 904745) B904745
theorem B3519551 : Blo 599292 3519551 := bstep (se 1 (by rfl) ⟨2639663, by rfl⟩ : syracuseStep 3519551 = 5279327) B5279327
theorem B1717787 : Blo 599292 1717787 := bstep (se 1 (by rfl) ⟨1288340, by rfl⟩ : syracuseStep 1717787 = 2576681) B2576681
theorem B8009441 : Blo 599292 8009441 := bstep (se 2 (by rfl) ⟨3003540, by rfl⟩ : syracuseStep 8009441 = 6007081) B6007081
theorem B3749771 : Blo 599292 3749771 := bstep (se 1 (by rfl) ⟨2812328, by rfl⟩ : syracuseStep 3749771 = 5624657) B5624657
theorem B2570393 : Blo 599292 2570393 := bstep (se 2 (by rfl) ⟨963897, by rfl⟩ : syracuseStep 2570393 = 1927795) B1927795
theorem B2276059 : Blo 599292 2276059 := bstep (se 1 (by rfl) ⟨1707044, by rfl⟩ : syracuseStep 2276059 = 3414089) B3414089
theorem B965339 : Blo 599292 965339 := bstep (se 1 (by rfl) ⟨724004, by rfl⟩ : syracuseStep 965339 = 1448009) B1448009
theorem B900203 : Blo 599292 900203 := bstep (se 1 (by rfl) ⟨675152, by rfl⟩ : syracuseStep 900203 = 1350305) B1350305
theorem B5127421 : Blo 599292 5127421 := bstep (se 3 (by rfl) ⟨961391, by rfl⟩ : syracuseStep 5127421 = 1922783) B1922783
theorem B900443 : Blo 599292 900443 := bstep (se 1 (by rfl) ⟨675332, by rfl⟩ : syracuseStep 900443 = 1350665) B1350665
theorem B966185 : Blo 599292 966185 := bstep (se 2 (by rfl) ⟨362319, by rfl⟩ : syracuseStep 966185 = 724639) B724639
theorem B1621615 : Blo 599292 1621615 := bstep (se 1 (by rfl) ⟨1216211, by rfl⟩ : syracuseStep 1621615 = 2432423) B2432423
theorem B2277031 : Blo 599292 2277031 := bstep (se 1 (by rfl) ⟨1707773, by rfl⟩ : syracuseStep 2277031 = 3415547) B3415547
theorem B900791 : Blo 599292 900791 := bstep (se 1 (by rfl) ⟨675593, by rfl⟩ : syracuseStep 900791 = 1351187) B1351187
theorem B1523681 : Blo 599292 1523681 := bstep (se 2 (by rfl) ⟨571380, by rfl⟩ : syracuseStep 1523681 = 1142761) B1142761
theorem B901103 : Blo 599292 901103 := bstep (se 1 (by rfl) ⟨675827, by rfl⟩ : syracuseStep 901103 = 1351655) B1351655
theorem B1392713 : Blo 599292 1392713 := bstep (se 2 (by rfl) ⟨522267, by rfl⟩ : syracuseStep 1392713 = 1044535) B1044535
theorem B901223 : Blo 599292 901223 := bstep (se 1 (by rfl) ⟨675917, by rfl⟩ : syracuseStep 901223 = 1351835) B1351835
theorem B6504617 : Blo 599292 6504617 := bstep (se 2 (by rfl) ⟨2439231, by rfl⟩ : syracuseStep 6504617 = 4878463) B4878463
theorem B5194057 : Blo 599292 5194057 := bstep (se 2 (by rfl) ⟨1947771, by rfl⟩ : syracuseStep 5194057 = 3895543) B3895543
theorem B2277791 : Blo 599292 2277791 := bstep (se 1 (by rfl) ⟨1708343, by rfl⟩ : syracuseStep 2277791 = 3416687) B3416687
theorem B1524217 : Blo 599292 1524217 := bstep (se 2 (by rfl) ⟨571581, by rfl⟩ : syracuseStep 1524217 = 1143163) B1143163
theorem B901943 : Blo 599292 901943 := bstep (se 1 (by rfl) ⟨676457, by rfl⟩ : syracuseStep 901943 = 1352915) B1352915
theorem B902111 : Blo 599292 902111 := bstep (se 1 (by rfl) ⟨676583, by rfl⟩ : syracuseStep 902111 = 1353167) B1353167
theorem B902123 : Blo 599292 902123 := bstep (se 1 (by rfl) ⟨676592, by rfl⟩ : syracuseStep 902123 = 1353185) B1353185
theorem B1524865 : Blo 599292 1524865 := bstep (se 2 (by rfl) ⟨571824, by rfl⟩ : syracuseStep 1524865 = 1143649) B1143649
theorem B902375 : Blo 599292 902375 := bstep (se 1 (by rfl) ⟨676781, by rfl⟩ : syracuseStep 902375 = 1353563) B1353563
theorem B902441 : Blo 599292 902441 := bstep (se 2 (by rfl) ⟨338415, by rfl⟩ : syracuseStep 902441 = 676831) B676831
theorem B903023 : Blo 599292 903023 := bstep (se 1 (by rfl) ⟨677267, by rfl⟩ : syracuseStep 903023 = 1354535) B1354535
theorem B903209 : Blo 599292 903209 := bstep (se 2 (by rfl) ⟨338703, by rfl⟩ : syracuseStep 903209 = 677407) B677407
theorem B32983595 : Blo 599292 32983595 := bstep (se 1 (by rfl) ⟨24737696, by rfl⟩ : syracuseStep 32983595 = 49475393) B49475393
theorem B3427211 : Blo 599292 3427211 := bstep (se 1 (by rfl) ⟨2570408, by rfl⟩ : syracuseStep 3427211 = 5140817) B5140817
theorem B31771541 : Blo 599292 31771541 := bstep (se 6 (by rfl) ⟨744645, by rfl⟩ : syracuseStep 31771541 = 1489291) B1489291
theorem B32820173 : Blo 599292 32820173 := bstep (se 3 (by rfl) ⟨6153782, by rfl⟩ : syracuseStep 32820173 = 12307565) B12307565
theorem B904361 : Blo 599292 904361 := bstep (se 2 (by rfl) ⟨339135, by rfl⟩ : syracuseStep 904361 = 678271) B678271
theorem B675067 : Blo 599292 675067 := bstep (se 1 (by rfl) ⟨506300, by rfl⟩ : syracuseStep 675067 = 1012601) B1012601
theorem B904475 : Blo 599292 904475 := bstep (se 1 (by rfl) ⟨678356, by rfl⟩ : syracuseStep 904475 = 1356713) B1356713
theorem B4115767 : Blo 599292 4115767 := bstep (se 1 (by rfl) ⟨3086825, by rfl⟩ : syracuseStep 4115767 = 6173651) B6173651
theorem B1298575 : Blo 599292 1298575 := bstep (se 1 (by rfl) ⟨973931, by rfl⟩ : syracuseStep 1298575 = 1947863) B1947863
theorem B676399 : Blo 599292 676399 := bstep (se 1 (by rfl) ⟨507299, by rfl⟩ : syracuseStep 676399 = 1014599) B1014599
theorem B1627303 : Blo 599292 1627303 := bstep (se 1 (by rfl) ⟨1220477, by rfl⟩ : syracuseStep 1627303 = 2440955) B2440955
theorem B2282863 : Blo 599292 2282863 := bstep (se 1 (by rfl) ⟨1712147, by rfl⟩ : syracuseStep 2282863 = 3424295) B3424295
theorem B3855923 : Blo 599292 3855923 := bstep (se 1 (by rfl) ⟨2891942, by rfl⟩ : syracuseStep 3855923 = 5783885) B5783885
theorem B678055 : Blo 599292 678055 := bstep (se 1 (by rfl) ⟨508541, by rfl⟩ : syracuseStep 678055 = 1017083) B1017083
theorem B4577633 : Blo 599292 4577633 := bstep (se 2 (by rfl) ⟨1716612, by rfl⟩ : syracuseStep 4577633 = 3433225) B3433225
theorem B1923527 : Blo 599292 1923527 := bstep (se 1 (by rfl) ⟨1442645, by rfl⟩ : syracuseStep 1923527 = 2885291) B2885291
theorem B1367689 : Blo 599292 1367689 := bstep (se 2 (by rfl) ⟨512883, by rfl⟩ : syracuseStep 1367689 = 1025767) B1025767
theorem B2285279 : Blo 599292 2285279 := bstep (se 1 (by rfl) ⟨1713959, by rfl⟩ : syracuseStep 2285279 = 3427919) B3427919
theorem B75260335 : Blo 599292 75260335 := bstep (se 1 (by rfl) ⟨56445251, by rfl⟩ : syracuseStep 75260335 = 112890503) B112890503
theorem B3433043 : Blo 599292 3433043 := bstep (se 1 (by rfl) ⟨2574782, by rfl⟩ : syracuseStep 3433043 = 5149565) B5149565
theorem B4121351 : Blo 599292 4121351 := bstep (se 1 (by rfl) ⟨3091013, by rfl⟩ : syracuseStep 4121351 = 6182027) B6182027
theorem B4875065 : Blo 599292 4875065 := bstep (se 2 (by rfl) ⟨1828149, by rfl⟩ : syracuseStep 4875065 = 3656299) B3656299
theorem B2024891 : Blo 599292 2024891 := bstep (se 1 (by rfl) ⟨1518668, by rfl⟩ : syracuseStep 2024891 = 3037337) B3037337
theorem B1140331 : Blo 599292 1140331 := bstep (se 1 (by rfl) ⟨855248, by rfl⟩ : syracuseStep 1140331 = 1710497) B1710497
theorem B14641235 : Blo 599292 14641235 := bstep (se 1 (by rfl) ⟨10980926, by rfl⟩ : syracuseStep 14641235 = 21961853) B21961853
theorem B2025593 : Blo 599292 2025593 := bstep (se 2 (by rfl) ⟨759597, by rfl⟩ : syracuseStep 2025593 = 1519195) B1519195
theorem B2025755 : Blo 599292 2025755 := bstep (se 1 (by rfl) ⟨1519316, by rfl⟩ : syracuseStep 2025755 = 3038633) B3038633
theorem B7695233 : Blo 599292 7695233 := bstep (se 2 (by rfl) ⟨2885712, by rfl⟩ : syracuseStep 7695233 = 5771425) B5771425
theorem B2288513 : Blo 599292 2288513 := bstep (se 2 (by rfl) ⟨858192, by rfl⟩ : syracuseStep 2288513 = 1716385) B1716385
theorem B3042683 : Blo 599292 3042683 := bstep (se 1 (by rfl) ⟨2282012, by rfl⟩ : syracuseStep 3042683 = 4564025) B4564025
theorem B1011359 : Blo 599292 1011359 := bstep (se 1 (by rfl) ⟨758519, by rfl⟩ : syracuseStep 1011359 = 1517039) B1517039
theorem B3043007 : Blo 599292 3043007 := bstep (se 1 (by rfl) ⟨2282255, by rfl⟩ : syracuseStep 3043007 = 4564511) B4564511
theorem B1011487 : Blo 599292 1011487 := bstep (se 1 (by rfl) ⟨758615, by rfl⟩ : syracuseStep 1011487 = 1517231) B1517231
theorem B1011703 : Blo 599292 1011703 := bstep (se 1 (by rfl) ⟨758777, by rfl⟩ : syracuseStep 1011703 = 1517555) B1517555
theorem B3862637 : Blo 599292 3862637 := bstep (se 3 (by rfl) ⟨724244, by rfl⟩ : syracuseStep 3862637 = 1448489) B1448489
theorem B2027915 : Blo 599292 2027915 := bstep (se 1 (by rfl) ⟨1520936, by rfl⟩ : syracuseStep 2027915 = 3041873) B3041873
theorem B1143209 : Blo 599292 1143209 := bstep (se 2 (by rfl) ⟨428703, by rfl⟩ : syracuseStep 1143209 = 857407) B857407
theorem B2290153 : Blo 599292 2290153 := bstep (se 2 (by rfl) ⟨858807, by rfl⟩ : syracuseStep 2290153 = 1717615) B1717615
theorem B2028023 : Blo 599292 2028023 := bstep (se 1 (by rfl) ⟨1521017, by rfl⟩ : syracuseStep 2028023 = 3042035) B3042035
theorem B3043979 : Blo 599292 3043979 := bstep (se 1 (by rfl) ⟨2282984, by rfl⟩ : syracuseStep 3043979 = 4565969) B4565969
theorem B2290457 : Blo 599292 2290457 := bstep (se 2 (by rfl) ⟨858921, by rfl⟩ : syracuseStep 2290457 = 1717843) B1717843
theorem B7304033 : Blo 599292 7304033 := bstep (se 2 (by rfl) ⟨2739012, by rfl⟩ : syracuseStep 7304033 = 5478025) B5478025
theorem B6845309 : Blo 599292 6845309 := bstep (se 3 (by rfl) ⟨1283495, by rfl⟩ : syracuseStep 6845309 = 2566991) B2566991
theorem B1012783 : Blo 599292 1012783 := bstep (se 1 (by rfl) ⟨759587, by rfl⟩ : syracuseStep 1012783 = 1519175) B1519175
theorem B1930729 : Blo 599292 1930729 := bstep (se 2 (by rfl) ⟨724023, by rfl⟩ : syracuseStep 1930729 = 1448047) B1448047
theorem B2029103 : Blo 599292 2029103 := bstep (se 1 (by rfl) ⟨1521827, by rfl⟩ : syracuseStep 2029103 = 3043655) B3043655
theorem B8451793 : Blo 599292 8451793 := bstep (se 2 (by rfl) ⟨3169422, by rfl⟩ : syracuseStep 8451793 = 6338845) B6338845
theorem B1144667 : Blo 599292 1144667 := bstep (se 1 (by rfl) ⟨858500, by rfl⟩ : syracuseStep 1144667 = 1717001) B1717001
theorem B1013755 : Blo 599292 1013755 := bstep (se 1 (by rfl) ⟨760316, by rfl⟩ : syracuseStep 1013755 = 1520633) B1520633
theorem B1013897 : Blo 599292 1013897 := bstep (se 2 (by rfl) ⟨380211, by rfl⟩ : syracuseStep 1013897 = 760423) B760423
theorem B10287647 : Blo 599292 10287647 := bstep (se 1 (by rfl) ⟨7715735, by rfl⟩ : syracuseStep 10287647 = 15431471) B15431471
theorem B1014511 : Blo 599292 1014511 := bstep (se 1 (by rfl) ⟨760883, by rfl⟩ : syracuseStep 1014511 = 1521767) B1521767
theorem B1014815 : Blo 599292 1014815 := bstep (se 1 (by rfl) ⟨761111, by rfl⟩ : syracuseStep 1014815 = 1522223) B1522223
theorem B1441127 : Blo 599292 1441127 := bstep (se 1 (by rfl) ⟨1080845, by rfl⟩ : syracuseStep 1441127 = 2161691) B2161691
theorem B3046895 : Blo 599292 3046895 := bstep (se 1 (by rfl) ⟨2285171, by rfl⟩ : syracuseStep 3046895 = 4570343) B4570343
theorem B8781455 : Blo 599292 8781455 := bstep (se 1 (by rfl) ⟨6586091, by rfl⟩ : syracuseStep 8781455 = 13172183) B13172183
theorem B2032289 : Blo 599292 2032289 := bstep (se 2 (by rfl) ⟨762108, by rfl⟩ : syracuseStep 2032289 = 1524217) B1524217
theorem B2033153 : Blo 599292 2033153 := bstep (se 2 (by rfl) ⟨762432, by rfl⟩ : syracuseStep 2033153 = 1524865) B1524865
theorem B21989063 : Blo 599292 21989063 := bstep (se 1 (by rfl) ⟨16491797, by rfl⟩ : syracuseStep 21989063 = 32983595) B32983595
theorem B9767051 : Blo 599292 9767051 := bstep (se 1 (by rfl) ⟨7325288, by rfl⟩ : syracuseStep 9767051 = 14650577) B14650577
theorem B12717155 : Blo 599292 12717155 := bstep (se 1 (by rfl) ⟨9537866, by rfl⟩ : syracuseStep 12717155 = 19075733) B19075733
theorem B2035151 : Blo 599292 2035151 := bstep (se 1 (by rfl) ⟨1526363, by rfl⟩ : syracuseStep 2035151 = 3052727) B3052727
theorem B3247901 : Blo 599292 3247901 := bstep (se 3 (by rfl) ⟨608981, by rfl⟩ : syracuseStep 3247901 = 1217963) B1217963
theorem B3051755 : Blo 599292 3051755 := bstep (se 1 (by rfl) ⟨2288816, by rfl⟩ : syracuseStep 3051755 = 4577633) B4577633
theorem B2167199 : Blo 599292 2167199 := bstep (se 1 (by rfl) ⟨1625399, by rfl⟩ : syracuseStep 2167199 = 3250799) B3250799
theorem B4329953 : Blo 599292 4329953 := bstep (se 2 (by rfl) ⟨1623732, by rfl⟩ : syracuseStep 4329953 = 3247465) B3247465
theorem B9999389 : Blo 599292 9999389 := bstep (se 3 (by rfl) ⟨1874885, by rfl⟩ : syracuseStep 9999389 = 3749771) B3749771
theorem B1348649 : Blo 599292 1348649 := bstep (se 2 (by rfl) ⟨505743, by rfl⟩ : syracuseStep 1348649 = 1011487) B1011487
theorem B1348937 : Blo 599292 1348937 := bstep (se 2 (by rfl) ⟨505851, by rfl⟩ : syracuseStep 1348937 = 1011703) B1011703
theorem B3085823 : Blo 599292 3085823 := bstep (se 1 (by rfl) ⟨2314367, by rfl⟩ : syracuseStep 3085823 = 4628735) B4628735
theorem B3250043 : Blo 599292 3250043 := bstep (se 1 (by rfl) ⟨2437532, by rfl⟩ : syracuseStep 3250043 = 4875065) B4875065
theorem B3053537 : Blo 599292 3053537 := bstep (se 2 (by rfl) ⟨1145076, by rfl⟩ : syracuseStep 3053537 = 2290153) B2290153
theorem B3414271 : Blo 599292 3414271 := bstep (se 1 (by rfl) ⟨2560703, by rfl⟩ : syracuseStep 3414271 = 5121407) B5121407
theorem B1349927 : Blo 599292 1349927 := bstep (se 1 (by rfl) ⟨1012445, by rfl⟩ : syracuseStep 1349927 = 2024891) B2024891
theorem B1350377 : Blo 599292 1350377 := bstep (se 2 (by rfl) ⟨506391, by rfl⟩ : syracuseStep 1350377 = 1012783) B1012783
theorem B1350395 : Blo 599292 1350395 := bstep (se 1 (by rfl) ⟨1012796, by rfl⟩ : syracuseStep 1350395 = 2025593) B2025593
theorem B1710895 : Blo 599292 1710895 := bstep (se 1 (by rfl) ⟨1283171, by rfl⟩ : syracuseStep 1710895 = 2566343) B2566343
theorem B1350503 : Blo 599292 1350503 := bstep (se 1 (by rfl) ⟨1012877, by rfl⟩ : syracuseStep 1350503 = 2025755) B2025755
theorem B2169737 : Blo 599292 2169737 := bstep (se 2 (by rfl) ⟨813651, by rfl⟩ : syracuseStep 2169737 = 1627303) B1627303
theorem B1712011 : Blo 599292 1712011 := bstep (se 1 (by rfl) ⟨1284008, by rfl⟩ : syracuseStep 1712011 = 2568017) B2568017
theorem B1351673 : Blo 599292 1351673 := bstep (se 2 (by rfl) ⟨506877, by rfl⟩ : syracuseStep 1351673 = 1013755) B1013755
theorem B1351943 : Blo 599292 1351943 := bstep (se 1 (by rfl) ⟨1013957, by rfl⟩ : syracuseStep 1351943 = 2027915) B2027915
theorem B762139 : Blo 599292 762139 := bstep (se 1 (by rfl) ⟨571604, by rfl⟩ : syracuseStep 762139 = 1143209) B1143209
theorem B1352015 : Blo 599292 1352015 := bstep (se 1 (by rfl) ⟨1014011, by rfl⟩ : syracuseStep 1352015 = 2028023) B2028023
theorem B4563539 : Blo 599292 4563539 := bstep (se 1 (by rfl) ⟨3422654, by rfl⟩ : syracuseStep 4563539 = 6845309) B6845309
theorem B19538657 : Blo 599292 19538657 := bstep (se 2 (by rfl) ⟨7326996, by rfl⟩ : syracuseStep 19538657 = 14653993) B14653993
theorem B1352681 : Blo 599292 1352681 := bstep (se 2 (by rfl) ⟨507255, by rfl⟩ : syracuseStep 1352681 = 1014511) B1014511
theorem B1352735 : Blo 599292 1352735 := bstep (se 1 (by rfl) ⟨1014551, by rfl⟩ : syracuseStep 1352735 = 2029103) B2029103
theorem B763111 : Blo 599292 763111 := bstep (se 1 (by rfl) ⟨572333, by rfl⟩ : syracuseStep 763111 = 1144667) B1144667
theorem B1713595 : Blo 599292 1713595 := bstep (se 1 (by rfl) ⟨1285196, by rfl⟩ : syracuseStep 1713595 = 2570393) B2570393
theorem B6858431 : Blo 599292 6858431 := bstep (se 1 (by rfl) ⟨5143823, by rfl⟩ : syracuseStep 6858431 = 10287647) B10287647
theorem B600135 : Blo 599292 600135 := bstep (se 1 (by rfl) ⟨450101, by rfl⟩ : syracuseStep 600135 = 900203) B900203
theorem B600295 : Blo 599292 600295 := bstep (se 1 (by rfl) ⟨450221, by rfl⟩ : syracuseStep 600295 = 900443) B900443
theorem B960751 : Blo 599292 960751 := bstep (se 1 (by rfl) ⟨720563, by rfl⟩ : syracuseStep 960751 = 1441127) B1441127
theorem B600527 : Blo 599292 600527 := bstep (se 1 (by rfl) ⟨450395, by rfl⟩ : syracuseStep 600527 = 900791) B900791
theorem B600735 : Blo 599292 600735 := bstep (se 1 (by rfl) ⟨450551, by rfl⟩ : syracuseStep 600735 = 901103) B901103
theorem B928475 : Blo 599292 928475 := bstep (se 1 (by rfl) ⟨696356, by rfl⟩ : syracuseStep 928475 = 1392713) B1392713
theorem B600815 : Blo 599292 600815 := bstep (se 1 (by rfl) ⟨450611, by rfl⟩ : syracuseStep 600815 = 901223) B901223
theorem B4336411 : Blo 599292 4336411 := bstep (se 1 (by rfl) ⟨3252308, by rfl⟩ : syracuseStep 4336411 = 6504617) B6504617
theorem B1354607 : Blo 599292 1354607 := bstep (se 1 (by rfl) ⟨1015955, by rfl⟩ : syracuseStep 1354607 = 2031911) B2031911
theorem B1518527 : Blo 599292 1518527 := bstep (se 1 (by rfl) ⟨1138895, by rfl⟩ : syracuseStep 1518527 = 2277791) B2277791
theorem B6925409 : Blo 599292 6925409 := bstep (se 2 (by rfl) ⟨2597028, by rfl⟩ : syracuseStep 6925409 = 5194057) B5194057
theorem B601295 : Blo 599292 601295 := bstep (se 1 (by rfl) ⟨450971, by rfl⟩ : syracuseStep 601295 = 901943) B901943
theorem B100347113 : Blo 599292 100347113 := bstep (se 2 (by rfl) ⟨37630167, by rfl⟩ : syracuseStep 100347113 = 75260335) B75260335
theorem B601407 : Blo 599292 601407 := bstep (se 1 (by rfl) ⟨451055, by rfl⟩ : syracuseStep 601407 = 902111) B902111
theorem B601415 : Blo 599292 601415 := bstep (se 1 (by rfl) ⟨451061, by rfl⟩ : syracuseStep 601415 = 902123) B902123
theorem B6925733 : Blo 599292 6925733 := bstep (se 4 (by rfl) ⟨649287, by rfl⟩ : syracuseStep 6925733 = 1298575) B1298575
theorem B601583 : Blo 599292 601583 := bstep (se 1 (by rfl) ⟨451187, by rfl⟩ : syracuseStep 601583 = 902375) B902375
theorem B601627 : Blo 599292 601627 := bstep (se 1 (by rfl) ⟨451220, by rfl⟩ : syracuseStep 601627 = 902441) B902441
theorem B2895401 : Blo 599292 2895401 := bstep (se 2 (by rfl) ⟨1085775, by rfl⟩ : syracuseStep 2895401 = 2171551) B2171551
theorem B1159039 : Blo 599292 1159039 := bstep (se 1 (by rfl) ⟨869279, by rfl⟩ : syracuseStep 1159039 = 1738559) B1738559
theorem B602015 : Blo 599292 602015 := bstep (se 1 (by rfl) ⟨451511, by rfl⟩ : syracuseStep 602015 = 903023) B903023
theorem B602139 : Blo 599292 602139 := bstep (se 1 (by rfl) ⟨451604, by rfl⟩ : syracuseStep 602139 = 903209) B903209
theorem B42315979 : Blo 599292 42315979 := bstep (se 1 (by rfl) ⟨31736984, by rfl⟩ : syracuseStep 42315979 = 63473969) B63473969
theorem B3289673 : Blo 599292 3289673 := bstep (se 2 (by rfl) ⟨1233627, by rfl⟩ : syracuseStep 3289673 = 2467255) B2467255
theorem B21181027 : Blo 599292 21181027 := bstep (se 1 (by rfl) ⟨15885770, by rfl⟩ : syracuseStep 21181027 = 31771541) B31771541
theorem B1356479 : Blo 599292 1356479 := bstep (se 1 (by rfl) ⟨1017359, by rfl⟩ : syracuseStep 1356479 = 2034719) B2034719
theorem B602907 : Blo 599292 602907 := bstep (se 1 (by rfl) ⟨452180, by rfl⟩ : syracuseStep 602907 = 904361) B904361
theorem B1520441 : Blo 599292 1520441 := bstep (se 2 (by rfl) ⟨570165, by rfl⟩ : syracuseStep 1520441 = 1140331) B1140331
theorem B602983 : Blo 599292 602983 := bstep (se 1 (by rfl) ⟨452237, by rfl⟩ : syracuseStep 602983 = 904475) B904475
theorem B1357055 : Blo 599292 1357055 := bstep (se 1 (by rfl) ⟨1017791, by rfl⟩ : syracuseStep 1357055 = 2035583) B2035583
theorem B1357289 : Blo 599292 1357289 := bstep (se 2 (by rfl) ⟨508983, by rfl⟩ : syracuseStep 1357289 = 1017967) B1017967
theorem B899039 : Blo 599292 899039 := bstep (se 1 (by rfl) ⟨674279, by rfl⟩ : syracuseStep 899039 = 1348559) B1348559
theorem B899279 : Blo 599292 899279 := bstep (se 1 (by rfl) ⟨674459, by rfl⟩ : syracuseStep 899279 = 1348919) B1348919
theorem B899327 : Blo 599292 899327 := bstep (se 1 (by rfl) ⟨674495, by rfl⟩ : syracuseStep 899327 = 1348991) B1348991
theorem B2570615 : Blo 599292 2570615 := bstep (se 1 (by rfl) ⟨1927961, by rfl⟩ : syracuseStep 2570615 = 3855923) B3855923
theorem B899483 : Blo 599292 899483 := bstep (se 1 (by rfl) ⟨674612, by rfl⟩ : syracuseStep 899483 = 1349225) B1349225
theorem B900089 : Blo 599292 900089 := bstep (se 2 (by rfl) ⟨337533, by rfl⟩ : syracuseStep 900089 = 675067) B675067
theorem B5487689 : Blo 599292 5487689 := bstep (se 2 (by rfl) ⟨2057883, by rfl⟩ : syracuseStep 5487689 = 4115767) B4115767
theorem B900347 : Blo 599292 900347 := bstep (se 1 (by rfl) ⟨675260, by rfl⟩ : syracuseStep 900347 = 1350521) B1350521
theorem B10239533 : Blo 599292 10239533 := bstep (se 3 (by rfl) ⟨1919912, by rfl⟩ : syracuseStep 10239533 = 3839825) B3839825
theorem B1523519 : Blo 599292 1523519 := bstep (se 1 (by rfl) ⟨1142639, by rfl⟩ : syracuseStep 1523519 = 2285279) B2285279
theorem B770143 : Blo 599292 770143 := bstep (se 1 (by rfl) ⟨577607, by rfl⟩ : syracuseStep 770143 = 1155215) B1155215
theorem B901865 : Blo 599292 901865 := bstep (se 2 (by rfl) ⟨338199, by rfl⟩ : syracuseStep 901865 = 676399) B676399
theorem B5129405 : Blo 599292 5129405 := bstep (se 3 (by rfl) ⟨961763, by rfl⟩ : syracuseStep 5129405 = 1923527) B1923527
theorem B3851513 : Blo 599292 3851513 := bstep (se 2 (by rfl) ⟨1444317, by rfl⟩ : syracuseStep 3851513 = 2888635) B2888635
theorem B2279279 : Blo 599292 2279279 := bstep (se 1 (by rfl) ⟨1709459, by rfl⟩ : syracuseStep 2279279 = 3418919) B3418919
theorem B5130155 : Blo 599292 5130155 := bstep (se 1 (by rfl) ⟨3847616, by rfl⟩ : syracuseStep 5130155 = 7695233) B7695233
theorem B1525675 : Blo 599292 1525675 := bstep (se 1 (by rfl) ⟨1144256, by rfl⟩ : syracuseStep 1525675 = 2288513) B2288513
theorem B2574305 : Blo 599292 2574305 := bstep (se 2 (by rfl) ⟨965364, by rfl⟩ : syracuseStep 2574305 = 1930729) B1930729
theorem B903419 : Blo 599292 903419 := bstep (se 1 (by rfl) ⟨677564, by rfl⟩ : syracuseStep 903419 = 1355129) B1355129
theorem B674239 : Blo 599292 674239 := bstep (se 1 (by rfl) ⟨505679, by rfl⟩ : syracuseStep 674239 = 1011359) B1011359
theorem B903887 : Blo 599292 903887 := bstep (se 1 (by rfl) ⟨677915, by rfl⟩ : syracuseStep 903887 = 1355831) B1355831
theorem B2575091 : Blo 599292 2575091 := bstep (se 1 (by rfl) ⟨1931318, by rfl⟩ : syracuseStep 2575091 = 3862637) B3862637
theorem B904073 : Blo 599292 904073 := bstep (se 2 (by rfl) ⟨339027, by rfl⟩ : syracuseStep 904073 = 678055) B678055
theorem B1526971 : Blo 599292 1526971 := bstep (se 1 (by rfl) ⟨1145228, by rfl⟩ : syracuseStep 1526971 = 2290457) B2290457
theorem B4869355 : Blo 599292 4869355 := bstep (se 1 (by rfl) ⟨3652016, by rfl⟩ : syracuseStep 4869355 = 7304033) B7304033
theorem B2346367 : Blo 599292 2346367 := bstep (se 1 (by rfl) ⟨1759775, by rfl⟩ : syracuseStep 2346367 = 3519551) B3519551
theorem B3034745 : Blo 599292 3034745 := bstep (se 2 (by rfl) ⟨1138029, by rfl⟩ : syracuseStep 3034745 = 2276059) B2276059
theorem B675931 : Blo 599292 675931 := bstep (se 1 (by rfl) ⟨506948, by rfl⟩ : syracuseStep 675931 = 1013897) B1013897
theorem B6836561 : Blo 599292 6836561 := bstep (se 2 (by rfl) ⟨2563710, by rfl⟩ : syracuseStep 6836561 = 5127421) B5127421
theorem B643559 : Blo 599292 643559 := bstep (se 1 (by rfl) ⟨482669, by rfl⟩ : syracuseStep 643559 = 965339) B965339
theorem B676543 : Blo 599292 676543 := bstep (se 1 (by rfl) ⟨507407, by rfl⟩ : syracuseStep 676543 = 1014815) B1014815
theorem B1823585 : Blo 599292 1823585 := bstep (se 2 (by rfl) ⟨683844, by rfl⟩ : syracuseStep 1823585 = 1367689) B1367689
theorem B3036041 : Blo 599292 3036041 := bstep (se 2 (by rfl) ⟨1138515, by rfl⟩ : syracuseStep 3036041 = 2277031) B2277031
theorem B644123 : Blo 599292 644123 := bstep (se 1 (by rfl) ⟨483092, by rfl⟩ : syracuseStep 644123 = 966185) B966185
theorem B5854303 : Blo 599292 5854303 := bstep (se 1 (by rfl) ⟨4390727, by rfl⟩ : syracuseStep 5854303 = 8781455) B8781455
theorem B677479 : Blo 599292 677479 := bstep (se 1 (by rfl) ⟨508109, by rfl⟩ : syracuseStep 677479 = 1016219) B1016219
theorem B3430127 : Blo 599292 3430127 := bstep (se 1 (by rfl) ⟨2572595, by rfl⟩ : syracuseStep 3430127 = 5145191) B5145191
theorem B3037175 : Blo 599292 3037175 := bstep (se 1 (by rfl) ⟨2277881, by rfl⟩ : syracuseStep 3037175 = 4555763) B4555763
theorem B2284807 : Blo 599292 2284807 := bstep (se 1 (by rfl) ⟨1713605, by rfl⟩ : syracuseStep 2284807 = 3427211) B3427211
theorem B21880115 : Blo 599292 21880115 := bstep (se 1 (by rfl) ⟨16410086, by rfl⟩ : syracuseStep 21880115 = 32820173) B32820173
theorem B3431767 : Blo 599292 3431767 := bstep (se 1 (by rfl) ⟨2573825, by rfl⟩ : syracuseStep 3431767 = 5147651) B5147651
theorem B6840935 : Blo 599292 6840935 := bstep (se 1 (by rfl) ⟨5130701, by rfl⟩ : syracuseStep 6840935 = 10261403) B10261403
theorem B1139579 : Blo 599292 1139579 := bstep (se 1 (by rfl) ⟨854684, by rfl⟩ : syracuseStep 1139579 = 1709369) B1709369
theorem B1139807 : Blo 599292 1139807 := bstep (se 1 (by rfl) ⟨854855, by rfl⟩ : syracuseStep 1139807 = 1709711) B1709711
theorem B6186131 : Blo 599292 6186131 := bstep (se 1 (by rfl) ⟨4639598, by rfl⟩ : syracuseStep 6186131 = 9279197) B9279197
theorem B1140095 : Blo 599292 1140095 := bstep (se 1 (by rfl) ⟨855071, by rfl⟩ : syracuseStep 1140095 = 1710143) B1710143
theorem B3041387 : Blo 599292 3041387 := bstep (se 1 (by rfl) ⟨2281040, by rfl⟩ : syracuseStep 3041387 = 4562081) B4562081
theorem B3434683 : Blo 599292 3434683 := bstep (se 1 (by rfl) ⟨2576012, by rfl⟩ : syracuseStep 3434683 = 5152025) B5152025
theorem B1140961 : Blo 599292 1140961 := bstep (se 2 (by rfl) ⟨427860, by rfl⟩ : syracuseStep 1140961 = 855721) B855721
theorem B3041711 : Blo 599292 3041711 := bstep (se 1 (by rfl) ⟨2281283, by rfl⟩ : syracuseStep 3041711 = 4562567) B4562567
theorem B2714489 : Blo 599292 2714489 := bstep (se 2 (by rfl) ⟨1017933, by rfl⟩ : syracuseStep 2714489 = 2035867) B2035867
theorem B2288695 : Blo 599292 2288695 := bstep (se 1 (by rfl) ⟨1716521, by rfl⟩ : syracuseStep 2288695 = 3433043) B3433043
theorem B2747567 : Blo 599292 2747567 := bstep (se 1 (by rfl) ⟨2060675, by rfl⟩ : syracuseStep 2747567 = 4121351) B4121351
theorem B9760823 : Blo 599292 9760823 := bstep (se 1 (by rfl) ⟨7320617, by rfl⟩ : syracuseStep 9760823 = 14641235) B14641235
theorem B1012007 : Blo 599292 1012007 := bstep (se 1 (by rfl) ⟨759005, by rfl⟩ : syracuseStep 1012007 = 1518011) B1518011
theorem B3043817 : Blo 599292 3043817 := bstep (se 2 (by rfl) ⟨1141431, by rfl⟩ : syracuseStep 3043817 = 2282863) B2282863
theorem B6517381 : Blo 599292 6517381 := bstep (se 4 (by rfl) ⟨611004, by rfl⟩ : syracuseStep 6517381 = 1222009) B1222009
theorem B2028455 : Blo 599292 2028455 := bstep (se 1 (by rfl) ⟨1521341, by rfl⟩ : syracuseStep 2028455 = 3042683) B3042683
theorem B11269057 : Blo 599292 11269057 := bstep (se 2 (by rfl) ⟨4225896, by rfl⟩ : syracuseStep 11269057 = 8451793) B8451793
theorem B3044303 : Blo 599292 3044303 := bstep (se 1 (by rfl) ⟨2283227, by rfl⟩ : syracuseStep 3044303 = 4566455) B4566455
theorem B1012763 : Blo 599292 1012763 := bstep (se 1 (by rfl) ⟨759572, by rfl⟩ : syracuseStep 1012763 = 1519145) B1519145
theorem B2028671 : Blo 599292 2028671 := bstep (se 1 (by rfl) ⟨1521503, by rfl⟩ : syracuseStep 2028671 = 3043007) B3043007
theorem B2029319 : Blo 599292 2029319 := bstep (se 1 (by rfl) ⟨1521989, by rfl⟩ : syracuseStep 2029319 = 3043979) B3043979
theorem B1145191 : Blo 599292 1145191 := bstep (se 1 (by rfl) ⟨858893, by rfl⟩ : syracuseStep 1145191 = 1717787) B1717787
theorem B5339627 : Blo 599292 5339627 := bstep (se 1 (by rfl) ⟨4004720, by rfl⟩ : syracuseStep 5339627 = 8009441) B8009441
theorem B2162153 : Blo 599292 2162153 := bstep (se 2 (by rfl) ⟨810807, by rfl⟩ : syracuseStep 2162153 = 1621615) B1621615
theorem B2031263 : Blo 599292 2031263 := bstep (se 1 (by rfl) ⟨1523447, by rfl⟩ : syracuseStep 2031263 = 3046895) B3046895
theorem B1015787 : Blo 599292 1015787 := bstep (se 1 (by rfl) ⟨761840, by rfl⟩ : syracuseStep 1015787 = 1523681) B1523681
theorem B1016185 : Blo 599292 1016185 := bstep (se 2 (by rfl) ⟨381069, by rfl⟩ : syracuseStep 1016185 = 762139) B762139
theorem B1017481 : Blo 599292 1017481 := bstep (se 2 (by rfl) ⟨381555, by rfl⟩ : syracuseStep 1017481 = 763111) B763111
theorem B2165267 : Blo 599292 2165267 := bstep (se 1 (by rfl) ⟨1623950, by rfl⟩ : syracuseStep 2165267 = 3247901) B3247901
theorem B2034233 : Blo 599292 2034233 := bstep (se 2 (by rfl) ⟨762837, by rfl⟩ : syracuseStep 2034233 = 1525675) B1525675
theorem B2034503 : Blo 599292 2034503 := bstep (se 1 (by rfl) ⟨1525877, by rfl⟩ : syracuseStep 2034503 = 3051755) B3051755
theorem B4557707 : Blo 599292 4557707 := bstep (se 1 (by rfl) ⟨3418280, by rfl⟩ : syracuseStep 4557707 = 6836561) B6836561
theorem B1444799 : Blo 599292 1444799 := bstep (se 1 (by rfl) ⟨1083599, by rfl⟩ : syracuseStep 1444799 = 2167199) B2167199
theorem B2886635 : Blo 599292 2886635 := bstep (se 1 (by rfl) ⟨2164976, by rfl⟩ : syracuseStep 2886635 = 4329953) B4329953
theorem B2166695 : Blo 599292 2166695 := bstep (se 1 (by rfl) ⟨1625021, by rfl⟩ : syracuseStep 2166695 = 3250043) B3250043
theorem B2035691 : Blo 599292 2035691 := bstep (se 1 (by rfl) ⟨1526768, by rfl⟩ : syracuseStep 2035691 = 3053537) B3053537
theorem B8228861 : Blo 599292 8228861 := bstep (se 3 (by rfl) ⟨1542911, by rfl⟩ : syracuseStep 8228861 = 3085823) B3085823
theorem B3051593 : Blo 599292 3051593 := bstep (se 2 (by rfl) ⟨1144347, by rfl⟩ : syracuseStep 3051593 = 2288695) B2288695
theorem B2035961 : Blo 599292 2035961 := bstep (se 2 (by rfl) ⟨763485, by rfl⟩ : syracuseStep 2035961 = 1526971) B1526971
theorem B6492473 : Blo 599292 6492473 := bstep (se 2 (by rfl) ⟨2434677, by rfl⟩ : syracuseStep 6492473 = 4869355) B4869355
theorem B1446491 : Blo 599292 1446491 := bstep (se 1 (by rfl) ⟨1084868, by rfl⟩ : syracuseStep 1446491 = 2169737) B2169737
theorem B14586743 : Blo 599292 14586743 := bstep (se 1 (by rfl) ⟨10940057, by rfl⟩ : syracuseStep 14586743 = 21880115) B21880115
theorem B4560623 : Blo 599292 4560623 := bstep (se 1 (by rfl) ⟨3420467, by rfl⟩ : syracuseStep 4560623 = 6840935) B6840935
theorem B759719 : Blo 599292 759719 := bstep (se 1 (by rfl) ⟨569789, by rfl⟩ : syracuseStep 759719 = 1139579) B1139579
theorem B759871 : Blo 599292 759871 := bstep (se 1 (by rfl) ⟨569903, by rfl⟩ : syracuseStep 759871 = 1139807) B1139807
theorem B8689841 : Blo 599292 8689841 := bstep (se 2 (by rfl) ⟨3258690, by rfl⟩ : syracuseStep 8689841 = 6517381) B6517381
theorem B7805737 : Blo 599292 7805737 := bstep (se 2 (by rfl) ⟨2927151, by rfl⟩ : syracuseStep 7805737 = 5854303) B5854303
theorem B1809659 : Blo 599292 1809659 := bstep (se 1 (by rfl) ⟨1357244, by rfl⟩ : syracuseStep 1809659 = 2714489) B2714489
theorem B1352303 : Blo 599292 1352303 := bstep (se 1 (by rfl) ⟨1014227, by rfl⟩ : syracuseStep 1352303 = 2028455) B2028455
theorem B1352447 : Blo 599292 1352447 := bstep (se 1 (by rfl) ⟨1014335, by rfl⟩ : syracuseStep 1352447 = 2028671) B2028671
theorem B1352879 : Blo 599292 1352879 := bstep (se 1 (by rfl) ⟨1014659, by rfl⟩ : syracuseStep 1352879 = 2029319) B2029319
theorem B599359 : Blo 599292 599359 := bstep (se 1 (by rfl) ⟨449519, by rfl⟩ : syracuseStep 599359 = 899039) B899039
theorem B599519 : Blo 599292 599519 := bstep (se 1 (by rfl) ⟨449639, by rfl⟩ : syracuseStep 599519 = 899279) B899279
theorem B599551 : Blo 599292 599551 := bstep (se 1 (by rfl) ⟨449663, by rfl⟩ : syracuseStep 599551 = 899327) B899327
theorem B1713743 : Blo 599292 1713743 := bstep (se 1 (by rfl) ⟨1285307, by rfl⟩ : syracuseStep 1713743 = 2570615) B2570615
theorem B599655 : Blo 599292 599655 := bstep (se 1 (by rfl) ⟨449741, by rfl⟩ : syracuseStep 599655 = 899483) B899483
theorem B600059 : Blo 599292 600059 := bstep (se 1 (by rfl) ⟨450044, by rfl⟩ : syracuseStep 600059 = 900089) B900089
theorem B600231 : Blo 599292 600231 := bstep (se 1 (by rfl) ⟨450173, by rfl⟩ : syracuseStep 600231 = 900347) B900347
theorem B6826355 : Blo 599292 6826355 := bstep (se 1 (by rfl) ⟨5119766, by rfl⟩ : syracuseStep 6826355 = 10239533) B10239533
theorem B1354175 : Blo 599292 1354175 := bstep (se 1 (by rfl) ⟨1015631, by rfl⟩ : syracuseStep 1354175 = 2031263) B2031263
theorem B1026857 : Blo 599292 1026857 := bstep (se 2 (by rfl) ⟨385071, by rfl⟩ : syracuseStep 1026857 = 770143) B770143
theorem B1354859 : Blo 599292 1354859 := bstep (se 1 (by rfl) ⟨1016144, by rfl⟩ : syracuseStep 1354859 = 2032289) B2032289
theorem B601243 : Blo 599292 601243 := bstep (se 1 (by rfl) ⟨450932, by rfl⟩ : syracuseStep 601243 = 901865) B901865
theorem B3419603 : Blo 599292 3419603 := bstep (se 1 (by rfl) ⟨2564702, by rfl⟩ : syracuseStep 3419603 = 5129405) B5129405
theorem B2567675 : Blo 599292 2567675 := bstep (se 1 (by rfl) ⟨1925756, by rfl⟩ : syracuseStep 2567675 = 3851513) B3851513
theorem B1355435 : Blo 599292 1355435 := bstep (se 1 (by rfl) ⟨1016576, by rfl⟩ : syracuseStep 1355435 = 2033153) B2033153
theorem B14659375 : Blo 599292 14659375 := bstep (se 1 (by rfl) ⟨10994531, by rfl⟩ : syracuseStep 14659375 = 21989063) B21989063
theorem B1519519 : Blo 599292 1519519 := bstep (se 1 (by rfl) ⟨1139639, by rfl⟩ : syracuseStep 1519519 = 2279279) B2279279
theorem B5124005 : Blo 599292 5124005 := bstep (se 4 (by rfl) ⟨480375, by rfl⟩ : syracuseStep 5124005 = 960751) B960751
theorem B1716157 : Blo 599292 1716157 := bstep (se 3 (by rfl) ⟨321779, by rfl⟩ : syracuseStep 1716157 = 643559) B643559
theorem B3420103 : Blo 599292 3420103 := bstep (se 1 (by rfl) ⟨2565077, by rfl⟩ : syracuseStep 3420103 = 5130155) B5130155
theorem B1716203 : Blo 599292 1716203 := bstep (se 1 (by rfl) ⟨1287152, by rfl⟩ : syracuseStep 1716203 = 2574305) B2574305
theorem B602279 : Blo 599292 602279 := bstep (se 1 (by rfl) ⟨451709, by rfl⟩ : syracuseStep 602279 = 903419) B903419
theorem B602591 : Blo 599292 602591 := bstep (se 1 (by rfl) ⟨451943, by rfl⟩ : syracuseStep 602591 = 903887) B903887
theorem B1716727 : Blo 599292 1716727 := bstep (se 1 (by rfl) ⟨1287545, by rfl⟩ : syracuseStep 1716727 = 2575091) B2575091
theorem B602715 : Blo 599292 602715 := bstep (se 1 (by rfl) ⟨452036, by rfl⟩ : syracuseStep 602715 = 904073) B904073
theorem B1356767 : Blo 599292 1356767 := bstep (se 1 (by rfl) ⟨1017575, by rfl⟩ : syracuseStep 1356767 = 2035151) B2035151
theorem B1717661 : Blo 599292 1717661 := bstep (se 3 (by rfl) ⟨322061, by rfl⟩ : syracuseStep 1717661 = 644123) B644123
theorem B1521281 : Blo 599292 1521281 := bstep (se 2 (by rfl) ⟨570480, by rfl⟩ : syracuseStep 1521281 = 1140961) B1140961
theorem B898985 : Blo 599292 898985 := bstep (se 2 (by rfl) ⟨337119, by rfl⟩ : syracuseStep 898985 = 674239) B674239
theorem B6666259 : Blo 599292 6666259 := bstep (se 1 (by rfl) ⟨4999694, by rfl⟩ : syracuseStep 6666259 = 9999389) B9999389
theorem B899099 : Blo 599292 899099 := bstep (se 1 (by rfl) ⟨674324, by rfl⟩ : syracuseStep 899099 = 1348649) B1348649
theorem B899291 : Blo 599292 899291 := bstep (se 1 (by rfl) ⟨674468, by rfl⟩ : syracuseStep 899291 = 1348937) B1348937
theorem B5781881 : Blo 599292 5781881 := bstep (se 2 (by rfl) ⟨2168205, by rfl⟩ : syracuseStep 5781881 = 4336411) B4336411
theorem B899951 : Blo 599292 899951 := bstep (se 1 (by rfl) ⟨674963, by rfl⟩ : syracuseStep 899951 = 1349927) B1349927
theorem B900251 : Blo 599292 900251 := bstep (se 1 (by rfl) ⟨675188, by rfl⟩ : syracuseStep 900251 = 1350377) B1350377
theorem B900263 : Blo 599292 900263 := bstep (se 1 (by rfl) ⟨675197, by rfl⟩ : syracuseStep 900263 = 1350395) B1350395
theorem B3128489 : Blo 599292 3128489 := bstep (se 2 (by rfl) ⟨1173183, by rfl⟩ : syracuseStep 3128489 = 2346367) B2346367
theorem B900335 : Blo 599292 900335 := bstep (se 1 (by rfl) ⟨675251, by rfl⟩ : syracuseStep 900335 = 1350503) B1350503
theorem B901115 : Blo 599292 901115 := bstep (se 1 (by rfl) ⟨675836, by rfl⟩ : syracuseStep 901115 = 1351673) B1351673
theorem B901241 : Blo 599292 901241 := bstep (se 2 (by rfl) ⟨337965, by rfl⟩ : syracuseStep 901241 = 675931) B675931
theorem B901295 : Blo 599292 901295 := bstep (se 1 (by rfl) ⟨675971, by rfl⟩ : syracuseStep 901295 = 1351943) B1351943
theorem B901343 : Blo 599292 901343 := bstep (se 1 (by rfl) ⟨676007, by rfl⟩ : syracuseStep 901343 = 1352015) B1352015
theorem B13025771 : Blo 599292 13025771 := bstep (se 1 (by rfl) ⟨9769328, by rfl⟩ : syracuseStep 13025771 = 19538657) B19538657
theorem B901787 : Blo 599292 901787 := bstep (se 1 (by rfl) ⟨676340, by rfl⟩ : syracuseStep 901787 = 1352681) B1352681
theorem B901823 : Blo 599292 901823 := bstep (se 1 (by rfl) ⟨676367, by rfl⟩ : syracuseStep 901823 = 1352735) B1352735
theorem B902057 : Blo 599292 902057 := bstep (se 2 (by rfl) ⟨338271, by rfl⟩ : syracuseStep 902057 = 676543) B676543
theorem B4572287 : Blo 599292 4572287 := bstep (se 1 (by rfl) ⟨3429215, by rfl⟩ : syracuseStep 4572287 = 6858431) B6858431
theorem B15025409 : Blo 599292 15025409 := bstep (se 2 (by rfl) ⟨5634528, by rfl⟩ : syracuseStep 15025409 = 11269057) B11269057
theorem B903071 : Blo 599292 903071 := bstep (se 1 (by rfl) ⟨677303, by rfl⟩ : syracuseStep 903071 = 1354607) B1354607
theorem B903305 : Blo 599292 903305 := bstep (se 2 (by rfl) ⟨338739, by rfl⟩ : syracuseStep 903305 = 677479) B677479
theorem B66898075 : Blo 599292 66898075 := bstep (se 1 (by rfl) ⟨50173556, by rfl⟩ : syracuseStep 66898075 = 100347113) B100347113
theorem B6507215 : Blo 599292 6507215 := bstep (se 1 (by rfl) ⟨4880411, by rfl⟩ : syracuseStep 6507215 = 9760823) B9760823
theorem B674671 : Blo 599292 674671 := bstep (se 1 (by rfl) ⟨506003, by rfl⟩ : syracuseStep 674671 = 1012007) B1012007
theorem B7326845 : Blo 599292 7326845 := bstep (se 3 (by rfl) ⟨1373783, by rfl⟩ : syracuseStep 7326845 = 2747567) B2747567
theorem B904319 : Blo 599292 904319 := bstep (se 1 (by rfl) ⟨678239, by rfl⟩ : syracuseStep 904319 = 1356479) B1356479
theorem B1526921 : Blo 599292 1526921 := bstep (se 2 (by rfl) ⟨572595, by rfl⟩ : syracuseStep 1526921 = 1145191) B1145191
theorem B675175 : Blo 599292 675175 := bstep (se 1 (by rfl) ⟨506381, by rfl⟩ : syracuseStep 675175 = 1012763) B1012763
theorem B904703 : Blo 599292 904703 := bstep (se 1 (by rfl) ⟨678527, by rfl⟩ : syracuseStep 904703 = 1357055) B1357055
theorem B904859 : Blo 599292 904859 := bstep (se 1 (by rfl) ⟨678644, by rfl⟩ : syracuseStep 904859 = 1357289) B1357289
theorem B19451573 : Blo 599292 19451573 := bstep (se 5 (by rfl) ⟨911792, by rfl⟩ : syracuseStep 19451573 = 1823585) B1823585
theorem B2281193 : Blo 599292 2281193 := bstep (se 2 (by rfl) ⟨855447, by rfl⟩ : syracuseStep 2281193 = 1710895) B1710895
theorem B3559751 : Blo 599292 3559751 := bstep (se 1 (by rfl) ⟨2669813, by rfl⟩ : syracuseStep 3559751 = 5339627) B5339627
theorem B4575689 : Blo 599292 4575689 := bstep (se 2 (by rfl) ⟨1715883, by rfl⟩ : syracuseStep 4575689 = 3431767) B3431767
theorem B6181541 : Blo 599292 6181541 := bstep (se 4 (by rfl) ⟨579519, by rfl⟩ : syracuseStep 6181541 = 1159039) B1159039
theorem B3658459 : Blo 599292 3658459 := bstep (se 1 (by rfl) ⟨2743844, by rfl⟩ : syracuseStep 3658459 = 5487689) B5487689
theorem B2282681 : Blo 599292 2282681 := bstep (se 2 (by rfl) ⟨856005, by rfl⟩ : syracuseStep 2282681 = 1712011) B1712011
theorem B677191 : Blo 599292 677191 := bstep (se 1 (by rfl) ⟨507893, by rfl⟩ : syracuseStep 677191 = 1015787) B1015787
theorem B6511367 : Blo 599292 6511367 := bstep (se 1 (by rfl) ⟨4883525, by rfl⟩ : syracuseStep 6511367 = 9767051) B9767051
theorem B2284793 : Blo 599292 2284793 := bstep (se 2 (by rfl) ⟨856797, by rfl⟩ : syracuseStep 2284793 = 1713595) B1713595
theorem B8478103 : Blo 599292 8478103 := bstep (se 1 (by rfl) ⟨6358577, by rfl⟩ : syracuseStep 8478103 = 12717155) B12717155
theorem B2023163 : Blo 599292 2023163 := bstep (se 1 (by rfl) ⟨1517372, by rfl⟩ : syracuseStep 2023163 = 3034745) B3034745
theorem B4579577 : Blo 599292 4579577 := bstep (se 2 (by rfl) ⟨1717341, by rfl⟩ : syracuseStep 4579577 = 3434683) B3434683
theorem B2024027 : Blo 599292 2024027 := bstep (se 1 (by rfl) ⟨1518020, by rfl⟩ : syracuseStep 2024027 = 3036041) B3036041
theorem B3040253 : Blo 599292 3040253 := bstep (se 3 (by rfl) ⟨570047, by rfl⟩ : syracuseStep 3040253 = 1140095) B1140095
theorem B2286751 : Blo 599292 2286751 := bstep (se 1 (by rfl) ⟨1715063, by rfl⟩ : syracuseStep 2286751 = 3430127) B3430127
theorem B2024783 : Blo 599292 2024783 := bstep (se 1 (by rfl) ⟨1518587, by rfl⟩ : syracuseStep 2024783 = 3037175) B3037175
theorem B56421305 : Blo 599292 56421305 := bstep (se 2 (by rfl) ⟨21157989, by rfl⟩ : syracuseStep 56421305 = 42315979) B42315979
theorem B3042359 : Blo 599292 3042359 := bstep (se 1 (by rfl) ⟨2281769, by rfl⟩ : syracuseStep 3042359 = 4563539) B4563539
theorem B4124087 : Blo 599292 4124087 := bstep (se 1 (by rfl) ⟨3093065, by rfl⟩ : syracuseStep 4124087 = 6186131) B6186131
theorem B28241369 : Blo 599292 28241369 := bstep (se 2 (by rfl) ⟨10590513, by rfl⟩ : syracuseStep 28241369 = 21181027) B21181027
theorem B2027591 : Blo 599292 2027591 := bstep (se 1 (by rfl) ⟨1520693, by rfl⟩ : syracuseStep 2027591 = 3041387) B3041387
theorem B2027807 : Blo 599292 2027807 := bstep (se 1 (by rfl) ⟨1520855, by rfl⟩ : syracuseStep 2027807 = 3041711) B3041711
theorem B618983 : Blo 599292 618983 := bstep (se 1 (by rfl) ⟨464237, by rfl⟩ : syracuseStep 618983 = 928475) B928475
theorem B1012351 : Blo 599292 1012351 := bstep (se 1 (by rfl) ⟨759263, by rfl⟩ : syracuseStep 1012351 = 1518527) B1518527
theorem B4616939 : Blo 599292 4616939 := bstep (se 1 (by rfl) ⟨3462704, by rfl⟩ : syracuseStep 4616939 = 6925409) B6925409
theorem B4617155 : Blo 599292 4617155 := bstep (se 1 (by rfl) ⟨3462866, by rfl⟩ : syracuseStep 4617155 = 6925733) B6925733
theorem B1930267 : Blo 599292 1930267 := bstep (se 1 (by rfl) ⟨1447700, by rfl⟩ : syracuseStep 1930267 = 2895401) B2895401
theorem B2029211 : Blo 599292 2029211 := bstep (se 1 (by rfl) ⟨1521908, by rfl⟩ : syracuseStep 2029211 = 3043817) B3043817
theorem B4552361 : Blo 599292 4552361 := bstep (se 2 (by rfl) ⟨1707135, by rfl⟩ : syracuseStep 4552361 = 3414271) B3414271
theorem B2193115 : Blo 599292 2193115 := bstep (se 1 (by rfl) ⟨1644836, by rfl⟩ : syracuseStep 2193115 = 3289673) B3289673
theorem B1013627 : Blo 599292 1013627 := bstep (se 1 (by rfl) ⟨760220, by rfl⟩ : syracuseStep 1013627 = 1520441) B1520441
theorem B2029535 : Blo 599292 2029535 := bstep (se 1 (by rfl) ⟨1522151, by rfl⟩ : syracuseStep 2029535 = 3044303) B3044303
theorem B3046409 : Blo 599292 3046409 := bstep (se 2 (by rfl) ⟨1142403, by rfl⟩ : syracuseStep 3046409 = 2284807) B2284807
theorem B1441435 : Blo 599292 1441435 := bstep (se 1 (by rfl) ⟨1081076, by rfl⟩ : syracuseStep 1441435 = 2162153) B2162153
theorem B1015679 : Blo 599292 1015679 := bstep (se 1 (by rfl) ⟨761759, by rfl⟩ : syracuseStep 1015679 = 1523519) B1523519
theorem B8683847 : Blo 599292 8683847 := bstep (se 1 (by rfl) ⟨6512885, by rfl⟩ : syracuseStep 8683847 = 13025771) B13025771
theorem B3048191 : Blo 599292 3048191 := bstep (se 1 (by rfl) ⟨2286143, by rfl⟩ : syracuseStep 3048191 = 4572287) B4572287
theorem B3049001 : Blo 599292 3049001 := bstep (se 2 (by rfl) ⟨1143375, by rfl⟩ : syracuseStep 3049001 = 2286751) B2286751
theorem B1443511 : Blo 599292 1443511 := bstep (se 1 (by rfl) ⟨1082633, by rfl⟩ : syracuseStep 1443511 = 2165267) B2165267
theorem B4884563 : Blo 599292 4884563 := bstep (se 1 (by rfl) ⟨3663422, by rfl⟩ : syracuseStep 4884563 = 7326845) B7326845
theorem B1017947 : Blo 599292 1017947 := bstep (se 1 (by rfl) ⟨763460, by rfl⟩ : syracuseStep 1017947 = 1526921) B1526921
theorem B1444463 : Blo 599292 1444463 := bstep (se 1 (by rfl) ⟨1083347, by rfl⟩ : syracuseStep 1444463 = 2166695) B2166695
theorem B2034395 : Blo 599292 2034395 := bstep (se 1 (by rfl) ⟨1525796, by rfl⟩ : syracuseStep 2034395 = 3051593) B3051593
theorem B89197433 : Blo 599292 89197433 := bstep (se 2 (by rfl) ⟨33449037, by rfl⟩ : syracuseStep 89197433 = 66898075) B66898075
theorem B4328315 : Blo 599292 4328315 := bstep (se 1 (by rfl) ⟨3246236, by rfl⟩ : syracuseStep 4328315 = 6492473) B6492473
theorem B3050459 : Blo 599292 3050459 := bstep (se 1 (by rfl) ⟨2287844, by rfl⟩ : syracuseStep 3050459 = 4575689) B4575689
theorem B1348775 : Blo 599292 1348775 := bstep (se 1 (by rfl) ⟨1011581, by rfl⟩ : syracuseStep 1348775 = 2023163) B2023163
theorem B4560137 : Blo 599292 4560137 := bstep (se 2 (by rfl) ⟨1710051, by rfl⟩ : syracuseStep 4560137 = 3420103) B3420103
theorem B3053051 : Blo 599292 3053051 := bstep (se 1 (by rfl) ⟨2289788, by rfl⟩ : syracuseStep 3053051 = 4579577) B4579577
theorem B1349351 : Blo 599292 1349351 := bstep (se 1 (by rfl) ⟨1012013, by rfl⟩ : syracuseStep 1349351 = 2024027) B2024027
theorem B1349801 : Blo 599292 1349801 := bstep (se 2 (by rfl) ⟨506175, by rfl⟩ : syracuseStep 1349801 = 1012351) B1012351
theorem B1349855 : Blo 599292 1349855 := bstep (se 1 (by rfl) ⟨1012391, by rfl⟩ : syracuseStep 1349855 = 2024783) B2024783
theorem B2924153 : Blo 599292 2924153 := bstep (se 2 (by rfl) ⟨1096557, by rfl⟩ : syracuseStep 2924153 = 2193115) B2193115
theorem B1711783 : Blo 599292 1711783 := bstep (se 1 (by rfl) ⟨1283837, by rfl⟩ : syracuseStep 1711783 = 2567675) B2567675
theorem B3416003 : Blo 599292 3416003 := bstep (se 1 (by rfl) ⟨2562002, by rfl⟩ : syracuseStep 3416003 = 5124005) B5124005
theorem B8888345 : Blo 599292 8888345 := bstep (se 2 (by rfl) ⟨3333129, by rfl⟩ : syracuseStep 8888345 = 6666259) B6666259
theorem B1351727 : Blo 599292 1351727 := bstep (se 1 (by rfl) ⟨1013795, by rfl⟩ : syracuseStep 1351727 = 2027591) B2027591
theorem B1351871 : Blo 599292 1351871 := bstep (se 1 (by rfl) ⟨1013903, by rfl⟩ : syracuseStep 1351871 = 2027807) B2027807
theorem B4825757 : Blo 599292 4825757 := bstep (se 3 (by rfl) ⟨904829, by rfl⟩ : syracuseStep 4825757 = 1809659) B1809659
theorem B1352807 : Blo 599292 1352807 := bstep (se 1 (by rfl) ⟨1014605, by rfl⟩ : syracuseStep 1352807 = 2029211) B2029211
theorem B599323 : Blo 599292 599323 := bstep (se 1 (by rfl) ⟨449492, by rfl⟩ : syracuseStep 599323 = 898985) B898985
theorem B1353023 : Blo 599292 1353023 := bstep (se 1 (by rfl) ⟨1014767, by rfl⟩ : syracuseStep 1353023 = 2029535) B2029535
theorem B599399 : Blo 599292 599399 := bstep (se 1 (by rfl) ⟨449549, by rfl⟩ : syracuseStep 599399 = 899099) B899099
theorem B599527 : Blo 599292 599527 := bstep (se 1 (by rfl) ⟨449645, by rfl⟩ : syracuseStep 599527 = 899291) B899291
theorem B599967 : Blo 599292 599967 := bstep (se 1 (by rfl) ⟨449975, by rfl⟩ : syracuseStep 599967 = 899951) B899951
theorem B600167 : Blo 599292 600167 := bstep (se 1 (by rfl) ⟨450125, by rfl⟩ : syracuseStep 600167 = 900251) B900251
theorem B600175 : Blo 599292 600175 := bstep (se 1 (by rfl) ⟨450131, by rfl⟩ : syracuseStep 600175 = 900263) B900263
theorem B600223 : Blo 599292 600223 := bstep (se 1 (by rfl) ⟨450167, by rfl⟩ : syracuseStep 600223 = 900335) B900335
theorem B600743 : Blo 599292 600743 := bstep (se 1 (by rfl) ⟨450557, by rfl⟩ : syracuseStep 600743 = 901115) B901115
theorem B600827 : Blo 599292 600827 := bstep (se 1 (by rfl) ⟨450620, by rfl⟩ : syracuseStep 600827 = 901241) B901241
theorem B600863 : Blo 599292 600863 := bstep (se 1 (by rfl) ⟨450647, by rfl⟩ : syracuseStep 600863 = 901295) B901295
theorem B600895 : Blo 599292 600895 := bstep (se 1 (by rfl) ⟨450671, by rfl⟩ : syracuseStep 600895 = 901343) B901343
theorem B601191 : Blo 599292 601191 := bstep (se 1 (by rfl) ⟨450893, by rfl⟩ : syracuseStep 601191 = 901787) B901787
theorem B601215 : Blo 599292 601215 := bstep (se 1 (by rfl) ⟨450911, by rfl⟩ : syracuseStep 601215 = 901823) B901823
theorem B1354913 : Blo 599292 1354913 := bstep (se 2 (by rfl) ⟨508092, by rfl⟩ : syracuseStep 1354913 = 1016185) B1016185
theorem B601371 : Blo 599292 601371 := bstep (se 1 (by rfl) ⟨451028, by rfl⟩ : syracuseStep 601371 = 902057) B902057
theorem B602047 : Blo 599292 602047 := bstep (se 1 (by rfl) ⟨451535, by rfl⟩ : syracuseStep 602047 = 903071) B903071
theorem B602203 : Blo 599292 602203 := bstep (se 1 (by rfl) ⟨451652, by rfl⟩ : syracuseStep 602203 = 903305) B903305
theorem B1356155 : Blo 599292 1356155 := bstep (se 1 (by rfl) ⟨1017116, by rfl⟩ : syracuseStep 1356155 = 2034233) B2034233
theorem B4338143 : Blo 599292 4338143 := bstep (se 1 (by rfl) ⟨3253607, by rfl⟩ : syracuseStep 4338143 = 6507215) B6507215
theorem B1356335 : Blo 599292 1356335 := bstep (se 1 (by rfl) ⟨1017251, by rfl⟩ : syracuseStep 1356335 = 2034503) B2034503
theorem B963199 : Blo 599292 963199 := bstep (se 1 (by rfl) ⟨722399, by rfl⟩ : syracuseStep 963199 = 1444799) B1444799
theorem B602879 : Blo 599292 602879 := bstep (se 1 (by rfl) ⟨452159, by rfl⟩ : syracuseStep 602879 = 904319) B904319
theorem B1356641 : Blo 599292 1356641 := bstep (se 2 (by rfl) ⟨508740, by rfl⟩ : syracuseStep 1356641 = 1017481) B1017481
theorem B603135 : Blo 599292 603135 := bstep (se 1 (by rfl) ⟨452351, by rfl⟩ : syracuseStep 603135 = 904703) B904703
theorem B603239 : Blo 599292 603239 := bstep (se 1 (by rfl) ⟨452429, by rfl⟩ : syracuseStep 603239 = 904859) B904859
theorem B1520795 : Blo 599292 1520795 := bstep (se 1 (by rfl) ⟨1140596, by rfl⟩ : syracuseStep 1520795 = 2281193) B2281193
theorem B1357127 : Blo 599292 1357127 := bstep (se 1 (by rfl) ⟨1017845, by rfl⟩ : syracuseStep 1357127 = 2035691) B2035691
theorem B5485907 : Blo 599292 5485907 := bstep (se 1 (by rfl) ⟨4114430, by rfl⟩ : syracuseStep 5485907 = 8228861) B8228861
theorem B1357307 : Blo 599292 1357307 := bstep (se 1 (by rfl) ⟨1017980, by rfl⟩ : syracuseStep 1357307 = 2035961) B2035961
theorem B2373167 : Blo 599292 2373167 := bstep (se 1 (by rfl) ⟨1779875, by rfl⟩ : syracuseStep 2373167 = 3559751) B3559751
theorem B964327 : Blo 599292 964327 := bstep (se 1 (by rfl) ⟨723245, by rfl⟩ : syracuseStep 964327 = 1446491) B1446491
theorem B1521787 : Blo 599292 1521787 := bstep (se 1 (by rfl) ⟨1141340, by rfl⟩ : syracuseStep 1521787 = 2282681) B2282681
theorem B899561 : Blo 599292 899561 := bstep (se 2 (by rfl) ⟨337335, by rfl⟩ : syracuseStep 899561 = 674671) B674671
theorem B900233 : Blo 599292 900233 := bstep (se 2 (by rfl) ⟨337587, by rfl⟩ : syracuseStep 900233 = 675175) B675175
theorem B4340911 : Blo 599292 4340911 := bstep (se 1 (by rfl) ⟨3255683, by rfl⟩ : syracuseStep 4340911 = 6511367) B6511367
theorem B1523195 : Blo 599292 1523195 := bstep (se 1 (by rfl) ⟨1142396, by rfl⟩ : syracuseStep 1523195 = 2284793) B2284793
theorem B19545833 : Blo 599292 19545833 := bstep (se 2 (by rfl) ⟨7329687, by rfl⟩ : syracuseStep 19545833 = 14659375) B14659375
theorem B6602485 : Blo 599292 6602485 := bstep (se 5 (by rfl) ⟨309491, by rfl⟩ : syracuseStep 6602485 = 618983) B618983
theorem B901535 : Blo 599292 901535 := bstep (se 1 (by rfl) ⟨676151, by rfl⟩ : syracuseStep 901535 = 1352303) B1352303
theorem B901631 : Blo 599292 901631 := bstep (se 1 (by rfl) ⟨676223, by rfl⟩ : syracuseStep 901631 = 1352447) B1352447
theorem B901919 : Blo 599292 901919 := bstep (se 1 (by rfl) ⟨676439, by rfl⟩ : syracuseStep 901919 = 1352879) B1352879
theorem B15418349 : Blo 599292 15418349 := bstep (se 3 (by rfl) ⟨2890940, by rfl⟩ : syracuseStep 15418349 = 5781881) B5781881
theorem B2573689 : Blo 599292 2573689 := bstep (se 2 (by rfl) ⟨965133, by rfl⟩ : syracuseStep 2573689 = 1930267) B1930267
theorem B902783 : Blo 599292 902783 := bstep (se 1 (by rfl) ⟨677087, by rfl⟩ : syracuseStep 902783 = 1354175) B1354175
theorem B902921 : Blo 599292 902921 := bstep (se 2 (by rfl) ⟨338595, by rfl⟩ : syracuseStep 902921 = 677191) B677191
theorem B903239 : Blo 599292 903239 := bstep (se 1 (by rfl) ⟨677429, by rfl⟩ : syracuseStep 903239 = 1354859) B1354859
theorem B2738285 : Blo 599292 2738285 := bstep (se 3 (by rfl) ⟨513428, by rfl⟩ : syracuseStep 2738285 = 1026857) B1026857
theorem B2279735 : Blo 599292 2279735 := bstep (se 1 (by rfl) ⟨1709801, by rfl⟩ : syracuseStep 2279735 = 3419603) B3419603
theorem B18827579 : Blo 599292 18827579 := bstep (se 1 (by rfl) ⟨14120684, by rfl⟩ : syracuseStep 18827579 = 28241369) B28241369
theorem B903623 : Blo 599292 903623 := bstep (se 1 (by rfl) ⟨677717, by rfl⟩ : syracuseStep 903623 = 1355435) B1355435
theorem B904511 : Blo 599292 904511 := bstep (se 1 (by rfl) ⟨678383, by rfl⟩ : syracuseStep 904511 = 1356767) B1356767
theorem B10407649 : Blo 599292 10407649 := bstep (se 2 (by rfl) ⟨3902868, by rfl⟩ : syracuseStep 10407649 = 7805737) B7805737
theorem B3034907 : Blo 599292 3034907 := bstep (se 1 (by rfl) ⟨2276180, by rfl⟩ : syracuseStep 3034907 = 4552361) B4552361
theorem B675751 : Blo 599292 675751 := bstep (se 1 (by rfl) ⟨506813, by rfl⟩ : syracuseStep 675751 = 1013627) B1013627
theorem B2085659 : Blo 599292 2085659 := bstep (se 1 (by rfl) ⟨1564244, by rfl⟩ : syracuseStep 2085659 = 3128489) B3128489
theorem B1921913 : Blo 599292 1921913 := bstep (se 2 (by rfl) ⟨720717, by rfl⟩ : syracuseStep 1921913 = 1441435) B1441435
theorem B677119 : Blo 599292 677119 := bstep (se 1 (by rfl) ⟨507839, by rfl⟩ : syracuseStep 677119 = 1015679) B1015679
theorem B10016939 : Blo 599292 10016939 := bstep (se 1 (by rfl) ⟨7512704, by rfl⟩ : syracuseStep 10016939 = 15025409) B15025409
theorem B3038471 : Blo 599292 3038471 := bstep (se 1 (by rfl) ⟨2278853, by rfl⟩ : syracuseStep 3038471 = 4557707) B4557707
theorem B12967715 : Blo 599292 12967715 := bstep (se 1 (by rfl) ⟨9725786, by rfl⟩ : syracuseStep 12967715 = 19451573) B19451573
theorem B4121027 : Blo 599292 4121027 := bstep (se 1 (by rfl) ⟨3090770, by rfl⟩ : syracuseStep 4121027 = 6181541) B6181541
theorem B9724495 : Blo 599292 9724495 := bstep (se 1 (by rfl) ⟨7293371, by rfl⟩ : syracuseStep 9724495 = 14586743) B14586743
theorem B3040415 : Blo 599292 3040415 := bstep (se 1 (by rfl) ⟨2280311, by rfl⟩ : syracuseStep 3040415 = 4560623) B4560623
theorem B5793227 : Blo 599292 5793227 := bstep (se 1 (by rfl) ⟨4344920, by rfl⟩ : syracuseStep 5793227 = 8689841) B8689841
theorem B2025917 : Blo 599292 2025917 := bstep (se 3 (by rfl) ⟨379859, by rfl⟩ : syracuseStep 2025917 = 759719) B759719
theorem B2026025 : Blo 599292 2026025 := bstep (se 2 (by rfl) ⟨759759, by rfl⟩ : syracuseStep 2026025 = 1519519) B1519519
theorem B2288209 : Blo 599292 2288209 := bstep (se 2 (by rfl) ⟨858078, by rfl⟩ : syracuseStep 2288209 = 1716157) B1716157
theorem B2288969 : Blo 599292 2288969 := bstep (se 2 (by rfl) ⟨858363, by rfl⟩ : syracuseStep 2288969 = 1716727) B1716727
theorem B2026835 : Blo 599292 2026835 := bstep (se 1 (by rfl) ⟨1520126, by rfl⟩ : syracuseStep 2026835 = 3040253) B3040253
theorem B4877945 : Blo 599292 4877945 := bstep (se 2 (by rfl) ⟨1829229, by rfl⟩ : syracuseStep 4877945 = 3658459) B3658459
theorem B1142495 : Blo 599292 1142495 := bstep (se 1 (by rfl) ⟨856871, by rfl⟩ : syracuseStep 1142495 = 1713743) B1713743
theorem B4550903 : Blo 599292 4550903 := bstep (se 1 (by rfl) ⟨3413177, by rfl⟩ : syracuseStep 4550903 = 6826355) B6826355
theorem B37614203 : Blo 599292 37614203 := bstep (se 1 (by rfl) ⟨28210652, by rfl⟩ : syracuseStep 37614203 = 56421305) B56421305
theorem B2028239 : Blo 599292 2028239 := bstep (se 1 (by rfl) ⟨1521179, by rfl⟩ : syracuseStep 2028239 = 3042359) B3042359
theorem B2749391 : Blo 599292 2749391 := bstep (se 1 (by rfl) ⟨2062043, by rfl⟩ : syracuseStep 2749391 = 4124087) B4124087
theorem B7697693 : Blo 599292 7697693 := bstep (se 3 (by rfl) ⟨1443317, by rfl⟩ : syracuseStep 7697693 = 2886635) B2886635
theorem B1144135 : Blo 599292 1144135 := bstep (se 1 (by rfl) ⟨858101, by rfl⟩ : syracuseStep 1144135 = 1716203) B1716203
theorem B1013161 : Blo 599292 1013161 := bstep (se 2 (by rfl) ⟨379935, by rfl⟩ : syracuseStep 1013161 = 759871) B759871
theorem B3077959 : Blo 599292 3077959 := bstep (se 1 (by rfl) ⟨2308469, by rfl⟩ : syracuseStep 3077959 = 4616939) B4616939
theorem B3078103 : Blo 599292 3078103 := bstep (se 1 (by rfl) ⟨2308577, by rfl⟩ : syracuseStep 3078103 = 4617155) B4617155
theorem B1145107 : Blo 599292 1145107 := bstep (se 1 (by rfl) ⟨858830, by rfl⟩ : syracuseStep 1145107 = 1717661) B1717661
theorem B1014187 : Blo 599292 1014187 := bstep (se 1 (by rfl) ⟨760640, by rfl⟩ : syracuseStep 1014187 = 1521281) B1521281
theorem B11304137 : Blo 599292 11304137 := bstep (se 2 (by rfl) ⟨4239051, by rfl⟩ : syracuseStep 11304137 = 8478103) B8478103
theorem B2030939 : Blo 599292 2030939 := bstep (se 1 (by rfl) ⟨1523204, by rfl⟩ : syracuseStep 2030939 = 3046409) B3046409
theorem B2032127 : Blo 599292 2032127 := bstep (se 1 (by rfl) ⟨1524095, by rfl⟩ : syracuseStep 2032127 = 3048191) B3048191
theorem B2032667 : Blo 599292 2032667 := bstep (se 1 (by rfl) ⟨1524500, by rfl⟩ : syracuseStep 2032667 = 3049001) B3049001
theorem B2885543 : Blo 599292 2885543 := bstep (se 1 (by rfl) ⟨2164157, by rfl⟩ : syracuseStep 2885543 = 4328315) B4328315
theorem B2033639 : Blo 599292 2033639 := bstep (se 1 (by rfl) ⟨1525229, by rfl⟩ : syracuseStep 2033639 = 3050459) B3050459
theorem B1281275 : Blo 599292 1281275 := bstep (se 1 (by rfl) ⟨960956, by rfl⟩ : syracuseStep 1281275 = 1921913) B1921913
theorem B3050945 : Blo 599292 3050945 := bstep (se 2 (by rfl) ⟨1144104, by rfl⟩ : syracuseStep 3050945 = 2288209) B2288209
theorem B2035367 : Blo 599292 2035367 := bstep (se 1 (by rfl) ⟨1526525, by rfl⟩ : syracuseStep 2035367 = 3053051) B3053051
theorem B3217171 : Blo 599292 3217171 := bstep (se 1 (by rfl) ⟨2412878, by rfl⟩ : syracuseStep 3217171 = 4825757) B4825757
theorem B50206877 : Blo 599292 50206877 := bstep (se 3 (by rfl) ⟨9413789, by rfl⟩ : syracuseStep 50206877 = 18827579) B18827579
theorem B1284265 : Blo 599292 1284265 := bstep (se 2 (by rfl) ⟨481599, by rfl⟩ : syracuseStep 1284265 = 963199) B963199
theorem B1350611 : Blo 599292 1350611 := bstep (se 1 (by rfl) ⟨1012958, by rfl⟩ : syracuseStep 1350611 = 2025917) B2025917
theorem B1350683 : Blo 599292 1350683 := bstep (se 1 (by rfl) ⟨1013012, by rfl⟩ : syracuseStep 1350683 = 2026025) B2026025
theorem B1350881 : Blo 599292 1350881 := bstep (se 2 (by rfl) ⟨506580, by rfl⟩ : syracuseStep 1350881 = 1013161) B1013161
theorem B1351223 : Blo 599292 1351223 := bstep (se 1 (by rfl) ⟨1013417, by rfl⟩ : syracuseStep 1351223 = 2026835) B2026835
theorem B1285769 : Blo 599292 1285769 := bstep (se 2 (by rfl) ⟨482163, by rfl⟩ : syracuseStep 1285769 = 964327) B964327
theorem B3251963 : Blo 599292 3251963 := bstep (se 1 (by rfl) ⟨2438972, by rfl⟩ : syracuseStep 3251963 = 4877945) B4877945
theorem B4103945 : Blo 599292 4103945 := bstep (se 2 (by rfl) ⟨1538979, by rfl⟩ : syracuseStep 4103945 = 3077959) B3077959
theorem B761663 : Blo 599292 761663 := bstep (se 1 (by rfl) ⟨571247, by rfl⟩ : syracuseStep 761663 = 1142495) B1142495
theorem B4104137 : Blo 599292 4104137 := bstep (se 2 (by rfl) ⟨1539051, by rfl⟩ : syracuseStep 4104137 = 3078103) B3078103
theorem B2892095 : Blo 599292 2892095 := bstep (se 1 (by rfl) ⟨2169071, by rfl⟩ : syracuseStep 2892095 = 4338143) B4338143
theorem B25076135 : Blo 599292 25076135 := bstep (se 1 (by rfl) ⟨18807101, by rfl⟩ : syracuseStep 25076135 = 37614203) B37614203
theorem B1352159 : Blo 599292 1352159 := bstep (se 1 (by rfl) ⟨1014119, by rfl⟩ : syracuseStep 1352159 = 2028239) B2028239
theorem B1352249 : Blo 599292 1352249 := bstep (se 2 (by rfl) ⟨507093, by rfl⟩ : syracuseStep 1352249 = 1014187) B1014187
theorem B1582111 : Blo 599292 1582111 := bstep (se 1 (by rfl) ⟨1186583, by rfl⟩ : syracuseStep 1582111 = 2373167) B2373167
theorem B599707 : Blo 599292 599707 := bstep (se 1 (by rfl) ⟨449780, by rfl⟩ : syracuseStep 599707 = 899561) B899561
theorem B600155 : Blo 599292 600155 := bstep (se 1 (by rfl) ⟨450116, by rfl⟩ : syracuseStep 600155 = 900233) B900233
theorem B1353959 : Blo 599292 1353959 := bstep (se 1 (by rfl) ⟨1015469, by rfl⟩ : syracuseStep 1353959 = 2030939) B2030939
theorem B601023 : Blo 599292 601023 := bstep (se 1 (by rfl) ⟨450767, by rfl⟩ : syracuseStep 601023 = 901535) B901535
theorem B601087 : Blo 599292 601087 := bstep (se 1 (by rfl) ⟨450815, by rfl⟩ : syracuseStep 601087 = 901631) B901631
theorem B601279 : Blo 599292 601279 := bstep (se 1 (by rfl) ⟨450959, by rfl⟩ : syracuseStep 601279 = 901919) B901919
theorem B601855 : Blo 599292 601855 := bstep (se 1 (by rfl) ⟨451391, by rfl⟩ : syracuseStep 601855 = 902783) B902783
theorem B601947 : Blo 599292 601947 := bstep (se 1 (by rfl) ⟨451460, by rfl⟩ : syracuseStep 601947 = 902921) B902921
theorem B602159 : Blo 599292 602159 := bstep (se 1 (by rfl) ⟨451619, by rfl⟩ : syracuseStep 602159 = 903239) B903239
theorem B3256375 : Blo 599292 3256375 := bstep (se 1 (by rfl) ⟨2442281, by rfl⟩ : syracuseStep 3256375 = 4884563) B4884563
theorem B1519823 : Blo 599292 1519823 := bstep (se 1 (by rfl) ⟨1139867, by rfl⟩ : syracuseStep 1519823 = 2279735) B2279735
theorem B602415 : Blo 599292 602415 := bstep (se 1 (by rfl) ⟨451811, by rfl⟩ : syracuseStep 602415 = 903623) B903623
theorem B962975 : Blo 599292 962975 := bstep (se 1 (by rfl) ⟨722231, by rfl⟩ : syracuseStep 962975 = 1444463) B1444463
theorem B1356263 : Blo 599292 1356263 := bstep (se 1 (by rfl) ⟨1017197, by rfl⟩ : syracuseStep 1356263 = 2034395) B2034395
theorem B603007 : Blo 599292 603007 := bstep (se 1 (by rfl) ⟨452255, by rfl⟩ : syracuseStep 603007 = 904511) B904511
theorem B1390439 : Blo 599292 1390439 := bstep (se 1 (by rfl) ⟨1042829, by rfl⟩ : syracuseStep 1390439 = 2085659) B2085659
theorem B899183 : Blo 599292 899183 := bstep (se 1 (by rfl) ⟨674387, by rfl⟩ : syracuseStep 899183 = 1348775) B1348775
theorem B14629085 : Blo 599292 14629085 := bstep (se 3 (by rfl) ⟨2742953, by rfl⟩ : syracuseStep 14629085 = 5485907) B5485907
theorem B899567 : Blo 599292 899567 := bstep (se 1 (by rfl) ⟨674675, by rfl⟩ : syracuseStep 899567 = 1349351) B1349351
theorem B899867 : Blo 599292 899867 := bstep (se 1 (by rfl) ⟨674900, by rfl⟩ : syracuseStep 899867 = 1349801) B1349801
theorem B899903 : Blo 599292 899903 := bstep (se 1 (by rfl) ⟨674927, by rfl⟩ : syracuseStep 899903 = 1349855) B1349855
theorem B13876865 : Blo 599292 13876865 := bstep (se 2 (by rfl) ⟨5203824, by rfl⟩ : syracuseStep 13876865 = 10407649) B10407649
theorem B1949435 : Blo 599292 1949435 := bstep (se 1 (by rfl) ⟨1462076, by rfl⟩ : syracuseStep 1949435 = 2924153) B2924153
theorem B901001 : Blo 599292 901001 := bstep (se 2 (by rfl) ⟨337875, by rfl⟩ : syracuseStep 901001 = 675751) B675751
theorem B2277335 : Blo 599292 2277335 := bstep (se 1 (by rfl) ⟨1708001, by rfl⟩ : syracuseStep 2277335 = 3416003) B3416003
theorem B901151 : Blo 599292 901151 := bstep (se 1 (by rfl) ⟨675863, by rfl⟩ : syracuseStep 901151 = 1351727) B1351727
theorem B901247 : Blo 599292 901247 := bstep (se 1 (by rfl) ⟨675935, by rfl⟩ : syracuseStep 901247 = 1351871) B1351871
theorem B901871 : Blo 599292 901871 := bstep (se 1 (by rfl) ⟨676403, by rfl⟩ : syracuseStep 901871 = 1352807) B1352807
theorem B902015 : Blo 599292 902015 := bstep (se 1 (by rfl) ⟨676511, by rfl⟩ : syracuseStep 902015 = 1353023) B1353023
theorem B902825 : Blo 599292 902825 := bstep (se 2 (by rfl) ⟨338559, by rfl⟩ : syracuseStep 902825 = 677119) B677119
theorem B1525513 : Blo 599292 1525513 := bstep (se 2 (by rfl) ⟨572067, by rfl⟩ : syracuseStep 1525513 = 1144135) B1144135
theorem B903275 : Blo 599292 903275 := bstep (se 1 (by rfl) ⟨677456, by rfl⟩ : syracuseStep 903275 = 1354913) B1354913
theorem B1525979 : Blo 599292 1525979 := bstep (se 1 (by rfl) ⟨1144484, by rfl⟩ : syracuseStep 1525979 = 2288969) B2288969
theorem B3033935 : Blo 599292 3033935 := bstep (se 1 (by rfl) ⟨2275451, by rfl⟩ : syracuseStep 3033935 = 4550903) B4550903
theorem B904103 : Blo 599292 904103 := bstep (se 1 (by rfl) ⟨678077, by rfl⟩ : syracuseStep 904103 = 1356155) B1356155
theorem B1526809 : Blo 599292 1526809 := bstep (se 2 (by rfl) ⟨572553, by rfl⟩ : syracuseStep 1526809 = 1145107) B1145107
theorem B904223 : Blo 599292 904223 := bstep (se 1 (by rfl) ⟨678167, by rfl⟩ : syracuseStep 904223 = 1356335) B1356335
theorem B904427 : Blo 599292 904427 := bstep (se 1 (by rfl) ⟨678320, by rfl⟩ : syracuseStep 904427 = 1356641) B1356641
theorem B5131795 : Blo 599292 5131795 := bstep (se 1 (by rfl) ⟨3848846, by rfl⟩ : syracuseStep 5131795 = 7697693) B7697693
theorem B904751 : Blo 599292 904751 := bstep (se 1 (by rfl) ⟨678563, by rfl⟩ : syracuseStep 904751 = 1357127) B1357127
theorem B904871 : Blo 599292 904871 := bstep (se 1 (by rfl) ⟨678653, by rfl⟩ : syracuseStep 904871 = 1357307) B1357307
theorem B5787881 : Blo 599292 5787881 := bstep (se 2 (by rfl) ⟨2170455, by rfl⟩ : syracuseStep 5787881 = 4340911) B4340911
theorem B2282377 : Blo 599292 2282377 := bstep (se 2 (by rfl) ⟨855891, by rfl⟩ : syracuseStep 2282377 = 1711783) B1711783
theorem B8803313 : Blo 599292 8803313 := bstep (se 2 (by rfl) ⟨3301242, by rfl⟩ : syracuseStep 8803313 = 6602485) B6602485
theorem B13030555 : Blo 599292 13030555 := bstep (se 1 (by rfl) ⟨9772916, by rfl⟩ : syracuseStep 13030555 = 19545833) B19545833
theorem B5789231 : Blo 599292 5789231 := bstep (se 1 (by rfl) ⟨4341923, by rfl⟩ : syracuseStep 5789231 = 8683847) B8683847
theorem B10278899 : Blo 599292 10278899 := bstep (se 1 (by rfl) ⟨7709174, by rfl⟩ : syracuseStep 10278899 = 15418349) B15418349
theorem B12965993 : Blo 599292 12965993 := bstep (se 2 (by rfl) ⟨4862247, by rfl⟩ : syracuseStep 12965993 = 9724495) B9724495
theorem B678631 : Blo 599292 678631 := bstep (se 1 (by rfl) ⟨508973, by rfl⟩ : syracuseStep 678631 = 1017947) B1017947
theorem B1825523 : Blo 599292 1825523 := bstep (se 1 (by rfl) ⟨1369142, by rfl⟩ : syracuseStep 1825523 = 2738285) B2738285
theorem B3431585 : Blo 599292 3431585 := bstep (se 2 (by rfl) ⟨1286844, by rfl⟩ : syracuseStep 3431585 = 2573689) B2573689
theorem B59464955 : Blo 599292 59464955 := bstep (se 1 (by rfl) ⟨44598716, by rfl⟩ : syracuseStep 59464955 = 89197433) B89197433
theorem B1924681 : Blo 599292 1924681 := bstep (se 2 (by rfl) ⟨721755, by rfl⟩ : syracuseStep 1924681 = 1443511) B1443511
theorem B2023271 : Blo 599292 2023271 := bstep (se 1 (by rfl) ⟨1517453, by rfl⟩ : syracuseStep 2023271 = 3034907) B3034907
theorem B3040091 : Blo 599292 3040091 := bstep (se 1 (by rfl) ⟨2280068, by rfl⟩ : syracuseStep 3040091 = 4560137) B4560137
theorem B6677959 : Blo 599292 6677959 := bstep (se 1 (by rfl) ⟨5008469, by rfl⟩ : syracuseStep 6677959 = 10016939) B10016939
theorem B2025647 : Blo 599292 2025647 := bstep (se 1 (by rfl) ⟨1519235, by rfl⟩ : syracuseStep 2025647 = 3038471) B3038471
theorem B8645143 : Blo 599292 8645143 := bstep (se 1 (by rfl) ⟨6483857, by rfl⟩ : syracuseStep 8645143 = 12967715) B12967715
theorem B5925563 : Blo 599292 5925563 := bstep (se 1 (by rfl) ⟨4444172, by rfl⟩ : syracuseStep 5925563 = 8888345) B8888345
theorem B2747351 : Blo 599292 2747351 := bstep (se 1 (by rfl) ⟨2060513, by rfl⟩ : syracuseStep 2747351 = 4121027) B4121027
theorem B2026943 : Blo 599292 2026943 := bstep (se 1 (by rfl) ⟨1520207, by rfl⟩ : syracuseStep 2026943 = 3040415) B3040415
theorem B3862151 : Blo 599292 3862151 := bstep (se 1 (by rfl) ⟨2896613, by rfl⟩ : syracuseStep 3862151 = 5793227) B5793227
theorem B2029049 : Blo 599292 2029049 := bstep (se 2 (by rfl) ⟨760893, by rfl⟩ : syracuseStep 2029049 = 1521787) B1521787
theorem B1832927 : Blo 599292 1832927 := bstep (se 1 (by rfl) ⟨1374695, by rfl⟩ : syracuseStep 1832927 = 2749391) B2749391
theorem B1013863 : Blo 599292 1013863 := bstep (se 1 (by rfl) ⟨760397, by rfl⟩ : syracuseStep 1013863 = 1520795) B1520795
theorem B7536091 : Blo 599292 7536091 := bstep (se 1 (by rfl) ⟨5652068, by rfl⟩ : syracuseStep 7536091 = 11304137) B11304137
theorem B1015463 : Blo 599292 1015463 := bstep (se 1 (by rfl) ⟨761597, by rfl⟩ : syracuseStep 1015463 = 1523195) B1523195
theorem B1017319 : Blo 599292 1017319 := bstep (se 1 (by rfl) ⟨762989, by rfl⟩ : syracuseStep 1017319 = 1525979) B1525979
theorem B854183 : Blo 599292 854183 := bstep (se 1 (by rfl) ⟨640637, by rfl⟩ : syracuseStep 854183 = 1281275) B1281275
theorem B2033963 : Blo 599292 2033963 := bstep (se 1 (by rfl) ⟨1525472, by rfl⟩ : syracuseStep 2033963 = 3050945) B3050945
theorem B2034017 : Blo 599292 2034017 := bstep (se 2 (by rfl) ⟨762756, by rfl⟩ : syracuseStep 2034017 = 1525513) B1525513
theorem B5868875 : Blo 599292 5868875 := bstep (se 1 (by rfl) ⟨4401656, by rfl⟩ : syracuseStep 5868875 = 8803313) B8803313
theorem B6852599 : Blo 599292 6852599 := bstep (se 1 (by rfl) ⟨5139449, by rfl⟩ : syracuseStep 6852599 = 10278899) B10278899
theorem B2035745 : Blo 599292 2035745 := bstep (se 2 (by rfl) ⟨763404, by rfl⟩ : syracuseStep 2035745 = 1526809) B1526809
theorem B1217015 : Blo 599292 1217015 := bstep (se 1 (by rfl) ⟨912761, by rfl⟩ : syracuseStep 1217015 = 1825523) B1825523
theorem B857179 : Blo 599292 857179 := bstep (se 1 (by rfl) ⟨642884, by rfl⟩ : syracuseStep 857179 = 1285769) B1285769
theorem B2167975 : Blo 599292 2167975 := bstep (se 1 (by rfl) ⟨1625981, by rfl⟩ : syracuseStep 2167975 = 3251963) B3251963
theorem B1348847 : Blo 599292 1348847 := bstep (se 1 (by rfl) ⟨1011635, by rfl⟩ : syracuseStep 1348847 = 2023271) B2023271
theorem B4887805 : Blo 599292 4887805 := bstep (se 3 (by rfl) ⟨916463, by rfl⟩ : syracuseStep 4887805 = 1832927) B1832927
theorem B16717423 : Blo 599292 16717423 := bstep (se 1 (by rfl) ⟨12538067, by rfl⟩ : syracuseStep 16717423 = 25076135) B25076135
theorem B1350431 : Blo 599292 1350431 := bstep (se 1 (by rfl) ⟨1012823, by rfl⟩ : syracuseStep 1350431 = 2025647) B2025647
theorem B17374073 : Blo 599292 17374073 := bstep (se 2 (by rfl) ⟨6515277, by rfl⟩ : syracuseStep 17374073 = 13030555) B13030555
theorem B1351295 : Blo 599292 1351295 := bstep (se 1 (by rfl) ⟨1013471, by rfl⟩ : syracuseStep 1351295 = 2026943) B2026943
theorem B1351817 : Blo 599292 1351817 := bstep (se 2 (by rfl) ⟨506931, by rfl⟩ : syracuseStep 1351817 = 1013863) B1013863
theorem B1712353 : Blo 599292 1712353 := bstep (se 2 (by rfl) ⟨642132, by rfl⟩ : syracuseStep 1712353 = 1284265) B1284265
theorem B1352699 : Blo 599292 1352699 := bstep (se 1 (by rfl) ⟨1014524, by rfl⟩ : syracuseStep 1352699 = 2029049) B2029049
theorem B926959 : Blo 599292 926959 := bstep (se 1 (by rfl) ⟨695219, by rfl⟩ : syracuseStep 926959 = 1390439) B1390439
theorem B599455 : Blo 599292 599455 := bstep (se 1 (by rfl) ⟨449591, by rfl⟩ : syracuseStep 599455 = 899183) B899183
theorem B599711 : Blo 599292 599711 := bstep (se 1 (by rfl) ⟨449783, by rfl⟩ : syracuseStep 599711 = 899567) B899567
theorem B599911 : Blo 599292 599911 := bstep (se 1 (by rfl) ⟨449933, by rfl⟩ : syracuseStep 599911 = 899867) B899867
theorem B599935 : Blo 599292 599935 := bstep (se 1 (by rfl) ⟨449951, by rfl⟩ : syracuseStep 599935 = 899903) B899903
theorem B2566241 : Blo 599292 2566241 := bstep (se 2 (by rfl) ⟨962340, by rfl⟩ : syracuseStep 2566241 = 1924681) B1924681
theorem B9251243 : Blo 599292 9251243 := bstep (se 1 (by rfl) ⟨6938432, by rfl⟩ : syracuseStep 9251243 = 13876865) B13876865
theorem B600667 : Blo 599292 600667 := bstep (se 1 (by rfl) ⟨450500, by rfl⟩ : syracuseStep 600667 = 901001) B901001
theorem B1518223 : Blo 599292 1518223 := bstep (se 1 (by rfl) ⟨1138667, by rfl⟩ : syracuseStep 1518223 = 2277335) B2277335
theorem B600767 : Blo 599292 600767 := bstep (se 1 (by rfl) ⟨450575, by rfl⟩ : syracuseStep 600767 = 901151) B901151
theorem B600831 : Blo 599292 600831 := bstep (se 1 (by rfl) ⟨450623, by rfl⟩ : syracuseStep 600831 = 901247) B901247
theorem B1354751 : Blo 599292 1354751 := bstep (se 1 (by rfl) ⟨1016063, by rfl⟩ : syracuseStep 1354751 = 2032127) B2032127
theorem B601247 : Blo 599292 601247 := bstep (se 1 (by rfl) ⟨450935, by rfl⟩ : syracuseStep 601247 = 901871) B901871
theorem B601343 : Blo 599292 601343 := bstep (se 1 (by rfl) ⟨451007, by rfl⟩ : syracuseStep 601343 = 902015) B902015
theorem B1355111 : Blo 599292 1355111 := bstep (se 1 (by rfl) ⟨1016333, by rfl⟩ : syracuseStep 1355111 = 2032667) B2032667
theorem B2567933 : Blo 599292 2567933 := bstep (se 3 (by rfl) ⟨481487, by rfl⟩ : syracuseStep 2567933 = 962975) B962975
theorem B601883 : Blo 599292 601883 := bstep (se 1 (by rfl) ⟨451412, by rfl⟩ : syracuseStep 601883 = 902825) B902825
theorem B1355759 : Blo 599292 1355759 := bstep (se 1 (by rfl) ⟨1016819, by rfl⟩ : syracuseStep 1355759 = 2033639) B2033639
theorem B602183 : Blo 599292 602183 := bstep (se 1 (by rfl) ⟨451637, by rfl⟩ : syracuseStep 602183 = 903275) B903275
theorem B602735 : Blo 599292 602735 := bstep (se 1 (by rfl) ⟨452051, by rfl⟩ : syracuseStep 602735 = 904103) B904103
theorem B602815 : Blo 599292 602815 := bstep (se 1 (by rfl) ⟨452111, by rfl⟩ : syracuseStep 602815 = 904223) B904223
theorem B602951 : Blo 599292 602951 := bstep (se 1 (by rfl) ⟨452213, by rfl⟩ : syracuseStep 602951 = 904427) B904427
theorem B603167 : Blo 599292 603167 := bstep (se 1 (by rfl) ⟨452375, by rfl⟩ : syracuseStep 603167 = 904751) B904751
theorem B1356911 : Blo 599292 1356911 := bstep (se 1 (by rfl) ⟨1017683, by rfl⟩ : syracuseStep 1356911 = 2035367) B2035367
theorem B603247 : Blo 599292 603247 := bstep (se 1 (by rfl) ⟨452435, by rfl⟩ : syracuseStep 603247 = 904871) B904871
theorem B33471251 : Blo 599292 33471251 := bstep (se 1 (by rfl) ⟨25103438, by rfl⟩ : syracuseStep 33471251 = 50206877) B50206877
theorem B900407 : Blo 599292 900407 := bstep (se 1 (by rfl) ⟨675305, by rfl⟩ : syracuseStep 900407 = 1350611) B1350611
theorem B900455 : Blo 599292 900455 := bstep (se 1 (by rfl) ⟨675341, by rfl⟩ : syracuseStep 900455 = 1350683) B1350683
theorem B900587 : Blo 599292 900587 := bstep (se 1 (by rfl) ⟨675440, by rfl⟩ : syracuseStep 900587 = 1350881) B1350881
theorem B900815 : Blo 599292 900815 := bstep (se 1 (by rfl) ⟨675611, by rfl⟩ : syracuseStep 900815 = 1351223) B1351223
theorem B2735963 : Blo 599292 2735963 := bstep (se 1 (by rfl) ⟨2051972, by rfl⟩ : syracuseStep 2735963 = 4103945) B4103945
theorem B2736091 : Blo 599292 2736091 := bstep (se 1 (by rfl) ⟨2052068, by rfl⟩ : syracuseStep 2736091 = 4104137) B4104137
theorem B4341833 : Blo 599292 4341833 := bstep (se 2 (by rfl) ⟨1628187, by rfl⟩ : syracuseStep 4341833 = 3256375) B3256375
theorem B8437925 : Blo 599292 8437925 := bstep (se 4 (by rfl) ⟨791055, by rfl⟩ : syracuseStep 8437925 = 1582111) B1582111
theorem B901439 : Blo 599292 901439 := bstep (se 1 (by rfl) ⟨676079, by rfl⟩ : syracuseStep 901439 = 1352159) B1352159
theorem B901499 : Blo 599292 901499 := bstep (se 1 (by rfl) ⟨676124, by rfl⟩ : syracuseStep 901499 = 1352249) B1352249
theorem B902639 : Blo 599292 902639 := bstep (se 1 (by rfl) ⟨676979, by rfl⟩ : syracuseStep 902639 = 1353959) B1353959
theorem B3950375 : Blo 599292 3950375 := bstep (se 1 (by rfl) ⟨2962781, by rfl⟩ : syracuseStep 3950375 = 5925563) B5925563
theorem B2574767 : Blo 599292 2574767 := bstep (se 1 (by rfl) ⟨1931075, by rfl⟩ : syracuseStep 2574767 = 3862151) B3862151
theorem B904175 : Blo 599292 904175 := bstep (se 1 (by rfl) ⟨678131, by rfl⟩ : syracuseStep 904175 = 1356263) B1356263
theorem B904841 : Blo 599292 904841 := bstep (se 2 (by rfl) ⟨339315, by rfl⟩ : syracuseStep 904841 = 678631) B678631
theorem B9752723 : Blo 599292 9752723 := bstep (se 1 (by rfl) ⟨7314542, by rfl⟩ : syracuseStep 9752723 = 14629085) B14629085
theorem B10048121 : Blo 599292 10048121 := bstep (se 2 (by rfl) ⟨3768045, by rfl⟩ : syracuseStep 10048121 = 7536091) B7536091
theorem B676975 : Blo 599292 676975 := bstep (se 1 (by rfl) ⟨507731, by rfl⟩ : syracuseStep 676975 = 1015463) B1015463
theorem B1299623 : Blo 599292 1299623 := bstep (se 1 (by rfl) ⟨974717, by rfl⟩ : syracuseStep 1299623 = 1949435) B1949435
theorem B1923695 : Blo 599292 1923695 := bstep (se 1 (by rfl) ⟨1442771, by rfl⟩ : syracuseStep 1923695 = 2885543) B2885543
theorem B2022623 : Blo 599292 2022623 := bstep (se 1 (by rfl) ⟨1516967, by rfl⟩ : syracuseStep 2022623 = 3033935) B3033935
theorem B8903945 : Blo 599292 8903945 := bstep (se 2 (by rfl) ⟨3338979, by rfl⟩ : syracuseStep 8903945 = 6677959) B6677959
theorem B3858587 : Blo 599292 3858587 := bstep (se 1 (by rfl) ⟨2893940, by rfl⟩ : syracuseStep 3858587 = 5787881) B5787881
theorem B11526857 : Blo 599292 11526857 := bstep (se 2 (by rfl) ⟨4322571, by rfl⟩ : syracuseStep 11526857 = 8645143) B8645143
theorem B3859487 : Blo 599292 3859487 := bstep (se 1 (by rfl) ⟨2894615, by rfl⟩ : syracuseStep 3859487 = 5789231) B5789231
theorem B8643995 : Blo 599292 8643995 := bstep (se 1 (by rfl) ⟨6482996, by rfl⟩ : syracuseStep 8643995 = 12965993) B12965993
theorem B6842393 : Blo 599292 6842393 := bstep (se 2 (by rfl) ⟨2565897, by rfl⟩ : syracuseStep 6842393 = 5131795) B5131795
theorem B2287723 : Blo 599292 2287723 := bstep (se 1 (by rfl) ⟨1715792, by rfl⟩ : syracuseStep 2287723 = 3431585) B3431585
theorem B39643303 : Blo 599292 39643303 := bstep (se 1 (by rfl) ⟨29732477, by rfl⟩ : syracuseStep 39643303 = 59464955) B59464955
theorem B1928063 : Blo 599292 1928063 := bstep (se 1 (by rfl) ⟨1446047, by rfl⟩ : syracuseStep 1928063 = 2892095) B2892095
theorem B2026727 : Blo 599292 2026727 := bstep (se 1 (by rfl) ⟨1520045, by rfl⟩ : syracuseStep 2026727 = 3040091) B3040091
theorem B3043169 : Blo 599292 3043169 := bstep (se 2 (by rfl) ⟨1141188, by rfl⟩ : syracuseStep 3043169 = 2282377) B2282377
theorem B1831567 : Blo 599292 1831567 := bstep (se 1 (by rfl) ⟨1373675, by rfl⟩ : syracuseStep 1831567 = 2747351) B2747351
theorem B4289561 : Blo 599292 4289561 := bstep (se 2 (by rfl) ⟨1608585, by rfl⟩ : syracuseStep 4289561 = 3217171) B3217171
theorem B1013215 : Blo 599292 1013215 := bstep (se 1 (by rfl) ⟨759911, by rfl⟩ : syracuseStep 1013215 = 1519823) B1519823
theorem B2031101 : Blo 599292 2031101 := bstep (se 3 (by rfl) ⟨380831, by rfl⟩ : syracuseStep 2031101 = 761663) B761663
theorem B3050297 : Blo 599292 3050297 := bstep (se 2 (by rfl) ⟨1143861, by rfl⟩ : syracuseStep 3050297 = 2287723) B2287723
theorem B52857737 : Blo 599292 52857737 := bstep (se 2 (by rfl) ⟨19821651, by rfl⟩ : syracuseStep 52857737 = 39643303) B39643303
theorem B1282463 : Blo 599292 1282463 := bstep (se 1 (by rfl) ⟨961847, by rfl⟩ : syracuseStep 1282463 = 1923695) B1923695
theorem B1348415 : Blo 599292 1348415 := bstep (se 1 (by rfl) ⟨1011311, by rfl⟩ : syracuseStep 1348415 = 2022623) B2022623
theorem B5935963 : Blo 599292 5935963 := bstep (se 1 (by rfl) ⟨4451972, by rfl⟩ : syracuseStep 5935963 = 8903945) B8903945
theorem B4561595 : Blo 599292 4561595 := bstep (se 1 (by rfl) ⟨3421196, by rfl⟩ : syracuseStep 4561595 = 6842393) B6842393
theorem B1710827 : Blo 599292 1710827 := bstep (se 1 (by rfl) ⟨1283120, by rfl⟩ : syracuseStep 1710827 = 2566241) B2566241
theorem B6167495 : Blo 599292 6167495 := bstep (se 1 (by rfl) ⟨4625621, by rfl⟩ : syracuseStep 6167495 = 9251243) B9251243
theorem B1350953 : Blo 599292 1350953 := bstep (se 2 (by rfl) ⟨506607, by rfl⟩ : syracuseStep 1350953 = 1013215) B1013215
theorem B22289897 : Blo 599292 22289897 := bstep (se 2 (by rfl) ⟨8358711, by rfl⟩ : syracuseStep 22289897 = 16717423) B16717423
theorem B1351151 : Blo 599292 1351151 := bstep (se 1 (by rfl) ⟨1013363, by rfl⟩ : syracuseStep 1351151 = 2026727) B2026727
theorem B1711955 : Blo 599292 1711955 := bstep (se 1 (by rfl) ⟨1283966, by rfl⟩ : syracuseStep 1711955 = 2567933) B2567933
theorem B2859707 : Blo 599292 2859707 := bstep (se 1 (by rfl) ⟨2144780, by rfl⟩ : syracuseStep 2859707 = 4289561) B4289561
theorem B600271 : Blo 599292 600271 := bstep (se 1 (by rfl) ⟨450203, by rfl⟩ : syracuseStep 600271 = 900407) B900407
theorem B600303 : Blo 599292 600303 := bstep (se 1 (by rfl) ⟨450227, by rfl⟩ : syracuseStep 600303 = 900455) B900455
theorem B600391 : Blo 599292 600391 := bstep (se 1 (by rfl) ⟨450293, by rfl⟩ : syracuseStep 600391 = 900587) B900587
theorem B1354067 : Blo 599292 1354067 := bstep (se 1 (by rfl) ⟨1015550, by rfl⟩ : syracuseStep 1354067 = 2031101) B2031101
theorem B600543 : Blo 599292 600543 := bstep (se 1 (by rfl) ⟨450407, by rfl⟩ : syracuseStep 600543 = 900815) B900815
theorem B3648121 : Blo 599292 3648121 := bstep (se 2 (by rfl) ⟨1368045, by rfl⟩ : syracuseStep 3648121 = 2736091) B2736091
theorem B2894555 : Blo 599292 2894555 := bstep (se 1 (by rfl) ⟨2170916, by rfl⟩ : syracuseStep 2894555 = 4341833) B4341833
theorem B600959 : Blo 599292 600959 := bstep (se 1 (by rfl) ⟨450719, by rfl⟩ : syracuseStep 600959 = 901439) B901439
theorem B600999 : Blo 599292 600999 := bstep (se 1 (by rfl) ⟨450749, by rfl⟩ : syracuseStep 600999 = 901499) B901499
theorem B601759 : Blo 599292 601759 := bstep (se 1 (by rfl) ⟨451319, by rfl⟩ : syracuseStep 601759 = 902639) B902639
theorem B1355975 : Blo 599292 1355975 := bstep (se 1 (by rfl) ⟨1016981, by rfl⟩ : syracuseStep 1355975 = 2033963) B2033963
theorem B1356011 : Blo 599292 1356011 := bstep (se 1 (by rfl) ⟨1017008, by rfl⟩ : syracuseStep 1356011 = 2034017) B2034017
theorem B1716511 : Blo 599292 1716511 := bstep (se 1 (by rfl) ⟨1287383, by rfl⟩ : syracuseStep 1716511 = 2574767) B2574767
theorem B1356425 : Blo 599292 1356425 := bstep (se 2 (by rfl) ⟨508659, by rfl⟩ : syracuseStep 1356425 = 1017319) B1017319
theorem B602783 : Blo 599292 602783 := bstep (se 1 (by rfl) ⟨452087, by rfl⟩ : syracuseStep 602783 = 904175) B904175
theorem B603227 : Blo 599292 603227 := bstep (se 1 (by rfl) ⟨452420, by rfl⟩ : syracuseStep 603227 = 904841) B904841
theorem B4568399 : Blo 599292 4568399 := bstep (se 1 (by rfl) ⟨3426299, by rfl⟩ : syracuseStep 4568399 = 6852599) B6852599
theorem B1357163 : Blo 599292 1357163 := bstep (se 1 (by rfl) ⟨1017872, by rfl⟩ : syracuseStep 1357163 = 2035745) B2035745
theorem B6501815 : Blo 599292 6501815 := bstep (se 1 (by rfl) ⟨4876361, by rfl⟩ : syracuseStep 6501815 = 9752723) B9752723
theorem B6698747 : Blo 599292 6698747 := bstep (se 1 (by rfl) ⟨5024060, by rfl⟩ : syracuseStep 6698747 = 10048121) B10048121
theorem B899231 : Blo 599292 899231 := bstep (se 1 (by rfl) ⟨674423, by rfl⟩ : syracuseStep 899231 = 1348847) B1348847
theorem B900287 : Blo 599292 900287 := bstep (se 1 (by rfl) ⟨675215, by rfl⟩ : syracuseStep 900287 = 1350431) B1350431
theorem B900863 : Blo 599292 900863 := bstep (se 1 (by rfl) ⟨675647, by rfl⟩ : syracuseStep 900863 = 1351295) B1351295
theorem B901211 : Blo 599292 901211 := bstep (se 1 (by rfl) ⟨675908, by rfl⟩ : syracuseStep 901211 = 1351817) B1351817
theorem B2572391 : Blo 599292 2572391 := bstep (se 1 (by rfl) ⟨1929293, by rfl⟩ : syracuseStep 2572391 = 3858587) B3858587
theorem B2277821 : Blo 599292 2277821 := bstep (se 3 (by rfl) ⟨427091, by rfl⟩ : syracuseStep 2277821 = 854183) B854183
theorem B7684571 : Blo 599292 7684571 := bstep (se 1 (by rfl) ⟨5763428, by rfl⟩ : syracuseStep 7684571 = 11526857) B11526857
theorem B901799 : Blo 599292 901799 := bstep (se 1 (by rfl) ⟨676349, by rfl⟩ : syracuseStep 901799 = 1352699) B1352699
theorem B2572991 : Blo 599292 2572991 := bstep (se 1 (by rfl) ⟨1929743, by rfl⟩ : syracuseStep 2572991 = 3859487) B3859487
theorem B2442089 : Blo 599292 2442089 := bstep (se 2 (by rfl) ⟨915783, by rfl⟩ : syracuseStep 2442089 = 1831567) B1831567
theorem B902633 : Blo 599292 902633 := bstep (se 2 (by rfl) ⟨338487, by rfl⟩ : syracuseStep 902633 = 676975) B676975
theorem B903167 : Blo 599292 903167 := bstep (se 1 (by rfl) ⟨677375, by rfl⟩ : syracuseStep 903167 = 1354751) B1354751
theorem B903407 : Blo 599292 903407 := bstep (se 1 (by rfl) ⟨677555, by rfl⟩ : syracuseStep 903407 = 1355111) B1355111
theorem B903839 : Blo 599292 903839 := bstep (se 1 (by rfl) ⟨677879, by rfl⟩ : syracuseStep 903839 = 1355759) B1355759
theorem B904607 : Blo 599292 904607 := bstep (se 1 (by rfl) ⟨678455, by rfl⟩ : syracuseStep 904607 = 1356911) B1356911
theorem B15650333 : Blo 599292 15650333 := bstep (se 3 (by rfl) ⟨2934437, by rfl⟩ : syracuseStep 15650333 = 5868875) B5868875
theorem B1823975 : Blo 599292 1823975 := bstep (se 1 (by rfl) ⟨1367981, by rfl⟩ : syracuseStep 1823975 = 2735963) B2735963
theorem B5625283 : Blo 599292 5625283 := bstep (se 1 (by rfl) ⟨4218962, by rfl⟩ : syracuseStep 5625283 = 8437925) B8437925
theorem B2283137 : Blo 599292 2283137 := bstep (se 2 (by rfl) ⟨856176, by rfl⟩ : syracuseStep 2283137 = 1712353) B1712353
theorem B1235945 : Blo 599292 1235945 := bstep (se 2 (by rfl) ⟨463479, by rfl⟩ : syracuseStep 1235945 = 926959) B926959
theorem B811343 : Blo 599292 811343 := bstep (se 1 (by rfl) ⟨608507, by rfl⟩ : syracuseStep 811343 = 1217015) B1217015
theorem B3465661 : Blo 599292 3465661 := bstep (se 3 (by rfl) ⟨649811, by rfl⟩ : syracuseStep 3465661 = 1299623) B1299623
theorem B2024297 : Blo 599292 2024297 := bstep (se 2 (by rfl) ⟨759111, by rfl⟩ : syracuseStep 2024297 = 1518223) B1518223
theorem B11562533 : Blo 599292 11562533 := bstep (se 4 (by rfl) ⟨1083987, by rfl⟩ : syracuseStep 11562533 = 2167975) B2167975
theorem B5762663 : Blo 599292 5762663 := bstep (se 1 (by rfl) ⟨4321997, by rfl⟩ : syracuseStep 5762663 = 8643995) B8643995
theorem B1142905 : Blo 599292 1142905 := bstep (se 2 (by rfl) ⟨428589, by rfl⟩ : syracuseStep 1142905 = 857179) B857179
theorem B6517073 : Blo 599292 6517073 := bstep (se 2 (by rfl) ⟨2443902, by rfl⟩ : syracuseStep 6517073 = 4887805) B4887805
theorem B46330861 : Blo 599292 46330861 := bstep (se 3 (by rfl) ⟨8687036, by rfl⟩ : syracuseStep 46330861 = 17374073) B17374073
theorem B5141501 : Blo 599292 5141501 := bstep (se 3 (by rfl) ⟨964031, by rfl⟩ : syracuseStep 5141501 = 1928063) B1928063
theorem B2028779 : Blo 599292 2028779 := bstep (se 1 (by rfl) ⟨1521584, by rfl⟩ : syracuseStep 2028779 = 3043169) B3043169
theorem B42137333 : Blo 599292 42137333 := bstep (se 5 (by rfl) ⟨1975187, by rfl⟩ : syracuseStep 42137333 = 3950375) B3950375
theorem B22314167 : Blo 599292 22314167 := bstep (se 1 (by rfl) ⟨16735625, by rfl⟩ : syracuseStep 22314167 = 33471251) B33471251
theorem B4620881 : Blo 599292 4620881 := bstep (se 2 (by rfl) ⟨1732830, by rfl⟩ : syracuseStep 4620881 = 3465661) B3465661
theorem B2163581 : Blo 599292 2163581 := bstep (se 3 (by rfl) ⟨405671, by rfl⟩ : syracuseStep 2163581 = 811343) B811343
theorem B2033531 : Blo 599292 2033531 := bstep (se 1 (by rfl) ⟨1525148, by rfl⟩ : syracuseStep 2033531 = 3050297) B3050297
theorem B854975 : Blo 599292 854975 := bstep (se 1 (by rfl) ⟨641231, by rfl⟩ : syracuseStep 854975 = 1282463) B1282463
theorem B1215983 : Blo 599292 1215983 := bstep (se 1 (by rfl) ⟨911987, by rfl⟩ : syracuseStep 1215983 = 1823975) B1823975
theorem B823963 : Blo 599292 823963 := bstep (se 1 (by rfl) ⟨617972, by rfl⟩ : syracuseStep 823963 = 1235945) B1235945
theorem B17863325 : Blo 599292 17863325 := bstep (se 3 (by rfl) ⟨3349373, by rfl⟩ : syracuseStep 17863325 = 6698747) B6698747
theorem B1906471 : Blo 599292 1906471 := bstep (se 1 (by rfl) ⟨1429853, by rfl⟩ : syracuseStep 1906471 = 2859707) B2859707
theorem B1349531 : Blo 599292 1349531 := bstep (se 1 (by rfl) ⟨1012148, by rfl⟩ : syracuseStep 1349531 = 2024297) B2024297
theorem B61774481 : Blo 599292 61774481 := bstep (se 2 (by rfl) ⟨23165430, by rfl⟩ : syracuseStep 61774481 = 46330861) B46330861
theorem B7708355 : Blo 599292 7708355 := bstep (se 1 (by rfl) ⟨5781266, by rfl⟩ : syracuseStep 7708355 = 11562533) B11562533
theorem B3841775 : Blo 599292 3841775 := bstep (se 1 (by rfl) ⟨2881331, by rfl⟩ : syracuseStep 3841775 = 5762663) B5762663
theorem B1352519 : Blo 599292 1352519 := bstep (se 1 (by rfl) ⟨1014389, by rfl⟩ : syracuseStep 1352519 = 2028779) B2028779
theorem B4334543 : Blo 599292 4334543 := bstep (se 1 (by rfl) ⟨3250907, by rfl⟩ : syracuseStep 4334543 = 6501815) B6501815
theorem B28091555 : Blo 599292 28091555 := bstep (se 1 (by rfl) ⟨21068666, by rfl⟩ : syracuseStep 28091555 = 42137333) B42137333
theorem B599487 : Blo 599292 599487 := bstep (se 1 (by rfl) ⟨449615, by rfl⟩ : syracuseStep 599487 = 899231) B899231
theorem B600191 : Blo 599292 600191 := bstep (se 1 (by rfl) ⟨450143, by rfl⟩ : syracuseStep 600191 = 900287) B900287
theorem B600575 : Blo 599292 600575 := bstep (se 1 (by rfl) ⟨450431, by rfl⟩ : syracuseStep 600575 = 900863) B900863
theorem B600807 : Blo 599292 600807 := bstep (se 1 (by rfl) ⟨450605, by rfl⟩ : syracuseStep 600807 = 901211) B901211
theorem B1714927 : Blo 599292 1714927 := bstep (se 1 (by rfl) ⟨1286195, by rfl⟩ : syracuseStep 1714927 = 2572391) B2572391
theorem B1518547 : Blo 599292 1518547 := bstep (se 1 (by rfl) ⟨1138910, by rfl⟩ : syracuseStep 1518547 = 2277821) B2277821
theorem B5123047 : Blo 599292 5123047 := bstep (se 1 (by rfl) ⟨3842285, by rfl⟩ : syracuseStep 5123047 = 7684571) B7684571
theorem B601199 : Blo 599292 601199 := bstep (se 1 (by rfl) ⟨450899, by rfl⟩ : syracuseStep 601199 = 901799) B901799
theorem B1715327 : Blo 599292 1715327 := bstep (se 1 (by rfl) ⟨1286495, by rfl⟩ : syracuseStep 1715327 = 2572991) B2572991
theorem B601755 : Blo 599292 601755 := bstep (se 1 (by rfl) ⟨451316, by rfl⟩ : syracuseStep 601755 = 902633) B902633
theorem B602111 : Blo 599292 602111 := bstep (se 1 (by rfl) ⟨451583, by rfl⟩ : syracuseStep 602111 = 903167) B903167
theorem B602271 : Blo 599292 602271 := bstep (se 1 (by rfl) ⟨451703, by rfl⟩ : syracuseStep 602271 = 903407) B903407
theorem B602559 : Blo 599292 602559 := bstep (se 1 (by rfl) ⟨451919, by rfl⟩ : syracuseStep 602559 = 903839) B903839
theorem B35238491 : Blo 599292 35238491 := bstep (se 1 (by rfl) ⟨26428868, by rfl⟩ : syracuseStep 35238491 = 52857737) B52857737
theorem B603071 : Blo 599292 603071 := bstep (se 1 (by rfl) ⟨452303, by rfl⟩ : syracuseStep 603071 = 904607) B904607
theorem B10433555 : Blo 599292 10433555 := bstep (se 1 (by rfl) ⟨7825166, by rfl⟩ : syracuseStep 10433555 = 15650333) B15650333
theorem B898943 : Blo 599292 898943 := bstep (se 1 (by rfl) ⟨674207, by rfl⟩ : syracuseStep 898943 = 1348415) B1348415
theorem B1522091 : Blo 599292 1522091 := bstep (se 1 (by rfl) ⟨1141568, by rfl⟩ : syracuseStep 1522091 = 2283137) B2283137
theorem B4111663 : Blo 599292 4111663 := bstep (se 1 (by rfl) ⟨3083747, by rfl⟩ : syracuseStep 4111663 = 6167495) B6167495
theorem B900635 : Blo 599292 900635 := bstep (se 1 (by rfl) ⟨675476, by rfl⟩ : syracuseStep 900635 = 1350953) B1350953
theorem B14859931 : Blo 599292 14859931 := bstep (se 1 (by rfl) ⟨11144948, by rfl⟩ : syracuseStep 14859931 = 22289897) B22289897
theorem B900767 : Blo 599292 900767 := bstep (se 1 (by rfl) ⟨675575, by rfl⟩ : syracuseStep 900767 = 1351151) B1351151
theorem B1523873 : Blo 599292 1523873 := bstep (se 2 (by rfl) ⟨571452, by rfl⟩ : syracuseStep 1523873 = 1142905) B1142905
theorem B7914617 : Blo 599292 7914617 := bstep (se 2 (by rfl) ⟨2967981, by rfl⟩ : syracuseStep 7914617 = 5935963) B5935963
theorem B902711 : Blo 599292 902711 := bstep (se 1 (by rfl) ⟨677033, by rfl⟩ : syracuseStep 902711 = 1354067) B1354067
theorem B7718813 : Blo 599292 7718813 := bstep (se 3 (by rfl) ⟨1447277, by rfl⟩ : syracuseStep 7718813 = 2894555) B2894555
theorem B903983 : Blo 599292 903983 := bstep (se 1 (by rfl) ⟨677987, by rfl⟩ : syracuseStep 903983 = 1355975) B1355975
theorem B904007 : Blo 599292 904007 := bstep (se 1 (by rfl) ⟨678005, by rfl⟩ : syracuseStep 904007 = 1356011) B1356011
theorem B4344715 : Blo 599292 4344715 := bstep (se 1 (by rfl) ⟨3258536, by rfl⟩ : syracuseStep 4344715 = 6517073) B6517073
theorem B904283 : Blo 599292 904283 := bstep (se 1 (by rfl) ⟨678212, by rfl⟩ : syracuseStep 904283 = 1356425) B1356425
theorem B3427667 : Blo 599292 3427667 := bstep (se 1 (by rfl) ⟨2570750, by rfl⟩ : syracuseStep 3427667 = 5141501) B5141501
theorem B904775 : Blo 599292 904775 := bstep (se 1 (by rfl) ⟨678581, by rfl⟩ : syracuseStep 904775 = 1357163) B1357163
theorem B1628059 : Blo 599292 1628059 := bstep (se 1 (by rfl) ⟨1221044, by rfl⟩ : syracuseStep 1628059 = 2442089) B2442089
theorem B19456645 : Blo 599292 19456645 := bstep (se 4 (by rfl) ⟨1824060, by rfl⟩ : syracuseStep 19456645 = 3648121) B3648121
theorem B3041063 : Blo 599292 3041063 := bstep (se 1 (by rfl) ⟨2280797, by rfl⟩ : syracuseStep 3041063 = 4561595) B4561595
theorem B1140551 : Blo 599292 1140551 := bstep (se 1 (by rfl) ⟨855413, by rfl⟩ : syracuseStep 1140551 = 1710827) B1710827
theorem B1141303 : Blo 599292 1141303 := bstep (se 1 (by rfl) ⟨855977, by rfl⟩ : syracuseStep 1141303 = 1711955) B1711955
theorem B2288681 : Blo 599292 2288681 := bstep (se 2 (by rfl) ⟨858255, by rfl⟩ : syracuseStep 2288681 = 1716511) B1716511
theorem B7500377 : Blo 599292 7500377 := bstep (se 2 (by rfl) ⟨2812641, by rfl⟩ : syracuseStep 7500377 = 5625283) B5625283
theorem B3045599 : Blo 599292 3045599 := bstep (se 1 (by rfl) ⟨2284199, by rfl⟩ : syracuseStep 3045599 = 4568399) B4568399
theorem B14876111 : Blo 599292 14876111 := bstep (se 1 (by rfl) ⟨11157083, by rfl⟩ : syracuseStep 14876111 = 22314167) B22314167
theorem B1015915 : Blo 599292 1015915 := bstep (se 1 (by rfl) ⟨761936, by rfl⟩ : syracuseStep 1015915 = 1523873) B1523873
theorem B3080587 : Blo 599292 3080587 := bstep (se 1 (by rfl) ⟨2310440, by rfl⟩ : syracuseStep 3080587 = 4620881) B4620881
theorem B1442387 : Blo 599292 1442387 := bstep (se 1 (by rfl) ⟨1081790, by rfl⟩ : syracuseStep 1442387 = 2163581) B2163581
theorem B5276411 : Blo 599292 5276411 := bstep (se 1 (by rfl) ⟨3957308, by rfl⟩ : syracuseStep 5276411 = 7914617) B7914617
theorem B5145875 : Blo 599292 5145875 := bstep (se 1 (by rfl) ⟨3859406, by rfl⟩ : syracuseStep 5145875 = 7718813) B7718813
theorem B2561183 : Blo 599292 2561183 := bstep (se 1 (by rfl) ⟨1920887, by rfl⟩ : syracuseStep 2561183 = 3841775) B3841775
theorem B2889695 : Blo 599292 2889695 := bstep (se 1 (by rfl) ⟨2167271, by rfl⟩ : syracuseStep 2889695 = 4334543) B4334543
theorem B760367 : Blo 599292 760367 := bstep (se 1 (by rfl) ⟨570275, by rfl⟩ : syracuseStep 760367 = 1140551) B1140551
theorem B2170745 : Blo 599292 2170745 := bstep (se 2 (by rfl) ⟨814029, by rfl⟩ : syracuseStep 2170745 = 1628059) B1628059
theorem B6955703 : Blo 599292 6955703 := bstep (se 1 (by rfl) ⟨5216777, by rfl⟩ : syracuseStep 6955703 = 10433555) B10433555
theorem B599295 : Blo 599292 599295 := bstep (se 1 (by rfl) ⟨449471, by rfl⟩ : syracuseStep 599295 = 898943) B898943
theorem B5482217 : Blo 599292 5482217 := bstep (se 2 (by rfl) ⟨2055831, by rfl⟩ : syracuseStep 5482217 = 4111663) B4111663
theorem B600423 : Blo 599292 600423 := bstep (se 1 (by rfl) ⟨450317, by rfl⟩ : syracuseStep 600423 = 900635) B900635
theorem B600511 : Blo 599292 600511 := bstep (se 1 (by rfl) ⟨450383, by rfl⟩ : syracuseStep 600511 = 900767) B900767
theorem B601807 : Blo 599292 601807 := bstep (se 1 (by rfl) ⟨451355, by rfl⟩ : syracuseStep 601807 = 902711) B902711
theorem B1355687 : Blo 599292 1355687 := bstep (se 1 (by rfl) ⟨1016765, by rfl⟩ : syracuseStep 1355687 = 2033531) B2033531
theorem B20001005 : Blo 599292 20001005 := bstep (se 3 (by rfl) ⟨3750188, by rfl⟩ : syracuseStep 20001005 = 7500377) B7500377
theorem B602655 : Blo 599292 602655 := bstep (se 1 (by rfl) ⟨451991, by rfl⟩ : syracuseStep 602655 = 903983) B903983
theorem B602671 : Blo 599292 602671 := bstep (se 1 (by rfl) ⟨452003, by rfl⟩ : syracuseStep 602671 = 904007) B904007
theorem B602855 : Blo 599292 602855 := bstep (se 1 (by rfl) ⟨452141, by rfl⟩ : syracuseStep 602855 = 904283) B904283
theorem B603183 : Blo 599292 603183 := bstep (se 1 (by rfl) ⟨452387, by rfl⟩ : syracuseStep 603183 = 904775) B904775
theorem B11908883 : Blo 599292 11908883 := bstep (se 1 (by rfl) ⟨8931662, by rfl⟩ : syracuseStep 11908883 = 17863325) B17863325
theorem B1521737 : Blo 599292 1521737 := bstep (se 2 (by rfl) ⟨570651, by rfl⟩ : syracuseStep 1521737 = 1141303) B1141303
theorem B899687 : Blo 599292 899687 := bstep (se 1 (by rfl) ⟨674765, by rfl⟩ : syracuseStep 899687 = 1349531) B1349531
theorem B6830729 : Blo 599292 6830729 := bstep (se 2 (by rfl) ⟨2561523, by rfl⟩ : syracuseStep 6830729 = 5123047) B5123047
theorem B901679 : Blo 599292 901679 := bstep (se 1 (by rfl) ⟨676259, by rfl⟩ : syracuseStep 901679 = 1352519) B1352519
theorem B18727703 : Blo 599292 18727703 := bstep (se 1 (by rfl) ⟨14045777, by rfl⟩ : syracuseStep 18727703 = 28091555) B28091555
theorem B1098617 : Blo 599292 1098617 := bstep (se 2 (by rfl) ⟨411981, by rfl⟩ : syracuseStep 1098617 = 823963) B823963
theorem B1525787 : Blo 599292 1525787 := bstep (se 1 (by rfl) ⟨1144340, by rfl⟩ : syracuseStep 1525787 = 2288681) B2288681
theorem B2541961 : Blo 599292 2541961 := bstep (se 2 (by rfl) ⟨953235, by rfl⟩ : syracuseStep 2541961 = 1906471) B1906471
theorem B2279933 : Blo 599292 2279933 := bstep (se 3 (by rfl) ⟨427487, by rfl⟩ : syracuseStep 2279933 = 854975) B854975
theorem B19813241 : Blo 599292 19813241 := bstep (se 2 (by rfl) ⟨7429965, by rfl⟩ : syracuseStep 19813241 = 14859931) B14859931
theorem B9917407 : Blo 599292 9917407 := bstep (se 1 (by rfl) ⟨7438055, by rfl⟩ : syracuseStep 9917407 = 14876111) B14876111
theorem B25942193 : Blo 599292 25942193 := bstep (se 2 (by rfl) ⟨9728322, by rfl⟩ : syracuseStep 25942193 = 19456645) B19456645
theorem B2285111 : Blo 599292 2285111 := bstep (se 1 (by rfl) ⟨1713833, by rfl⟩ : syracuseStep 2285111 = 3427667) B3427667
theorem B2286569 : Blo 599292 2286569 := bstep (se 2 (by rfl) ⟨857463, by rfl⟩ : syracuseStep 2286569 = 1714927) B1714927
theorem B5792953 : Blo 599292 5792953 := bstep (se 2 (by rfl) ⟨2172357, by rfl⟩ : syracuseStep 5792953 = 4344715) B4344715
theorem B2024729 : Blo 599292 2024729 := bstep (se 2 (by rfl) ⟨759273, by rfl⟩ : syracuseStep 2024729 = 1518547) B1518547
theorem B41182987 : Blo 599292 41182987 := bstep (se 1 (by rfl) ⟨30887240, by rfl⟩ : syracuseStep 41182987 = 61774481) B61774481
theorem B5138903 : Blo 599292 5138903 := bstep (se 1 (by rfl) ⟨3854177, by rfl⟩ : syracuseStep 5138903 = 7708355) B7708355
theorem B2027375 : Blo 599292 2027375 := bstep (se 1 (by rfl) ⟨1520531, by rfl⟩ : syracuseStep 2027375 = 3041063) B3041063
theorem B1143551 : Blo 599292 1143551 := bstep (se 1 (by rfl) ⟨857663, by rfl⟩ : syracuseStep 1143551 = 1715327) B1715327
theorem B23492327 : Blo 599292 23492327 := bstep (se 1 (by rfl) ⟨17619245, by rfl⟩ : syracuseStep 23492327 = 35238491) B35238491
theorem B3242621 : Blo 599292 3242621 := bstep (se 3 (by rfl) ⟨607991, by rfl⟩ : syracuseStep 3242621 = 1215983) B1215983
theorem B2030399 : Blo 599292 2030399 := bstep (se 1 (by rfl) ⟨1522799, by rfl⟩ : syracuseStep 2030399 = 3045599) B3045599
theorem B1014727 : Blo 599292 1014727 := bstep (se 1 (by rfl) ⟨761045, by rfl⟩ : syracuseStep 1014727 = 1522091) B1522091
theorem B12485135 : Blo 599292 12485135 := bstep (se 1 (by rfl) ⟨9363851, by rfl⟩ : syracuseStep 12485135 = 18727703) B18727703
theorem B1017191 : Blo 599292 1017191 := bstep (se 1 (by rfl) ⟨762893, by rfl⟩ : syracuseStep 1017191 = 1525787) B1525787
theorem B13208827 : Blo 599292 13208827 := bstep (se 1 (by rfl) ⟨9906620, by rfl⟩ : syracuseStep 13208827 = 19813241) B19813241
theorem B1707455 : Blo 599292 1707455 := bstep (se 1 (by rfl) ⟨1280591, by rfl⟩ : syracuseStep 1707455 = 2561183) B2561183
theorem B52892837 : Blo 599292 52892837 := bstep (se 4 (by rfl) ⟨4958703, by rfl⟩ : syracuseStep 52892837 = 9917407) B9917407
theorem B1447163 : Blo 599292 1447163 := bstep (se 1 (by rfl) ⟨1085372, by rfl⟩ : syracuseStep 1447163 = 2170745) B2170745
theorem B1349819 : Blo 599292 1349819 := bstep (se 1 (by rfl) ⟨1012364, by rfl⟩ : syracuseStep 1349819 = 2024729) B2024729
theorem B1351583 : Blo 599292 1351583 := bstep (se 1 (by rfl) ⟨1013687, by rfl⟩ : syracuseStep 1351583 = 2027375) B2027375
theorem B762367 : Blo 599292 762367 := bstep (se 1 (by rfl) ⟨571775, by rfl⟩ : syracuseStep 762367 = 1143551) B1143551
theorem B7939255 : Blo 599292 7939255 := bstep (se 1 (by rfl) ⟨5954441, by rfl⟩ : syracuseStep 7939255 = 11908883) B11908883
theorem B1352969 : Blo 599292 1352969 := bstep (se 2 (by rfl) ⟨507363, by rfl⟩ : syracuseStep 1352969 = 1014727) B1014727
theorem B599791 : Blo 599292 599791 := bstep (se 1 (by rfl) ⟨449843, by rfl⟩ : syracuseStep 599791 = 899687) B899687
theorem B1353599 : Blo 599292 1353599 := bstep (se 1 (by rfl) ⟨1015199, by rfl⟩ : syracuseStep 1353599 = 2030399) B2030399
theorem B1354553 : Blo 599292 1354553 := bstep (se 2 (by rfl) ⟨507957, by rfl⟩ : syracuseStep 1354553 = 1015915) B1015915
theorem B601119 : Blo 599292 601119 := bstep (se 1 (by rfl) ⟨450839, by rfl⟩ : syracuseStep 601119 = 901679) B901679
theorem B3517607 : Blo 599292 3517607 := bstep (se 1 (by rfl) ⟨2638205, by rfl⟩ : syracuseStep 3517607 = 5276411) B5276411
theorem B4107449 : Blo 599292 4107449 := bstep (se 2 (by rfl) ⟨1540293, by rfl⟩ : syracuseStep 4107449 = 3080587) B3080587
theorem B3846365 : Blo 599292 3846365 := bstep (se 3 (by rfl) ⟨721193, by rfl⟩ : syracuseStep 3846365 = 1442387) B1442387
theorem B1519955 : Blo 599292 1519955 := bstep (se 1 (by rfl) ⟨1139966, by rfl⟩ : syracuseStep 1519955 = 2279933) B2279933
theorem B2929645 : Blo 599292 2929645 := bstep (se 3 (by rfl) ⟨549308, by rfl⟩ : syracuseStep 2929645 = 1098617) B1098617
theorem B1523407 : Blo 599292 1523407 := bstep (se 1 (by rfl) ⟨1142555, by rfl⟩ : syracuseStep 1523407 = 2285111) B2285111
theorem B4637135 : Blo 599292 4637135 := bstep (se 1 (by rfl) ⟨3477851, by rfl⟩ : syracuseStep 4637135 = 6955703) B6955703
theorem B1524379 : Blo 599292 1524379 := bstep (se 1 (by rfl) ⟨1143284, by rfl⟩ : syracuseStep 1524379 = 2286569) B2286569
theorem B3654811 : Blo 599292 3654811 := bstep (se 1 (by rfl) ⟨2741108, by rfl⟩ : syracuseStep 3654811 = 5482217) B5482217
theorem B3425935 : Blo 599292 3425935 := bstep (se 1 (by rfl) ⟨2569451, by rfl⟩ : syracuseStep 3425935 = 5138903) B5138903
theorem B903791 : Blo 599292 903791 := bstep (se 1 (by rfl) ⟨677843, by rfl⟩ : syracuseStep 903791 = 1355687) B1355687
theorem B3430583 : Blo 599292 3430583 := bstep (se 1 (by rfl) ⟨2572937, by rfl⟩ : syracuseStep 3430583 = 5145875) B5145875
theorem B7723937 : Blo 599292 7723937 := bstep (se 2 (by rfl) ⟨2896476, by rfl⟩ : syracuseStep 7723937 = 5792953) B5792953
theorem B13557125 : Blo 599292 13557125 := bstep (se 4 (by rfl) ⟨1270980, by rfl⟩ : syracuseStep 13557125 = 2541961) B2541961
theorem B54910649 : Blo 599292 54910649 := bstep (se 2 (by rfl) ⟨20591493, by rfl⟩ : syracuseStep 54910649 = 41182987) B41182987
theorem B1926463 : Blo 599292 1926463 := bstep (se 1 (by rfl) ⟨1444847, by rfl⟩ : syracuseStep 1926463 = 2889695) B2889695
theorem B17294795 : Blo 599292 17294795 := bstep (se 1 (by rfl) ⟨12971096, by rfl⟩ : syracuseStep 17294795 = 25942193) B25942193
theorem B62646205 : Blo 599292 62646205 := bstep (se 3 (by rfl) ⟨11746163, by rfl⟩ : syracuseStep 62646205 = 23492327) B23492327
theorem B2027645 : Blo 599292 2027645 := bstep (se 3 (by rfl) ⟨380183, by rfl⟩ : syracuseStep 2027645 = 760367) B760367
theorem B13334003 : Blo 599292 13334003 := bstep (se 1 (by rfl) ⟨10000502, by rfl⟩ : syracuseStep 13334003 = 20001005) B20001005
theorem B1014491 : Blo 599292 1014491 := bstep (se 1 (by rfl) ⟨760868, by rfl⟩ : syracuseStep 1014491 = 1521737) B1521737
theorem B2161747 : Blo 599292 2161747 := bstep (se 1 (by rfl) ⟨1621310, by rfl⟩ : syracuseStep 2161747 = 3242621) B3242621
theorem B4553819 : Blo 599292 4553819 := bstep (se 1 (by rfl) ⟨3415364, by rfl⟩ : syracuseStep 4553819 = 6830729) B6830729
theorem B1016489 : Blo 599292 1016489 := bstep (se 2 (by rfl) ⟨381183, by rfl⟩ : syracuseStep 1016489 = 762367) B762367
theorem B2032505 : Blo 599292 2032505 := bstep (se 2 (by rfl) ⟨762189, by rfl⟩ : syracuseStep 2032505 = 1524379) B1524379
theorem B33293693 : Blo 599292 33293693 := bstep (se 3 (by rfl) ⟨6242567, by rfl⟩ : syracuseStep 33293693 = 12485135) B12485135
theorem B10585673 : Blo 599292 10585673 := bstep (se 2 (by rfl) ⟨3969627, by rfl⟩ : syracuseStep 10585673 = 7939255) B7939255
theorem B83528273 : Blo 599292 83528273 := bstep (se 2 (by rfl) ⟨31323102, by rfl⟩ : syracuseStep 83528273 = 62646205) B62646205
theorem B35261891 : Blo 599292 35261891 := bstep (se 1 (by rfl) ⟨26446418, by rfl⟩ : syracuseStep 35261891 = 52892837) B52892837
theorem B5149291 : Blo 599292 5149291 := bstep (se 1 (by rfl) ⟨3861968, by rfl⟩ : syracuseStep 5149291 = 7723937) B7723937
theorem B36607099 : Blo 599292 36607099 := bstep (se 1 (by rfl) ⟨27455324, by rfl⟩ : syracuseStep 36607099 = 54910649) B54910649
theorem B3906193 : Blo 599292 3906193 := bstep (se 2 (by rfl) ⟨1464822, by rfl⟩ : syracuseStep 3906193 = 2929645) B2929645
theorem B1351763 : Blo 599292 1351763 := bstep (se 1 (by rfl) ⟨1013822, by rfl⟩ : syracuseStep 1351763 = 2027645) B2027645
theorem B2564243 : Blo 599292 2564243 := bstep (se 1 (by rfl) ⟨1923182, by rfl⟩ : syracuseStep 2564243 = 3846365) B3846365
theorem B8889335 : Blo 599292 8889335 := bstep (se 1 (by rfl) ⟨6667001, by rfl⟩ : syracuseStep 8889335 = 13334003) B13334003
theorem B12365693 : Blo 599292 12365693 := bstep (se 3 (by rfl) ⟨2318567, by rfl⟩ : syracuseStep 12365693 = 4637135) B4637135
theorem B602527 : Blo 599292 602527 := bstep (se 1 (by rfl) ⟨451895, by rfl⟩ : syracuseStep 602527 = 903791) B903791
theorem B2568617 : Blo 599292 2568617 := bstep (se 2 (by rfl) ⟨963231, by rfl⟩ : syracuseStep 2568617 = 1926463) B1926463
theorem B4567913 : Blo 599292 4567913 := bstep (se 2 (by rfl) ⟨1712967, by rfl⟩ : syracuseStep 4567913 = 3425935) B3425935
theorem B964775 : Blo 599292 964775 := bstep (se 1 (by rfl) ⟨723581, by rfl⟩ : syracuseStep 964775 = 1447163) B1447163
theorem B899879 : Blo 599292 899879 := bstep (se 1 (by rfl) ⟨674909, by rfl⟩ : syracuseStep 899879 = 1349819) B1349819
theorem B17611769 : Blo 599292 17611769 := bstep (se 2 (by rfl) ⟨6604413, by rfl⟩ : syracuseStep 17611769 = 13208827) B13208827
theorem B901055 : Blo 599292 901055 := bstep (se 1 (by rfl) ⟨675791, by rfl⟩ : syracuseStep 901055 = 1351583) B1351583
theorem B901979 : Blo 599292 901979 := bstep (se 1 (by rfl) ⟨676484, by rfl⟩ : syracuseStep 901979 = 1352969) B1352969
theorem B902399 : Blo 599292 902399 := bstep (se 1 (by rfl) ⟨676799, by rfl⟩ : syracuseStep 902399 = 1353599) B1353599
theorem B903035 : Blo 599292 903035 := bstep (se 1 (by rfl) ⟨677276, by rfl⟩ : syracuseStep 903035 = 1354553) B1354553
theorem B2345071 : Blo 599292 2345071 := bstep (se 1 (by rfl) ⟨1758803, by rfl⟩ : syracuseStep 2345071 = 3517607) B3517607
theorem B2738299 : Blo 599292 2738299 := bstep (se 1 (by rfl) ⟨2053724, by rfl⟩ : syracuseStep 2738299 = 4107449) B4107449
theorem B676327 : Blo 599292 676327 := bstep (se 1 (by rfl) ⟨507245, by rfl⟩ : syracuseStep 676327 = 1014491) B1014491
theorem B3035879 : Blo 599292 3035879 := bstep (se 1 (by rfl) ⟨2276909, by rfl⟩ : syracuseStep 3035879 = 4553819) B4553819
theorem B678127 : Blo 599292 678127 := bstep (se 1 (by rfl) ⟨508595, by rfl⟩ : syracuseStep 678127 = 1017191) B1017191
theorem B4873081 : Blo 599292 4873081 := bstep (se 2 (by rfl) ⟨1827405, by rfl⟩ : syracuseStep 4873081 = 3654811) B3654811
theorem B1138303 : Blo 599292 1138303 := bstep (se 1 (by rfl) ⟨853727, by rfl⟩ : syracuseStep 1138303 = 1707455) B1707455
theorem B2287055 : Blo 599292 2287055 := bstep (se 1 (by rfl) ⟨1715291, by rfl⟩ : syracuseStep 2287055 = 3430583) B3430583
theorem B9038083 : Blo 599292 9038083 := bstep (se 1 (by rfl) ⟨6778562, by rfl⟩ : syracuseStep 9038083 = 13557125) B13557125
theorem B11529317 : Blo 599292 11529317 := bstep (se 4 (by rfl) ⟨1080873, by rfl⟩ : syracuseStep 11529317 = 2161747) B2161747
theorem B11529863 : Blo 599292 11529863 := bstep (se 1 (by rfl) ⟨8647397, by rfl⟩ : syracuseStep 11529863 = 17294795) B17294795
theorem B1013303 : Blo 599292 1013303 := bstep (se 1 (by rfl) ⟨759977, by rfl⟩ : syracuseStep 1013303 = 1519955) B1519955
theorem B2031209 : Blo 599292 2031209 := bstep (se 2 (by rfl) ⟨761703, by rfl⟩ : syracuseStep 2031209 = 1523407) B1523407
theorem B1709495 : Blo 599292 1709495 := bstep (se 1 (by rfl) ⟨1282121, by rfl⟩ : syracuseStep 1709495 = 2564243) B2564243
theorem B46964717 : Blo 599292 46964717 := bstep (se 3 (by rfl) ⟨8805884, by rfl⟩ : syracuseStep 46964717 = 17611769) B17611769
theorem B1712411 : Blo 599292 1712411 := bstep (se 1 (by rfl) ⟨1284308, by rfl⟩ : syracuseStep 1712411 = 2568617) B2568617
theorem B6497441 : Blo 599292 6497441 := bstep (se 2 (by rfl) ⟨2436540, by rfl⟩ : syracuseStep 6497441 = 4873081) B4873081
theorem B599919 : Blo 599292 599919 := bstep (se 1 (by rfl) ⟨449939, by rfl⟩ : syracuseStep 599919 = 899879) B899879
theorem B1517737 : Blo 599292 1517737 := bstep (se 2 (by rfl) ⟨569151, by rfl⟩ : syracuseStep 1517737 = 1138303) B1138303
theorem B1354139 : Blo 599292 1354139 := bstep (se 1 (by rfl) ⟨1015604, by rfl⟩ : syracuseStep 1354139 = 2031209) B2031209
theorem B600703 : Blo 599292 600703 := bstep (se 1 (by rfl) ⟨450527, by rfl⟩ : syracuseStep 600703 = 901055) B901055
theorem B601319 : Blo 599292 601319 := bstep (se 1 (by rfl) ⟨450989, by rfl⟩ : syracuseStep 601319 = 901979) B901979
theorem B1355003 : Blo 599292 1355003 := bstep (se 1 (by rfl) ⟨1016252, by rfl⟩ : syracuseStep 1355003 = 2032505) B2032505
theorem B601599 : Blo 599292 601599 := bstep (se 1 (by rfl) ⟨451199, by rfl⟩ : syracuseStep 601599 = 902399) B902399
theorem B22195795 : Blo 599292 22195795 := bstep (se 1 (by rfl) ⟨16646846, by rfl⟩ : syracuseStep 22195795 = 33293693) B33293693
theorem B7057115 : Blo 599292 7057115 := bstep (se 1 (by rfl) ⟨5292836, by rfl⟩ : syracuseStep 7057115 = 10585673) B10585673
theorem B602023 : Blo 599292 602023 := bstep (se 1 (by rfl) ⟨451517, by rfl⟩ : syracuseStep 602023 = 903035) B903035
theorem B55685515 : Blo 599292 55685515 := bstep (se 1 (by rfl) ⟨41764136, by rfl⟩ : syracuseStep 55685515 = 83528273) B83528273
theorem B23507927 : Blo 599292 23507927 := bstep (se 1 (by rfl) ⟨17630945, by rfl⟩ : syracuseStep 23507927 = 35261891) B35261891
theorem B3126761 : Blo 599292 3126761 := bstep (se 2 (by rfl) ⟨1172535, by rfl⟩ : syracuseStep 3126761 = 2345071) B2345071
theorem B3651065 : Blo 599292 3651065 := bstep (se 2 (by rfl) ⟨1369149, by rfl⟩ : syracuseStep 3651065 = 2738299) B2738299
theorem B901175 : Blo 599292 901175 := bstep (se 1 (by rfl) ⟨675881, by rfl⟩ : syracuseStep 901175 = 1351763) B1351763
theorem B901769 : Blo 599292 901769 := bstep (se 2 (by rfl) ⟨338163, by rfl⟩ : syracuseStep 901769 = 676327) B676327
theorem B6865721 : Blo 599292 6865721 := bstep (se 2 (by rfl) ⟨2574645, by rfl⟩ : syracuseStep 6865721 = 5149291) B5149291
theorem B1524703 : Blo 599292 1524703 := bstep (se 1 (by rfl) ⟨1143527, by rfl⟩ : syracuseStep 1524703 = 2287055) B2287055
theorem B48809465 : Blo 599292 48809465 := bstep (se 2 (by rfl) ⟨18303549, by rfl⟩ : syracuseStep 48809465 = 36607099) B36607099
theorem B7686211 : Blo 599292 7686211 := bstep (se 1 (by rfl) ⟨5764658, by rfl⟩ : syracuseStep 7686211 = 11529317) B11529317
theorem B7686575 : Blo 599292 7686575 := bstep (se 1 (by rfl) ⟨5764931, by rfl⟩ : syracuseStep 7686575 = 11529863) B11529863
theorem B8243795 : Blo 599292 8243795 := bstep (se 1 (by rfl) ⟨6182846, by rfl⟩ : syracuseStep 8243795 = 12365693) B12365693
theorem B904169 : Blo 599292 904169 := bstep (se 2 (by rfl) ⟨339063, by rfl⟩ : syracuseStep 904169 = 678127) B678127
theorem B675535 : Blo 599292 675535 := bstep (se 1 (by rfl) ⟨506651, by rfl⟩ : syracuseStep 675535 = 1013303) B1013303
theorem B643183 : Blo 599292 643183 := bstep (se 1 (by rfl) ⟨482387, by rfl⟩ : syracuseStep 643183 = 964775) B964775
theorem B677659 : Blo 599292 677659 := bstep (se 1 (by rfl) ⟨508244, by rfl⟩ : syracuseStep 677659 = 1016489) B1016489
theorem B12050777 : Blo 599292 12050777 := bstep (se 2 (by rfl) ⟨4519041, by rfl⟩ : syracuseStep 12050777 = 9038083) B9038083
theorem B2023919 : Blo 599292 2023919 := bstep (se 1 (by rfl) ⟨1517939, by rfl⟩ : syracuseStep 2023919 = 3035879) B3035879
theorem B5926223 : Blo 599292 5926223 := bstep (se 1 (by rfl) ⟨4444667, by rfl⟩ : syracuseStep 5926223 = 8889335) B8889335
theorem B3045275 : Blo 599292 3045275 := bstep (se 1 (by rfl) ⟨2283956, by rfl⟩ : syracuseStep 3045275 = 4567913) B4567913
theorem B5208257 : Blo 599292 5208257 := bstep (se 2 (by rfl) ⟨1953096, by rfl⟩ : syracuseStep 5208257 = 3906193) B3906193
theorem B32539643 : Blo 599292 32539643 := bstep (se 1 (by rfl) ⟨24404732, by rfl⟩ : syracuseStep 32539643 = 48809465) B48809465
theorem B2032937 : Blo 599292 2032937 := bstep (se 2 (by rfl) ⟨762351, by rfl⟩ : syracuseStep 2032937 = 1524703) B1524703
theorem B29594393 : Blo 599292 29594393 := bstep (se 2 (by rfl) ⟨11097897, by rfl⟩ : syracuseStep 29594393 = 22195795) B22195795
theorem B8033851 : Blo 599292 8033851 := bstep (se 1 (by rfl) ⟨6025388, by rfl⟩ : syracuseStep 8033851 = 12050777) B12050777
theorem B1349279 : Blo 599292 1349279 := bstep (se 1 (by rfl) ⟨1011959, by rfl⟩ : syracuseStep 1349279 = 2023919) B2023919
theorem B4331627 : Blo 599292 4331627 := bstep (se 1 (by rfl) ⟨3248720, by rfl⟩ : syracuseStep 4331627 = 6497441) B6497441
theorem B15671951 : Blo 599292 15671951 := bstep (se 1 (by rfl) ⟨11753963, by rfl⟩ : syracuseStep 15671951 = 23507927) B23507927
theorem B2434043 : Blo 599292 2434043 := bstep (se 1 (by rfl) ⟨1825532, by rfl⟩ : syracuseStep 2434043 = 3651065) B3651065
theorem B600783 : Blo 599292 600783 := bstep (se 1 (by rfl) ⟨450587, by rfl⟩ : syracuseStep 600783 = 901175) B901175
theorem B601179 : Blo 599292 601179 := bstep (se 1 (by rfl) ⟨450884, by rfl⟩ : syracuseStep 601179 = 901769) B901769
theorem B5124383 : Blo 599292 5124383 := bstep (se 1 (by rfl) ⟨3843287, by rfl⟩ : syracuseStep 5124383 = 7686575) B7686575
theorem B602779 : Blo 599292 602779 := bstep (se 1 (by rfl) ⟨452084, by rfl⟩ : syracuseStep 602779 = 904169) B904169
theorem B900713 : Blo 599292 900713 := bstep (se 2 (by rfl) ⟨337767, by rfl⟩ : syracuseStep 900713 = 675535) B675535
theorem B31309811 : Blo 599292 31309811 := bstep (se 1 (by rfl) ⟨23482358, by rfl⟩ : syracuseStep 31309811 = 46964717) B46964717
theorem B902759 : Blo 599292 902759 := bstep (se 1 (by rfl) ⟨677069, by rfl⟩ : syracuseStep 902759 = 1354139) B1354139
theorem B903335 : Blo 599292 903335 := bstep (se 1 (by rfl) ⟨677501, by rfl⟩ : syracuseStep 903335 = 1355003) B1355003
theorem B3950815 : Blo 599292 3950815 := bstep (se 1 (by rfl) ⟨2963111, by rfl⟩ : syracuseStep 3950815 = 5926223) B5926223
theorem B903545 : Blo 599292 903545 := bstep (se 2 (by rfl) ⟨338829, by rfl⟩ : syracuseStep 903545 = 677659) B677659
theorem B4704743 : Blo 599292 4704743 := bstep (se 1 (by rfl) ⟨3528557, by rfl⟩ : syracuseStep 4704743 = 7057115) B7057115
theorem B2084507 : Blo 599292 2084507 := bstep (se 1 (by rfl) ⟨1563380, by rfl⟩ : syracuseStep 2084507 = 3126761) B3126761
theorem B4577147 : Blo 599292 4577147 := bstep (se 1 (by rfl) ⟨3432860, by rfl⟩ : syracuseStep 4577147 = 6865721) B6865721
theorem B3430309 : Blo 599292 3430309 := bstep (se 4 (by rfl) ⟨321591, by rfl⟩ : syracuseStep 3430309 = 643183) B643183
theorem B5495863 : Blo 599292 5495863 := bstep (se 1 (by rfl) ⟨4121897, by rfl⟩ : syracuseStep 5495863 = 8243795) B8243795
theorem B10248281 : Blo 599292 10248281 := bstep (se 2 (by rfl) ⟨3843105, by rfl⟩ : syracuseStep 10248281 = 7686211) B7686211
theorem B2023649 : Blo 599292 2023649 := bstep (se 2 (by rfl) ⟨758868, by rfl⟩ : syracuseStep 2023649 = 1517737) B1517737
theorem B1139663 : Blo 599292 1139663 := bstep (se 1 (by rfl) ⟨854747, by rfl⟩ : syracuseStep 1139663 = 1709495) B1709495
theorem B1141607 : Blo 599292 1141607 := bstep (se 1 (by rfl) ⟨856205, by rfl⟩ : syracuseStep 1141607 = 1712411) B1712411
theorem B13888685 : Blo 599292 13888685 := bstep (se 3 (by rfl) ⟨2604128, by rfl⟩ : syracuseStep 13888685 = 5208257) B5208257
theorem B74247353 : Blo 599292 74247353 := bstep (se 2 (by rfl) ⟨27842757, by rfl⟩ : syracuseStep 74247353 = 55685515) B55685515
theorem B2030183 : Blo 599292 2030183 := bstep (se 1 (by rfl) ⟨1522637, by rfl⟩ : syracuseStep 2030183 = 3045275) B3045275
theorem B21693095 : Blo 599292 21693095 := bstep (se 1 (by rfl) ⟨16269821, by rfl⟩ : syracuseStep 21693095 = 32539643) B32539643
theorem B19729595 : Blo 599292 19729595 := bstep (se 1 (by rfl) ⟨14797196, by rfl⟩ : syracuseStep 19729595 = 29594393) B29594393
theorem B3051431 : Blo 599292 3051431 := bstep (se 1 (by rfl) ⟨2288573, by rfl⟩ : syracuseStep 3051431 = 4577147) B4577147
theorem B2887751 : Blo 599292 2887751 := bstep (se 1 (by rfl) ⟨2165813, by rfl⟩ : syracuseStep 2887751 = 4331627) B4331627
theorem B1349099 : Blo 599292 1349099 := bstep (se 1 (by rfl) ⟨1011824, by rfl⟩ : syracuseStep 1349099 = 2023649) B2023649
theorem B759775 : Blo 599292 759775 := bstep (se 1 (by rfl) ⟨569831, by rfl⟩ : syracuseStep 759775 = 1139663) B1139663
theorem B761071 : Blo 599292 761071 := bstep (se 1 (by rfl) ⟨570803, by rfl⟩ : syracuseStep 761071 = 1141607) B1141607
theorem B3416255 : Blo 599292 3416255 := bstep (se 1 (by rfl) ⟨2562191, by rfl⟩ : syracuseStep 3416255 = 5124383) B5124383
theorem B1353455 : Blo 599292 1353455 := bstep (se 1 (by rfl) ⟨1015091, by rfl⟩ : syracuseStep 1353455 = 2030183) B2030183
theorem B600475 : Blo 599292 600475 := bstep (se 1 (by rfl) ⟨450356, by rfl⟩ : syracuseStep 600475 = 900713) B900713
theorem B1355291 : Blo 599292 1355291 := bstep (se 1 (by rfl) ⟨1016468, by rfl⟩ : syracuseStep 1355291 = 2032937) B2032937
theorem B601839 : Blo 599292 601839 := bstep (se 1 (by rfl) ⟨451379, by rfl⟩ : syracuseStep 601839 = 902759) B902759
theorem B602223 : Blo 599292 602223 := bstep (se 1 (by rfl) ⟨451667, by rfl⟩ : syracuseStep 602223 = 903335) B903335
theorem B602363 : Blo 599292 602363 := bstep (se 1 (by rfl) ⟨451772, by rfl⟩ : syracuseStep 602363 = 903545) B903545
theorem B1389671 : Blo 599292 1389671 := bstep (se 1 (by rfl) ⟨1042253, by rfl⟩ : syracuseStep 1389671 = 2084507) B2084507
theorem B899519 : Blo 599292 899519 := bstep (se 1 (by rfl) ⟨674639, by rfl⟩ : syracuseStep 899519 = 1349279) B1349279
theorem B6832187 : Blo 599292 6832187 := bstep (se 1 (by rfl) ⟨5124140, by rfl⟩ : syracuseStep 6832187 = 10248281) B10248281
theorem B1622695 : Blo 599292 1622695 := bstep (se 1 (by rfl) ⟨1217021, by rfl⟩ : syracuseStep 1622695 = 2434043) B2434043
theorem B9259123 : Blo 599292 9259123 := bstep (se 1 (by rfl) ⟨6944342, by rfl⟩ : syracuseStep 9259123 = 13888685) B13888685
theorem B49498235 : Blo 599292 49498235 := bstep (se 1 (by rfl) ⟨37123676, by rfl⟩ : syracuseStep 49498235 = 74247353) B74247353
theorem B4573745 : Blo 599292 4573745 := bstep (se 2 (by rfl) ⟨1715154, by rfl⟩ : syracuseStep 4573745 = 3430309) B3430309
theorem B7327817 : Blo 599292 7327817 := bstep (se 2 (by rfl) ⟨2747931, by rfl⟩ : syracuseStep 7327817 = 5495863) B5495863
theorem B3136495 : Blo 599292 3136495 := bstep (se 1 (by rfl) ⟨2352371, by rfl⟩ : syracuseStep 3136495 = 4704743) B4704743
theorem B5267753 : Blo 599292 5267753 := bstep (se 2 (by rfl) ⟨1975407, by rfl⟩ : syracuseStep 5267753 = 3950815) B3950815
theorem B10447967 : Blo 599292 10447967 := bstep (se 1 (by rfl) ⟨7835975, by rfl⟩ : syracuseStep 10447967 = 15671951) B15671951
theorem B10711801 : Blo 599292 10711801 := bstep (se 2 (by rfl) ⟨4016925, by rfl⟩ : syracuseStep 10711801 = 8033851) B8033851
theorem B20873207 : Blo 599292 20873207 := bstep (se 1 (by rfl) ⟨15654905, by rfl⟩ : syracuseStep 20873207 = 31309811) B31309811
theorem B4554791 : Blo 599292 4554791 := bstep (se 1 (by rfl) ⟨3416093, by rfl⟩ : syracuseStep 4554791 = 6832187) B6832187
theorem B7700669 : Blo 599292 7700669 := bstep (se 3 (by rfl) ⟨1443875, by rfl⟩ : syracuseStep 7700669 = 2887751) B2887751
theorem B2163593 : Blo 599292 2163593 := bstep (se 2 (by rfl) ⟨811347, by rfl⟩ : syracuseStep 2163593 = 1622695) B1622695
theorem B32998823 : Blo 599292 32998823 := bstep (se 1 (by rfl) ⟨24749117, by rfl⟩ : syracuseStep 32998823 = 49498235) B49498235
theorem B3049163 : Blo 599292 3049163 := bstep (se 1 (by rfl) ⟨2286872, by rfl⟩ : syracuseStep 3049163 = 4573745) B4573745
theorem B2034287 : Blo 599292 2034287 := bstep (se 1 (by rfl) ⟨1525715, by rfl⟩ : syracuseStep 2034287 = 3051431) B3051431
theorem B4885211 : Blo 599292 4885211 := bstep (se 1 (by rfl) ⟨3663908, by rfl⟩ : syracuseStep 4885211 = 7327817) B7327817
theorem B3511835 : Blo 599292 3511835 := bstep (se 1 (by rfl) ⟨2633876, by rfl⟩ : syracuseStep 3511835 = 5267753) B5267753
theorem B926447 : Blo 599292 926447 := bstep (se 1 (by rfl) ⟨694835, by rfl⟩ : syracuseStep 926447 = 1389671) B1389671
theorem B599679 : Blo 599292 599679 := bstep (se 1 (by rfl) ⟨449759, by rfl⟩ : syracuseStep 599679 = 899519) B899519
theorem B14462063 : Blo 599292 14462063 := bstep (se 1 (by rfl) ⟨10846547, by rfl⟩ : syracuseStep 14462063 = 21693095) B21693095
theorem B13153063 : Blo 599292 13153063 := bstep (se 1 (by rfl) ⟨9864797, by rfl⟩ : syracuseStep 13153063 = 19729595) B19729595
theorem B899399 : Blo 599292 899399 := bstep (se 1 (by rfl) ⟨674549, by rfl⟩ : syracuseStep 899399 = 1349099) B1349099
theorem B2277503 : Blo 599292 2277503 := bstep (se 1 (by rfl) ⟨1708127, by rfl⟩ : syracuseStep 2277503 = 3416255) B3416255
theorem B902303 : Blo 599292 902303 := bstep (se 1 (by rfl) ⟨676727, by rfl⟩ : syracuseStep 902303 = 1353455) B1353455
theorem B6965311 : Blo 599292 6965311 := bstep (se 1 (by rfl) ⟨5223983, by rfl⟩ : syracuseStep 6965311 = 10447967) B10447967
theorem B903527 : Blo 599292 903527 := bstep (se 1 (by rfl) ⟨677645, by rfl⟩ : syracuseStep 903527 = 1355291) B1355291
theorem B4181993 : Blo 599292 4181993 := bstep (se 2 (by rfl) ⟨1568247, by rfl⟩ : syracuseStep 4181993 = 3136495) B3136495
theorem B13915471 : Blo 599292 13915471 := bstep (se 1 (by rfl) ⟨10436603, by rfl⟩ : syracuseStep 13915471 = 20873207) B20873207
theorem B12345497 : Blo 599292 12345497 := bstep (se 2 (by rfl) ⟨4629561, by rfl⟩ : syracuseStep 12345497 = 9259123) B9259123
theorem B14282401 : Blo 599292 14282401 := bstep (se 2 (by rfl) ⟨5355900, by rfl⟩ : syracuseStep 14282401 = 10711801) B10711801
theorem B1013033 : Blo 599292 1013033 := bstep (se 2 (by rfl) ⟨379887, by rfl⟩ : syracuseStep 1013033 = 759775) B759775
theorem B1014761 : Blo 599292 1014761 := bstep (se 2 (by rfl) ⟨380535, by rfl⟩ : syracuseStep 1014761 = 761071) B761071
theorem B1442395 : Blo 599292 1442395 := bstep (se 1 (by rfl) ⟨1081796, by rfl⟩ : syracuseStep 1442395 = 2163593) B2163593
theorem B2032775 : Blo 599292 2032775 := bstep (se 1 (by rfl) ⟨1524581, by rfl⟩ : syracuseStep 2032775 = 3049163) B3049163
theorem B2787995 : Blo 599292 2787995 := bstep (se 1 (by rfl) ⟨2090996, by rfl⟩ : syracuseStep 2787995 = 4181993) B4181993
theorem B19043201 : Blo 599292 19043201 := bstep (se 2 (by rfl) ⟨7141200, by rfl⟩ : syracuseStep 19043201 = 14282401) B14282401
theorem B8230331 : Blo 599292 8230331 := bstep (se 1 (by rfl) ⟨6172748, by rfl⟩ : syracuseStep 8230331 = 12345497) B12345497
theorem B17537417 : Blo 599292 17537417 := bstep (se 2 (by rfl) ⟨6576531, by rfl⟩ : syracuseStep 17537417 = 13153063) B13153063
theorem B18553961 : Blo 599292 18553961 := bstep (se 2 (by rfl) ⟨6957735, by rfl⟩ : syracuseStep 18553961 = 13915471) B13915471
theorem B9641375 : Blo 599292 9641375 := bstep (se 1 (by rfl) ⟨7231031, by rfl⟩ : syracuseStep 9641375 = 14462063) B14462063
theorem B599599 : Blo 599292 599599 := bstep (se 1 (by rfl) ⟨449699, by rfl⟩ : syracuseStep 599599 = 899399) B899399
theorem B1518335 : Blo 599292 1518335 := bstep (se 1 (by rfl) ⟨1138751, by rfl⟩ : syracuseStep 1518335 = 2277503) B2277503
theorem B601535 : Blo 599292 601535 := bstep (se 1 (by rfl) ⟨451151, by rfl⟩ : syracuseStep 601535 = 902303) B902303
theorem B21999215 : Blo 599292 21999215 := bstep (se 1 (by rfl) ⟨16499411, by rfl⟩ : syracuseStep 21999215 = 32998823) B32998823
theorem B602351 : Blo 599292 602351 := bstep (se 1 (by rfl) ⟨451763, by rfl⟩ : syracuseStep 602351 = 903527) B903527
theorem B1356191 : Blo 599292 1356191 := bstep (se 1 (by rfl) ⟨1017143, by rfl⟩ : syracuseStep 1356191 = 2034287) B2034287
theorem B9287081 : Blo 599292 9287081 := bstep (se 2 (by rfl) ⟨3482655, by rfl⟩ : syracuseStep 9287081 = 6965311) B6965311
theorem B2341223 : Blo 599292 2341223 := bstep (se 1 (by rfl) ⟨1755917, by rfl⟩ : syracuseStep 2341223 = 3511835) B3511835
theorem B13027229 : Blo 599292 13027229 := bstep (se 3 (by rfl) ⟨2442605, by rfl⟩ : syracuseStep 13027229 = 4885211) B4885211
theorem B9882101 : Blo 599292 9882101 := bstep (se 5 (by rfl) ⟨463223, by rfl⟩ : syracuseStep 9882101 = 926447) B926447
theorem B675355 : Blo 599292 675355 := bstep (se 1 (by rfl) ⟨506516, by rfl⟩ : syracuseStep 675355 = 1013033) B1013033
theorem B676507 : Blo 599292 676507 := bstep (se 1 (by rfl) ⟨507380, by rfl⟩ : syracuseStep 676507 = 1014761) B1014761
theorem B3036527 : Blo 599292 3036527 := bstep (se 1 (by rfl) ⟨2277395, by rfl⟩ : syracuseStep 3036527 = 4554791) B4554791
theorem B5133779 : Blo 599292 5133779 := bstep (se 1 (by rfl) ⟨3850334, by rfl⟩ : syracuseStep 5133779 = 7700669) B7700669
theorem B8684819 : Blo 599292 8684819 := bstep (se 1 (by rfl) ⟨6513614, by rfl⟩ : syracuseStep 8684819 = 13027229) B13027229
theorem B6588067 : Blo 599292 6588067 := bstep (se 1 (by rfl) ⟨4941050, by rfl⟩ : syracuseStep 6588067 = 9882101) B9882101
theorem B6427583 : Blo 599292 6427583 := bstep (se 1 (by rfl) ⟨4820687, by rfl⟩ : syracuseStep 6427583 = 9641375) B9641375
theorem B1355183 : Blo 599292 1355183 := bstep (se 1 (by rfl) ⟨1016387, by rfl⟩ : syracuseStep 1355183 = 2032775) B2032775
theorem B12695467 : Blo 599292 12695467 := bstep (se 1 (by rfl) ⟨9521600, by rfl⟩ : syracuseStep 12695467 = 19043201) B19043201
theorem B5486887 : Blo 599292 5486887 := bstep (se 1 (by rfl) ⟨4115165, by rfl⟩ : syracuseStep 5486887 = 8230331) B8230331
theorem B3422519 : Blo 599292 3422519 := bstep (se 1 (by rfl) ⟨2566889, by rfl⟩ : syracuseStep 3422519 = 5133779) B5133779
theorem B900473 : Blo 599292 900473 := bstep (se 2 (by rfl) ⟨337677, by rfl⟩ : syracuseStep 900473 = 675355) B675355
theorem B12369307 : Blo 599292 12369307 := bstep (se 1 (by rfl) ⟨9276980, by rfl⟩ : syracuseStep 12369307 = 18553961) B18553961
theorem B902009 : Blo 599292 902009 := bstep (se 2 (by rfl) ⟨338253, by rfl⟩ : syracuseStep 902009 = 676507) B676507
theorem B14666143 : Blo 599292 14666143 := bstep (se 1 (by rfl) ⟨10999607, by rfl⟩ : syracuseStep 14666143 = 21999215) B21999215
theorem B904127 : Blo 599292 904127 := bstep (se 1 (by rfl) ⟨678095, by rfl⟩ : syracuseStep 904127 = 1356191) B1356191
theorem B1560815 : Blo 599292 1560815 := bstep (se 1 (by rfl) ⟨1170611, by rfl⟩ : syracuseStep 1560815 = 2341223) B2341223
theorem B1923193 : Blo 599292 1923193 := bstep (se 2 (by rfl) ⟨721197, by rfl⟩ : syracuseStep 1923193 = 1442395) B1442395
theorem B1858663 : Blo 599292 1858663 := bstep (se 1 (by rfl) ⟨1393997, by rfl⟩ : syracuseStep 1858663 = 2787995) B2787995
theorem B2024351 : Blo 599292 2024351 := bstep (se 1 (by rfl) ⟨1518263, by rfl⟩ : syracuseStep 2024351 = 3036527) B3036527
theorem B11691611 : Blo 599292 11691611 := bstep (se 1 (by rfl) ⟨8768708, by rfl⟩ : syracuseStep 11691611 = 17537417) B17537417
theorem B1012223 : Blo 599292 1012223 := bstep (se 1 (by rfl) ⟨759167, by rfl⟩ : syracuseStep 1012223 = 1518335) B1518335
theorem B6191387 : Blo 599292 6191387 := bstep (se 1 (by rfl) ⟨4643540, by rfl⟩ : syracuseStep 6191387 = 9287081) B9287081
theorem B10257029 : Blo 599292 10257029 := bstep (se 4 (by rfl) ⟨961596, by rfl⟩ : syracuseStep 10257029 = 1923193) B1923193
theorem B8784089 : Blo 599292 8784089 := bstep (se 2 (by rfl) ⟨3294033, by rfl⟩ : syracuseStep 8784089 = 6588067) B6588067
theorem B1349567 : Blo 599292 1349567 := bstep (se 1 (by rfl) ⟨1012175, by rfl⟩ : syracuseStep 1349567 = 2024351) B2024351
theorem B7315849 : Blo 599292 7315849 := bstep (se 2 (by rfl) ⟨2743443, by rfl⟩ : syracuseStep 7315849 = 5486887) B5486887
theorem B16492409 : Blo 599292 16492409 := bstep (se 2 (by rfl) ⟨6184653, by rfl⟩ : syracuseStep 16492409 = 12369307) B12369307
theorem B600315 : Blo 599292 600315 := bstep (se 1 (by rfl) ⟨450236, by rfl⟩ : syracuseStep 600315 = 900473) B900473
theorem B601339 : Blo 599292 601339 := bstep (se 1 (by rfl) ⟨451004, by rfl⟩ : syracuseStep 601339 = 902009) B902009
theorem B602751 : Blo 599292 602751 := bstep (se 1 (by rfl) ⟨452063, by rfl⟩ : syracuseStep 602751 = 904127) B904127
theorem B903455 : Blo 599292 903455 := bstep (se 1 (by rfl) ⟨677591, by rfl⟩ : syracuseStep 903455 = 1355183) B1355183
theorem B16927289 : Blo 599292 16927289 := bstep (se 2 (by rfl) ⟨6347733, by rfl⟩ : syracuseStep 16927289 = 12695467) B12695467
theorem B674815 : Blo 599292 674815 := bstep (se 1 (by rfl) ⟨506111, by rfl⟩ : syracuseStep 674815 = 1012223) B1012223
theorem B2478217 : Blo 599292 2478217 := bstep (se 2 (by rfl) ⟨929331, by rfl⟩ : syracuseStep 2478217 = 1858663) B1858663
theorem B2281679 : Blo 599292 2281679 := bstep (se 1 (by rfl) ⟨1711259, by rfl⟩ : syracuseStep 2281679 = 3422519) B3422519
theorem B5789879 : Blo 599292 5789879 := bstep (se 1 (by rfl) ⟨4342409, by rfl⟩ : syracuseStep 5789879 = 8684819) B8684819
theorem B1040543 : Blo 599292 1040543 := bstep (se 1 (by rfl) ⟨780407, by rfl⟩ : syracuseStep 1040543 = 1560815) B1560815
theorem B19554857 : Blo 599292 19554857 := bstep (se 2 (by rfl) ⟨7333071, by rfl⟩ : syracuseStep 19554857 = 14666143) B14666143
theorem B4285055 : Blo 599292 4285055 := bstep (se 1 (by rfl) ⟨3213791, by rfl⟩ : syracuseStep 4285055 = 6427583) B6427583
theorem B7794407 : Blo 599292 7794407 := bstep (se 1 (by rfl) ⟨5845805, by rfl⟩ : syracuseStep 7794407 = 11691611) B11691611
theorem B4127591 : Blo 599292 4127591 := bstep (se 1 (by rfl) ⟨3095693, by rfl⟩ : syracuseStep 4127591 = 6191387) B6191387
theorem B693695 : Blo 599292 693695 := bstep (se 1 (by rfl) ⟨520271, by rfl⟩ : syracuseStep 693695 = 1040543) B1040543
theorem B2856703 : Blo 599292 2856703 := bstep (se 1 (by rfl) ⟨2142527, by rfl⟩ : syracuseStep 2856703 = 4285055) B4285055
theorem B602303 : Blo 599292 602303 := bstep (se 1 (by rfl) ⟨451727, by rfl⟩ : syracuseStep 602303 = 903455) B903455
theorem B11284859 : Blo 599292 11284859 := bstep (se 1 (by rfl) ⟨8463644, by rfl⟩ : syracuseStep 11284859 = 16927289) B16927289
theorem B1521119 : Blo 599292 1521119 := bstep (se 1 (by rfl) ⟨1140839, by rfl⟩ : syracuseStep 1521119 = 2281679) B2281679
theorem B52868629 : Blo 599292 52868629 := bstep (se 6 (by rfl) ⟨1239108, by rfl⟩ : syracuseStep 52868629 = 2478217) B2478217
theorem B899711 : Blo 599292 899711 := bstep (se 1 (by rfl) ⟨674783, by rfl⟩ : syracuseStep 899711 = 1349567) B1349567
theorem B899753 : Blo 599292 899753 := bstep (se 2 (by rfl) ⟨337407, by rfl⟩ : syracuseStep 899753 = 674815) B674815
theorem B10994939 : Blo 599292 10994939 := bstep (se 1 (by rfl) ⟨8246204, by rfl⟩ : syracuseStep 10994939 = 16492409) B16492409
theorem B5196271 : Blo 599292 5196271 := bstep (se 1 (by rfl) ⟨3897203, by rfl⟩ : syracuseStep 5196271 = 7794407) B7794407
theorem B6838019 : Blo 599292 6838019 := bstep (se 1 (by rfl) ⟨5128514, by rfl⟩ : syracuseStep 6838019 = 10257029) B10257029
theorem B9754465 : Blo 599292 9754465 := bstep (se 2 (by rfl) ⟨3657924, by rfl⟩ : syracuseStep 9754465 = 7315849) B7315849
theorem B5856059 : Blo 599292 5856059 := bstep (se 1 (by rfl) ⟨4392044, by rfl⟩ : syracuseStep 5856059 = 8784089) B8784089
theorem B3859919 : Blo 599292 3859919 := bstep (se 1 (by rfl) ⟨2894939, by rfl⟩ : syracuseStep 3859919 = 5789879) B5789879
theorem B13036571 : Blo 599292 13036571 := bstep (se 1 (by rfl) ⟨9777428, by rfl⟩ : syracuseStep 13036571 = 19554857) B19554857
theorem B2751727 : Blo 599292 2751727 := bstep (se 1 (by rfl) ⟨2063795, by rfl⟩ : syracuseStep 2751727 = 4127591) B4127591
theorem B4558679 : Blo 599292 4558679 := bstep (se 1 (by rfl) ⟨3419009, by rfl⟩ : syracuseStep 4558679 = 6838019) B6838019
theorem B3904039 : Blo 599292 3904039 := bstep (se 1 (by rfl) ⟨2928029, by rfl⟩ : syracuseStep 3904039 = 5856059) B5856059
theorem B8691047 : Blo 599292 8691047 := bstep (se 1 (by rfl) ⟨6518285, by rfl⟩ : syracuseStep 8691047 = 13036571) B13036571
theorem B70491505 : Blo 599292 70491505 := bstep (se 2 (by rfl) ⟨26434314, by rfl⟩ : syracuseStep 70491505 = 52868629) B52868629
theorem B3808937 : Blo 599292 3808937 := bstep (se 2 (by rfl) ⟨1428351, by rfl⟩ : syracuseStep 3808937 = 2856703) B2856703
theorem B599807 : Blo 599292 599807 := bstep (se 1 (by rfl) ⟨449855, by rfl⟩ : syracuseStep 599807 = 899711) B899711
theorem B599835 : Blo 599292 599835 := bstep (se 1 (by rfl) ⟨449876, by rfl⟩ : syracuseStep 599835 = 899753) B899753
theorem B6928361 : Blo 599292 6928361 := bstep (se 2 (by rfl) ⟨2598135, by rfl⟩ : syracuseStep 6928361 = 5196271) B5196271
theorem B1849853 : Blo 599292 1849853 := bstep (se 3 (by rfl) ⟨346847, by rfl⟩ : syracuseStep 1849853 = 693695) B693695
theorem B2573279 : Blo 599292 2573279 := bstep (se 1 (by rfl) ⟨1929959, by rfl⟩ : syracuseStep 2573279 = 3859919) B3859919
theorem B7523239 : Blo 599292 7523239 := bstep (se 1 (by rfl) ⟨5642429, by rfl⟩ : syracuseStep 7523239 = 11284859) B11284859
theorem B7329959 : Blo 599292 7329959 := bstep (se 1 (by rfl) ⟨5497469, by rfl⟩ : syracuseStep 7329959 = 10994939) B10994939
theorem B13005953 : Blo 599292 13005953 := bstep (se 2 (by rfl) ⟨4877232, by rfl⟩ : syracuseStep 13005953 = 9754465) B9754465
theorem B1014079 : Blo 599292 1014079 := bstep (se 1 (by rfl) ⟨760559, by rfl⟩ : syracuseStep 1014079 = 1521119) B1521119
theorem B3668969 : Blo 599292 3668969 := bstep (se 2 (by rfl) ⟨1375863, by rfl⟩ : syracuseStep 3668969 = 2751727) B2751727
theorem B10030985 : Blo 599292 10030985 := bstep (se 2 (by rfl) ⟨3761619, by rfl⟩ : syracuseStep 10030985 = 7523239) B7523239
theorem B4886639 : Blo 599292 4886639 := bstep (se 1 (by rfl) ⟨3664979, by rfl⟩ : syracuseStep 4886639 = 7329959) B7329959
theorem B1352105 : Blo 599292 1352105 := bstep (se 2 (by rfl) ⟨507039, by rfl⟩ : syracuseStep 1352105 = 1014079) B1014079
theorem B93988673 : Blo 599292 93988673 := bstep (se 2 (by rfl) ⟨35245752, by rfl⟩ : syracuseStep 93988673 = 70491505) B70491505
theorem B1715519 : Blo 599292 1715519 := bstep (se 1 (by rfl) ⟨1286639, by rfl⟩ : syracuseStep 1715519 = 2573279) B2573279
theorem B2539291 : Blo 599292 2539291 := bstep (se 1 (by rfl) ⟨1904468, by rfl⟩ : syracuseStep 2539291 = 3808937) B3808937
theorem B8670635 : Blo 599292 8670635 := bstep (se 1 (by rfl) ⟨6502976, by rfl⟩ : syracuseStep 8670635 = 13005953) B13005953
theorem B1233235 : Blo 599292 1233235 := bstep (se 1 (by rfl) ⟨924926, by rfl⟩ : syracuseStep 1233235 = 1849853) B1849853
theorem B2445979 : Blo 599292 2445979 := bstep (se 1 (by rfl) ⟨1834484, by rfl⟩ : syracuseStep 2445979 = 3668969) B3668969
theorem B3039119 : Blo 599292 3039119 := bstep (se 1 (by rfl) ⟨2279339, by rfl⟩ : syracuseStep 3039119 = 4558679) B4558679
theorem B5794031 : Blo 599292 5794031 := bstep (se 1 (by rfl) ⟨4345523, by rfl⟩ : syracuseStep 5794031 = 8691047) B8691047
theorem B5205385 : Blo 599292 5205385 := bstep (se 2 (by rfl) ⟨1952019, by rfl⟩ : syracuseStep 5205385 = 3904039) B3904039
theorem B4618907 : Blo 599292 4618907 := bstep (se 1 (by rfl) ⟨3464180, by rfl⟩ : syracuseStep 4618907 = 6928361) B6928361
theorem B6687323 : Blo 599292 6687323 := bstep (se 1 (by rfl) ⟨5015492, by rfl⟩ : syracuseStep 6687323 = 10030985) B10030985
theorem B1644313 : Blo 599292 1644313 := bstep (se 2 (by rfl) ⟨616617, by rfl⟩ : syracuseStep 1644313 = 1233235) B1233235
theorem B62659115 : Blo 599292 62659115 := bstep (se 1 (by rfl) ⟨46994336, by rfl⟩ : syracuseStep 62659115 = 93988673) B93988673
theorem B3385721 : Blo 599292 3385721 := bstep (se 2 (by rfl) ⟨1269645, by rfl⟩ : syracuseStep 3385721 = 2539291) B2539291
theorem B5780423 : Blo 599292 5780423 := bstep (se 1 (by rfl) ⟨4335317, by rfl⟩ : syracuseStep 5780423 = 8670635) B8670635
theorem B3257759 : Blo 599292 3257759 := bstep (se 1 (by rfl) ⟨2443319, by rfl⟩ : syracuseStep 3257759 = 4886639) B4886639
theorem B901403 : Blo 599292 901403 := bstep (se 1 (by rfl) ⟨676052, by rfl⟩ : syracuseStep 901403 = 1352105) B1352105
theorem B3261305 : Blo 599292 3261305 := bstep (se 2 (by rfl) ⟨1222989, by rfl⟩ : syracuseStep 3261305 = 2445979) B2445979
theorem B4574717 : Blo 599292 4574717 := bstep (se 3 (by rfl) ⟨857759, by rfl⟩ : syracuseStep 4574717 = 1715519) B1715519
theorem B6940513 : Blo 599292 6940513 := bstep (se 2 (by rfl) ⟨2602692, by rfl⟩ : syracuseStep 6940513 = 5205385) B5205385
theorem B2026079 : Blo 599292 2026079 := bstep (se 1 (by rfl) ⟨1519559, by rfl⟩ : syracuseStep 2026079 = 3039119) B3039119
theorem B3862687 : Blo 599292 3862687 := bstep (se 1 (by rfl) ⟨2897015, by rfl⟩ : syracuseStep 3862687 = 5794031) B5794031
theorem B3079271 : Blo 599292 3079271 := bstep (se 1 (by rfl) ⟨2309453, by rfl⟩ : syracuseStep 3079271 = 4618907) B4618907
theorem B4458215 : Blo 599292 4458215 := bstep (se 1 (by rfl) ⟨3343661, by rfl⟩ : syracuseStep 4458215 = 6687323) B6687323
theorem B3049811 : Blo 599292 3049811 := bstep (se 1 (by rfl) ⟨2287358, by rfl⟩ : syracuseStep 3049811 = 4574717) B4574717
theorem B8687357 : Blo 599292 8687357 := bstep (se 3 (by rfl) ⟨1628879, by rfl⟩ : syracuseStep 8687357 = 3257759) B3257759
theorem B5150249 : Blo 599292 5150249 := bstep (se 2 (by rfl) ⟨1931343, by rfl⟩ : syracuseStep 5150249 = 3862687) B3862687
theorem B1350719 : Blo 599292 1350719 := bstep (se 1 (by rfl) ⟨1013039, by rfl⟩ : syracuseStep 1350719 = 2026079) B2026079
theorem B600935 : Blo 599292 600935 := bstep (se 1 (by rfl) ⟨450701, by rfl⟩ : syracuseStep 600935 = 901403) B901403
theorem B2174203 : Blo 599292 2174203 := bstep (se 1 (by rfl) ⟨1630652, by rfl⟩ : syracuseStep 2174203 = 3261305) B3261305
theorem B9254017 : Blo 599292 9254017 := bstep (se 2 (by rfl) ⟨3470256, by rfl⟩ : syracuseStep 9254017 = 6940513) B6940513
theorem B3853615 : Blo 599292 3853615 := bstep (se 1 (by rfl) ⟨2890211, by rfl⟩ : syracuseStep 3853615 = 5780423) B5780423
theorem B2052847 : Blo 599292 2052847 := bstep (se 1 (by rfl) ⟨1539635, by rfl⟩ : syracuseStep 2052847 = 3079271) B3079271
theorem B41772743 : Blo 599292 41772743 := bstep (se 1 (by rfl) ⟨31329557, by rfl⟩ : syracuseStep 41772743 = 62659115) B62659115
theorem B2257147 : Blo 599292 2257147 := bstep (se 1 (by rfl) ⟨1692860, by rfl⟩ : syracuseStep 2257147 = 3385721) B3385721
theorem B2192417 : Blo 599292 2192417 := bstep (se 2 (by rfl) ⟨822156, by rfl⟩ : syracuseStep 2192417 = 1644313) B1644313
theorem B2033207 : Blo 599292 2033207 := bstep (se 1 (by rfl) ⟨1524905, by rfl⟩ : syracuseStep 2033207 = 3049811) B3049811
theorem B2898937 : Blo 599292 2898937 := bstep (se 2 (by rfl) ⟨1087101, by rfl⟩ : syracuseStep 2898937 = 2174203) B2174203
theorem B900479 : Blo 599292 900479 := bstep (se 1 (by rfl) ⟨675359, by rfl⟩ : syracuseStep 900479 = 1350719) B1350719
theorem B2737129 : Blo 599292 2737129 := bstep (se 2 (by rfl) ⟨1026423, by rfl⟩ : syracuseStep 2737129 = 2052847) B2052847
theorem B12338689 : Blo 599292 12338689 := bstep (se 2 (by rfl) ⟨4627008, by rfl⟩ : syracuseStep 12338689 = 9254017) B9254017
theorem B1461611 : Blo 599292 1461611 := bstep (se 1 (by rfl) ⟨1096208, by rfl⟩ : syracuseStep 1461611 = 2192417) B2192417
theorem B2972143 : Blo 599292 2972143 := bstep (se 1 (by rfl) ⟨2229107, by rfl⟩ : syracuseStep 2972143 = 4458215) B4458215
theorem B5791571 : Blo 599292 5791571 := bstep (se 1 (by rfl) ⟨4343678, by rfl⟩ : syracuseStep 5791571 = 8687357) B8687357
theorem B3433499 : Blo 599292 3433499 := bstep (se 1 (by rfl) ⟨2575124, by rfl⟩ : syracuseStep 3433499 = 5150249) B5150249
theorem B5138153 : Blo 599292 5138153 := bstep (se 2 (by rfl) ⟨1926807, by rfl⟩ : syracuseStep 5138153 = 3853615) B3853615
theorem B3009529 : Blo 599292 3009529 := bstep (se 2 (by rfl) ⟨1128573, by rfl⟩ : syracuseStep 3009529 = 2257147) B2257147
theorem B27848495 : Blo 599292 27848495 := bstep (se 1 (by rfl) ⟨20886371, by rfl⟩ : syracuseStep 27848495 = 41772743) B41772743
theorem B16451585 : Blo 599292 16451585 := bstep (se 2 (by rfl) ⟨6169344, by rfl⟩ : syracuseStep 16451585 = 12338689) B12338689
theorem B74262653 : Blo 599292 74262653 := bstep (se 3 (by rfl) ⟨13924247, by rfl⟩ : syracuseStep 74262653 = 27848495) B27848495
theorem B600319 : Blo 599292 600319 := bstep (se 1 (by rfl) ⟨450239, by rfl⟩ : syracuseStep 600319 = 900479) B900479
theorem B1355471 : Blo 599292 1355471 := bstep (se 1 (by rfl) ⟨1016603, by rfl⟩ : syracuseStep 1355471 = 2033207) B2033207
theorem B3649505 : Blo 599292 3649505 := bstep (se 2 (by rfl) ⟨1368564, by rfl⟩ : syracuseStep 3649505 = 2737129) B2737129
theorem B4012705 : Blo 599292 4012705 := bstep (se 2 (by rfl) ⟨1504764, by rfl⟩ : syracuseStep 4012705 = 3009529) B3009529
theorem B3425435 : Blo 599292 3425435 := bstep (se 1 (by rfl) ⟨2569076, by rfl⟩ : syracuseStep 3425435 = 5138153) B5138153
theorem B3861047 : Blo 599292 3861047 := bstep (se 1 (by rfl) ⟨2895785, by rfl⟩ : syracuseStep 3861047 = 5791571) B5791571
theorem B2288999 : Blo 599292 2288999 := bstep (se 1 (by rfl) ⟨1716749, by rfl⟩ : syracuseStep 2288999 = 3433499) B3433499
theorem B3962857 : Blo 599292 3962857 := bstep (se 2 (by rfl) ⟨1486071, by rfl⟩ : syracuseStep 3962857 = 2972143) B2972143
theorem B3897629 : Blo 599292 3897629 := bstep (se 3 (by rfl) ⟨730805, by rfl⟩ : syracuseStep 3897629 = 1461611) B1461611
theorem B3865249 : Blo 599292 3865249 := bstep (se 2 (by rfl) ⟨1449468, by rfl⟩ : syracuseStep 3865249 = 2898937) B2898937
theorem B5283809 : Blo 599292 5283809 := bstep (se 2 (by rfl) ⟨1981428, by rfl⟩ : syracuseStep 5283809 = 3962857) B3962857
theorem B5350273 : Blo 599292 5350273 := bstep (se 2 (by rfl) ⟨2006352, by rfl⟩ : syracuseStep 5350273 = 4012705) B4012705
theorem B5153665 : Blo 599292 5153665 := bstep (se 2 (by rfl) ⟨1932624, by rfl⟩ : syracuseStep 5153665 = 3865249) B3865249
theorem B2598419 : Blo 599292 2598419 := bstep (se 1 (by rfl) ⟨1948814, by rfl⟩ : syracuseStep 2598419 = 3897629) B3897629
theorem B2574031 : Blo 599292 2574031 := bstep (se 1 (by rfl) ⟨1930523, by rfl⟩ : syracuseStep 2574031 = 3861047) B3861047
theorem B1525999 : Blo 599292 1525999 := bstep (se 1 (by rfl) ⟨1144499, by rfl⟩ : syracuseStep 1525999 = 2288999) B2288999
theorem B903647 : Blo 599292 903647 := bstep (se 1 (by rfl) ⟨677735, by rfl⟩ : syracuseStep 903647 = 1355471) B1355471
theorem B2283623 : Blo 599292 2283623 := bstep (se 1 (by rfl) ⟨1712717, by rfl⟩ : syracuseStep 2283623 = 3425435) B3425435
theorem B10967723 : Blo 599292 10967723 := bstep (se 1 (by rfl) ⟨8225792, by rfl⟩ : syracuseStep 10967723 = 16451585) B16451585
theorem B49508435 : Blo 599292 49508435 := bstep (se 1 (by rfl) ⟨37131326, by rfl⟩ : syracuseStep 49508435 = 74262653) B74262653
theorem B38928053 : Blo 599292 38928053 := bstep (se 5 (by rfl) ⟨1824752, by rfl⟩ : syracuseStep 38928053 = 3649505) B3649505
theorem B132022493 : Blo 599292 132022493 := bstep (se 3 (by rfl) ⟨24754217, by rfl⟩ : syracuseStep 132022493 = 49508435) B49508435
theorem B2034665 : Blo 599292 2034665 := bstep (se 2 (by rfl) ⟨762999, by rfl⟩ : syracuseStep 2034665 = 1525999) B1525999
theorem B7311815 : Blo 599292 7311815 := bstep (se 1 (by rfl) ⟨5483861, by rfl⟩ : syracuseStep 7311815 = 10967723) B10967723
theorem B602431 : Blo 599292 602431 := bstep (se 1 (by rfl) ⟨451823, by rfl⟩ : syracuseStep 602431 = 903647) B903647
theorem B1522415 : Blo 599292 1522415 := bstep (se 1 (by rfl) ⟨1141811, by rfl⟩ : syracuseStep 1522415 = 2283623) B2283623
theorem B3522539 : Blo 599292 3522539 := bstep (se 1 (by rfl) ⟨2641904, by rfl⟩ : syracuseStep 3522539 = 5283809) B5283809
theorem B6871553 : Blo 599292 6871553 := bstep (se 2 (by rfl) ⟨2576832, by rfl⟩ : syracuseStep 6871553 = 5153665) B5153665
theorem B3432041 : Blo 599292 3432041 := bstep (se 2 (by rfl) ⟨1287015, by rfl⟩ : syracuseStep 3432041 = 2574031) B2574031
theorem B28534789 : Blo 599292 28534789 := bstep (se 4 (by rfl) ⟨2675136, by rfl⟩ : syracuseStep 28534789 = 5350273) B5350273
theorem B1732279 : Blo 599292 1732279 := bstep (se 1 (by rfl) ⟨1299209, by rfl⟩ : syracuseStep 1732279 = 2598419) B2598419
theorem B25952035 : Blo 599292 25952035 := bstep (se 1 (by rfl) ⟨19464026, by rfl⟩ : syracuseStep 25952035 = 38928053) B38928053
theorem B88014995 : Blo 599292 88014995 := bstep (se 1 (by rfl) ⟨66011246, by rfl⟩ : syracuseStep 88014995 = 132022493) B132022493
theorem B38046385 : Blo 599292 38046385 := bstep (se 2 (by rfl) ⟨14267394, by rfl⟩ : syracuseStep 38046385 = 28534789) B28534789
theorem B1356443 : Blo 599292 1356443 := bstep (se 1 (by rfl) ⟨1017332, by rfl⟩ : syracuseStep 1356443 = 2034665) B2034665
theorem B2309705 : Blo 599292 2309705 := bstep (se 2 (by rfl) ⟨866139, by rfl⟩ : syracuseStep 2309705 = 1732279) B1732279
theorem B2348359 : Blo 599292 2348359 := bstep (se 1 (by rfl) ⟨1761269, by rfl⟩ : syracuseStep 2348359 = 3522539) B3522539
theorem B4874543 : Blo 599292 4874543 := bstep (se 1 (by rfl) ⟨3655907, by rfl⟩ : syracuseStep 4874543 = 7311815) B7311815
theorem B4581035 : Blo 599292 4581035 := bstep (se 1 (by rfl) ⟨3435776, by rfl⟩ : syracuseStep 4581035 = 6871553) B6871553
theorem B2288027 : Blo 599292 2288027 := bstep (se 1 (by rfl) ⟨1716020, by rfl⟩ : syracuseStep 2288027 = 3432041) B3432041
theorem B1014943 : Blo 599292 1014943 := bstep (se 1 (by rfl) ⟨761207, by rfl⟩ : syracuseStep 1014943 = 1522415) B1522415
theorem B34602713 : Blo 599292 34602713 := bstep (se 2 (by rfl) ⟨12976017, by rfl⟩ : syracuseStep 34602713 = 25952035) B25952035
theorem B50728513 : Blo 599292 50728513 := bstep (se 2 (by rfl) ⟨19023192, by rfl⟩ : syracuseStep 50728513 = 38046385) B38046385
theorem B3249695 : Blo 599292 3249695 := bstep (se 1 (by rfl) ⟨2437271, by rfl⟩ : syracuseStep 3249695 = 4874543) B4874543
theorem B3054023 : Blo 599292 3054023 := bstep (se 1 (by rfl) ⟨2290517, by rfl⟩ : syracuseStep 3054023 = 4581035) B4581035
theorem B12524581 : Blo 599292 12524581 := bstep (se 4 (by rfl) ⟨1174179, by rfl⟩ : syracuseStep 12524581 = 2348359) B2348359
theorem B1353257 : Blo 599292 1353257 := bstep (se 2 (by rfl) ⟨507471, by rfl⟩ : syracuseStep 1353257 = 1014943) B1014943
theorem B1525351 : Blo 599292 1525351 := bstep (se 1 (by rfl) ⟨1144013, by rfl⟩ : syracuseStep 1525351 = 2288027) B2288027
theorem B904295 : Blo 599292 904295 := bstep (se 1 (by rfl) ⟨678221, by rfl⟩ : syracuseStep 904295 = 1356443) B1356443
theorem B58676663 : Blo 599292 58676663 := bstep (se 1 (by rfl) ⟨44007497, by rfl⟩ : syracuseStep 58676663 = 88014995) B88014995
theorem B1539803 : Blo 599292 1539803 := bstep (se 1 (by rfl) ⟨1154852, by rfl⟩ : syracuseStep 1539803 = 2309705) B2309705
theorem B23068475 : Blo 599292 23068475 := bstep (se 1 (by rfl) ⟨17301356, by rfl⟩ : syracuseStep 23068475 = 34602713) B34602713
theorem B2033801 : Blo 599292 2033801 := bstep (se 2 (by rfl) ⟨762675, by rfl⟩ : syracuseStep 2033801 = 1525351) B1525351
theorem B2166463 : Blo 599292 2166463 := bstep (se 1 (by rfl) ⟨1624847, by rfl⟩ : syracuseStep 2166463 = 3249695) B3249695
theorem B2036015 : Blo 599292 2036015 := bstep (se 1 (by rfl) ⟨1527011, by rfl⟩ : syracuseStep 2036015 = 3054023) B3054023
theorem B67638017 : Blo 599292 67638017 := bstep (se 2 (by rfl) ⟨25364256, by rfl⟩ : syracuseStep 67638017 = 50728513) B50728513
theorem B1026535 : Blo 599292 1026535 := bstep (se 1 (by rfl) ⟨769901, by rfl⟩ : syracuseStep 1026535 = 1539803) B1539803
theorem B15378983 : Blo 599292 15378983 := bstep (se 1 (by rfl) ⟨11534237, by rfl⟩ : syracuseStep 15378983 = 23068475) B23068475
theorem B602863 : Blo 599292 602863 := bstep (se 1 (by rfl) ⟨452147, by rfl⟩ : syracuseStep 602863 = 904295) B904295
theorem B902171 : Blo 599292 902171 := bstep (se 1 (by rfl) ⟨676628, by rfl⟩ : syracuseStep 902171 = 1353257) B1353257
theorem B16699441 : Blo 599292 16699441 := bstep (se 2 (by rfl) ⟨6262290, by rfl⟩ : syracuseStep 16699441 = 12524581) B12524581
theorem B39117775 : Blo 599292 39117775 := bstep (se 1 (by rfl) ⟨29338331, by rfl⟩ : syracuseStep 39117775 = 58676663) B58676663
theorem B45092011 : Blo 599292 45092011 := bstep (se 1 (by rfl) ⟨33819008, by rfl⟩ : syracuseStep 45092011 = 67638017) B67638017
theorem B2888617 : Blo 599292 2888617 := bstep (se 2 (by rfl) ⟨1083231, by rfl⟩ : syracuseStep 2888617 = 2166463) B2166463
theorem B601447 : Blo 599292 601447 := bstep (se 1 (by rfl) ⟨451085, by rfl⟩ : syracuseStep 601447 = 902171) B902171
theorem B1355867 : Blo 599292 1355867 := bstep (se 1 (by rfl) ⟨1016900, by rfl⟩ : syracuseStep 1355867 = 2033801) B2033801
theorem B1357343 : Blo 599292 1357343 := bstep (se 1 (by rfl) ⟨1018007, by rfl⟩ : syracuseStep 1357343 = 2036015) B2036015
theorem B22265921 : Blo 599292 22265921 := bstep (se 2 (by rfl) ⟨8349720, by rfl⟩ : syracuseStep 22265921 = 16699441) B16699441
theorem B52157033 : Blo 599292 52157033 := bstep (se 2 (by rfl) ⟨19558887, by rfl⟩ : syracuseStep 52157033 = 39117775) B39117775
theorem B1368713 : Blo 599292 1368713 := bstep (se 2 (by rfl) ⟨513267, by rfl⟩ : syracuseStep 1368713 = 1026535) B1026535
theorem B10252655 : Blo 599292 10252655 := bstep (se 1 (by rfl) ⟨7689491, by rfl⟩ : syracuseStep 10252655 = 15378983) B15378983
theorem B14843947 : Blo 599292 14843947 := bstep (se 1 (by rfl) ⟨11132960, by rfl⟩ : syracuseStep 14843947 = 22265921) B22265921
theorem B34771355 : Blo 599292 34771355 := bstep (se 1 (by rfl) ⟨26078516, by rfl⟩ : syracuseStep 34771355 = 52157033) B52157033
theorem B3851489 : Blo 599292 3851489 := bstep (se 2 (by rfl) ⟨1444308, by rfl⟩ : syracuseStep 3851489 = 2888617) B2888617
theorem B903911 : Blo 599292 903911 := bstep (se 1 (by rfl) ⟨677933, by rfl⟩ : syracuseStep 903911 = 1355867) B1355867
theorem B6835103 : Blo 599292 6835103 := bstep (se 1 (by rfl) ⟨5126327, by rfl⟩ : syracuseStep 6835103 = 10252655) B10252655
theorem B904895 : Blo 599292 904895 := bstep (se 1 (by rfl) ⟨678671, by rfl⟩ : syracuseStep 904895 = 1357343) B1357343
theorem B60122681 : Blo 599292 60122681 := bstep (se 2 (by rfl) ⟨22546005, by rfl⟩ : syracuseStep 60122681 = 45092011) B45092011
theorem B912475 : Blo 599292 912475 := bstep (se 1 (by rfl) ⟨684356, by rfl⟩ : syracuseStep 912475 = 1368713) B1368713
theorem B19791929 : Blo 599292 19791929 := bstep (se 2 (by rfl) ⟨7421973, by rfl⟩ : syracuseStep 19791929 = 14843947) B14843947
theorem B4556735 : Blo 599292 4556735 := bstep (se 1 (by rfl) ⟨3417551, by rfl⟩ : syracuseStep 4556735 = 6835103) B6835103
theorem B1216633 : Blo 599292 1216633 := bstep (se 2 (by rfl) ⟨456237, by rfl⟩ : syracuseStep 1216633 = 912475) B912475
theorem B40081787 : Blo 599292 40081787 := bstep (se 1 (by rfl) ⟨30061340, by rfl⟩ : syracuseStep 40081787 = 60122681) B60122681
theorem B2567659 : Blo 599292 2567659 := bstep (se 1 (by rfl) ⟨1925744, by rfl⟩ : syracuseStep 2567659 = 3851489) B3851489
theorem B602607 : Blo 599292 602607 := bstep (se 1 (by rfl) ⟨451955, by rfl⟩ : syracuseStep 602607 = 903911) B903911
theorem B603263 : Blo 599292 603263 := bstep (se 1 (by rfl) ⟨452447, by rfl⟩ : syracuseStep 603263 = 904895) B904895
theorem B23180903 : Blo 599292 23180903 := bstep (se 1 (by rfl) ⟨17385677, by rfl⟩ : syracuseStep 23180903 = 34771355) B34771355
theorem B26721191 : Blo 599292 26721191 := bstep (se 1 (by rfl) ⟨20040893, by rfl⟩ : syracuseStep 26721191 = 40081787) B40081787
theorem B3423545 : Blo 599292 3423545 := bstep (se 2 (by rfl) ⟨1283829, by rfl⟩ : syracuseStep 3423545 = 2567659) B2567659
theorem B1622177 : Blo 599292 1622177 := bstep (se 2 (by rfl) ⟨608316, by rfl⟩ : syracuseStep 1622177 = 1216633) B1216633
theorem B15453935 : Blo 599292 15453935 := bstep (se 1 (by rfl) ⟨11590451, by rfl⟩ : syracuseStep 15453935 = 23180903) B23180903
theorem B13194619 : Blo 599292 13194619 := bstep (se 1 (by rfl) ⟨9895964, by rfl⟩ : syracuseStep 13194619 = 19791929) B19791929
theorem B3037823 : Blo 599292 3037823 := bstep (se 1 (by rfl) ⟨2278367, by rfl⟩ : syracuseStep 3037823 = 4556735) B4556735
theorem B1081451 : Blo 599292 1081451 := bstep (se 1 (by rfl) ⟨811088, by rfl⟩ : syracuseStep 1081451 = 1622177) B1622177
theorem B10302623 : Blo 599292 10302623 := bstep (se 1 (by rfl) ⟨7726967, by rfl⟩ : syracuseStep 10302623 = 15453935) B15453935
theorem B70371301 : Blo 599292 70371301 := bstep (se 4 (by rfl) ⟨6597309, by rfl⟩ : syracuseStep 70371301 = 13194619) B13194619
theorem B17814127 : Blo 599292 17814127 := bstep (se 1 (by rfl) ⟨13360595, by rfl⟩ : syracuseStep 17814127 = 26721191) B26721191
theorem B2282363 : Blo 599292 2282363 := bstep (se 1 (by rfl) ⟨1711772, by rfl⟩ : syracuseStep 2282363 = 3423545) B3423545
theorem B2025215 : Blo 599292 2025215 := bstep (se 1 (by rfl) ⟨1518911, by rfl⟩ : syracuseStep 2025215 = 3037823) B3037823
theorem B2883869 : Blo 599292 2883869 := bstep (se 3 (by rfl) ⟨540725, by rfl⟩ : syracuseStep 2883869 = 1081451) B1081451
theorem B1350143 : Blo 599292 1350143 := bstep (se 1 (by rfl) ⟨1012607, by rfl⟩ : syracuseStep 1350143 = 2025215) B2025215
theorem B93828401 : Blo 599292 93828401 := bstep (se 2 (by rfl) ⟨35185650, by rfl⟩ : syracuseStep 93828401 = 70371301) B70371301
theorem B1521575 : Blo 599292 1521575 := bstep (se 1 (by rfl) ⟨1141181, by rfl⟩ : syracuseStep 1521575 = 2282363) B2282363
theorem B6868415 : Blo 599292 6868415 := bstep (se 1 (by rfl) ⟨5151311, by rfl⟩ : syracuseStep 6868415 = 10302623) B10302623
theorem B23752169 : Blo 599292 23752169 := bstep (se 2 (by rfl) ⟨8907063, by rfl⟩ : syracuseStep 23752169 = 17814127) B17814127
theorem B15834779 : Blo 599292 15834779 := bstep (se 1 (by rfl) ⟨11876084, by rfl⟩ : syracuseStep 15834779 = 23752169) B23752169
theorem B900095 : Blo 599292 900095 := bstep (se 1 (by rfl) ⟨675071, by rfl⟩ : syracuseStep 900095 = 1350143) B1350143
theorem B1922579 : Blo 599292 1922579 := bstep (se 1 (by rfl) ⟨1441934, by rfl⟩ : syracuseStep 1922579 = 2883869) B2883869
theorem B62552267 : Blo 599292 62552267 := bstep (se 1 (by rfl) ⟨46914200, by rfl⟩ : syracuseStep 62552267 = 93828401) B93828401
theorem B18315773 : Blo 599292 18315773 := bstep (se 3 (by rfl) ⟨3434207, by rfl⟩ : syracuseStep 18315773 = 6868415) B6868415
theorem B1014383 : Blo 599292 1014383 := bstep (se 1 (by rfl) ⟨760787, by rfl⟩ : syracuseStep 1014383 = 1521575) B1521575
theorem B1281719 : Blo 599292 1281719 := bstep (se 1 (by rfl) ⟨961289, by rfl⟩ : syracuseStep 1281719 = 1922579) B1922579
theorem B10556519 : Blo 599292 10556519 := bstep (se 1 (by rfl) ⟨7917389, by rfl⟩ : syracuseStep 10556519 = 15834779) B15834779
theorem B600063 : Blo 599292 600063 := bstep (se 1 (by rfl) ⟨450047, by rfl⟩ : syracuseStep 600063 = 900095) B900095
theorem B41701511 : Blo 599292 41701511 := bstep (se 1 (by rfl) ⟨31276133, by rfl⟩ : syracuseStep 41701511 = 62552267) B62552267
theorem B12210515 : Blo 599292 12210515 := bstep (se 1 (by rfl) ⟨9157886, by rfl⟩ : syracuseStep 12210515 = 18315773) B18315773
theorem B676255 : Blo 599292 676255 := bstep (se 1 (by rfl) ⟨507191, by rfl⟩ : syracuseStep 676255 = 1014383) B1014383
theorem B854479 : Blo 599292 854479 := bstep (se 1 (by rfl) ⟨640859, by rfl⟩ : syracuseStep 854479 = 1281719) B1281719
theorem B112602869 : Blo 599292 112602869 := bstep (se 5 (by rfl) ⟨5278259, by rfl⟩ : syracuseStep 112602869 = 10556519) B10556519
theorem B8140343 : Blo 599292 8140343 := bstep (se 1 (by rfl) ⟨6105257, by rfl⟩ : syracuseStep 8140343 = 12210515) B12210515
theorem B901673 : Blo 599292 901673 := bstep (se 2 (by rfl) ⟨338127, by rfl⟩ : syracuseStep 901673 = 676255) B676255
theorem B111204029 : Blo 599292 111204029 := bstep (se 3 (by rfl) ⟨20850755, by rfl⟩ : syracuseStep 111204029 = 41701511) B41701511
theorem B4557221 : Blo 599292 4557221 := bstep (se 4 (by rfl) ⟨427239, by rfl⟩ : syracuseStep 4557221 = 854479) B854479
theorem B601115 : Blo 599292 601115 := bstep (se 1 (by rfl) ⟨450836, by rfl⟩ : syracuseStep 601115 = 901673) B901673
theorem B296544077 : Blo 599292 296544077 := bstep (se 3 (by rfl) ⟨55602014, by rfl⟩ : syracuseStep 296544077 = 111204029) B111204029
theorem B86830325 : Blo 599292 86830325 := bstep (se 5 (by rfl) ⟨4070171, by rfl⟩ : syracuseStep 86830325 = 8140343) B8140343
theorem B75068579 : Blo 599292 75068579 := bstep (se 1 (by rfl) ⟨56301434, by rfl⟩ : syracuseStep 75068579 = 112602869) B112602869
theorem B200182877 : Blo 599292 200182877 := bstep (se 3 (by rfl) ⟨37534289, by rfl⟩ : syracuseStep 200182877 = 75068579) B75068579
theorem B197696051 : Blo 599292 197696051 := bstep (se 1 (by rfl) ⟨148272038, by rfl⟩ : syracuseStep 197696051 = 296544077) B296544077
theorem B57886883 : Blo 599292 57886883 := bstep (se 1 (by rfl) ⟨43415162, by rfl⟩ : syracuseStep 57886883 = 86830325) B86830325
theorem B3038147 : Blo 599292 3038147 := bstep (se 1 (by rfl) ⟨2278610, by rfl⟩ : syracuseStep 3038147 = 4557221) B4557221
theorem B131797367 : Blo 599292 131797367 := bstep (se 1 (by rfl) ⟨98848025, by rfl⟩ : syracuseStep 131797367 = 197696051) B197696051
theorem B38591255 : Blo 599292 38591255 := bstep (se 1 (by rfl) ⟨28943441, by rfl⟩ : syracuseStep 38591255 = 57886883) B57886883
theorem B133455251 : Blo 599292 133455251 := bstep (se 1 (by rfl) ⟨100091438, by rfl⟩ : syracuseStep 133455251 = 200182877) B200182877
theorem B2025431 : Blo 599292 2025431 := bstep (se 1 (by rfl) ⟨1519073, by rfl⟩ : syracuseStep 2025431 = 3038147) B3038147
theorem B25727503 : Blo 599292 25727503 := bstep (se 1 (by rfl) ⟨19295627, by rfl⟩ : syracuseStep 25727503 = 38591255) B38591255
theorem B88970167 : Blo 599292 88970167 := bstep (se 1 (by rfl) ⟨66727625, by rfl⟩ : syracuseStep 88970167 = 133455251) B133455251
theorem B1350287 : Blo 599292 1350287 := bstep (se 1 (by rfl) ⟨1012715, by rfl⟩ : syracuseStep 1350287 = 2025431) B2025431
theorem B87864911 : Blo 599292 87864911 := bstep (se 1 (by rfl) ⟨65898683, by rfl⟩ : syracuseStep 87864911 = 131797367) B131797367
theorem B118626889 : Blo 599292 118626889 := bstep (se 2 (by rfl) ⟨44485083, by rfl⟩ : syracuseStep 118626889 = 88970167) B88970167
theorem B900191 : Blo 599292 900191 := bstep (se 1 (by rfl) ⟨675143, by rfl⟩ : syracuseStep 900191 = 1350287) B1350287
theorem B58576607 : Blo 599292 58576607 := bstep (se 1 (by rfl) ⟨43932455, by rfl⟩ : syracuseStep 58576607 = 87864911) B87864911
theorem B34303337 : Blo 599292 34303337 := bstep (se 2 (by rfl) ⟨12863751, by rfl⟩ : syracuseStep 34303337 = 25727503) B25727503
theorem B600127 : Blo 599292 600127 := bstep (se 1 (by rfl) ⟨450095, by rfl⟩ : syracuseStep 600127 = 900191) B900191
theorem B39051071 : Blo 599292 39051071 := bstep (se 1 (by rfl) ⟨29288303, by rfl⟩ : syracuseStep 39051071 = 58576607) B58576607
theorem B22868891 : Blo 599292 22868891 := bstep (se 1 (by rfl) ⟨17151668, by rfl⟩ : syracuseStep 22868891 = 34303337) B34303337
theorem B158169185 : Blo 599292 158169185 := bstep (se 2 (by rfl) ⟨59313444, by rfl⟩ : syracuseStep 158169185 = 118626889) B118626889
theorem B15245927 : Blo 599292 15245927 := bstep (se 1 (by rfl) ⟨11434445, by rfl⟩ : syracuseStep 15245927 = 22868891) B22868891
theorem B26034047 : Blo 599292 26034047 := bstep (se 1 (by rfl) ⟨19525535, by rfl⟩ : syracuseStep 26034047 = 39051071) B39051071
theorem B105446123 : Blo 599292 105446123 := bstep (se 1 (by rfl) ⟨79084592, by rfl⟩ : syracuseStep 105446123 = 158169185) B158169185
theorem B10163951 : Blo 599292 10163951 := bstep (se 1 (by rfl) ⟨7622963, by rfl⟩ : syracuseStep 10163951 = 15245927) B15245927
theorem B70297415 : Blo 599292 70297415 := bstep (se 1 (by rfl) ⟨52723061, by rfl⟩ : syracuseStep 70297415 = 105446123) B105446123
theorem B17356031 : Blo 599292 17356031 := bstep (se 1 (by rfl) ⟨13017023, by rfl⟩ : syracuseStep 17356031 = 26034047) B26034047
theorem B11570687 : Blo 599292 11570687 := bstep (se 1 (by rfl) ⟨8678015, by rfl⟩ : syracuseStep 11570687 = 17356031) B17356031
theorem B46864943 : Blo 599292 46864943 := bstep (se 1 (by rfl) ⟨35148707, by rfl⟩ : syracuseStep 46864943 = 70297415) B70297415
theorem B6775967 : Blo 599292 6775967 := bstep (se 1 (by rfl) ⟨5081975, by rfl⟩ : syracuseStep 6775967 = 10163951) B10163951
theorem B7713791 : Blo 599292 7713791 := bstep (se 1 (by rfl) ⟨5785343, by rfl⟩ : syracuseStep 7713791 = 11570687) B11570687
theorem B18069245 : Blo 599292 18069245 := bstep (se 3 (by rfl) ⟨3387983, by rfl⟩ : syracuseStep 18069245 = 6775967) B6775967
theorem B31243295 : Blo 599292 31243295 := bstep (se 1 (by rfl) ⟨23432471, by rfl⟩ : syracuseStep 31243295 = 46864943) B46864943
theorem B12046163 : Blo 599292 12046163 := bstep (se 1 (by rfl) ⟨9034622, by rfl⟩ : syracuseStep 12046163 = 18069245) B18069245
theorem B20828863 : Blo 599292 20828863 := bstep (se 1 (by rfl) ⟨15621647, by rfl⟩ : syracuseStep 20828863 = 31243295) B31243295
theorem B5142527 : Blo 599292 5142527 := bstep (se 1 (by rfl) ⟨3856895, by rfl⟩ : syracuseStep 5142527 = 7713791) B7713791
theorem B32123101 : Blo 599292 32123101 := bstep (se 3 (by rfl) ⟨6023081, by rfl⟩ : syracuseStep 32123101 = 12046163) B12046163
theorem B27771817 : Blo 599292 27771817 := bstep (se 2 (by rfl) ⟨10414431, by rfl⟩ : syracuseStep 27771817 = 20828863) B20828863
theorem B3428351 : Blo 599292 3428351 := bstep (se 1 (by rfl) ⟨2571263, by rfl⟩ : syracuseStep 3428351 = 5142527) B5142527
theorem B37029089 : Blo 599292 37029089 := bstep (se 2 (by rfl) ⟨13885908, by rfl⟩ : syracuseStep 37029089 = 27771817) B27771817
theorem B42830801 : Blo 599292 42830801 := bstep (se 2 (by rfl) ⟨16061550, by rfl⟩ : syracuseStep 42830801 = 32123101) B32123101
theorem B2285567 : Blo 599292 2285567 := bstep (se 1 (by rfl) ⟨1714175, by rfl⟩ : syracuseStep 2285567 = 3428351) B3428351
theorem B24686059 : Blo 599292 24686059 := bstep (se 1 (by rfl) ⟨18514544, by rfl⟩ : syracuseStep 24686059 = 37029089) B37029089
theorem B28553867 : Blo 599292 28553867 := bstep (se 1 (by rfl) ⟨21415400, by rfl⟩ : syracuseStep 28553867 = 42830801) B42830801
theorem B1523711 : Blo 599292 1523711 := bstep (se 1 (by rfl) ⟨1142783, by rfl⟩ : syracuseStep 1523711 = 2285567) B2285567
theorem B32914745 : Blo 599292 32914745 := bstep (se 2 (by rfl) ⟨12343029, by rfl⟩ : syracuseStep 32914745 = 24686059) B24686059
theorem B19035911 : Blo 599292 19035911 := bstep (se 1 (by rfl) ⟨14276933, by rfl⟩ : syracuseStep 19035911 = 28553867) B28553867
theorem B1015807 : Blo 599292 1015807 := bstep (se 1 (by rfl) ⟨761855, by rfl⟩ : syracuseStep 1015807 = 1523711) B1523711
theorem B12690607 : Blo 599292 12690607 := bstep (se 1 (by rfl) ⟨9517955, by rfl⟩ : syracuseStep 12690607 = 19035911) B19035911
theorem B1354409 : Blo 599292 1354409 := bstep (se 2 (by rfl) ⟨507903, by rfl⟩ : syracuseStep 1354409 = 1015807) B1015807
theorem B21943163 : Blo 599292 21943163 := bstep (se 1 (by rfl) ⟨16457372, by rfl⟩ : syracuseStep 21943163 = 32914745) B32914745
theorem B16920809 : Blo 599292 16920809 := bstep (se 2 (by rfl) ⟨6345303, by rfl⟩ : syracuseStep 16920809 = 12690607) B12690607
theorem B14628775 : Blo 599292 14628775 := bstep (se 1 (by rfl) ⟨10971581, by rfl⟩ : syracuseStep 14628775 = 21943163) B21943163
theorem B902939 : Blo 599292 902939 := bstep (se 1 (by rfl) ⟨677204, by rfl⟩ : syracuseStep 902939 = 1354409) B1354409
theorem B19505033 : Blo 599292 19505033 := bstep (se 2 (by rfl) ⟨7314387, by rfl⟩ : syracuseStep 19505033 = 14628775) B14628775
theorem B11280539 : Blo 599292 11280539 := bstep (se 1 (by rfl) ⟨8460404, by rfl⟩ : syracuseStep 11280539 = 16920809) B16920809
theorem B601959 : Blo 599292 601959 := bstep (se 1 (by rfl) ⟨451469, by rfl⟩ : syracuseStep 601959 = 902939) B902939
theorem B7520359 : Blo 599292 7520359 := bstep (se 1 (by rfl) ⟨5640269, by rfl⟩ : syracuseStep 7520359 = 11280539) B11280539
theorem B13003355 : Blo 599292 13003355 := bstep (se 1 (by rfl) ⟨9752516, by rfl⟩ : syracuseStep 13003355 = 19505033) B19505033
theorem B10027145 : Blo 599292 10027145 := bstep (se 2 (by rfl) ⟨3760179, by rfl⟩ : syracuseStep 10027145 = 7520359) B7520359
theorem B8668903 : Blo 599292 8668903 := bstep (se 1 (by rfl) ⟨6501677, by rfl⟩ : syracuseStep 8668903 = 13003355) B13003355
theorem B6684763 : Blo 599292 6684763 := bstep (se 1 (by rfl) ⟨5013572, by rfl⟩ : syracuseStep 6684763 = 10027145) B10027145
theorem B11558537 : Blo 599292 11558537 := bstep (se 2 (by rfl) ⟨4334451, by rfl⟩ : syracuseStep 11558537 = 8668903) B8668903
theorem B8913017 : Blo 599292 8913017 := bstep (se 2 (by rfl) ⟨3342381, by rfl⟩ : syracuseStep 8913017 = 6684763) B6684763
theorem B7705691 : Blo 599292 7705691 := bstep (se 1 (by rfl) ⟨5779268, by rfl⟩ : syracuseStep 7705691 = 11558537) B11558537
theorem B5942011 : Blo 599292 5942011 := bstep (se 1 (by rfl) ⟨4456508, by rfl⟩ : syracuseStep 5942011 = 8913017) B8913017
theorem B5137127 : Blo 599292 5137127 := bstep (se 1 (by rfl) ⟨3852845, by rfl⟩ : syracuseStep 5137127 = 7705691) B7705691
theorem B3424751 : Blo 599292 3424751 := bstep (se 1 (by rfl) ⟨2568563, by rfl⟩ : syracuseStep 3424751 = 5137127) B5137127
theorem B7922681 : Blo 599292 7922681 := bstep (se 2 (by rfl) ⟨2971005, by rfl⟩ : syracuseStep 7922681 = 5942011) B5942011
theorem B5281787 : Blo 599292 5281787 := bstep (se 1 (by rfl) ⟨3961340, by rfl⟩ : syracuseStep 5281787 = 7922681) B7922681
theorem B2283167 : Blo 599292 2283167 := bstep (se 1 (by rfl) ⟨1712375, by rfl⟩ : syracuseStep 2283167 = 3424751) B3424751
theorem B1522111 : Blo 599292 1522111 := bstep (se 1 (by rfl) ⟨1141583, by rfl⟩ : syracuseStep 1522111 = 2283167) B2283167
theorem B3521191 : Blo 599292 3521191 := bstep (se 1 (by rfl) ⟨2640893, by rfl⟩ : syracuseStep 3521191 = 5281787) B5281787
theorem B4694921 : Blo 599292 4694921 := bstep (se 2 (by rfl) ⟨1760595, by rfl⟩ : syracuseStep 4694921 = 3521191) B3521191
theorem B2029481 : Blo 599292 2029481 := bstep (se 2 (by rfl) ⟨761055, by rfl⟩ : syracuseStep 2029481 = 1522111) B1522111
theorem B1352987 : Blo 599292 1352987 := bstep (se 1 (by rfl) ⟨1014740, by rfl⟩ : syracuseStep 1352987 = 2029481) B2029481
theorem B3129947 : Blo 599292 3129947 := bstep (se 1 (by rfl) ⟨2347460, by rfl⟩ : syracuseStep 3129947 = 4694921) B4694921
theorem B901991 : Blo 599292 901991 := bstep (se 1 (by rfl) ⟨676493, by rfl⟩ : syracuseStep 901991 = 1352987) B1352987
theorem B2086631 : Blo 599292 2086631 := bstep (se 1 (by rfl) ⟨1564973, by rfl⟩ : syracuseStep 2086631 = 3129947) B3129947
theorem B601327 : Blo 599292 601327 := bstep (se 1 (by rfl) ⟨450995, by rfl⟩ : syracuseStep 601327 = 901991) B901991
theorem B1391087 : Blo 599292 1391087 := bstep (se 1 (by rfl) ⟨1043315, by rfl⟩ : syracuseStep 1391087 = 2086631) B2086631
theorem B927391 : Blo 599292 927391 := bstep (se 1 (by rfl) ⟨695543, by rfl⟩ : syracuseStep 927391 = 1391087) B1391087
theorem B1236521 : Blo 599292 1236521 := bstep (se 2 (by rfl) ⟨463695, by rfl⟩ : syracuseStep 1236521 = 927391) B927391
theorem B824347 : Blo 599292 824347 := bstep (se 1 (by rfl) ⟨618260, by rfl⟩ : syracuseStep 824347 = 1236521) B1236521
theorem B1099129 : Blo 599292 1099129 := bstep (se 2 (by rfl) ⟨412173, by rfl⟩ : syracuseStep 1099129 = 824347) B824347
theorem B1465505 : Blo 599292 1465505 := bstep (se 2 (by rfl) ⟨549564, by rfl⟩ : syracuseStep 1465505 = 1099129) B1099129
theorem B977003 : Blo 599292 977003 := bstep (se 1 (by rfl) ⟨732752, by rfl⟩ : syracuseStep 977003 = 1465505) B1465505
theorem B651335 : Blo 599292 651335 := bstep (se 1 (by rfl) ⟨488501, by rfl⟩ : syracuseStep 651335 = 977003) B977003
theorem B1736893 : Blo 599292 1736893 := bstep (se 3 (by rfl) ⟨325667, by rfl⟩ : syracuseStep 1736893 = 651335) B651335
theorem B9263429 : Blo 599292 9263429 := bstep (se 4 (by rfl) ⟨868446, by rfl⟩ : syracuseStep 9263429 = 1736893) B1736893
theorem B6175619 : Blo 599292 6175619 := bstep (se 1 (by rfl) ⟨4631714, by rfl⟩ : syracuseStep 6175619 = 9263429) B9263429
theorem B4117079 : Blo 599292 4117079 := bstep (se 1 (by rfl) ⟨3087809, by rfl⟩ : syracuseStep 4117079 = 6175619) B6175619
theorem B10978877 : Blo 599292 10978877 := bstep (se 3 (by rfl) ⟨2058539, by rfl⟩ : syracuseStep 10978877 = 4117079) B4117079
theorem B7319251 : Blo 599292 7319251 := bstep (se 1 (by rfl) ⟨5489438, by rfl⟩ : syracuseStep 7319251 = 10978877) B10978877
theorem B39036005 : Blo 599292 39036005 := bstep (se 4 (by rfl) ⟨3659625, by rfl⟩ : syracuseStep 39036005 = 7319251) B7319251
theorem B26024003 : Blo 599292 26024003 := bstep (se 1 (by rfl) ⟨19518002, by rfl⟩ : syracuseStep 26024003 = 39036005) B39036005
theorem B17349335 : Blo 599292 17349335 := bstep (se 1 (by rfl) ⟨13012001, by rfl⟩ : syracuseStep 17349335 = 26024003) B26024003
theorem B11566223 : Blo 599292 11566223 := bstep (se 1 (by rfl) ⟨8674667, by rfl⟩ : syracuseStep 11566223 = 17349335) B17349335
theorem B7710815 : Blo 599292 7710815 := bstep (se 1 (by rfl) ⟨5783111, by rfl⟩ : syracuseStep 7710815 = 11566223) B11566223
theorem B5140543 : Blo 599292 5140543 := bstep (se 1 (by rfl) ⟨3855407, by rfl⟩ : syracuseStep 5140543 = 7710815) B7710815
theorem B6854057 : Blo 599292 6854057 := bstep (se 2 (by rfl) ⟨2570271, by rfl⟩ : syracuseStep 6854057 = 5140543) B5140543
theorem B4569371 : Blo 599292 4569371 := bstep (se 1 (by rfl) ⟨3427028, by rfl⟩ : syracuseStep 4569371 = 6854057) B6854057
theorem B3046247 : Blo 599292 3046247 := bstep (se 1 (by rfl) ⟨2284685, by rfl⟩ : syracuseStep 3046247 = 4569371) B4569371
theorem B2030831 : Blo 599292 2030831 := bstep (se 1 (by rfl) ⟨1523123, by rfl⟩ : syracuseStep 2030831 = 3046247) B3046247
theorem B1353887 : Blo 599292 1353887 := bstep (se 1 (by rfl) ⟨1015415, by rfl⟩ : syracuseStep 1353887 = 2030831) B2030831
theorem B902591 : Blo 599292 902591 := bstep (se 1 (by rfl) ⟨676943, by rfl⟩ : syracuseStep 902591 = 1353887) B1353887
theorem B601727 : Blo 599292 601727 := bstep (se 1 (by rfl) ⟨451295, by rfl⟩ : syracuseStep 601727 = 902591) B902591

theorem C0 (j : ℕ) (h1 : 149823 ≤ j) (h2 : j ≤ 150522) : Blo 599292 (4 * j + 3) := by
  interval_cases j
  · exact B599295
  · exact B599299
  · exact B599303
  · exact B599307
  · exact B599311
  · exact B599315
  · exact B599319
  · exact B599323
  · exact B599327
  · exact B599331
  · exact B599335
  · exact B599339
  · exact B599343
  · exact B599347
  · exact B599351
  · exact B599355
  · exact B599359
  · exact B599363
  · exact B599367
  · exact B599371
  · exact B599375
  · exact B599379
  · exact B599383
  · exact B599387
  · exact B599391
  · exact B599395
  · exact B599399
  · exact B599403
  · exact B599407
  · exact B599411
  · exact B599415
  · exact B599419
  · exact B599423
  · exact B599427
  · exact B599431
  · exact B599435
  · exact B599439
  · exact B599443
  · exact B599447
  · exact B599451
  · exact B599455
  · exact B599459
  · exact B599463
  · exact B599467
  · exact B599471
  · exact B599475
  · exact B599479
  · exact B599483
  · exact B599487
  · exact B599491
  · exact B599495
  · exact B599499
  · exact B599503
  · exact B599507
  · exact B599511
  · exact B599515
  · exact B599519
  · exact B599523
  · exact B599527
  · exact B599531
  · exact B599535
  · exact B599539
  · exact B599543
  · exact B599547
  · exact B599551
  · exact B599555
  · exact B599559
  · exact B599563
  · exact B599567
  · exact B599571
  · exact B599575
  · exact B599579
  · exact B599583
  · exact B599587
  · exact B599591
  · exact B599595
  · exact B599599
  · exact B599603
  · exact B599607
  · exact B599611
  · exact B599615
  · exact B599619
  · exact B599623
  · exact B599627
  · exact B599631
  · exact B599635
  · exact B599639
  · exact B599643
  · exact B599647
  · exact B599651
  · exact B599655
  · exact B599659
  · exact B599663
  · exact B599667
  · exact B599671
  · exact B599675
  · exact B599679
  · exact B599683
  · exact B599687
  · exact B599691
  · exact B599695
  · exact B599699
  · exact B599703
  · exact B599707
  · exact B599711
  · exact B599715
  · exact B599719
  · exact B599723
  · exact B599727
  · exact B599731
  · exact B599735
  · exact B599739
  · exact B599743
  · exact B599747
  · exact B599751
  · exact B599755
  · exact B599759
  · exact B599763
  · exact B599767
  · exact B599771
  · exact B599775
  · exact B599779
  · exact B599783
  · exact B599787
  · exact B599791
  · exact B599795
  · exact B599799
  · exact B599803
  · exact B599807
  · exact B599811
  · exact B599815
  · exact B599819
  · exact B599823
  · exact B599827
  · exact B599831
  · exact B599835
  · exact B599839
  · exact B599843
  · exact B599847
  · exact B599851
  · exact B599855
  · exact B599859
  · exact B599863
  · exact B599867
  · exact B599871
  · exact B599875
  · exact B599879
  · exact B599883
  · exact B599887
  · exact B599891
  · exact B599895
  · exact B599899
  · exact B599903
  · exact B599907
  · exact B599911
  · exact B599915
  · exact B599919
  · exact B599923
  · exact B599927
  · exact B599931
  · exact B599935
  · exact B599939
  · exact B599943
  · exact B599947
  · exact B599951
  · exact B599955
  · exact B599959
  · exact B599963
  · exact B599967
  · exact B599971
  · exact B599975
  · exact B599979
  · exact B599983
  · exact B599987
  · exact B599991
  · exact B599995
  · exact B599999
  · exact B600003
  · exact B600007
  · exact B600011
  · exact B600015
  · exact B600019
  · exact B600023
  · exact B600027
  · exact B600031
  · exact B600035
  · exact B600039
  · exact B600043
  · exact B600047
  · exact B600051
  · exact B600055
  · exact B600059
  · exact B600063
  · exact B600067
  · exact B600071
  · exact B600075
  · exact B600079
  · exact B600083
  · exact B600087
  · exact B600091
  · exact B600095
  · exact B600099
  · exact B600103
  · exact B600107
  · exact B600111
  · exact B600115
  · exact B600119
  · exact B600123
  · exact B600127
  · exact B600131
  · exact B600135
  · exact B600139
  · exact B600143
  · exact B600147
  · exact B600151
  · exact B600155
  · exact B600159
  · exact B600163
  · exact B600167
  · exact B600171
  · exact B600175
  · exact B600179
  · exact B600183
  · exact B600187
  · exact B600191
  · exact B600195
  · exact B600199
  · exact B600203
  · exact B600207
  · exact B600211
  · exact B600215
  · exact B600219
  · exact B600223
  · exact B600227
  · exact B600231
  · exact B600235
  · exact B600239
  · exact B600243
  · exact B600247
  · exact B600251
  · exact B600255
  · exact B600259
  · exact B600263
  · exact B600267
  · exact B600271
  · exact B600275
  · exact B600279
  · exact B600283
  · exact B600287
  · exact B600291
  · exact B600295
  · exact B600299
  · exact B600303
  · exact B600307
  · exact B600311
  · exact B600315
  · exact B600319
  · exact B600323
  · exact B600327
  · exact B600331
  · exact B600335
  · exact B600339
  · exact B600343
  · exact B600347
  · exact B600351
  · exact B600355
  · exact B600359
  · exact B600363
  · exact B600367
  · exact B600371
  · exact B600375
  · exact B600379
  · exact B600383
  · exact B600387
  · exact B600391
  · exact B600395
  · exact B600399
  · exact B600403
  · exact B600407
  · exact B600411
  · exact B600415
  · exact B600419
  · exact B600423
  · exact B600427
  · exact B600431
  · exact B600435
  · exact B600439
  · exact B600443
  · exact B600447
  · exact B600451
  · exact B600455
  · exact B600459
  · exact B600463
  · exact B600467
  · exact B600471
  · exact B600475
  · exact B600479
  · exact B600483
  · exact B600487
  · exact B600491
  · exact B600495
  · exact B600499
  · exact B600503
  · exact B600507
  · exact B600511
  · exact B600515
  · exact B600519
  · exact B600523
  · exact B600527
  · exact B600531
  · exact B600535
  · exact B600539
  · exact B600543
  · exact B600547
  · exact B600551
  · exact B600555
  · exact B600559
  · exact B600563
  · exact B600567
  · exact B600571
  · exact B600575
  · exact B600579
  · exact B600583
  · exact B600587
  · exact B600591
  · exact B600595
  · exact B600599
  · exact B600603
  · exact B600607
  · exact B600611
  · exact B600615
  · exact B600619
  · exact B600623
  · exact B600627
  · exact B600631
  · exact B600635
  · exact B600639
  · exact B600643
  · exact B600647
  · exact B600651
  · exact B600655
  · exact B600659
  · exact B600663
  · exact B600667
  · exact B600671
  · exact B600675
  · exact B600679
  · exact B600683
  · exact B600687
  · exact B600691
  · exact B600695
  · exact B600699
  · exact B600703
  · exact B600707
  · exact B600711
  · exact B600715
  · exact B600719
  · exact B600723
  · exact B600727
  · exact B600731
  · exact B600735
  · exact B600739
  · exact B600743
  · exact B600747
  · exact B600751
  · exact B600755
  · exact B600759
  · exact B600763
  · exact B600767
  · exact B600771
  · exact B600775
  · exact B600779
  · exact B600783
  · exact B600787
  · exact B600791
  · exact B600795
  · exact B600799
  · exact B600803
  · exact B600807
  · exact B600811
  · exact B600815
  · exact B600819
  · exact B600823
  · exact B600827
  · exact B600831
  · exact B600835
  · exact B600839
  · exact B600843
  · exact B600847
  · exact B600851
  · exact B600855
  · exact B600859
  · exact B600863
  · exact B600867
  · exact B600871
  · exact B600875
  · exact B600879
  · exact B600883
  · exact B600887
  · exact B600891
  · exact B600895
  · exact B600899
  · exact B600903
  · exact B600907
  · exact B600911
  · exact B600915
  · exact B600919
  · exact B600923
  · exact B600927
  · exact B600931
  · exact B600935
  · exact B600939
  · exact B600943
  · exact B600947
  · exact B600951
  · exact B600955
  · exact B600959
  · exact B600963
  · exact B600967
  · exact B600971
  · exact B600975
  · exact B600979
  · exact B600983
  · exact B600987
  · exact B600991
  · exact B600995
  · exact B600999
  · exact B601003
  · exact B601007
  · exact B601011
  · exact B601015
  · exact B601019
  · exact B601023
  · exact B601027
  · exact B601031
  · exact B601035
  · exact B601039
  · exact B601043
  · exact B601047
  · exact B601051
  · exact B601055
  · exact B601059
  · exact B601063
  · exact B601067
  · exact B601071
  · exact B601075
  · exact B601079
  · exact B601083
  · exact B601087
  · exact B601091
  · exact B601095
  · exact B601099
  · exact B601103
  · exact B601107
  · exact B601111
  · exact B601115
  · exact B601119
  · exact B601123
  · exact B601127
  · exact B601131
  · exact B601135
  · exact B601139
  · exact B601143
  · exact B601147
  · exact B601151
  · exact B601155
  · exact B601159
  · exact B601163
  · exact B601167
  · exact B601171
  · exact B601175
  · exact B601179
  · exact B601183
  · exact B601187
  · exact B601191
  · exact B601195
  · exact B601199
  · exact B601203
  · exact B601207
  · exact B601211
  · exact B601215
  · exact B601219
  · exact B601223
  · exact B601227
  · exact B601231
  · exact B601235
  · exact B601239
  · exact B601243
  · exact B601247
  · exact B601251
  · exact B601255
  · exact B601259
  · exact B601263
  · exact B601267
  · exact B601271
  · exact B601275
  · exact B601279
  · exact B601283
  · exact B601287
  · exact B601291
  · exact B601295
  · exact B601299
  · exact B601303
  · exact B601307
  · exact B601311
  · exact B601315
  · exact B601319
  · exact B601323
  · exact B601327
  · exact B601331
  · exact B601335
  · exact B601339
  · exact B601343
  · exact B601347
  · exact B601351
  · exact B601355
  · exact B601359
  · exact B601363
  · exact B601367
  · exact B601371
  · exact B601375
  · exact B601379
  · exact B601383
  · exact B601387
  · exact B601391
  · exact B601395
  · exact B601399
  · exact B601403
  · exact B601407
  · exact B601411
  · exact B601415
  · exact B601419
  · exact B601423
  · exact B601427
  · exact B601431
  · exact B601435
  · exact B601439
  · exact B601443
  · exact B601447
  · exact B601451
  · exact B601455
  · exact B601459
  · exact B601463
  · exact B601467
  · exact B601471
  · exact B601475
  · exact B601479
  · exact B601483
  · exact B601487
  · exact B601491
  · exact B601495
  · exact B601499
  · exact B601503
  · exact B601507
  · exact B601511
  · exact B601515
  · exact B601519
  · exact B601523
  · exact B601527
  · exact B601531
  · exact B601535
  · exact B601539
  · exact B601543
  · exact B601547
  · exact B601551
  · exact B601555
  · exact B601559
  · exact B601563
  · exact B601567
  · exact B601571
  · exact B601575
  · exact B601579
  · exact B601583
  · exact B601587
  · exact B601591
  · exact B601595
  · exact B601599
  · exact B601603
  · exact B601607
  · exact B601611
  · exact B601615
  · exact B601619
  · exact B601623
  · exact B601627
  · exact B601631
  · exact B601635
  · exact B601639
  · exact B601643
  · exact B601647
  · exact B601651
  · exact B601655
  · exact B601659
  · exact B601663
  · exact B601667
  · exact B601671
  · exact B601675
  · exact B601679
  · exact B601683
  · exact B601687
  · exact B601691
  · exact B601695
  · exact B601699
  · exact B601703
  · exact B601707
  · exact B601711
  · exact B601715
  · exact B601719
  · exact B601723
  · exact B601727
  · exact B601731
  · exact B601735
  · exact B601739
  · exact B601743
  · exact B601747
  · exact B601751
  · exact B601755
  · exact B601759
  · exact B601763
  · exact B601767
  · exact B601771
  · exact B601775
  · exact B601779
  · exact B601783
  · exact B601787
  · exact B601791
  · exact B601795
  · exact B601799
  · exact B601803
  · exact B601807
  · exact B601811
  · exact B601815
  · exact B601819
  · exact B601823
  · exact B601827
  · exact B601831
  · exact B601835
  · exact B601839
  · exact B601843
  · exact B601847
  · exact B601851
  · exact B601855
  · exact B601859
  · exact B601863
  · exact B601867
  · exact B601871
  · exact B601875
  · exact B601879
  · exact B601883
  · exact B601887
  · exact B601891
  · exact B601895
  · exact B601899
  · exact B601903
  · exact B601907
  · exact B601911
  · exact B601915
  · exact B601919
  · exact B601923
  · exact B601927
  · exact B601931
  · exact B601935
  · exact B601939
  · exact B601943
  · exact B601947
  · exact B601951
  · exact B601955
  · exact B601959
  · exact B601963
  · exact B601967
  · exact B601971
  · exact B601975
  · exact B601979
  · exact B601983
  · exact B601987
  · exact B601991
  · exact B601995
  · exact B601999
  · exact B602003
  · exact B602007
  · exact B602011
  · exact B602015
  · exact B602019
  · exact B602023
  · exact B602027
  · exact B602031
  · exact B602035
  · exact B602039
  · exact B602043
  · exact B602047
  · exact B602051
  · exact B602055
  · exact B602059
  · exact B602063
  · exact B602067
  · exact B602071
  · exact B602075
  · exact B602079
  · exact B602083
  · exact B602087
  · exact B602091

theorem C1 (j : ℕ) (h1 : 150523 ≤ j) (h2 : j ≤ 150822) : Blo 599292 (4 * j + 3) := by
  interval_cases j
  · exact B602095
  · exact B602099
  · exact B602103
  · exact B602107
  · exact B602111
  · exact B602115
  · exact B602119
  · exact B602123
  · exact B602127
  · exact B602131
  · exact B602135
  · exact B602139
  · exact B602143
  · exact B602147
  · exact B602151
  · exact B602155
  · exact B602159
  · exact B602163
  · exact B602167
  · exact B602171
  · exact B602175
  · exact B602179
  · exact B602183
  · exact B602187
  · exact B602191
  · exact B602195
  · exact B602199
  · exact B602203
  · exact B602207
  · exact B602211
  · exact B602215
  · exact B602219
  · exact B602223
  · exact B602227
  · exact B602231
  · exact B602235
  · exact B602239
  · exact B602243
  · exact B602247
  · exact B602251
  · exact B602255
  · exact B602259
  · exact B602263
  · exact B602267
  · exact B602271
  · exact B602275
  · exact B602279
  · exact B602283
  · exact B602287
  · exact B602291
  · exact B602295
  · exact B602299
  · exact B602303
  · exact B602307
  · exact B602311
  · exact B602315
  · exact B602319
  · exact B602323
  · exact B602327
  · exact B602331
  · exact B602335
  · exact B602339
  · exact B602343
  · exact B602347
  · exact B602351
  · exact B602355
  · exact B602359
  · exact B602363
  · exact B602367
  · exact B602371
  · exact B602375
  · exact B602379
  · exact B602383
  · exact B602387
  · exact B602391
  · exact B602395
  · exact B602399
  · exact B602403
  · exact B602407
  · exact B602411
  · exact B602415
  · exact B602419
  · exact B602423
  · exact B602427
  · exact B602431
  · exact B602435
  · exact B602439
  · exact B602443
  · exact B602447
  · exact B602451
  · exact B602455
  · exact B602459
  · exact B602463
  · exact B602467
  · exact B602471
  · exact B602475
  · exact B602479
  · exact B602483
  · exact B602487
  · exact B602491
  · exact B602495
  · exact B602499
  · exact B602503
  · exact B602507
  · exact B602511
  · exact B602515
  · exact B602519
  · exact B602523
  · exact B602527
  · exact B602531
  · exact B602535
  · exact B602539
  · exact B602543
  · exact B602547
  · exact B602551
  · exact B602555
  · exact B602559
  · exact B602563
  · exact B602567
  · exact B602571
  · exact B602575
  · exact B602579
  · exact B602583
  · exact B602587
  · exact B602591
  · exact B602595
  · exact B602599
  · exact B602603
  · exact B602607
  · exact B602611
  · exact B602615
  · exact B602619
  · exact B602623
  · exact B602627
  · exact B602631
  · exact B602635
  · exact B602639
  · exact B602643
  · exact B602647
  · exact B602651
  · exact B602655
  · exact B602659
  · exact B602663
  · exact B602667
  · exact B602671
  · exact B602675
  · exact B602679
  · exact B602683
  · exact B602687
  · exact B602691
  · exact B602695
  · exact B602699
  · exact B602703
  · exact B602707
  · exact B602711
  · exact B602715
  · exact B602719
  · exact B602723
  · exact B602727
  · exact B602731
  · exact B602735
  · exact B602739
  · exact B602743
  · exact B602747
  · exact B602751
  · exact B602755
  · exact B602759
  · exact B602763
  · exact B602767
  · exact B602771
  · exact B602775
  · exact B602779
  · exact B602783
  · exact B602787
  · exact B602791
  · exact B602795
  · exact B602799
  · exact B602803
  · exact B602807
  · exact B602811
  · exact B602815
  · exact B602819
  · exact B602823
  · exact B602827
  · exact B602831
  · exact B602835
  · exact B602839
  · exact B602843
  · exact B602847
  · exact B602851
  · exact B602855
  · exact B602859
  · exact B602863
  · exact B602867
  · exact B602871
  · exact B602875
  · exact B602879
  · exact B602883
  · exact B602887
  · exact B602891
  · exact B602895
  · exact B602899
  · exact B602903
  · exact B602907
  · exact B602911
  · exact B602915
  · exact B602919
  · exact B602923
  · exact B602927
  · exact B602931
  · exact B602935
  · exact B602939
  · exact B602943
  · exact B602947
  · exact B602951
  · exact B602955
  · exact B602959
  · exact B602963
  · exact B602967
  · exact B602971
  · exact B602975
  · exact B602979
  · exact B602983
  · exact B602987
  · exact B602991
  · exact B602995
  · exact B602999
  · exact B603003
  · exact B603007
  · exact B603011
  · exact B603015
  · exact B603019
  · exact B603023
  · exact B603027
  · exact B603031
  · exact B603035
  · exact B603039
  · exact B603043
  · exact B603047
  · exact B603051
  · exact B603055
  · exact B603059
  · exact B603063
  · exact B603067
  · exact B603071
  · exact B603075
  · exact B603079
  · exact B603083
  · exact B603087
  · exact B603091
  · exact B603095
  · exact B603099
  · exact B603103
  · exact B603107
  · exact B603111
  · exact B603115
  · exact B603119
  · exact B603123
  · exact B603127
  · exact B603131
  · exact B603135
  · exact B603139
  · exact B603143
  · exact B603147
  · exact B603151
  · exact B603155
  · exact B603159
  · exact B603163
  · exact B603167
  · exact B603171
  · exact B603175
  · exact B603179
  · exact B603183
  · exact B603187
  · exact B603191
  · exact B603195
  · exact B603199
  · exact B603203
  · exact B603207
  · exact B603211
  · exact B603215
  · exact B603219
  · exact B603223
  · exact B603227
  · exact B603231
  · exact B603235
  · exact B603239
  · exact B603243
  · exact B603247
  · exact B603251
  · exact B603255
  · exact B603259
  · exact B603263
  · exact B603267
  · exact B603271
  · exact B603275
  · exact B603279
  · exact B603283
  · exact B603287
  · exact B603291

theorem solution (m : ℕ) (hlo : 599292 ≤ m) (hhi : m ≤ 603292) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 149823 ≤ j := by omega
    have hj2 : j ≤ 150822 := by omega
    have hb : Blo 599292 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 150523 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
